/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table026
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table026.pv65167
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table005
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr65167 : PrimeCertificate 65167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv10861]) (by decide +kernel)
def pv65167 : PrimeValue := ⟨65167, pr65167⟩
private theorem pr65171 : PrimeCertificate 65171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv19]) (by decide +kernel)
def pv65171 : PrimeValue := ⟨65171, pr65171⟩
private theorem pr65173 : PrimeCertificate 65173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5431]) (by decide +kernel)
def pv65173 : PrimeValue := ⟨65173, pr65173⟩
private theorem pr65179 : PrimeCertificate 65179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv71]) (by decide +kernel)
def pv65179 : PrimeValue := ⟨65179, pr65179⟩
private theorem pr65183 : PrimeCertificate 65183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv23,pv109]) (by decide +kernel)
def pv65183 : PrimeValue := ⟨65183, pr65183⟩
private theorem pr65203 : PrimeCertificate 65203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10867]) (by decide +kernel)
def pv65203 : PrimeValue := ⟨65203, pr65203⟩
private theorem pr65213 : PrimeCertificate 65213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv137]) (by decide +kernel)
def pv65213 : PrimeValue := ⟨65213, pr65213⟩
private theorem pr65239 : PrimeCertificate 65239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv83,pv131]) (by decide +kernel)
def pv65239 : PrimeValue := ⟨65239, pr65239⟩
private theorem pr65257 : PrimeCertificate 65257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2719]) (by decide +kernel)
def pv65257 : PrimeValue := ⟨65257, pr65257⟩
private theorem pr65267 : PrimeCertificate 65267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32633]) (by decide +kernel)
def pv65267 : PrimeValue := ⟨65267, pr65267⟩
private theorem pr65269 : PrimeCertificate 65269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv65269 : PrimeValue := ⟨65269, pr65269⟩
private theorem pr65287 : PrimeCertificate 65287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv65287 : PrimeValue := ⟨65287, pr65287⟩
private theorem pr65293 : PrimeCertificate 65293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5441]) (by decide +kernel)
def pv65293 : PrimeValue := ⟨65293, pr65293⟩
private theorem pr65309 : PrimeCertificate 65309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv563]) (by decide +kernel)
def pv65309 : PrimeValue := ⟨65309, pr65309⟩
private theorem pr65323 : PrimeCertificate 65323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv191]) (by decide +kernel)
def pv65323 : PrimeValue := ⟨65323, pr65323⟩
private theorem pr65327 : PrimeCertificate 65327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv89,pv367]) (by decide +kernel)
def pv65327 : PrimeValue := ⟨65327, pr65327⟩
private theorem pr65353 : PrimeCertificate 65353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv389]) (by decide +kernel)
def pv65353 : PrimeValue := ⟨65353, pr65353⟩
private theorem pr65357 : PrimeCertificate 65357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv16339]) (by decide +kernel)
def pv65357 : PrimeValue := ⟨65357, pr65357⟩
private theorem pr65371 : PrimeCertificate 65371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2179]) (by decide +kernel)
def pv65371 : PrimeValue := ⟨65371, pr65371⟩
private theorem pr65381 : PrimeCertificate 65381 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv467]) (by decide +kernel)
def pv65381 : PrimeValue := ⟨65381, pr65381⟩
private theorem pr65393 : PrimeCertificate 65393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61,pv67]) (by decide +kernel)
def pv65393 : PrimeValue := ⟨65393, pr65393⟩
private theorem pr65407 : PrimeCertificate 65407 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv991]) (by decide +kernel)
def pv65407 : PrimeValue := ⟨65407, pr65407⟩
private theorem pr65413 : PrimeCertificate 65413 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv79]) (by decide +kernel)
def pv65413 : PrimeValue := ⟨65413, pr65413⟩
private theorem pr65419 : PrimeCertificate 65419 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10903]) (by decide +kernel)
def pv65419 : PrimeValue := ⟨65419, pr65419⟩
private theorem pr65423 : PrimeCertificate 65423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv4673]) (by decide +kernel)
def pv65423 : PrimeValue := ⟨65423, pr65423⟩
private theorem pr65437 : PrimeCertificate 65437 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv19,pv41]) (by decide +kernel)
def pv65437 : PrimeValue := ⟨65437, pr65437⟩
private theorem pr65447 : PrimeCertificate 65447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv761]) (by decide +kernel)
def pv65447 : PrimeValue := ⟨65447, pr65447⟩
private theorem pr65449 : PrimeCertificate 65449 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv65449 : PrimeValue := ⟨65449, pr65449⟩
private theorem pr65479 : PrimeCertificate 65479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv1559]) (by decide +kernel)
def pv65479 : PrimeValue := ⟨65479, pr65479⟩
private theorem pr65497 : PrimeCertificate 65497 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2729]) (by decide +kernel)
def pv65497 : PrimeValue := ⟨65497, pr65497⟩
private theorem pr65519 : PrimeCertificate 65519 :=
  certifyPrime (q := pv11) (ls := [pv2,pv17,pv41,pv47]) (by decide +kernel)
def pv65519 : PrimeValue := ⟨65519, pr65519⟩
private theorem pr65521 : PrimeCertificate 65521 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv65521 : PrimeValue := ⟨65521, pr65521⟩
private theorem pr65537 : PrimeCertificate 65537 :=
  certifyPrime (q := pv3) (ls := [pv2]) (by decide +kernel)
def pv65537 : PrimeValue := ⟨65537, pr65537⟩
private theorem pr65539 : PrimeCertificate 65539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv331]) (by decide +kernel)
def pv65539 : PrimeValue := ⟨65539, pr65539⟩
private theorem pr65543 : PrimeCertificate 65543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv32771]) (by decide +kernel)
def pv65543 : PrimeValue := ⟨65543, pr65543⟩
private theorem pr65551 : PrimeCertificate 65551 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv19,pv23]) (by decide +kernel)
def pv65551 : PrimeValue := ⟨65551, pr65551⟩
private theorem pr65557 : PrimeCertificate 65557 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv607]) (by decide +kernel)
def pv65557 : PrimeValue := ⟨65557, pr65557⟩
private theorem pr65563 : PrimeCertificate 65563 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv223]) (by decide +kernel)
def pv65563 : PrimeValue := ⟨65563, pr65563⟩
private theorem pr65579 : PrimeCertificate 65579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32789]) (by decide +kernel)
def pv65579 : PrimeValue := ⟨65579, pr65579⟩
private theorem pr65581 : PrimeCertificate 65581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1093]) (by decide +kernel)
def pv65581 : PrimeValue := ⟨65581, pr65581⟩
private theorem pr65587 : PrimeCertificate 65587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv643]) (by decide +kernel)
def pv65587 : PrimeValue := ⟨65587, pr65587⟩
private theorem pr65609 : PrimeCertificate 65609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv139]) (by decide +kernel)
def pv65609 : PrimeValue := ⟨65609, pr65609⟩
private theorem pr65617 : PrimeCertificate 65617 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1367]) (by decide +kernel)
def pv65617 : PrimeValue := ⟨65617, pr65617⟩
private theorem pr65629 : PrimeCertificate 65629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1823]) (by decide +kernel)
def pv65629 : PrimeValue := ⟨65629, pr65629⟩
private theorem pr65633 : PrimeCertificate 65633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv293]) (by decide +kernel)
def pv65633 : PrimeValue := ⟨65633, pr65633⟩
private theorem pr65647 : PrimeCertificate 65647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv521]) (by decide +kernel)
def pv65647 : PrimeValue := ⟨65647, pr65647⟩
private theorem pr65651 : PrimeCertificate 65651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv101]) (by decide +kernel)
def pv65651 : PrimeValue := ⟨65651, pr65651⟩
private theorem pr65657 : PrimeCertificate 65657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv283]) (by decide +kernel)
def pv65657 : PrimeValue := ⟨65657, pr65657⟩
private theorem pr65677 : PrimeCertificate 65677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv421]) (by decide +kernel)
def pv65677 : PrimeValue := ⟨65677, pr65677⟩
private theorem pr65687 : PrimeCertificate 65687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv32843]) (by decide +kernel)
def pv65687 : PrimeValue := ⟨65687, pr65687⟩
private theorem pr65699 : PrimeCertificate 65699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv307]) (by decide +kernel)
def pv65699 : PrimeValue := ⟨65699, pr65699⟩
private theorem pr65701 : PrimeCertificate 65701 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv65701 : PrimeValue := ⟨65701, pr65701⟩
private theorem pr65707 : PrimeCertificate 65707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv233]) (by decide +kernel)
def pv65707 : PrimeValue := ⟨65707, pr65707⟩
private theorem pr65713 : PrimeCertificate 65713 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv65713 : PrimeValue := ⟨65713, pr65713⟩
private theorem pr65717 : PrimeCertificate 65717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv2347]) (by decide +kernel)
def pv65717 : PrimeValue := ⟨65717, pr65717⟩
private theorem pr65719 : PrimeCertificate 65719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1217]) (by decide +kernel)
def pv65719 : PrimeValue := ⟨65719, pr65719⟩
private theorem pr65729 : PrimeCertificate 65729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv79]) (by decide +kernel)
def pv65729 : PrimeValue := ⟨65729, pr65729⟩
private theorem pr65731 : PrimeCertificate 65731 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv7,pv313]) (by decide +kernel)
def pv65731 : PrimeValue := ⟨65731, pr65731⟩
private theorem pr65761 : PrimeCertificate 65761 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv137]) (by decide +kernel)
def pv65761 : PrimeValue := ⟨65761, pr65761⟩
private theorem pr65777 : PrimeCertificate 65777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4111]) (by decide +kernel)
def pv65777 : PrimeValue := ⟨65777, pr65777⟩
private theorem pr65789 : PrimeCertificate 65789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv16447]) (by decide +kernel)
def pv65789 : PrimeValue := ⟨65789, pr65789⟩
private theorem pr65809 : PrimeCertificate 65809 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv457]) (by decide +kernel)
def pv65809 : PrimeValue := ⟨65809, pr65809⟩
private theorem pr65827 : PrimeCertificate 65827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv53]) (by decide +kernel)
def pv65827 : PrimeValue := ⟨65827, pr65827⟩
private theorem pr65831 : PrimeCertificate 65831 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv29,pv227]) (by decide +kernel)
def pv65831 : PrimeValue := ⟨65831, pr65831⟩
private theorem pr65837 : PrimeCertificate 65837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv151]) (by decide +kernel)
def pv65837 : PrimeValue := ⟨65837, pr65837⟩
private theorem pr65839 : PrimeCertificate 65839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10973]) (by decide +kernel)
def pv65839 : PrimeValue := ⟨65839, pr65839⟩
private theorem pr65843 : PrimeCertificate 65843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4703]) (by decide +kernel)
def pv65843 : PrimeValue := ⟨65843, pr65843⟩
private theorem pr65851 : PrimeCertificate 65851 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv439]) (by decide +kernel)
def pv65851 : PrimeValue := ⟨65851, pr65851⟩
private theorem pr65867 : PrimeCertificate 65867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32933]) (by decide +kernel)
def pv65867 : PrimeValue := ⟨65867, pr65867⟩
private theorem pr65881 : PrimeCertificate 65881 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv65881 : PrimeValue := ⟨65881, pr65881⟩
private theorem pr65899 : PrimeCertificate 65899 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv523]) (by decide +kernel)
def pv65899 : PrimeValue := ⟨65899, pr65899⟩
private theorem pr65921 : PrimeCertificate 65921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv103]) (by decide +kernel)
def pv65921 : PrimeValue := ⟨65921, pr65921⟩
private theorem pr65927 : PrimeCertificate 65927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv17,pv277]) (by decide +kernel)
def pv65927 : PrimeValue := ⟨65927, pr65927⟩
private theorem pr65929 : PrimeCertificate 65929 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv41,pv67]) (by decide +kernel)
def pv65929 : PrimeValue := ⟨65929, pr65929⟩
private theorem pr65951 : PrimeCertificate 65951 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv1319]) (by decide +kernel)
def pv65951 : PrimeValue := ⟨65951, pr65951⟩
private theorem pr65957 : PrimeCertificate 65957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1499]) (by decide +kernel)
def pv65957 : PrimeValue := ⟨65957, pr65957⟩
private theorem pr65963 : PrimeCertificate 65963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv43,pv59]) (by decide +kernel)
def pv65963 : PrimeValue := ⟨65963, pr65963⟩
private theorem pr65981 : PrimeCertificate 65981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3299]) (by decide +kernel)
def pv65981 : PrimeValue := ⟨65981, pr65981⟩
private theorem pr65983 : PrimeCertificate 65983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1571]) (by decide +kernel)
def pv65983 : PrimeValue := ⟨65983, pr65983⟩
private theorem pr65993 : PrimeCertificate 65993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv113]) (by decide +kernel)
def pv65993 : PrimeValue := ⟨65993, pr65993⟩
private theorem pr66029 : PrimeCertificate 66029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv971]) (by decide +kernel)
def pv66029 : PrimeValue := ⟨66029, pr66029⟩
private theorem pr66037 : PrimeCertificate 66037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5503]) (by decide +kernel)
def pv66037 : PrimeValue := ⟨66037, pr66037⟩
private theorem pr66041 : PrimeCertificate 66041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv127]) (by decide +kernel)
def pv66041 : PrimeValue := ⟨66041, pr66041⟩
private theorem pr66047 : PrimeCertificate 66047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv33023]) (by decide +kernel)
def pv66047 : PrimeValue := ⟨66047, pr66047⟩
private theorem pr66067 : PrimeCertificate 66067 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv13]) (by decide +kernel)
def pv66067 : PrimeValue := ⟨66067, pr66067⟩
private theorem pr66071 : PrimeCertificate 66071 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv6607]) (by decide +kernel)
def pv66071 : PrimeValue := ⟨66071, pr66071⟩
private theorem pr66083 : PrimeCertificate 66083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv37,pv47]) (by decide +kernel)
def pv66083 : PrimeValue := ⟨66083, pr66083⟩
private theorem pr66089 : PrimeCertificate 66089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv751]) (by decide +kernel)
def pv66089 : PrimeValue := ⟨66089, pr66089⟩
private theorem pr66103 : PrimeCertificate 66103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv479]) (by decide +kernel)
def pv66103 : PrimeValue := ⟨66103, pr66103⟩
private theorem pr66107 : PrimeCertificate 66107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33053]) (by decide +kernel)
def pv66107 : PrimeValue := ⟨66107, pr66107⟩
private theorem pr66109 : PrimeCertificate 66109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv787]) (by decide +kernel)
def pv66109 : PrimeValue := ⟨66109, pr66109⟩
private theorem pr66137 : PrimeCertificate 66137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1181]) (by decide +kernel)
def pv66137 : PrimeValue := ⟨66137, pr66137⟩
private theorem pr66161 : PrimeCertificate 66161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv827]) (by decide +kernel)
def pv66161 : PrimeValue := ⟨66161, pr66161⟩
private theorem pr66169 : PrimeCertificate 66169 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv919]) (by decide +kernel)
def pv66169 : PrimeValue := ⟨66169, pr66169⟩
private theorem pr66173 : PrimeCertificate 66173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv233]) (by decide +kernel)
def pv66173 : PrimeValue := ⟨66173, pr66173⟩
private theorem pr66179 : PrimeCertificate 66179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv163]) (by decide +kernel)
def pv66179 : PrimeValue := ⟨66179, pr66179⟩
private theorem pr66191 : PrimeCertificate 66191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv6619]) (by decide +kernel)
def pv66191 : PrimeValue := ⟨66191, pr66191⟩
private theorem pr66221 : PrimeCertificate 66221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv43]) (by decide +kernel)
def pv66221 : PrimeValue := ⟨66221, pr66221⟩
private theorem pr66239 : PrimeCertificate 66239 :=
  certifyPrime (q := pv17) (ls := [pv2,pv33119]) (by decide +kernel)
def pv66239 : PrimeValue := ⟨66239, pr66239⟩
private theorem pr66271 : PrimeCertificate 66271 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv66271 : PrimeValue := ⟨66271, pr66271⟩
private theorem pr66293 : PrimeCertificate 66293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv16573]) (by decide +kernel)
def pv66293 : PrimeValue := ⟨66293, pr66293⟩
private theorem pr66301 : PrimeCertificate 66301 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv13,pv17]) (by decide +kernel)
def pv66301 : PrimeValue := ⟨66301, pr66301⟩
private theorem pr66337 : PrimeCertificate 66337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv691]) (by decide +kernel)
def pv66337 : PrimeValue := ⟨66337, pr66337⟩
private theorem pr66343 : PrimeCertificate 66343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11057]) (by decide +kernel)
def pv66343 : PrimeValue := ⟨66343, pr66343⟩
private theorem pr66347 : PrimeCertificate 66347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv677]) (by decide +kernel)
def pv66347 : PrimeValue := ⟨66347, pr66347⟩
private theorem pr66359 : PrimeCertificate 66359 :=
  certifyPrime (q := pv13) (ls := [pv2,pv33179]) (by decide +kernel)
def pv66359 : PrimeValue := ⟨66359, pr66359⟩
private theorem pr66361 : PrimeCertificate 66361 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv79]) (by decide +kernel)
def pv66361 : PrimeValue := ⟨66361, pr66361⟩
private theorem pr66373 : PrimeCertificate 66373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5531]) (by decide +kernel)
def pv66373 : PrimeValue := ⟨66373, pr66373⟩
private theorem pr66377 : PrimeCertificate 66377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8297]) (by decide +kernel)
def pv66377 : PrimeValue := ⟨66377, pr66377⟩
private theorem pr66383 : PrimeCertificate 66383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv33191]) (by decide +kernel)
def pv66383 : PrimeValue := ⟨66383, pr66383⟩
private theorem pr66403 : PrimeCertificate 66403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv31]) (by decide +kernel)
def pv66403 : PrimeValue := ⟨66403, pr66403⟩
private theorem pr66413 : PrimeCertificate 66413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv16603]) (by decide +kernel)
def pv66413 : PrimeValue := ⟨66413, pr66413⟩
private theorem pr66431 : PrimeCertificate 66431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv73]) (by decide +kernel)
def pv66431 : PrimeValue := ⟨66431, pr66431⟩
private theorem pr66449 : PrimeCertificate 66449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4153]) (by decide +kernel)
def pv66449 : PrimeValue := ⟨66449, pr66449⟩
private theorem pr66457 : PrimeCertificate 66457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv71]) (by decide +kernel)
def pv66457 : PrimeValue := ⟨66457, pr66457⟩
private theorem pr66463 : PrimeCertificate 66463 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv19,pv53]) (by decide +kernel)
def pv66463 : PrimeValue := ⟨66463, pr66463⟩
private theorem pr66467 : PrimeCertificate 66467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167,pv199]) (by decide +kernel)
def pv66467 : PrimeValue := ⟨66467, pr66467⟩
private theorem pr66491 : PrimeCertificate 66491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61,pv109]) (by decide +kernel)
def pv66491 : PrimeValue := ⟨66491, pr66491⟩
private theorem pr66499 : PrimeCertificate 66499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11083]) (by decide +kernel)
def pv66499 : PrimeValue := ⟨66499, pr66499⟩
private theorem pr66509 : PrimeCertificate 66509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1279]) (by decide +kernel)
def pv66509 : PrimeValue := ⟨66509, pr66509⟩
private theorem pr66523 : PrimeCertificate 66523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11087]) (by decide +kernel)
def pv66523 : PrimeValue := ⟨66523, pr66523⟩
private theorem pr66529 : PrimeCertificate 66529 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv66529 : PrimeValue := ⟨66529, pr66529⟩
private theorem pr66533 : PrimeCertificate 66533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv16633]) (by decide +kernel)
def pv66533 : PrimeValue := ⟨66533, pr66533⟩
private theorem pr66541 : PrimeCertificate 66541 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1109]) (by decide +kernel)
def pv66541 : PrimeValue := ⟨66541, pr66541⟩
private theorem pr66553 : PrimeCertificate 66553 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv47,pv59]) (by decide +kernel)
def pv66553 : PrimeValue := ⟨66553, pr66553⟩
private theorem pr66569 : PrimeCertificate 66569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv157]) (by decide +kernel)
def pv66569 : PrimeValue := ⟨66569, pr66569⟩
private theorem pr66571 : PrimeCertificate 66571 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv317]) (by decide +kernel)
def pv66571 : PrimeValue := ⟨66571, pr66571⟩
private theorem pr66587 : PrimeCertificate 66587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv197]) (by decide +kernel)
def pv66587 : PrimeValue := ⟨66587, pr66587⟩
private theorem pr66593 : PrimeCertificate 66593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2081]) (by decide +kernel)
def pv66593 : PrimeValue := ⟨66593, pr66593⟩
private theorem pr66601 : PrimeCertificate 66601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv66601 : PrimeValue := ⟨66601, pr66601⟩
private theorem pr66617 : PrimeCertificate 66617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv757]) (by decide +kernel)
def pv66617 : PrimeValue := ⟨66617, pr66617⟩
private theorem pr66629 : PrimeCertificate 66629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv16657]) (by decide +kernel)
def pv66629 : PrimeValue := ⟨66629, pr66629⟩
private theorem pr66643 : PrimeCertificate 66643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv383]) (by decide +kernel)
def pv66643 : PrimeValue := ⟨66643, pr66643⟩
private theorem pr66653 : PrimeCertificate 66653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv877]) (by decide +kernel)
def pv66653 : PrimeValue := ⟨66653, pr66653⟩
private theorem pr66683 : PrimeCertificate 66683 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv433]) (by decide +kernel)
def pv66683 : PrimeValue := ⟨66683, pr66683⟩
private theorem pr66697 : PrimeCertificate 66697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv397]) (by decide +kernel)
def pv66697 : PrimeValue := ⟨66697, pr66697⟩
private theorem pr66701 : PrimeCertificate 66701 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv29]) (by decide +kernel)
def pv66701 : PrimeValue := ⟨66701, pr66701⟩
private theorem pr66713 : PrimeCertificate 66713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv269]) (by decide +kernel)
def pv66713 : PrimeValue := ⟨66713, pr66713⟩
private theorem pr66721 : PrimeCertificate 66721 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv139]) (by decide +kernel)
def pv66721 : PrimeValue := ⟨66721, pr66721⟩
private theorem pr66733 : PrimeCertificate 66733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv83]) (by decide +kernel)
def pv66733 : PrimeValue := ⟨66733, pr66733⟩
private theorem pr66739 : PrimeCertificate 66739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv227]) (by decide +kernel)
def pv66739 : PrimeValue := ⟨66739, pr66739⟩
private theorem pr66749 : PrimeCertificate 66749 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv37,pv41]) (by decide +kernel)
def pv66749 : PrimeValue := ⟨66749, pr66749⟩
private theorem pr66751 : PrimeCertificate 66751 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv89]) (by decide +kernel)
def pv66751 : PrimeValue := ⟨66751, pr66751⟩
private theorem pr66763 : PrimeCertificate 66763 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3709]) (by decide +kernel)
def pv66763 : PrimeValue := ⟨66763, pr66763⟩
private theorem pr66791 : PrimeCertificate 66791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv6679]) (by decide +kernel)
def pv66791 : PrimeValue := ⟨66791, pr66791⟩
private theorem pr66797 : PrimeCertificate 66797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv16699]) (by decide +kernel)
def pv66797 : PrimeValue := ⟨66797, pr66797⟩
private theorem pr66809 : PrimeCertificate 66809 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv1193]) (by decide +kernel)
def pv66809 : PrimeValue := ⟨66809, pr66809⟩
private theorem pr66821 : PrimeCertificate 66821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv257]) (by decide +kernel)
def pv66821 : PrimeValue := ⟨66821, pr66821⟩
private theorem pr66841 : PrimeCertificate 66841 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv557]) (by decide +kernel)
def pv66841 : PrimeValue := ⟨66841, pr66841⟩
private theorem pr66851 : PrimeCertificate 66851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv191]) (by decide +kernel)
def pv66851 : PrimeValue := ⟨66851, pr66851⟩
private theorem pr66853 : PrimeCertificate 66853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv619]) (by decide +kernel)
def pv66853 : PrimeValue := ⟨66853, pr66853⟩
private theorem pr66863 : PrimeCertificate 66863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv101,pv331]) (by decide +kernel)
def pv66863 : PrimeValue := ⟨66863, pr66863⟩
private theorem pr66877 : PrimeCertificate 66877 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5573]) (by decide +kernel)
def pv66877 : PrimeValue := ⟨66877, pr66877⟩
private theorem pr66883 : PrimeCertificate 66883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv157]) (by decide +kernel)
def pv66883 : PrimeValue := ⟨66883, pr66883⟩
private theorem pr66889 : PrimeCertificate 66889 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv929]) (by decide +kernel)
def pv66889 : PrimeValue := ⟨66889, pr66889⟩
private theorem pr66919 : PrimeCertificate 66919 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv19,pv587]) (by decide +kernel)
def pv66919 : PrimeValue := ⟨66919, pr66919⟩
private theorem pr66923 : PrimeCertificate 66923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33461]) (by decide +kernel)
def pv66923 : PrimeValue := ⟨66923, pr66923⟩
private theorem pr66931 : PrimeCertificate 66931 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv97]) (by decide +kernel)
def pv66931 : PrimeValue := ⟨66931, pr66931⟩
private theorem pr66943 : PrimeCertificate 66943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3719]) (by decide +kernel)
def pv66943 : PrimeValue := ⟨66943, pr66943⟩
private theorem pr66947 : PrimeCertificate 66947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv179]) (by decide +kernel)
def pv66947 : PrimeValue := ⟨66947, pr66947⟩
private theorem pr66949 : PrimeCertificate 66949 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv797]) (by decide +kernel)
def pv66949 : PrimeValue := ⟨66949, pr66949⟩
private theorem pr66959 : PrimeCertificate 66959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv33479]) (by decide +kernel)
def pv66959 : PrimeValue := ⟨66959, pr66959⟩
private theorem pr66973 : PrimeCertificate 66973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5581]) (by decide +kernel)
def pv66973 : PrimeValue := ⟨66973, pr66973⟩
private theorem pr66977 : PrimeCertificate 66977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv23]) (by decide +kernel)
def pv66977 : PrimeValue := ⟨66977, pr66977⟩
private theorem pr67003 : PrimeCertificate 67003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv859]) (by decide +kernel)
def pv67003 : PrimeValue := ⟨67003, pr67003⟩
private theorem pr67021 : PrimeCertificate 67021 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1117]) (by decide +kernel)
def pv67021 : PrimeValue := ⟨67021, pr67021⟩
private theorem pr67033 : PrimeCertificate 67033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv67033 : PrimeValue := ⟨67033, pr67033⟩
private theorem pr67043 : PrimeCertificate 67043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33521]) (by decide +kernel)
def pv67043 : PrimeValue := ⟨67043, pr67043⟩
private theorem pr67049 : PrimeCertificate 67049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv29]) (by decide +kernel)
def pv67049 : PrimeValue := ⟨67049, pr67049⟩
private theorem pr67057 : PrimeCertificate 67057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv127]) (by decide +kernel)
def pv67057 : PrimeValue := ⟨67057, pr67057⟩
private theorem pr67061 : PrimeCertificate 67061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv479]) (by decide +kernel)
def pv67061 : PrimeValue := ⟨67061, pr67061⟩
private theorem pr67073 : PrimeCertificate 67073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv131]) (by decide +kernel)
def pv67073 : PrimeValue := ⟨67073, pr67073⟩
private theorem pr67079 : PrimeCertificate 67079 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv3049]) (by decide +kernel)
def pv67079 : PrimeValue := ⟨67079, pr67079⟩
private theorem pr67103 : PrimeCertificate 67103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv4793]) (by decide +kernel)
def pv67103 : PrimeValue := ⟨67103, pr67103⟩
private theorem pr67121 : PrimeCertificate 67121 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv839]) (by decide +kernel)
def pv67121 : PrimeValue := ⟨67121, pr67121⟩
private theorem pr67129 : PrimeCertificate 67129 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2797]) (by decide +kernel)
def pv67129 : PrimeValue := ⟨67129, pr67129⟩
private theorem pr67139 : PrimeCertificate 67139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33569]) (by decide +kernel)
def pv67139 : PrimeValue := ⟨67139, pr67139⟩
private theorem pr67141 : PrimeCertificate 67141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv373]) (by decide +kernel)
def pv67141 : PrimeValue := ⟨67141, pr67141⟩
private theorem pr67153 : PrimeCertificate 67153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1399]) (by decide +kernel)
def pv67153 : PrimeValue := ⟨67153, pr67153⟩
private theorem pr67157 : PrimeCertificate 67157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv163]) (by decide +kernel)
def pv67157 : PrimeValue := ⟨67157, pr67157⟩
private theorem pr67169 : PrimeCertificate 67169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2099]) (by decide +kernel)
def pv67169 : PrimeValue := ⟨67169, pr67169⟩
private theorem pr67181 : PrimeCertificate 67181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3359]) (by decide +kernel)
def pv67181 : PrimeValue := ⟨67181, pr67181⟩
private theorem pr67187 : PrimeCertificate 67187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4799]) (by decide +kernel)
def pv67187 : PrimeValue := ⟨67187, pr67187⟩
private theorem pr67189 : PrimeCertificate 67189 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv509]) (by decide +kernel)
def pv67189 : PrimeValue := ⟨67189, pr67189⟩
private theorem pr67211 : PrimeCertificate 67211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv47]) (by decide +kernel)
def pv67211 : PrimeValue := ⟨67211, pr67211⟩
private theorem pr67213 : PrimeCertificate 67213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1867]) (by decide +kernel)
def pv67213 : PrimeValue := ⟨67213, pr67213⟩
private theorem pr67217 : PrimeCertificate 67217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4201]) (by decide +kernel)
def pv67217 : PrimeValue := ⟨67217, pr67217⟩
private theorem pr67219 : PrimeCertificate 67219 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv659]) (by decide +kernel)
def pv67219 : PrimeValue := ⟨67219, pr67219⟩
private theorem pr67231 : PrimeCertificate 67231 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv83]) (by decide +kernel)
def pv67231 : PrimeValue := ⟨67231, pr67231⟩
private theorem pr67247 : PrimeCertificate 67247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv33623]) (by decide +kernel)
def pv67247 : PrimeValue := ⟨67247, pr67247⟩
private theorem pr67261 : PrimeCertificate 67261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv59]) (by decide +kernel)
def pv67261 : PrimeValue := ⟨67261, pr67261⟩
private theorem pr67271 : PrimeCertificate 67271 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv7,pv31]) (by decide +kernel)
def pv67271 : PrimeValue := ⟨67271, pr67271⟩
private theorem pr67273 : PrimeCertificate 67273 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2803]) (by decide +kernel)
def pv67273 : PrimeValue := ⟨67273, pr67273⟩
private theorem pr67289 : PrimeCertificate 67289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv647]) (by decide +kernel)
def pv67289 : PrimeValue := ⟨67289, pr67289⟩
private theorem pr67307 : PrimeCertificate 67307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv461]) (by decide +kernel)
def pv67307 : PrimeValue := ⟨67307, pr67307⟩
private theorem pr67339 : PrimeCertificate 67339 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv43]) (by decide +kernel)
def pv67339 : PrimeValue := ⟨67339, pr67339⟩
private theorem pr67343 : PrimeCertificate 67343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv3061]) (by decide +kernel)
def pv67343 : PrimeValue := ⟨67343, pr67343⟩
private theorem pr67349 : PrimeCertificate 67349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv149]) (by decide +kernel)
def pv67349 : PrimeValue := ⟨67349, pr67349⟩
private theorem pr67391 : PrimeCertificate 67391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv23,pv293]) (by decide +kernel)
def pv67391 : PrimeValue := ⟨67391, pr67391⟩
private theorem pr67399 : PrimeCertificate 67399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv239]) (by decide +kernel)
def pv67399 : PrimeValue := ⟨67399, pr67399⟩
private theorem pr67409 : PrimeCertificate 67409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv383]) (by decide +kernel)
def pv67409 : PrimeValue := ⟨67409, pr67409⟩
private theorem pr67411 : PrimeCertificate 67411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv107]) (by decide +kernel)
def pv67411 : PrimeValue := ⟨67411, pr67411⟩
private theorem pr67421 : PrimeCertificate 67421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3371]) (by decide +kernel)
def pv67421 : PrimeValue := ⟨67421, pr67421⟩
private theorem pr67427 : PrimeCertificate 67427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33713]) (by decide +kernel)
def pv67427 : PrimeValue := ⟨67427, pr67427⟩
private theorem pr67429 : PrimeCertificate 67429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1873]) (by decide +kernel)
def pv67429 : PrimeValue := ⟨67429, pr67429⟩
private theorem pr67433 : PrimeCertificate 67433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8429]) (by decide +kernel)
def pv67433 : PrimeValue := ⟨67433, pr67433⟩
private theorem pr67447 : PrimeCertificate 67447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1249]) (by decide +kernel)
def pv67447 : PrimeValue := ⟨67447, pr67447⟩
private theorem pr67453 : PrimeCertificate 67453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv73]) (by decide +kernel)
def pv67453 : PrimeValue := ⟨67453, pr67453⟩
private theorem pr67477 : PrimeCertificate 67477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5623]) (by decide +kernel)
def pv67477 : PrimeValue := ⟨67477, pr67477⟩
private theorem pr67481 : PrimeCertificate 67481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv241]) (by decide +kernel)
def pv67481 : PrimeValue := ⟨67481, pr67481⟩
private theorem pr67489 : PrimeCertificate 67489 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv19,pv37]) (by decide +kernel)
def pv67489 : PrimeValue := ⟨67489, pr67489⟩
private theorem pr67493 : PrimeCertificate 67493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv359]) (by decide +kernel)
def pv67493 : PrimeValue := ⟨67493, pr67493⟩
private theorem pr67499 : PrimeCertificate 67499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33749]) (by decide +kernel)
def pv67499 : PrimeValue := ⟨67499, pr67499⟩
private theorem pr67511 : PrimeCertificate 67511 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv43,pv157]) (by decide +kernel)
def pv67511 : PrimeValue := ⟨67511, pr67511⟩
private theorem pr67523 : PrimeCertificate 67523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv53]) (by decide +kernel)
def pv67523 : PrimeValue := ⟨67523, pr67523⟩
private theorem pr67531 : PrimeCertificate 67531 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv2251]) (by decide +kernel)
def pv67531 : PrimeValue := ⟨67531, pr67531⟩
private theorem pr67537 : PrimeCertificate 67537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv67537 : PrimeValue := ⟨67537, pr67537⟩
private theorem pr67547 : PrimeCertificate 67547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33773]) (by decide +kernel)
def pv67547 : PrimeValue := ⟨67547, pr67547⟩
private theorem pr67559 : PrimeCertificate 67559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv1987]) (by decide +kernel)
def pv67559 : PrimeValue := ⟨67559, pr67559⟩
private theorem pr67567 : PrimeCertificate 67567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11261]) (by decide +kernel)
def pv67567 : PrimeValue := ⟨67567, pr67567⟩
private theorem pr67577 : PrimeCertificate 67577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8447]) (by decide +kernel)
def pv67577 : PrimeValue := ⟨67577, pr67577⟩
private theorem pr67579 : PrimeCertificate 67579 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv1609]) (by decide +kernel)
def pv67579 : PrimeValue := ⟨67579, pr67579⟩
private theorem pr67589 : PrimeCertificate 67589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv277]) (by decide +kernel)
def pv67589 : PrimeValue := ⟨67589, pr67589⟩
private theorem pr67601 : PrimeCertificate 67601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv67601 : PrimeValue := ⟨67601, pr67601⟩
private theorem pr67607 : PrimeCertificate 67607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv439]) (by decide +kernel)
def pv67607 : PrimeValue := ⟨67607, pr67607⟩
private theorem pr67619 : PrimeCertificate 67619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33809]) (by decide +kernel)
def pv67619 : PrimeValue := ⟨67619, pr67619⟩
private theorem pr67631 : PrimeCertificate 67631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv6763]) (by decide +kernel)
def pv67631 : PrimeValue := ⟨67631, pr67631⟩
private theorem pr67651 : PrimeCertificate 67651 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv41]) (by decide +kernel)
def pv67651 : PrimeValue := ⟨67651, pr67651⟩
private theorem pr67679 : PrimeCertificate 67679 :=
  certifyPrime (q := pv19) (ls := [pv2,pv13,pv19,pv137]) (by decide +kernel)
def pv67679 : PrimeValue := ⟨67679, pr67679⟩
private theorem pr67699 : PrimeCertificate 67699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3761]) (by decide +kernel)
def pv67699 : PrimeValue := ⟨67699, pr67699⟩
private theorem pr67709 : PrimeCertificate 67709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv16927]) (by decide +kernel)
def pv67709 : PrimeValue := ⟨67709, pr67709⟩
private theorem pr67723 : PrimeCertificate 67723 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11287]) (by decide +kernel)
def pv67723 : PrimeValue := ⟨67723, pr67723⟩
private theorem pr67733 : PrimeCertificate 67733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv41,pv59]) (by decide +kernel)
def pv67733 : PrimeValue := ⟨67733, pr67733⟩
private theorem pr67741 : PrimeCertificate 67741 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv1129]) (by decide +kernel)
def pv67741 : PrimeValue := ⟨67741, pr67741⟩
private theorem pr67751 : PrimeCertificate 67751 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv271]) (by decide +kernel)
def pv67751 : PrimeValue := ⟨67751, pr67751⟩
private theorem pr67757 : PrimeCertificate 67757 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1303]) (by decide +kernel)
def pv67757 : PrimeValue := ⟨67757, pr67757⟩
private theorem pr67759 : PrimeCertificate 67759 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv23,pv491]) (by decide +kernel)
def pv67759 : PrimeValue := ⟨67759, pr67759⟩
private theorem pr67763 : PrimeCertificate 67763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1993]) (by decide +kernel)
def pv67763 : PrimeValue := ⟨67763, pr67763⟩
private theorem pr67777 : PrimeCertificate 67777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv353]) (by decide +kernel)
def pv67777 : PrimeValue := ⟨67777, pr67777⟩
private theorem pr67783 : PrimeCertificate 67783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv79]) (by decide +kernel)
def pv67783 : PrimeValue := ⟨67783, pr67783⟩
private theorem pr67789 : PrimeCertificate 67789 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv269]) (by decide +kernel)
def pv67789 : PrimeValue := ⟨67789, pr67789⟩
private theorem pr67801 : PrimeCertificate 67801 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv113]) (by decide +kernel)
def pv67801 : PrimeValue := ⟨67801, pr67801⟩
private theorem pr67807 : PrimeCertificate 67807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3767]) (by decide +kernel)
def pv67807 : PrimeValue := ⟨67807, pr67807⟩
private theorem pr67819 : PrimeCertificate 67819 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv89,pv127]) (by decide +kernel)
def pv67819 : PrimeValue := ⟨67819, pr67819⟩
private theorem pr67829 : PrimeCertificate 67829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv547]) (by decide +kernel)
def pv67829 : PrimeValue := ⟨67829, pr67829⟩
private theorem pr67843 : PrimeCertificate 67843 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv3769]) (by decide +kernel)
def pv67843 : PrimeValue := ⟨67843, pr67843⟩
private theorem pr67853 : PrimeCertificate 67853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv16963]) (by decide +kernel)
def pv67853 : PrimeValue := ⟨67853, pr67853⟩
private theorem pr67867 : PrimeCertificate 67867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11311]) (by decide +kernel)
def pv67867 : PrimeValue := ⟨67867, pr67867⟩
private theorem pr67883 : PrimeCertificate 67883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33941]) (by decide +kernel)
def pv67883 : PrimeValue := ⟨67883, pr67883⟩
private theorem pr67891 : PrimeCertificate 67891 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv31,pv73]) (by decide +kernel)
def pv67891 : PrimeValue := ⟨67891, pr67891⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
