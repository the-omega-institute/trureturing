/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table117
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table117.pv564643
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table082
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table083

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr564643 : PrimeCertificate 564643 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv127]) (by decide +kernel)
def pv564643 : PrimeValue := ⟨564643, pr564643⟩
private theorem pr564653 : PrimeCertificate 564653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv41,pv313]) (by decide +kernel)
def pv564653 : PrimeValue := ⟨564653, pr564653⟩
private theorem pr564671 : PrimeCertificate 564671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv56467]) (by decide +kernel)
def pv564671 : PrimeValue := ⟨564671, pr564671⟩
private theorem pr564679 : PrimeCertificate 564679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10457]) (by decide +kernel)
def pv564679 : PrimeValue := ⟨564679, pr564679⟩
private theorem pr564713 : PrimeCertificate 564713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv70589]) (by decide +kernel)
def pv564713 : PrimeValue := ⟨564713, pr564713⟩
private theorem pr564761 : PrimeCertificate 564761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv2017]) (by decide +kernel)
def pv564761 : PrimeValue := ⟨564761, pr564761⟩
private theorem pr564779 : PrimeCertificate 564779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv282389]) (by decide +kernel)
def pv564779 : PrimeValue := ⟨564779, pr564779⟩
private theorem pr564827 : PrimeCertificate 564827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv282413]) (by decide +kernel)
def pv564827 : PrimeValue := ⟨564827, pr564827⟩
private theorem pr564881 : PrimeCertificate 564881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv307]) (by decide +kernel)
def pv564881 : PrimeValue := ⟨564881, pr564881⟩
private theorem pr564923 : PrimeCertificate 564923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv282461]) (by decide +kernel)
def pv564923 : PrimeValue := ⟨564923, pr564923⟩
private theorem pr565039 : PrimeCertificate 565039 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv31391]) (by decide +kernel)
def pv565039 : PrimeValue := ⟨565039, pr565039⟩
private theorem pr565049 : PrimeCertificate 565049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv6421]) (by decide +kernel)
def pv565049 : PrimeValue := ⟨565049, pr565049⟩
private theorem pr565057 : PrimeCertificate 565057 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv109]) (by decide +kernel)
def pv565057 : PrimeValue := ⟨565057, pr565057⟩
private theorem pr565127 : PrimeCertificate 565127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv282563]) (by decide +kernel)
def pv565127 : PrimeValue := ⟨565127, pr565127⟩
private theorem pr565163 : PrimeCertificate 565163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv21737]) (by decide +kernel)
def pv565163 : PrimeValue := ⟨565163, pr565163⟩
private theorem pr565183 : PrimeCertificate 565183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv1847]) (by decide +kernel)
def pv565183 : PrimeValue := ⟨565183, pr565183⟩
private theorem pr565273 : PrimeCertificate 565273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2617]) (by decide +kernel)
def pv565273 : PrimeValue := ⟨565273, pr565273⟩
private theorem pr565289 : PrimeCertificate 565289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv3719]) (by decide +kernel)
def pv565289 : PrimeValue := ⟨565289, pr565289⟩
private theorem pr565303 : PrimeCertificate 565303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv1327]) (by decide +kernel)
def pv565303 : PrimeValue := ⟨565303, pr565303⟩
private theorem pr565319 : PrimeCertificate 565319 :=
  certifyPrime (q := pv23) (ls := [pv2,pv13,pv17,pv1279]) (by decide +kernel)
def pv565319 : PrimeValue := ⟨565319, pr565319⟩
private theorem pr565387 : PrimeCertificate 565387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv23,pv241]) (by decide +kernel)
def pv565387 : PrimeValue := ⟨565387, pr565387⟩
private theorem pr565391 : PrimeCertificate 565391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv41,pv197]) (by decide +kernel)
def pv565391 : PrimeValue := ⟨565391, pr565391⟩
private theorem pr565393 : PrimeCertificate 565393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11779]) (by decide +kernel)
def pv565393 : PrimeValue := ⟨565393, pr565393⟩
private theorem pr565427 : PrimeCertificate 565427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv282713]) (by decide +kernel)
def pv565427 : PrimeValue := ⟨565427, pr565427⟩
private theorem pr565429 : PrimeCertificate 565429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47119]) (by decide +kernel)
def pv565429 : PrimeValue := ⟨565429, pr565429⟩
private theorem pr565469 : PrimeCertificate 565469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv373,pv379]) (by decide +kernel)
def pv565469 : PrimeValue := ⟨565469, pr565469⟩
private theorem pr565483 : PrimeCertificate 565483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79,pv1193]) (by decide +kernel)
def pv565483 : PrimeValue := ⟨565483, pr565483⟩
private theorem pr565511 : PrimeCertificate 565511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv53,pv97]) (by decide +kernel)
def pv565511 : PrimeValue := ⟨565511, pr565511⟩
private theorem pr565567 : PrimeCertificate 565567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv94261]) (by decide +kernel)
def pv565567 : PrimeValue := ⟨565567, pr565567⟩
private theorem pr565571 : PrimeCertificate 565571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv2459]) (by decide +kernel)
def pv565571 : PrimeValue := ⟨565571, pr565571⟩
private theorem pr565597 : PrimeCertificate 565597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5237]) (by decide +kernel)
def pv565597 : PrimeValue := ⟨565597, pr565597⟩
private theorem pr565603 : PrimeCertificate 565603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv107,pv881]) (by decide +kernel)
def pv565603 : PrimeValue := ⟨565603, pr565603⟩
private theorem pr565661 : PrimeCertificate 565661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv28283]) (by decide +kernel)
def pv565661 : PrimeValue := ⟨565661, pr565661⟩
private theorem pr565771 : PrimeCertificate 565771 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv18859]) (by decide +kernel)
def pv565771 : PrimeValue := ⟨565771, pr565771⟩
private theorem pr565813 : PrimeCertificate 565813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv565813 : PrimeValue := ⟨565813, pr565813⟩
private theorem pr565891 : PrimeCertificate 565891 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv1451]) (by decide +kernel)
def pv565891 : PrimeValue := ⟨565891, pr565891⟩
private theorem pr565919 : PrimeCertificate 565919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv282959]) (by decide +kernel)
def pv565919 : PrimeValue := ⟨565919, pr565919⟩
private theorem pr565979 : PrimeCertificate 565979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv40427]) (by decide +kernel)
def pv565979 : PrimeValue := ⟨565979, pr565979⟩
private theorem pr565997 : PrimeCertificate 565997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv141499]) (by decide +kernel)
def pv565997 : PrimeValue := ⟨565997, pr565997⟩
private theorem pr566023 : PrimeCertificate 566023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv3253]) (by decide +kernel)
def pv566023 : PrimeValue := ⟨566023, pr566023⟩
private theorem pr566077 : PrimeCertificate 566077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv293]) (by decide +kernel)
def pv566077 : PrimeValue := ⟨566077, pr566077⟩
private theorem pr566089 : PrimeCertificate 566089 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv103,pv229]) (by decide +kernel)
def pv566089 : PrimeValue := ⟨566089, pr566089⟩
private theorem pr566107 : PrimeCertificate 566107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv94351]) (by decide +kernel)
def pv566107 : PrimeValue := ⟨566107, pr566107⟩
private theorem pr566173 : PrimeCertificate 566173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15727]) (by decide +kernel)
def pv566173 : PrimeValue := ⟨566173, pr566173⟩
private theorem pr566201 : PrimeCertificate 566201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv149]) (by decide +kernel)
def pv566201 : PrimeValue := ⟨566201, pr566201⟩
private theorem pr566227 : PrimeCertificate 566227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv379]) (by decide +kernel)
def pv566227 : PrimeValue := ⟨566227, pr566227⟩
private theorem pr566231 : PrimeCertificate 566231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv8089]) (by decide +kernel)
def pv566231 : PrimeValue := ⟨566231, pr566231⟩
private theorem pr566323 : PrimeCertificate 566323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv2551]) (by decide +kernel)
def pv566323 : PrimeValue := ⟨566323, pr566323⟩
private theorem pr566393 : PrimeCertificate 566393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv853]) (by decide +kernel)
def pv566393 : PrimeValue := ⟨566393, pr566393⟩
private theorem pr566437 : PrimeCertificate 566437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv3631]) (by decide +kernel)
def pv566437 : PrimeValue := ⟨566437, pr566437⟩
private theorem pr566441 : PrimeCertificate 566441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv17]) (by decide +kernel)
def pv566441 : PrimeValue := ⟨566441, pr566441⟩
private theorem pr566453 : PrimeCertificate 566453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv141613]) (by decide +kernel)
def pv566453 : PrimeValue := ⟨566453, pr566453⟩
private theorem pr566521 : PrimeCertificate 566521 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv4721]) (by decide +kernel)
def pv566521 : PrimeValue := ⟨566521, pr566521⟩
private theorem pr566539 : PrimeCertificate 566539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv47]) (by decide +kernel)
def pv566539 : PrimeValue := ⟨566539, pr566539⟩
private theorem pr566543 : PrimeCertificate 566543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv19,pv877]) (by decide +kernel)
def pv566543 : PrimeValue := ⟨566543, pr566543⟩
private theorem pr566551 : PrimeCertificate 566551 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1259]) (by decide +kernel)
def pv566551 : PrimeValue := ⟨566551, pr566551⟩
private theorem pr566557 : PrimeCertificate 566557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv1523]) (by decide +kernel)
def pv566557 : PrimeValue := ⟨566557, pr566557⟩
private theorem pr566617 : PrimeCertificate 566617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23609]) (by decide +kernel)
def pv566617 : PrimeValue := ⟨566617, pr566617⟩
private theorem pr566653 : PrimeCertificate 566653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47221]) (by decide +kernel)
def pv566653 : PrimeValue := ⟨566653, pr566653⟩
private theorem pr566659 : PrimeCertificate 566659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31481]) (by decide +kernel)
def pv566659 : PrimeValue := ⟨566659, pr566659⟩
private theorem pr566677 : PrimeCertificate 566677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv53]) (by decide +kernel)
def pv566677 : PrimeValue := ⟨566677, pr566677⟩
private theorem pr566681 : PrimeCertificate 566681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv457]) (by decide +kernel)
def pv566681 : PrimeValue := ⟨566681, pr566681⟩
private theorem pr566693 : PrimeCertificate 566693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv37,pv547]) (by decide +kernel)
def pv566693 : PrimeValue := ⟨566693, pr566693⟩
private theorem pr566701 : PrimeCertificate 566701 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv1889]) (by decide +kernel)
def pv566701 : PrimeValue := ⟨566701, pr566701⟩
private theorem pr566707 : PrimeCertificate 566707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv103,pv131]) (by decide +kernel)
def pv566707 : PrimeValue := ⟨566707, pr566707⟩
private theorem pr566717 : PrimeCertificate 566717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv141679]) (by decide +kernel)
def pv566717 : PrimeValue := ⟨566717, pr566717⟩
private theorem pr566759 : PrimeCertificate 566759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv251,pv1129]) (by decide +kernel)
def pv566759 : PrimeValue := ⟨566759, pr566759⟩
private theorem pr566767 : PrimeCertificate 566767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv37]) (by decide +kernel)
def pv566767 : PrimeValue := ⟨566767, pr566767⟩
private theorem pr566821 : PrimeCertificate 566821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv47,pv67]) (by decide +kernel)
def pv566821 : PrimeValue := ⟨566821, pr566821⟩
private theorem pr566851 : PrimeCertificate 566851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3779]) (by decide +kernel)
def pv566851 : PrimeValue := ⟨566851, pr566851⟩
private theorem pr566911 : PrimeCertificate 566911 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv6299]) (by decide +kernel)
def pv566911 : PrimeValue := ⟨566911, pr566911⟩
private theorem pr567013 : PrimeCertificate 567013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47251]) (by decide +kernel)
def pv567013 : PrimeValue := ⟨567013, pr567013⟩
private theorem pr567053 : PrimeCertificate 567053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv31,pv269]) (by decide +kernel)
def pv567053 : PrimeValue := ⟨567053, pr567053⟩
private theorem pr567067 : PrimeCertificate 567067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv3259]) (by decide +kernel)
def pv567067 : PrimeValue := ⟨567067, pr567067⟩
private theorem pr567097 : PrimeCertificate 567097 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23629]) (by decide +kernel)
def pv567097 : PrimeValue := ⟨567097, pr567097⟩
private theorem pr567121 : PrimeCertificate 567121 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv17,pv139]) (by decide +kernel)
def pv567121 : PrimeValue := ⟨567121, pr567121⟩
private theorem pr567277 : PrimeCertificate 567277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv1153]) (by decide +kernel)
def pv567277 : PrimeValue := ⟨567277, pr567277⟩
private theorem pr567319 : PrimeCertificate 567319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv4111]) (by decide +kernel)
def pv567319 : PrimeValue := ⟨567319, pr567319⟩
private theorem pr567487 : PrimeCertificate 567487 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31,pv113]) (by decide +kernel)
def pv567487 : PrimeValue := ⟨567487, pr567487⟩
private theorem pr567493 : PrimeCertificate 567493 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv131]) (by decide +kernel)
def pv567493 : PrimeValue := ⟨567493, pr567493⟩
private theorem pr567527 : PrimeCertificate 567527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv283763]) (by decide +kernel)
def pv567527 : PrimeValue := ⟨567527, pr567527⟩
private theorem pr567529 : PrimeCertificate 567529 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv17,pv107]) (by decide +kernel)
def pv567529 : PrimeValue := ⟨567529, pr567529⟩
private theorem pr567667 : PrimeCertificate 567667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv47,pv61]) (by decide +kernel)
def pv567667 : PrimeValue := ⟨567667, pr567667⟩
private theorem pr567673 : PrimeCertificate 567673 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv31,pv109]) (by decide +kernel)
def pv567673 : PrimeValue := ⟨567673, pr567673⟩
private theorem pr567719 : PrimeCertificate 567719 :=
  certifyPrime (q := pv11) (ls := [pv2,pv283859]) (by decide +kernel)
def pv567719 : PrimeValue := ⟨567719, pr567719⟩
private theorem pr567793 : PrimeCertificate 567793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3943]) (by decide +kernel)
def pv567793 : PrimeValue := ⟨567793, pr567793⟩
private theorem pr567857 : PrimeCertificate 567857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv35491]) (by decide +kernel)
def pv567857 : PrimeValue := ⟨567857, pr567857⟩
private theorem pr567937 : PrimeCertificate 567937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv29]) (by decide +kernel)
def pv567937 : PrimeValue := ⟨567937, pr567937⟩
private theorem pr567943 : PrimeCertificate 567943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv103,pv919]) (by decide +kernel)
def pv567943 : PrimeValue := ⟨567943, pr567943⟩
private theorem pr567947 : PrimeCertificate 567947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv199,pv1427]) (by decide +kernel)
def pv567947 : PrimeValue := ⟨567947, pr567947⟩
private theorem pr567991 : PrimeCertificate 567991 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv6311]) (by decide +kernel)
def pv567991 : PrimeValue := ⟨567991, pr567991⟩
private theorem pr567997 : PrimeCertificate 567997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv331]) (by decide +kernel)
def pv567997 : PrimeValue := ⟨567997, pr567997⟩
private theorem pr568091 : PrimeCertificate 568091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv56809]) (by decide +kernel)
def pv568091 : PrimeValue := ⟨568091, pr568091⟩
private theorem pr568097 : PrimeCertificate 568097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv433]) (by decide +kernel)
def pv568097 : PrimeValue := ⟨568097, pr568097⟩
private theorem pr568133 : PrimeCertificate 568133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv821]) (by decide +kernel)
def pv568133 : PrimeValue := ⟨568133, pr568133⟩
private theorem pr568153 : PrimeCertificate 568153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv607]) (by decide +kernel)
def pv568153 : PrimeValue := ⟨568153, pr568153⟩
private theorem pr568163 : PrimeCertificate 568163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv40583]) (by decide +kernel)
def pv568163 : PrimeValue := ⟨568163, pr568163⟩
private theorem pr568189 : PrimeCertificate 568189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5261]) (by decide +kernel)
def pv568189 : PrimeValue := ⟨568189, pr568189⟩
private theorem pr568231 : PrimeCertificate 568231 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv31,pv47]) (by decide +kernel)
def pv568231 : PrimeValue := ⟨568231, pr568231⟩
private theorem pr568241 : PrimeCertificate 568241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7103]) (by decide +kernel)
def pv568241 : PrimeValue := ⟨568241, pr568241⟩
private theorem pr568289 : PrimeCertificate 568289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv43,pv59]) (by decide +kernel)
def pv568289 : PrimeValue := ⟨568289, pr568289⟩
private theorem pr568303 : PrimeCertificate 568303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1933]) (by decide +kernel)
def pv568303 : PrimeValue := ⟨568303, pr568303⟩
private theorem pr568349 : PrimeCertificate 568349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv12917]) (by decide +kernel)
def pv568349 : PrimeValue := ⟨568349, pr568349⟩
private theorem pr568367 : PrimeCertificate 568367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv14957]) (by decide +kernel)
def pv568367 : PrimeValue := ⟨568367, pr568367⟩
private theorem pr568387 : PrimeCertificate 568387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv347]) (by decide +kernel)
def pv568387 : PrimeValue := ⟨568387, pr568387⟩
private theorem pr568391 : PrimeCertificate 568391 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv113,pv503]) (by decide +kernel)
def pv568391 : PrimeValue := ⟨568391, pr568391⟩
private theorem pr568433 : PrimeCertificate 568433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv35527]) (by decide +kernel)
def pv568433 : PrimeValue := ⟨568433, pr568433⟩
private theorem pr568657 : PrimeCertificate 568657 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv359]) (by decide +kernel)
def pv568657 : PrimeValue := ⟨568657, pr568657⟩
private theorem pr568723 : PrimeCertificate 568723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv1231]) (by decide +kernel)
def pv568723 : PrimeValue := ⟨568723, pr568723⟩
private theorem pr568751 : PrimeCertificate 568751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv13]) (by decide +kernel)
def pv568751 : PrimeValue := ⟨568751, pr568751⟩
private theorem pr568831 : PrimeCertificate 568831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv67,pv283]) (by decide +kernel)
def pv568831 : PrimeValue := ⟨568831, pr568831⟩
private theorem pr568853 : PrimeCertificate 568853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv2003]) (by decide +kernel)
def pv568853 : PrimeValue := ⟨568853, pr568853⟩
private theorem pr568903 : PrimeCertificate 568903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53,pv1789]) (by decide +kernel)
def pv568903 : PrimeValue := ⟨568903, pr568903⟩
private theorem pr568963 : PrimeCertificate 568963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv433]) (by decide +kernel)
def pv568963 : PrimeValue := ⟨568963, pr568963⟩
private theorem pr568979 : PrimeCertificate 568979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv284489]) (by decide +kernel)
def pv568979 : PrimeValue := ⟨568979, pr568979⟩
private theorem pr569057 : PrimeCertificate 569057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17783]) (by decide +kernel)
def pv569057 : PrimeValue := ⟨569057, pr569057⟩
private theorem pr569071 : PrimeCertificate 569071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv6323]) (by decide +kernel)
def pv569071 : PrimeValue := ⟨569071, pr569071⟩
private theorem pr569081 : PrimeCertificate 569081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv41,pv347]) (by decide +kernel)
def pv569081 : PrimeValue := ⟨569081, pr569081⟩
private theorem pr569197 : PrimeCertificate 569197 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv97,pv163]) (by decide +kernel)
def pv569197 : PrimeValue := ⟨569197, pr569197⟩
private theorem pr569213 : PrimeCertificate 569213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv701]) (by decide +kernel)
def pv569213 : PrimeValue := ⟨569213, pr569213⟩
private theorem pr569263 : PrimeCertificate 569263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv5581]) (by decide +kernel)
def pv569263 : PrimeValue := ⟨569263, pr569263⟩
private theorem pr569417 : PrimeCertificate 569417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv109,pv653]) (by decide +kernel)
def pv569417 : PrimeValue := ⟨569417, pr569417⟩
private theorem pr569447 : PrimeCertificate 569447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv284723]) (by decide +kernel)
def pv569447 : PrimeValue := ⟨569447, pr569447⟩
private theorem pr569461 : PrimeCertificate 569461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv9491]) (by decide +kernel)
def pv569461 : PrimeValue := ⟨569461, pr569461⟩
private theorem pr569479 : PrimeCertificate 569479 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv149]) (by decide +kernel)
def pv569479 : PrimeValue := ⟨569479, pr569479⟩
private theorem pr569533 : PrimeCertificate 569533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv1531]) (by decide +kernel)
def pv569533 : PrimeValue := ⟨569533, pr569533⟩
private theorem pr569573 : PrimeCertificate 569573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv41,pv151]) (by decide +kernel)
def pv569573 : PrimeValue := ⟨569573, pr569573⟩
private theorem pr569581 : PrimeCertificate 569581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv863]) (by decide +kernel)
def pv569581 : PrimeValue := ⟨569581, pr569581⟩
private theorem pr569617 : PrimeCertificate 569617 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11867]) (by decide +kernel)
def pv569617 : PrimeValue := ⟨569617, pr569617⟩
private theorem pr569659 : PrimeCertificate 569659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv263]) (by decide +kernel)
def pv569659 : PrimeValue := ⟨569659, pr569659⟩
private theorem pr569711 : PrimeCertificate 569711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv23,pv2477]) (by decide +kernel)
def pv569711 : PrimeValue := ⟨569711, pr569711⟩
private theorem pr569713 : PrimeCertificate 569713 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv11,pv13,pv83]) (by decide +kernel)
def pv569713 : PrimeValue := ⟨569713, pr569713⟩
private theorem pr569759 : PrimeCertificate 569759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv40697]) (by decide +kernel)
def pv569759 : PrimeValue := ⟨569759, pr569759⟩
private theorem pr569771 : PrimeCertificate 569771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv227,pv251]) (by decide +kernel)
def pv569771 : PrimeValue := ⟨569771, pr569771⟩
private theorem pr569797 : PrimeCertificate 569797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103,pv461]) (by decide +kernel)
def pv569797 : PrimeValue := ⟨569797, pr569797⟩
private theorem pr569843 : PrimeCertificate 569843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv31,pv101]) (by decide +kernel)
def pv569843 : PrimeValue := ⟨569843, pr569843⟩
private theorem pr569861 : PrimeCertificate 569861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv28493]) (by decide +kernel)
def pv569861 : PrimeValue := ⟨569861, pr569861⟩
private theorem pr569903 : PrimeCertificate 569903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv67,pv4253]) (by decide +kernel)
def pv569903 : PrimeValue := ⟨569903, pr569903⟩
private theorem pr569983 : PrimeCertificate 569983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv41,pv331]) (by decide +kernel)
def pv569983 : PrimeValue := ⟨569983, pr569983⟩
private theorem pr570013 : PrimeCertificate 570013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47501]) (by decide +kernel)
def pv570013 : PrimeValue := ⟨570013, pr570013⟩
private theorem pr570071 : PrimeCertificate 570071 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv109,pv523]) (by decide +kernel)
def pv570071 : PrimeValue := ⟨570071, pr570071⟩
private theorem pr570083 : PrimeCertificate 570083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv9829]) (by decide +kernel)
def pv570083 : PrimeValue := ⟨570083, pr570083⟩
private theorem pr570131 : PrimeCertificate 570131 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv71,pv73]) (by decide +kernel)
def pv570131 : PrimeValue := ⟨570131, pr570131⟩
private theorem pr570173 : PrimeCertificate 570173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv142543]) (by decide +kernel)
def pv570173 : PrimeValue := ⟨570173, pr570173⟩
private theorem pr570191 : PrimeCertificate 570191 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv19,pv3001]) (by decide +kernel)
def pv570191 : PrimeValue := ⟨570191, pr570191⟩
private theorem pr570217 : PrimeCertificate 570217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1033]) (by decide +kernel)
def pv570217 : PrimeValue := ⟨570217, pr570217⟩
private theorem pr570233 : PrimeCertificate 570233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv5483]) (by decide +kernel)
def pv570233 : PrimeValue := ⟨570233, pr570233⟩
private theorem pr570373 : PrimeCertificate 570373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv29,pv149]) (by decide +kernel)
def pv570373 : PrimeValue := ⟨570373, pr570373⟩
private theorem pr570491 : PrimeCertificate 570491 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv89,pv641]) (by decide +kernel)
def pv570491 : PrimeValue := ⟨570491, pr570491⟩
private theorem pr570569 : PrimeCertificate 570569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv977]) (by decide +kernel)
def pv570569 : PrimeValue := ⟨570569, pr570569⟩
private theorem pr570587 : PrimeCertificate 570587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv9203]) (by decide +kernel)
def pv570587 : PrimeValue := ⟨570587, pr570587⟩
private theorem pr570613 : PrimeCertificate 570613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv6793]) (by decide +kernel)
def pv570613 : PrimeValue := ⟨570613, pr570613⟩
private theorem pr570637 : PrimeCertificate 570637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv131]) (by decide +kernel)
def pv570637 : PrimeValue := ⟨570637, pr570637⟩
private theorem pr570643 : PrimeCertificate 570643 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv95107]) (by decide +kernel)
def pv570643 : PrimeValue := ⟨570643, pr570643⟩
private theorem pr570649 : PrimeCertificate 570649 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv31,pv59]) (by decide +kernel)
def pv570649 : PrimeValue := ⟨570649, pr570649⟩
private theorem pr570659 : PrimeCertificate 570659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv25939]) (by decide +kernel)
def pv570659 : PrimeValue := ⟨570659, pr570659⟩
private theorem pr570677 : PrimeCertificate 570677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv6203]) (by decide +kernel)
def pv570677 : PrimeValue := ⟨570677, pr570677⟩
private theorem pr570737 : PrimeCertificate 570737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv35671]) (by decide +kernel)
def pv570737 : PrimeValue := ⟨570737, pr570737⟩
private theorem pr570743 : PrimeCertificate 570743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv137,pv2083]) (by decide +kernel)
def pv570743 : PrimeValue := ⟨570743, pr570743⟩
private theorem pr570841 : PrimeCertificate 570841 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv67,pv71]) (by decide +kernel)
def pv570841 : PrimeValue := ⟨570841, pr570841⟩
private theorem pr570967 : PrimeCertificate 570967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv41,pv211]) (by decide +kernel)
def pv570967 : PrimeValue := ⟨570967, pr570967⟩
private theorem pr571001 : PrimeCertificate 571001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv571]) (by decide +kernel)
def pv571001 : PrimeValue := ⟨571001, pr571001⟩
private theorem pr571019 : PrimeCertificate 571019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv40787]) (by decide +kernel)
def pv571019 : PrimeValue := ⟨571019, pr571019⟩
private theorem pr571069 : PrimeCertificate 571069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv547]) (by decide +kernel)
def pv571069 : PrimeValue := ⟨571069, pr571069⟩
private theorem pr571093 : PrimeCertificate 571093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47591]) (by decide +kernel)
def pv571093 : PrimeValue := ⟨571093, pr571093⟩
private theorem pr571111 : PrimeCertificate 571111 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv19037]) (by decide +kernel)
def pv571111 : PrimeValue := ⟨571111, pr571111⟩
private theorem pr571147 : PrimeCertificate 571147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv95191]) (by decide +kernel)
def pv571147 : PrimeValue := ⟨571147, pr571147⟩
private theorem pr571211 : PrimeCertificate 571211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv239]) (by decide +kernel)
def pv571211 : PrimeValue := ⟨571211, pr571211⟩
private theorem pr571223 : PrimeCertificate 571223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv285611]) (by decide +kernel)
def pv571223 : PrimeValue := ⟨571223, pr571223⟩
private theorem pr571267 : PrimeCertificate 571267 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv149]) (by decide +kernel)
def pv571267 : PrimeValue := ⟨571267, pr571267⟩
private theorem pr571303 : PrimeCertificate 571303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv1867]) (by decide +kernel)
def pv571303 : PrimeValue := ⟨571303, pr571303⟩
private theorem pr571339 : PrimeCertificate 571339 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31741]) (by decide +kernel)
def pv571339 : PrimeValue := ⟨571339, pr571339⟩
private theorem pr571369 : PrimeCertificate 571369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv19,pv179]) (by decide +kernel)
def pv571369 : PrimeValue := ⟨571369, pr571369⟩
private theorem pr571381 : PrimeCertificate 571381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv89,pv107]) (by decide +kernel)
def pv571381 : PrimeValue := ⟨571381, pr571381⟩
private theorem pr571399 : PrimeCertificate 571399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv95233]) (by decide +kernel)
def pv571399 : PrimeValue := ⟨571399, pr571399⟩
private theorem pr571433 : PrimeCertificate 571433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71429]) (by decide +kernel)
def pv571433 : PrimeValue := ⟨571433, pr571433⟩
private theorem pr571453 : PrimeCertificate 571453 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv6803]) (by decide +kernel)
def pv571453 : PrimeValue := ⟨571453, pr571453⟩
private theorem pr571583 : PrimeCertificate 571583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv25981]) (by decide +kernel)
def pv571583 : PrimeValue := ⟨571583, pr571583⟩
private theorem pr571603 : PrimeCertificate 571603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv95267]) (by decide +kernel)
def pv571603 : PrimeValue := ⟨571603, pr571603⟩
private theorem pr571633 : PrimeCertificate 571633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11909]) (by decide +kernel)
def pv571633 : PrimeValue := ⟨571633, pr571633⟩
private theorem pr571657 : PrimeCertificate 571657 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv23819]) (by decide +kernel)
def pv571657 : PrimeValue := ⟨571657, pr571657⟩
private theorem pr571673 : PrimeCertificate 571673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv3761]) (by decide +kernel)
def pv571673 : PrimeValue := ⟨571673, pr571673⟩
private theorem pr571699 : PrimeCertificate 571699 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv3529]) (by decide +kernel)
def pv571699 : PrimeValue := ⟨571699, pr571699⟩
private theorem pr571717 : PrimeCertificate 571717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15881]) (by decide +kernel)
def pv571717 : PrimeValue := ⟨571717, pr571717⟩
private theorem pr571777 : PrimeCertificate 571777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1489]) (by decide +kernel)
def pv571777 : PrimeValue := ⟨571777, pr571777⟩
private theorem pr571783 : PrimeCertificate 571783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv233,pv409]) (by decide +kernel)
def pv571783 : PrimeValue := ⟨571783, pr571783⟩
private theorem pr571853 : PrimeCertificate 571853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv142963]) (by decide +kernel)
def pv571853 : PrimeValue := ⟨571853, pr571853⟩
private theorem pr571867 : PrimeCertificate 571867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv95311]) (by decide +kernel)
def pv571867 : PrimeValue := ⟨571867, pr571867⟩
private theorem pr571903 : PrimeCertificate 571903 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv95317]) (by decide +kernel)
def pv571903 : PrimeValue := ⟨571903, pr571903⟩
private theorem pr572051 : PrimeCertificate 572051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv673]) (by decide +kernel)
def pv572051 : PrimeValue := ⟨572051, pr572051⟩
private theorem pr572053 : PrimeCertificate 572053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv19,pv193]) (by decide +kernel)
def pv572053 : PrimeValue := ⟨572053, pr572053⟩
private theorem pr572069 : PrimeCertificate 572069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv20431]) (by decide +kernel)
def pv572069 : PrimeValue := ⟨572069, pr572069⟩
private theorem pr572087 : PrimeCertificate 572087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv286043]) (by decide +kernel)
def pv572087 : PrimeValue := ⟨572087, pr572087⟩
private theorem pr572161 : PrimeCertificate 572161 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv149]) (by decide +kernel)
def pv572161 : PrimeValue := ⟨572161, pr572161⟩
private theorem pr572303 : PrimeCertificate 572303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv4691]) (by decide +kernel)
def pv572303 : PrimeValue := ⟨572303, pr572303⟩
private theorem pr572321 : PrimeCertificate 572321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv73]) (by decide +kernel)
def pv572321 : PrimeValue := ⟨572321, pr572321⟩
private theorem pr572333 : PrimeCertificate 572333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv6221]) (by decide +kernel)
def pv572333 : PrimeValue := ⟨572333, pr572333⟩
private theorem pr572549 : PrimeCertificate 572549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv143137]) (by decide +kernel)
def pv572549 : PrimeValue := ⟨572549, pr572549⟩
private theorem pr572567 : PrimeCertificate 572567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv353,pv811]) (by decide +kernel)
def pv572567 : PrimeValue := ⟨572567, pr572567⟩
private theorem pr572597 : PrimeCertificate 572597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv257,pv557]) (by decide +kernel)
def pv572597 : PrimeValue := ⟨572597, pr572597⟩
private theorem pr572629 : PrimeCertificate 572629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv401]) (by decide +kernel)
def pv572629 : PrimeValue := ⟨572629, pr572629⟩
private theorem pr572633 : PrimeCertificate 572633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv2309]) (by decide +kernel)
def pv572633 : PrimeValue := ⟨572633, pr572633⟩
private theorem pr572651 : PrimeCertificate 572651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv881]) (by decide +kernel)
def pv572651 : PrimeValue := ⟨572651, pr572651⟩
private theorem pr572659 : PrimeCertificate 572659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv95443]) (by decide +kernel)
def pv572659 : PrimeValue := ⟨572659, pr572659⟩
private theorem pr572707 : PrimeCertificate 572707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31817]) (by decide +kernel)
def pv572707 : PrimeValue := ⟨572707, pr572707⟩
private theorem pr572711 : PrimeCertificate 572711 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv57271]) (by decide +kernel)
def pv572711 : PrimeValue := ⟨572711, pr572711⟩
private theorem pr572807 : PrimeCertificate 572807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv22031]) (by decide +kernel)
def pv572807 : PrimeValue := ⟨572807, pr572807⟩
private theorem pr572941 : PrimeCertificate 572941 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1061]) (by decide +kernel)
def pv572941 : PrimeValue := ⟨572941, pr572941⟩
private theorem pr573047 : PrimeCertificate 573047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv181,pv1583]) (by decide +kernel)
def pv573047 : PrimeValue := ⟨573047, pr573047⟩
private theorem pr573161 : PrimeCertificate 573161 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv23,pv89]) (by decide +kernel)
def pv573161 : PrimeValue := ⟨573161, pr573161⟩
private theorem pr573163 : PrimeCertificate 573163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv95527]) (by decide +kernel)
def pv573163 : PrimeValue := ⟨573163, pr573163⟩
private theorem pr573253 : PrimeCertificate 573253 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv31,pv67]) (by decide +kernel)
def pv573253 : PrimeValue := ⟨573253, pr573253⟩
private theorem pr573277 : PrimeCertificate 573277 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv43,pv101]) (by decide +kernel)
def pv573277 : PrimeValue := ⟨573277, pr573277⟩
private theorem pr573289 : PrimeCertificate 573289 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23887]) (by decide +kernel)
def pv573289 : PrimeValue := ⟨573289, pr573289⟩
private theorem pr573409 : PrimeCertificate 573409 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv181]) (by decide +kernel)
def pv573409 : PrimeValue := ⟨573409, pr573409⟩
private theorem pr573457 : PrimeCertificate 573457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv919]) (by decide +kernel)
def pv573457 : PrimeValue := ⟨573457, pr573457⟩
private theorem pr573473 : PrimeCertificate 573473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17921]) (by decide +kernel)
def pv573473 : PrimeValue := ⟨573473, pr573473⟩
private theorem pr573673 : PrimeCertificate 573673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv41,pv53]) (by decide +kernel)
def pv573673 : PrimeValue := ⟨573673, pr573673⟩
private theorem pr573737 : PrimeCertificate 573737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv2473]) (by decide +kernel)
def pv573737 : PrimeValue := ⟨573737, pr573737⟩
private theorem pr573761 : PrimeCertificate 573761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv163]) (by decide +kernel)
def pv573761 : PrimeValue := ⟨573761, pr573761⟩
private theorem pr573763 : PrimeCertificate 573763 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv719]) (by decide +kernel)
def pv573763 : PrimeValue := ⟨573763, pr573763⟩
private theorem pr573791 : PrimeCertificate 573791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv1171]) (by decide +kernel)
def pv573791 : PrimeValue := ⟨573791, pr573791⟩
private theorem pr573817 : PrimeCertificate 573817 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv23909]) (by decide +kernel)
def pv573817 : PrimeValue := ⟨573817, pr573817⟩
private theorem pr573847 : PrimeCertificate 573847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv1051]) (by decide +kernel)
def pv573847 : PrimeValue := ⟨573847, pr573847⟩
private theorem pr573863 : PrimeCertificate 573863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv83,pv3457]) (by decide +kernel)
def pv573863 : PrimeValue := ⟨573863, pr573863⟩
private theorem pr573871 : PrimeCertificate 573871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv37,pv47]) (by decide +kernel)
def pv573871 : PrimeValue := ⟨573871, pr573871⟩
private theorem pr573883 : PrimeCertificate 573883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv947]) (by decide +kernel)
def pv573883 : PrimeValue := ⟨573883, pr573883⟩
private theorem pr573953 : PrimeCertificate 573953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv59]) (by decide +kernel)
def pv573953 : PrimeValue := ⟨573953, pr573953⟩
private theorem pr573967 : PrimeCertificate 573967 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1181]) (by decide +kernel)
def pv573967 : PrimeValue := ⟨573967, pr573967⟩
private theorem pr573977 : PrimeCertificate 573977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv5519]) (by decide +kernel)
def pv573977 : PrimeValue := ⟨573977, pr573977⟩
private theorem pr574051 : PrimeCertificate 574051 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv43,pv89]) (by decide +kernel)
def pv574051 : PrimeValue := ⟨574051, pr574051⟩
private theorem pr574109 : PrimeCertificate 574109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv143527]) (by decide +kernel)
def pv574109 : PrimeValue := ⟨574109, pr574109⟩
private theorem pr574163 : PrimeCertificate 574163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv2683]) (by decide +kernel)
def pv574163 : PrimeValue := ⟨574163, pr574163⟩
private theorem pr574169 : PrimeCertificate 574169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv10253]) (by decide +kernel)
def pv574169 : PrimeValue := ⟨574169, pr574169⟩
private theorem pr574183 : PrimeCertificate 574183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv574183 : PrimeValue := ⟨574183, pr574183⟩
private theorem pr574261 : PrimeCertificate 574261 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv17,pv563]) (by decide +kernel)
def pv574261 : PrimeValue := ⟨574261, pr574261⟩
private theorem pr574367 : PrimeCertificate 574367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv22091]) (by decide +kernel)
def pv574367 : PrimeValue := ⟨574367, pr574367⟩
private theorem pr574373 : PrimeCertificate 574373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv143593]) (by decide +kernel)
def pv574373 : PrimeValue := ⟨574373, pr574373⟩
private theorem pr574393 : PrimeCertificate 574393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv263]) (by decide +kernel)
def pv574393 : PrimeValue := ⟨574393, pr574393⟩
private theorem pr574423 : PrimeCertificate 574423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv95737]) (by decide +kernel)
def pv574423 : PrimeValue := ⟨574423, pr574423⟩
private theorem pr574429 : PrimeCertificate 574429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47869]) (by decide +kernel)
def pv574429 : PrimeValue := ⟨574429, pr574429⟩
private theorem pr574433 : PrimeCertificate 574433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv619]) (by decide +kernel)
def pv574433 : PrimeValue := ⟨574433, pr574433⟩
private theorem pr574439 : PrimeCertificate 574439 :=
  certifyPrime (q := pv13) (ls := [pv2,pv287219]) (by decide +kernel)
def pv574439 : PrimeValue := ⟨574439, pr574439⟩
private theorem pr574477 : PrimeCertificate 574477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv977]) (by decide +kernel)
def pv574477 : PrimeValue := ⟨574477, pr574477⟩
private theorem pr574489 : PrimeCertificate 574489 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv79,pv101]) (by decide +kernel)
def pv574489 : PrimeValue := ⟨574489, pr574489⟩
private theorem pr574493 : PrimeCertificate 574493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv41,pv113]) (by decide +kernel)
def pv574493 : PrimeValue := ⟨574493, pr574493⟩
private theorem pr574507 : PrimeCertificate 574507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10639]) (by decide +kernel)
def pv574507 : PrimeValue := ⟨574507, pr574507⟩
private theorem pr574529 : PrimeCertificate 574529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv191]) (by decide +kernel)
def pv574529 : PrimeValue := ⟨574529, pr574529⟩
private theorem pr574597 : PrimeCertificate 574597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1451]) (by decide +kernel)
def pv574597 : PrimeValue := ⟨574597, pr574597⟩
private theorem pr574643 : PrimeCertificate 574643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv287321]) (by decide +kernel)
def pv574643 : PrimeValue := ⟨574643, pr574643⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
