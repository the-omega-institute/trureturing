/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table045
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table045.pv122561
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr122561 : PrimeCertificate 122561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv383]) (by decide +kernel)
def pv122561 : PrimeValue := ⟨122561, pr122561⟩
private theorem pr122579 : PrimeCertificate 122579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167,pv367]) (by decide +kernel)
def pv122579 : PrimeValue := ⟨122579, pr122579⟩
private theorem pr122597 : PrimeCertificate 122597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv30649]) (by decide +kernel)
def pv122597 : PrimeValue := ⟨122597, pr122597⟩
private theorem pr122599 : PrimeCertificate 122599 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv139]) (by decide +kernel)
def pv122599 : PrimeValue := ⟨122599, pr122599⟩
private theorem pr122609 : PrimeCertificate 122609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79,pv97]) (by decide +kernel)
def pv122609 : PrimeValue := ⟨122609, pr122609⟩
private theorem pr122611 : PrimeCertificate 122611 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv61,pv67]) (by decide +kernel)
def pv122611 : PrimeValue := ⟨122611, pr122611⟩
private theorem pr122651 : PrimeCertificate 122651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv223]) (by decide +kernel)
def pv122651 : PrimeValue := ⟨122651, pr122651⟩
private theorem pr122653 : PrimeCertificate 122653 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3407]) (by decide +kernel)
def pv122653 : PrimeValue := ⟨122653, pr122653⟩
private theorem pr122663 : PrimeCertificate 122663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61331]) (by decide +kernel)
def pv122663 : PrimeValue := ⟨122663, pr122663⟩
private theorem pr122693 : PrimeCertificate 122693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv829]) (by decide +kernel)
def pv122693 : PrimeValue := ⟨122693, pr122693⟩
private theorem pr122701 : PrimeCertificate 122701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv409]) (by decide +kernel)
def pv122701 : PrimeValue := ⟨122701, pr122701⟩
private theorem pr122719 : PrimeCertificate 122719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv113,pv181]) (by decide +kernel)
def pv122719 : PrimeValue := ⟨122719, pr122719⟩
private theorem pr122741 : PrimeCertificate 122741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv19]) (by decide +kernel)
def pv122741 : PrimeValue := ⟨122741, pr122741⟩
private theorem pr122743 : PrimeCertificate 122743 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv2273]) (by decide +kernel)
def pv122743 : PrimeValue := ⟨122743, pr122743⟩
private theorem pr122761 : PrimeCertificate 122761 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv31]) (by decide +kernel)
def pv122761 : PrimeValue := ⟨122761, pr122761⟩
private theorem pr122777 : PrimeCertificate 122777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv103,pv149]) (by decide +kernel)
def pv122777 : PrimeValue := ⟨122777, pr122777⟩
private theorem pr122789 : PrimeCertificate 122789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv30697]) (by decide +kernel)
def pv122789 : PrimeValue := ⟨122789, pr122789⟩
private theorem pr122819 : PrimeCertificate 122819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61409]) (by decide +kernel)
def pv122819 : PrimeValue := ⟨122819, pr122819⟩
private theorem pr122833 : PrimeCertificate 122833 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv853]) (by decide +kernel)
def pv122833 : PrimeValue := ⟨122833, pr122833⟩
private theorem pr122839 : PrimeCertificate 122839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv347]) (by decide +kernel)
def pv122839 : PrimeValue := ⟨122839, pr122839⟩
private theorem pr122849 : PrimeCertificate 122849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv349]) (by decide +kernel)
def pv122849 : PrimeValue := ⟨122849, pr122849⟩
private theorem pr122861 : PrimeCertificate 122861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6143]) (by decide +kernel)
def pv122861 : PrimeValue := ⟨122861, pr122861⟩
private theorem pr122867 : PrimeCertificate 122867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2671]) (by decide +kernel)
def pv122867 : PrimeValue := ⟨122867, pr122867⟩
private theorem pr122869 : PrimeCertificate 122869 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv3413]) (by decide +kernel)
def pv122869 : PrimeValue := ⟨122869, pr122869⟩
private theorem pr122887 : PrimeCertificate 122887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6827]) (by decide +kernel)
def pv122887 : PrimeValue := ⟨122887, pr122887⟩
private theorem pr122891 : PrimeCertificate 122891 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv12289]) (by decide +kernel)
def pv122891 : PrimeValue := ⟨122891, pr122891⟩
private theorem pr122921 : PrimeCertificate 122921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv439]) (by decide +kernel)
def pv122921 : PrimeValue := ⟨122921, pr122921⟩
private theorem pr122929 : PrimeCertificate 122929 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv13,pv197]) (by decide +kernel)
def pv122929 : PrimeValue := ⟨122929, pr122929⟩
private theorem pr122939 : PrimeCertificate 122939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61469]) (by decide +kernel)
def pv122939 : PrimeValue := ⟨122939, pr122939⟩
private theorem pr122953 : PrimeCertificate 122953 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv109]) (by decide +kernel)
def pv122953 : PrimeValue := ⟨122953, pr122953⟩
private theorem pr122957 : PrimeCertificate 122957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv521]) (by decide +kernel)
def pv122957 : PrimeValue := ⟨122957, pr122957⟩
private theorem pr123001 : PrimeCertificate 123001 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv123001 : PrimeValue := ⟨123001, pr123001⟩
private theorem pr123007 : PrimeCertificate 123007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv19,pv83]) (by decide +kernel)
def pv123007 : PrimeValue := ⟨123007, pr123007⟩
private theorem pr123031 : PrimeCertificate 123031 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv1367]) (by decide +kernel)
def pv123031 : PrimeValue := ⟨123031, pr123031⟩
private theorem pr123049 : PrimeCertificate 123049 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1709]) (by decide +kernel)
def pv123049 : PrimeValue := ⟨123049, pr123049⟩
private theorem pr123059 : PrimeCertificate 123059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv4733]) (by decide +kernel)
def pv123059 : PrimeValue := ⟨123059, pr123059⟩
private theorem pr123077 : PrimeCertificate 123077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1061]) (by decide +kernel)
def pv123077 : PrimeValue := ⟨123077, pr123077⟩
private theorem pr123083 : PrimeCertificate 123083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv41,pv79]) (by decide +kernel)
def pv123083 : PrimeValue := ⟨123083, pr123083⟩
private theorem pr123091 : PrimeCertificate 123091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv373]) (by decide +kernel)
def pv123091 : PrimeValue := ⟨123091, pr123091⟩
private theorem pr123113 : PrimeCertificate 123113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1399]) (by decide +kernel)
def pv123113 : PrimeValue := ⟨123113, pr123113⟩
private theorem pr123121 : PrimeCertificate 123121 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv123121 : PrimeValue := ⟨123121, pr123121⟩
private theorem pr123127 : PrimeCertificate 123127 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv20521]) (by decide +kernel)
def pv123127 : PrimeValue := ⟨123127, pr123127⟩
private theorem pr123143 : PrimeCertificate 123143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv2677]) (by decide +kernel)
def pv123143 : PrimeValue := ⟨123143, pr123143⟩
private theorem pr123169 : PrimeCertificate 123169 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1283]) (by decide +kernel)
def pv123169 : PrimeValue := ⟨123169, pr123169⟩
private theorem pr123191 : PrimeCertificate 123191 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv97,pv127]) (by decide +kernel)
def pv123191 : PrimeValue := ⟨123191, pr123191⟩
private theorem pr123203 : PrimeCertificate 123203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv229,pv269]) (by decide +kernel)
def pv123203 : PrimeValue := ⟨123203, pr123203⟩
private theorem pr123209 : PrimeCertificate 123209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv15401]) (by decide +kernel)
def pv123209 : PrimeValue := ⟨123209, pr123209⟩
private theorem pr123217 : PrimeCertificate 123217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv151]) (by decide +kernel)
def pv123217 : PrimeValue := ⟨123217, pr123217⟩
private theorem pr123229 : PrimeCertificate 123229 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv163]) (by decide +kernel)
def pv123229 : PrimeValue := ⟨123229, pr123229⟩
private theorem pr123259 : PrimeCertificate 123259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20543]) (by decide +kernel)
def pv123259 : PrimeValue := ⟨123259, pr123259⟩
private theorem pr123269 : PrimeCertificate 123269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv30817]) (by decide +kernel)
def pv123269 : PrimeValue := ⟨123269, pr123269⟩
private theorem pr123289 : PrimeCertificate 123289 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv467]) (by decide +kernel)
def pv123289 : PrimeValue := ⟨123289, pr123289⟩
private theorem pr123307 : PrimeCertificate 123307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20551]) (by decide +kernel)
def pv123307 : PrimeValue := ⟨123307, pr123307⟩
private theorem pr123311 : PrimeCertificate 123311 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv19,pv59]) (by decide +kernel)
def pv123311 : PrimeValue := ⟨123311, pr123311⟩
private theorem pr123323 : PrimeCertificate 123323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197,pv313]) (by decide +kernel)
def pv123323 : PrimeValue := ⟨123323, pr123323⟩
private theorem pr123341 : PrimeCertificate 123341 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv881]) (by decide +kernel)
def pv123341 : PrimeValue := ⟨123341, pr123341⟩
private theorem pr123377 : PrimeCertificate 123377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv701]) (by decide +kernel)
def pv123377 : PrimeValue := ⟨123377, pr123377⟩
private theorem pr123397 : PrimeCertificate 123397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv113]) (by decide +kernel)
def pv123397 : PrimeValue := ⟨123397, pr123397⟩
private theorem pr123401 : PrimeCertificate 123401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv617]) (by decide +kernel)
def pv123401 : PrimeValue := ⟨123401, pr123401⟩
private theorem pr123407 : PrimeCertificate 123407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61703]) (by decide +kernel)
def pv123407 : PrimeValue := ⟨123407, pr123407⟩
private theorem pr123419 : PrimeCertificate 123419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2683]) (by decide +kernel)
def pv123419 : PrimeValue := ⟨123419, pr123419⟩
private theorem pr123427 : PrimeCertificate 123427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6857]) (by decide +kernel)
def pv123427 : PrimeValue := ⟨123427, pr123427⟩
private theorem pr123433 : PrimeCertificate 123433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv139]) (by decide +kernel)
def pv123433 : PrimeValue := ⟨123433, pr123433⟩
private theorem pr123439 : PrimeCertificate 123439 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv2939]) (by decide +kernel)
def pv123439 : PrimeValue := ⟨123439, pr123439⟩
private theorem pr123449 : PrimeCertificate 123449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1187]) (by decide +kernel)
def pv123449 : PrimeValue := ⟨123449, pr123449⟩
private theorem pr123457 : PrimeCertificate 123457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv643]) (by decide +kernel)
def pv123457 : PrimeValue := ⟨123457, pr123457⟩
private theorem pr123479 : PrimeCertificate 123479 :=
  certifyPrime (q := pv11) (ls := [pv2,pv107,pv577]) (by decide +kernel)
def pv123479 : PrimeValue := ⟨123479, pr123479⟩
private theorem pr123491 : PrimeCertificate 123491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv233]) (by decide +kernel)
def pv123491 : PrimeValue := ⟨123491, pr123491⟩
private theorem pr123493 : PrimeCertificate 123493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv251]) (by decide +kernel)
def pv123493 : PrimeValue := ⟨123493, pr123493⟩
private theorem pr123499 : PrimeCertificate 123499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2287]) (by decide +kernel)
def pv123499 : PrimeValue := ⟨123499, pr123499⟩
private theorem pr123503 : PrimeCertificate 123503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61751]) (by decide +kernel)
def pv123503 : PrimeValue := ⟨123503, pr123503⟩
private theorem pr123517 : PrimeCertificate 123517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv73]) (by decide +kernel)
def pv123517 : PrimeValue := ⟨123517, pr123517⟩
private theorem pr123527 : PrimeCertificate 123527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv4751]) (by decide +kernel)
def pv123527 : PrimeValue := ⟨123527, pr123527⟩
private theorem pr123547 : PrimeCertificate 123547 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv349]) (by decide +kernel)
def pv123547 : PrimeValue := ⟨123547, pr123547⟩
private theorem pr123551 : PrimeCertificate 123551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv353]) (by decide +kernel)
def pv123551 : PrimeValue := ⟨123551, pr123551⟩
private theorem pr123553 : PrimeCertificate 123553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv123553 : PrimeValue := ⟨123553, pr123553⟩
private theorem pr123581 : PrimeCertificate 123581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv167]) (by decide +kernel)
def pv123581 : PrimeValue := ⟨123581, pr123581⟩
private theorem pr123583 : PrimeCertificate 123583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv479]) (by decide +kernel)
def pv123583 : PrimeValue := ⟨123583, pr123583⟩
private theorem pr123593 : PrimeCertificate 123593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv2207]) (by decide +kernel)
def pv123593 : PrimeValue := ⟨123593, pr123593⟩
private theorem pr123601 : PrimeCertificate 123601 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv103]) (by decide +kernel)
def pv123601 : PrimeValue := ⟨123601, pr123601⟩
private theorem pr123619 : PrimeCertificate 123619 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv1873]) (by decide +kernel)
def pv123619 : PrimeValue := ⟨123619, pr123619⟩
private theorem pr123631 : PrimeCertificate 123631 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv317]) (by decide +kernel)
def pv123631 : PrimeValue := ⟨123631, pr123631⟩
private theorem pr123661 : PrimeCertificate 123661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv229]) (by decide +kernel)
def pv123661 : PrimeValue := ⟨123661, pr123661⟩
private theorem pr123667 : PrimeCertificate 123667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20611]) (by decide +kernel)
def pv123667 : PrimeValue := ⟨123667, pr123667⟩
private theorem pr123677 : PrimeCertificate 123677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv631]) (by decide +kernel)
def pv123677 : PrimeValue := ⟨123677, pr123677⟩
private theorem pr123701 : PrimeCertificate 123701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1237]) (by decide +kernel)
def pv123701 : PrimeValue := ⟨123701, pr123701⟩
private theorem pr123707 : PrimeCertificate 123707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv5623]) (by decide +kernel)
def pv123707 : PrimeValue := ⟨123707, pr123707⟩
private theorem pr123719 : PrimeCertificate 123719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv8837]) (by decide +kernel)
def pv123719 : PrimeValue := ⟨123719, pr123719⟩
private theorem pr123727 : PrimeCertificate 123727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv1213]) (by decide +kernel)
def pv123727 : PrimeValue := ⟨123727, pr123727⟩
private theorem pr123731 : PrimeCertificate 123731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv12373]) (by decide +kernel)
def pv123731 : PrimeValue := ⟨123731, pr123731⟩
private theorem pr123733 : PrimeCertificate 123733 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7,pv491]) (by decide +kernel)
def pv123733 : PrimeValue := ⟨123733, pr123733⟩
private theorem pr123737 : PrimeCertificate 123737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv15467]) (by decide +kernel)
def pv123737 : PrimeValue := ⟨123737, pr123737⟩
private theorem pr123757 : PrimeCertificate 123757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10313]) (by decide +kernel)
def pv123757 : PrimeValue := ⟨123757, pr123757⟩
private theorem pr123787 : PrimeCertificate 123787 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv23]) (by decide +kernel)
def pv123787 : PrimeValue := ⟨123787, pr123787⟩
private theorem pr123791 : PrimeCertificate 123791 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv12379]) (by decide +kernel)
def pv123791 : PrimeValue := ⟨123791, pr123791⟩
private theorem pr123803 : PrimeCertificate 123803 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv37,pv239]) (by decide +kernel)
def pv123803 : PrimeValue := ⟨123803, pr123803⟩
private theorem pr123817 : PrimeCertificate 123817 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv11,pv67]) (by decide +kernel)
def pv123817 : PrimeValue := ⟨123817, pr123817⟩
private theorem pr123821 : PrimeCertificate 123821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv151]) (by decide +kernel)
def pv123821 : PrimeValue := ⟨123821, pr123821⟩
private theorem pr123829 : PrimeCertificate 123829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv607]) (by decide +kernel)
def pv123829 : PrimeValue := ⟨123829, pr123829⟩
private theorem pr123833 : PrimeCertificate 123833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv673]) (by decide +kernel)
def pv123833 : PrimeValue := ⟨123833, pr123833⟩
private theorem pr123853 : PrimeCertificate 123853 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv10321]) (by decide +kernel)
def pv123853 : PrimeValue := ⟨123853, pr123853⟩
private theorem pr123863 : PrimeCertificate 123863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv3643]) (by decide +kernel)
def pv123863 : PrimeValue := ⟨123863, pr123863⟩
private theorem pr123887 : PrimeCertificate 123887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv8849]) (by decide +kernel)
def pv123887 : PrimeValue := ⟨123887, pr123887⟩
private theorem pr123911 : PrimeCertificate 123911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv12391]) (by decide +kernel)
def pv123911 : PrimeValue := ⟨123911, pr123911⟩
private theorem pr123923 : PrimeCertificate 123923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61961]) (by decide +kernel)
def pv123923 : PrimeValue := ⟨123923, pr123923⟩
private theorem pr123931 : PrimeCertificate 123931 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv123931 : PrimeValue := ⟨123931, pr123931⟩
private theorem pr123941 : PrimeCertificate 123941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6197]) (by decide +kernel)
def pv123941 : PrimeValue := ⟨123941, pr123941⟩
private theorem pr123973 : PrimeCertificate 123973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10331]) (by decide +kernel)
def pv123973 : PrimeValue := ⟨123973, pr123973⟩
private theorem pr123979 : PrimeCertificate 123979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20663]) (by decide +kernel)
def pv123979 : PrimeValue := ⟨123979, pr123979⟩
private theorem pr123983 : PrimeCertificate 123983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61991]) (by decide +kernel)
def pv123983 : PrimeValue := ⟨123983, pr123983⟩
private theorem pr123989 : PrimeCertificate 123989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139,pv223]) (by decide +kernel)
def pv123989 : PrimeValue := ⟨123989, pr123989⟩
private theorem pr123997 : PrimeCertificate 123997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10333]) (by decide +kernel)
def pv123997 : PrimeValue := ⟨123997, pr123997⟩
private theorem pr124001 : PrimeCertificate 124001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31]) (by decide +kernel)
def pv124001 : PrimeValue := ⟨124001, pr124001⟩
private theorem pr124021 : PrimeCertificate 124021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv53]) (by decide +kernel)
def pv124021 : PrimeValue := ⟨124021, pr124021⟩
private theorem pr124067 : PrimeCertificate 124067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv41,pv89]) (by decide +kernel)
def pv124067 : PrimeValue := ⟨124067, pr124067⟩
private theorem pr124087 : PrimeCertificate 124087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv20681]) (by decide +kernel)
def pv124087 : PrimeValue := ⟨124087, pr124087⟩
private theorem pr124097 : PrimeCertificate 124097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv277]) (by decide +kernel)
def pv124097 : PrimeValue := ⟨124097, pr124097⟩
private theorem pr124121 : PrimeCertificate 124121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv107]) (by decide +kernel)
def pv124121 : PrimeValue := ⟨124121, pr124121⟩
private theorem pr124123 : PrimeCertificate 124123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137,pv151]) (by decide +kernel)
def pv124123 : PrimeValue := ⟨124123, pr124123⟩
private theorem pr124133 : PrimeCertificate 124133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31033]) (by decide +kernel)
def pv124133 : PrimeValue := ⟨124133, pr124133⟩
private theorem pr124139 : PrimeCertificate 124139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8867]) (by decide +kernel)
def pv124139 : PrimeValue := ⟨124139, pr124139⟩
private theorem pr124153 : PrimeCertificate 124153 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv7,pv739]) (by decide +kernel)
def pv124153 : PrimeValue := ⟨124153, pr124153⟩
private theorem pr124171 : PrimeCertificate 124171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4139]) (by decide +kernel)
def pv124171 : PrimeValue := ⟨124171, pr124171⟩
private theorem pr124183 : PrimeCertificate 124183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6899]) (by decide +kernel)
def pv124183 : PrimeValue := ⟨124183, pr124183⟩
private theorem pr124193 : PrimeCertificate 124193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3881]) (by decide +kernel)
def pv124193 : PrimeValue := ⟨124193, pr124193⟩
private theorem pr124213 : PrimeCertificate 124213 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv941]) (by decide +kernel)
def pv124213 : PrimeValue := ⟨124213, pr124213⟩
private theorem pr124231 : PrimeCertificate 124231 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv41,pv101]) (by decide +kernel)
def pv124231 : PrimeValue := ⟨124231, pr124231⟩
private theorem pr124247 : PrimeCertificate 124247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv37,pv73]) (by decide +kernel)
def pv124247 : PrimeValue := ⟨124247, pr124247⟩
private theorem pr124249 : PrimeCertificate 124249 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31,pv167]) (by decide +kernel)
def pv124249 : PrimeValue := ⟨124249, pr124249⟩
private theorem pr124277 : PrimeCertificate 124277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31069]) (by decide +kernel)
def pv124277 : PrimeValue := ⟨124277, pr124277⟩
private theorem pr124291 : PrimeCertificate 124291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1381]) (by decide +kernel)
def pv124291 : PrimeValue := ⟨124291, pr124291⟩
private theorem pr124309 : PrimeCertificate 124309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1151]) (by decide +kernel)
def pv124309 : PrimeValue := ⟨124309, pr124309⟩
private theorem pr124337 : PrimeCertificate 124337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv409]) (by decide +kernel)
def pv124337 : PrimeValue := ⟨124337, pr124337⟩
private theorem pr124339 : PrimeCertificate 124339 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv23,pv53]) (by decide +kernel)
def pv124339 : PrimeValue := ⟨124339, pr124339⟩
private theorem pr124349 : PrimeCertificate 124349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4441]) (by decide +kernel)
def pv124349 : PrimeValue := ⟨124349, pr124349⟩
private theorem pr124351 : PrimeCertificate 124351 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv829]) (by decide +kernel)
def pv124351 : PrimeValue := ⟨124351, pr124351⟩
private theorem pr124363 : PrimeCertificate 124363 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv47]) (by decide +kernel)
def pv124363 : PrimeValue := ⟨124363, pr124363⟩
private theorem pr124367 : PrimeCertificate 124367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv5653]) (by decide +kernel)
def pv124367 : PrimeValue := ⟨124367, pr124367⟩
private theorem pr124427 : PrimeCertificate 124427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv62213]) (by decide +kernel)
def pv124427 : PrimeValue := ⟨124427, pr124427⟩
private theorem pr124429 : PrimeCertificate 124429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10369]) (by decide +kernel)
def pv124429 : PrimeValue := ⟨124429, pr124429⟩
private theorem pr124433 : PrimeCertificate 124433 :=
  certifyPrime (q := pv17) (ls := [pv2,pv7,pv11,pv101]) (by decide +kernel)
def pv124433 : PrimeValue := ⟨124433, pr124433⟩
private theorem pr124447 : PrimeCertificate 124447 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv2963]) (by decide +kernel)
def pv124447 : PrimeValue := ⟨124447, pr124447⟩
private theorem pr124459 : PrimeCertificate 124459 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv20743]) (by decide +kernel)
def pv124459 : PrimeValue := ⟨124459, pr124459⟩
private theorem pr124471 : PrimeCertificate 124471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv461]) (by decide +kernel)
def pv124471 : PrimeValue := ⟨124471, pr124471⟩
private theorem pr124477 : PrimeCertificate 124477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv41]) (by decide +kernel)
def pv124477 : PrimeValue := ⟨124477, pr124477⟩
private theorem pr124489 : PrimeCertificate 124489 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv19]) (by decide +kernel)
def pv124489 : PrimeValue := ⟨124489, pr124489⟩
private theorem pr124493 : PrimeCertificate 124493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31123]) (by decide +kernel)
def pv124493 : PrimeValue := ⟨124493, pr124493⟩
private theorem pr124513 : PrimeCertificate 124513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1297]) (by decide +kernel)
def pv124513 : PrimeValue := ⟨124513, pr124513⟩
private theorem pr124529 : PrimeCertificate 124529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv181]) (by decide +kernel)
def pv124529 : PrimeValue := ⟨124529, pr124529⟩
private theorem pr124541 : PrimeCertificate 124541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv479]) (by decide +kernel)
def pv124541 : PrimeValue := ⟨124541, pr124541⟩
private theorem pr124543 : PrimeCertificate 124543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv17,pv37]) (by decide +kernel)
def pv124543 : PrimeValue := ⟨124543, pr124543⟩
private theorem pr124561 : PrimeCertificate 124561 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv173]) (by decide +kernel)
def pv124561 : PrimeValue := ⟨124561, pr124561⟩
private theorem pr124577 : PrimeCertificate 124577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv229]) (by decide +kernel)
def pv124577 : PrimeValue := ⟨124577, pr124577⟩
private theorem pr124601 : PrimeCertificate 124601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv89]) (by decide +kernel)
def pv124601 : PrimeValue := ⟨124601, pr124601⟩
private theorem pr124633 : PrimeCertificate 124633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv577]) (by decide +kernel)
def pv124633 : PrimeValue := ⟨124633, pr124633⟩
private theorem pr124643 : PrimeCertificate 124643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv307]) (by decide +kernel)
def pv124643 : PrimeValue := ⟨124643, pr124643⟩
private theorem pr124673 : PrimeCertificate 124673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv487]) (by decide +kernel)
def pv124673 : PrimeValue := ⟨124673, pr124673⟩
private theorem pr124679 : PrimeCertificate 124679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv19,pv193]) (by decide +kernel)
def pv124679 : PrimeValue := ⟨124679, pr124679⟩
private theorem pr124699 : PrimeCertificate 124699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2969]) (by decide +kernel)
def pv124699 : PrimeValue := ⟨124699, pr124699⟩
private theorem pr124703 : PrimeCertificate 124703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv62351]) (by decide +kernel)
def pv124703 : PrimeValue := ⟨124703, pr124703⟩
private theorem pr124717 : PrimeCertificate 124717 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv547]) (by decide +kernel)
def pv124717 : PrimeValue := ⟨124717, pr124717⟩
private theorem pr124721 : PrimeCertificate 124721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1559]) (by decide +kernel)
def pv124721 : PrimeValue := ⟨124721, pr124721⟩
private theorem pr124739 : PrimeCertificate 124739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1327]) (by decide +kernel)
def pv124739 : PrimeValue := ⟨124739, pr124739⟩
private theorem pr124759 : PrimeCertificate 124759 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29,pv239]) (by decide +kernel)
def pv124759 : PrimeValue := ⟨124759, pr124759⟩
private theorem pr124769 : PrimeCertificate 124769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv557]) (by decide +kernel)
def pv124769 : PrimeValue := ⟨124769, pr124769⟩
private theorem pr124771 : PrimeCertificate 124771 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv4159]) (by decide +kernel)
def pv124771 : PrimeValue := ⟨124771, pr124771⟩
private theorem pr124781 : PrimeCertificate 124781 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv367]) (by decide +kernel)
def pv124781 : PrimeValue := ⟨124781, pr124781⟩
private theorem pr124783 : PrimeCertificate 124783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv2971]) (by decide +kernel)
def pv124783 : PrimeValue := ⟨124783, pr124783⟩
private theorem pr124793 : PrimeCertificate 124793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv821]) (by decide +kernel)
def pv124793 : PrimeValue := ⟨124793, pr124793⟩
private theorem pr124799 : PrimeCertificate 124799 :=
  certifyPrime (q := pv11) (ls := [pv2,pv23,pv2713]) (by decide +kernel)
def pv124799 : PrimeValue := ⟨124799, pr124799⟩
private theorem pr124819 : PrimeCertificate 124819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv293]) (by decide +kernel)
def pv124819 : PrimeValue := ⟨124819, pr124819⟩
private theorem pr124823 : PrimeCertificate 124823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv139,pv449]) (by decide +kernel)
def pv124823 : PrimeValue := ⟨124823, pr124823⟩
private theorem pr124847 : PrimeCertificate 124847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv62423]) (by decide +kernel)
def pv124847 : PrimeValue := ⟨124847, pr124847⟩
private theorem pr124853 : PrimeCertificate 124853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13]) (by decide +kernel)
def pv124853 : PrimeValue := ⟨124853, pr124853⟩
private theorem pr124897 : PrimeCertificate 124897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1301]) (by decide +kernel)
def pv124897 : PrimeValue := ⟨124897, pr124897⟩
private theorem pr124907 : PrimeCertificate 124907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv173]) (by decide +kernel)
def pv124907 : PrimeValue := ⟨124907, pr124907⟩
private theorem pr124909 : PrimeCertificate 124909 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv1487]) (by decide +kernel)
def pv124909 : PrimeValue := ⟨124909, pr124909⟩
private theorem pr124919 : PrimeCertificate 124919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv62459]) (by decide +kernel)
def pv124919 : PrimeValue := ⟨124919, pr124919⟩
private theorem pr124951 : PrimeCertificate 124951 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv124951 : PrimeValue := ⟨124951, pr124951⟩
private theorem pr124981 : PrimeCertificate 124981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2083]) (by decide +kernel)
def pv124981 : PrimeValue := ⟨124981, pr124981⟩
private theorem pr124987 : PrimeCertificate 124987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv563]) (by decide +kernel)
def pv124987 : PrimeValue := ⟨124987, pr124987⟩
private theorem pr124991 : PrimeCertificate 124991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv29,pv431]) (by decide +kernel)
def pv124991 : PrimeValue := ⟨124991, pr124991⟩
private theorem pr125003 : PrimeCertificate 125003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv62501]) (by decide +kernel)
def pv125003 : PrimeValue := ⟨125003, pr125003⟩
private theorem pr125017 : PrimeCertificate 125017 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5209]) (by decide +kernel)
def pv125017 : PrimeValue := ⟨125017, pr125017⟩
private theorem pr125029 : PrimeCertificate 125029 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv23,pv151]) (by decide +kernel)
def pv125029 : PrimeValue := ⟨125029, pr125029⟩
private theorem pr125093 : PrimeCertificate 125093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2843]) (by decide +kernel)
def pv125093 : PrimeValue := ⟨125093, pr125093⟩
private theorem pr125101 : PrimeCertificate 125101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv139]) (by decide +kernel)
def pv125101 : PrimeValue := ⟨125101, pr125101⟩
private theorem pr125107 : PrimeCertificate 125107 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv719]) (by decide +kernel)
def pv125107 : PrimeValue := ⟨125107, pr125107⟩
private theorem pr125113 : PrimeCertificate 125113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv401]) (by decide +kernel)
def pv125113 : PrimeValue := ⟨125113, pr125113⟩
private theorem pr125117 : PrimeCertificate 125117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1009]) (by decide +kernel)
def pv125117 : PrimeValue := ⟨125117, pr125117⟩
private theorem pr125119 : PrimeCertificate 125119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv331]) (by decide +kernel)
def pv125119 : PrimeValue := ⟨125119, pr125119⟩
private theorem pr125131 : PrimeCertificate 125131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv43,pv97]) (by decide +kernel)
def pv125131 : PrimeValue := ⟨125131, pr125131⟩
private theorem pr125141 : PrimeCertificate 125141 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6257]) (by decide +kernel)
def pv125141 : PrimeValue := ⟨125141, pr125141⟩
private theorem pr125149 : PrimeCertificate 125149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10429]) (by decide +kernel)
def pv125149 : PrimeValue := ⟨125149, pr125149⟩
private theorem pr125183 : PrimeCertificate 125183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv62591]) (by decide +kernel)
def pv125183 : PrimeValue := ⟨125183, pr125183⟩
private theorem pr125197 : PrimeCertificate 125197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10433]) (by decide +kernel)
def pv125197 : PrimeValue := ⟨125197, pr125197⟩
private theorem pr125201 : PrimeCertificate 125201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv313]) (by decide +kernel)
def pv125201 : PrimeValue := ⟨125201, pr125201⟩
private theorem pr125207 : PrimeCertificate 125207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv62603]) (by decide +kernel)
def pv125207 : PrimeValue := ⟨125207, pr125207⟩
private theorem pr125219 : PrimeCertificate 125219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv457]) (by decide +kernel)
def pv125219 : PrimeValue := ⟨125219, pr125219⟩
private theorem pr125221 : PrimeCertificate 125221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2087]) (by decide +kernel)
def pv125221 : PrimeValue := ⟨125221, pr125221⟩
private theorem pr125231 : PrimeCertificate 125231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv1789]) (by decide +kernel)
def pv125231 : PrimeValue := ⟨125231, pr125231⟩
private theorem pr125243 : PrimeCertificate 125243 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv4817]) (by decide +kernel)
def pv125243 : PrimeValue := ⟨125243, pr125243⟩
private theorem pr125261 : PrimeCertificate 125261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6263]) (by decide +kernel)
def pv125261 : PrimeValue := ⟨125261, pr125261⟩
private theorem pr125269 : PrimeCertificate 125269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv73]) (by decide +kernel)
def pv125269 : PrimeValue := ⟨125269, pr125269⟩
private theorem pr125287 : PrimeCertificate 125287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv157]) (by decide +kernel)
def pv125287 : PrimeValue := ⟨125287, pr125287⟩
private theorem pr125299 : PrimeCertificate 125299 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6961]) (by decide +kernel)
def pv125299 : PrimeValue := ⟨125299, pr125299⟩
private theorem pr125303 : PrimeCertificate 125303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv43,pv47]) (by decide +kernel)
def pv125303 : PrimeValue := ⟨125303, pr125303⟩
private theorem pr125311 : PrimeCertificate 125311 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4177]) (by decide +kernel)
def pv125311 : PrimeValue := ⟨125311, pr125311⟩
private theorem pr125329 : PrimeCertificate 125329 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv7,pv373]) (by decide +kernel)
def pv125329 : PrimeValue := ⟨125329, pr125329⟩
private theorem pr125339 : PrimeCertificate 125339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv2161]) (by decide +kernel)
def pv125339 : PrimeValue := ⟨125339, pr125339⟩
private theorem pr125353 : PrimeCertificate 125353 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1741]) (by decide +kernel)
def pv125353 : PrimeValue := ⟨125353, pr125353⟩
private theorem pr125371 : PrimeCertificate 125371 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv199]) (by decide +kernel)
def pv125371 : PrimeValue := ⟨125371, pr125371⟩
private theorem pr125383 : PrimeCertificate 125383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv20897]) (by decide +kernel)
def pv125383 : PrimeValue := ⟨125383, pr125383⟩
private theorem pr125387 : PrimeCertificate 125387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv883]) (by decide +kernel)
def pv125387 : PrimeValue := ⟨125387, pr125387⟩
private theorem pr125399 : PrimeCertificate 125399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv53]) (by decide +kernel)
def pv125399 : PrimeValue := ⟨125399, pr125399⟩
private theorem pr125423 : PrimeCertificate 125423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv5701]) (by decide +kernel)
def pv125423 : PrimeValue := ⟨125423, pr125423⟩
private theorem pr125429 : PrimeCertificate 125429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31357]) (by decide +kernel)
def pv125429 : PrimeValue := ⟨125429, pr125429⟩
private theorem pr125441 : PrimeCertificate 125441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv125441 : PrimeValue := ⟨125441, pr125441⟩
private theorem pr125453 : PrimeCertificate 125453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv397]) (by decide +kernel)
def pv125453 : PrimeValue := ⟨125453, pr125453⟩
private theorem pr125471 : PrimeCertificate 125471 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv12547]) (by decide +kernel)
def pv125471 : PrimeValue := ⟨125471, pr125471⟩
private theorem pr125497 : PrimeCertificate 125497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv83]) (by decide +kernel)
def pv125497 : PrimeValue := ⟨125497, pr125497⟩
private theorem pr125507 : PrimeCertificate 125507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv62753]) (by decide +kernel)
def pv125507 : PrimeValue := ⟨125507, pr125507⟩
private theorem pr125527 : PrimeCertificate 125527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv20921]) (by decide +kernel)
def pv125527 : PrimeValue := ⟨125527, pr125527⟩
private theorem pr125539 : PrimeCertificate 125539 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv61]) (by decide +kernel)
def pv125539 : PrimeValue := ⟨125539, pr125539⟩
private theorem pr125551 : PrimeCertificate 125551 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv125551 : PrimeValue := ⟨125551, pr125551⟩
private theorem pr125591 : PrimeCertificate 125591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv661]) (by decide +kernel)
def pv125591 : PrimeValue := ⟨125591, pr125591⟩
private theorem pr125597 : PrimeCertificate 125597 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1847]) (by decide +kernel)
def pv125597 : PrimeValue := ⟨125597, pr125597⟩
private theorem pr125617 : PrimeCertificate 125617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2617]) (by decide +kernel)
def pv125617 : PrimeValue := ⟨125617, pr125617⟩
private theorem pr125621 : PrimeCertificate 125621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv571]) (by decide +kernel)
def pv125621 : PrimeValue := ⟨125621, pr125621⟩
private theorem pr125639 : PrimeCertificate 125639 :=
  certifyPrime (q := pv13) (ls := [pv2,pv62819]) (by decide +kernel)
def pv125639 : PrimeValue := ⟨125639, pr125639⟩
private theorem pr125641 : PrimeCertificate 125641 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv349]) (by decide +kernel)
def pv125641 : PrimeValue := ⟨125641, pr125641⟩
private theorem pr125651 : PrimeCertificate 125651 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv359]) (by decide +kernel)
def pv125651 : PrimeValue := ⟨125651, pr125651⟩
private theorem pr125659 : PrimeCertificate 125659 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv13,pv179]) (by decide +kernel)
def pv125659 : PrimeValue := ⟨125659, pr125659⟩
private theorem pr125683 : PrimeCertificate 125683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20947]) (by decide +kernel)
def pv125683 : PrimeValue := ⟨125683, pr125683⟩
private theorem pr125687 : PrimeCertificate 125687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv29,pv197]) (by decide +kernel)
def pv125687 : PrimeValue := ⟨125687, pr125687⟩
private theorem pr125693 : PrimeCertificate 125693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv67]) (by decide +kernel)
def pv125693 : PrimeValue := ⟨125693, pr125693⟩
private theorem pr125707 : PrimeCertificate 125707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv73]) (by decide +kernel)
def pv125707 : PrimeValue := ⟨125707, pr125707⟩
private theorem pr125711 : PrimeCertificate 125711 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv967]) (by decide +kernel)
def pv125711 : PrimeValue := ⟨125711, pr125711⟩
private theorem pr125717 : PrimeCertificate 125717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv593]) (by decide +kernel)
def pv125717 : PrimeValue := ⟨125717, pr125717⟩
private theorem pr125731 : PrimeCertificate 125731 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv127]) (by decide +kernel)
def pv125731 : PrimeValue := ⟨125731, pr125731⟩
private theorem pr125737 : PrimeCertificate 125737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv125737 : PrimeValue := ⟨125737, pr125737⟩
private theorem pr125743 : PrimeCertificate 125743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv1103]) (by decide +kernel)
def pv125743 : PrimeValue := ⟨125743, pr125743⟩
private theorem pr125777 : PrimeCertificate 125777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1123]) (by decide +kernel)
def pv125777 : PrimeValue := ⟨125777, pr125777⟩
private theorem pr125789 : PrimeCertificate 125789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv41,pv59]) (by decide +kernel)
def pv125789 : PrimeValue := ⟨125789, pr125789⟩
private theorem pr125791 : PrimeCertificate 125791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv599]) (by decide +kernel)
def pv125791 : PrimeValue := ⟨125791, pr125791⟩
private theorem pr125803 : PrimeCertificate 125803 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv241]) (by decide +kernel)
def pv125803 : PrimeValue := ⟨125803, pr125803⟩
private theorem pr125813 : PrimeCertificate 125813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv443]) (by decide +kernel)
def pv125813 : PrimeValue := ⟨125813, pr125813⟩
private theorem pr125821 : PrimeCertificate 125821 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv233]) (by decide +kernel)
def pv125821 : PrimeValue := ⟨125821, pr125821⟩
private theorem pr125863 : PrimeCertificate 125863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1907]) (by decide +kernel)
def pv125863 : PrimeValue := ⟨125863, pr125863⟩
private theorem pr125887 : PrimeCertificate 125887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv20981]) (by decide +kernel)
def pv125887 : PrimeValue := ⟨125887, pr125887⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
