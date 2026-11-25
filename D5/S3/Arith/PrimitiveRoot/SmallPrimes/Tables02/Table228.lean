/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table228
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table228.pv1059787
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table061

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1059787 : PrimeCertificate 1059787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv647]) (by decide +kernel)
def pv1059787 : PrimeValue := ⟨1059787, pr1059787⟩
private theorem pr1059823 : PrimeCertificate 1059823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv97,pv607]) (by decide +kernel)
def pv1059823 : PrimeValue := ⟨1059823, pr1059823⟩
private theorem pr1060009 : PrimeCertificate 1060009 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv1523]) (by decide +kernel)
def pv1060009 : PrimeValue := ⟨1060009, pr1060009⟩
private theorem pr1060123 : PrimeCertificate 1060123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv43,pv587]) (by decide +kernel)
def pv1060123 : PrimeValue := ⟨1060123, pr1060123⟩
private theorem pr1060357 : PrimeCertificate 1060357 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv29,pv277]) (by decide +kernel)
def pv1060357 : PrimeValue := ⟨1060357, pr1060357⟩
private theorem pr1060453 : PrimeCertificate 1060453 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1091]) (by decide +kernel)
def pv1060453 : PrimeValue := ⟨1060453, pr1060453⟩
private theorem pr1060567 : PrimeCertificate 1060567 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv13597]) (by decide +kernel)
def pv1060567 : PrimeValue := ⟨1060567, pr1060567⟩
private theorem pr1060723 : PrimeCertificate 1060723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1511]) (by decide +kernel)
def pv1060723 : PrimeValue := ⟨1060723, pr1060723⟩
private theorem pr1060747 : PrimeCertificate 1060747 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv176791]) (by decide +kernel)
def pv1060747 : PrimeValue := ⟨1060747, pr1060747⟩
private theorem pr1060867 : PrimeCertificate 1060867 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv58937]) (by decide +kernel)
def pv1060867 : PrimeValue := ⟨1060867, pr1060867⟩
private theorem pr1061227 : PrimeCertificate 1061227 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv29,pv107]) (by decide +kernel)
def pv1061227 : PrimeValue := ⟨1061227, pr1061227⟩
private theorem pr1061287 : PrimeCertificate 1061287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv2239]) (by decide +kernel)
def pv1061287 : PrimeValue := ⟨1061287, pr1061287⟩
private theorem pr1061353 : PrimeCertificate 1061353 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv14741]) (by decide +kernel)
def pv1061353 : PrimeValue := ⟨1061353, pr1061353⟩
private theorem pr1061617 : PrimeCertificate 1061617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv1301]) (by decide +kernel)
def pv1061617 : PrimeValue := ⟨1061617, pr1061617⟩
private theorem pr1062547 : PrimeCertificate 1062547 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv177091]) (by decide +kernel)
def pv1062547 : PrimeValue := ⟨1062547, pr1062547⟩
private theorem pr1062643 : PrimeCertificate 1062643 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv25301]) (by decide +kernel)
def pv1062643 : PrimeValue := ⟨1062643, pr1062643⟩
private theorem pr1062907 : PrimeCertificate 1062907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv13627]) (by decide +kernel)
def pv1062907 : PrimeValue := ⟨1062907, pr1062907⟩
private theorem pr1062979 : PrimeCertificate 1062979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv25309]) (by decide +kernel)
def pv1062979 : PrimeValue := ⟨1062979, pr1062979⟩
private theorem pr1063009 : PrimeCertificate 1063009 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv3691]) (by decide +kernel)
def pv1063009 : PrimeValue := ⟨1063009, pr1063009⟩
private theorem pr1063177 : PrimeCertificate 1063177 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv31,pv1429]) (by decide +kernel)
def pv1063177 : PrimeValue := ⟨1063177, pr1063177⟩
private theorem pr1063189 : PrimeCertificate 1063189 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv4219]) (by decide +kernel)
def pv1063189 : PrimeValue := ⟨1063189, pr1063189⟩
private theorem pr1063219 : PrimeCertificate 1063219 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv43,pv317]) (by decide +kernel)
def pv1063219 : PrimeValue := ⟨1063219, pr1063219⟩
private theorem pr1063453 : PrimeCertificate 1063453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv17,pv401]) (by decide +kernel)
def pv1063453 : PrimeValue := ⟨1063453, pr1063453⟩
private theorem pr1063597 : PrimeCertificate 1063597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv1453]) (by decide +kernel)
def pv1063597 : PrimeValue := ⟨1063597, pr1063597⟩
private theorem pr1063969 : PrimeCertificate 1063969 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11083]) (by decide +kernel)
def pv1063969 : PrimeValue := ⟨1063969, pr1063969⟩
private theorem pr1063987 : PrimeCertificate 1063987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv47]) (by decide +kernel)
def pv1063987 : PrimeValue := ⟨1063987, pr1063987⟩
private theorem pr1063999 : PrimeCertificate 1063999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv4547]) (by decide +kernel)
def pv1063999 : PrimeValue := ⟨1063999, pr1063999⟩
private theorem pr1064029 : PrimeCertificate 1064029 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv53,pv239]) (by decide +kernel)
def pv1064029 : PrimeValue := ⟨1064029, pr1064029⟩
private theorem pr1064179 : PrimeCertificate 1064179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6569]) (by decide +kernel)
def pv1064179 : PrimeValue := ⟨1064179, pr1064179⟩
private theorem pr1064263 : PrimeCertificate 1064263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv89,pv1993]) (by decide +kernel)
def pv1064263 : PrimeValue := ⟨1064263, pr1064263⟩
private theorem pr1064317 : PrimeCertificate 1064317 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv733]) (by decide +kernel)
def pv1064317 : PrimeValue := ⟨1064317, pr1064317⟩
private theorem pr1064689 : PrimeCertificate 1064689 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv41,pv541]) (by decide +kernel)
def pv1064689 : PrimeValue := ⟨1064689, pr1064689⟩
private theorem pr1064737 : PrimeCertificate 1064737 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv3697]) (by decide +kernel)
def pv1064737 : PrimeValue := ⟨1064737, pr1064737⟩
private theorem pr1064743 : PrimeCertificate 1064743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv101,pv251]) (by decide +kernel)
def pv1064743 : PrimeValue := ⟨1064743, pr1064743⟩
private theorem pr1064977 : PrimeCertificate 1064977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv2017]) (by decide +kernel)
def pv1064977 : PrimeValue := ⟨1064977, pr1064977⟩
private theorem pr1065019 : PrimeCertificate 1065019 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv139,pv1277]) (by decide +kernel)
def pv1065019 : PrimeValue := ⟨1065019, pr1065019⟩
private theorem pr1065073 : PrimeCertificate 1065073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv22189]) (by decide +kernel)
def pv1065073 : PrimeValue := ⟨1065073, pr1065073⟩
private theorem pr1065109 : PrimeCertificate 1065109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv8069]) (by decide +kernel)
def pv1065109 : PrimeValue := ⟨1065109, pr1065109⟩
private theorem pr1065277 : PrimeCertificate 1065277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv127,pv233]) (by decide +kernel)
def pv1065277 : PrimeValue := ⟨1065277, pr1065277⟩
private theorem pr1065733 : PrimeCertificate 1065733 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv88811]) (by decide +kernel)
def pv1065733 : PrimeValue := ⟨1065733, pr1065733⟩
private theorem pr1066339 : PrimeCertificate 1066339 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv31]) (by decide +kernel)
def pv1066339 : PrimeValue := ⟨1066339, pr1066339⟩
private theorem pr1067047 : PrimeCertificate 1067047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv177841]) (by decide +kernel)
def pv1067047 : PrimeValue := ⟨1067047, pr1067047⟩
private theorem pr1067083 : PrimeCertificate 1067083 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv5737]) (by decide +kernel)
def pv1067083 : PrimeValue := ⟨1067083, pr1067083⟩
private theorem pr1067203 : PrimeCertificate 1067203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19763]) (by decide +kernel)
def pv1067203 : PrimeValue := ⟨1067203, pr1067203⟩
private theorem pr1067557 : PrimeCertificate 1067557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv71,pv179]) (by decide +kernel)
def pv1067557 : PrimeValue := ⟨1067557, pr1067557⟩
private theorem pr1067707 : PrimeCertificate 1067707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv2579]) (by decide +kernel)
def pv1067707 : PrimeValue := ⟨1067707, pr1067707⟩
private theorem pr1067749 : PrimeCertificate 1067749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv8089]) (by decide +kernel)
def pv1067749 : PrimeValue := ⟨1067749, pr1067749⟩
private theorem pr1068103 : PrimeCertificate 1068103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv173]) (by decide +kernel)
def pv1068103 : PrimeValue := ⟨1068103, pr1068103⟩
private theorem pr1068259 : PrimeCertificate 1068259 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv7741]) (by decide +kernel)
def pv1068259 : PrimeValue := ⟨1068259, pr1068259⟩
private theorem pr1068703 : PrimeCertificate 1068703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv178117]) (by decide +kernel)
def pv1068703 : PrimeValue := ⟨1068703, pr1068703⟩
private theorem pr1069039 : PrimeCertificate 1069039 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv6599]) (by decide +kernel)
def pv1069039 : PrimeValue := ⟨1069039, pr1069039⟩
private theorem pr1069207 : PrimeCertificate 1069207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv83,pv113]) (by decide +kernel)
def pv1069207 : PrimeValue := ⟨1069207, pr1069207⟩
private theorem pr1069273 : PrimeCertificate 1069273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv14851]) (by decide +kernel)
def pv1069273 : PrimeValue := ⟨1069273, pr1069273⟩
private theorem pr1069363 : PrimeCertificate 1069363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv41]) (by decide +kernel)
def pv1069363 : PrimeValue := ⟨1069363, pr1069363⟩
private theorem pr1069459 : PrimeCertificate 1069459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv13711]) (by decide +kernel)
def pv1069459 : PrimeValue := ⟨1069459, pr1069459⟩
private theorem pr1069603 : PrimeCertificate 1069603 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv89,pv2003]) (by decide +kernel)
def pv1069603 : PrimeValue := ⟨1069603, pr1069603⟩
private theorem pr1069639 : PrimeCertificate 1069639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv337]) (by decide +kernel)
def pv1069639 : PrimeValue := ⟨1069639, pr1069639⟩
private theorem pr1069693 : PrimeCertificate 1069693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv6857]) (by decide +kernel)
def pv1069693 : PrimeValue := ⟨1069693, pr1069693⟩
private theorem pr1069807 : PrimeCertificate 1069807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv178301]) (by decide +kernel)
def pv1069807 : PrimeValue := ⟨1069807, pr1069807⟩
private theorem pr1070323 : PrimeCertificate 1070323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv16217]) (by decide +kernel)
def pv1070323 : PrimeValue := ⟨1070323, pr1070323⟩
private theorem pr1070497 : PrimeCertificate 1070497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv59]) (by decide +kernel)
def pv1070497 : PrimeValue := ⟨1070497, pr1070497⟩
private theorem pr1070533 : PrimeCertificate 1070533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv131,pv227]) (by decide +kernel)
def pv1070533 : PrimeValue := ⟨1070533, pr1070533⟩
private theorem pr1071223 : PrimeCertificate 1071223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv178537]) (by decide +kernel)
def pv1071223 : PrimeValue := ⟨1071223, pr1071223⟩
private theorem pr1071337 : PrimeCertificate 1071337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv911]) (by decide +kernel)
def pv1071337 : PrimeValue := ⟨1071337, pr1071337⟩
private theorem pr1071379 : PrimeCertificate 1071379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv773]) (by decide +kernel)
def pv1071379 : PrimeValue := ⟨1071379, pr1071379⟩
private theorem pr1071487 : PrimeCertificate 1071487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv241]) (by decide +kernel)
def pv1071487 : PrimeValue := ⟨1071487, pr1071487⟩
private theorem pr1071589 : PrimeCertificate 1071589 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv12757]) (by decide +kernel)
def pv1071589 : PrimeValue := ⟨1071589, pr1071589⟩
private theorem pr1071643 : PrimeCertificate 1071643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv1249]) (by decide +kernel)
def pv1071643 : PrimeValue := ⟨1071643, pr1071643⟩
private theorem pr1071739 : PrimeCertificate 1071739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv223]) (by decide +kernel)
def pv1071739 : PrimeValue := ⟨1071739, pr1071739⟩
private theorem pr1071919 : PrimeCertificate 1071919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv31,pv113]) (by decide +kernel)
def pv1071919 : PrimeValue := ⟨1071919, pr1071919⟩
private theorem pr1072129 : PrimeCertificate 1072129 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv349]) (by decide +kernel)
def pv1072129 : PrimeValue := ⟨1072129, pr1072129⟩
private theorem pr1072147 : PrimeCertificate 1072147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv178691]) (by decide +kernel)
def pv1072147 : PrimeValue := ⟨1072147, pr1072147⟩
private theorem pr1072429 : PrimeCertificate 1072429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv751]) (by decide +kernel)
def pv1072429 : PrimeValue := ⟨1072429, pr1072429⟩
private theorem pr1072459 : PrimeCertificate 1072459 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv59581]) (by decide +kernel)
def pv1072459 : PrimeValue := ⟨1072459, pr1072459⟩
private theorem pr1072957 : PrimeCertificate 1072957 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv89413]) (by decide +kernel)
def pv1072957 : PrimeValue := ⟨1072957, pr1072957⟩
private theorem pr1073053 : PrimeCertificate 1073053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv727]) (by decide +kernel)
def pv1073053 : PrimeValue := ⟨1073053, pr1073053⟩
private theorem pr1073089 : PrimeCertificate 1073089 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv1073089 : PrimeValue := ⟨1073089, pr1073089⟩
private theorem pr1073143 : PrimeCertificate 1073143 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv17,pv167]) (by decide +kernel)
def pv1073143 : PrimeValue := ⟨1073143, pr1073143⟩
private theorem pr1073593 : PrimeCertificate 1073593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv31,pv37]) (by decide +kernel)
def pv1073593 : PrimeValue := ⟨1073593, pr1073593⟩
private theorem pr1073869 : PrimeCertificate 1073869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv109,pv821]) (by decide +kernel)
def pv1073869 : PrimeValue := ⟨1073869, pr1073869⟩
private theorem pr1074133 : PrimeCertificate 1074133 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29837]) (by decide +kernel)
def pv1074133 : PrimeValue := ⟨1074133, pr1074133⟩
private theorem pr1074223 : PrimeCertificate 1074223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv349]) (by decide +kernel)
def pv1074223 : PrimeValue := ⟨1074223, pr1074223⟩
private theorem pr1074259 : PrimeCertificate 1074259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv1613]) (by decide +kernel)
def pv1074259 : PrimeValue := ⟨1074259, pr1074259⟩
private theorem pr1074877 : PrimeCertificate 1074877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv479]) (by decide +kernel)
def pv1074877 : PrimeValue := ⟨1074877, pr1074877⟩
private theorem pr1074889 : PrimeCertificate 1074889 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv14929]) (by decide +kernel)
def pv1074889 : PrimeValue := ⟨1074889, pr1074889⟩
private theorem pr1075279 : PrimeCertificate 1075279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv179213]) (by decide +kernel)
def pv1075279 : PrimeValue := ⟨1075279, pr1075279⟩
private theorem pr1075693 : PrimeCertificate 1075693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv5273]) (by decide +kernel)
def pv1075693 : PrimeValue := ⟨1075693, pr1075693⟩
private theorem pr1075729 : PrimeCertificate 1075729 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv73,pv307]) (by decide +kernel)
def pv1075729 : PrimeValue := ⟨1075729, pr1075729⟩
private theorem pr1075843 : PrimeCertificate 1075843 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv229]) (by decide +kernel)
def pv1075843 : PrimeValue := ⟨1075843, pr1075843⟩
private theorem pr1076077 : PrimeCertificate 1076077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv421]) (by decide +kernel)
def pv1076077 : PrimeValue := ⟨1076077, pr1076077⟩
private theorem pr1076167 : PrimeCertificate 1076167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv73]) (by decide +kernel)
def pv1076167 : PrimeValue := ⟨1076167, pr1076167⟩
private theorem pr1076473 : PrimeCertificate 1076473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv14951]) (by decide +kernel)
def pv1076473 : PrimeValue := ⟨1076473, pr1076473⟩
private theorem pr1076503 : PrimeCertificate 1076503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv71]) (by decide +kernel)
def pv1076503 : PrimeValue := ⟨1076503, pr1076503⟩
private theorem pr1076557 : PrimeCertificate 1076557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv67,pv103]) (by decide +kernel)
def pv1076557 : PrimeValue := ⟨1076557, pr1076557⟩
private theorem pr1076587 : PrimeCertificate 1076587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv25633]) (by decide +kernel)
def pv1076587 : PrimeValue := ⟨1076587, pr1076587⟩
private theorem pr1076707 : PrimeCertificate 1076707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv127,pv157]) (by decide +kernel)
def pv1076707 : PrimeValue := ⟨1076707, pr1076707⟩
private theorem pr1076827 : PrimeCertificate 1076827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv179471]) (by decide +kernel)
def pv1076827 : PrimeValue := ⟨1076827, pr1076827⟩
private theorem pr1076917 : PrimeCertificate 1076917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv5279]) (by decide +kernel)
def pv1076917 : PrimeValue := ⟨1076917, pr1076917⟩
private theorem pr1077127 : PrimeCertificate 1077127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv5791]) (by decide +kernel)
def pv1077127 : PrimeValue := ⟨1077127, pr1077127⟩
private theorem pr1077607 : PrimeCertificate 1077607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv131,pv457]) (by decide +kernel)
def pv1077607 : PrimeValue := ⟨1077607, pr1077607⟩
private theorem pr1077673 : PrimeCertificate 1077673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv83,pv541]) (by decide +kernel)
def pv1077673 : PrimeValue := ⟨1077673, pr1077673⟩
private theorem pr1077793 : PrimeCertificate 1077793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103,pv109]) (by decide +kernel)
def pv1077793 : PrimeValue := ⟨1077793, pr1077793⟩
private theorem pr1078183 : PrimeCertificate 1078183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv43,pv199]) (by decide +kernel)
def pv1078183 : PrimeValue := ⟨1078183, pr1078183⟩
private theorem pr1078333 : PrimeCertificate 1078333 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv23,pv3907]) (by decide +kernel)
def pv1078333 : PrimeValue := ⟨1078333, pr1078333⟩
private theorem pr1078417 : PrimeCertificate 1078417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7489]) (by decide +kernel)
def pv1078417 : PrimeValue := ⟨1078417, pr1078417⟩
private theorem pr1078507 : PrimeCertificate 1078507 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv419]) (by decide +kernel)
def pv1078507 : PrimeValue := ⟨1078507, pr1078507⟩
private theorem pr1078849 : PrimeCertificate 1078849 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1873]) (by decide +kernel)
def pv1078849 : PrimeValue := ⟨1078849, pr1078849⟩
private theorem pr1078927 : PrimeCertificate 1078927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv179821]) (by decide +kernel)
def pv1078927 : PrimeValue := ⟨1078927, pr1078927⟩
private theorem pr1079173 : PrimeCertificate 1079173 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv967]) (by decide +kernel)
def pv1079173 : PrimeValue := ⟨1079173, pr1079173⟩
private theorem pr1079359 : PrimeCertificate 1079359 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7,pv31,pv829]) (by decide +kernel)
def pv1079359 : PrimeValue := ⟨1079359, pr1079359⟩
private theorem pr1079473 : PrimeCertificate 1079473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv523]) (by decide +kernel)
def pv1079473 : PrimeValue := ⟨1079473, pr1079473⟩
private theorem pr1079527 : PrimeCertificate 1079527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv25703]) (by decide +kernel)
def pv1079527 : PrimeValue := ⟨1079527, pr1079527⟩
private theorem pr1079539 : PrimeCertificate 1079539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv179923]) (by decide +kernel)
def pv1079539 : PrimeValue := ⟨1079539, pr1079539⟩
private theorem pr1079569 : PrimeCertificate 1079569 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv1079569 : PrimeValue := ⟨1079569, pr1079569⟩
private theorem pr1079983 : PrimeCertificate 1079983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59999]) (by decide +kernel)
def pv1079983 : PrimeValue := ⟨1079983, pr1079983⟩
private theorem pr1080223 : PrimeCertificate 1080223 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv13,pv1259]) (by decide +kernel)
def pv1080223 : PrimeValue := ⟨1080223, pr1080223⟩
private theorem pr1080229 : PrimeCertificate 1080229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv90019]) (by decide +kernel)
def pv1080229 : PrimeValue := ⟨1080229, pr1080229⟩
private theorem pr1080613 : PrimeCertificate 1080613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv2309]) (by decide +kernel)
def pv1080613 : PrimeValue := ⟨1080613, pr1080613⟩
private theorem pr1080907 : PrimeCertificate 1080907 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv3833]) (by decide +kernel)
def pv1080907 : PrimeValue := ⟨1080907, pr1080907⟩
private theorem pr1080913 : PrimeCertificate 1080913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv3217]) (by decide +kernel)
def pv1080913 : PrimeValue := ⟨1080913, pr1080913⟩
private theorem pr1081027 : PrimeCertificate 1081027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6673]) (by decide +kernel)
def pv1081027 : PrimeValue := ⟨1081027, pr1081027⟩
private theorem pr1081279 : PrimeCertificate 1081279 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv43,pv127]) (by decide +kernel)
def pv1081279 : PrimeValue := ⟨1081279, pr1081279⟩
private theorem pr1081657 : PrimeCertificate 1081657 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv83,pv181]) (by decide +kernel)
def pv1081657 : PrimeValue := ⟨1081657, pr1081657⟩
private theorem pr1081699 : PrimeCertificate 1081699 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv139,pv1297]) (by decide +kernel)
def pv1081699 : PrimeValue := ⟨1081699, pr1081699⟩
private theorem pr1081723 : PrimeCertificate 1081723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv180287]) (by decide +kernel)
def pv1081723 : PrimeValue := ⟨1081723, pr1081723⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
