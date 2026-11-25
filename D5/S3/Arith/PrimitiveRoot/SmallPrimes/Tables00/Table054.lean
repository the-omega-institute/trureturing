/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table054
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table054.pv153523
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr153523 : PrimeCertificate 153523 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2843]) (by decide +kernel)
def pv153523 : PrimeValue := ⟨153523, pr153523⟩
private theorem pr153529 : PrimeCertificate 153529 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv6397]) (by decide +kernel)
def pv153529 : PrimeValue := ⟨153529, pr153529⟩
private theorem pr153533 : PrimeCertificate 153533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv131,pv293]) (by decide +kernel)
def pv153533 : PrimeValue := ⟨153533, pr153533⟩
private theorem pr153557 : PrimeCertificate 153557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2953]) (by decide +kernel)
def pv153557 : PrimeValue := ⟨153557, pr153557⟩
private theorem pr153563 : PrimeCertificate 153563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv76781]) (by decide +kernel)
def pv153563 : PrimeValue := ⟨153563, pr153563⟩
private theorem pr153607 : PrimeCertificate 153607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25601]) (by decide +kernel)
def pv153607 : PrimeValue := ⟨153607, pr153607⟩
private theorem pr153611 : PrimeCertificate 153611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv15361]) (by decide +kernel)
def pv153611 : PrimeValue := ⟨153611, pr153611⟩
private theorem pr153641 : PrimeCertificate 153641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv167]) (by decide +kernel)
def pv153641 : PrimeValue := ⟨153641, pr153641⟩
private theorem pr153649 : PrimeCertificate 153649 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv97]) (by decide +kernel)
def pv153649 : PrimeValue := ⟨153649, pr153649⟩
private theorem pr153689 : PrimeCertificate 153689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19211]) (by decide +kernel)
def pv153689 : PrimeValue := ⟨153689, pr153689⟩
private theorem pr153701 : PrimeCertificate 153701 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv53]) (by decide +kernel)
def pv153701 : PrimeValue := ⟨153701, pr153701⟩
private theorem pr153719 : PrimeCertificate 153719 :=
  certifyPrime (q := pv11) (ls := [pv2,pv151,pv509]) (by decide +kernel)
def pv153719 : PrimeValue := ⟨153719, pr153719⟩
private theorem pr153739 : PrimeCertificate 153739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv73]) (by decide +kernel)
def pv153739 : PrimeValue := ⟨153739, pr153739⟩
private theorem pr153743 : PrimeCertificate 153743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv76871]) (by decide +kernel)
def pv153743 : PrimeValue := ⟨153743, pr153743⟩
private theorem pr153749 : PrimeCertificate 153749 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv17,pv19]) (by decide +kernel)
def pv153749 : PrimeValue := ⟨153749, pr153749⟩
private theorem pr153757 : PrimeCertificate 153757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4271]) (by decide +kernel)
def pv153757 : PrimeValue := ⟨153757, pr153757⟩
private theorem pr153763 : PrimeCertificate 153763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv523]) (by decide +kernel)
def pv153763 : PrimeValue := ⟨153763, pr153763⟩
private theorem pr153817 : PrimeCertificate 153817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv17,pv29]) (by decide +kernel)
def pv153817 : PrimeValue := ⟨153817, pr153817⟩
private theorem pr153841 : PrimeCertificate 153841 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv641]) (by decide +kernel)
def pv153841 : PrimeValue := ⟨153841, pr153841⟩
private theorem pr153871 : PrimeCertificate 153871 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv23,pv223]) (by decide +kernel)
def pv153871 : PrimeValue := ⟨153871, pr153871⟩
private theorem pr153877 : PrimeCertificate 153877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12823]) (by decide +kernel)
def pv153877 : PrimeValue := ⟨153877, pr153877⟩
private theorem pr153887 : PrimeCertificate 153887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv76943]) (by decide +kernel)
def pv153887 : PrimeValue := ⟨153887, pr153887⟩
private theorem pr153889 : PrimeCertificate 153889 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv229]) (by decide +kernel)
def pv153889 : PrimeValue := ⟨153889, pr153889⟩
private theorem pr153911 : PrimeCertificate 153911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv15391]) (by decide +kernel)
def pv153911 : PrimeValue := ⟨153911, pr153911⟩
private theorem pr153913 : PrimeCertificate 153913 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv53]) (by decide +kernel)
def pv153913 : PrimeValue := ⟨153913, pr153913⟩
private theorem pr153929 : PrimeCertificate 153929 :=
  certifyPrime (q := pv7) (ls := [pv2,pv71,pv271]) (by decide +kernel)
def pv153929 : PrimeValue := ⟨153929, pr153929⟩
private theorem pr153941 : PrimeCertificate 153941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv179]) (by decide +kernel)
def pv153941 : PrimeValue := ⟨153941, pr153941⟩
private theorem pr153947 : PrimeCertificate 153947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv31,pv191]) (by decide +kernel)
def pv153947 : PrimeValue := ⟨153947, pr153947⟩
private theorem pr153953 : PrimeCertificate 153953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv283]) (by decide +kernel)
def pv153953 : PrimeValue := ⟨153953, pr153953⟩
private theorem pr153991 : PrimeCertificate 153991 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv29,pv59]) (by decide +kernel)
def pv153991 : PrimeValue := ⟨153991, pr153991⟩
private theorem pr153997 : PrimeCertificate 153997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv313]) (by decide +kernel)
def pv153997 : PrimeValue := ⟨153997, pr153997⟩
private theorem pr154001 : PrimeCertificate 154001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv11]) (by decide +kernel)
def pv154001 : PrimeValue := ⟨154001, pr154001⟩
private theorem pr154057 : PrimeCertificate 154057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv131]) (by decide +kernel)
def pv154057 : PrimeValue := ⟨154057, pr154057⟩
private theorem pr154067 : PrimeCertificate 154067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv47,pv149]) (by decide +kernel)
def pv154067 : PrimeValue := ⟨154067, pr154067⟩
private theorem pr154073 : PrimeCertificate 154073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19259]) (by decide +kernel)
def pv154073 : PrimeValue := ⟨154073, pr154073⟩
private theorem pr154079 : PrimeCertificate 154079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv41,pv1879]) (by decide +kernel)
def pv154079 : PrimeValue := ⟨154079, pr154079⟩
private theorem pr154087 : PrimeCertificate 154087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61,pv421]) (by decide +kernel)
def pv154087 : PrimeValue := ⟨154087, pr154087⟩
private theorem pr154097 : PrimeCertificate 154097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9631]) (by decide +kernel)
def pv154097 : PrimeValue := ⟨154097, pr154097⟩
private theorem pr154111 : PrimeCertificate 154111 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv467]) (by decide +kernel)
def pv154111 : PrimeValue := ⟨154111, pr154111⟩
private theorem pr154127 : PrimeCertificate 154127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv101,pv109]) (by decide +kernel)
def pv154127 : PrimeValue := ⟨154127, pr154127⟩
private theorem pr154153 : PrimeCertificate 154153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2141]) (by decide +kernel)
def pv154153 : PrimeValue := ⟨154153, pr154153⟩
private theorem pr154157 : PrimeCertificate 154157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2267]) (by decide +kernel)
def pv154157 : PrimeValue := ⟨154157, pr154157⟩
private theorem pr154159 : PrimeCertificate 154159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25693]) (by decide +kernel)
def pv154159 : PrimeValue := ⟨154159, pr154159⟩
private theorem pr154181 : PrimeCertificate 154181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv593]) (by decide +kernel)
def pv154181 : PrimeValue := ⟨154181, pr154181⟩
private theorem pr154211 : PrimeCertificate 154211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2203]) (by decide +kernel)
def pv154211 : PrimeValue := ⟨154211, pr154211⟩
private theorem pr154213 : PrimeCertificate 154213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv181]) (by decide +kernel)
def pv154213 : PrimeValue := ⟨154213, pr154213⟩
private theorem pr154229 : PrimeCertificate 154229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38557]) (by decide +kernel)
def pv154229 : PrimeValue := ⟨154229, pr154229⟩
private theorem pr154243 : PrimeCertificate 154243 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv19,pv41]) (by decide +kernel)
def pv154243 : PrimeValue := ⟨154243, pr154243⟩
private theorem pr154247 : PrimeCertificate 154247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv233,pv331]) (by decide +kernel)
def pv154247 : PrimeValue := ⟨154247, pr154247⟩
private theorem pr154267 : PrimeCertificate 154267 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv3673]) (by decide +kernel)
def pv154267 : PrimeValue := ⟨154267, pr154267⟩
private theorem pr154277 : PrimeCertificate 154277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38569]) (by decide +kernel)
def pv154277 : PrimeValue := ⟨154277, pr154277⟩
private theorem pr154279 : PrimeCertificate 154279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2857]) (by decide +kernel)
def pv154279 : PrimeValue := ⟨154279, pr154279⟩
private theorem pr154291 : PrimeCertificate 154291 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv37,pv139]) (by decide +kernel)
def pv154291 : PrimeValue := ⟨154291, pr154291⟩
private theorem pr154303 : PrimeCertificate 154303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv25717]) (by decide +kernel)
def pv154303 : PrimeValue := ⟨154303, pr154303⟩
private theorem pr154313 : PrimeCertificate 154313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19289]) (by decide +kernel)
def pv154313 : PrimeValue := ⟨154313, pr154313⟩
private theorem pr154333 : PrimeCertificate 154333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1429]) (by decide +kernel)
def pv154333 : PrimeValue := ⟨154333, pr154333⟩
private theorem pr154339 : PrimeCertificate 154339 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv887]) (by decide +kernel)
def pv154339 : PrimeValue := ⟨154339, pr154339⟩
private theorem pr154351 : PrimeCertificate 154351 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv154351 : PrimeValue := ⟨154351, pr154351⟩
private theorem pr154369 : PrimeCertificate 154369 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv154369 : PrimeValue := ⟨154369, pr154369⟩
private theorem pr154373 : PrimeCertificate 154373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38593]) (by decide +kernel)
def pv154373 : PrimeValue := ⟨154373, pr154373⟩
private theorem pr154387 : PrimeCertificate 154387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv953]) (by decide +kernel)
def pv154387 : PrimeValue := ⟨154387, pr154387⟩
private theorem pr154409 : PrimeCertificate 154409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19301]) (by decide +kernel)
def pv154409 : PrimeValue := ⟨154409, pr154409⟩
private theorem pr154417 : PrimeCertificate 154417 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv3217]) (by decide +kernel)
def pv154417 : PrimeValue := ⟨154417, pr154417⟩
private theorem pr154423 : PrimeCertificate 154423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv373]) (by decide +kernel)
def pv154423 : PrimeValue := ⟨154423, pr154423⟩
private theorem pr154459 : PrimeCertificate 154459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8581]) (by decide +kernel)
def pv154459 : PrimeValue := ⟨154459, pr154459⟩
private theorem pr154501 : PrimeCertificate 154501 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv103]) (by decide +kernel)
def pv154501 : PrimeValue := ⟨154501, pr154501⟩
private theorem pr154523 : PrimeCertificate 154523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv77261]) (by decide +kernel)
def pv154523 : PrimeValue := ⟨154523, pr154523⟩
private theorem pr154543 : PrimeCertificate 154543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv599]) (by decide +kernel)
def pv154543 : PrimeValue := ⟨154543, pr154543⟩
private theorem pr154571 : PrimeCertificate 154571 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv29,pv41]) (by decide +kernel)
def pv154571 : PrimeValue := ⟨154571, pr154571⟩
private theorem pr154573 : PrimeCertificate 154573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1171]) (by decide +kernel)
def pv154573 : PrimeValue := ⟨154573, pr154573⟩
private theorem pr154579 : PrimeCertificate 154579 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv25763]) (by decide +kernel)
def pv154579 : PrimeValue := ⟨154579, pr154579⟩
private theorem pr154589 : PrimeCertificate 154589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv5521]) (by decide +kernel)
def pv154589 : PrimeValue := ⟨154589, pr154589⟩
private theorem pr154591 : PrimeCertificate 154591 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv5153]) (by decide +kernel)
def pv154591 : PrimeValue := ⟨154591, pr154591⟩
private theorem pr154613 : PrimeCertificate 154613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38653]) (by decide +kernel)
def pv154613 : PrimeValue := ⟨154613, pr154613⟩
private theorem pr154619 : PrimeCertificate 154619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv797]) (by decide +kernel)
def pv154619 : PrimeValue := ⟨154619, pr154619⟩
private theorem pr154621 : PrimeCertificate 154621 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv859]) (by decide +kernel)
def pv154621 : PrimeValue := ⟨154621, pr154621⟩
private theorem pr154667 : PrimeCertificate 154667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv4549]) (by decide +kernel)
def pv154667 : PrimeValue := ⟨154667, pr154667⟩
private theorem pr154669 : PrimeCertificate 154669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12889]) (by decide +kernel)
def pv154669 : PrimeValue := ⟨154669, pr154669⟩
private theorem pr154681 : PrimeCertificate 154681 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1289]) (by decide +kernel)
def pv154681 : PrimeValue := ⟨154681, pr154681⟩
private theorem pr154691 : PrimeCertificate 154691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv499]) (by decide +kernel)
def pv154691 : PrimeValue := ⟨154691, pr154691⟩
private theorem pr154699 : PrimeCertificate 154699 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv23,pv59]) (by decide +kernel)
def pv154699 : PrimeValue := ⟨154699, pr154699⟩
private theorem pr154727 : PrimeCertificate 154727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv541]) (by decide +kernel)
def pv154727 : PrimeValue := ⟨154727, pr154727⟩
private theorem pr154733 : PrimeCertificate 154733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv383]) (by decide +kernel)
def pv154733 : PrimeValue := ⟨154733, pr154733⟩
private theorem pr154747 : PrimeCertificate 154747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8597]) (by decide +kernel)
def pv154747 : PrimeValue := ⟨154747, pr154747⟩
private theorem pr154753 : PrimeCertificate 154753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv154753 : PrimeValue := ⟨154753, pr154753⟩
private theorem pr154769 : PrimeCertificate 154769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv569]) (by decide +kernel)
def pv154769 : PrimeValue := ⟨154769, pr154769⟩
private theorem pr154787 : PrimeCertificate 154787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193,pv401]) (by decide +kernel)
def pv154787 : PrimeValue := ⟨154787, pr154787⟩
private theorem pr154789 : PrimeCertificate 154789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12899]) (by decide +kernel)
def pv154789 : PrimeValue := ⟨154789, pr154789⟩
private theorem pr154799 : PrimeCertificate 154799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11057]) (by decide +kernel)
def pv154799 : PrimeValue := ⟨154799, pr154799⟩
private theorem pr154807 : PrimeCertificate 154807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25801]) (by decide +kernel)
def pv154807 : PrimeValue := ⟨154807, pr154807⟩
private theorem pr154823 : PrimeCertificate 154823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv199,pv389]) (by decide +kernel)
def pv154823 : PrimeValue := ⟨154823, pr154823⟩
private theorem pr154841 : PrimeCertificate 154841 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv79]) (by decide +kernel)
def pv154841 : PrimeValue := ⟨154841, pr154841⟩
private theorem pr154849 : PrimeCertificate 154849 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1613]) (by decide +kernel)
def pv154849 : PrimeValue := ⟨154849, pr154849⟩
private theorem pr154873 : PrimeCertificate 154873 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv239]) (by decide +kernel)
def pv154873 : PrimeValue := ⟨154873, pr154873⟩
private theorem pr154877 : PrimeCertificate 154877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1249]) (by decide +kernel)
def pv154877 : PrimeValue := ⟨154877, pr154877⟩
private theorem pr154883 : PrimeCertificate 154883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv23,pv37]) (by decide +kernel)
def pv154883 : PrimeValue := ⟨154883, pr154883⟩
private theorem pr154897 : PrimeCertificate 154897 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv461]) (by decide +kernel)
def pv154897 : PrimeValue := ⟨154897, pr154897⟩
private theorem pr154927 : PrimeCertificate 154927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv151]) (by decide +kernel)
def pv154927 : PrimeValue := ⟨154927, pr154927⟩
private theorem pr154933 : PrimeCertificate 154933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12911]) (by decide +kernel)
def pv154933 : PrimeValue := ⟨154933, pr154933⟩
private theorem pr154937 : PrimeCertificate 154937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107,pv181]) (by decide +kernel)
def pv154937 : PrimeValue := ⟨154937, pr154937⟩
private theorem pr154943 : PrimeCertificate 154943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv77471]) (by decide +kernel)
def pv154943 : PrimeValue := ⟨154943, pr154943⟩
private theorem pr154981 : PrimeCertificate 154981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv41]) (by decide +kernel)
def pv154981 : PrimeValue := ⟨154981, pr154981⟩
private theorem pr155003 : PrimeCertificate 155003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv4079]) (by decide +kernel)
def pv155003 : PrimeValue := ⟨155003, pr155003⟩
private theorem pr155009 : PrimeCertificate 155009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv173]) (by decide +kernel)
def pv155009 : PrimeValue := ⟨155009, pr155009⟩
private theorem pr155027 : PrimeCertificate 155027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv77513]) (by decide +kernel)
def pv155027 : PrimeValue := ⟨155027, pr155027⟩
private theorem pr155047 : PrimeCertificate 155047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv25841]) (by decide +kernel)
def pv155047 : PrimeValue := ⟨155047, pr155047⟩
private theorem pr155069 : PrimeCertificate 155069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38767]) (by decide +kernel)
def pv155069 : PrimeValue := ⟨155069, pr155069⟩
private theorem pr155083 : PrimeCertificate 155083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25847]) (by decide +kernel)
def pv155083 : PrimeValue := ⟨155083, pr155083⟩
private theorem pr155087 : PrimeCertificate 155087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv77543]) (by decide +kernel)
def pv155087 : PrimeValue := ⟨155087, pr155087⟩
private theorem pr155119 : PrimeCertificate 155119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv103,pv251]) (by decide +kernel)
def pv155119 : PrimeValue := ⟨155119, pr155119⟩
private theorem pr155137 : PrimeCertificate 155137 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv155137 : PrimeValue := ⟨155137, pr155137⟩
private theorem pr155167 : PrimeCertificate 155167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2351]) (by decide +kernel)
def pv155167 : PrimeValue := ⟨155167, pr155167⟩
private theorem pr155171 : PrimeCertificate 155171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv263]) (by decide +kernel)
def pv155171 : PrimeValue := ⟨155171, pr155171⟩
private theorem pr155191 : PrimeCertificate 155191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv739]) (by decide +kernel)
def pv155191 : PrimeValue := ⟨155191, pr155191⟩
private theorem pr155203 : PrimeCertificate 155203 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25867]) (by decide +kernel)
def pv155203 : PrimeValue := ⟨155203, pr155203⟩
private theorem pr155219 : PrimeCertificate 155219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11087]) (by decide +kernel)
def pv155219 : PrimeValue := ⟨155219, pr155219⟩
private theorem pr155231 : PrimeCertificate 155231 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv19,pv43]) (by decide +kernel)
def pv155231 : PrimeValue := ⟨155231, pr155231⟩
private theorem pr155251 : PrimeCertificate 155251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv155251 : PrimeValue := ⟨155251, pr155251⟩
private theorem pr155269 : PrimeCertificate 155269 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv19,pv227]) (by decide +kernel)
def pv155269 : PrimeValue := ⟨155269, pr155269⟩
private theorem pr155291 : PrimeCertificate 155291 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv53,pv293]) (by decide +kernel)
def pv155291 : PrimeValue := ⟨155291, pr155291⟩
private theorem pr155299 : PrimeCertificate 155299 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv181]) (by decide +kernel)
def pv155299 : PrimeValue := ⟨155299, pr155299⟩
private theorem pr155303 : PrimeCertificate 155303 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11093]) (by decide +kernel)
def pv155303 : PrimeValue := ⟨155303, pr155303⟩
private theorem pr155317 : PrimeCertificate 155317 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv155317 : PrimeValue := ⟨155317, pr155317⟩
private theorem pr155327 : PrimeCertificate 155327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv2099]) (by decide +kernel)
def pv155327 : PrimeValue := ⟨155327, pr155327⟩
private theorem pr155333 : PrimeCertificate 155333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38833]) (by decide +kernel)
def pv155333 : PrimeValue := ⟨155333, pr155333⟩
private theorem pr155371 : PrimeCertificate 155371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv5179]) (by decide +kernel)
def pv155371 : PrimeValue := ⟨155371, pr155371⟩
private theorem pr155377 : PrimeCertificate 155377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv83]) (by decide +kernel)
def pv155377 : PrimeValue := ⟨155377, pr155377⟩
private theorem pr155387 : PrimeCertificate 155387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv1009]) (by decide +kernel)
def pv155387 : PrimeValue := ⟨155387, pr155387⟩
private theorem pr155399 : PrimeCertificate 155399 :=
  certifyPrime (q := pv19) (ls := [pv2,pv77699]) (by decide +kernel)
def pv155399 : PrimeValue := ⟨155399, pr155399⟩
private theorem pr155423 : PrimeCertificate 155423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv77711]) (by decide +kernel)
def pv155423 : PrimeValue := ⟨155423, pr155423⟩
private theorem pr155461 : PrimeCertificate 155461 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2591]) (by decide +kernel)
def pv155461 : PrimeValue := ⟨155461, pr155461⟩
private theorem pr155473 : PrimeCertificate 155473 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv41,pv79]) (by decide +kernel)
def pv155473 : PrimeValue := ⟨155473, pr155473⟩
private theorem pr155509 : PrimeCertificate 155509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12959]) (by decide +kernel)
def pv155509 : PrimeValue := ⟨155509, pr155509⟩
private theorem pr155537 : PrimeCertificate 155537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9721]) (by decide +kernel)
def pv155537 : PrimeValue := ⟨155537, pr155537⟩
private theorem pr155539 : PrimeCertificate 155539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8641]) (by decide +kernel)
def pv155539 : PrimeValue := ⟨155539, pr155539⟩
private theorem pr155557 : PrimeCertificate 155557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv149]) (by decide +kernel)
def pv155557 : PrimeValue := ⟨155557, pr155557⟩
private theorem pr155569 : PrimeCertificate 155569 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv463]) (by decide +kernel)
def pv155569 : PrimeValue := ⟨155569, pr155569⟩
private theorem pr155581 : PrimeCertificate 155581 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2593]) (by decide +kernel)
def pv155581 : PrimeValue := ⟨155581, pr155581⟩
private theorem pr155593 : PrimeCertificate 155593 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv2161]) (by decide +kernel)
def pv155593 : PrimeValue := ⟨155593, pr155593⟩
private theorem pr155599 : PrimeCertificate 155599 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv25933]) (by decide +kernel)
def pv155599 : PrimeValue := ⟨155599, pr155599⟩
private theorem pr155621 : PrimeCertificate 155621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv251]) (by decide +kernel)
def pv155621 : PrimeValue := ⟨155621, pr155621⟩
private theorem pr155627 : PrimeCertificate 155627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv77813]) (by decide +kernel)
def pv155627 : PrimeValue := ⟨155627, pr155627⟩
private theorem pr155653 : PrimeCertificate 155653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv109]) (by decide +kernel)
def pv155653 : PrimeValue := ⟨155653, pr155653⟩
private theorem pr155657 : PrimeCertificate 155657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19457]) (by decide +kernel)
def pv155657 : PrimeValue := ⟨155657, pr155657⟩
private theorem pr155663 : PrimeCertificate 155663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv5987]) (by decide +kernel)
def pv155663 : PrimeValue := ⟨155663, pr155663⟩
private theorem pr155671 : PrimeCertificate 155671 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv5189]) (by decide +kernel)
def pv155671 : PrimeValue := ⟨155671, pr155671⟩
private theorem pr155689 : PrimeCertificate 155689 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv499]) (by decide +kernel)
def pv155689 : PrimeValue := ⟨155689, pr155689⟩
private theorem pr155693 : PrimeCertificate 155693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38923]) (by decide +kernel)
def pv155693 : PrimeValue := ⟨155693, pr155693⟩
private theorem pr155699 : PrimeCertificate 155699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv77849]) (by decide +kernel)
def pv155699 : PrimeValue := ⟨155699, pr155699⟩
private theorem pr155707 : PrimeCertificate 155707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25951]) (by decide +kernel)
def pv155707 : PrimeValue := ⟨155707, pr155707⟩
private theorem pr155717 : PrimeCertificate 155717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv3539]) (by decide +kernel)
def pv155717 : PrimeValue := ⟨155717, pr155717⟩
private theorem pr155723 : PrimeCertificate 155723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv227]) (by decide +kernel)
def pv155723 : PrimeValue := ⟨155723, pr155723⟩
private theorem pr155731 : PrimeCertificate 155731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv179]) (by decide +kernel)
def pv155731 : PrimeValue := ⟨155731, pr155731⟩
private theorem pr155741 : PrimeCertificate 155741 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv13,pv599]) (by decide +kernel)
def pv155741 : PrimeValue := ⟨155741, pr155741⟩
private theorem pr155773 : PrimeCertificate 155773 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4327]) (by decide +kernel)
def pv155773 : PrimeValue := ⟨155773, pr155773⟩
private theorem pr155783 : PrimeCertificate 155783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv73,pv97]) (by decide +kernel)
def pv155783 : PrimeValue := ⟨155783, pr155783⟩
private theorem pr155801 : PrimeCertificate 155801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv41]) (by decide +kernel)
def pv155801 : PrimeValue := ⟨155801, pr155801⟩
private theorem pr155809 : PrimeCertificate 155809 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv541]) (by decide +kernel)
def pv155809 : PrimeValue := ⟨155809, pr155809⟩
private theorem pr155821 : PrimeCertificate 155821 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv53]) (by decide +kernel)
def pv155821 : PrimeValue := ⟨155821, pr155821⟩
private theorem pr155833 : PrimeCertificate 155833 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv43,pv151]) (by decide +kernel)
def pv155833 : PrimeValue := ⟨155833, pr155833⟩
private theorem pr155851 : PrimeCertificate 155851 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv1039]) (by decide +kernel)
def pv155851 : PrimeValue := ⟨155851, pr155851⟩
private theorem pr155861 : PrimeCertificate 155861 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7793]) (by decide +kernel)
def pv155861 : PrimeValue := ⟨155861, pr155861⟩
private theorem pr155863 : PrimeCertificate 155863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1237]) (by decide +kernel)
def pv155863 : PrimeValue := ⟨155863, pr155863⟩
private theorem pr155887 : PrimeCertificate 155887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25981]) (by decide +kernel)
def pv155887 : PrimeValue := ⟨155887, pr155887⟩
private theorem pr155893 : PrimeCertificate 155893 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1181]) (by decide +kernel)
def pv155893 : PrimeValue := ⟨155893, pr155893⟩
private theorem pr156011 : PrimeCertificate 156011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv15601]) (by decide +kernel)
def pv156011 : PrimeValue := ⟨156011, pr156011⟩
private theorem pr156019 : PrimeCertificate 156019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv26003]) (by decide +kernel)
def pv156019 : PrimeValue := ⟨156019, pr156019⟩
private theorem pr156041 : PrimeCertificate 156041 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv47,pv83]) (by decide +kernel)
def pv156041 : PrimeValue := ⟨156041, pr156041⟩
private theorem pr156059 : PrimeCertificate 156059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv71,pv157]) (by decide +kernel)
def pv156059 : PrimeValue := ⟨156059, pr156059⟩
private theorem pr156061 : PrimeCertificate 156061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv156061 : PrimeValue := ⟨156061, pr156061⟩
private theorem pr156089 : PrimeCertificate 156089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv109,pv179]) (by decide +kernel)
def pv156089 : PrimeValue := ⟨156089, pr156089⟩
private theorem pr156109 : PrimeCertificate 156109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13009]) (by decide +kernel)
def pv156109 : PrimeValue := ⟨156109, pr156109⟩
private theorem pr156119 : PrimeCertificate 156119 :=
  certifyPrime (q := pv13) (ls := [pv2,pv78059]) (by decide +kernel)
def pv156119 : PrimeValue := ⟨156119, pr156119⟩
private theorem pr156127 : PrimeCertificate 156127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv26021]) (by decide +kernel)
def pv156127 : PrimeValue := ⟨156127, pr156127⟩
private theorem pr156131 : PrimeCertificate 156131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv1201]) (by decide +kernel)
def pv156131 : PrimeValue := ⟨156131, pr156131⟩
private theorem pr156139 : PrimeCertificate 156139 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv53,pv491]) (by decide +kernel)
def pv156139 : PrimeValue := ⟨156139, pr156139⟩
private theorem pr156151 : PrimeCertificate 156151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv347]) (by decide +kernel)
def pv156151 : PrimeValue := ⟨156151, pr156151⟩
private theorem pr156157 : PrimeCertificate 156157 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv13]) (by decide +kernel)
def pv156157 : PrimeValue := ⟨156157, pr156157⟩
private theorem pr156227 : PrimeCertificate 156227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11159]) (by decide +kernel)
def pv156227 : PrimeValue := ⟨156227, pr156227⟩
private theorem pr156229 : PrimeCertificate 156229 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv47,pv277]) (by decide +kernel)
def pv156229 : PrimeValue := ⟨156229, pr156229⟩
private theorem pr156241 : PrimeCertificate 156241 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv156241 : PrimeValue := ⟨156241, pr156241⟩
private theorem pr156253 : PrimeCertificate 156253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv449]) (by decide +kernel)
def pv156253 : PrimeValue := ⟨156253, pr156253⟩
private theorem pr156257 : PrimeCertificate 156257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv257]) (by decide +kernel)
def pv156257 : PrimeValue := ⟨156257, pr156257⟩
private theorem pr156259 : PrimeCertificate 156259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8681]) (by decide +kernel)
def pv156259 : PrimeValue := ⟨156259, pr156259⟩
private theorem pr156269 : PrimeCertificate 156269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv5581]) (by decide +kernel)
def pv156269 : PrimeValue := ⟨156269, pr156269⟩
private theorem pr156329 : PrimeCertificate 156329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19541]) (by decide +kernel)
def pv156329 : PrimeValue := ⟨156329, pr156329⟩
private theorem pr156347 : PrimeCertificate 156347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv78173]) (by decide +kernel)
def pv156347 : PrimeValue := ⟨156347, pr156347⟩
private theorem pr156361 : PrimeCertificate 156361 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv1303]) (by decide +kernel)
def pv156361 : PrimeValue := ⟨156361, pr156361⟩
private theorem pr156371 : PrimeCertificate 156371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv823]) (by decide +kernel)
def pv156371 : PrimeValue := ⟨156371, pr156371⟩
private theorem pr156419 : PrimeCertificate 156419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197,pv397]) (by decide +kernel)
def pv156419 : PrimeValue := ⟨156419, pr156419⟩
private theorem pr156467 : PrimeCertificate 156467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv78233]) (by decide +kernel)
def pv156467 : PrimeValue := ⟨156467, pr156467⟩
private theorem pr156487 : PrimeCertificate 156487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2371]) (by decide +kernel)
def pv156487 : PrimeValue := ⟨156487, pr156487⟩
private theorem pr156491 : PrimeCertificate 156491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv15649]) (by decide +kernel)
def pv156491 : PrimeValue := ⟨156491, pr156491⟩
private theorem pr156493 : PrimeCertificate 156493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv156493 : PrimeValue := ⟨156493, pr156493⟩
private theorem pr156511 : PrimeCertificate 156511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv37,pv47]) (by decide +kernel)
def pv156511 : PrimeValue := ⟨156511, pr156511⟩
private theorem pr156589 : PrimeCertificate 156589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13049]) (by decide +kernel)
def pv156589 : PrimeValue := ⟨156589, pr156589⟩
private theorem pr156593 : PrimeCertificate 156593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9787]) (by decide +kernel)
def pv156593 : PrimeValue := ⟨156593, pr156593⟩
private theorem pr156619 : PrimeCertificate 156619 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv11,pv113]) (by decide +kernel)
def pv156619 : PrimeValue := ⟨156619, pr156619⟩
private theorem pr156623 : PrimeCertificate 156623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv78311]) (by decide +kernel)
def pv156623 : PrimeValue := ⟨156623, pr156623⟩
private theorem pr156641 : PrimeCertificate 156641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv89]) (by decide +kernel)
def pv156641 : PrimeValue := ⟨156641, pr156641⟩
private theorem pr156659 : PrimeCertificate 156659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv37,pv73]) (by decide +kernel)
def pv156659 : PrimeValue := ⟨156659, pr156659⟩
private theorem pr156671 : PrimeCertificate 156671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv15667]) (by decide +kernel)
def pv156671 : PrimeValue := ⟨156671, pr156671⟩
private theorem pr156677 : PrimeCertificate 156677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv131]) (by decide +kernel)
def pv156677 : PrimeValue := ⟨156677, pr156677⟩
private theorem pr156679 : PrimeCertificate 156679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv26113]) (by decide +kernel)
def pv156679 : PrimeValue := ⟨156679, pr156679⟩
private theorem pr156691 : PrimeCertificate 156691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1741]) (by decide +kernel)
def pv156691 : PrimeValue := ⟨156691, pr156691⟩
private theorem pr156703 : PrimeCertificate 156703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv41]) (by decide +kernel)
def pv156703 : PrimeValue := ⟨156703, pr156703⟩
private theorem pr156719 : PrimeCertificate 156719 :=
  certifyPrime (q := pv19) (ls := [pv2,pv127,pv617]) (by decide +kernel)
def pv156719 : PrimeValue := ⟨156719, pr156719⟩
private theorem pr156727 : PrimeCertificate 156727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv8707]) (by decide +kernel)
def pv156727 : PrimeValue := ⟨156727, pr156727⟩
private theorem pr156733 : PrimeCertificate 156733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv353]) (by decide +kernel)
def pv156733 : PrimeValue := ⟨156733, pr156733⟩
private theorem pr156749 : PrimeCertificate 156749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv149,pv263]) (by decide +kernel)
def pv156749 : PrimeValue := ⟨156749, pr156749⟩
private theorem pr156797 : PrimeCertificate 156797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv39199]) (by decide +kernel)
def pv156797 : PrimeValue := ⟨156797, pr156797⟩
private theorem pr156799 : PrimeCertificate 156799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv281]) (by decide +kernel)
def pv156799 : PrimeValue := ⟨156799, pr156799⟩
private theorem pr156817 : PrimeCertificate 156817 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv156817 : PrimeValue := ⟨156817, pr156817⟩
private theorem pr156823 : PrimeCertificate 156823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv443]) (by decide +kernel)
def pv156823 : PrimeValue := ⟨156823, pr156823⟩
private theorem pr156887 : PrimeCertificate 156887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv47,pv1669]) (by decide +kernel)
def pv156887 : PrimeValue := ⟨156887, pr156887⟩
private theorem pr156901 : PrimeCertificate 156901 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv523]) (by decide +kernel)
def pv156901 : PrimeValue := ⟨156901, pr156901⟩
private theorem pr156913 : PrimeCertificate 156913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv467]) (by decide +kernel)
def pv156913 : PrimeValue := ⟨156913, pr156913⟩
private theorem pr156941 : PrimeCertificate 156941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv59]) (by decide +kernel)
def pv156941 : PrimeValue := ⟨156941, pr156941⟩
private theorem pr156943 : PrimeCertificate 156943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv8719]) (by decide +kernel)
def pv156943 : PrimeValue := ⟨156943, pr156943⟩
private theorem pr156967 : PrimeCertificate 156967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv26161]) (by decide +kernel)
def pv156967 : PrimeValue := ⟨156967, pr156967⟩
private theorem pr156971 : PrimeCertificate 156971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1427]) (by decide +kernel)
def pv156971 : PrimeValue := ⟨156971, pr156971⟩
private theorem pr157007 : PrimeCertificate 157007 :=
  certifyPrime (q := pv11) (ls := [pv2,pv29,pv2707]) (by decide +kernel)
def pv157007 : PrimeValue := ⟨157007, pr157007⟩
private theorem pr157013 : PrimeCertificate 157013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2309]) (by decide +kernel)
def pv157013 : PrimeValue := ⟨157013, pr157013⟩
private theorem pr157037 : PrimeCertificate 157037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv43,pv83]) (by decide +kernel)
def pv157037 : PrimeValue := ⟨157037, pr157037⟩
private theorem pr157049 : PrimeCertificate 157049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv293]) (by decide +kernel)
def pv157049 : PrimeValue := ⟨157049, pr157049⟩
private theorem pr157051 : PrimeCertificate 157051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv349]) (by decide +kernel)
def pv157051 : PrimeValue := ⟨157051, pr157051⟩
private theorem pr157061 : PrimeCertificate 157061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7853]) (by decide +kernel)
def pv157061 : PrimeValue := ⟨157061, pr157061⟩
private theorem pr157081 : PrimeCertificate 157081 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv11,pv17]) (by decide +kernel)
def pv157081 : PrimeValue := ⟨157081, pr157081⟩
private theorem pr157109 : PrimeCertificate 157109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv181]) (by decide +kernel)
def pv157109 : PrimeValue := ⟨157109, pr157109⟩
private theorem pr157127 : PrimeCertificate 157127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv251,pv313]) (by decide +kernel)
def pv157127 : PrimeValue := ⟨157127, pr157127⟩
private theorem pr157133 : PrimeCertificate 157133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163,pv241]) (by decide +kernel)
def pv157133 : PrimeValue := ⟨157133, pr157133⟩
private theorem pr157141 : PrimeCertificate 157141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv97]) (by decide +kernel)
def pv157141 : PrimeValue := ⟨157141, pr157141⟩
private theorem pr157163 : PrimeCertificate 157163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179,pv439]) (by decide +kernel)
def pv157163 : PrimeValue := ⟨157163, pr157163⟩
private theorem pr157177 : PrimeCertificate 157177 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv37,pv59]) (by decide +kernel)
def pv157177 : PrimeValue := ⟨157177, pr157177⟩
private theorem pr157181 : PrimeCertificate 157181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv271]) (by decide +kernel)
def pv157181 : PrimeValue := ⟨157181, pr157181⟩
private theorem pr157189 : PrimeCertificate 157189 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13099]) (by decide +kernel)
def pv157189 : PrimeValue := ⟨157189, pr157189⟩
private theorem pr157207 : PrimeCertificate 157207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv197]) (by decide +kernel)
def pv157207 : PrimeValue := ⟨157207, pr157207⟩
private theorem pr157211 : PrimeCertificate 157211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv79,pv199]) (by decide +kernel)
def pv157211 : PrimeValue := ⟨157211, pr157211⟩
private theorem pr157217 : PrimeCertificate 157217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17]) (by decide +kernel)
def pv157217 : PrimeValue := ⟨157217, pr157217⟩
private theorem pr157219 : PrimeCertificate 157219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv26203]) (by decide +kernel)
def pv157219 : PrimeValue := ⟨157219, pr157219⟩
private theorem pr157229 : PrimeCertificate 157229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv1709]) (by decide +kernel)
def pv157229 : PrimeValue := ⟨157229, pr157229⟩
private theorem pr157231 : PrimeCertificate 157231 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1747]) (by decide +kernel)
def pv157231 : PrimeValue := ⟨157231, pr157231⟩
private theorem pr157243 : PrimeCertificate 157243 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73,pv359]) (by decide +kernel)
def pv157243 : PrimeValue := ⟨157243, pr157243⟩
private theorem pr157247 : PrimeCertificate 157247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv78623]) (by decide +kernel)
def pv157247 : PrimeValue := ⟨157247, pr157247⟩
private theorem pr157253 : PrimeCertificate 157253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv39313]) (by decide +kernel)
def pv157253 : PrimeValue := ⟨157253, pr157253⟩
private theorem pr157259 : PrimeCertificate 157259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv1289]) (by decide +kernel)
def pv157259 : PrimeValue := ⟨157259, pr157259⟩
private theorem pr157271 : PrimeCertificate 157271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv15727]) (by decide +kernel)
def pv157271 : PrimeValue := ⟨157271, pr157271⟩
private theorem pr157273 : PrimeCertificate 157273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6553]) (by decide +kernel)
def pv157273 : PrimeValue := ⟨157273, pr157273⟩
private theorem pr157277 : PrimeCertificate 157277 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv41,pv137]) (by decide +kernel)
def pv157277 : PrimeValue := ⟨157277, pr157277⟩
private theorem pr157279 : PrimeCertificate 157279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2383]) (by decide +kernel)
def pv157279 : PrimeValue := ⟨157279, pr157279⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
