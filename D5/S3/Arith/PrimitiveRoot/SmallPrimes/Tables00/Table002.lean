/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table002
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table002.pv3581
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table001

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr3581 : PrimeCertificate 3581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv179]) (by decide +kernel)
def pv3581 : PrimeValue := ⟨3581, pr3581⟩
private theorem pr3583 : PrimeCertificate 3583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv199]) (by decide +kernel)
def pv3583 : PrimeValue := ⟨3583, pr3583⟩
private theorem pr3593 : PrimeCertificate 3593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv449]) (by decide +kernel)
def pv3593 : PrimeValue := ⟨3593, pr3593⟩
private theorem pr3607 : PrimeCertificate 3607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv601]) (by decide +kernel)
def pv3607 : PrimeValue := ⟨3607, pr3607⟩
private theorem pr3613 : PrimeCertificate 3613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv3613 : PrimeValue := ⟨3613, pr3613⟩
private theorem pr3617 : PrimeCertificate 3617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv113]) (by decide +kernel)
def pv3617 : PrimeValue := ⟨3617, pr3617⟩
private theorem pr3623 : PrimeCertificate 3623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv1811]) (by decide +kernel)
def pv3623 : PrimeValue := ⟨3623, pr3623⟩
private theorem pr3631 : PrimeCertificate 3631 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv3631 : PrimeValue := ⟨3631, pr3631⟩
private theorem pr3637 : PrimeCertificate 3637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv3637 : PrimeValue := ⟨3637, pr3637⟩
private theorem pr3643 : PrimeCertificate 3643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv607]) (by decide +kernel)
def pv3643 : PrimeValue := ⟨3643, pr3643⟩
private theorem pr3659 : PrimeCertificate 3659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv59]) (by decide +kernel)
def pv3659 : PrimeValue := ⟨3659, pr3659⟩
private theorem pr3671 : PrimeCertificate 3671 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv367]) (by decide +kernel)
def pv3671 : PrimeValue := ⟨3671, pr3671⟩
private theorem pr3673 : PrimeCertificate 3673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv3673 : PrimeValue := ⟨3673, pr3673⟩
private theorem pr3677 : PrimeCertificate 3677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv919]) (by decide +kernel)
def pv3677 : PrimeValue := ⟨3677, pr3677⟩
private theorem pr3691 : PrimeCertificate 3691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv3691 : PrimeValue := ⟨3691, pr3691⟩
private theorem pr3697 : PrimeCertificate 3697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv3697 : PrimeValue := ⟨3697, pr3697⟩
private theorem pr3701 : PrimeCertificate 3701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37]) (by decide +kernel)
def pv3701 : PrimeValue := ⟨3701, pr3701⟩
private theorem pr3709 : PrimeCertificate 3709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv3709 : PrimeValue := ⟨3709, pr3709⟩
private theorem pr3719 : PrimeCertificate 3719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv13]) (by decide +kernel)
def pv3719 : PrimeValue := ⟨3719, pr3719⟩
private theorem pr3727 : PrimeCertificate 3727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv3727 : PrimeValue := ⟨3727, pr3727⟩
private theorem pr3733 : PrimeCertificate 3733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv311]) (by decide +kernel)
def pv3733 : PrimeValue := ⟨3733, pr3733⟩
private theorem pr3739 : PrimeCertificate 3739 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv89]) (by decide +kernel)
def pv3739 : PrimeValue := ⟨3739, pr3739⟩
private theorem pr3761 : PrimeCertificate 3761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47]) (by decide +kernel)
def pv3761 : PrimeValue := ⟨3761, pr3761⟩
private theorem pr3767 : PrimeCertificate 3767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv269]) (by decide +kernel)
def pv3767 : PrimeValue := ⟨3767, pr3767⟩
private theorem pr3769 : PrimeCertificate 3769 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv157]) (by decide +kernel)
def pv3769 : PrimeValue := ⟨3769, pr3769⟩
private theorem pr3779 : PrimeCertificate 3779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1889]) (by decide +kernel)
def pv3779 : PrimeValue := ⟨3779, pr3779⟩
private theorem pr3793 : PrimeCertificate 3793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv3793 : PrimeValue := ⟨3793, pr3793⟩
private theorem pr3797 : PrimeCertificate 3797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv73]) (by decide +kernel)
def pv3797 : PrimeValue := ⟨3797, pr3797⟩
private theorem pr3803 : PrimeCertificate 3803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1901]) (by decide +kernel)
def pv3803 : PrimeValue := ⟨3803, pr3803⟩
private theorem pr3821 : PrimeCertificate 3821 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv191]) (by decide +kernel)
def pv3821 : PrimeValue := ⟨3821, pr3821⟩
private theorem pr3823 : PrimeCertificate 3823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv3823 : PrimeValue := ⟨3823, pr3823⟩
private theorem pr3833 : PrimeCertificate 3833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv479]) (by decide +kernel)
def pv3833 : PrimeValue := ⟨3833, pr3833⟩
private theorem pr3847 : PrimeCertificate 3847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv641]) (by decide +kernel)
def pv3847 : PrimeValue := ⟨3847, pr3847⟩
private theorem pr3851 : PrimeCertificate 3851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11]) (by decide +kernel)
def pv3851 : PrimeValue := ⟨3851, pr3851⟩
private theorem pr3853 : PrimeCertificate 3853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv3853 : PrimeValue := ⟨3853, pr3853⟩
private theorem pr3863 : PrimeCertificate 3863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv1931]) (by decide +kernel)
def pv3863 : PrimeValue := ⟨3863, pr3863⟩
private theorem pr3877 : PrimeCertificate 3877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv19]) (by decide +kernel)
def pv3877 : PrimeValue := ⟨3877, pr3877⟩
private theorem pr3881 : PrimeCertificate 3881 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv97]) (by decide +kernel)
def pv3881 : PrimeValue := ⟨3881, pr3881⟩
private theorem pr3889 : PrimeCertificate 3889 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3]) (by decide +kernel)
def pv3889 : PrimeValue := ⟨3889, pr3889⟩
private theorem pr3907 : PrimeCertificate 3907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv3907 : PrimeValue := ⟨3907, pr3907⟩
private theorem pr3911 : PrimeCertificate 3911 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv23]) (by decide +kernel)
def pv3911 : PrimeValue := ⟨3911, pr3911⟩
private theorem pr3917 : PrimeCertificate 3917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv89]) (by decide +kernel)
def pv3917 : PrimeValue := ⟨3917, pr3917⟩
private theorem pr3919 : PrimeCertificate 3919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv653]) (by decide +kernel)
def pv3919 : PrimeValue := ⟨3919, pr3919⟩
private theorem pr3923 : PrimeCertificate 3923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv53]) (by decide +kernel)
def pv3923 : PrimeValue := ⟨3923, pr3923⟩
private theorem pr3929 : PrimeCertificate 3929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv491]) (by decide +kernel)
def pv3929 : PrimeValue := ⟨3929, pr3929⟩
private theorem pr3931 : PrimeCertificate 3931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv131]) (by decide +kernel)
def pv3931 : PrimeValue := ⟨3931, pr3931⟩
private theorem pr3943 : PrimeCertificate 3943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv3943 : PrimeValue := ⟨3943, pr3943⟩
private theorem pr3947 : PrimeCertificate 3947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1973]) (by decide +kernel)
def pv3947 : PrimeValue := ⟨3947, pr3947⟩
private theorem pr3967 : PrimeCertificate 3967 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv661]) (by decide +kernel)
def pv3967 : PrimeValue := ⟨3967, pr3967⟩
private theorem pr3989 : PrimeCertificate 3989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv997]) (by decide +kernel)
def pv3989 : PrimeValue := ⟨3989, pr3989⟩
private theorem pr4001 : PrimeCertificate 4001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5]) (by decide +kernel)
def pv4001 : PrimeValue := ⟨4001, pr4001⟩
private theorem pr4003 : PrimeCertificate 4003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv29]) (by decide +kernel)
def pv4003 : PrimeValue := ⟨4003, pr4003⟩
private theorem pr4007 : PrimeCertificate 4007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv2003]) (by decide +kernel)
def pv4007 : PrimeValue := ⟨4007, pr4007⟩
private theorem pr4013 : PrimeCertificate 4013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv59]) (by decide +kernel)
def pv4013 : PrimeValue := ⟨4013, pr4013⟩
private theorem pr4019 : PrimeCertificate 4019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv41]) (by decide +kernel)
def pv4019 : PrimeValue := ⟨4019, pr4019⟩
private theorem pr4021 : PrimeCertificate 4021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv67]) (by decide +kernel)
def pv4021 : PrimeValue := ⟨4021, pr4021⟩
private theorem pr4027 : PrimeCertificate 4027 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv61]) (by decide +kernel)
def pv4027 : PrimeValue := ⟨4027, pr4027⟩
private theorem pr4049 : PrimeCertificate 4049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv23]) (by decide +kernel)
def pv4049 : PrimeValue := ⟨4049, pr4049⟩
private theorem pr4051 : PrimeCertificate 4051 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv4051 : PrimeValue := ⟨4051, pr4051⟩
private theorem pr4057 : PrimeCertificate 4057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv4057 : PrimeValue := ⟨4057, pr4057⟩
private theorem pr4073 : PrimeCertificate 4073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv509]) (by decide +kernel)
def pv4073 : PrimeValue := ⟨4073, pr4073⟩
private theorem pr4079 : PrimeCertificate 4079 :=
  certifyPrime (q := pv11) (ls := [pv2,pv2039]) (by decide +kernel)
def pv4079 : PrimeValue := ⟨4079, pr4079⟩
private theorem pr4091 : PrimeCertificate 4091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv409]) (by decide +kernel)
def pv4091 : PrimeValue := ⟨4091, pr4091⟩
private theorem pr4093 : PrimeCertificate 4093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv31]) (by decide +kernel)
def pv4093 : PrimeValue := ⟨4093, pr4093⟩
private theorem pr4099 : PrimeCertificate 4099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv683]) (by decide +kernel)
def pv4099 : PrimeValue := ⟨4099, pr4099⟩
private theorem pr4111 : PrimeCertificate 4111 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv137]) (by decide +kernel)
def pv4111 : PrimeValue := ⟨4111, pr4111⟩
private theorem pr4127 : PrimeCertificate 4127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv2063]) (by decide +kernel)
def pv4127 : PrimeValue := ⟨4127, pr4127⟩
private theorem pr4129 : PrimeCertificate 4129 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv4129 : PrimeValue := ⟨4129, pr4129⟩
private theorem pr4133 : PrimeCertificate 4133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1033]) (by decide +kernel)
def pv4133 : PrimeValue := ⟨4133, pr4133⟩
private theorem pr4139 : PrimeCertificate 4139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2069]) (by decide +kernel)
def pv4139 : PrimeValue := ⟨4139, pr4139⟩
private theorem pr4153 : PrimeCertificate 4153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv173]) (by decide +kernel)
def pv4153 : PrimeValue := ⟨4153, pr4153⟩
private theorem pr4157 : PrimeCertificate 4157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1039]) (by decide +kernel)
def pv4157 : PrimeValue := ⟨4157, pr4157⟩
private theorem pr4159 : PrimeCertificate 4159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv4159 : PrimeValue := ⟨4159, pr4159⟩
private theorem pr4177 : PrimeCertificate 4177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv4177 : PrimeValue := ⟨4177, pr4177⟩
private theorem pr4201 : PrimeCertificate 4201 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv4201 : PrimeValue := ⟨4201, pr4201⟩
private theorem pr4211 : PrimeCertificate 4211 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv421]) (by decide +kernel)
def pv4211 : PrimeValue := ⟨4211, pr4211⟩
private theorem pr4217 : PrimeCertificate 4217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv31]) (by decide +kernel)
def pv4217 : PrimeValue := ⟨4217, pr4217⟩
private theorem pr4219 : PrimeCertificate 4219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv37]) (by decide +kernel)
def pv4219 : PrimeValue := ⟨4219, pr4219⟩
private theorem pr4229 : PrimeCertificate 4229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv151]) (by decide +kernel)
def pv4229 : PrimeValue := ⟨4229, pr4229⟩
private theorem pr4231 : PrimeCertificate 4231 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv4231 : PrimeValue := ⟨4231, pr4231⟩
private theorem pr4241 : PrimeCertificate 4241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv53]) (by decide +kernel)
def pv4241 : PrimeValue := ⟨4241, pr4241⟩
private theorem pr4243 : PrimeCertificate 4243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv101]) (by decide +kernel)
def pv4243 : PrimeValue := ⟨4243, pr4243⟩
private theorem pr4253 : PrimeCertificate 4253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1063]) (by decide +kernel)
def pv4253 : PrimeValue := ⟨4253, pr4253⟩
private theorem pr4259 : PrimeCertificate 4259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2129]) (by decide +kernel)
def pv4259 : PrimeValue := ⟨4259, pr4259⟩
private theorem pr4261 : PrimeCertificate 4261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv4261 : PrimeValue := ⟨4261, pr4261⟩
private theorem pr4271 : PrimeCertificate 4271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv61]) (by decide +kernel)
def pv4271 : PrimeValue := ⟨4271, pr4271⟩
private theorem pr4273 : PrimeCertificate 4273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv89]) (by decide +kernel)
def pv4273 : PrimeValue := ⟨4273, pr4273⟩
private theorem pr4283 : PrimeCertificate 4283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2141]) (by decide +kernel)
def pv4283 : PrimeValue := ⟨4283, pr4283⟩
private theorem pr4289 : PrimeCertificate 4289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67]) (by decide +kernel)
def pv4289 : PrimeValue := ⟨4289, pr4289⟩
private theorem pr4297 : PrimeCertificate 4297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv179]) (by decide +kernel)
def pv4297 : PrimeValue := ⟨4297, pr4297⟩
private theorem pr4327 : PrimeCertificate 4327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv103]) (by decide +kernel)
def pv4327 : PrimeValue := ⟨4327, pr4327⟩
private theorem pr4337 : PrimeCertificate 4337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv271]) (by decide +kernel)
def pv4337 : PrimeValue := ⟨4337, pr4337⟩
private theorem pr4339 : PrimeCertificate 4339 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv241]) (by decide +kernel)
def pv4339 : PrimeValue := ⟨4339, pr4339⟩
private theorem pr4349 : PrimeCertificate 4349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1087]) (by decide +kernel)
def pv4349 : PrimeValue := ⟨4349, pr4349⟩
private theorem pr4357 : PrimeCertificate 4357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv4357 : PrimeValue := ⟨4357, pr4357⟩
private theorem pr4363 : PrimeCertificate 4363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv727]) (by decide +kernel)
def pv4363 : PrimeValue := ⟨4363, pr4363⟩
private theorem pr4373 : PrimeCertificate 4373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1093]) (by decide +kernel)
def pv4373 : PrimeValue := ⟨4373, pr4373⟩
private theorem pr4391 : PrimeCertificate 4391 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv439]) (by decide +kernel)
def pv4391 : PrimeValue := ⟨4391, pr4391⟩
private theorem pr4397 : PrimeCertificate 4397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv157]) (by decide +kernel)
def pv4397 : PrimeValue := ⟨4397, pr4397⟩
private theorem pr4409 : PrimeCertificate 4409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv29]) (by decide +kernel)
def pv4409 : PrimeValue := ⟨4409, pr4409⟩
private theorem pr4421 : PrimeCertificate 4421 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv17]) (by decide +kernel)
def pv4421 : PrimeValue := ⟨4421, pr4421⟩
private theorem pr4423 : PrimeCertificate 4423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv67]) (by decide +kernel)
def pv4423 : PrimeValue := ⟨4423, pr4423⟩
private theorem pr4441 : PrimeCertificate 4441 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv4441 : PrimeValue := ⟨4441, pr4441⟩
private theorem pr4447 : PrimeCertificate 4447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv4447 : PrimeValue := ⟨4447, pr4447⟩
private theorem pr4451 : PrimeCertificate 4451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv89]) (by decide +kernel)
def pv4451 : PrimeValue := ⟨4451, pr4451⟩
private theorem pr4457 : PrimeCertificate 4457 :=
  certifyPrime (q := pv3) (ls := [pv2,pv557]) (by decide +kernel)
def pv4457 : PrimeValue := ⟨4457, pr4457⟩
private theorem pr4463 : PrimeCertificate 4463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv97]) (by decide +kernel)
def pv4463 : PrimeValue := ⟨4463, pr4463⟩
private theorem pr4481 : PrimeCertificate 4481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv4481 : PrimeValue := ⟨4481, pr4481⟩
private theorem pr4483 : PrimeCertificate 4483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv4483 : PrimeValue := ⟨4483, pr4483⟩
private theorem pr4493 : PrimeCertificate 4493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1123]) (by decide +kernel)
def pv4493 : PrimeValue := ⟨4493, pr4493⟩
private theorem pr4507 : PrimeCertificate 4507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv751]) (by decide +kernel)
def pv4507 : PrimeValue := ⟨4507, pr4507⟩
private theorem pr4513 : PrimeCertificate 4513 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv4513 : PrimeValue := ⟨4513, pr4513⟩
private theorem pr4517 : PrimeCertificate 4517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1129]) (by decide +kernel)
def pv4517 : PrimeValue := ⟨4517, pr4517⟩
private theorem pr4519 : PrimeCertificate 4519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv251]) (by decide +kernel)
def pv4519 : PrimeValue := ⟨4519, pr4519⟩
private theorem pr4523 : PrimeCertificate 4523 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv17,pv19]) (by decide +kernel)
def pv4523 : PrimeValue := ⟨4523, pr4523⟩
private theorem pr4547 : PrimeCertificate 4547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2273]) (by decide +kernel)
def pv4547 : PrimeValue := ⟨4547, pr4547⟩
private theorem pr4549 : PrimeCertificate 4549 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv379]) (by decide +kernel)
def pv4549 : PrimeValue := ⟨4549, pr4549⟩
private theorem pr4561 : PrimeCertificate 4561 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv4561 : PrimeValue := ⟨4561, pr4561⟩
private theorem pr4567 : PrimeCertificate 4567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv761]) (by decide +kernel)
def pv4567 : PrimeValue := ⟨4567, pr4567⟩
private theorem pr4583 : PrimeCertificate 4583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv79]) (by decide +kernel)
def pv4583 : PrimeValue := ⟨4583, pr4583⟩
private theorem pr4591 : PrimeCertificate 4591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv4591 : PrimeValue := ⟨4591, pr4591⟩
private theorem pr4597 : PrimeCertificate 4597 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv383]) (by decide +kernel)
def pv4597 : PrimeValue := ⟨4597, pr4597⟩
private theorem pr4603 : PrimeCertificate 4603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv59]) (by decide +kernel)
def pv4603 : PrimeValue := ⟨4603, pr4603⟩
private theorem pr4621 : PrimeCertificate 4621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv4621 : PrimeValue := ⟨4621, pr4621⟩
private theorem pr4637 : PrimeCertificate 4637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv61]) (by decide +kernel)
def pv4637 : PrimeValue := ⟨4637, pr4637⟩
private theorem pr4639 : PrimeCertificate 4639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv773]) (by decide +kernel)
def pv4639 : PrimeValue := ⟨4639, pr4639⟩
private theorem pr4643 : PrimeCertificate 4643 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv211]) (by decide +kernel)
def pv4643 : PrimeValue := ⟨4643, pr4643⟩
private theorem pr4649 : PrimeCertificate 4649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv83]) (by decide +kernel)
def pv4649 : PrimeValue := ⟨4649, pr4649⟩
private theorem pr4651 : PrimeCertificate 4651 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv4651 : PrimeValue := ⟨4651, pr4651⟩
private theorem pr4657 : PrimeCertificate 4657 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv97]) (by decide +kernel)
def pv4657 : PrimeValue := ⟨4657, pr4657⟩
private theorem pr4663 : PrimeCertificate 4663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv4663 : PrimeValue := ⟨4663, pr4663⟩
private theorem pr4673 : PrimeCertificate 4673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73]) (by decide +kernel)
def pv4673 : PrimeValue := ⟨4673, pr4673⟩
private theorem pr4679 : PrimeCertificate 4679 :=
  certifyPrime (q := pv11) (ls := [pv2,pv2339]) (by decide +kernel)
def pv4679 : PrimeValue := ⟨4679, pr4679⟩
private theorem pr4691 : PrimeCertificate 4691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv67]) (by decide +kernel)
def pv4691 : PrimeValue := ⟨4691, pr4691⟩
private theorem pr4703 : PrimeCertificate 4703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv2351]) (by decide +kernel)
def pv4703 : PrimeValue := ⟨4703, pr4703⟩
private theorem pr4721 : PrimeCertificate 4721 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv59]) (by decide +kernel)
def pv4721 : PrimeValue := ⟨4721, pr4721⟩
private theorem pr4723 : PrimeCertificate 4723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv787]) (by decide +kernel)
def pv4723 : PrimeValue := ⟨4723, pr4723⟩
private theorem pr4729 : PrimeCertificate 4729 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv197]) (by decide +kernel)
def pv4729 : PrimeValue := ⟨4729, pr4729⟩
private theorem pr4733 : PrimeCertificate 4733 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13]) (by decide +kernel)
def pv4733 : PrimeValue := ⟨4733, pr4733⟩
private theorem pr4751 : PrimeCertificate 4751 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv4751 : PrimeValue := ⟨4751, pr4751⟩
private theorem pr4759 : PrimeCertificate 4759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv61]) (by decide +kernel)
def pv4759 : PrimeValue := ⟨4759, pr4759⟩
private theorem pr4783 : PrimeCertificate 4783 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv797]) (by decide +kernel)
def pv4783 : PrimeValue := ⟨4783, pr4783⟩
private theorem pr4787 : PrimeCertificate 4787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2393]) (by decide +kernel)
def pv4787 : PrimeValue := ⟨4787, pr4787⟩
private theorem pr4789 : PrimeCertificate 4789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv4789 : PrimeValue := ⟨4789, pr4789⟩
private theorem pr4793 : PrimeCertificate 4793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv599]) (by decide +kernel)
def pv4793 : PrimeValue := ⟨4793, pr4793⟩
private theorem pr4799 : PrimeCertificate 4799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv2399]) (by decide +kernel)
def pv4799 : PrimeValue := ⟨4799, pr4799⟩
private theorem pr4801 : PrimeCertificate 4801 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv4801 : PrimeValue := ⟨4801, pr4801⟩
private theorem pr4813 : PrimeCertificate 4813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv401]) (by decide +kernel)
def pv4813 : PrimeValue := ⟨4813, pr4813⟩
private theorem pr4817 : PrimeCertificate 4817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv43]) (by decide +kernel)
def pv4817 : PrimeValue := ⟨4817, pr4817⟩
private theorem pr4831 : PrimeCertificate 4831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv23]) (by decide +kernel)
def pv4831 : PrimeValue := ⟨4831, pr4831⟩
private theorem pr4861 : PrimeCertificate 4861 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv4861 : PrimeValue := ⟨4861, pr4861⟩
private theorem pr4871 : PrimeCertificate 4871 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv487]) (by decide +kernel)
def pv4871 : PrimeValue := ⟨4871, pr4871⟩
private theorem pr4877 : PrimeCertificate 4877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv53]) (by decide +kernel)
def pv4877 : PrimeValue := ⟨4877, pr4877⟩
private theorem pr4889 : PrimeCertificate 4889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv47]) (by decide +kernel)
def pv4889 : PrimeValue := ⟨4889, pr4889⟩
private theorem pr4903 : PrimeCertificate 4903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv43]) (by decide +kernel)
def pv4903 : PrimeValue := ⟨4903, pr4903⟩
private theorem pr4909 : PrimeCertificate 4909 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv409]) (by decide +kernel)
def pv4909 : PrimeValue := ⟨4909, pr4909⟩
private theorem pr4919 : PrimeCertificate 4919 :=
  certifyPrime (q := pv13) (ls := [pv2,pv2459]) (by decide +kernel)
def pv4919 : PrimeValue := ⟨4919, pr4919⟩
private theorem pr4931 : PrimeCertificate 4931 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv17,pv29]) (by decide +kernel)
def pv4931 : PrimeValue := ⟨4931, pr4931⟩
private theorem pr4933 : PrimeCertificate 4933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137]) (by decide +kernel)
def pv4933 : PrimeValue := ⟨4933, pr4933⟩
private theorem pr4937 : PrimeCertificate 4937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv617]) (by decide +kernel)
def pv4937 : PrimeValue := ⟨4937, pr4937⟩
private theorem pr4943 : PrimeCertificate 4943 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv353]) (by decide +kernel)
def pv4943 : PrimeValue := ⟨4943, pr4943⟩
private theorem pr4951 : PrimeCertificate 4951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv4951 : PrimeValue := ⟨4951, pr4951⟩
private theorem pr4957 : PrimeCertificate 4957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv59]) (by decide +kernel)
def pv4957 : PrimeValue := ⟨4957, pr4957⟩
private theorem pr4967 : PrimeCertificate 4967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv191]) (by decide +kernel)
def pv4967 : PrimeValue := ⟨4967, pr4967⟩
private theorem pr4969 : PrimeCertificate 4969 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv4969 : PrimeValue := ⟨4969, pr4969⟩
private theorem pr4973 : PrimeCertificate 4973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv113]) (by decide +kernel)
def pv4973 : PrimeValue := ⟨4973, pr4973⟩
private theorem pr4987 : PrimeCertificate 4987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv277]) (by decide +kernel)
def pv4987 : PrimeValue := ⟨4987, pr4987⟩
private theorem pr4993 : PrimeCertificate 4993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv4993 : PrimeValue := ⟨4993, pr4993⟩
private theorem pr4999 : PrimeCertificate 4999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv4999 : PrimeValue := ⟨4999, pr4999⟩
private theorem pr5003 : PrimeCertificate 5003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv61]) (by decide +kernel)
def pv5003 : PrimeValue := ⟨5003, pr5003⟩
private theorem pr5009 : PrimeCertificate 5009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv313]) (by decide +kernel)
def pv5009 : PrimeValue := ⟨5009, pr5009⟩
private theorem pr5011 : PrimeCertificate 5011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv167]) (by decide +kernel)
def pv5011 : PrimeValue := ⟨5011, pr5011⟩
private theorem pr5021 : PrimeCertificate 5021 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv251]) (by decide +kernel)
def pv5021 : PrimeValue := ⟨5021, pr5021⟩
private theorem pr5023 : PrimeCertificate 5023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv5023 : PrimeValue := ⟨5023, pr5023⟩
private theorem pr5039 : PrimeCertificate 5039 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv229]) (by decide +kernel)
def pv5039 : PrimeValue := ⟨5039, pr5039⟩
private theorem pr5051 : PrimeCertificate 5051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv101]) (by decide +kernel)
def pv5051 : PrimeValue := ⟨5051, pr5051⟩
private theorem pr5059 : PrimeCertificate 5059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv281]) (by decide +kernel)
def pv5059 : PrimeValue := ⟨5059, pr5059⟩
private theorem pr5077 : PrimeCertificate 5077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv5077 : PrimeValue := ⟨5077, pr5077⟩
private theorem pr5081 : PrimeCertificate 5081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv127]) (by decide +kernel)
def pv5081 : PrimeValue := ⟨5081, pr5081⟩
private theorem pr5087 : PrimeCertificate 5087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv2543]) (by decide +kernel)
def pv5087 : PrimeValue := ⟨5087, pr5087⟩
private theorem pr5099 : PrimeCertificate 5099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2549]) (by decide +kernel)
def pv5099 : PrimeValue := ⟨5099, pr5099⟩
private theorem pr5101 : PrimeCertificate 5101 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv5101 : PrimeValue := ⟨5101, pr5101⟩
private theorem pr5107 : PrimeCertificate 5107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv37]) (by decide +kernel)
def pv5107 : PrimeValue := ⟨5107, pr5107⟩
private theorem pr5113 : PrimeCertificate 5113 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv5113 : PrimeValue := ⟨5113, pr5113⟩
private theorem pr5119 : PrimeCertificate 5119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv853]) (by decide +kernel)
def pv5119 : PrimeValue := ⟨5119, pr5119⟩
private theorem pr5147 : PrimeCertificate 5147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv83]) (by decide +kernel)
def pv5147 : PrimeValue := ⟨5147, pr5147⟩
private theorem pr5153 : PrimeCertificate 5153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv23]) (by decide +kernel)
def pv5153 : PrimeValue := ⟨5153, pr5153⟩
private theorem pr5167 : PrimeCertificate 5167 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv41]) (by decide +kernel)
def pv5167 : PrimeValue := ⟨5167, pr5167⟩
private theorem pr5171 : PrimeCertificate 5171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv47]) (by decide +kernel)
def pv5171 : PrimeValue := ⟨5171, pr5171⟩
private theorem pr5179 : PrimeCertificate 5179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv863]) (by decide +kernel)
def pv5179 : PrimeValue := ⟨5179, pr5179⟩
private theorem pr5189 : PrimeCertificate 5189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1297]) (by decide +kernel)
def pv5189 : PrimeValue := ⟨5189, pr5189⟩
private theorem pr5197 : PrimeCertificate 5197 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv433]) (by decide +kernel)
def pv5197 : PrimeValue := ⟨5197, pr5197⟩
private theorem pr5209 : PrimeCertificate 5209 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv5209 : PrimeValue := ⟨5209, pr5209⟩
private theorem pr5227 : PrimeCertificate 5227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv67]) (by decide +kernel)
def pv5227 : PrimeValue := ⟨5227, pr5227⟩
private theorem pr5231 : PrimeCertificate 5231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv523]) (by decide +kernel)
def pv5231 : PrimeValue := ⟨5231, pr5231⟩
private theorem pr5233 : PrimeCertificate 5233 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv109]) (by decide +kernel)
def pv5233 : PrimeValue := ⟨5233, pr5233⟩
private theorem pr5237 : PrimeCertificate 5237 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv17]) (by decide +kernel)
def pv5237 : PrimeValue := ⟨5237, pr5237⟩
private theorem pr5261 : PrimeCertificate 5261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv263]) (by decide +kernel)
def pv5261 : PrimeValue := ⟨5261, pr5261⟩
private theorem pr5273 : PrimeCertificate 5273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv659]) (by decide +kernel)
def pv5273 : PrimeValue := ⟨5273, pr5273⟩
private theorem pr5279 : PrimeCertificate 5279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv29]) (by decide +kernel)
def pv5279 : PrimeValue := ⟨5279, pr5279⟩
private theorem pr5281 : PrimeCertificate 5281 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv5281 : PrimeValue := ⟨5281, pr5281⟩
private theorem pr5297 : PrimeCertificate 5297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv331]) (by decide +kernel)
def pv5297 : PrimeValue := ⟨5297, pr5297⟩
private theorem pr5303 : PrimeCertificate 5303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv241]) (by decide +kernel)
def pv5303 : PrimeValue := ⟨5303, pr5303⟩
private theorem pr5309 : PrimeCertificate 5309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1327]) (by decide +kernel)
def pv5309 : PrimeValue := ⟨5309, pr5309⟩
private theorem pr5323 : PrimeCertificate 5323 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv887]) (by decide +kernel)
def pv5323 : PrimeValue := ⟨5323, pr5323⟩
private theorem pr5333 : PrimeCertificate 5333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv43]) (by decide +kernel)
def pv5333 : PrimeValue := ⟨5333, pr5333⟩
private theorem pr5347 : PrimeCertificate 5347 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv5347 : PrimeValue := ⟨5347, pr5347⟩
private theorem pr5351 : PrimeCertificate 5351 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv107]) (by decide +kernel)
def pv5351 : PrimeValue := ⟨5351, pr5351⟩
private theorem pr5381 : PrimeCertificate 5381 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv269]) (by decide +kernel)
def pv5381 : PrimeValue := ⟨5381, pr5381⟩
private theorem pr5387 : PrimeCertificate 5387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2693]) (by decide +kernel)
def pv5387 : PrimeValue := ⟨5387, pr5387⟩
private theorem pr5393 : PrimeCertificate 5393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv337]) (by decide +kernel)
def pv5393 : PrimeValue := ⟨5393, pr5393⟩
private theorem pr5399 : PrimeCertificate 5399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv2699]) (by decide +kernel)
def pv5399 : PrimeValue := ⟨5399, pr5399⟩
private theorem pr5407 : PrimeCertificate 5407 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv53]) (by decide +kernel)
def pv5407 : PrimeValue := ⟨5407, pr5407⟩
private theorem pr5413 : PrimeCertificate 5413 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv41]) (by decide +kernel)
def pv5413 : PrimeValue := ⟨5413, pr5413⟩
private theorem pr5417 : PrimeCertificate 5417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv677]) (by decide +kernel)
def pv5417 : PrimeValue := ⟨5417, pr5417⟩
private theorem pr5419 : PrimeCertificate 5419 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv5419 : PrimeValue := ⟨5419, pr5419⟩
private theorem pr5431 : PrimeCertificate 5431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv181]) (by decide +kernel)
def pv5431 : PrimeValue := ⟨5431, pr5431⟩
private theorem pr5437 : PrimeCertificate 5437 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv151]) (by decide +kernel)
def pv5437 : PrimeValue := ⟨5437, pr5437⟩
private theorem pr5441 : PrimeCertificate 5441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17]) (by decide +kernel)
def pv5441 : PrimeValue := ⟨5441, pr5441⟩
private theorem pr5443 : PrimeCertificate 5443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv907]) (by decide +kernel)
def pv5443 : PrimeValue := ⟨5443, pr5443⟩
private theorem pr5449 : PrimeCertificate 5449 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv227]) (by decide +kernel)
def pv5449 : PrimeValue := ⟨5449, pr5449⟩
private theorem pr5471 : PrimeCertificate 5471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv547]) (by decide +kernel)
def pv5471 : PrimeValue := ⟨5471, pr5471⟩
private theorem pr5477 : PrimeCertificate 5477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37]) (by decide +kernel)
def pv5477 : PrimeValue := ⟨5477, pr5477⟩
private theorem pr5479 : PrimeCertificate 5479 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv83]) (by decide +kernel)
def pv5479 : PrimeValue := ⟨5479, pr5479⟩
private theorem pr5483 : PrimeCertificate 5483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2741]) (by decide +kernel)
def pv5483 : PrimeValue := ⟨5483, pr5483⟩
private theorem pr5501 : PrimeCertificate 5501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv5501 : PrimeValue := ⟨5501, pr5501⟩
private theorem pr5503 : PrimeCertificate 5503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv131]) (by decide +kernel)
def pv5503 : PrimeValue := ⟨5503, pr5503⟩
private theorem pr5507 : PrimeCertificate 5507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2753]) (by decide +kernel)
def pv5507 : PrimeValue := ⟨5507, pr5507⟩
private theorem pr5519 : PrimeCertificate 5519 :=
  certifyPrime (q := pv13) (ls := [pv2,pv31,pv89]) (by decide +kernel)
def pv5519 : PrimeValue := ⟨5519, pr5519⟩
private theorem pr5521 : PrimeCertificate 5521 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv5521 : PrimeValue := ⟨5521, pr5521⟩
private theorem pr5527 : PrimeCertificate 5527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv307]) (by decide +kernel)
def pv5527 : PrimeValue := ⟨5527, pr5527⟩
private theorem pr5531 : PrimeCertificate 5531 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv79]) (by decide +kernel)
def pv5531 : PrimeValue := ⟨5531, pr5531⟩
private theorem pr5557 : PrimeCertificate 5557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv463]) (by decide +kernel)
def pv5557 : PrimeValue := ⟨5557, pr5557⟩
private theorem pr5563 : PrimeCertificate 5563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv5563 : PrimeValue := ⟨5563, pr5563⟩
private theorem pr5569 : PrimeCertificate 5569 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv5569 : PrimeValue := ⟨5569, pr5569⟩
private theorem pr5573 : PrimeCertificate 5573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv199]) (by decide +kernel)
def pv5573 : PrimeValue := ⟨5573, pr5573⟩
private theorem pr5581 : PrimeCertificate 5581 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv5581 : PrimeValue := ⟨5581, pr5581⟩
private theorem pr5591 : PrimeCertificate 5591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv43]) (by decide +kernel)
def pv5591 : PrimeValue := ⟨5591, pr5591⟩
private theorem pr5623 : PrimeCertificate 5623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv937]) (by decide +kernel)
def pv5623 : PrimeValue := ⟨5623, pr5623⟩
private theorem pr5639 : PrimeCertificate 5639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv2819]) (by decide +kernel)
def pv5639 : PrimeValue := ⟨5639, pr5639⟩
private theorem pr5641 : PrimeCertificate 5641 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv5641 : PrimeValue := ⟨5641, pr5641⟩
private theorem pr5647 : PrimeCertificate 5647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv941]) (by decide +kernel)
def pv5647 : PrimeValue := ⟨5647, pr5647⟩
private theorem pr5651 : PrimeCertificate 5651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv113]) (by decide +kernel)
def pv5651 : PrimeValue := ⟨5651, pr5651⟩
private theorem pr5653 : PrimeCertificate 5653 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv157]) (by decide +kernel)
def pv5653 : PrimeValue := ⟨5653, pr5653⟩
private theorem pr5657 : PrimeCertificate 5657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv101]) (by decide +kernel)
def pv5657 : PrimeValue := ⟨5657, pr5657⟩
private theorem pr5659 : PrimeCertificate 5659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv41]) (by decide +kernel)
def pv5659 : PrimeValue := ⟨5659, pr5659⟩
private theorem pr5669 : PrimeCertificate 5669 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv109]) (by decide +kernel)
def pv5669 : PrimeValue := ⟨5669, pr5669⟩
private theorem pr5683 : PrimeCertificate 5683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv947]) (by decide +kernel)
def pv5683 : PrimeValue := ⟨5683, pr5683⟩
private theorem pr5689 : PrimeCertificate 5689 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv5689 : PrimeValue := ⟨5689, pr5689⟩
private theorem pr5693 : PrimeCertificate 5693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1423]) (by decide +kernel)
def pv5693 : PrimeValue := ⟨5693, pr5693⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
