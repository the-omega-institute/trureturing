/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table115
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table115.pv544627
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table034
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table035
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table080
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table081

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr544627 : PrimeCertificate 544627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79,pv383]) (by decide +kernel)
def pv544627 : PrimeValue := ⟨544627, pr544627⟩
private theorem pr544631 : PrimeCertificate 544631 :=
  certifyPrime (q := pv41) (ls := [pv2,pv5,pv107,pv509]) (by decide +kernel)
def pv544631 : PrimeValue := ⟨544631, pr544631⟩
private theorem pr544651 : PrimeCertificate 544651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3631]) (by decide +kernel)
def pv544651 : PrimeValue := ⟨544651, pr544651⟩
private theorem pr544699 : PrimeCertificate 544699 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv131]) (by decide +kernel)
def pv544699 : PrimeValue := ⟨544699, pr544699⟩
private theorem pr544717 : PrimeCertificate 544717 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv15131]) (by decide +kernel)
def pv544717 : PrimeValue := ⟨544717, pr544717⟩
private theorem pr544723 : PrimeCertificate 544723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv90787]) (by decide +kernel)
def pv544723 : PrimeValue := ⟨544723, pr544723⟩
private theorem pr544781 : PrimeCertificate 544781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv27239]) (by decide +kernel)
def pv544781 : PrimeValue := ⟨544781, pr544781⟩
private theorem pr544813 : PrimeCertificate 544813 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv83,pv547]) (by decide +kernel)
def pv544813 : PrimeValue := ⟨544813, pr544813⟩
private theorem pr544897 : PrimeCertificate 544897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv43]) (by decide +kernel)
def pv544897 : PrimeValue := ⟨544897, pr544897⟩
private theorem pr545023 : PrimeCertificate 545023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10093]) (by decide +kernel)
def pv545023 : PrimeValue := ⟨545023, pr545023⟩
private theorem pr545033 : PrimeCertificate 545033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv193,pv353]) (by decide +kernel)
def pv545033 : PrimeValue := ⟨545033, pr545033⟩
private theorem pr545057 : PrimeCertificate 545057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17033]) (by decide +kernel)
def pv545057 : PrimeValue := ⟨545057, pr545057⟩
private theorem pr545063 : PrimeCertificate 545063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv38933]) (by decide +kernel)
def pv545063 : PrimeValue := ⟨545063, pr545063⟩
private theorem pr545087 : PrimeCertificate 545087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv449,pv607]) (by decide +kernel)
def pv545087 : PrimeValue := ⟨545087, pr545087⟩
private theorem pr545089 : PrimeCertificate 545089 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv167]) (by decide +kernel)
def pv545089 : PrimeValue := ⟨545089, pr545089⟩
private theorem pr545203 : PrimeCertificate 545203 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4327]) (by decide +kernel)
def pv545203 : PrimeValue := ⟨545203, pr545203⟩
private theorem pr545239 : PrimeCertificate 545239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv439]) (by decide +kernel)
def pv545239 : PrimeValue := ⟨545239, pr545239⟩
private theorem pr545387 : PrimeCertificate 545387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv272693]) (by decide +kernel)
def pv545387 : PrimeValue := ⟨545387, pr545387⟩
private theorem pr545473 : PrimeCertificate 545473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv947]) (by decide +kernel)
def pv545473 : PrimeValue := ⟨545473, pr545473⟩
private theorem pr545483 : PrimeCertificate 545483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv47,pv829]) (by decide +kernel)
def pv545483 : PrimeValue := ⟨545483, pr545483⟩
private theorem pr545527 : PrimeCertificate 545527 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv30307]) (by decide +kernel)
def pv545527 : PrimeValue := ⟨545527, pr545527⟩
private theorem pr545533 : PrimeCertificate 545533 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv269]) (by decide +kernel)
def pv545533 : PrimeValue := ⟨545533, pr545533⟩
private theorem pr545551 : PrimeCertificate 545551 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3637]) (by decide +kernel)
def pv545551 : PrimeValue := ⟨545551, pr545551⟩
private theorem pr545579 : PrimeCertificate 545579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv24799]) (by decide +kernel)
def pv545579 : PrimeValue := ⟨545579, pr545579⟩
private theorem pr545609 : PrimeCertificate 545609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv9743]) (by decide +kernel)
def pv545609 : PrimeValue := ⟨545609, pr545609⟩
private theorem pr545617 : PrimeCertificate 545617 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv421]) (by decide +kernel)
def pv545617 : PrimeValue := ⟨545617, pr545617⟩
private theorem pr545621 : PrimeCertificate 545621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv27281]) (by decide +kernel)
def pv545621 : PrimeValue := ⟨545621, pr545621⟩
private theorem pr545749 : PrimeCertificate 545749 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv73,pv89]) (by decide +kernel)
def pv545749 : PrimeValue := ⟨545749, pr545749⟩
private theorem pr545827 : PrimeCertificate 545827 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv90971]) (by decide +kernel)
def pv545827 : PrimeValue := ⟨545827, pr545827⟩
private theorem pr545843 : PrimeCertificate 545843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv43,pv577]) (by decide +kernel)
def pv545843 : PrimeValue := ⟨545843, pr545843⟩
private theorem pr545863 : PrimeCertificate 545863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv90977]) (by decide +kernel)
def pv545863 : PrimeValue := ⟨545863, pr545863⟩
private theorem pr545893 : PrimeCertificate 545893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv45491]) (by decide +kernel)
def pv545893 : PrimeValue := ⟨545893, pr545893⟩
private theorem pr545933 : PrimeCertificate 545933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv136483]) (by decide +kernel)
def pv545933 : PrimeValue := ⟨545933, pr545933⟩
private theorem pr545947 : PrimeCertificate 545947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv4789]) (by decide +kernel)
def pv545947 : PrimeValue := ⟨545947, pr545947⟩
private theorem pr546017 : PrimeCertificate 546017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv113,pv151]) (by decide +kernel)
def pv546017 : PrimeValue := ⟨546017, pr546017⟩
private theorem pr546047 : PrimeCertificate 546047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv47,pv157]) (by decide +kernel)
def pv546047 : PrimeValue := ⟨546047, pr546047⟩
private theorem pr546053 : PrimeCertificate 546053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv10501]) (by decide +kernel)
def pv546053 : PrimeValue := ⟨546053, pr546053⟩
private theorem pr546097 : PrimeCertificate 546097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv367]) (by decide +kernel)
def pv546097 : PrimeValue := ⟨546097, pr546097⟩
private theorem pr546233 : PrimeCertificate 546233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv68279]) (by decide +kernel)
def pv546233 : PrimeValue := ⟨546233, pr546233⟩
private theorem pr546239 : PrimeCertificate 546239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv3547]) (by decide +kernel)
def pv546239 : PrimeValue := ⟨546239, pr546239⟩
private theorem pr546263 : PrimeCertificate 546263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv273131]) (by decide +kernel)
def pv546263 : PrimeValue := ⟨546263, pr546263⟩
private theorem pr546283 : PrimeCertificate 546283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv31,pv89]) (by decide +kernel)
def pv546283 : PrimeValue := ⟨546283, pr546283⟩
private theorem pr546317 : PrimeCertificate 546317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv2239]) (by decide +kernel)
def pv546317 : PrimeValue := ⟨546317, pr546317⟩
private theorem pr546341 : PrimeCertificate 546341 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv59,pv463]) (by decide +kernel)
def pv546341 : PrimeValue := ⟨546341, pr546341⟩
private theorem pr546373 : PrimeCertificate 546373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5059]) (by decide +kernel)
def pv546373 : PrimeValue := ⟨546373, pr546373⟩
private theorem pr546391 : PrimeCertificate 546391 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv13,pv467]) (by decide +kernel)
def pv546391 : PrimeValue := ⟨546391, pr546391⟩
private theorem pr546547 : PrimeCertificate 546547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv13]) (by decide +kernel)
def pv546547 : PrimeValue := ⟨546547, pr546547⟩
private theorem pr546583 : PrimeCertificate 546583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv91097]) (by decide +kernel)
def pv546583 : PrimeValue := ⟨546583, pr546583⟩
private theorem pr546599 : PrimeCertificate 546599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv21023]) (by decide +kernel)
def pv546599 : PrimeValue := ⟨546599, pr546599⟩
private theorem pr546613 : PrimeCertificate 546613 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv41,pv101]) (by decide +kernel)
def pv546613 : PrimeValue := ⟨546613, pr546613⟩
private theorem pr546643 : PrimeCertificate 546643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv191]) (by decide +kernel)
def pv546643 : PrimeValue := ⟨546643, pr546643⟩
private theorem pr546709 : PrimeCertificate 546709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv1571]) (by decide +kernel)
def pv546709 : PrimeValue := ⟨546709, pr546709⟩
private theorem pr546781 : PrimeCertificate 546781 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv701]) (by decide +kernel)
def pv546781 : PrimeValue := ⟨546781, pr546781⟩
private theorem pr546869 : PrimeCertificate 546869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19531]) (by decide +kernel)
def pv546869 : PrimeValue := ⟨546869, pr546869⟩
private theorem pr546893 : PrimeCertificate 546893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv2909]) (by decide +kernel)
def pv546893 : PrimeValue := ⟨546893, pr546893⟩
private theorem pr546961 : PrimeCertificate 546961 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv43,pv53]) (by decide +kernel)
def pv546961 : PrimeValue := ⟨546961, pr546961⟩
private theorem pr547021 : PrimeCertificate 547021 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1013]) (by decide +kernel)
def pv547021 : PrimeValue := ⟨547021, pr547021⟩
private theorem pr547061 : PrimeCertificate 547061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv1609]) (by decide +kernel)
def pv547061 : PrimeValue := ⟨547061, pr547061⟩
private theorem pr547087 : PrimeCertificate 547087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv4799]) (by decide +kernel)
def pv547087 : PrimeValue := ⟨547087, pr547087⟩
private theorem pr547223 : PrimeCertificate 547223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv1619]) (by decide +kernel)
def pv547223 : PrimeValue := ⟨547223, pr547223⟩
private theorem pr547271 : PrimeCertificate 547271 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv54727]) (by decide +kernel)
def pv547271 : PrimeValue := ⟨547271, pr547271⟩
private theorem pr547291 : PrimeCertificate 547291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2027]) (by decide +kernel)
def pv547291 : PrimeValue := ⟨547291, pr547291⟩
private theorem pr547301 : PrimeCertificate 547301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv421]) (by decide +kernel)
def pv547301 : PrimeValue := ⟨547301, pr547301⟩
private theorem pr547321 : PrimeCertificate 547321 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv4561]) (by decide +kernel)
def pv547321 : PrimeValue := ⟨547321, pr547321⟩
private theorem pr547357 : PrimeCertificate 547357 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv45613]) (by decide +kernel)
def pv547357 : PrimeValue := ⟨547357, pr547357⟩
private theorem pr547369 : PrimeCertificate 547369 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv22807]) (by decide +kernel)
def pv547369 : PrimeValue := ⟨547369, pr547369⟩
private theorem pr547373 : PrimeCertificate 547373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv113,pv173]) (by decide +kernel)
def pv547373 : PrimeValue := ⟨547373, pr547373⟩
private theorem pr547411 : PrimeCertificate 547411 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv71,pv257]) (by decide +kernel)
def pv547411 : PrimeValue := ⟨547411, pr547411⟩
private theorem pr547441 : PrimeCertificate 547441 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv2281]) (by decide +kernel)
def pv547441 : PrimeValue := ⟨547441, pr547441⟩
private theorem pr547453 : PrimeCertificate 547453 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv37,pv137]) (by decide +kernel)
def pv547453 : PrimeValue := ⟨547453, pr547453⟩
private theorem pr547487 : PrimeCertificate 547487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv457,pv599]) (by decide +kernel)
def pv547487 : PrimeValue := ⟨547487, pr547487⟩
private theorem pr547493 : PrimeCertificate 547493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv541]) (by decide +kernel)
def pv547493 : PrimeValue := ⟨547493, pr547493⟩
private theorem pr547499 : PrimeCertificate 547499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv39107]) (by decide +kernel)
def pv547499 : PrimeValue := ⟨547499, pr547499⟩
private theorem pr547559 : PrimeCertificate 547559 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv24889]) (by decide +kernel)
def pv547559 : PrimeValue := ⟨547559, pr547559⟩
private theorem pr547567 : PrimeCertificate 547567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv263,pv347]) (by decide +kernel)
def pv547567 : PrimeValue := ⟨547567, pr547567⟩
private theorem pr547619 : PrimeCertificate 547619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv14411]) (by decide +kernel)
def pv547619 : PrimeValue := ⟨547619, pr547619⟩
private theorem pr547643 : PrimeCertificate 547643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv273821]) (by decide +kernel)
def pv547643 : PrimeValue := ⟨547643, pr547643⟩
private theorem pr547663 : PrimeCertificate 547663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv97,pv941]) (by decide +kernel)
def pv547663 : PrimeValue := ⟨547663, pr547663⟩
private theorem pr547763 : PrimeCertificate 547763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv273881]) (by decide +kernel)
def pv547763 : PrimeValue := ⟨547763, pr547763⟩
private theorem pr547823 : PrimeCertificate 547823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv37,pv673]) (by decide +kernel)
def pv547823 : PrimeValue := ⟨547823, pr547823⟩
private theorem pr547889 : PrimeCertificate 547889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv283]) (by decide +kernel)
def pv547889 : PrimeValue := ⟨547889, pr547889⟩
private theorem pr548039 : PrimeCertificate 548039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv274019]) (by decide +kernel)
def pv548039 : PrimeValue := ⟨548039, pr548039⟩
private theorem pr548083 : PrimeCertificate 548083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30449]) (by decide +kernel)
def pv548083 : PrimeValue := ⟨548083, pr548083⟩
private theorem pr548143 : PrimeCertificate 548143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv31,pv421]) (by decide +kernel)
def pv548143 : PrimeValue := ⟨548143, pr548143⟩
private theorem pr548153 : PrimeCertificate 548153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv6229]) (by decide +kernel)
def pv548153 : PrimeValue := ⟨548153, pr548153⟩
private theorem pr548189 : PrimeCertificate 548189 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv7213]) (by decide +kernel)
def pv548189 : PrimeValue := ⟨548189, pr548189⟩
private theorem pr548213 : PrimeCertificate 548213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv2797]) (by decide +kernel)
def pv548213 : PrimeValue := ⟨548213, pr548213⟩
private theorem pr548221 : PrimeCertificate 548221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv9137]) (by decide +kernel)
def pv548221 : PrimeValue := ⟨548221, pr548221⟩
private theorem pr548243 : PrimeCertificate 548243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv274121]) (by decide +kernel)
def pv548243 : PrimeValue := ⟨548243, pr548243⟩
private theorem pr548263 : PrimeCertificate 548263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv71]) (by decide +kernel)
def pv548263 : PrimeValue := ⟨548263, pr548263⟩
private theorem pr548291 : PrimeCertificate 548291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv54829]) (by decide +kernel)
def pv548291 : PrimeValue := ⟨548291, pr548291⟩
private theorem pr548347 : PrimeCertificate 548347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv1549]) (by decide +kernel)
def pv548347 : PrimeValue := ⟨548347, pr548347⟩
private theorem pr548351 : PrimeCertificate 548351 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv997]) (by decide +kernel)
def pv548351 : PrimeValue := ⟨548351, pr548351⟩
private theorem pr548363 : PrimeCertificate 548363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv487,pv563]) (by decide +kernel)
def pv548363 : PrimeValue := ⟨548363, pr548363⟩
private theorem pr548393 : PrimeCertificate 548393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv5273]) (by decide +kernel)
def pv548393 : PrimeValue := ⟨548393, pr548393⟩
private theorem pr548441 : PrimeCertificate 548441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13711]) (by decide +kernel)
def pv548441 : PrimeValue := ⟨548441, pr548441⟩
private theorem pr548459 : PrimeCertificate 548459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv11923]) (by decide +kernel)
def pv548459 : PrimeValue := ⟨548459, pr548459⟩
private theorem pr548503 : PrimeCertificate 548503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv113,pv809]) (by decide +kernel)
def pv548503 : PrimeValue := ⟨548503, pr548503⟩
private theorem pr548519 : PrimeCertificate 548519 :=
  certifyPrime (q := pv11) (ls := [pv2,pv274259]) (by decide +kernel)
def pv548519 : PrimeValue := ⟨548519, pr548519⟩
private theorem pr548533 : PrimeCertificate 548533 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1693]) (by decide +kernel)
def pv548533 : PrimeValue := ⟨548533, pr548533⟩
private theorem pr548543 : PrimeCertificate 548543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv274271]) (by decide +kernel)
def pv548543 : PrimeValue := ⟨548543, pr548543⟩
private theorem pr548557 : PrimeCertificate 548557 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv2689]) (by decide +kernel)
def pv548557 : PrimeValue := ⟨548557, pr548557⟩
private theorem pr548657 : PrimeCertificate 548657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv647]) (by decide +kernel)
def pv548657 : PrimeValue := ⟨548657, pr548657⟩
private theorem pr548671 : PrimeCertificate 548671 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv18289]) (by decide +kernel)
def pv548671 : PrimeValue := ⟨548671, pr548671⟩
private theorem pr548677 : PrimeCertificate 548677 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv15241]) (by decide +kernel)
def pv548677 : PrimeValue := ⟨548677, pr548677⟩
private theorem pr548771 : PrimeCertificate 548771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv54877]) (by decide +kernel)
def pv548771 : PrimeValue := ⟨548771, pr548771⟩
private theorem pr548861 : PrimeCertificate 548861 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv2111]) (by decide +kernel)
def pv548861 : PrimeValue := ⟨548861, pr548861⟩
private theorem pr548903 : PrimeCertificate 548903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv274451]) (by decide +kernel)
def pv548903 : PrimeValue := ⟨548903, pr548903⟩
private theorem pr548909 : PrimeCertificate 548909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv3347]) (by decide +kernel)
def pv548909 : PrimeValue := ⟨548909, pr548909⟩
private theorem pr549001 : PrimeCertificate 549001 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv549001 : PrimeValue := ⟨549001, pr549001⟩
private theorem pr549011 : PrimeCertificate 549011 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv23,pv31]) (by decide +kernel)
def pv549011 : PrimeValue := ⟨549011, pr549011⟩
private theorem pr549013 : PrimeCertificate 549013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv45751]) (by decide +kernel)
def pv549013 : PrimeValue := ⟨549013, pr549013⟩
private theorem pr549037 : PrimeCertificate 549037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv151]) (by decide +kernel)
def pv549037 : PrimeValue := ⟨549037, pr549037⟩
private theorem pr549163 : PrimeCertificate 549163 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv30509]) (by decide +kernel)
def pv549163 : PrimeValue := ⟨549163, pr549163⟩
private theorem pr549221 : PrimeCertificate 549221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv3923]) (by decide +kernel)
def pv549221 : PrimeValue := ⟨549221, pr549221⟩
private theorem pr549229 : PrimeCertificate 549229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv1237]) (by decide +kernel)
def pv549229 : PrimeValue := ⟨549229, pr549229⟩
private theorem pr549247 : PrimeCertificate 549247 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv91541]) (by decide +kernel)
def pv549247 : PrimeValue := ⟨549247, pr549247⟩
private theorem pr549257 : PrimeCertificate 549257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv967]) (by decide +kernel)
def pv549257 : PrimeValue := ⟨549257, pr549257⟩
private theorem pr549313 : PrimeCertificate 549313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2861]) (by decide +kernel)
def pv549313 : PrimeValue := ⟨549313, pr549313⟩
private theorem pr549319 : PrimeCertificate 549319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv29,pv41]) (by decide +kernel)
def pv549319 : PrimeValue := ⟨549319, pr549319⟩
private theorem pr549323 : PrimeCertificate 549323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv274661]) (by decide +kernel)
def pv549323 : PrimeValue := ⟨549323, pr549323⟩
private theorem pr549391 : PrimeCertificate 549391 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv18313]) (by decide +kernel)
def pv549391 : PrimeValue := ⟨549391, pr549391⟩
private theorem pr549517 : PrimeCertificate 549517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv181]) (by decide +kernel)
def pv549517 : PrimeValue := ⟨549517, pr549517⟩
private theorem pr549533 : PrimeCertificate 549533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137383]) (by decide +kernel)
def pv549533 : PrimeValue := ⟨549533, pr549533⟩
private theorem pr549551 : PrimeCertificate 549551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29,pv379]) (by decide +kernel)
def pv549551 : PrimeValue := ⟨549551, pr549551⟩
private theorem pr549553 : PrimeCertificate 549553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv549553 : PrimeValue := ⟨549553, pr549553⟩
private theorem pr549569 : PrimeCertificate 549569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv277]) (by decide +kernel)
def pv549569 : PrimeValue := ⟨549569, pr549569⟩
private theorem pr549623 : PrimeCertificate 549623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv274811]) (by decide +kernel)
def pv549623 : PrimeValue := ⟨549623, pr549623⟩
private theorem pr549643 : PrimeCertificate 549643 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv101,pv907]) (by decide +kernel)
def pv549643 : PrimeValue := ⟨549643, pr549643⟩
private theorem pr549649 : PrimeCertificate 549649 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv347]) (by decide +kernel)
def pv549649 : PrimeValue := ⟨549649, pr549649⟩
private theorem pr549667 : PrimeCertificate 549667 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv29]) (by decide +kernel)
def pv549667 : PrimeValue := ⟨549667, pr549667⟩
private theorem pr549713 : PrimeCertificate 549713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv43,pv47]) (by decide +kernel)
def pv549713 : PrimeValue := ⟨549713, pr549713⟩
private theorem pr549737 : PrimeCertificate 549737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv6247]) (by decide +kernel)
def pv549737 : PrimeValue := ⟨549737, pr549737⟩
private theorem pr549749 : PrimeCertificate 549749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137437]) (by decide +kernel)
def pv549749 : PrimeValue := ⟨549749, pr549749⟩
private theorem pr549863 : PrimeCertificate 549863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv274931]) (by decide +kernel)
def pv549863 : PrimeValue := ⟨549863, pr549863⟩
private theorem pr549911 : PrimeCertificate 549911 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv127,pv433]) (by decide +kernel)
def pv549911 : PrimeValue := ⟨549911, pr549911⟩
private theorem pr549979 : PrimeCertificate 549979 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv641]) (by decide +kernel)
def pv549979 : PrimeValue := ⟨549979, pr549979⟩
private theorem pr550061 : PrimeCertificate 550061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv3929]) (by decide +kernel)
def pv550061 : PrimeValue := ⟨550061, pr550061⟩
private theorem pr550073 : PrimeCertificate 550073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv2371]) (by decide +kernel)
def pv550073 : PrimeValue := ⟨550073, pr550073⟩
private theorem pr550139 : PrimeCertificate 550139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv6709]) (by decide +kernel)
def pv550139 : PrimeValue := ⟨550139, pr550139⟩
private theorem pr550211 : PrimeCertificate 550211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv55021]) (by decide +kernel)
def pv550211 : PrimeValue := ⟨550211, pr550211⟩
private theorem pr550241 : PrimeCertificate 550241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv181]) (by decide +kernel)
def pv550241 : PrimeValue := ⟨550241, pr550241⟩
private theorem pr550267 : PrimeCertificate 550267 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv91711]) (by decide +kernel)
def pv550267 : PrimeValue := ⟨550267, pr550267⟩
private theorem pr550351 : PrimeCertificate 550351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1223]) (by decide +kernel)
def pv550351 : PrimeValue := ⟨550351, pr550351⟩
private theorem pr550447 : PrimeCertificate 550447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv7057]) (by decide +kernel)
def pv550447 : PrimeValue := ⟨550447, pr550447⟩
private theorem pr550489 : PrimeCertificate 550489 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv22937]) (by decide +kernel)
def pv550489 : PrimeValue := ⟨550489, pr550489⟩
private theorem pr550519 : PrimeCertificate 550519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv91753]) (by decide +kernel)
def pv550519 : PrimeValue := ⟨550519, pr550519⟩
private theorem pr550553 : PrimeCertificate 550553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv68819]) (by decide +kernel)
def pv550553 : PrimeValue := ⟨550553, pr550553⟩
private theorem pr550609 : PrimeCertificate 550609 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11471]) (by decide +kernel)
def pv550609 : PrimeValue := ⟨550609, pr550609⟩
private theorem pr550661 : PrimeCertificate 550661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv2503]) (by decide +kernel)
def pv550661 : PrimeValue := ⟨550661, pr550661⟩
private theorem pr550703 : PrimeCertificate 550703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv227,pv1213]) (by decide +kernel)
def pv550703 : PrimeValue := ⟨550703, pr550703⟩
private theorem pr550733 : PrimeCertificate 550733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv17,pv89]) (by decide +kernel)
def pv550733 : PrimeValue := ⟨550733, pr550733⟩
private theorem pr550841 : PrimeCertificate 550841 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv47,pv293]) (by decide +kernel)
def pv550841 : PrimeValue := ⟨550841, pr550841⟩
private theorem pr550909 : PrimeCertificate 550909 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5101]) (by decide +kernel)
def pv550909 : PrimeValue := ⟨550909, pr550909⟩
private theorem pr550993 : PrimeCertificate 550993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv883]) (by decide +kernel)
def pv550993 : PrimeValue := ⟨550993, pr550993⟩
private theorem pr550997 : PrimeCertificate 550997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139,pv991]) (by decide +kernel)
def pv550997 : PrimeValue := ⟨550997, pr550997⟩
private theorem pr551003 : PrimeCertificate 551003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv149]) (by decide +kernel)
def pv551003 : PrimeValue := ⟨551003, pr551003⟩
private theorem pr551063 : PrimeCertificate 551063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv275531]) (by decide +kernel)
def pv551063 : PrimeValue := ⟨551063, pr551063⟩
private theorem pr551093 : PrimeCertificate 551093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv311,pv443]) (by decide +kernel)
def pv551093 : PrimeValue := ⟨551093, pr551093⟩
private theorem pr551107 : PrimeCertificate 551107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv1801]) (by decide +kernel)
def pv551107 : PrimeValue := ⟨551107, pr551107⟩
private theorem pr551113 : PrimeCertificate 551113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv22963]) (by decide +kernel)
def pv551113 : PrimeValue := ⟨551113, pr551113⟩
private theorem pr551129 : PrimeCertificate 551129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv68891]) (by decide +kernel)
def pv551129 : PrimeValue := ⟨551129, pr551129⟩
private theorem pr551143 : PrimeCertificate 551143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv457]) (by decide +kernel)
def pv551143 : PrimeValue := ⟨551143, pr551143⟩
private theorem pr551197 : PrimeCertificate 551197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv251]) (by decide +kernel)
def pv551197 : PrimeValue := ⟨551197, pr551197⟩
private theorem pr551231 : PrimeCertificate 551231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv199,pv277]) (by decide +kernel)
def pv551231 : PrimeValue := ⟨551231, pr551231⟩
private theorem pr551233 : PrimeCertificate 551233 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv29]) (by decide +kernel)
def pv551233 : PrimeValue := ⟨551233, pr551233⟩
private theorem pr551339 : PrimeCertificate 551339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv275669]) (by decide +kernel)
def pv551339 : PrimeValue := ⟨551339, pr551339⟩
private theorem pr551347 : PrimeCertificate 551347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv2137]) (by decide +kernel)
def pv551347 : PrimeValue := ⟨551347, pr551347⟩
private theorem pr551363 : PrimeCertificate 551363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv39383]) (by decide +kernel)
def pv551363 : PrimeValue := ⟨551363, pr551363⟩
private theorem pr551387 : PrimeCertificate 551387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv71,pv353]) (by decide +kernel)
def pv551387 : PrimeValue := ⟨551387, pr551387⟩
private theorem pr551407 : PrimeCertificate 551407 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv29,pv3169]) (by decide +kernel)
def pv551407 : PrimeValue := ⟨551407, pr551407⟩
private theorem pr551423 : PrimeCertificate 551423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv275711]) (by decide +kernel)
def pv551423 : PrimeValue := ⟨551423, pr551423⟩
private theorem pr551483 : PrimeCertificate 551483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv275741]) (by decide +kernel)
def pv551483 : PrimeValue := ⟨551483, pr551483⟩
private theorem pr551489 : PrimeCertificate 551489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1231]) (by decide +kernel)
def pv551489 : PrimeValue := ⟨551489, pr551489⟩
private theorem pr551543 : PrimeCertificate 551543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv97,pv2843]) (by decide +kernel)
def pv551543 : PrimeValue := ⟨551543, pr551543⟩
private theorem pr551597 : PrimeCertificate 551597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv3727]) (by decide +kernel)
def pv551597 : PrimeValue := ⟨551597, pr551597⟩
private theorem pr551653 : PrimeCertificate 551653 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv45971]) (by decide +kernel)
def pv551653 : PrimeValue := ⟨551653, pr551653⟩
private theorem pr551731 : PrimeCertificate 551731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv53,pv347]) (by decide +kernel)
def pv551731 : PrimeValue := ⟨551731, pr551731⟩
private theorem pr551767 : PrimeCertificate 551767 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv91961]) (by decide +kernel)
def pv551767 : PrimeValue := ⟨551767, pr551767⟩
private theorem pr551773 : PrimeCertificate 551773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv131]) (by decide +kernel)
def pv551773 : PrimeValue := ⟨551773, pr551773⟩
private theorem pr551801 : PrimeCertificate 551801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv89]) (by decide +kernel)
def pv551801 : PrimeValue := ⟨551801, pr551801⟩
private theorem pr551809 : PrimeCertificate 551809 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv479]) (by decide +kernel)
def pv551809 : PrimeValue := ⟨551809, pr551809⟩
private theorem pr551843 : PrimeCertificate 551843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv275921]) (by decide +kernel)
def pv551843 : PrimeValue := ⟨551843, pr551843⟩
private theorem pr551849 : PrimeCertificate 551849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv6271]) (by decide +kernel)
def pv551849 : PrimeValue := ⟨551849, pr551849⟩
private theorem pr551861 : PrimeCertificate 551861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv673]) (by decide +kernel)
def pv551861 : PrimeValue := ⟨551861, pr551861⟩
private theorem pr551911 : PrimeCertificate 551911 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv18397]) (by decide +kernel)
def pv551911 : PrimeValue := ⟨551911, pr551911⟩
private theorem pr551951 : PrimeCertificate 551951 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv19,pv83]) (by decide +kernel)
def pv551951 : PrimeValue := ⟨551951, pr551951⟩
private theorem pr552031 : PrimeCertificate 552031 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv18401]) (by decide +kernel)
def pv552031 : PrimeValue := ⟨552031, pr552031⟩
private theorem pr552053 : PrimeCertificate 552053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv1747]) (by decide +kernel)
def pv552053 : PrimeValue := ⟨552053, pr552053⟩
private theorem pr552059 : PrimeCertificate 552059 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv17,pv1249]) (by decide +kernel)
def pv552059 : PrimeValue := ⟨552059, pr552059⟩
private theorem pr552089 : PrimeCertificate 552089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv69011]) (by decide +kernel)
def pv552089 : PrimeValue := ⟨552089, pr552089⟩
private theorem pr552103 : PrimeCertificate 552103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv29,pv167]) (by decide +kernel)
def pv552103 : PrimeValue := ⟨552103, pr552103⟩
private theorem pr552113 : PrimeCertificate 552113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv3137]) (by decide +kernel)
def pv552113 : PrimeValue := ⟨552113, pr552113⟩
private theorem pr552137 : PrimeCertificate 552137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv5309]) (by decide +kernel)
def pv552137 : PrimeValue := ⟨552137, pr552137⟩
private theorem pr552193 : PrimeCertificate 552193 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv719]) (by decide +kernel)
def pv552193 : PrimeValue := ⟨552193, pr552193⟩
private theorem pr552239 : PrimeCertificate 552239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv71,pv3889]) (by decide +kernel)
def pv552239 : PrimeValue := ⟨552239, pr552239⟩
private theorem pr552283 : PrimeCertificate 552283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv1109]) (by decide +kernel)
def pv552283 : PrimeValue := ⟨552283, pr552283⟩
private theorem pr552317 : PrimeCertificate 552317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv138079]) (by decide +kernel)
def pv552317 : PrimeValue := ⟨552317, pr552317⟩
private theorem pr552341 : PrimeCertificate 552341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv27617]) (by decide +kernel)
def pv552341 : PrimeValue := ⟨552341, pr552341⟩
private theorem pr552353 : PrimeCertificate 552353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv421]) (by decide +kernel)
def pv552353 : PrimeValue := ⟨552353, pr552353⟩
private theorem pr552397 : PrimeCertificate 552397 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv3541]) (by decide +kernel)
def pv552397 : PrimeValue := ⟨552397, pr552397⟩
private theorem pr552401 : PrimeCertificate 552401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1381]) (by decide +kernel)
def pv552401 : PrimeValue := ⟨552401, pr552401⟩
private theorem pr552473 : PrimeCertificate 552473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv1303]) (by decide +kernel)
def pv552473 : PrimeValue := ⟨552473, pr552473⟩
private theorem pr552581 : PrimeCertificate 552581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv3947]) (by decide +kernel)
def pv552581 : PrimeValue := ⟨552581, pr552581⟩
private theorem pr552583 : PrimeCertificate 552583 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv379]) (by decide +kernel)
def pv552583 : PrimeValue := ⟨552583, pr552583⟩
private theorem pr552709 : PrimeCertificate 552709 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv1181]) (by decide +kernel)
def pv552709 : PrimeValue := ⟨552709, pr552709⟩
private theorem pr552731 : PrimeCertificate 552731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv1783]) (by decide +kernel)
def pv552731 : PrimeValue := ⟨552731, pr552731⟩
private theorem pr552757 : PrimeCertificate 552757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv631]) (by decide +kernel)
def pv552757 : PrimeValue := ⟨552757, pr552757⟩
private theorem pr552787 : PrimeCertificate 552787 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv373]) (by decide +kernel)
def pv552787 : PrimeValue := ⟨552787, pr552787⟩
private theorem pr552791 : PrimeCertificate 552791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv53,pv149]) (by decide +kernel)
def pv552791 : PrimeValue := ⟨552791, pr552791⟩
private theorem pr552809 : PrimeCertificate 552809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv1607]) (by decide +kernel)
def pv552809 : PrimeValue := ⟨552809, pr552809⟩
private theorem pr552821 : PrimeCertificate 552821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv131,pv211]) (by decide +kernel)
def pv552821 : PrimeValue := ⟨552821, pr552821⟩
private theorem pr552883 : PrimeCertificate 552883 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv8377]) (by decide +kernel)
def pv552883 : PrimeValue := ⟨552883, pr552883⟩
private theorem pr552971 : PrimeCertificate 552971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv457]) (by decide +kernel)
def pv552971 : PrimeValue := ⟨552971, pr552971⟩
private theorem pr552991 : PrimeCertificate 552991 :=
  certifyPrime (q := pv61) (ls := [pv2,pv3,pv5,pv18433]) (by decide +kernel)
def pv552991 : PrimeValue := ⟨552991, pr552991⟩
private theorem pr553037 : PrimeCertificate 553037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv12569]) (by decide +kernel)
def pv553037 : PrimeValue := ⟨553037, pr553037⟩
private theorem pr553043 : PrimeCertificate 553043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv39503]) (by decide +kernel)
def pv553043 : PrimeValue := ⟨553043, pr553043⟩
private theorem pr553051 : PrimeCertificate 553051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1229]) (by decide +kernel)
def pv553051 : PrimeValue := ⟨553051, pr553051⟩
private theorem pr553057 : PrimeCertificate 553057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv823]) (by decide +kernel)
def pv553057 : PrimeValue := ⟨553057, pr553057⟩
private theorem pr553139 : PrimeCertificate 553139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193,pv1433]) (by decide +kernel)
def pv553139 : PrimeValue := ⟨553139, pr553139⟩
private theorem pr553153 : PrimeCertificate 553153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv67]) (by decide +kernel)
def pv553153 : PrimeValue := ⟨553153, pr553153⟩
private theorem pr553181 : PrimeCertificate 553181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv1627]) (by decide +kernel)
def pv553181 : PrimeValue := ⟨553181, pr553181⟩
private theorem pr553211 : PrimeCertificate 553211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1129]) (by decide +kernel)
def pv553211 : PrimeValue := ⟨553211, pr553211⟩
private theorem pr553447 : PrimeCertificate 553447 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv37,pv277]) (by decide +kernel)
def pv553447 : PrimeValue := ⟨553447, pr553447⟩
private theorem pr553463 : PrimeCertificate 553463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv3041]) (by decide +kernel)
def pv553463 : PrimeValue := ⟨553463, pr553463⟩
private theorem pr553471 : PrimeCertificate 553471 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv19,pv971]) (by decide +kernel)
def pv553471 : PrimeValue := ⟨553471, pr553471⟩
private theorem pr553481 : PrimeCertificate 553481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv101,pv137]) (by decide +kernel)
def pv553481 : PrimeValue := ⟨553481, pr553481⟩
private theorem pr553543 : PrimeCertificate 553543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv8387]) (by decide +kernel)
def pv553543 : PrimeValue := ⟨553543, pr553543⟩
private theorem pr553583 : PrimeCertificate 553583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv43,pv157]) (by decide +kernel)
def pv553583 : PrimeValue := ⟨553583, pr553583⟩
private theorem pr553601 : PrimeCertificate 553601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv173]) (by decide +kernel)
def pv553601 : PrimeValue := ⟨553601, pr553601⟩
private theorem pr553627 : PrimeCertificate 553627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30757]) (by decide +kernel)
def pv553627 : PrimeValue := ⟨553627, pr553627⟩
private theorem pr553643 : PrimeCertificate 553643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv276821]) (by decide +kernel)
def pv553643 : PrimeValue := ⟨553643, pr553643⟩
private theorem pr553667 : PrimeCertificate 553667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv276833]) (by decide +kernel)
def pv553667 : PrimeValue := ⟨553667, pr553667⟩
private theorem pr553687 : PrimeCertificate 553687 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv13183]) (by decide +kernel)
def pv553687 : PrimeValue := ⟨553687, pr553687⟩
private theorem pr553703 : PrimeCertificate 553703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv12037]) (by decide +kernel)
def pv553703 : PrimeValue := ⟨553703, pr553703⟩
private theorem pr553733 : PrimeCertificate 553733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv138433]) (by decide +kernel)
def pv553733 : PrimeValue := ⟨553733, pr553733⟩
private theorem pr553811 : PrimeCertificate 553811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv55381]) (by decide +kernel)
def pv553811 : PrimeValue := ⟨553811, pr553811⟩
private theorem pr553837 : PrimeCertificate 553837 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv46153]) (by decide +kernel)
def pv553837 : PrimeValue := ⟨553837, pr553837⟩
private theorem pr553867 : PrimeCertificate 553867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv92311]) (by decide +kernel)
def pv553867 : PrimeValue := ⟨553867, pr553867⟩
private theorem pr553873 : PrimeCertificate 553873 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv1049]) (by decide +kernel)
def pv553873 : PrimeValue := ⟨553873, pr553873⟩
private theorem pr553901 : PrimeCertificate 553901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv191]) (by decide +kernel)
def pv553901 : PrimeValue := ⟨553901, pr553901⟩
private theorem pr553961 : PrimeCertificate 553961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv1259]) (by decide +kernel)
def pv553961 : PrimeValue := ⟨553961, pr553961⟩
private theorem pr553963 : PrimeCertificate 553963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv5431]) (by decide +kernel)
def pv553963 : PrimeValue := ⟨553963, pr553963⟩
private theorem pr554003 : PrimeCertificate 554003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv61,pv239]) (by decide +kernel)
def pv554003 : PrimeValue := ⟨554003, pr554003⟩
private theorem pr554017 : PrimeCertificate 554017 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv199]) (by decide +kernel)
def pv554017 : PrimeValue := ⟨554017, pr554017⟩
private theorem pr554051 : PrimeCertificate 554051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1583]) (by decide +kernel)
def pv554051 : PrimeValue := ⟨554051, pr554051⟩
private theorem pr554077 : PrimeCertificate 554077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15391]) (by decide +kernel)
def pv554077 : PrimeValue := ⟨554077, pr554077⟩
private theorem pr554087 : PrimeCertificate 554087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv101,pv211]) (by decide +kernel)
def pv554087 : PrimeValue := ⟨554087, pr554087⟩
private theorem pr554117 : PrimeCertificate 554117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv23,pv317]) (by decide +kernel)
def pv554117 : PrimeValue := ⟨554117, pr554117⟩
private theorem pr554129 : PrimeCertificate 554129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv587]) (by decide +kernel)
def pv554129 : PrimeValue := ⟨554129, pr554129⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
