/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table091
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table091.pv334987
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table057
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table058

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr334987 : PrimeCertificate 334987 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv1801]) (by decide +kernel)
def pv334987 : PrimeValue := ⟨334987, pr334987⟩
private theorem pr334993 : PrimeCertificate 334993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv997]) (by decide +kernel)
def pv334993 : PrimeValue := ⟨334993, pr334993⟩
private theorem pr335047 : PrimeCertificate 335047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv2939]) (by decide +kernel)
def pv335047 : PrimeValue := ⟨335047, pr335047⟩
private theorem pr335051 : PrimeCertificate 335051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6701]) (by decide +kernel)
def pv335051 : PrimeValue := ⟨335051, pr335051⟩
private theorem pr335089 : PrimeCertificate 335089 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv13,pv179]) (by decide +kernel)
def pv335089 : PrimeValue := ⟨335089, pr335089⟩
private theorem pr335107 : PrimeCertificate 335107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18617]) (by decide +kernel)
def pv335107 : PrimeValue := ⟨335107, pr335107⟩
private theorem pr335117 : PrimeCertificate 335117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv199,pv421]) (by decide +kernel)
def pv335117 : PrimeValue := ⟨335117, pr335117⟩
private theorem pr335161 : PrimeCertificate 335161 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv335161 : PrimeValue := ⟨335161, pr335161⟩
private theorem pr335171 : PrimeCertificate 335171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv277]) (by decide +kernel)
def pv335171 : PrimeValue := ⟨335171, pr335171⟩
private theorem pr335249 : PrimeCertificate 335249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv911]) (by decide +kernel)
def pv335249 : PrimeValue := ⟨335249, pr335249⟩
private theorem pr335323 : PrimeCertificate 335323 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1433]) (by decide +kernel)
def pv335323 : PrimeValue := ⟨335323, pr335323⟩
private theorem pr335341 : PrimeCertificate 335341 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv335341 : PrimeValue := ⟨335341, pr335341⟩
private theorem pr335347 : PrimeCertificate 335347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv5081]) (by decide +kernel)
def pv335347 : PrimeValue := ⟨335347, pr335347⟩
private theorem pr335381 : PrimeCertificate 335381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv409]) (by decide +kernel)
def pv335381 : PrimeValue := ⟨335381, pr335381⟩
private theorem pr335383 : PrimeCertificate 335383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv55897]) (by decide +kernel)
def pv335383 : PrimeValue := ⟨335383, pr335383⟩
private theorem pr335411 : PrimeCertificate 335411 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv1973]) (by decide +kernel)
def pv335411 : PrimeValue := ⟨335411, pr335411⟩
private theorem pr335453 : PrimeCertificate 335453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv6451]) (by decide +kernel)
def pv335453 : PrimeValue := ⟨335453, pr335453⟩
private theorem pr335459 : PrimeCertificate 335459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167729]) (by decide +kernel)
def pv335459 : PrimeValue := ⟨335459, pr335459⟩
private theorem pr335473 : PrimeCertificate 335473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv241]) (by decide +kernel)
def pv335473 : PrimeValue := ⟨335473, pr335473⟩
private theorem pr335507 : PrimeCertificate 335507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv739]) (by decide +kernel)
def pv335507 : PrimeValue := ⟨335507, pr335507⟩
private theorem pr335519 : PrimeCertificate 335519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv167759]) (by decide +kernel)
def pv335519 : PrimeValue := ⟨335519, pr335519⟩
private theorem pr335527 : PrimeCertificate 335527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv55921]) (by decide +kernel)
def pv335527 : PrimeValue := ⟨335527, pr335527⟩
private theorem pr335557 : PrimeCertificate 335557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv239]) (by decide +kernel)
def pv335557 : PrimeValue := ⟨335557, pr335557⟩
private theorem pr335579 : PrimeCertificate 335579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv8831]) (by decide +kernel)
def pv335579 : PrimeValue := ⟨335579, pr335579⟩
private theorem pr335609 : PrimeCertificate 335609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv461]) (by decide +kernel)
def pv335609 : PrimeValue := ⟨335609, pr335609⟩
private theorem pr335669 : PrimeCertificate 335669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2707]) (by decide +kernel)
def pv335669 : PrimeValue := ⟨335669, pr335669⟩
private theorem pr335719 : PrimeCertificate 335719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6217]) (by decide +kernel)
def pv335719 : PrimeValue := ⟨335719, pr335719⟩
private theorem pr335743 : PrimeCertificate 335743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv5087]) (by decide +kernel)
def pv335743 : PrimeValue := ⟨335743, pr335743⟩
private theorem pr335807 : PrimeCertificate 335807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv8837]) (by decide +kernel)
def pv335807 : PrimeValue := ⟨335807, pr335807⟩
private theorem pr335833 : PrimeCertificate 335833 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv1999]) (by decide +kernel)
def pv335833 : PrimeValue := ⟨335833, pr335833⟩
private theorem pr335879 : PrimeCertificate 335879 :=
  certifyPrime (q := pv11) (ls := [pv2,pv29,pv5791]) (by decide +kernel)
def pv335879 : PrimeValue := ⟨335879, pr335879⟩
private theorem pr335893 : PrimeCertificate 335893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1217]) (by decide +kernel)
def pv335893 : PrimeValue := ⟨335893, pr335893⟩
private theorem pr335917 : PrimeCertificate 335917 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv31,pv43]) (by decide +kernel)
def pv335917 : PrimeValue := ⟨335917, pr335917⟩
private theorem pr335999 : PrimeCertificate 335999 :=
  certifyPrime (q := pv11) (ls := [pv2,pv13,pv12923]) (by decide +kernel)
def pv335999 : PrimeValue := ⟨335999, pr335999⟩
private theorem pr336029 : PrimeCertificate 336029 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv1091]) (by decide +kernel)
def pv336029 : PrimeValue := ⟨336029, pr336029⟩
private theorem pr336041 : PrimeCertificate 336041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv271]) (by decide +kernel)
def pv336041 : PrimeValue := ⟨336041, pr336041⟩
private theorem pr336059 : PrimeCertificate 336059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv168029]) (by decide +kernel)
def pv336059 : PrimeValue := ⟨336059, pr336059⟩
private theorem pr336101 : PrimeCertificate 336101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3361]) (by decide +kernel)
def pv336101 : PrimeValue := ⟨336101, pr336101⟩
private theorem pr336103 : PrimeCertificate 336103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv31,pv139]) (by decide +kernel)
def pv336103 : PrimeValue := ⟨336103, pr336103⟩
private theorem pr336109 : PrimeCertificate 336109 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv37,pv757]) (by decide +kernel)
def pv336109 : PrimeValue := ⟨336109, pr336109⟩
private theorem pr336113 : PrimeCertificate 336113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv3001]) (by decide +kernel)
def pv336113 : PrimeValue := ⟨336113, pr336113⟩
private theorem pr336151 : PrimeCertificate 336151 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv83]) (by decide +kernel)
def pv336151 : PrimeValue := ⟨336151, pr336151⟩
private theorem pr336157 : PrimeCertificate 336157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv109,pv257]) (by decide +kernel)
def pv336157 : PrimeValue := ⟨336157, pr336157⟩
private theorem pr336181 : PrimeCertificate 336181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv431]) (by decide +kernel)
def pv336181 : PrimeValue := ⟨336181, pr336181⟩
private theorem pr336199 : PrimeCertificate 336199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv137,pv409]) (by decide +kernel)
def pv336199 : PrimeValue := ⟨336199, pr336199⟩
private theorem pr336211 : PrimeCertificate 336211 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv1601]) (by decide +kernel)
def pv336211 : PrimeValue := ⟨336211, pr336211⟩
private theorem pr336221 : PrimeCertificate 336221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv16811]) (by decide +kernel)
def pv336221 : PrimeValue := ⟨336221, pr336221⟩
private theorem pr336253 : PrimeCertificate 336253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv4003]) (by decide +kernel)
def pv336253 : PrimeValue := ⟨336253, pr336253⟩
private theorem pr336263 : PrimeCertificate 336263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv8849]) (by decide +kernel)
def pv336263 : PrimeValue := ⟨336263, pr336263⟩
private theorem pr336307 : PrimeCertificate 336307 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv2437]) (by decide +kernel)
def pv336307 : PrimeValue := ⟨336307, pr336307⟩
private theorem pr336361 : PrimeCertificate 336361 :=
  certifyPrime (q := pv71) (ls := [pv2,pv3,pv5,pv2803]) (by decide +kernel)
def pv336361 : PrimeValue := ⟨336361, pr336361⟩
private theorem pr336397 : PrimeCertificate 336397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv97]) (by decide +kernel)
def pv336397 : PrimeValue := ⟨336397, pr336397⟩
private theorem pr336437 : PrimeCertificate 336437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv241,pv349]) (by decide +kernel)
def pv336437 : PrimeValue := ⟨336437, pr336437⟩
private theorem pr336491 : PrimeCertificate 336491 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv11,pv19,pv23]) (by decide +kernel)
def pv336491 : PrimeValue := ⟨336491, pr336491⟩
private theorem pr336499 : PrimeCertificate 336499 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv3299]) (by decide +kernel)
def pv336499 : PrimeValue := ⟨336499, pr336499⟩
private theorem pr336503 : PrimeCertificate 336503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv311,pv541]) (by decide +kernel)
def pv336503 : PrimeValue := ⟨336503, pr336503⟩
private theorem pr336521 : PrimeCertificate 336521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47,pv179]) (by decide +kernel)
def pv336521 : PrimeValue := ⟨336521, pr336521⟩
private theorem pr336529 : PrimeCertificate 336529 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv41]) (by decide +kernel)
def pv336529 : PrimeValue := ⟨336529, pr336529⟩
private theorem pr336577 : PrimeCertificate 336577 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1753]) (by decide +kernel)
def pv336577 : PrimeValue := ⟨336577, pr336577⟩
private theorem pr336599 : PrimeCertificate 336599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv31,pv61,pv89]) (by decide +kernel)
def pv336599 : PrimeValue := ⟨336599, pr336599⟩
private theorem pr336613 : PrimeCertificate 336613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv28051]) (by decide +kernel)
def pv336613 : PrimeValue := ⟨336613, pr336613⟩
private theorem pr336643 : PrimeCertificate 336643 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv2953]) (by decide +kernel)
def pv336643 : PrimeValue := ⟨336643, pr336643⟩
private theorem pr336667 : PrimeCertificate 336667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv5101]) (by decide +kernel)
def pv336667 : PrimeValue := ⟨336667, pr336667⟩
private theorem pr336671 : PrimeCertificate 336671 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv131,pv257]) (by decide +kernel)
def pv336671 : PrimeValue := ⟨336671, pr336671⟩
private theorem pr336727 : PrimeCertificate 336727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1439]) (by decide +kernel)
def pv336727 : PrimeValue := ⟨336727, pr336727⟩
private theorem pr336757 : PrimeCertificate 336757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv211]) (by decide +kernel)
def pv336757 : PrimeValue := ⟨336757, pr336757⟩
private theorem pr336761 : PrimeCertificate 336761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv8419]) (by decide +kernel)
def pv336761 : PrimeValue := ⟨336761, pr336761⟩
private theorem pr336769 : PrimeCertificate 336769 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv877]) (by decide +kernel)
def pv336769 : PrimeValue := ⟨336769, pr336769⟩
private theorem pr336803 : PrimeCertificate 336803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv3583]) (by decide +kernel)
def pv336803 : PrimeValue := ⟨336803, pr336803⟩
private theorem pr336823 : PrimeCertificate 336823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73,pv769]) (by decide +kernel)
def pv336823 : PrimeValue := ⟨336823, pr336823⟩
private theorem pr336857 : PrimeCertificate 336857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv41,pv79]) (by decide +kernel)
def pv336857 : PrimeValue := ⟨336857, pr336857⟩
private theorem pr336863 : PrimeCertificate 336863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv3917]) (by decide +kernel)
def pv336863 : PrimeValue := ⟨336863, pr336863⟩
private theorem pr336977 : PrimeCertificate 336977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv21061]) (by decide +kernel)
def pv336977 : PrimeValue := ⟨336977, pr336977⟩
private theorem pr336989 : PrimeCertificate 336989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv84247]) (by decide +kernel)
def pv336989 : PrimeValue := ⟨336989, pr336989⟩
private theorem pr336997 : PrimeCertificate 336997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv37]) (by decide +kernel)
def pv336997 : PrimeValue := ⟨336997, pr336997⟩
private theorem pr337031 : PrimeCertificate 337031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv33703]) (by decide +kernel)
def pv337031 : PrimeValue := ⟨337031, pr337031⟩
private theorem pr337039 : PrimeCertificate 337039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv29,pv149]) (by decide +kernel)
def pv337039 : PrimeValue := ⟨337039, pr337039⟩
private theorem pr337049 : PrimeCertificate 337049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv42131]) (by decide +kernel)
def pv337049 : PrimeValue := ⟨337049, pr337049⟩
private theorem pr337069 : PrimeCertificate 337069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3121]) (by decide +kernel)
def pv337069 : PrimeValue := ⟨337069, pr337069⟩
private theorem pr337081 : PrimeCertificate 337081 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv53]) (by decide +kernel)
def pv337081 : PrimeValue := ⟨337081, pr337081⟩
private theorem pr337091 : PrimeCertificate 337091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv2593]) (by decide +kernel)
def pv337091 : PrimeValue := ⟨337091, pr337091⟩
private theorem pr337097 : PrimeCertificate 337097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv1453]) (by decide +kernel)
def pv337097 : PrimeValue := ⟨337097, pr337097⟩
private theorem pr337189 : PrimeCertificate 337189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv28099]) (by decide +kernel)
def pv337189 : PrimeValue := ⟨337189, pr337189⟩
private theorem pr337201 : PrimeCertificate 337201 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv281]) (by decide +kernel)
def pv337201 : PrimeValue := ⟨337201, pr337201⟩
private theorem pr337277 : PrimeCertificate 337277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv84319]) (by decide +kernel)
def pv337277 : PrimeValue := ⟨337277, pr337277⟩
private theorem pr337291 : PrimeCertificate 337291 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11243]) (by decide +kernel)
def pv337291 : PrimeValue := ⟨337291, pr337291⟩
private theorem pr337301 : PrimeCertificate 337301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3373]) (by decide +kernel)
def pv337301 : PrimeValue := ⟨337301, pr337301⟩
private theorem pr337327 : PrimeCertificate 337327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv19,pv269]) (by decide +kernel)
def pv337327 : PrimeValue := ⟨337327, pr337327⟩
private theorem pr337339 : PrimeCertificate 337339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6247]) (by decide +kernel)
def pv337339 : PrimeValue := ⟨337339, pr337339⟩
private theorem pr337349 : PrimeCertificate 337349 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17,pv41]) (by decide +kernel)
def pv337349 : PrimeValue := ⟨337349, pr337349⟩
private theorem pr337361 : PrimeCertificate 337361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv4217]) (by decide +kernel)
def pv337361 : PrimeValue := ⟨337361, pr337361⟩
private theorem pr337397 : PrimeCertificate 337397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv84349]) (by decide +kernel)
def pv337397 : PrimeValue := ⟨337397, pr337397⟩
private theorem pr337457 : PrimeCertificate 337457 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23,pv131]) (by decide +kernel)
def pv337457 : PrimeValue := ⟨337457, pr337457⟩
private theorem pr337517 : PrimeCertificate 337517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv4441]) (by decide +kernel)
def pv337517 : PrimeValue := ⟨337517, pr337517⟩
private theorem pr337529 : PrimeCertificate 337529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv1361]) (by decide +kernel)
def pv337529 : PrimeValue := ⟨337529, pr337529⟩
private theorem pr337541 : PrimeCertificate 337541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2411]) (by decide +kernel)
def pv337541 : PrimeValue := ⟨337541, pr337541⟩
private theorem pr337543 : PrimeCertificate 337543 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv101,pv557]) (by decide +kernel)
def pv337543 : PrimeValue := ⟨337543, pr337543⟩
private theorem pr337607 : PrimeCertificate 337607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv168803]) (by decide +kernel)
def pv337607 : PrimeValue := ⟨337607, pr337607⟩
private theorem pr337627 : PrimeCertificate 337627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18757]) (by decide +kernel)
def pv337627 : PrimeValue := ⟨337627, pr337627⟩
private theorem pr337633 : PrimeCertificate 337633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3517]) (by decide +kernel)
def pv337633 : PrimeValue := ⟨337633, pr337633⟩
private theorem pr337669 : PrimeCertificate 337669 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv1481]) (by decide +kernel)
def pv337669 : PrimeValue := ⟨337669, pr337669⟩
private theorem pr337681 : PrimeCertificate 337681 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv7,pv67]) (by decide +kernel)
def pv337681 : PrimeValue := ⟨337681, pr337681⟩
private theorem pr337691 : PrimeCertificate 337691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv33769]) (by decide +kernel)
def pv337691 : PrimeValue := ⟨337691, pr337691⟩
private theorem pr337697 : PrimeCertificate 337697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61,pv173]) (by decide +kernel)
def pv337697 : PrimeValue := ⟨337697, pr337697⟩
private theorem pr337721 : PrimeCertificate 337721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv8443]) (by decide +kernel)
def pv337721 : PrimeValue := ⟨337721, pr337721⟩
private theorem pr337741 : PrimeCertificate 337741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv433]) (by decide +kernel)
def pv337741 : PrimeValue := ⟨337741, pr337741⟩
private theorem pr337759 : PrimeCertificate 337759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv1373]) (by decide +kernel)
def pv337759 : PrimeValue := ⟨337759, pr337759⟩
private theorem pr337837 : PrimeCertificate 337837 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv599]) (by decide +kernel)
def pv337837 : PrimeValue := ⟨337837, pr337837⟩
private theorem pr337861 : PrimeCertificate 337861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1877]) (by decide +kernel)
def pv337861 : PrimeValue := ⟨337861, pr337861⟩
private theorem pr337867 : PrimeCertificate 337867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv56311]) (by decide +kernel)
def pv337867 : PrimeValue := ⟨337867, pr337867⟩
private theorem pr337871 : PrimeCertificate 337871 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv13,pv23,pv113]) (by decide +kernel)
def pv337871 : PrimeValue := ⟨337871, pr337871⟩
private theorem pr337873 : PrimeCertificate 337873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7039]) (by decide +kernel)
def pv337873 : PrimeValue := ⟨337873, pr337873⟩
private theorem pr337919 : PrimeCertificate 337919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv24137]) (by decide +kernel)
def pv337919 : PrimeValue := ⟨337919, pr337919⟩
private theorem pr337949 : PrimeCertificate 337949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv67,pv97]) (by decide +kernel)
def pv337949 : PrimeValue := ⟨337949, pr337949⟩
private theorem pr337957 : PrimeCertificate 337957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv28163]) (by decide +kernel)
def pv337957 : PrimeValue := ⟨337957, pr337957⟩
private theorem pr337999 : PrimeCertificate 337999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv56333]) (by decide +kernel)
def pv337999 : PrimeValue := ⟨337999, pr337999⟩
private theorem pr338017 : PrimeCertificate 338017 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv7,pv503]) (by decide +kernel)
def pv338017 : PrimeValue := ⟨338017, pr338017⟩
private theorem pr338027 : PrimeCertificate 338027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv13001]) (by decide +kernel)
def pv338027 : PrimeValue := ⟨338027, pr338027⟩
private theorem pr338033 : PrimeCertificate 338033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv571]) (by decide +kernel)
def pv338033 : PrimeValue := ⟨338033, pr338033⟩
private theorem pr338141 : PrimeCertificate 338141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv29,pv53]) (by decide +kernel)
def pv338141 : PrimeValue := ⟨338141, pr338141⟩
private theorem pr338167 : PrimeCertificate 338167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv18787]) (by decide +kernel)
def pv338167 : PrimeValue := ⟨338167, pr338167⟩
private theorem pr338197 : PrimeCertificate 338197 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv28183]) (by decide +kernel)
def pv338197 : PrimeValue := ⟨338197, pr338197⟩
private theorem pr338207 : PrimeCertificate 338207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv15373]) (by decide +kernel)
def pv338207 : PrimeValue := ⟨338207, pr338207⟩
private theorem pr338213 : PrimeCertificate 338213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv47,pv257]) (by decide +kernel)
def pv338213 : PrimeValue := ⟨338213, pr338213⟩
private theorem pr338231 : PrimeCertificate 338231 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv149,pv227]) (by decide +kernel)
def pv338231 : PrimeValue := ⟨338231, pr338231⟩
private theorem pr338287 : PrimeCertificate 338287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv4337]) (by decide +kernel)
def pv338287 : PrimeValue := ⟨338287, pr338287⟩
private theorem pr338293 : PrimeCertificate 338293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9397]) (by decide +kernel)
def pv338293 : PrimeValue := ⟨338293, pr338293⟩
private theorem pr338323 : PrimeCertificate 338323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv113,pv499]) (by decide +kernel)
def pv338323 : PrimeValue := ⟨338323, pr338323⟩
private theorem pr338339 : PrimeCertificate 338339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv13]) (by decide +kernel)
def pv338339 : PrimeValue := ⟨338339, pr338339⟩
private theorem pr338341 : PrimeCertificate 338341 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv5639]) (by decide +kernel)
def pv338341 : PrimeValue := ⟨338341, pr338341⟩
private theorem pr338369 : PrimeCertificate 338369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv311]) (by decide +kernel)
def pv338369 : PrimeValue := ⟨338369, pr338369⟩
private theorem pr338383 : PrimeCertificate 338383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1709]) (by decide +kernel)
def pv338383 : PrimeValue := ⟨338383, pr338383⟩
private theorem pr338407 : PrimeCertificate 338407 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv56401]) (by decide +kernel)
def pv338407 : PrimeValue := ⟨338407, pr338407⟩
private theorem pr338411 : PrimeCertificate 338411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv787]) (by decide +kernel)
def pv338411 : PrimeValue := ⟨338411, pr338411⟩
private theorem pr338473 : PrimeCertificate 338473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1567]) (by decide +kernel)
def pv338473 : PrimeValue := ⟨338473, pr338473⟩
private theorem pr338497 : PrimeCertificate 338497 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv41,pv43]) (by decide +kernel)
def pv338497 : PrimeValue := ⟨338497, pr338497⟩
private theorem pr338531 : PrimeCertificate 338531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv97,pv349]) (by decide +kernel)
def pv338531 : PrimeValue := ⟨338531, pr338531⟩
private theorem pr338573 : PrimeCertificate 338573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv383]) (by decide +kernel)
def pv338573 : PrimeValue := ⟨338573, pr338573⟩
private theorem pr338579 : PrimeCertificate 338579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv4129]) (by decide +kernel)
def pv338579 : PrimeValue := ⟨338579, pr338579⟩
private theorem pr338581 : PrimeCertificate 338581 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv19]) (by decide +kernel)
def pv338581 : PrimeValue := ⟨338581, pr338581⟩
private theorem pr338659 : PrimeCertificate 338659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv56443]) (by decide +kernel)
def pv338659 : PrimeValue := ⟨338659, pr338659⟩
private theorem pr338717 : PrimeCertificate 338717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv12097]) (by decide +kernel)
def pv338717 : PrimeValue := ⟨338717, pr338717⟩
private theorem pr338731 : PrimeCertificate 338731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv1613]) (by decide +kernel)
def pv338731 : PrimeValue := ⟨338731, pr338731⟩
private theorem pr338753 : PrimeCertificate 338753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv79]) (by decide +kernel)
def pv338753 : PrimeValue := ⟨338753, pr338753⟩
private theorem pr338773 : PrimeCertificate 338773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv37,pv109]) (by decide +kernel)
def pv338773 : PrimeValue := ⟨338773, pr338773⟩
private theorem pr338777 : PrimeCertificate 338777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv47,pv53]) (by decide +kernel)
def pv338777 : PrimeValue := ⟨338777, pr338777⟩
private theorem pr338791 : PrimeCertificate 338791 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv491]) (by decide +kernel)
def pv338791 : PrimeValue := ⟨338791, pr338791⟩
private theorem pr338803 : PrimeCertificate 338803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv56467]) (by decide +kernel)
def pv338803 : PrimeValue := ⟨338803, pr338803⟩
private theorem pr338839 : PrimeCertificate 338839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv56473]) (by decide +kernel)
def pv338839 : PrimeValue := ⟨338839, pr338839⟩
private theorem pr338857 : PrimeCertificate 338857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv2017]) (by decide +kernel)
def pv338857 : PrimeValue := ⟨338857, pr338857⟩
private theorem pr338867 : PrimeCertificate 338867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv73,pv211]) (by decide +kernel)
def pv338867 : PrimeValue := ⟨338867, pr338867⟩
private theorem pr338893 : PrimeCertificate 338893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv911]) (by decide +kernel)
def pv338893 : PrimeValue := ⟨338893, pr338893⟩
private theorem pr338927 : PrimeCertificate 338927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv43,pv563]) (by decide +kernel)
def pv338927 : PrimeValue := ⟨338927, pr338927⟩
private theorem pr338959 : PrimeCertificate 338959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6277]) (by decide +kernel)
def pv338959 : PrimeValue := ⟨338959, pr338959⟩
private theorem pr339023 : PrimeCertificate 339023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv337,pv503]) (by decide +kernel)
def pv339023 : PrimeValue := ⟨339023, pr339023⟩
private theorem pr339049 : PrimeCertificate 339049 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv17,pv277]) (by decide +kernel)
def pv339049 : PrimeValue := ⟨339049, pr339049⟩
private theorem pr339067 : PrimeCertificate 339067 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv13,pv23]) (by decide +kernel)
def pv339067 : PrimeValue := ⟨339067, pr339067⟩
private theorem pr339071 : PrimeCertificate 339071 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv41,pv827]) (by decide +kernel)
def pv339071 : PrimeValue := ⟨339071, pr339071⟩
private theorem pr339103 : PrimeCertificate 339103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv18839]) (by decide +kernel)
def pv339103 : PrimeValue := ⟨339103, pr339103⟩
private theorem pr339161 : PrimeCertificate 339161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv61,pv139]) (by decide +kernel)
def pv339161 : PrimeValue := ⟨339161, pr339161⟩
private theorem pr339173 : PrimeCertificate 339173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv84793]) (by decide +kernel)
def pv339173 : PrimeValue := ⟨339173, pr339173⟩
private theorem pr339211 : PrimeCertificate 339211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3769]) (by decide +kernel)
def pv339211 : PrimeValue := ⟨339211, pr339211⟩
private theorem pr339239 : PrimeCertificate 339239 :=
  certifyPrime (q := pv23) (ls := [pv2,pv71,pv2389]) (by decide +kernel)
def pv339239 : PrimeValue := ⟨339239, pr339239⟩
private theorem pr339257 : PrimeCertificate 339257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv42407]) (by decide +kernel)
def pv339257 : PrimeValue := ⟨339257, pr339257⟩
private theorem pr339307 : PrimeCertificate 339307 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv53,pv97]) (by decide +kernel)
def pv339307 : PrimeValue := ⟨339307, pr339307⟩
private theorem pr339323 : PrimeCertificate 339323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv169661]) (by decide +kernel)
def pv339323 : PrimeValue := ⟨339323, pr339323⟩
private theorem pr339331 : PrimeCertificate 339331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11311]) (by decide +kernel)
def pv339331 : PrimeValue := ⟨339331, pr339331⟩
private theorem pr339341 : PrimeCertificate 339341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv47]) (by decide +kernel)
def pv339341 : PrimeValue := ⟨339341, pr339341⟩
private theorem pr339389 : PrimeCertificate 339389 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv17,pv23,pv31]) (by decide +kernel)
def pv339389 : PrimeValue := ⟨339389, pr339389⟩
private theorem pr339413 : PrimeCertificate 339413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv1601]) (by decide +kernel)
def pv339413 : PrimeValue := ⟨339413, pr339413⟩
private theorem pr339467 : PrimeCertificate 339467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv169733]) (by decide +kernel)
def pv339467 : PrimeValue := ⟨339467, pr339467⟩
private theorem pr339491 : PrimeCertificate 339491 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv17,pv1997]) (by decide +kernel)
def pv339491 : PrimeValue := ⟨339491, pr339491⟩
private theorem pr339557 : PrimeCertificate 339557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv67,pv181]) (by decide +kernel)
def pv339557 : PrimeValue := ⟨339557, pr339557⟩
private theorem pr339583 : PrimeCertificate 339583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv56597]) (by decide +kernel)
def pv339583 : PrimeValue := ⟨339583, pr339583⟩
private theorem pr339631 : PrimeCertificate 339631 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv11321]) (by decide +kernel)
def pv339631 : PrimeValue := ⟨339631, pr339631⟩
private theorem pr339659 : PrimeCertificate 339659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv15439]) (by decide +kernel)
def pv339659 : PrimeValue := ⟨339659, pr339659⟩
private theorem pr339671 : PrimeCertificate 339671 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv33967]) (by decide +kernel)
def pv339671 : PrimeValue := ⟨339671, pr339671⟩
private theorem pr339673 : PrimeCertificate 339673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv14153]) (by decide +kernel)
def pv339673 : PrimeValue := ⟨339673, pr339673⟩
private theorem pr339679 : PrimeCertificate 339679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv113,pv167]) (by decide +kernel)
def pv339679 : PrimeValue := ⟨339679, pr339679⟩
private theorem pr339727 : PrimeCertificate 339727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv1381]) (by decide +kernel)
def pv339727 : PrimeValue := ⟨339727, pr339727⟩
private theorem pr339749 : PrimeCertificate 339749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv157,pv541]) (by decide +kernel)
def pv339749 : PrimeValue := ⟨339749, pr339749⟩
private theorem pr339751 : PrimeCertificate 339751 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv151]) (by decide +kernel)
def pv339751 : PrimeValue := ⟨339751, pr339751⟩
private theorem pr339769 : PrimeCertificate 339769 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv339769 : PrimeValue := ⟨339769, pr339769⟩
private theorem pr339799 : PrimeCertificate 339799 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv56633]) (by decide +kernel)
def pv339799 : PrimeValue := ⟨339799, pr339799⟩
private theorem pr339811 : PrimeCertificate 339811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv47,pv241]) (by decide +kernel)
def pv339811 : PrimeValue := ⟨339811, pr339811⟩
private theorem pr339839 : PrimeCertificate 339839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv169919]) (by decide +kernel)
def pv339839 : PrimeValue := ⟨339839, pr339839⟩
private theorem pr339863 : PrimeCertificate 339863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv109,pv1559]) (by decide +kernel)
def pv339863 : PrimeValue := ⟨339863, pr339863⟩
private theorem pr339959 : PrimeCertificate 339959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv43,pv59,pv67]) (by decide +kernel)
def pv339959 : PrimeValue := ⟨339959, pr339959⟩
private theorem pr339991 : PrimeCertificate 339991 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv1619]) (by decide +kernel)
def pv339991 : PrimeValue := ⟨339991, pr339991⟩
private theorem pr340037 : PrimeCertificate 340037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv85009]) (by decide +kernel)
def pv340037 : PrimeValue := ⟨340037, pr340037⟩
private theorem pr340061 : PrimeCertificate 340061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv347]) (by decide +kernel)
def pv340061 : PrimeValue := ⟨340061, pr340061⟩
private theorem pr340063 : PrimeCertificate 340063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv157]) (by decide +kernel)
def pv340063 : PrimeValue := ⟨340063, pr340063⟩
private theorem pr340079 : PrimeCertificate 340079 :=
  certifyPrime (q := pv11) (ls := [pv2,pv23,pv7393]) (by decide +kernel)
def pv340079 : PrimeValue := ⟨340079, pr340079⟩
private theorem pr340129 : PrimeCertificate 340129 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1181]) (by decide +kernel)
def pv340129 : PrimeValue := ⟨340129, pr340129⟩
private theorem pr340183 : PrimeCertificate 340183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv18899]) (by decide +kernel)
def pv340183 : PrimeValue := ⟨340183, pr340183⟩
private theorem pr340267 : PrimeCertificate 340267 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv56711]) (by decide +kernel)
def pv340267 : PrimeValue := ⟨340267, pr340267⟩
private theorem pr340283 : PrimeCertificate 340283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv170141]) (by decide +kernel)
def pv340283 : PrimeValue := ⟨340283, pr340283⟩
private theorem pr340297 : PrimeCertificate 340297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1289]) (by decide +kernel)
def pv340297 : PrimeValue := ⟨340297, pr340297⟩
private theorem pr340339 : PrimeCertificate 340339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv131,pv433]) (by decide +kernel)
def pv340339 : PrimeValue := ⟨340339, pr340339⟩
private theorem pr340387 : PrimeCertificate 340387 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv56731]) (by decide +kernel)
def pv340387 : PrimeValue := ⟨340387, pr340387⟩
private theorem pr340393 : PrimeCertificate 340393 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv13,pv1091]) (by decide +kernel)
def pv340393 : PrimeValue := ⟨340393, pr340393⟩
private theorem pr340453 : PrimeCertificate 340453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv193]) (by decide +kernel)
def pv340453 : PrimeValue := ⟨340453, pr340453⟩
private theorem pr340477 : PrimeCertificate 340477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv1669]) (by decide +kernel)
def pv340477 : PrimeValue := ⟨340477, pr340477⟩
private theorem pr340519 : PrimeCertificate 340519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv29,pv103]) (by decide +kernel)
def pv340519 : PrimeValue := ⟨340519, pr340519⟩
private theorem pr340541 : PrimeCertificate 340541 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17027]) (by decide +kernel)
def pv340541 : PrimeValue := ⟨340541, pr340541⟩
private theorem pr340573 : PrimeCertificate 340573 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv101,pv281]) (by decide +kernel)
def pv340573 : PrimeValue := ⟨340573, pr340573⟩
private theorem pr340579 : PrimeCertificate 340579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv53]) (by decide +kernel)
def pv340579 : PrimeValue := ⟨340579, pr340579⟩
private theorem pr340583 : PrimeCertificate 340583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv113,pv137]) (by decide +kernel)
def pv340583 : PrimeValue := ⟨340583, pr340583⟩
private theorem pr340657 : PrimeCertificate 340657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv151]) (by decide +kernel)
def pv340657 : PrimeValue := ⟨340657, pr340657⟩
private theorem pr340709 : PrimeCertificate 340709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv4483]) (by decide +kernel)
def pv340709 : PrimeValue := ⟨340709, pr340709⟩
private theorem pr340757 : PrimeCertificate 340757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv6553]) (by decide +kernel)
def pv340757 : PrimeValue := ⟨340757, pr340757⟩
private theorem pr340777 : PrimeCertificate 340777 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4733]) (by decide +kernel)
def pv340777 : PrimeValue := ⟨340777, pr340777⟩
private theorem pr340789 : PrimeCertificate 340789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv4057]) (by decide +kernel)
def pv340789 : PrimeValue := ⟨340789, pr340789⟩
private theorem pr340793 : PrimeCertificate 340793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv1039]) (by decide +kernel)
def pv340793 : PrimeValue := ⟨340793, pr340793⟩
private theorem pr340811 : PrimeCertificate 340811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv173,pv197]) (by decide +kernel)
def pv340811 : PrimeValue := ⟨340811, pr340811⟩
private theorem pr340819 : PrimeCertificate 340819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv1321]) (by decide +kernel)
def pv340819 : PrimeValue := ⟨340819, pr340819⟩
private theorem pr340859 : PrimeCertificate 340859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv97,pv251]) (by decide +kernel)
def pv340859 : PrimeValue := ⟨340859, pr340859⟩
private theorem pr340889 : PrimeCertificate 340889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv42611]) (by decide +kernel)
def pv340889 : PrimeValue := ⟨340889, pr340889⟩
private theorem pr340903 : PrimeCertificate 340903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv107]) (by decide +kernel)
def pv340903 : PrimeValue := ⟨340903, pr340903⟩
private theorem pr340919 : PrimeCertificate 340919 :=
  certifyPrime (q := pv13) (ls := [pv2,pv17,pv37,pv271]) (by decide +kernel)
def pv340919 : PrimeValue := ⟨340919, pr340919⟩
private theorem pr340927 : PrimeCertificate 340927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv56821]) (by decide +kernel)
def pv340927 : PrimeValue := ⟨340927, pr340927⟩
private theorem pr340931 : PrimeCertificate 340931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv103,pv331]) (by decide +kernel)
def pv340931 : PrimeValue := ⟨340931, pr340931⟩
private theorem pr340933 : PrimeCertificate 340933 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv28411]) (by decide +kernel)
def pv340933 : PrimeValue := ⟨340933, pr340933⟩
private theorem pr341017 : PrimeCertificate 341017 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv1093]) (by decide +kernel)
def pv341017 : PrimeValue := ⟨341017, pr341017⟩
private theorem pr341123 : PrimeCertificate 341123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv79,pv127]) (by decide +kernel)
def pv341123 : PrimeValue := ⟨341123, pr341123⟩
private theorem pr341179 : PrimeCertificate 341179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv563]) (by decide +kernel)
def pv341179 : PrimeValue := ⟨341179, pr341179⟩
private theorem pr341203 : PrimeCertificate 341203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv41,pv73]) (by decide +kernel)
def pv341203 : PrimeValue := ⟨341203, pr341203⟩
private theorem pr341219 : PrimeCertificate 341219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv170609]) (by decide +kernel)
def pv341219 : PrimeValue := ⟨341219, pr341219⟩
private theorem pr341227 : PrimeCertificate 341227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv89]) (by decide +kernel)
def pv341227 : PrimeValue := ⟨341227, pr341227⟩
private theorem pr341273 : PrimeCertificate 341273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv1471]) (by decide +kernel)
def pv341273 : PrimeValue := ⟨341273, pr341273⟩
private theorem pr341287 : PrimeCertificate 341287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv5171]) (by decide +kernel)
def pv341287 : PrimeValue := ⟨341287, pr341287⟩
private theorem pr341293 : PrimeCertificate 341293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv239]) (by decide +kernel)
def pv341293 : PrimeValue := ⟨341293, pr341293⟩
private theorem pr341303 : PrimeCertificate 341303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv13127]) (by decide +kernel)
def pv341303 : PrimeValue := ⟨341303, pr341303⟩
private theorem pr341321 : PrimeCertificate 341321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv23,pv53]) (by decide +kernel)
def pv341321 : PrimeValue := ⟨341321, pr341321⟩
private theorem pr341339 : PrimeCertificate 341339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv170669]) (by decide +kernel)
def pv341339 : PrimeValue := ⟨341339, pr341339⟩
private theorem pr341501 : PrimeCertificate 341501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv683]) (by decide +kernel)
def pv341501 : PrimeValue := ⟨341501, pr341501⟩
private theorem pr341507 : PrimeCertificate 341507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv43]) (by decide +kernel)
def pv341507 : PrimeValue := ⟨341507, pr341507⟩
private theorem pr341521 : PrimeCertificate 341521 :=
  certifyPrime (q := pv61) (ls := [pv2,pv3,pv5,pv1423]) (by decide +kernel)
def pv341521 : PrimeValue := ⟨341521, pr341521⟩
private theorem pr341543 : PrimeCertificate 341543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv389,pv439]) (by decide +kernel)
def pv341543 : PrimeValue := ⟨341543, pr341543⟩
private theorem pr341587 : PrimeCertificate 341587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2711]) (by decide +kernel)
def pv341587 : PrimeValue := ⟨341587, pr341587⟩
private theorem pr341617 : PrimeCertificate 341617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv647]) (by decide +kernel)
def pv341617 : PrimeValue := ⟨341617, pr341617⟩
private theorem pr341623 : PrimeCertificate 341623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv18979]) (by decide +kernel)
def pv341623 : PrimeValue := ⟨341623, pr341623⟩
private theorem pr341629 : PrimeCertificate 341629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv83]) (by decide +kernel)
def pv341629 : PrimeValue := ⟨341629, pr341629⟩
private theorem pr341641 : PrimeCertificate 341641 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv73]) (by decide +kernel)
def pv341641 : PrimeValue := ⟨341641, pr341641⟩
private theorem pr341743 : PrimeCertificate 341743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv56957]) (by decide +kernel)
def pv341743 : PrimeValue := ⟨341743, pr341743⟩
private theorem pr341749 : PrimeCertificate 341749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv863]) (by decide +kernel)
def pv341749 : PrimeValue := ⟨341749, pr341749⟩
private theorem pr341773 : PrimeCertificate 341773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1499]) (by decide +kernel)
def pv341773 : PrimeValue := ⟨341773, pr341773⟩
private theorem pr341827 : PrimeCertificate 341827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv2477]) (by decide +kernel)
def pv341827 : PrimeValue := ⟨341827, pr341827⟩
private theorem pr341851 : PrimeCertificate 341851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv43,pv53]) (by decide +kernel)
def pv341851 : PrimeValue := ⟨341851, pr341851⟩
private theorem pr341879 : PrimeCertificate 341879 :=
  certifyPrime (q := pv13) (ls := [pv2,pv47,pv3637]) (by decide +kernel)
def pv341879 : PrimeValue := ⟨341879, pr341879⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
