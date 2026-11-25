/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table154
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table154.pv1647251
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table044
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table057
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table131
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table132

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1647251 : PrimeCertificate 1647251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv599]) (by decide +kernel)
def pv1647251 : PrimeValue := ⟨1647251, pr1647251⟩
private theorem pr1647599 : PrimeCertificate 1647599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv823799]) (by decide +kernel)
def pv1647599 : PrimeValue := ⟨1647599, pr1647599⟩
private theorem pr1647941 : PrimeCertificate 1647941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv79,pv149]) (by decide +kernel)
def pv1647941 : PrimeValue := ⟨1647941, pr1647941⟩
private theorem pr1648001 : PrimeCertificate 1648001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv103]) (by decide +kernel)
def pv1648001 : PrimeValue := ⟨1648001, pr1648001⟩
private theorem pr1648499 : PrimeCertificate 1648499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv22277]) (by decide +kernel)
def pv1648499 : PrimeValue := ⟨1648499, pr1648499⟩
private theorem pr1648529 : PrimeCertificate 1648529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv41,pv359]) (by decide +kernel)
def pv1648529 : PrimeValue := ⟨1648529, pr1648529⟩
private theorem pr1648739 : PrimeCertificate 1648739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv9059]) (by decide +kernel)
def pv1648739 : PrimeValue := ⟨1648739, pr1648739⟩
private theorem pr1648793 : PrimeCertificate 1648793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv4793]) (by decide +kernel)
def pv1648793 : PrimeValue := ⟨1648793, pr1648793⟩
private theorem pr1649003 : PrimeCertificate 1649003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv824501]) (by decide +kernel)
def pv1649003 : PrimeValue := ⟨1649003, pr1649003⟩
private theorem pr1649129 : PrimeCertificate 1649129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv101,pv157]) (by decide +kernel)
def pv1649129 : PrimeValue := ⟨1649129, pr1649129⟩
private theorem pr1649309 : PrimeCertificate 1649309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv223]) (by decide +kernel)
def pv1649309 : PrimeValue := ⟨1649309, pr1649309⟩
private theorem pr1649369 : PrimeCertificate 1649369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv29453]) (by decide +kernel)
def pv1649369 : PrimeValue := ⟨1649369, pr1649369⟩
private theorem pr1649489 : PrimeCertificate 1649489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv103093]) (by decide +kernel)
def pv1649489 : PrimeValue := ⟨1649489, pr1649489⟩
private theorem pr1649591 : PrimeCertificate 1649591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv293,pv563]) (by decide +kernel)
def pv1649591 : PrimeValue := ⟨1649591, pr1649591⟩
private theorem pr1649639 : PrimeCertificate 1649639 :=
  certifyPrime (q := pv17) (ls := [pv2,pv347,pv2377]) (by decide +kernel)
def pv1649639 : PrimeValue := ⟨1649639, pr1649639⟩
private theorem pr1650101 : PrimeCertificate 1650101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv569]) (by decide +kernel)
def pv1650101 : PrimeValue := ⟨1650101, pr1650101⟩
private theorem pr1650179 : PrimeCertificate 1650179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv509,pv1621]) (by decide +kernel)
def pv1650179 : PrimeValue := ⟨1650179, pr1650179⟩
private theorem pr1650221 : PrimeCertificate 1650221 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv13,pv577]) (by decide +kernel)
def pv1650221 : PrimeValue := ⟨1650221, pr1650221⟩
private theorem pr1650959 : PrimeCertificate 1650959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv825479]) (by decide +kernel)
def pv1650959 : PrimeValue := ⟨1650959, pr1650959⟩
private theorem pr1651151 : PrimeCertificate 1651151 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv33023]) (by decide +kernel)
def pv1651151 : PrimeValue := ⟨1651151, pr1651151⟩
private theorem pr1651229 : PrimeCertificate 1651229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv412807]) (by decide +kernel)
def pv1651229 : PrimeValue := ⟨1651229, pr1651229⟩
private theorem pr1651283 : PrimeCertificate 1651283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv12323]) (by decide +kernel)
def pv1651283 : PrimeValue := ⟨1651283, pr1651283⟩
private theorem pr1651493 : PrimeCertificate 1651493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv29,pv619]) (by decide +kernel)
def pv1651493 : PrimeValue := ⟨1651493, pr1651493⟩
private theorem pr1651511 : PrimeCertificate 1651511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv23593]) (by decide +kernel)
def pv1651511 : PrimeValue := ⟨1651511, pr1651511⟩
private theorem pr1651691 : PrimeCertificate 1651691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv331,pv499]) (by decide +kernel)
def pv1651691 : PrimeValue := ⟨1651691, pr1651691⟩
private theorem pr1652039 : PrimeCertificate 1652039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv826019]) (by decide +kernel)
def pv1652039 : PrimeValue := ⟨1652039, pr1652039⟩
private theorem pr1652243 : PrimeCertificate 1652243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv151,pv5471]) (by decide +kernel)
def pv1652243 : PrimeValue := ⟨1652243, pr1652243⟩
private theorem pr1652741 : PrimeCertificate 1652741 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv4861]) (by decide +kernel)
def pv1652741 : PrimeValue := ⟨1652741, pr1652741⟩
private theorem pr1652879 : PrimeCertificate 1652879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv487,pv1697]) (by decide +kernel)
def pv1652879 : PrimeValue := ⟨1652879, pr1652879⟩
private theorem pr1653293 : PrimeCertificate 1653293 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv67,pv199]) (by decide +kernel)
def pv1653293 : PrimeValue := ⟨1653293, pr1653293⟩
private theorem pr1653329 : PrimeCertificate 1653329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv103333]) (by decide +kernel)
def pv1653329 : PrimeValue := ⟨1653329, pr1653329⟩
private theorem pr1653611 : PrimeCertificate 1653611 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv23623]) (by decide +kernel)
def pv1653611 : PrimeValue := ⟨1653611, pr1653611⟩
private theorem pr1653689 : PrimeCertificate 1653689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv421,pv491]) (by decide +kernel)
def pv1653689 : PrimeValue := ⟨1653689, pr1653689⟩
private theorem pr1653929 : PrimeCertificate 1653929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv7129]) (by decide +kernel)
def pv1653929 : PrimeValue := ⟨1653929, pr1653929⟩
private theorem pr1654013 : PrimeCertificate 1654013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197,pv2099]) (by decide +kernel)
def pv1654013 : PrimeValue := ⟨1654013, pr1654013⟩
private theorem pr1654043 : PrimeCertificate 1654043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv63617]) (by decide +kernel)
def pv1654043 : PrimeValue := ⟨1654043, pr1654043⟩
private theorem pr1654199 : PrimeCertificate 1654199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv61,pv149]) (by decide +kernel)
def pv1654199 : PrimeValue := ⟨1654199, pr1654199⟩
private theorem pr1654223 : PrimeCertificate 1654223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv26681]) (by decide +kernel)
def pv1654223 : PrimeValue := ⟨1654223, pr1654223⟩
private theorem pr1654241 : PrimeCertificate 1654241 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv7,pv211]) (by decide +kernel)
def pv1654241 : PrimeValue := ⟨1654241, pr1654241⟩
private theorem pr1654673 : PrimeCertificate 1654673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv5443]) (by decide +kernel)
def pv1654673 : PrimeValue := ⟨1654673, pr1654673⟩
private theorem pr1655039 : PrimeCertificate 1655039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv977]) (by decide +kernel)
def pv1655039 : PrimeValue := ⟨1655039, pr1655039⟩
private theorem pr1655141 : PrimeCertificate 1655141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv82757]) (by decide +kernel)
def pv1655141 : PrimeValue := ⟨1655141, pr1655141⟩
private theorem pr1655963 : PrimeCertificate 1655963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv10753]) (by decide +kernel)
def pv1655963 : PrimeValue := ⟨1655963, pr1655963⟩
private theorem pr1655999 : PrimeCertificate 1655999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv47,pv79,pv223]) (by decide +kernel)
def pv1655999 : PrimeValue := ⟨1655999, pr1655999⟩
private theorem pr1656251 : PrimeCertificate 1656251 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv53]) (by decide +kernel)
def pv1656251 : PrimeValue := ⟨1656251, pr1656251⟩
private theorem pr1656311 : PrimeCertificate 1656311 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv9743]) (by decide +kernel)
def pv1656311 : PrimeValue := ⟨1656311, pr1656311⟩
private theorem pr1656383 : PrimeCertificate 1656383 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv19,pv479]) (by decide +kernel)
def pv1656383 : PrimeValue := ⟨1656383, pr1656383⟩
private theorem pr1656521 : PrimeCertificate 1656521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv41413]) (by decide +kernel)
def pv1656521 : PrimeValue := ⟨1656521, pr1656521⟩
private theorem pr1656533 : PrimeCertificate 1656533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv9631]) (by decide +kernel)
def pv1656533 : PrimeValue := ⟨1656533, pr1656533⟩
private theorem pr1656659 : PrimeCertificate 1656659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv433,pv1913]) (by decide +kernel)
def pv1656659 : PrimeValue := ⟨1656659, pr1656659⟩
private theorem pr1656719 : PrimeCertificate 1656719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17,pv6961]) (by decide +kernel)
def pv1656719 : PrimeValue := ⟨1656719, pr1656719⟩
private theorem pr1656911 : PrimeCertificate 1656911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv67,pv2473]) (by decide +kernel)
def pv1656911 : PrimeValue := ⟨1656911, pr1656911⟩
private theorem pr1657013 : PrimeCertificate 1657013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv31,pv83]) (by decide +kernel)
def pv1657013 : PrimeValue := ⟨1657013, pr1657013⟩
private theorem pr1657121 : PrimeCertificate 1657121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv10357]) (by decide +kernel)
def pv1657121 : PrimeValue := ⟨1657121, pr1657121⟩
private theorem pr1657889 : PrimeCertificate 1657889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv103,pv503]) (by decide +kernel)
def pv1657889 : PrimeValue := ⟨1657889, pr1657889⟩
private theorem pr1658201 : PrimeCertificate 1658201 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv8291]) (by decide +kernel)
def pv1658201 : PrimeValue := ⟨1658201, pr1658201⟩
private theorem pr1658213 : PrimeCertificate 1658213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv414553]) (by decide +kernel)
def pv1658213 : PrimeValue := ⟨1658213, pr1658213⟩
private theorem pr1658243 : PrimeCertificate 1658243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv829121]) (by decide +kernel)
def pv1658243 : PrimeValue := ⟨1658243, pr1658243⟩
private theorem pr1658309 : PrimeCertificate 1658309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv414577]) (by decide +kernel)
def pv1658309 : PrimeValue := ⟨1658309, pr1658309⟩
private theorem pr1658411 : PrimeCertificate 1658411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv12757]) (by decide +kernel)
def pv1658411 : PrimeValue := ⟨1658411, pr1658411⟩
private theorem pr1658483 : PrimeCertificate 1658483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv118463]) (by decide +kernel)
def pv1658483 : PrimeValue := ⟨1658483, pr1658483⟩
private theorem pr1658561 : PrimeCertificate 1658561 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv71,pv73]) (by decide +kernel)
def pv1658561 : PrimeValue := ⟨1658561, pr1658561⟩
private theorem pr1658711 : PrimeCertificate 1658711 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv37,pv4483]) (by decide +kernel)
def pv1658711 : PrimeValue := ⟨1658711, pr1658711⟩
private theorem pr1658753 : PrimeCertificate 1658753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12959]) (by decide +kernel)
def pv1658753 : PrimeValue := ⟨1658753, pr1658753⟩
private theorem pr1658801 : PrimeCertificate 1658801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv13,pv29]) (by decide +kernel)
def pv1658801 : PrimeValue := ⟨1658801, pr1658801⟩
private theorem pr1659041 : PrimeCertificate 1659041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv10369]) (by decide +kernel)
def pv1659041 : PrimeValue := ⟨1659041, pr1659041⟩
private theorem pr1659083 : PrimeCertificate 1659083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv36067]) (by decide +kernel)
def pv1659083 : PrimeValue := ⟨1659083, pr1659083⟩
private theorem pr1659239 : PrimeCertificate 1659239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv16931]) (by decide +kernel)
def pv1659239 : PrimeValue := ⟨1659239, pr1659239⟩
private theorem pr1659299 : PrimeCertificate 1659299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv359,pv2311]) (by decide +kernel)
def pv1659299 : PrimeValue := ⟨1659299, pr1659299⟩
private theorem pr1659401 : PrimeCertificate 1659401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv8297]) (by decide +kernel)
def pv1659401 : PrimeValue := ⟨1659401, pr1659401⟩
private theorem pr1659491 : PrimeCertificate 1659491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv151,pv157]) (by decide +kernel)
def pv1659491 : PrimeValue := ⟨1659491, pr1659491⟩
private theorem pr1659533 : PrimeCertificate 1659533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8467]) (by decide +kernel)
def pv1659533 : PrimeValue := ⟨1659533, pr1659533⟩
private theorem pr1659551 : PrimeCertificate 1659551 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv33191]) (by decide +kernel)
def pv1659551 : PrimeValue := ⟨1659551, pr1659551⟩
private theorem pr1659719 : PrimeCertificate 1659719 :=
  certifyPrime (q := pv23) (ls := [pv2,pv467,pv1777]) (by decide +kernel)
def pv1659719 : PrimeValue := ⟨1659719, pr1659719⟩
private theorem pr1659809 : PrimeCertificate 1659809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv51869]) (by decide +kernel)
def pv1659809 : PrimeValue := ⟨1659809, pr1659809⟩
private theorem pr1659851 : PrimeCertificate 1659851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv89,pv373]) (by decide +kernel)
def pv1659851 : PrimeValue := ⟨1659851, pr1659851⟩
private theorem pr1659881 : PrimeCertificate 1659881 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv17,pv2441]) (by decide +kernel)
def pv1659881 : PrimeValue := ⟨1659881, pr1659881⟩
private theorem pr1660259 : PrimeCertificate 1660259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv43691]) (by decide +kernel)
def pv1660259 : PrimeValue := ⟨1660259, pr1660259⟩
private theorem pr1660283 : PrimeCertificate 1660283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv63857]) (by decide +kernel)
def pv1660283 : PrimeValue := ⟨1660283, pr1660283⟩
private theorem pr1660469 : PrimeCertificate 1660469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv571,pv727]) (by decide +kernel)
def pv1660469 : PrimeValue := ⟨1660469, pr1660469⟩
private theorem pr1660553 : PrimeCertificate 1660553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv207569]) (by decide +kernel)
def pv1660553 : PrimeValue := ⟨1660553, pr1660553⟩
private theorem pr1660559 : PrimeCertificate 1660559 :=
  certifyPrime (q := pv19) (ls := [pv2,pv830279]) (by decide +kernel)
def pv1660559 : PrimeValue := ⟨1660559, pr1660559⟩
private theorem pr1660601 : PrimeCertificate 1660601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv23]) (by decide +kernel)
def pv1660601 : PrimeValue := ⟨1660601, pr1660601⟩
private theorem pr1660661 : PrimeCertificate 1660661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv1931]) (by decide +kernel)
def pv1660661 : PrimeValue := ⟨1660661, pr1660661⟩
private theorem pr1660709 : PrimeCertificate 1660709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv37,pv229]) (by decide +kernel)
def pv1660709 : PrimeValue := ⟨1660709, pr1660709⟩
private theorem pr1660751 : PrimeCertificate 1660751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv73]) (by decide +kernel)
def pv1660751 : PrimeValue := ⟨1660751, pr1660751⟩
private theorem pr1660943 : PrimeCertificate 1660943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv109,pv401]) (by decide +kernel)
def pv1660943 : PrimeValue := ⟨1660943, pr1660943⟩
private theorem pr1661021 : PrimeCertificate 1661021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv1567]) (by decide +kernel)
def pv1661021 : PrimeValue := ⟨1661021, pr1661021⟩
private theorem pr1661069 : PrimeCertificate 1661069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv3881]) (by decide +kernel)
def pv1661069 : PrimeValue := ⟨1661069, pr1661069⟩
private theorem pr1661273 : PrimeCertificate 1661273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv281,pv739]) (by decide +kernel)
def pv1661273 : PrimeValue := ⟨1661273, pr1661273⟩
private theorem pr1661969 : PrimeCertificate 1661969 :=
  certifyPrime (q := pv29) (ls := [pv2,pv7,pv11,pv19,pv71]) (by decide +kernel)
def pv1661969 : PrimeValue := ⟨1661969, pr1661969⟩
private theorem pr1662161 : PrimeCertificate 1662161 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv79,pv263]) (by decide +kernel)
def pv1662161 : PrimeValue := ⟨1662161, pr1662161⟩
private theorem pr1662389 : PrimeCertificate 1662389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv4567]) (by decide +kernel)
def pv1662389 : PrimeValue := ⟨1662389, pr1662389⟩
private theorem pr1662491 : PrimeCertificate 1662491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv83,pv2003]) (by decide +kernel)
def pv1662491 : PrimeValue := ⟨1662491, pr1662491⟩
private theorem pr1662593 : PrimeCertificate 1662593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv419]) (by decide +kernel)
def pv1662593 : PrimeValue := ⟨1662593, pr1662593⟩
private theorem pr1662701 : PrimeCertificate 1662701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv1279]) (by decide +kernel)
def pv1662701 : PrimeValue := ⟨1662701, pr1662701⟩
private theorem pr1662893 : PrimeCertificate 1662893 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv5399]) (by decide +kernel)
def pv1662893 : PrimeValue := ⟨1662893, pr1662893⟩
private theorem pr1662929 : PrimeCertificate 1662929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv53]) (by decide +kernel)
def pv1662929 : PrimeValue := ⟨1662929, pr1662929⟩
private theorem pr1663391 : PrimeCertificate 1663391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv181,pv919]) (by decide +kernel)
def pv1663391 : PrimeValue := ⟨1663391, pr1663391⟩
private theorem pr1663589 : PrimeCertificate 1663589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv4673]) (by decide +kernel)
def pv1663589 : PrimeValue := ⟨1663589, pr1663589⟩
private theorem pr1663619 : PrimeCertificate 1663619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv75619]) (by decide +kernel)
def pv1663619 : PrimeValue := ⟨1663619, pr1663619⟩
private theorem pr1663703 : PrimeCertificate 1663703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv831851]) (by decide +kernel)
def pv1663703 : PrimeValue := ⟨1663703, pr1663703⟩
private theorem pr1663709 : PrimeCertificate 1663709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv13417]) (by decide +kernel)
def pv1663709 : PrimeValue := ⟨1663709, pr1663709⟩
private theorem pr1663919 : PrimeCertificate 1663919 :=
  certifyPrime (q := pv11) (ls := [pv2,pv59,pv239]) (by decide +kernel)
def pv1663919 : PrimeValue := ⟨1663919, pr1663919⟩
private theorem pr1664009 : PrimeCertificate 1664009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv208001]) (by decide +kernel)
def pv1664009 : PrimeValue := ⟨1664009, pr1664009⟩
private theorem pr1664021 : PrimeCertificate 1664021 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv19,pv29,pv151]) (by decide +kernel)
def pv1664021 : PrimeValue := ⟨1664021, pr1664021⟩
private theorem pr1664501 : PrimeCertificate 1664501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3329]) (by decide +kernel)
def pv1664501 : PrimeValue := ⟨1664501, pr1664501⟩
private theorem pr1664543 : PrimeCertificate 1664543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv29,pv2609]) (by decide +kernel)
def pv1664543 : PrimeValue := ⟨1664543, pr1664543⟩
private theorem pr1664633 : PrimeCertificate 1664633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv251,pv829]) (by decide +kernel)
def pv1664633 : PrimeValue := ⟨1664633, pr1664633⟩
private theorem pr1664651 : PrimeCertificate 1664651 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv197]) (by decide +kernel)
def pv1664651 : PrimeValue := ⟨1664651, pr1664651⟩
private theorem pr1664681 : PrimeCertificate 1664681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv41617]) (by decide +kernel)
def pv1664681 : PrimeValue := ⟨1664681, pr1664681⟩
private theorem pr1664711 : PrimeCertificate 1664711 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv166471]) (by decide +kernel)
def pv1664711 : PrimeValue := ⟨1664711, pr1664711⟩
private theorem pr1664909 : PrimeCertificate 1664909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv97,pv613]) (by decide +kernel)
def pv1664909 : PrimeValue := ⟨1664909, pr1664909⟩
private theorem pr1665143 : PrimeCertificate 1665143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv157,pv5303]) (by decide +kernel)
def pv1665143 : PrimeValue := ⟨1665143, pr1665143⟩
private theorem pr1665161 : PrimeCertificate 1665161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv313]) (by decide +kernel)
def pv1665161 : PrimeValue := ⟨1665161, pr1665161⟩
private theorem pr1665263 : PrimeCertificate 1665263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv832631]) (by decide +kernel)
def pv1665263 : PrimeValue := ⟨1665263, pr1665263⟩
private theorem pr1665479 : PrimeCertificate 1665479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv79,pv83,pv127]) (by decide +kernel)
def pv1665479 : PrimeValue := ⟨1665479, pr1665479⟩
private theorem pr1665623 : PrimeCertificate 1665623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv118973]) (by decide +kernel)
def pv1665623 : PrimeValue := ⟨1665623, pr1665623⟩
private theorem pr1665659 : PrimeCertificate 1665659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167,pv4987]) (by decide +kernel)
def pv1665659 : PrimeValue := ⟨1665659, pr1665659⟩
private theorem pr1665899 : PrimeCertificate 1665899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv3769]) (by decide +kernel)
def pv1665899 : PrimeValue := ⟨1665899, pr1665899⟩
private theorem pr1666019 : PrimeCertificate 1666019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv833009]) (by decide +kernel)
def pv1666019 : PrimeValue := ⟨1666019, pr1666019⟩
private theorem pr1666139 : PrimeCertificate 1666139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv251,pv3319]) (by decide +kernel)
def pv1666139 : PrimeValue := ⟨1666139, pr1666139⟩
private theorem pr1666403 : PrimeCertificate 1666403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv833201]) (by decide +kernel)
def pv1666403 : PrimeValue := ⟨1666403, pr1666403⟩
private theorem pr1666421 : PrimeCertificate 1666421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11903]) (by decide +kernel)
def pv1666421 : PrimeValue := ⟨1666421, pr1666421⟩
private theorem pr1666481 : PrimeCertificate 1666481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv563]) (by decide +kernel)
def pv1666481 : PrimeValue := ⟨1666481, pr1666481⟩
private theorem pr1666523 : PrimeCertificate 1666523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv5827]) (by decide +kernel)
def pv1666523 : PrimeValue := ⟨1666523, pr1666523⟩
private theorem pr1666559 : PrimeCertificate 1666559 :=
  certifyPrime (q := pv11) (ls := [pv2,pv67,pv12437]) (by decide +kernel)
def pv1666559 : PrimeValue := ⟨1666559, pr1666559⟩
private theorem pr1667279 : PrimeCertificate 1667279 :=
  certifyPrime (q := pv11) (ls := [pv2,pv47,pv17737]) (by decide +kernel)
def pv1667279 : PrimeValue := ⟨1667279, pr1667279⟩
private theorem pr1667579 : PrimeCertificate 1667579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv229,pv331]) (by decide +kernel)
def pv1667579 : PrimeValue := ⟨1667579, pr1667579⟩
private theorem pr1667651 : PrimeCertificate 1667651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv33353]) (by decide +kernel)
def pv1667651 : PrimeValue := ⟨1667651, pr1667651⟩
private theorem pr1667873 : PrimeCertificate 1667873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv52121]) (by decide +kernel)
def pv1667873 : PrimeValue := ⟨1667873, pr1667873⟩
private theorem pr1667933 : PrimeCertificate 1667933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv71,pv839]) (by decide +kernel)
def pv1667933 : PrimeValue := ⟨1667933, pr1667933⟩
private theorem pr1667951 : PrimeCertificate 1667951 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv33359]) (by decide +kernel)
def pv1667951 : PrimeValue := ⟨1667951, pr1667951⟩
private theorem pr1668083 : PrimeCertificate 1668083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv64157]) (by decide +kernel)
def pv1668083 : PrimeValue := ⟨1668083, pr1668083⟩
private theorem pr1668113 : PrimeCertificate 1668113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv137,pv761]) (by decide +kernel)
def pv1668113 : PrimeValue := ⟨1668113, pr1668113⟩
private theorem pr1668119 : PrimeCertificate 1668119 :=
  certifyPrime (q := pv13) (ls := [pv2,pv834059]) (by decide +kernel)
def pv1668119 : PrimeValue := ⟨1668119, pr1668119⟩
private theorem pr1668449 : PrimeCertificate 1668449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv3067]) (by decide +kernel)
def pv1668449 : PrimeValue := ⟨1668449, pr1668449⟩
private theorem pr1668503 : PrimeCertificate 1668503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv149,pv509]) (by decide +kernel)
def pv1668503 : PrimeValue := ⟨1668503, pr1668503⟩
private theorem pr1668521 : PrimeCertificate 1668521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv59,pv101]) (by decide +kernel)
def pv1668521 : PrimeValue := ⟨1668521, pr1668521⟩
private theorem pr1668791 : PrimeCertificate 1668791 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv109,pv1531]) (by decide +kernel)
def pv1668791 : PrimeValue := ⟨1668791, pr1668791⟩
private theorem pr1668911 : PrimeCertificate 1668911 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv157,pv1063]) (by decide +kernel)
def pv1668911 : PrimeValue := ⟨1668911, pr1668911⟩
private theorem pr1669301 : PrimeCertificate 1669301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv16693]) (by decide +kernel)
def pv1669301 : PrimeValue := ⟨1669301, pr1669301⟩
private theorem pr1669313 : PrimeCertificate 1669313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv26083]) (by decide +kernel)
def pv1669313 : PrimeValue := ⟨1669313, pr1669313⟩
private theorem pr1669469 : PrimeCertificate 1669469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv24551]) (by decide +kernel)
def pv1669469 : PrimeValue := ⟨1669469, pr1669469⟩
private theorem pr1669571 : PrimeCertificate 1669571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv17,pv23,pv61]) (by decide +kernel)
def pv1669571 : PrimeValue := ⟨1669571, pr1669571⟩
private theorem pr1669589 : PrimeCertificate 1669589 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv37,pv389]) (by decide +kernel)
def pv1669589 : PrimeValue := ⟨1669589, pr1669589⟩
private theorem pr1669751 : PrimeCertificate 1669751 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv6679]) (by decide +kernel)
def pv1669751 : PrimeValue := ⟨1669751, pr1669751⟩
private theorem pr1669763 : PrimeCertificate 1669763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv28789]) (by decide +kernel)
def pv1669763 : PrimeValue := ⟨1669763, pr1669763⟩
private theorem pr1669781 : PrimeCertificate 1669781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11927]) (by decide +kernel)
def pv1669781 : PrimeValue := ⟨1669781, pr1669781⟩
private theorem pr1669793 : PrimeCertificate 1669793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv52181]) (by decide +kernel)
def pv1669793 : PrimeValue := ⟨1669793, pr1669793⟩
private theorem pr1669931 : PrimeCertificate 1669931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv4073]) (by decide +kernel)
def pv1669931 : PrimeValue := ⟨1669931, pr1669931⟩
private theorem pr1670183 : PrimeCertificate 1670183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv49123]) (by decide +kernel)
def pv1670183 : PrimeValue := ⟨1670183, pr1670183⟩
private theorem pr1670213 : PrimeCertificate 1670213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv417553]) (by decide +kernel)
def pv1670213 : PrimeValue := ⟨1670213, pr1670213⟩
private theorem pr1670633 : PrimeCertificate 1670633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv29,pv379]) (by decide +kernel)
def pv1670633 : PrimeValue := ⟨1670633, pr1670633⟩
private theorem pr1670741 : PrimeCertificate 1670741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv83537]) (by decide +kernel)
def pv1670741 : PrimeValue := ⟨1670741, pr1670741⟩
private theorem pr1670813 : PrimeCertificate 1670813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv23,pv127]) (by decide +kernel)
def pv1670813 : PrimeValue := ⟨1670813, pr1670813⟩
private theorem pr1670891 : PrimeCertificate 1670891 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv12853]) (by decide +kernel)
def pv1670891 : PrimeValue := ⟨1670891, pr1670891⟩
private theorem pr1671161 : PrimeCertificate 1671161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv41,pv1019]) (by decide +kernel)
def pv1671161 : PrimeValue := ⟨1671161, pr1671161⟩
private theorem pr1671209 : PrimeCertificate 1671209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv2713]) (by decide +kernel)
def pv1671209 : PrimeValue := ⟨1671209, pr1671209⟩
private theorem pr1671311 : PrimeCertificate 1671311 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv97,pv1723]) (by decide +kernel)
def pv1671311 : PrimeValue := ⟨1671311, pr1671311⟩
private theorem pr1671359 : PrimeCertificate 1671359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv64283]) (by decide +kernel)
def pv1671359 : PrimeValue := ⟨1671359, pr1671359⟩
private theorem pr1671443 : PrimeCertificate 1671443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv835721]) (by decide +kernel)
def pv1671443 : PrimeValue := ⟨1671443, pr1671443⟩
private theorem pr1671671 : PrimeCertificate 1671671 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv11,pv13,pv167]) (by decide +kernel)
def pv1671671 : PrimeValue := ⟨1671671, pr1671671⟩
private theorem pr1672271 : PrimeCertificate 1672271 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv43,pv3889]) (by decide +kernel)
def pv1672271 : PrimeValue := ⟨1672271, pr1672271⟩
private theorem pr1672523 : PrimeCertificate 1672523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv239,pv3499]) (by decide +kernel)
def pv1672523 : PrimeValue := ⟨1672523, pr1672523⟩
private theorem pr1672631 : PrimeCertificate 1672631 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv17,pv9839]) (by decide +kernel)
def pv1672631 : PrimeValue := ⟨1672631, pr1672631⟩
private theorem pr1673069 : PrimeCertificate 1673069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv14423]) (by decide +kernel)
def pv1673069 : PrimeValue := ⟨1673069, pr1673069⟩
private theorem pr1673099 : PrimeCertificate 1673099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv127,pv941]) (by decide +kernel)
def pv1673099 : PrimeValue := ⟨1673099, pr1673099⟩
private theorem pr1673279 : PrimeCertificate 1673279 :=
  certifyPrime (q := pv11) (ls := [pv2,pv373,pv2243]) (by decide +kernel)
def pv1673279 : PrimeValue := ⟨1673279, pr1673279⟩
private theorem pr1673489 : PrimeCertificate 1673489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv104593]) (by decide +kernel)
def pv1673489 : PrimeValue := ⟨1673489, pr1673489⟩
private theorem pr1673543 : PrimeCertificate 1673543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv191,pv337]) (by decide +kernel)
def pv1673543 : PrimeValue := ⟨1673543, pr1673543⟩
private theorem pr1673663 : PrimeCertificate 1673663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv283,pv2957]) (by decide +kernel)
def pv1673663 : PrimeValue := ⟨1673663, pr1673663⟩
private theorem pr1673723 : PrimeCertificate 1673723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv836861]) (by decide +kernel)
def pv1673723 : PrimeValue := ⟨1673723, pr1673723⟩
private theorem pr1673849 : PrimeCertificate 1673849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv23,pv827]) (by decide +kernel)
def pv1673849 : PrimeValue := ⟨1673849, pr1673849⟩
private theorem pr1673933 : PrimeCertificate 1673933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv32191]) (by decide +kernel)
def pv1673933 : PrimeValue := ⟨1673933, pr1673933⟩
private theorem pr1673993 : PrimeCertificate 1673993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv209249]) (by decide +kernel)
def pv1673993 : PrimeValue := ⟨1673993, pr1673993⟩
private theorem pr1674203 : PrimeCertificate 1674203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv293,pv2857]) (by decide +kernel)
def pv1674203 : PrimeValue := ⟨1674203, pr1674203⟩
private theorem pr1674209 : PrimeCertificate 1674209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv113,pv463]) (by decide +kernel)
def pv1674209 : PrimeValue := ⟨1674209, pr1674209⟩
private theorem pr1674353 : PrimeCertificate 1674353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv227,pv461]) (by decide +kernel)
def pv1674353 : PrimeValue := ⟨1674353, pr1674353⟩
private theorem pr1674581 : PrimeCertificate 1674581 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv101,pv829]) (by decide +kernel)
def pv1674581 : PrimeValue := ⟨1674581, pr1674581⟩
private theorem pr1675013 : PrimeCertificate 1675013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv7901]) (by decide +kernel)
def pv1675013 : PrimeValue := ⟨1675013, pr1675013⟩
private theorem pr1675073 : PrimeCertificate 1675073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv3739]) (by decide +kernel)
def pv1675073 : PrimeValue := ⟨1675073, pr1675073⟩
private theorem pr1675109 : PrimeCertificate 1675109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv9739]) (by decide +kernel)
def pv1675109 : PrimeValue := ⟨1675109, pr1675109⟩
private theorem pr1675139 : PrimeCertificate 1675139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv22637]) (by decide +kernel)
def pv1675139 : PrimeValue := ⟨1675139, pr1675139⟩
private theorem pr1675259 : PrimeCertificate 1675259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv64433]) (by decide +kernel)
def pv1675259 : PrimeValue := ⟨1675259, pr1675259⟩
private theorem pr1675361 : PrimeCertificate 1675361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv283]) (by decide +kernel)
def pv1675361 : PrimeValue := ⟨1675361, pr1675361⟩
private theorem pr1675631 : PrimeCertificate 1675631 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv15233]) (by decide +kernel)
def pv1675631 : PrimeValue := ⟨1675631, pr1675631⟩
private theorem pr1675763 : PrimeCertificate 1675763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv211]) (by decide +kernel)
def pv1675763 : PrimeValue := ⟨1675763, pr1675763⟩
private theorem pr1675799 : PrimeCertificate 1675799 :=
  certifyPrime (q := pv11) (ls := [pv2,pv31,pv151,pv179]) (by decide +kernel)
def pv1675799 : PrimeValue := ⟨1675799, pr1675799⟩
private theorem pr1676393 : PrimeCertificate 1676393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv209549]) (by decide +kernel)
def pv1676393 : PrimeValue := ⟨1676393, pr1676393⟩
private theorem pr1676501 : PrimeCertificate 1676501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv479]) (by decide +kernel)
def pv1676501 : PrimeValue := ⟨1676501, pr1676501⟩
private theorem pr1676621 : PrimeCertificate 1676621 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv7621]) (by decide +kernel)
def pv1676621 : PrimeValue := ⟨1676621, pr1676621⟩
private theorem pr1676651 : PrimeCertificate 1676651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv33533]) (by decide +kernel)
def pv1676651 : PrimeValue := ⟨1676651, pr1676651⟩
private theorem pr1676813 : PrimeCertificate 1676813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv24659]) (by decide +kernel)
def pv1676813 : PrimeValue := ⟨1676813, pr1676813⟩
private theorem pr1676963 : PrimeCertificate 1676963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv119783]) (by decide +kernel)
def pv1676963 : PrimeValue := ⟨1676963, pr1676963⟩
private theorem pr1677251 : PrimeCertificate 1677251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6709]) (by decide +kernel)
def pv1677251 : PrimeValue := ⟨1677251, pr1677251⟩
private theorem pr1677323 : PrimeCertificate 1677323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv49333]) (by decide +kernel)
def pv1677323 : PrimeValue := ⟨1677323, pr1677323⟩
private theorem pr1677353 : PrimeCertificate 1677353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv209669]) (by decide +kernel)
def pv1677353 : PrimeValue := ⟨1677353, pr1677353⟩
private theorem pr1677743 : PrimeCertificate 1677743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv76261]) (by decide +kernel)
def pv1677743 : PrimeValue := ⟨1677743, pr1677743⟩
private theorem pr1678073 : PrimeCertificate 1678073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv19069]) (by decide +kernel)
def pv1678073 : PrimeValue := ⟨1678073, pr1678073⟩
private theorem pr1678133 : PrimeCertificate 1678133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv281,pv1493]) (by decide +kernel)
def pv1678133 : PrimeValue := ⟨1678133, pr1678133⟩
private theorem pr1678151 : PrimeCertificate 1678151 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv33563]) (by decide +kernel)
def pv1678151 : PrimeValue := ⟨1678151, pr1678151⟩
private theorem pr1678349 : PrimeCertificate 1678349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8563]) (by decide +kernel)
def pv1678349 : PrimeValue := ⟨1678349, pr1678349⟩
private theorem pr1678361 : PrimeCertificate 1678361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv41959]) (by decide +kernel)
def pv1678361 : PrimeValue := ⟨1678361, pr1678361⟩
private theorem pr1678739 : PrimeCertificate 1678739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv839369]) (by decide +kernel)
def pv1678739 : PrimeValue := ⟨1678739, pr1678739⟩
private theorem pr1678889 : PrimeCertificate 1678889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv209861]) (by decide +kernel)
def pv1678889 : PrimeValue := ⟨1678889, pr1678889⟩
private theorem pr1679033 : PrimeCertificate 1679033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv5119]) (by decide +kernel)
def pv1679033 : PrimeValue := ⟨1679033, pr1679033⟩
private theorem pr1679273 : PrimeCertificate 1679273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv157,pv191]) (by decide +kernel)
def pv1679273 : PrimeValue := ⟨1679273, pr1679273⟩
private theorem pr1679351 : PrimeCertificate 1679351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv33587]) (by decide +kernel)
def pv1679351 : PrimeValue := ⟨1679351, pr1679351⟩
private theorem pr1679963 : PrimeCertificate 1679963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv839981]) (by decide +kernel)
def pv1679963 : PrimeValue := ⟨1679963, pr1679963⟩
private theorem pr1680149 : PrimeCertificate 1680149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv420037]) (by decide +kernel)
def pv1680149 : PrimeValue := ⟨1680149, pr1680149⟩
private theorem pr1680359 : PrimeCertificate 1680359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv840179]) (by decide +kernel)
def pv1680359 : PrimeValue := ⟨1680359, pr1680359⟩
private theorem pr1680491 : PrimeCertificate 1680491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv24007]) (by decide +kernel)
def pv1680491 : PrimeValue := ⟨1680491, pr1680491⟩
private theorem pr1680803 : PrimeCertificate 1680803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv643,pv1307]) (by decide +kernel)
def pv1680803 : PrimeValue := ⟨1680803, pr1680803⟩
private theorem pr1680839 : PrimeCertificate 1680839 :=
  certifyPrime (q := pv19) (ls := [pv2,pv359,pv2341]) (by decide +kernel)
def pv1680839 : PrimeValue := ⟨1680839, pr1680839⟩
private theorem pr1681103 : PrimeCertificate 1681103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv809,pv1039]) (by decide +kernel)
def pv1681103 : PrimeValue := ⟨1681103, pr1681103⟩
private theorem pr1681259 : PrimeCertificate 1681259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv389,pv2161]) (by decide +kernel)
def pv1681259 : PrimeValue := ⟨1681259, pr1681259⟩
private theorem pr1681721 : PrimeCertificate 1681721 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv42043]) (by decide +kernel)
def pv1681721 : PrimeValue := ⟨1681721, pr1681721⟩
private theorem pr1682069 : PrimeCertificate 1682069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv5323]) (by decide +kernel)
def pv1682069 : PrimeValue := ⟨1682069, pr1682069⟩
private theorem pr1682111 : PrimeCertificate 1682111 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv168211]) (by decide +kernel)
def pv1682111 : PrimeValue := ⟨1682111, pr1682111⟩
private theorem pr1682363 : PrimeCertificate 1682363 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv76471]) (by decide +kernel)
def pv1682363 : PrimeValue := ⟨1682363, pr1682363⟩
private theorem pr1682399 : PrimeCertificate 1682399 :=
  certifyPrime (q := pv11) (ls := [pv2,pv353,pv2383]) (by decide +kernel)
def pv1682399 : PrimeValue := ⟨1682399, pr1682399⟩
private theorem pr1682489 : PrimeCertificate 1682489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv11069]) (by decide +kernel)
def pv1682489 : PrimeValue := ⟨1682489, pr1682489⟩
private theorem pr1682669 : PrimeCertificate 1682669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv32359]) (by decide +kernel)
def pv1682669 : PrimeValue := ⟨1682669, pr1682669⟩
private theorem pr1682693 : PrimeCertificate 1682693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv167,pv229]) (by decide +kernel)
def pv1682693 : PrimeValue := ⟨1682693, pr1682693⟩
private theorem pr1683053 : PrimeCertificate 1683053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv277]) (by decide +kernel)
def pv1683053 : PrimeValue := ⟨1683053, pr1683053⟩
private theorem pr1683089 : PrimeCertificate 1683089 :=
  certifyPrime (q := pv13) (ls := [pv2,pv11,pv73,pv131]) (by decide +kernel)
def pv1683089 : PrimeValue := ⟨1683089, pr1683089⟩
private theorem pr1683491 : PrimeCertificate 1683491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv79,pv2131]) (by decide +kernel)
def pv1683491 : PrimeValue := ⟨1683491, pr1683491⟩
private theorem pr1683581 : PrimeCertificate 1683581 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv84179]) (by decide +kernel)
def pv1683581 : PrimeValue := ⟨1683581, pr1683581⟩
private theorem pr1683971 : PrimeCertificate 1683971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv8863]) (by decide +kernel)
def pv1683971 : PrimeValue := ⟨1683971, pr1683971⟩
private theorem pr1684373 : PrimeCertificate 1684373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv421093]) (by decide +kernel)
def pv1684373 : PrimeValue := ⟨1684373, pr1684373⟩
private theorem pr1684829 : PrimeCertificate 1684829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv421207]) (by decide +kernel)
def pv1684829 : PrimeValue := ⟨1684829, pr1684829⟩
private theorem pr1684883 : PrimeCertificate 1684883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv101,pv439]) (by decide +kernel)
def pv1684883 : PrimeValue := ⟨1684883, pr1684883⟩
private theorem pr1684979 : PrimeCertificate 1684979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv842489]) (by decide +kernel)
def pv1684979 : PrimeValue := ⟨1684979, pr1684979⟩
private theorem pr1685441 : PrimeCertificate 1685441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv23,pv229]) (by decide +kernel)
def pv1685441 : PrimeValue := ⟨1685441, pr1685441⟩
private theorem pr1685459 : PrimeCertificate 1685459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv842729]) (by decide +kernel)
def pv1685459 : PrimeValue := ⟨1685459, pr1685459⟩
private theorem pr1685483 : PrimeCertificate 1685483 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv89,pv557]) (by decide +kernel)
def pv1685483 : PrimeValue := ⟨1685483, pr1685483⟩
private theorem pr1685591 : PrimeCertificate 1685591 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv168559]) (by decide +kernel)
def pv1685591 : PrimeValue := ⟨1685591, pr1685591⟩
private theorem pr1685759 : PrimeCertificate 1685759 :=
  certifyPrime (q := pv11) (ls := [pv2,pv842879]) (by decide +kernel)
def pv1685759 : PrimeValue := ⟨1685759, pr1685759⟩
private theorem pr1685933 : PrimeCertificate 1685933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv421483]) (by decide +kernel)
def pv1685933 : PrimeValue := ⟨1685933, pr1685933⟩
private theorem pr1686029 : PrimeCertificate 1686029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv13597]) (by decide +kernel)
def pv1686029 : PrimeValue := ⟨1686029, pr1686029⟩
private theorem pr1686203 : PrimeCertificate 1686203 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv43,pv2801]) (by decide +kernel)
def pv1686203 : PrimeValue := ⟨1686203, pr1686203⟩
private theorem pr1686389 : PrimeCertificate 1686389 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv38327]) (by decide +kernel)
def pv1686389 : PrimeValue := ⟨1686389, pr1686389⟩
private theorem pr1686491 : PrimeCertificate 1686491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv12973]) (by decide +kernel)
def pv1686491 : PrimeValue := ⟨1686491, pr1686491⟩
private theorem pr1686551 : PrimeCertificate 1686551 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv89,pv379]) (by decide +kernel)
def pv1686551 : PrimeValue := ⟨1686551, pr1686551⟩
private theorem pr1686749 : PrimeCertificate 1686749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv107,pv563]) (by decide +kernel)
def pv1686749 : PrimeValue := ⟨1686749, pr1686749⟩
private theorem pr1687373 : PrimeCertificate 1687373 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv18341]) (by decide +kernel)
def pv1687373 : PrimeValue := ⟨1687373, pr1687373⟩
private theorem pr1687583 : PrimeCertificate 1687583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv47,pv1381]) (by decide +kernel)
def pv1687583 : PrimeValue := ⟨1687583, pr1687583⟩
private theorem pr1687643 : PrimeCertificate 1687643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv41,pv1871]) (by decide +kernel)
def pv1687643 : PrimeValue := ⟨1687643, pr1687643⟩
private theorem pr1687739 : PrimeCertificate 1687739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv139,pv467]) (by decide +kernel)
def pv1687739 : PrimeValue := ⟨1687739, pr1687739⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
