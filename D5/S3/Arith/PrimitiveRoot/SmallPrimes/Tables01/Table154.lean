/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table154
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table154.pv1647251
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

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1647251 : Nat.Prime 1647251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv599]) (by decide +kernel)
def pv1647251 : PrimeValue := ⟨1647251, pr1647251⟩
private theorem pr1647599 : Nat.Prime 1647599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv823799]) (by decide +kernel)
def pv1647599 : PrimeValue := ⟨1647599, pr1647599⟩
private theorem pr1647941 : Nat.Prime 1647941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv79,pv149]) (by decide +kernel)
def pv1647941 : PrimeValue := ⟨1647941, pr1647941⟩
private theorem pr1648001 : Nat.Prime 1648001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv103]) (by decide +kernel)
def pv1648001 : PrimeValue := ⟨1648001, pr1648001⟩
private theorem pr1648499 : Nat.Prime 1648499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv22277]) (by decide +kernel)
def pv1648499 : PrimeValue := ⟨1648499, pr1648499⟩
private theorem pr1648529 : Nat.Prime 1648529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv41,pv359]) (by decide +kernel)
def pv1648529 : PrimeValue := ⟨1648529, pr1648529⟩
private theorem pr1648739 : Nat.Prime 1648739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv9059]) (by decide +kernel)
def pv1648739 : PrimeValue := ⟨1648739, pr1648739⟩
private theorem pr1648793 : Nat.Prime 1648793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv4793]) (by decide +kernel)
def pv1648793 : PrimeValue := ⟨1648793, pr1648793⟩
private theorem pr1649003 : Nat.Prime 1649003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv824501]) (by decide +kernel)
def pv1649003 : PrimeValue := ⟨1649003, pr1649003⟩
private theorem pr1649129 : Nat.Prime 1649129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv101,pv157]) (by decide +kernel)
def pv1649129 : PrimeValue := ⟨1649129, pr1649129⟩
private theorem pr1649309 : Nat.Prime 1649309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv223]) (by decide +kernel)
def pv1649309 : PrimeValue := ⟨1649309, pr1649309⟩
private theorem pr1649369 : Nat.Prime 1649369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv29453]) (by decide +kernel)
def pv1649369 : PrimeValue := ⟨1649369, pr1649369⟩
private theorem pr1649489 : Nat.Prime 1649489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv103093]) (by decide +kernel)
def pv1649489 : PrimeValue := ⟨1649489, pr1649489⟩
private theorem pr1649591 : Nat.Prime 1649591 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv293,pv563]) (by decide +kernel)
def pv1649591 : PrimeValue := ⟨1649591, pr1649591⟩
private theorem pr1649639 : Nat.Prime 1649639 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv347,pv2377]) (by decide +kernel)
def pv1649639 : PrimeValue := ⟨1649639, pr1649639⟩
private theorem pr1650101 : Nat.Prime 1650101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv569]) (by decide +kernel)
def pv1650101 : PrimeValue := ⟨1650101, pr1650101⟩
private theorem pr1650179 : Nat.Prime 1650179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv509,pv1621]) (by decide +kernel)
def pv1650179 : PrimeValue := ⟨1650179, pr1650179⟩
private theorem pr1650221 : Nat.Prime 1650221 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv13,pv577]) (by decide +kernel)
def pv1650221 : PrimeValue := ⟨1650221, pr1650221⟩
private theorem pr1650959 : Nat.Prime 1650959 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv825479]) (by decide +kernel)
def pv1650959 : PrimeValue := ⟨1650959, pr1650959⟩
private theorem pr1651151 : Nat.Prime 1651151 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv33023]) (by decide +kernel)
def pv1651151 : PrimeValue := ⟨1651151, pr1651151⟩
private theorem pr1651229 : Nat.Prime 1651229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv412807]) (by decide +kernel)
def pv1651229 : PrimeValue := ⟨1651229, pr1651229⟩
private theorem pr1651283 : Nat.Prime 1651283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv12323]) (by decide +kernel)
def pv1651283 : PrimeValue := ⟨1651283, pr1651283⟩
private theorem pr1651493 : Nat.Prime 1651493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv29,pv619]) (by decide +kernel)
def pv1651493 : PrimeValue := ⟨1651493, pr1651493⟩
private theorem pr1651511 : Nat.Prime 1651511 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv23593]) (by decide +kernel)
def pv1651511 : PrimeValue := ⟨1651511, pr1651511⟩
private theorem pr1651691 : Nat.Prime 1651691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv331,pv499]) (by decide +kernel)
def pv1651691 : PrimeValue := ⟨1651691, pr1651691⟩
private theorem pr1652039 : Nat.Prime 1652039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv826019]) (by decide +kernel)
def pv1652039 : PrimeValue := ⟨1652039, pr1652039⟩
private theorem pr1652243 : Nat.Prime 1652243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv5471]) (by decide +kernel)
def pv1652243 : PrimeValue := ⟨1652243, pr1652243⟩
private theorem pr1652741 : Nat.Prime 1652741 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv4861]) (by decide +kernel)
def pv1652741 : PrimeValue := ⟨1652741, pr1652741⟩
private theorem pr1652879 : Nat.Prime 1652879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv487,pv1697]) (by decide +kernel)
def pv1652879 : PrimeValue := ⟨1652879, pr1652879⟩
private theorem pr1653293 : Nat.Prime 1653293 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv67,pv199]) (by decide +kernel)
def pv1653293 : PrimeValue := ⟨1653293, pr1653293⟩
private theorem pr1653329 : Nat.Prime 1653329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv103333]) (by decide +kernel)
def pv1653329 : PrimeValue := ⟨1653329, pr1653329⟩
private theorem pr1653611 : Nat.Prime 1653611 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv23623]) (by decide +kernel)
def pv1653611 : PrimeValue := ⟨1653611, pr1653611⟩
private theorem pr1653689 : Nat.Prime 1653689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv421,pv491]) (by decide +kernel)
def pv1653689 : PrimeValue := ⟨1653689, pr1653689⟩
private theorem pr1653929 : Nat.Prime 1653929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv7129]) (by decide +kernel)
def pv1653929 : PrimeValue := ⟨1653929, pr1653929⟩
private theorem pr1654013 : Nat.Prime 1654013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv197,pv2099]) (by decide +kernel)
def pv1654013 : PrimeValue := ⟨1654013, pr1654013⟩
private theorem pr1654043 : Nat.Prime 1654043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv63617]) (by decide +kernel)
def pv1654043 : PrimeValue := ⟨1654043, pr1654043⟩
private theorem pr1654199 : Nat.Prime 1654199 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv13,pv61,pv149]) (by decide +kernel)
def pv1654199 : PrimeValue := ⟨1654199, pr1654199⟩
private theorem pr1654223 : Nat.Prime 1654223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv26681]) (by decide +kernel)
def pv1654223 : PrimeValue := ⟨1654223, pr1654223⟩
private theorem pr1654241 : Nat.Prime 1654241 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv7,pv211]) (by decide +kernel)
def pv1654241 : PrimeValue := ⟨1654241, pr1654241⟩
private theorem pr1654673 : Nat.Prime 1654673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv5443]) (by decide +kernel)
def pv1654673 : PrimeValue := ⟨1654673, pr1654673⟩
private theorem pr1655039 : Nat.Prime 1655039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv11,pv977]) (by decide +kernel)
def pv1655039 : PrimeValue := ⟨1655039, pr1655039⟩
private theorem pr1655141 : Nat.Prime 1655141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv82757]) (by decide +kernel)
def pv1655141 : PrimeValue := ⟨1655141, pr1655141⟩
private theorem pr1655963 : Nat.Prime 1655963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv10753]) (by decide +kernel)
def pv1655963 : PrimeValue := ⟨1655963, pr1655963⟩
private theorem pr1655999 : Nat.Prime 1655999 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv47,pv79,pv223]) (by decide +kernel)
def pv1655999 : PrimeValue := ⟨1655999, pr1655999⟩
private theorem pr1656251 : Nat.Prime 1656251 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv53]) (by decide +kernel)
def pv1656251 : PrimeValue := ⟨1656251, pr1656251⟩
private theorem pr1656311 : Nat.Prime 1656311 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv17,pv9743]) (by decide +kernel)
def pv1656311 : PrimeValue := ⟨1656311, pr1656311⟩
private theorem pr1656383 : Nat.Prime 1656383 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv13,pv19,pv479]) (by decide +kernel)
def pv1656383 : PrimeValue := ⟨1656383, pr1656383⟩
private theorem pr1656521 : Nat.Prime 1656521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv41413]) (by decide +kernel)
def pv1656521 : PrimeValue := ⟨1656521, pr1656521⟩
private theorem pr1656533 : Nat.Prime 1656533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv9631]) (by decide +kernel)
def pv1656533 : PrimeValue := ⟨1656533, pr1656533⟩
private theorem pr1656659 : Nat.Prime 1656659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv433,pv1913]) (by decide +kernel)
def pv1656659 : PrimeValue := ⟨1656659, pr1656659⟩
private theorem pr1656719 : Nat.Prime 1656719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv17,pv6961]) (by decide +kernel)
def pv1656719 : PrimeValue := ⟨1656719, pr1656719⟩
private theorem pr1656911 : Nat.Prime 1656911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv67,pv2473]) (by decide +kernel)
def pv1656911 : PrimeValue := ⟨1656911, pr1656911⟩
private theorem pr1657013 : Nat.Prime 1657013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv31,pv83]) (by decide +kernel)
def pv1657013 : PrimeValue := ⟨1657013, pr1657013⟩
private theorem pr1657121 : Nat.Prime 1657121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv10357]) (by decide +kernel)
def pv1657121 : PrimeValue := ⟨1657121, pr1657121⟩
private theorem pr1657889 : Nat.Prime 1657889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv103,pv503]) (by decide +kernel)
def pv1657889 : PrimeValue := ⟨1657889, pr1657889⟩
private theorem pr1658201 : Nat.Prime 1658201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv8291]) (by decide +kernel)
def pv1658201 : PrimeValue := ⟨1658201, pr1658201⟩
private theorem pr1658213 : Nat.Prime 1658213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv414553]) (by decide +kernel)
def pv1658213 : PrimeValue := ⟨1658213, pr1658213⟩
private theorem pr1658243 : Nat.Prime 1658243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv829121]) (by decide +kernel)
def pv1658243 : PrimeValue := ⟨1658243, pr1658243⟩
private theorem pr1658309 : Nat.Prime 1658309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv414577]) (by decide +kernel)
def pv1658309 : PrimeValue := ⟨1658309, pr1658309⟩
private theorem pr1658411 : Nat.Prime 1658411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv12757]) (by decide +kernel)
def pv1658411 : PrimeValue := ⟨1658411, pr1658411⟩
private theorem pr1658483 : Nat.Prime 1658483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv118463]) (by decide +kernel)
def pv1658483 : PrimeValue := ⟨1658483, pr1658483⟩
private theorem pr1658561 : Nat.Prime 1658561 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv71,pv73]) (by decide +kernel)
def pv1658561 : PrimeValue := ⟨1658561, pr1658561⟩
private theorem pr1658711 : Nat.Prime 1658711 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv37,pv4483]) (by decide +kernel)
def pv1658711 : PrimeValue := ⟨1658711, pr1658711⟩
private theorem pr1658753 : Nat.Prime 1658753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12959]) (by decide +kernel)
def pv1658753 : PrimeValue := ⟨1658753, pr1658753⟩
private theorem pr1658801 : Nat.Prime 1658801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv13,pv29]) (by decide +kernel)
def pv1658801 : PrimeValue := ⟨1658801, pr1658801⟩
private theorem pr1659041 : Nat.Prime 1659041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv10369]) (by decide +kernel)
def pv1659041 : PrimeValue := ⟨1659041, pr1659041⟩
private theorem pr1659083 : Nat.Prime 1659083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv36067]) (by decide +kernel)
def pv1659083 : PrimeValue := ⟨1659083, pr1659083⟩
private theorem pr1659239 : Nat.Prime 1659239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv16931]) (by decide +kernel)
def pv1659239 : PrimeValue := ⟨1659239, pr1659239⟩
private theorem pr1659299 : Nat.Prime 1659299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv359,pv2311]) (by decide +kernel)
def pv1659299 : PrimeValue := ⟨1659299, pr1659299⟩
private theorem pr1659401 : Nat.Prime 1659401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv8297]) (by decide +kernel)
def pv1659401 : PrimeValue := ⟨1659401, pr1659401⟩
private theorem pr1659491 : Nat.Prime 1659491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv151,pv157]) (by decide +kernel)
def pv1659491 : PrimeValue := ⟨1659491, pr1659491⟩
private theorem pr1659533 : Nat.Prime 1659533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv8467]) (by decide +kernel)
def pv1659533 : PrimeValue := ⟨1659533, pr1659533⟩
private theorem pr1659551 : Nat.Prime 1659551 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv33191]) (by decide +kernel)
def pv1659551 : PrimeValue := ⟨1659551, pr1659551⟩
private theorem pr1659719 : Nat.Prime 1659719 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv467,pv1777]) (by decide +kernel)
def pv1659719 : PrimeValue := ⟨1659719, pr1659719⟩
private theorem pr1659809 : Nat.Prime 1659809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv51869]) (by decide +kernel)
def pv1659809 : PrimeValue := ⟨1659809, pr1659809⟩
private theorem pr1659851 : Nat.Prime 1659851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv89,pv373]) (by decide +kernel)
def pv1659851 : PrimeValue := ⟨1659851, pr1659851⟩
private theorem pr1659881 : Nat.Prime 1659881 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv5,pv17,pv2441]) (by decide +kernel)
def pv1659881 : PrimeValue := ⟨1659881, pr1659881⟩
private theorem pr1660259 : Nat.Prime 1660259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv43691]) (by decide +kernel)
def pv1660259 : PrimeValue := ⟨1660259, pr1660259⟩
private theorem pr1660283 : Nat.Prime 1660283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv63857]) (by decide +kernel)
def pv1660283 : PrimeValue := ⟨1660283, pr1660283⟩
private theorem pr1660469 : Nat.Prime 1660469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv571,pv727]) (by decide +kernel)
def pv1660469 : PrimeValue := ⟨1660469, pr1660469⟩
private theorem pr1660553 : Nat.Prime 1660553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv207569]) (by decide +kernel)
def pv1660553 : PrimeValue := ⟨1660553, pr1660553⟩
private theorem pr1660559 : Nat.Prime 1660559 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv830279]) (by decide +kernel)
def pv1660559 : PrimeValue := ⟨1660559, pr1660559⟩
private theorem pr1660601 : Nat.Prime 1660601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv23]) (by decide +kernel)
def pv1660601 : PrimeValue := ⟨1660601, pr1660601⟩
private theorem pr1660661 : Nat.Prime 1660661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv1931]) (by decide +kernel)
def pv1660661 : PrimeValue := ⟨1660661, pr1660661⟩
private theorem pr1660709 : Nat.Prime 1660709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv37,pv229]) (by decide +kernel)
def pv1660709 : PrimeValue := ⟨1660709, pr1660709⟩
private theorem pr1660751 : Nat.Prime 1660751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv73]) (by decide +kernel)
def pv1660751 : PrimeValue := ⟨1660751, pr1660751⟩
private theorem pr1660943 : Nat.Prime 1660943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv109,pv401]) (by decide +kernel)
def pv1660943 : PrimeValue := ⟨1660943, pr1660943⟩
private theorem pr1661021 : Nat.Prime 1661021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv53,pv1567]) (by decide +kernel)
def pv1661021 : PrimeValue := ⟨1661021, pr1661021⟩
private theorem pr1661069 : Nat.Prime 1661069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv3881]) (by decide +kernel)
def pv1661069 : PrimeValue := ⟨1661069, pr1661069⟩
private theorem pr1661273 : Nat.Prime 1661273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv281,pv739]) (by decide +kernel)
def pv1661273 : PrimeValue := ⟨1661273, pr1661273⟩
private theorem pr1661969 : Nat.Prime 1661969 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv7,pv11,pv19,pv71]) (by decide +kernel)
def pv1661969 : PrimeValue := ⟨1661969, pr1661969⟩
private theorem pr1662161 : Nat.Prime 1662161 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv79,pv263]) (by decide +kernel)
def pv1662161 : PrimeValue := ⟨1662161, pr1662161⟩
private theorem pr1662389 : Nat.Prime 1662389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv4567]) (by decide +kernel)
def pv1662389 : PrimeValue := ⟨1662389, pr1662389⟩
private theorem pr1662491 : Nat.Prime 1662491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv83,pv2003]) (by decide +kernel)
def pv1662491 : PrimeValue := ⟨1662491, pr1662491⟩
private theorem pr1662593 : Nat.Prime 1662593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv419]) (by decide +kernel)
def pv1662593 : PrimeValue := ⟨1662593, pr1662593⟩
private theorem pr1662701 : Nat.Prime 1662701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv1279]) (by decide +kernel)
def pv1662701 : PrimeValue := ⟨1662701, pr1662701⟩
private theorem pr1662893 : Nat.Prime 1662893 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv5399]) (by decide +kernel)
def pv1662893 : PrimeValue := ⟨1662893, pr1662893⟩
private theorem pr1662929 : Nat.Prime 1662929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv53]) (by decide +kernel)
def pv1662929 : PrimeValue := ⟨1662929, pr1662929⟩
private theorem pr1663391 : Nat.Prime 1663391 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv181,pv919]) (by decide +kernel)
def pv1663391 : PrimeValue := ⟨1663391, pr1663391⟩
private theorem pr1663589 : Nat.Prime 1663589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv4673]) (by decide +kernel)
def pv1663589 : PrimeValue := ⟨1663589, pr1663589⟩
private theorem pr1663619 : Nat.Prime 1663619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv75619]) (by decide +kernel)
def pv1663619 : PrimeValue := ⟨1663619, pr1663619⟩
private theorem pr1663703 : Nat.Prime 1663703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv831851]) (by decide +kernel)
def pv1663703 : PrimeValue := ⟨1663703, pr1663703⟩
private theorem pr1663709 : Nat.Prime 1663709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv13417]) (by decide +kernel)
def pv1663709 : PrimeValue := ⟨1663709, pr1663709⟩
private theorem pr1663919 : Nat.Prime 1663919 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv59,pv239]) (by decide +kernel)
def pv1663919 : PrimeValue := ⟨1663919, pr1663919⟩
private theorem pr1664009 : Nat.Prime 1664009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv208001]) (by decide +kernel)
def pv1664009 : PrimeValue := ⟨1664009, pr1664009⟩
private theorem pr1664021 : Nat.Prime 1664021 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv29,pv151]) (by decide +kernel)
def pv1664021 : PrimeValue := ⟨1664021, pr1664021⟩
private theorem pr1664501 : Nat.Prime 1664501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3329]) (by decide +kernel)
def pv1664501 : PrimeValue := ⟨1664501, pr1664501⟩
private theorem pr1664543 : Nat.Prime 1664543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv29,pv2609]) (by decide +kernel)
def pv1664543 : PrimeValue := ⟨1664543, pr1664543⟩
private theorem pr1664633 : Nat.Prime 1664633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv251,pv829]) (by decide +kernel)
def pv1664633 : PrimeValue := ⟨1664633, pr1664633⟩
private theorem pr1664651 : Nat.Prime 1664651 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv197]) (by decide +kernel)
def pv1664651 : PrimeValue := ⟨1664651, pr1664651⟩
private theorem pr1664681 : Nat.Prime 1664681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv41617]) (by decide +kernel)
def pv1664681 : PrimeValue := ⟨1664681, pr1664681⟩
private theorem pr1664711 : Nat.Prime 1664711 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv166471]) (by decide +kernel)
def pv1664711 : PrimeValue := ⟨1664711, pr1664711⟩
private theorem pr1664909 : Nat.Prime 1664909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv97,pv613]) (by decide +kernel)
def pv1664909 : PrimeValue := ⟨1664909, pr1664909⟩
private theorem pr1665143 : Nat.Prime 1665143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv157,pv5303]) (by decide +kernel)
def pv1665143 : PrimeValue := ⟨1665143, pr1665143⟩
private theorem pr1665161 : Nat.Prime 1665161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv313]) (by decide +kernel)
def pv1665161 : PrimeValue := ⟨1665161, pr1665161⟩
private theorem pr1665263 : Nat.Prime 1665263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv832631]) (by decide +kernel)
def pv1665263 : PrimeValue := ⟨1665263, pr1665263⟩
private theorem pr1665479 : Nat.Prime 1665479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv79,pv83,pv127]) (by decide +kernel)
def pv1665479 : PrimeValue := ⟨1665479, pr1665479⟩
private theorem pr1665623 : Nat.Prime 1665623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv118973]) (by decide +kernel)
def pv1665623 : PrimeValue := ⟨1665623, pr1665623⟩
private theorem pr1665659 : Nat.Prime 1665659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv167,pv4987]) (by decide +kernel)
def pv1665659 : PrimeValue := ⟨1665659, pr1665659⟩
private theorem pr1665899 : Nat.Prime 1665899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17,pv3769]) (by decide +kernel)
def pv1665899 : PrimeValue := ⟨1665899, pr1665899⟩
private theorem pr1666019 : Nat.Prime 1666019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv833009]) (by decide +kernel)
def pv1666019 : PrimeValue := ⟨1666019, pr1666019⟩
private theorem pr1666139 : Nat.Prime 1666139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv251,pv3319]) (by decide +kernel)
def pv1666139 : PrimeValue := ⟨1666139, pr1666139⟩
private theorem pr1666403 : Nat.Prime 1666403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv833201]) (by decide +kernel)
def pv1666403 : PrimeValue := ⟨1666403, pr1666403⟩
private theorem pr1666421 : Nat.Prime 1666421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11903]) (by decide +kernel)
def pv1666421 : PrimeValue := ⟨1666421, pr1666421⟩
private theorem pr1666481 : Nat.Prime 1666481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv37,pv563]) (by decide +kernel)
def pv1666481 : PrimeValue := ⟨1666481, pr1666481⟩
private theorem pr1666523 : Nat.Prime 1666523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv5827]) (by decide +kernel)
def pv1666523 : PrimeValue := ⟨1666523, pr1666523⟩
private theorem pr1666559 : Nat.Prime 1666559 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv67,pv12437]) (by decide +kernel)
def pv1666559 : PrimeValue := ⟨1666559, pr1666559⟩
private theorem pr1667279 : Nat.Prime 1667279 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv47,pv17737]) (by decide +kernel)
def pv1667279 : PrimeValue := ⟨1667279, pr1667279⟩
private theorem pr1667579 : Nat.Prime 1667579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv229,pv331]) (by decide +kernel)
def pv1667579 : PrimeValue := ⟨1667579, pr1667579⟩
private theorem pr1667651 : Nat.Prime 1667651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv33353]) (by decide +kernel)
def pv1667651 : PrimeValue := ⟨1667651, pr1667651⟩
private theorem pr1667873 : Nat.Prime 1667873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv52121]) (by decide +kernel)
def pv1667873 : PrimeValue := ⟨1667873, pr1667873⟩
private theorem pr1667933 : Nat.Prime 1667933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv71,pv839]) (by decide +kernel)
def pv1667933 : PrimeValue := ⟨1667933, pr1667933⟩
private theorem pr1667951 : Nat.Prime 1667951 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv33359]) (by decide +kernel)
def pv1667951 : PrimeValue := ⟨1667951, pr1667951⟩
private theorem pr1668083 : Nat.Prime 1668083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv64157]) (by decide +kernel)
def pv1668083 : PrimeValue := ⟨1668083, pr1668083⟩
private theorem pr1668113 : Nat.Prime 1668113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv137,pv761]) (by decide +kernel)
def pv1668113 : PrimeValue := ⟨1668113, pr1668113⟩
private theorem pr1668119 : Nat.Prime 1668119 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv834059]) (by decide +kernel)
def pv1668119 : PrimeValue := ⟨1668119, pr1668119⟩
private theorem pr1668449 : Nat.Prime 1668449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv3067]) (by decide +kernel)
def pv1668449 : PrimeValue := ⟨1668449, pr1668449⟩
private theorem pr1668503 : Nat.Prime 1668503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv149,pv509]) (by decide +kernel)
def pv1668503 : PrimeValue := ⟨1668503, pr1668503⟩
private theorem pr1668521 : Nat.Prime 1668521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv59,pv101]) (by decide +kernel)
def pv1668521 : PrimeValue := ⟨1668521, pr1668521⟩
private theorem pr1668791 : Nat.Prime 1668791 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv109,pv1531]) (by decide +kernel)
def pv1668791 : PrimeValue := ⟨1668791, pr1668791⟩
private theorem pr1668911 : Nat.Prime 1668911 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv157,pv1063]) (by decide +kernel)
def pv1668911 : PrimeValue := ⟨1668911, pr1668911⟩
private theorem pr1669301 : Nat.Prime 1669301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv16693]) (by decide +kernel)
def pv1669301 : PrimeValue := ⟨1669301, pr1669301⟩
private theorem pr1669313 : Nat.Prime 1669313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26083]) (by decide +kernel)
def pv1669313 : PrimeValue := ⟨1669313, pr1669313⟩
private theorem pr1669469 : Nat.Prime 1669469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv24551]) (by decide +kernel)
def pv1669469 : PrimeValue := ⟨1669469, pr1669469⟩
private theorem pr1669571 : Nat.Prime 1669571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv17,pv23,pv61]) (by decide +kernel)
def pv1669571 : PrimeValue := ⟨1669571, pr1669571⟩
private theorem pr1669589 : Nat.Prime 1669589 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv37,pv389]) (by decide +kernel)
def pv1669589 : PrimeValue := ⟨1669589, pr1669589⟩
private theorem pr1669751 : Nat.Prime 1669751 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv6679]) (by decide +kernel)
def pv1669751 : PrimeValue := ⟨1669751, pr1669751⟩
private theorem pr1669763 : Nat.Prime 1669763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv28789]) (by decide +kernel)
def pv1669763 : PrimeValue := ⟨1669763, pr1669763⟩
private theorem pr1669781 : Nat.Prime 1669781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11927]) (by decide +kernel)
def pv1669781 : PrimeValue := ⟨1669781, pr1669781⟩
private theorem pr1669793 : Nat.Prime 1669793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv52181]) (by decide +kernel)
def pv1669793 : PrimeValue := ⟨1669793, pr1669793⟩
private theorem pr1669931 : Nat.Prime 1669931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv4073]) (by decide +kernel)
def pv1669931 : PrimeValue := ⟨1669931, pr1669931⟩
private theorem pr1670183 : Nat.Prime 1670183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv49123]) (by decide +kernel)
def pv1670183 : PrimeValue := ⟨1670183, pr1670183⟩
private theorem pr1670213 : Nat.Prime 1670213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv417553]) (by decide +kernel)
def pv1670213 : PrimeValue := ⟨1670213, pr1670213⟩
private theorem pr1670633 : Nat.Prime 1670633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv29,pv379]) (by decide +kernel)
def pv1670633 : PrimeValue := ⟨1670633, pr1670633⟩
private theorem pr1670741 : Nat.Prime 1670741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv83537]) (by decide +kernel)
def pv1670741 : PrimeValue := ⟨1670741, pr1670741⟩
private theorem pr1670813 : Nat.Prime 1670813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv23,pv127]) (by decide +kernel)
def pv1670813 : PrimeValue := ⟨1670813, pr1670813⟩
private theorem pr1670891 : Nat.Prime 1670891 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv12853]) (by decide +kernel)
def pv1670891 : PrimeValue := ⟨1670891, pr1670891⟩
private theorem pr1671161 : Nat.Prime 1671161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv41,pv1019]) (by decide +kernel)
def pv1671161 : PrimeValue := ⟨1671161, pr1671161⟩
private theorem pr1671209 : Nat.Prime 1671209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv2713]) (by decide +kernel)
def pv1671209 : PrimeValue := ⟨1671209, pr1671209⟩
private theorem pr1671311 : Nat.Prime 1671311 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv97,pv1723]) (by decide +kernel)
def pv1671311 : PrimeValue := ⟨1671311, pr1671311⟩
private theorem pr1671359 : Nat.Prime 1671359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv64283]) (by decide +kernel)
def pv1671359 : PrimeValue := ⟨1671359, pr1671359⟩
private theorem pr1671443 : Nat.Prime 1671443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv835721]) (by decide +kernel)
def pv1671443 : PrimeValue := ⟨1671443, pr1671443⟩
private theorem pr1671671 : Nat.Prime 1671671 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv11,pv13,pv167]) (by decide +kernel)
def pv1671671 : PrimeValue := ⟨1671671, pr1671671⟩
private theorem pr1672271 : Nat.Prime 1672271 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv43,pv3889]) (by decide +kernel)
def pv1672271 : PrimeValue := ⟨1672271, pr1672271⟩
private theorem pr1672523 : Nat.Prime 1672523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv239,pv3499]) (by decide +kernel)
def pv1672523 : PrimeValue := ⟨1672523, pr1672523⟩
private theorem pr1672631 : Nat.Prime 1672631 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv9839]) (by decide +kernel)
def pv1672631 : PrimeValue := ⟨1672631, pr1672631⟩
private theorem pr1673069 : Nat.Prime 1673069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv14423]) (by decide +kernel)
def pv1673069 : PrimeValue := ⟨1673069, pr1673069⟩
private theorem pr1673099 : Nat.Prime 1673099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv127,pv941]) (by decide +kernel)
def pv1673099 : PrimeValue := ⟨1673099, pr1673099⟩
private theorem pr1673279 : Nat.Prime 1673279 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv373,pv2243]) (by decide +kernel)
def pv1673279 : PrimeValue := ⟨1673279, pr1673279⟩
private theorem pr1673489 : Nat.Prime 1673489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv104593]) (by decide +kernel)
def pv1673489 : PrimeValue := ⟨1673489, pr1673489⟩
private theorem pr1673543 : Nat.Prime 1673543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv191,pv337]) (by decide +kernel)
def pv1673543 : PrimeValue := ⟨1673543, pr1673543⟩
private theorem pr1673663 : Nat.Prime 1673663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv283,pv2957]) (by decide +kernel)
def pv1673663 : PrimeValue := ⟨1673663, pr1673663⟩
private theorem pr1673723 : Nat.Prime 1673723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv836861]) (by decide +kernel)
def pv1673723 : PrimeValue := ⟨1673723, pr1673723⟩
private theorem pr1673849 : Nat.Prime 1673849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv23,pv827]) (by decide +kernel)
def pv1673849 : PrimeValue := ⟨1673849, pr1673849⟩
private theorem pr1673933 : Nat.Prime 1673933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv32191]) (by decide +kernel)
def pv1673933 : PrimeValue := ⟨1673933, pr1673933⟩
private theorem pr1673993 : Nat.Prime 1673993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv209249]) (by decide +kernel)
def pv1673993 : PrimeValue := ⟨1673993, pr1673993⟩
private theorem pr1674203 : Nat.Prime 1674203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv293,pv2857]) (by decide +kernel)
def pv1674203 : PrimeValue := ⟨1674203, pr1674203⟩
private theorem pr1674209 : Nat.Prime 1674209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv113,pv463]) (by decide +kernel)
def pv1674209 : PrimeValue := ⟨1674209, pr1674209⟩
private theorem pr1674353 : Nat.Prime 1674353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv227,pv461]) (by decide +kernel)
def pv1674353 : PrimeValue := ⟨1674353, pr1674353⟩
private theorem pr1674581 : Nat.Prime 1674581 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv101,pv829]) (by decide +kernel)
def pv1674581 : PrimeValue := ⟨1674581, pr1674581⟩
private theorem pr1675013 : Nat.Prime 1675013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv7901]) (by decide +kernel)
def pv1675013 : PrimeValue := ⟨1675013, pr1675013⟩
private theorem pr1675073 : Nat.Prime 1675073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3739]) (by decide +kernel)
def pv1675073 : PrimeValue := ⟨1675073, pr1675073⟩
private theorem pr1675109 : Nat.Prime 1675109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv9739]) (by decide +kernel)
def pv1675109 : PrimeValue := ⟨1675109, pr1675109⟩
private theorem pr1675139 : Nat.Prime 1675139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv22637]) (by decide +kernel)
def pv1675139 : PrimeValue := ⟨1675139, pr1675139⟩
private theorem pr1675259 : Nat.Prime 1675259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv64433]) (by decide +kernel)
def pv1675259 : PrimeValue := ⟨1675259, pr1675259⟩
private theorem pr1675361 : Nat.Prime 1675361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv37,pv283]) (by decide +kernel)
def pv1675361 : PrimeValue := ⟨1675361, pr1675361⟩
private theorem pr1675631 : Nat.Prime 1675631 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv15233]) (by decide +kernel)
def pv1675631 : PrimeValue := ⟨1675631, pr1675631⟩
private theorem pr1675763 : Nat.Prime 1675763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv211]) (by decide +kernel)
def pv1675763 : PrimeValue := ⟨1675763, pr1675763⟩
private theorem pr1675799 : Nat.Prime 1675799 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv31,pv151,pv179]) (by decide +kernel)
def pv1675799 : PrimeValue := ⟨1675799, pr1675799⟩
private theorem pr1676393 : Nat.Prime 1676393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv209549]) (by decide +kernel)
def pv1676393 : PrimeValue := ⟨1676393, pr1676393⟩
private theorem pr1676501 : Nat.Prime 1676501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv479]) (by decide +kernel)
def pv1676501 : PrimeValue := ⟨1676501, pr1676501⟩
private theorem pr1676621 : Nat.Prime 1676621 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv7621]) (by decide +kernel)
def pv1676621 : PrimeValue := ⟨1676621, pr1676621⟩
private theorem pr1676651 : Nat.Prime 1676651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv33533]) (by decide +kernel)
def pv1676651 : PrimeValue := ⟨1676651, pr1676651⟩
private theorem pr1676813 : Nat.Prime 1676813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv24659]) (by decide +kernel)
def pv1676813 : PrimeValue := ⟨1676813, pr1676813⟩
private theorem pr1676963 : Nat.Prime 1676963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv119783]) (by decide +kernel)
def pv1676963 : PrimeValue := ⟨1676963, pr1676963⟩
private theorem pr1677251 : Nat.Prime 1677251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv6709]) (by decide +kernel)
def pv1677251 : PrimeValue := ⟨1677251, pr1677251⟩
private theorem pr1677323 : Nat.Prime 1677323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv49333]) (by decide +kernel)
def pv1677323 : PrimeValue := ⟨1677323, pr1677323⟩
private theorem pr1677353 : Nat.Prime 1677353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv209669]) (by decide +kernel)
def pv1677353 : PrimeValue := ⟨1677353, pr1677353⟩
private theorem pr1677743 : Nat.Prime 1677743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv76261]) (by decide +kernel)
def pv1677743 : PrimeValue := ⟨1677743, pr1677743⟩
private theorem pr1678073 : Nat.Prime 1678073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv19069]) (by decide +kernel)
def pv1678073 : PrimeValue := ⟨1678073, pr1678073⟩
private theorem pr1678133 : Nat.Prime 1678133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv281,pv1493]) (by decide +kernel)
def pv1678133 : PrimeValue := ⟨1678133, pr1678133⟩
private theorem pr1678151 : Nat.Prime 1678151 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv33563]) (by decide +kernel)
def pv1678151 : PrimeValue := ⟨1678151, pr1678151⟩
private theorem pr1678349 : Nat.Prime 1678349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv8563]) (by decide +kernel)
def pv1678349 : PrimeValue := ⟨1678349, pr1678349⟩
private theorem pr1678361 : Nat.Prime 1678361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv41959]) (by decide +kernel)
def pv1678361 : PrimeValue := ⟨1678361, pr1678361⟩
private theorem pr1678739 : Nat.Prime 1678739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv839369]) (by decide +kernel)
def pv1678739 : PrimeValue := ⟨1678739, pr1678739⟩
private theorem pr1678889 : Nat.Prime 1678889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv209861]) (by decide +kernel)
def pv1678889 : PrimeValue := ⟨1678889, pr1678889⟩
private theorem pr1679033 : Nat.Prime 1679033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv5119]) (by decide +kernel)
def pv1679033 : PrimeValue := ⟨1679033, pr1679033⟩
private theorem pr1679273 : Nat.Prime 1679273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv157,pv191]) (by decide +kernel)
def pv1679273 : PrimeValue := ⟨1679273, pr1679273⟩
private theorem pr1679351 : Nat.Prime 1679351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv33587]) (by decide +kernel)
def pv1679351 : PrimeValue := ⟨1679351, pr1679351⟩
private theorem pr1679963 : Nat.Prime 1679963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv839981]) (by decide +kernel)
def pv1679963 : PrimeValue := ⟨1679963, pr1679963⟩
private theorem pr1680149 : Nat.Prime 1680149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv420037]) (by decide +kernel)
def pv1680149 : PrimeValue := ⟨1680149, pr1680149⟩
private theorem pr1680359 : Nat.Prime 1680359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv840179]) (by decide +kernel)
def pv1680359 : PrimeValue := ⟨1680359, pr1680359⟩
private theorem pr1680491 : Nat.Prime 1680491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv24007]) (by decide +kernel)
def pv1680491 : PrimeValue := ⟨1680491, pr1680491⟩
private theorem pr1680803 : Nat.Prime 1680803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv643,pv1307]) (by decide +kernel)
def pv1680803 : PrimeValue := ⟨1680803, pr1680803⟩
private theorem pr1680839 : Nat.Prime 1680839 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv359,pv2341]) (by decide +kernel)
def pv1680839 : PrimeValue := ⟨1680839, pr1680839⟩
private theorem pr1681103 : Nat.Prime 1681103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv809,pv1039]) (by decide +kernel)
def pv1681103 : PrimeValue := ⟨1681103, pr1681103⟩
private theorem pr1681259 : Nat.Prime 1681259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv389,pv2161]) (by decide +kernel)
def pv1681259 : PrimeValue := ⟨1681259, pr1681259⟩
private theorem pr1681721 : Nat.Prime 1681721 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv42043]) (by decide +kernel)
def pv1681721 : PrimeValue := ⟨1681721, pr1681721⟩
private theorem pr1682069 : Nat.Prime 1682069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv5323]) (by decide +kernel)
def pv1682069 : PrimeValue := ⟨1682069, pr1682069⟩
private theorem pr1682111 : Nat.Prime 1682111 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv168211]) (by decide +kernel)
def pv1682111 : PrimeValue := ⟨1682111, pr1682111⟩
private theorem pr1682363 : Nat.Prime 1682363 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv76471]) (by decide +kernel)
def pv1682363 : PrimeValue := ⟨1682363, pr1682363⟩
private theorem pr1682399 : Nat.Prime 1682399 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv353,pv2383]) (by decide +kernel)
def pv1682399 : PrimeValue := ⟨1682399, pr1682399⟩
private theorem pr1682489 : Nat.Prime 1682489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv11069]) (by decide +kernel)
def pv1682489 : PrimeValue := ⟨1682489, pr1682489⟩
private theorem pr1682669 : Nat.Prime 1682669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv32359]) (by decide +kernel)
def pv1682669 : PrimeValue := ⟨1682669, pr1682669⟩
private theorem pr1682693 : Nat.Prime 1682693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv167,pv229]) (by decide +kernel)
def pv1682693 : PrimeValue := ⟨1682693, pr1682693⟩
private theorem pr1683053 : Nat.Prime 1683053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv31,pv277]) (by decide +kernel)
def pv1683053 : PrimeValue := ⟨1683053, pr1683053⟩
private theorem pr1683089 : Nat.Prime 1683089 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv11,pv73,pv131]) (by decide +kernel)
def pv1683089 : PrimeValue := ⟨1683089, pr1683089⟩
private theorem pr1683491 : Nat.Prime 1683491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv79,pv2131]) (by decide +kernel)
def pv1683491 : PrimeValue := ⟨1683491, pr1683491⟩
private theorem pr1683581 : Nat.Prime 1683581 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv84179]) (by decide +kernel)
def pv1683581 : PrimeValue := ⟨1683581, pr1683581⟩
private theorem pr1683971 : Nat.Prime 1683971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv8863]) (by decide +kernel)
def pv1683971 : PrimeValue := ⟨1683971, pr1683971⟩
private theorem pr1684373 : Nat.Prime 1684373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv421093]) (by decide +kernel)
def pv1684373 : PrimeValue := ⟨1684373, pr1684373⟩
private theorem pr1684829 : Nat.Prime 1684829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv421207]) (by decide +kernel)
def pv1684829 : PrimeValue := ⟨1684829, pr1684829⟩
private theorem pr1684883 : Nat.Prime 1684883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv101,pv439]) (by decide +kernel)
def pv1684883 : PrimeValue := ⟨1684883, pr1684883⟩
private theorem pr1684979 : Nat.Prime 1684979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv842489]) (by decide +kernel)
def pv1684979 : PrimeValue := ⟨1684979, pr1684979⟩
private theorem pr1685441 : Nat.Prime 1685441 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv23,pv229]) (by decide +kernel)
def pv1685441 : PrimeValue := ⟨1685441, pr1685441⟩
private theorem pr1685459 : Nat.Prime 1685459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv842729]) (by decide +kernel)
def pv1685459 : PrimeValue := ⟨1685459, pr1685459⟩
private theorem pr1685483 : Nat.Prime 1685483 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv89,pv557]) (by decide +kernel)
def pv1685483 : PrimeValue := ⟨1685483, pr1685483⟩
private theorem pr1685591 : Nat.Prime 1685591 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv168559]) (by decide +kernel)
def pv1685591 : PrimeValue := ⟨1685591, pr1685591⟩
private theorem pr1685759 : Nat.Prime 1685759 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv842879]) (by decide +kernel)
def pv1685759 : PrimeValue := ⟨1685759, pr1685759⟩
private theorem pr1685933 : Nat.Prime 1685933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv421483]) (by decide +kernel)
def pv1685933 : PrimeValue := ⟨1685933, pr1685933⟩
private theorem pr1686029 : Nat.Prime 1686029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv13597]) (by decide +kernel)
def pv1686029 : PrimeValue := ⟨1686029, pr1686029⟩
private theorem pr1686203 : Nat.Prime 1686203 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv43,pv2801]) (by decide +kernel)
def pv1686203 : PrimeValue := ⟨1686203, pr1686203⟩
private theorem pr1686389 : Nat.Prime 1686389 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv38327]) (by decide +kernel)
def pv1686389 : PrimeValue := ⟨1686389, pr1686389⟩
private theorem pr1686491 : Nat.Prime 1686491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv12973]) (by decide +kernel)
def pv1686491 : PrimeValue := ⟨1686491, pr1686491⟩
private theorem pr1686551 : Nat.Prime 1686551 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv89,pv379]) (by decide +kernel)
def pv1686551 : PrimeValue := ⟨1686551, pr1686551⟩
private theorem pr1686749 : Nat.Prime 1686749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv107,pv563]) (by decide +kernel)
def pv1686749 : PrimeValue := ⟨1686749, pr1686749⟩
private theorem pr1687373 : Nat.Prime 1687373 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv18341]) (by decide +kernel)
def pv1687373 : PrimeValue := ⟨1687373, pr1687373⟩
private theorem pr1687583 : Nat.Prime 1687583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv47,pv1381]) (by decide +kernel)
def pv1687583 : PrimeValue := ⟨1687583, pr1687583⟩
private theorem pr1687643 : Nat.Prime 1687643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv41,pv1871]) (by decide +kernel)
def pv1687643 : PrimeValue := ⟨1687643, pr1687643⟩
private theorem pr1687739 : Nat.Prime 1687739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv139,pv467]) (by decide +kernel)
def pv1687739 : PrimeValue := ⟨1687739, pr1687739⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
