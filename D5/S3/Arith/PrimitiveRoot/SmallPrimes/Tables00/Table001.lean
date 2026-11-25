/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table001
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table001.pv1597
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table000

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1597 : PrimeCertificate 1597 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv1597 : PrimeValue := ⟨1597, pr1597⟩
private theorem pr1601 : PrimeCertificate 1601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5]) (by decide +kernel)
def pv1601 : PrimeValue := ⟨1601, pr1601⟩
private theorem pr1607 : PrimeCertificate 1607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv73]) (by decide +kernel)
def pv1607 : PrimeValue := ⟨1607, pr1607⟩
private theorem pr1609 : PrimeCertificate 1609 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv1609 : PrimeValue := ⟨1609, pr1609⟩
private theorem pr1613 : PrimeCertificate 1613 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv31]) (by decide +kernel)
def pv1613 : PrimeValue := ⟨1613, pr1613⟩
private theorem pr1619 : PrimeCertificate 1619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv809]) (by decide +kernel)
def pv1619 : PrimeValue := ⟨1619, pr1619⟩
private theorem pr1621 : PrimeCertificate 1621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv1621 : PrimeValue := ⟨1621, pr1621⟩
private theorem pr1627 : PrimeCertificate 1627 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv271]) (by decide +kernel)
def pv1627 : PrimeValue := ⟨1627, pr1627⟩
private theorem pr1637 : PrimeCertificate 1637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv409]) (by decide +kernel)
def pv1637 : PrimeValue := ⟨1637, pr1637⟩
private theorem pr1657 : PrimeCertificate 1657 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv1657 : PrimeValue := ⟨1657, pr1657⟩
private theorem pr1663 : PrimeCertificate 1663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv277]) (by decide +kernel)
def pv1663 : PrimeValue := ⟨1663, pr1663⟩
private theorem pr1667 : PrimeCertificate 1667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17]) (by decide +kernel)
def pv1667 : PrimeValue := ⟨1667, pr1667⟩
private theorem pr1669 : PrimeCertificate 1669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv139]) (by decide +kernel)
def pv1669 : PrimeValue := ⟨1669, pr1669⟩
private theorem pr1693 : PrimeCertificate 1693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv1693 : PrimeValue := ⟨1693, pr1693⟩
private theorem pr1697 : PrimeCertificate 1697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53]) (by decide +kernel)
def pv1697 : PrimeValue := ⟨1697, pr1697⟩
private theorem pr1699 : PrimeCertificate 1699 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv283]) (by decide +kernel)
def pv1699 : PrimeValue := ⟨1699, pr1699⟩
private theorem pr1709 : PrimeCertificate 1709 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv61]) (by decide +kernel)
def pv1709 : PrimeValue := ⟨1709, pr1709⟩
private theorem pr1721 : PrimeCertificate 1721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv43]) (by decide +kernel)
def pv1721 : PrimeValue := ⟨1721, pr1721⟩
private theorem pr1723 : PrimeCertificate 1723 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv41]) (by decide +kernel)
def pv1723 : PrimeValue := ⟨1723, pr1723⟩
private theorem pr1733 : PrimeCertificate 1733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv433]) (by decide +kernel)
def pv1733 : PrimeValue := ⟨1733, pr1733⟩
private theorem pr1741 : PrimeCertificate 1741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv1741 : PrimeValue := ⟨1741, pr1741⟩
private theorem pr1747 : PrimeCertificate 1747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97]) (by decide +kernel)
def pv1747 : PrimeValue := ⟨1747, pr1747⟩
private theorem pr1753 : PrimeCertificate 1753 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv1753 : PrimeValue := ⟨1753, pr1753⟩
private theorem pr1759 : PrimeCertificate 1759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv293]) (by decide +kernel)
def pv1759 : PrimeValue := ⟨1759, pr1759⟩
private theorem pr1777 : PrimeCertificate 1777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv1777 : PrimeValue := ⟨1777, pr1777⟩
private theorem pr1783 : PrimeCertificate 1783 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv1783 : PrimeValue := ⟨1783, pr1783⟩
private theorem pr1787 : PrimeCertificate 1787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv47]) (by decide +kernel)
def pv1787 : PrimeValue := ⟨1787, pr1787⟩
private theorem pr1789 : PrimeCertificate 1789 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv149]) (by decide +kernel)
def pv1789 : PrimeValue := ⟨1789, pr1789⟩
private theorem pr1801 : PrimeCertificate 1801 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv1801 : PrimeValue := ⟨1801, pr1801⟩
private theorem pr1811 : PrimeCertificate 1811 :=
  certifyPrime (q := pv41) (ls := [pv2,pv5,pv181]) (by decide +kernel)
def pv1811 : PrimeValue := ⟨1811, pr1811⟩
private theorem pr1823 : PrimeCertificate 1823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv911]) (by decide +kernel)
def pv1823 : PrimeValue := ⟨1823, pr1823⟩
private theorem pr1831 : PrimeCertificate 1831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv1831 : PrimeValue := ⟨1831, pr1831⟩
private theorem pr1847 : PrimeCertificate 1847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv71]) (by decide +kernel)
def pv1847 : PrimeValue := ⟨1847, pr1847⟩
private theorem pr1861 : PrimeCertificate 1861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv1861 : PrimeValue := ⟨1861, pr1861⟩
private theorem pr1867 : PrimeCertificate 1867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv311]) (by decide +kernel)
def pv1867 : PrimeValue := ⟨1867, pr1867⟩
private theorem pr1871 : PrimeCertificate 1871 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv11,pv17]) (by decide +kernel)
def pv1871 : PrimeValue := ⟨1871, pr1871⟩
private theorem pr1873 : PrimeCertificate 1873 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv1873 : PrimeValue := ⟨1873, pr1873⟩
private theorem pr1877 : PrimeCertificate 1877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv67]) (by decide +kernel)
def pv1877 : PrimeValue := ⟨1877, pr1877⟩
private theorem pr1879 : PrimeCertificate 1879 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv313]) (by decide +kernel)
def pv1879 : PrimeValue := ⟨1879, pr1879⟩
private theorem pr1889 : PrimeCertificate 1889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59]) (by decide +kernel)
def pv1889 : PrimeValue := ⟨1889, pr1889⟩
private theorem pr1901 : PrimeCertificate 1901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv1901 : PrimeValue := ⟨1901, pr1901⟩
private theorem pr1907 : PrimeCertificate 1907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv953]) (by decide +kernel)
def pv1907 : PrimeValue := ⟨1907, pr1907⟩
private theorem pr1913 : PrimeCertificate 1913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv239]) (by decide +kernel)
def pv1913 : PrimeValue := ⟨1913, pr1913⟩
private theorem pr1931 : PrimeCertificate 1931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv193]) (by decide +kernel)
def pv1931 : PrimeValue := ⟨1931, pr1931⟩
private theorem pr1933 : PrimeCertificate 1933 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv1933 : PrimeValue := ⟨1933, pr1933⟩
private theorem pr1949 : PrimeCertificate 1949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv487]) (by decide +kernel)
def pv1949 : PrimeValue := ⟨1949, pr1949⟩
private theorem pr1951 : PrimeCertificate 1951 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv1951 : PrimeValue := ⟨1951, pr1951⟩
private theorem pr1973 : PrimeCertificate 1973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv29]) (by decide +kernel)
def pv1973 : PrimeValue := ⟨1973, pr1973⟩
private theorem pr1979 : PrimeCertificate 1979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv43]) (by decide +kernel)
def pv1979 : PrimeValue := ⟨1979, pr1979⟩
private theorem pr1987 : PrimeCertificate 1987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv331]) (by decide +kernel)
def pv1987 : PrimeValue := ⟨1987, pr1987⟩
private theorem pr1993 : PrimeCertificate 1993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv1993 : PrimeValue := ⟨1993, pr1993⟩
private theorem pr1997 : PrimeCertificate 1997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv499]) (by decide +kernel)
def pv1997 : PrimeValue := ⟨1997, pr1997⟩
private theorem pr1999 : PrimeCertificate 1999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv1999 : PrimeValue := ⟨1999, pr1999⟩
private theorem pr2003 : PrimeCertificate 2003 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv13]) (by decide +kernel)
def pv2003 : PrimeValue := ⟨2003, pr2003⟩
private theorem pr2011 : PrimeCertificate 2011 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv67]) (by decide +kernel)
def pv2011 : PrimeValue := ⟨2011, pr2011⟩
private theorem pr2017 : PrimeCertificate 2017 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv2017 : PrimeValue := ⟨2017, pr2017⟩
private theorem pr2027 : PrimeCertificate 2027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1013]) (by decide +kernel)
def pv2027 : PrimeValue := ⟨2027, pr2027⟩
private theorem pr2029 : PrimeCertificate 2029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv2029 : PrimeValue := ⟨2029, pr2029⟩
private theorem pr2039 : PrimeCertificate 2039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv1019]) (by decide +kernel)
def pv2039 : PrimeValue := ⟨2039, pr2039⟩
private theorem pr2053 : PrimeCertificate 2053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv2053 : PrimeValue := ⟨2053, pr2053⟩
private theorem pr2063 : PrimeCertificate 2063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv1031]) (by decide +kernel)
def pv2063 : PrimeValue := ⟨2063, pr2063⟩
private theorem pr2069 : PrimeCertificate 2069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv47]) (by decide +kernel)
def pv2069 : PrimeValue := ⟨2069, pr2069⟩
private theorem pr2081 : PrimeCertificate 2081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv2081 : PrimeValue := ⟨2081, pr2081⟩
private theorem pr2083 : PrimeCertificate 2083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv347]) (by decide +kernel)
def pv2083 : PrimeValue := ⟨2083, pr2083⟩
private theorem pr2087 : PrimeCertificate 2087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv149]) (by decide +kernel)
def pv2087 : PrimeValue := ⟨2087, pr2087⟩
private theorem pr2089 : PrimeCertificate 2089 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv2089 : PrimeValue := ⟨2089, pr2089⟩
private theorem pr2099 : PrimeCertificate 2099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1049]) (by decide +kernel)
def pv2099 : PrimeValue := ⟨2099, pr2099⟩
private theorem pr2111 : PrimeCertificate 2111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv211]) (by decide +kernel)
def pv2111 : PrimeValue := ⟨2111, pr2111⟩
private theorem pr2113 : PrimeCertificate 2113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv2113 : PrimeValue := ⟨2113, pr2113⟩
private theorem pr2129 : PrimeCertificate 2129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv19]) (by decide +kernel)
def pv2129 : PrimeValue := ⟨2129, pr2129⟩
private theorem pr2131 : PrimeCertificate 2131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv2131 : PrimeValue := ⟨2131, pr2131⟩
private theorem pr2137 : PrimeCertificate 2137 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv89]) (by decide +kernel)
def pv2137 : PrimeValue := ⟨2137, pr2137⟩
private theorem pr2141 : PrimeCertificate 2141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv107]) (by decide +kernel)
def pv2141 : PrimeValue := ⟨2141, pr2141⟩
private theorem pr2143 : PrimeCertificate 2143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv2143 : PrimeValue := ⟨2143, pr2143⟩
private theorem pr2153 : PrimeCertificate 2153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv269]) (by decide +kernel)
def pv2153 : PrimeValue := ⟨2153, pr2153⟩
private theorem pr2161 : PrimeCertificate 2161 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv2161 : PrimeValue := ⟨2161, pr2161⟩
private theorem pr2179 : PrimeCertificate 2179 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv2179 : PrimeValue := ⟨2179, pr2179⟩
private theorem pr2203 : PrimeCertificate 2203 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv367]) (by decide +kernel)
def pv2203 : PrimeValue := ⟨2203, pr2203⟩
private theorem pr2207 : PrimeCertificate 2207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv1103]) (by decide +kernel)
def pv2207 : PrimeValue := ⟨2207, pr2207⟩
private theorem pr2213 : PrimeCertificate 2213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv79]) (by decide +kernel)
def pv2213 : PrimeValue := ⟨2213, pr2213⟩
private theorem pr2221 : PrimeCertificate 2221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv2221 : PrimeValue := ⟨2221, pr2221⟩
private theorem pr2237 : PrimeCertificate 2237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv43]) (by decide +kernel)
def pv2237 : PrimeValue := ⟨2237, pr2237⟩
private theorem pr2239 : PrimeCertificate 2239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv373]) (by decide +kernel)
def pv2239 : PrimeValue := ⟨2239, pr2239⟩
private theorem pr2243 : PrimeCertificate 2243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv59]) (by decide +kernel)
def pv2243 : PrimeValue := ⟨2243, pr2243⟩
private theorem pr2251 : PrimeCertificate 2251 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv2251 : PrimeValue := ⟨2251, pr2251⟩
private theorem pr2267 : PrimeCertificate 2267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv103]) (by decide +kernel)
def pv2267 : PrimeValue := ⟨2267, pr2267⟩
private theorem pr2269 : PrimeCertificate 2269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv2269 : PrimeValue := ⟨2269, pr2269⟩
private theorem pr2273 : PrimeCertificate 2273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71]) (by decide +kernel)
def pv2273 : PrimeValue := ⟨2273, pr2273⟩
private theorem pr2281 : PrimeCertificate 2281 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv2281 : PrimeValue := ⟨2281, pr2281⟩
private theorem pr2287 : PrimeCertificate 2287 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv127]) (by decide +kernel)
def pv2287 : PrimeValue := ⟨2287, pr2287⟩
private theorem pr2293 : PrimeCertificate 2293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv191]) (by decide +kernel)
def pv2293 : PrimeValue := ⟨2293, pr2293⟩
private theorem pr2297 : PrimeCertificate 2297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv41]) (by decide +kernel)
def pv2297 : PrimeValue := ⟨2297, pr2297⟩
private theorem pr2309 : PrimeCertificate 2309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv577]) (by decide +kernel)
def pv2309 : PrimeValue := ⟨2309, pr2309⟩
private theorem pr2311 : PrimeCertificate 2311 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv2311 : PrimeValue := ⟨2311, pr2311⟩
private theorem pr2333 : PrimeCertificate 2333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv53]) (by decide +kernel)
def pv2333 : PrimeValue := ⟨2333, pr2333⟩
private theorem pr2339 : PrimeCertificate 2339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv167]) (by decide +kernel)
def pv2339 : PrimeValue := ⟨2339, pr2339⟩
private theorem pr2341 : PrimeCertificate 2341 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv2341 : PrimeValue := ⟨2341, pr2341⟩
private theorem pr2347 : PrimeCertificate 2347 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv23]) (by decide +kernel)
def pv2347 : PrimeValue := ⟨2347, pr2347⟩
private theorem pr2351 : PrimeCertificate 2351 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv47]) (by decide +kernel)
def pv2351 : PrimeValue := ⟨2351, pr2351⟩
private theorem pr2357 : PrimeCertificate 2357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv31]) (by decide +kernel)
def pv2357 : PrimeValue := ⟨2357, pr2357⟩
private theorem pr2371 : PrimeCertificate 2371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv79]) (by decide +kernel)
def pv2371 : PrimeValue := ⟨2371, pr2371⟩
private theorem pr2377 : PrimeCertificate 2377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv2377 : PrimeValue := ⟨2377, pr2377⟩
private theorem pr2381 : PrimeCertificate 2381 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv17]) (by decide +kernel)
def pv2381 : PrimeValue := ⟨2381, pr2381⟩
private theorem pr2383 : PrimeCertificate 2383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv397]) (by decide +kernel)
def pv2383 : PrimeValue := ⟨2383, pr2383⟩
private theorem pr2389 : PrimeCertificate 2389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv199]) (by decide +kernel)
def pv2389 : PrimeValue := ⟨2389, pr2389⟩
private theorem pr2393 : PrimeCertificate 2393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv23]) (by decide +kernel)
def pv2393 : PrimeValue := ⟨2393, pr2393⟩
private theorem pr2399 : PrimeCertificate 2399 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv109]) (by decide +kernel)
def pv2399 : PrimeValue := ⟨2399, pr2399⟩
private theorem pr2411 : PrimeCertificate 2411 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv241]) (by decide +kernel)
def pv2411 : PrimeValue := ⟨2411, pr2411⟩
private theorem pr2417 : PrimeCertificate 2417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv151]) (by decide +kernel)
def pv2417 : PrimeValue := ⟨2417, pr2417⟩
private theorem pr2423 : PrimeCertificate 2423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv173]) (by decide +kernel)
def pv2423 : PrimeValue := ⟨2423, pr2423⟩
private theorem pr2437 : PrimeCertificate 2437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv2437 : PrimeValue := ⟨2437, pr2437⟩
private theorem pr2441 : PrimeCertificate 2441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv61]) (by decide +kernel)
def pv2441 : PrimeValue := ⟨2441, pr2441⟩
private theorem pr2447 : PrimeCertificate 2447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv1223]) (by decide +kernel)
def pv2447 : PrimeValue := ⟨2447, pr2447⟩
private theorem pr2459 : PrimeCertificate 2459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1229]) (by decide +kernel)
def pv2459 : PrimeValue := ⟨2459, pr2459⟩
private theorem pr2467 : PrimeCertificate 2467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137]) (by decide +kernel)
def pv2467 : PrimeValue := ⟨2467, pr2467⟩
private theorem pr2473 : PrimeCertificate 2473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv2473 : PrimeValue := ⟨2473, pr2473⟩
private theorem pr2477 : PrimeCertificate 2477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv619]) (by decide +kernel)
def pv2477 : PrimeValue := ⟨2477, pr2477⟩
private theorem pr2503 : PrimeCertificate 2503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv139]) (by decide +kernel)
def pv2503 : PrimeValue := ⟨2503, pr2503⟩
private theorem pr2521 : PrimeCertificate 2521 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv2521 : PrimeValue := ⟨2521, pr2521⟩
private theorem pr2531 : PrimeCertificate 2531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv23]) (by decide +kernel)
def pv2531 : PrimeValue := ⟨2531, pr2531⟩
private theorem pr2539 : PrimeCertificate 2539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv2539 : PrimeValue := ⟨2539, pr2539⟩
private theorem pr2543 : PrimeCertificate 2543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv41]) (by decide +kernel)
def pv2543 : PrimeValue := ⟨2543, pr2543⟩
private theorem pr2549 : PrimeCertificate 2549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13]) (by decide +kernel)
def pv2549 : PrimeValue := ⟨2549, pr2549⟩
private theorem pr2551 : PrimeCertificate 2551 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv2551 : PrimeValue := ⟨2551, pr2551⟩
private theorem pr2557 : PrimeCertificate 2557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv2557 : PrimeValue := ⟨2557, pr2557⟩
private theorem pr2579 : PrimeCertificate 2579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1289]) (by decide +kernel)
def pv2579 : PrimeValue := ⟨2579, pr2579⟩
private theorem pr2591 : PrimeCertificate 2591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv37]) (by decide +kernel)
def pv2591 : PrimeValue := ⟨2591, pr2591⟩
private theorem pr2593 : PrimeCertificate 2593 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3]) (by decide +kernel)
def pv2593 : PrimeValue := ⟨2593, pr2593⟩
private theorem pr2609 : PrimeCertificate 2609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv163]) (by decide +kernel)
def pv2609 : PrimeValue := ⟨2609, pr2609⟩
private theorem pr2617 : PrimeCertificate 2617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv109]) (by decide +kernel)
def pv2617 : PrimeValue := ⟨2617, pr2617⟩
private theorem pr2621 : PrimeCertificate 2621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv131]) (by decide +kernel)
def pv2621 : PrimeValue := ⟨2621, pr2621⟩
private theorem pr2633 : PrimeCertificate 2633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv47]) (by decide +kernel)
def pv2633 : PrimeValue := ⟨2633, pr2633⟩
private theorem pr2647 : PrimeCertificate 2647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv2647 : PrimeValue := ⟨2647, pr2647⟩
private theorem pr2657 : PrimeCertificate 2657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83]) (by decide +kernel)
def pv2657 : PrimeValue := ⟨2657, pr2657⟩
private theorem pr2659 : PrimeCertificate 2659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv443]) (by decide +kernel)
def pv2659 : PrimeValue := ⟨2659, pr2659⟩
private theorem pr2663 : PrimeCertificate 2663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11]) (by decide +kernel)
def pv2663 : PrimeValue := ⟨2663, pr2663⟩
private theorem pr2671 : PrimeCertificate 2671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv89]) (by decide +kernel)
def pv2671 : PrimeValue := ⟨2671, pr2671⟩
private theorem pr2677 : PrimeCertificate 2677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv223]) (by decide +kernel)
def pv2677 : PrimeValue := ⟨2677, pr2677⟩
private theorem pr2683 : PrimeCertificate 2683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv149]) (by decide +kernel)
def pv2683 : PrimeValue := ⟨2683, pr2683⟩
private theorem pr2687 : PrimeCertificate 2687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv79]) (by decide +kernel)
def pv2687 : PrimeValue := ⟨2687, pr2687⟩
private theorem pr2689 : PrimeCertificate 2689 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv2689 : PrimeValue := ⟨2689, pr2689⟩
private theorem pr2693 : PrimeCertificate 2693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv673]) (by decide +kernel)
def pv2693 : PrimeValue := ⟨2693, pr2693⟩
private theorem pr2699 : PrimeCertificate 2699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv71]) (by decide +kernel)
def pv2699 : PrimeValue := ⟨2699, pr2699⟩
private theorem pr2707 : PrimeCertificate 2707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv41]) (by decide +kernel)
def pv2707 : PrimeValue := ⟨2707, pr2707⟩
private theorem pr2711 : PrimeCertificate 2711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv271]) (by decide +kernel)
def pv2711 : PrimeValue := ⟨2711, pr2711⟩
private theorem pr2713 : PrimeCertificate 2713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv113]) (by decide +kernel)
def pv2713 : PrimeValue := ⟨2713, pr2713⟩
private theorem pr2719 : PrimeCertificate 2719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv151]) (by decide +kernel)
def pv2719 : PrimeValue := ⟨2719, pr2719⟩
private theorem pr2729 : PrimeCertificate 2729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv31]) (by decide +kernel)
def pv2729 : PrimeValue := ⟨2729, pr2729⟩
private theorem pr2731 : PrimeCertificate 2731 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv2731 : PrimeValue := ⟨2731, pr2731⟩
private theorem pr2741 : PrimeCertificate 2741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv137]) (by decide +kernel)
def pv2741 : PrimeValue := ⟨2741, pr2741⟩
private theorem pr2749 : PrimeCertificate 2749 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv229]) (by decide +kernel)
def pv2749 : PrimeValue := ⟨2749, pr2749⟩
private theorem pr2753 : PrimeCertificate 2753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43]) (by decide +kernel)
def pv2753 : PrimeValue := ⟨2753, pr2753⟩
private theorem pr2767 : PrimeCertificate 2767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv461]) (by decide +kernel)
def pv2767 : PrimeValue := ⟨2767, pr2767⟩
private theorem pr2777 : PrimeCertificate 2777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv347]) (by decide +kernel)
def pv2777 : PrimeValue := ⟨2777, pr2777⟩
private theorem pr2789 : PrimeCertificate 2789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv41]) (by decide +kernel)
def pv2789 : PrimeValue := ⟨2789, pr2789⟩
private theorem pr2791 : PrimeCertificate 2791 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv2791 : PrimeValue := ⟨2791, pr2791⟩
private theorem pr2797 : PrimeCertificate 2797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv233]) (by decide +kernel)
def pv2797 : PrimeValue := ⟨2797, pr2797⟩
private theorem pr2801 : PrimeCertificate 2801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv2801 : PrimeValue := ⟨2801, pr2801⟩
private theorem pr2803 : PrimeCertificate 2803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv467]) (by decide +kernel)
def pv2803 : PrimeValue := ⟨2803, pr2803⟩
private theorem pr2819 : PrimeCertificate 2819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1409]) (by decide +kernel)
def pv2819 : PrimeValue := ⟨2819, pr2819⟩
private theorem pr2833 : PrimeCertificate 2833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv2833 : PrimeValue := ⟨2833, pr2833⟩
private theorem pr2837 : PrimeCertificate 2837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv709]) (by decide +kernel)
def pv2837 : PrimeValue := ⟨2837, pr2837⟩
private theorem pr2843 : PrimeCertificate 2843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29]) (by decide +kernel)
def pv2843 : PrimeValue := ⟨2843, pr2843⟩
private theorem pr2851 : PrimeCertificate 2851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv2851 : PrimeValue := ⟨2851, pr2851⟩
private theorem pr2857 : PrimeCertificate 2857 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv2857 : PrimeValue := ⟨2857, pr2857⟩
private theorem pr2861 : PrimeCertificate 2861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13]) (by decide +kernel)
def pv2861 : PrimeValue := ⟨2861, pr2861⟩
private theorem pr2879 : PrimeCertificate 2879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv1439]) (by decide +kernel)
def pv2879 : PrimeValue := ⟨2879, pr2879⟩
private theorem pr2887 : PrimeCertificate 2887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv37]) (by decide +kernel)
def pv2887 : PrimeValue := ⟨2887, pr2887⟩
private theorem pr2897 : PrimeCertificate 2897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv181]) (by decide +kernel)
def pv2897 : PrimeValue := ⟨2897, pr2897⟩
private theorem pr2903 : PrimeCertificate 2903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv1451]) (by decide +kernel)
def pv2903 : PrimeValue := ⟨2903, pr2903⟩
private theorem pr2909 : PrimeCertificate 2909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv727]) (by decide +kernel)
def pv2909 : PrimeValue := ⟨2909, pr2909⟩
private theorem pr2917 : PrimeCertificate 2917 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv2917 : PrimeValue := ⟨2917, pr2917⟩
private theorem pr2927 : PrimeCertificate 2927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv19]) (by decide +kernel)
def pv2927 : PrimeValue := ⟨2927, pr2927⟩
private theorem pr2939 : PrimeCertificate 2939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv113]) (by decide +kernel)
def pv2939 : PrimeValue := ⟨2939, pr2939⟩
private theorem pr2953 : PrimeCertificate 2953 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv2953 : PrimeValue := ⟨2953, pr2953⟩
private theorem pr2957 : PrimeCertificate 2957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv739]) (by decide +kernel)
def pv2957 : PrimeValue := ⟨2957, pr2957⟩
private theorem pr2963 : PrimeCertificate 2963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1481]) (by decide +kernel)
def pv2963 : PrimeValue := ⟨2963, pr2963⟩
private theorem pr2969 : PrimeCertificate 2969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv53]) (by decide +kernel)
def pv2969 : PrimeValue := ⟨2969, pr2969⟩
private theorem pr2971 : PrimeCertificate 2971 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv2971 : PrimeValue := ⟨2971, pr2971⟩
private theorem pr2999 : PrimeCertificate 2999 :=
  certifyPrime (q := pv17) (ls := [pv2,pv1499]) (by decide +kernel)
def pv2999 : PrimeValue := ⟨2999, pr2999⟩
private theorem pr3001 : PrimeCertificate 3001 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv3001 : PrimeValue := ⟨3001, pr3001⟩
private theorem pr3011 : PrimeCertificate 3011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv43]) (by decide +kernel)
def pv3011 : PrimeValue := ⟨3011, pr3011⟩
private theorem pr3019 : PrimeCertificate 3019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv503]) (by decide +kernel)
def pv3019 : PrimeValue := ⟨3019, pr3019⟩
private theorem pr3023 : PrimeCertificate 3023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv1511]) (by decide +kernel)
def pv3023 : PrimeValue := ⟨3023, pr3023⟩
private theorem pr3037 : PrimeCertificate 3037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv3037 : PrimeValue := ⟨3037, pr3037⟩
private theorem pr3041 : PrimeCertificate 3041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv3041 : PrimeValue := ⟨3041, pr3041⟩
private theorem pr3049 : PrimeCertificate 3049 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv127]) (by decide +kernel)
def pv3049 : PrimeValue := ⟨3049, pr3049⟩
private theorem pr3061 : PrimeCertificate 3061 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv3061 : PrimeValue := ⟨3061, pr3061⟩
private theorem pr3067 : PrimeCertificate 3067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv73]) (by decide +kernel)
def pv3067 : PrimeValue := ⟨3067, pr3067⟩
private theorem pr3079 : PrimeCertificate 3079 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv3079 : PrimeValue := ⟨3079, pr3079⟩
private theorem pr3083 : PrimeCertificate 3083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv67]) (by decide +kernel)
def pv3083 : PrimeValue := ⟨3083, pr3083⟩
private theorem pr3089 : PrimeCertificate 3089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv193]) (by decide +kernel)
def pv3089 : PrimeValue := ⟨3089, pr3089⟩
private theorem pr3109 : PrimeCertificate 3109 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv3109 : PrimeValue := ⟨3109, pr3109⟩
private theorem pr3119 : PrimeCertificate 3119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv1559]) (by decide +kernel)
def pv3119 : PrimeValue := ⟨3119, pr3119⟩
private theorem pr3121 : PrimeCertificate 3121 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv3121 : PrimeValue := ⟨3121, pr3121⟩
private theorem pr3137 : PrimeCertificate 3137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7]) (by decide +kernel)
def pv3137 : PrimeValue := ⟨3137, pr3137⟩
private theorem pr3163 : PrimeCertificate 3163 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv31]) (by decide +kernel)
def pv3163 : PrimeValue := ⟨3163, pr3163⟩
private theorem pr3167 : PrimeCertificate 3167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv1583]) (by decide +kernel)
def pv3167 : PrimeValue := ⟨3167, pr3167⟩
private theorem pr3169 : PrimeCertificate 3169 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv3169 : PrimeValue := ⟨3169, pr3169⟩
private theorem pr3181 : PrimeCertificate 3181 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv53]) (by decide +kernel)
def pv3181 : PrimeValue := ⟨3181, pr3181⟩
private theorem pr3187 : PrimeCertificate 3187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv3187 : PrimeValue := ⟨3187, pr3187⟩
private theorem pr3191 : PrimeCertificate 3191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv29]) (by decide +kernel)
def pv3191 : PrimeValue := ⟨3191, pr3191⟩
private theorem pr3203 : PrimeCertificate 3203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1601]) (by decide +kernel)
def pv3203 : PrimeValue := ⟨3203, pr3203⟩
private theorem pr3209 : PrimeCertificate 3209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv401]) (by decide +kernel)
def pv3209 : PrimeValue := ⟨3209, pr3209⟩
private theorem pr3217 : PrimeCertificate 3217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv3217 : PrimeValue := ⟨3217, pr3217⟩
private theorem pr3221 : PrimeCertificate 3221 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv23]) (by decide +kernel)
def pv3221 : PrimeValue := ⟨3221, pr3221⟩
private theorem pr3229 : PrimeCertificate 3229 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv269]) (by decide +kernel)
def pv3229 : PrimeValue := ⟨3229, pr3229⟩
private theorem pr3251 : PrimeCertificate 3251 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv3251 : PrimeValue := ⟨3251, pr3251⟩
private theorem pr3253 : PrimeCertificate 3253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv271]) (by decide +kernel)
def pv3253 : PrimeValue := ⟨3253, pr3253⟩
private theorem pr3257 : PrimeCertificate 3257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv37]) (by decide +kernel)
def pv3257 : PrimeValue := ⟨3257, pr3257⟩
private theorem pr3259 : PrimeCertificate 3259 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv181]) (by decide +kernel)
def pv3259 : PrimeValue := ⟨3259, pr3259⟩
private theorem pr3271 : PrimeCertificate 3271 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv109]) (by decide +kernel)
def pv3271 : PrimeValue := ⟨3271, pr3271⟩
private theorem pr3299 : PrimeCertificate 3299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv97]) (by decide +kernel)
def pv3299 : PrimeValue := ⟨3299, pr3299⟩
private theorem pr3301 : PrimeCertificate 3301 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv3301 : PrimeValue := ⟨3301, pr3301⟩
private theorem pr3307 : PrimeCertificate 3307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv29]) (by decide +kernel)
def pv3307 : PrimeValue := ⟨3307, pr3307⟩
private theorem pr3313 : PrimeCertificate 3313 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv3313 : PrimeValue := ⟨3313, pr3313⟩
private theorem pr3319 : PrimeCertificate 3319 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv79]) (by decide +kernel)
def pv3319 : PrimeValue := ⟨3319, pr3319⟩
private theorem pr3323 : PrimeCertificate 3323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv151]) (by decide +kernel)
def pv3323 : PrimeValue := ⟨3323, pr3323⟩
private theorem pr3329 : PrimeCertificate 3329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13]) (by decide +kernel)
def pv3329 : PrimeValue := ⟨3329, pr3329⟩
private theorem pr3331 : PrimeCertificate 3331 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv3331 : PrimeValue := ⟨3331, pr3331⟩
private theorem pr3343 : PrimeCertificate 3343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv557]) (by decide +kernel)
def pv3343 : PrimeValue := ⟨3343, pr3343⟩
private theorem pr3347 : PrimeCertificate 3347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv239]) (by decide +kernel)
def pv3347 : PrimeValue := ⟨3347, pr3347⟩
private theorem pr3359 : PrimeCertificate 3359 :=
  certifyPrime (q := pv11) (ls := [pv2,pv23,pv73]) (by decide +kernel)
def pv3359 : PrimeValue := ⟨3359, pr3359⟩
private theorem pr3361 : PrimeCertificate 3361 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv3361 : PrimeValue := ⟨3361, pr3361⟩
private theorem pr3371 : PrimeCertificate 3371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv337]) (by decide +kernel)
def pv3371 : PrimeValue := ⟨3371, pr3371⟩
private theorem pr3373 : PrimeCertificate 3373 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv281]) (by decide +kernel)
def pv3373 : PrimeValue := ⟨3373, pr3373⟩
private theorem pr3389 : PrimeCertificate 3389 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11]) (by decide +kernel)
def pv3389 : PrimeValue := ⟨3389, pr3389⟩
private theorem pr3391 : PrimeCertificate 3391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv113]) (by decide +kernel)
def pv3391 : PrimeValue := ⟨3391, pr3391⟩
private theorem pr3407 : PrimeCertificate 3407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv131]) (by decide +kernel)
def pv3407 : PrimeValue := ⟨3407, pr3407⟩
private theorem pr3413 : PrimeCertificate 3413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv853]) (by decide +kernel)
def pv3413 : PrimeValue := ⟨3413, pr3413⟩
private theorem pr3433 : PrimeCertificate 3433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv3433 : PrimeValue := ⟨3433, pr3433⟩
private theorem pr3449 : PrimeCertificate 3449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv431]) (by decide +kernel)
def pv3449 : PrimeValue := ⟨3449, pr3449⟩
private theorem pr3457 : PrimeCertificate 3457 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3]) (by decide +kernel)
def pv3457 : PrimeValue := ⟨3457, pr3457⟩
private theorem pr3461 : PrimeCertificate 3461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv173]) (by decide +kernel)
def pv3461 : PrimeValue := ⟨3461, pr3461⟩
private theorem pr3463 : PrimeCertificate 3463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv577]) (by decide +kernel)
def pv3463 : PrimeValue := ⟨3463, pr3463⟩
private theorem pr3467 : PrimeCertificate 3467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1733]) (by decide +kernel)
def pv3467 : PrimeValue := ⟨3467, pr3467⟩
private theorem pr3469 : PrimeCertificate 3469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv3469 : PrimeValue := ⟨3469, pr3469⟩
private theorem pr3491 : PrimeCertificate 3491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv349]) (by decide +kernel)
def pv3491 : PrimeValue := ⟨3491, pr3491⟩
private theorem pr3499 : PrimeCertificate 3499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv53]) (by decide +kernel)
def pv3499 : PrimeValue := ⟨3499, pr3499⟩
private theorem pr3511 : PrimeCertificate 3511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv3511 : PrimeValue := ⟨3511, pr3511⟩
private theorem pr3517 : PrimeCertificate 3517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv293]) (by decide +kernel)
def pv3517 : PrimeValue := ⟨3517, pr3517⟩
private theorem pr3527 : PrimeCertificate 3527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv43]) (by decide +kernel)
def pv3527 : PrimeValue := ⟨3527, pr3527⟩
private theorem pr3529 : PrimeCertificate 3529 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv3529 : PrimeValue := ⟨3529, pr3529⟩
private theorem pr3533 : PrimeCertificate 3533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv883]) (by decide +kernel)
def pv3533 : PrimeValue := ⟨3533, pr3533⟩
private theorem pr3539 : PrimeCertificate 3539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv61]) (by decide +kernel)
def pv3539 : PrimeValue := ⟨3539, pr3539⟩
private theorem pr3541 : PrimeCertificate 3541 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv59]) (by decide +kernel)
def pv3541 : PrimeValue := ⟨3541, pr3541⟩
private theorem pr3547 : PrimeCertificate 3547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv197]) (by decide +kernel)
def pv3547 : PrimeValue := ⟨3547, pr3547⟩
private theorem pr3557 : PrimeCertificate 3557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv127]) (by decide +kernel)
def pv3557 : PrimeValue := ⟨3557, pr3557⟩
private theorem pr3559 : PrimeCertificate 3559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv593]) (by decide +kernel)
def pv3559 : PrimeValue := ⟨3559, pr3559⟩
private theorem pr3571 : PrimeCertificate 3571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv3571 : PrimeValue := ⟨3571, pr3571⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
