/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables03/Table245
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables03/Table245.pv1893173
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table063
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table136

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1893173 : PrimeCertificate 1893173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv473293]) (by decide +kernel)
def pv1893173 : PrimeValue := ⟨1893173, pr1893173⟩
private theorem pr1893329 : PrimeCertificate 1893329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv1621]) (by decide +kernel)
def pv1893329 : PrimeValue := ⟨1893329, pr1893329⟩
private theorem pr1893533 : PrimeCertificate 1893533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv473383]) (by decide +kernel)
def pv1893533 : PrimeValue := ⟨1893533, pr1893533⟩
private theorem pr1893581 : PrimeCertificate 1893581 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv7283]) (by decide +kernel)
def pv1893581 : PrimeValue := ⟨1893581, pr1893581⟩
private theorem pr1893971 : PrimeCertificate 1893971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv17,pv857]) (by decide +kernel)
def pv1893971 : PrimeValue := ⟨1893971, pr1893971⟩
private theorem pr1894001 : PrimeCertificate 1894001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv947]) (by decide +kernel)
def pv1894001 : PrimeValue := ⟨1894001, pr1894001⟩
private theorem pr1894121 : PrimeCertificate 1894121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47353]) (by decide +kernel)
def pv1894121 : PrimeValue := ⟨1894121, pr1894121⟩
private theorem pr1894229 : PrimeCertificate 1894229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv67651]) (by decide +kernel)
def pv1894229 : PrimeValue := ⟨1894229, pr1894229⟩
private theorem pr1894481 : PrimeCertificate 1894481 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv17,pv199]) (by decide +kernel)
def pv1894481 : PrimeValue := ⟨1894481, pr1894481⟩
private theorem pr1894643 : PrimeCertificate 1894643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv73,pv683]) (by decide +kernel)
def pv1894643 : PrimeValue := ⟨1894643, pr1894643⟩
private theorem pr1894853 : PrimeCertificate 1894853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv10079]) (by decide +kernel)
def pv1894853 : PrimeValue := ⟨1894853, pr1894853⟩
private theorem pr1895051 : PrimeCertificate 1895051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv151,pv251]) (by decide +kernel)
def pv1895051 : PrimeValue := ⟨1895051, pr1895051⟩
private theorem pr1895093 : PrimeCertificate 1895093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv29,pv31]) (by decide +kernel)
def pv1895093 : PrimeValue := ⟨1895093, pr1895093⟩
private theorem pr1895273 : PrimeCertificate 1895273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv236909]) (by decide +kernel)
def pv1895273 : PrimeValue := ⟨1895273, pr1895273⟩
private theorem pr1895513 : PrimeCertificate 1895513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv5779]) (by decide +kernel)
def pv1895513 : PrimeValue := ⟨1895513, pr1895513⟩
private theorem pr1895609 : PrimeCertificate 1895609 :=
  certifyPrime (q := pv17) (ls := [pv2,pv11,pv13,pv1657]) (by decide +kernel)
def pv1895609 : PrimeValue := ⟨1895609, pr1895609⟩
private theorem pr1895693 : PrimeCertificate 1895693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv473923]) (by decide +kernel)
def pv1895693 : PrimeValue := ⟨1895693, pr1895693⟩
private theorem pr1895711 : PrimeCertificate 1895711 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv293,pv647]) (by decide +kernel)
def pv1895711 : PrimeValue := ⟨1895711, pr1895711⟩
private theorem pr1895903 : PrimeCertificate 1895903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv547,pv1733]) (by decide +kernel)
def pv1895903 : PrimeValue := ⟨1895903, pr1895903⟩
private theorem pr1896221 : PrimeCertificate 1896221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv94811]) (by decide +kernel)
def pv1896221 : PrimeValue := ⟨1896221, pr1896221⟩
private theorem pr1896263 : PrimeCertificate 1896263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv47,pv20173]) (by decide +kernel)
def pv1896263 : PrimeValue := ⟨1896263, pr1896263⟩
private theorem pr1896413 : PrimeCertificate 1896413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv89,pv761]) (by decide +kernel)
def pv1896413 : PrimeValue := ⟨1896413, pr1896413⟩
private theorem pr1896431 : PrimeCertificate 1896431 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv189643]) (by decide +kernel)
def pv1896431 : PrimeValue := ⟨1896431, pr1896431⟩
private theorem pr1897001 : PrimeCertificate 1897001 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv271]) (by decide +kernel)
def pv1897001 : PrimeValue := ⟨1897001, pr1897001⟩
private theorem pr1897139 : PrimeCertificate 1897139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv37,pv827]) (by decide +kernel)
def pv1897139 : PrimeValue := ⟨1897139, pr1897139⟩
private theorem pr1897229 : PrimeCertificate 1897229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv474307]) (by decide +kernel)
def pv1897229 : PrimeValue := ⟨1897229, pr1897229⟩
private theorem pr1897481 : PrimeCertificate 1897481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv41,pv89]) (by decide +kernel)
def pv1897481 : PrimeValue := ⟨1897481, pr1897481⟩
private theorem pr1897529 : PrimeCertificate 1897529 :=
  certifyPrime (q := pv11) (ls := [pv2,pv29,pv8179]) (by decide +kernel)
def pv1897529 : PrimeValue := ⟨1897529, pr1897529⟩
private theorem pr1897751 : PrimeCertificate 1897751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7591]) (by decide +kernel)
def pv1897751 : PrimeValue := ⟨1897751, pr1897751⟩
private theorem pr1897793 : PrimeCertificate 1897793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv2281]) (by decide +kernel)
def pv1897793 : PrimeValue := ⟨1897793, pr1897793⟩
private theorem pr1897943 : PrimeCertificate 1897943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv948971]) (by decide +kernel)
def pv1897943 : PrimeValue := ⟨1897943, pr1897943⟩
private theorem pr1897949 : PrimeCertificate 1897949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv19,pv113]) (by decide +kernel)
def pv1897949 : PrimeValue := ⟨1897949, pr1897949⟩
private theorem pr1897979 : PrimeCertificate 1897979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv948989]) (by decide +kernel)
def pv1897979 : PrimeValue := ⟨1897979, pr1897979⟩
private theorem pr1897991 : PrimeCertificate 1897991 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv189799]) (by decide +kernel)
def pv1897991 : PrimeValue := ⟨1897991, pr1897991⟩
private theorem pr1898153 : PrimeCertificate 1898153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv821]) (by decide +kernel)
def pv1898153 : PrimeValue := ⟨1898153, pr1898153⟩
private theorem pr1898243 : PrimeCertificate 1898243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv949121]) (by decide +kernel)
def pv1898243 : PrimeValue := ⟨1898243, pr1898243⟩
private theorem pr1898609 : PrimeCertificate 1898609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107,pv1109]) (by decide +kernel)
def pv1898609 : PrimeValue := ⟨1898609, pr1898609⟩
private theorem pr1898783 : PrimeCertificate 1898783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv949391]) (by decide +kernel)
def pv1898783 : PrimeValue := ⟨1898783, pr1898783⟩
private theorem pr1898801 : PrimeCertificate 1898801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47,pv101]) (by decide +kernel)
def pv1898801 : PrimeValue := ⟨1898801, pr1898801⟩
private theorem pr1898861 : PrimeCertificate 1898861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv263]) (by decide +kernel)
def pv1898861 : PrimeValue := ⟨1898861, pr1898861⟩
private theorem pr1899119 : PrimeCertificate 1899119 :=
  certifyPrime (q := pv31) (ls := [pv2,pv13,pv73043]) (by decide +kernel)
def pv1899119 : PrimeValue := ⟨1899119, pr1899119⟩
private theorem pr1899701 : PrimeCertificate 1899701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv157]) (by decide +kernel)
def pv1899701 : PrimeValue := ⟨1899701, pr1899701⟩
private theorem pr1900499 : PrimeCertificate 1900499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv55897]) (by decide +kernel)
def pv1900499 : PrimeValue := ⟨1900499, pr1900499⟩
private theorem pr1900571 : PrimeCertificate 1900571 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv19,pv1429]) (by decide +kernel)
def pv1900571 : PrimeValue := ⟨1900571, pr1900571⟩
private theorem pr1900709 : PrimeCertificate 1900709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv643,pv739]) (by decide +kernel)
def pv1900709 : PrimeValue := ⟨1900709, pr1900709⟩
private theorem pr1900721 : PrimeCertificate 1900721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv1033]) (by decide +kernel)
def pv1900721 : PrimeValue := ⟨1900721, pr1900721⟩
private theorem pr1901489 : PrimeCertificate 1901489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv118843]) (by decide +kernel)
def pv1901489 : PrimeValue := ⟨1901489, pr1901489⟩
private theorem pr1901771 : PrimeCertificate 1901771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv14629]) (by decide +kernel)
def pv1901771 : PrimeValue := ⟨1901771, pr1901771⟩
private theorem pr1901891 : PrimeCertificate 1901891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv4423]) (by decide +kernel)
def pv1901891 : PrimeValue := ⟨1901891, pr1901891⟩
private theorem pr1902209 : PrimeCertificate 1902209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv193]) (by decide +kernel)
def pv1902209 : PrimeValue := ⟨1902209, pr1902209⟩
private theorem pr1902293 : PrimeCertificate 1902293 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv67939]) (by decide +kernel)
def pv1902293 : PrimeValue := ⟨1902293, pr1902293⟩
private theorem pr1902311 : PrimeCertificate 1902311 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv181,pv1051]) (by decide +kernel)
def pv1902311 : PrimeValue := ⟨1902311, pr1902311⟩
private theorem pr1902611 : PrimeCertificate 1902611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv190261]) (by decide +kernel)
def pv1902611 : PrimeValue := ⟨1902611, pr1902611⟩
private theorem pr1902839 : PrimeCertificate 1902839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv199,pv683]) (by decide +kernel)
def pv1902839 : PrimeValue := ⟨1902839, pr1902839⟩
private theorem pr1903061 : PrimeCertificate 1903061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv95153]) (by decide +kernel)
def pv1903061 : PrimeValue := ⟨1903061, pr1903061⟩
private theorem pr1903103 : PrimeCertificate 1903103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv107,pv8893]) (by decide +kernel)
def pv1903103 : PrimeValue := ⟨1903103, pr1903103⟩
private theorem pr1903463 : PrimeCertificate 1903463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv31,pv2791]) (by decide +kernel)
def pv1903463 : PrimeValue := ⟨1903463, pr1903463⟩
private theorem pr1903529 : PrimeCertificate 1903529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv97,pv223]) (by decide +kernel)
def pv1903529 : PrimeValue := ⟨1903529, pr1903529⟩
private theorem pr1903931 : PrimeCertificate 1903931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv59,pv461]) (by decide +kernel)
def pv1903931 : PrimeValue := ⟨1903931, pr1903931⟩
private theorem pr1904069 : PrimeCertificate 1904069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv28001]) (by decide +kernel)
def pv1904069 : PrimeValue := ⟨1904069, pr1904069⟩
private theorem pr1904489 : PrimeCertificate 1904489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv8209]) (by decide +kernel)
def pv1904489 : PrimeValue := ⟨1904489, pr1904489⟩
private theorem pr1904849 : PrimeCertificate 1904849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv79,pv137]) (by decide +kernel)
def pv1904849 : PrimeValue := ⟨1904849, pr1904849⟩
private theorem pr1904951 : PrimeCertificate 1904951 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv31,pv1229]) (by decide +kernel)
def pv1904951 : PrimeValue := ⟨1904951, pr1904951⟩
private theorem pr1905023 : PrimeCertificate 1905023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv2777]) (by decide +kernel)
def pv1905023 : PrimeValue := ⟨1905023, pr1905023⟩
private theorem pr1905041 : PrimeCertificate 1905041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23813]) (by decide +kernel)
def pv1905041 : PrimeValue := ⟨1905041, pr1905041⟩
private theorem pr1905383 : PrimeCertificate 1905383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv952691]) (by decide +kernel)
def pv1905383 : PrimeValue := ⟨1905383, pr1905383⟩
private theorem pr1905713 : PrimeCertificate 1905713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv119107]) (by decide +kernel)
def pv1905713 : PrimeValue := ⟨1905713, pr1905713⟩
private theorem pr1905773 : PrimeCertificate 1905773 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv43313]) (by decide +kernel)
def pv1905773 : PrimeValue := ⟨1905773, pr1905773⟩
private theorem pr1905983 : PrimeCertificate 1905983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv5639]) (by decide +kernel)
def pv1905983 : PrimeValue := ⟨1905983, pr1905983⟩
private theorem pr1906109 : PrimeCertificate 1906109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv28031]) (by decide +kernel)
def pv1906109 : PrimeValue := ⟨1906109, pr1906109⟩
private theorem pr1906379 : PrimeCertificate 1906379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv41443]) (by decide +kernel)
def pv1906379 : PrimeValue := ⟨1906379, pr1906379⟩
private theorem pr1906511 : PrimeCertificate 1906511 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv83,pv2297]) (by decide +kernel)
def pv1906511 : PrimeValue := ⟨1906511, pr1906511⟩
private theorem pr1907063 : PrimeCertificate 1907063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv827,pv1153]) (by decide +kernel)
def pv1907063 : PrimeValue := ⟨1907063, pr1907063⟩
private theorem pr1907291 : PrimeCertificate 1907291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv2477]) (by decide +kernel)
def pv1907291 : PrimeValue := ⟨1907291, pr1907291⟩
private theorem pr1907303 : PrimeCertificate 1907303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv953651]) (by decide +kernel)
def pv1907303 : PrimeValue := ⟨1907303, pr1907303⟩
private theorem pr1907333 : PrimeCertificate 1907333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv4007]) (by decide +kernel)
def pv1907333 : PrimeValue := ⟨1907333, pr1907333⟩
private theorem pr1907369 : PrimeCertificate 1907369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv7691]) (by decide +kernel)
def pv1907369 : PrimeValue := ⟨1907369, pr1907369⟩
private theorem pr1907729 : PrimeCertificate 1907729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv119233]) (by decide +kernel)
def pv1907729 : PrimeValue := ⟨1907729, pr1907729⟩
private theorem pr1907819 : PrimeCertificate 1907819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv86719]) (by decide +kernel)
def pv1907819 : PrimeValue := ⟨1907819, pr1907819⟩
private theorem pr1907903 : PrimeCertificate 1907903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv521,pv1831]) (by decide +kernel)
def pv1907903 : PrimeValue := ⟨1907903, pr1907903⟩
private theorem pr1907963 : PrimeCertificate 1907963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19469]) (by decide +kernel)
def pv1907963 : PrimeValue := ⟨1907963, pr1907963⟩
private theorem pr1907981 : PrimeCertificate 1907981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv5021]) (by decide +kernel)
def pv1907981 : PrimeValue := ⟨1907981, pr1907981⟩
private theorem pr1908083 : PrimeCertificate 1908083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv43,pv2017]) (by decide +kernel)
def pv1908083 : PrimeValue := ⟨1908083, pr1908083⟩
private theorem pr1908299 : PrimeCertificate 1908299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv4397]) (by decide +kernel)
def pv1908299 : PrimeValue := ⟨1908299, pr1908299⟩
private theorem pr1908311 : PrimeCertificate 1908311 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv23,pv8297]) (by decide +kernel)
def pv1908311 : PrimeValue := ⟨1908311, pr1908311⟩
private theorem pr1908323 : PrimeCertificate 1908323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv3863]) (by decide +kernel)
def pv1908323 : PrimeValue := ⟨1908323, pr1908323⟩
private theorem pr1908761 : PrimeCertificate 1908761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv17,pv401]) (by decide +kernel)
def pv1908761 : PrimeValue := ⟨1908761, pr1908761⟩
private theorem pr1908779 : PrimeCertificate 1908779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv50231]) (by decide +kernel)
def pv1908779 : PrimeValue := ⟨1908779, pr1908779⟩
private theorem pr1908869 : PrimeCertificate 1908869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv36709]) (by decide +kernel)
def pv1908869 : PrimeValue := ⟨1908869, pr1908869⟩
private theorem pr1909109 : PrimeCertificate 1909109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv477277]) (by decide +kernel)
def pv1909109 : PrimeValue := ⟨1909109, pr1909109⟩
private theorem pr1909223 : PrimeCertificate 1909223 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv136373]) (by decide +kernel)
def pv1909223 : PrimeValue := ⟨1909223, pr1909223⟩
private theorem pr1909343 : PrimeCertificate 1909343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv954671]) (by decide +kernel)
def pv1909343 : PrimeValue := ⟨1909343, pr1909343⟩
private theorem pr1909949 : PrimeCertificate 1909949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv8093]) (by decide +kernel)
def pv1909949 : PrimeValue := ⟨1909949, pr1909949⟩
private theorem pr1909991 : PrimeCertificate 1909991 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv389,pv491]) (by decide +kernel)
def pv1909991 : PrimeValue := ⟨1909991, pr1909991⟩
private theorem pr1910063 : PrimeCertificate 1910063 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv11,pv79,pv157]) (by decide +kernel)
def pv1910063 : PrimeValue := ⟨1910063, pr1910063⟩
private theorem pr1910159 : PrimeCertificate 1910159 :=
  certifyPrime (q := pv11) (ls := [pv2,pv31,pv30809]) (by decide +kernel)
def pv1910159 : PrimeValue := ⟨1910159, pr1910159⟩
private theorem pr1910399 : PrimeCertificate 1910399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv61,pv2237]) (by decide +kernel)
def pv1910399 : PrimeValue := ⟨1910399, pr1910399⟩
private theorem pr1910423 : PrimeCertificate 1910423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv955211]) (by decide +kernel)
def pv1910423 : PrimeValue := ⟨1910423, pr1910423⟩
private theorem pr1910663 : PrimeCertificate 1910663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv43,pv1709]) (by decide +kernel)
def pv1910663 : PrimeValue := ⟨1910663, pr1910663⟩
private theorem pr1910693 : PrimeCertificate 1910693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv68239]) (by decide +kernel)
def pv1910693 : PrimeValue := ⟨1910693, pr1910693⟩
private theorem pr1910813 : PrimeCertificate 1910813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv541,pv883]) (by decide +kernel)
def pv1910813 : PrimeValue := ⟨1910813, pr1910813⟩
private theorem pr1911053 : PrimeCertificate 1911053 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv257]) (by decide +kernel)
def pv1911053 : PrimeValue := ⟨1911053, pr1911053⟩
private theorem pr1911083 : PrimeCertificate 1911083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv955541]) (by decide +kernel)
def pv1911083 : PrimeValue := ⟨1911083, pr1911083⟩
private theorem pr1911209 : PrimeCertificate 1911209 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv17,pv23,pv47]) (by decide +kernel)
def pv1911209 : PrimeValue := ⟨1911209, pr1911209⟩
private theorem pr1911263 : PrimeCertificate 1911263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv433,pv2207]) (by decide +kernel)
def pv1911263 : PrimeValue := ⟨1911263, pr1911263⟩
private theorem pr1911653 : PrimeCertificate 1911653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv477913]) (by decide +kernel)
def pv1911653 : PrimeValue := ⟨1911653, pr1911653⟩
private theorem pr1912061 : PrimeCertificate 1912061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv95603]) (by decide +kernel)
def pv1912061 : PrimeValue := ⟨1912061, pr1912061⟩
private theorem pr1912121 : PrimeCertificate 1912121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv6829]) (by decide +kernel)
def pv1912121 : PrimeValue := ⟨1912121, pr1912121⟩
private theorem pr1912133 : PrimeCertificate 1912133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv4733]) (by decide +kernel)
def pv1912133 : PrimeValue := ⟨1912133, pr1912133⟩
private theorem pr1912259 : PrimeCertificate 1912259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv9857]) (by decide +kernel)
def pv1912259 : PrimeValue := ⟨1912259, pr1912259⟩
private theorem pr1912499 : PrimeCertificate 1912499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv136607]) (by decide +kernel)
def pv1912499 : PrimeValue := ⟨1912499, pr1912499⟩
private theorem pr1912541 : PrimeCertificate 1912541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv719]) (by decide +kernel)
def pv1912541 : PrimeValue := ⟨1912541, pr1912541⟩
private theorem pr1912583 : PrimeCertificate 1912583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv67,pv2039]) (by decide +kernel)
def pv1912583 : PrimeValue := ⟨1912583, pr1912583⟩
private theorem pr1912679 : PrimeCertificate 1912679 :=
  certifyPrime (q := pv13) (ls := [pv2,pv37,pv25847]) (by decide +kernel)
def pv1912679 : PrimeValue := ⟨1912679, pr1912679⟩
private theorem pr1912913 : PrimeCertificate 1912913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv119557]) (by decide +kernel)
def pv1912913 : PrimeValue := ⟨1912913, pr1912913⟩
private theorem pr1913003 : PrimeCertificate 1913003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv23,pv457]) (by decide +kernel)
def pv1913003 : PrimeValue := ⟨1913003, pr1913003⟩
private theorem pr1913291 : PrimeCertificate 1913291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv293,pv653]) (by decide +kernel)
def pv1913291 : PrimeValue := ⟨1913291, pr1913291⟩
private theorem pr1913501 : PrimeCertificate 1913501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv89]) (by decide +kernel)
def pv1913501 : PrimeValue := ⟨1913501, pr1913501⟩
private theorem pr1913819 : PrimeCertificate 1913819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv956909]) (by decide +kernel)
def pv1913819 : PrimeValue := ⟨1913819, pr1913819⟩
private theorem pr1913861 : PrimeCertificate 1913861 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv17,pv433]) (by decide +kernel)
def pv1913861 : PrimeValue := ⟨1913861, pr1913861⟩
private theorem pr1913963 : PrimeCertificate 1913963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv41,pv1373]) (by decide +kernel)
def pv1913963 : PrimeValue := ⟨1913963, pr1913963⟩
private theorem pr1913969 : PrimeCertificate 1913969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23,pv743]) (by decide +kernel)
def pv1913969 : PrimeValue := ⟨1913969, pr1913969⟩
private theorem pr1914131 : PrimeCertificate 1914131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv191413]) (by decide +kernel)
def pv1914131 : PrimeValue := ⟨1914131, pr1914131⟩
private theorem pr1914179 : PrimeCertificate 1914179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv136727]) (by decide +kernel)
def pv1914179 : PrimeValue := ⟨1914179, pr1914179⟩
private theorem pr1914371 : PrimeCertificate 1914371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv11261]) (by decide +kernel)
def pv1914371 : PrimeValue := ⟨1914371, pr1914371⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
