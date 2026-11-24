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

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1893173 : Nat.Prime 1893173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv473293]) (by decide +kernel)
def pv1893173 : PrimeValue := ⟨1893173, pr1893173⟩
private theorem pr1893329 : Nat.Prime 1893329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv73,pv1621]) (by decide +kernel)
def pv1893329 : PrimeValue := ⟨1893329, pr1893329⟩
private theorem pr1893533 : Nat.Prime 1893533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv473383]) (by decide +kernel)
def pv1893533 : PrimeValue := ⟨1893533, pr1893533⟩
private theorem pr1893581 : Nat.Prime 1893581 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv7283]) (by decide +kernel)
def pv1893581 : PrimeValue := ⟨1893581, pr1893581⟩
private theorem pr1893971 : Nat.Prime 1893971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv17,pv857]) (by decide +kernel)
def pv1893971 : PrimeValue := ⟨1893971, pr1893971⟩
private theorem pr1894001 : Nat.Prime 1894001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv947]) (by decide +kernel)
def pv1894001 : PrimeValue := ⟨1894001, pr1894001⟩
private theorem pr1894121 : Nat.Prime 1894121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv47353]) (by decide +kernel)
def pv1894121 : PrimeValue := ⟨1894121, pr1894121⟩
private theorem pr1894229 : Nat.Prime 1894229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv67651]) (by decide +kernel)
def pv1894229 : PrimeValue := ⟨1894229, pr1894229⟩
private theorem pr1894481 : Nat.Prime 1894481 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv17,pv199]) (by decide +kernel)
def pv1894481 : PrimeValue := ⟨1894481, pr1894481⟩
private theorem pr1894643 : Nat.Prime 1894643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv73,pv683]) (by decide +kernel)
def pv1894643 : PrimeValue := ⟨1894643, pr1894643⟩
private theorem pr1894853 : Nat.Prime 1894853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv10079]) (by decide +kernel)
def pv1894853 : PrimeValue := ⟨1894853, pr1894853⟩
private theorem pr1895051 : Nat.Prime 1895051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv151,pv251]) (by decide +kernel)
def pv1895051 : PrimeValue := ⟨1895051, pr1895051⟩
private theorem pr1895093 : Nat.Prime 1895093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv29,pv31]) (by decide +kernel)
def pv1895093 : PrimeValue := ⟨1895093, pr1895093⟩
private theorem pr1895273 : Nat.Prime 1895273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv236909]) (by decide +kernel)
def pv1895273 : PrimeValue := ⟨1895273, pr1895273⟩
private theorem pr1895513 : Nat.Prime 1895513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv5779]) (by decide +kernel)
def pv1895513 : PrimeValue := ⟨1895513, pr1895513⟩
private theorem pr1895609 : Nat.Prime 1895609 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv11,pv13,pv1657]) (by decide +kernel)
def pv1895609 : PrimeValue := ⟨1895609, pr1895609⟩
private theorem pr1895693 : Nat.Prime 1895693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv473923]) (by decide +kernel)
def pv1895693 : PrimeValue := ⟨1895693, pr1895693⟩
private theorem pr1895711 : Nat.Prime 1895711 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv293,pv647]) (by decide +kernel)
def pv1895711 : PrimeValue := ⟨1895711, pr1895711⟩
private theorem pr1895903 : Nat.Prime 1895903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv547,pv1733]) (by decide +kernel)
def pv1895903 : PrimeValue := ⟨1895903, pr1895903⟩
private theorem pr1896221 : Nat.Prime 1896221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv94811]) (by decide +kernel)
def pv1896221 : PrimeValue := ⟨1896221, pr1896221⟩
private theorem pr1896263 : Nat.Prime 1896263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv20173]) (by decide +kernel)
def pv1896263 : PrimeValue := ⟨1896263, pr1896263⟩
private theorem pr1896413 : Nat.Prime 1896413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv89,pv761]) (by decide +kernel)
def pv1896413 : PrimeValue := ⟨1896413, pr1896413⟩
private theorem pr1896431 : Nat.Prime 1896431 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv189643]) (by decide +kernel)
def pv1896431 : PrimeValue := ⟨1896431, pr1896431⟩
private theorem pr1897001 : Nat.Prime 1897001 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv271]) (by decide +kernel)
def pv1897001 : PrimeValue := ⟨1897001, pr1897001⟩
private theorem pr1897139 : Nat.Prime 1897139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv37,pv827]) (by decide +kernel)
def pv1897139 : PrimeValue := ⟨1897139, pr1897139⟩
private theorem pr1897229 : Nat.Prime 1897229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv474307]) (by decide +kernel)
def pv1897229 : PrimeValue := ⟨1897229, pr1897229⟩
private theorem pr1897481 : Nat.Prime 1897481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv41,pv89]) (by decide +kernel)
def pv1897481 : PrimeValue := ⟨1897481, pr1897481⟩
private theorem pr1897529 : Nat.Prime 1897529 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv29,pv8179]) (by decide +kernel)
def pv1897529 : PrimeValue := ⟨1897529, pr1897529⟩
private theorem pr1897751 : Nat.Prime 1897751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7591]) (by decide +kernel)
def pv1897751 : PrimeValue := ⟨1897751, pr1897751⟩
private theorem pr1897793 : Nat.Prime 1897793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv2281]) (by decide +kernel)
def pv1897793 : PrimeValue := ⟨1897793, pr1897793⟩
private theorem pr1897943 : Nat.Prime 1897943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv948971]) (by decide +kernel)
def pv1897943 : PrimeValue := ⟨1897943, pr1897943⟩
private theorem pr1897949 : Nat.Prime 1897949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17,pv19,pv113]) (by decide +kernel)
def pv1897949 : PrimeValue := ⟨1897949, pr1897949⟩
private theorem pr1897979 : Nat.Prime 1897979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv948989]) (by decide +kernel)
def pv1897979 : PrimeValue := ⟨1897979, pr1897979⟩
private theorem pr1897991 : Nat.Prime 1897991 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv189799]) (by decide +kernel)
def pv1897991 : PrimeValue := ⟨1897991, pr1897991⟩
private theorem pr1898153 : Nat.Prime 1898153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv821]) (by decide +kernel)
def pv1898153 : PrimeValue := ⟨1898153, pr1898153⟩
private theorem pr1898243 : Nat.Prime 1898243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv949121]) (by decide +kernel)
def pv1898243 : PrimeValue := ⟨1898243, pr1898243⟩
private theorem pr1898609 : Nat.Prime 1898609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv107,pv1109]) (by decide +kernel)
def pv1898609 : PrimeValue := ⟨1898609, pr1898609⟩
private theorem pr1898783 : Nat.Prime 1898783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv949391]) (by decide +kernel)
def pv1898783 : PrimeValue := ⟨1898783, pr1898783⟩
private theorem pr1898801 : Nat.Prime 1898801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv47,pv101]) (by decide +kernel)
def pv1898801 : PrimeValue := ⟨1898801, pr1898801⟩
private theorem pr1898861 : Nat.Prime 1898861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv263]) (by decide +kernel)
def pv1898861 : PrimeValue := ⟨1898861, pr1898861⟩
private theorem pr1899119 : Nat.Prime 1899119 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv13,pv73043]) (by decide +kernel)
def pv1899119 : PrimeValue := ⟨1899119, pr1899119⟩
private theorem pr1899701 : Nat.Prime 1899701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv157]) (by decide +kernel)
def pv1899701 : PrimeValue := ⟨1899701, pr1899701⟩
private theorem pr1900499 : Nat.Prime 1900499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv55897]) (by decide +kernel)
def pv1900499 : PrimeValue := ⟨1900499, pr1900499⟩
private theorem pr1900571 : Nat.Prime 1900571 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv19,pv1429]) (by decide +kernel)
def pv1900571 : PrimeValue := ⟨1900571, pr1900571⟩
private theorem pr1900709 : Nat.Prime 1900709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv643,pv739]) (by decide +kernel)
def pv1900709 : PrimeValue := ⟨1900709, pr1900709⟩
private theorem pr1900721 : Nat.Prime 1900721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv1033]) (by decide +kernel)
def pv1900721 : PrimeValue := ⟨1900721, pr1900721⟩
private theorem pr1901489 : Nat.Prime 1901489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv118843]) (by decide +kernel)
def pv1901489 : PrimeValue := ⟨1901489, pr1901489⟩
private theorem pr1901771 : Nat.Prime 1901771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv14629]) (by decide +kernel)
def pv1901771 : PrimeValue := ⟨1901771, pr1901771⟩
private theorem pr1901891 : Nat.Prime 1901891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv4423]) (by decide +kernel)
def pv1901891 : PrimeValue := ⟨1901891, pr1901891⟩
private theorem pr1902209 : Nat.Prime 1902209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv193]) (by decide +kernel)
def pv1902209 : PrimeValue := ⟨1902209, pr1902209⟩
private theorem pr1902293 : Nat.Prime 1902293 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv67939]) (by decide +kernel)
def pv1902293 : PrimeValue := ⟨1902293, pr1902293⟩
private theorem pr1902311 : Nat.Prime 1902311 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv181,pv1051]) (by decide +kernel)
def pv1902311 : PrimeValue := ⟨1902311, pr1902311⟩
private theorem pr1902611 : Nat.Prime 1902611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv190261]) (by decide +kernel)
def pv1902611 : PrimeValue := ⟨1902611, pr1902611⟩
private theorem pr1902839 : Nat.Prime 1902839 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv199,pv683]) (by decide +kernel)
def pv1902839 : PrimeValue := ⟨1902839, pr1902839⟩
private theorem pr1903061 : Nat.Prime 1903061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv95153]) (by decide +kernel)
def pv1903061 : PrimeValue := ⟨1903061, pr1903061⟩
private theorem pr1903103 : Nat.Prime 1903103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv107,pv8893]) (by decide +kernel)
def pv1903103 : PrimeValue := ⟨1903103, pr1903103⟩
private theorem pr1903463 : Nat.Prime 1903463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv31,pv2791]) (by decide +kernel)
def pv1903463 : PrimeValue := ⟨1903463, pr1903463⟩
private theorem pr1903529 : Nat.Prime 1903529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv97,pv223]) (by decide +kernel)
def pv1903529 : PrimeValue := ⟨1903529, pr1903529⟩
private theorem pr1903931 : Nat.Prime 1903931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv59,pv461]) (by decide +kernel)
def pv1903931 : PrimeValue := ⟨1903931, pr1903931⟩
private theorem pr1904069 : Nat.Prime 1904069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv28001]) (by decide +kernel)
def pv1904069 : PrimeValue := ⟨1904069, pr1904069⟩
private theorem pr1904489 : Nat.Prime 1904489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv8209]) (by decide +kernel)
def pv1904489 : PrimeValue := ⟨1904489, pr1904489⟩
private theorem pr1904849 : Nat.Prime 1904849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv79,pv137]) (by decide +kernel)
def pv1904849 : PrimeValue := ⟨1904849, pr1904849⟩
private theorem pr1904951 : Nat.Prime 1904951 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv31,pv1229]) (by decide +kernel)
def pv1904951 : PrimeValue := ⟨1904951, pr1904951⟩
private theorem pr1905023 : Nat.Prime 1905023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv2777]) (by decide +kernel)
def pv1905023 : PrimeValue := ⟨1905023, pr1905023⟩
private theorem pr1905041 : Nat.Prime 1905041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23813]) (by decide +kernel)
def pv1905041 : PrimeValue := ⟨1905041, pr1905041⟩
private theorem pr1905383 : Nat.Prime 1905383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv952691]) (by decide +kernel)
def pv1905383 : PrimeValue := ⟨1905383, pr1905383⟩
private theorem pr1905713 : Nat.Prime 1905713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv119107]) (by decide +kernel)
def pv1905713 : PrimeValue := ⟨1905713, pr1905713⟩
private theorem pr1905773 : Nat.Prime 1905773 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv43313]) (by decide +kernel)
def pv1905773 : PrimeValue := ⟨1905773, pr1905773⟩
private theorem pr1905983 : Nat.Prime 1905983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv5639]) (by decide +kernel)
def pv1905983 : PrimeValue := ⟨1905983, pr1905983⟩
private theorem pr1906109 : Nat.Prime 1906109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv28031]) (by decide +kernel)
def pv1906109 : PrimeValue := ⟨1906109, pr1906109⟩
private theorem pr1906379 : Nat.Prime 1906379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv41443]) (by decide +kernel)
def pv1906379 : PrimeValue := ⟨1906379, pr1906379⟩
private theorem pr1906511 : Nat.Prime 1906511 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv83,pv2297]) (by decide +kernel)
def pv1906511 : PrimeValue := ⟨1906511, pr1906511⟩
private theorem pr1907063 : Nat.Prime 1907063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv827,pv1153]) (by decide +kernel)
def pv1907063 : PrimeValue := ⟨1907063, pr1907063⟩
private theorem pr1907291 : Nat.Prime 1907291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv2477]) (by decide +kernel)
def pv1907291 : PrimeValue := ⟨1907291, pr1907291⟩
private theorem pr1907303 : Nat.Prime 1907303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv953651]) (by decide +kernel)
def pv1907303 : PrimeValue := ⟨1907303, pr1907303⟩
private theorem pr1907333 : Nat.Prime 1907333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv4007]) (by decide +kernel)
def pv1907333 : PrimeValue := ⟨1907333, pr1907333⟩
private theorem pr1907369 : Nat.Prime 1907369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv7691]) (by decide +kernel)
def pv1907369 : PrimeValue := ⟨1907369, pr1907369⟩
private theorem pr1907729 : Nat.Prime 1907729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv119233]) (by decide +kernel)
def pv1907729 : PrimeValue := ⟨1907729, pr1907729⟩
private theorem pr1907819 : Nat.Prime 1907819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv86719]) (by decide +kernel)
def pv1907819 : PrimeValue := ⟨1907819, pr1907819⟩
private theorem pr1907903 : Nat.Prime 1907903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv521,pv1831]) (by decide +kernel)
def pv1907903 : PrimeValue := ⟨1907903, pr1907903⟩
private theorem pr1907963 : Nat.Prime 1907963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19469]) (by decide +kernel)
def pv1907963 : PrimeValue := ⟨1907963, pr1907963⟩
private theorem pr1907981 : Nat.Prime 1907981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv5021]) (by decide +kernel)
def pv1907981 : PrimeValue := ⟨1907981, pr1907981⟩
private theorem pr1908083 : Nat.Prime 1908083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv43,pv2017]) (by decide +kernel)
def pv1908083 : PrimeValue := ⟨1908083, pr1908083⟩
private theorem pr1908299 : Nat.Prime 1908299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv31,pv4397]) (by decide +kernel)
def pv1908299 : PrimeValue := ⟨1908299, pr1908299⟩
private theorem pr1908311 : Nat.Prime 1908311 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv23,pv8297]) (by decide +kernel)
def pv1908311 : PrimeValue := ⟨1908311, pr1908311⟩
private theorem pr1908323 : Nat.Prime 1908323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv19,pv3863]) (by decide +kernel)
def pv1908323 : PrimeValue := ⟨1908323, pr1908323⟩
private theorem pr1908761 : Nat.Prime 1908761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv17,pv401]) (by decide +kernel)
def pv1908761 : PrimeValue := ⟨1908761, pr1908761⟩
private theorem pr1908779 : Nat.Prime 1908779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv50231]) (by decide +kernel)
def pv1908779 : PrimeValue := ⟨1908779, pr1908779⟩
private theorem pr1908869 : Nat.Prime 1908869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv36709]) (by decide +kernel)
def pv1908869 : PrimeValue := ⟨1908869, pr1908869⟩
private theorem pr1909109 : Nat.Prime 1909109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv477277]) (by decide +kernel)
def pv1909109 : PrimeValue := ⟨1909109, pr1909109⟩
private theorem pr1909223 : Nat.Prime 1909223 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv136373]) (by decide +kernel)
def pv1909223 : PrimeValue := ⟨1909223, pr1909223⟩
private theorem pr1909343 : Nat.Prime 1909343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv954671]) (by decide +kernel)
def pv1909343 : PrimeValue := ⟨1909343, pr1909343⟩
private theorem pr1909949 : Nat.Prime 1909949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv8093]) (by decide +kernel)
def pv1909949 : PrimeValue := ⟨1909949, pr1909949⟩
private theorem pr1909991 : Nat.Prime 1909991 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv389,pv491]) (by decide +kernel)
def pv1909991 : PrimeValue := ⟨1909991, pr1909991⟩
private theorem pr1910063 : Nat.Prime 1910063 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv11,pv79,pv157]) (by decide +kernel)
def pv1910063 : PrimeValue := ⟨1910063, pr1910063⟩
private theorem pr1910159 : Nat.Prime 1910159 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv31,pv30809]) (by decide +kernel)
def pv1910159 : PrimeValue := ⟨1910159, pr1910159⟩
private theorem pr1910399 : Nat.Prime 1910399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv61,pv2237]) (by decide +kernel)
def pv1910399 : PrimeValue := ⟨1910399, pr1910399⟩
private theorem pr1910423 : Nat.Prime 1910423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv955211]) (by decide +kernel)
def pv1910423 : PrimeValue := ⟨1910423, pr1910423⟩
private theorem pr1910663 : Nat.Prime 1910663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv43,pv1709]) (by decide +kernel)
def pv1910663 : PrimeValue := ⟨1910663, pr1910663⟩
private theorem pr1910693 : Nat.Prime 1910693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv68239]) (by decide +kernel)
def pv1910693 : PrimeValue := ⟨1910693, pr1910693⟩
private theorem pr1910813 : Nat.Prime 1910813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv541,pv883]) (by decide +kernel)
def pv1910813 : PrimeValue := ⟨1910813, pr1910813⟩
private theorem pr1911053 : Nat.Prime 1911053 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv13,pv257]) (by decide +kernel)
def pv1911053 : PrimeValue := ⟨1911053, pr1911053⟩
private theorem pr1911083 : Nat.Prime 1911083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv955541]) (by decide +kernel)
def pv1911083 : PrimeValue := ⟨1911083, pr1911083⟩
private theorem pr1911209 : Nat.Prime 1911209 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv17,pv23,pv47]) (by decide +kernel)
def pv1911209 : PrimeValue := ⟨1911209, pr1911209⟩
private theorem pr1911263 : Nat.Prime 1911263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv433,pv2207]) (by decide +kernel)
def pv1911263 : PrimeValue := ⟨1911263, pr1911263⟩
private theorem pr1911653 : Nat.Prime 1911653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv477913]) (by decide +kernel)
def pv1911653 : PrimeValue := ⟨1911653, pr1911653⟩
private theorem pr1912061 : Nat.Prime 1912061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv95603]) (by decide +kernel)
def pv1912061 : PrimeValue := ⟨1912061, pr1912061⟩
private theorem pr1912121 : Nat.Prime 1912121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv6829]) (by decide +kernel)
def pv1912121 : PrimeValue := ⟨1912121, pr1912121⟩
private theorem pr1912133 : Nat.Prime 1912133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv4733]) (by decide +kernel)
def pv1912133 : PrimeValue := ⟨1912133, pr1912133⟩
private theorem pr1912259 : Nat.Prime 1912259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv9857]) (by decide +kernel)
def pv1912259 : PrimeValue := ⟨1912259, pr1912259⟩
private theorem pr1912499 : Nat.Prime 1912499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv136607]) (by decide +kernel)
def pv1912499 : PrimeValue := ⟨1912499, pr1912499⟩
private theorem pr1912541 : Nat.Prime 1912541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv719]) (by decide +kernel)
def pv1912541 : PrimeValue := ⟨1912541, pr1912541⟩
private theorem pr1912583 : Nat.Prime 1912583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv67,pv2039]) (by decide +kernel)
def pv1912583 : PrimeValue := ⟨1912583, pr1912583⟩
private theorem pr1912679 : Nat.Prime 1912679 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv37,pv25847]) (by decide +kernel)
def pv1912679 : PrimeValue := ⟨1912679, pr1912679⟩
private theorem pr1912913 : Nat.Prime 1912913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv119557]) (by decide +kernel)
def pv1912913 : PrimeValue := ⟨1912913, pr1912913⟩
private theorem pr1913003 : Nat.Prime 1913003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv23,pv457]) (by decide +kernel)
def pv1913003 : PrimeValue := ⟨1913003, pr1913003⟩
private theorem pr1913291 : Nat.Prime 1913291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv293,pv653]) (by decide +kernel)
def pv1913291 : PrimeValue := ⟨1913291, pr1913291⟩
private theorem pr1913501 : Nat.Prime 1913501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv89]) (by decide +kernel)
def pv1913501 : PrimeValue := ⟨1913501, pr1913501⟩
private theorem pr1913819 : Nat.Prime 1913819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv956909]) (by decide +kernel)
def pv1913819 : PrimeValue := ⟨1913819, pr1913819⟩
private theorem pr1913861 : Nat.Prime 1913861 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv17,pv433]) (by decide +kernel)
def pv1913861 : PrimeValue := ⟨1913861, pr1913861⟩
private theorem pr1913963 : Nat.Prime 1913963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv41,pv1373]) (by decide +kernel)
def pv1913963 : PrimeValue := ⟨1913963, pr1913963⟩
private theorem pr1913969 : Nat.Prime 1913969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv23,pv743]) (by decide +kernel)
def pv1913969 : PrimeValue := ⟨1913969, pr1913969⟩
private theorem pr1914131 : Nat.Prime 1914131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv191413]) (by decide +kernel)
def pv1914131 : PrimeValue := ⟨1914131, pr1914131⟩
private theorem pr1914179 : Nat.Prime 1914179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv136727]) (by decide +kernel)
def pv1914179 : PrimeValue := ⟨1914179, pr1914179⟩
private theorem pr1914371 : Nat.Prime 1914371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv11261]) (by decide +kernel)
def pv1914371 : PrimeValue := ⟨1914371, pr1914371⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
