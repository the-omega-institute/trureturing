/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table156
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table156.pv1729961
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table134

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1729961 : Nat.Prime 1729961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv61,pv709]) (by decide +kernel)
def pv1729961 : PrimeValue := ⟨1729961, pr1729961⟩
private theorem pr1730153 : Nat.Prime 1730153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv9403]) (by decide +kernel)
def pv1730153 : PrimeValue := ⟨1730153, pr1730153⟩
private theorem pr1730213 : Nat.Prime 1730213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv39323]) (by decide +kernel)
def pv1730213 : PrimeValue := ⟨1730213, pr1730213⟩
private theorem pr1730441 : Nat.Prime 1730441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43261]) (by decide +kernel)
def pv1730441 : PrimeValue := ⟨1730441, pr1730441⟩
private theorem pr1730831 : Nat.Prime 1730831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv73,pv2371]) (by decide +kernel)
def pv1730831 : PrimeValue := ⟨1730831, pr1730831⟩
private theorem pr1730849 : Nat.Prime 1730849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv7727]) (by decide +kernel)
def pv1730849 : PrimeValue := ⟨1730849, pr1730849⟩
private theorem pr1731209 : Nat.Prime 1731209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv216401]) (by decide +kernel)
def pv1731209 : PrimeValue := ⟨1731209, pr1731209⟩
private theorem pr1731311 : Nat.Prime 1731311 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv7,pv24733]) (by decide +kernel)
def pv1731311 : PrimeValue := ⟨1731311, pr1731311⟩
private theorem pr1731659 : Nat.Prime 1731659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv865829]) (by decide +kernel)
def pv1731659 : PrimeValue := ⟨1731659, pr1731659⟩
private theorem pr1731953 : Nat.Prime 1731953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv108247]) (by decide +kernel)
def pv1731953 : PrimeValue := ⟨1731953, pr1731953⟩
private theorem pr1732421 : Nat.Prime 1732421 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv47,pv97]) (by decide +kernel)
def pv1732421 : PrimeValue := ⟨1732421, pr1732421⟩
private theorem pr1732799 : Nat.Prime 1732799 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv866399]) (by decide +kernel)
def pv1732799 : PrimeValue := ⟨1732799, pr1732799⟩
private theorem pr1733159 : Nat.Prime 1733159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv43,pv2879]) (by decide +kernel)
def pv1733159 : PrimeValue := ⟨1733159, pr1733159⟩
private theorem pr1733183 : Nat.Prime 1733183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv78781]) (by decide +kernel)
def pv1733183 : PrimeValue := ⟨1733183, pr1733183⟩
private theorem pr1733279 : Nat.Prime 1733279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv866639]) (by decide +kernel)
def pv1733279 : PrimeValue := ⟨1733279, pr1733279⟩
private theorem pr1733321 : Nat.Prime 1733321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv2549]) (by decide +kernel)
def pv1733321 : PrimeValue := ⟨1733321, pr1733321⟩
private theorem pr1733393 : Nat.Prime 1733393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv131,pv827]) (by decide +kernel)
def pv1733393 : PrimeValue := ⟨1733393, pr1733393⟩
private theorem pr1733519 : Nat.Prime 1733519 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv866759]) (by decide +kernel)
def pv1733519 : PrimeValue := ⟨1733519, pr1733519⟩
private theorem pr1733639 : Nat.Prime 1733639 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv866819]) (by decide +kernel)
def pv1733639 : PrimeValue := ⟨1733639, pr1733639⟩
private theorem pr1733741 : Nat.Prime 1733741 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv3769]) (by decide +kernel)
def pv1733741 : PrimeValue := ⟨1733741, pr1733741⟩
private theorem pr1733909 : Nat.Prime 1733909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv157,pv251]) (by decide +kernel)
def pv1733909 : PrimeValue := ⟨1733909, pr1733909⟩
private theorem pr1733999 : Nat.Prime 1733999 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv211,pv587]) (by decide +kernel)
def pv1733999 : PrimeValue := ⟨1733999, pr1733999⟩
private theorem pr1734179 : Nat.Prime 1734179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv131,pv6619]) (by decide +kernel)
def pv1734179 : PrimeValue := ⟨1734179, pr1734179⟩
private theorem pr1734203 : Nat.Prime 1734203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv83,pv337]) (by decide +kernel)
def pv1734203 : PrimeValue := ⟨1734203, pr1734203⟩
private theorem pr1734371 : Nat.Prime 1734371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv15767]) (by decide +kernel)
def pv1734371 : PrimeValue := ⟨1734371, pr1734371⟩
private theorem pr1734431 : Nat.Prime 1734431 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv23,pv7541]) (by decide +kernel)
def pv1734431 : PrimeValue := ⟨1734431, pr1734431⟩
private theorem pr1734611 : Nat.Prime 1734611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv89,pv1949]) (by decide +kernel)
def pv1734611 : PrimeValue := ⟨1734611, pr1734611⟩
private theorem pr1735001 : Nat.Prime 1735001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv347]) (by decide +kernel)
def pv1735001 : PrimeValue := ⟨1735001, pr1735001⟩
private theorem pr1735043 : Nat.Prime 1735043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv45659]) (by decide +kernel)
def pv1735043 : PrimeValue := ⟨1735043, pr1735043⟩
private theorem pr1735049 : Nat.Prime 1735049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv30983]) (by decide +kernel)
def pv1735049 : PrimeValue := ⟨1735049, pr1735049⟩
private theorem pr1735313 : Nat.Prime 1735313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv108457]) (by decide +kernel)
def pv1735313 : PrimeValue := ⟨1735313, pr1735313⟩
private theorem pr1735463 : Nat.Prime 1735463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv51043]) (by decide +kernel)
def pv1735463 : PrimeValue := ⟨1735463, pr1735463⟩
private theorem pr1735529 : Nat.Prime 1735529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv401,pv541]) (by decide +kernel)
def pv1735529 : PrimeValue := ⟨1735529, pr1735529⟩
private theorem pr1735703 : Nat.Prime 1735703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv67,pv12953]) (by decide +kernel)
def pv1735703 : PrimeValue := ⟨1735703, pr1735703⟩
private theorem pr1735823 : Nat.Prime 1735823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv78901]) (by decide +kernel)
def pv1735823 : PrimeValue := ⟨1735823, pr1735823⟩
private theorem pr1736369 : Nat.Prime 1736369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv2309]) (by decide +kernel)
def pv1736369 : PrimeValue := ⟨1736369, pr1736369⟩
private theorem pr1736393 : Nat.Prime 1736393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv101,pv307]) (by decide +kernel)
def pv1736393 : PrimeValue := ⟨1736393, pr1736393⟩
private theorem pr1736519 : Nat.Prime 1736519 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv71,pv1747]) (by decide +kernel)
def pv1736519 : PrimeValue := ⟨1736519, pr1736519⟩
private theorem pr1736681 : Nat.Prime 1736681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv3947]) (by decide +kernel)
def pv1736681 : PrimeValue := ⟨1736681, pr1736681⟩
private theorem pr1736831 : Nat.Prime 1736831 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv173683]) (by decide +kernel)
def pv1736831 : PrimeValue := ⟨1736831, pr1736831⟩
private theorem pr1736849 : Nat.Prime 1736849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv108553]) (by decide +kernel)
def pv1736849 : PrimeValue := ⟨1736849, pr1736849⟩
private theorem pr1736921 : Nat.Prime 1736921 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv173,pv251]) (by decide +kernel)
def pv1736921 : PrimeValue := ⟨1736921, pr1736921⟩
private theorem pr1737041 : Nat.Prime 1737041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv21713]) (by decide +kernel)
def pv1737041 : PrimeValue := ⟨1737041, pr1737041⟩
private theorem pr1737089 : Nat.Prime 1737089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv331]) (by decide +kernel)
def pv1737089 : PrimeValue := ⟨1737089, pr1737089⟩
private theorem pr1737161 : Nat.Prime 1737161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv137,pv317]) (by decide +kernel)
def pv1737161 : PrimeValue := ⟨1737161, pr1737161⟩
private theorem pr1737269 : Nat.Prime 1737269 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv33409]) (by decide +kernel)
def pv1737269 : PrimeValue := ⟨1737269, pr1737269⟩
private theorem pr1737311 : Nat.Prime 1737311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv67,pv2593]) (by decide +kernel)
def pv1737311 : PrimeValue := ⟨1737311, pr1737311⟩
private theorem pr1737899 : Nat.Prime 1737899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv277,pv3137]) (by decide +kernel)
def pv1737899 : PrimeValue := ⟨1737899, pr1737899⟩
private theorem pr1738043 : Nat.Prime 1738043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv869021]) (by decide +kernel)
def pv1738043 : PrimeValue := ⟨1738043, pr1738043⟩
private theorem pr1738211 : Nat.Prime 1738211 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv101,pv1721]) (by decide +kernel)
def pv1738211 : PrimeValue := ⟨1738211, pr1738211⟩
private theorem pr1738391 : Nat.Prime 1738391 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv173839]) (by decide +kernel)
def pv1738391 : PrimeValue := ⟨1738391, pr1738391⟩
private theorem pr1738421 : Nat.Prime 1738421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv5113]) (by decide +kernel)
def pv1738421 : PrimeValue := ⟨1738421, pr1738421⟩
private theorem pr1738493 : Nat.Prime 1738493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv2141]) (by decide +kernel)
def pv1738493 : PrimeValue := ⟨1738493, pr1738493⟩
private theorem pr1738703 : Nat.Prime 1738703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv124193]) (by decide +kernel)
def pv1738703 : PrimeValue := ⟨1738703, pr1738703⟩
private theorem pr1739063 : Nat.Prime 1739063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv211,pv317]) (by decide +kernel)
def pv1739063 : PrimeValue := ⟨1739063, pr1739063⟩
private theorem pr1739453 : Nat.Prime 1739453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv3041]) (by decide +kernel)
def pv1739453 : PrimeValue := ⟨1739453, pr1739453⟩
private theorem pr1739603 : Nat.Prime 1739603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv45779]) (by decide +kernel)
def pv1739603 : PrimeValue := ⟨1739603, pr1739603⟩
private theorem pr1739891 : Nat.Prime 1739891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv257,pv677]) (by decide +kernel)
def pv1739891 : PrimeValue := ⟨1739891, pr1739891⟩
private theorem pr1740209 : Nat.Prime 1740209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61,pv1783]) (by decide +kernel)
def pv1740209 : PrimeValue := ⟨1740209, pr1740209⟩
private theorem pr1740503 : Nat.Prime 1740503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv157,pv241]) (by decide +kernel)
def pv1740503 : PrimeValue := ⟨1740503, pr1740503⟩
private theorem pr1740521 : Nat.Prime 1740521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv53,pv821]) (by decide +kernel)
def pv1740521 : PrimeValue := ⟨1740521, pr1740521⟩
private theorem pr1740701 : Nat.Prime 1740701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv103]) (by decide +kernel)
def pv1740701 : PrimeValue := ⟨1740701, pr1740701⟩
private theorem pr1740731 : Nat.Prime 1740731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv109,pv1597]) (by decide +kernel)
def pv1740731 : PrimeValue := ⟨1740731, pr1740731⟩
private theorem pr1740779 : Nat.Prime 1740779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv23,pv41,pv71]) (by decide +kernel)
def pv1740779 : PrimeValue := ⟨1740779, pr1740779⟩
private theorem pr1740911 : Nat.Prime 1740911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv174091]) (by decide +kernel)
def pv1740911 : PrimeValue := ⟨1740911, pr1740911⟩
private theorem pr1741079 : Nat.Prime 1741079 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv659,pv1321]) (by decide +kernel)
def pv1741079 : PrimeValue := ⟨1741079, pr1741079⟩
private theorem pr1741469 : Nat.Prime 1741469 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv823]) (by decide +kernel)
def pv1741469 : PrimeValue := ⟨1741469, pr1741469⟩
private theorem pr1741529 : Nat.Prime 1741529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv217691]) (by decide +kernel)
def pv1741529 : PrimeValue := ⟨1741529, pr1741529⟩
private theorem pr1741541 : Nat.Prime 1741541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv4583]) (by decide +kernel)
def pv1741541 : PrimeValue := ⟨1741541, pr1741541⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
