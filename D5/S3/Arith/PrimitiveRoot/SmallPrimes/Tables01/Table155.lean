/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table155
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table155.pv1687799
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table044
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table058
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table132
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table133
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table134

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1687799 : Nat.Prime 1687799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv120557]) (by decide +kernel)
def pv1687799 : PrimeValue := ⟨1687799, pr1687799⟩
private theorem pr1687859 : Nat.Prime 1687859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv29101]) (by decide +kernel)
def pv1687859 : PrimeValue := ⟨1687859, pr1687859⟩
private theorem pr1688189 : Nat.Prime 1688189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv97,pv229]) (by decide +kernel)
def pv1688189 : PrimeValue := ⟨1688189, pr1688189⟩
private theorem pr1688231 : Nat.Prime 1688231 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv5,pv79,pv2137]) (by decide +kernel)
def pv1688231 : PrimeValue := ⟨1688231, pr1688231⟩
private theorem pr1688243 : Nat.Prime 1688243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv844121]) (by decide +kernel)
def pv1688243 : PrimeValue := ⟨1688243, pr1688243⟩
private theorem pr1688279 : Nat.Prime 1688279 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv844139]) (by decide +kernel)
def pv1688279 : PrimeValue := ⟨1688279, pr1688279⟩
private theorem pr1688369 : Nat.Prime 1688369 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv11,pv53,pv181]) (by decide +kernel)
def pv1688369 : PrimeValue := ⟨1688369, pr1688369⟩
private theorem pr1688411 : Nat.Prime 1688411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv109,pv1549]) (by decide +kernel)
def pv1688411 : PrimeValue := ⟨1688411, pr1688411⟩
private theorem pr1688471 : Nat.Prime 1688471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv24121]) (by decide +kernel)
def pv1688471 : PrimeValue := ⟨1688471, pr1688471⟩
private theorem pr1688651 : Nat.Prime 1688651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv33773]) (by decide +kernel)
def pv1688651 : PrimeValue := ⟨1688651, pr1688651⟩
private theorem pr1688741 : Nat.Prime 1688741 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv84437]) (by decide +kernel)
def pv1688741 : PrimeValue := ⟨1688741, pr1688741⟩
private theorem pr1688789 : Nat.Prime 1688789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103,pv4099]) (by decide +kernel)
def pv1688789 : PrimeValue := ⟨1688789, pr1688789⟩
private theorem pr1688861 : Nat.Prime 1688861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv84443]) (by decide +kernel)
def pv1688861 : PrimeValue := ⟨1688861, pr1688861⟩
private theorem pr1688903 : Nat.Prime 1688903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv37,pv787]) (by decide +kernel)
def pv1688903 : PrimeValue := ⟨1688903, pr1688903⟩
private theorem pr1689053 : Nat.Prime 1689053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv59,pv421]) (by decide +kernel)
def pv1689053 : PrimeValue := ⟨1689053, pr1689053⟩
private theorem pr1689263 : Nat.Prime 1689263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv844631]) (by decide +kernel)
def pv1689263 : PrimeValue := ⟨1689263, pr1689263⟩
private theorem pr1689521 : Nat.Prime 1689521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv431]) (by decide +kernel)
def pv1689521 : PrimeValue := ⟨1689521, pr1689521⟩
private theorem pr1689713 : Nat.Prime 1689713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv105607]) (by decide +kernel)
def pv1689713 : PrimeValue := ⟨1689713, pr1689713⟩
private theorem pr1689923 : Nat.Prime 1689923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv64997]) (by decide +kernel)
def pv1689923 : PrimeValue := ⟨1689923, pr1689923⟩
private theorem pr1690103 : Nat.Prime 1690103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv20611]) (by decide +kernel)
def pv1690103 : PrimeValue := ⟨1690103, pr1690103⟩
private theorem pr1690121 : Nat.Prime 1690121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv31,pv47]) (by decide +kernel)
def pv1690121 : PrimeValue := ⟨1690121, pr1690121⟩
private theorem pr1690193 : Nat.Prime 1690193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv15091]) (by decide +kernel)
def pv1690193 : PrimeValue := ⟨1690193, pr1690193⟩
private theorem pr1690229 : Nat.Prime 1690229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv422557]) (by decide +kernel)
def pv1690229 : PrimeValue := ⟨1690229, pr1690229⟩
private theorem pr1690313 : Nat.Prime 1690313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv16253]) (by decide +kernel)
def pv1690313 : PrimeValue := ⟨1690313, pr1690313⟩
private theorem pr1690571 : Nat.Prime 1690571 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv24151]) (by decide +kernel)
def pv1690571 : PrimeValue := ⟨1690571, pr1690571⟩
private theorem pr1690739 : Nat.Prime 1690739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv120767]) (by decide +kernel)
def pv1690739 : PrimeValue := ⟨1690739, pr1690739⟩
private theorem pr1690883 : Nat.Prime 1690883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv845441]) (by decide +kernel)
def pv1690883 : PrimeValue := ⟨1690883, pr1690883⟩
private theorem pr1691051 : Nat.Prime 1691051 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv31,pv1091]) (by decide +kernel)
def pv1691051 : PrimeValue := ⟨1691051, pr1691051⟩
private theorem pr1691099 : Nat.Prime 1691099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv97,pv379]) (by decide +kernel)
def pv1691099 : PrimeValue := ⟨1691099, pr1691099⟩
private theorem pr1691303 : Nat.Prime 1691303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv571,pv1481]) (by decide +kernel)
def pv1691303 : PrimeValue := ⟨1691303, pr1691303⟩
private theorem pr1691633 : Nat.Prime 1691633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv105727]) (by decide +kernel)
def pv1691633 : PrimeValue := ⟨1691633, pr1691633⟩
private theorem pr1691759 : Nat.Prime 1691759 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv845879]) (by decide +kernel)
def pv1691759 : PrimeValue := ⟨1691759, pr1691759⟩
private theorem pr1691771 : Nat.Prime 1691771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv169177]) (by decide +kernel)
def pv1691771 : PrimeValue := ⟨1691771, pr1691771⟩
private theorem pr1691939 : Nat.Prime 1691939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv845969]) (by decide +kernel)
def pv1691939 : PrimeValue := ⟨1691939, pr1691939⟩
private theorem pr1692059 : Nat.Prime 1692059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv227,pv3727]) (by decide +kernel)
def pv1692059 : PrimeValue := ⟨1692059, pr1692059⟩
private theorem pr1692191 : Nat.Prime 1692191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv169219]) (by decide +kernel)
def pv1692191 : PrimeValue := ⟨1692191, pr1692191⟩
private theorem pr1692233 : Nat.Prime 1692233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv5717]) (by decide +kernel)
def pv1692233 : PrimeValue := ⟨1692233, pr1692233⟩
private theorem pr1692293 : Nat.Prime 1692293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv3181]) (by decide +kernel)
def pv1692293 : PrimeValue := ⟨1692293, pr1692293⟩
private theorem pr1692479 : Nat.Prime 1692479 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv23,pv36793]) (by decide +kernel)
def pv1692479 : PrimeValue := ⟨1692479, pr1692479⟩
private theorem pr1692563 : Nat.Prime 1692563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv20641]) (by decide +kernel)
def pv1692563 : PrimeValue := ⟨1692563, pr1692563⟩
private theorem pr1692791 : Nat.Prime 1692791 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv11,pv1399]) (by decide +kernel)
def pv1692791 : PrimeValue := ⟨1692791, pr1692791⟩
private theorem pr1693031 : Nat.Prime 1693031 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv23,pv433]) (by decide +kernel)
def pv1693031 : PrimeValue := ⟨1693031, pr1693031⟩
private theorem pr1693493 : Nat.Prime 1693493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv71,pv89]) (by decide +kernel)
def pv1693493 : PrimeValue := ⟨1693493, pr1693493⟩
private theorem pr1693553 : Nat.Prime 1693553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv15121]) (by decide +kernel)
def pv1693553 : PrimeValue := ⟨1693553, pr1693553⟩
private theorem pr1693661 : Nat.Prime 1693661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv4457]) (by decide +kernel)
def pv1693661 : PrimeValue := ⟨1693661, pr1693661⟩
private theorem pr1693943 : Nat.Prime 1693943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv19697]) (by decide +kernel)
def pv1693943 : PrimeValue := ⟨1693943, pr1693943⟩
private theorem pr1694573 : Nat.Prime 1694573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv2027]) (by decide +kernel)
def pv1694573 : PrimeValue := ⟨1694573, pr1694573⟩
private theorem pr1694831 : Nat.Prime 1694831 :=
  checkPrime_prime (q := pv53) (ls := [pv2,pv5,pv169483]) (by decide +kernel)
def pv1694831 : PrimeValue := ⟨1694831, pr1694831⟩
private theorem pr1695041 : Nat.Prime 1695041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv5297]) (by decide +kernel)
def pv1695041 : PrimeValue := ⟨1695041, pr1695041⟩
private theorem pr1695143 : Nat.Prime 1695143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv31,pv1439]) (by decide +kernel)
def pv1695143 : PrimeValue := ⟨1695143, pr1695143⟩
private theorem pr1695293 : Nat.Prime 1695293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv423823]) (by decide +kernel)
def pv1695293 : PrimeValue := ⟨1695293, pr1695293⟩
private theorem pr1695581 : Nat.Prime 1695581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv4987]) (by decide +kernel)
def pv1695581 : PrimeValue := ⟨1695581, pr1695581⟩
private theorem pr1695593 : Nat.Prime 1695593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv211949]) (by decide +kernel)
def pv1695593 : PrimeValue := ⟨1695593, pr1695593⟩
private theorem pr1695671 : Nat.Prime 1695671 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv169567]) (by decide +kernel)
def pv1695671 : PrimeValue := ⟨1695671, pr1695671⟩
private theorem pr1695779 : Nat.Prime 1695779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv59,pv2053]) (by decide +kernel)
def pv1695779 : PrimeValue := ⟨1695779, pr1695779⟩
private theorem pr1695929 : Nat.Prime 1695929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv23,pv709]) (by decide +kernel)
def pv1695929 : PrimeValue := ⟨1695929, pr1695929⟩
private theorem pr1696109 : Nat.Prime 1696109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv424027]) (by decide +kernel)
def pv1696109 : PrimeValue := ⟨1696109, pr1696109⟩
private theorem pr1696511 : Nat.Prime 1696511 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv19,pv8929]) (by decide +kernel)
def pv1696511 : PrimeValue := ⟨1696511, pr1696511⟩
private theorem pr1696811 : Nat.Prime 1696811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv169681]) (by decide +kernel)
def pv1696811 : PrimeValue := ⟨1696811, pr1696811⟩
private theorem pr1696979 : Nat.Prime 1696979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv848489]) (by decide +kernel)
def pv1696979 : PrimeValue := ⟨1696979, pr1696979⟩
private theorem pr1697243 : Nat.Prime 1697243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv193,pv4397]) (by decide +kernel)
def pv1697243 : PrimeValue := ⟨1697243, pr1697243⟩
private theorem pr1697309 : Nat.Prime 1697309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv23,pv971]) (by decide +kernel)
def pv1697309 : PrimeValue := ⟨1697309, pr1697309⟩
private theorem pr1697453 : Nat.Prime 1697453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv9029]) (by decide +kernel)
def pv1697453 : PrimeValue := ⟨1697453, pr1697453⟩
private theorem pr1697519 : Nat.Prime 1697519 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv17,pv49927]) (by decide +kernel)
def pv1697519 : PrimeValue := ⟨1697519, pr1697519⟩
private theorem pr1697873 : Nat.Prime 1697873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv877]) (by decide +kernel)
def pv1697873 : PrimeValue := ⟨1697873, pr1697873⟩
private theorem pr1698023 : Nat.Prime 1698023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv131,pv6481]) (by decide +kernel)
def pv1698023 : PrimeValue := ⟨1698023, pr1698023⟩
private theorem pr1698029 : Nat.Prime 1698029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv24971]) (by decide +kernel)
def pv1698029 : PrimeValue := ⟨1698029, pr1698029⟩
private theorem pr1698569 : Nat.Prime 1698569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv241,pv881]) (by decide +kernel)
def pv1698569 : PrimeValue := ⟨1698569, pr1698569⟩
private theorem pr1698701 : Nat.Prime 1698701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv16987]) (by decide +kernel)
def pv1698701 : PrimeValue := ⟨1698701, pr1698701⟩
private theorem pr1698881 : Nat.Prime 1698881 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv5309]) (by decide +kernel)
def pv1698881 : PrimeValue := ⟨1698881, pr1698881⟩
private theorem pr1698953 : Nat.Prime 1698953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv212369]) (by decide +kernel)
def pv1698953 : PrimeValue := ⟨1698953, pr1698953⟩
private theorem pr1699319 : Nat.Prime 1699319 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv59,pv14401]) (by decide +kernel)
def pv1699319 : PrimeValue := ⟨1699319, pr1699319⟩
private theorem pr1699361 : Nat.Prime 1699361 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv19,pv43]) (by decide +kernel)
def pv1699361 : PrimeValue := ⟨1699361, pr1699361⟩
private theorem pr1699469 : Nat.Prime 1699469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv424867]) (by decide +kernel)
def pv1699469 : PrimeValue := ⟨1699469, pr1699469⟩
private theorem pr1699679 : Nat.Prime 1699679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv849839]) (by decide +kernel)
def pv1699679 : PrimeValue := ⟨1699679, pr1699679⟩
private theorem pr1699781 : Nat.Prime 1699781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv2297]) (by decide +kernel)
def pv1699781 : PrimeValue := ⟨1699781, pr1699781⟩
private theorem pr1699829 : Nat.Prime 1699829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv97,pv337]) (by decide +kernel)
def pv1699829 : PrimeValue := ⟨1699829, pr1699829⟩
private theorem pr1699853 : Nat.Prime 1699853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv5519]) (by decide +kernel)
def pv1699853 : PrimeValue := ⟨1699853, pr1699853⟩
private theorem pr1700021 : Nat.Prime 1700021 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv12143]) (by decide +kernel)
def pv1700021 : PrimeValue := ⟨1700021, pr1700021⟩
private theorem pr1700189 : Nat.Prime 1700189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv41,pv1481]) (by decide +kernel)
def pv1700189 : PrimeValue := ⟨1700189, pr1700189⟩
private theorem pr1700423 : Nat.Prime 1700423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv850211]) (by decide +kernel)
def pv1700423 : PrimeValue := ⟨1700423, pr1700423⟩
private theorem pr1700441 : Nat.Prime 1700441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv6073]) (by decide +kernel)
def pv1700441 : PrimeValue := ⟨1700441, pr1700441⟩
private theorem pr1700591 : Nat.Prime 1700591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv173,pv983]) (by decide +kernel)
def pv1700591 : PrimeValue := ⟨1700591, pr1700591⟩
private theorem pr1700801 : Nat.Prime 1700801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1063]) (by decide +kernel)
def pv1700801 : PrimeValue := ⟨1700801, pr1700801⟩
private theorem pr1700921 : Nat.Prime 1700921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv3271]) (by decide +kernel)
def pv1700921 : PrimeValue := ⟨1700921, pr1700921⟩
private theorem pr1700981 : Nat.Prime 1700981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv85049]) (by decide +kernel)
def pv1700981 : PrimeValue := ⟨1700981, pr1700981⟩
private theorem pr1701179 : Nat.Prime 1701179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv739,pv1151]) (by decide +kernel)
def pv1701179 : PrimeValue := ⟨1701179, pr1701179⟩
private theorem pr1701263 : Nat.Prime 1701263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv850631]) (by decide +kernel)
def pv1701263 : PrimeValue := ⟨1701263, pr1701263⟩
private theorem pr1701449 : Nat.Prime 1701449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv23,pv1321]) (by decide +kernel)
def pv1701449 : PrimeValue := ⟨1701449, pr1701449⟩
private theorem pr1701461 : Nat.Prime 1701461 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv241,pv353]) (by decide +kernel)
def pv1701461 : PrimeValue := ⟨1701461, pr1701461⟩
private theorem pr1701509 : Nat.Prime 1701509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv425377]) (by decide +kernel)
def pv1701509 : PrimeValue := ⟨1701509, pr1701509⟩
private theorem pr1701533 : Nat.Prime 1701533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv67,pv907]) (by decide +kernel)
def pv1701533 : PrimeValue := ⟨1701533, pr1701533⟩
private theorem pr1701629 : Nat.Prime 1701629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv173,pv2459]) (by decide +kernel)
def pv1701629 : PrimeValue := ⟨1701629, pr1701629⟩
private theorem pr1701743 : Nat.Prime 1701743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv121553]) (by decide +kernel)
def pv1701743 : PrimeValue := ⟨1701743, pr1701743⟩
private theorem pr1701761 : Nat.Prime 1701761 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv2659]) (by decide +kernel)
def pv1701761 : PrimeValue := ⟨1701761, pr1701761⟩
private theorem pr1701809 : Nat.Prime 1701809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv106363]) (by decide +kernel)
def pv1701809 : PrimeValue := ⟨1701809, pr1701809⟩
private theorem pr1701851 : Nat.Prime 1701851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv101,pv337]) (by decide +kernel)
def pv1701851 : PrimeValue := ⟨1701851, pr1701851⟩
private theorem pr1702139 : Nat.Prime 1702139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv37003]) (by decide +kernel)
def pv1702139 : PrimeValue := ⟨1702139, pr1702139⟩
private theorem pr1702373 : Nat.Prime 1702373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv163,pv373]) (by decide +kernel)
def pv1702373 : PrimeValue := ⟨1702373, pr1702373⟩
private theorem pr1702511 : Nat.Prime 1702511 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv61,pv2791]) (by decide +kernel)
def pv1702511 : PrimeValue := ⟨1702511, pr1702511⟩
private theorem pr1702901 : Nat.Prime 1702901 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17029]) (by decide +kernel)
def pv1702901 : PrimeValue := ⟨1702901, pr1702901⟩
private theorem pr1703231 : Nat.Prime 1703231 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv17,pv43,pv233]) (by decide +kernel)
def pv1703231 : PrimeValue := ⟨1703231, pr1703231⟩
private theorem pr1703381 : Nat.Prime 1703381 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv23]) (by decide +kernel)
def pv1703381 : PrimeValue := ⟨1703381, pr1703381⟩
private theorem pr1703501 : Nat.Prime 1703501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3407]) (by decide +kernel)
def pv1703501 : PrimeValue := ⟨1703501, pr1703501⟩
private theorem pr1703573 : Nat.Prime 1703573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv181]) (by decide +kernel)
def pv1703573 : PrimeValue := ⟨1703573, pr1703573⟩
private theorem pr1704161 : Nat.Prime 1704161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv10651]) (by decide +kernel)
def pv1704161 : PrimeValue := ⟨1704161, pr1704161⟩
private theorem pr1704203 : Nat.Prime 1704203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv852101]) (by decide +kernel)
def pv1704203 : PrimeValue := ⟨1704203, pr1704203⟩
private theorem pr1704299 : Nat.Prime 1704299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv852149]) (by decide +kernel)
def pv1704299 : PrimeValue := ⟨1704299, pr1704299⟩
private theorem pr1704611 : Nat.Prime 1704611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv373,pv457]) (by decide +kernel)
def pv1704611 : PrimeValue := ⟨1704611, pr1704611⟩
private theorem pr1705103 : Nat.Prime 1705103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv127,pv137]) (by decide +kernel)
def pv1705103 : PrimeValue := ⟨1705103, pr1705103⟩
private theorem pr1705199 : Nat.Prime 1705199 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv77509]) (by decide +kernel)
def pv1705199 : PrimeValue := ⟨1705199, pr1705199⟩
private theorem pr1705271 : Nat.Prime 1705271 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv17,pv1433]) (by decide +kernel)
def pv1705271 : PrimeValue := ⟨1705271, pr1705271⟩
private theorem pr1705409 : Nat.Prime 1705409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26647]) (by decide +kernel)
def pv1705409 : PrimeValue := ⟨1705409, pr1705409⟩
private theorem pr1705481 : Nat.Prime 1705481 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv6091]) (by decide +kernel)
def pv1705481 : PrimeValue := ⟨1705481, pr1705481⟩
private theorem pr1705799 : Nat.Prime 1705799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv241,pv3539]) (by decide +kernel)
def pv1705799 : PrimeValue := ⟨1705799, pr1705799⟩
private theorem pr1705859 : Nat.Prime 1705859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv19,pv53]) (by decide +kernel)
def pv1705859 : PrimeValue := ⟨1705859, pr1705859⟩
private theorem pr1705871 : Nat.Prime 1705871 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv179,pv953]) (by decide +kernel)
def pv1705871 : PrimeValue := ⟨1705871, pr1705871⟩
private theorem pr1706063 : Nat.Prime 1706063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv853031]) (by decide +kernel)
def pv1706063 : PrimeValue := ⟨1706063, pr1706063⟩
private theorem pr1706249 : Nat.Prime 1706249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv213281]) (by decide +kernel)
def pv1706249 : PrimeValue := ⟨1706249, pr1706249⟩
private theorem pr1706291 : Nat.Prime 1706291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv10037]) (by decide +kernel)
def pv1706291 : PrimeValue := ⟨1706291, pr1706291⟩
private theorem pr1706363 : Nat.Prime 1706363 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv121883]) (by decide +kernel)
def pv1706363 : PrimeValue := ⟨1706363, pr1706363⟩
private theorem pr1707113 : Nat.Prime 1707113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv19,pv1021]) (by decide +kernel)
def pv1707113 : PrimeValue := ⟨1707113, pr1707113⟩
private theorem pr1707119 : Nat.Prime 1707119 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv121937]) (by decide +kernel)
def pv1707119 : PrimeValue := ⟨1707119, pr1707119⟩
private theorem pr1707353 : Nat.Prime 1707353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv457,pv467]) (by decide +kernel)
def pv1707353 : PrimeValue := ⟨1707353, pr1707353⟩
private theorem pr1707941 : Nat.Prime 1707941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv6569]) (by decide +kernel)
def pv1707941 : PrimeValue := ⟨1707941, pr1707941⟩
private theorem pr1707983 : Nat.Prime 1707983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv277,pv3083]) (by decide +kernel)
def pv1707983 : PrimeValue := ⟨1707983, pr1707983⟩
private theorem pr1708103 : Nat.Prime 1708103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv77641]) (by decide +kernel)
def pv1708103 : PrimeValue := ⟨1708103, pr1708103⟩
private theorem pr1708229 : Nat.Prime 1708229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv25121]) (by decide +kernel)
def pv1708229 : PrimeValue := ⟨1708229, pr1708229⟩
private theorem pr1708373 : Nat.Prime 1708373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv239,pv1787]) (by decide +kernel)
def pv1708373 : PrimeValue := ⟨1708373, pr1708373⟩
private theorem pr1708391 : Nat.Prime 1708391 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv29,pv43,pv137]) (by decide +kernel)
def pv1708391 : PrimeValue := ⟨1708391, pr1708391⟩
private theorem pr1708523 : Nat.Prime 1708523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv14479]) (by decide +kernel)
def pv1708523 : PrimeValue := ⟨1708523, pr1708523⟩
private theorem pr1708541 : Nat.Prime 1708541 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv85427]) (by decide +kernel)
def pv1708541 : PrimeValue := ⟨1708541, pr1708541⟩
private theorem pr1708571 : Nat.Prime 1708571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv170857]) (by decide +kernel)
def pv1708571 : PrimeValue := ⟨1708571, pr1708571⟩
private theorem pr1708649 : Nat.Prime 1708649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv4967]) (by decide +kernel)
def pv1708649 : PrimeValue := ⟨1708649, pr1708649⟩
private theorem pr1708769 : Nat.Prime 1708769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv67,pv797]) (by decide +kernel)
def pv1708769 : PrimeValue := ⟨1708769, pr1708769⟩
private theorem pr1708853 : Nat.Prime 1708853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv427213]) (by decide +kernel)
def pv1708853 : PrimeValue := ⟨1708853, pr1708853⟩
private theorem pr1708961 : Nat.Prime 1708961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv971]) (by decide +kernel)
def pv1708961 : PrimeValue := ⟨1708961, pr1708961⟩
private theorem pr1709033 : Nat.Prime 1709033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv16433]) (by decide +kernel)
def pv1709033 : PrimeValue := ⟨1709033, pr1709033⟩
private theorem pr1710011 : Nat.Prime 1710011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv271,pv631]) (by decide +kernel)
def pv1710011 : PrimeValue := ⟨1710011, pr1710011⟩
private theorem pr1710413 : Nat.Prime 1710413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv38873]) (by decide +kernel)
def pv1710413 : PrimeValue := ⟨1710413, pr1710413⟩
private theorem pr1710419 : Nat.Prime 1710419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv23,pv103]) (by decide +kernel)
def pv1710419 : PrimeValue := ⟨1710419, pr1710419⟩
private theorem pr1710539 : Nat.Prime 1710539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv855269]) (by decide +kernel)
def pv1710539 : PrimeValue := ⟨1710539, pr1710539⟩
private theorem pr1710833 : Nat.Prime 1710833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv4649]) (by decide +kernel)
def pv1710833 : PrimeValue := ⟨1710833, pr1710833⟩
private theorem pr1710953 : Nat.Prime 1710953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv6899]) (by decide +kernel)
def pv1710953 : PrimeValue := ⟨1710953, pr1710953⟩
private theorem pr1711049 : Nat.Prime 1711049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv213881]) (by decide +kernel)
def pv1711049 : PrimeValue := ⟨1711049, pr1711049⟩
private theorem pr1711103 : Nat.Prime 1711103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv37,pv1217]) (by decide +kernel)
def pv1711103 : PrimeValue := ⟨1711103, pr1711103⟩
private theorem pr1711511 : Nat.Prime 1711511 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv5,pv31,pv5521]) (by decide +kernel)
def pv1711511 : PrimeValue := ⟨1711511, pr1711511⟩
private theorem pr1711673 : Nat.Prime 1711673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv11261]) (by decide +kernel)
def pv1711673 : PrimeValue := ⟨1711673, pr1711673⟩
private theorem pr1711793 : Nat.Prime 1711793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv83,pv1289]) (by decide +kernel)
def pv1711793 : PrimeValue := ⟨1711793, pr1711793⟩
private theorem pr1711799 : Nat.Prime 1711799 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv11,pv17,pv23,pv199]) (by decide +kernel)
def pv1711799 : PrimeValue := ⟨1711799, pr1711799⟩
private theorem pr1711949 : Nat.Prime 1711949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv61141]) (by decide +kernel)
def pv1711949 : PrimeValue := ⟨1711949, pr1711949⟩
private theorem pr1712141 : Nat.Prime 1712141 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv85607]) (by decide +kernel)
def pv1712141 : PrimeValue := ⟨1712141, pr1712141⟩
private theorem pr1712153 : Nat.Prime 1712153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv101,pv163]) (by decide +kernel)
def pv1712153 : PrimeValue := ⟨1712153, pr1712153⟩
private theorem pr1712339 : Nat.Prime 1712339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv856169]) (by decide +kernel)
def pv1712339 : PrimeValue := ⟨1712339, pr1712339⟩
private theorem pr1712369 : Nat.Prime 1712369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv15289]) (by decide +kernel)
def pv1712369 : PrimeValue := ⟨1712369, pr1712369⟩
private theorem pr1712621 : Nat.Prime 1712621 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv13,pv941]) (by decide +kernel)
def pv1712621 : PrimeValue := ⟨1712621, pr1712621⟩
private theorem pr1712813 : Nat.Prime 1712813 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv31,pv727]) (by decide +kernel)
def pv1712813 : PrimeValue := ⟨1712813, pr1712813⟩
private theorem pr1713083 : Nat.Prime 1713083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv122363]) (by decide +kernel)
def pv1713083 : PrimeValue := ⟨1713083, pr1713083⟩
private theorem pr1713221 : Nat.Prime 1713221 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv85661]) (by decide +kernel)
def pv1713221 : PrimeValue := ⟨1713221, pr1713221⟩
private theorem pr1713671 : Nat.Prime 1713671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv24481]) (by decide +kernel)
def pv1713671 : PrimeValue := ⟨1713671, pr1713671⟩
private theorem pr1713683 : Nat.Prime 1713683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv856841]) (by decide +kernel)
def pv1713683 : PrimeValue := ⟨1713683, pr1713683⟩
private theorem pr1713689 : Nat.Prime 1713689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv214211]) (by decide +kernel)
def pv1713689 : PrimeValue := ⟨1713689, pr1713689⟩
private theorem pr1713791 : Nat.Prime 1713791 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv13183]) (by decide +kernel)
def pv1713791 : PrimeValue := ⟨1713791, pr1713791⟩
private theorem pr1714049 : Nat.Prime 1714049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1913]) (by decide +kernel)
def pv1714049 : PrimeValue := ⟨1714049, pr1714049⟩
private theorem pr1714133 : Nat.Prime 1714133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv2111]) (by decide +kernel)
def pv1714133 : PrimeValue := ⟨1714133, pr1714133⟩
private theorem pr1714211 : Nat.Prime 1714211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv41,pv113]) (by decide +kernel)
def pv1714211 : PrimeValue := ⟨1714211, pr1714211⟩
private theorem pr1714403 : Nat.Prime 1714403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv857201]) (by decide +kernel)
def pv1714403 : PrimeValue := ⟨1714403, pr1714403⟩
private theorem pr1714409 : Nat.Prime 1714409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv11279]) (by decide +kernel)
def pv1714409 : PrimeValue := ⟨1714409, pr1714409⟩
private theorem pr1715039 : Nat.Prime 1715039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv65963]) (by decide +kernel)
def pv1715039 : PrimeValue := ⟨1715039, pr1715039⟩
private theorem pr1715243 : Nat.Prime 1715243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv331,pv2591]) (by decide +kernel)
def pv1715243 : PrimeValue := ⟨1715243, pr1715243⟩
private theorem pr1715309 : Nat.Prime 1715309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv61261]) (by decide +kernel)
def pv1715309 : PrimeValue := ⟨1715309, pr1715309⟩
private theorem pr1715561 : Nat.Prime 1715561 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv11,pv557]) (by decide +kernel)
def pv1715561 : PrimeValue := ⟨1715561, pr1715561⟩
private theorem pr1715621 : Nat.Prime 1715621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv85781]) (by decide +kernel)
def pv1715621 : PrimeValue := ⟨1715621, pr1715621⟩
private theorem pr1715723 : Nat.Prime 1715723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv10859]) (by decide +kernel)
def pv1715723 : PrimeValue := ⟨1715723, pr1715723⟩
private theorem pr1715729 : Nat.Prime 1715729 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv15319]) (by decide +kernel)
def pv1715729 : PrimeValue := ⟨1715729, pr1715729⟩
private theorem pr1715783 : Nat.Prime 1715783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv18253]) (by decide +kernel)
def pv1715783 : PrimeValue := ⟨1715783, pr1715783⟩
private theorem pr1715849 : Nat.Prime 1715849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv214481]) (by decide +kernel)
def pv1715849 : PrimeValue := ⟨1715849, pr1715849⟩
private theorem pr1716521 : Nat.Prime 1716521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv3301]) (by decide +kernel)
def pv1716521 : PrimeValue := ⟨1716521, pr1716521⟩
private theorem pr1716653 : Nat.Prime 1716653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv37,pv1657]) (by decide +kernel)
def pv1716653 : PrimeValue := ⟨1716653, pr1716653⟩
private theorem pr1716791 : Nat.Prime 1716791 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv171679]) (by decide +kernel)
def pv1716791 : PrimeValue := ⟨1716791, pr1716791⟩
private theorem pr1716941 : Nat.Prime 1716941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv85847]) (by decide +kernel)
def pv1716941 : PrimeValue := ⟨1716941, pr1716941⟩
private theorem pr1716971 : Nat.Prime 1716971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv171697]) (by decide +kernel)
def pv1716971 : PrimeValue := ⟨1716971, pr1716971⟩
private theorem pr1717139 : Nat.Prime 1717139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv647,pv1327]) (by decide +kernel)
def pv1717139 : PrimeValue := ⟨1717139, pr1717139⟩
private theorem pr1717181 : Nat.Prime 1717181 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv3733]) (by decide +kernel)
def pv1717181 : PrimeValue := ⟨1717181, pr1717181⟩
private theorem pr1717379 : Nat.Prime 1717379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv5081]) (by decide +kernel)
def pv1717379 : PrimeValue := ⟨1717379, pr1717379⟩
private theorem pr1717451 : Nat.Prime 1717451 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv701]) (by decide +kernel)
def pv1717451 : PrimeValue := ⟨1717451, pr1717451⟩
private theorem pr1717673 : Nat.Prime 1717673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv131,pv149]) (by decide +kernel)
def pv1717673 : PrimeValue := ⟨1717673, pr1717673⟩
private theorem pr1718033 : Nat.Prime 1718033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv107377]) (by decide +kernel)
def pv1718033 : PrimeValue := ⟨1718033, pr1718033⟩
private theorem pr1718219 : Nat.Prime 1718219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv859109]) (by decide +kernel)
def pv1718219 : PrimeValue := ⟨1718219, pr1718219⟩
private theorem pr1718291 : Nat.Prime 1718291 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv24547]) (by decide +kernel)
def pv1718291 : PrimeValue := ⟨1718291, pr1718291⟩
private theorem pr1718441 : Nat.Prime 1718441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv42961]) (by decide +kernel)
def pv1718441 : PrimeValue := ⟨1718441, pr1718441⟩
private theorem pr1718669 : Nat.Prime 1718669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv61381]) (by decide +kernel)
def pv1718669 : PrimeValue := ⟨1718669, pr1718669⟩
private theorem pr1718693 : Nat.Prime 1718693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv429673]) (by decide +kernel)
def pv1718693 : PrimeValue := ⟨1718693, pr1718693⟩
private theorem pr1718771 : Nat.Prime 1718771 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv171877]) (by decide +kernel)
def pv1718771 : PrimeValue := ⟨1718771, pr1718771⟩
private theorem pr1719143 : Nat.Prime 1719143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv59,pv857]) (by decide +kernel)
def pv1719143 : PrimeValue := ⟨1719143, pr1719143⟩
private theorem pr1719209 : Nat.Prime 1719209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv311,pv691]) (by decide +kernel)
def pv1719209 : PrimeValue := ⟨1719209, pr1719209⟩
private theorem pr1719719 : Nat.Prime 1719719 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv11,pv13,pv859]) (by decide +kernel)
def pv1719719 : PrimeValue := ⟨1719719, pr1719719⟩
private theorem pr1720643 : Nat.Prime 1720643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv11173]) (by decide +kernel)
def pv1720643 : PrimeValue := ⟨1720643, pr1720643⟩
private theorem pr1720973 : Nat.Prime 1720973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv39113]) (by decide +kernel)
def pv1720973 : PrimeValue := ⟨1720973, pr1720973⟩
private theorem pr1721081 : Nat.Prime 1721081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv2531]) (by decide +kernel)
def pv1721081 : PrimeValue := ⟨1721081, pr1721081⟩
private theorem pr1721243 : Nat.Prime 1721243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv8521]) (by decide +kernel)
def pv1721243 : PrimeValue := ⟨1721243, pr1721243⟩
private theorem pr1721339 : Nat.Prime 1721339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv211,pv4079]) (by decide +kernel)
def pv1721339 : PrimeValue := ⟨1721339, pr1721339⟩
private theorem pr1721441 : Nat.Prime 1721441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv29,pv53]) (by decide +kernel)
def pv1721441 : PrimeValue := ⟨1721441, pr1721441⟩
private theorem pr1721543 : Nat.Prime 1721543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv61,pv103,pv137]) (by decide +kernel)
def pv1721543 : PrimeValue := ⟨1721543, pr1721543⟩
private theorem pr1721579 : Nat.Prime 1721579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv860789]) (by decide +kernel)
def pv1721579 : PrimeValue := ⟨1721579, pr1721579⟩
private theorem pr1722029 : Nat.Prime 1722029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv5591]) (by decide +kernel)
def pv1722029 : PrimeValue := ⟨1722029, pr1722029⟩
private theorem pr1722053 : Nat.Prime 1722053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv430513]) (by decide +kernel)
def pv1722053 : PrimeValue := ⟨1722053, pr1722053⟩
private theorem pr1722323 : Nat.Prime 1722323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv43,pv2861]) (by decide +kernel)
def pv1722323 : PrimeValue := ⟨1722323, pr1722323⟩
private theorem pr1722449 : Nat.Prime 1722449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13]) (by decide +kernel)
def pv1722449 : PrimeValue := ⟨1722449, pr1722449⟩
private theorem pr1722599 : Nat.Prime 1722599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv861299]) (by decide +kernel)
def pv1722599 : PrimeValue := ⟨1722599, pr1722599⟩
private theorem pr1722821 : Nat.Prime 1722821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv41,pv191]) (by decide +kernel)
def pv1722821 : PrimeValue := ⟨1722821, pr1722821⟩
private theorem pr1722893 : Nat.Prime 1722893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv430723]) (by decide +kernel)
def pv1722893 : PrimeValue := ⟨1722893, pr1722893⟩
private theorem pr1723721 : Nat.Prime 1723721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43093]) (by decide +kernel)
def pv1723721 : PrimeValue := ⟨1723721, pr1723721⟩
private theorem pr1723751 : Nat.Prime 1723751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv197]) (by decide +kernel)
def pv1723751 : PrimeValue := ⟨1723751, pr1723751⟩
private theorem pr1723973 : Nat.Prime 1723973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv13903]) (by decide +kernel)
def pv1723973 : PrimeValue := ⟨1723973, pr1723973⟩
private theorem pr1724351 : Nat.Prime 1724351 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv34487]) (by decide +kernel)
def pv1724351 : PrimeValue := ⟨1724351, pr1724351⟩
private theorem pr1724399 : Nat.Prime 1724399 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv13,pv29,pv2287]) (by decide +kernel)
def pv1724399 : PrimeValue := ⟨1724399, pr1724399⟩
private theorem pr1724741 : Nat.Prime 1724741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv83,pv1039]) (by decide +kernel)
def pv1724741 : PrimeValue := ⟨1724741, pr1724741⟩
private theorem pr1724861 : Nat.Prime 1724861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv86243]) (by decide +kernel)
def pv1724861 : PrimeValue := ⟨1724861, pr1724861⟩
private theorem pr1724969 : Nat.Prime 1724969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv30803]) (by decide +kernel)
def pv1724969 : PrimeValue := ⟨1724969, pr1724969⟩
private theorem pr1725089 : Nat.Prime 1725089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv37,pv47]) (by decide +kernel)
def pv1725089 : PrimeValue := ⟨1725089, pr1725089⟩
private theorem pr1725173 : Nat.Prime 1725173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv331,pv1303]) (by decide +kernel)
def pv1725173 : PrimeValue := ⟨1725173, pr1725173⟩
private theorem pr1725233 : Nat.Prime 1725233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv107827]) (by decide +kernel)
def pv1725233 : PrimeValue := ⟨1725233, pr1725233⟩
private theorem pr1725359 : Nat.Prime 1725359 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv479,pv1801]) (by decide +kernel)
def pv1725359 : PrimeValue := ⟨1725359, pr1725359⟩
private theorem pr1725539 : Nat.Prime 1725539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv862769]) (by decide +kernel)
def pv1725539 : PrimeValue := ⟨1725539, pr1725539⟩
private theorem pr1725929 : Nat.Prime 1725929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv443,pv487]) (by decide +kernel)
def pv1725929 : PrimeValue := ⟨1725929, pr1725929⟩
private theorem pr1726139 : Nat.Prime 1726139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv29761]) (by decide +kernel)
def pv1726139 : PrimeValue := ⟨1726139, pr1726139⟩
private theorem pr1726313 : Nat.Prime 1726313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv29,pv1063]) (by decide +kernel)
def pv1726313 : PrimeValue := ⟨1726313, pr1726313⟩
private theorem pr1726379 : Nat.Prime 1726379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv181,pv251]) (by decide +kernel)
def pv1726379 : PrimeValue := ⟨1726379, pr1726379⟩
private theorem pr1726811 : Nat.Prime 1726811 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv172681]) (by decide +kernel)
def pv1726811 : PrimeValue := ⟨1726811, pr1726811⟩
private theorem pr1726859 : Nat.Prime 1726859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv67,pv263]) (by decide +kernel)
def pv1726859 : PrimeValue := ⟨1726859, pr1726859⟩
private theorem pr1726883 : Nat.Prime 1726883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv773,pv1117]) (by decide +kernel)
def pv1726883 : PrimeValue := ⟨1726883, pr1726883⟩
private theorem pr1727321 : Nat.Prime 1727321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv31,pv199]) (by decide +kernel)
def pv1727321 : PrimeValue := ⟨1727321, pr1727321⟩
private theorem pr1727339 : Nat.Prime 1727339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv491,pv1759]) (by decide +kernel)
def pv1727339 : PrimeValue := ⟨1727339, pr1727339⟩
private theorem pr1727441 : Nat.Prime 1727441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv13,pv151]) (by decide +kernel)
def pv1727441 : PrimeValue := ⟨1727441, pr1727441⟩
private theorem pr1727483 : Nat.Prime 1727483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv53,pv379]) (by decide +kernel)
def pv1727483 : PrimeValue := ⟨1727483, pr1727483⟩
private theorem pr1727669 : Nat.Prime 1727669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv89,pv211]) (by decide +kernel)
def pv1727669 : PrimeValue := ⟨1727669, pr1727669⟩
private theorem pr1727969 : Nat.Prime 1727969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv4909]) (by decide +kernel)
def pv1727969 : PrimeValue := ⟨1727969, pr1727969⟩
private theorem pr1728581 : Nat.Prime 1728581 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv12347]) (by decide +kernel)
def pv1728581 : PrimeValue := ⟨1728581, pr1728581⟩
private theorem pr1728593 : Nat.Prime 1728593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv108037]) (by decide +kernel)
def pv1728593 : PrimeValue := ⟨1728593, pr1728593⟩
private theorem pr1728659 : Nat.Prime 1728659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv45491]) (by decide +kernel)
def pv1728659 : PrimeValue := ⟨1728659, pr1728659⟩
private theorem pr1728983 : Nat.Prime 1728983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv864491]) (by decide +kernel)
def pv1728983 : PrimeValue := ⟨1728983, pr1728983⟩
private theorem pr1729043 : Nat.Prime 1729043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv123503]) (by decide +kernel)
def pv1729043 : PrimeValue := ⟨1729043, pr1729043⟩
private theorem pr1729103 : Nat.Prime 1729103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv864551]) (by decide +kernel)
def pv1729103 : PrimeValue := ⟨1729103, pr1729103⟩
private theorem pr1729109 : Nat.Prime 1729109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv432277]) (by decide +kernel)
def pv1729109 : PrimeValue := ⟨1729109, pr1729109⟩
private theorem pr1729373 : Nat.Prime 1729373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv432343]) (by decide +kernel)
def pv1729373 : PrimeValue := ⟨1729373, pr1729373⟩
private theorem pr1729391 : Nat.Prime 1729391 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv53,pv251]) (by decide +kernel)
def pv1729391 : PrimeValue := ⟨1729391, pr1729391⟩
private theorem pr1729499 : Nat.Prime 1729499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv179,pv4831]) (by decide +kernel)
def pv1729499 : PrimeValue := ⟨1729499, pr1729499⟩
private theorem pr1729709 : Nat.Prime 1729709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv53,pv199]) (by decide +kernel)
def pv1729709 : PrimeValue := ⟨1729709, pr1729709⟩
private theorem pr1729943 : Nat.Prime 1729943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv79,pv10949]) (by decide +kernel)
def pv1729943 : PrimeValue := ⟨1729943, pr1729943⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
