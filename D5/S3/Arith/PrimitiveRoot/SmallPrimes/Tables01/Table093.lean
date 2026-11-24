/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table093
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table093.pv348827
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr348827 : Nat.Prime 348827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv174413]) (by decide +kernel)
def pv348827 : PrimeValue := ⟨348827, pr348827⟩
private theorem pr348833 : Nat.Prime 348833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv991]) (by decide +kernel)
def pv348833 : PrimeValue := ⟨348833, pr348833⟩
private theorem pr348851 : Nat.Prime 348851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv6977]) (by decide +kernel)
def pv348851 : PrimeValue := ⟨348851, pr348851⟩
private theorem pr348883 : Nat.Prime 348883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv58147]) (by decide +kernel)
def pv348883 : PrimeValue := ⟨348883, pr348883⟩
private theorem pr348889 : Nat.Prime 348889 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv14537]) (by decide +kernel)
def pv348889 : PrimeValue := ⟨348889, pr348889⟩
private theorem pr348911 : Nat.Prime 348911 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv23,pv37,pv41]) (by decide +kernel)
def pv348911 : PrimeValue := ⟨348911, pr348911⟩
private theorem pr348917 : Nat.Prime 348917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv4591]) (by decide +kernel)
def pv348917 : PrimeValue := ⟨348917, pr348917⟩
private theorem pr348937 : Nat.Prime 348937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv31,pv67]) (by decide +kernel)
def pv348937 : PrimeValue := ⟨348937, pr348937⟩
private theorem pr348989 : Nat.Prime 348989 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv2029]) (by decide +kernel)
def pv348989 : PrimeValue := ⟨348989, pr348989⟩
private theorem pr349121 : Nat.Prime 349121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1091]) (by decide +kernel)
def pv349121 : PrimeValue := ⟨349121, pr349121⟩
private theorem pr349183 : Nat.Prime 349183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv1021]) (by decide +kernel)
def pv349183 : PrimeValue := ⟨349183, pr349183⟩
private theorem pr349241 : Nat.Prime 349241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv8731]) (by decide +kernel)
def pv349241 : PrimeValue := ⟨349241, pr349241⟩
private theorem pr349291 : Nat.Prime 349291 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv3881]) (by decide +kernel)
def pv349291 : PrimeValue := ⟨349291, pr349291⟩
private theorem pr349331 : Nat.Prime 349331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv181,pv193]) (by decide +kernel)
def pv349331 : PrimeValue := ⟨349331, pr349331⟩
private theorem pr349369 : Nat.Prime 349369 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv14557]) (by decide +kernel)
def pv349369 : PrimeValue := ⟨349369, pr349369⟩
private theorem pr349423 : Nat.Prime 349423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv58237]) (by decide +kernel)
def pv349423 : PrimeValue := ⟨349423, pr349423⟩
private theorem pr349477 : Nat.Prime 349477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29123]) (by decide +kernel)
def pv349477 : PrimeValue := ⟨349477, pr349477⟩
private theorem pr349483 : Nat.Prime 349483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv53,pv157]) (by decide +kernel)
def pv349483 : PrimeValue := ⟨349483, pr349483⟩
private theorem pr349493 : Nat.Prime 349493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv47]) (by decide +kernel)
def pv349493 : PrimeValue := ⟨349493, pr349493⟩
private theorem pr349499 : Nat.Prime 349499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv174749]) (by decide +kernel)
def pv349499 : PrimeValue := ⟨349499, pr349499⟩
private theorem pr349529 : Nat.Prime 349529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43691]) (by decide +kernel)
def pv349529 : PrimeValue := ⟨349529, pr349529⟩
private theorem pr349567 : Nat.Prime 349567 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv29,pv41]) (by decide +kernel)
def pv349567 : PrimeValue := ⟨349567, pr349567⟩
private theorem pr349603 : Nat.Prime 349603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv5297]) (by decide +kernel)
def pv349603 : PrimeValue := ⟨349603, pr349603⟩
private theorem pr349667 : Nat.Prime 349667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv359,pv487]) (by decide +kernel)
def pv349667 : PrimeValue := ⟨349667, pr349667⟩
private theorem pr349697 : Nat.Prime 349697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv683]) (by decide +kernel)
def pv349697 : PrimeValue := ⟨349697, pr349697⟩
private theorem pr349753 : Nat.Prime 349753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv59]) (by decide +kernel)
def pv349753 : PrimeValue := ⟨349753, pr349753⟩
private theorem pr349759 : Nat.Prime 349759 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv127]) (by decide +kernel)
def pv349759 : PrimeValue := ⟨349759, pr349759⟩
private theorem pr349841 : Nat.Prime 349841 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv4373]) (by decide +kernel)
def pv349841 : PrimeValue := ⟨349841, pr349841⟩
private theorem pr349871 : Nat.Prime 349871 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv59,pv593]) (by decide +kernel)
def pv349871 : PrimeValue := ⟨349871, pr349871⟩
private theorem pr349913 : Nat.Prime 349913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv191,pv229]) (by decide +kernel)
def pv349913 : PrimeValue := ⟨349913, pr349913⟩
private theorem pr349927 : Nat.Prime 349927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv58321]) (by decide +kernel)
def pv349927 : PrimeValue := ⟨349927, pr349927⟩
private theorem pr349931 : Nat.Prime 349931 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv4999]) (by decide +kernel)
def pv349931 : PrimeValue := ⟨349931, pr349931⟩
private theorem pr349933 : Nat.Prime 349933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv241]) (by decide +kernel)
def pv349933 : PrimeValue := ⟨349933, pr349933⟩
private theorem pr349981 : Nat.Prime 349981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv307]) (by decide +kernel)
def pv349981 : PrimeValue := ⟨349981, pr349981⟩
private theorem pr350033 : Nat.Prime 350033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv131,pv167]) (by decide +kernel)
def pv350033 : PrimeValue := ⟨350033, pr350033⟩
private theorem pr350039 : Nat.Prime 350039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv13463]) (by decide +kernel)
def pv350039 : PrimeValue := ⟨350039, pr350039⟩
private theorem pr350087 : Nat.Prime 350087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv15913]) (by decide +kernel)
def pv350087 : PrimeValue := ⟨350087, pr350087⟩
private theorem pr350093 : Nat.Prime 350093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv87523]) (by decide +kernel)
def pv350093 : PrimeValue := ⟨350093, pr350093⟩
private theorem pr350111 : Nat.Prime 350111 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv157,pv223]) (by decide +kernel)
def pv350111 : PrimeValue := ⟨350111, pr350111⟩
private theorem pr350159 : Nat.Prime 350159 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv175079]) (by decide +kernel)
def pv350159 : PrimeValue := ⟨350159, pr350159⟩
private theorem pr350237 : Nat.Prime 350237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv87559]) (by decide +kernel)
def pv350237 : PrimeValue := ⟨350237, pr350237⟩
private theorem pr350249 : Nat.Prime 350249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43781]) (by decide +kernel)
def pv350249 : PrimeValue := ⟨350249, pr350249⟩
private theorem pr350347 : Nat.Prime 350347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv58391]) (by decide +kernel)
def pv350347 : PrimeValue := ⟨350347, pr350347⟩
private theorem pr350351 : Nat.Prime 350351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv13]) (by decide +kernel)
def pv350351 : PrimeValue := ⟨350351, pr350351⟩
private theorem pr350411 : Nat.Prime 350411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv67,pv523]) (by decide +kernel)
def pv350411 : PrimeValue := ⟨350411, pr350411⟩
private theorem pr350429 : Nat.Prime 350429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv23,pv293]) (by decide +kernel)
def pv350429 : PrimeValue := ⟨350429, pr350429⟩
private theorem pr350437 : Nat.Prime 350437 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv29,pv53]) (by decide +kernel)
def pv350437 : PrimeValue := ⟨350437, pr350437⟩
private theorem pr350453 : Nat.Prime 350453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv87613]) (by decide +kernel)
def pv350453 : PrimeValue := ⟨350453, pr350453⟩
private theorem pr350459 : Nat.Prime 350459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv175229]) (by decide +kernel)
def pv350459 : PrimeValue := ⟨350459, pr350459⟩
private theorem pr350587 : Nat.Prime 350587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19477]) (by decide +kernel)
def pv350587 : PrimeValue := ⟨350587, pr350587⟩
private theorem pr350699 : Nat.Prime 350699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv175349]) (by decide +kernel)
def pv350699 : PrimeValue := ⟨350699, pr350699⟩
private theorem pr350711 : Nat.Prime 350711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv2063]) (by decide +kernel)
def pv350711 : PrimeValue := ⟨350711, pr350711⟩
private theorem pr350737 : Nat.Prime 350737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7307]) (by decide +kernel)
def pv350737 : PrimeValue := ⟨350737, pr350737⟩
private theorem pr350747 : Nat.Prime 350747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv107,pv149]) (by decide +kernel)
def pv350747 : PrimeValue := ⟨350747, pr350747⟩
private theorem pr350771 : Nat.Prime 350771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv5011]) (by decide +kernel)
def pv350771 : PrimeValue := ⟨350771, pr350771⟩
private theorem pr350783 : Nat.Prime 350783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv175391]) (by decide +kernel)
def pv350783 : PrimeValue := ⟨350783, pr350783⟩
private theorem pr350789 : Nat.Prime 350789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv87697]) (by decide +kernel)
def pv350789 : PrimeValue := ⟨350789, pr350789⟩
private theorem pr350881 : Nat.Prime 350881 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv43]) (by decide +kernel)
def pv350881 : PrimeValue := ⟨350881, pr350881⟩
private theorem pr350891 : Nat.Prime 350891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv35089]) (by decide +kernel)
def pv350891 : PrimeValue := ⟨350891, pr350891⟩
private theorem pr350947 : Nat.Prime 350947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv97]) (by decide +kernel)
def pv350947 : PrimeValue := ⟨350947, pr350947⟩
private theorem pr350981 : Nat.Prime 350981 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv23,pv109]) (by decide +kernel)
def pv350981 : PrimeValue := ⟨350981, pr350981⟩
private theorem pr350983 : Nat.Prime 350983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv31,pv37]) (by decide +kernel)
def pv350983 : PrimeValue := ⟨350983, pr350983⟩
private theorem pr350989 : Nat.Prime 350989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv2659]) (by decide +kernel)
def pv350989 : PrimeValue := ⟨350989, pr350989⟩
private theorem pr351041 : Nat.Prime 351041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1097]) (by decide +kernel)
def pv351041 : PrimeValue := ⟨351041, pr351041⟩
private theorem pr351077 : Nat.Prime 351077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv79,pv101]) (by decide +kernel)
def pv351077 : PrimeValue := ⟨351077, pr351077⟩
private theorem pr351157 : Nat.Prime 351157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2251]) (by decide +kernel)
def pv351157 : PrimeValue := ⟨351157, pr351157⟩
private theorem pr351217 : Nat.Prime 351217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv271]) (by decide +kernel)
def pv351217 : PrimeValue := ⟨351217, pr351217⟩
private theorem pr351257 : Nat.Prime 351257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv83]) (by decide +kernel)
def pv351257 : PrimeValue := ⟨351257, pr351257⟩
private theorem pr351269 : Nat.Prime 351269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv137,pv641]) (by decide +kernel)
def pv351269 : PrimeValue := ⟨351269, pr351269⟩
private theorem pr351287 : Nat.Prime 351287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv59,pv229]) (by decide +kernel)
def pv351287 : PrimeValue := ⟨351287, pr351287⟩
private theorem pr351293 : Nat.Prime 351293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv2833]) (by decide +kernel)
def pv351293 : PrimeValue := ⟨351293, pr351293⟩
private theorem pr351311 : Nat.Prime 351311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv43]) (by decide +kernel)
def pv351311 : PrimeValue := ⟨351311, pr351311⟩
private theorem pr351341 : Nat.Prime 351341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv1597]) (by decide +kernel)
def pv351341 : PrimeValue := ⟨351341, pr351341⟩
private theorem pr351343 : Nat.Prime 351343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv131,pv149]) (by decide +kernel)
def pv351343 : PrimeValue := ⟨351343, pr351343⟩
private theorem pr351383 : Nat.Prime 351383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv175691]) (by decide +kernel)
def pv351383 : PrimeValue := ⟨351383, pr351383⟩
private theorem pr351391 : Nat.Prime 351391 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv17,pv53]) (by decide +kernel)
def pv351391 : PrimeValue := ⟨351391, pr351391⟩
private theorem pr351397 : Nat.Prime 351397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv227]) (by decide +kernel)
def pv351397 : PrimeValue := ⟨351397, pr351397⟩
private theorem pr351401 : Nat.Prime 351401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv251]) (by decide +kernel)
def pv351401 : PrimeValue := ⟨351401, pr351401⟩
private theorem pr351413 : Nat.Prime 351413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv87853]) (by decide +kernel)
def pv351413 : PrimeValue := ⟨351413, pr351413⟩
private theorem pr351427 : Nat.Prime 351427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv1583]) (by decide +kernel)
def pv351427 : PrimeValue := ⟨351427, pr351427⟩
private theorem pr351479 : Nat.Prime 351479 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv31,pv5669]) (by decide +kernel)
def pv351479 : PrimeValue := ⟨351479, pr351479⟩
private theorem pr351497 : Nat.Prime 351497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53,pv829]) (by decide +kernel)
def pv351497 : PrimeValue := ⟨351497, pr351497⟩
private theorem pr351517 : Nat.Prime 351517 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv2663]) (by decide +kernel)
def pv351517 : PrimeValue := ⟨351517, pr351517⟩
private theorem pr351563 : Nat.Prime 351563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv175781]) (by decide +kernel)
def pv351563 : PrimeValue := ⟨351563, pr351563⟩
private theorem pr351587 : Nat.Prime 351587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv367,pv479]) (by decide +kernel)
def pv351587 : PrimeValue := ⟨351587, pr351587⟩
private theorem pr351731 : Nat.Prime 351731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv2069]) (by decide +kernel)
def pv351731 : PrimeValue := ⟨351731, pr351731⟩
private theorem pr351733 : Nat.Prime 351733 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29311]) (by decide +kernel)
def pv351733 : PrimeValue := ⟨351733, pr351733⟩
private theorem pr351749 : Nat.Prime 351749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv1871]) (by decide +kernel)
def pv351749 : PrimeValue := ⟨351749, pr351749⟩
private theorem pr351763 : Nat.Prime 351763 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv2549]) (by decide +kernel)
def pv351763 : PrimeValue := ⟨351763, pr351763⟩
private theorem pr351779 : Nat.Prime 351779 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv25127]) (by decide +kernel)
def pv351779 : PrimeValue := ⟨351779, pr351779⟩
private theorem pr351829 : Nat.Prime 351829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv337]) (by decide +kernel)
def pv351829 : PrimeValue := ⟨351829, pr351829⟩
private theorem pr351847 : Nat.Prime 351847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1777]) (by decide +kernel)
def pv351847 : PrimeValue := ⟨351847, pr351847⟩
private theorem pr351851 : Nat.Prime 351851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv227]) (by decide +kernel)
def pv351851 : PrimeValue := ⟨351851, pr351851⟩
private theorem pr351971 : Nat.Prime 351971 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv61,pv577]) (by decide +kernel)
def pv351971 : PrimeValue := ⟨351971, pr351971⟩
private theorem pr352007 : Nat.Prime 352007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv73,pv2411]) (by decide +kernel)
def pv352007 : PrimeValue := ⟨352007, pr352007⟩
private theorem pr352021 : Nat.Prime 352021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv5867]) (by decide +kernel)
def pv352021 : PrimeValue := ⟨352021, pr352021⟩
private theorem pr352043 : Nat.Prime 352043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv176021]) (by decide +kernel)
def pv352043 : PrimeValue := ⟨352043, pr352043⟩
private theorem pr352097 : Nat.Prime 352097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11003]) (by decide +kernel)
def pv352097 : PrimeValue := ⟨352097, pr352097⟩
private theorem pr352109 : Nat.Prime 352109 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv19,pv41,pv113]) (by decide +kernel)
def pv352109 : PrimeValue := ⟨352109, pr352109⟩
private theorem pr352123 : Nat.Prime 352123 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv58687]) (by decide +kernel)
def pv352123 : PrimeValue := ⟨352123, pr352123⟩
private theorem pr352181 : Nat.Prime 352181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17609]) (by decide +kernel)
def pv352181 : PrimeValue := ⟨352181, pr352181⟩
private theorem pr352193 : Nat.Prime 352193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5503]) (by decide +kernel)
def pv352193 : PrimeValue := ⟨352193, pr352193⟩
private theorem pr352201 : Nat.Prime 352201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv587]) (by decide +kernel)
def pv352201 : PrimeValue := ⟨352201, pr352201⟩
private theorem pr352267 : Nat.Prime 352267 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv58711]) (by decide +kernel)
def pv352267 : PrimeValue := ⟨352267, pr352267⟩
private theorem pr352301 : Nat.Prime 352301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv271]) (by decide +kernel)
def pv352301 : PrimeValue := ⟨352301, pr352301⟩
private theorem pr352309 : Nat.Prime 352309 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv11,pv17,pv157]) (by decide +kernel)
def pv352309 : PrimeValue := ⟨352309, pr352309⟩
private theorem pr352403 : Nat.Prime 352403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv176201]) (by decide +kernel)
def pv352403 : PrimeValue := ⟨352403, pr352403⟩
private theorem pr352409 : Nat.Prime 352409 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv29,pv31]) (by decide +kernel)
def pv352409 : PrimeValue := ⟨352409, pr352409⟩
private theorem pr352411 : Nat.Prime 352411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv691]) (by decide +kernel)
def pv352411 : PrimeValue := ⟨352411, pr352411⟩
private theorem pr352481 : Nat.Prime 352481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv2203]) (by decide +kernel)
def pv352481 : PrimeValue := ⟨352481, pr352481⟩
private theorem pr352489 : Nat.Prime 352489 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv19,pv773]) (by decide +kernel)
def pv352489 : PrimeValue := ⟨352489, pr352489⟩
private theorem pr352511 : Nat.Prime 352511 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv35251]) (by decide +kernel)
def pv352511 : PrimeValue := ⟨352511, pr352511⟩
private theorem pr352549 : Nat.Prime 352549 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv1399]) (by decide +kernel)
def pv352549 : PrimeValue := ⟨352549, pr352549⟩
private theorem pr352601 : Nat.Prime 352601 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv41,pv43]) (by decide +kernel)
def pv352601 : PrimeValue := ⟨352601, pr352601⟩
private theorem pr352637 : Nat.Prime 352637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv3833]) (by decide +kernel)
def pv352637 : PrimeValue := ⟨352637, pr352637⟩
private theorem pr352661 : Nat.Prime 352661 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv7,pv11,pv229]) (by decide +kernel)
def pv352661 : PrimeValue := ⟨352661, pr352661⟩
private theorem pr352739 : Nat.Prime 352739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv176369]) (by decide +kernel)
def pv352739 : PrimeValue := ⟨352739, pr352739⟩
private theorem pr352741 : Nat.Prime 352741 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv5879]) (by decide +kernel)
def pv352741 : PrimeValue := ⟨352741, pr352741⟩
private theorem pr352753 : Nat.Prime 352753 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7349]) (by decide +kernel)
def pv352753 : PrimeValue := ⟨352753, pr352753⟩
private theorem pr352771 : Nat.Prime 352771 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv1069]) (by decide +kernel)
def pv352771 : PrimeValue := ⟨352771, pr352771⟩
private theorem pr352817 : Nat.Prime 352817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv22051]) (by decide +kernel)
def pv352817 : PrimeValue := ⟨352817, pr352817⟩
private theorem pr352831 : Nat.Prime 352831 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv19,pv619]) (by decide +kernel)
def pv352831 : PrimeValue := ⟨352831, pr352831⟩
private theorem pr352853 : Nat.Prime 352853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv5189]) (by decide +kernel)
def pv352853 : PrimeValue := ⟨352853, pr352853⟩
private theorem pr352909 : Nat.Prime 352909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9803]) (by decide +kernel)
def pv352909 : PrimeValue := ⟨352909, pr352909⟩
private theorem pr352931 : Nat.Prime 352931 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv29,pv1217]) (by decide +kernel)
def pv352931 : PrimeValue := ⟨352931, pr352931⟩
private theorem pr352949 : Nat.Prime 352949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv88237]) (by decide +kernel)
def pv352949 : PrimeValue := ⟨352949, pr352949⟩
private theorem pr353047 : Nat.Prime 353047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv2029]) (by decide +kernel)
def pv353047 : PrimeValue := ⟨353047, pr353047⟩
private theorem pr353057 : Nat.Prime 353057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv17,pv59]) (by decide +kernel)
def pv353057 : PrimeValue := ⟨353057, pr353057⟩
private theorem pr353069 : Nat.Prime 353069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv1447]) (by decide +kernel)
def pv353069 : PrimeValue := ⟨353069, pr353069⟩
private theorem pr353081 : Nat.Prime 353081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv97]) (by decide +kernel)
def pv353081 : PrimeValue := ⟨353081, pr353081⟩
private theorem pr353099 : Nat.Prime 353099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv176549]) (by decide +kernel)
def pv353099 : PrimeValue := ⟨353099, pr353099⟩
private theorem pr353117 : Nat.Prime 353117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv2053]) (by decide +kernel)
def pv353117 : PrimeValue := ⟨353117, pr353117⟩
private theorem pr353149 : Nat.Prime 353149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29429]) (by decide +kernel)
def pv353149 : PrimeValue := ⟨353149, pr353149⟩
private theorem pr353173 : Nat.Prime 353173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1549]) (by decide +kernel)
def pv353173 : PrimeValue := ⟨353173, pr353173⟩
private theorem pr353201 : Nat.Prime 353201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv883]) (by decide +kernel)
def pv353201 : PrimeValue := ⟨353201, pr353201⟩
private theorem pr353203 : Nat.Prime 353203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv43]) (by decide +kernel)
def pv353203 : PrimeValue := ⟨353203, pr353203⟩
private theorem pr353293 : Nat.Prime 353293 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv59,pv499]) (by decide +kernel)
def pv353293 : PrimeValue := ⟨353293, pr353293⟩
private theorem pr353443 : Nat.Prime 353443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv58907]) (by decide +kernel)
def pv353443 : PrimeValue := ⟨353443, pr353443⟩
private theorem pr353453 : Nat.Prime 353453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv29,pv277]) (by decide +kernel)
def pv353453 : PrimeValue := ⟨353453, pr353453⟩
private theorem pr353459 : Nat.Prime 353459 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv25247]) (by decide +kernel)
def pv353459 : PrimeValue := ⟨353459, pr353459⟩
private theorem pr353471 : Nat.Prime 353471 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv2719]) (by decide +kernel)
def pv353471 : PrimeValue := ⟨353471, pr353471⟩
private theorem pr353531 : Nat.Prime 353531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv35353]) (by decide +kernel)
def pv353531 : PrimeValue := ⟨353531, pr353531⟩
private theorem pr353567 : Nat.Prime 353567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv10399]) (by decide +kernel)
def pv353567 : PrimeValue := ⟨353567, pr353567⟩
private theorem pr353603 : Nat.Prime 353603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv7687]) (by decide +kernel)
def pv353603 : PrimeValue := ⟨353603, pr353603⟩
private theorem pr353611 : Nat.Prime 353611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3929]) (by decide +kernel)
def pv353611 : PrimeValue := ⟨353611, pr353611⟩
private theorem pr353653 : Nat.Prime 353653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2267]) (by decide +kernel)
def pv353653 : PrimeValue := ⟨353653, pr353653⟩
private theorem pr353657 : Nat.Prime 353657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv44207]) (by decide +kernel)
def pv353657 : PrimeValue := ⟨353657, pr353657⟩
private theorem pr353677 : Nat.Prime 353677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29473]) (by decide +kernel)
def pv353677 : PrimeValue := ⟨353677, pr353677⟩
private theorem pr353687 : Nat.Prime 353687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv89,pv1987]) (by decide +kernel)
def pv353687 : PrimeValue := ⟨353687, pr353687⟩
private theorem pr353747 : Nat.Prime 353747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv2131]) (by decide +kernel)
def pv353747 : PrimeValue := ⟨353747, pr353747⟩
private theorem pr353767 : Nat.Prime 353767 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv8423]) (by decide +kernel)
def pv353767 : PrimeValue := ⟨353767, pr353767⟩
private theorem pr353807 : Nat.Prime 353807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv176903]) (by decide +kernel)
def pv353807 : PrimeValue := ⟨353807, pr353807⟩
private theorem pr353813 : Nat.Prime 353813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv197,pv449]) (by decide +kernel)
def pv353813 : PrimeValue := ⟨353813, pr353813⟩
private theorem pr353867 : Nat.Prime 353867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv176933]) (by decide +kernel)
def pv353867 : PrimeValue := ⟨353867, pr353867⟩
private theorem pr353897 : Nat.Prime 353897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv1427]) (by decide +kernel)
def pv353897 : PrimeValue := ⟨353897, pr353897⟩
private theorem pr354001 : Nat.Prime 354001 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv59]) (by decide +kernel)
def pv354001 : PrimeValue := ⟨354001, pr354001⟩
private theorem pr354007 : Nat.Prime 354007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71,pv277]) (by decide +kernel)
def pv354007 : PrimeValue := ⟨354007, pr354007⟩
private theorem pr354023 : Nat.Prime 354023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv177011]) (by decide +kernel)
def pv354023 : PrimeValue := ⟨354023, pr354023⟩
private theorem pr354037 : Nat.Prime 354037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv163,pv181]) (by decide +kernel)
def pv354037 : PrimeValue := ⟨354037, pr354037⟩
private theorem pr354041 : Nat.Prime 354041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv53,pv167]) (by decide +kernel)
def pv354041 : PrimeValue := ⟨354041, pr354041⟩
private theorem pr354073 : Nat.Prime 354073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv14753]) (by decide +kernel)
def pv354073 : PrimeValue := ⟨354073, pr354073⟩
private theorem pr354143 : Nat.Prime 354143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv113,pv1567]) (by decide +kernel)
def pv354143 : PrimeValue := ⟨354143, pr354143⟩
private theorem pr354181 : Nat.Prime 354181 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv5903]) (by decide +kernel)
def pv354181 : PrimeValue := ⟨354181, pr354181⟩
private theorem pr354257 : Nat.Prime 354257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv3163]) (by decide +kernel)
def pv354257 : PrimeValue := ⟨354257, pr354257⟩
private theorem pr354313 : Nat.Prime 354313 :=
  checkPrime_prime (q := pv53) (ls := [pv2,pv3,pv7,pv19,pv37]) (by decide +kernel)
def pv354313 : PrimeValue := ⟨354313, pr354313⟩
private theorem pr354323 : Nat.Prime 354323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv41,pv149]) (by decide +kernel)
def pv354323 : PrimeValue := ⟨354323, pr354323⟩
private theorem pr354337 : Nat.Prime 354337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3691]) (by decide +kernel)
def pv354337 : PrimeValue := ⟨354337, pr354337⟩
private theorem pr354371 : Nat.Prime 354371 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv35437]) (by decide +kernel)
def pv354371 : PrimeValue := ⟨354371, pr354371⟩
private theorem pr354401 : Nat.Prime 354401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv443]) (by decide +kernel)
def pv354401 : PrimeValue := ⟨354401, pr354401⟩
private theorem pr354443 : Nat.Prime 354443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv16111]) (by decide +kernel)
def pv354443 : PrimeValue := ⟨354443, pr354443⟩
private theorem pr354461 : Nat.Prime 354461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv479]) (by decide +kernel)
def pv354461 : PrimeValue := ⟨354461, pr354461⟩
private theorem pr354463 : Nat.Prime 354463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59077]) (by decide +kernel)
def pv354463 : PrimeValue := ⟨354463, pr354463⟩
private theorem pr354479 : Nat.Prime 354479 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv177239]) (by decide +kernel)
def pv354479 : PrimeValue := ⟨354479, pr354479⟩
private theorem pr354539 : Nat.Prime 354539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv177269]) (by decide +kernel)
def pv354539 : PrimeValue := ⟨354539, pr354539⟩
private theorem pr354553 : Nat.Prime 354553 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv17,pv79]) (by decide +kernel)
def pv354553 : PrimeValue := ⟨354553, pr354553⟩
private theorem pr354647 : Nat.Prime 354647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv177323]) (by decide +kernel)
def pv354647 : PrimeValue := ⟨354647, pr354647⟩
private theorem pr354661 : Nat.Prime 354661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv257]) (by decide +kernel)
def pv354661 : PrimeValue := ⟨354661, pr354661⟩
private theorem pr354701 : Nat.Prime 354701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3547]) (by decide +kernel)
def pv354701 : PrimeValue := ⟨354701, pr354701⟩
private theorem pr354791 : Nat.Prime 354791 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv17,pv2087]) (by decide +kernel)
def pv354791 : PrimeValue := ⟨354791, pr354791⟩
private theorem pr354829 : Nat.Prime 354829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29569]) (by decide +kernel)
def pv354829 : PrimeValue := ⟨354829, pr354829⟩
private theorem pr354839 : Nat.Prime 354839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv127]) (by decide +kernel)
def pv354839 : PrimeValue := ⟨354839, pr354839⟩
private theorem pr354847 : Nat.Prime 354847 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59141]) (by decide +kernel)
def pv354847 : PrimeValue := ⟨354847, pr354847⟩
private theorem pr354869 : Nat.Prime 354869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv1123]) (by decide +kernel)
def pv354869 : PrimeValue := ⟨354869, pr354869⟩
private theorem pr354877 : Nat.Prime 354877 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv29573]) (by decide +kernel)
def pv354877 : PrimeValue := ⟨354877, pr354877⟩
private theorem pr354881 : Nat.Prime 354881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1109]) (by decide +kernel)
def pv354881 : PrimeValue := ⟨354881, pr354881⟩
private theorem pr354883 : Nat.Prime 354883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv283]) (by decide +kernel)
def pv354883 : PrimeValue := ⟨354883, pr354883⟩
private theorem pr354911 : Nat.Prime 354911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv35491]) (by decide +kernel)
def pv354911 : PrimeValue := ⟨354911, pr354911⟩
private theorem pr354953 : Nat.Prime 354953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv3413]) (by decide +kernel)
def pv354953 : PrimeValue := ⟨354953, pr354953⟩
private theorem pr354971 : Nat.Prime 354971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv461]) (by decide +kernel)
def pv354971 : PrimeValue := ⟨354971, pr354971⟩
private theorem pr354983 : Nat.Prime 354983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv7717]) (by decide +kernel)
def pv354983 : PrimeValue := ⟨354983, pr354983⟩
private theorem pr354997 : Nat.Prime 354997 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19,pv173]) (by decide +kernel)
def pv354997 : PrimeValue := ⟨354997, pr354997⟩
private theorem pr355009 : Nat.Prime 355009 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv355009 : PrimeValue := ⟨355009, pr355009⟩
private theorem pr355027 : Nat.Prime 355027 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv79,pv107]) (by decide +kernel)
def pv355027 : PrimeValue := ⟨355027, pr355027⟩
private theorem pr355031 : Nat.Prime 355031 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv13,pv2731]) (by decide +kernel)
def pv355031 : PrimeValue := ⟨355031, pr355031⟩
private theorem pr355049 : Nat.Prime 355049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv44381]) (by decide +kernel)
def pv355049 : PrimeValue := ⟨355049, pr355049⟩
private theorem pr355057 : Nat.Prime 355057 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv569]) (by decide +kernel)
def pv355057 : PrimeValue := ⟨355057, pr355057⟩
private theorem pr355063 : Nat.Prime 355063 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv59]) (by decide +kernel)
def pv355063 : PrimeValue := ⟨355063, pr355063⟩
private theorem pr355073 : Nat.Prime 355073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv73]) (by decide +kernel)
def pv355073 : PrimeValue := ⟨355073, pr355073⟩
private theorem pr355087 : Nat.Prime 355087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19727]) (by decide +kernel)
def pv355087 : PrimeValue := ⟨355087, pr355087⟩
private theorem pr355093 : Nat.Prime 355093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv127,pv233]) (by decide +kernel)
def pv355093 : PrimeValue := ⟨355093, pr355093⟩
private theorem pr355109 : Nat.Prime 355109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv6829]) (by decide +kernel)
def pv355109 : PrimeValue := ⟨355109, pr355109⟩
private theorem pr355211 : Nat.Prime 355211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv35521]) (by decide +kernel)
def pv355211 : PrimeValue := ⟨355211, pr355211⟩
private theorem pr355261 : Nat.Prime 355261 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv31,pv191]) (by decide +kernel)
def pv355261 : PrimeValue := ⟨355261, pr355261⟩
private theorem pr355331 : Nat.Prime 355331 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv35533]) (by decide +kernel)
def pv355331 : PrimeValue := ⟨355331, pr355331⟩
private theorem pr355417 : Nat.Prime 355417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv59,pv251]) (by decide +kernel)
def pv355417 : PrimeValue := ⟨355417, pr355417⟩
private theorem pr355427 : Nat.Prime 355427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv2503]) (by decide +kernel)
def pv355427 : PrimeValue := ⟨355427, pr355427⟩
private theorem pr355483 : Nat.Prime 355483 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv227]) (by decide +kernel)
def pv355483 : PrimeValue := ⟨355483, pr355483⟩
private theorem pr355499 : Nat.Prime 355499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv113]) (by decide +kernel)
def pv355499 : PrimeValue := ⟨355499, pr355499⟩
private theorem pr355541 : Nat.Prime 355541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv613]) (by decide +kernel)
def pv355541 : PrimeValue := ⟨355541, pr355541⟩
private theorem pr355571 : Nat.Prime 355571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv37]) (by decide +kernel)
def pv355571 : PrimeValue := ⟨355571, pr355571⟩
private theorem pr355573 : Nat.Prime 355573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv83]) (by decide +kernel)
def pv355573 : PrimeValue := ⟨355573, pr355573⟩
private theorem pr355609 : Nat.Prime 355609 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv11,pv449]) (by decide +kernel)
def pv355609 : PrimeValue := ⟨355609, pr355609⟩
private theorem pr355633 : Nat.Prime 355633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv239]) (by decide +kernel)
def pv355633 : PrimeValue := ⟨355633, pr355633⟩
private theorem pr355643 : Nat.Prime 355643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv191]) (by decide +kernel)
def pv355643 : PrimeValue := ⟨355643, pr355643⟩
private theorem pr355669 : Nat.Prime 355669 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv107,pv277]) (by decide +kernel)
def pv355669 : PrimeValue := ⟨355669, pr355669⟩
private theorem pr355679 : Nat.Prime 355679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv177839]) (by decide +kernel)
def pv355679 : PrimeValue := ⟨355679, pr355679⟩
private theorem pr355697 : Nat.Prime 355697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv43,pv47]) (by decide +kernel)
def pv355697 : PrimeValue := ⟨355697, pr355697⟩
private theorem pr355717 : Nat.Prime 355717 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv41,pv241]) (by decide +kernel)
def pv355717 : PrimeValue := ⟨355717, pr355717⟩
private theorem pr355723 : Nat.Prime 355723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv101,pv587]) (by decide +kernel)
def pv355723 : PrimeValue := ⟨355723, pr355723⟩
private theorem pr355753 : Nat.Prime 355753 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv355753 : PrimeValue := ⟨355753, pr355753⟩
private theorem pr355763 : Nat.Prime 355763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv103,pv157]) (by decide +kernel)
def pv355763 : PrimeValue := ⟨355763, pr355763⟩
private theorem pr355819 : Nat.Prime 355819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv1913]) (by decide +kernel)
def pv355819 : PrimeValue := ⟨355819, pr355819⟩
private theorem pr355847 : Nat.Prime 355847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv181,pv983]) (by decide +kernel)
def pv355847 : PrimeValue := ⟨355847, pr355847⟩
private theorem pr355853 : Nat.Prime 355853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv71,pv179]) (by decide +kernel)
def pv355853 : PrimeValue := ⟨355853, pr355853⟩
private theorem pr355867 : Nat.Prime 355867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv37,pv229]) (by decide +kernel)
def pv355867 : PrimeValue := ⟨355867, pr355867⟩
private theorem pr355891 : Nat.Prime 355891 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11863]) (by decide +kernel)
def pv355891 : PrimeValue := ⟨355891, pr355891⟩
private theorem pr355909 : Nat.Prime 355909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv223]) (by decide +kernel)
def pv355909 : PrimeValue := ⟨355909, pr355909⟩
private theorem pr355913 : Nat.Prime 355913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv2617]) (by decide +kernel)
def pv355913 : PrimeValue := ⟨355913, pr355913⟩
private theorem pr355937 : Nat.Prime 355937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv227]) (by decide +kernel)
def pv355937 : PrimeValue := ⟨355937, pr355937⟩
private theorem pr355939 : Nat.Prime 355939 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv5393]) (by decide +kernel)
def pv355939 : PrimeValue := ⟨355939, pr355939⟩
private theorem pr356023 : Nat.Prime 356023 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19,pv347]) (by decide +kernel)
def pv356023 : PrimeValue := ⟨356023, pr356023⟩
private theorem pr356093 : Nat.Prime 356093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv8093]) (by decide +kernel)
def pv356093 : PrimeValue := ⟨356093, pr356093⟩
private theorem pr356141 : Nat.Prime 356141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17807]) (by decide +kernel)
def pv356141 : PrimeValue := ⟨356141, pr356141⟩
private theorem pr356143 : Nat.Prime 356143 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59357]) (by decide +kernel)
def pv356143 : PrimeValue := ⟨356143, pr356143⟩
private theorem pr356197 : Nat.Prime 356197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29683]) (by decide +kernel)
def pv356197 : PrimeValue := ⟨356197, pr356197⟩
private theorem pr356327 : Nat.Prime 356327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv9377]) (by decide +kernel)
def pv356327 : PrimeValue := ⟨356327, pr356327⟩
private theorem pr356333 : Nat.Prime 356333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89083]) (by decide +kernel)
def pv356333 : PrimeValue := ⟨356333, pr356333⟩
private theorem pr356387 : Nat.Prime 356387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv2441]) (by decide +kernel)
def pv356387 : PrimeValue := ⟨356387, pr356387⟩
private theorem pr356441 : Nat.Prime 356441 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv19,pv67]) (by decide +kernel)
def pv356441 : PrimeValue := ⟨356441, pr356441⟩
private theorem pr356449 : Nat.Prime 356449 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv47,pv79]) (by decide +kernel)
def pv356449 : PrimeValue := ⟨356449, pr356449⟩
private theorem pr356467 : Nat.Prime 356467 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv491]) (by decide +kernel)
def pv356467 : PrimeValue := ⟨356467, pr356467⟩
private theorem pr356479 : Nat.Prime 356479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv53,pv59]) (by decide +kernel)
def pv356479 : PrimeValue := ⟨356479, pr356479⟩
private theorem pr356533 : Nat.Prime 356533 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11,pv37,pv73]) (by decide +kernel)
def pv356533 : PrimeValue := ⟨356533, pr356533⟩
private theorem pr356561 : Nat.Prime 356561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4457]) (by decide +kernel)
def pv356561 : PrimeValue := ⟨356561, pr356561⟩
private theorem pr356579 : Nat.Prime 356579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv178289]) (by decide +kernel)
def pv356579 : PrimeValue := ⟨356579, pr356579⟩
private theorem pr356591 : Nat.Prime 356591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv211]) (by decide +kernel)
def pv356591 : PrimeValue := ⟨356591, pr356591⟩
private theorem pr356621 : Nat.Prime 356621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv1621]) (by decide +kernel)
def pv356621 : PrimeValue := ⟨356621, pr356621⟩
private theorem pr356663 : Nat.Prime 356663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv151,pv1181]) (by decide +kernel)
def pv356663 : PrimeValue := ⟨356663, pr356663⟩
private theorem pr356701 : Nat.Prime 356701 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv29,pv41]) (by decide +kernel)
def pv356701 : PrimeValue := ⟨356701, pr356701⟩
private theorem pr356731 : Nat.Prime 356731 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv23,pv47]) (by decide +kernel)
def pv356731 : PrimeValue := ⟨356731, pr356731⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
