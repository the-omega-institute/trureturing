/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table093
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table093.pv348827
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr348827 : PrimeCertificate 348827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv174413]) (by decide +kernel)
def pv348827 : PrimeValue := ⟨348827, pr348827⟩
private theorem pr348833 : PrimeCertificate 348833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv991]) (by decide +kernel)
def pv348833 : PrimeValue := ⟨348833, pr348833⟩
private theorem pr348851 : PrimeCertificate 348851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6977]) (by decide +kernel)
def pv348851 : PrimeValue := ⟨348851, pr348851⟩
private theorem pr348883 : PrimeCertificate 348883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv58147]) (by decide +kernel)
def pv348883 : PrimeValue := ⟨348883, pr348883⟩
private theorem pr348889 : PrimeCertificate 348889 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv14537]) (by decide +kernel)
def pv348889 : PrimeValue := ⟨348889, pr348889⟩
private theorem pr348911 : PrimeCertificate 348911 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv23,pv37,pv41]) (by decide +kernel)
def pv348911 : PrimeValue := ⟨348911, pr348911⟩
private theorem pr348917 : PrimeCertificate 348917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv4591]) (by decide +kernel)
def pv348917 : PrimeValue := ⟨348917, pr348917⟩
private theorem pr348937 : PrimeCertificate 348937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv31,pv67]) (by decide +kernel)
def pv348937 : PrimeValue := ⟨348937, pr348937⟩
private theorem pr348989 : PrimeCertificate 348989 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv2029]) (by decide +kernel)
def pv348989 : PrimeValue := ⟨348989, pr348989⟩
private theorem pr349121 : PrimeCertificate 349121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1091]) (by decide +kernel)
def pv349121 : PrimeValue := ⟨349121, pr349121⟩
private theorem pr349183 : PrimeCertificate 349183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv1021]) (by decide +kernel)
def pv349183 : PrimeValue := ⟨349183, pr349183⟩
private theorem pr349241 : PrimeCertificate 349241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv8731]) (by decide +kernel)
def pv349241 : PrimeValue := ⟨349241, pr349241⟩
private theorem pr349291 : PrimeCertificate 349291 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3881]) (by decide +kernel)
def pv349291 : PrimeValue := ⟨349291, pr349291⟩
private theorem pr349331 : PrimeCertificate 349331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv181,pv193]) (by decide +kernel)
def pv349331 : PrimeValue := ⟨349331, pr349331⟩
private theorem pr349369 : PrimeCertificate 349369 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv14557]) (by decide +kernel)
def pv349369 : PrimeValue := ⟨349369, pr349369⟩
private theorem pr349423 : PrimeCertificate 349423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv58237]) (by decide +kernel)
def pv349423 : PrimeValue := ⟨349423, pr349423⟩
private theorem pr349477 : PrimeCertificate 349477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29123]) (by decide +kernel)
def pv349477 : PrimeValue := ⟨349477, pr349477⟩
private theorem pr349483 : PrimeCertificate 349483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv53,pv157]) (by decide +kernel)
def pv349483 : PrimeValue := ⟨349483, pr349483⟩
private theorem pr349493 : PrimeCertificate 349493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv47]) (by decide +kernel)
def pv349493 : PrimeValue := ⟨349493, pr349493⟩
private theorem pr349499 : PrimeCertificate 349499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv174749]) (by decide +kernel)
def pv349499 : PrimeValue := ⟨349499, pr349499⟩
private theorem pr349529 : PrimeCertificate 349529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43691]) (by decide +kernel)
def pv349529 : PrimeValue := ⟨349529, pr349529⟩
private theorem pr349567 : PrimeCertificate 349567 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv29,pv41]) (by decide +kernel)
def pv349567 : PrimeValue := ⟨349567, pr349567⟩
private theorem pr349603 : PrimeCertificate 349603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv5297]) (by decide +kernel)
def pv349603 : PrimeValue := ⟨349603, pr349603⟩
private theorem pr349667 : PrimeCertificate 349667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv359,pv487]) (by decide +kernel)
def pv349667 : PrimeValue := ⟨349667, pr349667⟩
private theorem pr349697 : PrimeCertificate 349697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv683]) (by decide +kernel)
def pv349697 : PrimeValue := ⟨349697, pr349697⟩
private theorem pr349753 : PrimeCertificate 349753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv59]) (by decide +kernel)
def pv349753 : PrimeValue := ⟨349753, pr349753⟩
private theorem pr349759 : PrimeCertificate 349759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv127]) (by decide +kernel)
def pv349759 : PrimeValue := ⟨349759, pr349759⟩
private theorem pr349841 : PrimeCertificate 349841 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv4373]) (by decide +kernel)
def pv349841 : PrimeValue := ⟨349841, pr349841⟩
private theorem pr349871 : PrimeCertificate 349871 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv59,pv593]) (by decide +kernel)
def pv349871 : PrimeValue := ⟨349871, pr349871⟩
private theorem pr349913 : PrimeCertificate 349913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv191,pv229]) (by decide +kernel)
def pv349913 : PrimeValue := ⟨349913, pr349913⟩
private theorem pr349927 : PrimeCertificate 349927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv58321]) (by decide +kernel)
def pv349927 : PrimeValue := ⟨349927, pr349927⟩
private theorem pr349931 : PrimeCertificate 349931 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv4999]) (by decide +kernel)
def pv349931 : PrimeValue := ⟨349931, pr349931⟩
private theorem pr349933 : PrimeCertificate 349933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv241]) (by decide +kernel)
def pv349933 : PrimeValue := ⟨349933, pr349933⟩
private theorem pr349981 : PrimeCertificate 349981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv307]) (by decide +kernel)
def pv349981 : PrimeValue := ⟨349981, pr349981⟩
private theorem pr350033 : PrimeCertificate 350033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv131,pv167]) (by decide +kernel)
def pv350033 : PrimeValue := ⟨350033, pr350033⟩
private theorem pr350039 : PrimeCertificate 350039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv13463]) (by decide +kernel)
def pv350039 : PrimeValue := ⟨350039, pr350039⟩
private theorem pr350087 : PrimeCertificate 350087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv15913]) (by decide +kernel)
def pv350087 : PrimeValue := ⟨350087, pr350087⟩
private theorem pr350093 : PrimeCertificate 350093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv87523]) (by decide +kernel)
def pv350093 : PrimeValue := ⟨350093, pr350093⟩
private theorem pr350111 : PrimeCertificate 350111 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv157,pv223]) (by decide +kernel)
def pv350111 : PrimeValue := ⟨350111, pr350111⟩
private theorem pr350159 : PrimeCertificate 350159 :=
  certifyPrime (q := pv17) (ls := [pv2,pv175079]) (by decide +kernel)
def pv350159 : PrimeValue := ⟨350159, pr350159⟩
private theorem pr350237 : PrimeCertificate 350237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv87559]) (by decide +kernel)
def pv350237 : PrimeValue := ⟨350237, pr350237⟩
private theorem pr350249 : PrimeCertificate 350249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43781]) (by decide +kernel)
def pv350249 : PrimeValue := ⟨350249, pr350249⟩
private theorem pr350347 : PrimeCertificate 350347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv58391]) (by decide +kernel)
def pv350347 : PrimeValue := ⟨350347, pr350347⟩
private theorem pr350351 : PrimeCertificate 350351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv13]) (by decide +kernel)
def pv350351 : PrimeValue := ⟨350351, pr350351⟩
private theorem pr350411 : PrimeCertificate 350411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv67,pv523]) (by decide +kernel)
def pv350411 : PrimeValue := ⟨350411, pr350411⟩
private theorem pr350429 : PrimeCertificate 350429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv293]) (by decide +kernel)
def pv350429 : PrimeValue := ⟨350429, pr350429⟩
private theorem pr350437 : PrimeCertificate 350437 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv29,pv53]) (by decide +kernel)
def pv350437 : PrimeValue := ⟨350437, pr350437⟩
private theorem pr350453 : PrimeCertificate 350453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv87613]) (by decide +kernel)
def pv350453 : PrimeValue := ⟨350453, pr350453⟩
private theorem pr350459 : PrimeCertificate 350459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv175229]) (by decide +kernel)
def pv350459 : PrimeValue := ⟨350459, pr350459⟩
private theorem pr350587 : PrimeCertificate 350587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19477]) (by decide +kernel)
def pv350587 : PrimeValue := ⟨350587, pr350587⟩
private theorem pr350699 : PrimeCertificate 350699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv175349]) (by decide +kernel)
def pv350699 : PrimeValue := ⟨350699, pr350699⟩
private theorem pr350711 : PrimeCertificate 350711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv2063]) (by decide +kernel)
def pv350711 : PrimeValue := ⟨350711, pr350711⟩
private theorem pr350737 : PrimeCertificate 350737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7307]) (by decide +kernel)
def pv350737 : PrimeValue := ⟨350737, pr350737⟩
private theorem pr350747 : PrimeCertificate 350747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv107,pv149]) (by decide +kernel)
def pv350747 : PrimeValue := ⟨350747, pr350747⟩
private theorem pr350771 : PrimeCertificate 350771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv5011]) (by decide +kernel)
def pv350771 : PrimeValue := ⟨350771, pr350771⟩
private theorem pr350783 : PrimeCertificate 350783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv175391]) (by decide +kernel)
def pv350783 : PrimeValue := ⟨350783, pr350783⟩
private theorem pr350789 : PrimeCertificate 350789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv87697]) (by decide +kernel)
def pv350789 : PrimeValue := ⟨350789, pr350789⟩
private theorem pr350881 : PrimeCertificate 350881 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv43]) (by decide +kernel)
def pv350881 : PrimeValue := ⟨350881, pr350881⟩
private theorem pr350891 : PrimeCertificate 350891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv35089]) (by decide +kernel)
def pv350891 : PrimeValue := ⟨350891, pr350891⟩
private theorem pr350947 : PrimeCertificate 350947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv97]) (by decide +kernel)
def pv350947 : PrimeValue := ⟨350947, pr350947⟩
private theorem pr350981 : PrimeCertificate 350981 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv23,pv109]) (by decide +kernel)
def pv350981 : PrimeValue := ⟨350981, pr350981⟩
private theorem pr350983 : PrimeCertificate 350983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv31,pv37]) (by decide +kernel)
def pv350983 : PrimeValue := ⟨350983, pr350983⟩
private theorem pr350989 : PrimeCertificate 350989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv2659]) (by decide +kernel)
def pv350989 : PrimeValue := ⟨350989, pr350989⟩
private theorem pr351041 : PrimeCertificate 351041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1097]) (by decide +kernel)
def pv351041 : PrimeValue := ⟨351041, pr351041⟩
private theorem pr351077 : PrimeCertificate 351077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv79,pv101]) (by decide +kernel)
def pv351077 : PrimeValue := ⟨351077, pr351077⟩
private theorem pr351157 : PrimeCertificate 351157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv2251]) (by decide +kernel)
def pv351157 : PrimeValue := ⟨351157, pr351157⟩
private theorem pr351217 : PrimeCertificate 351217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv271]) (by decide +kernel)
def pv351217 : PrimeValue := ⟨351217, pr351217⟩
private theorem pr351257 : PrimeCertificate 351257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv83]) (by decide +kernel)
def pv351257 : PrimeValue := ⟨351257, pr351257⟩
private theorem pr351269 : PrimeCertificate 351269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv641]) (by decide +kernel)
def pv351269 : PrimeValue := ⟨351269, pr351269⟩
private theorem pr351287 : PrimeCertificate 351287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv59,pv229]) (by decide +kernel)
def pv351287 : PrimeValue := ⟨351287, pr351287⟩
private theorem pr351293 : PrimeCertificate 351293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2833]) (by decide +kernel)
def pv351293 : PrimeValue := ⟨351293, pr351293⟩
private theorem pr351311 : PrimeCertificate 351311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv43]) (by decide +kernel)
def pv351311 : PrimeValue := ⟨351311, pr351311⟩
private theorem pr351341 : PrimeCertificate 351341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1597]) (by decide +kernel)
def pv351341 : PrimeValue := ⟨351341, pr351341⟩
private theorem pr351343 : PrimeCertificate 351343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv131,pv149]) (by decide +kernel)
def pv351343 : PrimeValue := ⟨351343, pr351343⟩
private theorem pr351383 : PrimeCertificate 351383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv175691]) (by decide +kernel)
def pv351383 : PrimeValue := ⟨351383, pr351383⟩
private theorem pr351391 : PrimeCertificate 351391 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv17,pv53]) (by decide +kernel)
def pv351391 : PrimeValue := ⟨351391, pr351391⟩
private theorem pr351397 : PrimeCertificate 351397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv227]) (by decide +kernel)
def pv351397 : PrimeValue := ⟨351397, pr351397⟩
private theorem pr351401 : PrimeCertificate 351401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv251]) (by decide +kernel)
def pv351401 : PrimeValue := ⟨351401, pr351401⟩
private theorem pr351413 : PrimeCertificate 351413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv87853]) (by decide +kernel)
def pv351413 : PrimeValue := ⟨351413, pr351413⟩
private theorem pr351427 : PrimeCertificate 351427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv1583]) (by decide +kernel)
def pv351427 : PrimeValue := ⟨351427, pr351427⟩
private theorem pr351479 : PrimeCertificate 351479 :=
  certifyPrime (q := pv13) (ls := [pv2,pv31,pv5669]) (by decide +kernel)
def pv351479 : PrimeValue := ⟨351479, pr351479⟩
private theorem pr351497 : PrimeCertificate 351497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv829]) (by decide +kernel)
def pv351497 : PrimeValue := ⟨351497, pr351497⟩
private theorem pr351517 : PrimeCertificate 351517 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv2663]) (by decide +kernel)
def pv351517 : PrimeValue := ⟨351517, pr351517⟩
private theorem pr351563 : PrimeCertificate 351563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv175781]) (by decide +kernel)
def pv351563 : PrimeValue := ⟨351563, pr351563⟩
private theorem pr351587 : PrimeCertificate 351587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv367,pv479]) (by decide +kernel)
def pv351587 : PrimeValue := ⟨351587, pr351587⟩
private theorem pr351731 : PrimeCertificate 351731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv2069]) (by decide +kernel)
def pv351731 : PrimeValue := ⟨351731, pr351731⟩
private theorem pr351733 : PrimeCertificate 351733 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29311]) (by decide +kernel)
def pv351733 : PrimeValue := ⟨351733, pr351733⟩
private theorem pr351749 : PrimeCertificate 351749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1871]) (by decide +kernel)
def pv351749 : PrimeValue := ⟨351749, pr351749⟩
private theorem pr351763 : PrimeCertificate 351763 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv2549]) (by decide +kernel)
def pv351763 : PrimeValue := ⟨351763, pr351763⟩
private theorem pr351779 : PrimeCertificate 351779 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv25127]) (by decide +kernel)
def pv351779 : PrimeValue := ⟨351779, pr351779⟩
private theorem pr351829 : PrimeCertificate 351829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv337]) (by decide +kernel)
def pv351829 : PrimeValue := ⟨351829, pr351829⟩
private theorem pr351847 : PrimeCertificate 351847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1777]) (by decide +kernel)
def pv351847 : PrimeValue := ⟨351847, pr351847⟩
private theorem pr351851 : PrimeCertificate 351851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv227]) (by decide +kernel)
def pv351851 : PrimeValue := ⟨351851, pr351851⟩
private theorem pr351971 : PrimeCertificate 351971 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv61,pv577]) (by decide +kernel)
def pv351971 : PrimeValue := ⟨351971, pr351971⟩
private theorem pr352007 : PrimeCertificate 352007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv73,pv2411]) (by decide +kernel)
def pv352007 : PrimeValue := ⟨352007, pr352007⟩
private theorem pr352021 : PrimeCertificate 352021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv5867]) (by decide +kernel)
def pv352021 : PrimeValue := ⟨352021, pr352021⟩
private theorem pr352043 : PrimeCertificate 352043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv176021]) (by decide +kernel)
def pv352043 : PrimeValue := ⟨352043, pr352043⟩
private theorem pr352097 : PrimeCertificate 352097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11003]) (by decide +kernel)
def pv352097 : PrimeValue := ⟨352097, pr352097⟩
private theorem pr352109 : PrimeCertificate 352109 :=
  certifyPrime (q := pv11) (ls := [pv2,pv19,pv41,pv113]) (by decide +kernel)
def pv352109 : PrimeValue := ⟨352109, pr352109⟩
private theorem pr352123 : PrimeCertificate 352123 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv58687]) (by decide +kernel)
def pv352123 : PrimeValue := ⟨352123, pr352123⟩
private theorem pr352181 : PrimeCertificate 352181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17609]) (by decide +kernel)
def pv352181 : PrimeValue := ⟨352181, pr352181⟩
private theorem pr352193 : PrimeCertificate 352193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5503]) (by decide +kernel)
def pv352193 : PrimeValue := ⟨352193, pr352193⟩
private theorem pr352201 : PrimeCertificate 352201 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv587]) (by decide +kernel)
def pv352201 : PrimeValue := ⟨352201, pr352201⟩
private theorem pr352267 : PrimeCertificate 352267 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv58711]) (by decide +kernel)
def pv352267 : PrimeValue := ⟨352267, pr352267⟩
private theorem pr352301 : PrimeCertificate 352301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv271]) (by decide +kernel)
def pv352301 : PrimeValue := ⟨352301, pr352301⟩
private theorem pr352309 : PrimeCertificate 352309 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv11,pv17,pv157]) (by decide +kernel)
def pv352309 : PrimeValue := ⟨352309, pr352309⟩
private theorem pr352403 : PrimeCertificate 352403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv176201]) (by decide +kernel)
def pv352403 : PrimeValue := ⟨352403, pr352403⟩
private theorem pr352409 : PrimeCertificate 352409 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv29,pv31]) (by decide +kernel)
def pv352409 : PrimeValue := ⟨352409, pr352409⟩
private theorem pr352411 : PrimeCertificate 352411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv691]) (by decide +kernel)
def pv352411 : PrimeValue := ⟨352411, pr352411⟩
private theorem pr352481 : PrimeCertificate 352481 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv2203]) (by decide +kernel)
def pv352481 : PrimeValue := ⟨352481, pr352481⟩
private theorem pr352489 : PrimeCertificate 352489 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv19,pv773]) (by decide +kernel)
def pv352489 : PrimeValue := ⟨352489, pr352489⟩
private theorem pr352511 : PrimeCertificate 352511 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv35251]) (by decide +kernel)
def pv352511 : PrimeValue := ⟨352511, pr352511⟩
private theorem pr352549 : PrimeCertificate 352549 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv1399]) (by decide +kernel)
def pv352549 : PrimeValue := ⟨352549, pr352549⟩
private theorem pr352601 : PrimeCertificate 352601 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv41,pv43]) (by decide +kernel)
def pv352601 : PrimeValue := ⟨352601, pr352601⟩
private theorem pr352637 : PrimeCertificate 352637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv3833]) (by decide +kernel)
def pv352637 : PrimeValue := ⟨352637, pr352637⟩
private theorem pr352661 : PrimeCertificate 352661 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv11,pv229]) (by decide +kernel)
def pv352661 : PrimeValue := ⟨352661, pr352661⟩
private theorem pr352739 : PrimeCertificate 352739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv176369]) (by decide +kernel)
def pv352739 : PrimeValue := ⟨352739, pr352739⟩
private theorem pr352741 : PrimeCertificate 352741 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv5879]) (by decide +kernel)
def pv352741 : PrimeValue := ⟨352741, pr352741⟩
private theorem pr352753 : PrimeCertificate 352753 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7349]) (by decide +kernel)
def pv352753 : PrimeValue := ⟨352753, pr352753⟩
private theorem pr352771 : PrimeCertificate 352771 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv1069]) (by decide +kernel)
def pv352771 : PrimeValue := ⟨352771, pr352771⟩
private theorem pr352817 : PrimeCertificate 352817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22051]) (by decide +kernel)
def pv352817 : PrimeValue := ⟨352817, pr352817⟩
private theorem pr352831 : PrimeCertificate 352831 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv19,pv619]) (by decide +kernel)
def pv352831 : PrimeValue := ⟨352831, pr352831⟩
private theorem pr352853 : PrimeCertificate 352853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv5189]) (by decide +kernel)
def pv352853 : PrimeValue := ⟨352853, pr352853⟩
private theorem pr352909 : PrimeCertificate 352909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9803]) (by decide +kernel)
def pv352909 : PrimeValue := ⟨352909, pr352909⟩
private theorem pr352931 : PrimeCertificate 352931 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv29,pv1217]) (by decide +kernel)
def pv352931 : PrimeValue := ⟨352931, pr352931⟩
private theorem pr352949 : PrimeCertificate 352949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv88237]) (by decide +kernel)
def pv352949 : PrimeValue := ⟨352949, pr352949⟩
private theorem pr353047 : PrimeCertificate 353047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv2029]) (by decide +kernel)
def pv353047 : PrimeValue := ⟨353047, pr353047⟩
private theorem pr353057 : PrimeCertificate 353057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17,pv59]) (by decide +kernel)
def pv353057 : PrimeValue := ⟨353057, pr353057⟩
private theorem pr353069 : PrimeCertificate 353069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv1447]) (by decide +kernel)
def pv353069 : PrimeValue := ⟨353069, pr353069⟩
private theorem pr353081 : PrimeCertificate 353081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv97]) (by decide +kernel)
def pv353081 : PrimeValue := ⟨353081, pr353081⟩
private theorem pr353099 : PrimeCertificate 353099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv176549]) (by decide +kernel)
def pv353099 : PrimeValue := ⟨353099, pr353099⟩
private theorem pr353117 : PrimeCertificate 353117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv2053]) (by decide +kernel)
def pv353117 : PrimeValue := ⟨353117, pr353117⟩
private theorem pr353149 : PrimeCertificate 353149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29429]) (by decide +kernel)
def pv353149 : PrimeValue := ⟨353149, pr353149⟩
private theorem pr353173 : PrimeCertificate 353173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1549]) (by decide +kernel)
def pv353173 : PrimeValue := ⟨353173, pr353173⟩
private theorem pr353201 : PrimeCertificate 353201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv883]) (by decide +kernel)
def pv353201 : PrimeValue := ⟨353201, pr353201⟩
private theorem pr353203 : PrimeCertificate 353203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv43]) (by decide +kernel)
def pv353203 : PrimeValue := ⟨353203, pr353203⟩
private theorem pr353293 : PrimeCertificate 353293 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv499]) (by decide +kernel)
def pv353293 : PrimeValue := ⟨353293, pr353293⟩
private theorem pr353443 : PrimeCertificate 353443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv58907]) (by decide +kernel)
def pv353443 : PrimeValue := ⟨353443, pr353443⟩
private theorem pr353453 : PrimeCertificate 353453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv29,pv277]) (by decide +kernel)
def pv353453 : PrimeValue := ⟨353453, pr353453⟩
private theorem pr353459 : PrimeCertificate 353459 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv25247]) (by decide +kernel)
def pv353459 : PrimeValue := ⟨353459, pr353459⟩
private theorem pr353471 : PrimeCertificate 353471 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv2719]) (by decide +kernel)
def pv353471 : PrimeValue := ⟨353471, pr353471⟩
private theorem pr353531 : PrimeCertificate 353531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv35353]) (by decide +kernel)
def pv353531 : PrimeValue := ⟨353531, pr353531⟩
private theorem pr353567 : PrimeCertificate 353567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv10399]) (by decide +kernel)
def pv353567 : PrimeValue := ⟨353567, pr353567⟩
private theorem pr353603 : PrimeCertificate 353603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv7687]) (by decide +kernel)
def pv353603 : PrimeValue := ⟨353603, pr353603⟩
private theorem pr353611 : PrimeCertificate 353611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3929]) (by decide +kernel)
def pv353611 : PrimeValue := ⟨353611, pr353611⟩
private theorem pr353653 : PrimeCertificate 353653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv2267]) (by decide +kernel)
def pv353653 : PrimeValue := ⟨353653, pr353653⟩
private theorem pr353657 : PrimeCertificate 353657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv44207]) (by decide +kernel)
def pv353657 : PrimeValue := ⟨353657, pr353657⟩
private theorem pr353677 : PrimeCertificate 353677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29473]) (by decide +kernel)
def pv353677 : PrimeValue := ⟨353677, pr353677⟩
private theorem pr353687 : PrimeCertificate 353687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv89,pv1987]) (by decide +kernel)
def pv353687 : PrimeValue := ⟨353687, pr353687⟩
private theorem pr353747 : PrimeCertificate 353747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv2131]) (by decide +kernel)
def pv353747 : PrimeValue := ⟨353747, pr353747⟩
private theorem pr353767 : PrimeCertificate 353767 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv8423]) (by decide +kernel)
def pv353767 : PrimeValue := ⟨353767, pr353767⟩
private theorem pr353807 : PrimeCertificate 353807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv176903]) (by decide +kernel)
def pv353807 : PrimeValue := ⟨353807, pr353807⟩
private theorem pr353813 : PrimeCertificate 353813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197,pv449]) (by decide +kernel)
def pv353813 : PrimeValue := ⟨353813, pr353813⟩
private theorem pr353867 : PrimeCertificate 353867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv176933]) (by decide +kernel)
def pv353867 : PrimeValue := ⟨353867, pr353867⟩
private theorem pr353897 : PrimeCertificate 353897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv1427]) (by decide +kernel)
def pv353897 : PrimeValue := ⟨353897, pr353897⟩
private theorem pr354001 : PrimeCertificate 354001 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv59]) (by decide +kernel)
def pv354001 : PrimeValue := ⟨354001, pr354001⟩
private theorem pr354007 : PrimeCertificate 354007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv277]) (by decide +kernel)
def pv354007 : PrimeValue := ⟨354007, pr354007⟩
private theorem pr354023 : PrimeCertificate 354023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv177011]) (by decide +kernel)
def pv354023 : PrimeValue := ⟨354023, pr354023⟩
private theorem pr354037 : PrimeCertificate 354037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv163,pv181]) (by decide +kernel)
def pv354037 : PrimeValue := ⟨354037, pr354037⟩
private theorem pr354041 : PrimeCertificate 354041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv53,pv167]) (by decide +kernel)
def pv354041 : PrimeValue := ⟨354041, pr354041⟩
private theorem pr354073 : PrimeCertificate 354073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv14753]) (by decide +kernel)
def pv354073 : PrimeValue := ⟨354073, pr354073⟩
private theorem pr354143 : PrimeCertificate 354143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv113,pv1567]) (by decide +kernel)
def pv354143 : PrimeValue := ⟨354143, pr354143⟩
private theorem pr354181 : PrimeCertificate 354181 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv5903]) (by decide +kernel)
def pv354181 : PrimeValue := ⟨354181, pr354181⟩
private theorem pr354257 : PrimeCertificate 354257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv3163]) (by decide +kernel)
def pv354257 : PrimeValue := ⟨354257, pr354257⟩
private theorem pr354313 : PrimeCertificate 354313 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv7,pv19,pv37]) (by decide +kernel)
def pv354313 : PrimeValue := ⟨354313, pr354313⟩
private theorem pr354323 : PrimeCertificate 354323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv41,pv149]) (by decide +kernel)
def pv354323 : PrimeValue := ⟨354323, pr354323⟩
private theorem pr354337 : PrimeCertificate 354337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3691]) (by decide +kernel)
def pv354337 : PrimeValue := ⟨354337, pr354337⟩
private theorem pr354371 : PrimeCertificate 354371 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv35437]) (by decide +kernel)
def pv354371 : PrimeValue := ⟨354371, pr354371⟩
private theorem pr354401 : PrimeCertificate 354401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv443]) (by decide +kernel)
def pv354401 : PrimeValue := ⟨354401, pr354401⟩
private theorem pr354443 : PrimeCertificate 354443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv16111]) (by decide +kernel)
def pv354443 : PrimeValue := ⟨354443, pr354443⟩
private theorem pr354461 : PrimeCertificate 354461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv479]) (by decide +kernel)
def pv354461 : PrimeValue := ⟨354461, pr354461⟩
private theorem pr354463 : PrimeCertificate 354463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59077]) (by decide +kernel)
def pv354463 : PrimeValue := ⟨354463, pr354463⟩
private theorem pr354479 : PrimeCertificate 354479 :=
  certifyPrime (q := pv11) (ls := [pv2,pv177239]) (by decide +kernel)
def pv354479 : PrimeValue := ⟨354479, pr354479⟩
private theorem pr354539 : PrimeCertificate 354539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv177269]) (by decide +kernel)
def pv354539 : PrimeValue := ⟨354539, pr354539⟩
private theorem pr354553 : PrimeCertificate 354553 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv17,pv79]) (by decide +kernel)
def pv354553 : PrimeValue := ⟨354553, pr354553⟩
private theorem pr354647 : PrimeCertificate 354647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv177323]) (by decide +kernel)
def pv354647 : PrimeValue := ⟨354647, pr354647⟩
private theorem pr354661 : PrimeCertificate 354661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv257]) (by decide +kernel)
def pv354661 : PrimeValue := ⟨354661, pr354661⟩
private theorem pr354701 : PrimeCertificate 354701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3547]) (by decide +kernel)
def pv354701 : PrimeValue := ⟨354701, pr354701⟩
private theorem pr354791 : PrimeCertificate 354791 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv2087]) (by decide +kernel)
def pv354791 : PrimeValue := ⟨354791, pr354791⟩
private theorem pr354829 : PrimeCertificate 354829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29569]) (by decide +kernel)
def pv354829 : PrimeValue := ⟨354829, pr354829⟩
private theorem pr354839 : PrimeCertificate 354839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv127]) (by decide +kernel)
def pv354839 : PrimeValue := ⟨354839, pr354839⟩
private theorem pr354847 : PrimeCertificate 354847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59141]) (by decide +kernel)
def pv354847 : PrimeValue := ⟨354847, pr354847⟩
private theorem pr354869 : PrimeCertificate 354869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv1123]) (by decide +kernel)
def pv354869 : PrimeValue := ⟨354869, pr354869⟩
private theorem pr354877 : PrimeCertificate 354877 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv29573]) (by decide +kernel)
def pv354877 : PrimeValue := ⟨354877, pr354877⟩
private theorem pr354881 : PrimeCertificate 354881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1109]) (by decide +kernel)
def pv354881 : PrimeValue := ⟨354881, pr354881⟩
private theorem pr354883 : PrimeCertificate 354883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv283]) (by decide +kernel)
def pv354883 : PrimeValue := ⟨354883, pr354883⟩
private theorem pr354911 : PrimeCertificate 354911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv35491]) (by decide +kernel)
def pv354911 : PrimeValue := ⟨354911, pr354911⟩
private theorem pr354953 : PrimeCertificate 354953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv3413]) (by decide +kernel)
def pv354953 : PrimeValue := ⟨354953, pr354953⟩
private theorem pr354971 : PrimeCertificate 354971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv461]) (by decide +kernel)
def pv354971 : PrimeValue := ⟨354971, pr354971⟩
private theorem pr354983 : PrimeCertificate 354983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv7717]) (by decide +kernel)
def pv354983 : PrimeValue := ⟨354983, pr354983⟩
private theorem pr354997 : PrimeCertificate 354997 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv173]) (by decide +kernel)
def pv354997 : PrimeValue := ⟨354997, pr354997⟩
private theorem pr355009 : PrimeCertificate 355009 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv355009 : PrimeValue := ⟨355009, pr355009⟩
private theorem pr355027 : PrimeCertificate 355027 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv79,pv107]) (by decide +kernel)
def pv355027 : PrimeValue := ⟨355027, pr355027⟩
private theorem pr355031 : PrimeCertificate 355031 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv13,pv2731]) (by decide +kernel)
def pv355031 : PrimeValue := ⟨355031, pr355031⟩
private theorem pr355049 : PrimeCertificate 355049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv44381]) (by decide +kernel)
def pv355049 : PrimeValue := ⟨355049, pr355049⟩
private theorem pr355057 : PrimeCertificate 355057 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv569]) (by decide +kernel)
def pv355057 : PrimeValue := ⟨355057, pr355057⟩
private theorem pr355063 : PrimeCertificate 355063 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv59]) (by decide +kernel)
def pv355063 : PrimeValue := ⟨355063, pr355063⟩
private theorem pr355073 : PrimeCertificate 355073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv73]) (by decide +kernel)
def pv355073 : PrimeValue := ⟨355073, pr355073⟩
private theorem pr355087 : PrimeCertificate 355087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19727]) (by decide +kernel)
def pv355087 : PrimeValue := ⟨355087, pr355087⟩
private theorem pr355093 : PrimeCertificate 355093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv127,pv233]) (by decide +kernel)
def pv355093 : PrimeValue := ⟨355093, pr355093⟩
private theorem pr355109 : PrimeCertificate 355109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv6829]) (by decide +kernel)
def pv355109 : PrimeValue := ⟨355109, pr355109⟩
private theorem pr355211 : PrimeCertificate 355211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv35521]) (by decide +kernel)
def pv355211 : PrimeValue := ⟨355211, pr355211⟩
private theorem pr355261 : PrimeCertificate 355261 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv31,pv191]) (by decide +kernel)
def pv355261 : PrimeValue := ⟨355261, pr355261⟩
private theorem pr355331 : PrimeCertificate 355331 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv35533]) (by decide +kernel)
def pv355331 : PrimeValue := ⟨355331, pr355331⟩
private theorem pr355417 : PrimeCertificate 355417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv251]) (by decide +kernel)
def pv355417 : PrimeValue := ⟨355417, pr355417⟩
private theorem pr355427 : PrimeCertificate 355427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv2503]) (by decide +kernel)
def pv355427 : PrimeValue := ⟨355427, pr355427⟩
private theorem pr355483 : PrimeCertificate 355483 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv227]) (by decide +kernel)
def pv355483 : PrimeValue := ⟨355483, pr355483⟩
private theorem pr355499 : PrimeCertificate 355499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv113]) (by decide +kernel)
def pv355499 : PrimeValue := ⟨355499, pr355499⟩
private theorem pr355541 : PrimeCertificate 355541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv613]) (by decide +kernel)
def pv355541 : PrimeValue := ⟨355541, pr355541⟩
private theorem pr355571 : PrimeCertificate 355571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv37]) (by decide +kernel)
def pv355571 : PrimeValue := ⟨355571, pr355571⟩
private theorem pr355573 : PrimeCertificate 355573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv83]) (by decide +kernel)
def pv355573 : PrimeValue := ⟨355573, pr355573⟩
private theorem pr355609 : PrimeCertificate 355609 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv11,pv449]) (by decide +kernel)
def pv355609 : PrimeValue := ⟨355609, pr355609⟩
private theorem pr355633 : PrimeCertificate 355633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv239]) (by decide +kernel)
def pv355633 : PrimeValue := ⟨355633, pr355633⟩
private theorem pr355643 : PrimeCertificate 355643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv191]) (by decide +kernel)
def pv355643 : PrimeValue := ⟨355643, pr355643⟩
private theorem pr355669 : PrimeCertificate 355669 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv107,pv277]) (by decide +kernel)
def pv355669 : PrimeValue := ⟨355669, pr355669⟩
private theorem pr355679 : PrimeCertificate 355679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv177839]) (by decide +kernel)
def pv355679 : PrimeValue := ⟨355679, pr355679⟩
private theorem pr355697 : PrimeCertificate 355697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv43,pv47]) (by decide +kernel)
def pv355697 : PrimeValue := ⟨355697, pr355697⟩
private theorem pr355717 : PrimeCertificate 355717 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv41,pv241]) (by decide +kernel)
def pv355717 : PrimeValue := ⟨355717, pr355717⟩
private theorem pr355723 : PrimeCertificate 355723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv587]) (by decide +kernel)
def pv355723 : PrimeValue := ⟨355723, pr355723⟩
private theorem pr355753 : PrimeCertificate 355753 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv355753 : PrimeValue := ⟨355753, pr355753⟩
private theorem pr355763 : PrimeCertificate 355763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv103,pv157]) (by decide +kernel)
def pv355763 : PrimeValue := ⟨355763, pr355763⟩
private theorem pr355819 : PrimeCertificate 355819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv1913]) (by decide +kernel)
def pv355819 : PrimeValue := ⟨355819, pr355819⟩
private theorem pr355847 : PrimeCertificate 355847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv181,pv983]) (by decide +kernel)
def pv355847 : PrimeValue := ⟨355847, pr355847⟩
private theorem pr355853 : PrimeCertificate 355853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv71,pv179]) (by decide +kernel)
def pv355853 : PrimeValue := ⟨355853, pr355853⟩
private theorem pr355867 : PrimeCertificate 355867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv37,pv229]) (by decide +kernel)
def pv355867 : PrimeValue := ⟨355867, pr355867⟩
private theorem pr355891 : PrimeCertificate 355891 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11863]) (by decide +kernel)
def pv355891 : PrimeValue := ⟨355891, pr355891⟩
private theorem pr355909 : PrimeCertificate 355909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv223]) (by decide +kernel)
def pv355909 : PrimeValue := ⟨355909, pr355909⟩
private theorem pr355913 : PrimeCertificate 355913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv2617]) (by decide +kernel)
def pv355913 : PrimeValue := ⟨355913, pr355913⟩
private theorem pr355937 : PrimeCertificate 355937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv227]) (by decide +kernel)
def pv355937 : PrimeValue := ⟨355937, pr355937⟩
private theorem pr355939 : PrimeCertificate 355939 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv5393]) (by decide +kernel)
def pv355939 : PrimeValue := ⟨355939, pr355939⟩
private theorem pr356023 : PrimeCertificate 356023 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv347]) (by decide +kernel)
def pv356023 : PrimeValue := ⟨356023, pr356023⟩
private theorem pr356093 : PrimeCertificate 356093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv8093]) (by decide +kernel)
def pv356093 : PrimeValue := ⟨356093, pr356093⟩
private theorem pr356141 : PrimeCertificate 356141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17807]) (by decide +kernel)
def pv356141 : PrimeValue := ⟨356141, pr356141⟩
private theorem pr356143 : PrimeCertificate 356143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59357]) (by decide +kernel)
def pv356143 : PrimeValue := ⟨356143, pr356143⟩
private theorem pr356197 : PrimeCertificate 356197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29683]) (by decide +kernel)
def pv356197 : PrimeValue := ⟨356197, pr356197⟩
private theorem pr356327 : PrimeCertificate 356327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv9377]) (by decide +kernel)
def pv356327 : PrimeValue := ⟨356327, pr356327⟩
private theorem pr356333 : PrimeCertificate 356333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89083]) (by decide +kernel)
def pv356333 : PrimeValue := ⟨356333, pr356333⟩
private theorem pr356387 : PrimeCertificate 356387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv2441]) (by decide +kernel)
def pv356387 : PrimeValue := ⟨356387, pr356387⟩
private theorem pr356441 : PrimeCertificate 356441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv19,pv67]) (by decide +kernel)
def pv356441 : PrimeValue := ⟨356441, pr356441⟩
private theorem pr356449 : PrimeCertificate 356449 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv47,pv79]) (by decide +kernel)
def pv356449 : PrimeValue := ⟨356449, pr356449⟩
private theorem pr356467 : PrimeCertificate 356467 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv491]) (by decide +kernel)
def pv356467 : PrimeValue := ⟨356467, pr356467⟩
private theorem pr356479 : PrimeCertificate 356479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv53,pv59]) (by decide +kernel)
def pv356479 : PrimeValue := ⟨356479, pr356479⟩
private theorem pr356533 : PrimeCertificate 356533 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv37,pv73]) (by decide +kernel)
def pv356533 : PrimeValue := ⟨356533, pr356533⟩
private theorem pr356561 : PrimeCertificate 356561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv4457]) (by decide +kernel)
def pv356561 : PrimeValue := ⟨356561, pr356561⟩
private theorem pr356579 : PrimeCertificate 356579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv178289]) (by decide +kernel)
def pv356579 : PrimeValue := ⟨356579, pr356579⟩
private theorem pr356591 : PrimeCertificate 356591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv211]) (by decide +kernel)
def pv356591 : PrimeValue := ⟨356591, pr356591⟩
private theorem pr356621 : PrimeCertificate 356621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1621]) (by decide +kernel)
def pv356621 : PrimeValue := ⟨356621, pr356621⟩
private theorem pr356663 : PrimeCertificate 356663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv151,pv1181]) (by decide +kernel)
def pv356663 : PrimeValue := ⟨356663, pr356663⟩
private theorem pr356701 : PrimeCertificate 356701 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv29,pv41]) (by decide +kernel)
def pv356701 : PrimeValue := ⟨356701, pr356701⟩
private theorem pr356731 : PrimeCertificate 356731 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv23,pv47]) (by decide +kernel)
def pv356731 : PrimeValue := ⟨356731, pr356731⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
