/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table208
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table208.pv708347
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table044
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table093
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table094

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr708347 : Nat.Prime 708347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv149,pv2377]) (by decide +kernel)
def pv708347 : PrimeValue := ⟨708347, pr708347⟩
private theorem pr708481 : Nat.Prime 708481 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv708481 : PrimeValue := ⟨708481, pr708481⟩
private theorem pr708641 : Nat.Prime 708641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43,pv103]) (by decide +kernel)
def pv708641 : PrimeValue := ⟨708641, pr708641⟩
private theorem pr708803 : Nat.Prime 708803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv354401]) (by decide +kernel)
def pv708803 : PrimeValue := ⟨708803, pr708803⟩
private theorem pr708907 : Nat.Prime 708907 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11,pv23,pv467]) (by decide +kernel)
def pv708907 : PrimeValue := ⟨708907, pr708907⟩
private theorem pr709043 : Nat.Prime 709043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv47,pv397]) (by decide +kernel)
def pv709043 : PrimeValue := ⟨709043, pr709043⟩
private theorem pr709097 : Nat.Prime 709097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv151,pv587]) (by decide +kernel)
def pv709097 : PrimeValue := ⟨709097, pr709097⟩
private theorem pr709123 : Nat.Prime 709123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73,pv1619]) (by decide +kernel)
def pv709123 : PrimeValue := ⟨709123, pr709123⟩
private theorem pr709231 : Nat.Prime 709231 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv47,pv503]) (by decide +kernel)
def pv709231 : PrimeValue := ⟨709231, pr709231⟩
private theorem pr709547 : Nat.Prime 709547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv41,pv509]) (by decide +kernel)
def pv709547 : PrimeValue := ⟨709547, pr709547⟩
private theorem pr709831 : Nat.Prime 709831 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv239]) (by decide +kernel)
def pv709831 : PrimeValue := ⟨709831, pr709831⟩
private theorem pr709853 : Nat.Prime 709853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv17,pv73]) (by decide +kernel)
def pv709853 : PrimeValue := ⟨709853, pr709853⟩
private theorem pr709921 : Nat.Prime 709921 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv17,pv29]) (by decide +kernel)
def pv709921 : PrimeValue := ⟨709921, pr709921⟩
private theorem pr709981 : Nat.Prime 709981 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11833]) (by decide +kernel)
def pv709981 : PrimeValue := ⟨709981, pr709981⟩
private theorem pr710293 : Nat.Prime 710293 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv5381]) (by decide +kernel)
def pv710293 : PrimeValue := ⟨710293, pr710293⟩
private theorem pr710327 : Nat.Prime 710327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv37,pv331]) (by decide +kernel)
def pv710327 : PrimeValue := ⟨710327, pr710327⟩
private theorem pr710341 : Nat.Prime 710341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11839]) (by decide +kernel)
def pv710341 : PrimeValue := ⟨710341, pr710341⟩
private theorem pr710623 : Nat.Prime 710623 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv37,pv97]) (by decide +kernel)
def pv710623 : PrimeValue := ⟨710623, pr710623⟩
private theorem pr710663 : Nat.Prime 710663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv355331]) (by decide +kernel)
def pv710663 : PrimeValue := ⟨710663, pr710663⟩
private theorem pr710863 : Nat.Prime 710863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv257,pv461]) (by decide +kernel)
def pv710863 : PrimeValue := ⟨710863, pr710863⟩
private theorem pr711121 : Nat.Prime 711121 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv2963]) (by decide +kernel)
def pv711121 : PrimeValue := ⟨711121, pr711121⟩
private theorem pr711223 : Nat.Prime 711223 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv113,pv1049]) (by decide +kernel)
def pv711223 : PrimeValue := ⟨711223, pr711223⟩
private theorem pr711437 : Nat.Prime 711437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv23,pv37]) (by decide +kernel)
def pv711437 : PrimeValue := ⟨711437, pr711437⟩
private theorem pr711727 : Nat.Prime 711727 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv118621]) (by decide +kernel)
def pv711727 : PrimeValue := ⟨711727, pr711727⟩
private theorem pr711751 : Nat.Prime 711751 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv73]) (by decide +kernel)
def pv711751 : PrimeValue := ⟨711751, pr711751⟩
private theorem pr711757 : Nat.Prime 711757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv1163]) (by decide +kernel)
def pv711757 : PrimeValue := ⟨711757, pr711757⟩
private theorem pr711913 : Nat.Prime 711913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29663]) (by decide +kernel)
def pv711913 : PrimeValue := ⟨711913, pr711913⟩
private theorem pr711967 : Nat.Prime 711967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv118661]) (by decide +kernel)
def pv711967 : PrimeValue := ⟨711967, pr711967⟩
private theorem pr712121 : Nat.Prime 712121 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv19,pv937]) (by decide +kernel)
def pv712121 : PrimeValue := ⟨712121, pr712121⟩
private theorem pr712133 : Nat.Prime 712133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv5743]) (by decide +kernel)
def pv712133 : PrimeValue := ⟨712133, pr712133⟩
private theorem pr712157 : Nat.Prime 712157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv178039]) (by decide +kernel)
def pv712157 : PrimeValue := ⟨712157, pr712157⟩
private theorem pr712477 : Nat.Prime 712477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv733]) (by decide +kernel)
def pv712477 : PrimeValue := ⟨712477, pr712477⟩
private theorem pr712507 : Nat.Prime 712507 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv118751]) (by decide +kernel)
def pv712507 : PrimeValue := ⟨712507, pr712507⟩
private theorem pr712631 : Nat.Prime 712631 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv71263]) (by decide +kernel)
def pv712631 : PrimeValue := ⟨712631, pr712631⟩
private theorem pr712717 : Nat.Prime 712717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59393]) (by decide +kernel)
def pv712717 : PrimeValue := ⟨712717, pr712717⟩
private theorem pr712837 : Nat.Prime 712837 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19801]) (by decide +kernel)
def pv712837 : PrimeValue := ⟨712837, pr712837⟩
private theorem pr712843 : Nat.Prime 712843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv19,pv37]) (by decide +kernel)
def pv712843 : PrimeValue := ⟨712843, pr712843⟩
private theorem pr712913 : Nat.Prime 712913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv2621]) (by decide +kernel)
def pv712913 : PrimeValue := ⟨712913, pr712913⟩
private theorem pr712981 : Nat.Prime 712981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv233]) (by decide +kernel)
def pv712981 : PrimeValue := ⟨712981, pr712981⟩
private theorem pr713177 : Nat.Prime 713177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv239,pv373]) (by decide +kernel)
def pv713177 : PrimeValue := ⟨713177, pr713177⟩
private theorem pr713243 : Nat.Prime 713243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv356621]) (by decide +kernel)
def pv713243 : PrimeValue := ⟨713243, pr713243⟩
private theorem pr713261 : Nat.Prime 713261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv1877]) (by decide +kernel)
def pv713261 : PrimeValue := ⟨713261, pr713261⟩
private theorem pr713267 : Nat.Prime 713267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv5023]) (by decide +kernel)
def pv713267 : PrimeValue := ⟨713267, pr713267⟩
private theorem pr713281 : Nat.Prime 713281 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv743]) (by decide +kernel)
def pv713281 : PrimeValue := ⟨713281, pr713281⟩
private theorem pr713347 : Nat.Prime 713347 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv118891]) (by decide +kernel)
def pv713347 : PrimeValue := ⟨713347, pr713347⟩
private theorem pr713411 : Nat.Prime 713411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv71341]) (by decide +kernel)
def pv713411 : PrimeValue := ⟨713411, pr713411⟩
private theorem pr713417 : Nat.Prime 713417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv67]) (by decide +kernel)
def pv713417 : PrimeValue := ⟨713417, pr713417⟩
private theorem pr713597 : Nat.Prime 713597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv13723]) (by decide +kernel)
def pv713597 : PrimeValue := ⟨713597, pr713597⟩
private theorem pr713737 : Nat.Prime 713737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv431]) (by decide +kernel)
def pv713737 : PrimeValue := ⟨713737, pr713737⟩
private theorem pr713753 : Nat.Prime 713753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv6863]) (by decide +kernel)
def pv713753 : PrimeValue := ⟨713753, pr713753⟩
private theorem pr713941 : Nat.Prime 713941 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv73,pv163]) (by decide +kernel)
def pv713941 : PrimeValue := ⟨713941, pr713941⟩
private theorem pr713957 : Nat.Prime 713957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv178489]) (by decide +kernel)
def pv713957 : PrimeValue := ⟨713957, pr713957⟩
private theorem pr714073 : Nat.Prime 714073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29753]) (by decide +kernel)
def pv714073 : PrimeValue := ⟨714073, pr714073⟩
private theorem pr714223 : Nat.Prime 714223 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv39679]) (by decide +kernel)
def pv714223 : PrimeValue := ⟨714223, pr714223⟩
private theorem pr714257 : Nat.Prime 714257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv44641]) (by decide +kernel)
def pv714257 : PrimeValue := ⟨714257, pr714257⟩
private theorem pr714341 : Nat.Prime 714341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv17,pv191]) (by decide +kernel)
def pv714341 : PrimeValue := ⟨714341, pr714341⟩
private theorem pr714361 : Nat.Prime 714361 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv5953]) (by decide +kernel)
def pv714361 : PrimeValue := ⟨714361, pr714361⟩
private theorem pr714563 : Nat.Prime 714563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv357281]) (by decide +kernel)
def pv714563 : PrimeValue := ⟨714563, pr714563⟩
private theorem pr714601 : Nat.Prime 714601 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv397]) (by decide +kernel)
def pv714601 : PrimeValue := ⟨714601, pr714601⟩
private theorem pr714691 : Nat.Prime 714691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2647]) (by decide +kernel)
def pv714691 : PrimeValue := ⟨714691, pr714691⟩
private theorem pr714851 : Nat.Prime 714851 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv29]) (by decide +kernel)
def pv714851 : PrimeValue := ⟨714851, pr714851⟩
private theorem pr714947 : Nat.Prime 714947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv357473]) (by decide +kernel)
def pv714947 : PrimeValue := ⟨714947, pr714947⟩
private theorem pr715157 : Nat.Prime 715157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17,pv809]) (by decide +kernel)
def pv715157 : PrimeValue := ⟨715157, pr715157⟩
private theorem pr715397 : Nat.Prime 715397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv71,pv229]) (by decide +kernel)
def pv715397 : PrimeValue := ⟨715397, pr715397⟩
private theorem pr715453 : Nat.Prime 715453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59621]) (by decide +kernel)
def pv715453 : PrimeValue := ⟨715453, pr715453⟩
private theorem pr715577 : Nat.Prime 715577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv3889]) (by decide +kernel)
def pv715577 : PrimeValue := ⟨715577, pr715577⟩
private theorem pr715621 : Nat.Prime 715621 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv11927]) (by decide +kernel)
def pv715621 : PrimeValue := ⟨715621, pr715621⟩
private theorem pr715727 : Nat.Prime 715727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv32533]) (by decide +kernel)
def pv715727 : PrimeValue := ⟨715727, pr715727⟩
private theorem pr715811 : Nat.Prime 715811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv1523]) (by decide +kernel)
def pv715811 : PrimeValue := ⟨715811, pr715811⟩
private theorem pr715817 : Nat.Prime 715817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv89477]) (by decide +kernel)
def pv715817 : PrimeValue := ⟨715817, pr715817⟩
private theorem pr715843 : Nat.Prime 715843 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv39769]) (by decide +kernel)
def pv715843 : PrimeValue := ⟨715843, pr715843⟩
private theorem pr715927 : Nat.Prime 715927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv119321]) (by decide +kernel)
def pv715927 : PrimeValue := ⟨715927, pr715927⟩
private theorem pr716117 : Nat.Prime 716117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv179029]) (by decide +kernel)
def pv716117 : PrimeValue := ⟨716117, pr716117⟩
private theorem pr716123 : Nat.Prime 716123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv43,pv757]) (by decide +kernel)
def pv716123 : PrimeValue := ⟨716123, pr716123⟩
private theorem pr716137 : Nat.Prime 716137 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv53,pv563]) (by decide +kernel)
def pv716137 : PrimeValue := ⟨716137, pr716137⟩
private theorem pr716321 : Nat.Prime 716321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv37]) (by decide +kernel)
def pv716321 : PrimeValue := ⟨716321, pr716321⟩
private theorem pr716383 : Nat.Prime 716383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv39799]) (by decide +kernel)
def pv716383 : PrimeValue := ⟨716383, pr716383⟩
private theorem pr716447 : Nat.Prime 716447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv358223]) (by decide +kernel)
def pv716447 : PrimeValue := ⟨716447, pr716447⟩
private theorem pr716491 : Nat.Prime 716491 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv419]) (by decide +kernel)
def pv716491 : PrimeValue := ⟨716491, pr716491⟩
private theorem pr716501 : Nat.Prime 716501 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1433]) (by decide +kernel)
def pv716501 : PrimeValue := ⟨716501, pr716501⟩
private theorem pr716621 : Nat.Prime 716621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv35831]) (by decide +kernel)
def pv716621 : PrimeValue := ⟨716621, pr716621⟩
private theorem pr716713 : Nat.Prime 716713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29863]) (by decide +kernel)
def pv716713 : PrimeValue := ⟨716713, pr716713⟩
private theorem pr716741 : Nat.Prime 716741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv35837]) (by decide +kernel)
def pv716741 : PrimeValue := ⟨716741, pr716741⟩
private theorem pr716743 : Nat.Prime 716743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv1021]) (by decide +kernel)
def pv716743 : PrimeValue := ⟨716743, pr716743⟩
private theorem pr716827 : Nat.Prime 716827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv10861]) (by decide +kernel)
def pv716827 : PrimeValue := ⟨716827, pr716827⟩
private theorem pr717127 : Nat.Prime 717127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv2543]) (by decide +kernel)
def pv717127 : PrimeValue := ⟨717127, pr717127⟩
private theorem pr717133 : Nat.Prime 717133 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv4597]) (by decide +kernel)
def pv717133 : PrimeValue := ⟨717133, pr717133⟩
private theorem pr717463 : Nat.Prime 717463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv1733]) (by decide +kernel)
def pv717463 : PrimeValue := ⟨717463, pr717463⟩
private theorem pr717751 : Nat.Prime 717751 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv29]) (by decide +kernel)
def pv717751 : PrimeValue := ⟨717751, pr717751⟩
private theorem pr717811 : Nat.Prime 717811 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv71,pv337]) (by decide +kernel)
def pv717811 : PrimeValue := ⟨717811, pr717811⟩
private theorem pr717883 : Nat.Prime 717883 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv73,pv149]) (by decide +kernel)
def pv717883 : PrimeValue := ⟨717883, pr717883⟩
private theorem pr717887 : Nat.Prime 717887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv27611]) (by decide +kernel)
def pv717887 : PrimeValue := ⟨717887, pr717887⟩
private theorem pr717923 : Nat.Prime 717923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv15607]) (by decide +kernel)
def pv717923 : PrimeValue := ⟨717923, pr717923⟩
private theorem pr718007 : Nat.Prime 718007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv359003]) (by decide +kernel)
def pv718007 : PrimeValue := ⟨718007, pr718007⟩
private theorem pr718121 : Nat.Prime 718121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv1381]) (by decide +kernel)
def pv718121 : PrimeValue := ⟨718121, pr718121⟩
private theorem pr718303 : Nat.Prime 718303 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv13,pv9209]) (by decide +kernel)
def pv718303 : PrimeValue := ⟨718303, pr718303⟩
private theorem pr718321 : Nat.Prime 718321 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv41,pv73]) (by decide +kernel)
def pv718321 : PrimeValue := ⟨718321, pr718321⟩
private theorem pr718391 : Nat.Prime 718391 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv199]) (by decide +kernel)
def pv718391 : PrimeValue := ⟨718391, pr718391⟩
private theorem pr718427 : Nat.Prime 718427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv4547]) (by decide +kernel)
def pv718427 : PrimeValue := ⟨718427, pr718427⟩
private theorem pr718457 : Nat.Prime 718457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv2897]) (by decide +kernel)
def pv718457 : PrimeValue := ⟨718457, pr718457⟩
private theorem pr718541 : Nat.Prime 718541 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv37,pv971]) (by decide +kernel)
def pv718541 : PrimeValue := ⟨718541, pr718541⟩
private theorem pr718547 : Nat.Prime 718547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv443,pv811]) (by decide +kernel)
def pv718547 : PrimeValue := ⟨718547, pr718547⟩
private theorem pr718741 : Nat.Prime 718741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv718741 : PrimeValue := ⟨718741, pr718741⟩
private theorem pr718801 : Nat.Prime 718801 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv599]) (by decide +kernel)
def pv718801 : PrimeValue := ⟨718801, pr718801⟩
private theorem pr718813 : Nat.Prime 718813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv487]) (by decide +kernel)
def pv718813 : PrimeValue := ⟨718813, pr718813⟩
private theorem pr718897 : Nat.Prime 718897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv881]) (by decide +kernel)
def pv718897 : PrimeValue := ⟨718897, pr718897⟩
private theorem pr719177 : Nat.Prime 719177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv89897]) (by decide +kernel)
def pv719177 : PrimeValue := ⟨719177, pr719177⟩
private theorem pr719351 : Nat.Prime 719351 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv14387]) (by decide +kernel)
def pv719351 : PrimeValue := ⟨719351, pr719351⟩
private theorem pr719393 : Nat.Prime 719393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv22481]) (by decide +kernel)
def pv719393 : PrimeValue := ⟨719393, pr719393⟩
private theorem pr719567 : Nat.Prime 719567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv359783]) (by decide +kernel)
def pv719567 : PrimeValue := ⟨719567, pr719567⟩
private theorem pr719681 : Nat.Prime 719681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv173]) (by decide +kernel)
def pv719681 : PrimeValue := ⟨719681, pr719681⟩
private theorem pr719683 : Nat.Prime 719683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv59,pv107]) (by decide +kernel)
def pv719683 : PrimeValue := ⟨719683, pr719683⟩
private theorem pr719813 : Nat.Prime 719813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv179953]) (by decide +kernel)
def pv719813 : PrimeValue := ⟨719813, pr719813⟩
private theorem pr720403 : Nat.Prime 720403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv120067]) (by decide +kernel)
def pv720403 : PrimeValue := ⟨720403, pr720403⟩
private theorem pr720547 : Nat.Prime 720547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv120091]) (by decide +kernel)
def pv720547 : PrimeValue := ⟨720547, pr720547⟩
private theorem pr720571 : Nat.Prime 720571 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv24019]) (by decide +kernel)
def pv720571 : PrimeValue := ⟨720571, pr720571⟩
private theorem pr720607 : Nat.Prime 720607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv83,pv1447]) (by decide +kernel)
def pv720607 : PrimeValue := ⟨720607, pr720607⟩
private theorem pr720653 : Nat.Prime 720653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv2689]) (by decide +kernel)
def pv720653 : PrimeValue := ⟨720653, pr720653⟩
private theorem pr720677 : Nat.Prime 720677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1489]) (by decide +kernel)
def pv720677 : PrimeValue := ⟨720677, pr720677⟩
private theorem pr720857 : Nat.Prime 720857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv90107]) (by decide +kernel)
def pv720857 : PrimeValue := ⟨720857, pr720857⟩
private theorem pr720961 : Nat.Prime 720961 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv751]) (by decide +kernel)
def pv720961 : PrimeValue := ⟨720961, pr720961⟩
private theorem pr721013 : Nat.Prime 721013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv53,pv179]) (by decide +kernel)
def pv721013 : PrimeValue := ⟨721013, pr721013⟩
private theorem pr721111 : Nat.Prime 721111 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv43]) (by decide +kernel)
def pv721111 : PrimeValue := ⟨721111, pr721111⟩
private theorem pr721181 : Nat.Prime 721181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv107,pv337]) (by decide +kernel)
def pv721181 : PrimeValue := ⟨721181, pr721181⟩
private theorem pr721481 : Nat.Prime 721481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv1061]) (by decide +kernel)
def pv721481 : PrimeValue := ⟨721481, pr721481⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
