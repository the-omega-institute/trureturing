/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table202
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table202.pv640771
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table088
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table089

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr640771 : Nat.Prime 640771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv31,pv53]) (by decide +kernel)
def pv640771 : PrimeValue := ⟨640771, pr640771⟩
private theorem pr640853 : Nat.Prime 640853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv131,pv1223]) (by decide +kernel)
def pv640853 : PrimeValue := ⟨640853, pr640853⟩
private theorem pr641077 : Nat.Prime 641077 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv1303]) (by decide +kernel)
def pv641077 : PrimeValue := ⟨641077, pr641077⟩
private theorem pr641437 : Nat.Prime 641437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53453]) (by decide +kernel)
def pv641437 : PrimeValue := ⟨641437, pr641437⟩
private theorem pr641491 : Nat.Prime 641491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv21383]) (by decide +kernel)
def pv641491 : PrimeValue := ⟨641491, pr641491⟩
private theorem pr641521 : Nat.Prime 641521 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv641521 : PrimeValue := ⟨641521, pr641521⟩
private theorem pr641827 : Nat.Prime 641827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv181,pv197]) (by decide +kernel)
def pv641827 : PrimeValue := ⟨641827, pr641827⟩
private theorem pr641843 : Nat.Prime 641843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv5261]) (by decide +kernel)
def pv641843 : PrimeValue := ⟨641843, pr641843⟩
private theorem pr641863 : Nat.Prime 641863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv211]) (by decide +kernel)
def pv641863 : PrimeValue := ⟨641863, pr641863⟩
private theorem pr642011 : Nat.Prime 642011 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv31,pv109]) (by decide +kernel)
def pv642011 : PrimeValue := ⟨642011, pr642011⟩
private theorem pr642071 : Nat.Prime 642071 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv11,pv13,pv449]) (by decide +kernel)
def pv642071 : PrimeValue := ⟨642071, pr642071⟩
private theorem pr642151 : Nat.Prime 642151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1427]) (by decide +kernel)
def pv642151 : PrimeValue := ⟨642151, pr642151⟩
private theorem pr642197 : Nat.Prime 642197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv5179]) (by decide +kernel)
def pv642197 : PrimeValue := ⟨642197, pr642197⟩
private theorem pr642281 : Nat.Prime 642281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv16057]) (by decide +kernel)
def pv642281 : PrimeValue := ⟨642281, pr642281⟩
private theorem pr642361 : Nat.Prime 642361 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv53,pv101]) (by decide +kernel)
def pv642361 : PrimeValue := ⟨642361, pr642361⟩
private theorem pr642487 : Nat.Prime 642487 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv8237]) (by decide +kernel)
def pv642487 : PrimeValue := ⟨642487, pr642487⟩
private theorem pr642833 : Nat.Prime 642833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv40177]) (by decide +kernel)
def pv642833 : PrimeValue := ⟨642833, pr642833⟩
private theorem pr642907 : Nat.Prime 642907 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv17,pv191]) (by decide +kernel)
def pv642907 : PrimeValue := ⟨642907, pr642907⟩
private theorem pr642947 : Nat.Prime 642947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv563,pv571]) (by decide +kernel)
def pv642947 : PrimeValue := ⟨642947, pr642947⟩
private theorem pr642953 : Nat.Prime 642953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv80369]) (by decide +kernel)
def pv642953 : PrimeValue := ⟨642953, pr642953⟩
private theorem pr642977 : Nat.Prime 642977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv71,pv283]) (by decide +kernel)
def pv642977 : PrimeValue := ⟨642977, pr642977⟩
private theorem pr642997 : Nat.Prime 642997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv337]) (by decide +kernel)
def pv642997 : PrimeValue := ⟨642997, pr642997⟩
private theorem pr643043 : Nat.Prime 643043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv18913]) (by decide +kernel)
def pv643043 : PrimeValue := ⟨643043, pr643043⟩
private theorem pr643051 : Nat.Prime 643051 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1429]) (by decide +kernel)
def pv643051 : PrimeValue := ⟨643051, pr643051⟩
private theorem pr643061 : Nat.Prime 643061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv37,pv79]) (by decide +kernel)
def pv643061 : PrimeValue := ⟨643061, pr643061⟩
private theorem pr643081 : Nat.Prime 643081 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv233]) (by decide +kernel)
def pv643081 : PrimeValue := ⟨643081, pr643081⟩
private theorem pr643087 : Nat.Prime 643087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11909]) (by decide +kernel)
def pv643087 : PrimeValue := ⟨643087, pr643087⟩
private theorem pr643121 : Nat.Prime 643121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv8039]) (by decide +kernel)
def pv643121 : PrimeValue := ⟨643121, pr643121⟩
private theorem pr643183 : Nat.Prime 643183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv107197]) (by decide +kernel)
def pv643183 : PrimeValue := ⟨643183, pr643183⟩
private theorem pr643213 : Nat.Prime 643213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv1051]) (by decide +kernel)
def pv643213 : PrimeValue := ⟨643213, pr643213⟩
private theorem pr643303 : Nat.Prime 643303 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv19]) (by decide +kernel)
def pv643303 : PrimeValue := ⟨643303, pr643303⟩
private theorem pr643493 : Nat.Prime 643493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv8467]) (by decide +kernel)
def pv643493 : PrimeValue := ⟨643493, pr643493⟩
private theorem pr643681 : Nat.Prime 643681 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv149]) (by decide +kernel)
def pv643681 : PrimeValue := ⟨643681, pr643681⟩
private theorem pr643691 : Nat.Prime 643691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv1091]) (by decide +kernel)
def pv643691 : PrimeValue := ⟨643691, pr643691⟩
private theorem pr643703 : Nat.Prime 643703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv321851]) (by decide +kernel)
def pv643703 : PrimeValue := ⟨643703, pr643703⟩
private theorem pr644053 : Nat.Prime 644053 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv191,pv281]) (by decide +kernel)
def pv644053 : PrimeValue := ⟨644053, pr644053⟩
private theorem pr644101 : Nat.Prime 644101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv113]) (by decide +kernel)
def pv644101 : PrimeValue := ⟨644101, pr644101⟩
private theorem pr644117 : Nat.Prime 644117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv14639]) (by decide +kernel)
def pv644117 : PrimeValue := ⟨644117, pr644117⟩
private theorem pr644131 : Nat.Prime 644131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv421]) (by decide +kernel)
def pv644131 : PrimeValue := ⟨644131, pr644131⟩
private theorem pr644261 : Nat.Prime 644261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv32213]) (by decide +kernel)
def pv644261 : PrimeValue := ⟨644261, pr644261⟩
private theorem pr644291 : Nat.Prime 644291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv3391]) (by decide +kernel)
def pv644291 : PrimeValue := ⟨644291, pr644291⟩
private theorem pr644327 : Nat.Prime 644327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv113,pv2851]) (by decide +kernel)
def pv644327 : PrimeValue := ⟨644327, pr644327⟩
private theorem pr644377 : Nat.Prime 644377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv26849]) (by decide +kernel)
def pv644377 : PrimeValue := ⟨644377, pr644377⟩
private theorem pr644381 : Nat.Prime 644381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv29,pv101]) (by decide +kernel)
def pv644381 : PrimeValue := ⟨644381, pr644381⟩
private theorem pr644747 : Nat.Prime 644747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv47]) (by decide +kernel)
def pv644747 : PrimeValue := ⟨644747, pr644747⟩
private theorem pr644837 : Nat.Prime 644837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv4357]) (by decide +kernel)
def pv644837 : PrimeValue := ⟨644837, pr644837⟩
private theorem pr645367 : Nat.Prime 645367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv3709]) (by decide +kernel)
def pv645367 : PrimeValue := ⟨645367, pr645367⟩
private theorem pr645383 : Nat.Prime 645383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv523,pv617]) (by decide +kernel)
def pv645383 : PrimeValue := ⟨645383, pr645383⟩
private theorem pr645431 : Nat.Prime 645431 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv43,pv79]) (by decide +kernel)
def pv645431 : PrimeValue := ⟨645431, pr645431⟩
private theorem pr645481 : Nat.Prime 645481 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv11,pv163]) (by decide +kernel)
def pv645481 : PrimeValue := ⟨645481, pr645481⟩
private theorem pr645571 : Nat.Prime 645571 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv797]) (by decide +kernel)
def pv645571 : PrimeValue := ⟨645571, pr645571⟩
private theorem pr645641 : Nat.Prime 645641 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv16141]) (by decide +kernel)
def pv645641 : PrimeValue := ⟨645641, pr645641⟩
private theorem pr645683 : Nat.Prime 645683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv2857]) (by decide +kernel)
def pv645683 : PrimeValue := ⟨645683, pr645683⟩
private theorem pr645703 : Nat.Prime 645703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv4679]) (by decide +kernel)
def pv645703 : PrimeValue := ⟨645703, pr645703⟩
private theorem pr645713 : Nat.Prime 645713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv40357]) (by decide +kernel)
def pv645713 : PrimeValue := ⟨645713, pr645713⟩
private theorem pr645763 : Nat.Prime 645763 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv487]) (by decide +kernel)
def pv645763 : PrimeValue := ⟨645763, pr645763⟩
private theorem pr645787 : Nat.Prime 645787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11959]) (by decide +kernel)
def pv645787 : PrimeValue := ⟨645787, pr645787⟩
private theorem pr645857 : Nat.Prime 645857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv20183]) (by decide +kernel)
def pv645857 : PrimeValue := ⟨645857, pr645857⟩
private theorem pr645893 : Nat.Prime 645893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv12421]) (by decide +kernel)
def pv645893 : PrimeValue := ⟨645893, pr645893⟩
private theorem pr645901 : Nat.Prime 645901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2153]) (by decide +kernel)
def pv645901 : PrimeValue := ⟨645901, pr645901⟩
private theorem pr645937 : Nat.Prime 645937 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13457]) (by decide +kernel)
def pv645937 : PrimeValue := ⟨645937, pr645937⟩
private theorem pr646013 : Nat.Prime 646013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv161503]) (by decide +kernel)
def pv646013 : PrimeValue := ⟨646013, pr646013⟩
private theorem pr646067 : Nat.Prime 646067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv3019]) (by decide +kernel)
def pv646067 : PrimeValue := ⟨646067, pr646067⟩
private theorem pr646103 : Nat.Prime 646103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv31,pv613]) (by decide +kernel)
def pv646103 : PrimeValue := ⟨646103, pr646103⟩
private theorem pr646267 : Nat.Prime 646267 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19,pv5669]) (by decide +kernel)
def pv646267 : PrimeValue := ⟨646267, pr646267⟩
private theorem pr646757 : Nat.Prime 646757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv14699]) (by decide +kernel)
def pv646757 : PrimeValue := ⟨646757, pr646757⟩
private theorem pr646771 : Nat.Prime 646771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv21559]) (by decide +kernel)
def pv646771 : PrimeValue := ⟨646771, pr646771⟩
private theorem pr646873 : Nat.Prime 646873 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv26953]) (by decide +kernel)
def pv646873 : PrimeValue := ⟨646873, pr646873⟩
private theorem pr646883 : Nat.Prime 646883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv323441]) (by decide +kernel)
def pv646883 : PrimeValue := ⟨646883, pr646883⟩
private theorem pr646981 : Nat.Prime 646981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv41,pv263]) (by decide +kernel)
def pv646981 : PrimeValue := ⟨646981, pr646981⟩
private theorem pr646993 : Nat.Prime 646993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4493]) (by decide +kernel)
def pv646993 : PrimeValue := ⟨646993, pr646993⟩
private theorem pr647057 : Nat.Prime 647057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv1093]) (by decide +kernel)
def pv647057 : PrimeValue := ⟨647057, pr647057⟩
private theorem pr647111 : Nat.Prime 647111 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv163,pv397]) (by decide +kernel)
def pv647111 : PrimeValue := ⟨647111, pr647111⟩
private theorem pr647113 : Nat.Prime 647113 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv59,pv457]) (by decide +kernel)
def pv647113 : PrimeValue := ⟨647113, pr647113⟩
private theorem pr647131 : Nat.Prime 647131 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv37,pv53]) (by decide +kernel)
def pv647131 : PrimeValue := ⟨647131, pr647131⟩
private theorem pr647201 : Nat.Prime 647201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv809]) (by decide +kernel)
def pv647201 : PrimeValue := ⟨647201, pr647201⟩
private theorem pr647327 : Nat.Prime 647327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv79,pv241]) (by decide +kernel)
def pv647327 : PrimeValue := ⟨647327, pr647327⟩
private theorem pr647341 : Nat.Prime 647341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv10789]) (by decide +kernel)
def pv647341 : PrimeValue := ⟨647341, pr647341⟩
private theorem pr647401 : Nat.Prime 647401 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv83]) (by decide +kernel)
def pv647401 : PrimeValue := ⟨647401, pr647401⟩
private theorem pr647531 : Nat.Prime 647531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv17,pv293]) (by decide +kernel)
def pv647531 : PrimeValue := ⟨647531, pr647531⟩
private theorem pr647743 : Nat.Prime 647743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv89,pv1213]) (by decide +kernel)
def pv647743 : PrimeValue := ⟨647743, pr647743⟩
private theorem pr647783 : Nat.Prime 647783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv157,pv2063]) (by decide +kernel)
def pv647783 : PrimeValue := ⟨647783, pr647783⟩
private theorem pr647861 : Nat.Prime 647861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv1117]) (by decide +kernel)
def pv647861 : PrimeValue := ⟨647861, pr647861⟩
private theorem pr647951 : Nat.Prime 647951 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv12959]) (by decide +kernel)
def pv647951 : PrimeValue := ⟨647951, pr647951⟩
private theorem pr648101 : Nat.Prime 648101 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv6481]) (by decide +kernel)
def pv648101 : PrimeValue := ⟨648101, pr648101⟩
private theorem pr648391 : Nat.Prime 648391 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv21613]) (by decide +kernel)
def pv648391 : PrimeValue := ⟨648391, pr648391⟩
private theorem pr648563 : Nat.Prime 648563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv3907]) (by decide +kernel)
def pv648563 : PrimeValue := ⟨648563, pr648563⟩
private theorem pr648671 : Nat.Prime 648671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv5897]) (by decide +kernel)
def pv648671 : PrimeValue := ⟨648671, pr648671⟩
private theorem pr648731 : Nat.Prime 648731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv2237]) (by decide +kernel)
def pv648731 : PrimeValue := ⟨648731, pr648731⟩
private theorem pr648953 : Nat.Prime 648953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv81119]) (by decide +kernel)
def pv648953 : PrimeValue := ⟨648953, pr648953⟩
private theorem pr648997 : Nat.Prime 648997 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv54083]) (by decide +kernel)
def pv648997 : PrimeValue := ⟨648997, pr648997⟩
private theorem pr649007 : Nat.Prime 649007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv324503]) (by decide +kernel)
def pv649007 : PrimeValue := ⟨649007, pr649007⟩
private theorem pr649087 : Nat.Prime 649087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv251,pv431]) (by decide +kernel)
def pv649087 : PrimeValue := ⟨649087, pr649087⟩
private theorem pr649291 : Nat.Prime 649291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv941]) (by decide +kernel)
def pv649291 : PrimeValue := ⟨649291, pr649291⟩
private theorem pr649381 : Nat.Prime 649381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv79,pv137]) (by decide +kernel)
def pv649381 : PrimeValue := ⟨649381, pr649381⟩
private theorem pr649457 : Nat.Prime 649457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv40591]) (by decide +kernel)
def pv649457 : PrimeValue := ⟨649457, pr649457⟩
private theorem pr649487 : Nat.Prime 649487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv324743]) (by decide +kernel)
def pv649487 : PrimeValue := ⟨649487, pr649487⟩
private theorem pr649577 : Nat.Prime 649577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv81197]) (by decide +kernel)
def pv649577 : PrimeValue := ⟨649577, pr649577⟩
private theorem pr649633 : Nat.Prime 649633 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv67,pv101]) (by decide +kernel)
def pv649633 : PrimeValue := ⟨649633, pr649633⟩
private theorem pr649697 : Nat.Prime 649697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79,pv257]) (by decide +kernel)
def pv649697 : PrimeValue := ⟨649697, pr649697⟩
private theorem pr649717 : Nat.Prime 649717 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv1867]) (by decide +kernel)
def pv649717 : PrimeValue := ⟨649717, pr649717⟩
private theorem pr649751 : Nat.Prime 649751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv23,pv113]) (by decide +kernel)
def pv649751 : PrimeValue := ⟨649751, pr649751⟩
private theorem pr649813 : Nat.Prime 649813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv54151]) (by decide +kernel)
def pv649813 : PrimeValue := ⟨649813, pr649813⟩
private theorem pr649897 : Nat.Prime 649897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv2083]) (by decide +kernel)
def pv649897 : PrimeValue := ⟨649897, pr649897⟩
private theorem pr649921 : Nat.Prime 649921 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv677]) (by decide +kernel)
def pv649921 : PrimeValue := ⟨649921, pr649921⟩
private theorem pr649981 : Nat.Prime 649981 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv23,pv157]) (by decide +kernel)
def pv649981 : PrimeValue := ⟨649981, pr649981⟩
private theorem pr649991 : Nat.Prime 649991 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv19,pv311]) (by decide +kernel)
def pv649991 : PrimeValue := ⟨649991, pr649991⟩
private theorem pr650011 : Nat.Prime 650011 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv47,pv461]) (by decide +kernel)
def pv650011 : PrimeValue := ⟨650011, pr650011⟩
private theorem pr650227 : Nat.Prime 650227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv307,pv353]) (by decide +kernel)
def pv650227 : PrimeValue := ⟨650227, pr650227⟩
private theorem pr650537 : Nat.Prime 650537 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv233,pv349]) (by decide +kernel)
def pv650537 : PrimeValue := ⟨650537, pr650537⟩
private theorem pr650591 : Nat.Prime 650591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv43,pv89]) (by decide +kernel)
def pv650591 : PrimeValue := ⟨650591, pr650591⟩
private theorem pr650851 : Nat.Prime 650851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4339]) (by decide +kernel)
def pv650851 : PrimeValue := ⟨650851, pr650851⟩
private theorem pr650911 : Nat.Prime 650911 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv1669]) (by decide +kernel)
def pv650911 : PrimeValue := ⟨650911, pr650911⟩
private theorem pr650933 : Nat.Prime 650933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv353,pv461]) (by decide +kernel)
def pv650933 : PrimeValue := ⟨650933, pr650933⟩
private theorem pr651017 : Nat.Prime 651017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv4283]) (by decide +kernel)
def pv651017 : PrimeValue := ⟨651017, pr651017⟩
private theorem pr651193 : Nat.Prime 651193 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv43,pv631]) (by decide +kernel)
def pv651193 : PrimeValue := ⟨651193, pr651193⟩
private theorem pr651223 : Nat.Prime 651223 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv13,pv23]) (by decide +kernel)
def pv651223 : PrimeValue := ⟨651223, pr651223⟩
private theorem pr651331 : Nat.Prime 651331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7237]) (by decide +kernel)
def pv651331 : PrimeValue := ⟨651331, pr651331⟩
private theorem pr651347 : Nat.Prime 651347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv325673]) (by decide +kernel)
def pv651347 : PrimeValue := ⟨651347, pr651347⟩
private theorem pr651461 : Nat.Prime 651461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv32573]) (by decide +kernel)
def pv651461 : PrimeValue := ⟨651461, pr651461⟩
private theorem pr651481 : Nat.Prime 651481 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv61,pv89]) (by decide +kernel)
def pv651481 : PrimeValue := ⟨651481, pr651481⟩
private theorem pr651503 : Nat.Prime 651503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv325751]) (by decide +kernel)
def pv651503 : PrimeValue := ⟨651503, pr651503⟩
private theorem pr651587 : Nat.Prime 651587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv19,pv1319]) (by decide +kernel)
def pv651587 : PrimeValue := ⟨651587, pr651587⟩
private theorem pr651667 : Nat.Prime 651667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv313,pv347]) (by decide +kernel)
def pv651667 : PrimeValue := ⟨651667, pr651667⟩
private theorem pr651727 : Nat.Prime 651727 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv149]) (by decide +kernel)
def pv651727 : PrimeValue := ⟨651727, pr651727⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
