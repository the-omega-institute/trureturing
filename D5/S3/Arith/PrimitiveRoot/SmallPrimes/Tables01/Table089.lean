/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table089
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table089.pv322501
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table056

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr322501 : Nat.Prime 322501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv322501 : PrimeValue := ⟨322501, pr322501⟩
private theorem pr322513 : Nat.Prime 322513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6719]) (by decide +kernel)
def pv322513 : PrimeValue := ⟨322513, pr322513⟩
private theorem pr322519 : Nat.Prime 322519 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1097]) (by decide +kernel)
def pv322519 : PrimeValue := ⟨322519, pr322519⟩
private theorem pr322523 : Nat.Prime 322523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv131,pv1231]) (by decide +kernel)
def pv322523 : PrimeValue := ⟨322523, pr322523⟩
private theorem pr322537 : Nat.Prime 322537 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv89,pv151]) (by decide +kernel)
def pv322537 : PrimeValue := ⟨322537, pr322537⟩
private theorem pr322573 : Nat.Prime 322573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv26881]) (by decide +kernel)
def pv322573 : PrimeValue := ⟨322573, pr322573⟩
private theorem pr322589 : Nat.Prime 322589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv41,pv281]) (by decide +kernel)
def pv322589 : PrimeValue := ⟨322589, pr322589⟩
private theorem pr322607 : Nat.Prime 322607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv161303]) (by decide +kernel)
def pv322607 : PrimeValue := ⟨322607, pr322607⟩
private theorem pr322627 : Nat.Prime 322627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv3163]) (by decide +kernel)
def pv322627 : PrimeValue := ⟨322627, pr322627⟩
private theorem pr322631 : Nat.Prime 322631 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv419]) (by decide +kernel)
def pv322631 : PrimeValue := ⟨322631, pr322631⟩
private theorem pr322633 : Nat.Prime 322633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4481]) (by decide +kernel)
def pv322633 : PrimeValue := ⟨322633, pr322633⟩
private theorem pr322709 : Nat.Prime 322709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv80677]) (by decide +kernel)
def pv322709 : PrimeValue := ⟨322709, pr322709⟩
private theorem pr322807 : Nat.Prime 322807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv67,pv73]) (by decide +kernel)
def pv322807 : PrimeValue := ⟨322807, pr322807⟩
private theorem pr322871 : Nat.Prime 322871 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv83,pv389]) (by decide +kernel)
def pv322871 : PrimeValue := ⟨322871, pr322871⟩
private theorem pr322877 : Nat.Prime 322877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv1523]) (by decide +kernel)
def pv322877 : PrimeValue := ⟨322877, pr322877⟩
private theorem pr322901 : Nat.Prime 322901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3229]) (by decide +kernel)
def pv322901 : PrimeValue := ⟨322901, pr322901⟩
private theorem pr322919 : Nat.Prime 322919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv161459]) (by decide +kernel)
def pv322919 : PrimeValue := ⟨322919, pr322919⟩
private theorem pr322963 : Nat.Prime 322963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv2833]) (by decide +kernel)
def pv322963 : PrimeValue := ⟨322963, pr322963⟩
private theorem pr322969 : Nat.Prime 322969 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13457]) (by decide +kernel)
def pv322969 : PrimeValue := ⟨322969, pr322969⟩
private theorem pr323027 : Nat.Prime 323027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv14683]) (by decide +kernel)
def pv323027 : PrimeValue := ⟨323027, pr323027⟩
private theorem pr323053 : Nat.Prime 323053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv26921]) (by decide +kernel)
def pv323053 : PrimeValue := ⟨323053, pr323053⟩
private theorem pr323077 : Nat.Prime 323077 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv109]) (by decide +kernel)
def pv323077 : PrimeValue := ⟨323077, pr323077⟩
private theorem pr323083 : Nat.Prime 323083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv193]) (by decide +kernel)
def pv323083 : PrimeValue := ⟨323083, pr323083⟩
private theorem pr323131 : Nat.Prime 323131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv10771]) (by decide +kernel)
def pv323131 : PrimeValue := ⟨323131, pr323131⟩
private theorem pr323137 : Nat.Prime 323137 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv323137 : PrimeValue := ⟨323137, pr323137⟩
private theorem pr323149 : Nat.Prime 323149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv3847]) (by decide +kernel)
def pv323149 : PrimeValue := ⟨323149, pr323149⟩
private theorem pr323201 : Nat.Prime 323201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv101]) (by decide +kernel)
def pv323201 : PrimeValue := ⟨323201, pr323201⟩
private theorem pr323207 : Nat.Prime 323207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv31,pv401]) (by decide +kernel)
def pv323207 : PrimeValue := ⟨323207, pr323207⟩
private theorem pr323251 : Nat.Prime 323251 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv431]) (by decide +kernel)
def pv323251 : PrimeValue := ⟨323251, pr323251⟩
private theorem pr323333 : Nat.Prime 323333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv80833]) (by decide +kernel)
def pv323333 : PrimeValue := ⟨323333, pr323333⟩
private theorem pr323341 : Nat.Prime 323341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv317]) (by decide +kernel)
def pv323341 : PrimeValue := ⟨323341, pr323341⟩
private theorem pr323369 : Nat.Prime 323369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv83,pv487]) (by decide +kernel)
def pv323369 : PrimeValue := ⟨323369, pr323369⟩
private theorem pr323377 : Nat.Prime 323377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6737]) (by decide +kernel)
def pv323377 : PrimeValue := ⟨323377, pr323377⟩
private theorem pr323381 : Nat.Prime 323381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv23,pv37]) (by decide +kernel)
def pv323381 : PrimeValue := ⟨323381, pr323381⟩
private theorem pr323383 : Nat.Prime 323383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53897]) (by decide +kernel)
def pv323383 : PrimeValue := ⟨323383, pr323383⟩
private theorem pr323413 : Nat.Prime 323413 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv26951]) (by decide +kernel)
def pv323413 : PrimeValue := ⟨323413, pr323413⟩
private theorem pr323441 : Nat.Prime 323441 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv311]) (by decide +kernel)
def pv323441 : PrimeValue := ⟨323441, pr323441⟩
private theorem pr323467 : Nat.Prime 323467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv29]) (by decide +kernel)
def pv323467 : PrimeValue := ⟨323467, pr323467⟩
private theorem pr323509 : Nat.Prime 323509 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv26959]) (by decide +kernel)
def pv323509 : PrimeValue := ⟨323509, pr323509⟩
private theorem pr323537 : Nat.Prime 323537 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv73,pv277]) (by decide +kernel)
def pv323537 : PrimeValue := ⟨323537, pr323537⟩
private theorem pr323549 : Nat.Prime 323549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv1721]) (by decide +kernel)
def pv323549 : PrimeValue := ⟨323549, pr323549⟩
private theorem pr323567 : Nat.Prime 323567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv161783]) (by decide +kernel)
def pv323567 : PrimeValue := ⟨323567, pr323567⟩
private theorem pr323591 : Nat.Prime 323591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv32359]) (by decide +kernel)
def pv323591 : PrimeValue := ⟨323591, pr323591⟩
private theorem pr323623 : Nat.Prime 323623 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv461]) (by decide +kernel)
def pv323623 : PrimeValue := ⟨323623, pr323623⟩
private theorem pr323641 : Nat.Prime 323641 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv29,pv31]) (by decide +kernel)
def pv323641 : PrimeValue := ⟨323641, pr323641⟩
private theorem pr323651 : Nat.Prime 323651 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv6473]) (by decide +kernel)
def pv323651 : PrimeValue := ⟨323651, pr323651⟩
private theorem pr323699 : Nat.Prime 323699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv5581]) (by decide +kernel)
def pv323699 : PrimeValue := ⟨323699, pr323699⟩
private theorem pr323717 : Nat.Prime 323717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv80929]) (by decide +kernel)
def pv323717 : PrimeValue := ⟨323717, pr323717⟩
private theorem pr323767 : Nat.Prime 323767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17987]) (by decide +kernel)
def pv323767 : PrimeValue := ⟨323767, pr323767⟩
private theorem pr323789 : Nat.Prime 323789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv1327]) (by decide +kernel)
def pv323789 : PrimeValue := ⟨323789, pr323789⟩
private theorem pr323803 : Nat.Prime 323803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17989]) (by decide +kernel)
def pv323803 : PrimeValue := ⟨323803, pr323803⟩
private theorem pr323837 : Nat.Prime 323837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv4261]) (by decide +kernel)
def pv323837 : PrimeValue := ⟨323837, pr323837⟩
private theorem pr323903 : Nat.Prime 323903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv71,pv2281]) (by decide +kernel)
def pv323903 : PrimeValue := ⟨323903, pr323903⟩
private theorem pr323951 : Nat.Prime 323951 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv5,pv11,pv19,pv31]) (by decide +kernel)
def pv323951 : PrimeValue := ⟨323951, pr323951⟩
private theorem pr323957 : Nat.Prime 323957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv80989]) (by decide +kernel)
def pv323957 : PrimeValue := ⟨323957, pr323957⟩
private theorem pr323987 : Nat.Prime 323987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17,pv733]) (by decide +kernel)
def pv323987 : PrimeValue := ⟨323987, pr323987⟩
private theorem pr324011 : Nat.Prime 324011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv32401]) (by decide +kernel)
def pv324011 : PrimeValue := ⟨324011, pr324011⟩
private theorem pr324031 : Nat.Prime 324031 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv1543]) (by decide +kernel)
def pv324031 : PrimeValue := ⟨324031, pr324031⟩
private theorem pr324053 : Nat.Prime 324053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv81013]) (by decide +kernel)
def pv324053 : PrimeValue := ⟨324053, pr324053⟩
private theorem pr324073 : Nat.Prime 324073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv643]) (by decide +kernel)
def pv324073 : PrimeValue := ⟨324073, pr324073⟩
private theorem pr324097 : Nat.Prime 324097 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv211]) (by decide +kernel)
def pv324097 : PrimeValue := ⟨324097, pr324097⟩
private theorem pr324119 : Nat.Prime 324119 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv162059]) (by decide +kernel)
def pv324119 : PrimeValue := ⟨324119, pr324119⟩
private theorem pr324211 : Nat.Prime 324211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv101,pv107]) (by decide +kernel)
def pv324211 : PrimeValue := ⟨324211, pr324211⟩
private theorem pr324217 : Nat.Prime 324217 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv79]) (by decide +kernel)
def pv324217 : PrimeValue := ⟨324217, pr324217⟩
private theorem pr324419 : Nat.Prime 324419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv162209]) (by decide +kernel)
def pv324419 : PrimeValue := ⟨324419, pr324419⟩
private theorem pr324427 : Nat.Prime 324427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv139,pv389]) (by decide +kernel)
def pv324427 : PrimeValue := ⟨324427, pr324427⟩
private theorem pr324431 : Nat.Prime 324431 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv32443]) (by decide +kernel)
def pv324431 : PrimeValue := ⟨324431, pr324431⟩
private theorem pr324439 : Nat.Prime 324439 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv23,pv2351]) (by decide +kernel)
def pv324439 : PrimeValue := ⟨324439, pr324439⟩
private theorem pr324469 : Nat.Prime 324469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9013]) (by decide +kernel)
def pv324469 : PrimeValue := ⟨324469, pr324469⟩
private theorem pr324473 : Nat.Prime 324473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv40559]) (by decide +kernel)
def pv324473 : PrimeValue := ⟨324473, pr324473⟩
private theorem pr324491 : Nat.Prime 324491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv877]) (by decide +kernel)
def pv324491 : PrimeValue := ⟨324491, pr324491⟩
private theorem pr324503 : Nat.Prime 324503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv162251]) (by decide +kernel)
def pv324503 : PrimeValue := ⟨324503, pr324503⟩
private theorem pr324517 : Nat.Prime 324517 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv27043]) (by decide +kernel)
def pv324517 : PrimeValue := ⟨324517, pr324517⟩
private theorem pr324529 : Nat.Prime 324529 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv6761]) (by decide +kernel)
def pv324529 : PrimeValue := ⟨324529, pr324529⟩
private theorem pr324589 : Nat.Prime 324589 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv2459]) (by decide +kernel)
def pv324589 : PrimeValue := ⟨324589, pr324589⟩
private theorem pr324617 : Nat.Prime 324617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv40577]) (by decide +kernel)
def pv324617 : PrimeValue := ⟨324617, pr324617⟩
private theorem pr324641 : Nat.Prime 324641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2029]) (by decide +kernel)
def pv324641 : PrimeValue := ⟨324641, pr324641⟩
private theorem pr324689 : Nat.Prime 324689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv223]) (by decide +kernel)
def pv324689 : PrimeValue := ⟨324689, pr324689⟩
private theorem pr324697 : Nat.Prime 324697 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv83,pv163]) (by decide +kernel)
def pv324697 : PrimeValue := ⟨324697, pr324697⟩
private theorem pr324733 : Nat.Prime 324733 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv27061]) (by decide +kernel)
def pv324733 : PrimeValue := ⟨324733, pr324733⟩
private theorem pr324743 : Nat.Prime 324743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv29,pv509]) (by decide +kernel)
def pv324743 : PrimeValue := ⟨324743, pr324743⟩
private theorem pr324757 : Nat.Prime 324757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv97]) (by decide +kernel)
def pv324757 : PrimeValue := ⟨324757, pr324757⟩
private theorem pr324763 : Nat.Prime 324763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv113,pv479]) (by decide +kernel)
def pv324763 : PrimeValue := ⟨324763, pr324763⟩
private theorem pr324791 : Nat.Prime 324791 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv32479]) (by decide +kernel)
def pv324791 : PrimeValue := ⟨324791, pr324791⟩
private theorem pr324809 : Nat.Prime 324809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv3691]) (by decide +kernel)
def pv324809 : PrimeValue := ⟨324809, pr324809⟩
private theorem pr324811 : Nat.Prime 324811 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv401]) (by decide +kernel)
def pv324811 : PrimeValue := ⟨324811, pr324811⟩
private theorem pr324869 : Nat.Prime 324869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv241,pv337]) (by decide +kernel)
def pv324869 : PrimeValue := ⟨324869, pr324869⟩
private theorem pr324889 : Nat.Prime 324889 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13537]) (by decide +kernel)
def pv324889 : PrimeValue := ⟨324889, pr324889⟩
private theorem pr324893 : Nat.Prime 324893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv81223]) (by decide +kernel)
def pv324893 : PrimeValue := ⟨324893, pr324893⟩
private theorem pr324953 : Nat.Prime 324953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv151,pv269]) (by decide +kernel)
def pv324953 : PrimeValue := ⟨324953, pr324953⟩
private theorem pr324979 : Nat.Prime 324979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv54163]) (by decide +kernel)
def pv324979 : PrimeValue := ⟨324979, pr324979⟩
private theorem pr324991 : Nat.Prime 324991 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv157]) (by decide +kernel)
def pv324991 : PrimeValue := ⟨324991, pr324991⟩
private theorem pr324997 : Nat.Prime 324997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv53,pv73]) (by decide +kernel)
def pv324997 : PrimeValue := ⟨324997, pr324997⟩
private theorem pr325021 : Nat.Prime 325021 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv5417]) (by decide +kernel)
def pv325021 : PrimeValue := ⟨325021, pr325021⟩
private theorem pr325063 : Nat.Prime 325063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv18059]) (by decide +kernel)
def pv325063 : PrimeValue := ⟨325063, pr325063⟩
private theorem pr325081 : Nat.Prime 325081 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv43]) (by decide +kernel)
def pv325081 : PrimeValue := ⟨325081, pr325081⟩
private theorem pr325153 : Nat.Prime 325153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1129]) (by decide +kernel)
def pv325153 : PrimeValue := ⟨325153, pr325153⟩
private theorem pr325163 : Nat.Prime 325163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv367,pv443]) (by decide +kernel)
def pv325163 : PrimeValue := ⟨325163, pr325163⟩
private theorem pr325187 : Nat.Prime 325187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv162593]) (by decide +kernel)
def pv325187 : PrimeValue := ⟨325187, pr325187⟩
private theorem pr325189 : Nat.Prime 325189 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv3011]) (by decide +kernel)
def pv325189 : PrimeValue := ⟨325189, pr325189⟩
private theorem pr325217 : Nat.Prime 325217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10163]) (by decide +kernel)
def pv325217 : PrimeValue := ⟨325217, pr325217⟩
private theorem pr325219 : Nat.Prime 325219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv809]) (by decide +kernel)
def pv325219 : PrimeValue := ⟨325219, pr325219⟩
private theorem pr325231 : Nat.Prime 325231 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv37,pv293]) (by decide +kernel)
def pv325231 : PrimeValue := ⟨325231, pr325231⟩
private theorem pr325249 : Nat.Prime 325249 :=
  checkPrime_prime (q := pv53) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv325249 : PrimeValue := ⟨325249, pr325249⟩
private theorem pr325271 : Nat.Prime 325271 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv2957]) (by decide +kernel)
def pv325271 : PrimeValue := ⟨325271, pr325271⟩
private theorem pr325307 : Nat.Prime 325307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv311,pv523]) (by decide +kernel)
def pv325307 : PrimeValue := ⟨325307, pr325307⟩
private theorem pr325309 : Nat.Prime 325309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv27109]) (by decide +kernel)
def pv325309 : PrimeValue := ⟨325309, pr325309⟩
private theorem pr325349 : Nat.Prime 325349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163,pv499]) (by decide +kernel)
def pv325349 : PrimeValue := ⟨325349, pr325349⟩
private theorem pr325379 : Nat.Prime 325379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv4397]) (by decide +kernel)
def pv325379 : PrimeValue := ⟨325379, pr325379⟩
private theorem pr325421 : Nat.Prime 325421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv53,pv307]) (by decide +kernel)
def pv325421 : PrimeValue := ⟨325421, pr325421⟩
private theorem pr325459 : Nat.Prime 325459 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv41]) (by decide +kernel)
def pv325459 : PrimeValue := ⟨325459, pr325459⟩
private theorem pr325463 : Nat.Prime 325463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv162731]) (by decide +kernel)
def pv325463 : PrimeValue := ⟨325463, pr325463⟩
private theorem pr325487 : Nat.Prime 325487 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv67,pv347]) (by decide +kernel)
def pv325487 : PrimeValue := ⟨325487, pr325487⟩
private theorem pr325543 : Nat.Prime 325543 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv23,pv337]) (by decide +kernel)
def pv325543 : PrimeValue := ⟨325543, pr325543⟩
private theorem pr325571 : Nat.Prime 325571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv4651]) (by decide +kernel)
def pv325571 : PrimeValue := ⟨325571, pr325571⟩
private theorem pr325597 : Nat.Prime 325597 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv43,pv631]) (by decide +kernel)
def pv325597 : PrimeValue := ⟨325597, pr325597⟩
private theorem pr325607 : Nat.Prime 325607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv71,pv2293]) (by decide +kernel)
def pv325607 : PrimeValue := ⟨325607, pr325607⟩
private theorem pr325667 : Nat.Prime 325667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv113,pv131]) (by decide +kernel)
def pv325667 : PrimeValue := ⟨325667, pr325667⟩
private theorem pr325673 : Nat.Prime 325673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv40709]) (by decide +kernel)
def pv325673 : PrimeValue := ⟨325673, pr325673⟩
private theorem pr325681 : Nat.Prime 325681 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv59]) (by decide +kernel)
def pv325681 : PrimeValue := ⟨325681, pr325681⟩
private theorem pr325691 : Nat.Prime 325691 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv32569]) (by decide +kernel)
def pv325691 : PrimeValue := ⟨325691, pr325691⟩
private theorem pr325693 : Nat.Prime 325693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv109]) (by decide +kernel)
def pv325693 : PrimeValue := ⟨325693, pr325693⟩
private theorem pr325723 : Nat.Prime 325723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv54287]) (by decide +kernel)
def pv325723 : PrimeValue := ⟨325723, pr325723⟩
private theorem pr325729 : Nat.Prime 325729 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv13,pv29]) (by decide +kernel)
def pv325729 : PrimeValue := ⟨325729, pr325729⟩
private theorem pr325747 : Nat.Prime 325747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18097]) (by decide +kernel)
def pv325747 : PrimeValue := ⟨325747, pr325747⟩
private theorem pr325751 : Nat.Prime 325751 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv1303]) (by decide +kernel)
def pv325751 : PrimeValue := ⟨325751, pr325751⟩
private theorem pr325753 : Nat.Prime 325753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv277]) (by decide +kernel)
def pv325753 : PrimeValue := ⟨325753, pr325753⟩
private theorem pr325777 : Nat.Prime 325777 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv617]) (by decide +kernel)
def pv325777 : PrimeValue := ⟨325777, pr325777⟩
private theorem pr325783 : Nat.Prime 325783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2011]) (by decide +kernel)
def pv325783 : PrimeValue := ⟨325783, pr325783⟩
private theorem pr325849 : Nat.Prime 325849 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13577]) (by decide +kernel)
def pv325849 : PrimeValue := ⟨325849, pr325849⟩
private theorem pr325883 : Nat.Prime 325883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127,pv1283]) (by decide +kernel)
def pv325883 : PrimeValue := ⟨325883, pr325883⟩
private theorem pr325891 : Nat.Prime 325891 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv71]) (by decide +kernel)
def pv325891 : PrimeValue := ⟨325891, pr325891⟩
private theorem pr325901 : Nat.Prime 325901 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3259]) (by decide +kernel)
def pv325901 : PrimeValue := ⟨325901, pr325901⟩
private theorem pr325921 : Nat.Prime 325921 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv7,pv97]) (by decide +kernel)
def pv325921 : PrimeValue := ⟨325921, pr325921⟩
private theorem pr325993 : Nat.Prime 325993 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv47]) (by decide +kernel)
def pv325993 : PrimeValue := ⟨325993, pr325993⟩
private theorem pr326113 : Nat.Prime 326113 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv43,pv79]) (by decide +kernel)
def pv326113 : PrimeValue := ⟨326113, pr326113⟩
private theorem pr326119 : Nat.Prime 326119 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv37,pv113]) (by decide +kernel)
def pv326119 : PrimeValue := ⟨326119, pr326119⟩
private theorem pr326141 : Nat.Prime 326141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv709]) (by decide +kernel)
def pv326141 : PrimeValue := ⟨326141, pr326141⟩
private theorem pr326143 : Nat.Prime 326143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv18119]) (by decide +kernel)
def pv326143 : PrimeValue := ⟨326143, pr326143⟩
private theorem pr326147 : Nat.Prime 326147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv313,pv521]) (by decide +kernel)
def pv326147 : PrimeValue := ⟨326147, pr326147⟩
private theorem pr326149 : Nat.Prime 326149 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv27179]) (by decide +kernel)
def pv326149 : PrimeValue := ⟨326149, pr326149⟩
private theorem pr326159 : Nat.Prime 326159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv23297]) (by decide +kernel)
def pv326159 : PrimeValue := ⟨326159, pr326159⟩
private theorem pr326171 : Nat.Prime 326171 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv13,pv193]) (by decide +kernel)
def pv326171 : PrimeValue := ⟨326171, pr326171⟩
private theorem pr326189 : Nat.Prime 326189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv81547]) (by decide +kernel)
def pv326189 : PrimeValue := ⟨326189, pr326189⟩
private theorem pr326219 : Nat.Prime 326219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163109]) (by decide +kernel)
def pv326219 : PrimeValue := ⟨326219, pr326219⟩
private theorem pr326309 : Nat.Prime 326309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv97]) (by decide +kernel)
def pv326309 : PrimeValue := ⟨326309, pr326309⟩
private theorem pr326323 : Nat.Prime 326323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6043]) (by decide +kernel)
def pv326323 : PrimeValue := ⟨326323, pr326323⟩
private theorem pr326351 : Nat.Prime 326351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv61,pv107]) (by decide +kernel)
def pv326351 : PrimeValue := ⟨326351, pr326351⟩
private theorem pr326369 : Nat.Prime 326369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv31,pv47]) (by decide +kernel)
def pv326369 : PrimeValue := ⟨326369, pr326369⟩
private theorem pr326437 : Nat.Prime 326437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv2473]) (by decide +kernel)
def pv326437 : PrimeValue := ⟨326437, pr326437⟩
private theorem pr326441 : Nat.Prime 326441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv8161]) (by decide +kernel)
def pv326441 : PrimeValue := ⟨326441, pr326441⟩
private theorem pr326449 : Nat.Prime 326449 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv2267]) (by decide +kernel)
def pv326449 : PrimeValue := ⟨326449, pr326449⟩
private theorem pr326467 : Nat.Prime 326467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2591]) (by decide +kernel)
def pv326467 : PrimeValue := ⟨326467, pr326467⟩
private theorem pr326503 : Nat.Prime 326503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv97]) (by decide +kernel)
def pv326503 : PrimeValue := ⟨326503, pr326503⟩
private theorem pr326537 : Nat.Prime 326537 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17]) (by decide +kernel)
def pv326537 : PrimeValue := ⟨326537, pr326537⟩
private theorem pr326539 : Nat.Prime 326539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6047]) (by decide +kernel)
def pv326539 : PrimeValue := ⟨326539, pr326539⟩
private theorem pr326563 : Nat.Prime 326563 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv1471]) (by decide +kernel)
def pv326563 : PrimeValue := ⟨326563, pr326563⟩
private theorem pr326567 : Nat.Prime 326567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv269,pv607]) (by decide +kernel)
def pv326567 : PrimeValue := ⟨326567, pr326567⟩
private theorem pr326581 : Nat.Prime 326581 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv5443]) (by decide +kernel)
def pv326581 : PrimeValue := ⟨326581, pr326581⟩
private theorem pr326593 : Nat.Prime 326593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv326593 : PrimeValue := ⟨326593, pr326593⟩
private theorem pr326597 : Nat.Prime 326597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv81649]) (by decide +kernel)
def pv326597 : PrimeValue := ⟨326597, pr326597⟩
private theorem pr326609 : Nat.Prime 326609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv137,pv149]) (by decide +kernel)
def pv326609 : PrimeValue := ⟨326609, pr326609⟩
private theorem pr326633 : Nat.Prime 326633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv40829]) (by decide +kernel)
def pv326633 : PrimeValue := ⟨326633, pr326633⟩
private theorem pr326657 : Nat.Prime 326657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv29]) (by decide +kernel)
def pv326657 : PrimeValue := ⟨326657, pr326657⟩
private theorem pr326659 : Nat.Prime 326659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv54443]) (by decide +kernel)
def pv326659 : PrimeValue := ⟨326659, pr326659⟩
private theorem pr326681 : Nat.Prime 326681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv8167]) (by decide +kernel)
def pv326681 : PrimeValue := ⟨326681, pr326681⟩
private theorem pr326707 : Nat.Prime 326707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv3203]) (by decide +kernel)
def pv326707 : PrimeValue := ⟨326707, pr326707⟩
private theorem pr326737 : Nat.Prime 326737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2269]) (by decide +kernel)
def pv326737 : PrimeValue := ⟨326737, pr326737⟩
private theorem pr326741 : Nat.Prime 326741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv31]) (by decide +kernel)
def pv326741 : PrimeValue := ⟨326741, pr326741⟩
private theorem pr326773 : Nat.Prime 326773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv313]) (by decide +kernel)
def pv326773 : PrimeValue := ⟨326773, pr326773⟩
private theorem pr326903 : Nat.Prime 326903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv79,pv2069]) (by decide +kernel)
def pv326903 : PrimeValue := ⟨326903, pr326903⟩
private theorem pr326923 : Nat.Prime 326923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv103]) (by decide +kernel)
def pv326923 : PrimeValue := ⟨326923, pr326923⟩
private theorem pr326939 : Nat.Prime 326939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163469]) (by decide +kernel)
def pv326939 : PrimeValue := ⟨326939, pr326939⟩
private theorem pr326947 : Nat.Prime 326947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv1879]) (by decide +kernel)
def pv326947 : PrimeValue := ⟨326947, pr326947⟩
private theorem pr326951 : Nat.Prime 326951 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv503]) (by decide +kernel)
def pv326951 : PrimeValue := ⟨326951, pr326951⟩
private theorem pr326983 : Nat.Prime 326983 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv54497]) (by decide +kernel)
def pv326983 : PrimeValue := ⟨326983, pr326983⟩
private theorem pr327007 : Nat.Prime 327007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv491]) (by decide +kernel)
def pv327007 : PrimeValue := ⟨327007, pr327007⟩
private theorem pr327011 : Nat.Prime 327011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv53,pv617]) (by decide +kernel)
def pv327011 : PrimeValue := ⟨327011, pr327011⟩
private theorem pr327023 : Nat.Prime 327023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv113,pv1447]) (by decide +kernel)
def pv327023 : PrimeValue := ⟨327023, pr327023⟩
private theorem pr327127 : Nat.Prime 327127 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv54521]) (by decide +kernel)
def pv327127 : PrimeValue := ⟨327127, pr327127⟩
private theorem pr327193 : Nat.Prime 327193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13633]) (by decide +kernel)
def pv327193 : PrimeValue := ⟨327193, pr327193⟩
private theorem pr327203 : Nat.Prime 327203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163601]) (by decide +kernel)
def pv327203 : PrimeValue := ⟨327203, pr327203⟩
private theorem pr327209 : Nat.Prime 327209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv5843]) (by decide +kernel)
def pv327209 : PrimeValue := ⟨327209, pr327209⟩
private theorem pr327211 : Nat.Prime 327211 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv839]) (by decide +kernel)
def pv327211 : PrimeValue := ⟨327211, pr327211⟩
private theorem pr327263 : Nat.Prime 327263 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv13,pv41,pv307]) (by decide +kernel)
def pv327263 : PrimeValue := ⟨327263, pr327263⟩
private theorem pr327311 : Nat.Prime 327311 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv71,pv461]) (by decide +kernel)
def pv327311 : PrimeValue := ⟨327311, pr327311⟩
private theorem pr327317 : Nat.Prime 327317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv43,pv173]) (by decide +kernel)
def pv327317 : PrimeValue := ⟨327317, pr327317⟩
private theorem pr327319 : Nat.Prime 327319 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv3209]) (by decide +kernel)
def pv327319 : PrimeValue := ⟨327319, pr327319⟩
private theorem pr327337 : Nat.Prime 327337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv593]) (by decide +kernel)
def pv327337 : PrimeValue := ⟨327337, pr327337⟩
private theorem pr327343 : Nat.Prime 327343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv89,pv613]) (by decide +kernel)
def pv327343 : PrimeValue := ⟨327343, pr327343⟩
private theorem pr327401 : Nat.Prime 327401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1637]) (by decide +kernel)
def pv327401 : PrimeValue := ⟨327401, pr327401⟩
private theorem pr327407 : Nat.Prime 327407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv127,pv1289]) (by decide +kernel)
def pv327407 : PrimeValue := ⟨327407, pr327407⟩
private theorem pr327419 : Nat.Prime 327419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv257]) (by decide +kernel)
def pv327419 : PrimeValue := ⟨327419, pr327419⟩
private theorem pr327433 : Nat.Prime 327433 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv1949]) (by decide +kernel)
def pv327433 : PrimeValue := ⟨327433, pr327433⟩
private theorem pr327443 : Nat.Prime 327443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv1621]) (by decide +kernel)
def pv327443 : PrimeValue := ⟨327443, pr327443⟩
private theorem pr327469 : Nat.Prime 327469 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv29,pv941]) (by decide +kernel)
def pv327469 : PrimeValue := ⟨327469, pr327469⟩
private theorem pr327479 : Nat.Prime 327479 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv73,pv2243]) (by decide +kernel)
def pv327479 : PrimeValue := ⟨327479, pr327479⟩
private theorem pr327491 : Nat.Prime 327491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv32749]) (by decide +kernel)
def pv327491 : PrimeValue := ⟨327491, pr327491⟩
private theorem pr327529 : Nat.Prime 327529 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv4549]) (by decide +kernel)
def pv327529 : PrimeValue := ⟨327529, pr327529⟩
private theorem pr327571 : Nat.Prime 327571 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv61,pv179]) (by decide +kernel)
def pv327571 : PrimeValue := ⟨327571, pr327571⟩
private theorem pr327629 : Nat.Prime 327629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11701]) (by decide +kernel)
def pv327629 : PrimeValue := ⟨327629, pr327629⟩
private theorem pr327647 : Nat.Prime 327647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv53,pv281]) (by decide +kernel)
def pv327647 : PrimeValue := ⟨327647, pr327647⟩
private theorem pr327661 : Nat.Prime 327661 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv43,pv127]) (by decide +kernel)
def pv327661 : PrimeValue := ⟨327661, pr327661⟩
private theorem pr327667 : Nat.Prime 327667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv97,pv563]) (by decide +kernel)
def pv327667 : PrimeValue := ⟨327667, pr327667⟩
private theorem pr327673 : Nat.Prime 327673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv41]) (by decide +kernel)
def pv327673 : PrimeValue := ⟨327673, pr327673⟩
private theorem pr327689 : Nat.Prime 327689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv40961]) (by decide +kernel)
def pv327689 : PrimeValue := ⟨327689, pr327689⟩
private theorem pr327737 : Nat.Prime 327737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv71,pv577]) (by decide +kernel)
def pv327737 : PrimeValue := ⟨327737, pr327737⟩
private theorem pr327757 : Nat.Prime 327757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv191]) (by decide +kernel)
def pv327757 : PrimeValue := ⟨327757, pr327757⟩
private theorem pr327779 : Nat.Prime 327779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv47,pv317]) (by decide +kernel)
def pv327779 : PrimeValue := ⟨327779, pr327779⟩
private theorem pr327797 : Nat.Prime 327797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv509]) (by decide +kernel)
def pv327797 : PrimeValue := ⟨327797, pr327797⟩
private theorem pr327827 : Nat.Prime 327827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv8627]) (by decide +kernel)
def pv327827 : PrimeValue := ⟨327827, pr327827⟩
private theorem pr327829 : Nat.Prime 327829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv1607]) (by decide +kernel)
def pv327829 : PrimeValue := ⟨327829, pr327829⟩
private theorem pr327851 : Nat.Prime 327851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv79,pv83]) (by decide +kernel)
def pv327851 : PrimeValue := ⟨327851, pr327851⟩
private theorem pr327853 : Nat.Prime 327853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1301]) (by decide +kernel)
def pv327853 : PrimeValue := ⟨327853, pr327853⟩
private theorem pr327923 : Nat.Prime 327923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv59,pv397]) (by decide +kernel)
def pv327923 : PrimeValue := ⟨327923, pr327923⟩
private theorem pr327941 : Nat.Prime 327941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv863]) (by decide +kernel)
def pv327941 : PrimeValue := ⟨327941, pr327941⟩
private theorem pr327967 : Nat.Prime 327967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv1163]) (by decide +kernel)
def pv327967 : PrimeValue := ⟨327967, pr327967⟩
private theorem pr327979 : Nat.Prime 327979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv137]) (by decide +kernel)
def pv327979 : PrimeValue := ⟨327979, pr327979⟩
private theorem pr328067 : Nat.Prime 328067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv9649]) (by decide +kernel)
def pv328067 : PrimeValue := ⟨328067, pr328067⟩
private theorem pr328093 : Nat.Prime 328093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1439]) (by decide +kernel)
def pv328093 : PrimeValue := ⟨328093, pr328093⟩
private theorem pr328127 : Nat.Prime 328127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv359,pv457]) (by decide +kernel)
def pv328127 : PrimeValue := ⟨328127, pr328127⟩
private theorem pr328129 : Nat.Prime 328129 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv1709]) (by decide +kernel)
def pv328129 : PrimeValue := ⟨328129, pr328129⟩
private theorem pr328213 : Nat.Prime 328213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1013]) (by decide +kernel)
def pv328213 : PrimeValue := ⟨328213, pr328213⟩
private theorem pr328243 : Nat.Prime 328243 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv227,pv241]) (by decide +kernel)
def pv328243 : PrimeValue := ⟨328243, pr328243⟩
private theorem pr328283 : Nat.Prime 328283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv53,pv163]) (by decide +kernel)
def pv328283 : PrimeValue := ⟨328283, pr328283⟩
private theorem pr328303 : Nat.Prime 328303 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv13,pv23,pv61]) (by decide +kernel)
def pv328303 : PrimeValue := ⟨328303, pr328303⟩
private theorem pr328327 : Nat.Prime 328327 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv54721]) (by decide +kernel)
def pv328327 : PrimeValue := ⟨328327, pr328327⟩
private theorem pr328331 : Nat.Prime 328331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv32833]) (by decide +kernel)
def pv328331 : PrimeValue := ⟨328331, pr328331⟩
private theorem pr328343 : Nat.Prime 328343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv47,pv499]) (by decide +kernel)
def pv328343 : PrimeValue := ⟨328343, pr328343⟩
private theorem pr328357 : Nat.Prime 328357 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv1303]) (by decide +kernel)
def pv328357 : PrimeValue := ⟨328357, pr328357⟩
private theorem pr328411 : Nat.Prime 328411 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv41,pv89]) (by decide +kernel)
def pv328411 : PrimeValue := ⟨328411, pr328411⟩
private theorem pr328511 : Nat.Prime 328511 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv13,pv19]) (by decide +kernel)
def pv328511 : PrimeValue := ⟨328511, pr328511⟩
private theorem pr328543 : Nat.Prime 328543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv3221]) (by decide +kernel)
def pv328543 : PrimeValue := ⟨328543, pr328543⟩
private theorem pr328579 : Nat.Prime 328579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv2381]) (by decide +kernel)
def pv328579 : PrimeValue := ⟨328579, pr328579⟩
private theorem pr328589 : Nat.Prime 328589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv71,pv89]) (by decide +kernel)
def pv328589 : PrimeValue := ⟨328589, pr328589⟩
private theorem pr328619 : Nat.Prime 328619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv164309]) (by decide +kernel)
def pv328619 : PrimeValue := ⟨328619, pr328619⟩
private theorem pr328621 : Nat.Prime 328621 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv5477]) (by decide +kernel)
def pv328621 : PrimeValue := ⟨328621, pr328621⟩
private theorem pr328633 : Nat.Prime 328633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13693]) (by decide +kernel)
def pv328633 : PrimeValue := ⟨328633, pr328633⟩
private theorem pr328639 : Nat.Prime 328639 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv54773]) (by decide +kernel)
def pv328639 : PrimeValue := ⟨328639, pr328639⟩
private theorem pr328651 : Nat.Prime 328651 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv313]) (by decide +kernel)
def pv328651 : PrimeValue := ⟨328651, pr328651⟩
private theorem pr328687 : Nat.Prime 328687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv1889]) (by decide +kernel)
def pv328687 : PrimeValue := ⟨328687, pr328687⟩
private theorem pr328777 : Nat.Prime 328777 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv19,pv103]) (by decide +kernel)
def pv328777 : PrimeValue := ⟨328777, pr328777⟩
private theorem pr328813 : Nat.Prime 328813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv47,pv53]) (by decide +kernel)
def pv328813 : PrimeValue := ⟨328813, pr328813⟩
private theorem pr328829 : Nat.Prime 328829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv82207]) (by decide +kernel)
def pv328829 : PrimeValue := ⟨328829, pr328829⟩
private theorem pr328837 : Nat.Prime 328837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv409]) (by decide +kernel)
def pv328837 : PrimeValue := ⟨328837, pr328837⟩
private theorem pr328849 : Nat.Prime 328849 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv17,pv31]) (by decide +kernel)
def pv328849 : PrimeValue := ⟨328849, pr328849⟩
private theorem pr328883 : Nat.Prime 328883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv569]) (by decide +kernel)
def pv328883 : PrimeValue := ⟨328883, pr328883⟩
private theorem pr328891 : Nat.Prime 328891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv577]) (by decide +kernel)
def pv328891 : PrimeValue := ⟨328891, pr328891⟩
private theorem pr328901 : Nat.Prime 328901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv23]) (by decide +kernel)
def pv328901 : PrimeValue := ⟨328901, pr328901⟩
private theorem pr328921 : Nat.Prime 328921 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv2741]) (by decide +kernel)
def pv328921 : PrimeValue := ⟨328921, pr328921⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
