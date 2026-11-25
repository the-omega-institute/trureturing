/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table089
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table089.pv322501
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table056

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr322501 : PrimeCertificate 322501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv322501 : PrimeValue := ⟨322501, pr322501⟩
private theorem pr322513 : PrimeCertificate 322513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6719]) (by decide +kernel)
def pv322513 : PrimeValue := ⟨322513, pr322513⟩
private theorem pr322519 : PrimeCertificate 322519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1097]) (by decide +kernel)
def pv322519 : PrimeValue := ⟨322519, pr322519⟩
private theorem pr322523 : PrimeCertificate 322523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv131,pv1231]) (by decide +kernel)
def pv322523 : PrimeValue := ⟨322523, pr322523⟩
private theorem pr322537 : PrimeCertificate 322537 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv89,pv151]) (by decide +kernel)
def pv322537 : PrimeValue := ⟨322537, pr322537⟩
private theorem pr322573 : PrimeCertificate 322573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv26881]) (by decide +kernel)
def pv322573 : PrimeValue := ⟨322573, pr322573⟩
private theorem pr322589 : PrimeCertificate 322589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv41,pv281]) (by decide +kernel)
def pv322589 : PrimeValue := ⟨322589, pr322589⟩
private theorem pr322607 : PrimeCertificate 322607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv161303]) (by decide +kernel)
def pv322607 : PrimeValue := ⟨322607, pr322607⟩
private theorem pr322627 : PrimeCertificate 322627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv3163]) (by decide +kernel)
def pv322627 : PrimeValue := ⟨322627, pr322627⟩
private theorem pr322631 : PrimeCertificate 322631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv419]) (by decide +kernel)
def pv322631 : PrimeValue := ⟨322631, pr322631⟩
private theorem pr322633 : PrimeCertificate 322633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4481]) (by decide +kernel)
def pv322633 : PrimeValue := ⟨322633, pr322633⟩
private theorem pr322709 : PrimeCertificate 322709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv80677]) (by decide +kernel)
def pv322709 : PrimeValue := ⟨322709, pr322709⟩
private theorem pr322807 : PrimeCertificate 322807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv67,pv73]) (by decide +kernel)
def pv322807 : PrimeValue := ⟨322807, pr322807⟩
private theorem pr322871 : PrimeCertificate 322871 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv83,pv389]) (by decide +kernel)
def pv322871 : PrimeValue := ⟨322871, pr322871⟩
private theorem pr322877 : PrimeCertificate 322877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv1523]) (by decide +kernel)
def pv322877 : PrimeValue := ⟨322877, pr322877⟩
private theorem pr322901 : PrimeCertificate 322901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3229]) (by decide +kernel)
def pv322901 : PrimeValue := ⟨322901, pr322901⟩
private theorem pr322919 : PrimeCertificate 322919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv161459]) (by decide +kernel)
def pv322919 : PrimeValue := ⟨322919, pr322919⟩
private theorem pr322963 : PrimeCertificate 322963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv2833]) (by decide +kernel)
def pv322963 : PrimeValue := ⟨322963, pr322963⟩
private theorem pr322969 : PrimeCertificate 322969 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13457]) (by decide +kernel)
def pv322969 : PrimeValue := ⟨322969, pr322969⟩
private theorem pr323027 : PrimeCertificate 323027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv14683]) (by decide +kernel)
def pv323027 : PrimeValue := ⟨323027, pr323027⟩
private theorem pr323053 : PrimeCertificate 323053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv26921]) (by decide +kernel)
def pv323053 : PrimeValue := ⟨323053, pr323053⟩
private theorem pr323077 : PrimeCertificate 323077 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv109]) (by decide +kernel)
def pv323077 : PrimeValue := ⟨323077, pr323077⟩
private theorem pr323083 : PrimeCertificate 323083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv193]) (by decide +kernel)
def pv323083 : PrimeValue := ⟨323083, pr323083⟩
private theorem pr323131 : PrimeCertificate 323131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv10771]) (by decide +kernel)
def pv323131 : PrimeValue := ⟨323131, pr323131⟩
private theorem pr323137 : PrimeCertificate 323137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv323137 : PrimeValue := ⟨323137, pr323137⟩
private theorem pr323149 : PrimeCertificate 323149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv3847]) (by decide +kernel)
def pv323149 : PrimeValue := ⟨323149, pr323149⟩
private theorem pr323201 : PrimeCertificate 323201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv101]) (by decide +kernel)
def pv323201 : PrimeValue := ⟨323201, pr323201⟩
private theorem pr323207 : PrimeCertificate 323207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv31,pv401]) (by decide +kernel)
def pv323207 : PrimeValue := ⟨323207, pr323207⟩
private theorem pr323251 : PrimeCertificate 323251 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv431]) (by decide +kernel)
def pv323251 : PrimeValue := ⟨323251, pr323251⟩
private theorem pr323333 : PrimeCertificate 323333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv80833]) (by decide +kernel)
def pv323333 : PrimeValue := ⟨323333, pr323333⟩
private theorem pr323341 : PrimeCertificate 323341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv317]) (by decide +kernel)
def pv323341 : PrimeValue := ⟨323341, pr323341⟩
private theorem pr323369 : PrimeCertificate 323369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv487]) (by decide +kernel)
def pv323369 : PrimeValue := ⟨323369, pr323369⟩
private theorem pr323377 : PrimeCertificate 323377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6737]) (by decide +kernel)
def pv323377 : PrimeValue := ⟨323377, pr323377⟩
private theorem pr323381 : PrimeCertificate 323381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv23,pv37]) (by decide +kernel)
def pv323381 : PrimeValue := ⟨323381, pr323381⟩
private theorem pr323383 : PrimeCertificate 323383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53897]) (by decide +kernel)
def pv323383 : PrimeValue := ⟨323383, pr323383⟩
private theorem pr323413 : PrimeCertificate 323413 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv26951]) (by decide +kernel)
def pv323413 : PrimeValue := ⟨323413, pr323413⟩
private theorem pr323441 : PrimeCertificate 323441 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv311]) (by decide +kernel)
def pv323441 : PrimeValue := ⟨323441, pr323441⟩
private theorem pr323467 : PrimeCertificate 323467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv29]) (by decide +kernel)
def pv323467 : PrimeValue := ⟨323467, pr323467⟩
private theorem pr323509 : PrimeCertificate 323509 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv26959]) (by decide +kernel)
def pv323509 : PrimeValue := ⟨323509, pr323509⟩
private theorem pr323537 : PrimeCertificate 323537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv277]) (by decide +kernel)
def pv323537 : PrimeValue := ⟨323537, pr323537⟩
private theorem pr323549 : PrimeCertificate 323549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1721]) (by decide +kernel)
def pv323549 : PrimeValue := ⟨323549, pr323549⟩
private theorem pr323567 : PrimeCertificate 323567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv161783]) (by decide +kernel)
def pv323567 : PrimeValue := ⟨323567, pr323567⟩
private theorem pr323591 : PrimeCertificate 323591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv32359]) (by decide +kernel)
def pv323591 : PrimeValue := ⟨323591, pr323591⟩
private theorem pr323623 : PrimeCertificate 323623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv461]) (by decide +kernel)
def pv323623 : PrimeValue := ⟨323623, pr323623⟩
private theorem pr323641 : PrimeCertificate 323641 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv29,pv31]) (by decide +kernel)
def pv323641 : PrimeValue := ⟨323641, pr323641⟩
private theorem pr323651 : PrimeCertificate 323651 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv6473]) (by decide +kernel)
def pv323651 : PrimeValue := ⟨323651, pr323651⟩
private theorem pr323699 : PrimeCertificate 323699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv5581]) (by decide +kernel)
def pv323699 : PrimeValue := ⟨323699, pr323699⟩
private theorem pr323717 : PrimeCertificate 323717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv80929]) (by decide +kernel)
def pv323717 : PrimeValue := ⟨323717, pr323717⟩
private theorem pr323767 : PrimeCertificate 323767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17987]) (by decide +kernel)
def pv323767 : PrimeValue := ⟨323767, pr323767⟩
private theorem pr323789 : PrimeCertificate 323789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv1327]) (by decide +kernel)
def pv323789 : PrimeValue := ⟨323789, pr323789⟩
private theorem pr323803 : PrimeCertificate 323803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17989]) (by decide +kernel)
def pv323803 : PrimeValue := ⟨323803, pr323803⟩
private theorem pr323837 : PrimeCertificate 323837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv4261]) (by decide +kernel)
def pv323837 : PrimeValue := ⟨323837, pr323837⟩
private theorem pr323903 : PrimeCertificate 323903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv71,pv2281]) (by decide +kernel)
def pv323903 : PrimeValue := ⟨323903, pr323903⟩
private theorem pr323951 : PrimeCertificate 323951 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv11,pv19,pv31]) (by decide +kernel)
def pv323951 : PrimeValue := ⟨323951, pr323951⟩
private theorem pr323957 : PrimeCertificate 323957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv80989]) (by decide +kernel)
def pv323957 : PrimeValue := ⟨323957, pr323957⟩
private theorem pr323987 : PrimeCertificate 323987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv733]) (by decide +kernel)
def pv323987 : PrimeValue := ⟨323987, pr323987⟩
private theorem pr324011 : PrimeCertificate 324011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv32401]) (by decide +kernel)
def pv324011 : PrimeValue := ⟨324011, pr324011⟩
private theorem pr324031 : PrimeCertificate 324031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv1543]) (by decide +kernel)
def pv324031 : PrimeValue := ⟨324031, pr324031⟩
private theorem pr324053 : PrimeCertificate 324053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv81013]) (by decide +kernel)
def pv324053 : PrimeValue := ⟨324053, pr324053⟩
private theorem pr324073 : PrimeCertificate 324073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv643]) (by decide +kernel)
def pv324073 : PrimeValue := ⟨324073, pr324073⟩
private theorem pr324097 : PrimeCertificate 324097 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv211]) (by decide +kernel)
def pv324097 : PrimeValue := ⟨324097, pr324097⟩
private theorem pr324119 : PrimeCertificate 324119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv162059]) (by decide +kernel)
def pv324119 : PrimeValue := ⟨324119, pr324119⟩
private theorem pr324211 : PrimeCertificate 324211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv101,pv107]) (by decide +kernel)
def pv324211 : PrimeValue := ⟨324211, pr324211⟩
private theorem pr324217 : PrimeCertificate 324217 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv79]) (by decide +kernel)
def pv324217 : PrimeValue := ⟨324217, pr324217⟩
private theorem pr324419 : PrimeCertificate 324419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv162209]) (by decide +kernel)
def pv324419 : PrimeValue := ⟨324419, pr324419⟩
private theorem pr324427 : PrimeCertificate 324427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv139,pv389]) (by decide +kernel)
def pv324427 : PrimeValue := ⟨324427, pr324427⟩
private theorem pr324431 : PrimeCertificate 324431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv32443]) (by decide +kernel)
def pv324431 : PrimeValue := ⟨324431, pr324431⟩
private theorem pr324439 : PrimeCertificate 324439 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv2351]) (by decide +kernel)
def pv324439 : PrimeValue := ⟨324439, pr324439⟩
private theorem pr324469 : PrimeCertificate 324469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9013]) (by decide +kernel)
def pv324469 : PrimeValue := ⟨324469, pr324469⟩
private theorem pr324473 : PrimeCertificate 324473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv40559]) (by decide +kernel)
def pv324473 : PrimeValue := ⟨324473, pr324473⟩
private theorem pr324491 : PrimeCertificate 324491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv877]) (by decide +kernel)
def pv324491 : PrimeValue := ⟨324491, pr324491⟩
private theorem pr324503 : PrimeCertificate 324503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv162251]) (by decide +kernel)
def pv324503 : PrimeValue := ⟨324503, pr324503⟩
private theorem pr324517 : PrimeCertificate 324517 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv27043]) (by decide +kernel)
def pv324517 : PrimeValue := ⟨324517, pr324517⟩
private theorem pr324529 : PrimeCertificate 324529 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv6761]) (by decide +kernel)
def pv324529 : PrimeValue := ⟨324529, pr324529⟩
private theorem pr324589 : PrimeCertificate 324589 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv2459]) (by decide +kernel)
def pv324589 : PrimeValue := ⟨324589, pr324589⟩
private theorem pr324617 : PrimeCertificate 324617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv40577]) (by decide +kernel)
def pv324617 : PrimeValue := ⟨324617, pr324617⟩
private theorem pr324641 : PrimeCertificate 324641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2029]) (by decide +kernel)
def pv324641 : PrimeValue := ⟨324641, pr324641⟩
private theorem pr324689 : PrimeCertificate 324689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv223]) (by decide +kernel)
def pv324689 : PrimeValue := ⟨324689, pr324689⟩
private theorem pr324697 : PrimeCertificate 324697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv83,pv163]) (by decide +kernel)
def pv324697 : PrimeValue := ⟨324697, pr324697⟩
private theorem pr324733 : PrimeCertificate 324733 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv27061]) (by decide +kernel)
def pv324733 : PrimeValue := ⟨324733, pr324733⟩
private theorem pr324743 : PrimeCertificate 324743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv29,pv509]) (by decide +kernel)
def pv324743 : PrimeValue := ⟨324743, pr324743⟩
private theorem pr324757 : PrimeCertificate 324757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv97]) (by decide +kernel)
def pv324757 : PrimeValue := ⟨324757, pr324757⟩
private theorem pr324763 : PrimeCertificate 324763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv113,pv479]) (by decide +kernel)
def pv324763 : PrimeValue := ⟨324763, pr324763⟩
private theorem pr324791 : PrimeCertificate 324791 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv32479]) (by decide +kernel)
def pv324791 : PrimeValue := ⟨324791, pr324791⟩
private theorem pr324809 : PrimeCertificate 324809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv3691]) (by decide +kernel)
def pv324809 : PrimeValue := ⟨324809, pr324809⟩
private theorem pr324811 : PrimeCertificate 324811 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv401]) (by decide +kernel)
def pv324811 : PrimeValue := ⟨324811, pr324811⟩
private theorem pr324869 : PrimeCertificate 324869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv241,pv337]) (by decide +kernel)
def pv324869 : PrimeValue := ⟨324869, pr324869⟩
private theorem pr324889 : PrimeCertificate 324889 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13537]) (by decide +kernel)
def pv324889 : PrimeValue := ⟨324889, pr324889⟩
private theorem pr324893 : PrimeCertificate 324893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv81223]) (by decide +kernel)
def pv324893 : PrimeValue := ⟨324893, pr324893⟩
private theorem pr324953 : PrimeCertificate 324953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv151,pv269]) (by decide +kernel)
def pv324953 : PrimeValue := ⟨324953, pr324953⟩
private theorem pr324979 : PrimeCertificate 324979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv54163]) (by decide +kernel)
def pv324979 : PrimeValue := ⟨324979, pr324979⟩
private theorem pr324991 : PrimeCertificate 324991 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv157]) (by decide +kernel)
def pv324991 : PrimeValue := ⟨324991, pr324991⟩
private theorem pr324997 : PrimeCertificate 324997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv53,pv73]) (by decide +kernel)
def pv324997 : PrimeValue := ⟨324997, pr324997⟩
private theorem pr325021 : PrimeCertificate 325021 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv5417]) (by decide +kernel)
def pv325021 : PrimeValue := ⟨325021, pr325021⟩
private theorem pr325063 : PrimeCertificate 325063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv18059]) (by decide +kernel)
def pv325063 : PrimeValue := ⟨325063, pr325063⟩
private theorem pr325081 : PrimeCertificate 325081 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv43]) (by decide +kernel)
def pv325081 : PrimeValue := ⟨325081, pr325081⟩
private theorem pr325153 : PrimeCertificate 325153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1129]) (by decide +kernel)
def pv325153 : PrimeValue := ⟨325153, pr325153⟩
private theorem pr325163 : PrimeCertificate 325163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv367,pv443]) (by decide +kernel)
def pv325163 : PrimeValue := ⟨325163, pr325163⟩
private theorem pr325187 : PrimeCertificate 325187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv162593]) (by decide +kernel)
def pv325187 : PrimeValue := ⟨325187, pr325187⟩
private theorem pr325189 : PrimeCertificate 325189 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv3011]) (by decide +kernel)
def pv325189 : PrimeValue := ⟨325189, pr325189⟩
private theorem pr325217 : PrimeCertificate 325217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv10163]) (by decide +kernel)
def pv325217 : PrimeValue := ⟨325217, pr325217⟩
private theorem pr325219 : PrimeCertificate 325219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv809]) (by decide +kernel)
def pv325219 : PrimeValue := ⟨325219, pr325219⟩
private theorem pr325231 : PrimeCertificate 325231 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv37,pv293]) (by decide +kernel)
def pv325231 : PrimeValue := ⟨325231, pr325231⟩
private theorem pr325249 : PrimeCertificate 325249 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv325249 : PrimeValue := ⟨325249, pr325249⟩
private theorem pr325271 : PrimeCertificate 325271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv2957]) (by decide +kernel)
def pv325271 : PrimeValue := ⟨325271, pr325271⟩
private theorem pr325307 : PrimeCertificate 325307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv311,pv523]) (by decide +kernel)
def pv325307 : PrimeValue := ⟨325307, pr325307⟩
private theorem pr325309 : PrimeCertificate 325309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv27109]) (by decide +kernel)
def pv325309 : PrimeValue := ⟨325309, pr325309⟩
private theorem pr325349 : PrimeCertificate 325349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163,pv499]) (by decide +kernel)
def pv325349 : PrimeValue := ⟨325349, pr325349⟩
private theorem pr325379 : PrimeCertificate 325379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv4397]) (by decide +kernel)
def pv325379 : PrimeValue := ⟨325379, pr325379⟩
private theorem pr325421 : PrimeCertificate 325421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv307]) (by decide +kernel)
def pv325421 : PrimeValue := ⟨325421, pr325421⟩
private theorem pr325459 : PrimeCertificate 325459 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv41]) (by decide +kernel)
def pv325459 : PrimeValue := ⟨325459, pr325459⟩
private theorem pr325463 : PrimeCertificate 325463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv162731]) (by decide +kernel)
def pv325463 : PrimeValue := ⟨325463, pr325463⟩
private theorem pr325487 : PrimeCertificate 325487 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv67,pv347]) (by decide +kernel)
def pv325487 : PrimeValue := ⟨325487, pr325487⟩
private theorem pr325543 : PrimeCertificate 325543 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv23,pv337]) (by decide +kernel)
def pv325543 : PrimeValue := ⟨325543, pr325543⟩
private theorem pr325571 : PrimeCertificate 325571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv4651]) (by decide +kernel)
def pv325571 : PrimeValue := ⟨325571, pr325571⟩
private theorem pr325597 : PrimeCertificate 325597 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv43,pv631]) (by decide +kernel)
def pv325597 : PrimeValue := ⟨325597, pr325597⟩
private theorem pr325607 : PrimeCertificate 325607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv71,pv2293]) (by decide +kernel)
def pv325607 : PrimeValue := ⟨325607, pr325607⟩
private theorem pr325667 : PrimeCertificate 325667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv113,pv131]) (by decide +kernel)
def pv325667 : PrimeValue := ⟨325667, pr325667⟩
private theorem pr325673 : PrimeCertificate 325673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv40709]) (by decide +kernel)
def pv325673 : PrimeValue := ⟨325673, pr325673⟩
private theorem pr325681 : PrimeCertificate 325681 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv59]) (by decide +kernel)
def pv325681 : PrimeValue := ⟨325681, pr325681⟩
private theorem pr325691 : PrimeCertificate 325691 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv32569]) (by decide +kernel)
def pv325691 : PrimeValue := ⟨325691, pr325691⟩
private theorem pr325693 : PrimeCertificate 325693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv109]) (by decide +kernel)
def pv325693 : PrimeValue := ⟨325693, pr325693⟩
private theorem pr325723 : PrimeCertificate 325723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv54287]) (by decide +kernel)
def pv325723 : PrimeValue := ⟨325723, pr325723⟩
private theorem pr325729 : PrimeCertificate 325729 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv13,pv29]) (by decide +kernel)
def pv325729 : PrimeValue := ⟨325729, pr325729⟩
private theorem pr325747 : PrimeCertificate 325747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18097]) (by decide +kernel)
def pv325747 : PrimeValue := ⟨325747, pr325747⟩
private theorem pr325751 : PrimeCertificate 325751 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv1303]) (by decide +kernel)
def pv325751 : PrimeValue := ⟨325751, pr325751⟩
private theorem pr325753 : PrimeCertificate 325753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv277]) (by decide +kernel)
def pv325753 : PrimeValue := ⟨325753, pr325753⟩
private theorem pr325777 : PrimeCertificate 325777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv617]) (by decide +kernel)
def pv325777 : PrimeValue := ⟨325777, pr325777⟩
private theorem pr325783 : PrimeCertificate 325783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2011]) (by decide +kernel)
def pv325783 : PrimeValue := ⟨325783, pr325783⟩
private theorem pr325849 : PrimeCertificate 325849 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13577]) (by decide +kernel)
def pv325849 : PrimeValue := ⟨325849, pr325849⟩
private theorem pr325883 : PrimeCertificate 325883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv1283]) (by decide +kernel)
def pv325883 : PrimeValue := ⟨325883, pr325883⟩
private theorem pr325891 : PrimeCertificate 325891 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv71]) (by decide +kernel)
def pv325891 : PrimeValue := ⟨325891, pr325891⟩
private theorem pr325901 : PrimeCertificate 325901 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3259]) (by decide +kernel)
def pv325901 : PrimeValue := ⟨325901, pr325901⟩
private theorem pr325921 : PrimeCertificate 325921 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv7,pv97]) (by decide +kernel)
def pv325921 : PrimeValue := ⟨325921, pr325921⟩
private theorem pr325993 : PrimeCertificate 325993 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv47]) (by decide +kernel)
def pv325993 : PrimeValue := ⟨325993, pr325993⟩
private theorem pr326113 : PrimeCertificate 326113 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv43,pv79]) (by decide +kernel)
def pv326113 : PrimeValue := ⟨326113, pr326113⟩
private theorem pr326119 : PrimeCertificate 326119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv37,pv113]) (by decide +kernel)
def pv326119 : PrimeValue := ⟨326119, pr326119⟩
private theorem pr326141 : PrimeCertificate 326141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv709]) (by decide +kernel)
def pv326141 : PrimeValue := ⟨326141, pr326141⟩
private theorem pr326143 : PrimeCertificate 326143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv18119]) (by decide +kernel)
def pv326143 : PrimeValue := ⟨326143, pr326143⟩
private theorem pr326147 : PrimeCertificate 326147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv313,pv521]) (by decide +kernel)
def pv326147 : PrimeValue := ⟨326147, pr326147⟩
private theorem pr326149 : PrimeCertificate 326149 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv27179]) (by decide +kernel)
def pv326149 : PrimeValue := ⟨326149, pr326149⟩
private theorem pr326159 : PrimeCertificate 326159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv23297]) (by decide +kernel)
def pv326159 : PrimeValue := ⟨326159, pr326159⟩
private theorem pr326171 : PrimeCertificate 326171 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv13,pv193]) (by decide +kernel)
def pv326171 : PrimeValue := ⟨326171, pr326171⟩
private theorem pr326189 : PrimeCertificate 326189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv81547]) (by decide +kernel)
def pv326189 : PrimeValue := ⟨326189, pr326189⟩
private theorem pr326219 : PrimeCertificate 326219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163109]) (by decide +kernel)
def pv326219 : PrimeValue := ⟨326219, pr326219⟩
private theorem pr326309 : PrimeCertificate 326309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv97]) (by decide +kernel)
def pv326309 : PrimeValue := ⟨326309, pr326309⟩
private theorem pr326323 : PrimeCertificate 326323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6043]) (by decide +kernel)
def pv326323 : PrimeValue := ⟨326323, pr326323⟩
private theorem pr326351 : PrimeCertificate 326351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv61,pv107]) (by decide +kernel)
def pv326351 : PrimeValue := ⟨326351, pr326351⟩
private theorem pr326369 : PrimeCertificate 326369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv31,pv47]) (by decide +kernel)
def pv326369 : PrimeValue := ⟨326369, pr326369⟩
private theorem pr326437 : PrimeCertificate 326437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv2473]) (by decide +kernel)
def pv326437 : PrimeValue := ⟨326437, pr326437⟩
private theorem pr326441 : PrimeCertificate 326441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv8161]) (by decide +kernel)
def pv326441 : PrimeValue := ⟨326441, pr326441⟩
private theorem pr326449 : PrimeCertificate 326449 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv2267]) (by decide +kernel)
def pv326449 : PrimeValue := ⟨326449, pr326449⟩
private theorem pr326467 : PrimeCertificate 326467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2591]) (by decide +kernel)
def pv326467 : PrimeValue := ⟨326467, pr326467⟩
private theorem pr326503 : PrimeCertificate 326503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv97]) (by decide +kernel)
def pv326503 : PrimeValue := ⟨326503, pr326503⟩
private theorem pr326537 : PrimeCertificate 326537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17]) (by decide +kernel)
def pv326537 : PrimeValue := ⟨326537, pr326537⟩
private theorem pr326539 : PrimeCertificate 326539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6047]) (by decide +kernel)
def pv326539 : PrimeValue := ⟨326539, pr326539⟩
private theorem pr326563 : PrimeCertificate 326563 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv1471]) (by decide +kernel)
def pv326563 : PrimeValue := ⟨326563, pr326563⟩
private theorem pr326567 : PrimeCertificate 326567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv269,pv607]) (by decide +kernel)
def pv326567 : PrimeValue := ⟨326567, pr326567⟩
private theorem pr326581 : PrimeCertificate 326581 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv5443]) (by decide +kernel)
def pv326581 : PrimeValue := ⟨326581, pr326581⟩
private theorem pr326593 : PrimeCertificate 326593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv326593 : PrimeValue := ⟨326593, pr326593⟩
private theorem pr326597 : PrimeCertificate 326597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv81649]) (by decide +kernel)
def pv326597 : PrimeValue := ⟨326597, pr326597⟩
private theorem pr326609 : PrimeCertificate 326609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv137,pv149]) (by decide +kernel)
def pv326609 : PrimeValue := ⟨326609, pr326609⟩
private theorem pr326633 : PrimeCertificate 326633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv40829]) (by decide +kernel)
def pv326633 : PrimeValue := ⟨326633, pr326633⟩
private theorem pr326657 : PrimeCertificate 326657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv29]) (by decide +kernel)
def pv326657 : PrimeValue := ⟨326657, pr326657⟩
private theorem pr326659 : PrimeCertificate 326659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv54443]) (by decide +kernel)
def pv326659 : PrimeValue := ⟨326659, pr326659⟩
private theorem pr326681 : PrimeCertificate 326681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv8167]) (by decide +kernel)
def pv326681 : PrimeValue := ⟨326681, pr326681⟩
private theorem pr326707 : PrimeCertificate 326707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv3203]) (by decide +kernel)
def pv326707 : PrimeValue := ⟨326707, pr326707⟩
private theorem pr326737 : PrimeCertificate 326737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2269]) (by decide +kernel)
def pv326737 : PrimeValue := ⟨326737, pr326737⟩
private theorem pr326741 : PrimeCertificate 326741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv31]) (by decide +kernel)
def pv326741 : PrimeValue := ⟨326741, pr326741⟩
private theorem pr326773 : PrimeCertificate 326773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv313]) (by decide +kernel)
def pv326773 : PrimeValue := ⟨326773, pr326773⟩
private theorem pr326903 : PrimeCertificate 326903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv79,pv2069]) (by decide +kernel)
def pv326903 : PrimeValue := ⟨326903, pr326903⟩
private theorem pr326923 : PrimeCertificate 326923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv103]) (by decide +kernel)
def pv326923 : PrimeValue := ⟨326923, pr326923⟩
private theorem pr326939 : PrimeCertificate 326939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163469]) (by decide +kernel)
def pv326939 : PrimeValue := ⟨326939, pr326939⟩
private theorem pr326947 : PrimeCertificate 326947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv1879]) (by decide +kernel)
def pv326947 : PrimeValue := ⟨326947, pr326947⟩
private theorem pr326951 : PrimeCertificate 326951 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv503]) (by decide +kernel)
def pv326951 : PrimeValue := ⟨326951, pr326951⟩
private theorem pr326983 : PrimeCertificate 326983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv54497]) (by decide +kernel)
def pv326983 : PrimeValue := ⟨326983, pr326983⟩
private theorem pr327007 : PrimeCertificate 327007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv491]) (by decide +kernel)
def pv327007 : PrimeValue := ⟨327007, pr327007⟩
private theorem pr327011 : PrimeCertificate 327011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv617]) (by decide +kernel)
def pv327011 : PrimeValue := ⟨327011, pr327011⟩
private theorem pr327023 : PrimeCertificate 327023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv113,pv1447]) (by decide +kernel)
def pv327023 : PrimeValue := ⟨327023, pr327023⟩
private theorem pr327127 : PrimeCertificate 327127 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv54521]) (by decide +kernel)
def pv327127 : PrimeValue := ⟨327127, pr327127⟩
private theorem pr327193 : PrimeCertificate 327193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13633]) (by decide +kernel)
def pv327193 : PrimeValue := ⟨327193, pr327193⟩
private theorem pr327203 : PrimeCertificate 327203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163601]) (by decide +kernel)
def pv327203 : PrimeValue := ⟨327203, pr327203⟩
private theorem pr327209 : PrimeCertificate 327209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv5843]) (by decide +kernel)
def pv327209 : PrimeValue := ⟨327209, pr327209⟩
private theorem pr327211 : PrimeCertificate 327211 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv839]) (by decide +kernel)
def pv327211 : PrimeValue := ⟨327211, pr327211⟩
private theorem pr327263 : PrimeCertificate 327263 :=
  certifyPrime (q := pv19) (ls := [pv2,pv13,pv41,pv307]) (by decide +kernel)
def pv327263 : PrimeValue := ⟨327263, pr327263⟩
private theorem pr327311 : PrimeCertificate 327311 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv71,pv461]) (by decide +kernel)
def pv327311 : PrimeValue := ⟨327311, pr327311⟩
private theorem pr327317 : PrimeCertificate 327317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv43,pv173]) (by decide +kernel)
def pv327317 : PrimeValue := ⟨327317, pr327317⟩
private theorem pr327319 : PrimeCertificate 327319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv3209]) (by decide +kernel)
def pv327319 : PrimeValue := ⟨327319, pr327319⟩
private theorem pr327337 : PrimeCertificate 327337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv593]) (by decide +kernel)
def pv327337 : PrimeValue := ⟨327337, pr327337⟩
private theorem pr327343 : PrimeCertificate 327343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv89,pv613]) (by decide +kernel)
def pv327343 : PrimeValue := ⟨327343, pr327343⟩
private theorem pr327401 : PrimeCertificate 327401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1637]) (by decide +kernel)
def pv327401 : PrimeValue := ⟨327401, pr327401⟩
private theorem pr327407 : PrimeCertificate 327407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv127,pv1289]) (by decide +kernel)
def pv327407 : PrimeValue := ⟨327407, pr327407⟩
private theorem pr327419 : PrimeCertificate 327419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv257]) (by decide +kernel)
def pv327419 : PrimeValue := ⟨327419, pr327419⟩
private theorem pr327433 : PrimeCertificate 327433 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv1949]) (by decide +kernel)
def pv327433 : PrimeValue := ⟨327433, pr327433⟩
private theorem pr327443 : PrimeCertificate 327443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv1621]) (by decide +kernel)
def pv327443 : PrimeValue := ⟨327443, pr327443⟩
private theorem pr327469 : PrimeCertificate 327469 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv29,pv941]) (by decide +kernel)
def pv327469 : PrimeValue := ⟨327469, pr327469⟩
private theorem pr327479 : PrimeCertificate 327479 :=
  certifyPrime (q := pv29) (ls := [pv2,pv73,pv2243]) (by decide +kernel)
def pv327479 : PrimeValue := ⟨327479, pr327479⟩
private theorem pr327491 : PrimeCertificate 327491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv32749]) (by decide +kernel)
def pv327491 : PrimeValue := ⟨327491, pr327491⟩
private theorem pr327529 : PrimeCertificate 327529 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4549]) (by decide +kernel)
def pv327529 : PrimeValue := ⟨327529, pr327529⟩
private theorem pr327571 : PrimeCertificate 327571 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv61,pv179]) (by decide +kernel)
def pv327571 : PrimeValue := ⟨327571, pr327571⟩
private theorem pr327629 : PrimeCertificate 327629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11701]) (by decide +kernel)
def pv327629 : PrimeValue := ⟨327629, pr327629⟩
private theorem pr327647 : PrimeCertificate 327647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv53,pv281]) (by decide +kernel)
def pv327647 : PrimeValue := ⟨327647, pr327647⟩
private theorem pr327661 : PrimeCertificate 327661 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv43,pv127]) (by decide +kernel)
def pv327661 : PrimeValue := ⟨327661, pr327661⟩
private theorem pr327667 : PrimeCertificate 327667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv563]) (by decide +kernel)
def pv327667 : PrimeValue := ⟨327667, pr327667⟩
private theorem pr327673 : PrimeCertificate 327673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv41]) (by decide +kernel)
def pv327673 : PrimeValue := ⟨327673, pr327673⟩
private theorem pr327689 : PrimeCertificate 327689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv40961]) (by decide +kernel)
def pv327689 : PrimeValue := ⟨327689, pr327689⟩
private theorem pr327737 : PrimeCertificate 327737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv577]) (by decide +kernel)
def pv327737 : PrimeValue := ⟨327737, pr327737⟩
private theorem pr327757 : PrimeCertificate 327757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv191]) (by decide +kernel)
def pv327757 : PrimeValue := ⟨327757, pr327757⟩
private theorem pr327779 : PrimeCertificate 327779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv47,pv317]) (by decide +kernel)
def pv327779 : PrimeValue := ⟨327779, pr327779⟩
private theorem pr327797 : PrimeCertificate 327797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv509]) (by decide +kernel)
def pv327797 : PrimeValue := ⟨327797, pr327797⟩
private theorem pr327827 : PrimeCertificate 327827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv8627]) (by decide +kernel)
def pv327827 : PrimeValue := ⟨327827, pr327827⟩
private theorem pr327829 : PrimeCertificate 327829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv1607]) (by decide +kernel)
def pv327829 : PrimeValue := ⟨327829, pr327829⟩
private theorem pr327851 : PrimeCertificate 327851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv79,pv83]) (by decide +kernel)
def pv327851 : PrimeValue := ⟨327851, pr327851⟩
private theorem pr327853 : PrimeCertificate 327853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1301]) (by decide +kernel)
def pv327853 : PrimeValue := ⟨327853, pr327853⟩
private theorem pr327923 : PrimeCertificate 327923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv59,pv397]) (by decide +kernel)
def pv327923 : PrimeValue := ⟨327923, pr327923⟩
private theorem pr327941 : PrimeCertificate 327941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv863]) (by decide +kernel)
def pv327941 : PrimeValue := ⟨327941, pr327941⟩
private theorem pr327967 : PrimeCertificate 327967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv1163]) (by decide +kernel)
def pv327967 : PrimeValue := ⟨327967, pr327967⟩
private theorem pr327979 : PrimeCertificate 327979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv137]) (by decide +kernel)
def pv327979 : PrimeValue := ⟨327979, pr327979⟩
private theorem pr328067 : PrimeCertificate 328067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv9649]) (by decide +kernel)
def pv328067 : PrimeValue := ⟨328067, pr328067⟩
private theorem pr328093 : PrimeCertificate 328093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1439]) (by decide +kernel)
def pv328093 : PrimeValue := ⟨328093, pr328093⟩
private theorem pr328127 : PrimeCertificate 328127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv359,pv457]) (by decide +kernel)
def pv328127 : PrimeValue := ⟨328127, pr328127⟩
private theorem pr328129 : PrimeCertificate 328129 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1709]) (by decide +kernel)
def pv328129 : PrimeValue := ⟨328129, pr328129⟩
private theorem pr328213 : PrimeCertificate 328213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1013]) (by decide +kernel)
def pv328213 : PrimeValue := ⟨328213, pr328213⟩
private theorem pr328243 : PrimeCertificate 328243 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv227,pv241]) (by decide +kernel)
def pv328243 : PrimeValue := ⟨328243, pr328243⟩
private theorem pr328283 : PrimeCertificate 328283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv53,pv163]) (by decide +kernel)
def pv328283 : PrimeValue := ⟨328283, pr328283⟩
private theorem pr328303 : PrimeCertificate 328303 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv13,pv23,pv61]) (by decide +kernel)
def pv328303 : PrimeValue := ⟨328303, pr328303⟩
private theorem pr328327 : PrimeCertificate 328327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv54721]) (by decide +kernel)
def pv328327 : PrimeValue := ⟨328327, pr328327⟩
private theorem pr328331 : PrimeCertificate 328331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv32833]) (by decide +kernel)
def pv328331 : PrimeValue := ⟨328331, pr328331⟩
private theorem pr328343 : PrimeCertificate 328343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv47,pv499]) (by decide +kernel)
def pv328343 : PrimeValue := ⟨328343, pr328343⟩
private theorem pr328357 : PrimeCertificate 328357 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv1303]) (by decide +kernel)
def pv328357 : PrimeValue := ⟨328357, pr328357⟩
private theorem pr328411 : PrimeCertificate 328411 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv41,pv89]) (by decide +kernel)
def pv328411 : PrimeValue := ⟨328411, pr328411⟩
private theorem pr328511 : PrimeCertificate 328511 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv13,pv19]) (by decide +kernel)
def pv328511 : PrimeValue := ⟨328511, pr328511⟩
private theorem pr328543 : PrimeCertificate 328543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv3221]) (by decide +kernel)
def pv328543 : PrimeValue := ⟨328543, pr328543⟩
private theorem pr328579 : PrimeCertificate 328579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv2381]) (by decide +kernel)
def pv328579 : PrimeValue := ⟨328579, pr328579⟩
private theorem pr328589 : PrimeCertificate 328589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv71,pv89]) (by decide +kernel)
def pv328589 : PrimeValue := ⟨328589, pr328589⟩
private theorem pr328619 : PrimeCertificate 328619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv164309]) (by decide +kernel)
def pv328619 : PrimeValue := ⟨328619, pr328619⟩
private theorem pr328621 : PrimeCertificate 328621 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv5477]) (by decide +kernel)
def pv328621 : PrimeValue := ⟨328621, pr328621⟩
private theorem pr328633 : PrimeCertificate 328633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13693]) (by decide +kernel)
def pv328633 : PrimeValue := ⟨328633, pr328633⟩
private theorem pr328639 : PrimeCertificate 328639 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv54773]) (by decide +kernel)
def pv328639 : PrimeValue := ⟨328639, pr328639⟩
private theorem pr328651 : PrimeCertificate 328651 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv313]) (by decide +kernel)
def pv328651 : PrimeValue := ⟨328651, pr328651⟩
private theorem pr328687 : PrimeCertificate 328687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv1889]) (by decide +kernel)
def pv328687 : PrimeValue := ⟨328687, pr328687⟩
private theorem pr328777 : PrimeCertificate 328777 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv19,pv103]) (by decide +kernel)
def pv328777 : PrimeValue := ⟨328777, pr328777⟩
private theorem pr328813 : PrimeCertificate 328813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv47,pv53]) (by decide +kernel)
def pv328813 : PrimeValue := ⟨328813, pr328813⟩
private theorem pr328829 : PrimeCertificate 328829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv82207]) (by decide +kernel)
def pv328829 : PrimeValue := ⟨328829, pr328829⟩
private theorem pr328837 : PrimeCertificate 328837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv409]) (by decide +kernel)
def pv328837 : PrimeValue := ⟨328837, pr328837⟩
private theorem pr328849 : PrimeCertificate 328849 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv17,pv31]) (by decide +kernel)
def pv328849 : PrimeValue := ⟨328849, pr328849⟩
private theorem pr328883 : PrimeCertificate 328883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv569]) (by decide +kernel)
def pv328883 : PrimeValue := ⟨328883, pr328883⟩
private theorem pr328891 : PrimeCertificate 328891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv577]) (by decide +kernel)
def pv328891 : PrimeValue := ⟨328891, pr328891⟩
private theorem pr328901 : PrimeCertificate 328901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv23]) (by decide +kernel)
def pv328901 : PrimeValue := ⟨328901, pr328901⟩
private theorem pr328921 : PrimeCertificate 328921 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv2741]) (by decide +kernel)
def pv328921 : PrimeValue := ⟨328921, pr328921⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
