/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table021
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table021.pv51343
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table004
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr51343 : Nat.Prime 51343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv199]) (by decide +kernel)
def pv51343 : PrimeValue := ⟨51343, pr51343⟩
private theorem pr51347 : Nat.Prime 51347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv25673]) (by decide +kernel)
def pv51347 : PrimeValue := ⟨51347, pr51347⟩
private theorem pr51349 : Nat.Prime 51349 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv11,pv389]) (by decide +kernel)
def pv51349 : PrimeValue := ⟨51349, pr51349⟩
private theorem pr51361 : Nat.Prime 51361 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv51361 : PrimeValue := ⟨51361, pr51361⟩
private theorem pr51383 : Nat.Prime 51383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv1117]) (by decide +kernel)
def pv51383 : PrimeValue := ⟨51383, pr51383⟩
private theorem pr51407 : Nat.Prime 51407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv25703]) (by decide +kernel)
def pv51407 : PrimeValue := ⟨51407, pr51407⟩
private theorem pr51413 : Nat.Prime 51413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12853]) (by decide +kernel)
def pv51413 : PrimeValue := ⟨51413, pr51413⟩
private theorem pr51419 : Nat.Prime 51419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv547]) (by decide +kernel)
def pv51419 : PrimeValue := ⟨51419, pr51419⟩
private theorem pr51421 : Nat.Prime 51421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv857]) (by decide +kernel)
def pv51421 : PrimeValue := ⟨51421, pr51421⟩
private theorem pr51427 : Nat.Prime 51427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2857]) (by decide +kernel)
def pv51427 : PrimeValue := ⟨51427, pr51427⟩
private theorem pr51431 : Nat.Prime 51431 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv37,pv139]) (by decide +kernel)
def pv51431 : PrimeValue := ⟨51431, pr51431⟩
private theorem pr51437 : Nat.Prime 51437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv167]) (by decide +kernel)
def pv51437 : PrimeValue := ⟨51437, pr51437⟩
private theorem pr51439 : Nat.Prime 51439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8573]) (by decide +kernel)
def pv51439 : PrimeValue := ⟨51439, pr51439⟩
private theorem pr51449 : Nat.Prime 51449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv109]) (by decide +kernel)
def pv51449 : PrimeValue := ⟨51449, pr51449⟩
private theorem pr51461 : Nat.Prime 51461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv83]) (by decide +kernel)
def pv51461 : PrimeValue := ⟨51461, pr51461⟩
private theorem pr51473 : Nat.Prime 51473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3217]) (by decide +kernel)
def pv51473 : PrimeValue := ⟨51473, pr51473⟩
private theorem pr51479 : Nat.Prime 51479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv3677]) (by decide +kernel)
def pv51479 : PrimeValue := ⟨51479, pr51479⟩
private theorem pr51481 : Nat.Prime 51481 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv51481 : PrimeValue := ⟨51481, pr51481⟩
private theorem pr51487 : Nat.Prime 51487 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8581]) (by decide +kernel)
def pv51487 : PrimeValue := ⟨51487, pr51487⟩
private theorem pr51503 : Nat.Prime 51503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv2341]) (by decide +kernel)
def pv51503 : PrimeValue := ⟨51503, pr51503⟩
private theorem pr51511 : Nat.Prime 51511 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv17,pv101]) (by decide +kernel)
def pv51511 : PrimeValue := ⟨51511, pr51511⟩
private theorem pr51517 : Nat.Prime 51517 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv53]) (by decide +kernel)
def pv51517 : PrimeValue := ⟨51517, pr51517⟩
private theorem pr51521 : Nat.Prime 51521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv23]) (by decide +kernel)
def pv51521 : PrimeValue := ⟨51521, pr51521⟩
private theorem pr51539 : Nat.Prime 51539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv353]) (by decide +kernel)
def pv51539 : PrimeValue := ⟨51539, pr51539⟩
private theorem pr51551 : Nat.Prime 51551 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv1031]) (by decide +kernel)
def pv51551 : PrimeValue := ⟨51551, pr51551⟩
private theorem pr51563 : Nat.Prime 51563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv127]) (by decide +kernel)
def pv51563 : PrimeValue := ⟨51563, pr51563⟩
private theorem pr51577 : Nat.Prime 51577 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv307]) (by decide +kernel)
def pv51577 : PrimeValue := ⟨51577, pr51577⟩
private theorem pr51581 : Nat.Prime 51581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2579]) (by decide +kernel)
def pv51581 : PrimeValue := ⟨51581, pr51581⟩
private theorem pr51593 : Nat.Prime 51593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6449]) (by decide +kernel)
def pv51593 : PrimeValue := ⟨51593, pr51593⟩
private theorem pr51599 : Nat.Prime 51599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv25799]) (by decide +kernel)
def pv51599 : PrimeValue := ⟨51599, pr51599⟩
private theorem pr51607 : Nat.Prime 51607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv61]) (by decide +kernel)
def pv51607 : PrimeValue := ⟨51607, pr51607⟩
private theorem pr51613 : Nat.Prime 51613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv23]) (by decide +kernel)
def pv51613 : PrimeValue := ⟨51613, pr51613⟩
private theorem pr51631 : Nat.Prime 51631 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv1721]) (by decide +kernel)
def pv51631 : PrimeValue := ⟨51631, pr51631⟩
private theorem pr51637 : Nat.Prime 51637 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv331]) (by decide +kernel)
def pv51637 : PrimeValue := ⟨51637, pr51637⟩
private theorem pr51647 : Nat.Prime 51647 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv17,pv31]) (by decide +kernel)
def pv51647 : PrimeValue := ⟨51647, pr51647⟩
private theorem pr51659 : Nat.Prime 51659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv1123]) (by decide +kernel)
def pv51659 : PrimeValue := ⟨51659, pr51659⟩
private theorem pr51673 : Nat.Prime 51673 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2153]) (by decide +kernel)
def pv51673 : PrimeValue := ⟨51673, pr51673⟩
private theorem pr51679 : Nat.Prime 51679 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv11,pv29]) (by decide +kernel)
def pv51679 : PrimeValue := ⟨51679, pr51679⟩
private theorem pr51683 : Nat.Prime 51683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv25841]) (by decide +kernel)
def pv51683 : PrimeValue := ⟨51683, pr51683⟩
private theorem pr51691 : Nat.Prime 51691 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv1723]) (by decide +kernel)
def pv51691 : PrimeValue := ⟨51691, pr51691⟩
private theorem pr51713 : Nat.Prime 51713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv101]) (by decide +kernel)
def pv51713 : PrimeValue := ⟨51713, pr51713⟩
private theorem pr51719 : Nat.Prime 51719 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv19,pv1361]) (by decide +kernel)
def pv51719 : PrimeValue := ⟨51719, pr51719⟩
private theorem pr51721 : Nat.Prime 51721 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv431]) (by decide +kernel)
def pv51721 : PrimeValue := ⟨51721, pr51721⟩
private theorem pr51749 : Nat.Prime 51749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv761]) (by decide +kernel)
def pv51749 : PrimeValue := ⟨51749, pr51749⟩
private theorem pr51767 : Nat.Prime 51767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv13,pv181]) (by decide +kernel)
def pv51767 : PrimeValue := ⟨51767, pr51767⟩
private theorem pr51769 : Nat.Prime 51769 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv719]) (by decide +kernel)
def pv51769 : PrimeValue := ⟨51769, pr51769⟩
private theorem pr51787 : Nat.Prime 51787 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv137]) (by decide +kernel)
def pv51787 : PrimeValue := ⟨51787, pr51787⟩
private theorem pr51797 : Nat.Prime 51797 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv563]) (by decide +kernel)
def pv51797 : PrimeValue := ⟨51797, pr51797⟩
private theorem pr51803 : Nat.Prime 51803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv439]) (by decide +kernel)
def pv51803 : PrimeValue := ⟨51803, pr51803⟩
private theorem pr51817 : Nat.Prime 51817 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv127]) (by decide +kernel)
def pv51817 : PrimeValue := ⟨51817, pr51817⟩
private theorem pr51827 : Nat.Prime 51827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv25913]) (by decide +kernel)
def pv51827 : PrimeValue := ⟨51827, pr51827⟩
private theorem pr51829 : Nat.Prime 51829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv617]) (by decide +kernel)
def pv51829 : PrimeValue := ⟨51829, pr51829⟩
private theorem pr51839 : Nat.Prime 51839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv25919]) (by decide +kernel)
def pv51839 : PrimeValue := ⟨51839, pr51839⟩
private theorem pr51853 : Nat.Prime 51853 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv29,pv149]) (by decide +kernel)
def pv51853 : PrimeValue := ⟨51853, pr51853⟩
private theorem pr51859 : Nat.Prime 51859 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv67]) (by decide +kernel)
def pv51859 : PrimeValue := ⟨51859, pr51859⟩
private theorem pr51869 : Nat.Prime 51869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12967]) (by decide +kernel)
def pv51869 : PrimeValue := ⟨51869, pr51869⟩
private theorem pr51871 : Nat.Prime 51871 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv13,pv19]) (by decide +kernel)
def pv51871 : PrimeValue := ⟨51871, pr51871⟩
private theorem pr51893 : Nat.Prime 51893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12973]) (by decide +kernel)
def pv51893 : PrimeValue := ⟨51893, pr51893⟩
private theorem pr51899 : Nat.Prime 51899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv337]) (by decide +kernel)
def pv51899 : PrimeValue := ⟨51899, pr51899⟩
private theorem pr51907 : Nat.Prime 51907 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv41,pv211]) (by decide +kernel)
def pv51907 : PrimeValue := ⟨51907, pr51907⟩
private theorem pr51913 : Nat.Prime 51913 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv7,pv103]) (by decide +kernel)
def pv51913 : PrimeValue := ⟨51913, pr51913⟩
private theorem pr51929 : Nat.Prime 51929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6491]) (by decide +kernel)
def pv51929 : PrimeValue := ⟨51929, pr51929⟩
private theorem pr51941 : Nat.Prime 51941 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv53]) (by decide +kernel)
def pv51941 : PrimeValue := ⟨51941, pr51941⟩
private theorem pr51949 : Nat.Prime 51949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv37]) (by decide +kernel)
def pv51949 : PrimeValue := ⟨51949, pr51949⟩
private theorem pr51971 : Nat.Prime 51971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv5197]) (by decide +kernel)
def pv51971 : PrimeValue := ⟨51971, pr51971⟩
private theorem pr51973 : Nat.Prime 51973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv71]) (by decide +kernel)
def pv51973 : PrimeValue := ⟨51973, pr51973⟩
private theorem pr51977 : Nat.Prime 51977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv73,pv89]) (by decide +kernel)
def pv51977 : PrimeValue := ⟨51977, pr51977⟩
private theorem pr51991 : Nat.Prime 51991 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1733]) (by decide +kernel)
def pv51991 : PrimeValue := ⟨51991, pr51991⟩
private theorem pr52009 : Nat.Prime 52009 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv197]) (by decide +kernel)
def pv52009 : PrimeValue := ⟨52009, pr52009⟩
private theorem pr52021 : Nat.Prime 52021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv52021 : PrimeValue := ⟨52021, pr52021⟩
private theorem pr52027 : Nat.Prime 52027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv23,pv29]) (by decide +kernel)
def pv52027 : PrimeValue := ⟨52027, pr52027⟩
private theorem pr52051 : Nat.Prime 52051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv347]) (by decide +kernel)
def pv52051 : PrimeValue := ⟨52051, pr52051⟩
private theorem pr52057 : Nat.Prime 52057 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv241]) (by decide +kernel)
def pv52057 : PrimeValue := ⟨52057, pr52057⟩
private theorem pr52067 : Nat.Prime 52067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv3719]) (by decide +kernel)
def pv52067 : PrimeValue := ⟨52067, pr52067⟩
private theorem pr52069 : Nat.Prime 52069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4339]) (by decide +kernel)
def pv52069 : PrimeValue := ⟨52069, pr52069⟩
private theorem pr52081 : Nat.Prime 52081 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv52081 : PrimeValue := ⟨52081, pr52081⟩
private theorem pr52103 : Nat.Prime 52103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv109,pv239]) (by decide +kernel)
def pv52103 : PrimeValue := ⟨52103, pr52103⟩
private theorem pr52121 : Nat.Prime 52121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1303]) (by decide +kernel)
def pv52121 : PrimeValue := ⟨52121, pr52121⟩
private theorem pr52127 : Nat.Prime 52127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv67,pv389]) (by decide +kernel)
def pv52127 : PrimeValue := ⟨52127, pr52127⟩
private theorem pr52147 : Nat.Prime 52147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2897]) (by decide +kernel)
def pv52147 : PrimeValue := ⟨52147, pr52147⟩
private theorem pr52153 : Nat.Prime 52153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv53]) (by decide +kernel)
def pv52153 : PrimeValue := ⟨52153, pr52153⟩
private theorem pr52163 : Nat.Prime 52163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv2371]) (by decide +kernel)
def pv52163 : PrimeValue := ⟨52163, pr52163⟩
private theorem pr52177 : Nat.Prime 52177 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1087]) (by decide +kernel)
def pv52177 : PrimeValue := ⟨52177, pr52177⟩
private theorem pr52181 : Nat.Prime 52181 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2609]) (by decide +kernel)
def pv52181 : PrimeValue := ⟨52181, pr52181⟩
private theorem pr52183 : Nat.Prime 52183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv223]) (by decide +kernel)
def pv52183 : PrimeValue := ⟨52183, pr52183⟩
private theorem pr52189 : Nat.Prime 52189 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv4349]) (by decide +kernel)
def pv52189 : PrimeValue := ⟨52189, pr52189⟩
private theorem pr52201 : Nat.Prime 52201 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv52201 : PrimeValue := ⟨52201, pr52201⟩
private theorem pr52223 : Nat.Prime 52223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv26111]) (by decide +kernel)
def pv52223 : PrimeValue := ⟨52223, pr52223⟩
private theorem pr52237 : Nat.Prime 52237 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1451]) (by decide +kernel)
def pv52237 : PrimeValue := ⟨52237, pr52237⟩
private theorem pr52249 : Nat.Prime 52249 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv311]) (by decide +kernel)
def pv52249 : PrimeValue := ⟨52249, pr52249⟩
private theorem pr52253 : Nat.Prime 52253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13063]) (by decide +kernel)
def pv52253 : PrimeValue := ⟨52253, pr52253⟩
private theorem pr52259 : Nat.Prime 52259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv29,pv53]) (by decide +kernel)
def pv52259 : PrimeValue := ⟨52259, pr52259⟩
private theorem pr52267 : Nat.Prime 52267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv281]) (by decide +kernel)
def pv52267 : PrimeValue := ⟨52267, pr52267⟩
private theorem pr52289 : Nat.Prime 52289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv43]) (by decide +kernel)
def pv52289 : PrimeValue := ⟨52289, pr52289⟩
private theorem pr52291 : Nat.Prime 52291 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv83]) (by decide +kernel)
def pv52291 : PrimeValue := ⟨52291, pr52291⟩
private theorem pr52301 : Nat.Prime 52301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv523]) (by decide +kernel)
def pv52301 : PrimeValue := ⟨52301, pr52301⟩
private theorem pr52313 : Nat.Prime 52313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv503]) (by decide +kernel)
def pv52313 : PrimeValue := ⟨52313, pr52313⟩
private theorem pr52321 : Nat.Prime 52321 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv109]) (by decide +kernel)
def pv52321 : PrimeValue := ⟨52321, pr52321⟩
private theorem pr52361 : Nat.Prime 52361 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv7,pv11,pv17]) (by decide +kernel)
def pv52361 : PrimeValue := ⟨52361, pr52361⟩
private theorem pr52363 : Nat.Prime 52363 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2909]) (by decide +kernel)
def pv52363 : PrimeValue := ⟨52363, pr52363⟩
private theorem pr52369 : Nat.Prime 52369 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1091]) (by decide +kernel)
def pv52369 : PrimeValue := ⟨52369, pr52369⟩
private theorem pr52379 : Nat.Prime 52379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv26189]) (by decide +kernel)
def pv52379 : PrimeValue := ⟨52379, pr52379⟩
private theorem pr52387 : Nat.Prime 52387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8731]) (by decide +kernel)
def pv52387 : PrimeValue := ⟨52387, pr52387⟩
private theorem pr52391 : Nat.Prime 52391 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv31]) (by decide +kernel)
def pv52391 : PrimeValue := ⟨52391, pr52391⟩
private theorem pr52433 : Nat.Prime 52433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv113]) (by decide +kernel)
def pv52433 : PrimeValue := ⟨52433, pr52433⟩
private theorem pr52453 : Nat.Prime 52453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv47]) (by decide +kernel)
def pv52453 : PrimeValue := ⟨52453, pr52453⟩
private theorem pr52457 : Nat.Prime 52457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79,pv83]) (by decide +kernel)
def pv52457 : PrimeValue := ⟨52457, pr52457⟩
private theorem pr52489 : Nat.Prime 52489 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3]) (by decide +kernel)
def pv52489 : PrimeValue := ⟨52489, pr52489⟩
private theorem pr52501 : Nat.Prime 52501 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv52501 : PrimeValue := ⟨52501, pr52501⟩
private theorem pr52511 : Nat.Prime 52511 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv59,pv89]) (by decide +kernel)
def pv52511 : PrimeValue := ⟨52511, pr52511⟩
private theorem pr52517 : Nat.Prime 52517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv691]) (by decide +kernel)
def pv52517 : PrimeValue := ⟨52517, pr52517⟩
private theorem pr52529 : Nat.Prime 52529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv67]) (by decide +kernel)
def pv52529 : PrimeValue := ⟨52529, pr52529⟩
private theorem pr52541 : Nat.Prime 52541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv71]) (by decide +kernel)
def pv52541 : PrimeValue := ⟨52541, pr52541⟩
private theorem pr52543 : Nat.Prime 52543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv139]) (by decide +kernel)
def pv52543 : PrimeValue := ⟨52543, pr52543⟩
private theorem pr52553 : Nat.Prime 52553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6569]) (by decide +kernel)
def pv52553 : PrimeValue := ⟨52553, pr52553⟩
private theorem pr52561 : Nat.Prime 52561 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv52561 : PrimeValue := ⟨52561, pr52561⟩
private theorem pr52567 : Nat.Prime 52567 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8761]) (by decide +kernel)
def pv52567 : PrimeValue := ⟨52567, pr52567⟩
private theorem pr52571 : Nat.Prime 52571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv751]) (by decide +kernel)
def pv52571 : PrimeValue := ⟨52571, pr52571⟩
private theorem pr52579 : Nat.Prime 52579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv127]) (by decide +kernel)
def pv52579 : PrimeValue := ⟨52579, pr52579⟩
private theorem pr52583 : Nat.Prime 52583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv61,pv431]) (by decide +kernel)
def pv52583 : PrimeValue := ⟨52583, pr52583⟩
private theorem pr52609 : Nat.Prime 52609 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv137]) (by decide +kernel)
def pv52609 : PrimeValue := ⟨52609, pr52609⟩
private theorem pr52627 : Nat.Prime 52627 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv179]) (by decide +kernel)
def pv52627 : PrimeValue := ⟨52627, pr52627⟩
private theorem pr52631 : Nat.Prime 52631 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv277]) (by decide +kernel)
def pv52631 : PrimeValue := ⟨52631, pr52631⟩
private theorem pr52639 : Nat.Prime 52639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv283]) (by decide +kernel)
def pv52639 : PrimeValue := ⟨52639, pr52639⟩
private theorem pr52667 : Nat.Prime 52667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv1549]) (by decide +kernel)
def pv52667 : PrimeValue := ⟨52667, pr52667⟩
private theorem pr52673 : Nat.Prime 52673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv823]) (by decide +kernel)
def pv52673 : PrimeValue := ⟨52673, pr52673⟩
private theorem pr52691 : Nat.Prime 52691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv479]) (by decide +kernel)
def pv52691 : PrimeValue := ⟨52691, pr52691⟩
private theorem pr52697 : Nat.Prime 52697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv941]) (by decide +kernel)
def pv52697 : PrimeValue := ⟨52697, pr52697⟩
private theorem pr52709 : Nat.Prime 52709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13177]) (by decide +kernel)
def pv52709 : PrimeValue := ⟨52709, pr52709⟩
private theorem pr52711 : Nat.Prime 52711 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv7,pv251]) (by decide +kernel)
def pv52711 : PrimeValue := ⟨52711, pr52711⟩
private theorem pr52721 : Nat.Prime 52721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv659]) (by decide +kernel)
def pv52721 : PrimeValue := ⟨52721, pr52721⟩
private theorem pr52727 : Nat.Prime 52727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv643]) (by decide +kernel)
def pv52727 : PrimeValue := ⟨52727, pr52727⟩
private theorem pr52733 : Nat.Prime 52733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13183]) (by decide +kernel)
def pv52733 : PrimeValue := ⟨52733, pr52733⟩
private theorem pr52747 : Nat.Prime 52747 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59,pv149]) (by decide +kernel)
def pv52747 : PrimeValue := ⟨52747, pr52747⟩
private theorem pr52757 : Nat.Prime 52757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv109]) (by decide +kernel)
def pv52757 : PrimeValue := ⟨52757, pr52757⟩
private theorem pr52769 : Nat.Prime 52769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv97]) (by decide +kernel)
def pv52769 : PrimeValue := ⟨52769, pr52769⟩
private theorem pr52783 : Nat.Prime 52783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv463]) (by decide +kernel)
def pv52783 : PrimeValue := ⟨52783, pr52783⟩
private theorem pr52807 : Nat.Prime 52807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv677]) (by decide +kernel)
def pv52807 : PrimeValue := ⟨52807, pr52807⟩
private theorem pr52813 : Nat.Prime 52813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv163]) (by decide +kernel)
def pv52813 : PrimeValue := ⟨52813, pr52813⟩
private theorem pr52817 : Nat.Prime 52817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3301]) (by decide +kernel)
def pv52817 : PrimeValue := ⟨52817, pr52817⟩
private theorem pr52837 : Nat.Prime 52837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv37]) (by decide +kernel)
def pv52837 : PrimeValue := ⟨52837, pr52837⟩
private theorem pr52859 : Nat.Prime 52859 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv19,pv107]) (by decide +kernel)
def pv52859 : PrimeValue := ⟨52859, pr52859⟩
private theorem pr52861 : Nat.Prime 52861 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv881]) (by decide +kernel)
def pv52861 : PrimeValue := ⟨52861, pr52861⟩
private theorem pr52879 : Nat.Prime 52879 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1259]) (by decide +kernel)
def pv52879 : PrimeValue := ⟨52879, pr52879⟩
private theorem pr52883 : Nat.Prime 52883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv137,pv193]) (by decide +kernel)
def pv52883 : PrimeValue := ⟨52883, pr52883⟩
private theorem pr52889 : Nat.Prime 52889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv601]) (by decide +kernel)
def pv52889 : PrimeValue := ⟨52889, pr52889⟩
private theorem pr52901 : Nat.Prime 52901 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23]) (by decide +kernel)
def pv52901 : PrimeValue := ⟨52901, pr52901⟩
private theorem pr52903 : Nat.Prime 52903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2939]) (by decide +kernel)
def pv52903 : PrimeValue := ⟨52903, pr52903⟩
private theorem pr52919 : Nat.Prime 52919 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv26459]) (by decide +kernel)
def pv52919 : PrimeValue := ⟨52919, pr52919⟩
private theorem pr52937 : Nat.Prime 52937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv509]) (by decide +kernel)
def pv52937 : PrimeValue := ⟨52937, pr52937⟩
private theorem pr52951 : Nat.Prime 52951 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv353]) (by decide +kernel)
def pv52951 : PrimeValue := ⟨52951, pr52951⟩
private theorem pr52957 : Nat.Prime 52957 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1471]) (by decide +kernel)
def pv52957 : PrimeValue := ⟨52957, pr52957⟩
private theorem pr52963 : Nat.Prime 52963 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv97]) (by decide +kernel)
def pv52963 : PrimeValue := ⟨52963, pr52963⟩
private theorem pr52967 : Nat.Prime 52967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv71,pv373]) (by decide +kernel)
def pv52967 : PrimeValue := ⟨52967, pr52967⟩
private theorem pr52973 : Nat.Prime 52973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19,pv41]) (by decide +kernel)
def pv52973 : PrimeValue := ⟨52973, pr52973⟩
private theorem pr52981 : Nat.Prime 52981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv883]) (by decide +kernel)
def pv52981 : PrimeValue := ⟨52981, pr52981⟩
private theorem pr52999 : Nat.Prime 52999 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv73]) (by decide +kernel)
def pv52999 : PrimeValue := ⟨52999, pr52999⟩
private theorem pr53003 : Nat.Prime 53003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv26501]) (by decide +kernel)
def pv53003 : PrimeValue := ⟨53003, pr53003⟩
private theorem pr53017 : Nat.Prime 53017 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv53017 : PrimeValue := ⟨53017, pr53017⟩
private theorem pr53047 : Nat.Prime 53047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv421]) (by decide +kernel)
def pv53047 : PrimeValue := ⟨53047, pr53047⟩
private theorem pr53051 : Nat.Prime 53051 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv1061]) (by decide +kernel)
def pv53051 : PrimeValue := ⟨53051, pr53051⟩
private theorem pr53069 : Nat.Prime 53069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13267]) (by decide +kernel)
def pv53069 : PrimeValue := ⟨53069, pr53069⟩
private theorem pr53077 : Nat.Prime 53077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4423]) (by decide +kernel)
def pv53077 : PrimeValue := ⟨53077, pr53077⟩
private theorem pr53087 : Nat.Prime 53087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv19,pv127]) (by decide +kernel)
def pv53087 : PrimeValue := ⟨53087, pr53087⟩
private theorem pr53089 : Nat.Prime 53089 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7,pv79]) (by decide +kernel)
def pv53089 : PrimeValue := ⟨53089, pr53089⟩
private theorem pr53093 : Nat.Prime 53093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv1021]) (by decide +kernel)
def pv53093 : PrimeValue := ⟨53093, pr53093⟩
private theorem pr53101 : Nat.Prime 53101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv59]) (by decide +kernel)
def pv53101 : PrimeValue := ⟨53101, pr53101⟩
private theorem pr53113 : Nat.Prime 53113 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2213]) (by decide +kernel)
def pv53113 : PrimeValue := ⟨53113, pr53113⟩
private theorem pr53117 : Nat.Prime 53117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv271]) (by decide +kernel)
def pv53117 : PrimeValue := ⟨53117, pr53117⟩
private theorem pr53129 : Nat.Prime 53129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv229]) (by decide +kernel)
def pv53129 : PrimeValue := ⟨53129, pr53129⟩
private theorem pr53147 : Nat.Prime 53147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv26573]) (by decide +kernel)
def pv53147 : PrimeValue := ⟨53147, pr53147⟩
private theorem pr53149 : Nat.Prime 53149 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv43,pv103]) (by decide +kernel)
def pv53149 : PrimeValue := ⟨53149, pr53149⟩
private theorem pr53161 : Nat.Prime 53161 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv443]) (by decide +kernel)
def pv53161 : PrimeValue := ⟨53161, pr53161⟩
private theorem pr53171 : Nat.Prime 53171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv409]) (by decide +kernel)
def pv53171 : PrimeValue := ⟨53171, pr53171⟩
private theorem pr53173 : Nat.Prime 53173 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv211]) (by decide +kernel)
def pv53173 : PrimeValue := ⟨53173, pr53173⟩
private theorem pr53189 : Nat.Prime 53189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13297]) (by decide +kernel)
def pv53189 : PrimeValue := ⟨53189, pr53189⟩
private theorem pr53197 : Nat.Prime 53197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv31]) (by decide +kernel)
def pv53197 : PrimeValue := ⟨53197, pr53197⟩
private theorem pr53201 : Nat.Prime 53201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv19]) (by decide +kernel)
def pv53201 : PrimeValue := ⟨53201, pr53201⟩
private theorem pr53231 : Nat.Prime 53231 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv5323]) (by decide +kernel)
def pv53231 : PrimeValue := ⟨53231, pr53231⟩
private theorem pr53233 : Nat.Prime 53233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1109]) (by decide +kernel)
def pv53233 : PrimeValue := ⟨53233, pr53233⟩
private theorem pr53239 : Nat.Prime 53239 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv467]) (by decide +kernel)
def pv53239 : PrimeValue := ⟨53239, pr53239⟩
private theorem pr53267 : Nat.Prime 53267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv26633]) (by decide +kernel)
def pv53267 : PrimeValue := ⟨53267, pr53267⟩
private theorem pr53269 : Nat.Prime 53269 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv193]) (by decide +kernel)
def pv53269 : PrimeValue := ⟨53269, pr53269⟩
private theorem pr53279 : Nat.Prime 53279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv17,pv1567]) (by decide +kernel)
def pv53279 : PrimeValue := ⟨53279, pr53279⟩
private theorem pr53281 : Nat.Prime 53281 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv53281 : PrimeValue := ⟨53281, pr53281⟩
private theorem pr53299 : Nat.Prime 53299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv47]) (by decide +kernel)
def pv53299 : PrimeValue := ⟨53299, pr53299⟩
private theorem pr53309 : Nat.Prime 53309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13327]) (by decide +kernel)
def pv53309 : PrimeValue := ⟨53309, pr53309⟩
private theorem pr53323 : Nat.Prime 53323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8887]) (by decide +kernel)
def pv53323 : PrimeValue := ⟨53323, pr53323⟩
private theorem pr53327 : Nat.Prime 53327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv13,pv293]) (by decide +kernel)
def pv53327 : PrimeValue := ⟨53327, pr53327⟩
private theorem pr53353 : Nat.Prime 53353 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv53353 : PrimeValue := ⟨53353, pr53353⟩
private theorem pr53359 : Nat.Prime 53359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8893]) (by decide +kernel)
def pv53359 : PrimeValue := ⟨53359, pr53359⟩
private theorem pr53377 : Nat.Prime 53377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv139]) (by decide +kernel)
def pv53377 : PrimeValue := ⟨53377, pr53377⟩
private theorem pr53381 : Nat.Prime 53381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv157]) (by decide +kernel)
def pv53381 : PrimeValue := ⟨53381, pr53381⟩
private theorem pr53401 : Nat.Prime 53401 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv89]) (by decide +kernel)
def pv53401 : PrimeValue := ⟨53401, pr53401⟩
private theorem pr53407 : Nat.Prime 53407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv43]) (by decide +kernel)
def pv53407 : PrimeValue := ⟨53407, pr53407⟩
private theorem pr53411 : Nat.Prime 53411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv109]) (by decide +kernel)
def pv53411 : PrimeValue := ⟨53411, pr53411⟩
private theorem pr53419 : Nat.Prime 53419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv307]) (by decide +kernel)
def pv53419 : PrimeValue := ⟨53419, pr53419⟩
private theorem pr53437 : Nat.Prime 53437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv73]) (by decide +kernel)
def pv53437 : PrimeValue := ⟨53437, pr53437⟩
private theorem pr53441 : Nat.Prime 53441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv167]) (by decide +kernel)
def pv53441 : PrimeValue := ⟨53441, pr53441⟩
private theorem pr53453 : Nat.Prime 53453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv83]) (by decide +kernel)
def pv53453 : PrimeValue := ⟨53453, pr53453⟩
private theorem pr53479 : Nat.Prime 53479 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2971]) (by decide +kernel)
def pv53479 : PrimeValue := ⟨53479, pr53479⟩
private theorem pr53503 : Nat.Prime 53503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv241]) (by decide +kernel)
def pv53503 : PrimeValue := ⟨53503, pr53503⟩
private theorem pr53507 : Nat.Prime 53507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv863]) (by decide +kernel)
def pv53507 : PrimeValue := ⟨53507, pr53507⟩
private theorem pr53527 : Nat.Prime 53527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv811]) (by decide +kernel)
def pv53527 : PrimeValue := ⟨53527, pr53527⟩
private theorem pr53549 : Nat.Prime 53549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1217]) (by decide +kernel)
def pv53549 : PrimeValue := ⟨53549, pr53549⟩
private theorem pr53551 : Nat.Prime 53551 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv53551 : PrimeValue := ⟨53551, pr53551⟩
private theorem pr53569 : Nat.Prime 53569 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv53569 : PrimeValue := ⟨53569, pr53569⟩
private theorem pr53591 : Nat.Prime 53591 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv23,pv233]) (by decide +kernel)
def pv53591 : PrimeValue := ⟨53591, pr53591⟩
private theorem pr53593 : Nat.Prime 53593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv29]) (by decide +kernel)
def pv53593 : PrimeValue := ⟨53593, pr53593⟩
private theorem pr53597 : Nat.Prime 53597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13399]) (by decide +kernel)
def pv53597 : PrimeValue := ⟨53597, pr53597⟩
private theorem pr53609 : Nat.Prime 53609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6701]) (by decide +kernel)
def pv53609 : PrimeValue := ⟨53609, pr53609⟩
private theorem pr53611 : Nat.Prime 53611 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv1787]) (by decide +kernel)
def pv53611 : PrimeValue := ⟨53611, pr53611⟩
private theorem pr53617 : Nat.Prime 53617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1117]) (by decide +kernel)
def pv53617 : PrimeValue := ⟨53617, pr53617⟩
private theorem pr53623 : Nat.Prime 53623 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv331]) (by decide +kernel)
def pv53623 : PrimeValue := ⟨53623, pr53623⟩
private theorem pr53629 : Nat.Prime 53629 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv41,pv109]) (by decide +kernel)
def pv53629 : PrimeValue := ⟨53629, pr53629⟩
private theorem pr53633 : Nat.Prime 53633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv419]) (by decide +kernel)
def pv53633 : PrimeValue := ⟨53633, pr53633⟩
private theorem pr53639 : Nat.Prime 53639 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv13,pv2063]) (by decide +kernel)
def pv53639 : PrimeValue := ⟨53639, pr53639⟩
private theorem pr53653 : Nat.Prime 53653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv263]) (by decide +kernel)
def pv53653 : PrimeValue := ⟨53653, pr53653⟩
private theorem pr53657 : Nat.Prime 53657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv353]) (by decide +kernel)
def pv53657 : PrimeValue := ⟨53657, pr53657⟩
private theorem pr53681 : Nat.Prime 53681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv61]) (by decide +kernel)
def pv53681 : PrimeValue := ⟨53681, pr53681⟩
private theorem pr53693 : Nat.Prime 53693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv433]) (by decide +kernel)
def pv53693 : PrimeValue := ⟨53693, pr53693⟩
private theorem pr53699 : Nat.Prime 53699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv26849]) (by decide +kernel)
def pv53699 : PrimeValue := ⟨53699, pr53699⟩
private theorem pr53717 : Nat.Prime 53717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv1033]) (by decide +kernel)
def pv53717 : PrimeValue := ⟨53717, pr53717⟩
private theorem pr53719 : Nat.Prime 53719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv1279]) (by decide +kernel)
def pv53719 : PrimeValue := ⟨53719, pr53719⟩
private theorem pr53731 : Nat.Prime 53731 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv199]) (by decide +kernel)
def pv53731 : PrimeValue := ⟨53731, pr53731⟩
private theorem pr53759 : Nat.Prime 53759 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv26879]) (by decide +kernel)
def pv53759 : PrimeValue := ⟨53759, pr53759⟩
private theorem pr53773 : Nat.Prime 53773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4481]) (by decide +kernel)
def pv53773 : PrimeValue := ⟨53773, pr53773⟩
private theorem pr53777 : Nat.Prime 53777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3361]) (by decide +kernel)
def pv53777 : PrimeValue := ⟨53777, pr53777⟩
private theorem pr53783 : Nat.Prime 53783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv26891]) (by decide +kernel)
def pv53783 : PrimeValue := ⟨53783, pr53783⟩
private theorem pr53791 : Nat.Prime 53791 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv11,pv163]) (by decide +kernel)
def pv53791 : PrimeValue := ⟨53791, pr53791⟩
private theorem pr53813 : Nat.Prime 53813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1223]) (by decide +kernel)
def pv53813 : PrimeValue := ⟨53813, pr53813⟩
private theorem pr53819 : Nat.Prime 53819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv379]) (by decide +kernel)
def pv53819 : PrimeValue := ⟨53819, pr53819⟩
private theorem pr53831 : Nat.Prime 53831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv769]) (by decide +kernel)
def pv53831 : PrimeValue := ⟨53831, pr53831⟩
private theorem pr53849 : Nat.Prime 53849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53,pv127]) (by decide +kernel)
def pv53849 : PrimeValue := ⟨53849, pr53849⟩
private theorem pr53857 : Nat.Prime 53857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv53857 : PrimeValue := ⟨53857, pr53857⟩
private theorem pr53861 : Nat.Prime 53861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2693]) (by decide +kernel)
def pv53861 : PrimeValue := ⟨53861, pr53861⟩
private theorem pr53881 : Nat.Prime 53881 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv449]) (by decide +kernel)
def pv53881 : PrimeValue := ⟨53881, pr53881⟩
private theorem pr53887 : Nat.Prime 53887 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1283]) (by decide +kernel)
def pv53887 : PrimeValue := ⟨53887, pr53887⟩
private theorem pr53891 : Nat.Prime 53891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv317]) (by decide +kernel)
def pv53891 : PrimeValue := ⟨53891, pr53891⟩
private theorem pr53897 : Nat.Prime 53897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6737]) (by decide +kernel)
def pv53897 : PrimeValue := ⟨53897, pr53897⟩
private theorem pr53899 : Nat.Prime 53899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv691]) (by decide +kernel)
def pv53899 : PrimeValue := ⟨53899, pr53899⟩
private theorem pr53917 : Nat.Prime 53917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4493]) (by decide +kernel)
def pv53917 : PrimeValue := ⟨53917, pr53917⟩
private theorem pr53923 : Nat.Prime 53923 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv19,pv43]) (by decide +kernel)
def pv53923 : PrimeValue := ⟨53923, pr53923⟩
private theorem pr53927 : Nat.Prime 53927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv59,pv457]) (by decide +kernel)
def pv53927 : PrimeValue := ⟨53927, pr53927⟩
private theorem pr53939 : Nat.Prime 53939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv149,pv181]) (by decide +kernel)
def pv53939 : PrimeValue := ⟨53939, pr53939⟩
private theorem pr53951 : Nat.Prime 53951 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv83]) (by decide +kernel)
def pv53951 : PrimeValue := ⟨53951, pr53951⟩
private theorem pr53959 : Nat.Prime 53959 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv23]) (by decide +kernel)
def pv53959 : PrimeValue := ⟨53959, pr53959⟩
private theorem pr53987 : Nat.Prime 53987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv26993]) (by decide +kernel)
def pv53987 : PrimeValue := ⟨53987, pr53987⟩
private theorem pr53993 : Nat.Prime 53993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv397]) (by decide +kernel)
def pv53993 : PrimeValue := ⟨53993, pr53993⟩
private theorem pr54001 : Nat.Prime 54001 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv54001 : PrimeValue := ⟨54001, pr54001⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
