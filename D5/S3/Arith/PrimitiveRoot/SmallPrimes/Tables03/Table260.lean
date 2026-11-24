/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables03/Table260
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables03/Table260.pv2210801
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table038
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table055
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table070
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table140

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr2210801 : Nat.Prime 2210801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv5527]) (by decide +kernel)
def pv2210801 : PrimeValue := ⟨2210801, pr2210801⟩
private theorem pr2210891 : Nat.Prime 2210891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv101,pv199]) (by decide +kernel)
def pv2210891 : PrimeValue := ⟨2210891, pr2210891⟩
private theorem pr2210993 : Nat.Prime 2210993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv1039]) (by decide +kernel)
def pv2210993 : PrimeValue := ⟨2210993, pr2210993⟩
private theorem pr2211179 : Nat.Prime 2211179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1105589]) (by decide +kernel)
def pv2211179 : PrimeValue := ⟨2211179, pr2211179⟩
private theorem pr2211263 : Nat.Prime 2211263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv107,pv10333]) (by decide +kernel)
def pv2211263 : PrimeValue := ⟨2211263, pr2211263⟩
private theorem pr2211413 : Nat.Prime 2211413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv78979]) (by decide +kernel)
def pv2211413 : PrimeValue := ⟨2211413, pr2211413⟩
private theorem pr2211563 : Nat.Prime 2211563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv58199]) (by decide +kernel)
def pv2211563 : PrimeValue := ⟨2211563, pr2211563⟩
private theorem pr2211689 : Nat.Prime 2211689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv276461]) (by decide +kernel)
def pv2211689 : PrimeValue := ⟨2211689, pr2211689⟩
private theorem pr2211953 : Nat.Prime 2211953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv138247]) (by decide +kernel)
def pv2211953 : PrimeValue := ⟨2211953, pr2211953⟩
private theorem pr2212181 : Nat.Prime 2212181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv110609]) (by decide +kernel)
def pv2212181 : PrimeValue := ⟨2212181, pr2212181⟩
private theorem pr2212349 : Nat.Prime 2212349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv9067]) (by decide +kernel)
def pv2212349 : PrimeValue := ⟨2212349, pr2212349⟩
private theorem pr2212571 : Nat.Prime 2212571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv97,pv2281]) (by decide +kernel)
def pv2212571 : PrimeValue := ⟨2212571, pr2212571⟩
private theorem pr2213069 : Nat.Prime 2213069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv53,pv73]) (by decide +kernel)
def pv2213069 : PrimeValue := ⟨2213069, pr2213069⟩
private theorem pr2213423 : Nat.Prime 2213423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv79,pv14009]) (by decide +kernel)
def pv2213423 : PrimeValue := ⟨2213423, pr2213423⟩
private theorem pr2213759 : Nat.Prime 2213759 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv701,pv1579]) (by decide +kernel)
def pv2213759 : PrimeValue := ⟨2213759, pr2213759⟩
private theorem pr2214011 : Nat.Prime 2214011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv221401]) (by decide +kernel)
def pv2214011 : PrimeValue := ⟨2214011, pr2214011⟩
private theorem pr2214161 : Nat.Prime 2214161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv2129]) (by decide +kernel)
def pv2214161 : PrimeValue := ⟨2214161, pr2214161⟩
private theorem pr2214473 : Nat.Prime 2214473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv107,pv199]) (by decide +kernel)
def pv2214473 : PrimeValue := ⟨2214473, pr2214473⟩
private theorem pr2214713 : Nat.Prime 2214713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv276839]) (by decide +kernel)
def pv2214713 : PrimeValue := ⟨2214713, pr2214713⟩
private theorem pr2214731 : Nat.Prime 2214731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv29,pv1091]) (by decide +kernel)
def pv2214731 : PrimeValue := ⟨2214731, pr2214731⟩
private theorem pr2214749 : Nat.Prime 2214749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv553687]) (by decide +kernel)
def pv2214749 : PrimeValue := ⟨2214749, pr2214749⟩
private theorem pr2214791 : Nat.Prime 2214791 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv241,pv919]) (by decide +kernel)
def pv2214791 : PrimeValue := ⟨2214791, pr2214791⟩
private theorem pr2214869 : Nat.Prime 2214869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv151,pv193]) (by decide +kernel)
def pv2214869 : PrimeValue := ⟨2214869, pr2214869⟩
private theorem pr2214941 : Nat.Prime 2214941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv1217]) (by decide +kernel)
def pv2214941 : PrimeValue := ⟨2214941, pr2214941⟩
private theorem pr2215529 : Nat.Prime 2215529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv39563]) (by decide +kernel)
def pv2215529 : PrimeValue := ⟨2215529, pr2215529⟩
private theorem pr2215793 : Nat.Prime 2215793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79,pv1753]) (by decide +kernel)
def pv2215793 : PrimeValue := ⟨2215793, pr2215793⟩
private theorem pr2215901 : Nat.Prime 2215901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv22159]) (by decide +kernel)
def pv2215901 : PrimeValue := ⟨2215901, pr2215901⟩
private theorem pr2215949 : Nat.Prime 2215949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv2729]) (by decide +kernel)
def pv2215949 : PrimeValue := ⟨2215949, pr2215949⟩
private theorem pr2216309 : Nat.Prime 2216309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv554077]) (by decide +kernel)
def pv2216309 : PrimeValue := ⟨2216309, pr2216309⟩
private theorem pr2216471 : Nat.Prime 2216471 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv29,pv7643]) (by decide +kernel)
def pv2216471 : PrimeValue := ⟨2216471, pr2216471⟩
private theorem pr2216699 : Nat.Prime 2216699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv5927]) (by decide +kernel)
def pv2216699 : PrimeValue := ⟨2216699, pr2216699⟩
private theorem pr2216729 : Nat.Prime 2216729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv401,pv691]) (by decide +kernel)
def pv2216729 : PrimeValue := ⟨2216729, pr2216729⟩
private theorem pr2216759 : Nat.Prime 2216759 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv167,pv6637]) (by decide +kernel)
def pv2216759 : PrimeValue := ⟨2216759, pr2216759⟩
private theorem pr2216999 : Nat.Prime 2216999 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv158357]) (by decide +kernel)
def pv2216999 : PrimeValue := ⟨2216999, pr2216999⟩
private theorem pr2217041 : Nat.Prime 2217041 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv37,pv107]) (by decide +kernel)
def pv2217041 : PrimeValue := ⟨2217041, pr2217041⟩
private theorem pr2217251 : Nat.Prime 2217251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv181]) (by decide +kernel)
def pv2217251 : PrimeValue := ⟨2217251, pr2217251⟩
private theorem pr2217779 : Nat.Prime 2217779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163,pv6803]) (by decide +kernel)
def pv2217779 : PrimeValue := ⟨2217779, pr2217779⟩
private theorem pr2217881 : Nat.Prime 2217881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv89]) (by decide +kernel)
def pv2217881 : PrimeValue := ⟨2217881, pr2217881⟩
private theorem pr2218091 : Nat.Prime 2218091 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv31687]) (by decide +kernel)
def pv2218091 : PrimeValue := ⟨2218091, pr2218091⟩
private theorem pr2218283 : Nat.Prime 2218283 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv59,pv1709]) (by decide +kernel)
def pv2218283 : PrimeValue := ⟨2218283, pr2218283⟩
private theorem pr2218319 : Nat.Prime 2218319 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv1109159]) (by decide +kernel)
def pv2218319 : PrimeValue := ⟨2218319, pr2218319⟩
private theorem pr2218343 : Nat.Prime 2218343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv193,pv821]) (by decide +kernel)
def pv2218343 : PrimeValue := ⟨2218343, pr2218343⟩
private theorem pr2218439 : Nat.Prime 2218439 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv1109219]) (by decide +kernel)
def pv2218439 : PrimeValue := ⟨2218439, pr2218439⟩
private theorem pr2218451 : Nat.Prime 2218451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv3413]) (by decide +kernel)
def pv2218451 : PrimeValue := ⟨2218451, pr2218451⟩
private theorem pr2218613 : Nat.Prime 2218613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv50423]) (by decide +kernel)
def pv2218613 : PrimeValue := ⟨2218613, pr2218613⟩
private theorem pr2218691 : Nat.Prime 2218691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv127,pv1747]) (by decide +kernel)
def pv2218691 : PrimeValue := ⟨2218691, pr2218691⟩
private theorem pr2218883 : Nat.Prime 2218883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv367,pv3023]) (by decide +kernel)
def pv2218883 : PrimeValue := ⟨2218883, pr2218883⟩
private theorem pr2219033 : Nat.Prime 2219033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv103,pv2693]) (by decide +kernel)
def pv2219033 : PrimeValue := ⟨2219033, pr2219033⟩
private theorem pr2219039 : Nat.Prime 2219039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv37,pv157,pv191]) (by decide +kernel)
def pv2219039 : PrimeValue := ⟨2219039, pr2219039⟩
private theorem pr2219111 : Nat.Prime 2219111 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv53,pv79]) (by decide +kernel)
def pv2219111 : PrimeValue := ⟨2219111, pr2219111⟩
private theorem pr2219141 : Nat.Prime 2219141 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv131]) (by decide +kernel)
def pv2219141 : PrimeValue := ⟨2219141, pr2219141⟩
private theorem pr2219279 : Nat.Prime 2219279 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv1109639]) (by decide +kernel)
def pv2219279 : PrimeValue := ⟨2219279, pr2219279⟩
private theorem pr2219351 : Nat.Prime 2219351 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv7,pv17,pv373]) (by decide +kernel)
def pv2219351 : PrimeValue := ⟨2219351, pr2219351⟩
private theorem pr2219411 : Nat.Prime 2219411 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv221941]) (by decide +kernel)
def pv2219411 : PrimeValue := ⟨2219411, pr2219411⟩
private theorem pr2219543 : Nat.Prime 2219543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv19,pv4493]) (by decide +kernel)
def pv2219543 : PrimeValue := ⟨2219543, pr2219543⟩
private theorem pr2219771 : Nat.Prime 2219771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv1669]) (by decide +kernel)
def pv2219771 : PrimeValue := ⟨2219771, pr2219771⟩
private theorem pr2219813 : Nat.Prime 2219813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv79279]) (by decide +kernel)
def pv2219813 : PrimeValue := ⟨2219813, pr2219813⟩
private theorem pr2219831 : Nat.Prime 2219831 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv139,pv1597]) (by decide +kernel)
def pv2219831 : PrimeValue := ⟨2219831, pr2219831⟩
private theorem pr2220479 : Nat.Prime 2220479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv41,pv2083]) (by decide +kernel)
def pv2220479 : PrimeValue := ⟨2220479, pr2220479⟩
private theorem pr2220503 : Nat.Prime 2220503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv521,pv2131]) (by decide +kernel)
def pv2220503 : PrimeValue := ⟨2220503, pr2220503⟩
private theorem pr2220521 : Nat.Prime 2220521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43,pv1291]) (by decide +kernel)
def pv2220521 : PrimeValue := ⟨2220521, pr2220521⟩
private theorem pr2220551 : Nat.Prime 2220551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv89,pv499]) (by decide +kernel)
def pv2220551 : PrimeValue := ⟨2220551, pr2220551⟩
private theorem pr2220749 : Nat.Prime 2220749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv6689]) (by decide +kernel)
def pv2220749 : PrimeValue := ⟨2220749, pr2220749⟩
private theorem pr2220941 : Nat.Prime 2220941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv293,pv379]) (by decide +kernel)
def pv2220941 : PrimeValue := ⟨2220941, pr2220941⟩
private theorem pr2221253 : Nat.Prime 2221253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv2657]) (by decide +kernel)
def pv2221253 : PrimeValue := ⟨2221253, pr2221253⟩
private theorem pr2221403 : Nat.Prime 2221403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv269,pv4129]) (by decide +kernel)
def pv2221403 : PrimeValue := ⟨2221403, pr2221403⟩
private theorem pr2221871 : Nat.Prime 2221871 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv31741]) (by decide +kernel)
def pv2221871 : PrimeValue := ⟨2221871, pr2221871⟩
private theorem pr2221931 : Nat.Prime 2221931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv222193]) (by decide +kernel)
def pv2221931 : PrimeValue := ⟨2221931, pr2221931⟩
private theorem pr2221991 : Nat.Prime 2221991 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv222199]) (by decide +kernel)
def pv2221991 : PrimeValue := ⟨2221991, pr2221991⟩
private theorem pr2222243 : Nat.Prime 2222243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv83,pv1217]) (by decide +kernel)
def pv2222243 : PrimeValue := ⟨2222243, pr2222243⟩
private theorem pr2222351 : Nat.Prime 2222351 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv13,pv263]) (by decide +kernel)
def pv2222351 : PrimeValue := ⟨2222351, pr2222351⟩
private theorem pr2222543 : Nat.Prime 2222543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv22679]) (by decide +kernel)
def pv2222543 : PrimeValue := ⟨2222543, pr2222543⟩
private theorem pr2222579 : Nat.Prime 2222579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1111289]) (by decide +kernel)
def pv2222579 : PrimeValue := ⟨2222579, pr2222579⟩
private theorem pr2222723 : Nat.Prime 2222723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1111361]) (by decide +kernel)
def pv2222723 : PrimeValue := ⟨2222723, pr2222723⟩
private theorem pr2222729 : Nat.Prime 2222729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv109,pv2549]) (by decide +kernel)
def pv2222729 : PrimeValue := ⟨2222729, pr2222729⟩
private theorem pr2223059 : Nat.Prime 2223059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv857,pv1297]) (by decide +kernel)
def pv2223059 : PrimeValue := ⟨2223059, pr2223059⟩
private theorem pr2223101 : Nat.Prime 2223101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv43,pv47]) (by decide +kernel)
def pv2223101 : PrimeValue := ⟨2223101, pr2223101⟩
private theorem pr2223233 : Nat.Prime 2223233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv1579]) (by decide +kernel)
def pv2223233 : PrimeValue := ⟨2223233, pr2223233⟩
private theorem pr2223443 : Nat.Prime 2223443 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv85517]) (by decide +kernel)
def pv2223443 : PrimeValue := ⟨2223443, pr2223443⟩
private theorem pr2223449 : Nat.Prime 2223449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv449,pv619]) (by decide +kernel)
def pv2223449 : PrimeValue := ⟨2223449, pr2223449⟩
private theorem pr2223713 : Nat.Prime 2223713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv69491]) (by decide +kernel)
def pv2223713 : PrimeValue := ⟨2223713, pr2223713⟩
private theorem pr2223839 : Nat.Prime 2223839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv17,pv65407]) (by decide +kernel)
def pv2223839 : PrimeValue := ⟨2223839, pr2223839⟩
private theorem pr2223869 : Nat.Prime 2223869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv555967]) (by decide +kernel)
def pv2223869 : PrimeValue := ⟨2223869, pr2223869⟩
private theorem pr2223911 : Nat.Prime 2223911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv17107]) (by decide +kernel)
def pv2223911 : PrimeValue := ⟨2223911, pr2223911⟩
private theorem pr2224289 : Nat.Prime 2224289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv71,pv89]) (by decide +kernel)
def pv2224289 : PrimeValue := ⟨2224289, pr2224289⟩
private theorem pr2224559 : Nat.Prime 2224559 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv19,pv8363]) (by decide +kernel)
def pv2224559 : PrimeValue := ⟨2224559, pr2224559⟩
private theorem pr2224661 : Nat.Prime 2224661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv2713]) (by decide +kernel)
def pv2224661 : PrimeValue := ⟨2224661, pr2224661⟩
private theorem pr2224763 : Nat.Prime 2224763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1112381]) (by decide +kernel)
def pv2224763 : PrimeValue := ⟨2224763, pr2224763⟩
private theorem pr2224961 : Nat.Prime 2224961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv409]) (by decide +kernel)
def pv2224961 : PrimeValue := ⟨2224961, pr2224961⟩
private theorem pr2224991 : Nat.Prime 2224991 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv222499]) (by decide +kernel)
def pv2224991 : PrimeValue := ⟨2224991, pr2224991⟩
private theorem pr2225081 : Nat.Prime 2225081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv13,pv389]) (by decide +kernel)
def pv2225081 : PrimeValue := ⟨2225081, pr2225081⟩
private theorem pr2225159 : Nat.Prime 2225159 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv13,pv23,pv61]) (by decide +kernel)
def pv2225159 : PrimeValue := ⟨2225159, pr2225159⟩
private theorem pr2225339 : Nat.Prime 2225339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv16607]) (by decide +kernel)
def pv2225339 : PrimeValue := ⟨2225339, pr2225339⟩
private theorem pr2225543 : Nat.Prime 2225543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv101161]) (by decide +kernel)
def pv2225543 : PrimeValue := ⟨2225543, pr2225543⟩
private theorem pr2225771 : Nat.Prime 2225771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv73,pv3049]) (by decide +kernel)
def pv2225771 : PrimeValue := ⟨2225771, pr2225771⟩
private theorem pr2225819 : Nat.Prime 2225819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv173,pv919]) (by decide +kernel)
def pv2225819 : PrimeValue := ⟨2225819, pr2225819⟩
private theorem pr2225969 : Nat.Prime 2225969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv139123]) (by decide +kernel)
def pv2225969 : PrimeValue := ⟨2225969, pr2225969⟩
private theorem pr2225999 : Nat.Prime 2225999 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv109,pv10211]) (by decide +kernel)
def pv2225999 : PrimeValue := ⟨2225999, pr2225999⟩
private theorem pr2226221 : Nat.Prime 2226221 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv79,pv1409]) (by decide +kernel)
def pv2226221 : PrimeValue := ⟨2226221, pr2226221⟩
private theorem pr2226569 : Nat.Prime 2226569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv278321]) (by decide +kernel)
def pv2226569 : PrimeValue := ⟨2226569, pr2226569⟩
private theorem pr2226593 : Nat.Prime 2226593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv4093]) (by decide +kernel)
def pv2226593 : PrimeValue := ⟨2226593, pr2226593⟩
private theorem pr2226701 : Nat.Prime 2226701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv3181]) (by decide +kernel)
def pv2226701 : PrimeValue := ⟨2226701, pr2226701⟩
private theorem pr2227223 : Nat.Prime 2227223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv83,pv13417]) (by decide +kernel)
def pv2227223 : PrimeValue := ⟨2227223, pr2227223⟩
private theorem pr2227409 : Nat.Prime 2227409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv19,pv431]) (by decide +kernel)
def pv2227409 : PrimeValue := ⟨2227409, pr2227409⟩
private theorem pr2227451 : Nat.Prime 2227451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv44549]) (by decide +kernel)
def pv2227451 : PrimeValue := ⟨2227451, pr2227451⟩
private theorem pr2227583 : Nat.Prime 2227583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv159113]) (by decide +kernel)
def pv2227583 : PrimeValue := ⟨2227583, pr2227583⟩
private theorem pr2227601 : Nat.Prime 2227601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv5569]) (by decide +kernel)
def pv2227601 : PrimeValue := ⟨2227601, pr2227601⟩
private theorem pr2227661 : Nat.Prime 2227661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv3593]) (by decide +kernel)
def pv2227661 : PrimeValue := ⟨2227661, pr2227661⟩
private theorem pr2227763 : Nat.Prime 2227763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv379,pv2939]) (by decide +kernel)
def pv2227763 : PrimeValue := ⟨2227763, pr2227763⟩
private theorem pr2227853 : Nat.Prime 2227853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv4603]) (by decide +kernel)
def pv2227853 : PrimeValue := ⟨2227853, pr2227853⟩
private theorem pr2227859 : Nat.Prime 2227859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv101,pv269]) (by decide +kernel)
def pv2227859 : PrimeValue := ⟨2227859, pr2227859⟩
private theorem pr2227871 : Nat.Prime 2227871 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv222787]) (by decide +kernel)
def pv2227871 : PrimeValue := ⟨2227871, pr2227871⟩
private theorem pr2227889 : Nat.Prime 2227889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv10711]) (by decide +kernel)
def pv2227889 : PrimeValue := ⟨2227889, pr2227889⟩
private theorem pr2228183 : Nat.Prime 2228183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv101281]) (by decide +kernel)
def pv2228183 : PrimeValue := ⟨2228183, pr2228183⟩
private theorem pr2228321 : Nat.Prime 2228321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv733]) (by decide +kernel)
def pv2228321 : PrimeValue := ⟨2228321, pr2228321⟩
private theorem pr2228393 : Nat.Prime 2228393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv278549]) (by decide +kernel)
def pv2228393 : PrimeValue := ⟨2228393, pr2228393⟩
private theorem pr2228423 : Nat.Prime 2228423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv22739]) (by decide +kernel)
def pv2228423 : PrimeValue := ⟨2228423, pr2228423⟩
private theorem pr2228549 : Nat.Prime 2228549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv59,pv71]) (by decide +kernel)
def pv2228549 : PrimeValue := ⟨2228549, pr2228549⟩
private theorem pr2228753 : Nat.Prime 2228753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv139297]) (by decide +kernel)
def pv2228753 : PrimeValue := ⟨2228753, pr2228753⟩
private theorem pr2228771 : Nat.Prime 2228771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv222877]) (by decide +kernel)
def pv2228771 : PrimeValue := ⟨2228771, pr2228771⟩
private theorem pr2229299 : Nat.Prime 2229299 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv23,pv48463]) (by decide +kernel)
def pv2229299 : PrimeValue := ⟨2229299, pr2229299⟩
private theorem pr2229581 : Nat.Prime 2229581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv2719]) (by decide +kernel)
def pv2229581 : PrimeValue := ⟨2229581, pr2229581⟩
private theorem pr2229599 : Nat.Prime 2229599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv22751]) (by decide +kernel)
def pv2229599 : PrimeValue := ⟨2229599, pr2229599⟩
private theorem pr2229809 : Nat.Prime 2229809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv43,pv463]) (by decide +kernel)
def pv2229809 : PrimeValue := ⟨2229809, pr2229809⟩
private theorem pr2229833 : Nat.Prime 2229833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv25339]) (by decide +kernel)
def pv2229833 : PrimeValue := ⟨2229833, pr2229833⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
