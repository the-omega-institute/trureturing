/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables03/Table255
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables03/Table255.pv2105381
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table053
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table068
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table139

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr2105381 : Nat.Prime 2105381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv105269]) (by decide +kernel)
def pv2105381 : PrimeValue := ⟨2105381, pr2105381⟩
private theorem pr2105483 : Nat.Prime 2105483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv10853]) (by decide +kernel)
def pv2105483 : PrimeValue := ⟨2105483, pr2105483⟩
private theorem pr2105549 : Nat.Prime 2105549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv526387]) (by decide +kernel)
def pv2105549 : PrimeValue := ⟨2105549, pr2105549⟩
private theorem pr2105693 : Nat.Prime 2105693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv526423]) (by decide +kernel)
def pv2105693 : PrimeValue := ⟨2105693, pr2105693⟩
private theorem pr2105699 : Nat.Prime 2105699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv150407]) (by decide +kernel)
def pv2105699 : PrimeValue := ⟨2105699, pr2105699⟩
private theorem pr2105819 : Nat.Prime 2105819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv37,pv199]) (by decide +kernel)
def pv2105819 : PrimeValue := ⟨2105819, pr2105819⟩
private theorem pr2105963 : Nat.Prime 2105963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1052981]) (by decide +kernel)
def pv2105963 : PrimeValue := ⟨2105963, pr2105963⟩
private theorem pr2106059 : Nat.Prime 2106059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1053029]) (by decide +kernel)
def pv2106059 : PrimeValue := ⟨2106059, pr2106059⟩
private theorem pr2106089 : Nat.Prime 2106089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv6421]) (by decide +kernel)
def pv2106089 : PrimeValue := ⟨2106089, pr2106089⟩
private theorem pr2106239 : Nat.Prime 2106239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv137,pv7687]) (by decide +kernel)
def pv2106239 : PrimeValue := ⟨2106239, pr2106239⟩
private theorem pr2106353 : Nat.Prime 2106353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv2801]) (by decide +kernel)
def pv2106353 : PrimeValue := ⟨2106353, pr2106353⟩
private theorem pr2106431 : Nat.Prime 2106431 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv210643]) (by decide +kernel)
def pv2106431 : PrimeValue := ⟨2106431, pr2106431⟩
private theorem pr2106491 : Nat.Prime 2106491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv313,pv673]) (by decide +kernel)
def pv2106491 : PrimeValue := ⟨2106491, pr2106491⟩
private theorem pr2106551 : Nat.Prime 2106551 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv42131]) (by decide +kernel)
def pv2106551 : PrimeValue := ⟨2106551, pr2106551⟩
private theorem pr2106953 : Nat.Prime 2106953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv263369]) (by decide +kernel)
def pv2106953 : PrimeValue := ⟨2106953, pr2106953⟩
private theorem pr2107103 : Nat.Prime 2107103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv1053551]) (by decide +kernel)
def pv2107103 : PrimeValue := ⟨2107103, pr2107103⟩
private theorem pr2107403 : Nat.Prime 2107403 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv95791]) (by decide +kernel)
def pv2107403 : PrimeValue := ⟨2107403, pr2107403⟩
private theorem pr2107529 : Nat.Prime 2107529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv131,pv2011]) (by decide +kernel)
def pv2107529 : PrimeValue := ⟨2107529, pr2107529⟩
private theorem pr2107751 : Nat.Prime 2107751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv8431]) (by decide +kernel)
def pv2107751 : PrimeValue := ⟨2107751, pr2107751⟩
private theorem pr2108003 : Nat.Prime 2108003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv81077]) (by decide +kernel)
def pv2108003 : PrimeValue := ⟨2108003, pr2108003⟩
private theorem pr2108033 : Nat.Prime 2108033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv383]) (by decide +kernel)
def pv2108033 : PrimeValue := ⟨2108033, pr2108033⟩
private theorem pr2108063 : Nat.Prime 2108063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv31,pv281]) (by decide +kernel)
def pv2108063 : PrimeValue := ⟨2108063, pr2108063⟩
private theorem pr2108531 : Nat.Prime 2108531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv210853]) (by decide +kernel)
def pv2108531 : PrimeValue := ⟨2108531, pr2108531⟩
private theorem pr2108993 : Nat.Prime 2108993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv1063]) (by decide +kernel)
def pv2108993 : PrimeValue := ⟨2108993, pr2108993⟩
private theorem pr2109053 : Nat.Prime 2109053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv47933]) (by decide +kernel)
def pv2109053 : PrimeValue := ⟨2109053, pr2109053⟩
private theorem pr2109179 : Nat.Prime 2109179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv34019]) (by decide +kernel)
def pv2109179 : PrimeValue := ⟨2109179, pr2109179⟩
private theorem pr2109311 : Nat.Prime 2109311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv30133]) (by decide +kernel)
def pv2109311 : PrimeValue := ⟨2109311, pr2109311⟩
private theorem pr2109449 : Nat.Prime 2109449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv23971]) (by decide +kernel)
def pv2109449 : PrimeValue := ⟨2109449, pr2109449⟩
private theorem pr2109641 : Nat.Prime 2109641 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv4057]) (by decide +kernel)
def pv2109641 : PrimeValue := ⟨2109641, pr2109641⟩
private theorem pr2109743 : Nat.Prime 2109743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv139,pv7589]) (by decide +kernel)
def pv2109743 : PrimeValue := ⟨2109743, pr2109743⟩
private theorem pr2109791 : Nat.Prime 2109791 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv23,pv9173]) (by decide +kernel)
def pv2109791 : PrimeValue := ⟨2109791, pr2109791⟩
private theorem pr2109911 : Nat.Prime 2109911 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv19181]) (by decide +kernel)
def pv2109911 : PrimeValue := ⟨2109911, pr2109911⟩
private theorem pr2110019 : Nat.Prime 2110019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv22447]) (by decide +kernel)
def pv2110019 : PrimeValue := ⟨2110019, pr2110019⟩
private theorem pr2110103 : Nat.Prime 2110103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv55529]) (by decide +kernel)
def pv2110103 : PrimeValue := ⟨2110103, pr2110103⟩
private theorem pr2110259 : Nat.Prime 2110259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv28517]) (by decide +kernel)
def pv2110259 : PrimeValue := ⟨2110259, pr2110259⟩
private theorem pr2110343 : Nat.Prime 2110343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv23,pv3529]) (by decide +kernel)
def pv2110343 : PrimeValue := ⟨2110343, pr2110343⟩
private theorem pr2110469 : Nat.Prime 2110469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv4931]) (by decide +kernel)
def pv2110469 : PrimeValue := ⟨2110469, pr2110469⟩
private theorem pr2110523 : Nat.Prime 2110523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1055261]) (by decide +kernel)
def pv2110523 : PrimeValue := ⟨2110523, pr2110523⟩
private theorem pr2110709 : Nat.Prime 2110709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv3361]) (by decide +kernel)
def pv2110709 : PrimeValue := ⟨2110709, pr2110709⟩
private theorem pr2110781 : Nat.Prime 2110781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv15077]) (by decide +kernel)
def pv2110781 : PrimeValue := ⟨2110781, pr2110781⟩
private theorem pr2111159 : Nat.Prime 2111159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv150797]) (by decide +kernel)
def pv2111159 : PrimeValue := ⟨2111159, pr2111159⟩
private theorem pr2111309 : Nat.Prime 2111309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv53,pv433]) (by decide +kernel)
def pv2111309 : PrimeValue := ⟨2111309, pr2111309⟩
private theorem pr2111513 : Nat.Prime 2111513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv79,pv257]) (by decide +kernel)
def pv2111513 : PrimeValue := ⟨2111513, pr2111513⟩
private theorem pr2111633 : Nat.Prime 2111633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv271,pv487]) (by decide +kernel)
def pv2111633 : PrimeValue := ⟨2111633, pr2111633⟩
private theorem pr2111729 : Nat.Prime 2111729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv2237]) (by decide +kernel)
def pv2111729 : PrimeValue := ⟨2111729, pr2111729⟩
private theorem pr2111771 : Nat.Prime 2111771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv211177]) (by decide +kernel)
def pv2111771 : PrimeValue := ⟨2111771, pr2111771⟩
private theorem pr2112191 : Nat.Prime 2112191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv211219]) (by decide +kernel)
def pv2112191 : PrimeValue := ⟨2112191, pr2112191⟩
private theorem pr2112413 : Nat.Prime 2112413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv22961]) (by decide +kernel)
def pv2112413 : PrimeValue := ⟨2112413, pr2112413⟩
private theorem pr2112419 : Nat.Prime 2112419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv29,pv43]) (by decide +kernel)
def pv2112419 : PrimeValue := ⟨2112419, pr2112419⟩
private theorem pr2112713 : Nat.Prime 2112713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv31,pv1217]) (by decide +kernel)
def pv2112713 : PrimeValue := ⟨2112713, pr2112713⟩
private theorem pr2112893 : Nat.Prime 2112893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv528223]) (by decide +kernel)
def pv2112893 : PrimeValue := ⟨2112893, pr2112893⟩
private theorem pr2113109 : Nat.Prime 2113109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv653,pv809]) (by decide +kernel)
def pv2113109 : PrimeValue := ⟨2113109, pr2113109⟩
private theorem pr2113211 : Nat.Prime 2113211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv19211]) (by decide +kernel)
def pv2113211 : PrimeValue := ⟨2113211, pr2113211⟩
private theorem pr2113229 : Nat.Prime 2113229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv40639]) (by decide +kernel)
def pv2113229 : PrimeValue := ⟨2113229, pr2113229⟩
private theorem pr2113451 : Nat.Prime 2113451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv983]) (by decide +kernel)
def pv2113451 : PrimeValue := ⟨2113451, pr2113451⟩
private theorem pr2113469 : Nat.Prime 2113469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv41,pv263]) (by decide +kernel)
def pv2113469 : PrimeValue := ⟨2113469, pr2113469⟩
private theorem pr2113511 : Nat.Prime 2113511 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv109,pv277]) (by decide +kernel)
def pv2113511 : PrimeValue := ⟨2113511, pr2113511⟩
private theorem pr2113913 : Nat.Prime 2113913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv139,pv1901]) (by decide +kernel)
def pv2113913 : PrimeValue := ⟨2113913, pr2113913⟩
private theorem pr2114039 : Nat.Prime 2114039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv1057019]) (by decide +kernel)
def pv2114039 : PrimeValue := ⟨2114039, pr2114039⟩
private theorem pr2114243 : Nat.Prime 2114243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv233,pv349]) (by decide +kernel)
def pv2114243 : PrimeValue := ⟨2114243, pr2114243⟩
private theorem pr2114363 : Nat.Prime 2114363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1057181]) (by decide +kernel)
def pv2114363 : PrimeValue := ⟨2114363, pr2114363⟩
private theorem pr2114369 : Nat.Prime 2114369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv33037]) (by decide +kernel)
def pv2114369 : PrimeValue := ⟨2114369, pr2114369⟩
private theorem pr2114393 : Nat.Prime 2114393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv17,pv2221]) (by decide +kernel)
def pv2114393 : PrimeValue := ⟨2114393, pr2114393⟩
private theorem pr2114429 : Nat.Prime 2114429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv331,pv1597]) (by decide +kernel)
def pv2114429 : PrimeValue := ⟨2114429, pr2114429⟩
private theorem pr2114771 : Nat.Prime 2114771 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv30211]) (by decide +kernel)
def pv2114771 : PrimeValue := ⟨2114771, pr2114771⟩
private theorem pr2115059 : Nat.Prime 2115059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv127,pv757]) (by decide +kernel)
def pv2115059 : PrimeValue := ⟨2115059, pr2115059⟩
private theorem pr2115101 : Nat.Prime 2115101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv1627]) (by decide +kernel)
def pv2115101 : PrimeValue := ⟨2115101, pr2115101⟩
private theorem pr2115461 : Nat.Prime 2115461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv293]) (by decide +kernel)
def pv2115461 : PrimeValue := ⟨2115461, pr2115461⟩
private theorem pr2115713 : Nat.Prime 2115713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv16529]) (by decide +kernel)
def pv2115713 : PrimeValue := ⟨2115713, pr2115713⟩
private theorem pr2115983 : Nat.Prime 2115983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv96181]) (by decide +kernel)
def pv2115983 : PrimeValue := ⟨2115983, pr2115983⟩
private theorem pr2116409 : Nat.Prime 2116409 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv7,pv5399]) (by decide +kernel)
def pv2116409 : PrimeValue := ⟨2116409, pr2116409⟩
private theorem pr2117051 : Nat.Prime 2117051 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv3257]) (by decide +kernel)
def pv2117051 : PrimeValue := ⟨2117051, pr2117051⟩
private theorem pr2117411 : Nat.Prime 2117411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv211741]) (by decide +kernel)
def pv2117411 : PrimeValue := ⟨2117411, pr2117411⟩
private theorem pr2117663 : Nat.Prime 2117663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv83,pv12757]) (by decide +kernel)
def pv2117663 : PrimeValue := ⟨2117663, pr2117663⟩
private theorem pr2118359 : Nat.Prime 2118359 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv96289]) (by decide +kernel)
def pv2118359 : PrimeValue := ⟨2118359, pr2118359⟩
private theorem pr2118491 : Nat.Prime 2118491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv19259]) (by decide +kernel)
def pv2118491 : PrimeValue := ⟨2118491, pr2118491⟩
private theorem pr2119259 : Nat.Prime 2119259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv19993]) (by decide +kernel)
def pv2119259 : PrimeValue := ⟨2119259, pr2119259⟩
private theorem pr2119739 : Nat.Prime 2119739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv7019]) (by decide +kernel)
def pv2119739 : PrimeValue := ⟨2119739, pr2119739⟩
private theorem pr2120021 : Nat.Prime 2120021 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv19,pv797]) (by decide +kernel)
def pv2120021 : PrimeValue := ⟨2120021, pr2120021⟩
private theorem pr2120249 : Nat.Prime 2120249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv19,pv29,pv37]) (by decide +kernel)
def pv2120249 : PrimeValue := ⟨2120249, pr2120249⟩
private theorem pr2120309 : Nat.Prime 2120309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv31181]) (by decide +kernel)
def pv2120309 : PrimeValue := ⟨2120309, pr2120309⟩
private theorem pr2120411 : Nat.Prime 2120411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv12473]) (by decide +kernel)
def pv2120411 : PrimeValue := ⟨2120411, pr2120411⟩
private theorem pr2120549 : Nat.Prime 2120549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv530137]) (by decide +kernel)
def pv2120549 : PrimeValue := ⟨2120549, pr2120549⟩
private theorem pr2120753 : Nat.Prime 2120753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv132547]) (by decide +kernel)
def pv2120753 : PrimeValue := ⟨2120753, pr2120753⟩
private theorem pr2120819 : Nat.Prime 2120819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv19,pv67]) (by decide +kernel)
def pv2120819 : PrimeValue := ⟨2120819, pr2120819⟩
private theorem pr2120879 : Nat.Prime 2120879 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv373,pv2843]) (by decide +kernel)
def pv2120879 : PrimeValue := ⟨2120879, pr2120879⟩
private theorem pr2121011 : Nat.Prime 2121011 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv113,pv1877]) (by decide +kernel)
def pv2121011 : PrimeValue := ⟨2121011, pr2121011⟩
private theorem pr2121029 : Nat.Prime 2121029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv5827]) (by decide +kernel)
def pv2121029 : PrimeValue := ⟨2121029, pr2121029⟩
private theorem pr2121461 : Nat.Prime 2121461 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv9643]) (by decide +kernel)
def pv2121461 : PrimeValue := ⟨2121461, pr2121461⟩
private theorem pr2121569 : Nat.Prime 2121569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv167,pv397]) (by decide +kernel)
def pv2121569 : PrimeValue := ⟨2121569, pr2121569⟩
private theorem pr2121653 : Nat.Prime 2121653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv40801]) (by decide +kernel)
def pv2121653 : PrimeValue := ⟨2121653, pr2121653⟩
private theorem pr2121803 : Nat.Prime 2121803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv53,pv541]) (by decide +kernel)
def pv2121803 : PrimeValue := ⟨2121803, pr2121803⟩
private theorem pr2121809 : Nat.Prime 2121809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv101]) (by decide +kernel)
def pv2121809 : PrimeValue := ⟨2121809, pr2121809⟩
private theorem pr2121989 : Nat.Prime 2121989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv29,pv1663]) (by decide +kernel)
def pv2121989 : PrimeValue := ⟨2121989, pr2121989⟩
private theorem pr2122013 : Nat.Prime 2122013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv109,pv157]) (by decide +kernel)
def pv2122013 : PrimeValue := ⟨2122013, pr2122013⟩
private theorem pr2122181 : Nat.Prime 2122181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv106109]) (by decide +kernel)
def pv2122181 : PrimeValue := ⟨2122181, pr2122181⟩
private theorem pr2122409 : Nat.Prime 2122409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv359,pv739]) (by decide +kernel)
def pv2122409 : PrimeValue := ⟨2122409, pr2122409⟩
private theorem pr2122619 : Nat.Prime 2122619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv349,pv3041]) (by decide +kernel)
def pv2122619 : PrimeValue := ⟨2122619, pr2122619⟩
private theorem pr2122721 : Nat.Prime 2122721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13267]) (by decide +kernel)
def pv2122721 : PrimeValue := ⟨2122721, pr2122721⟩
private theorem pr2123063 : Nat.Prime 2123063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv41,pv1523]) (by decide +kernel)
def pv2123063 : PrimeValue := ⟨2123063, pr2123063⟩
private theorem pr2123783 : Nat.Prime 2123783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv55889]) (by decide +kernel)
def pv2123783 : PrimeValue := ⟨2123783, pr2123783⟩
private theorem pr2123879 : Nat.Prime 2123879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv17,pv62467]) (by decide +kernel)
def pv2123879 : PrimeValue := ⟨2123879, pr2123879⟩
private theorem pr2123909 : Nat.Prime 2123909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv530977]) (by decide +kernel)
def pv2123909 : PrimeValue := ⟨2123909, pr2123909⟩
private theorem pr2124173 : Nat.Prime 2124173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv531043]) (by decide +kernel)
def pv2124173 : PrimeValue := ⟨2124173, pr2124173⟩
private theorem pr2124359 : Nat.Prime 2124359 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv331,pv3209]) (by decide +kernel)
def pv2124359 : PrimeValue := ⟨2124359, pr2124359⟩
private theorem pr2124491 : Nat.Prime 2124491 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv17,pv12497]) (by decide +kernel)
def pv2124491 : PrimeValue := ⟨2124491, pr2124491⟩
private theorem pr2124761 : Nat.Prime 2124761 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv11,pv439]) (by decide +kernel)
def pv2124761 : PrimeValue := ⟨2124761, pr2124761⟩
private theorem pr2125373 : Nat.Prime 2125373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv531343]) (by decide +kernel)
def pv2125373 : PrimeValue := ⟨2125373, pr2125373⟩
private theorem pr2125451 : Nat.Prime 2125451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv42509]) (by decide +kernel)
def pv2125451 : PrimeValue := ⟨2125451, pr2125451⟩
private theorem pr2125661 : Nat.Prime 2125661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv4621]) (by decide +kernel)
def pv2125661 : PrimeValue := ⟨2125661, pr2125661⟩
private theorem pr2125703 : Nat.Prime 2125703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv193,pv5507]) (by decide +kernel)
def pv2125703 : PrimeValue := ⟨2125703, pr2125703⟩
private theorem pr2126339 : Nat.Prime 2126339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv61,pv601]) (by decide +kernel)
def pv2126339 : PrimeValue := ⟨2126339, pr2126339⟩
private theorem pr2126363 : Nat.Prime 2126363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv151883]) (by decide +kernel)
def pv2126363 : PrimeValue := ⟨2126363, pr2126363⟩
private theorem pr2126441 : Nat.Prime 2126441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv53161]) (by decide +kernel)
def pv2126441 : PrimeValue := ⟨2126441, pr2126441⟩
private theorem pr2126549 : Nat.Prime 2126549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv531637]) (by decide +kernel)
def pv2126549 : PrimeValue := ⟨2126549, pr2126549⟩
private theorem pr2126573 : Nat.Prime 2126573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv53,pv1433]) (by decide +kernel)
def pv2126573 : PrimeValue := ⟨2126573, pr2126573⟩
private theorem pr2126633 : Nat.Prime 2126633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv19,pv823]) (by decide +kernel)
def pv2126633 : PrimeValue := ⟨2126633, pr2126633⟩
private theorem pr2126783 : Nat.Prime 2126783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv73,pv2081]) (by decide +kernel)
def pv2126783 : PrimeValue := ⟨2126783, pr2126783⟩
private theorem pr2126849 : Nat.Prime 2126849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv67]) (by decide +kernel)
def pv2126849 : PrimeValue := ⟨2126849, pr2126849⟩
private theorem pr2126933 : Nat.Prime 2126933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv257,pv2069]) (by decide +kernel)
def pv2126933 : PrimeValue := ⟨2126933, pr2126933⟩
private theorem pr2127299 : Nat.Prime 2127299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1063649]) (by decide +kernel)
def pv2127299 : PrimeValue := ⟨2127299, pr2127299⟩
private theorem pr2127341 : Nat.Prime 2127341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv106367]) (by decide +kernel)
def pv2127341 : PrimeValue := ⟨2127341, pr2127341⟩
private theorem pr2127761 : Nat.Prime 2127761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv26597]) (by decide +kernel)
def pv2127761 : PrimeValue := ⟨2127761, pr2127761⟩
private theorem pr2128001 : Nat.Prime 2128001 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv19]) (by decide +kernel)
def pv2128001 : PrimeValue := ⟨2128001, pr2128001⟩
private theorem pr2128253 : Nat.Prime 2128253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv2621]) (by decide +kernel)
def pv2128253 : PrimeValue := ⟨2128253, pr2128253⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
