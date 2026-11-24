/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table000
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table000.pv2
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

def pv2 : PrimeValue := ⟨2, by decide +kernel⟩
def pv3 : PrimeValue := ⟨3,
  checkPrime_prime (q := pv2) (ls := [pv2])
    (by decide +kernel)⟩
def pv5 : PrimeValue := ⟨5,
  checkPrime_prime (q := pv2) (ls := [pv2])
    (by decide +kernel)⟩
def pv7 : PrimeValue := ⟨7,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv11 : PrimeValue := ⟨11,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5])
    (by decide +kernel)⟩
def pv13 : PrimeValue := ⟨13,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv17 : PrimeValue := ⟨17,
  checkPrime_prime (q := pv3) (ls := [pv2])
    (by decide +kernel)⟩
def pv19 : PrimeValue := ⟨19,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv23 : PrimeValue := ⟨23,
  checkPrime_prime (q := pv5) (ls := [pv2,pv11])
    (by decide +kernel)⟩
def pv29 : PrimeValue := ⟨29,
  checkPrime_prime (q := pv2) (ls := [pv2,pv7])
    (by decide +kernel)⟩
def pv31 : PrimeValue := ⟨31,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5])
    (by decide +kernel)⟩
def pv37 : PrimeValue := ⟨37,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv41 : PrimeValue := ⟨41,
  checkPrime_prime (q := pv7) (ls := [pv2,pv5])
    (by decide +kernel)⟩
def pv43 : PrimeValue := ⟨43,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7])
    (by decide +kernel)⟩
def pv47 : PrimeValue := ⟨47,
  checkPrime_prime (q := pv5) (ls := [pv2,pv23])
    (by decide +kernel)⟩
def pv53 : PrimeValue := ⟨53,
  checkPrime_prime (q := pv2) (ls := [pv2,pv13])
    (by decide +kernel)⟩
def pv59 : PrimeValue := ⟨59,
  checkPrime_prime (q := pv2) (ls := [pv2,pv29])
    (by decide +kernel)⟩
def pv61 : PrimeValue := ⟨61,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5])
    (by decide +kernel)⟩
def pv67 : PrimeValue := ⟨67,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11])
    (by decide +kernel)⟩
def pv71 : PrimeValue := ⟨71,
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7])
    (by decide +kernel)⟩
def pv73 : PrimeValue := ⟨73,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv79 : PrimeValue := ⟨79,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13])
    (by decide +kernel)⟩
def pv83 : PrimeValue := ⟨83,
  checkPrime_prime (q := pv2) (ls := [pv2,pv41])
    (by decide +kernel)⟩
def pv89 : PrimeValue := ⟨89,
  checkPrime_prime (q := pv3) (ls := [pv2,pv11])
    (by decide +kernel)⟩
def pv97 : PrimeValue := ⟨97,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv101 : PrimeValue := ⟨101,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5])
    (by decide +kernel)⟩
def pv103 : PrimeValue := ⟨103,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17])
    (by decide +kernel)⟩
def pv107 : PrimeValue := ⟨107,
  checkPrime_prime (q := pv2) (ls := [pv2,pv53])
    (by decide +kernel)⟩
def pv109 : PrimeValue := ⟨109,
  checkPrime_prime (q := pv11) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv113 : PrimeValue := ⟨113,
  checkPrime_prime (q := pv3) (ls := [pv2,pv7])
    (by decide +kernel)⟩
def pv127 : PrimeValue := ⟨127,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7])
    (by decide +kernel)⟩
def pv131 : PrimeValue := ⟨131,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13])
    (by decide +kernel)⟩
def pv137 : PrimeValue := ⟨137,
  checkPrime_prime (q := pv3) (ls := [pv2,pv17])
    (by decide +kernel)⟩
def pv139 : PrimeValue := ⟨139,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23])
    (by decide +kernel)⟩
def pv149 : PrimeValue := ⟨149,
  checkPrime_prime (q := pv2) (ls := [pv2,pv37])
    (by decide +kernel)⟩
def pv151 : PrimeValue := ⟨151,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5])
    (by decide +kernel)⟩
def pv157 : PrimeValue := ⟨157,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13])
    (by decide +kernel)⟩
def pv163 : PrimeValue := ⟨163,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv167 : PrimeValue := ⟨167,
  checkPrime_prime (q := pv5) (ls := [pv2,pv83])
    (by decide +kernel)⟩
def pv173 : PrimeValue := ⟨173,
  checkPrime_prime (q := pv2) (ls := [pv2,pv43])
    (by decide +kernel)⟩
def pv179 : PrimeValue := ⟨179,
  checkPrime_prime (q := pv2) (ls := [pv2,pv89])
    (by decide +kernel)⟩
def pv181 : PrimeValue := ⟨181,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5])
    (by decide +kernel)⟩
def pv191 : PrimeValue := ⟨191,
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv19])
    (by decide +kernel)⟩
def pv193 : PrimeValue := ⟨193,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv197 : PrimeValue := ⟨197,
  checkPrime_prime (q := pv2) (ls := [pv2,pv7])
    (by decide +kernel)⟩
def pv199 : PrimeValue := ⟨199,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11])
    (by decide +kernel)⟩
def pv211 : PrimeValue := ⟨211,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7])
    (by decide +kernel)⟩
def pv223 : PrimeValue := ⟨223,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37])
    (by decide +kernel)⟩
def pv227 : PrimeValue := ⟨227,
  checkPrime_prime (q := pv2) (ls := [pv2,pv113])
    (by decide +kernel)⟩
def pv229 : PrimeValue := ⟨229,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19])
    (by decide +kernel)⟩
def pv233 : PrimeValue := ⟨233,
  checkPrime_prime (q := pv3) (ls := [pv2,pv29])
    (by decide +kernel)⟩
def pv239 : PrimeValue := ⟨239,
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv17])
    (by decide +kernel)⟩
def pv241 : PrimeValue := ⟨241,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5])
    (by decide +kernel)⟩
def pv251 : PrimeValue := ⟨251,
  checkPrime_prime (q := pv11) (ls := [pv2,pv5])
    (by decide +kernel)⟩
def pv257 : PrimeValue := ⟨257,
  checkPrime_prime (q := pv3) (ls := [pv2])
    (by decide +kernel)⟩
def pv263 : PrimeValue := ⟨263,
  checkPrime_prime (q := pv5) (ls := [pv2,pv131])
    (by decide +kernel)⟩
def pv269 : PrimeValue := ⟨269,
  checkPrime_prime (q := pv2) (ls := [pv2,pv67])
    (by decide +kernel)⟩
def pv271 : PrimeValue := ⟨271,
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv5])
    (by decide +kernel)⟩
def pv277 : PrimeValue := ⟨277,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23])
    (by decide +kernel)⟩
def pv281 : PrimeValue := ⟨281,
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7])
    (by decide +kernel)⟩
def pv283 : PrimeValue := ⟨283,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47])
    (by decide +kernel)⟩
def pv293 : PrimeValue := ⟨293,
  checkPrime_prime (q := pv2) (ls := [pv2,pv73])
    (by decide +kernel)⟩
def pv307 : PrimeValue := ⟨307,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17])
    (by decide +kernel)⟩
def pv311 : PrimeValue := ⟨311,
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv31])
    (by decide +kernel)⟩
def pv313 : PrimeValue := ⟨313,
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13])
    (by decide +kernel)⟩
def pv317 : PrimeValue := ⟨317,
  checkPrime_prime (q := pv2) (ls := [pv2,pv79])
    (by decide +kernel)⟩
def pv331 : PrimeValue := ⟨331,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11])
    (by decide +kernel)⟩
def pv337 : PrimeValue := ⟨337,
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7])
    (by decide +kernel)⟩
def pv347 : PrimeValue := ⟨347,
  checkPrime_prime (q := pv2) (ls := [pv2,pv173])
    (by decide +kernel)⟩
def pv349 : PrimeValue := ⟨349,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29])
    (by decide +kernel)⟩
def pv353 : PrimeValue := ⟨353,
  checkPrime_prime (q := pv3) (ls := [pv2,pv11])
    (by decide +kernel)⟩
def pv359 : PrimeValue := ⟨359,
  checkPrime_prime (q := pv7) (ls := [pv2,pv179])
    (by decide +kernel)⟩
def pv367 : PrimeValue := ⟨367,
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv61])
    (by decide +kernel)⟩
def pv373 : PrimeValue := ⟨373,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31])
    (by decide +kernel)⟩
def pv379 : PrimeValue := ⟨379,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7])
    (by decide +kernel)⟩
def pv383 : PrimeValue := ⟨383,
  checkPrime_prime (q := pv5) (ls := [pv2,pv191])
    (by decide +kernel)⟩
def pv389 : PrimeValue := ⟨389,
  checkPrime_prime (q := pv2) (ls := [pv2,pv97])
    (by decide +kernel)⟩
def pv397 : PrimeValue := ⟨397,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11])
    (by decide +kernel)⟩
def pv401 : PrimeValue := ⟨401,
  checkPrime_prime (q := pv3) (ls := [pv2,pv5])
    (by decide +kernel)⟩
def pv409 : PrimeValue := ⟨409,
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv17])
    (by decide +kernel)⟩
def pv419 : PrimeValue := ⟨419,
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19])
    (by decide +kernel)⟩
def pv421 : PrimeValue := ⟨421,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7])
    (by decide +kernel)⟩
def pv431 : PrimeValue := ⟨431,
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv43])
    (by decide +kernel)⟩
def pv433 : PrimeValue := ⟨433,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv439 : PrimeValue := ⟨439,
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv73])
    (by decide +kernel)⟩
def pv443 : PrimeValue := ⟨443,
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17])
    (by decide +kernel)⟩
def pv449 : PrimeValue := ⟨449,
  checkPrime_prime (q := pv3) (ls := [pv2,pv7])
    (by decide +kernel)⟩
def pv457 : PrimeValue := ⟨457,
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19])
    (by decide +kernel)⟩
def pv461 : PrimeValue := ⟨461,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23])
    (by decide +kernel)⟩
def pv463 : PrimeValue := ⟨463,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11])
    (by decide +kernel)⟩
def pv467 : PrimeValue := ⟨467,
  checkPrime_prime (q := pv2) (ls := [pv2,pv233])
    (by decide +kernel)⟩
def pv479 : PrimeValue := ⟨479,
  checkPrime_prime (q := pv13) (ls := [pv2,pv239])
    (by decide +kernel)⟩
def pv487 : PrimeValue := ⟨487,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv491 : PrimeValue := ⟨491,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7])
    (by decide +kernel)⟩
def pv499 : PrimeValue := ⟨499,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv83])
    (by decide +kernel)⟩
def pv503 : PrimeValue := ⟨503,
  checkPrime_prime (q := pv5) (ls := [pv2,pv251])
    (by decide +kernel)⟩
def pv509 : PrimeValue := ⟨509,
  checkPrime_prime (q := pv2) (ls := [pv2,pv127])
    (by decide +kernel)⟩
def pv521 : PrimeValue := ⟨521,
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13])
    (by decide +kernel)⟩
def pv523 : PrimeValue := ⟨523,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29])
    (by decide +kernel)⟩
def pv541 : PrimeValue := ⟨541,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5])
    (by decide +kernel)⟩
def pv547 : PrimeValue := ⟨547,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13])
    (by decide +kernel)⟩
def pv557 : PrimeValue := ⟨557,
  checkPrime_prime (q := pv2) (ls := [pv2,pv139])
    (by decide +kernel)⟩
def pv563 : PrimeValue := ⟨563,
  checkPrime_prime (q := pv2) (ls := [pv2,pv281])
    (by decide +kernel)⟩
def pv569 : PrimeValue := ⟨569,
  checkPrime_prime (q := pv3) (ls := [pv2,pv71])
    (by decide +kernel)⟩
def pv571 : PrimeValue := ⟨571,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv19])
    (by decide +kernel)⟩
def pv577 : PrimeValue := ⟨577,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv587 : PrimeValue := ⟨587,
  checkPrime_prime (q := pv2) (ls := [pv2,pv293])
    (by decide +kernel)⟩
def pv593 : PrimeValue := ⟨593,
  checkPrime_prime (q := pv3) (ls := [pv2,pv37])
    (by decide +kernel)⟩
def pv599 : PrimeValue := ⟨599,
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv23])
    (by decide +kernel)⟩
def pv601 : PrimeValue := ⟨601,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5])
    (by decide +kernel)⟩
def pv607 : PrimeValue := ⟨607,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv101])
    (by decide +kernel)⟩
def pv613 : PrimeValue := ⟨613,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17])
    (by decide +kernel)⟩
def pv617 : PrimeValue := ⟨617,
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11])
    (by decide +kernel)⟩
def pv619 : PrimeValue := ⟨619,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103])
    (by decide +kernel)⟩
def pv631 : PrimeValue := ⟨631,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7])
    (by decide +kernel)⟩
def pv641 : PrimeValue := ⟨641,
  checkPrime_prime (q := pv3) (ls := [pv2,pv5])
    (by decide +kernel)⟩
def pv643 : PrimeValue := ⟨643,
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv107])
    (by decide +kernel)⟩
def pv647 : PrimeValue := ⟨647,
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv19])
    (by decide +kernel)⟩
def pv653 : PrimeValue := ⟨653,
  checkPrime_prime (q := pv2) (ls := [pv2,pv163])
    (by decide +kernel)⟩
def pv659 : PrimeValue := ⟨659,
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv47])
    (by decide +kernel)⟩
def pv661 : PrimeValue := ⟨661,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11])
    (by decide +kernel)⟩
def pv673 : PrimeValue := ⟨673,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7])
    (by decide +kernel)⟩
def pv677 : PrimeValue := ⟨677,
  checkPrime_prime (q := pv2) (ls := [pv2,pv13])
    (by decide +kernel)⟩
def pv683 : PrimeValue := ⟨683,
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv31])
    (by decide +kernel)⟩
def pv691 : PrimeValue := ⟨691,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv23])
    (by decide +kernel)⟩
def pv701 : PrimeValue := ⟨701,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7])
    (by decide +kernel)⟩
def pv709 : PrimeValue := ⟨709,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59])
    (by decide +kernel)⟩
def pv719 : PrimeValue := ⟨719,
  checkPrime_prime (q := pv11) (ls := [pv2,pv359])
    (by decide +kernel)⟩
def pv727 : PrimeValue := ⟨727,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11])
    (by decide +kernel)⟩
def pv733 : PrimeValue := ⟨733,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv61])
    (by decide +kernel)⟩
def pv739 : PrimeValue := ⟨739,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41])
    (by decide +kernel)⟩
def pv743 : PrimeValue := ⟨743,
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv53])
    (by decide +kernel)⟩
def pv751 : PrimeValue := ⟨751,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5])
    (by decide +kernel)⟩
def pv757 : PrimeValue := ⟨757,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7])
    (by decide +kernel)⟩
def pv761 : PrimeValue := ⟨761,
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19])
    (by decide +kernel)⟩
def pv769 : PrimeValue := ⟨769,
  checkPrime_prime (q := pv11) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv773 : PrimeValue := ⟨773,
  checkPrime_prime (q := pv2) (ls := [pv2,pv193])
    (by decide +kernel)⟩
def pv787 : PrimeValue := ⟨787,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv131])
    (by decide +kernel)⟩
def pv797 : PrimeValue := ⟨797,
  checkPrime_prime (q := pv2) (ls := [pv2,pv199])
    (by decide +kernel)⟩
def pv809 : PrimeValue := ⟨809,
  checkPrime_prime (q := pv3) (ls := [pv2,pv101])
    (by decide +kernel)⟩
def pv811 : PrimeValue := ⟨811,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5])
    (by decide +kernel)⟩
def pv821 : PrimeValue := ⟨821,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41])
    (by decide +kernel)⟩
def pv823 : PrimeValue := ⟨823,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv137])
    (by decide +kernel)⟩
def pv827 : PrimeValue := ⟨827,
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv59])
    (by decide +kernel)⟩
def pv829 : PrimeValue := ⟨829,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23])
    (by decide +kernel)⟩
def pv839 : PrimeValue := ⟨839,
  checkPrime_prime (q := pv11) (ls := [pv2,pv419])
    (by decide +kernel)⟩
def pv853 : PrimeValue := ⟨853,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71])
    (by decide +kernel)⟩
def pv857 : PrimeValue := ⟨857,
  checkPrime_prime (q := pv3) (ls := [pv2,pv107])
    (by decide +kernel)⟩
def pv859 : PrimeValue := ⟨859,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13])
    (by decide +kernel)⟩
def pv863 : PrimeValue := ⟨863,
  checkPrime_prime (q := pv5) (ls := [pv2,pv431])
    (by decide +kernel)⟩
def pv877 : PrimeValue := ⟨877,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73])
    (by decide +kernel)⟩
def pv881 : PrimeValue := ⟨881,
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11])
    (by decide +kernel)⟩
def pv883 : PrimeValue := ⟨883,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7])
    (by decide +kernel)⟩
def pv887 : PrimeValue := ⟨887,
  checkPrime_prime (q := pv5) (ls := [pv2,pv443])
    (by decide +kernel)⟩
def pv907 : PrimeValue := ⟨907,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv151])
    (by decide +kernel)⟩
def pv911 : PrimeValue := ⟨911,
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv13])
    (by decide +kernel)⟩
def pv919 : PrimeValue := ⟨919,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17])
    (by decide +kernel)⟩
def pv929 : PrimeValue := ⟨929,
  checkPrime_prime (q := pv3) (ls := [pv2,pv29])
    (by decide +kernel)⟩
def pv937 : PrimeValue := ⟨937,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13])
    (by decide +kernel)⟩
def pv941 : PrimeValue := ⟨941,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47])
    (by decide +kernel)⟩
def pv947 : PrimeValue := ⟨947,
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv43])
    (by decide +kernel)⟩
def pv953 : PrimeValue := ⟨953,
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17])
    (by decide +kernel)⟩
def pv967 : PrimeValue := ⟨967,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv23])
    (by decide +kernel)⟩
def pv971 : PrimeValue := ⟨971,
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv97])
    (by decide +kernel)⟩
def pv977 : PrimeValue := ⟨977,
  checkPrime_prime (q := pv3) (ls := [pv2,pv61])
    (by decide +kernel)⟩
def pv983 : PrimeValue := ⟨983,
  checkPrime_prime (q := pv5) (ls := [pv2,pv491])
    (by decide +kernel)⟩
def pv991 : PrimeValue := ⟨991,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11])
    (by decide +kernel)⟩
def pv997 : PrimeValue := ⟨997,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv83])
    (by decide +kernel)⟩
def pv1009 : PrimeValue := ⟨1009,
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7])
    (by decide +kernel)⟩
def pv1013 : PrimeValue := ⟨1013,
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv23])
    (by decide +kernel)⟩
def pv1019 : PrimeValue := ⟨1019,
  checkPrime_prime (q := pv2) (ls := [pv2,pv509])
    (by decide +kernel)⟩
def pv1021 : PrimeValue := ⟨1021,
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv17])
    (by decide +kernel)⟩
def pv1031 : PrimeValue := ⟨1031,
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv103])
    (by decide +kernel)⟩
def pv1033 : PrimeValue := ⟨1033,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43])
    (by decide +kernel)⟩
def pv1039 : PrimeValue := ⟨1039,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv173])
    (by decide +kernel)⟩
def pv1049 : PrimeValue := ⟨1049,
  checkPrime_prime (q := pv3) (ls := [pv2,pv131])
    (by decide +kernel)⟩
def pv1051 : PrimeValue := ⟨1051,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7])
    (by decide +kernel)⟩
def pv1061 : PrimeValue := ⟨1061,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv53])
    (by decide +kernel)⟩
def pv1063 : PrimeValue := ⟨1063,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59])
    (by decide +kernel)⟩
def pv1069 : PrimeValue := ⟨1069,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv89])
    (by decide +kernel)⟩
def pv1087 : PrimeValue := ⟨1087,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv181])
    (by decide +kernel)⟩
def pv1091 : PrimeValue := ⟨1091,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv109])
    (by decide +kernel)⟩
def pv1093 : PrimeValue := ⟨1093,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13])
    (by decide +kernel)⟩
def pv1097 : PrimeValue := ⟨1097,
  checkPrime_prime (q := pv3) (ls := [pv2,pv137])
    (by decide +kernel)⟩
def pv1103 : PrimeValue := ⟨1103,
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv29])
    (by decide +kernel)⟩
def pv1109 : PrimeValue := ⟨1109,
  checkPrime_prime (q := pv2) (ls := [pv2,pv277])
    (by decide +kernel)⟩
def pv1117 : PrimeValue := ⟨1117,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31])
    (by decide +kernel)⟩
def pv1123 : PrimeValue := ⟨1123,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv17])
    (by decide +kernel)⟩
def pv1129 : PrimeValue := ⟨1129,
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv47])
    (by decide +kernel)⟩
def pv1151 : PrimeValue := ⟨1151,
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv23])
    (by decide +kernel)⟩
def pv1153 : PrimeValue := ⟨1153,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv1163 : PrimeValue := ⟨1163,
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv83])
    (by decide +kernel)⟩
def pv1171 : PrimeValue := ⟨1171,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13])
    (by decide +kernel)⟩
def pv1181 : PrimeValue := ⟨1181,
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv59])
    (by decide +kernel)⟩
def pv1187 : PrimeValue := ⟨1187,
  checkPrime_prime (q := pv2) (ls := [pv2,pv593])
    (by decide +kernel)⟩
def pv1193 : PrimeValue := ⟨1193,
  checkPrime_prime (q := pv3) (ls := [pv2,pv149])
    (by decide +kernel)⟩
def pv1201 : PrimeValue := ⟨1201,
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5])
    (by decide +kernel)⟩
def pv1213 : PrimeValue := ⟨1213,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv101])
    (by decide +kernel)⟩
def pv1217 : PrimeValue := ⟨1217,
  checkPrime_prime (q := pv3) (ls := [pv2,pv19])
    (by decide +kernel)⟩
def pv1223 : PrimeValue := ⟨1223,
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv47])
    (by decide +kernel)⟩
def pv1229 : PrimeValue := ⟨1229,
  checkPrime_prime (q := pv2) (ls := [pv2,pv307])
    (by decide +kernel)⟩
def pv1231 : PrimeValue := ⟨1231,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv41])
    (by decide +kernel)⟩
def pv1237 : PrimeValue := ⟨1237,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103])
    (by decide +kernel)⟩
def pv1249 : PrimeValue := ⟨1249,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13])
    (by decide +kernel)⟩
def pv1259 : PrimeValue := ⟨1259,
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv37])
    (by decide +kernel)⟩
def pv1277 : PrimeValue := ⟨1277,
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv29])
    (by decide +kernel)⟩
def pv1279 : PrimeValue := ⟨1279,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71])
    (by decide +kernel)⟩
def pv1283 : PrimeValue := ⟨1283,
  checkPrime_prime (q := pv2) (ls := [pv2,pv641])
    (by decide +kernel)⟩
def pv1289 : PrimeValue := ⟨1289,
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv23])
    (by decide +kernel)⟩
def pv1291 : PrimeValue := ⟨1291,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv43])
    (by decide +kernel)⟩
def pv1297 : PrimeValue := ⟨1297,
  checkPrime_prime (q := pv17) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv1301 : PrimeValue := ⟨1301,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13])
    (by decide +kernel)⟩
def pv1303 : PrimeValue := ⟨1303,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv31])
    (by decide +kernel)⟩
def pv1307 : PrimeValue := ⟨1307,
  checkPrime_prime (q := pv2) (ls := [pv2,pv653])
    (by decide +kernel)⟩
def pv1319 : PrimeValue := ⟨1319,
  checkPrime_prime (q := pv13) (ls := [pv2,pv659])
    (by decide +kernel)⟩
def pv1321 : PrimeValue := ⟨1321,
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11])
    (by decide +kernel)⟩
def pv1327 : PrimeValue := ⟨1327,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv17])
    (by decide +kernel)⟩
def pv1361 : PrimeValue := ⟨1361,
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17])
    (by decide +kernel)⟩
def pv1367 : PrimeValue := ⟨1367,
  checkPrime_prime (q := pv5) (ls := [pv2,pv683])
    (by decide +kernel)⟩
def pv1373 : PrimeValue := ⟨1373,
  checkPrime_prime (q := pv2) (ls := [pv2,pv7])
    (by decide +kernel)⟩
def pv1381 : PrimeValue := ⟨1381,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23])
    (by decide +kernel)⟩
def pv1399 : PrimeValue := ⟨1399,
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv233])
    (by decide +kernel)⟩
def pv1409 : PrimeValue := ⟨1409,
  checkPrime_prime (q := pv3) (ls := [pv2,pv11])
    (by decide +kernel)⟩
def pv1423 : PrimeValue := ⟨1423,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv79])
    (by decide +kernel)⟩
def pv1427 : PrimeValue := ⟨1427,
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv31])
    (by decide +kernel)⟩
def pv1429 : PrimeValue := ⟨1429,
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv17])
    (by decide +kernel)⟩
def pv1433 : PrimeValue := ⟨1433,
  checkPrime_prime (q := pv3) (ls := [pv2,pv179])
    (by decide +kernel)⟩
def pv1439 : PrimeValue := ⟨1439,
  checkPrime_prime (q := pv7) (ls := [pv2,pv719])
    (by decide +kernel)⟩
def pv1447 : PrimeValue := ⟨1447,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv241])
    (by decide +kernel)⟩
def pv1451 : PrimeValue := ⟨1451,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29])
    (by decide +kernel)⟩
def pv1453 : PrimeValue := ⟨1453,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11])
    (by decide +kernel)⟩
def pv1459 : PrimeValue := ⟨1459,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3])
    (by decide +kernel)⟩
def pv1471 : PrimeValue := ⟨1471,
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7])
    (by decide +kernel)⟩
def pv1481 : PrimeValue := ⟨1481,
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv37])
    (by decide +kernel)⟩
def pv1483 : PrimeValue := ⟨1483,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv19])
    (by decide +kernel)⟩
def pv1487 : PrimeValue := ⟨1487,
  checkPrime_prime (q := pv5) (ls := [pv2,pv743])
    (by decide +kernel)⟩
def pv1489 : PrimeValue := ⟨1489,
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv31])
    (by decide +kernel)⟩
def pv1493 : PrimeValue := ⟨1493,
  checkPrime_prime (q := pv2) (ls := [pv2,pv373])
    (by decide +kernel)⟩
def pv1499 : PrimeValue := ⟨1499,
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv107])
    (by decide +kernel)⟩
def pv1511 : PrimeValue := ⟨1511,
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv151])
    (by decide +kernel)⟩
def pv1523 : PrimeValue := ⟨1523,
  checkPrime_prime (q := pv2) (ls := [pv2,pv761])
    (by decide +kernel)⟩
def pv1531 : PrimeValue := ⟨1531,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17])
    (by decide +kernel)⟩
def pv1543 : PrimeValue := ⟨1543,
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv257])
    (by decide +kernel)⟩
def pv1549 : PrimeValue := ⟨1549,
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43])
    (by decide +kernel)⟩
def pv1553 : PrimeValue := ⟨1553,
  checkPrime_prime (q := pv3) (ls := [pv2,pv97])
    (by decide +kernel)⟩
def pv1559 : PrimeValue := ⟨1559,
  checkPrime_prime (q := pv19) (ls := [pv2,pv19,pv41])
    (by decide +kernel)⟩
def pv1567 : PrimeValue := ⟨1567,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29])
    (by decide +kernel)⟩
def pv1571 : PrimeValue := ⟨1571,
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv157])
    (by decide +kernel)⟩
def pv1579 : PrimeValue := ⟨1579,
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv263])
    (by decide +kernel)⟩
def pv1583 : PrimeValue := ⟨1583,
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv113])
    (by decide +kernel)⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
