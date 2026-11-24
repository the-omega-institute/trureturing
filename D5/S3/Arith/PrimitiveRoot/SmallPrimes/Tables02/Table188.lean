/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table188
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table188.pv459301
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table072
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table073

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr459301 : Nat.Prime 459301 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1531]) (by decide +kernel)
def pv459301 : PrimeValue := ⟨459301, pr459301⟩
private theorem pr459317 : Nat.Prime 459317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv73]) (by decide +kernel)
def pv459317 : PrimeValue := ⟨459317, pr459317⟩
private theorem pr459469 : Nat.Prime 459469 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv12763]) (by decide +kernel)
def pv459469 : PrimeValue := ⟨459469, pr459469⟩
private theorem pr459619 : Nat.Prime 459619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv76603]) (by decide +kernel)
def pv459619 : PrimeValue := ⟨459619, pr459619⟩
private theorem pr459631 : Nat.Prime 459631 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv5107]) (by decide +kernel)
def pv459631 : PrimeValue := ⟨459631, pr459631⟩
private theorem pr459649 : Nat.Prime 459649 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv459649 : PrimeValue := ⟨459649, pr459649⟩
private theorem pr459671 : Nat.Prime 459671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv43,pv1069]) (by decide +kernel)
def pv459671 : PrimeValue := ⟨459671, pr459671⟩
private theorem pr460099 : Nat.Prime 460099 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv25561]) (by decide +kernel)
def pv460099 : PrimeValue := ⟨460099, pr460099⟩
private theorem pr460531 : Nat.Prime 460531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv17,pv43]) (by decide +kernel)
def pv460531 : PrimeValue := ⟨460531, pr460531⟩
private theorem pr460619 : Nat.Prime 460619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv230309]) (by decide +kernel)
def pv460619 : PrimeValue := ⟨460619, pr460619⟩
private theorem pr460657 : Nat.Prime 460657 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv457]) (by decide +kernel)
def pv460657 : PrimeValue := ⟨460657, pr460657⟩
private theorem pr460841 : Nat.Prime 460841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv41,pv281]) (by decide +kernel)
def pv460841 : PrimeValue := ⟨460841, pr460841⟩
private theorem pr460891 : Nat.Prime 460891 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv569]) (by decide +kernel)
def pv460891 : PrimeValue := ⟨460891, pr460891⟩
private theorem pr460951 : Nat.Prime 460951 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv439]) (by decide +kernel)
def pv460951 : PrimeValue := ⟨460951, pr460951⟩
private theorem pr460969 : Nat.Prime 460969 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19207]) (by decide +kernel)
def pv460969 : PrimeValue := ⟨460969, pr460969⟩
private theorem pr461053 : Nat.Prime 461053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1423]) (by decide +kernel)
def pv461053 : PrimeValue := ⟨461053, pr461053⟩
private theorem pr461101 : Nat.Prime 461101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv53]) (by decide +kernel)
def pv461101 : PrimeValue := ⟨461101, pr461101⟩
private theorem pr461359 : Nat.Prime 461359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv71]) (by decide +kernel)
def pv461359 : PrimeValue := ⟨461359, pr461359⟩
private theorem pr461443 : Nat.Prime 461443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv76907]) (by decide +kernel)
def pv461443 : PrimeValue := ⟨461443, pr461443⟩
private theorem pr461507 : Nat.Prime 461507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv73,pv109]) (by decide +kernel)
def pv461507 : PrimeValue := ⟨461507, pr461507⟩
private theorem pr461599 : Nat.Prime 461599 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv107,pv719]) (by decide +kernel)
def pv461599 : PrimeValue := ⟨461599, pr461599⟩
private theorem pr461609 : Nat.Prime 461609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv8243]) (by decide +kernel)
def pv461609 : PrimeValue := ⟨461609, pr461609⟩
private theorem pr461639 : Nat.Prime 461639 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv230819]) (by decide +kernel)
def pv461639 : PrimeValue := ⟨461639, pr461639⟩
private theorem pr461717 : Nat.Prime 461717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv115429]) (by decide +kernel)
def pv461717 : PrimeValue := ⟨461717, pr461717⟩
private theorem pr461819 : Nat.Prime 461819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv32987]) (by decide +kernel)
def pv461819 : PrimeValue := ⟨461819, pr461819⟩
private theorem pr461887 : Nat.Prime 461887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv3347]) (by decide +kernel)
def pv461887 : PrimeValue := ⟨461887, pr461887⟩
private theorem pr462073 : Nat.Prime 462073 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv1481]) (by decide +kernel)
def pv462073 : PrimeValue := ⟨462073, pr462073⟩
private theorem pr462103 : Nat.Prime 462103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv77017]) (by decide +kernel)
def pv462103 : PrimeValue := ⟨462103, pr462103⟩
private theorem pr462131 : Nat.Prime 462131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv1249]) (by decide +kernel)
def pv462131 : PrimeValue := ⟨462131, pr462131⟩
private theorem pr462311 : Nat.Prime 462311 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv83,pv557]) (by decide +kernel)
def pv462311 : PrimeValue := ⟨462311, pr462311⟩
private theorem pr462401 : Nat.Prime 462401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17]) (by decide +kernel)
def pv462401 : PrimeValue := ⟨462401, pr462401⟩
private theorem pr462421 : Nat.Prime 462421 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv7,pv367]) (by decide +kernel)
def pv462421 : PrimeValue := ⟨462421, pr462421⟩
private theorem pr462493 : Nat.Prime 462493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv443]) (by decide +kernel)
def pv462493 : PrimeValue := ⟨462493, pr462493⟩
private theorem pr462557 : Nat.Prime 462557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv197,pv587]) (by decide +kernel)
def pv462557 : PrimeValue := ⟨462557, pr462557⟩
private theorem pr462659 : Nat.Prime 462659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv4721]) (by decide +kernel)
def pv462659 : PrimeValue := ⟨462659, pr462659⟩
private theorem pr462841 : Nat.Prime 462841 :=
  checkPrime_prime (q := pv79) (ls := [pv2,pv3,pv5,pv7,pv19,pv29]) (by decide +kernel)
def pv462841 : PrimeValue := ⟨462841, pr462841⟩
private theorem pr463033 : Nat.Prime 463033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv59,pv109]) (by decide +kernel)
def pv463033 : PrimeValue := ⟨463033, pr463033⟩
private theorem pr463157 : Nat.Prime 463157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv1301]) (by decide +kernel)
def pv463157 : PrimeValue := ⟨463157, pr463157⟩
private theorem pr463219 : Nat.Prime 463219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv269]) (by decide +kernel)
def pv463219 : PrimeValue := ⟨463219, pr463219⟩
private theorem pr463261 : Nat.Prime 463261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv1103]) (by decide +kernel)
def pv463261 : PrimeValue := ⟨463261, pr463261⟩
private theorem pr463513 : Nat.Prime 463513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv31,pv89]) (by decide +kernel)
def pv463513 : PrimeValue := ⟨463513, pr463513⟩
private theorem pr463531 : Nat.Prime 463531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv15451]) (by decide +kernel)
def pv463531 : PrimeValue := ⟨463531, pr463531⟩
private theorem pr463711 : Nat.Prime 463711 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv13,pv29,pv41]) (by decide +kernel)
def pv463711 : PrimeValue := ⟨463711, pr463711⟩
private theorem pr463741 : Nat.Prime 463741 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv59,pv131]) (by decide +kernel)
def pv463741 : PrimeValue := ⟨463741, pr463741⟩
private theorem pr463891 : Nat.Prime 463891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv47]) (by decide +kernel)
def pv463891 : PrimeValue := ⟨463891, pr463891⟩
private theorem pr463919 : Nat.Prime 463919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv13,pv2549]) (by decide +kernel)
def pv463919 : PrimeValue := ⟨463919, pr463919⟩
private theorem pr464119 : Nat.Prime 464119 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv103,pv751]) (by decide +kernel)
def pv464119 : PrimeValue := ⟨464119, pr464119⟩
private theorem pr464281 : Nat.Prime 464281 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv53,pv73]) (by decide +kernel)
def pv464281 : PrimeValue := ⟨464281, pr464281⟩
private theorem pr464371 : Nat.Prime 464371 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv673]) (by decide +kernel)
def pv464371 : PrimeValue := ⟨464371, pr464371⟩
private theorem pr464437 : Nat.Prime 464437 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv97]) (by decide +kernel)
def pv464437 : PrimeValue := ⟨464437, pr464437⟩
private theorem pr464467 : Nat.Prime 464467 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv199,pv389]) (by decide +kernel)
def pv464467 : PrimeValue := ⟨464467, pr464467⟩
private theorem pr464549 : Nat.Prime 464549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv47,pv353]) (by decide +kernel)
def pv464549 : PrimeValue := ⟨464549, pr464549⟩
private theorem pr464803 : Nat.Prime 464803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv59,pv101]) (by decide +kernel)
def pv464803 : PrimeValue := ⟨464803, pr464803⟩
private theorem pr464909 : Nat.Prime 464909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv1637]) (by decide +kernel)
def pv464909 : PrimeValue := ⟨464909, pr464909⟩
private theorem pr464923 : Nat.Prime 464923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv1123]) (by decide +kernel)
def pv464923 : PrimeValue := ⟨464923, pr464923⟩
private theorem pr464999 : Nat.Prime 464999 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv232499]) (by decide +kernel)
def pv464999 : PrimeValue := ⟨464999, pr464999⟩
private theorem pr465013 : Nat.Prime 465013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12917]) (by decide +kernel)
def pv465013 : PrimeValue := ⟨465013, pr465013⟩
private theorem pr465077 : Nat.Prime 465077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv116269]) (by decide +kernel)
def pv465077 : PrimeValue := ⟨465077, pr465077⟩
private theorem pr465151 : Nat.Prime 465151 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv443]) (by decide +kernel)
def pv465151 : PrimeValue := ⟨465151, pr465151⟩
private theorem pr465167 : Nat.Prime 465167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv17891]) (by decide +kernel)
def pv465167 : PrimeValue := ⟨465167, pr465167⟩
private theorem pr465209 : Nat.Prime 465209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv58151]) (by decide +kernel)
def pv465209 : PrimeValue := ⟨465209, pr465209⟩
private theorem pr465277 : Nat.Prime 465277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv191]) (by decide +kernel)
def pv465277 : PrimeValue := ⟨465277, pr465277⟩
private theorem pr465281 : Nat.Prime 465281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv727]) (by decide +kernel)
def pv465281 : PrimeValue := ⟨465281, pr465281⟩
private theorem pr465299 : Nat.Prime 465299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv2803]) (by decide +kernel)
def pv465299 : PrimeValue := ⟨465299, pr465299⟩
private theorem pr465319 : Nat.Prime 465319 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv1231]) (by decide +kernel)
def pv465319 : PrimeValue := ⟨465319, pr465319⟩
private theorem pr465463 : Nat.Prime 465463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv1361]) (by decide +kernel)
def pv465463 : PrimeValue := ⟨465463, pr465463⟩
private theorem pr465541 : Nat.Prime 465541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7759]) (by decide +kernel)
def pv465541 : PrimeValue := ⟨465541, pr465541⟩
private theorem pr465781 : Nat.Prime 465781 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv1109]) (by decide +kernel)
def pv465781 : PrimeValue := ⟨465781, pr465781⟩
private theorem pr465931 : Nat.Prime 465931 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv31,pv167]) (by decide +kernel)
def pv465931 : PrimeValue := ⟨465931, pr465931⟩
private theorem pr466061 : Nat.Prime 466061 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv3329]) (by decide +kernel)
def pv466061 : PrimeValue := ⟨466061, pr466061⟩
private theorem pr466079 : Nat.Prime 466079 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv397,pv587]) (by decide +kernel)
def pv466079 : PrimeValue := ⟨466079, pr466079⟩
private theorem pr466121 : Nat.Prime 466121 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv43,pv271]) (by decide +kernel)
def pv466121 : PrimeValue := ⟨466121, pr466121⟩
private theorem pr466247 : Nat.Prime 466247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv21193]) (by decide +kernel)
def pv466247 : PrimeValue := ⟨466247, pr466247⟩
private theorem pr466369 : Nat.Prime 466369 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv347]) (by decide +kernel)
def pv466369 : PrimeValue := ⟨466369, pr466369⟩
private theorem pr466603 : Nat.Prime 466603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv4093]) (by decide +kernel)
def pv466603 : PrimeValue := ⟨466603, pr466603⟩
private theorem pr466649 : Nat.Prime 466649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv641]) (by decide +kernel)
def pv466649 : PrimeValue := ⟨466649, pr466649⟩
private theorem pr467021 : Nat.Prime 467021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv1229]) (by decide +kernel)
def pv467021 : PrimeValue := ⟨467021, pr467021⟩
private theorem pr467101 : Nat.Prime 467101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv173]) (by decide +kernel)
def pv467101 : PrimeValue := ⟨467101, pr467101⟩
private theorem pr467147 : Nat.Prime 467147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv131,pv1783]) (by decide +kernel)
def pv467147 : PrimeValue := ⟨467147, pr467147⟩
private theorem pr467447 : Nat.Prime 467447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv173,pv193]) (by decide +kernel)
def pv467447 : PrimeValue := ⟨467447, pr467447⟩
private theorem pr467549 : Nat.Prime 467549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv179,pv653]) (by decide +kernel)
def pv467549 : PrimeValue := ⟨467549, pr467549⟩
private theorem pr467729 : Nat.Prime 467729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv31,pv41]) (by decide +kernel)
def pv467729 : PrimeValue := ⟨467729, pr467729⟩
private theorem pr467977 : Nat.Prime 467977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv31,pv37]) (by decide +kernel)
def pv467977 : PrimeValue := ⟨467977, pr467977⟩
private theorem pr468011 : Nat.Prime 468011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv2753]) (by decide +kernel)
def pv468011 : PrimeValue := ⟨468011, pr468011⟩
private theorem pr468079 : Nat.Prime 468079 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv353]) (by decide +kernel)
def pv468079 : PrimeValue := ⟨468079, pr468079⟩
private theorem pr468121 : Nat.Prime 468121 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv47,pv83]) (by decide +kernel)
def pv468121 : PrimeValue := ⟨468121, pr468121⟩
private theorem pr468187 : Nat.Prime 468187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv78031]) (by decide +kernel)
def pv468187 : PrimeValue := ⟨468187, pr468187⟩
private theorem pr468191 : Nat.Prime 468191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv46819]) (by decide +kernel)
def pv468191 : PrimeValue := ⟨468191, pr468191⟩
private theorem pr468199 : Nat.Prime 468199 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv37]) (by decide +kernel)
def pv468199 : PrimeValue := ⟨468199, pr468199⟩
private theorem pr468239 : Nat.Prime 468239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv103,pv2273]) (by decide +kernel)
def pv468239 : PrimeValue := ⟨468239, pr468239⟩
private theorem pr468241 : Nat.Prime 468241 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv1951]) (by decide +kernel)
def pv468241 : PrimeValue := ⟨468241, pr468241⟩
private theorem pr468371 : Nat.Prime 468371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv6691]) (by decide +kernel)
def pv468371 : PrimeValue := ⟨468371, pr468371⟩
private theorem pr468439 : Nat.Prime 468439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv101,pv773]) (by decide +kernel)
def pv468439 : PrimeValue := ⟨468439, pr468439⟩
private theorem pr468491 : Nat.Prime 468491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv4259]) (by decide +kernel)
def pv468491 : PrimeValue := ⟨468491, pr468491⟩
private theorem pr468499 : Nat.Prime 468499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv113,pv691]) (by decide +kernel)
def pv468499 : PrimeValue := ⟨468499, pr468499⟩
private theorem pr468613 : Nat.Prime 468613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4339]) (by decide +kernel)
def pv468613 : PrimeValue := ⟨468613, pr468613⟩
private theorem pr468691 : Nat.Prime 468691 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv17,pv919]) (by decide +kernel)
def pv468691 : PrimeValue := ⟨468691, pr468691⟩
private theorem pr468817 : Nat.Prime 468817 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv9767]) (by decide +kernel)
def pv468817 : PrimeValue := ⟨468817, pr468817⟩
private theorem pr468869 : Nat.Prime 468869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv251,pv467]) (by decide +kernel)
def pv468869 : PrimeValue := ⟨468869, pr468869⟩
private theorem pr469031 : Nat.Prime 469031 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv17,pv31,pv89]) (by decide +kernel)
def pv469031 : PrimeValue := ⟨469031, pr469031⟩
private theorem pr469099 : Nat.Prime 469099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv73]) (by decide +kernel)
def pv469099 : PrimeValue := ⟨469099, pr469099⟩
private theorem pr469169 : Nat.Prime 469169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv59,pv71]) (by decide +kernel)
def pv469169 : PrimeValue := ⟨469169, pr469169⟩
private theorem pr469363 : Nat.Prime 469363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv137,pv571]) (by decide +kernel)
def pv469363 : PrimeValue := ⟨469363, pr469363⟩
private theorem pr469369 : Nat.Prime 469369 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv41,pv53]) (by decide +kernel)
def pv469369 : PrimeValue := ⟨469369, pr469369⟩
private theorem pr469411 : Nat.Prime 469411 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv15647]) (by decide +kernel)
def pv469411 : PrimeValue := ⟨469411, pr469411⟩
private theorem pr469627 : Nat.Prime 469627 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv2699]) (by decide +kernel)
def pv469627 : PrimeValue := ⟨469627, pr469627⟩
private theorem pr469687 : Nat.Prime 469687 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv53,pv211]) (by decide +kernel)
def pv469687 : PrimeValue := ⟨469687, pr469687⟩
private theorem pr469753 : Nat.Prime 469753 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv23,pv37]) (by decide +kernel)
def pv469753 : PrimeValue := ⟨469753, pr469753⟩
private theorem pr469787 : Nat.Prime 469787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv234893]) (by decide +kernel)
def pv469787 : PrimeValue := ⟨469787, pr469787⟩
private theorem pr469907 : Nat.Prime 469907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv4999]) (by decide +kernel)
def pv469907 : PrimeValue := ⟨469907, pr469907⟩
private theorem pr469939 : Nat.Prime 469939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv67,pv167]) (by decide +kernel)
def pv469939 : PrimeValue := ⟨469939, pr469939⟩
private theorem pr469969 : Nat.Prime 469969 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv9791]) (by decide +kernel)
def pv469969 : PrimeValue := ⟨469969, pr469969⟩
private theorem pr470161 : Nat.Prime 470161 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv653]) (by decide +kernel)
def pv470161 : PrimeValue := ⟨470161, pr470161⟩
private theorem pr470179 : Nat.Prime 470179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8707]) (by decide +kernel)
def pv470179 : PrimeValue := ⟨470179, pr470179⟩
private theorem pr470471 : Nat.Prime 470471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv13,pv47]) (by decide +kernel)
def pv470471 : PrimeValue := ⟨470471, pr470471⟩
private theorem pr470501 : Nat.Prime 470501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv941]) (by decide +kernel)
def pv470501 : PrimeValue := ⟨470501, pr470501⟩
private theorem pr470539 : Nat.Prime 470539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv26141]) (by decide +kernel)
def pv470539 : PrimeValue := ⟨470539, pr470539⟩
private theorem pr470653 : Nat.Prime 470653 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv431]) (by decide +kernel)
def pv470653 : PrimeValue := ⟨470653, pr470653⟩
private theorem pr470711 : Nat.Prime 470711 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv103,pv457]) (by decide +kernel)
def pv470711 : PrimeValue := ⟨470711, pr470711⟩
private theorem pr470863 : Nat.Prime 470863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv37,pv101]) (by decide +kernel)
def pv470863 : PrimeValue := ⟨470863, pr470863⟩
private theorem pr470867 : Nat.Prime 470867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv1259]) (by decide +kernel)
def pv470867 : PrimeValue := ⟨470867, pr470867⟩
private theorem pr470887 : Nat.Prime 470887 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv6037]) (by decide +kernel)
def pv470887 : PrimeValue := ⟨470887, pr470887⟩
private theorem pr470957 : Nat.Prime 470957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv281,pv419]) (by decide +kernel)
def pv470957 : PrimeValue := ⟨470957, pr470957⟩
private theorem pr470959 : Nat.Prime 470959 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv53,pv1481]) (by decide +kernel)
def pv470959 : PrimeValue := ⟨470959, pr470959⟩
private theorem pr471139 : Nat.Prime 471139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv31,pv149]) (by decide +kernel)
def pv471139 : PrimeValue := ⟨471139, pr471139⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
