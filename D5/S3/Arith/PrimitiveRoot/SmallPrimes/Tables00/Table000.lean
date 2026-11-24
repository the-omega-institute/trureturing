/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table000
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table000.pv2
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Checker

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

def pv2 : PrimeValue := ⟨2, by decide +kernel⟩
private theorem pr3 : Nat.Prime 3 :=
  checkPrime_prime (q := pv2) (ls := [pv2]) (by decide +kernel)
def pv3 : PrimeValue := ⟨3, pr3⟩
private theorem pr5 : Nat.Prime 5 :=
  checkPrime_prime (q := pv2) (ls := [pv2]) (by decide +kernel)
def pv5 : PrimeValue := ⟨5, pr5⟩
private theorem pr7 : Nat.Prime 7 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3]) (by decide +kernel)
def pv7 : PrimeValue := ⟨7, pr7⟩
private theorem pr11 : Nat.Prime 11 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5]) (by decide +kernel)
def pv11 : PrimeValue := ⟨11, pr11⟩
private theorem pr13 : Nat.Prime 13 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3]) (by decide +kernel)
def pv13 : PrimeValue := ⟨13, pr13⟩
private theorem pr17 : Nat.Prime 17 :=
  checkPrime_prime (q := pv3) (ls := [pv2]) (by decide +kernel)
def pv17 : PrimeValue := ⟨17, pr17⟩
private theorem pr19 : Nat.Prime 19 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3]) (by decide +kernel)
def pv19 : PrimeValue := ⟨19, pr19⟩
private theorem pr23 : Nat.Prime 23 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11]) (by decide +kernel)
def pv23 : PrimeValue := ⟨23, pr23⟩
private theorem pr29 : Nat.Prime 29 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7]) (by decide +kernel)
def pv29 : PrimeValue := ⟨29, pr29⟩
private theorem pr31 : Nat.Prime 31 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv31 : PrimeValue := ⟨31, pr31⟩
private theorem pr37 : Nat.Prime 37 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3]) (by decide +kernel)
def pv37 : PrimeValue := ⟨37, pr37⟩
private theorem pr41 : Nat.Prime 41 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5]) (by decide +kernel)
def pv41 : PrimeValue := ⟨41, pr41⟩
private theorem pr43 : Nat.Prime 43 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv43 : PrimeValue := ⟨43, pr43⟩
private theorem pr47 : Nat.Prime 47 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23]) (by decide +kernel)
def pv47 : PrimeValue := ⟨47, pr47⟩
private theorem pr53 : Nat.Prime 53 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13]) (by decide +kernel)
def pv53 : PrimeValue := ⟨53, pr53⟩
private theorem pr59 : Nat.Prime 59 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29]) (by decide +kernel)
def pv59 : PrimeValue := ⟨59, pr59⟩
private theorem pr61 : Nat.Prime 61 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv61 : PrimeValue := ⟨61, pr61⟩
private theorem pr67 : Nat.Prime 67 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv67 : PrimeValue := ⟨67, pr67⟩
private theorem pr71 : Nat.Prime 71 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv71 : PrimeValue := ⟨71, pr71⟩
private theorem pr73 : Nat.Prime 73 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv73 : PrimeValue := ⟨73, pr73⟩
private theorem pr79 : Nat.Prime 79 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv79 : PrimeValue := ⟨79, pr79⟩
private theorem pr83 : Nat.Prime 83 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41]) (by decide +kernel)
def pv83 : PrimeValue := ⟨83, pr83⟩
private theorem pr89 : Nat.Prime 89 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11]) (by decide +kernel)
def pv89 : PrimeValue := ⟨89, pr89⟩
private theorem pr97 : Nat.Prime 97 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv97 : PrimeValue := ⟨97, pr97⟩
private theorem pr101 : Nat.Prime 101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5]) (by decide +kernel)
def pv101 : PrimeValue := ⟨101, pr101⟩
private theorem pr103 : Nat.Prime 103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv103 : PrimeValue := ⟨103, pr103⟩
private theorem pr107 : Nat.Prime 107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53]) (by decide +kernel)
def pv107 : PrimeValue := ⟨107, pr107⟩
private theorem pr109 : Nat.Prime 109 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3]) (by decide +kernel)
def pv109 : PrimeValue := ⟨109, pr109⟩
private theorem pr113 : Nat.Prime 113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7]) (by decide +kernel)
def pv113 : PrimeValue := ⟨113, pr113⟩
private theorem pr127 : Nat.Prime 127 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv127 : PrimeValue := ⟨127, pr127⟩
private theorem pr131 : Nat.Prime 131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv131 : PrimeValue := ⟨131, pr131⟩
private theorem pr137 : Nat.Prime 137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17]) (by decide +kernel)
def pv137 : PrimeValue := ⟨137, pr137⟩
private theorem pr139 : Nat.Prime 139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv139 : PrimeValue := ⟨139, pr139⟩
private theorem pr149 : Nat.Prime 149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37]) (by decide +kernel)
def pv149 : PrimeValue := ⟨149, pr149⟩
private theorem pr151 : Nat.Prime 151 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv151 : PrimeValue := ⟨151, pr151⟩
private theorem pr157 : Nat.Prime 157 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv157 : PrimeValue := ⟨157, pr157⟩
private theorem pr163 : Nat.Prime 163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3]) (by decide +kernel)
def pv163 : PrimeValue := ⟨163, pr163⟩
private theorem pr167 : Nat.Prime 167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv83]) (by decide +kernel)
def pv167 : PrimeValue := ⟨167, pr167⟩
private theorem pr173 : Nat.Prime 173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43]) (by decide +kernel)
def pv173 : PrimeValue := ⟨173, pr173⟩
private theorem pr179 : Nat.Prime 179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89]) (by decide +kernel)
def pv179 : PrimeValue := ⟨179, pr179⟩
private theorem pr181 : Nat.Prime 181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv181 : PrimeValue := ⟨181, pr181⟩
private theorem pr191 : Nat.Prime 191 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv191 : PrimeValue := ⟨191, pr191⟩
private theorem pr193 : Nat.Prime 193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv193 : PrimeValue := ⟨193, pr193⟩
private theorem pr197 : Nat.Prime 197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7]) (by decide +kernel)
def pv197 : PrimeValue := ⟨197, pr197⟩
private theorem pr199 : Nat.Prime 199 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv199 : PrimeValue := ⟨199, pr199⟩
private theorem pr211 : Nat.Prime 211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv211 : PrimeValue := ⟨211, pr211⟩
private theorem pr223 : Nat.Prime 223 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv223 : PrimeValue := ⟨223, pr223⟩
private theorem pr227 : Nat.Prime 227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113]) (by decide +kernel)
def pv227 : PrimeValue := ⟨227, pr227⟩
private theorem pr229 : Nat.Prime 229 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv229 : PrimeValue := ⟨229, pr229⟩
private theorem pr233 : Nat.Prime 233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29]) (by decide +kernel)
def pv233 : PrimeValue := ⟨233, pr233⟩
private theorem pr239 : Nat.Prime 239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv17]) (by decide +kernel)
def pv239 : PrimeValue := ⟨239, pr239⟩
private theorem pr241 : Nat.Prime 241 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv241 : PrimeValue := ⟨241, pr241⟩
private theorem pr251 : Nat.Prime 251 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5]) (by decide +kernel)
def pv251 : PrimeValue := ⟨251, pr251⟩
private theorem pr257 : Nat.Prime 257 :=
  checkPrime_prime (q := pv3) (ls := [pv2]) (by decide +kernel)
def pv257 : PrimeValue := ⟨257, pr257⟩
private theorem pr263 : Nat.Prime 263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv131]) (by decide +kernel)
def pv263 : PrimeValue := ⟨263, pr263⟩
private theorem pr269 : Nat.Prime 269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67]) (by decide +kernel)
def pv269 : PrimeValue := ⟨269, pr269⟩
private theorem pr271 : Nat.Prime 271 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv271 : PrimeValue := ⟨271, pr271⟩
private theorem pr277 : Nat.Prime 277 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv277 : PrimeValue := ⟨277, pr277⟩
private theorem pr281 : Nat.Prime 281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv281 : PrimeValue := ⟨281, pr281⟩
private theorem pr283 : Nat.Prime 283 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv283 : PrimeValue := ⟨283, pr283⟩
private theorem pr293 : Nat.Prime 293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73]) (by decide +kernel)
def pv293 : PrimeValue := ⟨293, pr293⟩
private theorem pr307 : Nat.Prime 307 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv307 : PrimeValue := ⟨307, pr307⟩
private theorem pr311 : Nat.Prime 311 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv31]) (by decide +kernel)
def pv311 : PrimeValue := ⟨311, pr311⟩
private theorem pr313 : Nat.Prime 313 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv313 : PrimeValue := ⟨313, pr313⟩
private theorem pr317 : Nat.Prime 317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79]) (by decide +kernel)
def pv317 : PrimeValue := ⟨317, pr317⟩
private theorem pr331 : Nat.Prime 331 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv331 : PrimeValue := ⟨331, pr331⟩
private theorem pr337 : Nat.Prime 337 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv337 : PrimeValue := ⟨337, pr337⟩
private theorem pr347 : Nat.Prime 347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv173]) (by decide +kernel)
def pv347 : PrimeValue := ⟨347, pr347⟩
private theorem pr349 : Nat.Prime 349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv349 : PrimeValue := ⟨349, pr349⟩
private theorem pr353 : Nat.Prime 353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11]) (by decide +kernel)
def pv353 : PrimeValue := ⟨353, pr353⟩
private theorem pr359 : Nat.Prime 359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv179]) (by decide +kernel)
def pv359 : PrimeValue := ⟨359, pr359⟩
private theorem pr367 : Nat.Prime 367 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv367 : PrimeValue := ⟨367, pr367⟩
private theorem pr373 : Nat.Prime 373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv373 : PrimeValue := ⟨373, pr373⟩
private theorem pr379 : Nat.Prime 379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv379 : PrimeValue := ⟨379, pr379⟩
private theorem pr383 : Nat.Prime 383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv191]) (by decide +kernel)
def pv383 : PrimeValue := ⟨383, pr383⟩
private theorem pr389 : Nat.Prime 389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97]) (by decide +kernel)
def pv389 : PrimeValue := ⟨389, pr389⟩
private theorem pr397 : Nat.Prime 397 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv397 : PrimeValue := ⟨397, pr397⟩
private theorem pr401 : Nat.Prime 401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5]) (by decide +kernel)
def pv401 : PrimeValue := ⟨401, pr401⟩
private theorem pr409 : Nat.Prime 409 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv409 : PrimeValue := ⟨409, pr409⟩
private theorem pr419 : Nat.Prime 419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19]) (by decide +kernel)
def pv419 : PrimeValue := ⟨419, pr419⟩
private theorem pr421 : Nat.Prime 421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv421 : PrimeValue := ⟨421, pr421⟩
private theorem pr431 : Nat.Prime 431 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv43]) (by decide +kernel)
def pv431 : PrimeValue := ⟨431, pr431⟩
private theorem pr433 : Nat.Prime 433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv433 : PrimeValue := ⟨433, pr433⟩
private theorem pr439 : Nat.Prime 439 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv439 : PrimeValue := ⟨439, pr439⟩
private theorem pr443 : Nat.Prime 443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17]) (by decide +kernel)
def pv443 : PrimeValue := ⟨443, pr443⟩
private theorem pr449 : Nat.Prime 449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7]) (by decide +kernel)
def pv449 : PrimeValue := ⟨449, pr449⟩
private theorem pr457 : Nat.Prime 457 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv457 : PrimeValue := ⟨457, pr457⟩
private theorem pr461 : Nat.Prime 461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23]) (by decide +kernel)
def pv461 : PrimeValue := ⟨461, pr461⟩
private theorem pr463 : Nat.Prime 463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv463 : PrimeValue := ⟨463, pr463⟩
private theorem pr467 : Nat.Prime 467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv233]) (by decide +kernel)
def pv467 : PrimeValue := ⟨467, pr467⟩
private theorem pr479 : Nat.Prime 479 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv239]) (by decide +kernel)
def pv479 : PrimeValue := ⟨479, pr479⟩
private theorem pr487 : Nat.Prime 487 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3]) (by decide +kernel)
def pv487 : PrimeValue := ⟨487, pr487⟩
private theorem pr491 : Nat.Prime 491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv491 : PrimeValue := ⟨491, pr491⟩
private theorem pr499 : Nat.Prime 499 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv499 : PrimeValue := ⟨499, pr499⟩
private theorem pr503 : Nat.Prime 503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv251]) (by decide +kernel)
def pv503 : PrimeValue := ⟨503, pr503⟩
private theorem pr509 : Nat.Prime 509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127]) (by decide +kernel)
def pv509 : PrimeValue := ⟨509, pr509⟩
private theorem pr521 : Nat.Prime 521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv521 : PrimeValue := ⟨521, pr521⟩
private theorem pr523 : Nat.Prime 523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv523 : PrimeValue := ⟨523, pr523⟩
private theorem pr541 : Nat.Prime 541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv541 : PrimeValue := ⟨541, pr541⟩
private theorem pr547 : Nat.Prime 547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv547 : PrimeValue := ⟨547, pr547⟩
private theorem pr557 : Nat.Prime 557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv139]) (by decide +kernel)
def pv557 : PrimeValue := ⟨557, pr557⟩
private theorem pr563 : Nat.Prime 563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv281]) (by decide +kernel)
def pv563 : PrimeValue := ⟨563, pr563⟩
private theorem pr569 : Nat.Prime 569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv71]) (by decide +kernel)
def pv569 : PrimeValue := ⟨569, pr569⟩
private theorem pr571 : Nat.Prime 571 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv571 : PrimeValue := ⟨571, pr571⟩
private theorem pr577 : Nat.Prime 577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv577 : PrimeValue := ⟨577, pr577⟩
private theorem pr587 : Nat.Prime 587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv293]) (by decide +kernel)
def pv587 : PrimeValue := ⟨587, pr587⟩
private theorem pr593 : Nat.Prime 593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37]) (by decide +kernel)
def pv593 : PrimeValue := ⟨593, pr593⟩
private theorem pr599 : Nat.Prime 599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv23]) (by decide +kernel)
def pv599 : PrimeValue := ⟨599, pr599⟩
private theorem pr601 : Nat.Prime 601 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv601 : PrimeValue := ⟨601, pr601⟩
private theorem pr607 : Nat.Prime 607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv607 : PrimeValue := ⟨607, pr607⟩
private theorem pr613 : Nat.Prime 613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv613 : PrimeValue := ⟨613, pr613⟩
private theorem pr617 : Nat.Prime 617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11]) (by decide +kernel)
def pv617 : PrimeValue := ⟨617, pr617⟩
private theorem pr619 : Nat.Prime 619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv619 : PrimeValue := ⟨619, pr619⟩
private theorem pr631 : Nat.Prime 631 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv631 : PrimeValue := ⟨631, pr631⟩
private theorem pr641 : Nat.Prime 641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5]) (by decide +kernel)
def pv641 : PrimeValue := ⟨641, pr641⟩
private theorem pr643 : Nat.Prime 643 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv643 : PrimeValue := ⟨643, pr643⟩
private theorem pr647 : Nat.Prime 647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv19]) (by decide +kernel)
def pv647 : PrimeValue := ⟨647, pr647⟩
private theorem pr653 : Nat.Prime 653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163]) (by decide +kernel)
def pv653 : PrimeValue := ⟨653, pr653⟩
private theorem pr659 : Nat.Prime 659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv47]) (by decide +kernel)
def pv659 : PrimeValue := ⟨659, pr659⟩
private theorem pr661 : Nat.Prime 661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv661 : PrimeValue := ⟨661, pr661⟩
private theorem pr673 : Nat.Prime 673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv673 : PrimeValue := ⟨673, pr673⟩
private theorem pr677 : Nat.Prime 677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13]) (by decide +kernel)
def pv677 : PrimeValue := ⟨677, pr677⟩
private theorem pr683 : Nat.Prime 683 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv31]) (by decide +kernel)
def pv683 : PrimeValue := ⟨683, pr683⟩
private theorem pr691 : Nat.Prime 691 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv691 : PrimeValue := ⟨691, pr691⟩
private theorem pr701 : Nat.Prime 701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv701 : PrimeValue := ⟨701, pr701⟩
private theorem pr709 : Nat.Prime 709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv709 : PrimeValue := ⟨709, pr709⟩
private theorem pr719 : Nat.Prime 719 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv359]) (by decide +kernel)
def pv719 : PrimeValue := ⟨719, pr719⟩
private theorem pr727 : Nat.Prime 727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv727 : PrimeValue := ⟨727, pr727⟩
private theorem pr733 : Nat.Prime 733 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv733 : PrimeValue := ⟨733, pr733⟩
private theorem pr739 : Nat.Prime 739 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv739 : PrimeValue := ⟨739, pr739⟩
private theorem pr743 : Nat.Prime 743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv53]) (by decide +kernel)
def pv743 : PrimeValue := ⟨743, pr743⟩
private theorem pr751 : Nat.Prime 751 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv751 : PrimeValue := ⟨751, pr751⟩
private theorem pr757 : Nat.Prime 757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv757 : PrimeValue := ⟨757, pr757⟩
private theorem pr761 : Nat.Prime 761 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv761 : PrimeValue := ⟨761, pr761⟩
private theorem pr769 : Nat.Prime 769 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3]) (by decide +kernel)
def pv769 : PrimeValue := ⟨769, pr769⟩
private theorem pr773 : Nat.Prime 773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv193]) (by decide +kernel)
def pv773 : PrimeValue := ⟨773, pr773⟩
private theorem pr787 : Nat.Prime 787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv131]) (by decide +kernel)
def pv787 : PrimeValue := ⟨787, pr787⟩
private theorem pr797 : Nat.Prime 797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv199]) (by decide +kernel)
def pv797 : PrimeValue := ⟨797, pr797⟩
private theorem pr809 : Nat.Prime 809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv101]) (by decide +kernel)
def pv809 : PrimeValue := ⟨809, pr809⟩
private theorem pr811 : Nat.Prime 811 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv811 : PrimeValue := ⟨811, pr811⟩
private theorem pr821 : Nat.Prime 821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41]) (by decide +kernel)
def pv821 : PrimeValue := ⟨821, pr821⟩
private theorem pr823 : Nat.Prime 823 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv137]) (by decide +kernel)
def pv823 : PrimeValue := ⟨823, pr823⟩
private theorem pr827 : Nat.Prime 827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv59]) (by decide +kernel)
def pv827 : PrimeValue := ⟨827, pr827⟩
private theorem pr829 : Nat.Prime 829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv829 : PrimeValue := ⟨829, pr829⟩
private theorem pr839 : Nat.Prime 839 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv419]) (by decide +kernel)
def pv839 : PrimeValue := ⟨839, pr839⟩
private theorem pr853 : Nat.Prime 853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv853 : PrimeValue := ⟨853, pr853⟩
private theorem pr857 : Nat.Prime 857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv107]) (by decide +kernel)
def pv857 : PrimeValue := ⟨857, pr857⟩
private theorem pr859 : Nat.Prime 859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv859 : PrimeValue := ⟨859, pr859⟩
private theorem pr863 : Nat.Prime 863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv431]) (by decide +kernel)
def pv863 : PrimeValue := ⟨863, pr863⟩
private theorem pr877 : Nat.Prime 877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv877 : PrimeValue := ⟨877, pr877⟩
private theorem pr881 : Nat.Prime 881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv881 : PrimeValue := ⟨881, pr881⟩
private theorem pr883 : Nat.Prime 883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv883 : PrimeValue := ⟨883, pr883⟩
private theorem pr887 : Nat.Prime 887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv443]) (by decide +kernel)
def pv887 : PrimeValue := ⟨887, pr887⟩
private theorem pr907 : Nat.Prime 907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv151]) (by decide +kernel)
def pv907 : PrimeValue := ⟨907, pr907⟩
private theorem pr911 : Nat.Prime 911 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv13]) (by decide +kernel)
def pv911 : PrimeValue := ⟨911, pr911⟩
private theorem pr919 : Nat.Prime 919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv919 : PrimeValue := ⟨919, pr919⟩
private theorem pr929 : Nat.Prime 929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29]) (by decide +kernel)
def pv929 : PrimeValue := ⟨929, pr929⟩
private theorem pr937 : Nat.Prime 937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv937 : PrimeValue := ⟨937, pr937⟩
private theorem pr941 : Nat.Prime 941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47]) (by decide +kernel)
def pv941 : PrimeValue := ⟨941, pr941⟩
private theorem pr947 : Nat.Prime 947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv43]) (by decide +kernel)
def pv947 : PrimeValue := ⟨947, pr947⟩
private theorem pr953 : Nat.Prime 953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17]) (by decide +kernel)
def pv953 : PrimeValue := ⟨953, pr953⟩
private theorem pr967 : Nat.Prime 967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv967 : PrimeValue := ⟨967, pr967⟩
private theorem pr971 : Nat.Prime 971 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv97]) (by decide +kernel)
def pv971 : PrimeValue := ⟨971, pr971⟩
private theorem pr977 : Nat.Prime 977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61]) (by decide +kernel)
def pv977 : PrimeValue := ⟨977, pr977⟩
private theorem pr983 : Nat.Prime 983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv491]) (by decide +kernel)
def pv983 : PrimeValue := ⟨983, pr983⟩
private theorem pr991 : Nat.Prime 991 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv991 : PrimeValue := ⟨991, pr991⟩
private theorem pr997 : Nat.Prime 997 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv997 : PrimeValue := ⟨997, pr997⟩
private theorem pr1009 : Nat.Prime 1009 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv1009 : PrimeValue := ⟨1009, pr1009⟩
private theorem pr1013 : Nat.Prime 1013 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv23]) (by decide +kernel)
def pv1013 : PrimeValue := ⟨1013, pr1013⟩
private theorem pr1019 : Nat.Prime 1019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv509]) (by decide +kernel)
def pv1019 : PrimeValue := ⟨1019, pr1019⟩
private theorem pr1021 : Nat.Prime 1021 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv1021 : PrimeValue := ⟨1021, pr1021⟩
private theorem pr1031 : Nat.Prime 1031 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv103]) (by decide +kernel)
def pv1031 : PrimeValue := ⟨1031, pr1031⟩
private theorem pr1033 : Nat.Prime 1033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv1033 : PrimeValue := ⟨1033, pr1033⟩
private theorem pr1039 : Nat.Prime 1039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv173]) (by decide +kernel)
def pv1039 : PrimeValue := ⟨1039, pr1039⟩
private theorem pr1049 : Nat.Prime 1049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv131]) (by decide +kernel)
def pv1049 : PrimeValue := ⟨1049, pr1049⟩
private theorem pr1051 : Nat.Prime 1051 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv1051 : PrimeValue := ⟨1051, pr1051⟩
private theorem pr1061 : Nat.Prime 1061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv53]) (by decide +kernel)
def pv1061 : PrimeValue := ⟨1061, pr1061⟩
private theorem pr1063 : Nat.Prime 1063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv1063 : PrimeValue := ⟨1063, pr1063⟩
private theorem pr1069 : Nat.Prime 1069 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv89]) (by decide +kernel)
def pv1069 : PrimeValue := ⟨1069, pr1069⟩
private theorem pr1087 : Nat.Prime 1087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv181]) (by decide +kernel)
def pv1087 : PrimeValue := ⟨1087, pr1087⟩
private theorem pr1091 : Nat.Prime 1091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv109]) (by decide +kernel)
def pv1091 : PrimeValue := ⟨1091, pr1091⟩
private theorem pr1093 : Nat.Prime 1093 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv1093 : PrimeValue := ⟨1093, pr1093⟩
private theorem pr1097 : Nat.Prime 1097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv137]) (by decide +kernel)
def pv1097 : PrimeValue := ⟨1097, pr1097⟩
private theorem pr1103 : Nat.Prime 1103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv29]) (by decide +kernel)
def pv1103 : PrimeValue := ⟨1103, pr1103⟩
private theorem pr1109 : Nat.Prime 1109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv277]) (by decide +kernel)
def pv1109 : PrimeValue := ⟨1109, pr1109⟩
private theorem pr1117 : Nat.Prime 1117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv1117 : PrimeValue := ⟨1117, pr1117⟩
private theorem pr1123 : Nat.Prime 1123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv1123 : PrimeValue := ⟨1123, pr1123⟩
private theorem pr1129 : Nat.Prime 1129 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv1129 : PrimeValue := ⟨1129, pr1129⟩
private theorem pr1151 : Nat.Prime 1151 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv23]) (by decide +kernel)
def pv1151 : PrimeValue := ⟨1151, pr1151⟩
private theorem pr1153 : Nat.Prime 1153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv1153 : PrimeValue := ⟨1153, pr1153⟩
private theorem pr1163 : Nat.Prime 1163 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv83]) (by decide +kernel)
def pv1163 : PrimeValue := ⟨1163, pr1163⟩
private theorem pr1171 : Nat.Prime 1171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv1171 : PrimeValue := ⟨1171, pr1171⟩
private theorem pr1181 : Nat.Prime 1181 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv59]) (by decide +kernel)
def pv1181 : PrimeValue := ⟨1181, pr1181⟩
private theorem pr1187 : Nat.Prime 1187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv593]) (by decide +kernel)
def pv1187 : PrimeValue := ⟨1187, pr1187⟩
private theorem pr1193 : Nat.Prime 1193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv149]) (by decide +kernel)
def pv1193 : PrimeValue := ⟨1193, pr1193⟩
private theorem pr1201 : Nat.Prime 1201 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv1201 : PrimeValue := ⟨1201, pr1201⟩
private theorem pr1213 : Nat.Prime 1213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv1213 : PrimeValue := ⟨1213, pr1213⟩
private theorem pr1217 : Nat.Prime 1217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19]) (by decide +kernel)
def pv1217 : PrimeValue := ⟨1217, pr1217⟩
private theorem pr1223 : Nat.Prime 1223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv47]) (by decide +kernel)
def pv1223 : PrimeValue := ⟨1223, pr1223⟩
private theorem pr1229 : Nat.Prime 1229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv307]) (by decide +kernel)
def pv1229 : PrimeValue := ⟨1229, pr1229⟩
private theorem pr1231 : Nat.Prime 1231 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv1231 : PrimeValue := ⟨1231, pr1231⟩
private theorem pr1237 : Nat.Prime 1237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv1237 : PrimeValue := ⟨1237, pr1237⟩
private theorem pr1249 : Nat.Prime 1249 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv1249 : PrimeValue := ⟨1249, pr1249⟩
private theorem pr1259 : Nat.Prime 1259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv37]) (by decide +kernel)
def pv1259 : PrimeValue := ⟨1259, pr1259⟩
private theorem pr1277 : Nat.Prime 1277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv29]) (by decide +kernel)
def pv1277 : PrimeValue := ⟨1277, pr1277⟩
private theorem pr1279 : Nat.Prime 1279 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv1279 : PrimeValue := ⟨1279, pr1279⟩
private theorem pr1283 : Nat.Prime 1283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv641]) (by decide +kernel)
def pv1283 : PrimeValue := ⟨1283, pr1283⟩
private theorem pr1289 : Nat.Prime 1289 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv23]) (by decide +kernel)
def pv1289 : PrimeValue := ⟨1289, pr1289⟩
private theorem pr1291 : Nat.Prime 1291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv1291 : PrimeValue := ⟨1291, pr1291⟩
private theorem pr1297 : Nat.Prime 1297 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3]) (by decide +kernel)
def pv1297 : PrimeValue := ⟨1297, pr1297⟩
private theorem pr1301 : Nat.Prime 1301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv1301 : PrimeValue := ⟨1301, pr1301⟩
private theorem pr1303 : Nat.Prime 1303 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv1303 : PrimeValue := ⟨1303, pr1303⟩
private theorem pr1307 : Nat.Prime 1307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv653]) (by decide +kernel)
def pv1307 : PrimeValue := ⟨1307, pr1307⟩
private theorem pr1319 : Nat.Prime 1319 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv659]) (by decide +kernel)
def pv1319 : PrimeValue := ⟨1319, pr1319⟩
private theorem pr1321 : Nat.Prime 1321 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv1321 : PrimeValue := ⟨1321, pr1321⟩
private theorem pr1327 : Nat.Prime 1327 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv1327 : PrimeValue := ⟨1327, pr1327⟩
private theorem pr1361 : Nat.Prime 1361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17]) (by decide +kernel)
def pv1361 : PrimeValue := ⟨1361, pr1361⟩
private theorem pr1367 : Nat.Prime 1367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv683]) (by decide +kernel)
def pv1367 : PrimeValue := ⟨1367, pr1367⟩
private theorem pr1373 : Nat.Prime 1373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7]) (by decide +kernel)
def pv1373 : PrimeValue := ⟨1373, pr1373⟩
private theorem pr1381 : Nat.Prime 1381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv1381 : PrimeValue := ⟨1381, pr1381⟩
private theorem pr1399 : Nat.Prime 1399 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv233]) (by decide +kernel)
def pv1399 : PrimeValue := ⟨1399, pr1399⟩
private theorem pr1409 : Nat.Prime 1409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11]) (by decide +kernel)
def pv1409 : PrimeValue := ⟨1409, pr1409⟩
private theorem pr1423 : Nat.Prime 1423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv1423 : PrimeValue := ⟨1423, pr1423⟩
private theorem pr1427 : Nat.Prime 1427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv31]) (by decide +kernel)
def pv1427 : PrimeValue := ⟨1427, pr1427⟩
private theorem pr1429 : Nat.Prime 1429 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv1429 : PrimeValue := ⟨1429, pr1429⟩
private theorem pr1433 : Nat.Prime 1433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv179]) (by decide +kernel)
def pv1433 : PrimeValue := ⟨1433, pr1433⟩
private theorem pr1439 : Nat.Prime 1439 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv719]) (by decide +kernel)
def pv1439 : PrimeValue := ⟨1439, pr1439⟩
private theorem pr1447 : Nat.Prime 1447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv241]) (by decide +kernel)
def pv1447 : PrimeValue := ⟨1447, pr1447⟩
private theorem pr1451 : Nat.Prime 1451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29]) (by decide +kernel)
def pv1451 : PrimeValue := ⟨1451, pr1451⟩
private theorem pr1453 : Nat.Prime 1453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv1453 : PrimeValue := ⟨1453, pr1453⟩
private theorem pr1459 : Nat.Prime 1459 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3]) (by decide +kernel)
def pv1459 : PrimeValue := ⟨1459, pr1459⟩
private theorem pr1471 : Nat.Prime 1471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv1471 : PrimeValue := ⟨1471, pr1471⟩
private theorem pr1481 : Nat.Prime 1481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv37]) (by decide +kernel)
def pv1481 : PrimeValue := ⟨1481, pr1481⟩
private theorem pr1483 : Nat.Prime 1483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv1483 : PrimeValue := ⟨1483, pr1483⟩
private theorem pr1487 : Nat.Prime 1487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv743]) (by decide +kernel)
def pv1487 : PrimeValue := ⟨1487, pr1487⟩
private theorem pr1489 : Nat.Prime 1489 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv1489 : PrimeValue := ⟨1489, pr1489⟩
private theorem pr1493 : Nat.Prime 1493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv373]) (by decide +kernel)
def pv1493 : PrimeValue := ⟨1493, pr1493⟩
private theorem pr1499 : Nat.Prime 1499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv107]) (by decide +kernel)
def pv1499 : PrimeValue := ⟨1499, pr1499⟩
private theorem pr1511 : Nat.Prime 1511 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv151]) (by decide +kernel)
def pv1511 : PrimeValue := ⟨1511, pr1511⟩
private theorem pr1523 : Nat.Prime 1523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv761]) (by decide +kernel)
def pv1523 : PrimeValue := ⟨1523, pr1523⟩
private theorem pr1531 : Nat.Prime 1531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv1531 : PrimeValue := ⟨1531, pr1531⟩
private theorem pr1543 : Nat.Prime 1543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv257]) (by decide +kernel)
def pv1543 : PrimeValue := ⟨1543, pr1543⟩
private theorem pr1549 : Nat.Prime 1549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv1549 : PrimeValue := ⟨1549, pr1549⟩
private theorem pr1553 : Nat.Prime 1553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv97]) (by decide +kernel)
def pv1553 : PrimeValue := ⟨1553, pr1553⟩
private theorem pr1559 : Nat.Prime 1559 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv19,pv41]) (by decide +kernel)
def pv1559 : PrimeValue := ⟨1559, pr1559⟩
private theorem pr1567 : Nat.Prime 1567 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv1567 : PrimeValue := ⟨1567, pr1567⟩
private theorem pr1571 : Nat.Prime 1571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv157]) (by decide +kernel)
def pv1571 : PrimeValue := ⟨1571, pr1571⟩
private theorem pr1579 : Nat.Prime 1579 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv263]) (by decide +kernel)
def pv1579 : PrimeValue := ⟨1579, pr1579⟩
private theorem pr1583 : Nat.Prime 1583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv113]) (by decide +kernel)
def pv1583 : PrimeValue := ⟨1583, pr1583⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
