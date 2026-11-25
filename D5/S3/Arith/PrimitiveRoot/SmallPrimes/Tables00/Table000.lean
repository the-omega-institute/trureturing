/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table000
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table000.pv2
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Kernel

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

def pv2 : PrimeValue := ⟨2, .two⟩
private theorem pr3 : PrimeCertificate 3 :=
  certifyPrime (q := pv2) (ls := [pv2]) (by decide +kernel)
def pv3 : PrimeValue := ⟨3, pr3⟩
private theorem pr5 : PrimeCertificate 5 :=
  certifyPrime (q := pv2) (ls := [pv2]) (by decide +kernel)
def pv5 : PrimeValue := ⟨5, pr5⟩
private theorem pr7 : PrimeCertificate 7 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3]) (by decide +kernel)
def pv7 : PrimeValue := ⟨7, pr7⟩
private theorem pr11 : PrimeCertificate 11 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5]) (by decide +kernel)
def pv11 : PrimeValue := ⟨11, pr11⟩
private theorem pr13 : PrimeCertificate 13 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3]) (by decide +kernel)
def pv13 : PrimeValue := ⟨13, pr13⟩
private theorem pr17 : PrimeCertificate 17 :=
  certifyPrime (q := pv3) (ls := [pv2]) (by decide +kernel)
def pv17 : PrimeValue := ⟨17, pr17⟩
private theorem pr19 : PrimeCertificate 19 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3]) (by decide +kernel)
def pv19 : PrimeValue := ⟨19, pr19⟩
private theorem pr23 : PrimeCertificate 23 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11]) (by decide +kernel)
def pv23 : PrimeValue := ⟨23, pr23⟩
private theorem pr29 : PrimeCertificate 29 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7]) (by decide +kernel)
def pv29 : PrimeValue := ⟨29, pr29⟩
private theorem pr31 : PrimeCertificate 31 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv31 : PrimeValue := ⟨31, pr31⟩
private theorem pr37 : PrimeCertificate 37 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3]) (by decide +kernel)
def pv37 : PrimeValue := ⟨37, pr37⟩
private theorem pr41 : PrimeCertificate 41 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5]) (by decide +kernel)
def pv41 : PrimeValue := ⟨41, pr41⟩
private theorem pr43 : PrimeCertificate 43 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv43 : PrimeValue := ⟨43, pr43⟩
private theorem pr47 : PrimeCertificate 47 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23]) (by decide +kernel)
def pv47 : PrimeValue := ⟨47, pr47⟩
private theorem pr53 : PrimeCertificate 53 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13]) (by decide +kernel)
def pv53 : PrimeValue := ⟨53, pr53⟩
private theorem pr59 : PrimeCertificate 59 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29]) (by decide +kernel)
def pv59 : PrimeValue := ⟨59, pr59⟩
private theorem pr61 : PrimeCertificate 61 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv61 : PrimeValue := ⟨61, pr61⟩
private theorem pr67 : PrimeCertificate 67 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv67 : PrimeValue := ⟨67, pr67⟩
private theorem pr71 : PrimeCertificate 71 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv71 : PrimeValue := ⟨71, pr71⟩
private theorem pr73 : PrimeCertificate 73 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv73 : PrimeValue := ⟨73, pr73⟩
private theorem pr79 : PrimeCertificate 79 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv79 : PrimeValue := ⟨79, pr79⟩
private theorem pr83 : PrimeCertificate 83 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41]) (by decide +kernel)
def pv83 : PrimeValue := ⟨83, pr83⟩
private theorem pr89 : PrimeCertificate 89 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11]) (by decide +kernel)
def pv89 : PrimeValue := ⟨89, pr89⟩
private theorem pr97 : PrimeCertificate 97 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv97 : PrimeValue := ⟨97, pr97⟩
private theorem pr101 : PrimeCertificate 101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5]) (by decide +kernel)
def pv101 : PrimeValue := ⟨101, pr101⟩
private theorem pr103 : PrimeCertificate 103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv103 : PrimeValue := ⟨103, pr103⟩
private theorem pr107 : PrimeCertificate 107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53]) (by decide +kernel)
def pv107 : PrimeValue := ⟨107, pr107⟩
private theorem pr109 : PrimeCertificate 109 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3]) (by decide +kernel)
def pv109 : PrimeValue := ⟨109, pr109⟩
private theorem pr113 : PrimeCertificate 113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7]) (by decide +kernel)
def pv113 : PrimeValue := ⟨113, pr113⟩
private theorem pr127 : PrimeCertificate 127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv127 : PrimeValue := ⟨127, pr127⟩
private theorem pr131 : PrimeCertificate 131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv131 : PrimeValue := ⟨131, pr131⟩
private theorem pr137 : PrimeCertificate 137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17]) (by decide +kernel)
def pv137 : PrimeValue := ⟨137, pr137⟩
private theorem pr139 : PrimeCertificate 139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv139 : PrimeValue := ⟨139, pr139⟩
private theorem pr149 : PrimeCertificate 149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37]) (by decide +kernel)
def pv149 : PrimeValue := ⟨149, pr149⟩
private theorem pr151 : PrimeCertificate 151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv151 : PrimeValue := ⟨151, pr151⟩
private theorem pr157 : PrimeCertificate 157 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv157 : PrimeValue := ⟨157, pr157⟩
private theorem pr163 : PrimeCertificate 163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3]) (by decide +kernel)
def pv163 : PrimeValue := ⟨163, pr163⟩
private theorem pr167 : PrimeCertificate 167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv83]) (by decide +kernel)
def pv167 : PrimeValue := ⟨167, pr167⟩
private theorem pr173 : PrimeCertificate 173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43]) (by decide +kernel)
def pv173 : PrimeValue := ⟨173, pr173⟩
private theorem pr179 : PrimeCertificate 179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89]) (by decide +kernel)
def pv179 : PrimeValue := ⟨179, pr179⟩
private theorem pr181 : PrimeCertificate 181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv181 : PrimeValue := ⟨181, pr181⟩
private theorem pr191 : PrimeCertificate 191 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv191 : PrimeValue := ⟨191, pr191⟩
private theorem pr193 : PrimeCertificate 193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv193 : PrimeValue := ⟨193, pr193⟩
private theorem pr197 : PrimeCertificate 197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7]) (by decide +kernel)
def pv197 : PrimeValue := ⟨197, pr197⟩
private theorem pr199 : PrimeCertificate 199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv199 : PrimeValue := ⟨199, pr199⟩
private theorem pr211 : PrimeCertificate 211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv211 : PrimeValue := ⟨211, pr211⟩
private theorem pr223 : PrimeCertificate 223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv223 : PrimeValue := ⟨223, pr223⟩
private theorem pr227 : PrimeCertificate 227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113]) (by decide +kernel)
def pv227 : PrimeValue := ⟨227, pr227⟩
private theorem pr229 : PrimeCertificate 229 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv229 : PrimeValue := ⟨229, pr229⟩
private theorem pr233 : PrimeCertificate 233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29]) (by decide +kernel)
def pv233 : PrimeValue := ⟨233, pr233⟩
private theorem pr239 : PrimeCertificate 239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17]) (by decide +kernel)
def pv239 : PrimeValue := ⟨239, pr239⟩
private theorem pr241 : PrimeCertificate 241 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv241 : PrimeValue := ⟨241, pr241⟩
private theorem pr251 : PrimeCertificate 251 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5]) (by decide +kernel)
def pv251 : PrimeValue := ⟨251, pr251⟩
private theorem pr257 : PrimeCertificate 257 :=
  certifyPrime (q := pv3) (ls := [pv2]) (by decide +kernel)
def pv257 : PrimeValue := ⟨257, pr257⟩
private theorem pr263 : PrimeCertificate 263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv131]) (by decide +kernel)
def pv263 : PrimeValue := ⟨263, pr263⟩
private theorem pr269 : PrimeCertificate 269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67]) (by decide +kernel)
def pv269 : PrimeValue := ⟨269, pr269⟩
private theorem pr271 : PrimeCertificate 271 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv271 : PrimeValue := ⟨271, pr271⟩
private theorem pr277 : PrimeCertificate 277 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv277 : PrimeValue := ⟨277, pr277⟩
private theorem pr281 : PrimeCertificate 281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv281 : PrimeValue := ⟨281, pr281⟩
private theorem pr283 : PrimeCertificate 283 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv283 : PrimeValue := ⟨283, pr283⟩
private theorem pr293 : PrimeCertificate 293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73]) (by decide +kernel)
def pv293 : PrimeValue := ⟨293, pr293⟩
private theorem pr307 : PrimeCertificate 307 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv307 : PrimeValue := ⟨307, pr307⟩
private theorem pr311 : PrimeCertificate 311 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv31]) (by decide +kernel)
def pv311 : PrimeValue := ⟨311, pr311⟩
private theorem pr313 : PrimeCertificate 313 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv313 : PrimeValue := ⟨313, pr313⟩
private theorem pr317 : PrimeCertificate 317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79]) (by decide +kernel)
def pv317 : PrimeValue := ⟨317, pr317⟩
private theorem pr331 : PrimeCertificate 331 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv331 : PrimeValue := ⟨331, pr331⟩
private theorem pr337 : PrimeCertificate 337 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv337 : PrimeValue := ⟨337, pr337⟩
private theorem pr347 : PrimeCertificate 347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173]) (by decide +kernel)
def pv347 : PrimeValue := ⟨347, pr347⟩
private theorem pr349 : PrimeCertificate 349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv349 : PrimeValue := ⟨349, pr349⟩
private theorem pr353 : PrimeCertificate 353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11]) (by decide +kernel)
def pv353 : PrimeValue := ⟨353, pr353⟩
private theorem pr359 : PrimeCertificate 359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv179]) (by decide +kernel)
def pv359 : PrimeValue := ⟨359, pr359⟩
private theorem pr367 : PrimeCertificate 367 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv367 : PrimeValue := ⟨367, pr367⟩
private theorem pr373 : PrimeCertificate 373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv373 : PrimeValue := ⟨373, pr373⟩
private theorem pr379 : PrimeCertificate 379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv379 : PrimeValue := ⟨379, pr379⟩
private theorem pr383 : PrimeCertificate 383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv191]) (by decide +kernel)
def pv383 : PrimeValue := ⟨383, pr383⟩
private theorem pr389 : PrimeCertificate 389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97]) (by decide +kernel)
def pv389 : PrimeValue := ⟨389, pr389⟩
private theorem pr397 : PrimeCertificate 397 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv397 : PrimeValue := ⟨397, pr397⟩
private theorem pr401 : PrimeCertificate 401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5]) (by decide +kernel)
def pv401 : PrimeValue := ⟨401, pr401⟩
private theorem pr409 : PrimeCertificate 409 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv409 : PrimeValue := ⟨409, pr409⟩
private theorem pr419 : PrimeCertificate 419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19]) (by decide +kernel)
def pv419 : PrimeValue := ⟨419, pr419⟩
private theorem pr421 : PrimeCertificate 421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv421 : PrimeValue := ⟨421, pr421⟩
private theorem pr431 : PrimeCertificate 431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv43]) (by decide +kernel)
def pv431 : PrimeValue := ⟨431, pr431⟩
private theorem pr433 : PrimeCertificate 433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv433 : PrimeValue := ⟨433, pr433⟩
private theorem pr439 : PrimeCertificate 439 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv439 : PrimeValue := ⟨439, pr439⟩
private theorem pr443 : PrimeCertificate 443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17]) (by decide +kernel)
def pv443 : PrimeValue := ⟨443, pr443⟩
private theorem pr449 : PrimeCertificate 449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7]) (by decide +kernel)
def pv449 : PrimeValue := ⟨449, pr449⟩
private theorem pr457 : PrimeCertificate 457 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv457 : PrimeValue := ⟨457, pr457⟩
private theorem pr461 : PrimeCertificate 461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23]) (by decide +kernel)
def pv461 : PrimeValue := ⟨461, pr461⟩
private theorem pr463 : PrimeCertificate 463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv463 : PrimeValue := ⟨463, pr463⟩
private theorem pr467 : PrimeCertificate 467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv233]) (by decide +kernel)
def pv467 : PrimeValue := ⟨467, pr467⟩
private theorem pr479 : PrimeCertificate 479 :=
  certifyPrime (q := pv13) (ls := [pv2,pv239]) (by decide +kernel)
def pv479 : PrimeValue := ⟨479, pr479⟩
private theorem pr487 : PrimeCertificate 487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3]) (by decide +kernel)
def pv487 : PrimeValue := ⟨487, pr487⟩
private theorem pr491 : PrimeCertificate 491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv491 : PrimeValue := ⟨491, pr491⟩
private theorem pr499 : PrimeCertificate 499 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv499 : PrimeValue := ⟨499, pr499⟩
private theorem pr503 : PrimeCertificate 503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv251]) (by decide +kernel)
def pv503 : PrimeValue := ⟨503, pr503⟩
private theorem pr509 : PrimeCertificate 509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127]) (by decide +kernel)
def pv509 : PrimeValue := ⟨509, pr509⟩
private theorem pr521 : PrimeCertificate 521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv521 : PrimeValue := ⟨521, pr521⟩
private theorem pr523 : PrimeCertificate 523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv523 : PrimeValue := ⟨523, pr523⟩
private theorem pr541 : PrimeCertificate 541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv541 : PrimeValue := ⟨541, pr541⟩
private theorem pr547 : PrimeCertificate 547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv547 : PrimeValue := ⟨547, pr547⟩
private theorem pr557 : PrimeCertificate 557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139]) (by decide +kernel)
def pv557 : PrimeValue := ⟨557, pr557⟩
private theorem pr563 : PrimeCertificate 563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv281]) (by decide +kernel)
def pv563 : PrimeValue := ⟨563, pr563⟩
private theorem pr569 : PrimeCertificate 569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71]) (by decide +kernel)
def pv569 : PrimeValue := ⟨569, pr569⟩
private theorem pr571 : PrimeCertificate 571 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv571 : PrimeValue := ⟨571, pr571⟩
private theorem pr577 : PrimeCertificate 577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv577 : PrimeValue := ⟨577, pr577⟩
private theorem pr587 : PrimeCertificate 587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv293]) (by decide +kernel)
def pv587 : PrimeValue := ⟨587, pr587⟩
private theorem pr593 : PrimeCertificate 593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37]) (by decide +kernel)
def pv593 : PrimeValue := ⟨593, pr593⟩
private theorem pr599 : PrimeCertificate 599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv23]) (by decide +kernel)
def pv599 : PrimeValue := ⟨599, pr599⟩
private theorem pr601 : PrimeCertificate 601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv601 : PrimeValue := ⟨601, pr601⟩
private theorem pr607 : PrimeCertificate 607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv607 : PrimeValue := ⟨607, pr607⟩
private theorem pr613 : PrimeCertificate 613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv613 : PrimeValue := ⟨613, pr613⟩
private theorem pr617 : PrimeCertificate 617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11]) (by decide +kernel)
def pv617 : PrimeValue := ⟨617, pr617⟩
private theorem pr619 : PrimeCertificate 619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv619 : PrimeValue := ⟨619, pr619⟩
private theorem pr631 : PrimeCertificate 631 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv631 : PrimeValue := ⟨631, pr631⟩
private theorem pr641 : PrimeCertificate 641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5]) (by decide +kernel)
def pv641 : PrimeValue := ⟨641, pr641⟩
private theorem pr643 : PrimeCertificate 643 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv643 : PrimeValue := ⟨643, pr643⟩
private theorem pr647 : PrimeCertificate 647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv19]) (by decide +kernel)
def pv647 : PrimeValue := ⟨647, pr647⟩
private theorem pr653 : PrimeCertificate 653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163]) (by decide +kernel)
def pv653 : PrimeValue := ⟨653, pr653⟩
private theorem pr659 : PrimeCertificate 659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv47]) (by decide +kernel)
def pv659 : PrimeValue := ⟨659, pr659⟩
private theorem pr661 : PrimeCertificate 661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv661 : PrimeValue := ⟨661, pr661⟩
private theorem pr673 : PrimeCertificate 673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv673 : PrimeValue := ⟨673, pr673⟩
private theorem pr677 : PrimeCertificate 677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13]) (by decide +kernel)
def pv677 : PrimeValue := ⟨677, pr677⟩
private theorem pr683 : PrimeCertificate 683 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv31]) (by decide +kernel)
def pv683 : PrimeValue := ⟨683, pr683⟩
private theorem pr691 : PrimeCertificate 691 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv691 : PrimeValue := ⟨691, pr691⟩
private theorem pr701 : PrimeCertificate 701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv701 : PrimeValue := ⟨701, pr701⟩
private theorem pr709 : PrimeCertificate 709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv709 : PrimeValue := ⟨709, pr709⟩
private theorem pr719 : PrimeCertificate 719 :=
  certifyPrime (q := pv11) (ls := [pv2,pv359]) (by decide +kernel)
def pv719 : PrimeValue := ⟨719, pr719⟩
private theorem pr727 : PrimeCertificate 727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv727 : PrimeValue := ⟨727, pr727⟩
private theorem pr733 : PrimeCertificate 733 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv733 : PrimeValue := ⟨733, pr733⟩
private theorem pr739 : PrimeCertificate 739 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv739 : PrimeValue := ⟨739, pr739⟩
private theorem pr743 : PrimeCertificate 743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv53]) (by decide +kernel)
def pv743 : PrimeValue := ⟨743, pr743⟩
private theorem pr751 : PrimeCertificate 751 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv751 : PrimeValue := ⟨751, pr751⟩
private theorem pr757 : PrimeCertificate 757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv757 : PrimeValue := ⟨757, pr757⟩
private theorem pr761 : PrimeCertificate 761 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv761 : PrimeValue := ⟨761, pr761⟩
private theorem pr769 : PrimeCertificate 769 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3]) (by decide +kernel)
def pv769 : PrimeValue := ⟨769, pr769⟩
private theorem pr773 : PrimeCertificate 773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193]) (by decide +kernel)
def pv773 : PrimeValue := ⟨773, pr773⟩
private theorem pr787 : PrimeCertificate 787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv131]) (by decide +kernel)
def pv787 : PrimeValue := ⟨787, pr787⟩
private theorem pr797 : PrimeCertificate 797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv199]) (by decide +kernel)
def pv797 : PrimeValue := ⟨797, pr797⟩
private theorem pr809 : PrimeCertificate 809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101]) (by decide +kernel)
def pv809 : PrimeValue := ⟨809, pr809⟩
private theorem pr811 : PrimeCertificate 811 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv811 : PrimeValue := ⟨811, pr811⟩
private theorem pr821 : PrimeCertificate 821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41]) (by decide +kernel)
def pv821 : PrimeValue := ⟨821, pr821⟩
private theorem pr823 : PrimeCertificate 823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv137]) (by decide +kernel)
def pv823 : PrimeValue := ⟨823, pr823⟩
private theorem pr827 : PrimeCertificate 827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv59]) (by decide +kernel)
def pv827 : PrimeValue := ⟨827, pr827⟩
private theorem pr829 : PrimeCertificate 829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv829 : PrimeValue := ⟨829, pr829⟩
private theorem pr839 : PrimeCertificate 839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv419]) (by decide +kernel)
def pv839 : PrimeValue := ⟨839, pr839⟩
private theorem pr853 : PrimeCertificate 853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv853 : PrimeValue := ⟨853, pr853⟩
private theorem pr857 : PrimeCertificate 857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107]) (by decide +kernel)
def pv857 : PrimeValue := ⟨857, pr857⟩
private theorem pr859 : PrimeCertificate 859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv859 : PrimeValue := ⟨859, pr859⟩
private theorem pr863 : PrimeCertificate 863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv431]) (by decide +kernel)
def pv863 : PrimeValue := ⟨863, pr863⟩
private theorem pr877 : PrimeCertificate 877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv877 : PrimeValue := ⟨877, pr877⟩
private theorem pr881 : PrimeCertificate 881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv881 : PrimeValue := ⟨881, pr881⟩
private theorem pr883 : PrimeCertificate 883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv883 : PrimeValue := ⟨883, pr883⟩
private theorem pr887 : PrimeCertificate 887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv443]) (by decide +kernel)
def pv887 : PrimeValue := ⟨887, pr887⟩
private theorem pr907 : PrimeCertificate 907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv151]) (by decide +kernel)
def pv907 : PrimeValue := ⟨907, pr907⟩
private theorem pr911 : PrimeCertificate 911 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv13]) (by decide +kernel)
def pv911 : PrimeValue := ⟨911, pr911⟩
private theorem pr919 : PrimeCertificate 919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv919 : PrimeValue := ⟨919, pr919⟩
private theorem pr929 : PrimeCertificate 929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29]) (by decide +kernel)
def pv929 : PrimeValue := ⟨929, pr929⟩
private theorem pr937 : PrimeCertificate 937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv937 : PrimeValue := ⟨937, pr937⟩
private theorem pr941 : PrimeCertificate 941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47]) (by decide +kernel)
def pv941 : PrimeValue := ⟨941, pr941⟩
private theorem pr947 : PrimeCertificate 947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv43]) (by decide +kernel)
def pv947 : PrimeValue := ⟨947, pr947⟩
private theorem pr953 : PrimeCertificate 953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17]) (by decide +kernel)
def pv953 : PrimeValue := ⟨953, pr953⟩
private theorem pr967 : PrimeCertificate 967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv967 : PrimeValue := ⟨967, pr967⟩
private theorem pr971 : PrimeCertificate 971 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv97]) (by decide +kernel)
def pv971 : PrimeValue := ⟨971, pr971⟩
private theorem pr977 : PrimeCertificate 977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61]) (by decide +kernel)
def pv977 : PrimeValue := ⟨977, pr977⟩
private theorem pr983 : PrimeCertificate 983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv491]) (by decide +kernel)
def pv983 : PrimeValue := ⟨983, pr983⟩
private theorem pr991 : PrimeCertificate 991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv991 : PrimeValue := ⟨991, pr991⟩
private theorem pr997 : PrimeCertificate 997 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv997 : PrimeValue := ⟨997, pr997⟩
private theorem pr1009 : PrimeCertificate 1009 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv1009 : PrimeValue := ⟨1009, pr1009⟩
private theorem pr1013 : PrimeCertificate 1013 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv23]) (by decide +kernel)
def pv1013 : PrimeValue := ⟨1013, pr1013⟩
private theorem pr1019 : PrimeCertificate 1019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv509]) (by decide +kernel)
def pv1019 : PrimeValue := ⟨1019, pr1019⟩
private theorem pr1021 : PrimeCertificate 1021 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv1021 : PrimeValue := ⟨1021, pr1021⟩
private theorem pr1031 : PrimeCertificate 1031 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv103]) (by decide +kernel)
def pv1031 : PrimeValue := ⟨1031, pr1031⟩
private theorem pr1033 : PrimeCertificate 1033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv1033 : PrimeValue := ⟨1033, pr1033⟩
private theorem pr1039 : PrimeCertificate 1039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv173]) (by decide +kernel)
def pv1039 : PrimeValue := ⟨1039, pr1039⟩
private theorem pr1049 : PrimeCertificate 1049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv131]) (by decide +kernel)
def pv1049 : PrimeValue := ⟨1049, pr1049⟩
private theorem pr1051 : PrimeCertificate 1051 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv1051 : PrimeValue := ⟨1051, pr1051⟩
private theorem pr1061 : PrimeCertificate 1061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53]) (by decide +kernel)
def pv1061 : PrimeValue := ⟨1061, pr1061⟩
private theorem pr1063 : PrimeCertificate 1063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv1063 : PrimeValue := ⟨1063, pr1063⟩
private theorem pr1069 : PrimeCertificate 1069 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv89]) (by decide +kernel)
def pv1069 : PrimeValue := ⟨1069, pr1069⟩
private theorem pr1087 : PrimeCertificate 1087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv181]) (by decide +kernel)
def pv1087 : PrimeValue := ⟨1087, pr1087⟩
private theorem pr1091 : PrimeCertificate 1091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv109]) (by decide +kernel)
def pv1091 : PrimeValue := ⟨1091, pr1091⟩
private theorem pr1093 : PrimeCertificate 1093 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv1093 : PrimeValue := ⟨1093, pr1093⟩
private theorem pr1097 : PrimeCertificate 1097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv137]) (by decide +kernel)
def pv1097 : PrimeValue := ⟨1097, pr1097⟩
private theorem pr1103 : PrimeCertificate 1103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv29]) (by decide +kernel)
def pv1103 : PrimeValue := ⟨1103, pr1103⟩
private theorem pr1109 : PrimeCertificate 1109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv277]) (by decide +kernel)
def pv1109 : PrimeValue := ⟨1109, pr1109⟩
private theorem pr1117 : PrimeCertificate 1117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv1117 : PrimeValue := ⟨1117, pr1117⟩
private theorem pr1123 : PrimeCertificate 1123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv1123 : PrimeValue := ⟨1123, pr1123⟩
private theorem pr1129 : PrimeCertificate 1129 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv1129 : PrimeValue := ⟨1129, pr1129⟩
private theorem pr1151 : PrimeCertificate 1151 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv23]) (by decide +kernel)
def pv1151 : PrimeValue := ⟨1151, pr1151⟩
private theorem pr1153 : PrimeCertificate 1153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv1153 : PrimeValue := ⟨1153, pr1153⟩
private theorem pr1163 : PrimeCertificate 1163 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv83]) (by decide +kernel)
def pv1163 : PrimeValue := ⟨1163, pr1163⟩
private theorem pr1171 : PrimeCertificate 1171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv1171 : PrimeValue := ⟨1171, pr1171⟩
private theorem pr1181 : PrimeCertificate 1181 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv59]) (by decide +kernel)
def pv1181 : PrimeValue := ⟨1181, pr1181⟩
private theorem pr1187 : PrimeCertificate 1187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv593]) (by decide +kernel)
def pv1187 : PrimeValue := ⟨1187, pr1187⟩
private theorem pr1193 : PrimeCertificate 1193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv149]) (by decide +kernel)
def pv1193 : PrimeValue := ⟨1193, pr1193⟩
private theorem pr1201 : PrimeCertificate 1201 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv1201 : PrimeValue := ⟨1201, pr1201⟩
private theorem pr1213 : PrimeCertificate 1213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv1213 : PrimeValue := ⟨1213, pr1213⟩
private theorem pr1217 : PrimeCertificate 1217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19]) (by decide +kernel)
def pv1217 : PrimeValue := ⟨1217, pr1217⟩
private theorem pr1223 : PrimeCertificate 1223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv47]) (by decide +kernel)
def pv1223 : PrimeValue := ⟨1223, pr1223⟩
private theorem pr1229 : PrimeCertificate 1229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv307]) (by decide +kernel)
def pv1229 : PrimeValue := ⟨1229, pr1229⟩
private theorem pr1231 : PrimeCertificate 1231 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv1231 : PrimeValue := ⟨1231, pr1231⟩
private theorem pr1237 : PrimeCertificate 1237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv1237 : PrimeValue := ⟨1237, pr1237⟩
private theorem pr1249 : PrimeCertificate 1249 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv1249 : PrimeValue := ⟨1249, pr1249⟩
private theorem pr1259 : PrimeCertificate 1259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv37]) (by decide +kernel)
def pv1259 : PrimeValue := ⟨1259, pr1259⟩
private theorem pr1277 : PrimeCertificate 1277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv29]) (by decide +kernel)
def pv1277 : PrimeValue := ⟨1277, pr1277⟩
private theorem pr1279 : PrimeCertificate 1279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv1279 : PrimeValue := ⟨1279, pr1279⟩
private theorem pr1283 : PrimeCertificate 1283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv641]) (by decide +kernel)
def pv1283 : PrimeValue := ⟨1283, pr1283⟩
private theorem pr1289 : PrimeCertificate 1289 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv23]) (by decide +kernel)
def pv1289 : PrimeValue := ⟨1289, pr1289⟩
private theorem pr1291 : PrimeCertificate 1291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv1291 : PrimeValue := ⟨1291, pr1291⟩
private theorem pr1297 : PrimeCertificate 1297 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3]) (by decide +kernel)
def pv1297 : PrimeValue := ⟨1297, pr1297⟩
private theorem pr1301 : PrimeCertificate 1301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv1301 : PrimeValue := ⟨1301, pr1301⟩
private theorem pr1303 : PrimeCertificate 1303 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv1303 : PrimeValue := ⟨1303, pr1303⟩
private theorem pr1307 : PrimeCertificate 1307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv653]) (by decide +kernel)
def pv1307 : PrimeValue := ⟨1307, pr1307⟩
private theorem pr1319 : PrimeCertificate 1319 :=
  certifyPrime (q := pv13) (ls := [pv2,pv659]) (by decide +kernel)
def pv1319 : PrimeValue := ⟨1319, pr1319⟩
private theorem pr1321 : PrimeCertificate 1321 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv1321 : PrimeValue := ⟨1321, pr1321⟩
private theorem pr1327 : PrimeCertificate 1327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv1327 : PrimeValue := ⟨1327, pr1327⟩
private theorem pr1361 : PrimeCertificate 1361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17]) (by decide +kernel)
def pv1361 : PrimeValue := ⟨1361, pr1361⟩
private theorem pr1367 : PrimeCertificate 1367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv683]) (by decide +kernel)
def pv1367 : PrimeValue := ⟨1367, pr1367⟩
private theorem pr1373 : PrimeCertificate 1373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7]) (by decide +kernel)
def pv1373 : PrimeValue := ⟨1373, pr1373⟩
private theorem pr1381 : PrimeCertificate 1381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv1381 : PrimeValue := ⟨1381, pr1381⟩
private theorem pr1399 : PrimeCertificate 1399 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv233]) (by decide +kernel)
def pv1399 : PrimeValue := ⟨1399, pr1399⟩
private theorem pr1409 : PrimeCertificate 1409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11]) (by decide +kernel)
def pv1409 : PrimeValue := ⟨1409, pr1409⟩
private theorem pr1423 : PrimeCertificate 1423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv1423 : PrimeValue := ⟨1423, pr1423⟩
private theorem pr1427 : PrimeCertificate 1427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv31]) (by decide +kernel)
def pv1427 : PrimeValue := ⟨1427, pr1427⟩
private theorem pr1429 : PrimeCertificate 1429 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv1429 : PrimeValue := ⟨1429, pr1429⟩
private theorem pr1433 : PrimeCertificate 1433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv179]) (by decide +kernel)
def pv1433 : PrimeValue := ⟨1433, pr1433⟩
private theorem pr1439 : PrimeCertificate 1439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv719]) (by decide +kernel)
def pv1439 : PrimeValue := ⟨1439, pr1439⟩
private theorem pr1447 : PrimeCertificate 1447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv241]) (by decide +kernel)
def pv1447 : PrimeValue := ⟨1447, pr1447⟩
private theorem pr1451 : PrimeCertificate 1451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29]) (by decide +kernel)
def pv1451 : PrimeValue := ⟨1451, pr1451⟩
private theorem pr1453 : PrimeCertificate 1453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv1453 : PrimeValue := ⟨1453, pr1453⟩
private theorem pr1459 : PrimeCertificate 1459 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3]) (by decide +kernel)
def pv1459 : PrimeValue := ⟨1459, pr1459⟩
private theorem pr1471 : PrimeCertificate 1471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv1471 : PrimeValue := ⟨1471, pr1471⟩
private theorem pr1481 : PrimeCertificate 1481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37]) (by decide +kernel)
def pv1481 : PrimeValue := ⟨1481, pr1481⟩
private theorem pr1483 : PrimeCertificate 1483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv1483 : PrimeValue := ⟨1483, pr1483⟩
private theorem pr1487 : PrimeCertificate 1487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv743]) (by decide +kernel)
def pv1487 : PrimeValue := ⟨1487, pr1487⟩
private theorem pr1489 : PrimeCertificate 1489 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv1489 : PrimeValue := ⟨1489, pr1489⟩
private theorem pr1493 : PrimeCertificate 1493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv373]) (by decide +kernel)
def pv1493 : PrimeValue := ⟨1493, pr1493⟩
private theorem pr1499 : PrimeCertificate 1499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv107]) (by decide +kernel)
def pv1499 : PrimeValue := ⟨1499, pr1499⟩
private theorem pr1511 : PrimeCertificate 1511 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv151]) (by decide +kernel)
def pv1511 : PrimeValue := ⟨1511, pr1511⟩
private theorem pr1523 : PrimeCertificate 1523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv761]) (by decide +kernel)
def pv1523 : PrimeValue := ⟨1523, pr1523⟩
private theorem pr1531 : PrimeCertificate 1531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv1531 : PrimeValue := ⟨1531, pr1531⟩
private theorem pr1543 : PrimeCertificate 1543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv257]) (by decide +kernel)
def pv1543 : PrimeValue := ⟨1543, pr1543⟩
private theorem pr1549 : PrimeCertificate 1549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv1549 : PrimeValue := ⟨1549, pr1549⟩
private theorem pr1553 : PrimeCertificate 1553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97]) (by decide +kernel)
def pv1553 : PrimeValue := ⟨1553, pr1553⟩
private theorem pr1559 : PrimeCertificate 1559 :=
  certifyPrime (q := pv19) (ls := [pv2,pv19,pv41]) (by decide +kernel)
def pv1559 : PrimeValue := ⟨1559, pr1559⟩
private theorem pr1567 : PrimeCertificate 1567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv1567 : PrimeValue := ⟨1567, pr1567⟩
private theorem pr1571 : PrimeCertificate 1571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv157]) (by decide +kernel)
def pv1571 : PrimeValue := ⟨1571, pr1571⟩
private theorem pr1579 : PrimeCertificate 1579 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv263]) (by decide +kernel)
def pv1579 : PrimeValue := ⟨1579, pr1579⟩
private theorem pr1583 : PrimeCertificate 1583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv113]) (by decide +kernel)
def pv1583 : PrimeValue := ⟨1583, pr1583⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
