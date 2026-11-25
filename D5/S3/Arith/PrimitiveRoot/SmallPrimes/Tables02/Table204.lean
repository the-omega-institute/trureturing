/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table204
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table204.pv662953
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table090
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table091

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr662953 : PrimeCertificate 662953 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1201]) (by decide +kernel)
def pv662953 : PrimeValue := ⟨662953, pr662953⟩
private theorem pr663161 : PrimeCertificate 663161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv59,pv281]) (by decide +kernel)
def pv663161 : PrimeValue := ⟨663161, pr663161⟩
private theorem pr663163 : PrimeCertificate 663163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv110527]) (by decide +kernel)
def pv663163 : PrimeValue := ⟨663163, pr663163⟩
private theorem pr663203 : PrimeCertificate 663203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv223,pv1487]) (by decide +kernel)
def pv663203 : PrimeValue := ⟨663203, pr663203⟩
private theorem pr663557 : PrimeCertificate 663557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv8731]) (by decide +kernel)
def pv663557 : PrimeValue := ⟨663557, pr663557⟩
private theorem pr663907 : PrimeCertificate 663907 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv110651]) (by decide +kernel)
def pv663907 : PrimeValue := ⟨663907, pr663907⟩
private theorem pr663973 : PrimeCertificate 663973 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv55331]) (by decide +kernel)
def pv663973 : PrimeValue := ⟨663973, pr663973⟩
private theorem pr663997 : PrimeCertificate 663997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv55333]) (by decide +kernel)
def pv663997 : PrimeValue := ⟨663997, pr663997⟩
private theorem pr664067 : PrimeCertificate 664067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv25541]) (by decide +kernel)
def pv664067 : PrimeValue := ⟨664067, pr664067⟩
private theorem pr664177 : PrimeCertificate 664177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv101,pv137]) (by decide +kernel)
def pv664177 : PrimeValue := ⟨664177, pr664177⟩
private theorem pr664381 : PrimeCertificate 664381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3691]) (by decide +kernel)
def pv664381 : PrimeValue := ⟨664381, pr664381⟩
private theorem pr664621 : PrimeCertificate 664621 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv19,pv53]) (by decide +kernel)
def pv664621 : PrimeValue := ⟨664621, pr664621⟩
private theorem pr664633 : PrimeCertificate 664633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv181]) (by decide +kernel)
def pv664633 : PrimeValue := ⟨664633, pr664633⟩
private theorem pr664667 : PrimeCertificate 664667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv113,pv173]) (by decide +kernel)
def pv664667 : PrimeValue := ⟨664667, pr664667⟩
private theorem pr664691 : PrimeCertificate 664691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv5113]) (by decide +kernel)
def pv664691 : PrimeValue := ⟨664691, pr664691⟩
private theorem pr664771 : PrimeCertificate 664771 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv22159]) (by decide +kernel)
def pv664771 : PrimeValue := ⟨664771, pr664771⟩
private theorem pr664793 : PrimeCertificate 664793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv3613]) (by decide +kernel)
def pv664793 : PrimeValue := ⟨664793, pr664793⟩
private theorem pr664997 : PrimeCertificate 664997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv2003]) (by decide +kernel)
def pv664997 : PrimeValue := ⟨664997, pr664997⟩
private theorem pr665153 : PrimeCertificate 665153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv547]) (by decide +kernel)
def pv665153 : PrimeValue := ⟨665153, pr665153⟩
private theorem pr665213 : PrimeCertificate 665213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv166303]) (by decide +kernel)
def pv665213 : PrimeValue := ⟨665213, pr665213⟩
private theorem pr665233 : PrimeCertificate 665233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13859]) (by decide +kernel)
def pv665233 : PrimeValue := ⟨665233, pr665233⟩
private theorem pr665387 : PrimeCertificate 665387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv443,pv751]) (by decide +kernel)
def pv665387 : PrimeValue := ⟨665387, pr665387⟩
private theorem pr665447 : PrimeCertificate 665447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv10733]) (by decide +kernel)
def pv665447 : PrimeValue := ⟨665447, pr665447⟩
private theorem pr665503 : PrimeCertificate 665503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv110917]) (by decide +kernel)
def pv665503 : PrimeValue := ⟨665503, pr665503⟩
private theorem pr665507 : PrimeCertificate 665507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv269,pv1237]) (by decide +kernel)
def pv665507 : PrimeValue := ⟨665507, pr665507⟩
private theorem pr665557 : PrimeCertificate 665557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv1499]) (by decide +kernel)
def pv665557 : PrimeValue := ⟨665557, pr665557⟩
private theorem pr665591 : PrimeCertificate 665591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv101,pv659]) (by decide +kernel)
def pv665591 : PrimeValue := ⟨665591, pr665591⟩
private theorem pr665713 : PrimeCertificate 665713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv67]) (by decide +kernel)
def pv665713 : PrimeValue := ⟨665713, pr665713⟩
private theorem pr666013 : PrimeCertificate 666013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv55501]) (by decide +kernel)
def pv666013 : PrimeValue := ⟨666013, pr666013⟩
private theorem pr666167 : PrimeCertificate 666167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv397,pv839]) (by decide +kernel)
def pv666167 : PrimeValue := ⟨666167, pr666167⟩
private theorem pr666173 : PrimeCertificate 666173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv557]) (by decide +kernel)
def pv666173 : PrimeValue := ⟨666173, pr666173⟩
private theorem pr666353 : PrimeCertificate 666353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41647]) (by decide +kernel)
def pv666353 : PrimeValue := ⟨666353, pr666353⟩
private theorem pr666403 : PrimeCertificate 666403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv439]) (by decide +kernel)
def pv666403 : PrimeValue := ⟨666403, pr666403⟩
private theorem pr666437 : PrimeCertificate 666437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv166609]) (by decide +kernel)
def pv666437 : PrimeValue := ⟨666437, pr666437⟩
private theorem pr666511 : PrimeCertificate 666511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv1709]) (by decide +kernel)
def pv666511 : PrimeValue := ⟨666511, pr666511⟩
private theorem pr666643 : PrimeCertificate 666643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137,pv811]) (by decide +kernel)
def pv666643 : PrimeValue := ⟨666643, pr666643⟩
private theorem pr666823 : PrimeCertificate 666823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv83,pv103]) (by decide +kernel)
def pv666823 : PrimeValue := ⟨666823, pr666823⟩
private theorem pr666871 : PrimeCertificate 666871 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv22229]) (by decide +kernel)
def pv666871 : PrimeValue := ⟨666871, pr666871⟩
private theorem pr666901 : PrimeCertificate 666901 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv13,pv19]) (by decide +kernel)
def pv666901 : PrimeValue := ⟨666901, pr666901⟩
private theorem pr667021 : PrimeCertificate 667021 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11117]) (by decide +kernel)
def pv667021 : PrimeValue := ⟨667021, pr667021⟩
private theorem pr667091 : PrimeCertificate 667091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv3511]) (by decide +kernel)
def pv667091 : PrimeValue := ⟨667091, pr667091⟩
private theorem pr667141 : PrimeCertificate 667141 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11119]) (by decide +kernel)
def pv667141 : PrimeValue := ⟨667141, pr667141⟩
private theorem pr667243 : PrimeCertificate 667243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1951]) (by decide +kernel)
def pv667243 : PrimeValue := ⟨667243, pr667243⟩
private theorem pr667333 : PrimeCertificate 667333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv167]) (by decide +kernel)
def pv667333 : PrimeValue := ⟨667333, pr667333⟩
private theorem pr667363 : PrimeCertificate 667363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv111227]) (by decide +kernel)
def pv667363 : PrimeValue := ⟨667363, pr667363⟩
private theorem pr667421 : PrimeCertificate 667421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv17,pv151]) (by decide +kernel)
def pv667421 : PrimeValue := ⟨667421, pr667421⟩
private theorem pr667463 : PrimeCertificate 667463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv5471]) (by decide +kernel)
def pv667463 : PrimeValue := ⟨667463, pr667463⟩
private theorem pr667561 : PrimeCertificate 667561 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv5563]) (by decide +kernel)
def pv667561 : PrimeValue := ⟨667561, pr667561⟩
private theorem pr667657 : PrimeCertificate 667657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv281]) (by decide +kernel)
def pv667657 : PrimeValue := ⟨667657, pr667657⟩
private theorem pr667673 : PrimeCertificate 667673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83459]) (by decide +kernel)
def pv667673 : PrimeValue := ⟨667673, pr667673⟩
private theorem pr667697 : PrimeCertificate 667697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv1439]) (by decide +kernel)
def pv667697 : PrimeValue := ⟨667697, pr667697⟩
private theorem pr667727 : PrimeCertificate 667727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv41,pv479]) (by decide +kernel)
def pv667727 : PrimeValue := ⟨667727, pr667727⟩
private theorem pr667837 : PrimeCertificate 667837 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv1427]) (by decide +kernel)
def pv667837 : PrimeValue := ⟨667837, pr667837⟩
private theorem pr667921 : PrimeCertificate 667921 :=
  certifyPrime (q := pv73) (ls := [pv2,pv3,pv5,pv11,pv23]) (by decide +kernel)
def pv667921 : PrimeValue := ⟨667921, pr667921⟩
private theorem pr668153 : PrimeCertificate 668153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv1777]) (by decide +kernel)
def pv668153 : PrimeValue := ⟨668153, pr668153⟩
private theorem pr668201 : PrimeCertificate 668201 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv257]) (by decide +kernel)
def pv668201 : PrimeValue := ⟨668201, pr668201⟩
private theorem pr668203 : PrimeCertificate 668203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv6551]) (by decide +kernel)
def pv668203 : PrimeValue := ⟨668203, pr668203⟩
private theorem pr668407 : PrimeCertificate 668407 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv6553]) (by decide +kernel)
def pv668407 : PrimeValue := ⟨668407, pr668407⟩
private theorem pr668581 : PrimeCertificate 668581 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv1013]) (by decide +kernel)
def pv668581 : PrimeValue := ⟨668581, pr668581⟩
private theorem pr668617 : PrimeCertificate 668617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv2143]) (by decide +kernel)
def pv668617 : PrimeValue := ⟨668617, pr668617⟩
private theorem pr668747 : PrimeCertificate 668747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv89]) (by decide +kernel)
def pv668747 : PrimeValue := ⟨668747, pr668747⟩
private theorem pr668791 : PrimeCertificate 668791 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2477]) (by decide +kernel)
def pv668791 : PrimeValue := ⟨668791, pr668791⟩
private theorem pr668821 : PrimeCertificate 668821 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv71,pv157]) (by decide +kernel)
def pv668821 : PrimeValue := ⟨668821, pr668821⟩
private theorem pr668903 : PrimeCertificate 668903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv1979]) (by decide +kernel)
def pv668903 : PrimeValue := ⟨668903, pr668903⟩
private theorem pr669023 : PrimeCertificate 669023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv334511]) (by decide +kernel)
def pv669023 : PrimeValue := ⟨669023, pr669023⟩
private theorem pr669127 : PrimeCertificate 669127 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv111521]) (by decide +kernel)
def pv669127 : PrimeValue := ⟨669127, pr669127⟩
private theorem pr669247 : PrimeCertificate 669247 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv71,pv1571]) (by decide +kernel)
def pv669247 : PrimeValue := ⟨669247, pr669247⟩
private theorem pr669391 : PrimeCertificate 669391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv53,pv421]) (by decide +kernel)
def pv669391 : PrimeValue := ⟨669391, pr669391⟩
private theorem pr669577 : PrimeCertificate 669577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1213]) (by decide +kernel)
def pv669577 : PrimeValue := ⟨669577, pr669577⟩
private theorem pr669673 : PrimeCertificate 669673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71,pv131]) (by decide +kernel)
def pv669673 : PrimeValue := ⟨669673, pr669673⟩
private theorem pr669701 : PrimeCertificate 669701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv181]) (by decide +kernel)
def pv669701 : PrimeValue := ⟨669701, pr669701⟩
private theorem pr669707 : PrimeCertificate 669707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv3251]) (by decide +kernel)
def pv669707 : PrimeValue := ⟨669707, pr669707⟩
private theorem pr670037 : PrimeCertificate 670037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv7283]) (by decide +kernel)
def pv670037 : PrimeValue := ⟨670037, pr670037⟩
private theorem pr670051 : PrimeCertificate 670051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1489]) (by decide +kernel)
def pv670051 : PrimeValue := ⟨670051, pr670051⟩
private theorem pr670231 : PrimeCertificate 670231 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv677]) (by decide +kernel)
def pv670231 : PrimeValue := ⟨670231, pr670231⟩
private theorem pr670471 : PrimeCertificate 670471 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv5,pv22349]) (by decide +kernel)
def pv670471 : PrimeValue := ⟨670471, pr670471⟩
private theorem pr670493 : PrimeCertificate 670493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167623]) (by decide +kernel)
def pv670493 : PrimeValue := ⟨670493, pr670493⟩
private theorem pr670673 : PrimeCertificate 670673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv167,pv251]) (by decide +kernel)
def pv670673 : PrimeValue := ⟨670673, pr670673⟩
private theorem pr670781 : PrimeCertificate 670781 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv3049]) (by decide +kernel)
def pv670781 : PrimeValue := ⟨670781, pr670781⟩
private theorem pr670963 : PrimeCertificate 670963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv111827]) (by decide +kernel)
def pv670963 : PrimeValue := ⟨670963, pr670963⟩
private theorem pr671087 : PrimeCertificate 671087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv53,pv487]) (by decide +kernel)
def pv671087 : PrimeValue := ⟨671087, pr671087⟩
private theorem pr671303 : PrimeCertificate 671303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv59,pv5689]) (by decide +kernel)
def pv671303 : PrimeValue := ⟨671303, pr671303⟩
private theorem pr671477 : PrimeCertificate 671477 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv37,pv349]) (by decide +kernel)
def pv671477 : PrimeValue := ⟨671477, pr671477⟩
private theorem pr671971 : PrimeCertificate 671971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv1723]) (by decide +kernel)
def pv671971 : PrimeValue := ⟨671971, pr671971⟩
private theorem pr672103 : PrimeCertificate 672103 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv37339]) (by decide +kernel)
def pv672103 : PrimeValue := ⟨672103, pr672103⟩
private theorem pr672151 : PrimeCertificate 672151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4481]) (by decide +kernel)
def pv672151 : PrimeValue := ⟨672151, pr672151⟩
private theorem pr672181 : PrimeCertificate 672181 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv17,pv659]) (by decide +kernel)
def pv672181 : PrimeValue := ⟨672181, pr672181⟩
private theorem pr672293 : PrimeCertificate 672293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv131,pv1283]) (by decide +kernel)
def pv672293 : PrimeValue := ⟨672293, pr672293⟩
private theorem pr672317 : PrimeCertificate 672317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv9887]) (by decide +kernel)
def pv672317 : PrimeValue := ⟨672317, pr672317⟩
private theorem pr672341 : PrimeCertificate 672341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv33617]) (by decide +kernel)
def pv672341 : PrimeValue := ⟨672341, pr672341⟩
private theorem pr672443 : PrimeCertificate 672443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv336221]) (by decide +kernel)
def pv672443 : PrimeValue := ⟨672443, pr672443⟩
private theorem pr672587 : PrimeCertificate 672587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv61,pv149]) (by decide +kernel)
def pv672587 : PrimeValue := ⟨672587, pr672587⟩
private theorem pr672781 : PrimeCertificate 672781 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11213]) (by decide +kernel)
def pv672781 : PrimeValue := ⟨672781, pr672781⟩
private theorem pr672863 : PrimeCertificate 672863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv101,pv3331]) (by decide +kernel)
def pv672863 : PrimeValue := ⟨672863, pr672863⟩
private theorem pr672913 : PrimeCertificate 672913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4673]) (by decide +kernel)
def pv672913 : PrimeValue := ⟨672913, pr672913⟩
private theorem pr672977 : PrimeCertificate 672977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv42061]) (by decide +kernel)
def pv672977 : PrimeValue := ⟨672977, pr672977⟩
private theorem pr673063 : PrimeCertificate 673063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv8629]) (by decide +kernel)
def pv673063 : PrimeValue := ⟨673063, pr673063⟩
private theorem pr673111 : PrimeCertificate 673111 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv277]) (by decide +kernel)
def pv673111 : PrimeValue := ⟨673111, pr673111⟩
private theorem pr673117 : PrimeCertificate 673117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv56093]) (by decide +kernel)
def pv673117 : PrimeValue := ⟨673117, pr673117⟩
private theorem pr673273 : PrimeCertificate 673273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1039]) (by decide +kernel)
def pv673273 : PrimeValue := ⟨673273, pr673273⟩
private theorem pr673381 : PrimeCertificate 673381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv43]) (by decide +kernel)
def pv673381 : PrimeValue := ⟨673381, pr673381⟩
private theorem pr673397 : PrimeCertificate 673397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv2131]) (by decide +kernel)
def pv673397 : PrimeValue := ⟨673397, pr673397⟩
private theorem pr673403 : PrimeCertificate 673403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv3089]) (by decide +kernel)
def pv673403 : PrimeValue := ⟨673403, pr673403⟩
private theorem pr673411 : PrimeCertificate 673411 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv22447]) (by decide +kernel)
def pv673411 : PrimeValue := ⟨673411, pr673411⟩
private theorem pr673427 : PrimeCertificate 673427 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv59,pv439]) (by decide +kernel)
def pv673427 : PrimeValue := ⟨673427, pr673427⟩
private theorem pr673447 : PrimeCertificate 673447 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv112241]) (by decide +kernel)
def pv673447 : PrimeValue := ⟨673447, pr673447⟩
private theorem pr673801 : PrimeCertificate 673801 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv1123]) (by decide +kernel)
def pv673801 : PrimeValue := ⟨673801, pr673801⟩
private theorem pr673837 : PrimeCertificate 673837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv233,pv241]) (by decide +kernel)
def pv673837 : PrimeValue := ⟨673837, pr673837⟩
private theorem pr673921 : PrimeCertificate 673921 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv673921 : PrimeValue := ⟨673921, pr673921⟩
private theorem pr674083 : PrimeCertificate 674083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv73]) (by decide +kernel)
def pv674083 : PrimeValue := ⟨674083, pr674083⟩
private theorem pr674231 : PrimeCertificate 674231 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv191,pv353]) (by decide +kernel)
def pv674231 : PrimeValue := ⟨674231, pr674231⟩
private theorem pr674321 : PrimeCertificate 674321 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv8429]) (by decide +kernel)
def pv674321 : PrimeValue := ⟨674321, pr674321⟩
private theorem pr674431 : PrimeCertificate 674431 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv22481]) (by decide +kernel)
def pv674431 : PrimeValue := ⟨674431, pr674431⟩
private theorem pr674483 : PrimeCertificate 674483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv401]) (by decide +kernel)
def pv674483 : PrimeValue := ⟨674483, pr674483⟩
private theorem pr674851 : PrimeCertificate 674851 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv409]) (by decide +kernel)
def pv674851 : PrimeValue := ⟨674851, pr674851⟩
private theorem pr674867 : PrimeCertificate 674867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv23,pv863]) (by decide +kernel)
def pv674867 : PrimeValue := ⟨674867, pr674867⟩
private theorem pr674957 : PrimeCertificate 674957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv83,pv107]) (by decide +kernel)
def pv674957 : PrimeValue := ⟨674957, pr674957⟩
private theorem pr674987 : PrimeCertificate 674987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1997]) (by decide +kernel)
def pv674987 : PrimeValue := ⟨674987, pr674987⟩
private theorem pr675083 : PrimeCertificate 675083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv337541]) (by decide +kernel)
def pv675083 : PrimeValue := ⟨675083, pr675083⟩
private theorem pr675163 : PrimeCertificate 675163 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12503]) (by decide +kernel)
def pv675163 : PrimeValue := ⟨675163, pr675163⟩
private theorem pr675413 : PrimeCertificate 675413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv8887]) (by decide +kernel)
def pv675413 : PrimeValue := ⟨675413, pr675413⟩
private theorem pr675457 : PrimeCertificate 675457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1759]) (by decide +kernel)
def pv675457 : PrimeValue := ⟨675457, pr675457⟩
private theorem pr675511 : PrimeCertificate 675511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv23,pv89]) (by decide +kernel)
def pv675511 : PrimeValue := ⟨675511, pr675511⟩
private theorem pr675593 : PrimeCertificate 675593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv84449]) (by decide +kernel)
def pv675593 : PrimeValue := ⟨675593, pr675593⟩
private theorem pr675601 : PrimeCertificate 675601 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv563]) (by decide +kernel)
def pv675601 : PrimeValue := ⟨675601, pr675601⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
