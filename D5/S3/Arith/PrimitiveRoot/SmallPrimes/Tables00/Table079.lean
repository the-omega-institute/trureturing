/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table079
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table079.pv264283
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table047
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table048

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr264283 : PrimeCertificate 264283 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv2591]) (by decide +kernel)
def pv264283 : PrimeValue := ⟨264283, pr264283⟩
private theorem pr264289 : PrimeCertificate 264289 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv2753]) (by decide +kernel)
def pv264289 : PrimeValue := ⟨264289, pr264289⟩
private theorem pr264349 : PrimeCertificate 264349 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv1049]) (by decide +kernel)
def pv264349 : PrimeValue := ⟨264349, pr264349⟩
private theorem pr264353 : PrimeCertificate 264353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv751]) (by decide +kernel)
def pv264353 : PrimeValue := ⟨264353, pr264353⟩
private theorem pr264359 : PrimeCertificate 264359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv131,pv1009]) (by decide +kernel)
def pv264359 : PrimeValue := ⟨264359, pr264359⟩
private theorem pr264371 : PrimeCertificate 264371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv26437]) (by decide +kernel)
def pv264371 : PrimeValue := ⟨264371, pr264371⟩
private theorem pr264403 : PrimeCertificate 264403 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv397]) (by decide +kernel)
def pv264403 : PrimeValue := ⟨264403, pr264403⟩
private theorem pr264437 : PrimeCertificate 264437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv66109]) (by decide +kernel)
def pv264437 : PrimeValue := ⟨264437, pr264437⟩
private theorem pr264463 : PrimeCertificate 264463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv4007]) (by decide +kernel)
def pv264463 : PrimeValue := ⟨264463, pr264463⟩
private theorem pr264529 : PrimeCertificate 264529 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv167]) (by decide +kernel)
def pv264529 : PrimeValue := ⟨264529, pr264529⟩
private theorem pr264581 : PrimeCertificate 264581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13229]) (by decide +kernel)
def pv264581 : PrimeValue := ⟨264581, pr264581⟩
private theorem pr264601 : PrimeCertificate 264601 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv264601 : PrimeValue := ⟨264601, pr264601⟩
private theorem pr264631 : PrimeCertificate 264631 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv8821]) (by decide +kernel)
def pv264631 : PrimeValue := ⟨264631, pr264631⟩
private theorem pr264637 : PrimeCertificate 264637 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7351]) (by decide +kernel)
def pv264637 : PrimeValue := ⟨264637, pr264637⟩
private theorem pr264659 : PrimeCertificate 264659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv132329]) (by decide +kernel)
def pv264659 : PrimeValue := ⟨264659, pr264659⟩
private theorem pr264697 : PrimeCertificate 264697 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv41,pv269]) (by decide +kernel)
def pv264697 : PrimeValue := ⟨264697, pr264697⟩
private theorem pr264731 : PrimeCertificate 264731 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv23,pv1151]) (by decide +kernel)
def pv264731 : PrimeValue := ⟨264731, pr264731⟩
private theorem pr264739 : PrimeCertificate 264739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv44123]) (by decide +kernel)
def pv264739 : PrimeValue := ⟨264739, pr264739⟩
private theorem pr264749 : PrimeCertificate 264749 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv547]) (by decide +kernel)
def pv264749 : PrimeValue := ⟨264749, pr264749⟩
private theorem pr264757 : PrimeCertificate 264757 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv22063]) (by decide +kernel)
def pv264757 : PrimeValue := ⟨264757, pr264757⟩
private theorem pr264769 : PrimeCertificate 264769 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv7,pv197]) (by decide +kernel)
def pv264769 : PrimeValue := ⟨264769, pr264769⟩
private theorem pr264791 : PrimeCertificate 264791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv26479]) (by decide +kernel)
def pv264791 : PrimeValue := ⟨264791, pr264791⟩
private theorem pr264793 : PrimeCertificate 264793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv17,pv59]) (by decide +kernel)
def pv264793 : PrimeValue := ⟨264793, pr264793⟩
private theorem pr264827 : PrimeCertificate 264827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv7789]) (by decide +kernel)
def pv264827 : PrimeValue := ⟨264827, pr264827⟩
private theorem pr264829 : PrimeCertificate 264829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv761]) (by decide +kernel)
def pv264829 : PrimeValue := ⟨264829, pr264829⟩
private theorem pr264889 : PrimeCertificate 264889 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv283]) (by decide +kernel)
def pv264889 : PrimeValue := ⟨264889, pr264889⟩
private theorem pr264893 : PrimeCertificate 264893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1409]) (by decide +kernel)
def pv264893 : PrimeValue := ⟨264893, pr264893⟩
private theorem pr264899 : PrimeCertificate 264899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv6971]) (by decide +kernel)
def pv264899 : PrimeValue := ⟨264899, pr264899⟩
private theorem pr264931 : PrimeCertificate 264931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv8831]) (by decide +kernel)
def pv264931 : PrimeValue := ⟨264931, pr264931⟩
private theorem pr264949 : PrimeCertificate 264949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22079]) (by decide +kernel)
def pv264949 : PrimeValue := ⟨264949, pr264949⟩
private theorem pr264959 : PrimeCertificate 264959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv137,pv967]) (by decide +kernel)
def pv264959 : PrimeValue := ⟨264959, pr264959⟩
private theorem pr264961 : PrimeCertificate 264961 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv264961 : PrimeValue := ⟨264961, pr264961⟩
private theorem pr265003 : PrimeCertificate 265003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv1523]) (by decide +kernel)
def pv265003 : PrimeValue := ⟨265003, pr265003⟩
private theorem pr265007 : PrimeCertificate 265007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv23,pv823]) (by decide +kernel)
def pv265007 : PrimeValue := ⟨265007, pr265007⟩
private theorem pr265021 : PrimeCertificate 265021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv631]) (by decide +kernel)
def pv265021 : PrimeValue := ⟨265021, pr265021⟩
private theorem pr265037 : PrimeCertificate 265037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv383]) (by decide +kernel)
def pv265037 : PrimeValue := ⟨265037, pr265037⟩
private theorem pr265091 : PrimeCertificate 265091 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv541]) (by decide +kernel)
def pv265091 : PrimeValue := ⟨265091, pr265091⟩
private theorem pr265093 : PrimeCertificate 265093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22091]) (by decide +kernel)
def pv265093 : PrimeValue := ⟨265093, pr265093⟩
private theorem pr265117 : PrimeCertificate 265117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22093]) (by decide +kernel)
def pv265117 : PrimeValue := ⟨265117, pr265117⟩
private theorem pr265123 : PrimeCertificate 265123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv103]) (by decide +kernel)
def pv265123 : PrimeValue := ⟨265123, pr265123⟩
private theorem pr265129 : PrimeCertificate 265129 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11047]) (by decide +kernel)
def pv265129 : PrimeValue := ⟨265129, pr265129⟩
private theorem pr265151 : PrimeCertificate 265151 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv5303]) (by decide +kernel)
def pv265151 : PrimeValue := ⟨265151, pr265151⟩
private theorem pr265169 : PrimeCertificate 265169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16573]) (by decide +kernel)
def pv265169 : PrimeValue := ⟨265169, pr265169⟩
private theorem pr265193 : PrimeCertificate 265193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv33149]) (by decide +kernel)
def pv265193 : PrimeValue := ⟨265193, pr265193⟩
private theorem pr265247 : PrimeCertificate 265247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv132623]) (by decide +kernel)
def pv265247 : PrimeValue := ⟨265247, pr265247⟩
private theorem pr265261 : PrimeCertificate 265261 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv4421]) (by decide +kernel)
def pv265261 : PrimeValue := ⟨265261, pr265261⟩
private theorem pr265273 : PrimeCertificate 265273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1579]) (by decide +kernel)
def pv265273 : PrimeValue := ⟨265273, pr265273⟩
private theorem pr265277 : PrimeCertificate 265277 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv6029]) (by decide +kernel)
def pv265277 : PrimeValue := ⟨265277, pr265277⟩
private theorem pr265313 : PrimeCertificate 265313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8291]) (by decide +kernel)
def pv265313 : PrimeValue := ⟨265313, pr265313⟩
private theorem pr265337 : PrimeCertificate 265337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1951]) (by decide +kernel)
def pv265337 : PrimeValue := ⟨265337, pr265337⟩
private theorem pr265381 : PrimeCertificate 265381 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv4423]) (by decide +kernel)
def pv265381 : PrimeValue := ⟨265381, pr265381⟩
private theorem pr265399 : PrimeCertificate 265399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv71,pv89]) (by decide +kernel)
def pv265399 : PrimeValue := ⟨265399, pr265399⟩
private theorem pr265403 : PrimeCertificate 265403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv132701]) (by decide +kernel)
def pv265403 : PrimeValue := ⟨265403, pr265403⟩
private theorem pr265471 : PrimeCertificate 265471 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv8849]) (by decide +kernel)
def pv265471 : PrimeValue := ⟨265471, pr265471⟩
private theorem pr265483 : PrimeCertificate 265483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv265483 : PrimeValue := ⟨265483, pr265483⟩
private theorem pr265511 : PrimeCertificate 265511 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv3793]) (by decide +kernel)
def pv265511 : PrimeValue := ⟨265511, pr265511⟩
private theorem pr265541 : PrimeCertificate 265541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv17,pv71]) (by decide +kernel)
def pv265541 : PrimeValue := ⟨265541, pr265541⟩
private theorem pr265543 : PrimeCertificate 265543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv44257]) (by decide +kernel)
def pv265543 : PrimeValue := ⟨265543, pr265543⟩
private theorem pr265547 : PrimeCertificate 265547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv4283]) (by decide +kernel)
def pv265547 : PrimeValue := ⟨265547, pr265547⟩
private theorem pr265571 : PrimeCertificate 265571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv26557]) (by decide +kernel)
def pv265571 : PrimeValue := ⟨265571, pr265571⟩
private theorem pr265607 : PrimeCertificate 265607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv12073]) (by decide +kernel)
def pv265607 : PrimeValue := ⟨265607, pr265607⟩
private theorem pr265619 : PrimeCertificate 265619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv2251]) (by decide +kernel)
def pv265619 : PrimeValue := ⟨265619, pr265619⟩
private theorem pr265621 : PrimeCertificate 265621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv233]) (by decide +kernel)
def pv265621 : PrimeValue := ⟨265621, pr265621⟩
private theorem pr265709 : PrimeCertificate 265709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181,pv367]) (by decide +kernel)
def pv265709 : PrimeValue := ⟨265709, pr265709⟩
private theorem pr265711 : PrimeCertificate 265711 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv521]) (by decide +kernel)
def pv265711 : PrimeValue := ⟨265711, pr265711⟩
private theorem pr265717 : PrimeCertificate 265717 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv61]) (by decide +kernel)
def pv265717 : PrimeValue := ⟨265717, pr265717⟩
private theorem pr265747 : PrimeCertificate 265747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv3407]) (by decide +kernel)
def pv265747 : PrimeValue := ⟨265747, pr265747⟩
private theorem pr265781 : PrimeCertificate 265781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv97,pv137]) (by decide +kernel)
def pv265781 : PrimeValue := ⟨265781, pr265781⟩
private theorem pr265787 : PrimeCertificate 265787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv132893]) (by decide +kernel)
def pv265787 : PrimeValue := ⟨265787, pr265787⟩
private theorem pr265831 : PrimeCertificate 265831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv8861]) (by decide +kernel)
def pv265831 : PrimeValue := ⟨265831, pr265831⟩
private theorem pr265841 : PrimeCertificate 265841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3323]) (by decide +kernel)
def pv265841 : PrimeValue := ⟨265841, pr265841⟩
private theorem pr265861 : PrimeCertificate 265861 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv211]) (by decide +kernel)
def pv265861 : PrimeValue := ⟨265861, pr265861⟩
private theorem pr265873 : PrimeCertificate 265873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv191]) (by decide +kernel)
def pv265873 : PrimeValue := ⟨265873, pr265873⟩
private theorem pr265883 : PrimeCertificate 265883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv3593]) (by decide +kernel)
def pv265883 : PrimeValue := ⟨265883, pr265883⟩
private theorem pr265921 : PrimeCertificate 265921 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv277]) (by decide +kernel)
def pv265921 : PrimeValue := ⟨265921, pr265921⟩
private theorem pr265957 : PrimeCertificate 265957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv599]) (by decide +kernel)
def pv265957 : PrimeValue := ⟨265957, pr265957⟩
private theorem pr265961 : PrimeCertificate 265961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv61,pv109]) (by decide +kernel)
def pv265961 : PrimeValue := ⟨265961, pr265961⟩
private theorem pr266003 : PrimeCertificate 266003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv107,pv113]) (by decide +kernel)
def pv266003 : PrimeValue := ⟨266003, pr266003⟩
private theorem pr266023 : PrimeCertificate 266023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv14779]) (by decide +kernel)
def pv266023 : PrimeValue := ⟨266023, pr266023⟩
private theorem pr266027 : PrimeCertificate 266027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv133013]) (by decide +kernel)
def pv266027 : PrimeValue := ⟨266027, pr266027⟩
private theorem pr266029 : PrimeCertificate 266029 :=
  certifyPrime (q := pv61) (ls := [pv2,pv3,pv7,pv3167]) (by decide +kernel)
def pv266029 : PrimeValue := ⟨266029, pr266029⟩
private theorem pr266051 : PrimeCertificate 266051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv313]) (by decide +kernel)
def pv266051 : PrimeValue := ⟨266051, pr266051⟩
private theorem pr266053 : PrimeCertificate 266053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22171]) (by decide +kernel)
def pv266053 : PrimeValue := ⟨266053, pr266053⟩
private theorem pr266059 : PrimeCertificate 266059 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv13,pv379]) (by decide +kernel)
def pv266059 : PrimeValue := ⟨266059, pr266059⟩
private theorem pr266081 : PrimeCertificate 266081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1663]) (by decide +kernel)
def pv266081 : PrimeValue := ⟨266081, pr266081⟩
private theorem pr266083 : PrimeCertificate 266083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv727]) (by decide +kernel)
def pv266083 : PrimeValue := ⟨266083, pr266083⟩
private theorem pr266093 : PrimeCertificate 266093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv66523]) (by decide +kernel)
def pv266093 : PrimeValue := ⟨266093, pr266093⟩
private theorem pr266099 : PrimeCertificate 266099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv83,pv229]) (by decide +kernel)
def pv266099 : PrimeValue := ⟨266099, pr266099⟩
private theorem pr266111 : PrimeCertificate 266111 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv23,pv89]) (by decide +kernel)
def pv266111 : PrimeValue := ⟨266111, pr266111⟩
private theorem pr266129 : PrimeCertificate 266129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16633]) (by decide +kernel)
def pv266129 : PrimeValue := ⟨266129, pr266129⟩
private theorem pr266137 : PrimeCertificate 266137 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv13,pv853]) (by decide +kernel)
def pv266137 : PrimeValue := ⟨266137, pr266137⟩
private theorem pr266153 : PrimeCertificate 266153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv19,pv103]) (by decide +kernel)
def pv266153 : PrimeValue := ⟨266153, pr266153⟩
private theorem pr266221 : PrimeCertificate 266221 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv17,pv29]) (by decide +kernel)
def pv266221 : PrimeValue := ⟨266221, pr266221⟩
private theorem pr266239 : PrimeCertificate 266239 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv2113]) (by decide +kernel)
def pv266239 : PrimeValue := ⟨266239, pr266239⟩
private theorem pr266261 : PrimeCertificate 266261 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13313]) (by decide +kernel)
def pv266261 : PrimeValue := ⟨266261, pr266261⟩
private theorem pr266281 : PrimeCertificate 266281 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv317]) (by decide +kernel)
def pv266281 : PrimeValue := ⟨266281, pr266281⟩
private theorem pr266291 : PrimeCertificate 266291 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv31,pv859]) (by decide +kernel)
def pv266291 : PrimeValue := ⟨266291, pr266291⟩
private theorem pr266293 : PrimeCertificate 266293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv569]) (by decide +kernel)
def pv266293 : PrimeValue := ⟨266293, pr266293⟩
private theorem pr266351 : PrimeCertificate 266351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv761]) (by decide +kernel)
def pv266351 : PrimeValue := ⟨266351, pr266351⟩
private theorem pr266369 : PrimeCertificate 266369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2081]) (by decide +kernel)
def pv266369 : PrimeValue := ⟨266369, pr266369⟩
private theorem pr266381 : PrimeCertificate 266381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv701]) (by decide +kernel)
def pv266381 : PrimeValue := ⟨266381, pr266381⟩
private theorem pr266411 : PrimeCertificate 266411 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv26641]) (by decide +kernel)
def pv266411 : PrimeValue := ⟨266411, pr266411⟩
private theorem pr266417 : PrimeCertificate 266417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16651]) (by decide +kernel)
def pv266417 : PrimeValue := ⟨266417, pr266417⟩
private theorem pr266491 : PrimeCertificate 266491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv47]) (by decide +kernel)
def pv266491 : PrimeValue := ⟨266491, pr266491⟩
private theorem pr266587 : PrimeCertificate 266587 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv157,pv283]) (by decide +kernel)
def pv266587 : PrimeValue := ⟨266587, pr266587⟩
private theorem pr266633 : PrimeCertificate 266633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv33329]) (by decide +kernel)
def pv266633 : PrimeValue := ⟨266633, pr266633⟩
private theorem pr266647 : PrimeCertificate 266647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv2339]) (by decide +kernel)
def pv266647 : PrimeValue := ⟨266647, pr266647⟩
private theorem pr266663 : PrimeCertificate 266663 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv17,pv23,pv31]) (by decide +kernel)
def pv266663 : PrimeValue := ⟨266663, pr266663⟩
private theorem pr266681 : PrimeCertificate 266681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv59,pv113]) (by decide +kernel)
def pv266681 : PrimeValue := ⟨266681, pr266681⟩
private theorem pr266683 : PrimeCertificate 266683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv263]) (by decide +kernel)
def pv266683 : PrimeValue := ⟨266683, pr266683⟩
private theorem pr266689 : PrimeCertificate 266689 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv463]) (by decide +kernel)
def pv266689 : PrimeValue := ⟨266689, pr266689⟩
private theorem pr266701 : PrimeCertificate 266701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv127]) (by decide +kernel)
def pv266701 : PrimeValue := ⟨266701, pr266701⟩
private theorem pr266711 : PrimeCertificate 266711 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv149,pv179]) (by decide +kernel)
def pv266711 : PrimeValue := ⟨266711, pr266711⟩
private theorem pr266719 : PrimeCertificate 266719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv44453]) (by decide +kernel)
def pv266719 : PrimeValue := ⟨266719, pr266719⟩
private theorem pr266759 : PrimeCertificate 266759 :=
  certifyPrime (q := pv11) (ls := [pv2,pv133379]) (by decide +kernel)
def pv266759 : PrimeValue := ⟨266759, pr266759⟩
private theorem pr266767 : PrimeCertificate 266767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv173,pv257]) (by decide +kernel)
def pv266767 : PrimeValue := ⟨266767, pr266767⟩
private theorem pr266801 : PrimeCertificate 266801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv29]) (by decide +kernel)
def pv266801 : PrimeValue := ⟨266801, pr266801⟩
private theorem pr266837 : PrimeCertificate 266837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv3511]) (by decide +kernel)
def pv266837 : PrimeValue := ⟨266837, pr266837⟩
private theorem pr266867 : PrimeCertificate 266867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv47,pv167]) (by decide +kernel)
def pv266867 : PrimeValue := ⟨266867, pr266867⟩
private theorem pr266899 : PrimeCertificate 266899 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv44483]) (by decide +kernel)
def pv266899 : PrimeValue := ⟨266899, pr266899⟩
private theorem pr266921 : PrimeCertificate 266921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6673]) (by decide +kernel)
def pv266921 : PrimeValue := ⟨266921, pr266921⟩
private theorem pr266927 : PrimeCertificate 266927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv1103]) (by decide +kernel)
def pv266927 : PrimeValue := ⟨266927, pr266927⟩
private theorem pr266933 : PrimeCertificate 266933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv66733]) (by decide +kernel)
def pv266933 : PrimeValue := ⟨266933, pr266933⟩
private theorem pr266947 : PrimeCertificate 266947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv44491]) (by decide +kernel)
def pv266947 : PrimeValue := ⟨266947, pr266947⟩
private theorem pr266971 : PrimeCertificate 266971 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv809]) (by decide +kernel)
def pv266971 : PrimeValue := ⟨266971, pr266971⟩
private theorem pr266977 : PrimeCertificate 266977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv266977 : PrimeValue := ⟨266977, pr266977⟩
private theorem pr266993 : PrimeCertificate 266993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv37,pv41]) (by decide +kernel)
def pv266993 : PrimeValue := ⟨266993, pr266993⟩
private theorem pr266999 : PrimeCertificate 266999 :=
  certifyPrime (q := pv13) (ls := [pv2,pv133499]) (by decide +kernel)
def pv266999 : PrimeValue := ⟨266999, pr266999⟩
private theorem pr267017 : PrimeCertificate 267017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv33377]) (by decide +kernel)
def pv267017 : PrimeValue := ⟨267017, pr267017⟩
private theorem pr267037 : PrimeCertificate 267037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv17]) (by decide +kernel)
def pv267037 : PrimeValue := ⟨267037, pr267037⟩
private theorem pr267049 : PrimeCertificate 267049 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv3709]) (by decide +kernel)
def pv267049 : PrimeValue := ⟨267049, pr267049⟩
private theorem pr267131 : PrimeCertificate 267131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv26713]) (by decide +kernel)
def pv267131 : PrimeValue := ⟨267131, pr267131⟩
private theorem pr267133 : PrimeCertificate 267133 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv113,pv197]) (by decide +kernel)
def pv267133 : PrimeValue := ⟨267133, pr267133⟩
private theorem pr267139 : PrimeCertificate 267139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv97]) (by decide +kernel)
def pv267139 : PrimeValue := ⟨267139, pr267139⟩
private theorem pr267193 : PrimeCertificate 267193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1237]) (by decide +kernel)
def pv267193 : PrimeValue := ⟨267193, pr267193⟩
private theorem pr267203 : PrimeCertificate 267203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv43,pv239]) (by decide +kernel)
def pv267203 : PrimeValue := ⟨267203, pr267203⟩
private theorem pr267217 : PrimeCertificate 267217 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv293]) (by decide +kernel)
def pv267217 : PrimeValue := ⟨267217, pr267217⟩
private theorem pr267227 : PrimeCertificate 267227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv2521]) (by decide +kernel)
def pv267227 : PrimeValue := ⟨267227, pr267227⟩
private theorem pr267229 : PrimeCertificate 267229 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv571]) (by decide +kernel)
def pv267229 : PrimeValue := ⟨267229, pr267229⟩
private theorem pr267277 : PrimeCertificate 267277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22273]) (by decide +kernel)
def pv267277 : PrimeValue := ⟨267277, pr267277⟩
private theorem pr267301 : PrimeCertificate 267301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv267301 : PrimeValue := ⟨267301, pr267301⟩
private theorem pr267307 : PrimeCertificate 267307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv23,pv149]) (by decide +kernel)
def pv267307 : PrimeValue := ⟨267307, pr267307⟩
private theorem pr267317 : PrimeCertificate 267317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv9547]) (by decide +kernel)
def pv267317 : PrimeValue := ⟨267317, pr267317⟩
private theorem pr267353 : PrimeCertificate 267353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv1453]) (by decide +kernel)
def pv267353 : PrimeValue := ⟨267353, pr267353⟩
private theorem pr267391 : PrimeCertificate 267391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2971]) (by decide +kernel)
def pv267391 : PrimeValue := ⟨267391, pr267391⟩
private theorem pr267401 : PrimeCertificate 267401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv191]) (by decide +kernel)
def pv267401 : PrimeValue := ⟨267401, pr267401⟩
private theorem pr267403 : PrimeCertificate 267403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv1087]) (by decide +kernel)
def pv267403 : PrimeValue := ⟨267403, pr267403⟩
private theorem pr267413 : PrimeCertificate 267413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv66853]) (by decide +kernel)
def pv267413 : PrimeValue := ⟨267413, pr267413⟩
private theorem pr267419 : PrimeCertificate 267419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv133709]) (by decide +kernel)
def pv267419 : PrimeValue := ⟨267419, pr267419⟩
private theorem pr267469 : PrimeCertificate 267469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv719]) (by decide +kernel)
def pv267469 : PrimeValue := ⟨267469, pr267469⟩
private theorem pr267493 : PrimeCertificate 267493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22291]) (by decide +kernel)
def pv267493 : PrimeValue := ⟨267493, pr267493⟩
private theorem pr267497 : PrimeCertificate 267497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv1153]) (by decide +kernel)
def pv267497 : PrimeValue := ⟨267497, pr267497⟩
private theorem pr267511 : PrimeCertificate 267511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv37,pv241]) (by decide +kernel)
def pv267511 : PrimeValue := ⟨267511, pr267511⟩
private theorem pr267517 : PrimeCertificate 267517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2477]) (by decide +kernel)
def pv267517 : PrimeValue := ⟨267517, pr267517⟩
private theorem pr267521 : PrimeCertificate 267521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv19]) (by decide +kernel)
def pv267521 : PrimeValue := ⟨267521, pr267521⟩
private theorem pr267523 : PrimeCertificate 267523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv44587]) (by decide +kernel)
def pv267523 : PrimeValue := ⟨267523, pr267523⟩
private theorem pr267551 : PrimeCertificate 267551 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv5351]) (by decide +kernel)
def pv267551 : PrimeValue := ⟨267551, pr267551⟩
private theorem pr267593 : PrimeCertificate 267593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv31,pv83]) (by decide +kernel)
def pv267593 : PrimeValue := ⟨267593, pr267593⟩
private theorem pr267601 : PrimeCertificate 267601 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv223]) (by decide +kernel)
def pv267601 : PrimeValue := ⟨267601, pr267601⟩
private theorem pr267613 : PrimeCertificate 267613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv769]) (by decide +kernel)
def pv267613 : PrimeValue := ⟨267613, pr267613⟩
private theorem pr267629 : PrimeCertificate 267629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2909]) (by decide +kernel)
def pv267629 : PrimeValue := ⟨267629, pr267629⟩
private theorem pr267637 : PrimeCertificate 267637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22303]) (by decide +kernel)
def pv267637 : PrimeValue := ⟨267637, pr267637⟩
private theorem pr267643 : PrimeCertificate 267643 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv14869]) (by decide +kernel)
def pv267643 : PrimeValue := ⟨267643, pr267643⟩
private theorem pr267649 : PrimeCertificate 267649 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv41]) (by decide +kernel)
def pv267649 : PrimeValue := ⟨267649, pr267649⟩
private theorem pr267677 : PrimeCertificate 267677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv66919]) (by decide +kernel)
def pv267677 : PrimeValue := ⟨267677, pr267677⟩
private theorem pr267719 : PrimeCertificate 267719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv43,pv283]) (by decide +kernel)
def pv267719 : PrimeValue := ⟨267719, pr267719⟩
private theorem pr267737 : PrimeCertificate 267737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv683]) (by decide +kernel)
def pv267737 : PrimeValue := ⟨267737, pr267737⟩
private theorem pr267749 : PrimeCertificate 267749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv271]) (by decide +kernel)
def pv267749 : PrimeValue := ⟨267749, pr267749⟩
private theorem pr267763 : PrimeCertificate 267763 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv4057]) (by decide +kernel)
def pv267763 : PrimeValue := ⟨267763, pr267763⟩
private theorem pr267781 : PrimeCertificate 267781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4463]) (by decide +kernel)
def pv267781 : PrimeValue := ⟨267781, pr267781⟩
private theorem pr267797 : PrimeCertificate 267797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv66949]) (by decide +kernel)
def pv267797 : PrimeValue := ⟨267797, pr267797⟩
private theorem pr267803 : PrimeCertificate 267803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv293,pv457]) (by decide +kernel)
def pv267803 : PrimeValue := ⟨267803, pr267803⟩
private theorem pr267811 : PrimeCertificate 267811 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv79,pv113]) (by decide +kernel)
def pv267811 : PrimeValue := ⟨267811, pr267811⟩
private theorem pr267857 : PrimeCertificate 267857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16741]) (by decide +kernel)
def pv267857 : PrimeValue := ⟨267857, pr267857⟩
private theorem pr267863 : PrimeCertificate 267863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv19,pv53]) (by decide +kernel)
def pv267863 : PrimeValue := ⟨267863, pr267863⟩
private theorem pr267901 : PrimeCertificate 267901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv47]) (by decide +kernel)
def pv267901 : PrimeValue := ⟨267901, pr267901⟩
private theorem pr267913 : PrimeCertificate 267913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv267913 : PrimeValue := ⟨267913, pr267913⟩
private theorem pr267929 : PrimeCertificate 267929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107,pv313]) (by decide +kernel)
def pv267929 : PrimeValue := ⟨267929, pr267929⟩
private theorem pr267959 : PrimeCertificate 267959 :=
  certifyPrime (q := pv17) (ls := [pv2,pv133979]) (by decide +kernel)
def pv267959 : PrimeValue := ⟨267959, pr267959⟩
private theorem pr268003 : PrimeCertificate 268003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv709]) (by decide +kernel)
def pv268003 : PrimeValue := ⟨268003, pr268003⟩
private theorem pr268043 : PrimeCertificate 268043 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv5827]) (by decide +kernel)
def pv268043 : PrimeValue := ⟨268043, pr268043⟩
private theorem pr268049 : PrimeCertificate 268049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1523]) (by decide +kernel)
def pv268049 : PrimeValue := ⟨268049, pr268049⟩
private theorem pr268063 : PrimeCertificate 268063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv1039]) (by decide +kernel)
def pv268063 : PrimeValue := ⟨268063, pr268063⟩
private theorem pr268091 : PrimeCertificate 268091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv19,pv83]) (by decide +kernel)
def pv268091 : PrimeValue := ⟨268091, pr268091⟩
private theorem pr268123 : PrimeCertificate 268123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv44687]) (by decide +kernel)
def pv268123 : PrimeValue := ⟨268123, pr268123⟩
private theorem pr268133 : PrimeCertificate 268133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67033]) (by decide +kernel)
def pv268133 : PrimeValue := ⟨268133, pr268133⟩
private theorem pr268153 : PrimeCertificate 268153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11173]) (by decide +kernel)
def pv268153 : PrimeValue := ⟨268153, pr268153⟩
private theorem pr268199 : PrimeCertificate 268199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv19157]) (by decide +kernel)
def pv268199 : PrimeValue := ⟨268199, pr268199⟩
private theorem pr268207 : PrimeCertificate 268207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv44701]) (by decide +kernel)
def pv268207 : PrimeValue := ⟨268207, pr268207⟩
private theorem pr268211 : PrimeCertificate 268211 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv26821]) (by decide +kernel)
def pv268211 : PrimeValue := ⟨268211, pr268211⟩
private theorem pr268237 : PrimeCertificate 268237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7451]) (by decide +kernel)
def pv268237 : PrimeValue := ⟨268237, pr268237⟩
private theorem pr268253 : PrimeCertificate 268253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv199,pv337]) (by decide +kernel)
def pv268253 : PrimeValue := ⟨268253, pr268253⟩
private theorem pr268267 : PrimeCertificate 268267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv44711]) (by decide +kernel)
def pv268267 : PrimeValue := ⟨268267, pr268267⟩
private theorem pr268271 : PrimeCertificate 268271 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv139,pv193]) (by decide +kernel)
def pv268271 : PrimeValue := ⟨268271, pr268271⟩
private theorem pr268343 : PrimeCertificate 268343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv134171]) (by decide +kernel)
def pv268343 : PrimeValue := ⟨268343, pr268343⟩
private theorem pr268439 : PrimeCertificate 268439 :=
  certifyPrime (q := pv13) (ls := [pv2,pv134219]) (by decide +kernel)
def pv268439 : PrimeValue := ⟨268439, pr268439⟩
private theorem pr268459 : PrimeCertificate 268459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv443]) (by decide +kernel)
def pv268459 : PrimeValue := ⟨268459, pr268459⟩
private theorem pr268487 : PrimeCertificate 268487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv134243]) (by decide +kernel)
def pv268487 : PrimeValue := ⟨268487, pr268487⟩
private theorem pr268493 : PrimeCertificate 268493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv43,pv223]) (by decide +kernel)
def pv268493 : PrimeValue := ⟨268493, pr268493⟩
private theorem pr268519 : PrimeCertificate 268519 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv44753]) (by decide +kernel)
def pv268519 : PrimeValue := ⟨268519, pr268519⟩
private theorem pr268531 : PrimeCertificate 268531 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv8951]) (by decide +kernel)
def pv268531 : PrimeValue := ⟨268531, pr268531⟩
private theorem pr268537 : PrimeCertificate 268537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv67,pv167]) (by decide +kernel)
def pv268537 : PrimeValue := ⟨268537, pr268537⟩
private theorem pr268573 : PrimeCertificate 268573 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv22381]) (by decide +kernel)
def pv268573 : PrimeValue := ⟨268573, pr268573⟩
private theorem pr268607 : PrimeCertificate 268607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv10331]) (by decide +kernel)
def pv268607 : PrimeValue := ⟨268607, pr268607⟩
private theorem pr268613 : PrimeCertificate 268613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67153]) (by decide +kernel)
def pv268613 : PrimeValue := ⟨268613, pr268613⟩
private theorem pr268643 : PrimeCertificate 268643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv12211]) (by decide +kernel)
def pv268643 : PrimeValue := ⟨268643, pr268643⟩
private theorem pr268661 : PrimeCertificate 268661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv101]) (by decide +kernel)
def pv268661 : PrimeValue := ⟨268661, pr268661⟩
private theorem pr268693 : PrimeCertificate 268693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22391]) (by decide +kernel)
def pv268693 : PrimeValue := ⟨268693, pr268693⟩
private theorem pr268721 : PrimeCertificate 268721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3359]) (by decide +kernel)
def pv268721 : PrimeValue := ⟨268721, pr268721⟩
private theorem pr268729 : PrimeCertificate 268729 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11197]) (by decide +kernel)
def pv268729 : PrimeValue := ⟨268729, pr268729⟩
private theorem pr268733 : PrimeCertificate 268733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv127]) (by decide +kernel)
def pv268733 : PrimeValue := ⟨268733, pr268733⟩
private theorem pr268747 : PrimeCertificate 268747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv953]) (by decide +kernel)
def pv268747 : PrimeValue := ⟨268747, pr268747⟩
private theorem pr268777 : PrimeCertificate 268777 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv3733]) (by decide +kernel)
def pv268777 : PrimeValue := ⟨268777, pr268777⟩
private theorem pr268781 : PrimeCertificate 268781 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv89,pv151]) (by decide +kernel)
def pv268781 : PrimeValue := ⟨268781, pr268781⟩
private theorem pr268783 : PrimeCertificate 268783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv44797]) (by decide +kernel)
def pv268783 : PrimeValue := ⟨268783, pr268783⟩
private theorem pr268789 : PrimeCertificate 268789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1723]) (by decide +kernel)
def pv268789 : PrimeValue := ⟨268789, pr268789⟩
private theorem pr268817 : PrimeCertificate 268817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv317]) (by decide +kernel)
def pv268817 : PrimeValue := ⟨268817, pr268817⟩
private theorem pr268861 : PrimeCertificate 268861 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv4481]) (by decide +kernel)
def pv268861 : PrimeValue := ⟨268861, pr268861⟩
private theorem pr268937 : PrimeCertificate 268937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv33617]) (by decide +kernel)
def pv268937 : PrimeValue := ⟨268937, pr268937⟩
private theorem pr268969 : PrimeCertificate 268969 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv7,pv1601]) (by decide +kernel)
def pv268969 : PrimeValue := ⟨268969, pr268969⟩
private theorem pr268993 : PrimeCertificate 268993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv467]) (by decide +kernel)
def pv268993 : PrimeValue := ⟨268993, pr268993⟩
private theorem pr268997 : PrimeCertificate 268997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv739]) (by decide +kernel)
def pv268997 : PrimeValue := ⟨268997, pr268997⟩
private theorem pr268999 : PrimeCertificate 268999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107,pv419]) (by decide +kernel)
def pv268999 : PrimeValue := ⟨268999, pr268999⟩
private theorem pr269039 : PrimeCertificate 269039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv1747]) (by decide +kernel)
def pv269039 : PrimeValue := ⟨269039, pr269039⟩
private theorem pr269041 : PrimeCertificate 269041 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv19,pv59]) (by decide +kernel)
def pv269041 : PrimeValue := ⟨269041, pr269041⟩
private theorem pr269057 : PrimeCertificate 269057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1051]) (by decide +kernel)
def pv269057 : PrimeValue := ⟨269057, pr269057⟩
private theorem pr269063 : PrimeCertificate 269063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv4639]) (by decide +kernel)
def pv269063 : PrimeValue := ⟨269063, pr269063⟩
private theorem pr269069 : PrimeCertificate 269069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv491]) (by decide +kernel)
def pv269069 : PrimeValue := ⟨269069, pr269069⟩
private theorem pr269131 : PrimeCertificate 269131 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv8971]) (by decide +kernel)
def pv269131 : PrimeValue := ⟨269131, pr269131⟩
private theorem pr269141 : PrimeCertificate 269141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13457]) (by decide +kernel)
def pv269141 : PrimeValue := ⟨269141, pr269141⟩
private theorem pr269179 : PrimeCertificate 269179 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv17,pv29]) (by decide +kernel)
def pv269179 : PrimeValue := ⟨269179, pr269179⟩
private theorem pr269183 : PrimeCertificate 269183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv134591]) (by decide +kernel)
def pv269183 : PrimeValue := ⟨269183, pr269183⟩
private theorem pr269327 : PrimeCertificate 269327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv311,pv433]) (by decide +kernel)
def pv269327 : PrimeValue := ⟨269327, pr269327⟩
private theorem pr269341 : PrimeCertificate 269341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv67]) (by decide +kernel)
def pv269341 : PrimeValue := ⟨269341, pr269341⟩
private theorem pr269383 : PrimeCertificate 269383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv19,pv139]) (by decide +kernel)
def pv269383 : PrimeValue := ⟨269383, pr269383⟩
private theorem pr269389 : PrimeCertificate 269389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1069]) (by decide +kernel)
def pv269389 : PrimeValue := ⟨269389, pr269389⟩
private theorem pr269393 : PrimeCertificate 269393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv113,pv149]) (by decide +kernel)
def pv269393 : PrimeValue := ⟨269393, pr269393⟩
private theorem pr269419 : PrimeCertificate 269419 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv83,pv541]) (by decide +kernel)
def pv269419 : PrimeValue := ⟨269419, pr269419⟩
private theorem pr269429 : PrimeCertificate 269429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193,pv349]) (by decide +kernel)
def pv269429 : PrimeValue := ⟨269429, pr269429⟩
private theorem pr269461 : PrimeCertificate 269461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv499]) (by decide +kernel)
def pv269461 : PrimeValue := ⟨269461, pr269461⟩
private theorem pr269473 : PrimeCertificate 269473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv401]) (by decide +kernel)
def pv269473 : PrimeValue := ⟨269473, pr269473⟩
private theorem pr269513 : PrimeCertificate 269513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv571]) (by decide +kernel)
def pv269513 : PrimeValue := ⟨269513, pr269513⟩
private theorem pr269519 : PrimeCertificate 269519 :=
  certifyPrime (q := pv19) (ls := [pv2,pv17,pv7927]) (by decide +kernel)
def pv269519 : PrimeValue := ⟨269519, pr269519⟩
private theorem pr269527 : PrimeCertificate 269527 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv29,pv1549]) (by decide +kernel)
def pv269527 : PrimeValue := ⟨269527, pr269527⟩
private theorem pr269539 : PrimeCertificate 269539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv167,pv269]) (by decide +kernel)
def pv269539 : PrimeValue := ⟨269539, pr269539⟩
private theorem pr269561 : PrimeCertificate 269561 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv23,pv293]) (by decide +kernel)
def pv269561 : PrimeValue := ⟨269561, pr269561⟩
private theorem pr269573 : PrimeCertificate 269573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv3547]) (by decide +kernel)
def pv269573 : PrimeValue := ⟨269573, pr269573⟩
private theorem pr269579 : PrimeCertificate 269579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv134789]) (by decide +kernel)
def pv269579 : PrimeValue := ⟨269579, pr269579⟩
private theorem pr269617 : PrimeCertificate 269617 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv41,pv137]) (by decide +kernel)
def pv269617 : PrimeValue := ⟨269617, pr269617⟩
private theorem pr269623 : PrimeCertificate 269623 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4993]) (by decide +kernel)
def pv269623 : PrimeValue := ⟨269623, pr269623⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
