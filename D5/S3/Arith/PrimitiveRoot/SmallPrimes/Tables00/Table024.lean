/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table024
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table024.pv59417
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table005
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr59417 : PrimeCertificate 59417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1061]) (by decide +kernel)
def pv59417 : PrimeValue := ⟨59417, pr59417⟩
private theorem pr59419 : PrimeCertificate 59419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3301]) (by decide +kernel)
def pv59419 : PrimeValue := ⟨59419, pr59419⟩
private theorem pr59441 : PrimeCertificate 59441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv743]) (by decide +kernel)
def pv59441 : PrimeValue := ⟨59441, pr59441⟩
private theorem pr59443 : PrimeCertificate 59443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9907]) (by decide +kernel)
def pv59443 : PrimeValue := ⟨59443, pr59443⟩
private theorem pr59447 : PrimeCertificate 59447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29723]) (by decide +kernel)
def pv59447 : PrimeValue := ⟨59447, pr59447⟩
private theorem pr59453 : PrimeCertificate 59453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv167]) (by decide +kernel)
def pv59453 : PrimeValue := ⟨59453, pr59453⟩
private theorem pr59467 : PrimeCertificate 59467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv53]) (by decide +kernel)
def pv59467 : PrimeValue := ⟨59467, pr59467⟩
private theorem pr59471 : PrimeCertificate 59471 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv313]) (by decide +kernel)
def pv59471 : PrimeValue := ⟨59471, pr59471⟩
private theorem pr59473 : PrimeCertificate 59473 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv59]) (by decide +kernel)
def pv59473 : PrimeValue := ⟨59473, pr59473⟩
private theorem pr59497 : PrimeCertificate 59497 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv37,pv67]) (by decide +kernel)
def pv59497 : PrimeValue := ⟨59497, pr59497⟩
private theorem pr59509 : PrimeCertificate 59509 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv29]) (by decide +kernel)
def pv59509 : PrimeValue := ⟨59509, pr59509⟩
private theorem pr59513 : PrimeCertificate 59513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv173]) (by decide +kernel)
def pv59513 : PrimeValue := ⟨59513, pr59513⟩
private theorem pr59539 : PrimeCertificate 59539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9923]) (by decide +kernel)
def pv59539 : PrimeValue := ⟨59539, pr59539⟩
private theorem pr59557 : PrimeCertificate 59557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv709]) (by decide +kernel)
def pv59557 : PrimeValue := ⟨59557, pr59557⟩
private theorem pr59561 : PrimeCertificate 59561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1489]) (by decide +kernel)
def pv59561 : PrimeValue := ⟨59561, pr59561⟩
private theorem pr59567 : PrimeCertificate 59567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv29,pv79]) (by decide +kernel)
def pv59567 : PrimeValue := ⟨59567, pr59567⟩
private theorem pr59581 : PrimeCertificate 59581 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv331]) (by decide +kernel)
def pv59581 : PrimeValue := ⟨59581, pr59581⟩
private theorem pr59611 : PrimeCertificate 59611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1987]) (by decide +kernel)
def pv59611 : PrimeValue := ⟨59611, pr59611⟩
private theorem pr59617 : PrimeCertificate 59617 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv59617 : PrimeValue := ⟨59617, pr59617⟩
private theorem pr59621 : PrimeCertificate 59621 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv271]) (by decide +kernel)
def pv59621 : PrimeValue := ⟨59621, pr59621⟩
private theorem pr59627 : PrimeCertificate 59627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4259]) (by decide +kernel)
def pv59627 : PrimeValue := ⟨59627, pr59627⟩
private theorem pr59629 : PrimeCertificate 59629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4969]) (by decide +kernel)
def pv59629 : PrimeValue := ⟨59629, pr59629⟩
private theorem pr59651 : PrimeCertificate 59651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1193]) (by decide +kernel)
def pv59651 : PrimeValue := ⟨59651, pr59651⟩
private theorem pr59659 : PrimeCertificate 59659 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv163]) (by decide +kernel)
def pv59659 : PrimeValue := ⟨59659, pr59659⟩
private theorem pr59663 : PrimeCertificate 59663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv1297]) (by decide +kernel)
def pv59663 : PrimeValue := ⟨59663, pr59663⟩
private theorem pr59669 : PrimeCertificate 59669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv2131]) (by decide +kernel)
def pv59669 : PrimeValue := ⟨59669, pr59669⟩
private theorem pr59671 : PrimeCertificate 59671 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv13,pv17]) (by decide +kernel)
def pv59671 : PrimeValue := ⟨59671, pr59671⟩
private theorem pr59693 : PrimeCertificate 59693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv14923]) (by decide +kernel)
def pv59693 : PrimeValue := ⟨59693, pr59693⟩
private theorem pr59699 : PrimeCertificate 59699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv1571]) (by decide +kernel)
def pv59699 : PrimeValue := ⟨59699, pr59699⟩
private theorem pr59707 : PrimeCertificate 59707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv107]) (by decide +kernel)
def pv59707 : PrimeValue := ⟨59707, pr59707⟩
private theorem pr59723 : PrimeCertificate 59723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2297]) (by decide +kernel)
def pv59723 : PrimeValue := ⟨59723, pr59723⟩
private theorem pr59729 : PrimeCertificate 59729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3733]) (by decide +kernel)
def pv59729 : PrimeValue := ⟨59729, pr59729⟩
private theorem pr59743 : PrimeCertificate 59743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3319]) (by decide +kernel)
def pv59743 : PrimeValue := ⟨59743, pr59743⟩
private theorem pr59747 : PrimeCertificate 59747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29873]) (by decide +kernel)
def pv59747 : PrimeValue := ⟨59747, pr59747⟩
private theorem pr59753 : PrimeCertificate 59753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv97]) (by decide +kernel)
def pv59753 : PrimeValue := ⟨59753, pr59753⟩
private theorem pr59771 : PrimeCertificate 59771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv139]) (by decide +kernel)
def pv59771 : PrimeValue := ⟨59771, pr59771⟩
private theorem pr59779 : PrimeCertificate 59779 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv59779 : PrimeValue := ⟨59779, pr59779⟩
private theorem pr59791 : PrimeCertificate 59791 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1993]) (by decide +kernel)
def pv59791 : PrimeValue := ⟨59791, pr59791⟩
private theorem pr59797 : PrimeCertificate 59797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv151]) (by decide +kernel)
def pv59797 : PrimeValue := ⟨59797, pr59797⟩
private theorem pr59809 : PrimeCertificate 59809 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv89]) (by decide +kernel)
def pv59809 : PrimeValue := ⟨59809, pr59809⟩
private theorem pr59833 : PrimeCertificate 59833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv277]) (by decide +kernel)
def pv59833 : PrimeValue := ⟨59833, pr59833⟩
private theorem pr59863 : PrimeCertificate 59863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv907]) (by decide +kernel)
def pv59863 : PrimeValue := ⟨59863, pr59863⟩
private theorem pr59879 : PrimeCertificate 59879 :=
  certifyPrime (q := pv17) (ls := [pv2,pv7,pv13,pv47]) (by decide +kernel)
def pv59879 : PrimeValue := ⟨59879, pr59879⟩
private theorem pr59887 : PrimeCertificate 59887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1109]) (by decide +kernel)
def pv59887 : PrimeValue := ⟨59887, pr59887⟩
private theorem pr59921 : PrimeCertificate 59921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv107]) (by decide +kernel)
def pv59921 : PrimeValue := ⟨59921, pr59921⟩
private theorem pr59929 : PrimeCertificate 59929 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv227]) (by decide +kernel)
def pv59929 : PrimeValue := ⟨59929, pr59929⟩
private theorem pr59951 : PrimeCertificate 59951 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv109]) (by decide +kernel)
def pv59951 : PrimeValue := ⟨59951, pr59951⟩
private theorem pr59957 : PrimeCertificate 59957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1153]) (by decide +kernel)
def pv59957 : PrimeValue := ⟨59957, pr59957⟩
private theorem pr59971 : PrimeCertificate 59971 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1999]) (by decide +kernel)
def pv59971 : PrimeValue := ⟨59971, pr59971⟩
private theorem pr59981 : PrimeCertificate 59981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2999]) (by decide +kernel)
def pv59981 : PrimeValue := ⟨59981, pr59981⟩
private theorem pr59999 : PrimeCertificate 59999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv131,pv229]) (by decide +kernel)
def pv59999 : PrimeValue := ⟨59999, pr59999⟩
private theorem pr60013 : PrimeCertificate 60013 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1667]) (by decide +kernel)
def pv60013 : PrimeValue := ⟨60013, pr60013⟩
private theorem pr60017 : PrimeCertificate 60017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv31]) (by decide +kernel)
def pv60017 : PrimeValue := ⟨60017, pr60017⟩
private theorem pr60029 : PrimeCertificate 60029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv349]) (by decide +kernel)
def pv60029 : PrimeValue := ⟨60029, pr60029⟩
private theorem pr60037 : PrimeCertificate 60037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5003]) (by decide +kernel)
def pv60037 : PrimeValue := ⟨60037, pr60037⟩
private theorem pr60041 : PrimeCertificate 60041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv79]) (by decide +kernel)
def pv60041 : PrimeValue := ⟨60041, pr60041⟩
private theorem pr60077 : PrimeCertificate 60077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv653]) (by decide +kernel)
def pv60077 : PrimeValue := ⟨60077, pr60077⟩
private theorem pr60083 : PrimeCertificate 60083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2731]) (by decide +kernel)
def pv60083 : PrimeValue := ⟨60083, pr60083⟩
private theorem pr60089 : PrimeCertificate 60089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv29,pv37]) (by decide +kernel)
def pv60089 : PrimeValue := ⟨60089, pr60089⟩
private theorem pr60091 : PrimeCertificate 60091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2003]) (by decide +kernel)
def pv60091 : PrimeValue := ⟨60091, pr60091⟩
private theorem pr60101 : PrimeCertificate 60101 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv601]) (by decide +kernel)
def pv60101 : PrimeValue := ⟨60101, pr60101⟩
private theorem pr60103 : PrimeCertificate 60103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv53]) (by decide +kernel)
def pv60103 : PrimeValue := ⟨60103, pr60103⟩
private theorem pr60107 : PrimeCertificate 60107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv733]) (by decide +kernel)
def pv60107 : PrimeValue := ⟨60107, pr60107⟩
private theorem pr60127 : PrimeCertificate 60127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv911]) (by decide +kernel)
def pv60127 : PrimeValue := ⟨60127, pr60127⟩
private theorem pr60133 : PrimeCertificate 60133 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5011]) (by decide +kernel)
def pv60133 : PrimeValue := ⟨60133, pr60133⟩
private theorem pr60139 : PrimeCertificate 60139 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv257]) (by decide +kernel)
def pv60139 : PrimeValue := ⟨60139, pr60139⟩
private theorem pr60149 : PrimeCertificate 60149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1367]) (by decide +kernel)
def pv60149 : PrimeValue := ⟨60149, pr60149⟩
private theorem pr60161 : PrimeCertificate 60161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47]) (by decide +kernel)
def pv60161 : PrimeValue := ⟨60161, pr60161⟩
private theorem pr60167 : PrimeCertificate 60167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv67,pv449]) (by decide +kernel)
def pv60167 : PrimeValue := ⟨60167, pr60167⟩
private theorem pr60169 : PrimeCertificate 60169 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv109]) (by decide +kernel)
def pv60169 : PrimeValue := ⟨60169, pr60169⟩
private theorem pr60209 : PrimeCertificate 60209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv71]) (by decide +kernel)
def pv60209 : PrimeValue := ⟨60209, pr60209⟩
private theorem pr60217 : PrimeCertificate 60217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv193]) (by decide +kernel)
def pv60217 : PrimeValue := ⟨60217, pr60217⟩
private theorem pr60223 : PrimeCertificate 60223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10037]) (by decide +kernel)
def pv60223 : PrimeValue := ⟨60223, pr60223⟩
private theorem pr60251 : PrimeCertificate 60251 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv241]) (by decide +kernel)
def pv60251 : PrimeValue := ⟨60251, pr60251⟩
private theorem pr60257 : PrimeCertificate 60257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv269]) (by decide +kernel)
def pv60257 : PrimeValue := ⟨60257, pr60257⟩
private theorem pr60259 : PrimeCertificate 60259 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv83]) (by decide +kernel)
def pv60259 : PrimeValue := ⟨60259, pr60259⟩
private theorem pr60271 : PrimeCertificate 60271 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv41]) (by decide +kernel)
def pv60271 : PrimeValue := ⟨60271, pr60271⟩
private theorem pr60289 : PrimeCertificate 60289 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv157]) (by decide +kernel)
def pv60289 : PrimeValue := ⟨60289, pr60289⟩
private theorem pr60293 : PrimeCertificate 60293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv15073]) (by decide +kernel)
def pv60293 : PrimeValue := ⟨60293, pr60293⟩
private theorem pr60317 : PrimeCertificate 60317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv887]) (by decide +kernel)
def pv60317 : PrimeValue := ⟨60317, pr60317⟩
private theorem pr60331 : PrimeCertificate 60331 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv2011]) (by decide +kernel)
def pv60331 : PrimeValue := ⟨60331, pr60331⟩
private theorem pr60337 : PrimeCertificate 60337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv419]) (by decide +kernel)
def pv60337 : PrimeValue := ⟨60337, pr60337⟩
private theorem pr60343 : PrimeCertificate 60343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv89,pv113]) (by decide +kernel)
def pv60343 : PrimeValue := ⟨60343, pr60343⟩
private theorem pr60353 : PrimeCertificate 60353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv41]) (by decide +kernel)
def pv60353 : PrimeValue := ⟨60353, pr60353⟩
private theorem pr60373 : PrimeCertificate 60373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv43]) (by decide +kernel)
def pv60373 : PrimeValue := ⟨60373, pr60373⟩
private theorem pr60383 : PrimeCertificate 60383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv19,pv227]) (by decide +kernel)
def pv60383 : PrimeValue := ⟨60383, pr60383⟩
private theorem pr60397 : PrimeCertificate 60397 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv719]) (by decide +kernel)
def pv60397 : PrimeValue := ⟨60397, pr60397⟩
private theorem pr60413 : PrimeCertificate 60413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1373]) (by decide +kernel)
def pv60413 : PrimeValue := ⟨60413, pr60413⟩
private theorem pr60427 : PrimeCertificate 60427 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv373]) (by decide +kernel)
def pv60427 : PrimeValue := ⟨60427, pr60427⟩
private theorem pr60443 : PrimeCertificate 60443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv643]) (by decide +kernel)
def pv60443 : PrimeValue := ⟨60443, pr60443⟩
private theorem pr60449 : PrimeCertificate 60449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1889]) (by decide +kernel)
def pv60449 : PrimeValue := ⟨60449, pr60449⟩
private theorem pr60457 : PrimeCertificate 60457 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv229]) (by decide +kernel)
def pv60457 : PrimeValue := ⟨60457, pr60457⟩
private theorem pr60493 : PrimeCertificate 60493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv60493 : PrimeValue := ⟨60493, pr60493⟩
private theorem pr60497 : PrimeCertificate 60497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv199]) (by decide +kernel)
def pv60497 : PrimeValue := ⟨60497, pr60497⟩
private theorem pr60509 : PrimeCertificate 60509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv2161]) (by decide +kernel)
def pv60509 : PrimeValue := ⟨60509, pr60509⟩
private theorem pr60521 : PrimeCertificate 60521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv89]) (by decide +kernel)
def pv60521 : PrimeValue := ⟨60521, pr60521⟩
private theorem pr60527 : PrimeCertificate 60527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv571]) (by decide +kernel)
def pv60527 : PrimeValue := ⟨60527, pr60527⟩
private theorem pr60539 : PrimeCertificate 60539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv30269]) (by decide +kernel)
def pv60539 : PrimeValue := ⟨60539, pr60539⟩
private theorem pr60589 : PrimeCertificate 60589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv60589 : PrimeValue := ⟨60589, pr60589⟩
private theorem pr60601 : PrimeCertificate 60601 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv101]) (by decide +kernel)
def pv60601 : PrimeValue := ⟨60601, pr60601⟩
private theorem pr60607 : PrimeCertificate 60607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv37]) (by decide +kernel)
def pv60607 : PrimeValue := ⟨60607, pr60607⟩
private theorem pr60611 : PrimeCertificate 60611 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv19,pv29]) (by decide +kernel)
def pv60611 : PrimeValue := ⟨60611, pr60611⟩
private theorem pr60617 : PrimeCertificate 60617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7577]) (by decide +kernel)
def pv60617 : PrimeValue := ⟨60617, pr60617⟩
private theorem pr60623 : PrimeCertificate 60623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv1783]) (by decide +kernel)
def pv60623 : PrimeValue := ⟨60623, pr60623⟩
private theorem pr60631 : PrimeCertificate 60631 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv43,pv47]) (by decide +kernel)
def pv60631 : PrimeValue := ⟨60631, pr60631⟩
private theorem pr60637 : PrimeCertificate 60637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv163]) (by decide +kernel)
def pv60637 : PrimeValue := ⟨60637, pr60637⟩
private theorem pr60647 : PrimeCertificate 60647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv30323]) (by decide +kernel)
def pv60647 : PrimeValue := ⟨60647, pr60647⟩
private theorem pr60649 : PrimeCertificate 60649 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv60649 : PrimeValue := ⟨60649, pr60649⟩
private theorem pr60659 : PrimeCertificate 60659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2333]) (by decide +kernel)
def pv60659 : PrimeValue := ⟨60659, pr60659⟩
private theorem pr60661 : PrimeCertificate 60661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv337]) (by decide +kernel)
def pv60661 : PrimeValue := ⟨60661, pr60661⟩
private theorem pr60679 : PrimeCertificate 60679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3371]) (by decide +kernel)
def pv60679 : PrimeValue := ⟨60679, pr60679⟩
private theorem pr60689 : PrimeCertificate 60689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3793]) (by decide +kernel)
def pv60689 : PrimeValue := ⟨60689, pr60689⟩
private theorem pr60703 : PrimeCertificate 60703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv151]) (by decide +kernel)
def pv60703 : PrimeValue := ⟨60703, pr60703⟩
private theorem pr60719 : PrimeCertificate 60719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv4337]) (by decide +kernel)
def pv60719 : PrimeValue := ⟨60719, pr60719⟩
private theorem pr60727 : PrimeCertificate 60727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv349]) (by decide +kernel)
def pv60727 : PrimeValue := ⟨60727, pr60727⟩
private theorem pr60733 : PrimeCertificate 60733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv241]) (by decide +kernel)
def pv60733 : PrimeValue := ⟨60733, pr60733⟩
private theorem pr60737 : PrimeCertificate 60737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv73]) (by decide +kernel)
def pv60737 : PrimeValue := ⟨60737, pr60737⟩
private theorem pr60757 : PrimeCertificate 60757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv83]) (by decide +kernel)
def pv60757 : PrimeValue := ⟨60757, pr60757⟩
private theorem pr60761 : PrimeCertificate 60761 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv31]) (by decide +kernel)
def pv60761 : PrimeValue := ⟨60761, pr60761⟩
private theorem pr60763 : PrimeCertificate 60763 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv19,pv41]) (by decide +kernel)
def pv60763 : PrimeValue := ⟨60763, pr60763⟩
private theorem pr60773 : PrimeCertificate 60773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv15193]) (by decide +kernel)
def pv60773 : PrimeValue := ⟨60773, pr60773⟩
private theorem pr60779 : PrimeCertificate 60779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv30389]) (by decide +kernel)
def pv60779 : PrimeValue := ⟨60779, pr60779⟩
private theorem pr60793 : PrimeCertificate 60793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv149]) (by decide +kernel)
def pv60793 : PrimeValue := ⟨60793, pr60793⟩
private theorem pr60811 : PrimeCertificate 60811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2027]) (by decide +kernel)
def pv60811 : PrimeValue := ⟨60811, pr60811⟩
private theorem pr60821 : PrimeCertificate 60821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3041]) (by decide +kernel)
def pv60821 : PrimeValue := ⟨60821, pr60821⟩
private theorem pr60859 : PrimeCertificate 60859 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv60859 : PrimeValue := ⟨60859, pr60859⟩
private theorem pr60869 : PrimeCertificate 60869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv15217]) (by decide +kernel)
def pv60869 : PrimeValue := ⟨60869, pr60869⟩
private theorem pr60887 : PrimeCertificate 60887 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv4349]) (by decide +kernel)
def pv60887 : PrimeValue := ⟨60887, pr60887⟩
private theorem pr60889 : PrimeCertificate 60889 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv43,pv59]) (by decide +kernel)
def pv60889 : PrimeValue := ⟨60889, pr60889⟩
private theorem pr60899 : PrimeCertificate 60899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv30449]) (by decide +kernel)
def pv60899 : PrimeValue := ⟨60899, pr60899⟩
private theorem pr60901 : PrimeCertificate 60901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv29]) (by decide +kernel)
def pv60901 : PrimeValue := ⟨60901, pr60901⟩
private theorem pr60913 : PrimeCertificate 60913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv60913 : PrimeValue := ⟨60913, pr60913⟩
private theorem pr60917 : PrimeCertificate 60917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv157]) (by decide +kernel)
def pv60917 : PrimeValue := ⟨60917, pr60917⟩
private theorem pr60919 : PrimeCertificate 60919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv71]) (by decide +kernel)
def pv60919 : PrimeValue := ⟨60919, pr60919⟩
private theorem pr60923 : PrimeCertificate 60923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv367]) (by decide +kernel)
def pv60923 : PrimeValue := ⟨60923, pr60923⟩
private theorem pr60937 : PrimeCertificate 60937 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv2539]) (by decide +kernel)
def pv60937 : PrimeValue := ⟨60937, pr60937⟩
private theorem pr60943 : PrimeCertificate 60943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1451]) (by decide +kernel)
def pv60943 : PrimeValue := ⟨60943, pr60943⟩
private theorem pr60953 : PrimeCertificate 60953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv401]) (by decide +kernel)
def pv60953 : PrimeValue := ⟨60953, pr60953⟩
private theorem pr60961 : PrimeCertificate 60961 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv127]) (by decide +kernel)
def pv60961 : PrimeValue := ⟨60961, pr60961⟩
private theorem pr61001 : PrimeCertificate 61001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv61]) (by decide +kernel)
def pv61001 : PrimeValue := ⟨61001, pr61001⟩
private theorem pr61007 : PrimeCertificate 61007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv47,pv59]) (by decide +kernel)
def pv61007 : PrimeValue := ⟨61007, pr61007⟩
private theorem pr61027 : PrimeCertificate 61027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1453]) (by decide +kernel)
def pv61027 : PrimeValue := ⟨61027, pr61027⟩
private theorem pr61031 : PrimeCertificate 61031 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv17,pv359]) (by decide +kernel)
def pv61031 : PrimeValue := ⟨61031, pr61031⟩
private theorem pr61043 : PrimeCertificate 61043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv1327]) (by decide +kernel)
def pv61043 : PrimeValue := ⟨61043, pr61043⟩
private theorem pr61051 : PrimeCertificate 61051 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv37]) (by decide +kernel)
def pv61051 : PrimeValue := ⟨61051, pr61051⟩
private theorem pr61057 : PrimeCertificate 61057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53]) (by decide +kernel)
def pv61057 : PrimeValue := ⟨61057, pr61057⟩
private theorem pr61091 : PrimeCertificate 61091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv149]) (by decide +kernel)
def pv61091 : PrimeValue := ⟨61091, pr61091⟩
private theorem pr61099 : PrimeCertificate 61099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv599]) (by decide +kernel)
def pv61099 : PrimeValue := ⟨61099, pr61099⟩
private theorem pr61121 : PrimeCertificate 61121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv191]) (by decide +kernel)
def pv61121 : PrimeValue := ⟨61121, pr61121⟩
private theorem pr61129 : PrimeCertificate 61129 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv283]) (by decide +kernel)
def pv61129 : PrimeValue := ⟨61129, pr61129⟩
private theorem pr61141 : PrimeCertificate 61141 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1019]) (by decide +kernel)
def pv61141 : PrimeValue := ⟨61141, pr61141⟩
private theorem pr61151 : PrimeCertificate 61151 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv1223]) (by decide +kernel)
def pv61151 : PrimeValue := ⟨61151, pr61151⟩
private theorem pr61153 : PrimeCertificate 61153 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv61153 : PrimeValue := ⟨61153, pr61153⟩
private theorem pr61169 : PrimeCertificate 61169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3823]) (by decide +kernel)
def pv61169 : PrimeValue := ⟨61169, pr61169⟩
private theorem pr61211 : PrimeCertificate 61211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6121]) (by decide +kernel)
def pv61211 : PrimeValue := ⟨61211, pr61211⟩
private theorem pr61223 : PrimeCertificate 61223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv4373]) (by decide +kernel)
def pv61223 : PrimeValue := ⟨61223, pr61223⟩
private theorem pr61231 : PrimeCertificate 61231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv157]) (by decide +kernel)
def pv61231 : PrimeValue := ⟨61231, pr61231⟩
private theorem pr61253 : PrimeCertificate 61253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv15313]) (by decide +kernel)
def pv61253 : PrimeValue := ⟨61253, pr61253⟩
private theorem pr61261 : PrimeCertificate 61261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1021]) (by decide +kernel)
def pv61261 : PrimeValue := ⟨61261, pr61261⟩
private theorem pr61283 : PrimeCertificate 61283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2357]) (by decide +kernel)
def pv61283 : PrimeValue := ⟨61283, pr61283⟩
private theorem pr61291 : PrimeCertificate 61291 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv227]) (by decide +kernel)
def pv61291 : PrimeValue := ⟨61291, pr61291⟩
private theorem pr61297 : PrimeCertificate 61297 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1277]) (by decide +kernel)
def pv61297 : PrimeValue := ⟨61297, pr61297⟩
private theorem pr61331 : PrimeCertificate 61331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6133]) (by decide +kernel)
def pv61331 : PrimeValue := ⟨61331, pr61331⟩
private theorem pr61333 : PrimeCertificate 61333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv269]) (by decide +kernel)
def pv61333 : PrimeValue := ⟨61333, pr61333⟩
private theorem pr61339 : PrimeCertificate 61339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10223]) (by decide +kernel)
def pv61339 : PrimeValue := ⟨61339, pr61339⟩
private theorem pr61343 : PrimeCertificate 61343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv30671]) (by decide +kernel)
def pv61343 : PrimeValue := ⟨61343, pr61343⟩
private theorem pr61357 : PrimeCertificate 61357 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5113]) (by decide +kernel)
def pv61357 : PrimeValue := ⟨61357, pr61357⟩
private theorem pr61363 : PrimeCertificate 61363 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv487]) (by decide +kernel)
def pv61363 : PrimeValue := ⟨61363, pr61363⟩
private theorem pr61379 : PrimeCertificate 61379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv30689]) (by decide +kernel)
def pv61379 : PrimeValue := ⟨61379, pr61379⟩
private theorem pr61381 : PrimeCertificate 61381 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv31]) (by decide +kernel)
def pv61381 : PrimeValue := ⟨61381, pr61381⟩
private theorem pr61409 : PrimeCertificate 61409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv101]) (by decide +kernel)
def pv61409 : PrimeValue := ⟨61409, pr61409⟩
private theorem pr61417 : PrimeCertificate 61417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv853]) (by decide +kernel)
def pv61417 : PrimeValue := ⟨61417, pr61417⟩
private theorem pr61441 : PrimeCertificate 61441 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv61441 : PrimeValue := ⟨61441, pr61441⟩
private theorem pr61463 : PrimeCertificate 61463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv79,pv389]) (by decide +kernel)
def pv61463 : PrimeValue := ⟨61463, pr61463⟩
private theorem pr61469 : PrimeCertificate 61469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv127]) (by decide +kernel)
def pv61469 : PrimeValue := ⟨61469, pr61469⟩
private theorem pr61471 : PrimeCertificate 61471 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv683]) (by decide +kernel)
def pv61471 : PrimeValue := ⟨61471, pr61471⟩
private theorem pr61483 : PrimeCertificate 61483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10247]) (by decide +kernel)
def pv61483 : PrimeValue := ⟨61483, pr61483⟩
private theorem pr61487 : PrimeCertificate 61487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv71,pv433]) (by decide +kernel)
def pv61487 : PrimeValue := ⟨61487, pr61487⟩
private theorem pr61493 : PrimeCertificate 61493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv15373]) (by decide +kernel)
def pv61493 : PrimeValue := ⟨61493, pr61493⟩
private theorem pr61507 : PrimeCertificate 61507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv67]) (by decide +kernel)
def pv61507 : PrimeValue := ⟨61507, pr61507⟩
private theorem pr61511 : PrimeCertificate 61511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv6151]) (by decide +kernel)
def pv61511 : PrimeValue := ⟨61511, pr61511⟩
private theorem pr61519 : PrimeCertificate 61519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10253]) (by decide +kernel)
def pv61519 : PrimeValue := ⟨61519, pr61519⟩
private theorem pr61543 : PrimeCertificate 61543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv263]) (by decide +kernel)
def pv61543 : PrimeValue := ⟨61543, pr61543⟩
private theorem pr61547 : PrimeCertificate 61547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv30773]) (by decide +kernel)
def pv61547 : PrimeValue := ⟨61547, pr61547⟩
private theorem pr61553 : PrimeCertificate 61553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3847]) (by decide +kernel)
def pv61553 : PrimeValue := ⟨61553, pr61553⟩
private theorem pr61559 : PrimeCertificate 61559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv4397]) (by decide +kernel)
def pv61559 : PrimeValue := ⟨61559, pr61559⟩
private theorem pr61561 : PrimeCertificate 61561 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv61561 : PrimeValue := ⟨61561, pr61561⟩
private theorem pr61583 : PrimeCertificate 61583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv751]) (by decide +kernel)
def pv61583 : PrimeValue := ⟨61583, pr61583⟩
private theorem pr61603 : PrimeCertificate 61603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10267]) (by decide +kernel)
def pv61603 : PrimeValue := ⟨61603, pr61603⟩
private theorem pr61609 : PrimeCertificate 61609 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv151]) (by decide +kernel)
def pv61609 : PrimeValue := ⟨61609, pr61609⟩
private theorem pr61613 : PrimeCertificate 61613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv211]) (by decide +kernel)
def pv61613 : PrimeValue := ⟨61613, pr61613⟩
private theorem pr61627 : PrimeCertificate 61627 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10271]) (by decide +kernel)
def pv61627 : PrimeValue := ⟨61627, pr61627⟩
private theorem pr61631 : PrimeCertificate 61631 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv6163]) (by decide +kernel)
def pv61631 : PrimeValue := ⟨61631, pr61631⟩
private theorem pr61637 : PrimeCertificate 61637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv811]) (by decide +kernel)
def pv61637 : PrimeValue := ⟨61637, pr61637⟩
private theorem pr61643 : PrimeCertificate 61643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv37]) (by decide +kernel)
def pv61643 : PrimeValue := ⟨61643, pr61643⟩
private theorem pr61651 : PrimeCertificate 61651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv137]) (by decide +kernel)
def pv61651 : PrimeValue := ⟨61651, pr61651⟩
private theorem pr61657 : PrimeCertificate 61657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv367]) (by decide +kernel)
def pv61657 : PrimeValue := ⟨61657, pr61657⟩
private theorem pr61667 : PrimeCertificate 61667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2803]) (by decide +kernel)
def pv61667 : PrimeValue := ⟨61667, pr61667⟩
private theorem pr61673 : PrimeCertificate 61673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv593]) (by decide +kernel)
def pv61673 : PrimeValue := ⟨61673, pr61673⟩
private theorem pr61681 : PrimeCertificate 61681 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv257]) (by decide +kernel)
def pv61681 : PrimeValue := ⟨61681, pr61681⟩
private theorem pr61687 : PrimeCertificate 61687 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv23,pv149]) (by decide +kernel)
def pv61687 : PrimeValue := ⟨61687, pr61687⟩
private theorem pr61703 : PrimeCertificate 61703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv30851]) (by decide +kernel)
def pv61703 : PrimeValue := ⟨61703, pr61703⟩
private theorem pr61717 : PrimeCertificate 61717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv139]) (by decide +kernel)
def pv61717 : PrimeValue := ⟨61717, pr61717⟩
private theorem pr61723 : PrimeCertificate 61723 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv127]) (by decide +kernel)
def pv61723 : PrimeValue := ⟨61723, pr61723⟩
private theorem pr61729 : PrimeCertificate 61729 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv643]) (by decide +kernel)
def pv61729 : PrimeValue := ⟨61729, pr61729⟩
private theorem pr61751 : PrimeCertificate 61751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv19]) (by decide +kernel)
def pv61751 : PrimeValue := ⟨61751, pr61751⟩
private theorem pr61757 : PrimeCertificate 61757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv15439]) (by decide +kernel)
def pv61757 : PrimeValue := ⟨61757, pr61757⟩
private theorem pr61781 : PrimeCertificate 61781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3089]) (by decide +kernel)
def pv61781 : PrimeValue := ⟨61781, pr61781⟩
private theorem pr61813 : PrimeCertificate 61813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv101]) (by decide +kernel)
def pv61813 : PrimeValue := ⟨61813, pr61813⟩
private theorem pr61837 : PrimeCertificate 61837 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5153]) (by decide +kernel)
def pv61837 : PrimeValue := ⟨61837, pr61837⟩
private theorem pr61843 : PrimeCertificate 61843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv937]) (by decide +kernel)
def pv61843 : PrimeValue := ⟨61843, pr61843⟩
private theorem pr61861 : PrimeCertificate 61861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1031]) (by decide +kernel)
def pv61861 : PrimeValue := ⟨61861, pr61861⟩
private theorem pr61871 : PrimeCertificate 61871 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv23,pv269]) (by decide +kernel)
def pv61871 : PrimeValue := ⟨61871, pr61871⟩
private theorem pr61879 : PrimeCertificate 61879 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10313]) (by decide +kernel)
def pv61879 : PrimeValue := ⟨61879, pr61879⟩
private theorem pr61909 : PrimeCertificate 61909 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7,pv11,pv67]) (by decide +kernel)
def pv61909 : PrimeValue := ⟨61909, pr61909⟩
private theorem pr61927 : PrimeCertificate 61927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10321]) (by decide +kernel)
def pv61927 : PrimeValue := ⟨61927, pr61927⟩
private theorem pr61933 : PrimeCertificate 61933 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv397]) (by decide +kernel)
def pv61933 : PrimeValue := ⟨61933, pr61933⟩
private theorem pr61949 : PrimeCertificate 61949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv911]) (by decide +kernel)
def pv61949 : PrimeValue := ⟨61949, pr61949⟩
private theorem pr61961 : PrimeCertificate 61961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1549]) (by decide +kernel)
def pv61961 : PrimeValue := ⟨61961, pr61961⟩
private theorem pr61967 : PrimeCertificate 61967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv30983]) (by decide +kernel)
def pv61967 : PrimeValue := ⟨61967, pr61967⟩
private theorem pr61979 : PrimeCertificate 61979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv233]) (by decide +kernel)
def pv61979 : PrimeValue := ⟨61979, pr61979⟩
private theorem pr61981 : PrimeCertificate 61981 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1033]) (by decide +kernel)
def pv61981 : PrimeValue := ⟨61981, pr61981⟩
private theorem pr61987 : PrimeCertificate 61987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10331]) (by decide +kernel)
def pv61987 : PrimeValue := ⟨61987, pr61987⟩
private theorem pr61991 : PrimeCertificate 61991 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv6199]) (by decide +kernel)
def pv61991 : PrimeValue := ⟨61991, pr61991⟩
private theorem pr62003 : PrimeCertificate 62003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1069]) (by decide +kernel)
def pv62003 : PrimeValue := ⟨62003, pr62003⟩
private theorem pr62011 : PrimeCertificate 62011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv53]) (by decide +kernel)
def pv62011 : PrimeValue := ⟨62011, pr62011⟩
private theorem pr62017 : PrimeCertificate 62017 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv17,pv19]) (by decide +kernel)
def pv62017 : PrimeValue := ⟨62017, pr62017⟩
private theorem pr62039 : PrimeCertificate 62039 :=
  certifyPrime (q := pv17) (ls := [pv2,pv31019]) (by decide +kernel)
def pv62039 : PrimeValue := ⟨62039, pr62039⟩
private theorem pr62047 : PrimeCertificate 62047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv383]) (by decide +kernel)
def pv62047 : PrimeValue := ⟨62047, pr62047⟩
private theorem pr62053 : PrimeCertificate 62053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5171]) (by decide +kernel)
def pv62053 : PrimeValue := ⟨62053, pr62053⟩
private theorem pr62057 : PrimeCertificate 62057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7757]) (by decide +kernel)
def pv62057 : PrimeValue := ⟨62057, pr62057⟩
private theorem pr62071 : PrimeCertificate 62071 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2069]) (by decide +kernel)
def pv62071 : PrimeValue := ⟨62071, pr62071⟩
private theorem pr62081 : PrimeCertificate 62081 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv97]) (by decide +kernel)
def pv62081 : PrimeValue := ⟨62081, pr62081⟩
private theorem pr62099 : PrimeCertificate 62099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv509]) (by decide +kernel)
def pv62099 : PrimeValue := ⟨62099, pr62099⟩
private theorem pr62119 : PrimeCertificate 62119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv17,pv29]) (by decide +kernel)
def pv62119 : PrimeValue := ⟨62119, pr62119⟩
private theorem pr62129 : PrimeCertificate 62129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv353]) (by decide +kernel)
def pv62129 : PrimeValue := ⟨62129, pr62129⟩
private theorem pr62131 : PrimeCertificate 62131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv109]) (by decide +kernel)
def pv62131 : PrimeValue := ⟨62131, pr62131⟩
private theorem pr62137 : PrimeCertificate 62137 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv863]) (by decide +kernel)
def pv62137 : PrimeValue := ⟨62137, pr62137⟩
private theorem pr62141 : PrimeCertificate 62141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv239]) (by decide +kernel)
def pv62141 : PrimeValue := ⟨62141, pr62141⟩
private theorem pr62143 : PrimeCertificate 62143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10357]) (by decide +kernel)
def pv62143 : PrimeValue := ⟨62143, pr62143⟩
private theorem pr62171 : PrimeCertificate 62171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6217]) (by decide +kernel)
def pv62171 : PrimeValue := ⟨62171, pr62171⟩
private theorem pr62189 : PrimeCertificate 62189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv2221]) (by decide +kernel)
def pv62189 : PrimeValue := ⟨62189, pr62189⟩
private theorem pr62191 : PrimeCertificate 62191 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv691]) (by decide +kernel)
def pv62191 : PrimeValue := ⟨62191, pr62191⟩
private theorem pr62201 : PrimeCertificate 62201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv311]) (by decide +kernel)
def pv62201 : PrimeValue := ⟨62201, pr62201⟩
private theorem pr62207 : PrimeCertificate 62207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv1637]) (by decide +kernel)
def pv62207 : PrimeValue := ⟨62207, pr62207⟩
private theorem pr62213 : PrimeCertificate 62213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv151]) (by decide +kernel)
def pv62213 : PrimeValue := ⟨62213, pr62213⟩
private theorem pr62219 : PrimeCertificate 62219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2393]) (by decide +kernel)
def pv62219 : PrimeValue := ⟨62219, pr62219⟩
private theorem pr62233 : PrimeCertificate 62233 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2593]) (by decide +kernel)
def pv62233 : PrimeValue := ⟨62233, pr62233⟩
private theorem pr62273 : PrimeCertificate 62273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv139]) (by decide +kernel)
def pv62273 : PrimeValue := ⟨62273, pr62273⟩
private theorem pr62297 : PrimeCertificate 62297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv599]) (by decide +kernel)
def pv62297 : PrimeValue := ⟨62297, pr62297⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
