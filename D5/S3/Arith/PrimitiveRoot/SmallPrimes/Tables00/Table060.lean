/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table060
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table060.pv176347
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table034

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr176347 : PrimeCertificate 176347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv101]) (by decide +kernel)
def pv176347 : PrimeValue := ⟨176347, pr176347⟩
private theorem pr176353 : PrimeCertificate 176353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv167]) (by decide +kernel)
def pv176353 : PrimeValue := ⟨176353, pr176353⟩
private theorem pr176357 : PrimeCertificate 176357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44089]) (by decide +kernel)
def pv176357 : PrimeValue := ⟨176357, pr176357⟩
private theorem pr176369 : PrimeCertificate 176369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv151]) (by decide +kernel)
def pv176369 : PrimeValue := ⟨176369, pr176369⟩
private theorem pr176383 : PrimeCertificate 176383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv239]) (by decide +kernel)
def pv176383 : PrimeValue := ⟨176383, pr176383⟩
private theorem pr176389 : PrimeCertificate 176389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14699]) (by decide +kernel)
def pv176389 : PrimeValue := ⟨176389, pr176389⟩
private theorem pr176401 : PrimeCertificate 176401 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv176401 : PrimeValue := ⟨176401, pr176401⟩
private theorem pr176413 : PrimeCertificate 176413 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61,pv241]) (by decide +kernel)
def pv176413 : PrimeValue := ⟨176413, pr176413⟩
private theorem pr176417 : PrimeCertificate 176417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv149]) (by decide +kernel)
def pv176417 : PrimeValue := ⟨176417, pr176417⟩
private theorem pr176459 : PrimeCertificate 176459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv1063]) (by decide +kernel)
def pv176459 : PrimeValue := ⟨176459, pr176459⟩
private theorem pr176461 : PrimeCertificate 176461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv173]) (by decide +kernel)
def pv176461 : PrimeValue := ⟨176461, pr176461⟩
private theorem pr176467 : PrimeCertificate 176467 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29411]) (by decide +kernel)
def pv176467 : PrimeValue := ⟨176467, pr176467⟩
private theorem pr176497 : PrimeCertificate 176497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3677]) (by decide +kernel)
def pv176497 : PrimeValue := ⟨176497, pr176497⟩
private theorem pr176503 : PrimeCertificate 176503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1279]) (by decide +kernel)
def pv176503 : PrimeValue := ⟨176503, pr176503⟩
private theorem pr176507 : PrimeCertificate 176507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv71,pv113]) (by decide +kernel)
def pv176507 : PrimeValue := ⟨176507, pr176507⟩
private theorem pr176521 : PrimeCertificate 176521 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv1471]) (by decide +kernel)
def pv176521 : PrimeValue := ⟨176521, pr176521⟩
private theorem pr176537 : PrimeCertificate 176537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22067]) (by decide +kernel)
def pv176537 : PrimeValue := ⟨176537, pr176537⟩
private theorem pr176549 : PrimeCertificate 176549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv23,pv101]) (by decide +kernel)
def pv176549 : PrimeValue := ⟨176549, pr176549⟩
private theorem pr176551 : PrimeCertificate 176551 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv107]) (by decide +kernel)
def pv176551 : PrimeValue := ⟨176551, pr176551⟩
private theorem pr176557 : PrimeCertificate 176557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14713]) (by decide +kernel)
def pv176557 : PrimeValue := ⟨176557, pr176557⟩
private theorem pr176573 : PrimeCertificate 176573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4013]) (by decide +kernel)
def pv176573 : PrimeValue := ⟨176573, pr176573⟩
private theorem pr176591 : PrimeCertificate 176591 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv17659]) (by decide +kernel)
def pv176591 : PrimeValue := ⟨176591, pr176591⟩
private theorem pr176597 : PrimeCertificate 176597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv53]) (by decide +kernel)
def pv176597 : PrimeValue := ⟨176597, pr176597⟩
private theorem pr176599 : PrimeCertificate 176599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv9811]) (by decide +kernel)
def pv176599 : PrimeValue := ⟨176599, pr176599⟩
private theorem pr176609 : PrimeCertificate 176609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5519]) (by decide +kernel)
def pv176609 : PrimeValue := ⟨176609, pr176609⟩
private theorem pr176611 : PrimeCertificate 176611 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv29]) (by decide +kernel)
def pv176611 : PrimeValue := ⟨176611, pr176611⟩
private theorem pr176629 : PrimeCertificate 176629 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv41,pv359]) (by decide +kernel)
def pv176629 : PrimeValue := ⟨176629, pr176629⟩
private theorem pr176641 : PrimeCertificate 176641 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv176641 : PrimeValue := ⟨176641, pr176641⟩
private theorem pr176677 : PrimeCertificate 176677 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv14723]) (by decide +kernel)
def pv176677 : PrimeValue := ⟨176677, pr176677⟩
private theorem pr176699 : PrimeCertificate 176699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv5197]) (by decide +kernel)
def pv176699 : PrimeValue := ⟨176699, pr176699⟩
private theorem pr176711 : PrimeCertificate 176711 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv41,pv431]) (by decide +kernel)
def pv176711 : PrimeValue := ⟨176711, pr176711⟩
private theorem pr176713 : PrimeCertificate 176713 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv37,pv199]) (by decide +kernel)
def pv176713 : PrimeValue := ⟨176713, pr176713⟩
private theorem pr176747 : PrimeCertificate 176747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv1319]) (by decide +kernel)
def pv176747 : PrimeValue := ⟨176747, pr176747⟩
private theorem pr176753 : PrimeCertificate 176753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11047]) (by decide +kernel)
def pv176753 : PrimeValue := ⟨176753, pr176753⟩
private theorem pr176779 : PrimeCertificate 176779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv61]) (by decide +kernel)
def pv176779 : PrimeValue := ⟨176779, pr176779⟩
private theorem pr176789 : PrimeCertificate 176789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193,pv229]) (by decide +kernel)
def pv176789 : PrimeValue := ⟨176789, pr176789⟩
private theorem pr176791 : PrimeCertificate 176791 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv71,pv83]) (by decide +kernel)
def pv176791 : PrimeValue := ⟨176791, pr176791⟩
private theorem pr176807 : PrimeCertificate 176807 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv73,pv173]) (by decide +kernel)
def pv176807 : PrimeValue := ⟨176807, pr176807⟩
private theorem pr176819 : PrimeCertificate 176819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211,pv419]) (by decide +kernel)
def pv176819 : PrimeValue := ⟨176819, pr176819⟩
private theorem pr176849 : PrimeCertificate 176849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1579]) (by decide +kernel)
def pv176849 : PrimeValue := ⟨176849, pr176849⟩
private theorem pr176857 : PrimeCertificate 176857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7369]) (by decide +kernel)
def pv176857 : PrimeValue := ⟨176857, pr176857⟩
private theorem pr176887 : PrimeCertificate 176887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv317]) (by decide +kernel)
def pv176887 : PrimeValue := ⟨176887, pr176887⟩
private theorem pr176903 : PrimeCertificate 176903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv17,pv43]) (by decide +kernel)
def pv176903 : PrimeValue := ⟨176903, pr176903⟩
private theorem pr176921 : PrimeCertificate 176921 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv4423]) (by decide +kernel)
def pv176921 : PrimeValue := ⟨176921, pr176921⟩
private theorem pr176933 : PrimeCertificate 176933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv71,pv89]) (by decide +kernel)
def pv176933 : PrimeValue := ⟨176933, pr176933⟩
private theorem pr176951 : PrimeCertificate 176951 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv3539]) (by decide +kernel)
def pv176951 : PrimeValue := ⟨176951, pr176951⟩
private theorem pr176977 : PrimeCertificate 176977 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1229]) (by decide +kernel)
def pv176977 : PrimeValue := ⟨176977, pr176977⟩
private theorem pr176983 : PrimeCertificate 176983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv2269]) (by decide +kernel)
def pv176983 : PrimeValue := ⟨176983, pr176983⟩
private theorem pr176989 : PrimeCertificate 176989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv176989 : PrimeValue := ⟨176989, pr176989⟩
private theorem pr177007 : PrimeCertificate 177007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29501]) (by decide +kernel)
def pv177007 : PrimeValue := ⟨177007, pr177007⟩
private theorem pr177011 : PrimeCertificate 177011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv571]) (by decide +kernel)
def pv177011 : PrimeValue := ⟨177011, pr177011⟩
private theorem pr177013 : PrimeCertificate 177013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv149]) (by decide +kernel)
def pv177013 : PrimeValue := ⟨177013, pr177013⟩
private theorem pr177019 : PrimeCertificate 177019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv163,pv181]) (by decide +kernel)
def pv177019 : PrimeValue := ⟨177019, pr177019⟩
private theorem pr177043 : PrimeCertificate 177043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1553]) (by decide +kernel)
def pv177043 : PrimeValue := ⟨177043, pr177043⟩
private theorem pr177091 : PrimeCertificate 177091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv5903]) (by decide +kernel)
def pv177091 : PrimeValue := ⟨177091, pr177091⟩
private theorem pr177101 : PrimeCertificate 177101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv23]) (by decide +kernel)
def pv177101 : PrimeValue := ⟨177101, pr177101⟩
private theorem pr177109 : PrimeCertificate 177109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14759]) (by decide +kernel)
def pv177109 : PrimeValue := ⟨177109, pr177109⟩
private theorem pr177113 : PrimeCertificate 177113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv131]) (by decide +kernel)
def pv177113 : PrimeValue := ⟨177113, pr177113⟩
private theorem pr177127 : PrimeCertificate 177127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv557]) (by decide +kernel)
def pv177127 : PrimeValue := ⟨177127, pr177127⟩
private theorem pr177167 : PrimeCertificate 177167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv8053]) (by decide +kernel)
def pv177167 : PrimeValue := ⟨177167, pr177167⟩
private theorem pr177173 : PrimeCertificate 177173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44293]) (by decide +kernel)
def pv177173 : PrimeValue := ⟨177173, pr177173⟩
private theorem pr177209 : PrimeCertificate 177209 :=
  certifyPrime (q := pv11) (ls := [pv2,pv17,pv1303]) (by decide +kernel)
def pv177209 : PrimeValue := ⟨177209, pr177209⟩
private theorem pr177211 : PrimeCertificate 177211 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv179]) (by decide +kernel)
def pv177211 : PrimeValue := ⟨177211, pr177211⟩
private theorem pr177217 : PrimeCertificate 177217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv71]) (by decide +kernel)
def pv177217 : PrimeValue := ⟨177217, pr177217⟩
private theorem pr177223 : PrimeCertificate 177223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29537]) (by decide +kernel)
def pv177223 : PrimeValue := ⟨177223, pr177223⟩
private theorem pr177239 : PrimeCertificate 177239 :=
  certifyPrime (q := pv17) (ls := [pv2,pv23,pv3853]) (by decide +kernel)
def pv177239 : PrimeValue := ⟨177239, pr177239⟩
private theorem pr177269 : PrimeCertificate 177269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv487]) (by decide +kernel)
def pv177269 : PrimeValue := ⟨177269, pr177269⟩
private theorem pr177301 : PrimeCertificate 177301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv197]) (by decide +kernel)
def pv177301 : PrimeValue := ⟨177301, pr177301⟩
private theorem pr177319 : PrimeCertificate 177319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv9851]) (by decide +kernel)
def pv177319 : PrimeValue := ⟨177319, pr177319⟩
private theorem pr177323 : PrimeCertificate 177323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv88661]) (by decide +kernel)
def pv177323 : PrimeValue := ⟨177323, pr177323⟩
private theorem pr177337 : PrimeCertificate 177337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv821]) (by decide +kernel)
def pv177337 : PrimeValue := ⟨177337, pr177337⟩
private theorem pr177379 : PrimeCertificate 177379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv37,pv47]) (by decide +kernel)
def pv177379 : PrimeValue := ⟨177379, pr177379⟩
private theorem pr177409 : PrimeCertificate 177409 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv177409 : PrimeValue := ⟨177409, pr177409⟩
private theorem pr177427 : PrimeCertificate 177427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9857]) (by decide +kernel)
def pv177427 : PrimeValue := ⟨177427, pr177427⟩
private theorem pr177431 : PrimeCertificate 177431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv1613]) (by decide +kernel)
def pv177431 : PrimeValue := ⟨177431, pr177431⟩
private theorem pr177467 : PrimeCertificate 177467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv997]) (by decide +kernel)
def pv177467 : PrimeValue := ⟨177467, pr177467⟩
private theorem pr177473 : PrimeCertificate 177473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv59]) (by decide +kernel)
def pv177473 : PrimeValue := ⟨177473, pr177473⟩
private theorem pr177481 : PrimeCertificate 177481 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv17,pv29]) (by decide +kernel)
def pv177481 : PrimeValue := ⟨177481, pr177481⟩
private theorem pr177511 : PrimeCertificate 177511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv61,pv97]) (by decide +kernel)
def pv177511 : PrimeValue := ⟨177511, pr177511⟩
private theorem pr177539 : PrimeCertificate 177539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv3061]) (by decide +kernel)
def pv177539 : PrimeValue := ⟨177539, pr177539⟩
private theorem pr177553 : PrimeCertificate 177553 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv137]) (by decide +kernel)
def pv177553 : PrimeValue := ⟨177553, pr177553⟩
private theorem pr177601 : PrimeCertificate 177601 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv177601 : PrimeValue := ⟨177601, pr177601⟩
private theorem pr177647 : PrimeCertificate 177647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv12689]) (by decide +kernel)
def pv177647 : PrimeValue := ⟨177647, pr177647⟩
private theorem pr177677 : PrimeCertificate 177677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv1033]) (by decide +kernel)
def pv177677 : PrimeValue := ⟨177677, pr177677⟩
private theorem pr177679 : PrimeCertificate 177679 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv9871]) (by decide +kernel)
def pv177679 : PrimeValue := ⟨177679, pr177679⟩
private theorem pr177739 : PrimeCertificate 177739 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2693]) (by decide +kernel)
def pv177739 : PrimeValue := ⟨177739, pr177739⟩
private theorem pr177761 : PrimeCertificate 177761 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv101]) (by decide +kernel)
def pv177761 : PrimeValue := ⟨177761, pr177761⟩
private theorem pr177787 : PrimeCertificate 177787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv83]) (by decide +kernel)
def pv177787 : PrimeValue := ⟨177787, pr177787⟩
private theorem pr177797 : PrimeCertificate 177797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44449]) (by decide +kernel)
def pv177797 : PrimeValue := ⟨177797, pr177797⟩
private theorem pr177811 : PrimeCertificate 177811 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv5927]) (by decide +kernel)
def pv177811 : PrimeValue := ⟨177811, pr177811⟩
private theorem pr177839 : PrimeCertificate 177839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv88919]) (by decide +kernel)
def pv177839 : PrimeValue := ⟨177839, pr177839⟩
private theorem pr177841 : PrimeCertificate 177841 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv19]) (by decide +kernel)
def pv177841 : PrimeValue := ⟨177841, pr177841⟩
private theorem pr177893 : PrimeCertificate 177893 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv13,pv311]) (by decide +kernel)
def pv177893 : PrimeValue := ⟨177893, pr177893⟩
private theorem pr177907 : PrimeCertificate 177907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv149,pv199]) (by decide +kernel)
def pv177907 : PrimeValue := ⟨177907, pr177907⟩
private theorem pr177913 : PrimeCertificate 177913 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv353]) (by decide +kernel)
def pv177913 : PrimeValue := ⟨177913, pr177913⟩
private theorem pr177929 : PrimeCertificate 177929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv967]) (by decide +kernel)
def pv177929 : PrimeValue := ⟨177929, pr177929⟩
private theorem pr177953 : PrimeCertificate 177953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv83]) (by decide +kernel)
def pv177953 : PrimeValue := ⟨177953, pr177953⟩
private theorem pr177967 : PrimeCertificate 177967 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv9887]) (by decide +kernel)
def pv177967 : PrimeValue := ⟨177967, pr177967⟩
private theorem pr178021 : PrimeCertificate 178021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv43]) (by decide +kernel)
def pv178021 : PrimeValue := ⟨178021, pr178021⟩
private theorem pr178037 : PrimeCertificate 178037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv947]) (by decide +kernel)
def pv178037 : PrimeValue := ⟨178037, pr178037⟩
private theorem pr178039 : PrimeCertificate 178039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv157]) (by decide +kernel)
def pv178039 : PrimeValue := ⟨178039, pr178039⟩
private theorem pr178069 : PrimeCertificate 178069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv71]) (by decide +kernel)
def pv178069 : PrimeValue := ⟨178069, pr178069⟩
private theorem pr178093 : PrimeCertificate 178093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv97]) (by decide +kernel)
def pv178093 : PrimeValue := ⟨178093, pr178093⟩
private theorem pr178103 : PrimeCertificate 178103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv89051]) (by decide +kernel)
def pv178103 : PrimeValue := ⟨178103, pr178103⟩
private theorem pr178117 : PrimeCertificate 178117 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv14843]) (by decide +kernel)
def pv178117 : PrimeValue := ⟨178117, pr178117⟩
private theorem pr178127 : PrimeCertificate 178127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv17,pv31]) (by decide +kernel)
def pv178127 : PrimeValue := ⟨178127, pr178127⟩
private theorem pr178141 : PrimeCertificate 178141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2969]) (by decide +kernel)
def pv178141 : PrimeValue := ⟨178141, pr178141⟩
private theorem pr178151 : PrimeCertificate 178151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv509]) (by decide +kernel)
def pv178151 : PrimeValue := ⟨178151, pr178151⟩
private theorem pr178169 : PrimeCertificate 178169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22271]) (by decide +kernel)
def pv178169 : PrimeValue := ⟨178169, pr178169⟩
private theorem pr178183 : PrimeCertificate 178183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv521]) (by decide +kernel)
def pv178183 : PrimeValue := ⟨178183, pr178183⟩
private theorem pr178187 : PrimeCertificate 178187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv53]) (by decide +kernel)
def pv178187 : PrimeValue := ⟨178187, pr178187⟩
private theorem pr178207 : PrimeCertificate 178207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4243]) (by decide +kernel)
def pv178207 : PrimeValue := ⟨178207, pr178207⟩
private theorem pr178223 : PrimeCertificate 178223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv8101]) (by decide +kernel)
def pv178223 : PrimeValue := ⟨178223, pr178223⟩
private theorem pr178247 : PrimeCertificate 178247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv89123]) (by decide +kernel)
def pv178247 : PrimeValue := ⟨178247, pr178247⟩
private theorem pr178249 : PrimeCertificate 178249 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv1061]) (by decide +kernel)
def pv178249 : PrimeValue := ⟨178249, pr178249⟩
private theorem pr178261 : PrimeCertificate 178261 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2971]) (by decide +kernel)
def pv178261 : PrimeValue := ⟨178261, pr178261⟩
private theorem pr178289 : PrimeCertificate 178289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1013]) (by decide +kernel)
def pv178289 : PrimeValue := ⟨178289, pr178289⟩
private theorem pr178301 : PrimeCertificate 178301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1783]) (by decide +kernel)
def pv178301 : PrimeValue := ⟨178301, pr178301⟩
private theorem pr178307 : PrimeCertificate 178307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89153]) (by decide +kernel)
def pv178307 : PrimeValue := ⟨178307, pr178307⟩
private theorem pr178327 : PrimeCertificate 178327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9907]) (by decide +kernel)
def pv178327 : PrimeValue := ⟨178327, pr178327⟩
private theorem pr178349 : PrimeCertificate 178349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44587]) (by decide +kernel)
def pv178349 : PrimeValue := ⟨178349, pr178349⟩
private theorem pr178361 : PrimeCertificate 178361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv13]) (by decide +kernel)
def pv178361 : PrimeValue := ⟨178361, pr178361⟩
private theorem pr178393 : PrimeCertificate 178393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7433]) (by decide +kernel)
def pv178393 : PrimeValue := ⟨178393, pr178393⟩
private theorem pr178417 : PrimeCertificate 178417 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv59]) (by decide +kernel)
def pv178417 : PrimeValue := ⟨178417, pr178417⟩
private theorem pr178439 : PrimeCertificate 178439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv6863]) (by decide +kernel)
def pv178439 : PrimeValue := ⟨178439, pr178439⟩
private theorem pr178441 : PrimeCertificate 178441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1487]) (by decide +kernel)
def pv178441 : PrimeValue := ⟨178441, pr178441⟩
private theorem pr178447 : PrimeCertificate 178447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29741]) (by decide +kernel)
def pv178447 : PrimeValue := ⟨178447, pr178447⟩
private theorem pr178469 : PrimeCertificate 178469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44617]) (by decide +kernel)
def pv178469 : PrimeValue := ⟨178469, pr178469⟩
private theorem pr178487 : PrimeCertificate 178487 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv19,pv61]) (by decide +kernel)
def pv178487 : PrimeValue := ⟨178487, pr178487⟩
private theorem pr178489 : PrimeCertificate 178489 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv37,pv67]) (by decide +kernel)
def pv178489 : PrimeValue := ⟨178489, pr178489⟩
private theorem pr178531 : PrimeCertificate 178531 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv541]) (by decide +kernel)
def pv178531 : PrimeValue := ⟨178531, pr178531⟩
private theorem pr178537 : PrimeCertificate 178537 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv43,pv173]) (by decide +kernel)
def pv178537 : PrimeValue := ⟨178537, pr178537⟩
private theorem pr178559 : PrimeCertificate 178559 :=
  certifyPrime (q := pv19) (ls := [pv2,pv73,pv1223]) (by decide +kernel)
def pv178559 : PrimeValue := ⟨178559, pr178559⟩
private theorem pr178561 : PrimeCertificate 178561 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv178561 : PrimeValue := ⟨178561, pr178561⟩
private theorem pr178567 : PrimeCertificate 178567 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29761]) (by decide +kernel)
def pv178567 : PrimeValue := ⟨178567, pr178567⟩
private theorem pr178571 : PrimeCertificate 178571 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv2551]) (by decide +kernel)
def pv178571 : PrimeValue := ⟨178571, pr178571⟩
private theorem pr178621 : PrimeCertificate 178621 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv13,pv229]) (by decide +kernel)
def pv178621 : PrimeValue := ⟨178621, pr178621⟩
private theorem pr178627 : PrimeCertificate 178627 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4253]) (by decide +kernel)
def pv178627 : PrimeValue := ⟨178627, pr178627⟩
private theorem pr178639 : PrimeCertificate 178639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv1567]) (by decide +kernel)
def pv178639 : PrimeValue := ⟨178639, pr178639⟩
private theorem pr178643 : PrimeCertificate 178643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179,pv499]) (by decide +kernel)
def pv178643 : PrimeValue := ⟨178643, pr178643⟩
private theorem pr178681 : PrimeCertificate 178681 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1489]) (by decide +kernel)
def pv178681 : PrimeValue := ⟨178681, pr178681⟩
private theorem pr178691 : PrimeCertificate 178691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv107,pv167]) (by decide +kernel)
def pv178691 : PrimeValue := ⟨178691, pr178691⟩
private theorem pr178693 : PrimeCertificate 178693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14891]) (by decide +kernel)
def pv178693 : PrimeValue := ⟨178693, pr178693⟩
private theorem pr178757 : PrimeCertificate 178757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv29,pv67]) (by decide +kernel)
def pv178757 : PrimeValue := ⟨178757, pr178757⟩
private theorem pr178781 : PrimeCertificate 178781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1277]) (by decide +kernel)
def pv178781 : PrimeValue := ⟨178781, pr178781⟩
private theorem pr178793 : PrimeCertificate 178793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22349]) (by decide +kernel)
def pv178793 : PrimeValue := ⟨178793, pr178793⟩
private theorem pr178807 : PrimeCertificate 178807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv1753]) (by decide +kernel)
def pv178807 : PrimeValue := ⟨178807, pr178807⟩
private theorem pr178813 : PrimeCertificate 178813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4967]) (by decide +kernel)
def pv178813 : PrimeValue := ⟨178813, pr178813⟩
private theorem pr178817 : PrimeCertificate 178817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv127]) (by decide +kernel)
def pv178817 : PrimeValue := ⟨178817, pr178817⟩
private theorem pr178819 : PrimeCertificate 178819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29803]) (by decide +kernel)
def pv178819 : PrimeValue := ⟨178819, pr178819⟩
private theorem pr178831 : PrimeCertificate 178831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1987]) (by decide +kernel)
def pv178831 : PrimeValue := ⟨178831, pr178831⟩
private theorem pr178873 : PrimeCertificate 178873 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv29,pv257]) (by decide +kernel)
def pv178873 : PrimeValue := ⟨178873, pr178873⟩
private theorem pr178877 : PrimeCertificate 178877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197,pv227]) (by decide +kernel)
def pv178877 : PrimeValue := ⟨178877, pr178877⟩
private theorem pr178889 : PrimeCertificate 178889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv379]) (by decide +kernel)
def pv178889 : PrimeValue := ⟨178889, pr178889⟩
private theorem pr178897 : PrimeCertificate 178897 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv3727]) (by decide +kernel)
def pv178897 : PrimeValue := ⟨178897, pr178897⟩
private theorem pr178903 : PrimeCertificate 178903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3313]) (by decide +kernel)
def pv178903 : PrimeValue := ⟨178903, pr178903⟩
private theorem pr178907 : PrimeCertificate 178907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv983]) (by decide +kernel)
def pv178907 : PrimeValue := ⟨178907, pr178907⟩
private theorem pr178909 : PrimeCertificate 178909 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv877]) (by decide +kernel)
def pv178909 : PrimeValue := ⟨178909, pr178909⟩
private theorem pr178921 : PrimeCertificate 178921 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv71]) (by decide +kernel)
def pv178921 : PrimeValue := ⟨178921, pr178921⟩
private theorem pr178931 : PrimeCertificate 178931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv617]) (by decide +kernel)
def pv178931 : PrimeValue := ⟨178931, pr178931⟩
private theorem pr178933 : PrimeCertificate 178933 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv31,pv37]) (by decide +kernel)
def pv178933 : PrimeValue := ⟨178933, pr178933⟩
private theorem pr178939 : PrimeCertificate 178939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9941]) (by decide +kernel)
def pv178939 : PrimeValue := ⟨178939, pr178939⟩
private theorem pr178973 : PrimeCertificate 178973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv443]) (by decide +kernel)
def pv178973 : PrimeValue := ⟨178973, pr178973⟩
private theorem pr178987 : PrimeCertificate 178987 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1297]) (by decide +kernel)
def pv178987 : PrimeValue := ⟨178987, pr178987⟩
private theorem pr179021 : PrimeCertificate 179021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8951]) (by decide +kernel)
def pv179021 : PrimeValue := ⟨179021, pr179021⟩
private theorem pr179029 : PrimeCertificate 179029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4973]) (by decide +kernel)
def pv179029 : PrimeValue := ⟨179029, pr179029⟩
private theorem pr179033 : PrimeCertificate 179033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23,pv139]) (by decide +kernel)
def pv179033 : PrimeValue := ⟨179033, pr179033⟩
private theorem pr179041 : PrimeCertificate 179041 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv373]) (by decide +kernel)
def pv179041 : PrimeValue := ⟨179041, pr179041⟩
private theorem pr179051 : PrimeCertificate 179051 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv3581]) (by decide +kernel)
def pv179051 : PrimeValue := ⟨179051, pr179051⟩
private theorem pr179057 : PrimeCertificate 179057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv31]) (by decide +kernel)
def pv179057 : PrimeValue := ⟨179057, pr179057⟩
private theorem pr179083 : PrimeCertificate 179083 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9949]) (by decide +kernel)
def pv179083 : PrimeValue := ⟨179083, pr179083⟩
private theorem pr179089 : PrimeCertificate 179089 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv13,pv41]) (by decide +kernel)
def pv179089 : PrimeValue := ⟨179089, pr179089⟩
private theorem pr179099 : PrimeCertificate 179099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv149,pv601]) (by decide +kernel)
def pv179099 : PrimeValue := ⟨179099, pr179099⟩
private theorem pr179107 : PrimeCertificate 179107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29851]) (by decide +kernel)
def pv179107 : PrimeValue := ⟨179107, pr179107⟩
private theorem pr179111 : PrimeCertificate 179111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17911]) (by decide +kernel)
def pv179111 : PrimeValue := ⟨179111, pr179111⟩
private theorem pr179119 : PrimeCertificate 179119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv107]) (by decide +kernel)
def pv179119 : PrimeValue := ⟨179119, pr179119⟩
private theorem pr179143 : PrimeCertificate 179143 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv73,pv409]) (by decide +kernel)
def pv179143 : PrimeValue := ⟨179143, pr179143⟩
private theorem pr179161 : PrimeCertificate 179161 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1493]) (by decide +kernel)
def pv179161 : PrimeValue := ⟨179161, pr179161⟩
private theorem pr179173 : PrimeCertificate 179173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv79]) (by decide +kernel)
def pv179173 : PrimeValue := ⟨179173, pr179173⟩
private theorem pr179203 : PrimeCertificate 179203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29867]) (by decide +kernel)
def pv179203 : PrimeValue := ⟨179203, pr179203⟩
private theorem pr179209 : PrimeCertificate 179209 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv19,pv131]) (by decide +kernel)
def pv179209 : PrimeValue := ⟨179209, pr179209⟩
private theorem pr179213 : PrimeCertificate 179213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4073]) (by decide +kernel)
def pv179213 : PrimeValue := ⟨179213, pr179213⟩
private theorem pr179233 : PrimeCertificate 179233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1867]) (by decide +kernel)
def pv179233 : PrimeValue := ⟨179233, pr179233⟩
private theorem pr179243 : PrimeCertificate 179243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv59]) (by decide +kernel)
def pv179243 : PrimeValue := ⟨179243, pr179243⟩
private theorem pr179261 : PrimeCertificate 179261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8963]) (by decide +kernel)
def pv179261 : PrimeValue := ⟨179261, pr179261⟩
private theorem pr179269 : PrimeCertificate 179269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14939]) (by decide +kernel)
def pv179269 : PrimeValue := ⟨179269, pr179269⟩
private theorem pr179281 : PrimeCertificate 179281 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv83]) (by decide +kernel)
def pv179281 : PrimeValue := ⟨179281, pr179281⟩
private theorem pr179287 : PrimeCertificate 179287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29881]) (by decide +kernel)
def pv179287 : PrimeValue := ⟨179287, pr179287⟩
private theorem pr179317 : PrimeCertificate 179317 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv293]) (by decide +kernel)
def pv179317 : PrimeValue := ⟨179317, pr179317⟩
private theorem pr179327 : PrimeCertificate 179327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv12809]) (by decide +kernel)
def pv179327 : PrimeValue := ⟨179327, pr179327⟩
private theorem pr179351 : PrimeCertificate 179351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv211]) (by decide +kernel)
def pv179351 : PrimeValue := ⟨179351, pr179351⟩
private theorem pr179357 : PrimeCertificate 179357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44839]) (by decide +kernel)
def pv179357 : PrimeValue := ⟨179357, pr179357⟩
private theorem pr179369 : PrimeCertificate 179369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv3203]) (by decide +kernel)
def pv179369 : PrimeValue := ⟨179369, pr179369⟩
private theorem pr179383 : PrimeCertificate 179383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4271]) (by decide +kernel)
def pv179383 : PrimeValue := ⟨179383, pr179383⟩
private theorem pr179393 : PrimeCertificate 179393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2803]) (by decide +kernel)
def pv179393 : PrimeValue := ⟨179393, pr179393⟩
private theorem pr179407 : PrimeCertificate 179407 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv9967]) (by decide +kernel)
def pv179407 : PrimeValue := ⟨179407, pr179407⟩
private theorem pr179411 : PrimeCertificate 179411 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv11,pv233]) (by decide +kernel)
def pv179411 : PrimeValue := ⟨179411, pr179411⟩
private theorem pr179429 : PrimeCertificate 179429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1447]) (by decide +kernel)
def pv179429 : PrimeValue := ⟨179429, pr179429⟩
private theorem pr179437 : PrimeCertificate 179437 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv19,pv787]) (by decide +kernel)
def pv179437 : PrimeValue := ⟨179437, pr179437⟩
private theorem pr179453 : PrimeCertificate 179453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv17,pv29]) (by decide +kernel)
def pv179453 : PrimeValue := ⟨179453, pr179453⟩
private theorem pr179461 : PrimeCertificate 179461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv997]) (by decide +kernel)
def pv179461 : PrimeValue := ⟨179461, pr179461⟩
private theorem pr179471 : PrimeCertificate 179471 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv131,pv137]) (by decide +kernel)
def pv179471 : PrimeValue := ⟨179471, pr179471⟩
private theorem pr179479 : PrimeCertificate 179479 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv59]) (by decide +kernel)
def pv179479 : PrimeValue := ⟨179479, pr179479⟩
private theorem pr179483 : PrimeCertificate 179483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv2087]) (by decide +kernel)
def pv179483 : PrimeValue := ⟨179483, pr179483⟩
private theorem pr179497 : PrimeCertificate 179497 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv277]) (by decide +kernel)
def pv179497 : PrimeValue := ⟨179497, pr179497⟩
private theorem pr179527 : PrimeCertificate 179527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29921]) (by decide +kernel)
def pv179527 : PrimeValue := ⟨179527, pr179527⟩
private theorem pr179533 : PrimeCertificate 179533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4987]) (by decide +kernel)
def pv179533 : PrimeValue := ⟨179533, pr179533⟩
private theorem pr179549 : PrimeCertificate 179549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44887]) (by decide +kernel)
def pv179549 : PrimeValue := ⟨179549, pr179549⟩
private theorem pr179573 : PrimeCertificate 179573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44893]) (by decide +kernel)
def pv179573 : PrimeValue := ⟨179573, pr179573⟩
private theorem pr179579 : PrimeCertificate 179579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv101,pv127]) (by decide +kernel)
def pv179579 : PrimeValue := ⟨179579, pr179579⟩
private theorem pr179581 : PrimeCertificate 179581 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv41,pv73]) (by decide +kernel)
def pv179581 : PrimeValue := ⟨179581, pr179581⟩
private theorem pr179593 : PrimeCertificate 179593 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv1069]) (by decide +kernel)
def pv179593 : PrimeValue := ⟨179593, pr179593⟩
private theorem pr179603 : PrimeCertificate 179603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv1009]) (by decide +kernel)
def pv179603 : PrimeValue := ⟨179603, pr179603⟩
private theorem pr179623 : PrimeCertificate 179623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv587]) (by decide +kernel)
def pv179623 : PrimeValue := ⟨179623, pr179623⟩
private theorem pr179633 : PrimeCertificate 179633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv103,pv109]) (by decide +kernel)
def pv179633 : PrimeValue := ⟨179633, pr179633⟩
private theorem pr179651 : PrimeCertificate 179651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3593]) (by decide +kernel)
def pv179651 : PrimeValue := ⟨179651, pr179651⟩
private theorem pr179657 : PrimeCertificate 179657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1321]) (by decide +kernel)
def pv179657 : PrimeValue := ⟨179657, pr179657⟩
private theorem pr179659 : PrimeCertificate 179659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1109]) (by decide +kernel)
def pv179659 : PrimeValue := ⟨179659, pr179659⟩
private theorem pr179671 : PrimeCertificate 179671 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv53,pv113]) (by decide +kernel)
def pv179671 : PrimeValue := ⟨179671, pr179671⟩
private theorem pr179689 : PrimeCertificate 179689 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7487]) (by decide +kernel)
def pv179689 : PrimeValue := ⟨179689, pr179689⟩
private theorem pr179693 : PrimeCertificate 179693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167,pv269]) (by decide +kernel)
def pv179693 : PrimeValue := ⟨179693, pr179693⟩
private theorem pr179719 : PrimeCertificate 179719 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv389]) (by decide +kernel)
def pv179719 : PrimeValue := ⟨179719, pr179719⟩
private theorem pr179737 : PrimeCertificate 179737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7489]) (by decide +kernel)
def pv179737 : PrimeValue := ⟨179737, pr179737⟩
private theorem pr179743 : PrimeCertificate 179743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv1033]) (by decide +kernel)
def pv179743 : PrimeValue := ⟨179743, pr179743⟩
private theorem pr179749 : PrimeCertificate 179749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4993]) (by decide +kernel)
def pv179749 : PrimeValue := ⟨179749, pr179749⟩
private theorem pr179801 : PrimeCertificate 179801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv31]) (by decide +kernel)
def pv179801 : PrimeValue := ⟨179801, pr179801⟩
private theorem pr179807 : PrimeCertificate 179807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv743]) (by decide +kernel)
def pv179807 : PrimeValue := ⟨179807, pr179807⟩
private theorem pr179813 : PrimeCertificate 179813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44953]) (by decide +kernel)
def pv179813 : PrimeValue := ⟨179813, pr179813⟩
private theorem pr179819 : PrimeCertificate 179819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89909]) (by decide +kernel)
def pv179819 : PrimeValue := ⟨179819, pr179819⟩
private theorem pr179821 : PrimeCertificate 179821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv179821 : PrimeValue := ⟨179821, pr179821⟩
private theorem pr179827 : PrimeCertificate 179827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv41,pv43]) (by decide +kernel)
def pv179827 : PrimeValue := ⟨179827, pr179827⟩
private theorem pr179833 : PrimeCertificate 179833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv127]) (by decide +kernel)
def pv179833 : PrimeValue := ⟨179833, pr179833⟩
private theorem pr179849 : PrimeCertificate 179849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22481]) (by decide +kernel)
def pv179849 : PrimeValue := ⟨179849, pr179849⟩
private theorem pr179897 : PrimeCertificate 179897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv113,pv199]) (by decide +kernel)
def pv179897 : PrimeValue := ⟨179897, pr179897⟩
private theorem pr179899 : PrimeCertificate 179899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29983]) (by decide +kernel)
def pv179899 : PrimeValue := ⟨179899, pr179899⟩
private theorem pr179903 : PrimeCertificate 179903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv293,pv307]) (by decide +kernel)
def pv179903 : PrimeValue := ⟨179903, pr179903⟩
private theorem pr179909 : PrimeCertificate 179909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv1097]) (by decide +kernel)
def pv179909 : PrimeValue := ⟨179909, pr179909⟩
private theorem pr179917 : PrimeCertificate 179917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv29,pv47]) (by decide +kernel)
def pv179917 : PrimeValue := ⟨179917, pr179917⟩
private theorem pr179923 : PrimeCertificate 179923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv157,pv191]) (by decide +kernel)
def pv179923 : PrimeValue := ⟨179923, pr179923⟩
private theorem pr179939 : PrimeCertificate 179939 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv8179]) (by decide +kernel)
def pv179939 : PrimeValue := ⟨179939, pr179939⟩
private theorem pr179953 : PrimeCertificate 179953 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv163]) (by decide +kernel)
def pv179953 : PrimeValue := ⟨179953, pr179953⟩
private theorem pr179981 : PrimeCertificate 179981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8999]) (by decide +kernel)
def pv179981 : PrimeValue := ⟨179981, pr179981⟩
private theorem pr179999 : PrimeCertificate 179999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv23,pv43]) (by decide +kernel)
def pv179999 : PrimeValue := ⟨179999, pr179999⟩
private theorem pr180001 : PrimeCertificate 180001 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv180001 : PrimeValue := ⟨180001, pr180001⟩
private theorem pr180007 : PrimeCertificate 180007 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv1579]) (by decide +kernel)
def pv180007 : PrimeValue := ⟨180007, pr180007⟩
private theorem pr180043 : PrimeCertificate 180043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv811]) (by decide +kernel)
def pv180043 : PrimeValue := ⟨180043, pr180043⟩
private theorem pr180073 : PrimeCertificate 180073 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv41,pv61]) (by decide +kernel)
def pv180073 : PrimeValue := ⟨180073, pr180073⟩
private theorem pr180077 : PrimeCertificate 180077 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv3463]) (by decide +kernel)
def pv180077 : PrimeValue := ⟨180077, pr180077⟩
private theorem pr180137 : PrimeCertificate 180137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv23,pv89]) (by decide +kernel)
def pv180137 : PrimeValue := ⟨180137, pr180137⟩
private theorem pr180161 : PrimeCertificate 180161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv563]) (by decide +kernel)
def pv180161 : PrimeValue := ⟨180161, pr180161⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
