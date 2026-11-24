/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table020
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table020.pv48623
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table004
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr48623 : Nat.Prime 48623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv23,pv151]) (by decide +kernel)
def pv48623 : PrimeValue := ⟨48623, pr48623⟩
private theorem pr48647 : Nat.Prime 48647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv1871]) (by decide +kernel)
def pv48647 : PrimeValue := ⟨48647, pr48647⟩
private theorem pr48649 : Nat.Prime 48649 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2027]) (by decide +kernel)
def pv48649 : PrimeValue := ⟨48649, pr48649⟩
private theorem pr48661 : Nat.Prime 48661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv811]) (by decide +kernel)
def pv48661 : PrimeValue := ⟨48661, pr48661⟩
private theorem pr48673 : Nat.Prime 48673 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv48673 : PrimeValue := ⟨48673, pr48673⟩
private theorem pr48677 : Nat.Prime 48677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv283]) (by decide +kernel)
def pv48677 : PrimeValue := ⟨48677, pr48677⟩
private theorem pr48679 : Nat.Prime 48679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv61]) (by decide +kernel)
def pv48679 : PrimeValue := ⟨48679, pr48679⟩
private theorem pr48731 : Nat.Prime 48731 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv443]) (by decide +kernel)
def pv48731 : PrimeValue := ⟨48731, pr48731⟩
private theorem pr48733 : Nat.Prime 48733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv131]) (by decide +kernel)
def pv48733 : PrimeValue := ⟨48733, pr48733⟩
private theorem pr48751 : Nat.Prime 48751 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv48751 : PrimeValue := ⟨48751, pr48751⟩
private theorem pr48757 : Nat.Prime 48757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv239]) (by decide +kernel)
def pv48757 : PrimeValue := ⟨48757, pr48757⟩
private theorem pr48761 : Nat.Prime 48761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv53]) (by decide +kernel)
def pv48761 : PrimeValue := ⟨48761, pr48761⟩
private theorem pr48767 : Nat.Prime 48767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv659]) (by decide +kernel)
def pv48767 : PrimeValue := ⟨48767, pr48767⟩
private theorem pr48779 : Nat.Prime 48779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29]) (by decide +kernel)
def pv48779 : PrimeValue := ⟨48779, pr48779⟩
private theorem pr48781 : Nat.Prime 48781 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv271]) (by decide +kernel)
def pv48781 : PrimeValue := ⟨48781, pr48781⟩
private theorem pr48787 : Nat.Prime 48787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv173]) (by decide +kernel)
def pv48787 : PrimeValue := ⟨48787, pr48787⟩
private theorem pr48799 : Nat.Prime 48799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2711]) (by decide +kernel)
def pv48799 : PrimeValue := ⟨48799, pr48799⟩
private theorem pr48809 : Nat.Prime 48809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6101]) (by decide +kernel)
def pv48809 : PrimeValue := ⟨48809, pr48809⟩
private theorem pr48817 : Nat.Prime 48817 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv113]) (by decide +kernel)
def pv48817 : PrimeValue := ⟨48817, pr48817⟩
private theorem pr48821 : Nat.Prime 48821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2441]) (by decide +kernel)
def pv48821 : PrimeValue := ⟨48821, pr48821⟩
private theorem pr48823 : Nat.Prime 48823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv79,pv103]) (by decide +kernel)
def pv48823 : PrimeValue := ⟨48823, pr48823⟩
private theorem pr48847 : Nat.Prime 48847 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1163]) (by decide +kernel)
def pv48847 : PrimeValue := ⟨48847, pr48847⟩
private theorem pr48857 : Nat.Prime 48857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv197]) (by decide +kernel)
def pv48857 : PrimeValue := ⟨48857, pr48857⟩
private theorem pr48859 : Nat.Prime 48859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv479]) (by decide +kernel)
def pv48859 : PrimeValue := ⟨48859, pr48859⟩
private theorem pr48869 : Nat.Prime 48869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv643]) (by decide +kernel)
def pv48869 : PrimeValue := ⟨48869, pr48869⟩
private theorem pr48871 : Nat.Prime 48871 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv181]) (by decide +kernel)
def pv48871 : PrimeValue := ⟨48871, pr48871⟩
private theorem pr48883 : Nat.Prime 48883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8147]) (by decide +kernel)
def pv48883 : PrimeValue := ⟨48883, pr48883⟩
private theorem pr48889 : Nat.Prime 48889 :=
  checkPrime_prime (q := pv53) (ls := [pv2,pv3,pv7,pv97]) (by decide +kernel)
def pv48889 : PrimeValue := ⟨48889, pr48889⟩
private theorem pr48907 : Nat.Prime 48907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv19]) (by decide +kernel)
def pv48907 : PrimeValue := ⟨48907, pr48907⟩
private theorem pr48947 : Nat.Prime 48947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv24473]) (by decide +kernel)
def pv48947 : PrimeValue := ⟨48947, pr48947⟩
private theorem pr48953 : Nat.Prime 48953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv211]) (by decide +kernel)
def pv48953 : PrimeValue := ⟨48953, pr48953⟩
private theorem pr48973 : Nat.Prime 48973 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv53]) (by decide +kernel)
def pv48973 : PrimeValue := ⟨48973, pr48973⟩
private theorem pr48989 : Nat.Prime 48989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv331]) (by decide +kernel)
def pv48989 : PrimeValue := ⟨48989, pr48989⟩
private theorem pr48991 : Nat.Prime 48991 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv23,pv71]) (by decide +kernel)
def pv48991 : PrimeValue := ⟨48991, pr48991⟩
private theorem pr49003 : Nat.Prime 49003 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv8167]) (by decide +kernel)
def pv49003 : PrimeValue := ⟨49003, pr49003⟩
private theorem pr49009 : Nat.Prime 49009 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv1021]) (by decide +kernel)
def pv49009 : PrimeValue := ⟨49009, pr49009⟩
private theorem pr49019 : Nat.Prime 49019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv24509]) (by decide +kernel)
def pv49019 : PrimeValue := ⟨49019, pr49019⟩
private theorem pr49031 : Nat.Prime 49031 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv4903]) (by decide +kernel)
def pv49031 : PrimeValue := ⟨49031, pr49031⟩
private theorem pr49033 : Nat.Prime 49033 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv227]) (by decide +kernel)
def pv49033 : PrimeValue := ⟨49033, pr49033⟩
private theorem pr49037 : Nat.Prime 49037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv23,pv41]) (by decide +kernel)
def pv49037 : PrimeValue := ⟨49037, pr49037⟩
private theorem pr49043 : Nat.Prime 49043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv31,pv113]) (by decide +kernel)
def pv49043 : PrimeValue := ⟨49043, pr49043⟩
private theorem pr49057 : Nat.Prime 49057 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv73]) (by decide +kernel)
def pv49057 : PrimeValue := ⟨49057, pr49057⟩
private theorem pr49069 : Nat.Prime 49069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv47]) (by decide +kernel)
def pv49069 : PrimeValue := ⟨49069, pr49069⟩
private theorem pr49081 : Nat.Prime 49081 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv409]) (by decide +kernel)
def pv49081 : PrimeValue := ⟨49081, pr49081⟩
private theorem pr49103 : Nat.Prime 49103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv24551]) (by decide +kernel)
def pv49103 : PrimeValue := ⟨49103, pr49103⟩
private theorem pr49109 : Nat.Prime 49109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12277]) (by decide +kernel)
def pv49109 : PrimeValue := ⟨49109, pr49109⟩
private theorem pr49117 : Nat.Prime 49117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4093]) (by decide +kernel)
def pv49117 : PrimeValue := ⟨49117, pr49117⟩
private theorem pr49121 : Nat.Prime 49121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv307]) (by decide +kernel)
def pv49121 : PrimeValue := ⟨49121, pr49121⟩
private theorem pr49123 : Nat.Prime 49123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2729]) (by decide +kernel)
def pv49123 : PrimeValue := ⟨49123, pr49123⟩
private theorem pr49139 : Nat.Prime 49139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv311]) (by decide +kernel)
def pv49139 : PrimeValue := ⟨49139, pr49139⟩
private theorem pr49157 : Nat.Prime 49157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12289]) (by decide +kernel)
def pv49157 : PrimeValue := ⟨49157, pr49157⟩
private theorem pr49169 : Nat.Prime 49169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv439]) (by decide +kernel)
def pv49169 : PrimeValue := ⟨49169, pr49169⟩
private theorem pr49171 : Nat.Prime 49171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv149]) (by decide +kernel)
def pv49171 : PrimeValue := ⟨49171, pr49171⟩
private theorem pr49177 : Nat.Prime 49177 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv683]) (by decide +kernel)
def pv49177 : PrimeValue := ⟨49177, pr49177⟩
private theorem pr49193 : Nat.Prime 49193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13,pv43]) (by decide +kernel)
def pv49193 : PrimeValue := ⟨49193, pr49193⟩
private theorem pr49199 : Nat.Prime 49199 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv17,pv1447]) (by decide +kernel)
def pv49199 : PrimeValue := ⟨49199, pr49199⟩
private theorem pr49201 : Nat.Prime 49201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv49201 : PrimeValue := ⟨49201, pr49201⟩
private theorem pr49207 : Nat.Prime 49207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59,pv139]) (by decide +kernel)
def pv49207 : PrimeValue := ⟨49207, pr49207⟩
private theorem pr49211 : Nat.Prime 49211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv37]) (by decide +kernel)
def pv49211 : PrimeValue := ⟨49211, pr49211⟩
private theorem pr49223 : Nat.Prime 49223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv24611]) (by decide +kernel)
def pv49223 : PrimeValue := ⟨49223, pr49223⟩
private theorem pr49253 : Nat.Prime 49253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1759]) (by decide +kernel)
def pv49253 : PrimeValue := ⟨49253, pr49253⟩
private theorem pr49261 : Nat.Prime 49261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv821]) (by decide +kernel)
def pv49261 : PrimeValue := ⟨49261, pr49261⟩
private theorem pr49277 : Nat.Prime 49277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv127]) (by decide +kernel)
def pv49277 : PrimeValue := ⟨49277, pr49277⟩
private theorem pr49279 : Nat.Prime 49279 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv191]) (by decide +kernel)
def pv49279 : PrimeValue := ⟨49279, pr49279⟩
private theorem pr49297 : Nat.Prime 49297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv79]) (by decide +kernel)
def pv49297 : PrimeValue := ⟨49297, pr49297⟩
private theorem pr49307 : Nat.Prime 49307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv277]) (by decide +kernel)
def pv49307 : PrimeValue := ⟨49307, pr49307⟩
private theorem pr49331 : Nat.Prime 49331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv4933]) (by decide +kernel)
def pv49331 : PrimeValue := ⟨49331, pr49331⟩
private theorem pr49333 : Nat.Prime 49333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4111]) (by decide +kernel)
def pv49333 : PrimeValue := ⟨49333, pr49333⟩
private theorem pr49339 : Nat.Prime 49339 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv2741]) (by decide +kernel)
def pv49339 : PrimeValue := ⟨49339, pr49339⟩
private theorem pr49363 : Nat.Prime 49363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv433]) (by decide +kernel)
def pv49363 : PrimeValue := ⟨49363, pr49363⟩
private theorem pr49367 : Nat.Prime 49367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv24683]) (by decide +kernel)
def pv49367 : PrimeValue := ⟨49367, pr49367⟩
private theorem pr49369 : Nat.Prime 49369 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv49369 : PrimeValue := ⟨49369, pr49369⟩
private theorem pr49391 : Nat.Prime 49391 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv449]) (by decide +kernel)
def pv49391 : PrimeValue := ⟨49391, pr49391⟩
private theorem pr49393 : Nat.Prime 49393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv49393 : PrimeValue := ⟨49393, pr49393⟩
private theorem pr49409 : Nat.Prime 49409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv193]) (by decide +kernel)
def pv49409 : PrimeValue := ⟨49409, pr49409⟩
private theorem pr49411 : Nat.Prime 49411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv49411 : PrimeValue := ⟨49411, pr49411⟩
private theorem pr49417 : Nat.Prime 49417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv71]) (by decide +kernel)
def pv49417 : PrimeValue := ⟨49417, pr49417⟩
private theorem pr49429 : Nat.Prime 49429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1373]) (by decide +kernel)
def pv49429 : PrimeValue := ⟨49429, pr49429⟩
private theorem pr49433 : Nat.Prime 49433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv167]) (by decide +kernel)
def pv49433 : PrimeValue := ⟨49433, pr49433⟩
private theorem pr49451 : Nat.Prime 49451 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv23,pv43]) (by decide +kernel)
def pv49451 : PrimeValue := ⟨49451, pr49451⟩
private theorem pr49459 : Nat.Prime 49459 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8243]) (by decide +kernel)
def pv49459 : PrimeValue := ⟨49459, pr49459⟩
private theorem pr49463 : Nat.Prime 49463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv3533]) (by decide +kernel)
def pv49463 : PrimeValue := ⟨49463, pr49463⟩
private theorem pr49477 : Nat.Prime 49477 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv19,pv31]) (by decide +kernel)
def pv49477 : PrimeValue := ⟨49477, pr49477⟩
private theorem pr49481 : Nat.Prime 49481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1237]) (by decide +kernel)
def pv49481 : PrimeValue := ⟨49481, pr49481⟩
private theorem pr49499 : Nat.Prime 49499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv24749]) (by decide +kernel)
def pv49499 : PrimeValue := ⟨49499, pr49499⟩
private theorem pr49523 : Nat.Prime 49523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv2251]) (by decide +kernel)
def pv49523 : PrimeValue := ⟨49523, pr49523⟩
private theorem pr49529 : Nat.Prime 49529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv151]) (by decide +kernel)
def pv49529 : PrimeValue := ⟨49529, pr49529⟩
private theorem pr49531 : Nat.Prime 49531 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv127]) (by decide +kernel)
def pv49531 : PrimeValue := ⟨49531, pr49531⟩
private theorem pr49537 : Nat.Prime 49537 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv49537 : PrimeValue := ⟨49537, pr49537⟩
private theorem pr49547 : Nat.Prime 49547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv3539]) (by decide +kernel)
def pv49547 : PrimeValue := ⟨49547, pr49547⟩
private theorem pr49549 : Nat.Prime 49549 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv4129]) (by decide +kernel)
def pv49549 : PrimeValue := ⟨49549, pr49549⟩
private theorem pr49559 : Nat.Prime 49559 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv71,pv349]) (by decide +kernel)
def pv49559 : PrimeValue := ⟨49559, pr49559⟩
private theorem pr49597 : Nat.Prime 49597 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4133]) (by decide +kernel)
def pv49597 : PrimeValue := ⟨49597, pr49597⟩
private theorem pr49603 : Nat.Prime 49603 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1181]) (by decide +kernel)
def pv49603 : PrimeValue := ⟨49603, pr49603⟩
private theorem pr49613 : Nat.Prime 49613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv157]) (by decide +kernel)
def pv49613 : PrimeValue := ⟨49613, pr49613⟩
private theorem pr49627 : Nat.Prime 49627 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv919]) (by decide +kernel)
def pv49627 : PrimeValue := ⟨49627, pr49627⟩
private theorem pr49633 : Nat.Prime 49633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv47]) (by decide +kernel)
def pv49633 : PrimeValue := ⟨49633, pr49633⟩
private theorem pr49639 : Nat.Prime 49639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8273]) (by decide +kernel)
def pv49639 : PrimeValue := ⟨49639, pr49639⟩
private theorem pr49663 : Nat.Prime 49663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv89]) (by decide +kernel)
def pv49663 : PrimeValue := ⟨49663, pr49663⟩
private theorem pr49667 : Nat.Prime 49667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv1307]) (by decide +kernel)
def pv49667 : PrimeValue := ⟨49667, pr49667⟩
private theorem pr49669 : Nat.Prime 49669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4139]) (by decide +kernel)
def pv49669 : PrimeValue := ⟨49669, pr49669⟩
private theorem pr49681 : Nat.Prime 49681 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv49681 : PrimeValue := ⟨49681, pr49681⟩
private theorem pr49697 : Nat.Prime 49697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1553]) (by decide +kernel)
def pv49697 : PrimeValue := ⟨49697, pr49697⟩
private theorem pr49711 : Nat.Prime 49711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1657]) (by decide +kernel)
def pv49711 : PrimeValue := ⟨49711, pr49711⟩
private theorem pr49727 : Nat.Prime 49727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv47]) (by decide +kernel)
def pv49727 : PrimeValue := ⟨49727, pr49727⟩
private theorem pr49739 : Nat.Prime 49739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv1913]) (by decide +kernel)
def pv49739 : PrimeValue := ⟨49739, pr49739⟩
private theorem pr49741 : Nat.Prime 49741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv829]) (by decide +kernel)
def pv49741 : PrimeValue := ⟨49741, pr49741⟩
private theorem pr49747 : Nat.Prime 49747 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8291]) (by decide +kernel)
def pv49747 : PrimeValue := ⟨49747, pr49747⟩
private theorem pr49757 : Nat.Prime 49757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1777]) (by decide +kernel)
def pv49757 : PrimeValue := ⟨49757, pr49757⟩
private theorem pr49783 : Nat.Prime 49783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8297]) (by decide +kernel)
def pv49783 : PrimeValue := ⟨49783, pr49783⟩
private theorem pr49787 : Nat.Prime 49787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv31,pv73]) (by decide +kernel)
def pv49787 : PrimeValue := ⟨49787, pr49787⟩
private theorem pr49789 : Nat.Prime 49789 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv461]) (by decide +kernel)
def pv49789 : PrimeValue := ⟨49789, pr49789⟩
private theorem pr49801 : Nat.Prime 49801 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv83]) (by decide +kernel)
def pv49801 : PrimeValue := ⟨49801, pr49801⟩
private theorem pr49807 : Nat.Prime 49807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2767]) (by decide +kernel)
def pv49807 : PrimeValue := ⟨49807, pr49807⟩
private theorem pr49811 : Nat.Prime 49811 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv293]) (by decide +kernel)
def pv49811 : PrimeValue := ⟨49811, pr49811⟩
private theorem pr49823 : Nat.Prime 49823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv859]) (by decide +kernel)
def pv49823 : PrimeValue := ⟨49823, pr49823⟩
private theorem pr49831 : Nat.Prime 49831 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv151]) (by decide +kernel)
def pv49831 : PrimeValue := ⟨49831, pr49831⟩
private theorem pr49843 : Nat.Prime 49843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv71]) (by decide +kernel)
def pv49843 : PrimeValue := ⟨49843, pr49843⟩
private theorem pr49853 : Nat.Prime 49853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv103]) (by decide +kernel)
def pv49853 : PrimeValue := ⟨49853, pr49853⟩
private theorem pr49871 : Nat.Prime 49871 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv4987]) (by decide +kernel)
def pv49871 : PrimeValue := ⟨49871, pr49871⟩
private theorem pr49877 : Nat.Prime 49877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv337]) (by decide +kernel)
def pv49877 : PrimeValue := ⟨49877, pr49877⟩
private theorem pr49891 : Nat.Prime 49891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1663]) (by decide +kernel)
def pv49891 : PrimeValue := ⟨49891, pr49891⟩
private theorem pr49919 : Nat.Prime 49919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv2269]) (by decide +kernel)
def pv49919 : PrimeValue := ⟨49919, pr49919⟩
private theorem pr49921 : Nat.Prime 49921 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv49921 : PrimeValue := ⟨49921, pr49921⟩
private theorem pr49927 : Nat.Prime 49927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53,pv157]) (by decide +kernel)
def pv49927 : PrimeValue := ⟨49927, pr49927⟩
private theorem pr49937 : Nat.Prime 49937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3121]) (by decide +kernel)
def pv49937 : PrimeValue := ⟨49937, pr49937⟩
private theorem pr49939 : Nat.Prime 49939 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv29,pv41]) (by decide +kernel)
def pv49939 : PrimeValue := ⟨49939, pr49939⟩
private theorem pr49943 : Nat.Prime 49943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv24971]) (by decide +kernel)
def pv49943 : PrimeValue := ⟨49943, pr49943⟩
private theorem pr49957 : Nat.Prime 49957 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv181]) (by decide +kernel)
def pv49957 : PrimeValue := ⟨49957, pr49957⟩
private theorem pr49991 : Nat.Prime 49991 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv4999]) (by decide +kernel)
def pv49991 : PrimeValue := ⟨49991, pr49991⟩
private theorem pr49993 : Nat.Prime 49993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2083]) (by decide +kernel)
def pv49993 : PrimeValue := ⟨49993, pr49993⟩
private theorem pr49999 : Nat.Prime 49999 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv641]) (by decide +kernel)
def pv49999 : PrimeValue := ⟨49999, pr49999⟩
private theorem pr50021 : Nat.Prime 50021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv61]) (by decide +kernel)
def pv50021 : PrimeValue := ⟨50021, pr50021⟩
private theorem pr50023 : Nat.Prime 50023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv397]) (by decide +kernel)
def pv50023 : PrimeValue := ⟨50023, pr50023⟩
private theorem pr50033 : Nat.Prime 50033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv59]) (by decide +kernel)
def pv50033 : PrimeValue := ⟨50033, pr50033⟩
private theorem pr50047 : Nat.Prime 50047 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv19,pv439]) (by decide +kernel)
def pv50047 : PrimeValue := ⟨50047, pr50047⟩
private theorem pr50051 : Nat.Prime 50051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv13]) (by decide +kernel)
def pv50051 : PrimeValue := ⟨50051, pr50051⟩
private theorem pr50053 : Nat.Prime 50053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv97]) (by decide +kernel)
def pv50053 : PrimeValue := ⟨50053, pr50053⟩
private theorem pr50069 : Nat.Prime 50069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12517]) (by decide +kernel)
def pv50069 : PrimeValue := ⟨50069, pr50069⟩
private theorem pr50077 : Nat.Prime 50077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv107]) (by decide +kernel)
def pv50077 : PrimeValue := ⟨50077, pr50077⟩
private theorem pr50087 : Nat.Prime 50087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv79,pv317]) (by decide +kernel)
def pv50087 : PrimeValue := ⟨50087, pr50087⟩
private theorem pr50093 : Nat.Prime 50093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1789]) (by decide +kernel)
def pv50093 : PrimeValue := ⟨50093, pr50093⟩
private theorem pr50101 : Nat.Prime 50101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv167]) (by decide +kernel)
def pv50101 : PrimeValue := ⟨50101, pr50101⟩
private theorem pr50111 : Nat.Prime 50111 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv5011]) (by decide +kernel)
def pv50111 : PrimeValue := ⟨50111, pr50111⟩
private theorem pr50119 : Nat.Prime 50119 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8353]) (by decide +kernel)
def pv50119 : PrimeValue := ⟨50119, pr50119⟩
private theorem pr50123 : Nat.Prime 50123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv1319]) (by decide +kernel)
def pv50123 : PrimeValue := ⟨50123, pr50123⟩
private theorem pr50129 : Nat.Prime 50129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv241]) (by decide +kernel)
def pv50129 : PrimeValue := ⟨50129, pr50129⟩
private theorem pr50131 : Nat.Prime 50131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv557]) (by decide +kernel)
def pv50131 : PrimeValue := ⟨50131, pr50131⟩
private theorem pr50147 : Nat.Prime 50147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv25073]) (by decide +kernel)
def pv50147 : PrimeValue := ⟨50147, pr50147⟩
private theorem pr50153 : Nat.Prime 50153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6269]) (by decide +kernel)
def pv50153 : PrimeValue := ⟨50153, pr50153⟩
private theorem pr50159 : Nat.Prime 50159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv31,pv809]) (by decide +kernel)
def pv50159 : PrimeValue := ⟨50159, pr50159⟩
private theorem pr50177 : Nat.Prime 50177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7]) (by decide +kernel)
def pv50177 : PrimeValue := ⟨50177, pr50177⟩
private theorem pr50207 : Nat.Prime 50207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv1931]) (by decide +kernel)
def pv50207 : PrimeValue := ⟨50207, pr50207⟩
private theorem pr50221 : Nat.Prime 50221 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv50221 : PrimeValue := ⟨50221, pr50221⟩
private theorem pr50227 : Nat.Prime 50227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv761]) (by decide +kernel)
def pv50227 : PrimeValue := ⟨50227, pr50227⟩
private theorem pr50231 : Nat.Prime 50231 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv5023]) (by decide +kernel)
def pv50231 : PrimeValue := ⟨50231, pr50231⟩
private theorem pr50261 : Nat.Prime 50261 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv359]) (by decide +kernel)
def pv50261 : PrimeValue := ⟨50261, pr50261⟩
private theorem pr50263 : Nat.Prime 50263 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8377]) (by decide +kernel)
def pv50263 : PrimeValue := ⟨50263, pr50263⟩
private theorem pr50273 : Nat.Prime 50273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1571]) (by decide +kernel)
def pv50273 : PrimeValue := ⟨50273, pr50273⟩
private theorem pr50287 : Nat.Prime 50287 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv29]) (by decide +kernel)
def pv50287 : PrimeValue := ⟨50287, pr50287⟩
private theorem pr50291 : Nat.Prime 50291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv107]) (by decide +kernel)
def pv50291 : PrimeValue := ⟨50291, pr50291⟩
private theorem pr50311 : Nat.Prime 50311 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv43]) (by decide +kernel)
def pv50311 : PrimeValue := ⟨50311, pr50311⟩
private theorem pr50321 : Nat.Prime 50321 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv37]) (by decide +kernel)
def pv50321 : PrimeValue := ⟨50321, pr50321⟩
private theorem pr50329 : Nat.Prime 50329 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv233]) (by decide +kernel)
def pv50329 : PrimeValue := ⟨50329, pr50329⟩
private theorem pr50333 : Nat.Prime 50333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12583]) (by decide +kernel)
def pv50333 : PrimeValue := ⟨50333, pr50333⟩
private theorem pr50341 : Nat.Prime 50341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv839]) (by decide +kernel)
def pv50341 : PrimeValue := ⟨50341, pr50341⟩
private theorem pr50359 : Nat.Prime 50359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv109]) (by decide +kernel)
def pv50359 : PrimeValue := ⟨50359, pr50359⟩
private theorem pr50363 : Nat.Prime 50363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv149]) (by decide +kernel)
def pv50363 : PrimeValue := ⟨50363, pr50363⟩
private theorem pr50377 : Nat.Prime 50377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2099]) (by decide +kernel)
def pv50377 : PrimeValue := ⟨50377, pr50377⟩
private theorem pr50383 : Nat.Prime 50383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv311]) (by decide +kernel)
def pv50383 : PrimeValue := ⟨50383, pr50383⟩
private theorem pr50387 : Nat.Prime 50387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv59,pv61]) (by decide +kernel)
def pv50387 : PrimeValue := ⟨50387, pr50387⟩
private theorem pr50411 : Nat.Prime 50411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv71]) (by decide +kernel)
def pv50411 : PrimeValue := ⟨50411, pr50411⟩
private theorem pr50417 : Nat.Prime 50417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv137]) (by decide +kernel)
def pv50417 : PrimeValue := ⟨50417, pr50417⟩
private theorem pr50423 : Nat.Prime 50423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv1483]) (by decide +kernel)
def pv50423 : PrimeValue := ⟨50423, pr50423⟩
private theorem pr50441 : Nat.Prime 50441 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv97]) (by decide +kernel)
def pv50441 : PrimeValue := ⟨50441, pr50441⟩
private theorem pr50459 : Nat.Prime 50459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv25229]) (by decide +kernel)
def pv50459 : PrimeValue := ⟨50459, pr50459⟩
private theorem pr50461 : Nat.Prime 50461 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv50461 : PrimeValue := ⟨50461, pr50461⟩
private theorem pr50497 : Nat.Prime 50497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv263]) (by decide +kernel)
def pv50497 : PrimeValue := ⟨50497, pr50497⟩
private theorem pr50503 : Nat.Prime 50503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv443]) (by decide +kernel)
def pv50503 : PrimeValue := ⟨50503, pr50503⟩
private theorem pr50513 : Nat.Prime 50513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv41]) (by decide +kernel)
def pv50513 : PrimeValue := ⟨50513, pr50513⟩
private theorem pr50527 : Nat.Prime 50527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv401]) (by decide +kernel)
def pv50527 : PrimeValue := ⟨50527, pr50527⟩
private theorem pr50539 : Nat.Prime 50539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8423]) (by decide +kernel)
def pv50539 : PrimeValue := ⟨50539, pr50539⟩
private theorem pr50543 : Nat.Prime 50543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv683]) (by decide +kernel)
def pv50543 : PrimeValue := ⟨50543, pr50543⟩
private theorem pr50549 : Nat.Prime 50549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12637]) (by decide +kernel)
def pv50549 : PrimeValue := ⟨50549, pr50549⟩
private theorem pr50551 : Nat.Prime 50551 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv337]) (by decide +kernel)
def pv50551 : PrimeValue := ⟨50551, pr50551⟩
private theorem pr50581 : Nat.Prime 50581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv281]) (by decide +kernel)
def pv50581 : PrimeValue := ⟨50581, pr50581⟩
private theorem pr50587 : Nat.Prime 50587 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv8431]) (by decide +kernel)
def pv50587 : PrimeValue := ⟨50587, pr50587⟩
private theorem pr50591 : Nat.Prime 50591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv5059]) (by decide +kernel)
def pv50591 : PrimeValue := ⟨50591, pr50591⟩
private theorem pr50593 : Nat.Prime 50593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv31]) (by decide +kernel)
def pv50593 : PrimeValue := ⟨50593, pr50593⟩
private theorem pr50599 : Nat.Prime 50599 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv937]) (by decide +kernel)
def pv50599 : PrimeValue := ⟨50599, pr50599⟩
private theorem pr50627 : Nat.Prime 50627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv1489]) (by decide +kernel)
def pv50627 : PrimeValue := ⟨50627, pr50627⟩
private theorem pr50647 : Nat.Prime 50647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv367]) (by decide +kernel)
def pv50647 : PrimeValue := ⟨50647, pr50647⟩
private theorem pr50651 : Nat.Prime 50651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1013]) (by decide +kernel)
def pv50651 : PrimeValue := ⟨50651, pr50651⟩
private theorem pr50671 : Nat.Prime 50671 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv563]) (by decide +kernel)
def pv50671 : PrimeValue := ⟨50671, pr50671⟩
private theorem pr50683 : Nat.Prime 50683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8447]) (by decide +kernel)
def pv50683 : PrimeValue := ⟨50683, pr50683⟩
private theorem pr50707 : Nat.Prime 50707 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv313]) (by decide +kernel)
def pv50707 : PrimeValue := ⟨50707, pr50707⟩
private theorem pr50723 : Nat.Prime 50723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv3623]) (by decide +kernel)
def pv50723 : PrimeValue := ⟨50723, pr50723⟩
private theorem pr50741 : Nat.Prime 50741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv59]) (by decide +kernel)
def pv50741 : PrimeValue := ⟨50741, pr50741⟩
private theorem pr50753 : Nat.Prime 50753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv61]) (by decide +kernel)
def pv50753 : PrimeValue := ⟨50753, pr50753⟩
private theorem pr50767 : Nat.Prime 50767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv8461]) (by decide +kernel)
def pv50767 : PrimeValue := ⟨50767, pr50767⟩
private theorem pr50773 : Nat.Prime 50773 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv4231]) (by decide +kernel)
def pv50773 : PrimeValue := ⟨50773, pr50773⟩
private theorem pr50777 : Nat.Prime 50777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv577]) (by decide +kernel)
def pv50777 : PrimeValue := ⟨50777, pr50777⟩
private theorem pr50789 : Nat.Prime 50789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12697]) (by decide +kernel)
def pv50789 : PrimeValue := ⟨50789, pr50789⟩
private theorem pr50821 : Nat.Prime 50821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv50821 : PrimeValue := ⟨50821, pr50821⟩
private theorem pr50833 : Nat.Prime 50833 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv353]) (by decide +kernel)
def pv50833 : PrimeValue := ⟨50833, pr50833⟩
private theorem pr50839 : Nat.Prime 50839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv229]) (by decide +kernel)
def pv50839 : PrimeValue := ⟨50839, pr50839⟩
private theorem pr50849 : Nat.Prime 50849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv227]) (by decide +kernel)
def pv50849 : PrimeValue := ⟨50849, pr50849⟩
private theorem pr50857 : Nat.Prime 50857 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv13,pv163]) (by decide +kernel)
def pv50857 : PrimeValue := ⟨50857, pr50857⟩
private theorem pr50867 : Nat.Prime 50867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv877]) (by decide +kernel)
def pv50867 : PrimeValue := ⟨50867, pr50867⟩
private theorem pr50873 : Nat.Prime 50873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6359]) (by decide +kernel)
def pv50873 : PrimeValue := ⟨50873, pr50873⟩
private theorem pr50891 : Nat.Prime 50891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv727]) (by decide +kernel)
def pv50891 : PrimeValue := ⟨50891, pr50891⟩
private theorem pr50893 : Nat.Prime 50893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4241]) (by decide +kernel)
def pv50893 : PrimeValue := ⟨50893, pr50893⟩
private theorem pr50909 : Nat.Prime 50909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv89]) (by decide +kernel)
def pv50909 : PrimeValue := ⟨50909, pr50909⟩
private theorem pr50923 : Nat.Prime 50923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv41]) (by decide +kernel)
def pv50923 : PrimeValue := ⟨50923, pr50923⟩
private theorem pr50929 : Nat.Prime 50929 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv1061]) (by decide +kernel)
def pv50929 : PrimeValue := ⟨50929, pr50929⟩
private theorem pr50951 : Nat.Prime 50951 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv1019]) (by decide +kernel)
def pv50951 : PrimeValue := ⟨50951, pr50951⟩
private theorem pr50957 : Nat.Prime 50957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12739]) (by decide +kernel)
def pv50957 : PrimeValue := ⟨50957, pr50957⟩
private theorem pr50969 : Nat.Prime 50969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv277]) (by decide +kernel)
def pv50969 : PrimeValue := ⟨50969, pr50969⟩
private theorem pr50971 : Nat.Prime 50971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1699]) (by decide +kernel)
def pv50971 : PrimeValue := ⟨50971, pr50971⟩
private theorem pr50989 : Nat.Prime 50989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv607]) (by decide +kernel)
def pv50989 : PrimeValue := ⟨50989, pr50989⟩
private theorem pr50993 : Nat.Prime 50993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3187]) (by decide +kernel)
def pv50993 : PrimeValue := ⟨50993, pr50993⟩
private theorem pr51001 : Nat.Prime 51001 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv51001 : PrimeValue := ⟨51001, pr51001⟩
private theorem pr51031 : Nat.Prime 51031 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv51031 : PrimeValue := ⟨51031, pr51031⟩
private theorem pr51043 : Nat.Prime 51043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv181]) (by decide +kernel)
def pv51043 : PrimeValue := ⟨51043, pr51043⟩
private theorem pr51047 : Nat.Prime 51047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv25523]) (by decide +kernel)
def pv51047 : PrimeValue := ⟨51047, pr51047⟩
private theorem pr51059 : Nat.Prime 51059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv521]) (by decide +kernel)
def pv51059 : PrimeValue := ⟨51059, pr51059⟩
private theorem pr51061 : Nat.Prime 51061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv37]) (by decide +kernel)
def pv51061 : PrimeValue := ⟨51061, pr51061⟩
private theorem pr51071 : Nat.Prime 51071 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv5107]) (by decide +kernel)
def pv51071 : PrimeValue := ⟨51071, pr51071⟩
private theorem pr51109 : Nat.Prime 51109 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv4259]) (by decide +kernel)
def pv51109 : PrimeValue := ⟨51109, pr51109⟩
private theorem pr51131 : Nat.Prime 51131 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv5113]) (by decide +kernel)
def pv51131 : PrimeValue := ⟨51131, pr51131⟩
private theorem pr51133 : Nat.Prime 51133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4261]) (by decide +kernel)
def pv51133 : PrimeValue := ⟨51133, pr51133⟩
private theorem pr51137 : Nat.Prime 51137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv47]) (by decide +kernel)
def pv51137 : PrimeValue := ⟨51137, pr51137⟩
private theorem pr51151 : Nat.Prime 51151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv31]) (by decide +kernel)
def pv51151 : PrimeValue := ⟨51151, pr51151⟩
private theorem pr51157 : Nat.Prime 51157 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv51157 : PrimeValue := ⟨51157, pr51157⟩
private theorem pr51169 : Nat.Prime 51169 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv13,pv41]) (by decide +kernel)
def pv51169 : PrimeValue := ⟨51169, pr51169⟩
private theorem pr51193 : Nat.Prime 51193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv51193 : PrimeValue := ⟨51193, pr51193⟩
private theorem pr51197 : Nat.Prime 51197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12799]) (by decide +kernel)
def pv51197 : PrimeValue := ⟨51197, pr51197⟩
private theorem pr51199 : Nat.Prime 51199 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv23,pv53]) (by decide +kernel)
def pv51199 : PrimeValue := ⟨51199, pr51199⟩
private theorem pr51203 : Nat.Prime 51203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv25601]) (by decide +kernel)
def pv51203 : PrimeValue := ⟨51203, pr51203⟩
private theorem pr51217 : Nat.Prime 51217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv97]) (by decide +kernel)
def pv51217 : PrimeValue := ⟨51217, pr51217⟩
private theorem pr51229 : Nat.Prime 51229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1423]) (by decide +kernel)
def pv51229 : PrimeValue := ⟨51229, pr51229⟩
private theorem pr51239 : Nat.Prime 51239 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv11,pv17,pv137]) (by decide +kernel)
def pv51239 : PrimeValue := ⟨51239, pr51239⟩
private theorem pr51241 : Nat.Prime 51241 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv61]) (by decide +kernel)
def pv51241 : PrimeValue := ⟨51241, pr51241⟩
private theorem pr51257 : Nat.Prime 51257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv149]) (by decide +kernel)
def pv51257 : PrimeValue := ⟨51257, pr51257⟩
private theorem pr51263 : Nat.Prime 51263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv71]) (by decide +kernel)
def pv51263 : PrimeValue := ⟨51263, pr51263⟩
private theorem pr51283 : Nat.Prime 51283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv37]) (by decide +kernel)
def pv51283 : PrimeValue := ⟨51283, pr51283⟩
private theorem pr51287 : Nat.Prime 51287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv25643]) (by decide +kernel)
def pv51287 : PrimeValue := ⟨51287, pr51287⟩
private theorem pr51307 : Nat.Prime 51307 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv503]) (by decide +kernel)
def pv51307 : PrimeValue := ⟨51307, pr51307⟩
private theorem pr51329 : Nat.Prime 51329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv401]) (by decide +kernel)
def pv51329 : PrimeValue := ⟨51329, pr51329⟩
private theorem pr51341 : Nat.Prime 51341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv151]) (by decide +kernel)
def pv51341 : PrimeValue := ⟨51341, pr51341⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
