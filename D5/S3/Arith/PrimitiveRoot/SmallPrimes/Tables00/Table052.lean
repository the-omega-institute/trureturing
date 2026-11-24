/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table052
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table052.pv146381
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr146381 : Nat.Prime 146381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv563]) (by decide +kernel)
def pv146381 : PrimeValue := ⟨146381, pr146381⟩
private theorem pr146383 : Nat.Prime 146383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv787]) (by decide +kernel)
def pv146383 : PrimeValue := ⟨146383, pr146383⟩
private theorem pr146407 : Nat.Prime 146407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv1877]) (by decide +kernel)
def pv146407 : PrimeValue := ⟨146407, pr146407⟩
private theorem pr146423 : Nat.Prime 146423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv179,pv409]) (by decide +kernel)
def pv146423 : PrimeValue := ⟨146423, pr146423⟩
private theorem pr146437 : Nat.Prime 146437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12203]) (by decide +kernel)
def pv146437 : PrimeValue := ⟨146437, pr146437⟩
private theorem pr146477 : Nat.Prime 146477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv3329]) (by decide +kernel)
def pv146477 : PrimeValue := ⟨146477, pr146477⟩
private theorem pr146513 : Nat.Prime 146513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9157]) (by decide +kernel)
def pv146513 : PrimeValue := ⟨146513, pr146513⟩
private theorem pr146519 : Nat.Prime 146519 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv73259]) (by decide +kernel)
def pv146519 : PrimeValue := ⟨146519, pr146519⟩
private theorem pr146521 : Nat.Prime 146521 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv37]) (by decide +kernel)
def pv146521 : PrimeValue := ⟨146521, pr146521⟩
private theorem pr146539 : Nat.Prime 146539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1163]) (by decide +kernel)
def pv146539 : PrimeValue := ⟨146539, pr146539⟩
private theorem pr146543 : Nat.Prime 146543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv6661]) (by decide +kernel)
def pv146543 : PrimeValue := ⟨146543, pr146543⟩
private theorem pr146563 : Nat.Prime 146563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1879]) (by decide +kernel)
def pv146563 : PrimeValue := ⟨146563, pr146563⟩
private theorem pr146581 : Nat.Prime 146581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv349]) (by decide +kernel)
def pv146581 : PrimeValue := ⟨146581, pr146581⟩
private theorem pr146603 : Nat.Prime 146603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv3187]) (by decide +kernel)
def pv146603 : PrimeValue := ⟨146603, pr146603⟩
private theorem pr146617 : Nat.Prime 146617 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv41,pv149]) (by decide +kernel)
def pv146617 : PrimeValue := ⟨146617, pr146617⟩
private theorem pr146639 : Nat.Prime 146639 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv157,pv467]) (by decide +kernel)
def pv146639 : PrimeValue := ⟨146639, pr146639⟩
private theorem pr146647 : Nat.Prime 146647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8147]) (by decide +kernel)
def pv146647 : PrimeValue := ⟨146647, pr146647⟩
private theorem pr146669 : Nat.Prime 146669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv991]) (by decide +kernel)
def pv146669 : PrimeValue := ⟨146669, pr146669⟩
private theorem pr146677 : Nat.Prime 146677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv719]) (by decide +kernel)
def pv146677 : PrimeValue := ⟨146677, pr146677⟩
private theorem pr146681 : Nat.Prime 146681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv193]) (by decide +kernel)
def pv146681 : PrimeValue := ⟨146681, pr146681⟩
private theorem pr146683 : Nat.Prime 146683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv281]) (by decide +kernel)
def pv146683 : PrimeValue := ⟨146683, pr146683⟩
private theorem pr146701 : Nat.Prime 146701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv163]) (by decide +kernel)
def pv146701 : PrimeValue := ⟨146701, pr146701⟩
private theorem pr146743 : Nat.Prime 146743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv661]) (by decide +kernel)
def pv146743 : PrimeValue := ⟨146743, pr146743⟩
private theorem pr146767 : Nat.Prime 146767 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv61,pv401]) (by decide +kernel)
def pv146767 : PrimeValue := ⟨146767, pr146767⟩
private theorem pr146801 : Nat.Prime 146801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv367]) (by decide +kernel)
def pv146801 : PrimeValue := ⟨146801, pr146801⟩
private theorem pr146807 : Nat.Prime 146807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv6673]) (by decide +kernel)
def pv146807 : PrimeValue := ⟨146807, pr146807⟩
private theorem pr146819 : Nat.Prime 146819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv10487]) (by decide +kernel)
def pv146819 : PrimeValue := ⟨146819, pr146819⟩
private theorem pr146833 : Nat.Prime 146833 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7,pv19,pv23]) (by decide +kernel)
def pv146833 : PrimeValue := ⟨146833, pr146833⟩
private theorem pr146837 : Nat.Prime 146837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv36709]) (by decide +kernel)
def pv146837 : PrimeValue := ⟨146837, pr146837⟩
private theorem pr146849 : Nat.Prime 146849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv353]) (by decide +kernel)
def pv146849 : PrimeValue := ⟨146849, pr146849⟩
private theorem pr146857 : Nat.Prime 146857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv211]) (by decide +kernel)
def pv146857 : PrimeValue := ⟨146857, pr146857⟩
private theorem pr146891 : Nat.Prime 146891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv397]) (by decide +kernel)
def pv146891 : PrimeValue := ⟨146891, pr146891⟩
private theorem pr146893 : Nat.Prime 146893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12241]) (by decide +kernel)
def pv146893 : PrimeValue := ⟨146893, pr146893⟩
private theorem pr146917 : Nat.Prime 146917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv53]) (by decide +kernel)
def pv146917 : PrimeValue := ⟨146917, pr146917⟩
private theorem pr146921 : Nat.Prime 146921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3673]) (by decide +kernel)
def pv146921 : PrimeValue := ⟨146921, pr146921⟩
private theorem pr146953 : Nat.Prime 146953 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv13,pv157]) (by decide +kernel)
def pv146953 : PrimeValue := ⟨146953, pr146953⟩
private theorem pr146983 : Nat.Prime 146983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv17,pv131]) (by decide +kernel)
def pv146983 : PrimeValue := ⟨146983, pr146983⟩
private theorem pr147011 : Nat.Prime 147011 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv61,pv241]) (by decide +kernel)
def pv147011 : PrimeValue := ⟨147011, pr147011⟩
private theorem pr147029 : Nat.Prime 147029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv59,pv89]) (by decide +kernel)
def pv147029 : PrimeValue := ⟨147029, pr147029⟩
private theorem pr147031 : Nat.Prime 147031 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv29]) (by decide +kernel)
def pv147031 : PrimeValue := ⟨147031, pr147031⟩
private theorem pr147047 : Nat.Prime 147047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv73523]) (by decide +kernel)
def pv147047 : PrimeValue := ⟨147047, pr147047⟩
private theorem pr147073 : Nat.Prime 147073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv383]) (by decide +kernel)
def pv147073 : PrimeValue := ⟨147073, pr147073⟩
private theorem pr147083 : Nat.Prime 147083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv5657]) (by decide +kernel)
def pv147083 : PrimeValue := ⟨147083, pr147083⟩
private theorem pr147089 : Nat.Prime 147089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv317]) (by decide +kernel)
def pv147089 : PrimeValue := ⟨147089, pr147089⟩
private theorem pr147097 : Nat.Prime 147097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv227]) (by decide +kernel)
def pv147097 : PrimeValue := ⟨147097, pr147097⟩
private theorem pr147107 : Nat.Prime 147107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73553]) (by decide +kernel)
def pv147107 : PrimeValue := ⟨147107, pr147107⟩
private theorem pr147137 : Nat.Prime 147137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv19]) (by decide +kernel)
def pv147137 : PrimeValue := ⟨147137, pr147137⟩
private theorem pr147151 : Nat.Prime 147151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv109]) (by decide +kernel)
def pv147151 : PrimeValue := ⟨147151, pr147151⟩
private theorem pr147163 : Nat.Prime 147163 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv24527]) (by decide +kernel)
def pv147163 : PrimeValue := ⟨147163, pr147163⟩
private theorem pr147179 : Nat.Prime 147179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73589]) (by decide +kernel)
def pv147179 : PrimeValue := ⟨147179, pr147179⟩
private theorem pr147197 : Nat.Prime 147197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv751]) (by decide +kernel)
def pv147197 : PrimeValue := ⟨147197, pr147197⟩
private theorem pr147209 : Nat.Prime 147209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv18401]) (by decide +kernel)
def pv147209 : PrimeValue := ⟨147209, pr147209⟩
private theorem pr147211 : Nat.Prime 147211 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv701]) (by decide +kernel)
def pv147211 : PrimeValue := ⟨147211, pr147211⟩
private theorem pr147221 : Nat.Prime 147221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv433]) (by decide +kernel)
def pv147221 : PrimeValue := ⟨147221, pr147221⟩
private theorem pr147227 : Nat.Prime 147227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73613]) (by decide +kernel)
def pv147227 : PrimeValue := ⟨147227, pr147227⟩
private theorem pr147229 : Nat.Prime 147229 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv12269]) (by decide +kernel)
def pv147229 : PrimeValue := ⟨147229, pr147229⟩
private theorem pr147253 : Nat.Prime 147253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1753]) (by decide +kernel)
def pv147253 : PrimeValue := ⟨147253, pr147253⟩
private theorem pr147263 : Nat.Prime 147263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv2539]) (by decide +kernel)
def pv147263 : PrimeValue := ⟨147263, pr147263⟩
private theorem pr147283 : Nat.Prime 147283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24547]) (by decide +kernel)
def pv147283 : PrimeValue := ⟨147283, pr147283⟩
private theorem pr147289 : Nat.Prime 147289 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv19]) (by decide +kernel)
def pv147289 : PrimeValue := ⟨147289, pr147289⟩
private theorem pr147293 : Nat.Prime 147293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv1601]) (by decide +kernel)
def pv147293 : PrimeValue := ⟨147293, pr147293⟩
private theorem pr147299 : Nat.Prime 147299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv1567]) (by decide +kernel)
def pv147299 : PrimeValue := ⟨147299, pr147299⟩
private theorem pr147311 : Nat.Prime 147311 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv14731]) (by decide +kernel)
def pv147311 : PrimeValue := ⟨147311, pr147311⟩
private theorem pr147319 : Nat.Prime 147319 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv571]) (by decide +kernel)
def pv147319 : PrimeValue := ⟨147319, pr147319⟩
private theorem pr147331 : Nat.Prime 147331 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv1637]) (by decide +kernel)
def pv147331 : PrimeValue := ⟨147331, pr147331⟩
private theorem pr147341 : Nat.Prime 147341 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv53,pv139]) (by decide +kernel)
def pv147341 : PrimeValue := ⟨147341, pr147341⟩
private theorem pr147347 : Nat.Prime 147347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73673]) (by decide +kernel)
def pv147347 : PrimeValue := ⟨147347, pr147347⟩
private theorem pr147353 : Nat.Prime 147353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv113,pv163]) (by decide +kernel)
def pv147353 : PrimeValue := ⟨147353, pr147353⟩
private theorem pr147377 : Nat.Prime 147377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61,pv151]) (by decide +kernel)
def pv147377 : PrimeValue := ⟨147377, pr147377⟩
private theorem pr147397 : Nat.Prime 147397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv173]) (by decide +kernel)
def pv147397 : PrimeValue := ⟨147397, pr147397⟩
private theorem pr147401 : Nat.Prime 147401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv67]) (by decide +kernel)
def pv147401 : PrimeValue := ⟨147401, pr147401⟩
private theorem pr147409 : Nat.Prime 147409 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv37,pv83]) (by decide +kernel)
def pv147409 : PrimeValue := ⟨147409, pr147409⟩
private theorem pr147419 : Nat.Prime 147419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73709]) (by decide +kernel)
def pv147419 : PrimeValue := ⟨147419, pr147419⟩
private theorem pr147449 : Nat.Prime 147449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv2633]) (by decide +kernel)
def pv147449 : PrimeValue := ⟨147449, pr147449⟩
private theorem pr147457 : Nat.Prime 147457 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3]) (by decide +kernel)
def pv147457 : PrimeValue := ⟨147457, pr147457⟩
private theorem pr147487 : Nat.Prime 147487 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv523]) (by decide +kernel)
def pv147487 : PrimeValue := ⟨147487, pr147487⟩
private theorem pr147503 : Nat.Prime 147503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv73751]) (by decide +kernel)
def pv147503 : PrimeValue := ⟨147503, pr147503⟩
private theorem pr147517 : Nat.Prime 147517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv647]) (by decide +kernel)
def pv147517 : PrimeValue := ⟨147517, pr147517⟩
private theorem pr147541 : Nat.Prime 147541 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv2459]) (by decide +kernel)
def pv147541 : PrimeValue := ⟨147541, pr147541⟩
private theorem pr147547 : Nat.Prime 147547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1171]) (by decide +kernel)
def pv147547 : PrimeValue := ⟨147547, pr147547⟩
private theorem pr147551 : Nat.Prime 147551 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv13,pv227]) (by decide +kernel)
def pv147551 : PrimeValue := ⟨147551, pr147551⟩
private theorem pr147557 : Nat.Prime 147557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv997]) (by decide +kernel)
def pv147557 : PrimeValue := ⟨147557, pr147557⟩
private theorem pr147571 : Nat.Prime 147571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4919]) (by decide +kernel)
def pv147571 : PrimeValue := ⟨147571, pr147571⟩
private theorem pr147583 : Nat.Prime 147583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv911]) (by decide +kernel)
def pv147583 : PrimeValue := ⟨147583, pr147583⟩
private theorem pr147607 : Nat.Prime 147607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv73,pv337]) (by decide +kernel)
def pv147607 : PrimeValue := ⟨147607, pr147607⟩
private theorem pr147613 : Nat.Prime 147613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12301]) (by decide +kernel)
def pv147613 : PrimeValue := ⟨147613, pr147613⟩
private theorem pr147617 : Nat.Prime 147617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv659]) (by decide +kernel)
def pv147617 : PrimeValue := ⟨147617, pr147617⟩
private theorem pr147629 : Nat.Prime 147629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17,pv167]) (by decide +kernel)
def pv147629 : PrimeValue := ⟨147629, pr147629⟩
private theorem pr147647 : Nat.Prime 147647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv73823]) (by decide +kernel)
def pv147647 : PrimeValue := ⟨147647, pr147647⟩
private theorem pr147661 : Nat.Prime 147661 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv107]) (by decide +kernel)
def pv147661 : PrimeValue := ⟨147661, pr147661⟩
private theorem pr147671 : Nat.Prime 147671 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv14767]) (by decide +kernel)
def pv147671 : PrimeValue := ⟨147671, pr147671⟩
private theorem pr147673 : Nat.Prime 147673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv293]) (by decide +kernel)
def pv147673 : PrimeValue := ⟨147673, pr147673⟩
private theorem pr147689 : Nat.Prime 147689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv18461]) (by decide +kernel)
def pv147689 : PrimeValue := ⟨147689, pr147689⟩
private theorem pr147703 : Nat.Prime 147703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv103,pv239]) (by decide +kernel)
def pv147703 : PrimeValue := ⟨147703, pr147703⟩
private theorem pr147739 : Nat.Prime 147739 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv24623]) (by decide +kernel)
def pv147739 : PrimeValue := ⟨147739, pr147739⟩
private theorem pr147743 : Nat.Prime 147743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv61,pv173]) (by decide +kernel)
def pv147743 : PrimeValue := ⟨147743, pr147743⟩
private theorem pr147769 : Nat.Prime 147769 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv47,pv131]) (by decide +kernel)
def pv147769 : PrimeValue := ⟨147769, pr147769⟩
private theorem pr147773 : Nat.Prime 147773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv36943]) (by decide +kernel)
def pv147773 : PrimeValue := ⟨147773, pr147773⟩
private theorem pr147779 : Nat.Prime 147779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv1997]) (by decide +kernel)
def pv147779 : PrimeValue := ⟨147779, pr147779⟩
private theorem pr147787 : Nat.Prime 147787 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv24631]) (by decide +kernel)
def pv147787 : PrimeValue := ⟨147787, pr147787⟩
private theorem pr147793 : Nat.Prime 147793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3079]) (by decide +kernel)
def pv147793 : PrimeValue := ⟨147793, pr147793⟩
private theorem pr147799 : Nat.Prime 147799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv23]) (by decide +kernel)
def pv147799 : PrimeValue := ⟨147799, pr147799⟩
private theorem pr147811 : Nat.Prime 147811 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv379]) (by decide +kernel)
def pv147811 : PrimeValue := ⟨147811, pr147811⟩
private theorem pr147827 : Nat.Prime 147827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv10559]) (by decide +kernel)
def pv147827 : PrimeValue := ⟨147827, pr147827⟩
private theorem pr147859 : Nat.Prime 147859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1297]) (by decide +kernel)
def pv147859 : PrimeValue := ⟨147859, pr147859⟩
private theorem pr147863 : Nat.Prime 147863 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv13,pv47]) (by decide +kernel)
def pv147863 : PrimeValue := ⟨147863, pr147863⟩
private theorem pr147881 : Nat.Prime 147881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3697]) (by decide +kernel)
def pv147881 : PrimeValue := ⟨147881, pr147881⟩
private theorem pr147919 : Nat.Prime 147919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv89,pv277]) (by decide +kernel)
def pv147919 : PrimeValue := ⟨147919, pr147919⟩
private theorem pr147937 : Nat.Prime 147937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv67]) (by decide +kernel)
def pv147937 : PrimeValue := ⟨147937, pr147937⟩
private theorem pr148013 : Nat.Prime 148013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37003]) (by decide +kernel)
def pv148013 : PrimeValue := ⟨148013, pr148013⟩
private theorem pr148021 : Nat.Prime 148021 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv2467]) (by decide +kernel)
def pv148021 : PrimeValue := ⟨148021, pr148021⟩
private theorem pr148061 : Nat.Prime 148061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv673]) (by decide +kernel)
def pv148061 : PrimeValue := ⟨148061, pr148061⟩
private theorem pr148063 : Nat.Prime 148063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv24677]) (by decide +kernel)
def pv148063 : PrimeValue := ⟨148063, pr148063⟩
private theorem pr148079 : Nat.Prime 148079 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv1511]) (by decide +kernel)
def pv148079 : PrimeValue := ⟨148079, pr148079⟩
private theorem pr148091 : Nat.Prime 148091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv251]) (by decide +kernel)
def pv148091 : PrimeValue := ⟨148091, pr148091⟩
private theorem pr148123 : Nat.Prime 148123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv211]) (by decide +kernel)
def pv148123 : PrimeValue := ⟨148123, pr148123⟩
private theorem pr148139 : Nat.Prime 148139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv4357]) (by decide +kernel)
def pv148139 : PrimeValue := ⟨148139, pr148139⟩
private theorem pr148147 : Nat.Prime 148147 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv24691]) (by decide +kernel)
def pv148147 : PrimeValue := ⟨148147, pr148147⟩
private theorem pr148153 : Nat.Prime 148153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6173]) (by decide +kernel)
def pv148153 : PrimeValue := ⟨148153, pr148153⟩
private theorem pr148157 : Nat.Prime 148157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37039]) (by decide +kernel)
def pv148157 : PrimeValue := ⟨148157, pr148157⟩
private theorem pr148171 : Nat.Prime 148171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv449]) (by decide +kernel)
def pv148171 : PrimeValue := ⟨148171, pr148171⟩
private theorem pr148193 : Nat.Prime 148193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv421]) (by decide +kernel)
def pv148193 : PrimeValue := ⟨148193, pr148193⟩
private theorem pr148201 : Nat.Prime 148201 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv13,pv19]) (by decide +kernel)
def pv148201 : PrimeValue := ⟨148201, pr148201⟩
private theorem pr148207 : Nat.Prime 148207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv1453]) (by decide +kernel)
def pv148207 : PrimeValue := ⟨148207, pr148207⟩
private theorem pr148229 : Nat.Prime 148229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37057]) (by decide +kernel)
def pv148229 : PrimeValue := ⟨148229, pr148229⟩
private theorem pr148243 : Nat.Prime 148243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv797]) (by decide +kernel)
def pv148243 : PrimeValue := ⟨148243, pr148243⟩
private theorem pr148249 : Nat.Prime 148249 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv29,pv71]) (by decide +kernel)
def pv148249 : PrimeValue := ⟨148249, pr148249⟩
private theorem pr148279 : Nat.Prime 148279 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13,pv1901]) (by decide +kernel)
def pv148279 : PrimeValue := ⟨148279, pr148279⟩
private theorem pr148301 : Nat.Prime 148301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1483]) (by decide +kernel)
def pv148301 : PrimeValue := ⟨148301, pr148301⟩
private theorem pr148303 : Nat.Prime 148303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv107]) (by decide +kernel)
def pv148303 : PrimeValue := ⟨148303, pr148303⟩
private theorem pr148331 : Nat.Prime 148331 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv163]) (by decide +kernel)
def pv148331 : PrimeValue := ⟨148331, pr148331⟩
private theorem pr148339 : Nat.Prime 148339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv67]) (by decide +kernel)
def pv148339 : PrimeValue := ⟨148339, pr148339⟩
private theorem pr148361 : Nat.Prime 148361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3709]) (by decide +kernel)
def pv148361 : PrimeValue := ⟨148361, pr148361⟩
private theorem pr148367 : Nat.Prime 148367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv2393]) (by decide +kernel)
def pv148367 : PrimeValue := ⟨148367, pr148367⟩
private theorem pr148381 : Nat.Prime 148381 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv2473]) (by decide +kernel)
def pv148381 : PrimeValue := ⟨148381, pr148381⟩
private theorem pr148399 : Nat.Prime 148399 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv24733]) (by decide +kernel)
def pv148399 : PrimeValue := ⟨148399, pr148399⟩
private theorem pr148403 : Nat.Prime 148403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv74201]) (by decide +kernel)
def pv148403 : PrimeValue := ⟨148403, pr148403⟩
private theorem pr148411 : Nat.Prime 148411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv97]) (by decide +kernel)
def pv148411 : PrimeValue := ⟨148411, pr148411⟩
private theorem pr148429 : Nat.Prime 148429 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv19,pv31]) (by decide +kernel)
def pv148429 : PrimeValue := ⟨148429, pr148429⟩
private theorem pr148439 : Nat.Prime 148439 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv74219]) (by decide +kernel)
def pv148439 : PrimeValue := ⟨148439, pr148439⟩
private theorem pr148457 : Nat.Prime 148457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv241]) (by decide +kernel)
def pv148457 : PrimeValue := ⟨148457, pr148457⟩
private theorem pr148469 : Nat.Prime 148469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37117]) (by decide +kernel)
def pv148469 : PrimeValue := ⟨148469, pr148469⟩
private theorem pr148471 : Nat.Prime 148471 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv101]) (by decide +kernel)
def pv148471 : PrimeValue := ⟨148471, pr148471⟩
private theorem pr148483 : Nat.Prime 148483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73,pv113]) (by decide +kernel)
def pv148483 : PrimeValue := ⟨148483, pr148483⟩
private theorem pr148501 : Nat.Prime 148501 :=
  checkPrime_prime (q := pv83) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv148501 : PrimeValue := ⟨148501, pr148501⟩
private theorem pr148517 : Nat.Prime 148517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv347]) (by decide +kernel)
def pv148517 : PrimeValue := ⟨148517, pr148517⟩
private theorem pr148531 : Nat.Prime 148531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4951]) (by decide +kernel)
def pv148531 : PrimeValue := ⟨148531, pr148531⟩
private theorem pr148537 : Nat.Prime 148537 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv2063]) (by decide +kernel)
def pv148537 : PrimeValue := ⟨148537, pr148537⟩
private theorem pr148549 : Nat.Prime 148549 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv12379]) (by decide +kernel)
def pv148549 : PrimeValue := ⟨148549, pr148549⟩
private theorem pr148573 : Nat.Prime 148573 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4127]) (by decide +kernel)
def pv148573 : PrimeValue := ⟨148573, pr148573⟩
private theorem pr148579 : Nat.Prime 148579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24763]) (by decide +kernel)
def pv148579 : PrimeValue := ⟨148579, pr148579⟩
private theorem pr148609 : Nat.Prime 148609 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv148609 : PrimeValue := ⟨148609, pr148609⟩
private theorem pr148627 : Nat.Prime 148627 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv23,pv359]) (by decide +kernel)
def pv148627 : PrimeValue := ⟨148627, pr148627⟩
private theorem pr148633 : Nat.Prime 148633 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv11,pv563]) (by decide +kernel)
def pv148633 : PrimeValue := ⟨148633, pr148633⟩
private theorem pr148639 : Nat.Prime 148639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv3539]) (by decide +kernel)
def pv148639 : PrimeValue := ⟨148639, pr148639⟩
private theorem pr148663 : Nat.Prime 148663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2753]) (by decide +kernel)
def pv148663 : PrimeValue := ⟨148663, pr148663⟩
private theorem pr148669 : Nat.Prime 148669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv953]) (by decide +kernel)
def pv148669 : PrimeValue := ⟨148669, pr148669⟩
private theorem pr148693 : Nat.Prime 148693 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv12391]) (by decide +kernel)
def pv148693 : PrimeValue := ⟨148693, pr148693⟩
private theorem pr148711 : Nat.Prime 148711 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv4957]) (by decide +kernel)
def pv148711 : PrimeValue := ⟨148711, pr148711⟩
private theorem pr148723 : Nat.Prime 148723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv3541]) (by decide +kernel)
def pv148723 : PrimeValue := ⟨148723, pr148723⟩
private theorem pr148747 : Nat.Prime 148747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1907]) (by decide +kernel)
def pv148747 : PrimeValue := ⟨148747, pr148747⟩
private theorem pr148763 : Nat.Prime 148763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv74381]) (by decide +kernel)
def pv148763 : PrimeValue := ⟨148763, pr148763⟩
private theorem pr148781 : Nat.Prime 148781 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43,pv173]) (by decide +kernel)
def pv148781 : PrimeValue := ⟨148781, pr148781⟩
private theorem pr148829 : Nat.Prime 148829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv1283]) (by decide +kernel)
def pv148829 : PrimeValue := ⟨148829, pr148829⟩
private theorem pr148853 : Nat.Prime 148853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv199]) (by decide +kernel)
def pv148853 : PrimeValue := ⟨148853, pr148853⟩
private theorem pr148859 : Nat.Prime 148859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv263,pv283]) (by decide +kernel)
def pv148859 : PrimeValue := ⟨148859, pr148859⟩
private theorem pr148861 : Nat.Prime 148861 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv827]) (by decide +kernel)
def pv148861 : PrimeValue := ⟨148861, pr148861⟩
private theorem pr148867 : Nat.Prime 148867 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv577]) (by decide +kernel)
def pv148867 : PrimeValue := ⟨148867, pr148867⟩
private theorem pr148873 : Nat.Prime 148873 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv6203]) (by decide +kernel)
def pv148873 : PrimeValue := ⟨148873, pr148873⟩
private theorem pr148891 : Nat.Prime 148891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv709]) (by decide +kernel)
def pv148891 : PrimeValue := ⟨148891, pr148891⟩
private theorem pr148913 : Nat.Prime 148913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv227]) (by decide +kernel)
def pv148913 : PrimeValue := ⟨148913, pr148913⟩
private theorem pr148921 : Nat.Prime 148921 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv73]) (by decide +kernel)
def pv148921 : PrimeValue := ⟨148921, pr148921⟩
private theorem pr148927 : Nat.Prime 148927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv24821]) (by decide +kernel)
def pv148927 : PrimeValue := ⟨148927, pr148927⟩
private theorem pr148931 : Nat.Prime 148931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv53,pv281]) (by decide +kernel)
def pv148931 : PrimeValue := ⟨148931, pr148931⟩
private theorem pr148933 : Nat.Prime 148933 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv197]) (by decide +kernel)
def pv148933 : PrimeValue := ⟨148933, pr148933⟩
private theorem pr148949 : Nat.Prime 148949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv1619]) (by decide +kernel)
def pv148949 : PrimeValue := ⟨148949, pr148949⟩
private theorem pr148957 : Nat.Prime 148957 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv12413]) (by decide +kernel)
def pv148957 : PrimeValue := ⟨148957, pr148957⟩
private theorem pr148991 : Nat.Prime 148991 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv47,pv317]) (by decide +kernel)
def pv148991 : PrimeValue := ⟨148991, pr148991⟩
private theorem pr149011 : Nat.Prime 149011 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv4967]) (by decide +kernel)
def pv149011 : PrimeValue := ⟨149011, pr149011⟩
private theorem pr149021 : Nat.Prime 149021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7451]) (by decide +kernel)
def pv149021 : PrimeValue := ⟨149021, pr149021⟩
private theorem pr149027 : Nat.Prime 149027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv269,pv277]) (by decide +kernel)
def pv149027 : PrimeValue := ⟨149027, pr149027⟩
private theorem pr149053 : Nat.Prime 149053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12421]) (by decide +kernel)
def pv149053 : PrimeValue := ⟨149053, pr149053⟩
private theorem pr149057 : Nat.Prime 149057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv137]) (by decide +kernel)
def pv149057 : PrimeValue := ⟨149057, pr149057⟩
private theorem pr149059 : Nat.Prime 149059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv149059 : PrimeValue := ⟨149059, pr149059⟩
private theorem pr149087 : Nat.Prime 149087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv23,pv463]) (by decide +kernel)
def pv149087 : PrimeValue := ⟨149087, pr149087⟩
private theorem pr149099 : Nat.Prime 149099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127,pv587]) (by decide +kernel)
def pv149099 : PrimeValue := ⟨149099, pr149099⟩
private theorem pr149111 : Nat.Prime 149111 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv31,pv37]) (by decide +kernel)
def pv149111 : PrimeValue := ⟨149111, pr149111⟩
private theorem pr149113 : Nat.Prime 149113 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv109]) (by decide +kernel)
def pv149113 : PrimeValue := ⟨149113, pr149113⟩
private theorem pr149143 : Nat.Prime 149143 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv53,pv67]) (by decide +kernel)
def pv149143 : PrimeValue := ⟨149143, pr149143⟩
private theorem pr149153 : Nat.Prime 149153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv79]) (by decide +kernel)
def pv149153 : PrimeValue := ⟨149153, pr149153⟩
private theorem pr149159 : Nat.Prime 149159 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv17,pv41,pv107]) (by decide +kernel)
def pv149159 : PrimeValue := ⟨149159, pr149159⟩
private theorem pr149161 : Nat.Prime 149161 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv11,pv113]) (by decide +kernel)
def pv149161 : PrimeValue := ⟨149161, pr149161⟩
private theorem pr149173 : Nat.Prime 149173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv401]) (by decide +kernel)
def pv149173 : PrimeValue := ⟨149173, pr149173⟩
private theorem pr149183 : Nat.Prime 149183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv6781]) (by decide +kernel)
def pv149183 : PrimeValue := ⟨149183, pr149183⟩
private theorem pr149197 : Nat.Prime 149197 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv12433]) (by decide +kernel)
def pv149197 : PrimeValue := ⟨149197, pr149197⟩
private theorem pr149213 : Nat.Prime 149213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv73]) (by decide +kernel)
def pv149213 : PrimeValue := ⟨149213, pr149213⟩
private theorem pr149239 : Nat.Prime 149239 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv8291]) (by decide +kernel)
def pv149239 : PrimeValue := ⟨149239, pr149239⟩
private theorem pr149249 : Nat.Prime 149249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv53]) (by decide +kernel)
def pv149249 : PrimeValue := ⟨149249, pr149249⟩
private theorem pr149251 : Nat.Prime 149251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv199]) (by decide +kernel)
def pv149251 : PrimeValue := ⟨149251, pr149251⟩
private theorem pr149257 : Nat.Prime 149257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv691]) (by decide +kernel)
def pv149257 : PrimeValue := ⟨149257, pr149257⟩
private theorem pr149287 : Nat.Prime 149287 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv139,pv179]) (by decide +kernel)
def pv149287 : PrimeValue := ⟨149287, pr149287⟩
private theorem pr149297 : Nat.Prime 149297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv31,pv43]) (by decide +kernel)
def pv149297 : PrimeValue := ⟨149297, pr149297⟩
private theorem pr149309 : Nat.Prime 149309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163,pv229]) (by decide +kernel)
def pv149309 : PrimeValue := ⟨149309, pr149309⟩
private theorem pr149333 : Nat.Prime 149333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv1009]) (by decide +kernel)
def pv149333 : PrimeValue := ⟨149333, pr149333⟩
private theorem pr149341 : Nat.Prime 149341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv131]) (by decide +kernel)
def pv149341 : PrimeValue := ⟨149341, pr149341⟩
private theorem pr149351 : Nat.Prime 149351 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv29,pv103]) (by decide +kernel)
def pv149351 : PrimeValue := ⟨149351, pr149351⟩
private theorem pr149377 : Nat.Prime 149377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv389]) (by decide +kernel)
def pv149377 : PrimeValue := ⟨149377, pr149377⟩
private theorem pr149381 : Nat.Prime 149381 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv97]) (by decide +kernel)
def pv149381 : PrimeValue := ⟨149381, pr149381⟩
private theorem pr149393 : Nat.Prime 149393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9337]) (by decide +kernel)
def pv149393 : PrimeValue := ⟨149393, pr149393⟩
private theorem pr149399 : Nat.Prime 149399 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv74699]) (by decide +kernel)
def pv149399 : PrimeValue := ⟨149399, pr149399⟩
private theorem pr149411 : Nat.Prime 149411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv67,pv223]) (by decide +kernel)
def pv149411 : PrimeValue := ⟨149411, pr149411⟩
private theorem pr149417 : Nat.Prime 149417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv983]) (by decide +kernel)
def pv149417 : PrimeValue := ⟨149417, pr149417⟩
private theorem pr149419 : Nat.Prime 149419 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2767]) (by decide +kernel)
def pv149419 : PrimeValue := ⟨149419, pr149419⟩
private theorem pr149423 : Nat.Prime 149423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv13,pv821]) (by decide +kernel)
def pv149423 : PrimeValue := ⟨149423, pr149423⟩
private theorem pr149441 : Nat.Prime 149441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv467]) (by decide +kernel)
def pv149441 : PrimeValue := ⟨149441, pr149441⟩
private theorem pr149459 : Nat.Prime 149459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv74729]) (by decide +kernel)
def pv149459 : PrimeValue := ⟨149459, pr149459⟩
private theorem pr149489 : Nat.Prime 149489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9343]) (by decide +kernel)
def pv149489 : PrimeValue := ⟨149489, pr149489⟩
private theorem pr149491 : Nat.Prime 149491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv151]) (by decide +kernel)
def pv149491 : PrimeValue := ⟨149491, pr149491⟩
private theorem pr149497 : Nat.Prime 149497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6229]) (by decide +kernel)
def pv149497 : PrimeValue := ⟨149497, pr149497⟩
private theorem pr149503 : Nat.Prime 149503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv24917]) (by decide +kernel)
def pv149503 : PrimeValue := ⟨149503, pr149503⟩
private theorem pr149519 : Nat.Prime 149519 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv74759]) (by decide +kernel)
def pv149519 : PrimeValue := ⟨149519, pr149519⟩
private theorem pr149521 : Nat.Prime 149521 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv89]) (by decide +kernel)
def pv149521 : PrimeValue := ⟨149521, pr149521⟩
private theorem pr149531 : Nat.Prime 149531 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv787]) (by decide +kernel)
def pv149531 : PrimeValue := ⟨149531, pr149531⟩
private theorem pr149543 : Nat.Prime 149543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv74771]) (by decide +kernel)
def pv149543 : PrimeValue := ⟨149543, pr149543⟩
private theorem pr149551 : Nat.Prime 149551 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv997]) (by decide +kernel)
def pv149551 : PrimeValue := ⟨149551, pr149551⟩
private theorem pr149561 : Nat.Prime 149561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3739]) (by decide +kernel)
def pv149561 : PrimeValue := ⟨149561, pr149561⟩
private theorem pr149563 : Nat.Prime 149563 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1187]) (by decide +kernel)
def pv149563 : PrimeValue := ⟨149563, pr149563⟩
private theorem pr149579 : Nat.Prime 149579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv523]) (by decide +kernel)
def pv149579 : PrimeValue := ⟨149579, pr149579⟩
private theorem pr149623 : Nat.Prime 149623 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv2267]) (by decide +kernel)
def pv149623 : PrimeValue := ⟨149623, pr149623⟩
private theorem pr149627 : Nat.Prime 149627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv947]) (by decide +kernel)
def pv149627 : PrimeValue := ⟨149627, pr149627⟩
private theorem pr149629 : Nat.Prime 149629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv337]) (by decide +kernel)
def pv149629 : PrimeValue := ⟨149629, pr149629⟩
private theorem pr149689 : Nat.Prime 149689 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv149689 : PrimeValue := ⟨149689, pr149689⟩
private theorem pr149713 : Nat.Prime 149713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3119]) (by decide +kernel)
def pv149713 : PrimeValue := ⟨149713, pr149713⟩
private theorem pr149717 : Nat.Prime 149717 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv5347]) (by decide +kernel)
def pv149717 : PrimeValue := ⟨149717, pr149717⟩
private theorem pr149729 : Nat.Prime 149729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4679]) (by decide +kernel)
def pv149729 : PrimeValue := ⟨149729, pr149729⟩
private theorem pr149749 : Nat.Prime 149749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12479]) (by decide +kernel)
def pv149749 : PrimeValue := ⟨149749, pr149749⟩
private theorem pr149759 : Nat.Prime 149759 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv19,pv563]) (by decide +kernel)
def pv149759 : PrimeValue := ⟨149759, pr149759⟩
private theorem pr149767 : Nat.Prime 149767 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv109,pv229]) (by decide +kernel)
def pv149767 : PrimeValue := ⟨149767, pr149767⟩
private theorem pr149791 : Nat.Prime 149791 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv4993]) (by decide +kernel)
def pv149791 : PrimeValue := ⟨149791, pr149791⟩
private theorem pr149803 : Nat.Prime 149803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24967]) (by decide +kernel)
def pv149803 : PrimeValue := ⟨149803, pr149803⟩
private theorem pr149827 : Nat.Prime 149827 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv24971]) (by decide +kernel)
def pv149827 : PrimeValue := ⟨149827, pr149827⟩
private theorem pr149839 : Nat.Prime 149839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv113]) (by decide +kernel)
def pv149839 : PrimeValue := ⟨149839, pr149839⟩
private theorem pr149861 : Nat.Prime 149861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv127]) (by decide +kernel)
def pv149861 : PrimeValue := ⟨149861, pr149861⟩
private theorem pr149867 : Nat.Prime 149867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv74933]) (by decide +kernel)
def pv149867 : PrimeValue := ⟨149867, pr149867⟩
private theorem pr149873 : Nat.Prime 149873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv19,pv29]) (by decide +kernel)
def pv149873 : PrimeValue := ⟨149873, pr149873⟩
private theorem pr149893 : Nat.Prime 149893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12491]) (by decide +kernel)
def pv149893 : PrimeValue := ⟨149893, pr149893⟩
private theorem pr149899 : Nat.Prime 149899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv43,pv83]) (by decide +kernel)
def pv149899 : PrimeValue := ⟨149899, pr149899⟩
private theorem pr149911 : Nat.Prime 149911 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv263]) (by decide +kernel)
def pv149911 : PrimeValue := ⟨149911, pr149911⟩
private theorem pr149921 : Nat.Prime 149921 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv937]) (by decide +kernel)
def pv149921 : PrimeValue := ⟨149921, pr149921⟩
private theorem pr149939 : Nat.Prime 149939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv1229]) (by decide +kernel)
def pv149939 : PrimeValue := ⟨149939, pr149939⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
