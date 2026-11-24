/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table113
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table113.pv524921
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table034
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table078
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table079

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr524921 : Nat.Prime 524921 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv1193]) (by decide +kernel)
def pv524921 : PrimeValue := ⟨524921, pr524921⟩
private theorem pr524933 : Nat.Prime 524933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv6907]) (by decide +kernel)
def pv524933 : PrimeValue := ⟨524933, pr524933⟩
private theorem pr524941 : Nat.Prime 524941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv673]) (by decide +kernel)
def pv524941 : PrimeValue := ⟨524941, pr524941⟩
private theorem pr524947 : Nat.Prime 524947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv87491]) (by decide +kernel)
def pv524947 : PrimeValue := ⟨524947, pr524947⟩
private theorem pr524959 : Nat.Prime 524959 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv29,pv431]) (by decide +kernel)
def pv524959 : PrimeValue := ⟨524959, pr524959⟩
private theorem pr524981 : Nat.Prime 524981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv26249]) (by decide +kernel)
def pv524981 : PrimeValue := ⟨524981, pr524981⟩
private theorem pr524983 : Nat.Prime 524983 :=
  checkPrime_prime (q := pv53) (ls := [pv2,pv3,pv59,pv1483]) (by decide +kernel)
def pv524983 : PrimeValue := ⟨524983, pr524983⟩
private theorem pr524999 : Nat.Prime 524999 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv23,pv101,pv113]) (by decide +kernel)
def pv524999 : PrimeValue := ⟨524999, pr524999⟩
private theorem pr525013 : Nat.Prime 525013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv653]) (by decide +kernel)
def pv525013 : PrimeValue := ⟨525013, pr525013⟩
private theorem pr525043 : Nat.Prime 525043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv463]) (by decide +kernel)
def pv525043 : PrimeValue := ⟨525043, pr525043⟩
private theorem pr525157 : Nat.Prime 525157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv107,pv409]) (by decide +kernel)
def pv525157 : PrimeValue := ⟨525157, pr525157⟩
private theorem pr525257 : Nat.Prime 525257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv65657]) (by decide +kernel)
def pv525257 : PrimeValue := ⟨525257, pr525257⟩
private theorem pr525313 : Nat.Prime 525313 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv525313 : PrimeValue := ⟨525313, pr525313⟩
private theorem pr525361 : Nat.Prime 525361 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv199]) (by decide +kernel)
def pv525361 : PrimeValue := ⟨525361, pr525361⟩
private theorem pr525373 : Nat.Prime 525373 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43781]) (by decide +kernel)
def pv525373 : PrimeValue := ⟨525373, pr525373⟩
private theorem pr525377 : Nat.Prime 525377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv8209]) (by decide +kernel)
def pv525377 : PrimeValue := ⟨525377, pr525377⟩
private theorem pr525433 : Nat.Prime 525433 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv21893]) (by decide +kernel)
def pv525433 : PrimeValue := ⟨525433, pr525433⟩
private theorem pr525461 : Nat.Prime 525461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv43,pv47]) (by decide +kernel)
def pv525461 : PrimeValue := ⟨525461, pr525461⟩
private theorem pr525493 : Nat.Prime 525493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1327]) (by decide +kernel)
def pv525493 : PrimeValue := ⟨525493, pr525493⟩
private theorem pr525517 : Nat.Prime 525517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43793]) (by decide +kernel)
def pv525517 : PrimeValue := ⟨525517, pr525517⟩
private theorem pr525529 : Nat.Prime 525529 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv811]) (by decide +kernel)
def pv525529 : PrimeValue := ⟨525529, pr525529⟩
private theorem pr525583 : Nat.Prime 525583 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv9733]) (by decide +kernel)
def pv525583 : PrimeValue := ⟨525583, pr525583⟩
private theorem pr525607 : Nat.Prime 525607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv5153]) (by decide +kernel)
def pv525607 : PrimeValue := ⟨525607, pr525607⟩
private theorem pr525641 : Nat.Prime 525641 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv773]) (by decide +kernel)
def pv525641 : PrimeValue := ⟨525641, pr525641⟩
private theorem pr525727 : Nat.Prime 525727 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29207]) (by decide +kernel)
def pv525727 : PrimeValue := ⟨525727, pr525727⟩
private theorem pr525731 : Nat.Prime 525731 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv2767]) (by decide +kernel)
def pv525731 : PrimeValue := ⟨525731, pr525731⟩
private theorem pr525809 : Nat.Prime 525809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv557]) (by decide +kernel)
def pv525809 : PrimeValue := ⟨525809, pr525809⟩
private theorem pr525817 : Nat.Prime 525817 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv67,pv109]) (by decide +kernel)
def pv525817 : PrimeValue := ⟨525817, pr525817⟩
private theorem pr525893 : Nat.Prime 525893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv1801]) (by decide +kernel)
def pv525893 : PrimeValue := ⟨525893, pr525893⟩
private theorem pr525913 : Nat.Prime 525913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv1289]) (by decide +kernel)
def pv525913 : PrimeValue := ⟨525913, pr525913⟩
private theorem pr525923 : Nat.Prime 525923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv439,pv599]) (by decide +kernel)
def pv525923 : PrimeValue := ⟨525923, pr525923⟩
private theorem pr525937 : Nat.Prime 525937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv10957]) (by decide +kernel)
def pv525937 : PrimeValue := ⟨525937, pr525937⟩
private theorem pr525949 : Nat.Prime 525949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv1069]) (by decide +kernel)
def pv525949 : PrimeValue := ⟨525949, pr525949⟩
private theorem pr526049 : Nat.Prime 526049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv967]) (by decide +kernel)
def pv526049 : PrimeValue := ⟨526049, pr526049⟩
private theorem pr526139 : Nat.Prime 526139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv503,pv523]) (by decide +kernel)
def pv526139 : PrimeValue := ⟨526139, pr526139⟩
private theorem pr526189 : Nat.Prime 526189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv3373]) (by decide +kernel)
def pv526189 : PrimeValue := ⟨526189, pr526189⟩
private theorem pr526213 : Nat.Prime 526213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv311]) (by decide +kernel)
def pv526213 : PrimeValue := ⟨526213, pr526213⟩
private theorem pr526223 : Nat.Prime 526223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv263111]) (by decide +kernel)
def pv526223 : PrimeValue := ⟨526223, pr526223⟩
private theorem pr526283 : Nat.Prime 526283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv271,pv971]) (by decide +kernel)
def pv526283 : PrimeValue := ⟨526283, pr526283⟩
private theorem pr526297 : Nat.Prime 526297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv21929]) (by decide +kernel)
def pv526297 : PrimeValue := ⟨526297, pr526297⟩
private theorem pr526367 : Nat.Prime 526367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv263183]) (by decide +kernel)
def pv526367 : PrimeValue := ⟨526367, pr526367⟩
private theorem pr526373 : Nat.Prime 526373 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv1709]) (by decide +kernel)
def pv526373 : PrimeValue := ⟨526373, pr526373⟩
private theorem pr526387 : Nat.Prime 526387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv83,pv151]) (by decide +kernel)
def pv526387 : PrimeValue := ⟨526387, pr526387⟩
private theorem pr526423 : Nat.Prime 526423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv397]) (by decide +kernel)
def pv526423 : PrimeValue := ⟨526423, pr526423⟩
private theorem pr526429 : Nat.Prime 526429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2089]) (by decide +kernel)
def pv526429 : PrimeValue := ⟨526429, pr526429⟩
private theorem pr526453 : Nat.Prime 526453 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv2309]) (by decide +kernel)
def pv526453 : PrimeValue := ⟨526453, pr526453⟩
private theorem pr526459 : Nat.Prime 526459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv87743]) (by decide +kernel)
def pv526459 : PrimeValue := ⟨526459, pr526459⟩
private theorem pr526483 : Nat.Prime 526483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv2659]) (by decide +kernel)
def pv526483 : PrimeValue := ⟨526483, pr526483⟩
private theorem pr526511 : Nat.Prime 526511 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv37,pv1423]) (by decide +kernel)
def pv526511 : PrimeValue := ⟨526511, pr526511⟩
private theorem pr526543 : Nat.Prime 526543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv127,pv691]) (by decide +kernel)
def pv526543 : PrimeValue := ⟨526543, pr526543⟩
private theorem pr526573 : Nat.Prime 526573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14627]) (by decide +kernel)
def pv526573 : PrimeValue := ⟨526573, pr526573⟩
private theorem pr526637 : Nat.Prime 526637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv11969]) (by decide +kernel)
def pv526637 : PrimeValue := ⟨526637, pr526637⟩
private theorem pr526651 : Nat.Prime 526651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3511]) (by decide +kernel)
def pv526651 : PrimeValue := ⟨526651, pr526651⟩
private theorem pr526703 : Nat.Prime 526703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv89,pv269]) (by decide +kernel)
def pv526703 : PrimeValue := ⟨526703, pr526703⟩
private theorem pr526717 : Nat.Prime 526717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4877]) (by decide +kernel)
def pv526717 : PrimeValue := ⟨526717, pr526717⟩
private theorem pr526733 : Nat.Prime 526733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv3559]) (by decide +kernel)
def pv526733 : PrimeValue := ⟨526733, pr526733⟩
private theorem pr526759 : Nat.Prime 526759 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv87793]) (by decide +kernel)
def pv526759 : PrimeValue := ⟨526759, pr526759⟩
private theorem pr526777 : Nat.Prime 526777 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv47,pv467]) (by decide +kernel)
def pv526777 : PrimeValue := ⟨526777, pr526777⟩
private theorem pr526781 : Nat.Prime 526781 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv26339]) (by decide +kernel)
def pv526781 : PrimeValue := ⟨526781, pr526781⟩
private theorem pr526837 : Nat.Prime 526837 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv43,pv1021]) (by decide +kernel)
def pv526837 : PrimeValue := ⟨526837, pr526837⟩
private theorem pr526853 : Nat.Prime 526853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv131713]) (by decide +kernel)
def pv526853 : PrimeValue := ⟨526853, pr526853⟩
private theorem pr526871 : Nat.Prime 526871 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv47,pv59]) (by decide +kernel)
def pv526871 : PrimeValue := ⟨526871, pr526871⟩
private theorem pr526913 : Nat.Prime 526913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv8233]) (by decide +kernel)
def pv526913 : PrimeValue := ⟨526913, pr526913⟩
private theorem pr526931 : Nat.Prime 526931 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv23,pv29,pv79]) (by decide +kernel)
def pv526931 : PrimeValue := ⟨526931, pr526931⟩
private theorem pr526951 : Nat.Prime 526951 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1171]) (by decide +kernel)
def pv526951 : PrimeValue := ⟨526951, pr526951⟩
private theorem pr527053 : Nat.Prime 527053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv167,pv263]) (by decide +kernel)
def pv527053 : PrimeValue := ⟨527053, pr527053⟩
private theorem pr527081 : Nat.Prime 527081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13177]) (by decide +kernel)
def pv527081 : PrimeValue := ⟨527081, pr527081⟩
private theorem pr527099 : Nat.Prime 527099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv19,pv97]) (by decide +kernel)
def pv527099 : PrimeValue := ⟨527099, pr527099⟩
private theorem pr527123 : Nat.Prime 527123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv263561]) (by decide +kernel)
def pv527123 : PrimeValue := ⟨527123, pr527123⟩
private theorem pr527129 : Nat.Prime 527129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv9413]) (by decide +kernel)
def pv527129 : PrimeValue := ⟨527129, pr527129⟩
private theorem pr527207 : Nat.Prime 527207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv73,pv157]) (by decide +kernel)
def pv527207 : PrimeValue := ⟨527207, pr527207⟩
private theorem pr527237 : Nat.Prime 527237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv1481]) (by decide +kernel)
def pv527237 : PrimeValue := ⟨527237, pr527237⟩
private theorem pr527281 : Nat.Prime 527281 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv527281 : PrimeValue := ⟨527281, pr527281⟩
private theorem pr527291 : Nat.Prime 527291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv67,pv787]) (by decide +kernel)
def pv527291 : PrimeValue := ⟨527291, pr527291⟩
private theorem pr527333 : Nat.Prime 527333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv10141]) (by decide +kernel)
def pv527333 : PrimeValue := ⟨527333, pr527333⟩
private theorem pr527377 : Nat.Prime 527377 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv10987]) (by decide +kernel)
def pv527377 : PrimeValue := ⟨527377, pr527377⟩
private theorem pr527407 : Nat.Prime 527407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv61,pv131]) (by decide +kernel)
def pv527407 : PrimeValue := ⟨527407, pr527407⟩
private theorem pr527453 : Nat.Prime 527453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv4547]) (by decide +kernel)
def pv527453 : PrimeValue := ⟨527453, pr527453⟩
private theorem pr527533 : Nat.Prime 527533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43961]) (by decide +kernel)
def pv527533 : PrimeValue := ⟨527533, pr527533⟩
private theorem pr527603 : Nat.Prime 527603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv251,pv1051]) (by decide +kernel)
def pv527603 : PrimeValue := ⟨527603, pr527603⟩
private theorem pr527623 : Nat.Prime 527623 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv1871]) (by decide +kernel)
def pv527623 : PrimeValue := ⟨527623, pr527623⟩
private theorem pr527633 : Nat.Prime 527633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv673]) (by decide +kernel)
def pv527633 : PrimeValue := ⟨527633, pr527633⟩
private theorem pr527699 : Nat.Prime 527699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv263849]) (by decide +kernel)
def pv527699 : PrimeValue := ⟨527699, pr527699⟩
private theorem pr527741 : Nat.Prime 527741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv26387]) (by decide +kernel)
def pv527741 : PrimeValue := ⟨527741, pr527741⟩
private theorem pr527753 : Nat.Prime 527753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv1609]) (by decide +kernel)
def pv527753 : PrimeValue := ⟨527753, pr527753⟩
private theorem pr527851 : Nat.Prime 527851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv23]) (by decide +kernel)
def pv527851 : PrimeValue := ⟨527851, pr527851⟩
private theorem pr527983 : Nat.Prime 527983 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv967]) (by decide +kernel)
def pv527983 : PrimeValue := ⟨527983, pr527983⟩
private theorem pr528001 : Nat.Prime 528001 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv528001 : PrimeValue := ⟨528001, pr528001⟩
private theorem pr528013 : Nat.Prime 528013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4889]) (by decide +kernel)
def pv528013 : PrimeValue := ⟨528013, pr528013⟩
private theorem pr528041 : Nat.Prime 528041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43,pv307]) (by decide +kernel)
def pv528041 : PrimeValue := ⟨528041, pr528041⟩
private theorem pr528043 : Nat.Prime 528043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv88007]) (by decide +kernel)
def pv528043 : PrimeValue := ⟨528043, pr528043⟩
private theorem pr528223 : Nat.Prime 528223 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv88037]) (by decide +kernel)
def pv528223 : PrimeValue := ⟨528223, pr528223⟩
private theorem pr528247 : Nat.Prime 528247 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29347]) (by decide +kernel)
def pv528247 : PrimeValue := ⟨528247, pr528247⟩
private theorem pr528299 : Nat.Prime 528299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv6143]) (by decide +kernel)
def pv528299 : PrimeValue := ⟨528299, pr528299⟩
private theorem pr528329 : Nat.Prime 528329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv66041]) (by decide +kernel)
def pv528329 : PrimeValue := ⟨528329, pr528329⟩
private theorem pr528433 : Nat.Prime 528433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv101,pv109]) (by decide +kernel)
def pv528433 : PrimeValue := ⟨528433, pr528433⟩
private theorem pr528487 : Nat.Prime 528487 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv12583]) (by decide +kernel)
def pv528487 : PrimeValue := ⟨528487, pr528487⟩
private theorem pr528509 : Nat.Prime 528509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv3571]) (by decide +kernel)
def pv528509 : PrimeValue := ⟨528509, pr528509⟩
private theorem pr528511 : Nat.Prime 528511 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv79,pv223]) (by decide +kernel)
def pv528511 : PrimeValue := ⟨528511, pr528511⟩
private theorem pr528611 : Nat.Prime 528611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv52861]) (by decide +kernel)
def pv528611 : PrimeValue := ⟨528611, pr528611⟩
private theorem pr528623 : Nat.Prime 528623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv4987]) (by decide +kernel)
def pv528623 : PrimeValue := ⟨528623, pr528623⟩
private theorem pr528631 : Nat.Prime 528631 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv67,pv263]) (by decide +kernel)
def pv528631 : PrimeValue := ⟨528631, pr528631⟩
private theorem pr528667 : Nat.Prime 528667 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv71,pv73]) (by decide +kernel)
def pv528667 : PrimeValue := ⟨528667, pr528667⟩
private theorem pr528707 : Nat.Prime 528707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv264353]) (by decide +kernel)
def pv528707 : PrimeValue := ⟨528707, pr528707⟩
private theorem pr528709 : Nat.Prime 528709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv44059]) (by decide +kernel)
def pv528709 : PrimeValue := ⟨528709, pr528709⟩
private theorem pr528791 : Nat.Prime 528791 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv52879]) (by decide +kernel)
def pv528791 : PrimeValue := ⟨528791, pr528791⟩
private theorem pr528821 : Nat.Prime 528821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv137,pv193]) (by decide +kernel)
def pv528821 : PrimeValue := ⟨528821, pr528821⟩
private theorem pr528877 : Nat.Prime 528877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv83]) (by decide +kernel)
def pv528877 : PrimeValue := ⟨528877, pr528877⟩
private theorem pr528947 : Nat.Prime 528947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv24043]) (by decide +kernel)
def pv528947 : PrimeValue := ⟨528947, pr528947⟩
private theorem pr528967 : Nat.Prime 528967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29387]) (by decide +kernel)
def pv528967 : PrimeValue := ⟨528967, pr528967⟩
private theorem pr529007 : Nat.Prime 529007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv15559]) (by decide +kernel)
def pv529007 : PrimeValue := ⟨529007, pr529007⟩
private theorem pr529027 : Nat.Prime 529027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv2383]) (by decide +kernel)
def pv529027 : PrimeValue := ⟨529027, pr529027⟩
private theorem pr529117 : Nat.Prime 529117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv6299]) (by decide +kernel)
def pv529117 : PrimeValue := ⟨529117, pr529117⟩
private theorem pr529183 : Nat.Prime 529183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29399]) (by decide +kernel)
def pv529183 : PrimeValue := ⟨529183, pr529183⟩
private theorem pr529237 : Nat.Prime 529237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv241]) (by decide +kernel)
def pv529237 : PrimeValue := ⟨529237, pr529237⟩
private theorem pr529271 : Nat.Prime 529271 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv7561]) (by decide +kernel)
def pv529271 : PrimeValue := ⟨529271, pr529271⟩
private theorem pr529313 : Nat.Prime 529313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17,pv139]) (by decide +kernel)
def pv529313 : PrimeValue := ⟨529313, pr529313⟩
private theorem pr529357 : Nat.Prime 529357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv1423]) (by decide +kernel)
def pv529357 : PrimeValue := ⟨529357, pr529357⟩
private theorem pr529393 : Nat.Prime 529393 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv41,pv269]) (by decide +kernel)
def pv529393 : PrimeValue := ⟨529393, pr529393⟩
private theorem pr529603 : Nat.Prime 529603 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv61,pv1447]) (by decide +kernel)
def pv529603 : PrimeValue := ⟨529603, pr529603⟩
private theorem pr529649 : Nat.Prime 529649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv4729]) (by decide +kernel)
def pv529649 : PrimeValue := ⟨529649, pr529649⟩
private theorem pr529657 : Nat.Prime 529657 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv29,pv761]) (by decide +kernel)
def pv529657 : PrimeValue := ⟨529657, pr529657⟩
private theorem pr529693 : Nat.Prime 529693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv1193]) (by decide +kernel)
def pv529693 : PrimeValue := ⟨529693, pr529693⟩
private theorem pr529709 : Nat.Prime 529709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv877]) (by decide +kernel)
def pv529709 : PrimeValue := ⟨529709, pr529709⟩
private theorem pr529751 : Nat.Prime 529751 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv163]) (by decide +kernel)
def pv529751 : PrimeValue := ⟨529751, pr529751⟩
private theorem pr529807 : Nat.Prime 529807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv88301]) (by decide +kernel)
def pv529807 : PrimeValue := ⟨529807, pr529807⟩
private theorem pr529871 : Nat.Prime 529871 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv5,pv11,pv4817]) (by decide +kernel)
def pv529871 : PrimeValue := ⟨529871, pr529871⟩
private theorem pr529957 : Nat.Prime 529957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv701]) (by decide +kernel)
def pv529957 : PrimeValue := ⟨529957, pr529957⟩
private theorem pr529961 : Nat.Prime 529961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13249]) (by decide +kernel)
def pv529961 : PrimeValue := ⟨529961, pr529961⟩
private theorem pr530017 : Nat.Prime 530017 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5521]) (by decide +kernel)
def pv530017 : PrimeValue := ⟨530017, pr530017⟩
private theorem pr530021 : Nat.Prime 530021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv26501]) (by decide +kernel)
def pv530021 : PrimeValue := ⟨530021, pr530021⟩
private theorem pr530087 : Nat.Prime 530087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv71,pv3733]) (by decide +kernel)
def pv530087 : PrimeValue := ⟨530087, pr530087⟩
private theorem pr530093 : Nat.Prime 530093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv132523]) (by decide +kernel)
def pv530093 : PrimeValue := ⟨530093, pr530093⟩
private theorem pr530137 : Nat.Prime 530137 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv199]) (by decide +kernel)
def pv530137 : PrimeValue := ⟨530137, pr530137⟩
private theorem pr530267 : Nat.Prime 530267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv24103]) (by decide +kernel)
def pv530267 : PrimeValue := ⟨530267, pr530267⟩
private theorem pr530333 : Nat.Prime 530333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv709]) (by decide +kernel)
def pv530333 : PrimeValue := ⟨530333, pr530333⟩
private theorem pr530393 : Nat.Prime 530393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv167,pv397]) (by decide +kernel)
def pv530393 : PrimeValue := ⟨530393, pr530393⟩
private theorem pr530443 : Nat.Prime 530443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv47]) (by decide +kernel)
def pv530443 : PrimeValue := ⟨530443, pr530443⟩
private theorem pr530507 : Nat.Prime 530507 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv67,pv107]) (by decide +kernel)
def pv530507 : PrimeValue := ⟨530507, pr530507⟩
private theorem pr530513 : Nat.Prime 530513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv71,pv467]) (by decide +kernel)
def pv530513 : PrimeValue := ⟨530513, pr530513⟩
private theorem pr530713 : Nat.Prime 530713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv530713 : PrimeValue := ⟨530713, pr530713⟩
private theorem pr530741 : Nat.Prime 530741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv17,pv223]) (by decide +kernel)
def pv530741 : PrimeValue := ⟨530741, pr530741⟩
private theorem pr530773 : Nat.Prime 530773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv4021]) (by decide +kernel)
def pv530773 : PrimeValue := ⟨530773, pr530773⟩
private theorem pr530833 : Nat.Prime 530833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11059]) (by decide +kernel)
def pv530833 : PrimeValue := ⟨530833, pr530833⟩
private theorem pr530837 : Nat.Prime 530837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv132709]) (by decide +kernel)
def pv530837 : PrimeValue := ⟨530837, pr530837⟩
private theorem pr530851 : Nat.Prime 530851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3539]) (by decide +kernel)
def pv530851 : PrimeValue := ⟨530851, pr530851⟩
private theorem pr530977 : Nat.Prime 530977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5531]) (by decide +kernel)
def pv530977 : PrimeValue := ⟨530977, pr530977⟩
private theorem pr530983 : Nat.Prime 530983 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv9833]) (by decide +kernel)
def pv530983 : PrimeValue := ⟨530983, pr530983⟩
private theorem pr531017 : Nat.Prime 531017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv66377]) (by decide +kernel)
def pv531017 : PrimeValue := ⟨531017, pr531017⟩
private theorem pr531043 : Nat.Prime 531043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv1321]) (by decide +kernel)
def pv531043 : PrimeValue := ⟨531043, pr531043⟩
private theorem pr531071 : Nat.Prime 531071 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv23,pv2309]) (by decide +kernel)
def pv531071 : PrimeValue := ⟨531071, pr531071⟩
private theorem pr531101 : Nat.Prime 531101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv113]) (by decide +kernel)
def pv531101 : PrimeValue := ⟨531101, pr531101⟩
private theorem pr531163 : Nat.Prime 531163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv1283]) (by decide +kernel)
def pv531163 : PrimeValue := ⟨531163, pr531163⟩
private theorem pr531173 : Nat.Prime 531173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv97]) (by decide +kernel)
def pv531173 : PrimeValue := ⟨531173, pr531173⟩
private theorem pr531203 : Nat.Prime 531203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv1997]) (by decide +kernel)
def pv531203 : PrimeValue := ⟨531203, pr531203⟩
private theorem pr531281 : Nat.Prime 531281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv229]) (by decide +kernel)
def pv531281 : PrimeValue := ⟨531281, pr531281⟩
private theorem pr531299 : Nat.Prime 531299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv211,pv1259]) (by decide +kernel)
def pv531299 : PrimeValue := ⟨531299, pr531299⟩
private theorem pr531343 : Nat.Prime 531343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv4217]) (by decide +kernel)
def pv531343 : PrimeValue := ⟨531343, pr531343⟩
private theorem pr531347 : Nat.Prime 531347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv11551]) (by decide +kernel)
def pv531347 : PrimeValue := ⟨531347, pr531347⟩
private theorem pr531353 : Nat.Prime 531353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv3907]) (by decide +kernel)
def pv531353 : PrimeValue := ⟨531353, pr531353⟩
private theorem pr531521 : Nat.Prime 531521 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv11,pv151]) (by decide +kernel)
def pv531521 : PrimeValue := ⟨531521, pr531521⟩
private theorem pr531571 : Nat.Prime 531571 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv29,pv47]) (by decide +kernel)
def pv531571 : PrimeValue := ⟨531571, pr531571⟩
private theorem pr531613 : Nat.Prime 531613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14767]) (by decide +kernel)
def pv531613 : PrimeValue := ⟨531613, pr531613⟩
private theorem pr531637 : Nat.Prime 531637 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv6329]) (by decide +kernel)
def pv531637 : PrimeValue := ⟨531637, pr531637⟩
private theorem pr531689 : Nat.Prime 531689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv1621]) (by decide +kernel)
def pv531689 : PrimeValue := ⟨531689, pr531689⟩
private theorem pr531701 : Nat.Prime 531701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv409]) (by decide +kernel)
def pv531701 : PrimeValue := ⟨531701, pr531701⟩
private theorem pr531731 : Nat.Prime 531731 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv53173]) (by decide +kernel)
def pv531731 : PrimeValue := ⟨531731, pr531731⟩
private theorem pr531863 : Nat.Prime 531863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv15643]) (by decide +kernel)
def pv531863 : PrimeValue := ⟨531863, pr531863⟩
private theorem pr531877 : Nat.Prime 531877 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv127,pv349]) (by decide +kernel)
def pv531877 : PrimeValue := ⟨531877, pr531877⟩
private theorem pr531901 : Nat.Prime 531901 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv197]) (by decide +kernel)
def pv531901 : PrimeValue := ⟨531901, pr531901⟩
private theorem pr531911 : Nat.Prime 531911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv43,pv1237]) (by decide +kernel)
def pv531911 : PrimeValue := ⟨531911, pr531911⟩
private theorem pr531983 : Nat.Prime 531983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv24181]) (by decide +kernel)
def pv531983 : PrimeValue := ⟨531983, pr531983⟩
private theorem pr532153 : Nat.Prime 532153 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv389]) (by decide +kernel)
def pv532153 : PrimeValue := ⟨532153, pr532153⟩
private theorem pr532183 : Nat.Prime 532183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv12671]) (by decide +kernel)
def pv532183 : PrimeValue := ⟨532183, pr532183⟩
private theorem pr532241 : Nat.Prime 532241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv6653]) (by decide +kernel)
def pv532241 : PrimeValue := ⟨532241, pr532241⟩
private theorem pr532267 : Nat.Prime 532267 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv23,pv29]) (by decide +kernel)
def pv532267 : PrimeValue := ⟨532267, pr532267⟩
private theorem pr532333 : Nat.Prime 532333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv53]) (by decide +kernel)
def pv532333 : PrimeValue := ⟨532333, pr532333⟩
private theorem pr532349 : Nat.Prime 532349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv133087]) (by decide +kernel)
def pv532349 : PrimeValue := ⟨532349, pr532349⟩
private theorem pr532391 : Nat.Prime 532391 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv53239]) (by decide +kernel)
def pv532391 : PrimeValue := ⟨532391, pr532391⟩
private theorem pr532447 : Nat.Prime 532447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv88741]) (by decide +kernel)
def pv532447 : PrimeValue := ⟨532447, pr532447⟩
private theorem pr532523 : Nat.Prime 532523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv266261]) (by decide +kernel)
def pv532523 : PrimeValue := ⟨532523, pr532523⟩
private theorem pr532529 : Nat.Prime 532529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv83,pv401]) (by decide +kernel)
def pv532529 : PrimeValue := ⟨532529, pr532529⟩
private theorem pr532537 : Nat.Prime 532537 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv22189]) (by decide +kernel)
def pv532537 : PrimeValue := ⟨532537, pr532537⟩
private theorem pr532739 : Nat.Prime 532739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv266369]) (by decide +kernel)
def pv532739 : PrimeValue := ⟨532739, pr532739⟩
private theorem pr532751 : Nat.Prime 532751 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv2131]) (by decide +kernel)
def pv532751 : PrimeValue := ⟨532751, pr532751⟩
private theorem pr532783 : Nat.Prime 532783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29599]) (by decide +kernel)
def pv532783 : PrimeValue := ⟨532783, pr532783⟩
private theorem pr532823 : Nat.Prime 532823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv266411]) (by decide +kernel)
def pv532823 : PrimeValue := ⟨532823, pr532823⟩
private theorem pr532867 : Nat.Prime 532867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv88811]) (by decide +kernel)
def pv532867 : PrimeValue := ⟨532867, pr532867⟩
private theorem pr532919 : Nat.Prime 532919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv41,pv67,pv97]) (by decide +kernel)
def pv532919 : PrimeValue := ⟨532919, pr532919⟩
private theorem pr532949 : Nat.Prime 532949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv37,pv277]) (by decide +kernel)
def pv532949 : PrimeValue := ⟨532949, pr532949⟩
private theorem pr532951 : Nat.Prime 532951 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv11,pv17,pv19]) (by decide +kernel)
def pv532951 : PrimeValue := ⟨532951, pr532951⟩
private theorem pr533011 : Nat.Prime 533011 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv109,pv163]) (by decide +kernel)
def pv533011 : PrimeValue := ⟨533011, pr533011⟩
private theorem pr533033 : Nat.Prime 533033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv66629]) (by decide +kernel)
def pv533033 : PrimeValue := ⟨533033, pr533033⟩
private theorem pr533053 : Nat.Prime 533053 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv13,pv17,pv67]) (by decide +kernel)
def pv533053 : PrimeValue := ⟨533053, pr533053⟩
private theorem pr533077 : Nat.Prime 533077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv1433]) (by decide +kernel)
def pv533077 : PrimeValue := ⟨533077, pr533077⟩
private theorem pr533111 : Nat.Prime 533111 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv89,pv599]) (by decide +kernel)
def pv533111 : PrimeValue := ⟨533111, pr533111⟩
private theorem pr533189 : Nat.Prime 533189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv7841]) (by decide +kernel)
def pv533189 : PrimeValue := ⟨533189, pr533189⟩
private theorem pr533257 : Nat.Prime 533257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv1307]) (by decide +kernel)
def pv533257 : PrimeValue := ⟨533257, pr533257⟩
private theorem pr533261 : Nat.Prime 533261 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv293]) (by decide +kernel)
def pv533261 : PrimeValue := ⟨533261, pr533261⟩
private theorem pr533321 : Nat.Prime 533321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv67,pv199]) (by decide +kernel)
def pv533321 : PrimeValue := ⟨533321, pr533321⟩
private theorem pr533353 : Nat.Prime 533353 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv71,pv313]) (by decide +kernel)
def pv533353 : PrimeValue := ⟨533353, pr533353⟩
private theorem pr533413 : Nat.Prime 533413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv449]) (by decide +kernel)
def pv533413 : PrimeValue := ⟨533413, pr533413⟩
private theorem pr533543 : Nat.Prime 533543 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv29,pv9199]) (by decide +kernel)
def pv533543 : PrimeValue := ⟨533543, pr533543⟩
private theorem pr533573 : Nat.Prime 533573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv31,pv331]) (by decide +kernel)
def pv533573 : PrimeValue := ⟨533573, pr533573⟩
private theorem pr533581 : Nat.Prime 533581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv8893]) (by decide +kernel)
def pv533581 : PrimeValue := ⟨533581, pr533581⟩
private theorem pr533593 : Nat.Prime 533593 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7411]) (by decide +kernel)
def pv533593 : PrimeValue := ⟨533593, pr533593⟩
private theorem pr533633 : Nat.Prime 533633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv379]) (by decide +kernel)
def pv533633 : PrimeValue := ⟨533633, pr533633⟩
private theorem pr533671 : Nat.Prime 533671 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv17789]) (by decide +kernel)
def pv533671 : PrimeValue := ⟨533671, pr533671⟩
private theorem pr533693 : Nat.Prime 533693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv5801]) (by decide +kernel)
def pv533693 : PrimeValue := ⟨533693, pr533693⟩
private theorem pr533737 : Nat.Prime 533737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv353]) (by decide +kernel)
def pv533737 : PrimeValue := ⟨533737, pr533737⟩
private theorem pr533747 : Nat.Prime 533747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103,pv2591]) (by decide +kernel)
def pv533747 : PrimeValue := ⟨533747, pr533747⟩
private theorem pr533777 : Nat.Prime 533777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv73,pv457]) (by decide +kernel)
def pv533777 : PrimeValue := ⟨533777, pr533777⟩
private theorem pr533893 : Nat.Prime 533893 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv44491]) (by decide +kernel)
def pv533893 : PrimeValue := ⟨533893, pr533893⟩
private theorem pr533921 : Nat.Prime 533921 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv47,pv71]) (by decide +kernel)
def pv533921 : PrimeValue := ⟨533921, pr533921⟩
private theorem pr533969 : Nat.Prime 533969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv1451]) (by decide +kernel)
def pv533969 : PrimeValue := ⟨533969, pr533969⟩
private theorem pr533989 : Nat.Prime 533989 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv13,pv163]) (by decide +kernel)
def pv533989 : PrimeValue := ⟨533989, pr533989⟩
private theorem pr533993 : Nat.Prime 533993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv66749]) (by decide +kernel)
def pv533993 : PrimeValue := ⟨533993, pr533993⟩
private theorem pr533999 : Nat.Prime 533999 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv266999]) (by decide +kernel)
def pv533999 : PrimeValue := ⟨533999, pr533999⟩
private theorem pr534019 : Nat.Prime 534019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv89003]) (by decide +kernel)
def pv534019 : PrimeValue := ⟨534019, pr534019⟩
private theorem pr534043 : Nat.Prime 534043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29669]) (by decide +kernel)
def pv534043 : PrimeValue := ⟨534043, pr534043⟩
private theorem pr534047 : Nat.Prime 534047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv257,pv1039]) (by decide +kernel)
def pv534047 : PrimeValue := ⟨534047, pr534047⟩
private theorem pr534077 : Nat.Prime 534077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv133519]) (by decide +kernel)
def pv534077 : PrimeValue := ⟨534077, pr534077⟩
private theorem pr534101 : Nat.Prime 534101 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv5,pv7,pv109]) (by decide +kernel)
def pv534101 : PrimeValue := ⟨534101, pr534101⟩
private theorem pr534113 : Nat.Prime 534113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv16691]) (by decide +kernel)
def pv534113 : PrimeValue := ⟨534113, pr534113⟩
private theorem pr534167 : Nat.Prime 534167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv14057]) (by decide +kernel)
def pv534167 : PrimeValue := ⟨534167, pr534167⟩
private theorem pr534173 : Nat.Prime 534173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv133543]) (by decide +kernel)
def pv534173 : PrimeValue := ⟨534173, pr534173⟩
private theorem pr534203 : Nat.Prime 534203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv5683]) (by decide +kernel)
def pv534203 : PrimeValue := ⟨534203, pr534203⟩
private theorem pr534253 : Nat.Prime 534253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv211]) (by decide +kernel)
def pv534253 : PrimeValue := ⟨534253, pr534253⟩
private theorem pr534283 : Nat.Prime 534283 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv12721]) (by decide +kernel)
def pv534283 : PrimeValue := ⟨534283, pr534283⟩
private theorem pr534371 : Nat.Prime 534371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv53437]) (by decide +kernel)
def pv534371 : PrimeValue := ⟨534371, pr534371⟩
private theorem pr534403 : Nat.Prime 534403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv2699]) (by decide +kernel)
def pv534403 : PrimeValue := ⟨534403, pr534403⟩
private theorem pr534607 : Nat.Prime 534607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv89101]) (by decide +kernel)
def pv534607 : PrimeValue := ⟨534607, pr534607⟩
private theorem pr534697 : Nat.Prime 534697 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv22279]) (by decide +kernel)
def pv534697 : PrimeValue := ⟨534697, pr534697⟩
private theorem pr534811 : Nat.Prime 534811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17827]) (by decide +kernel)
def pv534811 : PrimeValue := ⟨534811, pr534811⟩
private theorem pr534913 : Nat.Prime 534913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv199]) (by decide +kernel)
def pv534913 : PrimeValue := ⟨534913, pr534913⟩
private theorem pr535019 : Nat.Prime 535019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv83,pv293]) (by decide +kernel)
def pv535019 : PrimeValue := ⟨535019, pr535019⟩
private theorem pr535033 : Nat.Prime 535033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2477]) (by decide +kernel)
def pv535033 : PrimeValue := ⟨535033, pr535033⟩
private theorem pr535037 : Nat.Prime 535037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv181,pv739]) (by decide +kernel)
def pv535037 : PrimeValue := ⟨535037, pr535037⟩
private theorem pr535103 : Nat.Prime 535103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv267551]) (by decide +kernel)
def pv535103 : PrimeValue := ⟨535103, pr535103⟩
private theorem pr535159 : Nat.Prime 535159 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv2287]) (by decide +kernel)
def pv535159 : PrimeValue := ⟨535159, pr535159⟩
private theorem pr535169 : Nat.Prime 535169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv113]) (by decide +kernel)
def pv535169 : PrimeValue := ⟨535169, pr535169⟩
private theorem pr535219 : Nat.Prime 535219 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv89203]) (by decide +kernel)
def pv535219 : PrimeValue := ⟨535219, pr535219⟩
private theorem pr535243 : Nat.Prime 535243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv2411]) (by decide +kernel)
def pv535243 : PrimeValue := ⟨535243, pr535243⟩
private theorem pr535273 : Nat.Prime 535273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv22303]) (by decide +kernel)
def pv535273 : PrimeValue := ⟨535273, pr535273⟩
private theorem pr535303 : Nat.Prime 535303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv431]) (by decide +kernel)
def pv535303 : PrimeValue := ⟨535303, pr535303⟩
private theorem pr535333 : Nat.Prime 535333 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv6373]) (by decide +kernel)
def pv535333 : PrimeValue := ⟨535333, pr535333⟩
private theorem pr535387 : Nat.Prime 535387 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv89231]) (by decide +kernel)
def pv535387 : PrimeValue := ⟨535387, pr535387⟩
private theorem pr535391 : Nat.Prime 535391 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv37,pv1447]) (by decide +kernel)
def pv535391 : PrimeValue := ⟨535391, pr535391⟩
private theorem pr535511 : Nat.Prime 535511 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv53551]) (by decide +kernel)
def pv535511 : PrimeValue := ⟨535511, pr535511⟩
private theorem pr535523 : Nat.Prime 535523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv43,pv479]) (by decide +kernel)
def pv535523 : PrimeValue := ⟨535523, pr535523⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
