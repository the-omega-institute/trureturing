/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table008
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table008.pv17393
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table004

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr17393 : Nat.Prime 17393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1087]) (by decide +kernel)
def pv17393 : PrimeValue := ⟨17393, pr17393⟩
private theorem pr17401 : Nat.Prime 17401 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv17401 : PrimeValue := ⟨17401, pr17401⟩
private theorem pr17417 : Nat.Prime 17417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv311]) (by decide +kernel)
def pv17417 : PrimeValue := ⟨17417, pr17417⟩
private theorem pr17419 : Nat.Prime 17419 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2903]) (by decide +kernel)
def pv17419 : PrimeValue := ⟨17419, pr17419⟩
private theorem pr17431 : Nat.Prime 17431 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv83]) (by decide +kernel)
def pv17431 : PrimeValue := ⟨17431, pr17431⟩
private theorem pr17443 : Nat.Prime 17443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv19]) (by decide +kernel)
def pv17443 : PrimeValue := ⟨17443, pr17443⟩
private theorem pr17449 : Nat.Prime 17449 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv727]) (by decide +kernel)
def pv17449 : PrimeValue := ⟨17449, pr17449⟩
private theorem pr17467 : Nat.Prime 17467 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv71]) (by decide +kernel)
def pv17467 : PrimeValue := ⟨17467, pr17467⟩
private theorem pr17471 : Nat.Prime 17471 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv1747]) (by decide +kernel)
def pv17471 : PrimeValue := ⟨17471, pr17471⟩
private theorem pr17477 : Nat.Prime 17477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv257]) (by decide +kernel)
def pv17477 : PrimeValue := ⟨17477, pr17477⟩
private theorem pr17483 : Nat.Prime 17483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8741]) (by decide +kernel)
def pv17483 : PrimeValue := ⟨17483, pr17483⟩
private theorem pr17489 : Nat.Prime 17489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1093]) (by decide +kernel)
def pv17489 : PrimeValue := ⟨17489, pr17489⟩
private theorem pr17491 : Nat.Prime 17491 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv53]) (by decide +kernel)
def pv17491 : PrimeValue := ⟨17491, pr17491⟩
private theorem pr17497 : Nat.Prime 17497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv17497 : PrimeValue := ⟨17497, pr17497⟩
private theorem pr17509 : Nat.Prime 17509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1459]) (by decide +kernel)
def pv17509 : PrimeValue := ⟨17509, pr17509⟩
private theorem pr17519 : Nat.Prime 17519 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv19,pv461]) (by decide +kernel)
def pv17519 : PrimeValue := ⟨17519, pr17519⟩
private theorem pr17539 : Nat.Prime 17539 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv79]) (by decide +kernel)
def pv17539 : PrimeValue := ⟨17539, pr17539⟩
private theorem pr17551 : Nat.Prime 17551 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv17551 : PrimeValue := ⟨17551, pr17551⟩
private theorem pr17569 : Nat.Prime 17569 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv17569 : PrimeValue := ⟨17569, pr17569⟩
private theorem pr17573 : Nat.Prime 17573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv191]) (by decide +kernel)
def pv17573 : PrimeValue := ⟨17573, pr17573⟩
private theorem pr17579 : Nat.Prime 17579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv47]) (by decide +kernel)
def pv17579 : PrimeValue := ⟨17579, pr17579⟩
private theorem pr17581 : Nat.Prime 17581 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv293]) (by decide +kernel)
def pv17581 : PrimeValue := ⟨17581, pr17581⟩
private theorem pr17597 : Nat.Prime 17597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv83]) (by decide +kernel)
def pv17597 : PrimeValue := ⟨17597, pr17597⟩
private theorem pr17599 : Nat.Prime 17599 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv419]) (by decide +kernel)
def pv17599 : PrimeValue := ⟨17599, pr17599⟩
private theorem pr17609 : Nat.Prime 17609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv71]) (by decide +kernel)
def pv17609 : PrimeValue := ⟨17609, pr17609⟩
private theorem pr17623 : Nat.Prime 17623 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv89]) (by decide +kernel)
def pv17623 : PrimeValue := ⟨17623, pr17623⟩
private theorem pr17627 : Nat.Prime 17627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1259]) (by decide +kernel)
def pv17627 : PrimeValue := ⟨17627, pr17627⟩
private theorem pr17657 : Nat.Prime 17657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2207]) (by decide +kernel)
def pv17657 : PrimeValue := ⟨17657, pr17657⟩
private theorem pr17659 : Nat.Prime 17659 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv109]) (by decide +kernel)
def pv17659 : PrimeValue := ⟨17659, pr17659⟩
private theorem pr17669 : Nat.Prime 17669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv631]) (by decide +kernel)
def pv17669 : PrimeValue := ⟨17669, pr17669⟩
private theorem pr17681 : Nat.Prime 17681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv17]) (by decide +kernel)
def pv17681 : PrimeValue := ⟨17681, pr17681⟩
private theorem pr17683 : Nat.Prime 17683 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv421]) (by decide +kernel)
def pv17683 : PrimeValue := ⟨17683, pr17683⟩
private theorem pr17707 : Nat.Prime 17707 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv227]) (by decide +kernel)
def pv17707 : PrimeValue := ⟨17707, pr17707⟩
private theorem pr17713 : Nat.Prime 17713 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv17713 : PrimeValue := ⟨17713, pr17713⟩
private theorem pr17729 : Nat.Prime 17729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv277]) (by decide +kernel)
def pv17729 : PrimeValue := ⟨17729, pr17729⟩
private theorem pr17737 : Nat.Prime 17737 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv739]) (by decide +kernel)
def pv17737 : PrimeValue := ⟨17737, pr17737⟩
private theorem pr17747 : Nat.Prime 17747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv467]) (by decide +kernel)
def pv17747 : PrimeValue := ⟨17747, pr17747⟩
private theorem pr17749 : Nat.Prime 17749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv29]) (by decide +kernel)
def pv17749 : PrimeValue := ⟨17749, pr17749⟩
private theorem pr17761 : Nat.Prime 17761 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv17761 : PrimeValue := ⟨17761, pr17761⟩
private theorem pr17783 : Nat.Prime 17783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv523]) (by decide +kernel)
def pv17783 : PrimeValue := ⟨17783, pr17783⟩
private theorem pr17789 : Nat.Prime 17789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv4447]) (by decide +kernel)
def pv17789 : PrimeValue := ⟨17789, pr17789⟩
private theorem pr17791 : Nat.Prime 17791 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv593]) (by decide +kernel)
def pv17791 : PrimeValue := ⟨17791, pr17791⟩
private theorem pr17807 : Nat.Prime 17807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv307]) (by decide +kernel)
def pv17807 : PrimeValue := ⟨17807, pr17807⟩
private theorem pr17827 : Nat.Prime 17827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2971]) (by decide +kernel)
def pv17827 : PrimeValue := ⟨17827, pr17827⟩
private theorem pr17837 : Nat.Prime 17837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13]) (by decide +kernel)
def pv17837 : PrimeValue := ⟨17837, pr17837⟩
private theorem pr17839 : Nat.Prime 17839 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv991]) (by decide +kernel)
def pv17839 : PrimeValue := ⟨17839, pr17839⟩
private theorem pr17851 : Nat.Prime 17851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv17851 : PrimeValue := ⟨17851, pr17851⟩
private theorem pr17863 : Nat.Prime 17863 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv13,pv229]) (by decide +kernel)
def pv17863 : PrimeValue := ⟨17863, pr17863⟩
private theorem pr17881 : Nat.Prime 17881 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv149]) (by decide +kernel)
def pv17881 : PrimeValue := ⟨17881, pr17881⟩
private theorem pr17891 : Nat.Prime 17891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1789]) (by decide +kernel)
def pv17891 : PrimeValue := ⟨17891, pr17891⟩
private theorem pr17903 : Nat.Prime 17903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv8951]) (by decide +kernel)
def pv17903 : PrimeValue := ⟨17903, pr17903⟩
private theorem pr17909 : Nat.Prime 17909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv37]) (by decide +kernel)
def pv17909 : PrimeValue := ⟨17909, pr17909⟩
private theorem pr17911 : Nat.Prime 17911 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv199]) (by decide +kernel)
def pv17911 : PrimeValue := ⟨17911, pr17911⟩
private theorem pr17921 : Nat.Prime 17921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv17921 : PrimeValue := ⟨17921, pr17921⟩
private theorem pr17923 : Nat.Prime 17923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv103]) (by decide +kernel)
def pv17923 : PrimeValue := ⟨17923, pr17923⟩
private theorem pr17929 : Nat.Prime 17929 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv17929 : PrimeValue := ⟨17929, pr17929⟩
private theorem pr17939 : Nat.Prime 17939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8969]) (by decide +kernel)
def pv17939 : PrimeValue := ⟨17939, pr17939⟩
private theorem pr17957 : Nat.Prime 17957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67]) (by decide +kernel)
def pv17957 : PrimeValue := ⟨17957, pr17957⟩
private theorem pr17959 : Nat.Prime 17959 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv41,pv73]) (by decide +kernel)
def pv17959 : PrimeValue := ⟨17959, pr17959⟩
private theorem pr17971 : Nat.Prime 17971 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv599]) (by decide +kernel)
def pv17971 : PrimeValue := ⟨17971, pr17971⟩
private theorem pr17977 : Nat.Prime 17977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv107]) (by decide +kernel)
def pv17977 : PrimeValue := ⟨17977, pr17977⟩
private theorem pr17981 : Nat.Prime 17981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv31]) (by decide +kernel)
def pv17981 : PrimeValue := ⟨17981, pr17981⟩
private theorem pr17987 : Nat.Prime 17987 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv23]) (by decide +kernel)
def pv17987 : PrimeValue := ⟨17987, pr17987⟩
private theorem pr17989 : Nat.Prime 17989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1499]) (by decide +kernel)
def pv17989 : PrimeValue := ⟨17989, pr17989⟩
private theorem pr18013 : Nat.Prime 18013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv79]) (by decide +kernel)
def pv18013 : PrimeValue := ⟨18013, pr18013⟩
private theorem pr18041 : Nat.Prime 18041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv41]) (by decide +kernel)
def pv18041 : PrimeValue := ⟨18041, pr18041⟩
private theorem pr18043 : Nat.Prime 18043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv97]) (by decide +kernel)
def pv18043 : PrimeValue := ⟨18043, pr18043⟩
private theorem pr18047 : Nat.Prime 18047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv1289]) (by decide +kernel)
def pv18047 : PrimeValue := ⟨18047, pr18047⟩
private theorem pr18049 : Nat.Prime 18049 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv18049 : PrimeValue := ⟨18049, pr18049⟩
private theorem pr18059 : Nat.Prime 18059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9029]) (by decide +kernel)
def pv18059 : PrimeValue := ⟨18059, pr18059⟩
private theorem pr18061 : Nat.Prime 18061 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv43]) (by decide +kernel)
def pv18061 : PrimeValue := ⟨18061, pr18061⟩
private theorem pr18077 : Nat.Prime 18077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv4519]) (by decide +kernel)
def pv18077 : PrimeValue := ⟨18077, pr18077⟩
private theorem pr18089 : Nat.Prime 18089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17,pv19]) (by decide +kernel)
def pv18089 : PrimeValue := ⟨18089, pr18089⟩
private theorem pr18097 : Nat.Prime 18097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv29]) (by decide +kernel)
def pv18097 : PrimeValue := ⟨18097, pr18097⟩
private theorem pr18119 : Nat.Prime 18119 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv9059]) (by decide +kernel)
def pv18119 : PrimeValue := ⟨18119, pr18119⟩
private theorem pr18121 : Nat.Prime 18121 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv151]) (by decide +kernel)
def pv18121 : PrimeValue := ⟨18121, pr18121⟩
private theorem pr18127 : Nat.Prime 18127 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv53]) (by decide +kernel)
def pv18127 : PrimeValue := ⟨18127, pr18127⟩
private theorem pr18131 : Nat.Prime 18131 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv37]) (by decide +kernel)
def pv18131 : PrimeValue := ⟨18131, pr18131⟩
private theorem pr18133 : Nat.Prime 18133 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1511]) (by decide +kernel)
def pv18133 : PrimeValue := ⟨18133, pr18133⟩
private theorem pr18143 : Nat.Prime 18143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv193]) (by decide +kernel)
def pv18143 : PrimeValue := ⟨18143, pr18143⟩
private theorem pr18149 : Nat.Prime 18149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv349]) (by decide +kernel)
def pv18149 : PrimeValue := ⟨18149, pr18149⟩
private theorem pr18169 : Nat.Prime 18169 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv757]) (by decide +kernel)
def pv18169 : PrimeValue := ⟨18169, pr18169⟩
private theorem pr18181 : Nat.Prime 18181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv101]) (by decide +kernel)
def pv18181 : PrimeValue := ⟨18181, pr18181⟩
private theorem pr18191 : Nat.Prime 18191 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv17,pv107]) (by decide +kernel)
def pv18191 : PrimeValue := ⟨18191, pr18191⟩
private theorem pr18199 : Nat.Prime 18199 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv337]) (by decide +kernel)
def pv18199 : PrimeValue := ⟨18199, pr18199⟩
private theorem pr18211 : Nat.Prime 18211 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv607]) (by decide +kernel)
def pv18211 : PrimeValue := ⟨18211, pr18211⟩
private theorem pr18217 : Nat.Prime 18217 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv18217 : PrimeValue := ⟨18217, pr18217⟩
private theorem pr18223 : Nat.Prime 18223 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3037]) (by decide +kernel)
def pv18223 : PrimeValue := ⟨18223, pr18223⟩
private theorem pr18229 : Nat.Prime 18229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv18229 : PrimeValue := ⟨18229, pr18229⟩
private theorem pr18233 : Nat.Prime 18233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv53]) (by decide +kernel)
def pv18233 : PrimeValue := ⟨18233, pr18233⟩
private theorem pr18251 : Nat.Prime 18251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv73]) (by decide +kernel)
def pv18251 : PrimeValue := ⟨18251, pr18251⟩
private theorem pr18253 : Nat.Prime 18253 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv18253 : PrimeValue := ⟨18253, pr18253⟩
private theorem pr18257 : Nat.Prime 18257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv163]) (by decide +kernel)
def pv18257 : PrimeValue := ⟨18257, pr18257⟩
private theorem pr18269 : Nat.Prime 18269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv4567]) (by decide +kernel)
def pv18269 : PrimeValue := ⟨18269, pr18269⟩
private theorem pr18287 : Nat.Prime 18287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv223]) (by decide +kernel)
def pv18287 : PrimeValue := ⟨18287, pr18287⟩
private theorem pr18289 : Nat.Prime 18289 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv127]) (by decide +kernel)
def pv18289 : PrimeValue := ⟨18289, pr18289⟩
private theorem pr18301 : Nat.Prime 18301 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv18301 : PrimeValue := ⟨18301, pr18301⟩
private theorem pr18307 : Nat.Prime 18307 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv113]) (by decide +kernel)
def pv18307 : PrimeValue := ⟨18307, pr18307⟩
private theorem pr18311 : Nat.Prime 18311 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv1831]) (by decide +kernel)
def pv18311 : PrimeValue := ⟨18311, pr18311⟩
private theorem pr18313 : Nat.Prime 18313 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv109]) (by decide +kernel)
def pv18313 : PrimeValue := ⟨18313, pr18313⟩
private theorem pr18329 : Nat.Prime 18329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv79]) (by decide +kernel)
def pv18329 : PrimeValue := ⟨18329, pr18329⟩
private theorem pr18341 : Nat.Prime 18341 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv131]) (by decide +kernel)
def pv18341 : PrimeValue := ⟨18341, pr18341⟩
private theorem pr18353 : Nat.Prime 18353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv37]) (by decide +kernel)
def pv18353 : PrimeValue := ⟨18353, pr18353⟩
private theorem pr18367 : Nat.Prime 18367 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3061]) (by decide +kernel)
def pv18367 : PrimeValue := ⟨18367, pr18367⟩
private theorem pr18371 : Nat.Prime 18371 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv167]) (by decide +kernel)
def pv18371 : PrimeValue := ⟨18371, pr18371⟩
private theorem pr18379 : Nat.Prime 18379 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1021]) (by decide +kernel)
def pv18379 : PrimeValue := ⟨18379, pr18379⟩
private theorem pr18397 : Nat.Prime 18397 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv73]) (by decide +kernel)
def pv18397 : PrimeValue := ⟨18397, pr18397⟩
private theorem pr18401 : Nat.Prime 18401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23]) (by decide +kernel)
def pv18401 : PrimeValue := ⟨18401, pr18401⟩
private theorem pr18413 : Nat.Prime 18413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv4603]) (by decide +kernel)
def pv18413 : PrimeValue := ⟨18413, pr18413⟩
private theorem pr18427 : Nat.Prime 18427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv83]) (by decide +kernel)
def pv18427 : PrimeValue := ⟨18427, pr18427⟩
private theorem pr18433 : Nat.Prime 18433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv18433 : PrimeValue := ⟨18433, pr18433⟩
private theorem pr18439 : Nat.Prime 18439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv439]) (by decide +kernel)
def pv18439 : PrimeValue := ⟨18439, pr18439⟩
private theorem pr18443 : Nat.Prime 18443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9221]) (by decide +kernel)
def pv18443 : PrimeValue := ⟨18443, pr18443⟩
private theorem pr18451 : Nat.Prime 18451 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv18451 : PrimeValue := ⟨18451, pr18451⟩
private theorem pr18457 : Nat.Prime 18457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv769]) (by decide +kernel)
def pv18457 : PrimeValue := ⟨18457, pr18457⟩
private theorem pr18461 : Nat.Prime 18461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv71]) (by decide +kernel)
def pv18461 : PrimeValue := ⟨18461, pr18461⟩
private theorem pr18481 : Nat.Prime 18481 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv18481 : PrimeValue := ⟨18481, pr18481⟩
private theorem pr18493 : Nat.Prime 18493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv67]) (by decide +kernel)
def pv18493 : PrimeValue := ⟨18493, pr18493⟩
private theorem pr18503 : Nat.Prime 18503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv29]) (by decide +kernel)
def pv18503 : PrimeValue := ⟨18503, pr18503⟩
private theorem pr18517 : Nat.Prime 18517 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1543]) (by decide +kernel)
def pv18517 : PrimeValue := ⟨18517, pr18517⟩
private theorem pr18521 : Nat.Prime 18521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv463]) (by decide +kernel)
def pv18521 : PrimeValue := ⟨18521, pr18521⟩
private theorem pr18523 : Nat.Prime 18523 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv18523 : PrimeValue := ⟨18523, pr18523⟩
private theorem pr18539 : Nat.Prime 18539 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv13,pv23,pv31]) (by decide +kernel)
def pv18539 : PrimeValue := ⟨18539, pr18539⟩
private theorem pr18541 : Nat.Prime 18541 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv103]) (by decide +kernel)
def pv18541 : PrimeValue := ⟨18541, pr18541⟩
private theorem pr18553 : Nat.Prime 18553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv773]) (by decide +kernel)
def pv18553 : PrimeValue := ⟨18553, pr18553⟩
private theorem pr18583 : Nat.Prime 18583 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv163]) (by decide +kernel)
def pv18583 : PrimeValue := ⟨18583, pr18583⟩
private theorem pr18587 : Nat.Prime 18587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9293]) (by decide +kernel)
def pv18587 : PrimeValue := ⟨18587, pr18587⟩
private theorem pr18593 : Nat.Prime 18593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv83]) (by decide +kernel)
def pv18593 : PrimeValue := ⟨18593, pr18593⟩
private theorem pr18617 : Nat.Prime 18617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv179]) (by decide +kernel)
def pv18617 : PrimeValue := ⟨18617, pr18617⟩
private theorem pr18637 : Nat.Prime 18637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1553]) (by decide +kernel)
def pv18637 : PrimeValue := ⟨18637, pr18637⟩
private theorem pr18661 : Nat.Prime 18661 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv311]) (by decide +kernel)
def pv18661 : PrimeValue := ⟨18661, pr18661⟩
private theorem pr18671 : Nat.Prime 18671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv1867]) (by decide +kernel)
def pv18671 : PrimeValue := ⟨18671, pr18671⟩
private theorem pr18679 : Nat.Prime 18679 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv283]) (by decide +kernel)
def pv18679 : PrimeValue := ⟨18679, pr18679⟩
private theorem pr18691 : Nat.Prime 18691 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv89]) (by decide +kernel)
def pv18691 : PrimeValue := ⟨18691, pr18691⟩
private theorem pr18701 : Nat.Prime 18701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv17]) (by decide +kernel)
def pv18701 : PrimeValue := ⟨18701, pr18701⟩
private theorem pr18713 : Nat.Prime 18713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2339]) (by decide +kernel)
def pv18713 : PrimeValue := ⟨18713, pr18713⟩
private theorem pr18719 : Nat.Prime 18719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv191]) (by decide +kernel)
def pv18719 : PrimeValue := ⟨18719, pr18719⟩
private theorem pr18731 : Nat.Prime 18731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1873]) (by decide +kernel)
def pv18731 : PrimeValue := ⟨18731, pr18731⟩
private theorem pr18743 : Nat.Prime 18743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv9371]) (by decide +kernel)
def pv18743 : PrimeValue := ⟨18743, pr18743⟩
private theorem pr18749 : Nat.Prime 18749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv109]) (by decide +kernel)
def pv18749 : PrimeValue := ⟨18749, pr18749⟩
private theorem pr18757 : Nat.Prime 18757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv521]) (by decide +kernel)
def pv18757 : PrimeValue := ⟨18757, pr18757⟩
private theorem pr18773 : Nat.Prime 18773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv19]) (by decide +kernel)
def pv18773 : PrimeValue := ⟨18773, pr18773⟩
private theorem pr18787 : Nat.Prime 18787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv101]) (by decide +kernel)
def pv18787 : PrimeValue := ⟨18787, pr18787⟩
private theorem pr18793 : Nat.Prime 18793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv18793 : PrimeValue := ⟨18793, pr18793⟩
private theorem pr18797 : Nat.Prime 18797 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv127]) (by decide +kernel)
def pv18797 : PrimeValue := ⟨18797, pr18797⟩
private theorem pr18803 : Nat.Prime 18803 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv17,pv79]) (by decide +kernel)
def pv18803 : PrimeValue := ⟨18803, pr18803⟩
private theorem pr18839 : Nat.Prime 18839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv9419]) (by decide +kernel)
def pv18839 : PrimeValue := ⟨18839, pr18839⟩
private theorem pr18859 : Nat.Prime 18859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv449]) (by decide +kernel)
def pv18859 : PrimeValue := ⟨18859, pr18859⟩
private theorem pr18869 : Nat.Prime 18869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv89]) (by decide +kernel)
def pv18869 : PrimeValue := ⟨18869, pr18869⟩
private theorem pr18899 : Nat.Prime 18899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv859]) (by decide +kernel)
def pv18899 : PrimeValue := ⟨18899, pr18899⟩
private theorem pr18911 : Nat.Prime 18911 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv31,pv61]) (by decide +kernel)
def pv18911 : PrimeValue := ⟨18911, pr18911⟩
private theorem pr18913 : Nat.Prime 18913 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv197]) (by decide +kernel)
def pv18913 : PrimeValue := ⟨18913, pr18913⟩
private theorem pr18917 : Nat.Prime 18917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv4729]) (by decide +kernel)
def pv18917 : PrimeValue := ⟨18917, pr18917⟩
private theorem pr18919 : Nat.Prime 18919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1051]) (by decide +kernel)
def pv18919 : PrimeValue := ⟨18919, pr18919⟩
private theorem pr18947 : Nat.Prime 18947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9473]) (by decide +kernel)
def pv18947 : PrimeValue := ⟨18947, pr18947⟩
private theorem pr18959 : Nat.Prime 18959 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv9479]) (by decide +kernel)
def pv18959 : PrimeValue := ⟨18959, pr18959⟩
private theorem pr18973 : Nat.Prime 18973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv31]) (by decide +kernel)
def pv18973 : PrimeValue := ⟨18973, pr18973⟩
private theorem pr18979 : Nat.Prime 18979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3163]) (by decide +kernel)
def pv18979 : PrimeValue := ⟨18979, pr18979⟩
private theorem pr19001 : Nat.Prime 19001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv19001 : PrimeValue := ⟨19001, pr19001⟩
private theorem pr19009 : Nat.Prime 19009 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv19009 : PrimeValue := ⟨19009, pr19009⟩
private theorem pr19013 : Nat.Prime 19013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv97]) (by decide +kernel)
def pv19013 : PrimeValue := ⟨19013, pr19013⟩
private theorem pr19031 : Nat.Prime 19031 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv173]) (by decide +kernel)
def pv19031 : PrimeValue := ⟨19031, pr19031⟩
private theorem pr19037 : Nat.Prime 19037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv4759]) (by decide +kernel)
def pv19037 : PrimeValue := ⟨19037, pr19037⟩
private theorem pr19051 : Nat.Prime 19051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv127]) (by decide +kernel)
def pv19051 : PrimeValue := ⟨19051, pr19051⟩
private theorem pr19069 : Nat.Prime 19069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv227]) (by decide +kernel)
def pv19069 : PrimeValue := ⟨19069, pr19069⟩
private theorem pr19073 : Nat.Prime 19073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv149]) (by decide +kernel)
def pv19073 : PrimeValue := ⟨19073, pr19073⟩
private theorem pr19079 : Nat.Prime 19079 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv9539]) (by decide +kernel)
def pv19079 : PrimeValue := ⟨19079, pr19079⟩
private theorem pr19081 : Nat.Prime 19081 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv53]) (by decide +kernel)
def pv19081 : PrimeValue := ⟨19081, pr19081⟩
private theorem pr19087 : Nat.Prime 19087 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv3181]) (by decide +kernel)
def pv19087 : PrimeValue := ⟨19087, pr19087⟩
private theorem pr19121 : Nat.Prime 19121 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv239]) (by decide +kernel)
def pv19121 : PrimeValue := ⟨19121, pr19121⟩
private theorem pr19139 : Nat.Prime 19139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1367]) (by decide +kernel)
def pv19139 : PrimeValue := ⟨19139, pr19139⟩
private theorem pr19141 : Nat.Prime 19141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv29]) (by decide +kernel)
def pv19141 : PrimeValue := ⟨19141, pr19141⟩
private theorem pr19157 : Nat.Prime 19157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv4789]) (by decide +kernel)
def pv19157 : PrimeValue := ⟨19157, pr19157⟩
private theorem pr19163 : Nat.Prime 19163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv67]) (by decide +kernel)
def pv19163 : PrimeValue := ⟨19163, pr19163⟩
private theorem pr19181 : Nat.Prime 19181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv137]) (by decide +kernel)
def pv19181 : PrimeValue := ⟨19181, pr19181⟩
private theorem pr19183 : Nat.Prime 19183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv139]) (by decide +kernel)
def pv19183 : PrimeValue := ⟨19183, pr19183⟩
private theorem pr19207 : Nat.Prime 19207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv97]) (by decide +kernel)
def pv19207 : PrimeValue := ⟨19207, pr19207⟩
private theorem pr19211 : Nat.Prime 19211 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv113]) (by decide +kernel)
def pv19211 : PrimeValue := ⟨19211, pr19211⟩
private theorem pr19213 : Nat.Prime 19213 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1601]) (by decide +kernel)
def pv19213 : PrimeValue := ⟨19213, pr19213⟩
private theorem pr19219 : Nat.Prime 19219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3203]) (by decide +kernel)
def pv19219 : PrimeValue := ⟨19219, pr19219⟩
private theorem pr19231 : Nat.Prime 19231 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv641]) (by decide +kernel)
def pv19231 : PrimeValue := ⟨19231, pr19231⟩
private theorem pr19237 : Nat.Prime 19237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv229]) (by decide +kernel)
def pv19237 : PrimeValue := ⟨19237, pr19237⟩
private theorem pr19249 : Nat.Prime 19249 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv401]) (by decide +kernel)
def pv19249 : PrimeValue := ⟨19249, pr19249⟩
private theorem pr19259 : Nat.Prime 19259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9629]) (by decide +kernel)
def pv19259 : PrimeValue := ⟨19259, pr19259⟩
private theorem pr19267 : Nat.Prime 19267 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv19267 : PrimeValue := ⟨19267, pr19267⟩
private theorem pr19273 : Nat.Prime 19273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv73]) (by decide +kernel)
def pv19273 : PrimeValue := ⟨19273, pr19273⟩
private theorem pr19289 : Nat.Prime 19289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2411]) (by decide +kernel)
def pv19289 : PrimeValue := ⟨19289, pr19289⟩
private theorem pr19301 : Nat.Prime 19301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv193]) (by decide +kernel)
def pv19301 : PrimeValue := ⟨19301, pr19301⟩
private theorem pr19309 : Nat.Prime 19309 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1609]) (by decide +kernel)
def pv19309 : PrimeValue := ⟨19309, pr19309⟩
private theorem pr19319 : Nat.Prime 19319 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv13,pv743]) (by decide +kernel)
def pv19319 : PrimeValue := ⟨19319, pr19319⟩
private theorem pr19333 : Nat.Prime 19333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv179]) (by decide +kernel)
def pv19333 : PrimeValue := ⟨19333, pr19333⟩
private theorem pr19373 : Nat.Prime 19373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv167]) (by decide +kernel)
def pv19373 : PrimeValue := ⟨19373, pr19373⟩
private theorem pr19379 : Nat.Prime 19379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9689]) (by decide +kernel)
def pv19379 : PrimeValue := ⟨19379, pr19379⟩
private theorem pr19381 : Nat.Prime 19381 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv19]) (by decide +kernel)
def pv19381 : PrimeValue := ⟨19381, pr19381⟩
private theorem pr19387 : Nat.Prime 19387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv359]) (by decide +kernel)
def pv19387 : PrimeValue := ⟨19387, pr19387⟩
private theorem pr19391 : Nat.Prime 19391 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv277]) (by decide +kernel)
def pv19391 : PrimeValue := ⟨19391, pr19391⟩
private theorem pr19403 : Nat.Prime 19403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv109]) (by decide +kernel)
def pv19403 : PrimeValue := ⟨19403, pr19403⟩
private theorem pr19417 : Nat.Prime 19417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv809]) (by decide +kernel)
def pv19417 : PrimeValue := ⟨19417, pr19417⟩
private theorem pr19421 : Nat.Prime 19421 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv971]) (by decide +kernel)
def pv19421 : PrimeValue := ⟨19421, pr19421⟩
private theorem pr19423 : Nat.Prime 19423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv83]) (by decide +kernel)
def pv19423 : PrimeValue := ⟨19423, pr19423⟩
private theorem pr19427 : Nat.Prime 19427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv883]) (by decide +kernel)
def pv19427 : PrimeValue := ⟨19427, pr19427⟩
private theorem pr19429 : Nat.Prime 19429 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1619]) (by decide +kernel)
def pv19429 : PrimeValue := ⟨19429, pr19429⟩
private theorem pr19433 : Nat.Prime 19433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv347]) (by decide +kernel)
def pv19433 : PrimeValue := ⟨19433, pr19433⟩
private theorem pr19441 : Nat.Prime 19441 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv19441 : PrimeValue := ⟨19441, pr19441⟩
private theorem pr19447 : Nat.Prime 19447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv463]) (by decide +kernel)
def pv19447 : PrimeValue := ⟨19447, pr19447⟩
private theorem pr19457 : Nat.Prime 19457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19]) (by decide +kernel)
def pv19457 : PrimeValue := ⟨19457, pr19457⟩
private theorem pr19463 : Nat.Prime 19463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv263]) (by decide +kernel)
def pv19463 : PrimeValue := ⟨19463, pr19463⟩
private theorem pr19469 : Nat.Prime 19469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv157]) (by decide +kernel)
def pv19469 : PrimeValue := ⟨19469, pr19469⟩
private theorem pr19471 : Nat.Prime 19471 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv59]) (by decide +kernel)
def pv19471 : PrimeValue := ⟨19471, pr19471⟩
private theorem pr19477 : Nat.Prime 19477 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv541]) (by decide +kernel)
def pv19477 : PrimeValue := ⟨19477, pr19477⟩
private theorem pr19483 : Nat.Prime 19483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv191]) (by decide +kernel)
def pv19483 : PrimeValue := ⟨19483, pr19483⟩
private theorem pr19489 : Nat.Prime 19489 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv19489 : PrimeValue := ⟨19489, pr19489⟩
private theorem pr19501 : Nat.Prime 19501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv19501 : PrimeValue := ⟨19501, pr19501⟩
private theorem pr19507 : Nat.Prime 19507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3251]) (by decide +kernel)
def pv19507 : PrimeValue := ⟨19507, pr19507⟩
private theorem pr19531 : Nat.Prime 19531 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv19531 : PrimeValue := ⟨19531, pr19531⟩
private theorem pr19541 : Nat.Prime 19541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv977]) (by decide +kernel)
def pv19541 : PrimeValue := ⟨19541, pr19541⟩
private theorem pr19543 : Nat.Prime 19543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3257]) (by decide +kernel)
def pv19543 : PrimeValue := ⟨19543, pr19543⟩
private theorem pr19553 : Nat.Prime 19553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv47]) (by decide +kernel)
def pv19553 : PrimeValue := ⟨19553, pr19553⟩
private theorem pr19559 : Nat.Prime 19559 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv11,pv127]) (by decide +kernel)
def pv19559 : PrimeValue := ⟨19559, pr19559⟩
private theorem pr19571 : Nat.Prime 19571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv103]) (by decide +kernel)
def pv19571 : PrimeValue := ⟨19571, pr19571⟩
private theorem pr19577 : Nat.Prime 19577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2447]) (by decide +kernel)
def pv19577 : PrimeValue := ⟨19577, pr19577⟩
private theorem pr19583 : Nat.Prime 19583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv9791]) (by decide +kernel)
def pv19583 : PrimeValue := ⟨19583, pr19583⟩
private theorem pr19597 : Nat.Prime 19597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv71]) (by decide +kernel)
def pv19597 : PrimeValue := ⟨19597, pr19597⟩
private theorem pr19603 : Nat.Prime 19603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv19603 : PrimeValue := ⟨19603, pr19603⟩
private theorem pr19609 : Nat.Prime 19609 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19,pv43]) (by decide +kernel)
def pv19609 : PrimeValue := ⟨19609, pr19609⟩
private theorem pr19661 : Nat.Prime 19661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv983]) (by decide +kernel)
def pv19661 : PrimeValue := ⟨19661, pr19661⟩
private theorem pr19681 : Nat.Prime 19681 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv19681 : PrimeValue := ⟨19681, pr19681⟩
private theorem pr19687 : Nat.Prime 19687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv193]) (by decide +kernel)
def pv19687 : PrimeValue := ⟨19687, pr19687⟩
private theorem pr19697 : Nat.Prime 19697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1231]) (by decide +kernel)
def pv19697 : PrimeValue := ⟨19697, pr19697⟩
private theorem pr19699 : Nat.Prime 19699 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv19699 : PrimeValue := ⟨19699, pr19699⟩
private theorem pr19709 : Nat.Prime 19709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv379]) (by decide +kernel)
def pv19709 : PrimeValue := ⟨19709, pr19709⟩
private theorem pr19717 : Nat.Prime 19717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv53]) (by decide +kernel)
def pv19717 : PrimeValue := ⟨19717, pr19717⟩
private theorem pr19727 : Nat.Prime 19727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv1409]) (by decide +kernel)
def pv19727 : PrimeValue := ⟨19727, pr19727⟩
private theorem pr19739 : Nat.Prime 19739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv139]) (by decide +kernel)
def pv19739 : PrimeValue := ⟨19739, pr19739⟩
private theorem pr19751 : Nat.Prime 19751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv79]) (by decide +kernel)
def pv19751 : PrimeValue := ⟨19751, pr19751⟩
private theorem pr19753 : Nat.Prime 19753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv823]) (by decide +kernel)
def pv19753 : PrimeValue := ⟨19753, pr19753⟩
private theorem pr19759 : Nat.Prime 19759 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv89]) (by decide +kernel)
def pv19759 : PrimeValue := ⟨19759, pr19759⟩
private theorem pr19763 : Nat.Prime 19763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv241]) (by decide +kernel)
def pv19763 : PrimeValue := ⟨19763, pr19763⟩
private theorem pr19777 : Nat.Prime 19777 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv19777 : PrimeValue := ⟨19777, pr19777⟩
private theorem pr19793 : Nat.Prime 19793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1237]) (by decide +kernel)
def pv19793 : PrimeValue := ⟨19793, pr19793⟩
private theorem pr19801 : Nat.Prime 19801 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv19801 : PrimeValue := ⟨19801, pr19801⟩
private theorem pr19813 : Nat.Prime 19813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv127]) (by decide +kernel)
def pv19813 : PrimeValue := ⟨19813, pr19813⟩
private theorem pr19819 : Nat.Prime 19819 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv367]) (by decide +kernel)
def pv19819 : PrimeValue := ⟨19819, pr19819⟩
private theorem pr19841 : Nat.Prime 19841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv31]) (by decide +kernel)
def pv19841 : PrimeValue := ⟨19841, pr19841⟩
private theorem pr19843 : Nat.Prime 19843 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv3307]) (by decide +kernel)
def pv19843 : PrimeValue := ⟨19843, pr19843⟩
private theorem pr19853 : Nat.Prime 19853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv709]) (by decide +kernel)
def pv19853 : PrimeValue := ⟨19853, pr19853⟩
private theorem pr19861 : Nat.Prime 19861 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv331]) (by decide +kernel)
def pv19861 : PrimeValue := ⟨19861, pr19861⟩
private theorem pr19867 : Nat.Prime 19867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv43]) (by decide +kernel)
def pv19867 : PrimeValue := ⟨19867, pr19867⟩
private theorem pr19889 : Nat.Prime 19889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv113]) (by decide +kernel)
def pv19889 : PrimeValue := ⟨19889, pr19889⟩
private theorem pr19891 : Nat.Prime 19891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv17]) (by decide +kernel)
def pv19891 : PrimeValue := ⟨19891, pr19891⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
