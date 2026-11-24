/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table003
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table003.pv5701
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table002

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr5701 : Nat.Prime 5701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv5701 : PrimeValue := ⟨5701, pr5701⟩
private theorem pr5711 : Nat.Prime 5711 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv571]) (by decide +kernel)
def pv5711 : PrimeValue := ⟨5711, pr5711⟩
private theorem pr5717 : Nat.Prime 5717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1429]) (by decide +kernel)
def pv5717 : PrimeValue := ⟨5717, pr5717⟩
private theorem pr5737 : Nat.Prime 5737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv239]) (by decide +kernel)
def pv5737 : PrimeValue := ⟨5737, pr5737⟩
private theorem pr5741 : Nat.Prime 5741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv41]) (by decide +kernel)
def pv5741 : PrimeValue := ⟨5741, pr5741⟩
private theorem pr5743 : Nat.Prime 5743 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv29]) (by decide +kernel)
def pv5743 : PrimeValue := ⟨5743, pr5743⟩
private theorem pr5749 : Nat.Prime 5749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv479]) (by decide +kernel)
def pv5749 : PrimeValue := ⟨5749, pr5749⟩
private theorem pr5779 : Nat.Prime 5779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv5779 : PrimeValue := ⟨5779, pr5779⟩
private theorem pr5783 : Nat.Prime 5783 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv59]) (by decide +kernel)
def pv5783 : PrimeValue := ⟨5783, pr5783⟩
private theorem pr5791 : Nat.Prime 5791 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv193]) (by decide +kernel)
def pv5791 : PrimeValue := ⟨5791, pr5791⟩
private theorem pr5801 : Nat.Prime 5801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29]) (by decide +kernel)
def pv5801 : PrimeValue := ⟨5801, pr5801⟩
private theorem pr5807 : Nat.Prime 5807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv2903]) (by decide +kernel)
def pv5807 : PrimeValue := ⟨5807, pr5807⟩
private theorem pr5813 : Nat.Prime 5813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1453]) (by decide +kernel)
def pv5813 : PrimeValue := ⟨5813, pr5813⟩
private theorem pr5821 : Nat.Prime 5821 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv97]) (by decide +kernel)
def pv5821 : PrimeValue := ⟨5821, pr5821⟩
private theorem pr5827 : Nat.Prime 5827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv971]) (by decide +kernel)
def pv5827 : PrimeValue := ⟨5827, pr5827⟩
private theorem pr5839 : Nat.Prime 5839 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv139]) (by decide +kernel)
def pv5839 : PrimeValue := ⟨5839, pr5839⟩
private theorem pr5843 : Nat.Prime 5843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv127]) (by decide +kernel)
def pv5843 : PrimeValue := ⟨5843, pr5843⟩
private theorem pr5849 : Nat.Prime 5849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv43]) (by decide +kernel)
def pv5849 : PrimeValue := ⟨5849, pr5849⟩
private theorem pr5851 : Nat.Prime 5851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv5851 : PrimeValue := ⟨5851, pr5851⟩
private theorem pr5857 : Nat.Prime 5857 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv5857 : PrimeValue := ⟨5857, pr5857⟩
private theorem pr5861 : Nat.Prime 5861 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv293]) (by decide +kernel)
def pv5861 : PrimeValue := ⟨5861, pr5861⟩
private theorem pr5867 : Nat.Prime 5867 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv419]) (by decide +kernel)
def pv5867 : PrimeValue := ⟨5867, pr5867⟩
private theorem pr5869 : Nat.Prime 5869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv163]) (by decide +kernel)
def pv5869 : PrimeValue := ⟨5869, pr5869⟩
private theorem pr5879 : Nat.Prime 5879 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv2939]) (by decide +kernel)
def pv5879 : PrimeValue := ⟨5879, pr5879⟩
private theorem pr5881 : Nat.Prime 5881 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv5881 : PrimeValue := ⟨5881, pr5881⟩
private theorem pr5897 : Nat.Prime 5897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv67]) (by decide +kernel)
def pv5897 : PrimeValue := ⟨5897, pr5897⟩
private theorem pr5903 : Nat.Prime 5903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv227]) (by decide +kernel)
def pv5903 : PrimeValue := ⟨5903, pr5903⟩
private theorem pr5923 : Nat.Prime 5923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv47]) (by decide +kernel)
def pv5923 : PrimeValue := ⟨5923, pr5923⟩
private theorem pr5927 : Nat.Prime 5927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv2963]) (by decide +kernel)
def pv5927 : PrimeValue := ⟨5927, pr5927⟩
private theorem pr5939 : Nat.Prime 5939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv2969]) (by decide +kernel)
def pv5939 : PrimeValue := ⟨5939, pr5939⟩
private theorem pr5953 : Nat.Prime 5953 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv5953 : PrimeValue := ⟨5953, pr5953⟩
private theorem pr5981 : Nat.Prime 5981 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv23]) (by decide +kernel)
def pv5981 : PrimeValue := ⟨5981, pr5981⟩
private theorem pr5987 : Nat.Prime 5987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv73]) (by decide +kernel)
def pv5987 : PrimeValue := ⟨5987, pr5987⟩
private theorem pr6007 : Nat.Prime 6007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv13]) (by decide +kernel)
def pv6007 : PrimeValue := ⟨6007, pr6007⟩
private theorem pr6011 : Nat.Prime 6011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv601]) (by decide +kernel)
def pv6011 : PrimeValue := ⟨6011, pr6011⟩
private theorem pr6029 : Nat.Prime 6029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv137]) (by decide +kernel)
def pv6029 : PrimeValue := ⟨6029, pr6029⟩
private theorem pr6037 : Nat.Prime 6037 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv503]) (by decide +kernel)
def pv6037 : PrimeValue := ⟨6037, pr6037⟩
private theorem pr6043 : Nat.Prime 6043 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv53]) (by decide +kernel)
def pv6043 : PrimeValue := ⟨6043, pr6043⟩
private theorem pr6047 : Nat.Prime 6047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3023]) (by decide +kernel)
def pv6047 : PrimeValue := ⟨6047, pr6047⟩
private theorem pr6053 : Nat.Prime 6053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv89]) (by decide +kernel)
def pv6053 : PrimeValue := ⟨6053, pr6053⟩
private theorem pr6067 : Nat.Prime 6067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv337]) (by decide +kernel)
def pv6067 : PrimeValue := ⟨6067, pr6067⟩
private theorem pr6073 : Nat.Prime 6073 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv6073 : PrimeValue := ⟨6073, pr6073⟩
private theorem pr6079 : Nat.Prime 6079 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv1013]) (by decide +kernel)
def pv6079 : PrimeValue := ⟨6079, pr6079⟩
private theorem pr6089 : Nat.Prime 6089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv761]) (by decide +kernel)
def pv6089 : PrimeValue := ⟨6089, pr6089⟩
private theorem pr6091 : Nat.Prime 6091 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv29]) (by decide +kernel)
def pv6091 : PrimeValue := ⟨6091, pr6091⟩
private theorem pr6101 : Nat.Prime 6101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv61]) (by decide +kernel)
def pv6101 : PrimeValue := ⟨6101, pr6101⟩
private theorem pr6113 : Nat.Prime 6113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv191]) (by decide +kernel)
def pv6113 : PrimeValue := ⟨6113, pr6113⟩
private theorem pr6121 : Nat.Prime 6121 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv6121 : PrimeValue := ⟨6121, pr6121⟩
private theorem pr6131 : Nat.Prime 6131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv613]) (by decide +kernel)
def pv6131 : PrimeValue := ⟨6131, pr6131⟩
private theorem pr6133 : Nat.Prime 6133 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv73]) (by decide +kernel)
def pv6133 : PrimeValue := ⟨6133, pr6133⟩
private theorem pr6143 : Nat.Prime 6143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv83]) (by decide +kernel)
def pv6143 : PrimeValue := ⟨6143, pr6143⟩
private theorem pr6151 : Nat.Prime 6151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv6151 : PrimeValue := ⟨6151, pr6151⟩
private theorem pr6163 : Nat.Prime 6163 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv79]) (by decide +kernel)
def pv6163 : PrimeValue := ⟨6163, pr6163⟩
private theorem pr6173 : Nat.Prime 6173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1543]) (by decide +kernel)
def pv6173 : PrimeValue := ⟨6173, pr6173⟩
private theorem pr6197 : Nat.Prime 6197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1549]) (by decide +kernel)
def pv6197 : PrimeValue := ⟨6197, pr6197⟩
private theorem pr6199 : Nat.Prime 6199 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1033]) (by decide +kernel)
def pv6199 : PrimeValue := ⟨6199, pr6199⟩
private theorem pr6203 : Nat.Prime 6203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv443]) (by decide +kernel)
def pv6203 : PrimeValue := ⟨6203, pr6203⟩
private theorem pr6211 : Nat.Prime 6211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv6211 : PrimeValue := ⟨6211, pr6211⟩
private theorem pr6217 : Nat.Prime 6217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv6217 : PrimeValue := ⟨6217, pr6217⟩
private theorem pr6221 : Nat.Prime 6221 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv311]) (by decide +kernel)
def pv6221 : PrimeValue := ⟨6221, pr6221⟩
private theorem pr6229 : Nat.Prime 6229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv173]) (by decide +kernel)
def pv6229 : PrimeValue := ⟨6229, pr6229⟩
private theorem pr6247 : Nat.Prime 6247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv347]) (by decide +kernel)
def pv6247 : PrimeValue := ⟨6247, pr6247⟩
private theorem pr6257 : Nat.Prime 6257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv23]) (by decide +kernel)
def pv6257 : PrimeValue := ⟨6257, pr6257⟩
private theorem pr6263 : Nat.Prime 6263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv101]) (by decide +kernel)
def pv6263 : PrimeValue := ⟨6263, pr6263⟩
private theorem pr6269 : Nat.Prime 6269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1567]) (by decide +kernel)
def pv6269 : PrimeValue := ⟨6269, pr6269⟩
private theorem pr6271 : Nat.Prime 6271 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv19]) (by decide +kernel)
def pv6271 : PrimeValue := ⟨6271, pr6271⟩
private theorem pr6277 : Nat.Prime 6277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv523]) (by decide +kernel)
def pv6277 : PrimeValue := ⟨6277, pr6277⟩
private theorem pr6287 : Nat.Prime 6287 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv449]) (by decide +kernel)
def pv6287 : PrimeValue := ⟨6287, pr6287⟩
private theorem pr6299 : Nat.Prime 6299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv67]) (by decide +kernel)
def pv6299 : PrimeValue := ⟨6299, pr6299⟩
private theorem pr6301 : Nat.Prime 6301 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv6301 : PrimeValue := ⟨6301, pr6301⟩
private theorem pr6311 : Nat.Prime 6311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv631]) (by decide +kernel)
def pv6311 : PrimeValue := ⟨6311, pr6311⟩
private theorem pr6317 : Nat.Prime 6317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1579]) (by decide +kernel)
def pv6317 : PrimeValue := ⟨6317, pr6317⟩
private theorem pr6323 : Nat.Prime 6323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv109]) (by decide +kernel)
def pv6323 : PrimeValue := ⟨6323, pr6323⟩
private theorem pr6329 : Nat.Prime 6329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv113]) (by decide +kernel)
def pv6329 : PrimeValue := ⟨6329, pr6329⟩
private theorem pr6337 : Nat.Prime 6337 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv6337 : PrimeValue := ⟨6337, pr6337⟩
private theorem pr6343 : Nat.Prime 6343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv151]) (by decide +kernel)
def pv6343 : PrimeValue := ⟨6343, pr6343⟩
private theorem pr6353 : Nat.Prime 6353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv397]) (by decide +kernel)
def pv6353 : PrimeValue := ⟨6353, pr6353⟩
private theorem pr6359 : Nat.Prime 6359 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv11,pv17]) (by decide +kernel)
def pv6359 : PrimeValue := ⟨6359, pr6359⟩
private theorem pr6361 : Nat.Prime 6361 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv53]) (by decide +kernel)
def pv6361 : PrimeValue := ⟨6361, pr6361⟩
private theorem pr6367 : Nat.Prime 6367 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1061]) (by decide +kernel)
def pv6367 : PrimeValue := ⟨6367, pr6367⟩
private theorem pr6373 : Nat.Prime 6373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv6373 : PrimeValue := ⟨6373, pr6373⟩
private theorem pr6379 : Nat.Prime 6379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1063]) (by decide +kernel)
def pv6379 : PrimeValue := ⟨6379, pr6379⟩
private theorem pr6389 : Nat.Prime 6389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1597]) (by decide +kernel)
def pv6389 : PrimeValue := ⟨6389, pr6389⟩
private theorem pr6397 : Nat.Prime 6397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv41]) (by decide +kernel)
def pv6397 : PrimeValue := ⟨6397, pr6397⟩
private theorem pr6421 : Nat.Prime 6421 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv6421 : PrimeValue := ⟨6421, pr6421⟩
private theorem pr6427 : Nat.Prime 6427 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv6427 : PrimeValue := ⟨6427, pr6427⟩
private theorem pr6449 : Nat.Prime 6449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv31]) (by decide +kernel)
def pv6449 : PrimeValue := ⟨6449, pr6449⟩
private theorem pr6451 : Nat.Prime 6451 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv6451 : PrimeValue := ⟨6451, pr6451⟩
private theorem pr6469 : Nat.Prime 6469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv6469 : PrimeValue := ⟨6469, pr6469⟩
private theorem pr6473 : Nat.Prime 6473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv809]) (by decide +kernel)
def pv6473 : PrimeValue := ⟨6473, pr6473⟩
private theorem pr6481 : Nat.Prime 6481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv6481 : PrimeValue := ⟨6481, pr6481⟩
private theorem pr6491 : Nat.Prime 6491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv59]) (by decide +kernel)
def pv6491 : PrimeValue := ⟨6491, pr6491⟩
private theorem pr6521 : Nat.Prime 6521 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv163]) (by decide +kernel)
def pv6521 : PrimeValue := ⟨6521, pr6521⟩
private theorem pr6529 : Nat.Prime 6529 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv6529 : PrimeValue := ⟨6529, pr6529⟩
private theorem pr6547 : Nat.Prime 6547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1091]) (by decide +kernel)
def pv6547 : PrimeValue := ⟨6547, pr6547⟩
private theorem pr6551 : Nat.Prime 6551 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv131]) (by decide +kernel)
def pv6551 : PrimeValue := ⟨6551, pr6551⟩
private theorem pr6553 : Nat.Prime 6553 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv6553 : PrimeValue := ⟨6553, pr6553⟩
private theorem pr6563 : Nat.Prime 6563 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv193]) (by decide +kernel)
def pv6563 : PrimeValue := ⟨6563, pr6563⟩
private theorem pr6569 : Nat.Prime 6569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv821]) (by decide +kernel)
def pv6569 : PrimeValue := ⟨6569, pr6569⟩
private theorem pr6571 : Nat.Prime 6571 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv6571 : PrimeValue := ⟨6571, pr6571⟩
private theorem pr6577 : Nat.Prime 6577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv137]) (by decide +kernel)
def pv6577 : PrimeValue := ⟨6577, pr6577⟩
private theorem pr6581 : Nat.Prime 6581 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv7,pv47]) (by decide +kernel)
def pv6581 : PrimeValue := ⟨6581, pr6581⟩
private theorem pr6599 : Nat.Prime 6599 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3299]) (by decide +kernel)
def pv6599 : PrimeValue := ⟨6599, pr6599⟩
private theorem pr6607 : Nat.Prime 6607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv367]) (by decide +kernel)
def pv6607 : PrimeValue := ⟨6607, pr6607⟩
private theorem pr6619 : Nat.Prime 6619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1103]) (by decide +kernel)
def pv6619 : PrimeValue := ⟨6619, pr6619⟩
private theorem pr6637 : Nat.Prime 6637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv79]) (by decide +kernel)
def pv6637 : PrimeValue := ⟨6637, pr6637⟩
private theorem pr6653 : Nat.Prime 6653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1663]) (by decide +kernel)
def pv6653 : PrimeValue := ⟨6653, pr6653⟩
private theorem pr6659 : Nat.Prime 6659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3329]) (by decide +kernel)
def pv6659 : PrimeValue := ⟨6659, pr6659⟩
private theorem pr6661 : Nat.Prime 6661 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv6661 : PrimeValue := ⟨6661, pr6661⟩
private theorem pr6673 : Nat.Prime 6673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv139]) (by decide +kernel)
def pv6673 : PrimeValue := ⟨6673, pr6673⟩
private theorem pr6679 : Nat.Prime 6679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv53]) (by decide +kernel)
def pv6679 : PrimeValue := ⟨6679, pr6679⟩
private theorem pr6689 : Nat.Prime 6689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv19]) (by decide +kernel)
def pv6689 : PrimeValue := ⟨6689, pr6689⟩
private theorem pr6691 : Nat.Prime 6691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv223]) (by decide +kernel)
def pv6691 : PrimeValue := ⟨6691, pr6691⟩
private theorem pr6701 : Nat.Prime 6701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv67]) (by decide +kernel)
def pv6701 : PrimeValue := ⟨6701, pr6701⟩
private theorem pr6703 : Nat.Prime 6703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1117]) (by decide +kernel)
def pv6703 : PrimeValue := ⟨6703, pr6703⟩
private theorem pr6709 : Nat.Prime 6709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv43]) (by decide +kernel)
def pv6709 : PrimeValue := ⟨6709, pr6709⟩
private theorem pr6719 : Nat.Prime 6719 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3359]) (by decide +kernel)
def pv6719 : PrimeValue := ⟨6719, pr6719⟩
private theorem pr6733 : Nat.Prime 6733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv6733 : PrimeValue := ⟨6733, pr6733⟩
private theorem pr6737 : Nat.Prime 6737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv421]) (by decide +kernel)
def pv6737 : PrimeValue := ⟨6737, pr6737⟩
private theorem pr6761 : Nat.Prime 6761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv6761 : PrimeValue := ⟨6761, pr6761⟩
private theorem pr6763 : Nat.Prime 6763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv6763 : PrimeValue := ⟨6763, pr6763⟩
private theorem pr6779 : Nat.Prime 6779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3389]) (by decide +kernel)
def pv6779 : PrimeValue := ⟨6779, pr6779⟩
private theorem pr6781 : Nat.Prime 6781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv113]) (by decide +kernel)
def pv6781 : PrimeValue := ⟨6781, pr6781⟩
private theorem pr6791 : Nat.Prime 6791 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv97]) (by decide +kernel)
def pv6791 : PrimeValue := ⟨6791, pr6791⟩
private theorem pr6793 : Nat.Prime 6793 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv283]) (by decide +kernel)
def pv6793 : PrimeValue := ⟨6793, pr6793⟩
private theorem pr6803 : Nat.Prime 6803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv179]) (by decide +kernel)
def pv6803 : PrimeValue := ⟨6803, pr6803⟩
private theorem pr6823 : Nat.Prime 6823 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv379]) (by decide +kernel)
def pv6823 : PrimeValue := ⟨6823, pr6823⟩
private theorem pr6827 : Nat.Prime 6827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3413]) (by decide +kernel)
def pv6827 : PrimeValue := ⟨6827, pr6827⟩
private theorem pr6829 : Nat.Prime 6829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv569]) (by decide +kernel)
def pv6829 : PrimeValue := ⟨6829, pr6829⟩
private theorem pr6833 : Nat.Prime 6833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv61]) (by decide +kernel)
def pv6833 : PrimeValue := ⟨6833, pr6833⟩
private theorem pr6841 : Nat.Prime 6841 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv6841 : PrimeValue := ⟨6841, pr6841⟩
private theorem pr6857 : Nat.Prime 6857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv857]) (by decide +kernel)
def pv6857 : PrimeValue := ⟨6857, pr6857⟩
private theorem pr6863 : Nat.Prime 6863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv73]) (by decide +kernel)
def pv6863 : PrimeValue := ⟨6863, pr6863⟩
private theorem pr6869 : Nat.Prime 6869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv101]) (by decide +kernel)
def pv6869 : PrimeValue := ⟨6869, pr6869⟩
private theorem pr6871 : Nat.Prime 6871 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv229]) (by decide +kernel)
def pv6871 : PrimeValue := ⟨6871, pr6871⟩
private theorem pr6883 : Nat.Prime 6883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv37]) (by decide +kernel)
def pv6883 : PrimeValue := ⟨6883, pr6883⟩
private theorem pr6899 : Nat.Prime 6899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3449]) (by decide +kernel)
def pv6899 : PrimeValue := ⟨6899, pr6899⟩
private theorem pr6907 : Nat.Prime 6907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1151]) (by decide +kernel)
def pv6907 : PrimeValue := ⟨6907, pr6907⟩
private theorem pr6911 : Nat.Prime 6911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv691]) (by decide +kernel)
def pv6911 : PrimeValue := ⟨6911, pr6911⟩
private theorem pr6917 : Nat.Prime 6917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv19]) (by decide +kernel)
def pv6917 : PrimeValue := ⟨6917, pr6917⟩
private theorem pr6947 : Nat.Prime 6947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv151]) (by decide +kernel)
def pv6947 : PrimeValue := ⟨6947, pr6947⟩
private theorem pr6949 : Nat.Prime 6949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv193]) (by decide +kernel)
def pv6949 : PrimeValue := ⟨6949, pr6949⟩
private theorem pr6959 : Nat.Prime 6959 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv71]) (by decide +kernel)
def pv6959 : PrimeValue := ⟨6959, pr6959⟩
private theorem pr6961 : Nat.Prime 6961 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv6961 : PrimeValue := ⟨6961, pr6961⟩
private theorem pr6967 : Nat.Prime 6967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv6967 : PrimeValue := ⟨6967, pr6967⟩
private theorem pr6971 : Nat.Prime 6971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv41]) (by decide +kernel)
def pv6971 : PrimeValue := ⟨6971, pr6971⟩
private theorem pr6977 : Nat.Prime 6977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv109]) (by decide +kernel)
def pv6977 : PrimeValue := ⟨6977, pr6977⟩
private theorem pr6983 : Nat.Prime 6983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3491]) (by decide +kernel)
def pv6983 : PrimeValue := ⟨6983, pr6983⟩
private theorem pr6991 : Nat.Prime 6991 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv233]) (by decide +kernel)
def pv6991 : PrimeValue := ⟨6991, pr6991⟩
private theorem pr6997 : Nat.Prime 6997 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv53]) (by decide +kernel)
def pv6997 : PrimeValue := ⟨6997, pr6997⟩
private theorem pr7001 : Nat.Prime 7001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv7001 : PrimeValue := ⟨7001, pr7001⟩
private theorem pr7013 : Nat.Prime 7013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1753]) (by decide +kernel)
def pv7013 : PrimeValue := ⟨7013, pr7013⟩
private theorem pr7019 : Nat.Prime 7019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv29]) (by decide +kernel)
def pv7019 : PrimeValue := ⟨7019, pr7019⟩
private theorem pr7027 : Nat.Prime 7027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1171]) (by decide +kernel)
def pv7027 : PrimeValue := ⟨7027, pr7027⟩
private theorem pr7039 : Nat.Prime 7039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv23]) (by decide +kernel)
def pv7039 : PrimeValue := ⟨7039, pr7039⟩
private theorem pr7043 : Nat.Prime 7043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv503]) (by decide +kernel)
def pv7043 : PrimeValue := ⟨7043, pr7043⟩
private theorem pr7057 : Nat.Prime 7057 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv7057 : PrimeValue := ⟨7057, pr7057⟩
private theorem pr7069 : Nat.Prime 7069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv31]) (by decide +kernel)
def pv7069 : PrimeValue := ⟨7069, pr7069⟩
private theorem pr7079 : Nat.Prime 7079 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3539]) (by decide +kernel)
def pv7079 : PrimeValue := ⟨7079, pr7079⟩
private theorem pr7103 : Nat.Prime 7103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv67]) (by decide +kernel)
def pv7103 : PrimeValue := ⟨7103, pr7103⟩
private theorem pr7109 : Nat.Prime 7109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1777]) (by decide +kernel)
def pv7109 : PrimeValue := ⟨7109, pr7109⟩
private theorem pr7121 : Nat.Prime 7121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv89]) (by decide +kernel)
def pv7121 : PrimeValue := ⟨7121, pr7121⟩
private theorem pr7127 : Nat.Prime 7127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv509]) (by decide +kernel)
def pv7127 : PrimeValue := ⟨7127, pr7127⟩
private theorem pr7129 : Nat.Prime 7129 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv7129 : PrimeValue := ⟨7129, pr7129⟩
private theorem pr7151 : Nat.Prime 7151 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv13]) (by decide +kernel)
def pv7151 : PrimeValue := ⟨7151, pr7151⟩
private theorem pr7159 : Nat.Prime 7159 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1193]) (by decide +kernel)
def pv7159 : PrimeValue := ⟨7159, pr7159⟩
private theorem pr7177 : Nat.Prime 7177 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13,pv23]) (by decide +kernel)
def pv7177 : PrimeValue := ⟨7177, pr7177⟩
private theorem pr7187 : Nat.Prime 7187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3593]) (by decide +kernel)
def pv7187 : PrimeValue := ⟨7187, pr7187⟩
private theorem pr7193 : Nat.Prime 7193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv31]) (by decide +kernel)
def pv7193 : PrimeValue := ⟨7193, pr7193⟩
private theorem pr7207 : Nat.Prime 7207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1201]) (by decide +kernel)
def pv7207 : PrimeValue := ⟨7207, pr7207⟩
private theorem pr7211 : Nat.Prime 7211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv103]) (by decide +kernel)
def pv7211 : PrimeValue := ⟨7211, pr7211⟩
private theorem pr7213 : Nat.Prime 7213 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv601]) (by decide +kernel)
def pv7213 : PrimeValue := ⟨7213, pr7213⟩
private theorem pr7219 : Nat.Prime 7219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv401]) (by decide +kernel)
def pv7219 : PrimeValue := ⟨7219, pr7219⟩
private theorem pr7229 : Nat.Prime 7229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv139]) (by decide +kernel)
def pv7229 : PrimeValue := ⟨7229, pr7229⟩
private theorem pr7237 : Nat.Prime 7237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv7237 : PrimeValue := ⟨7237, pr7237⟩
private theorem pr7243 : Nat.Prime 7243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv71]) (by decide +kernel)
def pv7243 : PrimeValue := ⟨7243, pr7243⟩
private theorem pr7247 : Nat.Prime 7247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3623]) (by decide +kernel)
def pv7247 : PrimeValue := ⟨7247, pr7247⟩
private theorem pr7253 : Nat.Prime 7253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv37]) (by decide +kernel)
def pv7253 : PrimeValue := ⟨7253, pr7253⟩
private theorem pr7283 : Nat.Prime 7283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv331]) (by decide +kernel)
def pv7283 : PrimeValue := ⟨7283, pr7283⟩
private theorem pr7297 : Nat.Prime 7297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv7297 : PrimeValue := ⟨7297, pr7297⟩
private theorem pr7307 : Nat.Prime 7307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv281]) (by decide +kernel)
def pv7307 : PrimeValue := ⟨7307, pr7307⟩
private theorem pr7309 : Nat.Prime 7309 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv7309 : PrimeValue := ⟨7309, pr7309⟩
private theorem pr7321 : Nat.Prime 7321 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv7321 : PrimeValue := ⟨7321, pr7321⟩
private theorem pr7331 : Nat.Prime 7331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv733]) (by decide +kernel)
def pv7331 : PrimeValue := ⟨7331, pr7331⟩
private theorem pr7333 : Nat.Prime 7333 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv13,pv47]) (by decide +kernel)
def pv7333 : PrimeValue := ⟨7333, pr7333⟩
private theorem pr7349 : Nat.Prime 7349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv167]) (by decide +kernel)
def pv7349 : PrimeValue := ⟨7349, pr7349⟩
private theorem pr7351 : Nat.Prime 7351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv7351 : PrimeValue := ⟨7351, pr7351⟩
private theorem pr7369 : Nat.Prime 7369 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv307]) (by decide +kernel)
def pv7369 : PrimeValue := ⟨7369, pr7369⟩
private theorem pr7393 : Nat.Prime 7393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv7393 : PrimeValue := ⟨7393, pr7393⟩
private theorem pr7411 : Nat.Prime 7411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv19]) (by decide +kernel)
def pv7411 : PrimeValue := ⟨7411, pr7411⟩
private theorem pr7417 : Nat.Prime 7417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv7417 : PrimeValue := ⟨7417, pr7417⟩
private theorem pr7433 : Nat.Prime 7433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv929]) (by decide +kernel)
def pv7433 : PrimeValue := ⟨7433, pr7433⟩
private theorem pr7451 : Nat.Prime 7451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv149]) (by decide +kernel)
def pv7451 : PrimeValue := ⟨7451, pr7451⟩
private theorem pr7457 : Nat.Prime 7457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv233]) (by decide +kernel)
def pv7457 : PrimeValue := ⟨7457, pr7457⟩
private theorem pr7459 : Nat.Prime 7459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv113]) (by decide +kernel)
def pv7459 : PrimeValue := ⟨7459, pr7459⟩
private theorem pr7477 : Nat.Prime 7477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv89]) (by decide +kernel)
def pv7477 : PrimeValue := ⟨7477, pr7477⟩
private theorem pr7481 : Nat.Prime 7481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv17]) (by decide +kernel)
def pv7481 : PrimeValue := ⟨7481, pr7481⟩
private theorem pr7487 : Nat.Prime 7487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv197]) (by decide +kernel)
def pv7487 : PrimeValue := ⟨7487, pr7487⟩
private theorem pr7489 : Nat.Prime 7489 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv7489 : PrimeValue := ⟨7489, pr7489⟩
private theorem pr7499 : Nat.Prime 7499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv163]) (by decide +kernel)
def pv7499 : PrimeValue := ⟨7499, pr7499⟩
private theorem pr7507 : Nat.Prime 7507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv139]) (by decide +kernel)
def pv7507 : PrimeValue := ⟨7507, pr7507⟩
private theorem pr7517 : Nat.Prime 7517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1879]) (by decide +kernel)
def pv7517 : PrimeValue := ⟨7517, pr7517⟩
private theorem pr7523 : Nat.Prime 7523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3761]) (by decide +kernel)
def pv7523 : PrimeValue := ⟨7523, pr7523⟩
private theorem pr7529 : Nat.Prime 7529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv941]) (by decide +kernel)
def pv7529 : PrimeValue := ⟨7529, pr7529⟩
private theorem pr7537 : Nat.Prime 7537 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv157]) (by decide +kernel)
def pv7537 : PrimeValue := ⟨7537, pr7537⟩
private theorem pr7541 : Nat.Prime 7541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv29]) (by decide +kernel)
def pv7541 : PrimeValue := ⟨7541, pr7541⟩
private theorem pr7547 : Nat.Prime 7547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11]) (by decide +kernel)
def pv7547 : PrimeValue := ⟨7547, pr7547⟩
private theorem pr7549 : Nat.Prime 7549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv37]) (by decide +kernel)
def pv7549 : PrimeValue := ⟨7549, pr7549⟩
private theorem pr7559 : Nat.Prime 7559 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3779]) (by decide +kernel)
def pv7559 : PrimeValue := ⟨7559, pr7559⟩
private theorem pr7561 : Nat.Prime 7561 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv7561 : PrimeValue := ⟨7561, pr7561⟩
private theorem pr7573 : Nat.Prime 7573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv631]) (by decide +kernel)
def pv7573 : PrimeValue := ⟨7573, pr7573⟩
private theorem pr7577 : Nat.Prime 7577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv947]) (by decide +kernel)
def pv7577 : PrimeValue := ⟨7577, pr7577⟩
private theorem pr7583 : Nat.Prime 7583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv223]) (by decide +kernel)
def pv7583 : PrimeValue := ⟨7583, pr7583⟩
private theorem pr7589 : Nat.Prime 7589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv271]) (by decide +kernel)
def pv7589 : PrimeValue := ⟨7589, pr7589⟩
private theorem pr7591 : Nat.Prime 7591 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv11,pv23]) (by decide +kernel)
def pv7591 : PrimeValue := ⟨7591, pr7591⟩
private theorem pr7603 : Nat.Prime 7603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv181]) (by decide +kernel)
def pv7603 : PrimeValue := ⟨7603, pr7603⟩
private theorem pr7607 : Nat.Prime 7607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3803]) (by decide +kernel)
def pv7607 : PrimeValue := ⟨7607, pr7607⟩
private theorem pr7621 : Nat.Prime 7621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv127]) (by decide +kernel)
def pv7621 : PrimeValue := ⟨7621, pr7621⟩
private theorem pr7639 : Nat.Prime 7639 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv67]) (by decide +kernel)
def pv7639 : PrimeValue := ⟨7639, pr7639⟩
private theorem pr7643 : Nat.Prime 7643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3821]) (by decide +kernel)
def pv7643 : PrimeValue := ⟨7643, pr7643⟩
private theorem pr7649 : Nat.Prime 7649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv239]) (by decide +kernel)
def pv7649 : PrimeValue := ⟨7649, pr7649⟩
private theorem pr7669 : Nat.Prime 7669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv7669 : PrimeValue := ⟨7669, pr7669⟩
private theorem pr7673 : Nat.Prime 7673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv137]) (by decide +kernel)
def pv7673 : PrimeValue := ⟨7673, pr7673⟩
private theorem pr7681 : Nat.Prime 7681 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv7681 : PrimeValue := ⟨7681, pr7681⟩
private theorem pr7687 : Nat.Prime 7687 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv61]) (by decide +kernel)
def pv7687 : PrimeValue := ⟨7687, pr7687⟩
private theorem pr7691 : Nat.Prime 7691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv769]) (by decide +kernel)
def pv7691 : PrimeValue := ⟨7691, pr7691⟩
private theorem pr7699 : Nat.Prime 7699 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1283]) (by decide +kernel)
def pv7699 : PrimeValue := ⟨7699, pr7699⟩
private theorem pr7703 : Nat.Prime 7703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3851]) (by decide +kernel)
def pv7703 : PrimeValue := ⟨7703, pr7703⟩
private theorem pr7717 : Nat.Prime 7717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv643]) (by decide +kernel)
def pv7717 : PrimeValue := ⟨7717, pr7717⟩
private theorem pr7723 : Nat.Prime 7723 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv7723 : PrimeValue := ⟨7723, pr7723⟩
private theorem pr7727 : Nat.Prime 7727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3863]) (by decide +kernel)
def pv7727 : PrimeValue := ⟨7727, pr7727⟩
private theorem pr7741 : Nat.Prime 7741 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv7741 : PrimeValue := ⟨7741, pr7741⟩
private theorem pr7753 : Nat.Prime 7753 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv17,pv19]) (by decide +kernel)
def pv7753 : PrimeValue := ⟨7753, pr7753⟩
private theorem pr7757 : Nat.Prime 7757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv277]) (by decide +kernel)
def pv7757 : PrimeValue := ⟨7757, pr7757⟩
private theorem pr7759 : Nat.Prime 7759 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv431]) (by decide +kernel)
def pv7759 : PrimeValue := ⟨7759, pr7759⟩
private theorem pr7789 : Nat.Prime 7789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv59]) (by decide +kernel)
def pv7789 : PrimeValue := ⟨7789, pr7789⟩
private theorem pr7793 : Nat.Prime 7793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv487]) (by decide +kernel)
def pv7793 : PrimeValue := ⟨7793, pr7793⟩
private theorem pr7817 : Nat.Prime 7817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv977]) (by decide +kernel)
def pv7817 : PrimeValue := ⟨7817, pr7817⟩
private theorem pr7823 : Nat.Prime 7823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3911]) (by decide +kernel)
def pv7823 : PrimeValue := ⟨7823, pr7823⟩
private theorem pr7829 : Nat.Prime 7829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv103]) (by decide +kernel)
def pv7829 : PrimeValue := ⟨7829, pr7829⟩
private theorem pr7841 : Nat.Prime 7841 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv7841 : PrimeValue := ⟨7841, pr7841⟩
private theorem pr7853 : Nat.Prime 7853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv151]) (by decide +kernel)
def pv7853 : PrimeValue := ⟨7853, pr7853⟩
private theorem pr7867 : Nat.Prime 7867 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv23]) (by decide +kernel)
def pv7867 : PrimeValue := ⟨7867, pr7867⟩
private theorem pr7873 : Nat.Prime 7873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv7873 : PrimeValue := ⟨7873, pr7873⟩
private theorem pr7877 : Nat.Prime 7877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv179]) (by decide +kernel)
def pv7877 : PrimeValue := ⟨7877, pr7877⟩
private theorem pr7879 : Nat.Prime 7879 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv101]) (by decide +kernel)
def pv7879 : PrimeValue := ⟨7879, pr7879⟩
private theorem pr7883 : Nat.Prime 7883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv563]) (by decide +kernel)
def pv7883 : PrimeValue := ⟨7883, pr7883⟩
private theorem pr7901 : Nat.Prime 7901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv79]) (by decide +kernel)
def pv7901 : PrimeValue := ⟨7901, pr7901⟩
private theorem pr7907 : Nat.Prime 7907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv67]) (by decide +kernel)
def pv7907 : PrimeValue := ⟨7907, pr7907⟩
private theorem pr7919 : Nat.Prime 7919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv37,pv107]) (by decide +kernel)
def pv7919 : PrimeValue := ⟨7919, pr7919⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
