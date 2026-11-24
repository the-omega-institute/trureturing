/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table031
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table031.pv79433
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table006
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr79433 : Nat.Prime 79433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9929]) (by decide +kernel)
def pv79433 : PrimeValue := ⟨79433, pr79433⟩
private theorem pr79451 : Nat.Prime 79451 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv227]) (by decide +kernel)
def pv79451 : PrimeValue := ⟨79451, pr79451⟩
private theorem pr79481 : Nat.Prime 79481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv1987]) (by decide +kernel)
def pv79481 : PrimeValue := ⟨79481, pr79481⟩
private theorem pr79493 : Nat.Prime 79493 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv17,pv167]) (by decide +kernel)
def pv79493 : PrimeValue := ⟨79493, pr79493⟩
private theorem pr79531 : Nat.Prime 79531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv241]) (by decide +kernel)
def pv79531 : PrimeValue := ⟨79531, pr79531⟩
private theorem pr79537 : Nat.Prime 79537 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1657]) (by decide +kernel)
def pv79537 : PrimeValue := ⟨79537, pr79537⟩
private theorem pr79549 : Nat.Prime 79549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv947]) (by decide +kernel)
def pv79549 : PrimeValue := ⟨79549, pr79549⟩
private theorem pr79559 : Nat.Prime 79559 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv39779]) (by decide +kernel)
def pv79559 : PrimeValue := ⟨79559, pr79559⟩
private theorem pr79579 : Nat.Prime 79579 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv4421]) (by decide +kernel)
def pv79579 : PrimeValue := ⟨79579, pr79579⟩
private theorem pr79589 : Nat.Prime 79589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv197]) (by decide +kernel)
def pv79589 : PrimeValue := ⟨79589, pr79589⟩
private theorem pr79601 : Nat.Prime 79601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv199]) (by decide +kernel)
def pv79601 : PrimeValue := ⟨79601, pr79601⟩
private theorem pr79609 : Nat.Prime 79609 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv31,pv107]) (by decide +kernel)
def pv79609 : PrimeValue := ⟨79609, pr79609⟩
private theorem pr79613 : Nat.Prime 79613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv1531]) (by decide +kernel)
def pv79613 : PrimeValue := ⟨79613, pr79613⟩
private theorem pr79621 : Nat.Prime 79621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1327]) (by decide +kernel)
def pv79621 : PrimeValue := ⟨79621, pr79621⟩
private theorem pr79627 : Nat.Prime 79627 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv577]) (by decide +kernel)
def pv79627 : PrimeValue := ⟨79627, pr79627⟩
private theorem pr79631 : Nat.Prime 79631 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7963]) (by decide +kernel)
def pv79631 : PrimeValue := ⟨79631, pr79631⟩
private theorem pr79633 : Nat.Prime 79633 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv79]) (by decide +kernel)
def pv79633 : PrimeValue := ⟨79633, pr79633⟩
private theorem pr79657 : Nat.Prime 79657 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3319]) (by decide +kernel)
def pv79657 : PrimeValue := ⟨79657, pr79657⟩
private theorem pr79669 : Nat.Prime 79669 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv2213]) (by decide +kernel)
def pv79669 : PrimeValue := ⟨79669, pr79669⟩
private theorem pr79687 : Nat.Prime 79687 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv233]) (by decide +kernel)
def pv79687 : PrimeValue := ⟨79687, pr79687⟩
private theorem pr79691 : Nat.Prime 79691 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv613]) (by decide +kernel)
def pv79691 : PrimeValue := ⟨79691, pr79691⟩
private theorem pr79693 : Nat.Prime 79693 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv229]) (by decide +kernel)
def pv79693 : PrimeValue := ⟨79693, pr79693⟩
private theorem pr79697 : Nat.Prime 79697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv293]) (by decide +kernel)
def pv79697 : PrimeValue := ⟨79697, pr79697⟩
private theorem pr79699 : Nat.Prime 79699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv359]) (by decide +kernel)
def pv79699 : PrimeValue := ⟨79699, pr79699⟩
private theorem pr79757 : Nat.Prime 79757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127,pv157]) (by decide +kernel)
def pv79757 : PrimeValue := ⟨79757, pr79757⟩
private theorem pr79769 : Nat.Prime 79769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv59]) (by decide +kernel)
def pv79769 : PrimeValue := ⟨79769, pr79769⟩
private theorem pr79777 : Nat.Prime 79777 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv277]) (by decide +kernel)
def pv79777 : PrimeValue := ⟨79777, pr79777⟩
private theorem pr79801 : Nat.Prime 79801 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv79801 : PrimeValue := ⟨79801, pr79801⟩
private theorem pr79811 : Nat.Prime 79811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv347]) (by decide +kernel)
def pv79811 : PrimeValue := ⟨79811, pr79811⟩
private theorem pr79813 : Nat.Prime 79813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv739]) (by decide +kernel)
def pv79813 : PrimeValue := ⟨79813, pr79813⟩
private theorem pr79817 : Nat.Prime 79817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv907]) (by decide +kernel)
def pv79817 : PrimeValue := ⟨79817, pr79817⟩
private theorem pr79823 : Nat.Prime 79823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv107,pv373]) (by decide +kernel)
def pv79823 : PrimeValue := ⟨79823, pr79823⟩
private theorem pr79829 : Nat.Prime 79829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2851]) (by decide +kernel)
def pv79829 : PrimeValue := ⟨79829, pr79829⟩
private theorem pr79841 : Nat.Prime 79841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv499]) (by decide +kernel)
def pv79841 : PrimeValue := ⟨79841, pr79841⟩
private theorem pr79843 : Nat.Prime 79843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1901]) (by decide +kernel)
def pv79843 : PrimeValue := ⟨79843, pr79843⟩
private theorem pr79847 : Nat.Prime 79847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv37,pv83]) (by decide +kernel)
def pv79847 : PrimeValue := ⟨79847, pr79847⟩
private theorem pr79861 : Nat.Prime 79861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv79861 : PrimeValue := ⟨79861, pr79861⟩
private theorem pr79867 : Nat.Prime 79867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv29]) (by decide +kernel)
def pv79867 : PrimeValue := ⟨79867, pr79867⟩
private theorem pr79873 : Nat.Prime 79873 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv79873 : PrimeValue := ⟨79873, pr79873⟩
private theorem pr79889 : Nat.Prime 79889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4993]) (by decide +kernel)
def pv79889 : PrimeValue := ⟨79889, pr79889⟩
private theorem pr79901 : Nat.Prime 79901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv47]) (by decide +kernel)
def pv79901 : PrimeValue := ⟨79901, pr79901⟩
private theorem pr79903 : Nat.Prime 79903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv193]) (by decide +kernel)
def pv79903 : PrimeValue := ⟨79903, pr79903⟩
private theorem pr79907 : Nat.Prime 79907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv39953]) (by decide +kernel)
def pv79907 : PrimeValue := ⟨79907, pr79907⟩
private theorem pr79939 : Nat.Prime 79939 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4441]) (by decide +kernel)
def pv79939 : PrimeValue := ⟨79939, pr79939⟩
private theorem pr79967 : Nat.Prime 79967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv39983]) (by decide +kernel)
def pv79967 : PrimeValue := ⟨79967, pr79967⟩
private theorem pr79973 : Nat.Prime 79973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19993]) (by decide +kernel)
def pv79973 : PrimeValue := ⟨79973, pr79973⟩
private theorem pr79979 : Nat.Prime 79979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv39989]) (by decide +kernel)
def pv79979 : PrimeValue := ⟨79979, pr79979⟩
private theorem pr79987 : Nat.Prime 79987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13331]) (by decide +kernel)
def pv79987 : PrimeValue := ⟨79987, pr79987⟩
private theorem pr79997 : Nat.Prime 79997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2857]) (by decide +kernel)
def pv79997 : PrimeValue := ⟨79997, pr79997⟩
private theorem pr79999 : Nat.Prime 79999 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv67,pv199]) (by decide +kernel)
def pv79999 : PrimeValue := ⟨79999, pr79999⟩
private theorem pr80021 : Nat.Prime 80021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv4001]) (by decide +kernel)
def pv80021 : PrimeValue := ⟨80021, pr80021⟩
private theorem pr80039 : Nat.Prime 80039 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv5717]) (by decide +kernel)
def pv80039 : PrimeValue := ⟨80039, pr80039⟩
private theorem pr80051 : Nat.Prime 80051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1601]) (by decide +kernel)
def pv80051 : PrimeValue := ⟨80051, pr80051⟩
private theorem pr80071 : Nat.Prime 80071 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv157]) (by decide +kernel)
def pv80071 : PrimeValue := ⟨80071, pr80071⟩
private theorem pr80077 : Nat.Prime 80077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6673]) (by decide +kernel)
def pv80077 : PrimeValue := ⟨80077, pr80077⟩
private theorem pr80107 : Nat.Prime 80107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv79]) (by decide +kernel)
def pv80107 : PrimeValue := ⟨80107, pr80107⟩
private theorem pr80111 : Nat.Prime 80111 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv8011]) (by decide +kernel)
def pv80111 : PrimeValue := ⟨80111, pr80111⟩
private theorem pr80141 : Nat.Prime 80141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv4007]) (by decide +kernel)
def pv80141 : PrimeValue := ⟨80141, pr80141⟩
private theorem pr80147 : Nat.Prime 80147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv3643]) (by decide +kernel)
def pv80147 : PrimeValue := ⟨80147, pr80147⟩
private theorem pr80149 : Nat.Prime 80149 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv6679]) (by decide +kernel)
def pv80149 : PrimeValue := ⟨80149, pr80149⟩
private theorem pr80153 : Nat.Prime 80153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv233]) (by decide +kernel)
def pv80153 : PrimeValue := ⟨80153, pr80153⟩
private theorem pr80167 : Nat.Prime 80167 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv431]) (by decide +kernel)
def pv80167 : PrimeValue := ⟨80167, pr80167⟩
private theorem pr80173 : Nat.Prime 80173 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv131]) (by decide +kernel)
def pv80173 : PrimeValue := ⟨80173, pr80173⟩
private theorem pr80177 : Nat.Prime 80177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5011]) (by decide +kernel)
def pv80177 : PrimeValue := ⟨80177, pr80177⟩
private theorem pr80191 : Nat.Prime 80191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv80191 : PrimeValue := ⟨80191, pr80191⟩
private theorem pr80207 : Nat.Prime 80207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv17,pv337]) (by decide +kernel)
def pv80207 : PrimeValue := ⟨80207, pr80207⟩
private theorem pr80209 : Nat.Prime 80209 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv557]) (by decide +kernel)
def pv80209 : PrimeValue := ⟨80209, pr80209⟩
private theorem pr80221 : Nat.Prime 80221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv191]) (by decide +kernel)
def pv80221 : PrimeValue := ⟨80221, pr80221⟩
private theorem pr80231 : Nat.Prime 80231 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv71,pv113]) (by decide +kernel)
def pv80231 : PrimeValue := ⟨80231, pr80231⟩
private theorem pr80233 : Nat.Prime 80233 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv3343]) (by decide +kernel)
def pv80233 : PrimeValue := ⟨80233, pr80233⟩
private theorem pr80239 : Nat.Prime 80239 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv311]) (by decide +kernel)
def pv80239 : PrimeValue := ⟨80239, pr80239⟩
private theorem pr80251 : Nat.Prime 80251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv80251 : PrimeValue := ⟨80251, pr80251⟩
private theorem pr80263 : Nat.Prime 80263 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv80263 : PrimeValue := ⟨80263, pr80263⟩
private theorem pr80273 : Nat.Prime 80273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv173]) (by decide +kernel)
def pv80273 : PrimeValue := ⟨80273, pr80273⟩
private theorem pr80279 : Nat.Prime 80279 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv41,pv89]) (by decide +kernel)
def pv80279 : PrimeValue := ⟨80279, pr80279⟩
private theorem pr80309 : Nat.Prime 80309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv1181]) (by decide +kernel)
def pv80309 : PrimeValue := ⟨80309, pr80309⟩
private theorem pr80317 : Nat.Prime 80317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv97]) (by decide +kernel)
def pv80317 : PrimeValue := ⟨80317, pr80317⟩
private theorem pr80329 : Nat.Prime 80329 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv3347]) (by decide +kernel)
def pv80329 : PrimeValue := ⟨80329, pr80329⟩
private theorem pr80341 : Nat.Prime 80341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv103]) (by decide +kernel)
def pv80341 : PrimeValue := ⟨80341, pr80341⟩
private theorem pr80347 : Nat.Prime 80347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1913]) (by decide +kernel)
def pv80347 : PrimeValue := ⟨80347, pr80347⟩
private theorem pr80363 : Nat.Prime 80363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv1747]) (by decide +kernel)
def pv80363 : PrimeValue := ⟨80363, pr80363⟩
private theorem pr80369 : Nat.Prime 80369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5023]) (by decide +kernel)
def pv80369 : PrimeValue := ⟨80369, pr80369⟩
private theorem pr80387 : Nat.Prime 80387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv40193]) (by decide +kernel)
def pv80387 : PrimeValue := ⟨80387, pr80387⟩
private theorem pr80407 : Nat.Prime 80407 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1489]) (by decide +kernel)
def pv80407 : PrimeValue := ⟨80407, pr80407⟩
private theorem pr80429 : Nat.Prime 80429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv20107]) (by decide +kernel)
def pv80429 : PrimeValue := ⟨80429, pr80429⟩
private theorem pr80447 : Nat.Prime 80447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv29,pv73]) (by decide +kernel)
def pv80447 : PrimeValue := ⟨80447, pr80447⟩
private theorem pr80449 : Nat.Prime 80449 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv419]) (by decide +kernel)
def pv80449 : PrimeValue := ⟨80449, pr80449⟩
private theorem pr80471 : Nat.Prime 80471 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv619]) (by decide +kernel)
def pv80471 : PrimeValue := ⟨80471, pr80471⟩
private theorem pr80473 : Nat.Prime 80473 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv479]) (by decide +kernel)
def pv80473 : PrimeValue := ⟨80473, pr80473⟩
private theorem pr80489 : Nat.Prime 80489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10061]) (by decide +kernel)
def pv80489 : PrimeValue := ⟨80489, pr80489⟩
private theorem pr80491 : Nat.Prime 80491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2683]) (by decide +kernel)
def pv80491 : PrimeValue := ⟨80491, pr80491⟩
private theorem pr80513 : Nat.Prime 80513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv37]) (by decide +kernel)
def pv80513 : PrimeValue := ⟨80513, pr80513⟩
private theorem pr80527 : Nat.Prime 80527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13421]) (by decide +kernel)
def pv80527 : PrimeValue := ⟨80527, pr80527⟩
private theorem pr80537 : Nat.Prime 80537 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10067]) (by decide +kernel)
def pv80537 : PrimeValue := ⟨80537, pr80537⟩
private theorem pr80557 : Nat.Prime 80557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv137]) (by decide +kernel)
def pv80557 : PrimeValue := ⟨80557, pr80557⟩
private theorem pr80567 : Nat.Prime 80567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv40283]) (by decide +kernel)
def pv80567 : PrimeValue := ⟨80567, pr80567⟩
private theorem pr80599 : Nat.Prime 80599 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv101]) (by decide +kernel)
def pv80599 : PrimeValue := ⟨80599, pr80599⟩
private theorem pr80603 : Nat.Prime 80603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv191,pv211]) (by decide +kernel)
def pv80603 : PrimeValue := ⟨80603, pr80603⟩
private theorem pr80611 : Nat.Prime 80611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2687]) (by decide +kernel)
def pv80611 : PrimeValue := ⟨80611, pr80611⟩
private theorem pr80621 : Nat.Prime 80621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv139]) (by decide +kernel)
def pv80621 : PrimeValue := ⟨80621, pr80621⟩
private theorem pr80627 : Nat.Prime 80627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv443]) (by decide +kernel)
def pv80627 : PrimeValue := ⟨80627, pr80627⟩
private theorem pr80629 : Nat.Prime 80629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6719]) (by decide +kernel)
def pv80629 : PrimeValue := ⟨80629, pr80629⟩
private theorem pr80651 : Nat.Prime 80651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1613]) (by decide +kernel)
def pv80651 : PrimeValue := ⟨80651, pr80651⟩
private theorem pr80657 : Nat.Prime 80657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv71]) (by decide +kernel)
def pv80657 : PrimeValue := ⟨80657, pr80657⟩
private theorem pr80669 : Nat.Prime 80669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv43,pv67]) (by decide +kernel)
def pv80669 : PrimeValue := ⟨80669, pr80669⟩
private theorem pr80671 : Nat.Prime 80671 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv2689]) (by decide +kernel)
def pv80671 : PrimeValue := ⟨80671, pr80671⟩
private theorem pr80677 : Nat.Prime 80677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv80677 : PrimeValue := ⟨80677, pr80677⟩
private theorem pr80681 : Nat.Prime 80681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2017]) (by decide +kernel)
def pv80681 : PrimeValue := ⟨80681, pr80681⟩
private theorem pr80683 : Nat.Prime 80683 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv113]) (by decide +kernel)
def pv80683 : PrimeValue := ⟨80683, pr80683⟩
private theorem pr80687 : Nat.Prime 80687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv40343]) (by decide +kernel)
def pv80687 : PrimeValue := ⟨80687, pr80687⟩
private theorem pr80701 : Nat.Prime 80701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv269]) (by decide +kernel)
def pv80701 : PrimeValue := ⟨80701, pr80701⟩
private theorem pr80713 : Nat.Prime 80713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv59]) (by decide +kernel)
def pv80713 : PrimeValue := ⟨80713, pr80713⟩
private theorem pr80737 : Nat.Prime 80737 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv80737 : PrimeValue := ⟨80737, pr80737⟩
private theorem pr80747 : Nat.Prime 80747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv859]) (by decide +kernel)
def pv80747 : PrimeValue := ⟨80747, pr80747⟩
private theorem pr80749 : Nat.Prime 80749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2243]) (by decide +kernel)
def pv80749 : PrimeValue := ⟨80749, pr80749⟩
private theorem pr80761 : Nat.Prime 80761 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv673]) (by decide +kernel)
def pv80761 : PrimeValue := ⟨80761, pr80761⟩
private theorem pr80777 : Nat.Prime 80777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv439]) (by decide +kernel)
def pv80777 : PrimeValue := ⟨80777, pr80777⟩
private theorem pr80783 : Nat.Prime 80783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv239]) (by decide +kernel)
def pv80783 : PrimeValue := ⟨80783, pr80783⟩
private theorem pr80789 : Nat.Prime 80789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv1063]) (by decide +kernel)
def pv80789 : PrimeValue := ⟨80789, pr80789⟩
private theorem pr80803 : Nat.Prime 80803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv80803 : PrimeValue := ⟨80803, pr80803⟩
private theorem pr80809 : Nat.Prime 80809 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv13,pv37]) (by decide +kernel)
def pv80809 : PrimeValue := ⟨80809, pr80809⟩
private theorem pr80819 : Nat.Prime 80819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv2377]) (by decide +kernel)
def pv80819 : PrimeValue := ⟨80819, pr80819⟩
private theorem pr80831 : Nat.Prime 80831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv59,pv137]) (by decide +kernel)
def pv80831 : PrimeValue := ⟨80831, pr80831⟩
private theorem pr80833 : Nat.Prime 80833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv421]) (by decide +kernel)
def pv80833 : PrimeValue := ⟨80833, pr80833⟩
private theorem pr80849 : Nat.Prime 80849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv163]) (by decide +kernel)
def pv80849 : PrimeValue := ⟨80849, pr80849⟩
private theorem pr80863 : Nat.Prime 80863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13477]) (by decide +kernel)
def pv80863 : PrimeValue := ⟨80863, pr80863⟩
private theorem pr80897 : Nat.Prime 80897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79]) (by decide +kernel)
def pv80897 : PrimeValue := ⟨80897, pr80897⟩
private theorem pr80909 : Nat.Prime 80909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv179]) (by decide +kernel)
def pv80909 : PrimeValue := ⟨80909, pr80909⟩
private theorem pr80917 : Nat.Prime 80917 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv613]) (by decide +kernel)
def pv80917 : PrimeValue := ⟨80917, pr80917⟩
private theorem pr80923 : Nat.Prime 80923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13487]) (by decide +kernel)
def pv80923 : PrimeValue := ⟨80923, pr80923⟩
private theorem pr80929 : Nat.Prime 80929 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv281]) (by decide +kernel)
def pv80929 : PrimeValue := ⟨80929, pr80929⟩
private theorem pr80933 : Nat.Prime 80933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv20233]) (by decide +kernel)
def pv80933 : PrimeValue := ⟨80933, pr80933⟩
private theorem pr80953 : Nat.Prime 80953 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv3373]) (by decide +kernel)
def pv80953 : PrimeValue := ⟨80953, pr80953⟩
private theorem pr80963 : Nat.Prime 80963 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv5783]) (by decide +kernel)
def pv80963 : PrimeValue := ⟨80963, pr80963⟩
private theorem pr80989 : Nat.Prime 80989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv397]) (by decide +kernel)
def pv80989 : PrimeValue := ⟨80989, pr80989⟩
private theorem pr81001 : Nat.Prime 81001 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv81001 : PrimeValue := ⟨81001, pr81001⟩
private theorem pr81013 : Nat.Prime 81013 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv43,pv157]) (by decide +kernel)
def pv81013 : PrimeValue := ⟨81013, pr81013⟩
private theorem pr81017 : Nat.Prime 81017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv19,pv41]) (by decide +kernel)
def pv81017 : PrimeValue := ⟨81017, pr81017⟩
private theorem pr81019 : Nat.Prime 81019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv643]) (by decide +kernel)
def pv81019 : PrimeValue := ⟨81019, pr81019⟩
private theorem pr81023 : Nat.Prime 81023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv2383]) (by decide +kernel)
def pv81023 : PrimeValue := ⟨81023, pr81023⟩
private theorem pr81031 : Nat.Prime 81031 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv37,pv73]) (by decide +kernel)
def pv81031 : PrimeValue := ⟨81031, pr81031⟩
private theorem pr81041 : Nat.Prime 81041 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv5,pv1013]) (by decide +kernel)
def pv81041 : PrimeValue := ⟨81041, pr81041⟩
private theorem pr81043 : Nat.Prime 81043 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv1039]) (by decide +kernel)
def pv81043 : PrimeValue := ⟨81043, pr81043⟩
private theorem pr81047 : Nat.Prime 81047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv827]) (by decide +kernel)
def pv81047 : PrimeValue := ⟨81047, pr81047⟩
private theorem pr81049 : Nat.Prime 81049 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv307]) (by decide +kernel)
def pv81049 : PrimeValue := ⟨81049, pr81049⟩
private theorem pr81071 : Nat.Prime 81071 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv67]) (by decide +kernel)
def pv81071 : PrimeValue := ⟨81071, pr81071⟩
private theorem pr81077 : Nat.Prime 81077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv20269]) (by decide +kernel)
def pv81077 : PrimeValue := ⟨81077, pr81077⟩
private theorem pr81083 : Nat.Prime 81083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv571]) (by decide +kernel)
def pv81083 : PrimeValue := ⟨81083, pr81083⟩
private theorem pr81097 : Nat.Prime 81097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv109]) (by decide +kernel)
def pv81097 : PrimeValue := ⟨81097, pr81097⟩
private theorem pr81101 : Nat.Prime 81101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv811]) (by decide +kernel)
def pv81101 : PrimeValue := ⟨81101, pr81101⟩
private theorem pr81119 : Nat.Prime 81119 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv40559]) (by decide +kernel)
def pv81119 : PrimeValue := ⟨81119, pr81119⟩
private theorem pr81131 : Nat.Prime 81131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv61]) (by decide +kernel)
def pv81131 : PrimeValue := ⟨81131, pr81131⟩
private theorem pr81157 : Nat.Prime 81157 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv6763]) (by decide +kernel)
def pv81157 : PrimeValue := ⟨81157, pr81157⟩
private theorem pr81163 : Nat.Prime 81163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv167]) (by decide +kernel)
def pv81163 : PrimeValue := ⟨81163, pr81163⟩
private theorem pr81173 : Nat.Prime 81173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv223]) (by decide +kernel)
def pv81173 : PrimeValue := ⟨81173, pr81173⟩
private theorem pr81181 : Nat.Prime 81181 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv41]) (by decide +kernel)
def pv81181 : PrimeValue := ⟨81181, pr81181⟩
private theorem pr81197 : Nat.Prime 81197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv383]) (by decide +kernel)
def pv81197 : PrimeValue := ⟨81197, pr81197⟩
private theorem pr81199 : Nat.Prime 81199 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13,pv347]) (by decide +kernel)
def pv81199 : PrimeValue := ⟨81199, pr81199⟩
private theorem pr81203 : Nat.Prime 81203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv3691]) (by decide +kernel)
def pv81203 : PrimeValue := ⟨81203, pr81203⟩
private theorem pr81223 : Nat.Prime 81223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13537]) (by decide +kernel)
def pv81223 : PrimeValue := ⟨81223, pr81223⟩
private theorem pr81233 : Nat.Prime 81233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5077]) (by decide +kernel)
def pv81233 : PrimeValue := ⟨81233, pr81233⟩
private theorem pr81239 : Nat.Prime 81239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv151,pv269]) (by decide +kernel)
def pv81239 : PrimeValue := ⟨81239, pr81239⟩
private theorem pr81281 : Nat.Prime 81281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv127]) (by decide +kernel)
def pv81281 : PrimeValue := ⟨81281, pr81281⟩
private theorem pr81283 : Nat.Prime 81283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv23,pv31]) (by decide +kernel)
def pv81283 : PrimeValue := ⟨81283, pr81283⟩
private theorem pr81293 : Nat.Prime 81293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv20323]) (by decide +kernel)
def pv81293 : PrimeValue := ⟨81293, pr81293⟩
private theorem pr81299 : Nat.Prime 81299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv5807]) (by decide +kernel)
def pv81299 : PrimeValue := ⟨81299, pr81299⟩
private theorem pr81307 : Nat.Prime 81307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4517]) (by decide +kernel)
def pv81307 : PrimeValue := ⟨81307, pr81307⟩
private theorem pr81331 : Nat.Prime 81331 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv2711]) (by decide +kernel)
def pv81331 : PrimeValue := ⟨81331, pr81331⟩
private theorem pr81343 : Nat.Prime 81343 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv4519]) (by decide +kernel)
def pv81343 : PrimeValue := ⟨81343, pr81343⟩
private theorem pr81349 : Nat.Prime 81349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6779]) (by decide +kernel)
def pv81349 : PrimeValue := ⟨81349, pr81349⟩
private theorem pr81353 : Nat.Prime 81353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10169]) (by decide +kernel)
def pv81353 : PrimeValue := ⟨81353, pr81353⟩
private theorem pr81359 : Nat.Prime 81359 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv19,pv2141]) (by decide +kernel)
def pv81359 : PrimeValue := ⟨81359, pr81359⟩
private theorem pr81371 : Nat.Prime 81371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv79,pv103]) (by decide +kernel)
def pv81371 : PrimeValue := ⟨81371, pr81371⟩
private theorem pr81373 : Nat.Prime 81373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6781]) (by decide +kernel)
def pv81373 : PrimeValue := ⟨81373, pr81373⟩
private theorem pr81401 : Nat.Prime 81401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv37]) (by decide +kernel)
def pv81401 : PrimeValue := ⟨81401, pr81401⟩
private theorem pr81409 : Nat.Prime 81409 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv53]) (by decide +kernel)
def pv81409 : PrimeValue := ⟨81409, pr81409⟩
private theorem pr81421 : Nat.Prime 81421 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv23,pv59]) (by decide +kernel)
def pv81421 : PrimeValue := ⟨81421, pr81421⟩
private theorem pr81439 : Nat.Prime 81439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv277]) (by decide +kernel)
def pv81439 : PrimeValue := ⟨81439, pr81439⟩
private theorem pr81457 : Nat.Prime 81457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1697]) (by decide +kernel)
def pv81457 : PrimeValue := ⟨81457, pr81457⟩
private theorem pr81463 : Nat.Prime 81463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13577]) (by decide +kernel)
def pv81463 : PrimeValue := ⟨81463, pr81463⟩
private theorem pr81509 : Nat.Prime 81509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv41,pv71]) (by decide +kernel)
def pv81509 : PrimeValue := ⟨81509, pr81509⟩
private theorem pr81517 : Nat.Prime 81517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6793]) (by decide +kernel)
def pv81517 : PrimeValue := ⟨81517, pr81517⟩
private theorem pr81527 : Nat.Prime 81527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv40763]) (by decide +kernel)
def pv81527 : PrimeValue := ⟨81527, pr81527⟩
private theorem pr81533 : Nat.Prime 81533 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv17,pv109]) (by decide +kernel)
def pv81533 : PrimeValue := ⟨81533, pr81533⟩
private theorem pr81547 : Nat.Prime 81547 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13591]) (by decide +kernel)
def pv81547 : PrimeValue := ⟨81547, pr81547⟩
private theorem pr81551 : Nat.Prime 81551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv233]) (by decide +kernel)
def pv81551 : PrimeValue := ⟨81551, pr81551⟩
private theorem pr81553 : Nat.Prime 81553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1699]) (by decide +kernel)
def pv81553 : PrimeValue := ⟨81553, pr81553⟩
private theorem pr81559 : Nat.Prime 81559 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv23,pv197]) (by decide +kernel)
def pv81559 : PrimeValue := ⟨81559, pr81559⟩
private theorem pr81563 : Nat.Prime 81563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv3137]) (by decide +kernel)
def pv81563 : PrimeValue := ⟨81563, pr81563⟩
private theorem pr81569 : Nat.Prime 81569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2549]) (by decide +kernel)
def pv81569 : PrimeValue := ⟨81569, pr81569⟩
private theorem pr81611 : Nat.Prime 81611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv8161]) (by decide +kernel)
def pv81611 : PrimeValue := ⟨81611, pr81611⟩
private theorem pr81619 : Nat.Prime 81619 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv61,pv223]) (by decide +kernel)
def pv81619 : PrimeValue := ⟨81619, pr81619⟩
private theorem pr81629 : Nat.Prime 81629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv20407]) (by decide +kernel)
def pv81629 : PrimeValue := ⟨81629, pr81629⟩
private theorem pr81637 : Nat.Prime 81637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6803]) (by decide +kernel)
def pv81637 : PrimeValue := ⟨81637, pr81637⟩
private theorem pr81647 : Nat.Prime 81647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv40823]) (by decide +kernel)
def pv81647 : PrimeValue := ⟨81647, pr81647⟩
private theorem pr81649 : Nat.Prime 81649 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv81649 : PrimeValue := ⟨81649, pr81649⟩
private theorem pr81667 : Nat.Prime 81667 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv349]) (by decide +kernel)
def pv81667 : PrimeValue := ⟨81667, pr81667⟩
private theorem pr81671 : Nat.Prime 81671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv8167]) (by decide +kernel)
def pv81671 : PrimeValue := ⟨81671, pr81671⟩
private theorem pr81677 : Nat.Prime 81677 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv2917]) (by decide +kernel)
def pv81677 : PrimeValue := ⟨81677, pr81677⟩
private theorem pr81689 : Nat.Prime 81689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10211]) (by decide +kernel)
def pv81689 : PrimeValue := ⟨81689, pr81689⟩
private theorem pr81701 : Nat.Prime 81701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv43]) (by decide +kernel)
def pv81701 : PrimeValue := ⟨81701, pr81701⟩
private theorem pr81703 : Nat.Prime 81703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv89]) (by decide +kernel)
def pv81703 : PrimeValue := ⟨81703, pr81703⟩
private theorem pr81707 : Nat.Prime 81707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv40853]) (by decide +kernel)
def pv81707 : PrimeValue := ⟨81707, pr81707⟩
private theorem pr81727 : Nat.Prime 81727 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53,pv257]) (by decide +kernel)
def pv81727 : PrimeValue := ⟨81727, pr81727⟩
private theorem pr81737 : Nat.Prime 81737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv601]) (by decide +kernel)
def pv81737 : PrimeValue := ⟨81737, pr81737⟩
private theorem pr81749 : Nat.Prime 81749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv191]) (by decide +kernel)
def pv81749 : PrimeValue := ⟨81749, pr81749⟩
private theorem pr81761 : Nat.Prime 81761 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv7,pv73]) (by decide +kernel)
def pv81761 : PrimeValue := ⟨81761, pr81761⟩
private theorem pr81769 : Nat.Prime 81769 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv3407]) (by decide +kernel)
def pv81769 : PrimeValue := ⟨81769, pr81769⟩
private theorem pr81773 : Nat.Prime 81773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv20443]) (by decide +kernel)
def pv81773 : PrimeValue := ⟨81773, pr81773⟩
private theorem pr81799 : Nat.Prime 81799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13633]) (by decide +kernel)
def pv81799 : PrimeValue := ⟨81799, pr81799⟩
private theorem pr81817 : Nat.Prime 81817 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv487]) (by decide +kernel)
def pv81817 : PrimeValue := ⟨81817, pr81817⟩
private theorem pr81839 : Nat.Prime 81839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv17,pv29,pv83]) (by decide +kernel)
def pv81839 : PrimeValue := ⟨81839, pr81839⟩
private theorem pr81847 : Nat.Prime 81847 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4547]) (by decide +kernel)
def pv81847 : PrimeValue := ⟨81847, pr81847⟩
private theorem pr81853 : Nat.Prime 81853 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19,pv359]) (by decide +kernel)
def pv81853 : PrimeValue := ⟨81853, pr81853⟩
private theorem pr81869 : Nat.Prime 81869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv211]) (by decide +kernel)
def pv81869 : PrimeValue := ⟨81869, pr81869⟩
private theorem pr81883 : Nat.Prime 81883 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4549]) (by decide +kernel)
def pv81883 : PrimeValue := ⟨81883, pr81883⟩
private theorem pr81899 : Nat.Prime 81899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv40949]) (by decide +kernel)
def pv81899 : PrimeValue := ⟨81899, pr81899⟩
private theorem pr81901 : Nat.Prime 81901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv81901 : PrimeValue := ⟨81901, pr81901⟩
private theorem pr81919 : Nat.Prime 81919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv41]) (by decide +kernel)
def pv81919 : PrimeValue := ⟨81919, pr81919⟩
private theorem pr81929 : Nat.Prime 81929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv19]) (by decide +kernel)
def pv81929 : PrimeValue := ⟨81929, pr81929⟩
private theorem pr81931 : Nat.Prime 81931 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv2731]) (by decide +kernel)
def pv81931 : PrimeValue := ⟨81931, pr81931⟩
private theorem pr81937 : Nat.Prime 81937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv569]) (by decide +kernel)
def pv81937 : PrimeValue := ⟨81937, pr81937⟩
private theorem pr81943 : Nat.Prime 81943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1951]) (by decide +kernel)
def pv81943 : PrimeValue := ⟨81943, pr81943⟩
private theorem pr81953 : Nat.Prime 81953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv197]) (by decide +kernel)
def pv81953 : PrimeValue := ⟨81953, pr81953⟩
private theorem pr81967 : Nat.Prime 81967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv719]) (by decide +kernel)
def pv81967 : PrimeValue := ⟨81967, pr81967⟩
private theorem pr81971 : Nat.Prime 81971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv1171]) (by decide +kernel)
def pv81971 : PrimeValue := ⟨81971, pr81971⟩
private theorem pr81973 : Nat.Prime 81973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv81973 : PrimeValue := ⟨81973, pr81973⟩
private theorem pr82003 : Nat.Prime 82003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv173]) (by decide +kernel)
def pv82003 : PrimeValue := ⟨82003, pr82003⟩
private theorem pr82007 : Nat.Prime 82007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv131,pv313]) (by decide +kernel)
def pv82007 : PrimeValue := ⟨82007, pr82007⟩
private theorem pr82009 : Nat.Prime 82009 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv67]) (by decide +kernel)
def pv82009 : PrimeValue := ⟨82009, pr82009⟩
private theorem pr82021 : Nat.Prime 82021 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv1367]) (by decide +kernel)
def pv82021 : PrimeValue := ⟨82021, pr82021⟩
private theorem pr82031 : Nat.Prime 82031 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv631]) (by decide +kernel)
def pv82031 : PrimeValue := ⟨82031, pr82031⟩
private theorem pr82037 : Nat.Prime 82037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv20509]) (by decide +kernel)
def pv82037 : PrimeValue := ⟨82037, pr82037⟩
private theorem pr82039 : Nat.Prime 82039 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv113]) (by decide +kernel)
def pv82039 : PrimeValue := ⟨82039, pr82039⟩
private theorem pr82051 : Nat.Prime 82051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv547]) (by decide +kernel)
def pv82051 : PrimeValue := ⟨82051, pr82051⟩
private theorem pr82067 : Nat.Prime 82067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv1109]) (by decide +kernel)
def pv82067 : PrimeValue := ⟨82067, pr82067⟩
private theorem pr82073 : Nat.Prime 82073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10259]) (by decide +kernel)
def pv82073 : PrimeValue := ⟨82073, pr82073⟩
private theorem pr82129 : Nat.Prime 82129 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv29,pv59]) (by decide +kernel)
def pv82129 : PrimeValue := ⟨82129, pr82129⟩
private theorem pr82139 : Nat.Prime 82139 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv5867]) (by decide +kernel)
def pv82139 : PrimeValue := ⟨82139, pr82139⟩
private theorem pr82141 : Nat.Prime 82141 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv82141 : PrimeValue := ⟨82141, pr82141⟩
private theorem pr82153 : Nat.Prime 82153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv163]) (by decide +kernel)
def pv82153 : PrimeValue := ⟨82153, pr82153⟩
private theorem pr82163 : Nat.Prime 82163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41081]) (by decide +kernel)
def pv82163 : PrimeValue := ⟨82163, pr82163⟩
private theorem pr82171 : Nat.Prime 82171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv83]) (by decide +kernel)
def pv82171 : PrimeValue := ⟨82171, pr82171⟩
private theorem pr82183 : Nat.Prime 82183 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv13697]) (by decide +kernel)
def pv82183 : PrimeValue := ⟨82183, pr82183⟩
private theorem pr82189 : Nat.Prime 82189 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv761]) (by decide +kernel)
def pv82189 : PrimeValue := ⟨82189, pr82189⟩
private theorem pr82193 : Nat.Prime 82193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv467]) (by decide +kernel)
def pv82193 : PrimeValue := ⟨82193, pr82193⟩
private theorem pr82207 : Nat.Prime 82207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4567]) (by decide +kernel)
def pv82207 : PrimeValue := ⟨82207, pr82207⟩
private theorem pr82217 : Nat.Prime 82217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv239]) (by decide +kernel)
def pv82217 : PrimeValue := ⟨82217, pr82217⟩
private theorem pr82219 : Nat.Prime 82219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv193]) (by decide +kernel)
def pv82219 : PrimeValue := ⟨82219, pr82219⟩
private theorem pr82223 : Nat.Prime 82223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv839]) (by decide +kernel)
def pv82223 : PrimeValue := ⟨82223, pr82223⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
