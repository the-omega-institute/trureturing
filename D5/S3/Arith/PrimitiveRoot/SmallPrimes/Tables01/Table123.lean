/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table123
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table123.pv661483
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table090
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table091

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr661483 : Nat.Prime 661483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv36749]) (by decide +kernel)
def pv661483 : PrimeValue := ⟨661483, pr661483⟩
private theorem pr661553 : Nat.Prime 661553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv173,pv239]) (by decide +kernel)
def pv661553 : PrimeValue := ⟨661553, pr661553⟩
private theorem pr661663 : Nat.Prime 661663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12253]) (by decide +kernel)
def pv661663 : PrimeValue := ⟨661663, pr661663⟩
private theorem pr661849 : Nat.Prime 661849 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv23,pv109]) (by decide +kernel)
def pv661849 : PrimeValue := ⟨661849, pr661849⟩
private theorem pr661889 : Nat.Prime 661889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5171]) (by decide +kernel)
def pv661889 : PrimeValue := ⟨661889, pr661889⟩
private theorem pr661949 : Nat.Prime 661949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv47,pv503]) (by decide +kernel)
def pv661949 : PrimeValue := ⟨661949, pr661949⟩
private theorem pr661961 : Nat.Prime 661961 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv13,pv19,pv67]) (by decide +kernel)
def pv661961 : PrimeValue := ⟨661961, pr661961⟩
private theorem pr662003 : Nat.Prime 662003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv30091]) (by decide +kernel)
def pv662003 : PrimeValue := ⟨662003, pr662003⟩
private theorem pr662047 : Nat.Prime 662047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv1433]) (by decide +kernel)
def pv662047 : PrimeValue := ⟨662047, pr662047⟩
private theorem pr662111 : Nat.Prime 662111 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv73,pv907]) (by decide +kernel)
def pv662111 : PrimeValue := ⟨662111, pr662111⟩
private theorem pr662203 : Nat.Prime 662203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12263]) (by decide +kernel)
def pv662203 : PrimeValue := ⟨662203, pr662203⟩
private theorem pr662227 : Nat.Prime 662227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv37,pv157]) (by decide +kernel)
def pv662227 : PrimeValue := ⟨662227, pr662227⟩
private theorem pr662309 : Nat.Prime 662309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv313]) (by decide +kernel)
def pv662309 : PrimeValue := ⟨662309, pr662309⟩
private theorem pr662323 : Nat.Prime 662323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv167,pv661]) (by decide +kernel)
def pv662323 : PrimeValue := ⟨662323, pr662323⟩
private theorem pr662339 : Nat.Prime 662339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv89]) (by decide +kernel)
def pv662339 : PrimeValue := ⟨662339, pr662339⟩
private theorem pr662531 : Nat.Prime 662531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv19,pv317]) (by decide +kernel)
def pv662531 : PrimeValue := ⟨662531, pr662531⟩
private theorem pr662539 : Nat.Prime 662539 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv4801]) (by decide +kernel)
def pv662539 : PrimeValue := ⟨662539, pr662539⟩
private theorem pr662591 : Nat.Prime 662591 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv173,pv383]) (by decide +kernel)
def pv662591 : PrimeValue := ⟨662591, pr662591⟩
private theorem pr662689 : Nat.Prime 662689 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv59]) (by decide +kernel)
def pv662689 : PrimeValue := ⟨662689, pr662689⟩
private theorem pr662713 : Nat.Prime 662713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv53,pv521]) (by decide +kernel)
def pv662713 : PrimeValue := ⟨662713, pr662713⟩
private theorem pr662771 : Nat.Prime 662771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv191,pv347]) (by decide +kernel)
def pv662771 : PrimeValue := ⟨662771, pr662771⟩
private theorem pr662789 : Nat.Prime 662789 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv7,pv23671]) (by decide +kernel)
def pv662789 : PrimeValue := ⟨662789, pr662789⟩
private theorem pr662797 : Nat.Prime 662797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv19]) (by decide +kernel)
def pv662797 : PrimeValue := ⟨662797, pr662797⟩
private theorem pr662833 : Nat.Prime 662833 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv4603]) (by decide +kernel)
def pv662833 : PrimeValue := ⟨662833, pr662833⟩
private theorem pr662917 : Nat.Prime 662917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv55243]) (by decide +kernel)
def pv662917 : PrimeValue := ⟨662917, pr662917⟩
private theorem pr662951 : Nat.Prime 662951 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13259]) (by decide +kernel)
def pv662951 : PrimeValue := ⟨662951, pr662951⟩
private theorem pr663007 : Nat.Prime 663007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv110501]) (by decide +kernel)
def pv663007 : PrimeValue := ⟨663007, pr663007⟩
private theorem pr663037 : Nat.Prime 663037 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv5023]) (by decide +kernel)
def pv663037 : PrimeValue := ⟨663037, pr663037⟩
private theorem pr663097 : Nat.Prime 663097 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv3947]) (by decide +kernel)
def pv663097 : PrimeValue := ⟨663097, pr663097⟩
private theorem pr663191 : Nat.Prime 663191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv6029]) (by decide +kernel)
def pv663191 : PrimeValue := ⟨663191, pr663191⟩
private theorem pr663209 : Nat.Prime 663209 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv7,pv13,pv911]) (by decide +kernel)
def pv663209 : PrimeValue := ⟨663209, pr663209⟩
private theorem pr663529 : Nat.Prime 663529 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv27647]) (by decide +kernel)
def pv663529 : PrimeValue := ⟨663529, pr663529⟩
private theorem pr663599 : Nat.Prime 663599 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv13,pv25523]) (by decide +kernel)
def pv663599 : PrimeValue := ⟨663599, pr663599⟩
private theorem pr663713 : Nat.Prime 663713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv2963]) (by decide +kernel)
def pv663713 : PrimeValue := ⟨663713, pr663713⟩
private theorem pr663763 : Nat.Prime 663763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv89,pv113]) (by decide +kernel)
def pv663763 : PrimeValue := ⟨663763, pr663763⟩
private theorem pr664043 : Nat.Prime 664043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv107]) (by decide +kernel)
def pv664043 : PrimeValue := ⟨664043, pr664043⟩
private theorem pr664091 : Nat.Prime 664091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv53,pv179]) (by decide +kernel)
def pv664091 : PrimeValue := ⟨664091, pr664091⟩
private theorem pr664109 : Nat.Prime 664109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv166027]) (by decide +kernel)
def pv664109 : PrimeValue := ⟨664109, pr664109⟩
private theorem pr664193 : Nat.Prime 664193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5189]) (by decide +kernel)
def pv664193 : PrimeValue := ⟨664193, pr664193⟩
private theorem pr664253 : Nat.Prime 664253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv166063]) (by decide +kernel)
def pv664253 : PrimeValue := ⟨664253, pr664253⟩
private theorem pr664357 : Nat.Prime 664357 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv719]) (by decide +kernel)
def pv664357 : PrimeValue := ⟨664357, pr664357⟩
private theorem pr664369 : Nat.Prime 664369 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13841]) (by decide +kernel)
def pv664369 : PrimeValue := ⟨664369, pr664369⟩
private theorem pr664403 : Nat.Prime 664403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv332201]) (by decide +kernel)
def pv664403 : PrimeValue := ⟨664403, pr664403⟩
private theorem pr664421 : Nat.Prime 664421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv139,pv239]) (by decide +kernel)
def pv664421 : PrimeValue := ⟨664421, pr664421⟩
private theorem pr664571 : Nat.Prime 664571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv66457]) (by decide +kernel)
def pv664571 : PrimeValue := ⟨664571, pr664571⟩
private theorem pr664679 : Nat.Prime 664679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv197,pv241]) (by decide +kernel)
def pv664679 : PrimeValue := ⟨664679, pr664679⟩
private theorem pr664739 : Nat.Prime 664739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv73,pv157]) (by decide +kernel)
def pv664739 : PrimeValue := ⟨664739, pr664739⟩
private theorem pr664799 : Nat.Prime 664799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv332399]) (by decide +kernel)
def pv664799 : PrimeValue := ⟨664799, pr664799⟩
private theorem pr664949 : Nat.Prime 664949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv166237]) (by decide +kernel)
def pv664949 : PrimeValue := ⟨664949, pr664949⟩
private theorem pr665017 : Nat.Prime 665017 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv229]) (by decide +kernel)
def pv665017 : PrimeValue := ⟨665017, pr665017⟩
private theorem pr665029 : Nat.Prime 665029 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv29]) (by decide +kernel)
def pv665029 : PrimeValue := ⟨665029, pr665029⟩
private theorem pr665051 : Nat.Prime 665051 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv47,pv283]) (by decide +kernel)
def pv665051 : PrimeValue := ⟨665051, pr665051⟩
private theorem pr665111 : Nat.Prime 665111 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv227,pv293]) (by decide +kernel)
def pv665111 : PrimeValue := ⟨665111, pr665111⟩
private theorem pr665279 : Nat.Prime 665279 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv17,pv1151]) (by decide +kernel)
def pv665279 : PrimeValue := ⟨665279, pr665279⟩
private theorem pr665429 : Nat.Prime 665429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv166357]) (by decide +kernel)
def pv665429 : PrimeValue := ⟨665429, pr665429⟩
private theorem pr665479 : Nat.Prime 665479 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv3361]) (by decide +kernel)
def pv665479 : PrimeValue := ⟨665479, pr665479⟩
private theorem pr665603 : Nat.Prime 665603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv47543]) (by decide +kernel)
def pv665603 : PrimeValue := ⟨665603, pr665603⟩
private theorem pr665617 : Nat.Prime 665617 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv7,pv283]) (by decide +kernel)
def pv665617 : PrimeValue := ⟨665617, pr665617⟩
private theorem pr665783 : Nat.Prime 665783 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv13,pv29,pv883]) (by decide +kernel)
def pv665783 : PrimeValue := ⟨665783, pr665783⟩
private theorem pr665789 : Nat.Prime 665789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv9791]) (by decide +kernel)
def pv665789 : PrimeValue := ⟨665789, pr665789⟩
private theorem pr665857 : Nat.Prime 665857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv665857 : PrimeValue := ⟨665857, pr665857⟩
private theorem pr665923 : Nat.Prime 665923 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv2707]) (by decide +kernel)
def pv665923 : PrimeValue := ⟨665923, pr665923⟩
private theorem pr665953 : Nat.Prime 665953 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv991]) (by decide +kernel)
def pv665953 : PrimeValue := ⟨665953, pr665953⟩
private theorem pr665993 : Nat.Prime 665993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv59,pv83]) (by decide +kernel)
def pv665993 : PrimeValue := ⟨665993, pr665993⟩
private theorem pr666023 : Nat.Prime 666023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv113,pv421]) (by decide +kernel)
def pv666023 : PrimeValue := ⟨666023, pr666023⟩
private theorem pr666073 : Nat.Prime 666073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv29]) (by decide +kernel)
def pv666073 : PrimeValue := ⟨666073, pr666073⟩
private theorem pr666233 : Nat.Prime 666233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11897]) (by decide +kernel)
def pv666233 : PrimeValue := ⟨666233, pr666233⟩
private theorem pr666277 : Nat.Prime 666277 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv4271]) (by decide +kernel)
def pv666277 : PrimeValue := ⟨666277, pr666277⟩
private theorem pr666493 : Nat.Prime 666493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv55541]) (by decide +kernel)
def pv666493 : PrimeValue := ⟨666493, pr666493⟩
private theorem pr666529 : Nat.Prime 666529 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv53,pv131]) (by decide +kernel)
def pv666529 : PrimeValue := ⟨666529, pr666529⟩
private theorem pr666607 : Nat.Prime 666607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv241,pv461]) (by decide +kernel)
def pv666607 : PrimeValue := ⟨666607, pr666607⟩
private theorem pr666773 : Nat.Prime 666773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv166693]) (by decide +kernel)
def pv666773 : PrimeValue := ⟨666773, pr666773⟩
private theorem pr666959 : Nat.Prime 666959 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv333479]) (by decide +kernel)
def pv666959 : PrimeValue := ⟨666959, pr666959⟩
private theorem pr666983 : Nat.Prime 666983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv333491]) (by decide +kernel)
def pv666983 : PrimeValue := ⟨666983, pr666983⟩
private theorem pr667181 : Nat.Prime 667181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv33359]) (by decide +kernel)
def pv667181 : PrimeValue := ⟨667181, pr667181⟩
private theorem pr667211 : Nat.Prime 667211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv66721]) (by decide +kernel)
def pv667211 : PrimeValue := ⟨667211, pr667211⟩
private theorem pr667309 : Nat.Prime 667309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv55609]) (by decide +kernel)
def pv667309 : PrimeValue := ⟨667309, pr667309⟩
private theorem pr667417 : Nat.Prime 667417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv27809]) (by decide +kernel)
def pv667417 : PrimeValue := ⟨667417, pr667417⟩
private theorem pr667507 : Nat.Prime 667507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv691]) (by decide +kernel)
def pv667507 : PrimeValue := ⟨667507, pr667507⟩
private theorem pr667549 : Nat.Prime 667549 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv883]) (by decide +kernel)
def pv667549 : PrimeValue := ⟨667549, pr667549⟩
private theorem pr667643 : Nat.Prime 667643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv333821]) (by decide +kernel)
def pv667643 : PrimeValue := ⟨667643, pr667643⟩
private theorem pr667687 : Nat.Prime 667687 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv257,pv433]) (by decide +kernel)
def pv667687 : PrimeValue := ⟨667687, pr667687⟩
private theorem pr667699 : Nat.Prime 667699 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv5857]) (by decide +kernel)
def pv667699 : PrimeValue := ⟨667699, pr667699⟩
private theorem pr667781 : Nat.Prime 667781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv173,pv193]) (by decide +kernel)
def pv667781 : PrimeValue := ⟨667781, pr667781⟩
private theorem pr667949 : Nat.Prime 667949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv166987]) (by decide +kernel)
def pv667949 : PrimeValue := ⟨667949, pr667949⟩
private theorem pr668009 : Nat.Prime 668009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv7591]) (by decide +kernel)
def pv668009 : PrimeValue := ⟨668009, pr668009⟩
private theorem pr668051 : Nat.Prime 668051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv431]) (by decide +kernel)
def pv668051 : PrimeValue := ⟨668051, pr668051⟩
private theorem pr668089 : Nat.Prime 668089 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1031]) (by decide +kernel)
def pv668089 : PrimeValue := ⟨668089, pr668089⟩
private theorem pr668093 : Nat.Prime 668093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv167023]) (by decide +kernel)
def pv668093 : PrimeValue := ⟨668093, pr668093⟩
private theorem pr668243 : Nat.Prime 668243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv73,pv199]) (by decide +kernel)
def pv668243 : PrimeValue := ⟨668243, pr668243⟩
private theorem pr668273 : Nat.Prime 668273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv3797]) (by decide +kernel)
def pv668273 : PrimeValue := ⟨668273, pr668273⟩
private theorem pr668471 : Nat.Prime 668471 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv59,pv103]) (by decide +kernel)
def pv668471 : PrimeValue := ⟨668471, pr668471⟩
private theorem pr668513 : Nat.Prime 668513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv1607]) (by decide +kernel)
def pv668513 : PrimeValue := ⟨668513, pr668513⟩
private theorem pr668579 : Nat.Prime 668579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv334289]) (by decide +kernel)
def pv668579 : PrimeValue := ⟨668579, pr668579⟩
private theorem pr668713 : Nat.Prime 668713 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11,pv17,pv149]) (by decide +kernel)
def pv668713 : PrimeValue := ⟨668713, pr668713⟩
private theorem pr668803 : Nat.Prime 668803 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv111467]) (by decide +kernel)
def pv668803 : PrimeValue := ⟨668803, pr668803⟩
private theorem pr668813 : Nat.Prime 668813 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv4519]) (by decide +kernel)
def pv668813 : PrimeValue := ⟨668813, pr668813⟩
private theorem pr668989 : Nat.Prime 668989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18583]) (by decide +kernel)
def pv668989 : PrimeValue := ⟨668989, pr668989⟩
private theorem pr669283 : Nat.Prime 669283 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv331,pv337]) (by decide +kernel)
def pv669283 : PrimeValue := ⟨669283, pr669283⟩
private theorem pr669401 : Nat.Prime 669401 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv3347]) (by decide +kernel)
def pv669401 : PrimeValue := ⟨669401, pr669401⟩
private theorem pr669433 : Nat.Prime 669433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv27893]) (by decide +kernel)
def pv669433 : PrimeValue := ⟨669433, pr669433⟩
private theorem pr669611 : Nat.Prime 669611 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv29,pv2309]) (by decide +kernel)
def pv669611 : PrimeValue := ⟨669611, pr669611⟩
private theorem pr669637 : Nat.Prime 669637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv89]) (by decide +kernel)
def pv669637 : PrimeValue := ⟨669637, pr669637⟩
private theorem pr669649 : Nat.Prime 669649 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv1993]) (by decide +kernel)
def pv669649 : PrimeValue := ⟨669649, pr669649⟩
private theorem pr669847 : Nat.Prime 669847 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv111641]) (by decide +kernel)
def pv669847 : PrimeValue := ⟨669847, pr669847⟩
private theorem pr669913 : Nat.Prime 669913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv103,pv271]) (by decide +kernel)
def pv669913 : PrimeValue := ⟨669913, pr669913⟩
private theorem pr669937 : Nat.Prime 669937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv821]) (by decide +kernel)
def pv669937 : PrimeValue := ⟨669937, pr669937⟩
private theorem pr669943 : Nat.Prime 669943 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv13,pv409]) (by decide +kernel)
def pv669943 : PrimeValue := ⟨669943, pr669943⟩
private theorem pr670177 : Nat.Prime 670177 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv13,pv179]) (by decide +kernel)
def pv670177 : PrimeValue := ⟨670177, pr670177⟩
private theorem pr670193 : Nat.Prime 670193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41887]) (by decide +kernel)
def pv670193 : PrimeValue := ⟨670193, pr670193⟩
private theorem pr670223 : Nat.Prime 670223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv977]) (by decide +kernel)
def pv670223 : PrimeValue := ⟨670223, pr670223⟩
private theorem pr670279 : Nat.Prime 670279 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv15959]) (by decide +kernel)
def pv670279 : PrimeValue := ⟨670279, pr670279⟩
private theorem pr670303 : Nat.Prime 670303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12413]) (by decide +kernel)
def pv670303 : PrimeValue := ⟨670303, pr670303⟩
private theorem pr670343 : Nat.Prime 670343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv335171]) (by decide +kernel)
def pv670343 : PrimeValue := ⟨670343, pr670343⟩
private theorem pr670363 : Nat.Prime 670363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv1451]) (by decide +kernel)
def pv670363 : PrimeValue := ⟨670363, pr670363⟩
private theorem pr670511 : Nat.Prime 670511 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv19,pv3529]) (by decide +kernel)
def pv670511 : PrimeValue := ⟨670511, pr670511⟩
private theorem pr670583 : Nat.Prime 670583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv17,pv163]) (by decide +kernel)
def pv670583 : PrimeValue := ⟨670583, pr670583⟩
private theorem pr670627 : Nat.Prime 670627 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1129]) (by decide +kernel)
def pv670627 : PrimeValue := ⟨670627, pr670627⟩
private theorem pr670693 : Nat.Prime 670693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv5081]) (by decide +kernel)
def pv670693 : PrimeValue := ⟨670693, pr670693⟩
private theorem pr670849 : Nat.Prime 670849 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv1747]) (by decide +kernel)
def pv670849 : PrimeValue := ⟨670849, pr670849⟩
private theorem pr670853 : Nat.Prime 670853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv19,pv97]) (by decide +kernel)
def pv670853 : PrimeValue := ⟨670853, pr670853⟩
private theorem pr670897 : Nat.Prime 670897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1553]) (by decide +kernel)
def pv670897 : PrimeValue := ⟨670897, pr670897⟩
private theorem pr670903 : Nat.Prime 670903 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv31,pv3607]) (by decide +kernel)
def pv670903 : PrimeValue := ⟨670903, pr670903⟩
private theorem pr670919 : Nat.Prime 670919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv335459]) (by decide +kernel)
def pv670919 : PrimeValue := ⟨670919, pr670919⟩
private theorem pr670931 : Nat.Prime 670931 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv397]) (by decide +kernel)
def pv670931 : PrimeValue := ⟨670931, pr670931⟩
private theorem pr670991 : Nat.Prime 670991 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv17,pv3947]) (by decide +kernel)
def pv670991 : PrimeValue := ⟨670991, pr670991⟩
private theorem pr671003 : Nat.Prime 671003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv29,pv503]) (by decide +kernel)
def pv671003 : PrimeValue := ⟨671003, pr671003⟩
private theorem pr671017 : Nat.Prime 671017 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv73,pv383]) (by decide +kernel)
def pv671017 : PrimeValue := ⟨671017, pr671017⟩
private theorem pr671039 : Nat.Prime 671039 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv335519]) (by decide +kernel)
def pv671039 : PrimeValue := ⟨671039, pr671039⟩
private theorem pr671059 : Nat.Prime 671059 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv43]) (by decide +kernel)
def pv671059 : PrimeValue := ⟨671059, pr671059⟩
private theorem pr671081 : Nat.Prime 671081 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv883]) (by decide +kernel)
def pv671081 : PrimeValue := ⟨671081, pr671081⟩
private theorem pr671123 : Nat.Prime 671123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv5501]) (by decide +kernel)
def pv671123 : PrimeValue := ⟨671123, pr671123⟩
private theorem pr671141 : Nat.Prime 671141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv1459]) (by decide +kernel)
def pv671141 : PrimeValue := ⟨671141, pr671141⟩
private theorem pr671189 : Nat.Prime 671189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23971]) (by decide +kernel)
def pv671189 : PrimeValue := ⟨671189, pr671189⟩
private theorem pr671201 : Nat.Prime 671201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv839]) (by decide +kernel)
def pv671201 : PrimeValue := ⟨671201, pr671201⟩
private theorem pr671233 : Nat.Prime 671233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv23]) (by decide +kernel)
def pv671233 : PrimeValue := ⟨671233, pr671233⟩
private theorem pr671249 : Nat.Prime 671249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41953]) (by decide +kernel)
def pv671249 : PrimeValue := ⟨671249, pr671249⟩
private theorem pr671257 : Nat.Prime 671257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv9323]) (by decide +kernel)
def pv671257 : PrimeValue := ⟨671257, pr671257⟩
private theorem pr671269 : Nat.Prime 671269 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv13,pv331]) (by decide +kernel)
def pv671269 : PrimeValue := ⟨671269, pr671269⟩
private theorem pr671369 : Nat.Prime 671369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv83921]) (by decide +kernel)
def pv671369 : PrimeValue := ⟨671369, pr671369⟩
private theorem pr671501 : Nat.Prime 671501 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv79]) (by decide +kernel)
def pv671501 : PrimeValue := ⟨671501, pr671501⟩
private theorem pr671533 : Nat.Prime 671533 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv107,pv523]) (by decide +kernel)
def pv671533 : PrimeValue := ⟨671533, pr671533⟩
private theorem pr671591 : Nat.Prime 671591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv239,pv281]) (by decide +kernel)
def pv671591 : PrimeValue := ⟨671591, pr671591⟩
private theorem pr671609 : Nat.Prime 671609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv67,pv179]) (by decide +kernel)
def pv671609 : PrimeValue := ⟨671609, pr671609⟩
private theorem pr671743 : Nat.Prime 671743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv67,pv557]) (by decide +kernel)
def pv671743 : PrimeValue := ⟨671743, pr671743⟩
private theorem pr671779 : Nat.Prime 671779 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37321]) (by decide +kernel)
def pv671779 : PrimeValue := ⟨671779, pr671779⟩
private theorem pr671887 : Nat.Prime 671887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv163,pv229]) (by decide +kernel)
def pv671887 : PrimeValue := ⟨671887, pr671887⟩
private theorem pr671981 : Nat.Prime 671981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv33599]) (by decide +kernel)
def pv671981 : PrimeValue := ⟨671981, pr671981⟩
private theorem pr672043 : Nat.Prime 672043 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv16001]) (by decide +kernel)
def pv672043 : PrimeValue := ⟨672043, pr672043⟩
private theorem pr672251 : Nat.Prime 672251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2689]) (by decide +kernel)
def pv672251 : PrimeValue := ⟨672251, pr672251⟩
private theorem pr672323 : Nat.Prime 672323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv48023]) (by decide +kernel)
def pv672323 : PrimeValue := ⟨672323, pr672323⟩
private theorem pr672473 : Nat.Prime 672473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv84059]) (by decide +kernel)
def pv672473 : PrimeValue := ⟨672473, pr672473⟩
private theorem pr672499 : Nat.Prime 672499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37361]) (by decide +kernel)
def pv672499 : PrimeValue := ⟨672499, pr672499⟩
private theorem pr672779 : Nat.Prime 672779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv7823]) (by decide +kernel)
def pv672779 : PrimeValue := ⟨672779, pr672779⟩
private theorem pr672787 : Nat.Prime 672787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4153]) (by decide +kernel)
def pv672787 : PrimeValue := ⟨672787, pr672787⟩
private theorem pr672799 : Nat.Prime 672799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv83,pv193]) (by decide +kernel)
def pv672799 : PrimeValue := ⟨672799, pr672799⟩
private theorem pr673019 : Nat.Prime 673019 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv19,pv89,pv199]) (by decide +kernel)
def pv673019 : PrimeValue := ⟨673019, pr673019⟩
private theorem pr673091 : Nat.Prime 673091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv29,pv211]) (by decide +kernel)
def pv673091 : PrimeValue := ⟨673091, pr673091⟩
private theorem pr673121 : Nat.Prime 673121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv601]) (by decide +kernel)
def pv673121 : PrimeValue := ⟨673121, pr673121⟩
private theorem pr673223 : Nat.Prime 673223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv71,pv431]) (by decide +kernel)
def pv673223 : PrimeValue := ⟨673223, pr673223⟩
private theorem pr673241 : Nat.Prime 673241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv16831]) (by decide +kernel)
def pv673241 : PrimeValue := ⟨673241, pr673241⟩
private theorem pr673327 : Nat.Prime 673327 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv337]) (by decide +kernel)
def pv673327 : PrimeValue := ⟨673327, pr673327⟩
private theorem pr673339 : Nat.Prime 673339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv112223]) (by decide +kernel)
def pv673339 : PrimeValue := ⟨673339, pr673339⟩
private theorem pr673499 : Nat.Prime 673499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv73,pv659]) (by decide +kernel)
def pv673499 : PrimeValue := ⟨673499, pr673499⟩
private theorem pr673513 : Nat.Prime 673513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv211]) (by decide +kernel)
def pv673513 : PrimeValue := ⟨673513, pr673513⟩
private theorem pr673643 : Nat.Prime 673643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19813]) (by decide +kernel)
def pv673643 : PrimeValue := ⟨673643, pr673643⟩
private theorem pr673669 : Nat.Prime 673669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18713]) (by decide +kernel)
def pv673669 : PrimeValue := ⟨673669, pr673669⟩
private theorem pr673793 : Nat.Prime 673793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv47]) (by decide +kernel)
def pv673793 : PrimeValue := ⟨673793, pr673793⟩
private theorem pr673811 : Nat.Prime 673811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv1567]) (by decide +kernel)
def pv673811 : PrimeValue := ⟨673811, pr673811⟩
private theorem pr674017 : Nat.Prime 674017 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv59]) (by decide +kernel)
def pv674017 : PrimeValue := ⟨674017, pr674017⟩
private theorem pr674123 : Nat.Prime 674123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv8221]) (by decide +kernel)
def pv674123 : PrimeValue := ⟨674123, pr674123⟩
private theorem pr674189 : Nat.Prime 674189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv5437]) (by decide +kernel)
def pv674189 : PrimeValue := ⟨674189, pr674189⟩
private theorem pr674227 : Nat.Prime 674227 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv5351]) (by decide +kernel)
def pv674227 : PrimeValue := ⟨674227, pr674227⟩
private theorem pr674263 : Nat.Prime 674263 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv797]) (by decide +kernel)
def pv674263 : PrimeValue := ⟨674263, pr674263⟩
private theorem pr674273 : Nat.Prime 674273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv1109]) (by decide +kernel)
def pv674273 : PrimeValue := ⟨674273, pr674273⟩
private theorem pr674347 : Nat.Prime 674347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv167,pv673]) (by decide +kernel)
def pv674347 : PrimeValue := ⟨674347, pr674347⟩
private theorem pr674363 : Nat.Prime 674363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv37,pv701]) (by decide +kernel)
def pv674363 : PrimeValue := ⟨674363, pr674363⟩
private theorem pr674449 : Nat.Prime 674449 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv14051]) (by decide +kernel)
def pv674449 : PrimeValue := ⟨674449, pr674449⟩
private theorem pr674501 : Nat.Prime 674501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv71]) (by decide +kernel)
def pv674501 : PrimeValue := ⟨674501, pr674501⟩
private theorem pr674563 : Nat.Prime 674563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv16061]) (by decide +kernel)
def pv674563 : PrimeValue := ⟨674563, pr674563⟩
private theorem pr674603 : Nat.Prime 674603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv337301]) (by decide +kernel)
def pv674603 : PrimeValue := ⟨674603, pr674603⟩
private theorem pr674669 : Nat.Prime 674669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv1117]) (by decide +kernel)
def pv674669 : PrimeValue := ⟨674669, pr674669⟩
private theorem pr674711 : Nat.Prime 674711 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv109,pv619]) (by decide +kernel)
def pv674711 : PrimeValue := ⟨674711, pr674711⟩
private theorem pr674857 : Nat.Prime 674857 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv103]) (by decide +kernel)
def pv674857 : PrimeValue := ⟨674857, pr674857⟩
private theorem pr674903 : Nat.Prime 674903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv6367]) (by decide +kernel)
def pv674903 : PrimeValue := ⟨674903, pr674903⟩
private theorem pr675029 : Nat.Prime 675029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv4561]) (by decide +kernel)
def pv675029 : PrimeValue := ⟨675029, pr675029⟩
private theorem pr675097 : Nat.Prime 675097 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv1223]) (by decide +kernel)
def pv675097 : PrimeValue := ⟨675097, pr675097⟩
private theorem pr675247 : Nat.Prime 675247 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv787]) (by decide +kernel)
def pv675247 : PrimeValue := ⟨675247, pr675247⟩
private theorem pr675319 : Nat.Prime 675319 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv2297]) (by decide +kernel)
def pv675319 : PrimeValue := ⟨675319, pr675319⟩
private theorem pr675539 : Nat.Prime 675539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv6373]) (by decide +kernel)
def pv675539 : PrimeValue := ⟨675539, pr675539⟩
private theorem pr675553 : Nat.Prime 675553 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv31,pv227]) (by decide +kernel)
def pv675553 : PrimeValue := ⟨675553, pr675553⟩
private theorem pr675817 : Nat.Prime 675817 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv29,pv971]) (by decide +kernel)
def pv675817 : PrimeValue := ⟨675817, pr675817⟩
private theorem pr675959 : Nat.Prime 675959 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv137,pv2467]) (by decide +kernel)
def pv675959 : PrimeValue := ⟨675959, pr675959⟩
private theorem pr675979 : Nat.Prime 675979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv112663]) (by decide +kernel)
def pv675979 : PrimeValue := ⟨675979, pr675979⟩
private theorem pr676061 : Nat.Prime 676061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv439]) (by decide +kernel)
def pv676061 : PrimeValue := ⟨676061, pr676061⟩
private theorem pr676069 : Nat.Prime 676069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv1063]) (by decide +kernel)
def pv676069 : PrimeValue := ⟨676069, pr676069⟩
private theorem pr676103 : Nat.Prime 676103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv6899]) (by decide +kernel)
def pv676103 : PrimeValue := ⟨676103, pr676103⟩
private theorem pr676297 : Nat.Prime 676297 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv31,pv101]) (by decide +kernel)
def pv676297 : PrimeValue := ⟨676297, pr676297⟩
private theorem pr676391 : Nat.Prime 676391 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv13,pv43]) (by decide +kernel)
def pv676391 : PrimeValue := ⟨676391, pr676391⟩
private theorem pr676493 : Nat.Prime 676493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv3191]) (by decide +kernel)
def pv676493 : PrimeValue := ⟨676493, pr676493⟩
private theorem pr676573 : Nat.Prime 676573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv4337]) (by decide +kernel)
def pv676573 : PrimeValue := ⟨676573, pr676573⟩
private theorem pr676589 : Nat.Prime 676589 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv15377]) (by decide +kernel)
def pv676589 : PrimeValue := ⟨676589, pr676589⟩
private theorem pr676747 : Nat.Prime 676747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv131]) (by decide +kernel)
def pv676747 : PrimeValue := ⟨676747, pr676747⟩
private theorem pr676883 : Nat.Prime 676883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv3163]) (by decide +kernel)
def pv676883 : PrimeValue := ⟨676883, pr676883⟩
private theorem pr676919 : Nat.Prime 676919 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv29,pv1061]) (by decide +kernel)
def pv676919 : PrimeValue := ⟨676919, pr676919⟩
private theorem pr676943 : Nat.Prime 676943 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv48353]) (by decide +kernel)
def pv676943 : PrimeValue := ⟨676943, pr676943⟩
private theorem pr677021 : Nat.Prime 677021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv33851]) (by decide +kernel)
def pv677021 : PrimeValue := ⟨677021, pr677021⟩
private theorem pr677077 : Nat.Prime 677077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv3319]) (by decide +kernel)
def pv677077 : PrimeValue := ⟨677077, pr677077⟩
private theorem pr677107 : Nat.Prime 677107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12539]) (by decide +kernel)
def pv677107 : PrimeValue := ⟨677107, pr677107⟩
private theorem pr677119 : Nat.Prime 677119 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv8681]) (by decide +kernel)
def pv677119 : PrimeValue := ⟨677119, pr677119⟩
private theorem pr677167 : Nat.Prime 677167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv23,pv701]) (by decide +kernel)
def pv677167 : PrimeValue := ⟨677167, pr677167⟩
private theorem pr677323 : Nat.Prime 677323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv113]) (by decide +kernel)
def pv677323 : PrimeValue := ⟨677323, pr677323⟩
private theorem pr677471 : Nat.Prime 677471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv37,pv1831]) (by decide +kernel)
def pv677471 : PrimeValue := ⟨677471, pr677471⟩
private theorem pr677531 : Nat.Prime 677531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv9679]) (by decide +kernel)
def pv677531 : PrimeValue := ⟨677531, pr677531⟩
private theorem pr677639 : Nat.Prime 677639 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv67,pv389]) (by decide +kernel)
def pv677639 : PrimeValue := ⟨677639, pr677639⟩
private theorem pr677681 : Nat.Prime 677681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43,pv197]) (by decide +kernel)
def pv677681 : PrimeValue := ⟨677681, pr677681⟩
private theorem pr677959 : Nat.Prime 677959 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv19,pv313]) (by decide +kernel)
def pv677959 : PrimeValue := ⟨677959, pr677959⟩
private theorem pr678133 : Nat.Prime 678133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv23]) (by decide +kernel)
def pv678133 : PrimeValue := ⟨678133, pr678133⟩
private theorem pr678289 : Nat.Prime 678289 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv1087]) (by decide +kernel)
def pv678289 : PrimeValue := ⟨678289, pr678289⟩
private theorem pr678299 : Nat.Prime 678299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv229,pv1481]) (by decide +kernel)
def pv678299 : PrimeValue := ⟨678299, pr678299⟩
private theorem pr678329 : Nat.Prime 678329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv12113]) (by decide +kernel)
def pv678329 : PrimeValue := ⟨678329, pr678329⟩
private theorem pr678371 : Nat.Prime 678371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv881]) (by decide +kernel)
def pv678371 : PrimeValue := ⟨678371, pr678371⟩
private theorem pr678463 : Nat.Prime 678463 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv73,pv1549]) (by decide +kernel)
def pv678463 : PrimeValue := ⟨678463, pr678463⟩
private theorem pr678493 : Nat.Prime 678493 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv401]) (by decide +kernel)
def pv678493 : PrimeValue := ⟨678493, pr678493⟩
private theorem pr678581 : Nat.Prime 678581 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv37,pv131]) (by decide +kernel)
def pv678581 : PrimeValue := ⟨678581, pr678581⟩
private theorem pr678649 : Nat.Prime 678649 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv28277]) (by decide +kernel)
def pv678649 : PrimeValue := ⟨678649, pr678649⟩
private theorem pr678731 : Nat.Prime 678731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv23,pv227]) (by decide +kernel)
def pv678731 : PrimeValue := ⟨678731, pr678731⟩
private theorem pr678773 : Nat.Prime 678773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv169693]) (by decide +kernel)
def pv678773 : PrimeValue := ⟨678773, pr678773⟩
private theorem pr678809 : Nat.Prime 678809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv61,pv107]) (by decide +kernel)
def pv678809 : PrimeValue := ⟨678809, pr678809⟩
private theorem pr678859 : Nat.Prime 678859 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv113143]) (by decide +kernel)
def pv678859 : PrimeValue := ⟨678859, pr678859⟩
private theorem pr678883 : Nat.Prime 678883 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv113147]) (by decide +kernel)
def pv678883 : PrimeValue := ⟨678883, pr678883⟩
private theorem pr678941 : Nat.Prime 678941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv83,pv409]) (by decide +kernel)
def pv678941 : PrimeValue := ⟨678941, pr678941⟩
private theorem pr678959 : Nat.Prime 678959 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv48497]) (by decide +kernel)
def pv678959 : PrimeValue := ⟨678959, pr678959⟩
private theorem pr679039 : Nat.Prime 679039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv113173]) (by decide +kernel)
def pv679039 : PrimeValue := ⟨679039, pr679039⟩
private theorem pr679087 : Nat.Prime 679087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv1217]) (by decide +kernel)
def pv679087 : PrimeValue := ⟨679087, pr679087⟩
private theorem pr679153 : Nat.Prime 679153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv14149]) (by decide +kernel)
def pv679153 : PrimeValue := ⟨679153, pr679153⟩
private theorem pr679183 : Nat.Prime 679183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv103,pv157]) (by decide +kernel)
def pv679183 : PrimeValue := ⟨679183, pr679183⟩
private theorem pr679229 : Nat.Prime 679229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv43,pv359]) (by decide +kernel)
def pv679229 : PrimeValue := ⟨679229, pr679229⟩
private theorem pr679249 : Nat.Prime 679249 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv53,pv89]) (by decide +kernel)
def pv679249 : PrimeValue := ⟨679249, pr679249⟩
private theorem pr679297 : Nat.Prime 679297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv61]) (by decide +kernel)
def pv679297 : PrimeValue := ⟨679297, pr679297⟩
private theorem pr679319 : Nat.Prime 679319 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv339659]) (by decide +kernel)
def pv679319 : PrimeValue := ⟨679319, pr679319⟩
private theorem pr679403 : Nat.Prime 679403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv941]) (by decide +kernel)
def pv679403 : PrimeValue := ⟨679403, pr679403⟩
private theorem pr679463 : Nat.Prime 679463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv48533]) (by decide +kernel)
def pv679463 : PrimeValue := ⟨679463, pr679463⟩
private theorem pr679597 : Nat.Prime 679597 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv56633]) (by decide +kernel)
def pv679597 : PrimeValue := ⟨679597, pr679597⟩
private theorem pr679603 : Nat.Prime 679603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv1471]) (by decide +kernel)
def pv679603 : PrimeValue := ⟨679603, pr679603⟩
private theorem pr679633 : Nat.Prime 679633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv14159]) (by decide +kernel)
def pv679633 : PrimeValue := ⟨679633, pr679633⟩
private theorem pr679639 : Nat.Prime 679639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv227,pv499]) (by decide +kernel)
def pv679639 : PrimeValue := ⟨679639, pr679639⟩
private theorem pr679733 : Nat.Prime 679733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv169933]) (by decide +kernel)
def pv679733 : PrimeValue := ⟨679733, pr679733⟩
private theorem pr679781 : Nat.Prime 679781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv829]) (by decide +kernel)
def pv679781 : PrimeValue := ⟨679781, pr679781⟩
private theorem pr679823 : Nat.Prime 679823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv13,pv2377]) (by decide +kernel)
def pv679823 : PrimeValue := ⟨679823, pr679823⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
