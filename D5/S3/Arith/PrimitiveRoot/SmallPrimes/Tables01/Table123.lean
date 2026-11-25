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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr661483 : PrimeCertificate 661483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv36749]) (by decide +kernel)
def pv661483 : PrimeValue := ⟨661483, pr661483⟩
private theorem pr661553 : PrimeCertificate 661553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv173,pv239]) (by decide +kernel)
def pv661553 : PrimeValue := ⟨661553, pr661553⟩
private theorem pr661663 : PrimeCertificate 661663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12253]) (by decide +kernel)
def pv661663 : PrimeValue := ⟨661663, pr661663⟩
private theorem pr661849 : PrimeCertificate 661849 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv23,pv109]) (by decide +kernel)
def pv661849 : PrimeValue := ⟨661849, pr661849⟩
private theorem pr661889 : PrimeCertificate 661889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5171]) (by decide +kernel)
def pv661889 : PrimeValue := ⟨661889, pr661889⟩
private theorem pr661949 : PrimeCertificate 661949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv47,pv503]) (by decide +kernel)
def pv661949 : PrimeValue := ⟨661949, pr661949⟩
private theorem pr661961 : PrimeCertificate 661961 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv13,pv19,pv67]) (by decide +kernel)
def pv661961 : PrimeValue := ⟨661961, pr661961⟩
private theorem pr662003 : PrimeCertificate 662003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv30091]) (by decide +kernel)
def pv662003 : PrimeValue := ⟨662003, pr662003⟩
private theorem pr662047 : PrimeCertificate 662047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv1433]) (by decide +kernel)
def pv662047 : PrimeValue := ⟨662047, pr662047⟩
private theorem pr662111 : PrimeCertificate 662111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv73,pv907]) (by decide +kernel)
def pv662111 : PrimeValue := ⟨662111, pr662111⟩
private theorem pr662203 : PrimeCertificate 662203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12263]) (by decide +kernel)
def pv662203 : PrimeValue := ⟨662203, pr662203⟩
private theorem pr662227 : PrimeCertificate 662227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv37,pv157]) (by decide +kernel)
def pv662227 : PrimeValue := ⟨662227, pr662227⟩
private theorem pr662309 : PrimeCertificate 662309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv313]) (by decide +kernel)
def pv662309 : PrimeValue := ⟨662309, pr662309⟩
private theorem pr662323 : PrimeCertificate 662323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv167,pv661]) (by decide +kernel)
def pv662323 : PrimeValue := ⟨662323, pr662323⟩
private theorem pr662339 : PrimeCertificate 662339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv89]) (by decide +kernel)
def pv662339 : PrimeValue := ⟨662339, pr662339⟩
private theorem pr662531 : PrimeCertificate 662531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv19,pv317]) (by decide +kernel)
def pv662531 : PrimeValue := ⟨662531, pr662531⟩
private theorem pr662539 : PrimeCertificate 662539 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv4801]) (by decide +kernel)
def pv662539 : PrimeValue := ⟨662539, pr662539⟩
private theorem pr662591 : PrimeCertificate 662591 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv173,pv383]) (by decide +kernel)
def pv662591 : PrimeValue := ⟨662591, pr662591⟩
private theorem pr662689 : PrimeCertificate 662689 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv59]) (by decide +kernel)
def pv662689 : PrimeValue := ⟨662689, pr662689⟩
private theorem pr662713 : PrimeCertificate 662713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv521]) (by decide +kernel)
def pv662713 : PrimeValue := ⟨662713, pr662713⟩
private theorem pr662771 : PrimeCertificate 662771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv191,pv347]) (by decide +kernel)
def pv662771 : PrimeValue := ⟨662771, pr662771⟩
private theorem pr662789 : PrimeCertificate 662789 :=
  certifyPrime (q := pv17) (ls := [pv2,pv7,pv23671]) (by decide +kernel)
def pv662789 : PrimeValue := ⟨662789, pr662789⟩
private theorem pr662797 : PrimeCertificate 662797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv19]) (by decide +kernel)
def pv662797 : PrimeValue := ⟨662797, pr662797⟩
private theorem pr662833 : PrimeCertificate 662833 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4603]) (by decide +kernel)
def pv662833 : PrimeValue := ⟨662833, pr662833⟩
private theorem pr662917 : PrimeCertificate 662917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv55243]) (by decide +kernel)
def pv662917 : PrimeValue := ⟨662917, pr662917⟩
private theorem pr662951 : PrimeCertificate 662951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13259]) (by decide +kernel)
def pv662951 : PrimeValue := ⟨662951, pr662951⟩
private theorem pr663007 : PrimeCertificate 663007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv110501]) (by decide +kernel)
def pv663007 : PrimeValue := ⟨663007, pr663007⟩
private theorem pr663037 : PrimeCertificate 663037 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv5023]) (by decide +kernel)
def pv663037 : PrimeValue := ⟨663037, pr663037⟩
private theorem pr663097 : PrimeCertificate 663097 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv3947]) (by decide +kernel)
def pv663097 : PrimeValue := ⟨663097, pr663097⟩
private theorem pr663191 : PrimeCertificate 663191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv6029]) (by decide +kernel)
def pv663191 : PrimeValue := ⟨663191, pr663191⟩
private theorem pr663209 : PrimeCertificate 663209 :=
  certifyPrime (q := pv19) (ls := [pv2,pv7,pv13,pv911]) (by decide +kernel)
def pv663209 : PrimeValue := ⟨663209, pr663209⟩
private theorem pr663529 : PrimeCertificate 663529 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv27647]) (by decide +kernel)
def pv663529 : PrimeValue := ⟨663529, pr663529⟩
private theorem pr663599 : PrimeCertificate 663599 :=
  certifyPrime (q := pv19) (ls := [pv2,pv13,pv25523]) (by decide +kernel)
def pv663599 : PrimeValue := ⟨663599, pr663599⟩
private theorem pr663713 : PrimeCertificate 663713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv2963]) (by decide +kernel)
def pv663713 : PrimeValue := ⟨663713, pr663713⟩
private theorem pr663763 : PrimeCertificate 663763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv89,pv113]) (by decide +kernel)
def pv663763 : PrimeValue := ⟨663763, pr663763⟩
private theorem pr664043 : PrimeCertificate 664043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv107]) (by decide +kernel)
def pv664043 : PrimeValue := ⟨664043, pr664043⟩
private theorem pr664091 : PrimeCertificate 664091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv53,pv179]) (by decide +kernel)
def pv664091 : PrimeValue := ⟨664091, pr664091⟩
private theorem pr664109 : PrimeCertificate 664109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv166027]) (by decide +kernel)
def pv664109 : PrimeValue := ⟨664109, pr664109⟩
private theorem pr664193 : PrimeCertificate 664193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5189]) (by decide +kernel)
def pv664193 : PrimeValue := ⟨664193, pr664193⟩
private theorem pr664253 : PrimeCertificate 664253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv166063]) (by decide +kernel)
def pv664253 : PrimeValue := ⟨664253, pr664253⟩
private theorem pr664357 : PrimeCertificate 664357 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv719]) (by decide +kernel)
def pv664357 : PrimeValue := ⟨664357, pr664357⟩
private theorem pr664369 : PrimeCertificate 664369 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13841]) (by decide +kernel)
def pv664369 : PrimeValue := ⟨664369, pr664369⟩
private theorem pr664403 : PrimeCertificate 664403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv332201]) (by decide +kernel)
def pv664403 : PrimeValue := ⟨664403, pr664403⟩
private theorem pr664421 : PrimeCertificate 664421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv139,pv239]) (by decide +kernel)
def pv664421 : PrimeValue := ⟨664421, pr664421⟩
private theorem pr664571 : PrimeCertificate 664571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv66457]) (by decide +kernel)
def pv664571 : PrimeValue := ⟨664571, pr664571⟩
private theorem pr664679 : PrimeCertificate 664679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv197,pv241]) (by decide +kernel)
def pv664679 : PrimeValue := ⟨664679, pr664679⟩
private theorem pr664739 : PrimeCertificate 664739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv73,pv157]) (by decide +kernel)
def pv664739 : PrimeValue := ⟨664739, pr664739⟩
private theorem pr664799 : PrimeCertificate 664799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv332399]) (by decide +kernel)
def pv664799 : PrimeValue := ⟨664799, pr664799⟩
private theorem pr664949 : PrimeCertificate 664949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv166237]) (by decide +kernel)
def pv664949 : PrimeValue := ⟨664949, pr664949⟩
private theorem pr665017 : PrimeCertificate 665017 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv229]) (by decide +kernel)
def pv665017 : PrimeValue := ⟨665017, pr665017⟩
private theorem pr665029 : PrimeCertificate 665029 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv29]) (by decide +kernel)
def pv665029 : PrimeValue := ⟨665029, pr665029⟩
private theorem pr665051 : PrimeCertificate 665051 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv47,pv283]) (by decide +kernel)
def pv665051 : PrimeValue := ⟨665051, pr665051⟩
private theorem pr665111 : PrimeCertificate 665111 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv227,pv293]) (by decide +kernel)
def pv665111 : PrimeValue := ⟨665111, pr665111⟩
private theorem pr665279 : PrimeCertificate 665279 :=
  certifyPrime (q := pv23) (ls := [pv2,pv17,pv1151]) (by decide +kernel)
def pv665279 : PrimeValue := ⟨665279, pr665279⟩
private theorem pr665429 : PrimeCertificate 665429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv166357]) (by decide +kernel)
def pv665429 : PrimeValue := ⟨665429, pr665429⟩
private theorem pr665479 : PrimeCertificate 665479 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv3361]) (by decide +kernel)
def pv665479 : PrimeValue := ⟨665479, pr665479⟩
private theorem pr665603 : PrimeCertificate 665603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv47543]) (by decide +kernel)
def pv665603 : PrimeValue := ⟨665603, pr665603⟩
private theorem pr665617 : PrimeCertificate 665617 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7,pv283]) (by decide +kernel)
def pv665617 : PrimeValue := ⟨665617, pr665617⟩
private theorem pr665783 : PrimeCertificate 665783 :=
  certifyPrime (q := pv19) (ls := [pv2,pv13,pv29,pv883]) (by decide +kernel)
def pv665783 : PrimeValue := ⟨665783, pr665783⟩
private theorem pr665789 : PrimeCertificate 665789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv9791]) (by decide +kernel)
def pv665789 : PrimeValue := ⟨665789, pr665789⟩
private theorem pr665857 : PrimeCertificate 665857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv665857 : PrimeValue := ⟨665857, pr665857⟩
private theorem pr665923 : PrimeCertificate 665923 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv2707]) (by decide +kernel)
def pv665923 : PrimeValue := ⟨665923, pr665923⟩
private theorem pr665953 : PrimeCertificate 665953 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv991]) (by decide +kernel)
def pv665953 : PrimeValue := ⟨665953, pr665953⟩
private theorem pr665993 : PrimeCertificate 665993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv59,pv83]) (by decide +kernel)
def pv665993 : PrimeValue := ⟨665993, pr665993⟩
private theorem pr666023 : PrimeCertificate 666023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv113,pv421]) (by decide +kernel)
def pv666023 : PrimeValue := ⟨666023, pr666023⟩
private theorem pr666073 : PrimeCertificate 666073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv29]) (by decide +kernel)
def pv666073 : PrimeValue := ⟨666073, pr666073⟩
private theorem pr666233 : PrimeCertificate 666233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11897]) (by decide +kernel)
def pv666233 : PrimeValue := ⟨666233, pr666233⟩
private theorem pr666277 : PrimeCertificate 666277 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv4271]) (by decide +kernel)
def pv666277 : PrimeValue := ⟨666277, pr666277⟩
private theorem pr666493 : PrimeCertificate 666493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv55541]) (by decide +kernel)
def pv666493 : PrimeValue := ⟨666493, pr666493⟩
private theorem pr666529 : PrimeCertificate 666529 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv53,pv131]) (by decide +kernel)
def pv666529 : PrimeValue := ⟨666529, pr666529⟩
private theorem pr666607 : PrimeCertificate 666607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv241,pv461]) (by decide +kernel)
def pv666607 : PrimeValue := ⟨666607, pr666607⟩
private theorem pr666773 : PrimeCertificate 666773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv166693]) (by decide +kernel)
def pv666773 : PrimeValue := ⟨666773, pr666773⟩
private theorem pr666959 : PrimeCertificate 666959 :=
  certifyPrime (q := pv13) (ls := [pv2,pv333479]) (by decide +kernel)
def pv666959 : PrimeValue := ⟨666959, pr666959⟩
private theorem pr666983 : PrimeCertificate 666983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv333491]) (by decide +kernel)
def pv666983 : PrimeValue := ⟨666983, pr666983⟩
private theorem pr667181 : PrimeCertificate 667181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv33359]) (by decide +kernel)
def pv667181 : PrimeValue := ⟨667181, pr667181⟩
private theorem pr667211 : PrimeCertificate 667211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv66721]) (by decide +kernel)
def pv667211 : PrimeValue := ⟨667211, pr667211⟩
private theorem pr667309 : PrimeCertificate 667309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv55609]) (by decide +kernel)
def pv667309 : PrimeValue := ⟨667309, pr667309⟩
private theorem pr667417 : PrimeCertificate 667417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv27809]) (by decide +kernel)
def pv667417 : PrimeValue := ⟨667417, pr667417⟩
private theorem pr667507 : PrimeCertificate 667507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv691]) (by decide +kernel)
def pv667507 : PrimeValue := ⟨667507, pr667507⟩
private theorem pr667549 : PrimeCertificate 667549 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv883]) (by decide +kernel)
def pv667549 : PrimeValue := ⟨667549, pr667549⟩
private theorem pr667643 : PrimeCertificate 667643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv333821]) (by decide +kernel)
def pv667643 : PrimeValue := ⟨667643, pr667643⟩
private theorem pr667687 : PrimeCertificate 667687 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv257,pv433]) (by decide +kernel)
def pv667687 : PrimeValue := ⟨667687, pr667687⟩
private theorem pr667699 : PrimeCertificate 667699 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv5857]) (by decide +kernel)
def pv667699 : PrimeValue := ⟨667699, pr667699⟩
private theorem pr667781 : PrimeCertificate 667781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv173,pv193]) (by decide +kernel)
def pv667781 : PrimeValue := ⟨667781, pr667781⟩
private theorem pr667949 : PrimeCertificate 667949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv166987]) (by decide +kernel)
def pv667949 : PrimeValue := ⟨667949, pr667949⟩
private theorem pr668009 : PrimeCertificate 668009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv7591]) (by decide +kernel)
def pv668009 : PrimeValue := ⟨668009, pr668009⟩
private theorem pr668051 : PrimeCertificate 668051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv431]) (by decide +kernel)
def pv668051 : PrimeValue := ⟨668051, pr668051⟩
private theorem pr668089 : PrimeCertificate 668089 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1031]) (by decide +kernel)
def pv668089 : PrimeValue := ⟨668089, pr668089⟩
private theorem pr668093 : PrimeCertificate 668093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167023]) (by decide +kernel)
def pv668093 : PrimeValue := ⟨668093, pr668093⟩
private theorem pr668243 : PrimeCertificate 668243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv73,pv199]) (by decide +kernel)
def pv668243 : PrimeValue := ⟨668243, pr668243⟩
private theorem pr668273 : PrimeCertificate 668273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv3797]) (by decide +kernel)
def pv668273 : PrimeValue := ⟨668273, pr668273⟩
private theorem pr668471 : PrimeCertificate 668471 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv59,pv103]) (by decide +kernel)
def pv668471 : PrimeValue := ⟨668471, pr668471⟩
private theorem pr668513 : PrimeCertificate 668513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1607]) (by decide +kernel)
def pv668513 : PrimeValue := ⟨668513, pr668513⟩
private theorem pr668579 : PrimeCertificate 668579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv334289]) (by decide +kernel)
def pv668579 : PrimeValue := ⟨668579, pr668579⟩
private theorem pr668713 : PrimeCertificate 668713 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv17,pv149]) (by decide +kernel)
def pv668713 : PrimeValue := ⟨668713, pr668713⟩
private theorem pr668803 : PrimeCertificate 668803 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv111467]) (by decide +kernel)
def pv668803 : PrimeValue := ⟨668803, pr668803⟩
private theorem pr668813 : PrimeCertificate 668813 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv4519]) (by decide +kernel)
def pv668813 : PrimeValue := ⟨668813, pr668813⟩
private theorem pr668989 : PrimeCertificate 668989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18583]) (by decide +kernel)
def pv668989 : PrimeValue := ⟨668989, pr668989⟩
private theorem pr669283 : PrimeCertificate 669283 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv331,pv337]) (by decide +kernel)
def pv669283 : PrimeValue := ⟨669283, pr669283⟩
private theorem pr669401 : PrimeCertificate 669401 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv3347]) (by decide +kernel)
def pv669401 : PrimeValue := ⟨669401, pr669401⟩
private theorem pr669433 : PrimeCertificate 669433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv27893]) (by decide +kernel)
def pv669433 : PrimeValue := ⟨669433, pr669433⟩
private theorem pr669611 : PrimeCertificate 669611 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv29,pv2309]) (by decide +kernel)
def pv669611 : PrimeValue := ⟨669611, pr669611⟩
private theorem pr669637 : PrimeCertificate 669637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv89]) (by decide +kernel)
def pv669637 : PrimeValue := ⟨669637, pr669637⟩
private theorem pr669649 : PrimeCertificate 669649 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv1993]) (by decide +kernel)
def pv669649 : PrimeValue := ⟨669649, pr669649⟩
private theorem pr669847 : PrimeCertificate 669847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv111641]) (by decide +kernel)
def pv669847 : PrimeValue := ⟨669847, pr669847⟩
private theorem pr669913 : PrimeCertificate 669913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103,pv271]) (by decide +kernel)
def pv669913 : PrimeValue := ⟨669913, pr669913⟩
private theorem pr669937 : PrimeCertificate 669937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv821]) (by decide +kernel)
def pv669937 : PrimeValue := ⟨669937, pr669937⟩
private theorem pr669943 : PrimeCertificate 669943 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv13,pv409]) (by decide +kernel)
def pv669943 : PrimeValue := ⟨669943, pr669943⟩
private theorem pr670177 : PrimeCertificate 670177 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv13,pv179]) (by decide +kernel)
def pv670177 : PrimeValue := ⟨670177, pr670177⟩
private theorem pr670193 : PrimeCertificate 670193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41887]) (by decide +kernel)
def pv670193 : PrimeValue := ⟨670193, pr670193⟩
private theorem pr670223 : PrimeCertificate 670223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv977]) (by decide +kernel)
def pv670223 : PrimeValue := ⟨670223, pr670223⟩
private theorem pr670279 : PrimeCertificate 670279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv15959]) (by decide +kernel)
def pv670279 : PrimeValue := ⟨670279, pr670279⟩
private theorem pr670303 : PrimeCertificate 670303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12413]) (by decide +kernel)
def pv670303 : PrimeValue := ⟨670303, pr670303⟩
private theorem pr670343 : PrimeCertificate 670343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv335171]) (by decide +kernel)
def pv670343 : PrimeValue := ⟨670343, pr670343⟩
private theorem pr670363 : PrimeCertificate 670363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv1451]) (by decide +kernel)
def pv670363 : PrimeValue := ⟨670363, pr670363⟩
private theorem pr670511 : PrimeCertificate 670511 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv19,pv3529]) (by decide +kernel)
def pv670511 : PrimeValue := ⟨670511, pr670511⟩
private theorem pr670583 : PrimeCertificate 670583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv17,pv163]) (by decide +kernel)
def pv670583 : PrimeValue := ⟨670583, pr670583⟩
private theorem pr670627 : PrimeCertificate 670627 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1129]) (by decide +kernel)
def pv670627 : PrimeValue := ⟨670627, pr670627⟩
private theorem pr670693 : PrimeCertificate 670693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv5081]) (by decide +kernel)
def pv670693 : PrimeValue := ⟨670693, pr670693⟩
private theorem pr670849 : PrimeCertificate 670849 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv1747]) (by decide +kernel)
def pv670849 : PrimeValue := ⟨670849, pr670849⟩
private theorem pr670853 : PrimeCertificate 670853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv19,pv97]) (by decide +kernel)
def pv670853 : PrimeValue := ⟨670853, pr670853⟩
private theorem pr670897 : PrimeCertificate 670897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1553]) (by decide +kernel)
def pv670897 : PrimeValue := ⟨670897, pr670897⟩
private theorem pr670903 : PrimeCertificate 670903 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31,pv3607]) (by decide +kernel)
def pv670903 : PrimeValue := ⟨670903, pr670903⟩
private theorem pr670919 : PrimeCertificate 670919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv335459]) (by decide +kernel)
def pv670919 : PrimeValue := ⟨670919, pr670919⟩
private theorem pr670931 : PrimeCertificate 670931 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv397]) (by decide +kernel)
def pv670931 : PrimeValue := ⟨670931, pr670931⟩
private theorem pr670991 : PrimeCertificate 670991 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv17,pv3947]) (by decide +kernel)
def pv670991 : PrimeValue := ⟨670991, pr670991⟩
private theorem pr671003 : PrimeCertificate 671003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv29,pv503]) (by decide +kernel)
def pv671003 : PrimeValue := ⟨671003, pr671003⟩
private theorem pr671017 : PrimeCertificate 671017 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv73,pv383]) (by decide +kernel)
def pv671017 : PrimeValue := ⟨671017, pr671017⟩
private theorem pr671039 : PrimeCertificate 671039 :=
  certifyPrime (q := pv13) (ls := [pv2,pv335519]) (by decide +kernel)
def pv671039 : PrimeValue := ⟨671039, pr671039⟩
private theorem pr671059 : PrimeCertificate 671059 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv43]) (by decide +kernel)
def pv671059 : PrimeValue := ⟨671059, pr671059⟩
private theorem pr671081 : PrimeCertificate 671081 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv883]) (by decide +kernel)
def pv671081 : PrimeValue := ⟨671081, pr671081⟩
private theorem pr671123 : PrimeCertificate 671123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv5501]) (by decide +kernel)
def pv671123 : PrimeValue := ⟨671123, pr671123⟩
private theorem pr671141 : PrimeCertificate 671141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv1459]) (by decide +kernel)
def pv671141 : PrimeValue := ⟨671141, pr671141⟩
private theorem pr671189 : PrimeCertificate 671189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23971]) (by decide +kernel)
def pv671189 : PrimeValue := ⟨671189, pr671189⟩
private theorem pr671201 : PrimeCertificate 671201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv839]) (by decide +kernel)
def pv671201 : PrimeValue := ⟨671201, pr671201⟩
private theorem pr671233 : PrimeCertificate 671233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv23]) (by decide +kernel)
def pv671233 : PrimeValue := ⟨671233, pr671233⟩
private theorem pr671249 : PrimeCertificate 671249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41953]) (by decide +kernel)
def pv671249 : PrimeValue := ⟨671249, pr671249⟩
private theorem pr671257 : PrimeCertificate 671257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9323]) (by decide +kernel)
def pv671257 : PrimeValue := ⟨671257, pr671257⟩
private theorem pr671269 : PrimeCertificate 671269 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv13,pv331]) (by decide +kernel)
def pv671269 : PrimeValue := ⟨671269, pr671269⟩
private theorem pr671369 : PrimeCertificate 671369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83921]) (by decide +kernel)
def pv671369 : PrimeValue := ⟨671369, pr671369⟩
private theorem pr671501 : PrimeCertificate 671501 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv79]) (by decide +kernel)
def pv671501 : PrimeValue := ⟨671501, pr671501⟩
private theorem pr671533 : PrimeCertificate 671533 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv107,pv523]) (by decide +kernel)
def pv671533 : PrimeValue := ⟨671533, pr671533⟩
private theorem pr671591 : PrimeCertificate 671591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv239,pv281]) (by decide +kernel)
def pv671591 : PrimeValue := ⟨671591, pr671591⟩
private theorem pr671609 : PrimeCertificate 671609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv67,pv179]) (by decide +kernel)
def pv671609 : PrimeValue := ⟨671609, pr671609⟩
private theorem pr671743 : PrimeCertificate 671743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv557]) (by decide +kernel)
def pv671743 : PrimeValue := ⟨671743, pr671743⟩
private theorem pr671779 : PrimeCertificate 671779 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37321]) (by decide +kernel)
def pv671779 : PrimeValue := ⟨671779, pr671779⟩
private theorem pr671887 : PrimeCertificate 671887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv163,pv229]) (by decide +kernel)
def pv671887 : PrimeValue := ⟨671887, pr671887⟩
private theorem pr671981 : PrimeCertificate 671981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv33599]) (by decide +kernel)
def pv671981 : PrimeValue := ⟨671981, pr671981⟩
private theorem pr672043 : PrimeCertificate 672043 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv16001]) (by decide +kernel)
def pv672043 : PrimeValue := ⟨672043, pr672043⟩
private theorem pr672251 : PrimeCertificate 672251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2689]) (by decide +kernel)
def pv672251 : PrimeValue := ⟨672251, pr672251⟩
private theorem pr672323 : PrimeCertificate 672323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv48023]) (by decide +kernel)
def pv672323 : PrimeValue := ⟨672323, pr672323⟩
private theorem pr672473 : PrimeCertificate 672473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv84059]) (by decide +kernel)
def pv672473 : PrimeValue := ⟨672473, pr672473⟩
private theorem pr672499 : PrimeCertificate 672499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37361]) (by decide +kernel)
def pv672499 : PrimeValue := ⟨672499, pr672499⟩
private theorem pr672779 : PrimeCertificate 672779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv7823]) (by decide +kernel)
def pv672779 : PrimeValue := ⟨672779, pr672779⟩
private theorem pr672787 : PrimeCertificate 672787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4153]) (by decide +kernel)
def pv672787 : PrimeValue := ⟨672787, pr672787⟩
private theorem pr672799 : PrimeCertificate 672799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv83,pv193]) (by decide +kernel)
def pv672799 : PrimeValue := ⟨672799, pr672799⟩
private theorem pr673019 : PrimeCertificate 673019 :=
  certifyPrime (q := pv7) (ls := [pv2,pv19,pv89,pv199]) (by decide +kernel)
def pv673019 : PrimeValue := ⟨673019, pr673019⟩
private theorem pr673091 : PrimeCertificate 673091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv29,pv211]) (by decide +kernel)
def pv673091 : PrimeValue := ⟨673091, pr673091⟩
private theorem pr673121 : PrimeCertificate 673121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv601]) (by decide +kernel)
def pv673121 : PrimeValue := ⟨673121, pr673121⟩
private theorem pr673223 : PrimeCertificate 673223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv71,pv431]) (by decide +kernel)
def pv673223 : PrimeValue := ⟨673223, pr673223⟩
private theorem pr673241 : PrimeCertificate 673241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv16831]) (by decide +kernel)
def pv673241 : PrimeValue := ⟨673241, pr673241⟩
private theorem pr673327 : PrimeCertificate 673327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv337]) (by decide +kernel)
def pv673327 : PrimeValue := ⟨673327, pr673327⟩
private theorem pr673339 : PrimeCertificate 673339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv112223]) (by decide +kernel)
def pv673339 : PrimeValue := ⟨673339, pr673339⟩
private theorem pr673499 : PrimeCertificate 673499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv73,pv659]) (by decide +kernel)
def pv673499 : PrimeValue := ⟨673499, pr673499⟩
private theorem pr673513 : PrimeCertificate 673513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv211]) (by decide +kernel)
def pv673513 : PrimeValue := ⟨673513, pr673513⟩
private theorem pr673643 : PrimeCertificate 673643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv19813]) (by decide +kernel)
def pv673643 : PrimeValue := ⟨673643, pr673643⟩
private theorem pr673669 : PrimeCertificate 673669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18713]) (by decide +kernel)
def pv673669 : PrimeValue := ⟨673669, pr673669⟩
private theorem pr673793 : PrimeCertificate 673793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv47]) (by decide +kernel)
def pv673793 : PrimeValue := ⟨673793, pr673793⟩
private theorem pr673811 : PrimeCertificate 673811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv1567]) (by decide +kernel)
def pv673811 : PrimeValue := ⟨673811, pr673811⟩
private theorem pr674017 : PrimeCertificate 674017 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv59]) (by decide +kernel)
def pv674017 : PrimeValue := ⟨674017, pr674017⟩
private theorem pr674123 : PrimeCertificate 674123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv8221]) (by decide +kernel)
def pv674123 : PrimeValue := ⟨674123, pr674123⟩
private theorem pr674189 : PrimeCertificate 674189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv5437]) (by decide +kernel)
def pv674189 : PrimeValue := ⟨674189, pr674189⟩
private theorem pr674227 : PrimeCertificate 674227 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv5351]) (by decide +kernel)
def pv674227 : PrimeValue := ⟨674227, pr674227⟩
private theorem pr674263 : PrimeCertificate 674263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv797]) (by decide +kernel)
def pv674263 : PrimeValue := ⟨674263, pr674263⟩
private theorem pr674273 : PrimeCertificate 674273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv1109]) (by decide +kernel)
def pv674273 : PrimeValue := ⟨674273, pr674273⟩
private theorem pr674347 : PrimeCertificate 674347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv167,pv673]) (by decide +kernel)
def pv674347 : PrimeValue := ⟨674347, pr674347⟩
private theorem pr674363 : PrimeCertificate 674363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv37,pv701]) (by decide +kernel)
def pv674363 : PrimeValue := ⟨674363, pr674363⟩
private theorem pr674449 : PrimeCertificate 674449 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv14051]) (by decide +kernel)
def pv674449 : PrimeValue := ⟨674449, pr674449⟩
private theorem pr674501 : PrimeCertificate 674501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv71]) (by decide +kernel)
def pv674501 : PrimeValue := ⟨674501, pr674501⟩
private theorem pr674563 : PrimeCertificate 674563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv16061]) (by decide +kernel)
def pv674563 : PrimeValue := ⟨674563, pr674563⟩
private theorem pr674603 : PrimeCertificate 674603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv337301]) (by decide +kernel)
def pv674603 : PrimeValue := ⟨674603, pr674603⟩
private theorem pr674669 : PrimeCertificate 674669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv151,pv1117]) (by decide +kernel)
def pv674669 : PrimeValue := ⟨674669, pr674669⟩
private theorem pr674711 : PrimeCertificate 674711 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv109,pv619]) (by decide +kernel)
def pv674711 : PrimeValue := ⟨674711, pr674711⟩
private theorem pr674857 : PrimeCertificate 674857 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv103]) (by decide +kernel)
def pv674857 : PrimeValue := ⟨674857, pr674857⟩
private theorem pr674903 : PrimeCertificate 674903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv6367]) (by decide +kernel)
def pv674903 : PrimeValue := ⟨674903, pr674903⟩
private theorem pr675029 : PrimeCertificate 675029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv4561]) (by decide +kernel)
def pv675029 : PrimeValue := ⟨675029, pr675029⟩
private theorem pr675097 : PrimeCertificate 675097 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv1223]) (by decide +kernel)
def pv675097 : PrimeValue := ⟨675097, pr675097⟩
private theorem pr675247 : PrimeCertificate 675247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv787]) (by decide +kernel)
def pv675247 : PrimeValue := ⟨675247, pr675247⟩
private theorem pr675319 : PrimeCertificate 675319 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv2297]) (by decide +kernel)
def pv675319 : PrimeValue := ⟨675319, pr675319⟩
private theorem pr675539 : PrimeCertificate 675539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv6373]) (by decide +kernel)
def pv675539 : PrimeValue := ⟨675539, pr675539⟩
private theorem pr675553 : PrimeCertificate 675553 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv31,pv227]) (by decide +kernel)
def pv675553 : PrimeValue := ⟨675553, pr675553⟩
private theorem pr675817 : PrimeCertificate 675817 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv29,pv971]) (by decide +kernel)
def pv675817 : PrimeValue := ⟨675817, pr675817⟩
private theorem pr675959 : PrimeCertificate 675959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv137,pv2467]) (by decide +kernel)
def pv675959 : PrimeValue := ⟨675959, pr675959⟩
private theorem pr675979 : PrimeCertificate 675979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv112663]) (by decide +kernel)
def pv675979 : PrimeValue := ⟨675979, pr675979⟩
private theorem pr676061 : PrimeCertificate 676061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv439]) (by decide +kernel)
def pv676061 : PrimeValue := ⟨676061, pr676061⟩
private theorem pr676069 : PrimeCertificate 676069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv1063]) (by decide +kernel)
def pv676069 : PrimeValue := ⟨676069, pr676069⟩
private theorem pr676103 : PrimeCertificate 676103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv6899]) (by decide +kernel)
def pv676103 : PrimeValue := ⟨676103, pr676103⟩
private theorem pr676297 : PrimeCertificate 676297 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv31,pv101]) (by decide +kernel)
def pv676297 : PrimeValue := ⟨676297, pr676297⟩
private theorem pr676391 : PrimeCertificate 676391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv13,pv43]) (by decide +kernel)
def pv676391 : PrimeValue := ⟨676391, pr676391⟩
private theorem pr676493 : PrimeCertificate 676493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv3191]) (by decide +kernel)
def pv676493 : PrimeValue := ⟨676493, pr676493⟩
private theorem pr676573 : PrimeCertificate 676573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv4337]) (by decide +kernel)
def pv676573 : PrimeValue := ⟨676573, pr676573⟩
private theorem pr676589 : PrimeCertificate 676589 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv15377]) (by decide +kernel)
def pv676589 : PrimeValue := ⟨676589, pr676589⟩
private theorem pr676747 : PrimeCertificate 676747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv131]) (by decide +kernel)
def pv676747 : PrimeValue := ⟨676747, pr676747⟩
private theorem pr676883 : PrimeCertificate 676883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv3163]) (by decide +kernel)
def pv676883 : PrimeValue := ⟨676883, pr676883⟩
private theorem pr676919 : PrimeCertificate 676919 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv29,pv1061]) (by decide +kernel)
def pv676919 : PrimeValue := ⟨676919, pr676919⟩
private theorem pr676943 : PrimeCertificate 676943 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv48353]) (by decide +kernel)
def pv676943 : PrimeValue := ⟨676943, pr676943⟩
private theorem pr677021 : PrimeCertificate 677021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv33851]) (by decide +kernel)
def pv677021 : PrimeValue := ⟨677021, pr677021⟩
private theorem pr677077 : PrimeCertificate 677077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv3319]) (by decide +kernel)
def pv677077 : PrimeValue := ⟨677077, pr677077⟩
private theorem pr677107 : PrimeCertificate 677107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12539]) (by decide +kernel)
def pv677107 : PrimeValue := ⟨677107, pr677107⟩
private theorem pr677119 : PrimeCertificate 677119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv8681]) (by decide +kernel)
def pv677119 : PrimeValue := ⟨677119, pr677119⟩
private theorem pr677167 : PrimeCertificate 677167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv23,pv701]) (by decide +kernel)
def pv677167 : PrimeValue := ⟨677167, pr677167⟩
private theorem pr677323 : PrimeCertificate 677323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv113]) (by decide +kernel)
def pv677323 : PrimeValue := ⟨677323, pr677323⟩
private theorem pr677471 : PrimeCertificate 677471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv37,pv1831]) (by decide +kernel)
def pv677471 : PrimeValue := ⟨677471, pr677471⟩
private theorem pr677531 : PrimeCertificate 677531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv9679]) (by decide +kernel)
def pv677531 : PrimeValue := ⟨677531, pr677531⟩
private theorem pr677639 : PrimeCertificate 677639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv67,pv389]) (by decide +kernel)
def pv677639 : PrimeValue := ⟨677639, pr677639⟩
private theorem pr677681 : PrimeCertificate 677681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv43,pv197]) (by decide +kernel)
def pv677681 : PrimeValue := ⟨677681, pr677681⟩
private theorem pr677959 : PrimeCertificate 677959 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv19,pv313]) (by decide +kernel)
def pv677959 : PrimeValue := ⟨677959, pr677959⟩
private theorem pr678133 : PrimeCertificate 678133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv23]) (by decide +kernel)
def pv678133 : PrimeValue := ⟨678133, pr678133⟩
private theorem pr678289 : PrimeCertificate 678289 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv1087]) (by decide +kernel)
def pv678289 : PrimeValue := ⟨678289, pr678289⟩
private theorem pr678299 : PrimeCertificate 678299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv229,pv1481]) (by decide +kernel)
def pv678299 : PrimeValue := ⟨678299, pr678299⟩
private theorem pr678329 : PrimeCertificate 678329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv12113]) (by decide +kernel)
def pv678329 : PrimeValue := ⟨678329, pr678329⟩
private theorem pr678371 : PrimeCertificate 678371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv881]) (by decide +kernel)
def pv678371 : PrimeValue := ⟨678371, pr678371⟩
private theorem pr678463 : PrimeCertificate 678463 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv73,pv1549]) (by decide +kernel)
def pv678463 : PrimeValue := ⟨678463, pr678463⟩
private theorem pr678493 : PrimeCertificate 678493 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv401]) (by decide +kernel)
def pv678493 : PrimeValue := ⟨678493, pr678493⟩
private theorem pr678581 : PrimeCertificate 678581 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv37,pv131]) (by decide +kernel)
def pv678581 : PrimeValue := ⟨678581, pr678581⟩
private theorem pr678649 : PrimeCertificate 678649 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv28277]) (by decide +kernel)
def pv678649 : PrimeValue := ⟨678649, pr678649⟩
private theorem pr678731 : PrimeCertificate 678731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv23,pv227]) (by decide +kernel)
def pv678731 : PrimeValue := ⟨678731, pr678731⟩
private theorem pr678773 : PrimeCertificate 678773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv169693]) (by decide +kernel)
def pv678773 : PrimeValue := ⟨678773, pr678773⟩
private theorem pr678809 : PrimeCertificate 678809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv61,pv107]) (by decide +kernel)
def pv678809 : PrimeValue := ⟨678809, pr678809⟩
private theorem pr678859 : PrimeCertificate 678859 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv113143]) (by decide +kernel)
def pv678859 : PrimeValue := ⟨678859, pr678859⟩
private theorem pr678883 : PrimeCertificate 678883 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv113147]) (by decide +kernel)
def pv678883 : PrimeValue := ⟨678883, pr678883⟩
private theorem pr678941 : PrimeCertificate 678941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv83,pv409]) (by decide +kernel)
def pv678941 : PrimeValue := ⟨678941, pr678941⟩
private theorem pr678959 : PrimeCertificate 678959 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv48497]) (by decide +kernel)
def pv678959 : PrimeValue := ⟨678959, pr678959⟩
private theorem pr679039 : PrimeCertificate 679039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv113173]) (by decide +kernel)
def pv679039 : PrimeValue := ⟨679039, pr679039⟩
private theorem pr679087 : PrimeCertificate 679087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv1217]) (by decide +kernel)
def pv679087 : PrimeValue := ⟨679087, pr679087⟩
private theorem pr679153 : PrimeCertificate 679153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv14149]) (by decide +kernel)
def pv679153 : PrimeValue := ⟨679153, pr679153⟩
private theorem pr679183 : PrimeCertificate 679183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv103,pv157]) (by decide +kernel)
def pv679183 : PrimeValue := ⟨679183, pr679183⟩
private theorem pr679229 : PrimeCertificate 679229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv43,pv359]) (by decide +kernel)
def pv679229 : PrimeValue := ⟨679229, pr679229⟩
private theorem pr679249 : PrimeCertificate 679249 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv53,pv89]) (by decide +kernel)
def pv679249 : PrimeValue := ⟨679249, pr679249⟩
private theorem pr679297 : PrimeCertificate 679297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv61]) (by decide +kernel)
def pv679297 : PrimeValue := ⟨679297, pr679297⟩
private theorem pr679319 : PrimeCertificate 679319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv339659]) (by decide +kernel)
def pv679319 : PrimeValue := ⟨679319, pr679319⟩
private theorem pr679403 : PrimeCertificate 679403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv941]) (by decide +kernel)
def pv679403 : PrimeValue := ⟨679403, pr679403⟩
private theorem pr679463 : PrimeCertificate 679463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv48533]) (by decide +kernel)
def pv679463 : PrimeValue := ⟨679463, pr679463⟩
private theorem pr679597 : PrimeCertificate 679597 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv56633]) (by decide +kernel)
def pv679597 : PrimeValue := ⟨679597, pr679597⟩
private theorem pr679603 : PrimeCertificate 679603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv1471]) (by decide +kernel)
def pv679603 : PrimeValue := ⟨679603, pr679603⟩
private theorem pr679633 : PrimeCertificate 679633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv14159]) (by decide +kernel)
def pv679633 : PrimeValue := ⟨679633, pr679633⟩
private theorem pr679639 : PrimeCertificate 679639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv227,pv499]) (by decide +kernel)
def pv679639 : PrimeValue := ⟨679639, pr679639⟩
private theorem pr679733 : PrimeCertificate 679733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv169933]) (by decide +kernel)
def pv679733 : PrimeValue := ⟨679733, pr679733⟩
private theorem pr679781 : PrimeCertificate 679781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv829]) (by decide +kernel)
def pv679781 : PrimeValue := ⟨679781, pr679781⟩
private theorem pr679823 : PrimeCertificate 679823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv2377]) (by decide +kernel)
def pv679823 : PrimeValue := ⟨679823, pr679823⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
