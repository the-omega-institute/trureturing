/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table040
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table040.pv106391
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table005
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr106391 : PrimeCertificate 106391 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv10639]) (by decide +kernel)
def pv106391 : PrimeValue := ⟨106391, pr106391⟩
private theorem pr106397 : PrimeCertificate 106397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv397]) (by decide +kernel)
def pv106397 : PrimeValue := ⟨106397, pr106397⟩
private theorem pr106411 : PrimeCertificate 106411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3547]) (by decide +kernel)
def pv106411 : PrimeValue := ⟨106411, pr106411⟩
private theorem pr106427 : PrimeCertificate 106427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv419]) (by decide +kernel)
def pv106427 : PrimeValue := ⟨106427, pr106427⟩
private theorem pr106433 : PrimeCertificate 106433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1663]) (by decide +kernel)
def pv106433 : PrimeValue := ⟨106433, pr106433⟩
private theorem pr106441 : PrimeCertificate 106441 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv887]) (by decide +kernel)
def pv106441 : PrimeValue := ⟨106441, pr106441⟩
private theorem pr106451 : PrimeCertificate 106451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2129]) (by decide +kernel)
def pv106451 : PrimeValue := ⟨106451, pr106451⟩
private theorem pr106453 : PrimeCertificate 106453 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv2957]) (by decide +kernel)
def pv106453 : PrimeValue := ⟨106453, pr106453⟩
private theorem pr106487 : PrimeCertificate 106487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv1439]) (by decide +kernel)
def pv106487 : PrimeValue := ⟨106487, pr106487⟩
private theorem pr106501 : PrimeCertificate 106501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv106501 : PrimeValue := ⟨106501, pr106501⟩
private theorem pr106531 : PrimeCertificate 106531 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv53,pv67]) (by decide +kernel)
def pv106531 : PrimeValue := ⟨106531, pr106531⟩
private theorem pr106537 : PrimeCertificate 106537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv193]) (by decide +kernel)
def pv106537 : PrimeValue := ⟨106537, pr106537⟩
private theorem pr106541 : PrimeCertificate 106541 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv761]) (by decide +kernel)
def pv106541 : PrimeValue := ⟨106541, pr106541⟩
private theorem pr106543 : PrimeCertificate 106543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1973]) (by decide +kernel)
def pv106543 : PrimeValue := ⟨106543, pr106543⟩
private theorem pr106591 : PrimeCertificate 106591 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv17,pv19]) (by decide +kernel)
def pv106591 : PrimeValue := ⟨106591, pr106591⟩
private theorem pr106619 : PrimeCertificate 106619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53309]) (by decide +kernel)
def pv106619 : PrimeValue := ⟨106619, pr106619⟩
private theorem pr106627 : PrimeCertificate 106627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1367]) (by decide +kernel)
def pv106627 : PrimeValue := ⟨106627, pr106627⟩
private theorem pr106637 : PrimeCertificate 106637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv503]) (by decide +kernel)
def pv106637 : PrimeValue := ⟨106637, pr106637⟩
private theorem pr106649 : PrimeCertificate 106649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13331]) (by decide +kernel)
def pv106649 : PrimeValue := ⟨106649, pr106649⟩
private theorem pr106657 : PrimeCertificate 106657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv101]) (by decide +kernel)
def pv106657 : PrimeValue := ⟨106657, pr106657⟩
private theorem pr106661 : PrimeCertificate 106661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5333]) (by decide +kernel)
def pv106661 : PrimeValue := ⟨106661, pr106661⟩
private theorem pr106663 : PrimeCertificate 106663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv613]) (by decide +kernel)
def pv106663 : PrimeValue := ⟨106663, pr106663⟩
private theorem pr106669 : PrimeCertificate 106669 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv2963]) (by decide +kernel)
def pv106669 : PrimeValue := ⟨106669, pr106669⟩
private theorem pr106681 : PrimeCertificate 106681 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv7,pv127]) (by decide +kernel)
def pv106681 : PrimeValue := ⟨106681, pr106681⟩
private theorem pr106693 : PrimeCertificate 106693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv523]) (by decide +kernel)
def pv106693 : PrimeValue := ⟨106693, pr106693⟩
private theorem pr106699 : PrimeCertificate 106699 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17783]) (by decide +kernel)
def pv106699 : PrimeValue := ⟨106699, pr106699⟩
private theorem pr106703 : PrimeCertificate 106703 :=
  certifyPrime (q := pv7) (ls := [pv2,pv31,pv1721]) (by decide +kernel)
def pv106703 : PrimeValue := ⟨106703, pr106703⟩
private theorem pr106727 : PrimeCertificate 106727 :=
  certifyPrime (q := pv11) (ls := [pv2,pv17,pv43,pv73]) (by decide +kernel)
def pv106727 : PrimeValue := ⟨106727, pr106727⟩
private theorem pr106739 : PrimeCertificate 106739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv643]) (by decide +kernel)
def pv106739 : PrimeValue := ⟨106739, pr106739⟩
private theorem pr106747 : PrimeCertificate 106747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17791]) (by decide +kernel)
def pv106747 : PrimeValue := ⟨106747, pr106747⟩
private theorem pr106751 : PrimeCertificate 106751 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv61]) (by decide +kernel)
def pv106751 : PrimeValue := ⟨106751, pr106751⟩
private theorem pr106753 : PrimeCertificate 106753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv139]) (by decide +kernel)
def pv106753 : PrimeValue := ⟨106753, pr106753⟩
private theorem pr106781 : PrimeCertificate 106781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv281]) (by decide +kernel)
def pv106781 : PrimeValue := ⟨106781, pr106781⟩
private theorem pr106783 : PrimeCertificate 106783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv37]) (by decide +kernel)
def pv106783 : PrimeValue := ⟨106783, pr106783⟩
private theorem pr106787 : PrimeCertificate 106787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv499]) (by decide +kernel)
def pv106787 : PrimeValue := ⟨106787, pr106787⟩
private theorem pr106859 : PrimeCertificate 106859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv101]) (by decide +kernel)
def pv106859 : PrimeValue := ⟨106859, pr106859⟩
private theorem pr106861 : PrimeCertificate 106861 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv137]) (by decide +kernel)
def pv106861 : PrimeValue := ⟨106861, pr106861⟩
private theorem pr106867 : PrimeCertificate 106867 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1979]) (by decide +kernel)
def pv106867 : PrimeValue := ⟨106867, pr106867⟩
private theorem pr106871 : PrimeCertificate 106871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv10687]) (by decide +kernel)
def pv106871 : PrimeValue := ⟨106871, pr106871⟩
private theorem pr106877 : PrimeCertificate 106877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv347]) (by decide +kernel)
def pv106877 : PrimeValue := ⟨106877, pr106877⟩
private theorem pr106903 : PrimeCertificate 106903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5939]) (by decide +kernel)
def pv106903 : PrimeValue := ⟨106903, pr106903⟩
private theorem pr106907 : PrimeCertificate 106907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53453]) (by decide +kernel)
def pv106907 : PrimeValue := ⟨106907, pr106907⟩
private theorem pr106921 : PrimeCertificate 106921 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv106921 : PrimeValue := ⟨106921, pr106921⟩
private theorem pr106937 : PrimeCertificate 106937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13367]) (by decide +kernel)
def pv106937 : PrimeValue := ⟨106937, pr106937⟩
private theorem pr106949 : PrimeCertificate 106949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv26737]) (by decide +kernel)
def pv106949 : PrimeValue := ⟨106949, pr106949⟩
private theorem pr106957 : PrimeCertificate 106957 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2971]) (by decide +kernel)
def pv106957 : PrimeValue := ⟨106957, pr106957⟩
private theorem pr106961 : PrimeCertificate 106961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv191]) (by decide +kernel)
def pv106961 : PrimeValue := ⟨106961, pr106961⟩
private theorem pr106963 : PrimeCertificate 106963 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17827]) (by decide +kernel)
def pv106963 : PrimeValue := ⟨106963, pr106963⟩
private theorem pr106979 : PrimeCertificate 106979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv601]) (by decide +kernel)
def pv106979 : PrimeValue := ⟨106979, pr106979⟩
private theorem pr106993 : PrimeCertificate 106993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv743]) (by decide +kernel)
def pv106993 : PrimeValue := ⟨106993, pr106993⟩
private theorem pr107021 : PrimeCertificate 107021 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv5351]) (by decide +kernel)
def pv107021 : PrimeValue := ⟨107021, pr107021⟩
private theorem pr107033 : PrimeCertificate 107033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv787]) (by decide +kernel)
def pv107033 : PrimeValue := ⟨107033, pr107033⟩
private theorem pr107057 : PrimeCertificate 107057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6691]) (by decide +kernel)
def pv107057 : PrimeValue := ⟨107057, pr107057⟩
private theorem pr107069 : PrimeCertificate 107069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv29,pv71]) (by decide +kernel)
def pv107069 : PrimeValue := ⟨107069, pr107069⟩
private theorem pr107071 : PrimeCertificate 107071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv43,pv83]) (by decide +kernel)
def pv107071 : PrimeValue := ⟨107071, pr107071⟩
private theorem pr107089 : PrimeCertificate 107089 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv97]) (by decide +kernel)
def pv107089 : PrimeValue := ⟨107089, pr107089⟩
private theorem pr107099 : PrimeCertificate 107099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53549]) (by decide +kernel)
def pv107099 : PrimeValue := ⟨107099, pr107099⟩
private theorem pr107101 : PrimeCertificate 107101 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv107101 : PrimeValue := ⟨107101, pr107101⟩
private theorem pr107119 : PrimeCertificate 107119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv541]) (by decide +kernel)
def pv107119 : PrimeValue := ⟨107119, pr107119⟩
private theorem pr107123 : PrimeCertificate 107123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2819]) (by decide +kernel)
def pv107123 : PrimeValue := ⟨107123, pr107123⟩
private theorem pr107137 : PrimeCertificate 107137 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv107137 : PrimeValue := ⟨107137, pr107137⟩
private theorem pr107171 : PrimeCertificate 107171 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv1531]) (by decide +kernel)
def pv107171 : PrimeValue := ⟨107171, pr107171⟩
private theorem pr107183 : PrimeCertificate 107183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53591]) (by decide +kernel)
def pv107183 : PrimeValue := ⟨107183, pr107183⟩
private theorem pr107197 : PrimeCertificate 107197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8933]) (by decide +kernel)
def pv107197 : PrimeValue := ⟨107197, pr107197⟩
private theorem pr107201 : PrimeCertificate 107201 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv67]) (by decide +kernel)
def pv107201 : PrimeValue := ⟨107201, pr107201⟩
private theorem pr107209 : PrimeCertificate 107209 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1489]) (by decide +kernel)
def pv107209 : PrimeValue := ⟨107209, pr107209⟩
private theorem pr107227 : PrimeCertificate 107227 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv23,pv37]) (by decide +kernel)
def pv107227 : PrimeValue := ⟨107227, pr107227⟩
private theorem pr107243 : PrimeCertificate 107243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv43]) (by decide +kernel)
def pv107243 : PrimeValue := ⟨107243, pr107243⟩
private theorem pr107251 : PrimeCertificate 107251 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv107251 : PrimeValue := ⟨107251, pr107251⟩
private theorem pr107273 : PrimeCertificate 107273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv23,pv53]) (by decide +kernel)
def pv107273 : PrimeValue := ⟨107273, pr107273⟩
private theorem pr107279 : PrimeCertificate 107279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv53639]) (by decide +kernel)
def pv107279 : PrimeValue := ⟨107279, pr107279⟩
private theorem pr107309 : PrimeCertificate 107309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139,pv193]) (by decide +kernel)
def pv107309 : PrimeValue := ⟨107309, pr107309⟩
private theorem pr107323 : PrimeCertificate 107323 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv31,pv577]) (by decide +kernel)
def pv107323 : PrimeValue := ⟨107323, pr107323⟩
private theorem pr107339 : PrimeCertificate 107339 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv17,pv41]) (by decide +kernel)
def pv107339 : PrimeValue := ⟨107339, pr107339⟩
private theorem pr107347 : PrimeCertificate 107347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17891]) (by decide +kernel)
def pv107347 : PrimeValue := ⟨107347, pr107347⟩
private theorem pr107351 : PrimeCertificate 107351 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv19,pv113]) (by decide +kernel)
def pv107351 : PrimeValue := ⟨107351, pr107351⟩
private theorem pr107357 : PrimeCertificate 107357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv26839]) (by decide +kernel)
def pv107357 : PrimeValue := ⟨107357, pr107357⟩
private theorem pr107377 : PrimeCertificate 107377 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv2237]) (by decide +kernel)
def pv107377 : PrimeValue := ⟨107377, pr107377⟩
private theorem pr107441 : PrimeCertificate 107441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv79]) (by decide +kernel)
def pv107441 : PrimeValue := ⟨107441, pr107441⟩
private theorem pr107449 : PrimeCertificate 107449 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv37]) (by decide +kernel)
def pv107449 : PrimeValue := ⟨107449, pr107449⟩
private theorem pr107453 : PrimeCertificate 107453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv26863]) (by decide +kernel)
def pv107453 : PrimeValue := ⟨107453, pr107453⟩
private theorem pr107467 : PrimeCertificate 107467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17911]) (by decide +kernel)
def pv107467 : PrimeValue := ⟨107467, pr107467⟩
private theorem pr107473 : PrimeCertificate 107473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2239]) (by decide +kernel)
def pv107473 : PrimeValue := ⟨107473, pr107473⟩
private theorem pr107507 : PrimeCertificate 107507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1097]) (by decide +kernel)
def pv107507 : PrimeValue := ⟨107507, pr107507⟩
private theorem pr107509 : PrimeCertificate 107509 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv31]) (by decide +kernel)
def pv107509 : PrimeValue := ⟨107509, pr107509⟩
private theorem pr107563 : PrimeCertificate 107563 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv197]) (by decide +kernel)
def pv107563 : PrimeValue := ⟨107563, pr107563⟩
private theorem pr107581 : PrimeCertificate 107581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv163]) (by decide +kernel)
def pv107581 : PrimeValue := ⟨107581, pr107581⟩
private theorem pr107599 : PrimeCertificate 107599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv227]) (by decide +kernel)
def pv107599 : PrimeValue := ⟨107599, pr107599⟩
private theorem pr107603 : PrimeCertificate 107603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv67,pv73]) (by decide +kernel)
def pv107603 : PrimeValue := ⟨107603, pr107603⟩
private theorem pr107621 : PrimeCertificate 107621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5381]) (by decide +kernel)
def pv107621 : PrimeValue := ⟨107621, pr107621⟩
private theorem pr107641 : PrimeCertificate 107641 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv23]) (by decide +kernel)
def pv107641 : PrimeValue := ⟨107641, pr107641⟩
private theorem pr107647 : PrimeCertificate 107647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv233]) (by decide +kernel)
def pv107647 : PrimeValue := ⟨107647, pr107647⟩
private theorem pr107671 : PrimeCertificate 107671 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv37,pv97]) (by decide +kernel)
def pv107671 : PrimeValue := ⟨107671, pr107671⟩
private theorem pr107687 : PrimeCertificate 107687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv2341]) (by decide +kernel)
def pv107687 : PrimeValue := ⟨107687, pr107687⟩
private theorem pr107693 : PrimeCertificate 107693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv109]) (by decide +kernel)
def pv107693 : PrimeValue := ⟨107693, pr107693⟩
private theorem pr107699 : PrimeCertificate 107699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53849]) (by decide +kernel)
def pv107699 : PrimeValue := ⟨107699, pr107699⟩
private theorem pr107713 : PrimeCertificate 107713 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv107713 : PrimeValue := ⟨107713, pr107713⟩
private theorem pr107717 : PrimeCertificate 107717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv3847]) (by decide +kernel)
def pv107717 : PrimeValue := ⟨107717, pr107717⟩
private theorem pr107719 : PrimeCertificate 107719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1381]) (by decide +kernel)
def pv107719 : PrimeValue := ⟨107719, pr107719⟩
private theorem pr107741 : PrimeCertificate 107741 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv5387]) (by decide +kernel)
def pv107741 : PrimeValue := ⟨107741, pr107741⟩
private theorem pr107747 : PrimeCertificate 107747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv3169]) (by decide +kernel)
def pv107747 : PrimeValue := ⟨107747, pr107747⟩
private theorem pr107761 : PrimeCertificate 107761 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv449]) (by decide +kernel)
def pv107761 : PrimeValue := ⟨107761, pr107761⟩
private theorem pr107773 : PrimeCertificate 107773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1283]) (by decide +kernel)
def pv107773 : PrimeValue := ⟨107773, pr107773⟩
private theorem pr107777 : PrimeCertificate 107777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv421]) (by decide +kernel)
def pv107777 : PrimeValue := ⟨107777, pr107777⟩
private theorem pr107791 : PrimeCertificate 107791 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3593]) (by decide +kernel)
def pv107791 : PrimeValue := ⟨107791, pr107791⟩
private theorem pr107827 : PrimeCertificate 107827 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17971]) (by decide +kernel)
def pv107827 : PrimeValue := ⟨107827, pr107827⟩
private theorem pr107839 : PrimeCertificate 107839 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv1997]) (by decide +kernel)
def pv107839 : PrimeValue := ⟨107839, pr107839⟩
private theorem pr107843 : PrimeCertificate 107843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv7703]) (by decide +kernel)
def pv107843 : PrimeValue := ⟨107843, pr107843⟩
private theorem pr107857 : PrimeCertificate 107857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv107]) (by decide +kernel)
def pv107857 : PrimeValue := ⟨107857, pr107857⟩
private theorem pr107867 : PrimeCertificate 107867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4903]) (by decide +kernel)
def pv107867 : PrimeValue := ⟨107867, pr107867⟩
private theorem pr107873 : PrimeCertificate 107873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3371]) (by decide +kernel)
def pv107873 : PrimeValue := ⟨107873, pr107873⟩
private theorem pr107881 : PrimeCertificate 107881 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv29,pv31]) (by decide +kernel)
def pv107881 : PrimeValue := ⟨107881, pr107881⟩
private theorem pr107903 : PrimeCertificate 107903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53951]) (by decide +kernel)
def pv107903 : PrimeValue := ⟨107903, pr107903⟩
private theorem pr107923 : PrimeCertificate 107923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17987]) (by decide +kernel)
def pv107923 : PrimeValue := ⟨107923, pr107923⟩
private theorem pr107927 : PrimeCertificate 107927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv593]) (by decide +kernel)
def pv107927 : PrimeValue := ⟨107927, pr107927⟩
private theorem pr107941 : PrimeCertificate 107941 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv257]) (by decide +kernel)
def pv107941 : PrimeValue := ⟨107941, pr107941⟩
private theorem pr107951 : PrimeCertificate 107951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv127]) (by decide +kernel)
def pv107951 : PrimeValue := ⟨107951, pr107951⟩
private theorem pr107971 : PrimeCertificate 107971 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv59,pv61]) (by decide +kernel)
def pv107971 : PrimeValue := ⟨107971, pr107971⟩
private theorem pr107981 : PrimeCertificate 107981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5399]) (by decide +kernel)
def pv107981 : PrimeValue := ⟨107981, pr107981⟩
private theorem pr107999 : PrimeCertificate 107999 :=
  certifyPrime (q := pv13) (ls := [pv2,pv11,pv4909]) (by decide +kernel)
def pv107999 : PrimeValue := ⟨107999, pr107999⟩
private theorem pr108007 : PrimeCertificate 108007 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv47,pv383]) (by decide +kernel)
def pv108007 : PrimeValue := ⟨108007, pr108007⟩
private theorem pr108011 : PrimeCertificate 108011 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv1543]) (by decide +kernel)
def pv108011 : PrimeValue := ⟨108011, pr108011⟩
private theorem pr108013 : PrimeCertificate 108013 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv9001]) (by decide +kernel)
def pv108013 : PrimeValue := ⟨108013, pr108013⟩
private theorem pr108023 : PrimeCertificate 108023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv54011]) (by decide +kernel)
def pv108023 : PrimeValue := ⟨108023, pr108023⟩
private theorem pr108037 : PrimeCertificate 108037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3001]) (by decide +kernel)
def pv108037 : PrimeValue := ⟨108037, pr108037⟩
private theorem pr108061 : PrimeCertificate 108061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1801]) (by decide +kernel)
def pv108061 : PrimeValue := ⟨108061, pr108061⟩
private theorem pr108079 : PrimeCertificate 108079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv18013]) (by decide +kernel)
def pv108079 : PrimeValue := ⟨108079, pr108079⟩
private theorem pr108089 : PrimeCertificate 108089 :=
  certifyPrime (q := pv13) (ls := [pv2,pv59,pv229]) (by decide +kernel)
def pv108089 : PrimeValue := ⟨108089, pr108089⟩
private theorem pr108107 : PrimeCertificate 108107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv191,pv283]) (by decide +kernel)
def pv108107 : PrimeValue := ⟨108107, pr108107⟩
private theorem pr108109 : PrimeCertificate 108109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv13]) (by decide +kernel)
def pv108109 : PrimeValue := ⟨108109, pr108109⟩
private theorem pr108127 : PrimeCertificate 108127 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv6007]) (by decide +kernel)
def pv108127 : PrimeValue := ⟨108127, pr108127⟩
private theorem pr108131 : PrimeCertificate 108131 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv983]) (by decide +kernel)
def pv108131 : PrimeValue := ⟨108131, pr108131⟩
private theorem pr108139 : PrimeCertificate 108139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv269]) (by decide +kernel)
def pv108139 : PrimeValue := ⟨108139, pr108139⟩
private theorem pr108161 : PrimeCertificate 108161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv108161 : PrimeValue := ⟨108161, pr108161⟩
private theorem pr108179 : PrimeCertificate 108179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv7727]) (by decide +kernel)
def pv108179 : PrimeValue := ⟨108179, pr108179⟩
private theorem pr108187 : PrimeCertificate 108187 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv73]) (by decide +kernel)
def pv108187 : PrimeValue := ⟨108187, pr108187⟩
private theorem pr108191 : PrimeCertificate 108191 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv31,pv349]) (by decide +kernel)
def pv108191 : PrimeValue := ⟨108191, pr108191⟩
private theorem pr108193 : PrimeCertificate 108193 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv108193 : PrimeValue := ⟨108193, pr108193⟩
private theorem pr108203 : PrimeCertificate 108203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv54101]) (by decide +kernel)
def pv108203 : PrimeValue := ⟨108203, pr108203⟩
private theorem pr108211 : PrimeCertificate 108211 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3607]) (by decide +kernel)
def pv108211 : PrimeValue := ⟨108211, pr108211⟩
private theorem pr108217 : PrimeCertificate 108217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv167]) (by decide +kernel)
def pv108217 : PrimeValue := ⟨108217, pr108217⟩
private theorem pr108223 : PrimeCertificate 108223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv1061]) (by decide +kernel)
def pv108223 : PrimeValue := ⟨108223, pr108223⟩
private theorem pr108233 : PrimeCertificate 108233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv163]) (by decide +kernel)
def pv108233 : PrimeValue := ⟨108233, pr108233⟩
private theorem pr108247 : PrimeCertificate 108247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv18041]) (by decide +kernel)
def pv108247 : PrimeValue := ⟨108247, pr108247⟩
private theorem pr108263 : PrimeCertificate 108263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv19,pv37]) (by decide +kernel)
def pv108263 : PrimeValue := ⟨108263, pr108263⟩
private theorem pr108271 : PrimeCertificate 108271 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv401]) (by decide +kernel)
def pv108271 : PrimeValue := ⟨108271, pr108271⟩
private theorem pr108287 : PrimeCertificate 108287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv1867]) (by decide +kernel)
def pv108287 : PrimeValue := ⟨108287, pr108287⟩
private theorem pr108289 : PrimeCertificate 108289 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv108289 : PrimeValue := ⟨108289, pr108289⟩
private theorem pr108293 : PrimeCertificate 108293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv27073]) (by decide +kernel)
def pv108293 : PrimeValue := ⟨108293, pr108293⟩
private theorem pr108301 : PrimeCertificate 108301 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv108301 : PrimeValue := ⟨108301, pr108301⟩
private theorem pr108343 : PrimeCertificate 108343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv463]) (by decide +kernel)
def pv108343 : PrimeValue := ⟨108343, pr108343⟩
private theorem pr108347 : PrimeCertificate 108347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv71,pv109]) (by decide +kernel)
def pv108347 : PrimeValue := ⟨108347, pr108347⟩
private theorem pr108359 : PrimeCertificate 108359 :=
  certifyPrime (q := pv11) (ls := [pv2,pv17,pv3187]) (by decide +kernel)
def pv108359 : PrimeValue := ⟨108359, pr108359⟩
private theorem pr108377 : PrimeCertificate 108377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv23,pv31]) (by decide +kernel)
def pv108377 : PrimeValue := ⟨108377, pr108377⟩
private theorem pr108379 : PrimeCertificate 108379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv223]) (by decide +kernel)
def pv108379 : PrimeValue := ⟨108379, pr108379⟩
private theorem pr108401 : PrimeCertificate 108401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv271]) (by decide +kernel)
def pv108401 : PrimeValue := ⟨108401, pr108401⟩
private theorem pr108413 : PrimeCertificate 108413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv27103]) (by decide +kernel)
def pv108413 : PrimeValue := ⟨108413, pr108413⟩
private theorem pr108421 : PrimeCertificate 108421 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv13,pv139]) (by decide +kernel)
def pv108421 : PrimeValue := ⟨108421, pr108421⟩
private theorem pr108457 : PrimeCertificate 108457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4519]) (by decide +kernel)
def pv108457 : PrimeValue := ⟨108457, pr108457⟩
private theorem pr108461 : PrimeCertificate 108461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv17,pv29]) (by decide +kernel)
def pv108461 : PrimeValue := ⟨108461, pr108461⟩
private theorem pr108463 : PrimeCertificate 108463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv18077]) (by decide +kernel)
def pv108463 : PrimeValue := ⟨108463, pr108463⟩
private theorem pr108497 : PrimeCertificate 108497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6781]) (by decide +kernel)
def pv108497 : PrimeValue := ⟨108497, pr108497⟩
private theorem pr108499 : PrimeCertificate 108499 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv107]) (by decide +kernel)
def pv108499 : PrimeValue := ⟨108499, pr108499⟩
private theorem pr108503 : PrimeCertificate 108503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv54251]) (by decide +kernel)
def pv108503 : PrimeValue := ⟨108503, pr108503⟩
private theorem pr108517 : PrimeCertificate 108517 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9043]) (by decide +kernel)
def pv108517 : PrimeValue := ⟨108517, pr108517⟩
private theorem pr108529 : PrimeCertificate 108529 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv17,pv19]) (by decide +kernel)
def pv108529 : PrimeValue := ⟨108529, pr108529⟩
private theorem pr108533 : PrimeCertificate 108533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv631]) (by decide +kernel)
def pv108533 : PrimeValue := ⟨108533, pr108533⟩
private theorem pr108541 : PrimeCertificate 108541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv67]) (by decide +kernel)
def pv108541 : PrimeValue := ⟨108541, pr108541⟩
private theorem pr108553 : PrimeCertificate 108553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4523]) (by decide +kernel)
def pv108553 : PrimeValue := ⟨108553, pr108553⟩
private theorem pr108557 : PrimeCertificate 108557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv3877]) (by decide +kernel)
def pv108557 : PrimeValue := ⟨108557, pr108557⟩
private theorem pr108571 : PrimeCertificate 108571 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv11,pv47]) (by decide +kernel)
def pv108571 : PrimeValue := ⟨108571, pr108571⟩
private theorem pr108587 : PrimeCertificate 108587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv54293]) (by decide +kernel)
def pv108587 : PrimeValue := ⟨108587, pr108587⟩
private theorem pr108631 : PrimeCertificate 108631 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv17,pv71]) (by decide +kernel)
def pv108631 : PrimeValue := ⟨108631, pr108631⟩
private theorem pr108637 : PrimeCertificate 108637 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv823]) (by decide +kernel)
def pv108637 : PrimeValue := ⟨108637, pr108637⟩
private theorem pr108643 : PrimeCertificate 108643 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv953]) (by decide +kernel)
def pv108643 : PrimeValue := ⟨108643, pr108643⟩
private theorem pr108649 : PrimeCertificate 108649 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv503]) (by decide +kernel)
def pv108649 : PrimeValue := ⟨108649, pr108649⟩
private theorem pr108677 : PrimeCertificate 108677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv269]) (by decide +kernel)
def pv108677 : PrimeValue := ⟨108677, pr108677⟩
private theorem pr108707 : PrimeCertificate 108707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv37,pv113]) (by decide +kernel)
def pv108707 : PrimeValue := ⟨108707, pr108707⟩
private theorem pr108709 : PrimeCertificate 108709 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv9059]) (by decide +kernel)
def pv108709 : PrimeValue := ⟨108709, pr108709⟩
private theorem pr108727 : PrimeCertificate 108727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv18121]) (by decide +kernel)
def pv108727 : PrimeValue := ⟨108727, pr108727⟩
private theorem pr108739 : PrimeCertificate 108739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv863]) (by decide +kernel)
def pv108739 : PrimeValue := ⟨108739, pr108739⟩
private theorem pr108751 : PrimeCertificate 108751 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv108751 : PrimeValue := ⟨108751, pr108751⟩
private theorem pr108761 : PrimeCertificate 108761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2719]) (by decide +kernel)
def pv108761 : PrimeValue := ⟨108761, pr108761⟩
private theorem pr108769 : PrimeCertificate 108769 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv103]) (by decide +kernel)
def pv108769 : PrimeValue := ⟨108769, pr108769⟩
private theorem pr108791 : PrimeCertificate 108791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv23,pv43]) (by decide +kernel)
def pv108791 : PrimeValue := ⟨108791, pr108791⟩
private theorem pr108793 : PrimeCertificate 108793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1511]) (by decide +kernel)
def pv108793 : PrimeValue := ⟨108793, pr108793⟩
private theorem pr108799 : PrimeCertificate 108799 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv18133]) (by decide +kernel)
def pv108799 : PrimeValue := ⟨108799, pr108799⟩
private theorem pr108803 : PrimeCertificate 108803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv54401]) (by decide +kernel)
def pv108803 : PrimeValue := ⟨108803, pr108803⟩
private theorem pr108821 : PrimeCertificate 108821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5441]) (by decide +kernel)
def pv108821 : PrimeValue := ⟨108821, pr108821⟩
private theorem pr108827 : PrimeCertificate 108827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv54413]) (by decide +kernel)
def pv108827 : PrimeValue := ⟨108827, pr108827⟩
private theorem pr108863 : PrimeCertificate 108863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv53,pv79]) (by decide +kernel)
def pv108863 : PrimeValue := ⟨108863, pr108863⟩
private theorem pr108869 : PrimeCertificate 108869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1601]) (by decide +kernel)
def pv108869 : PrimeValue := ⟨108869, pr108869⟩
private theorem pr108877 : PrimeCertificate 108877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv211]) (by decide +kernel)
def pv108877 : PrimeValue := ⟨108877, pr108877⟩
private theorem pr108883 : PrimeCertificate 108883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv263]) (by decide +kernel)
def pv108883 : PrimeValue := ⟨108883, pr108883⟩
private theorem pr108887 : PrimeCertificate 108887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv54443]) (by decide +kernel)
def pv108887 : PrimeValue := ⟨108887, pr108887⟩
private theorem pr108893 : PrimeCertificate 108893 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv3889]) (by decide +kernel)
def pv108893 : PrimeValue := ⟨108893, pr108893⟩
private theorem pr108907 : PrimeCertificate 108907 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv2593]) (by decide +kernel)
def pv108907 : PrimeValue := ⟨108907, pr108907⟩
private theorem pr108917 : PrimeCertificate 108917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv373]) (by decide +kernel)
def pv108917 : PrimeValue := ⟨108917, pr108917⟩
private theorem pr108923 : PrimeCertificate 108923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4951]) (by decide +kernel)
def pv108923 : PrimeValue := ⟨108923, pr108923⟩
private theorem pr108929 : PrimeCertificate 108929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv37]) (by decide +kernel)
def pv108929 : PrimeValue := ⟨108929, pr108929⟩
private theorem pr108943 : PrimeCertificate 108943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv271]) (by decide +kernel)
def pv108943 : PrimeValue := ⟨108943, pr108943⟩
private theorem pr108947 : PrimeCertificate 108947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv47,pv61]) (by decide +kernel)
def pv108947 : PrimeValue := ⟨108947, pr108947⟩
private theorem pr108949 : PrimeCertificate 108949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1297]) (by decide +kernel)
def pv108949 : PrimeValue := ⟨108949, pr108949⟩
private theorem pr108961 : PrimeCertificate 108961 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv227]) (by decide +kernel)
def pv108961 : PrimeValue := ⟨108961, pr108961⟩
private theorem pr108967 : PrimeCertificate 108967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv127]) (by decide +kernel)
def pv108967 : PrimeValue := ⟨108967, pr108967⟩
private theorem pr108971 : PrimeCertificate 108971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv641]) (by decide +kernel)
def pv108971 : PrimeValue := ⟨108971, pr108971⟩
private theorem pr108991 : PrimeCertificate 108991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv173]) (by decide +kernel)
def pv108991 : PrimeValue := ⟨108991, pr108991⟩
private theorem pr109001 : PrimeCertificate 109001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv109]) (by decide +kernel)
def pv109001 : PrimeValue := ⟨109001, pr109001⟩
private theorem pr109013 : PrimeCertificate 109013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv27253]) (by decide +kernel)
def pv109013 : PrimeValue := ⟨109013, pr109013⟩
private theorem pr109037 : PrimeCertificate 109037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv27259]) (by decide +kernel)
def pv109037 : PrimeValue := ⟨109037, pr109037⟩
private theorem pr109049 : PrimeCertificate 109049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv317]) (by decide +kernel)
def pv109049 : PrimeValue := ⟨109049, pr109049⟩
private theorem pr109063 : PrimeCertificate 109063 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv73,pv83]) (by decide +kernel)
def pv109063 : PrimeValue := ⟨109063, pr109063⟩
private theorem pr109073 : PrimeCertificate 109073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv401]) (by decide +kernel)
def pv109073 : PrimeValue := ⟨109073, pr109073⟩
private theorem pr109097 : PrimeCertificate 109097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1049]) (by decide +kernel)
def pv109097 : PrimeValue := ⟨109097, pr109097⟩
private theorem pr109103 : PrimeCertificate 109103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv7793]) (by decide +kernel)
def pv109103 : PrimeValue := ⟨109103, pr109103⟩
private theorem pr109111 : PrimeCertificate 109111 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3637]) (by decide +kernel)
def pv109111 : PrimeValue := ⟨109111, pr109111⟩
private theorem pr109121 : PrimeCertificate 109121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv31]) (by decide +kernel)
def pv109121 : PrimeValue := ⟨109121, pr109121⟩
private theorem pr109133 : PrimeCertificate 109133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv27283]) (by decide +kernel)
def pv109133 : PrimeValue := ⟨109133, pr109133⟩
private theorem pr109139 : PrimeCertificate 109139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197,pv277]) (by decide +kernel)
def pv109139 : PrimeValue := ⟨109139, pr109139⟩
private theorem pr109141 : PrimeCertificate 109141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv107]) (by decide +kernel)
def pv109141 : PrimeValue := ⟨109141, pr109141⟩
private theorem pr109147 : PrimeCertificate 109147 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv18191]) (by decide +kernel)
def pv109147 : PrimeValue := ⟨109147, pr109147⟩
private theorem pr109159 : PrimeCertificate 109159 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv23,pv113]) (by decide +kernel)
def pv109159 : PrimeValue := ⟨109159, pr109159⟩
private theorem pr109171 : PrimeCertificate 109171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1213]) (by decide +kernel)
def pv109171 : PrimeValue := ⟨109171, pr109171⟩
private theorem pr109199 : PrimeCertificate 109199 :=
  certifyPrime (q := pv19) (ls := [pv2,pv71,pv769]) (by decide +kernel)
def pv109199 : PrimeValue := ⟨109199, pr109199⟩
private theorem pr109201 : PrimeCertificate 109201 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv109201 : PrimeValue := ⟨109201, pr109201⟩
private theorem pr109211 : PrimeCertificate 109211 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv67,pv163]) (by decide +kernel)
def pv109211 : PrimeValue := ⟨109211, pr109211⟩
private theorem pr109229 : PrimeCertificate 109229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv47,pv83]) (by decide +kernel)
def pv109229 : PrimeValue := ⟨109229, pr109229⟩
private theorem pr109267 : PrimeCertificate 109267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18211]) (by decide +kernel)
def pv109267 : PrimeValue := ⟨109267, pr109267⟩
private theorem pr109279 : PrimeCertificate 109279 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv467]) (by decide +kernel)
def pv109279 : PrimeValue := ⟨109279, pr109279⟩
private theorem pr109297 : PrimeCertificate 109297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv109297 : PrimeValue := ⟨109297, pr109297⟩
private theorem pr109303 : PrimeCertificate 109303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv18217]) (by decide +kernel)
def pv109303 : PrimeValue := ⟨109303, pr109303⟩
private theorem pr109313 : PrimeCertificate 109313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv61]) (by decide +kernel)
def pv109313 : PrimeValue := ⟨109313, pr109313⟩
private theorem pr109321 : PrimeCertificate 109321 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv911]) (by decide +kernel)
def pv109321 : PrimeValue := ⟨109321, pr109321⟩
private theorem pr109331 : PrimeCertificate 109331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv29]) (by decide +kernel)
def pv109331 : PrimeValue := ⟨109331, pr109331⟩
private theorem pr109357 : PrimeCertificate 109357 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv701]) (by decide +kernel)
def pv109357 : PrimeValue := ⟨109357, pr109357⟩
private theorem pr109363 : PrimeCertificate 109363 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1657]) (by decide +kernel)
def pv109363 : PrimeValue := ⟨109363, pr109363⟩
private theorem pr109367 : PrimeCertificate 109367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv149,pv367]) (by decide +kernel)
def pv109367 : PrimeValue := ⟨109367, pr109367⟩
private theorem pr109379 : PrimeCertificate 109379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv3217]) (by decide +kernel)
def pv109379 : PrimeValue := ⟨109379, pr109379⟩
private theorem pr109387 : PrimeCertificate 109387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv103]) (by decide +kernel)
def pv109387 : PrimeValue := ⟨109387, pr109387⟩
private theorem pr109391 : PrimeCertificate 109391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv10939]) (by decide +kernel)
def pv109391 : PrimeValue := ⟨109391, pr109391⟩
private theorem pr109397 : PrimeCertificate 109397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv3907]) (by decide +kernel)
def pv109397 : PrimeValue := ⟨109397, pr109397⟩
private theorem pr109423 : PrimeCertificate 109423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6079]) (by decide +kernel)
def pv109423 : PrimeValue := ⟨109423, pr109423⟩
private theorem pr109433 : PrimeCertificate 109433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13679]) (by decide +kernel)
def pv109433 : PrimeValue := ⟨109433, pr109433⟩
private theorem pr109441 : PrimeCertificate 109441 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv109441 : PrimeValue := ⟨109441, pr109441⟩
private theorem pr109451 : PrimeCertificate 109451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv199]) (by decide +kernel)
def pv109451 : PrimeValue := ⟨109451, pr109451⟩
private theorem pr109453 : PrimeCertificate 109453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1303]) (by decide +kernel)
def pv109453 : PrimeValue := ⟨109453, pr109453⟩
private theorem pr109469 : PrimeCertificate 109469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv27367]) (by decide +kernel)
def pv109469 : PrimeValue := ⟨109469, pr109469⟩
private theorem pr109471 : PrimeCertificate 109471 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv41,pv89]) (by decide +kernel)
def pv109471 : PrimeValue := ⟨109471, pr109471⟩
private theorem pr109481 : PrimeCertificate 109481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv17,pv23]) (by decide +kernel)
def pv109481 : PrimeValue := ⟨109481, pr109481⟩
private theorem pr109507 : PrimeCertificate 109507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18251]) (by decide +kernel)
def pv109507 : PrimeValue := ⟨109507, pr109507⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
