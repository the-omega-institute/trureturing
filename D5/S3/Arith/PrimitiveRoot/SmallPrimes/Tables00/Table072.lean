/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table072
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table072.pv229261
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr229261 : PrimeCertificate 229261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3821]) (by decide +kernel)
def pv229261 : PrimeValue := ⟨229261, pr229261⟩
private theorem pr229283 : PrimeCertificate 229283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv114641]) (by decide +kernel)
def pv229283 : PrimeValue := ⟨229283, pr229283⟩
private theorem pr229309 : PrimeCertificate 229309 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv97,pv197]) (by decide +kernel)
def pv229309 : PrimeValue := ⟨229309, pr229309⟩
private theorem pr229343 : PrimeCertificate 229343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv114671]) (by decide +kernel)
def pv229343 : PrimeValue := ⟨229343, pr229343⟩
private theorem pr229373 : PrimeCertificate 229373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv401]) (by decide +kernel)
def pv229373 : PrimeValue := ⟨229373, pr229373⟩
private theorem pr229393 : PrimeCertificate 229393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv229393 : PrimeValue := ⟨229393, pr229393⟩
private theorem pr229403 : PrimeCertificate 229403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv4987]) (by decide +kernel)
def pv229403 : PrimeValue := ⟨229403, pr229403⟩
private theorem pr229409 : PrimeCertificate 229409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv107]) (by decide +kernel)
def pv229409 : PrimeValue := ⟨229409, pr229409⟩
private theorem pr229423 : PrimeCertificate 229423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv38237]) (by decide +kernel)
def pv229423 : PrimeValue := ⟨229423, pr229423⟩
private theorem pr229433 : PrimeCertificate 229433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17,pv241]) (by decide +kernel)
def pv229433 : PrimeValue := ⟨229433, pr229433⟩
private theorem pr229459 : PrimeCertificate 229459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv167,pv229]) (by decide +kernel)
def pv229459 : PrimeValue := ⟨229459, pr229459⟩
private theorem pr229469 : PrimeCertificate 229469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv57367]) (by decide +kernel)
def pv229469 : PrimeValue := ⟨229469, pr229469⟩
private theorem pr229487 : PrimeCertificate 229487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv114743]) (by decide +kernel)
def pv229487 : PrimeValue := ⟨229487, pr229487⟩
private theorem pr229499 : PrimeCertificate 229499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv114749]) (by decide +kernel)
def pv229499 : PrimeValue := ⟨229499, pr229499⟩
private theorem pr229507 : PrimeCertificate 229507 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv1319]) (by decide +kernel)
def pv229507 : PrimeValue := ⟨229507, pr229507⟩
private theorem pr229547 : PrimeCertificate 229547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv114773]) (by decide +kernel)
def pv229547 : PrimeValue := ⟨229547, pr229547⟩
private theorem pr229583 : PrimeCertificate 229583 :=
  certifyPrime (q := pv7) (ls := [pv2,pv191,pv601]) (by decide +kernel)
def pv229583 : PrimeValue := ⟨229583, pr229583⟩
private theorem pr229589 : PrimeCertificate 229589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv57397]) (by decide +kernel)
def pv229589 : PrimeValue := ⟨229589, pr229589⟩
private theorem pr229591 : PrimeCertificate 229591 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv2551]) (by decide +kernel)
def pv229591 : PrimeValue := ⟨229591, pr229591⟩
private theorem pr229601 : PrimeCertificate 229601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv41]) (by decide +kernel)
def pv229601 : PrimeValue := ⟨229601, pr229601⟩
private theorem pr229613 : PrimeCertificate 229613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv419]) (by decide +kernel)
def pv229613 : PrimeValue := ⟨229613, pr229613⟩
private theorem pr229627 : PrimeCertificate 229627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12757]) (by decide +kernel)
def pv229627 : PrimeValue := ⟨229627, pr229627⟩
private theorem pr229631 : PrimeCertificate 229631 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv22963]) (by decide +kernel)
def pv229631 : PrimeValue := ⟨229631, pr229631⟩
private theorem pr229637 : PrimeCertificate 229637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv307]) (by decide +kernel)
def pv229637 : PrimeValue := ⟨229637, pr229637⟩
private theorem pr229703 : PrimeCertificate 229703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv53,pv197]) (by decide +kernel)
def pv229703 : PrimeValue := ⟨229703, pr229703⟩
private theorem pr229739 : PrimeCertificate 229739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv29,pv233]) (by decide +kernel)
def pv229739 : PrimeValue := ⟨229739, pr229739⟩
private theorem pr229753 : PrimeCertificate 229753 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv3191]) (by decide +kernel)
def pv229753 : PrimeValue := ⟨229753, pr229753⟩
private theorem pr229759 : PrimeCertificate 229759 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv149,pv257]) (by decide +kernel)
def pv229759 : PrimeValue := ⟨229759, pr229759⟩
private theorem pr229763 : PrimeCertificate 229763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv8837]) (by decide +kernel)
def pv229763 : PrimeValue := ⟨229763, pr229763⟩
private theorem pr229769 : PrimeCertificate 229769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv373]) (by decide +kernel)
def pv229769 : PrimeValue := ⟨229769, pr229769⟩
private theorem pr229777 : PrimeCertificate 229777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4787]) (by decide +kernel)
def pv229777 : PrimeValue := ⟨229777, pr229777⟩
private theorem pr229813 : PrimeCertificate 229813 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv1741]) (by decide +kernel)
def pv229813 : PrimeValue := ⟨229813, pr229813⟩
private theorem pr229819 : PrimeCertificate 229819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv38303]) (by decide +kernel)
def pv229819 : PrimeValue := ⟨229819, pr229819⟩
private theorem pr229837 : PrimeCertificate 229837 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv107,pv179]) (by decide +kernel)
def pv229837 : PrimeValue := ⟨229837, pr229837⟩
private theorem pr229841 : PrimeCertificate 229841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv17]) (by decide +kernel)
def pv229841 : PrimeValue := ⟨229841, pr229841⟩
private theorem pr229897 : PrimeCertificate 229897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv103]) (by decide +kernel)
def pv229897 : PrimeValue := ⟨229897, pr229897⟩
private theorem pr229903 : PrimeCertificate 229903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv38317]) (by decide +kernel)
def pv229903 : PrimeValue := ⟨229903, pr229903⟩
private theorem pr229939 : PrimeCertificate 229939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv2017]) (by decide +kernel)
def pv229939 : PrimeValue := ⟨229939, pr229939⟩
private theorem pr229961 : PrimeCertificate 229961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv5749]) (by decide +kernel)
def pv229961 : PrimeValue := ⟨229961, pr229961⟩
private theorem pr229979 : PrimeCertificate 229979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv16427]) (by decide +kernel)
def pv229979 : PrimeValue := ⟨229979, pr229979⟩
private theorem pr229981 : PrimeCertificate 229981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3833]) (by decide +kernel)
def pv229981 : PrimeValue := ⟨229981, pr229981⟩
private theorem pr230047 : PrimeCertificate 230047 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv1667]) (by decide +kernel)
def pv230047 : PrimeValue := ⟨230047, pr230047⟩
private theorem pr230059 : PrimeCertificate 230059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12781]) (by decide +kernel)
def pv230059 : PrimeValue := ⟨230059, pr230059⟩
private theorem pr230063 : PrimeCertificate 230063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv16433]) (by decide +kernel)
def pv230063 : PrimeValue := ⟨230063, pr230063⟩
private theorem pr230081 : PrimeCertificate 230081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv719]) (by decide +kernel)
def pv230081 : PrimeValue := ⟨230081, pr230081⟩
private theorem pr230089 : PrimeCertificate 230089 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv9587]) (by decide +kernel)
def pv230089 : PrimeValue := ⟨230089, pr230089⟩
private theorem pr230101 : PrimeCertificate 230101 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv13,pv59]) (by decide +kernel)
def pv230101 : PrimeValue := ⟨230101, pr230101⟩
private theorem pr230123 : PrimeCertificate 230123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv115061]) (by decide +kernel)
def pv230123 : PrimeValue := ⟨230123, pr230123⟩
private theorem pr230149 : PrimeCertificate 230149 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2131]) (by decide +kernel)
def pv230149 : PrimeValue := ⟨230149, pr230149⟩
private theorem pr230189 : PrimeCertificate 230189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8221]) (by decide +kernel)
def pv230189 : PrimeValue := ⟨230189, pr230189⟩
private theorem pr230203 : PrimeCertificate 230203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv230203 : PrimeValue := ⟨230203, pr230203⟩
private theorem pr230213 : PrimeCertificate 230213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv859]) (by decide +kernel)
def pv230213 : PrimeValue := ⟨230213, pr230213⟩
private theorem pr230221 : PrimeCertificate 230221 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv1279]) (by decide +kernel)
def pv230221 : PrimeValue := ⟨230221, pr230221⟩
private theorem pr230233 : PrimeCertificate 230233 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv53,pv181]) (by decide +kernel)
def pv230233 : PrimeValue := ⟨230233, pr230233⟩
private theorem pr230239 : PrimeCertificate 230239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv12791]) (by decide +kernel)
def pv230239 : PrimeValue := ⟨230239, pr230239⟩
private theorem pr230257 : PrimeCertificate 230257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv41]) (by decide +kernel)
def pv230257 : PrimeValue := ⟨230257, pr230257⟩
private theorem pr230281 : PrimeCertificate 230281 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv101]) (by decide +kernel)
def pv230281 : PrimeValue := ⟨230281, pr230281⟩
private theorem pr230291 : PrimeCertificate 230291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23029]) (by decide +kernel)
def pv230291 : PrimeValue := ⟨230291, pr230291⟩
private theorem pr230303 : PrimeCertificate 230303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv115151]) (by decide +kernel)
def pv230303 : PrimeValue := ⟨230303, pr230303⟩
private theorem pr230309 : PrimeCertificate 230309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv43,pv103]) (by decide +kernel)
def pv230309 : PrimeValue := ⟨230309, pr230309⟩
private theorem pr230353 : PrimeCertificate 230353 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv4799]) (by decide +kernel)
def pv230353 : PrimeValue := ⟨230353, pr230353⟩
private theorem pr230393 : PrimeCertificate 230393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv929]) (by decide +kernel)
def pv230393 : PrimeValue := ⟨230393, pr230393⟩
private theorem pr230431 : PrimeCertificate 230431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7681]) (by decide +kernel)
def pv230431 : PrimeValue := ⟨230431, pr230431⟩
private theorem pr230453 : PrimeCertificate 230453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv3389]) (by decide +kernel)
def pv230453 : PrimeValue := ⟨230453, pr230453⟩
private theorem pr230471 : PrimeCertificate 230471 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv19,pv1213]) (by decide +kernel)
def pv230471 : PrimeValue := ⟨230471, pr230471⟩
private theorem pr230479 : PrimeCertificate 230479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv107,pv359]) (by decide +kernel)
def pv230479 : PrimeValue := ⟨230479, pr230479⟩
private theorem pr230501 : PrimeCertificate 230501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv461]) (by decide +kernel)
def pv230501 : PrimeValue := ⟨230501, pr230501⟩
private theorem pr230507 : PrimeCertificate 230507 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv5011]) (by decide +kernel)
def pv230507 : PrimeValue := ⟨230507, pr230507⟩
private theorem pr230561 : PrimeCertificate 230561 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv131]) (by decide +kernel)
def pv230561 : PrimeValue := ⟨230561, pr230561⟩
private theorem pr230563 : PrimeCertificate 230563 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12809]) (by decide +kernel)
def pv230563 : PrimeValue := ⟨230563, pr230563⟩
private theorem pr230567 : PrimeCertificate 230567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv43,pv383]) (by decide +kernel)
def pv230567 : PrimeValue := ⟨230567, pr230567⟩
private theorem pr230597 : PrimeCertificate 230597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv57649]) (by decide +kernel)
def pv230597 : PrimeValue := ⟨230597, pr230597⟩
private theorem pr230611 : PrimeCertificate 230611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7687]) (by decide +kernel)
def pv230611 : PrimeValue := ⟨230611, pr230611⟩
private theorem pr230653 : PrimeCertificate 230653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv149]) (by decide +kernel)
def pv230653 : PrimeValue := ⟨230653, pr230653⟩
private theorem pr230663 : PrimeCertificate 230663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv115331]) (by decide +kernel)
def pv230663 : PrimeValue := ⟨230663, pr230663⟩
private theorem pr230683 : PrimeCertificate 230683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv38447]) (by decide +kernel)
def pv230683 : PrimeValue := ⟨230683, pr230683⟩
private theorem pr230693 : PrimeCertificate 230693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv107]) (by decide +kernel)
def pv230693 : PrimeValue := ⟨230693, pr230693⟩
private theorem pr230719 : PrimeCertificate 230719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv38453]) (by decide +kernel)
def pv230719 : PrimeValue := ⟨230719, pr230719⟩
private theorem pr230729 : PrimeCertificate 230729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv151,pv191]) (by decide +kernel)
def pv230729 : PrimeValue := ⟨230729, pr230729⟩
private theorem pr230743 : PrimeCertificate 230743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4273]) (by decide +kernel)
def pv230743 : PrimeValue := ⟨230743, pr230743⟩
private theorem pr230761 : PrimeCertificate 230761 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv641]) (by decide +kernel)
def pv230761 : PrimeValue := ⟨230761, pr230761⟩
private theorem pr230807 : PrimeCertificate 230807 :=
  certifyPrime (q := pv11) (ls := [pv2,pv37,pv3119]) (by decide +kernel)
def pv230807 : PrimeValue := ⟨230807, pr230807⟩
private theorem pr230819 : PrimeCertificate 230819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv16487]) (by decide +kernel)
def pv230819 : PrimeValue := ⟨230819, pr230819⟩
private theorem pr230827 : PrimeCertificate 230827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv31,pv73]) (by decide +kernel)
def pv230827 : PrimeValue := ⟨230827, pr230827⟩
private theorem pr230833 : PrimeCertificate 230833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv229]) (by decide +kernel)
def pv230833 : PrimeValue := ⟨230833, pr230833⟩
private theorem pr230863 : PrimeCertificate 230863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv109,pv353]) (by decide +kernel)
def pv230863 : PrimeValue := ⟨230863, pr230863⟩
private theorem pr230891 : PrimeCertificate 230891 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv2099]) (by decide +kernel)
def pv230891 : PrimeValue := ⟨230891, pr230891⟩
private theorem pr230939 : PrimeCertificate 230939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv115469]) (by decide +kernel)
def pv230939 : PrimeValue := ⟨230939, pr230939⟩
private theorem pr230941 : PrimeCertificate 230941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1283]) (by decide +kernel)
def pv230941 : PrimeValue := ⟨230941, pr230941⟩
private theorem pr230977 : PrimeCertificate 230977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv401]) (by decide +kernel)
def pv230977 : PrimeValue := ⟨230977, pr230977⟩
private theorem pr231017 : PrimeCertificate 231017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv431]) (by decide +kernel)
def pv231017 : PrimeValue := ⟨231017, pr231017⟩
private theorem pr231031 : PrimeCertificate 231031 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv151]) (by decide +kernel)
def pv231031 : PrimeValue := ⟨231031, pr231031⟩
private theorem pr231067 : PrimeCertificate 231067 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv389]) (by decide +kernel)
def pv231067 : PrimeValue := ⟨231067, pr231067⟩
private theorem pr231107 : PrimeCertificate 231107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv115553]) (by decide +kernel)
def pv231107 : PrimeValue := ⟨231107, pr231107⟩
private theorem pr231109 : PrimeCertificate 231109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19259]) (by decide +kernel)
def pv231109 : PrimeValue := ⟨231109, pr231109⟩
private theorem pr231131 : PrimeCertificate 231131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv797]) (by decide +kernel)
def pv231131 : PrimeValue := ⟨231131, pr231131⟩
private theorem pr231197 : PrimeCertificate 231197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv359]) (by decide +kernel)
def pv231197 : PrimeValue := ⟨231197, pr231197⟩
private theorem pr231223 : PrimeCertificate 231223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv89,pv433]) (by decide +kernel)
def pv231223 : PrimeValue := ⟨231223, pr231223⟩
private theorem pr231271 : PrimeCertificate 231271 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv13,pv593]) (by decide +kernel)
def pv231271 : PrimeValue := ⟨231271, pr231271⟩
private theorem pr231277 : PrimeCertificate 231277 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19273]) (by decide +kernel)
def pv231277 : PrimeValue := ⟨231277, pr231277⟩
private theorem pr231289 : PrimeCertificate 231289 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv23,pv419]) (by decide +kernel)
def pv231289 : PrimeValue := ⟨231289, pr231289⟩
private theorem pr231293 : PrimeCertificate 231293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv1091]) (by decide +kernel)
def pv231293 : PrimeValue := ⟨231293, pr231293⟩
private theorem pr231299 : PrimeCertificate 231299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv1061]) (by decide +kernel)
def pv231299 : PrimeValue := ⟨231299, pr231299⟩
private theorem pr231331 : PrimeCertificate 231331 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv11,pv701]) (by decide +kernel)
def pv231331 : PrimeValue := ⟨231331, pr231331⟩
private theorem pr231359 : PrimeCertificate 231359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv115679]) (by decide +kernel)
def pv231359 : PrimeValue := ⟨231359, pr231359⟩
private theorem pr231367 : PrimeCertificate 231367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv38561]) (by decide +kernel)
def pv231367 : PrimeValue := ⟨231367, pr231367⟩
private theorem pr231379 : PrimeCertificate 231379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv787]) (by decide +kernel)
def pv231379 : PrimeValue := ⟨231379, pr231379⟩
private theorem pr231409 : PrimeCertificate 231409 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1607]) (by decide +kernel)
def pv231409 : PrimeValue := ⟨231409, pr231409⟩
private theorem pr231419 : PrimeCertificate 231419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv67,pv157]) (by decide +kernel)
def pv231419 : PrimeValue := ⟨231419, pr231419⟩
private theorem pr231431 : PrimeCertificate 231431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv23143]) (by decide +kernel)
def pv231431 : PrimeValue := ⟨231431, pr231431⟩
private theorem pr231433 : PrimeCertificate 231433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9643]) (by decide +kernel)
def pv231433 : PrimeValue := ⟨231433, pr231433⟩
private theorem pr231443 : PrimeCertificate 231443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv1193]) (by decide +kernel)
def pv231443 : PrimeValue := ⟨231443, pr231443⟩
private theorem pr231463 : PrimeCertificate 231463 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv167]) (by decide +kernel)
def pv231463 : PrimeValue := ⟨231463, pr231463⟩
private theorem pr231479 : PrimeCertificate 231479 :=
  certifyPrime (q := pv17) (ls := [pv2,pv13,pv29,pv307]) (by decide +kernel)
def pv231479 : PrimeValue := ⟨231479, pr231479⟩
private theorem pr231481 : PrimeCertificate 231481 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv643]) (by decide +kernel)
def pv231481 : PrimeValue := ⟨231481, pr231481⟩
private theorem pr231493 : PrimeCertificate 231493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv191]) (by decide +kernel)
def pv231493 : PrimeValue := ⟨231493, pr231493⟩
private theorem pr231547 : PrimeCertificate 231547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv37,pv149]) (by decide +kernel)
def pv231547 : PrimeValue := ⟨231547, pr231547⟩
private theorem pr231551 : PrimeCertificate 231551 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv421]) (by decide +kernel)
def pv231551 : PrimeValue := ⟨231551, pr231551⟩
private theorem pr231589 : PrimeCertificate 231589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv919]) (by decide +kernel)
def pv231589 : PrimeValue := ⟨231589, pr231589⟩
private theorem pr231599 : PrimeCertificate 231599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv43,pv2693]) (by decide +kernel)
def pv231599 : PrimeValue := ⟨231599, pr231599⟩
private theorem pr231607 : PrimeCertificate 231607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4289]) (by decide +kernel)
def pv231607 : PrimeValue := ⟨231607, pr231607⟩
private theorem pr231611 : PrimeCertificate 231611 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv23,pv53]) (by decide +kernel)
def pv231611 : PrimeValue := ⟨231611, pr231611⟩
private theorem pr231643 : PrimeCertificate 231643 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv757]) (by decide +kernel)
def pv231643 : PrimeValue := ⟨231643, pr231643⟩
private theorem pr231701 : PrimeCertificate 231701 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv331]) (by decide +kernel)
def pv231701 : PrimeValue := ⟨231701, pr231701⟩
private theorem pr231719 : PrimeCertificate 231719 :=
  certifyPrime (q := pv11) (ls := [pv2,pv115859]) (by decide +kernel)
def pv231719 : PrimeValue := ⟨231719, pr231719⟩
private theorem pr231779 : PrimeCertificate 231779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv401]) (by decide +kernel)
def pv231779 : PrimeValue := ⟨231779, pr231779⟩
private theorem pr231799 : PrimeCertificate 231799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv5519]) (by decide +kernel)
def pv231799 : PrimeValue := ⟨231799, pr231799⟩
private theorem pr231809 : PrimeCertificate 231809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1811]) (by decide +kernel)
def pv231809 : PrimeValue := ⟨231809, pr231809⟩
private theorem pr231821 : PrimeCertificate 231821 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv67,pv173]) (by decide +kernel)
def pv231821 : PrimeValue := ⟨231821, pr231821⟩
private theorem pr231827 : PrimeCertificate 231827 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv29,pv571]) (by decide +kernel)
def pv231827 : PrimeValue := ⟨231827, pr231827⟩
private theorem pr231839 : PrimeCertificate 231839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv19,pv6101]) (by decide +kernel)
def pv231839 : PrimeValue := ⟨231839, pr231839⟩
private theorem pr231841 : PrimeCertificate 231841 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv23]) (by decide +kernel)
def pv231841 : PrimeValue := ⟨231841, pr231841⟩
private theorem pr231871 : PrimeCertificate 231871 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv59,pv131]) (by decide +kernel)
def pv231871 : PrimeValue := ⟨231871, pr231871⟩
private theorem pr231893 : PrimeCertificate 231893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv57973]) (by decide +kernel)
def pv231893 : PrimeValue := ⟨231893, pr231893⟩
private theorem pr231901 : PrimeCertificate 231901 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv773]) (by decide +kernel)
def pv231901 : PrimeValue := ⟨231901, pr231901⟩
private theorem pr231919 : PrimeCertificate 231919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv38653]) (by decide +kernel)
def pv231919 : PrimeValue := ⟨231919, pr231919⟩
private theorem pr231923 : PrimeCertificate 231923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv1901]) (by decide +kernel)
def pv231923 : PrimeValue := ⟨231923, pr231923⟩
private theorem pr231943 : PrimeCertificate 231943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv31,pv43]) (by decide +kernel)
def pv231943 : PrimeValue := ⟨231943, pr231943⟩
private theorem pr231947 : PrimeCertificate 231947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv811]) (by decide +kernel)
def pv231947 : PrimeValue := ⟨231947, pr231947⟩
private theorem pr231967 : PrimeCertificate 231967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv263]) (by decide +kernel)
def pv231967 : PrimeValue := ⟨231967, pr231967⟩
private theorem pr232013 : PrimeCertificate 232013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv5273]) (by decide +kernel)
def pv232013 : PrimeValue := ⟨232013, pr232013⟩
private theorem pr232051 : PrimeCertificate 232051 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv13,pv17]) (by decide +kernel)
def pv232051 : PrimeValue := ⟨232051, pr232051⟩
private theorem pr232079 : PrimeCertificate 232079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv137]) (by decide +kernel)
def pv232079 : PrimeValue := ⟨232079, pr232079⟩
private theorem pr232081 : PrimeCertificate 232081 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv967]) (by decide +kernel)
def pv232081 : PrimeValue := ⟨232081, pr232081⟩
private theorem pr232103 : PrimeCertificate 232103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv79,pv113]) (by decide +kernel)
def pv232103 : PrimeValue := ⟨232103, pr232103⟩
private theorem pr232109 : PrimeCertificate 232109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv58027]) (by decide +kernel)
def pv232109 : PrimeValue := ⟨232109, pr232109⟩
private theorem pr232117 : PrimeCertificate 232117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv29]) (by decide +kernel)
def pv232117 : PrimeValue := ⟨232117, pr232117⟩
private theorem pr232153 : PrimeCertificate 232153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv569]) (by decide +kernel)
def pv232153 : PrimeValue := ⟨232153, pr232153⟩
private theorem pr232171 : PrimeCertificate 232171 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv71,pv109]) (by decide +kernel)
def pv232171 : PrimeValue := ⟨232171, pr232171⟩
private theorem pr232187 : PrimeCertificate 232187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv6829]) (by decide +kernel)
def pv232187 : PrimeValue := ⟨232187, pr232187⟩
private theorem pr232207 : PrimeCertificate 232207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv229]) (by decide +kernel)
def pv232207 : PrimeValue := ⟨232207, pr232207⟩
private theorem pr232303 : PrimeCertificate 232303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv5531]) (by decide +kernel)
def pv232303 : PrimeValue := ⟨232303, pr232303⟩
private theorem pr232307 : PrimeCertificate 232307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv2833]) (by decide +kernel)
def pv232307 : PrimeValue := ⟨232307, pr232307⟩
private theorem pr232333 : PrimeCertificate 232333 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv1019]) (by decide +kernel)
def pv232333 : PrimeValue := ⟨232333, pr232333⟩
private theorem pr232357 : PrimeCertificate 232357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv67]) (by decide +kernel)
def pv232357 : PrimeValue := ⟨232357, pr232357⟩
private theorem pr232363 : PrimeCertificate 232363 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv331]) (by decide +kernel)
def pv232363 : PrimeValue := ⟨232363, pr232363⟩
private theorem pr232367 : PrimeCertificate 232367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv223,pv521]) (by decide +kernel)
def pv232367 : PrimeValue := ⟨232367, pr232367⟩
private theorem pr232391 : PrimeCertificate 232391 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv17,pv1367]) (by decide +kernel)
def pv232391 : PrimeValue := ⟨232391, pr232391⟩
private theorem pr232409 : PrimeCertificate 232409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv19,pv139]) (by decide +kernel)
def pv232409 : PrimeValue := ⟨232409, pr232409⟩
private theorem pr232417 : PrimeCertificate 232417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv269]) (by decide +kernel)
def pv232417 : PrimeValue := ⟨232417, pr232417⟩
private theorem pr232433 : PrimeCertificate 232433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv199]) (by decide +kernel)
def pv232433 : PrimeValue := ⟨232433, pr232433⟩
private theorem pr232439 : PrimeCertificate 232439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv23,pv31,pv163]) (by decide +kernel)
def pv232439 : PrimeValue := ⟨232439, pr232439⟩
private theorem pr232451 : PrimeCertificate 232451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4649]) (by decide +kernel)
def pv232451 : PrimeValue := ⟨232451, pr232451⟩
private theorem pr232499 : PrimeCertificate 232499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv16607]) (by decide +kernel)
def pv232499 : PrimeValue := ⟨232499, pr232499⟩
private theorem pr232513 : PrimeCertificate 232513 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv173]) (by decide +kernel)
def pv232513 : PrimeValue := ⟨232513, pr232513⟩
private theorem pr232549 : PrimeCertificate 232549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19379]) (by decide +kernel)
def pv232549 : PrimeValue := ⟨232549, pr232549⟩
private theorem pr232567 : PrimeCertificate 232567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv83,pv467]) (by decide +kernel)
def pv232567 : PrimeValue := ⟨232567, pr232567⟩
private theorem pr232571 : PrimeCertificate 232571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv1789]) (by decide +kernel)
def pv232571 : PrimeValue := ⟨232571, pr232571⟩
private theorem pr232591 : PrimeCertificate 232591 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7753]) (by decide +kernel)
def pv232591 : PrimeValue := ⟨232591, pr232591⟩
private theorem pr232597 : PrimeCertificate 232597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv71]) (by decide +kernel)
def pv232597 : PrimeValue := ⟨232597, pr232597⟩
private theorem pr232607 : PrimeCertificate 232607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv97,pv109]) (by decide +kernel)
def pv232607 : PrimeValue := ⟨232607, pr232607⟩
private theorem pr232621 : PrimeCertificate 232621 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv3877]) (by decide +kernel)
def pv232621 : PrimeValue := ⟨232621, pr232621⟩
private theorem pr232633 : PrimeCertificate 232633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv359]) (by decide +kernel)
def pv232633 : PrimeValue := ⟨232633, pr232633⟩
private theorem pr232643 : PrimeCertificate 232643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv293,pv397]) (by decide +kernel)
def pv232643 : PrimeValue := ⟨232643, pr232643⟩
private theorem pr232663 : PrimeCertificate 232663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv2281]) (by decide +kernel)
def pv232663 : PrimeValue := ⟨232663, pr232663⟩
private theorem pr232681 : PrimeCertificate 232681 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv277]) (by decide +kernel)
def pv232681 : PrimeValue := ⟨232681, pr232681⟩
private theorem pr232699 : PrimeCertificate 232699 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv38783]) (by decide +kernel)
def pv232699 : PrimeValue := ⟨232699, pr232699⟩
private theorem pr232709 : PrimeCertificate 232709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8311]) (by decide +kernel)
def pv232709 : PrimeValue := ⟨232709, pr232709⟩
private theorem pr232751 : PrimeCertificate 232751 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv19]) (by decide +kernel)
def pv232751 : PrimeValue := ⟨232751, pr232751⟩
private theorem pr232753 : PrimeCertificate 232753 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv373]) (by decide +kernel)
def pv232753 : PrimeValue := ⟨232753, pr232753⟩
private theorem pr232777 : PrimeCertificate 232777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv61]) (by decide +kernel)
def pv232777 : PrimeValue := ⟨232777, pr232777⟩
private theorem pr232811 : PrimeCertificate 232811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv751]) (by decide +kernel)
def pv232811 : PrimeValue := ⟨232811, pr232811⟩
private theorem pr232823 : PrimeCertificate 232823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv116411]) (by decide +kernel)
def pv232823 : PrimeValue := ⟨232823, pr232823⟩
private theorem pr232853 : PrimeCertificate 232853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2531]) (by decide +kernel)
def pv232853 : PrimeValue := ⟨232853, pr232853⟩
private theorem pr232861 : PrimeCertificate 232861 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv3881]) (by decide +kernel)
def pv232861 : PrimeValue := ⟨232861, pr232861⟩
private theorem pr232871 : PrimeCertificate 232871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv29,pv73]) (by decide +kernel)
def pv232871 : PrimeValue := ⟨232871, pr232871⟩
private theorem pr232907 : PrimeCertificate 232907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv1153]) (by decide +kernel)
def pv232907 : PrimeValue := ⟨232907, pr232907⟩
private theorem pr232919 : PrimeCertificate 232919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv127,pv131]) (by decide +kernel)
def pv232919 : PrimeValue := ⟨232919, pr232919⟩
private theorem pr232937 : PrimeCertificate 232937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv2647]) (by decide +kernel)
def pv232937 : PrimeValue := ⟨232937, pr232937⟩
private theorem pr232963 : PrimeCertificate 232963 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv947]) (by decide +kernel)
def pv232963 : PrimeValue := ⟨232963, pr232963⟩
private theorem pr232987 : PrimeCertificate 232987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv29,pv103]) (by decide +kernel)
def pv232987 : PrimeValue := ⟨232987, pr232987⟩
private theorem pr233021 : PrimeCertificate 233021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61,pv191]) (by decide +kernel)
def pv233021 : PrimeValue := ⟨233021, pr233021⟩
private theorem pr233069 : PrimeCertificate 233069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv5297]) (by decide +kernel)
def pv233069 : PrimeValue := ⟨233069, pr233069⟩
private theorem pr233071 : PrimeCertificate 233071 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv17,pv457]) (by decide +kernel)
def pv233071 : PrimeValue := ⟨233071, pr233071⟩
private theorem pr233083 : PrimeCertificate 233083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv563]) (by decide +kernel)
def pv233083 : PrimeValue := ⟨233083, pr233083⟩
private theorem pr233113 : PrimeCertificate 233113 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv883]) (by decide +kernel)
def pv233113 : PrimeValue := ⟨233113, pr233113⟩
private theorem pr233117 : PrimeCertificate 233117 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv4483]) (by decide +kernel)
def pv233117 : PrimeValue := ⟨233117, pr233117⟩
private theorem pr233141 : PrimeCertificate 233141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11657]) (by decide +kernel)
def pv233141 : PrimeValue := ⟨233141, pr233141⟩
private theorem pr233159 : PrimeCertificate 233159 :=
  certifyPrime (q := pv11) (ls := [pv2,pv116579]) (by decide +kernel)
def pv233159 : PrimeValue := ⟨233159, pr233159⟩
private theorem pr233161 : PrimeCertificate 233161 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv67]) (by decide +kernel)
def pv233161 : PrimeValue := ⟨233161, pr233161⟩
private theorem pr233173 : PrimeCertificate 233173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv127]) (by decide +kernel)
def pv233173 : PrimeValue := ⟨233173, pr233173⟩
private theorem pr233201 : PrimeCertificate 233201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv53]) (by decide +kernel)
def pv233201 : PrimeValue := ⟨233201, pr233201⟩
private theorem pr233231 : PrimeCertificate 233231 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv83,pv281]) (by decide +kernel)
def pv233231 : PrimeValue := ⟨233231, pr233231⟩
private theorem pr233239 : PrimeCertificate 233239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv38873]) (by decide +kernel)
def pv233239 : PrimeValue := ⟨233239, pr233239⟩
private theorem pr233251 : PrimeCertificate 233251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv311]) (by decide +kernel)
def pv233251 : PrimeValue := ⟨233251, pr233251⟩
private theorem pr233267 : PrimeCertificate 233267 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv23,pv461]) (by decide +kernel)
def pv233267 : PrimeValue := ⟨233267, pr233267⟩
private theorem pr233279 : PrimeCertificate 233279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv116639]) (by decide +kernel)
def pv233279 : PrimeValue := ⟨233279, pr233279⟩
private theorem pr233293 : PrimeCertificate 233293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19441]) (by decide +kernel)
def pv233293 : PrimeValue := ⟨233293, pr233293⟩
private theorem pr233323 : PrimeCertificate 233323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv1051]) (by decide +kernel)
def pv233323 : PrimeValue := ⟨233323, pr233323⟩
private theorem pr233327 : PrimeCertificate 233327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv116663]) (by decide +kernel)
def pv233327 : PrimeValue := ⟨233327, pr233327⟩
private theorem pr233347 : PrimeCertificate 233347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv38891]) (by decide +kernel)
def pv233347 : PrimeValue := ⟨233347, pr233347⟩
private theorem pr233353 : PrimeCertificate 233353 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv463]) (by decide +kernel)
def pv233353 : PrimeValue := ⟨233353, pr233353⟩
private theorem pr233357 : PrimeCertificate 233357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv257]) (by decide +kernel)
def pv233357 : PrimeValue := ⟨233357, pr233357⟩
private theorem pr233417 : PrimeCertificate 233417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv163,pv179]) (by decide +kernel)
def pv233417 : PrimeValue := ⟨233417, pr233417⟩
private theorem pr233419 : PrimeCertificate 233419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv38903]) (by decide +kernel)
def pv233419 : PrimeValue := ⟨233419, pr233419⟩
private theorem pr233477 : PrimeCertificate 233477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv58369]) (by decide +kernel)
def pv233477 : PrimeValue := ⟨233477, pr233477⟩
private theorem pr233489 : PrimeCertificate 233489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14593]) (by decide +kernel)
def pv233489 : PrimeValue := ⟨233489, pr233489⟩
private theorem pr233509 : PrimeCertificate 233509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv29,pv61]) (by decide +kernel)
def pv233509 : PrimeValue := ⟨233509, pr233509⟩
private theorem pr233549 : PrimeCertificate 233549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv439]) (by decide +kernel)
def pv233549 : PrimeValue := ⟨233549, pr233549⟩
private theorem pr233557 : PrimeCertificate 233557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19463]) (by decide +kernel)
def pv233557 : PrimeValue := ⟨233557, pr233557⟩
private theorem pr233591 : PrimeCertificate 233591 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv47,pv71]) (by decide +kernel)
def pv233591 : PrimeValue := ⟨233591, pr233591⟩
private theorem pr233617 : PrimeCertificate 233617 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv31,pv157]) (by decide +kernel)
def pv233617 : PrimeValue := ⟨233617, pr233617⟩
private theorem pr233641 : PrimeCertificate 233641 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv11,pv59]) (by decide +kernel)
def pv233641 : PrimeValue := ⟨233641, pr233641⟩
private theorem pr233663 : PrimeCertificate 233663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv19,pv43]) (by decide +kernel)
def pv233663 : PrimeValue := ⟨233663, pr233663⟩
private theorem pr233669 : PrimeCertificate 233669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv58417]) (by decide +kernel)
def pv233669 : PrimeValue := ⟨233669, pr233669⟩
private theorem pr233683 : PrimeCertificate 233683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv29,pv79]) (by decide +kernel)
def pv233683 : PrimeValue := ⟨233683, pr233683⟩
private theorem pr233687 : PrimeCertificate 233687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv331,pv353]) (by decide +kernel)
def pv233687 : PrimeValue := ⟨233687, pr233687⟩
private theorem pr233693 : PrimeCertificate 233693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv1579]) (by decide +kernel)
def pv233693 : PrimeValue := ⟨233693, pr233693⟩
private theorem pr233713 : PrimeCertificate 233713 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv541]) (by decide +kernel)
def pv233713 : PrimeValue := ⟨233713, pr233713⟩
private theorem pr233743 : PrimeCertificate 233743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv163,pv239]) (by decide +kernel)
def pv233743 : PrimeValue := ⟨233743, pr233743⟩
private theorem pr233747 : PrimeCertificate 233747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv1601]) (by decide +kernel)
def pv233747 : PrimeValue := ⟨233747, pr233747⟩
private theorem pr233777 : PrimeCertificate 233777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv769]) (by decide +kernel)
def pv233777 : PrimeValue := ⟨233777, pr233777⟩
private theorem pr233861 : PrimeCertificate 233861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1063]) (by decide +kernel)
def pv233861 : PrimeValue := ⟨233861, pr233861⟩
private theorem pr233881 : PrimeCertificate 233881 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv1949]) (by decide +kernel)
def pv233881 : PrimeValue := ⟨233881, pr233881⟩
private theorem pr233939 : PrimeCertificate 233939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv116969]) (by decide +kernel)
def pv233939 : PrimeValue := ⟨233939, pr233939⟩
private theorem pr233969 : PrimeCertificate 233969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2089]) (by decide +kernel)
def pv233969 : PrimeValue := ⟨233969, pr233969⟩
private theorem pr233993 : PrimeCertificate 233993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv2659]) (by decide +kernel)
def pv233993 : PrimeValue := ⟨233993, pr233993⟩
private theorem pr234007 : PrimeCertificate 234007 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv43,pv907]) (by decide +kernel)
def pv234007 : PrimeValue := ⟨234007, pr234007⟩
private theorem pr234029 : PrimeCertificate 234029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv1427]) (by decide +kernel)
def pv234029 : PrimeValue := ⟨234029, pr234029⟩
private theorem pr234043 : PrimeCertificate 234043 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv2053]) (by decide +kernel)
def pv234043 : PrimeValue := ⟨234043, pr234043⟩
private theorem pr234083 : PrimeCertificate 234083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv117041]) (by decide +kernel)
def pv234083 : PrimeValue := ⟨234083, pr234083⟩
private theorem pr234089 : PrimeCertificate 234089 :=
  certifyPrime (q := pv13) (ls := [pv2,pv29,pv1009]) (by decide +kernel)
def pv234089 : PrimeValue := ⟨234089, pr234089⟩
private theorem pr234103 : PrimeCertificate 234103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv3547]) (by decide +kernel)
def pv234103 : PrimeValue := ⟨234103, pr234103⟩
private theorem pr234121 : PrimeCertificate 234121 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv1951]) (by decide +kernel)
def pv234121 : PrimeValue := ⟨234121, pr234121⟩
private theorem pr234131 : PrimeCertificate 234131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv1801]) (by decide +kernel)
def pv234131 : PrimeValue := ⟨234131, pr234131⟩
private theorem pr234139 : PrimeCertificate 234139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv39023]) (by decide +kernel)
def pv234139 : PrimeValue := ⟨234139, pr234139⟩
private theorem pr234149 : PrimeCertificate 234149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv58537]) (by decide +kernel)
def pv234149 : PrimeValue := ⟨234149, pr234149⟩
private theorem pr234161 : PrimeCertificate 234161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2927]) (by decide +kernel)
def pv234161 : PrimeValue := ⟨234161, pr234161⟩
private theorem pr234167 : PrimeCertificate 234167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv191,pv613]) (by decide +kernel)
def pv234167 : PrimeValue := ⟨234167, pr234167⟩
private theorem pr234181 : PrimeCertificate 234181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1301]) (by decide +kernel)
def pv234181 : PrimeValue := ⟨234181, pr234181⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
