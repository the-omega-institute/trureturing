/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table009
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table009.pv19913
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table004
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table005

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr19913 : PrimeCertificate 19913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv131]) (by decide +kernel)
def pv19913 : PrimeValue := ⟨19913, pr19913⟩
private theorem pr19919 : PrimeCertificate 19919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv23,pv433]) (by decide +kernel)
def pv19919 : PrimeValue := ⟨19919, pr19919⟩
private theorem pr19927 : PrimeCertificate 19927 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv19927 : PrimeValue := ⟨19927, pr19927⟩
private theorem pr19937 : PrimeCertificate 19937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv89]) (by decide +kernel)
def pv19937 : PrimeValue := ⟨19937, pr19937⟩
private theorem pr19949 : PrimeCertificate 19949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv4987]) (by decide +kernel)
def pv19949 : PrimeValue := ⟨19949, pr19949⟩
private theorem pr19961 : PrimeCertificate 19961 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv499]) (by decide +kernel)
def pv19961 : PrimeValue := ⟨19961, pr19961⟩
private theorem pr19963 : PrimeCertificate 19963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1109]) (by decide +kernel)
def pv19963 : PrimeValue := ⟨19963, pr19963⟩
private theorem pr19973 : PrimeCertificate 19973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv4993]) (by decide +kernel)
def pv19973 : PrimeValue := ⟨19973, pr19973⟩
private theorem pr19979 : PrimeCertificate 19979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1427]) (by decide +kernel)
def pv19979 : PrimeValue := ⟨19979, pr19979⟩
private theorem pr19991 : PrimeCertificate 19991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv1999]) (by decide +kernel)
def pv19991 : PrimeValue := ⟨19991, pr19991⟩
private theorem pr19993 : PrimeCertificate 19993 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv19993 : PrimeValue := ⟨19993, pr19993⟩
private theorem pr19997 : PrimeCertificate 19997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv4999]) (by decide +kernel)
def pv19997 : PrimeValue := ⟨19997, pr19997⟩
private theorem pr20011 : PrimeCertificate 20011 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv23,pv29]) (by decide +kernel)
def pv20011 : PrimeValue := ⟨20011, pr20011⟩
private theorem pr20021 : PrimeCertificate 20021 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv13]) (by decide +kernel)
def pv20021 : PrimeValue := ⟨20021, pr20021⟩
private theorem pr20023 : PrimeCertificate 20023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv71]) (by decide +kernel)
def pv20023 : PrimeValue := ⟨20023, pr20023⟩
private theorem pr20029 : PrimeCertificate 20029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1669]) (by decide +kernel)
def pv20029 : PrimeValue := ⟨20029, pr20029⟩
private theorem pr20047 : PrimeCertificate 20047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv257]) (by decide +kernel)
def pv20047 : PrimeValue := ⟨20047, pr20047⟩
private theorem pr20051 : PrimeCertificate 20051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv401]) (by decide +kernel)
def pv20051 : PrimeValue := ⟨20051, pr20051⟩
private theorem pr20063 : PrimeCertificate 20063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv1433]) (by decide +kernel)
def pv20063 : PrimeValue := ⟨20063, pr20063⟩
private theorem pr20071 : PrimeCertificate 20071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv223]) (by decide +kernel)
def pv20071 : PrimeValue := ⟨20071, pr20071⟩
private theorem pr20089 : PrimeCertificate 20089 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv20089 : PrimeValue := ⟨20089, pr20089⟩
private theorem pr20101 : PrimeCertificate 20101 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv67]) (by decide +kernel)
def pv20101 : PrimeValue := ⟨20101, pr20101⟩
private theorem pr20107 : PrimeCertificate 20107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1117]) (by decide +kernel)
def pv20107 : PrimeValue := ⟨20107, pr20107⟩
private theorem pr20113 : PrimeCertificate 20113 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv419]) (by decide +kernel)
def pv20113 : PrimeValue := ⟨20113, pr20113⟩
private theorem pr20117 : PrimeCertificate 20117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv107]) (by decide +kernel)
def pv20117 : PrimeValue := ⟨20117, pr20117⟩
private theorem pr20123 : PrimeCertificate 20123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10061]) (by decide +kernel)
def pv20123 : PrimeValue := ⟨20123, pr20123⟩
private theorem pr20129 : PrimeCertificate 20129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv37]) (by decide +kernel)
def pv20129 : PrimeValue := ⟨20129, pr20129⟩
private theorem pr20143 : PrimeCertificate 20143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv373]) (by decide +kernel)
def pv20143 : PrimeValue := ⟨20143, pr20143⟩
private theorem pr20147 : PrimeCertificate 20147 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv1439]) (by decide +kernel)
def pv20147 : PrimeValue := ⟨20147, pr20147⟩
private theorem pr20149 : PrimeCertificate 20149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv73]) (by decide +kernel)
def pv20149 : PrimeValue := ⟨20149, pr20149⟩
private theorem pr20161 : PrimeCertificate 20161 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv20161 : PrimeValue := ⟨20161, pr20161⟩
private theorem pr20173 : PrimeCertificate 20173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv20173 : PrimeValue := ⟨20173, pr20173⟩
private theorem pr20177 : PrimeCertificate 20177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv97]) (by decide +kernel)
def pv20177 : PrimeValue := ⟨20177, pr20177⟩
private theorem pr20183 : PrimeCertificate 20183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv10091]) (by decide +kernel)
def pv20183 : PrimeValue := ⟨20183, pr20183⟩
private theorem pr20201 : PrimeCertificate 20201 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv101]) (by decide +kernel)
def pv20201 : PrimeValue := ⟨20201, pr20201⟩
private theorem pr20219 : PrimeCertificate 20219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv919]) (by decide +kernel)
def pv20219 : PrimeValue := ⟨20219, pr20219⟩
private theorem pr20231 : PrimeCertificate 20231 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv7,pv17]) (by decide +kernel)
def pv20231 : PrimeValue := ⟨20231, pr20231⟩
private theorem pr20233 : PrimeCertificate 20233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv281]) (by decide +kernel)
def pv20233 : PrimeValue := ⟨20233, pr20233⟩
private theorem pr20249 : PrimeCertificate 20249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2531]) (by decide +kernel)
def pv20249 : PrimeValue := ⟨20249, pr20249⟩
private theorem pr20261 : PrimeCertificate 20261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1013]) (by decide +kernel)
def pv20261 : PrimeValue := ⟨20261, pr20261⟩
private theorem pr20269 : PrimeCertificate 20269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv563]) (by decide +kernel)
def pv20269 : PrimeValue := ⟨20269, pr20269⟩
private theorem pr20287 : PrimeCertificate 20287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv20287 : PrimeValue := ⟨20287, pr20287⟩
private theorem pr20297 : PrimeCertificate 20297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv59]) (by decide +kernel)
def pv20297 : PrimeValue := ⟨20297, pr20297⟩
private theorem pr20323 : PrimeCertificate 20323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1129]) (by decide +kernel)
def pv20323 : PrimeValue := ⟨20323, pr20323⟩
private theorem pr20327 : PrimeCertificate 20327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv10163]) (by decide +kernel)
def pv20327 : PrimeValue := ⟨20327, pr20327⟩
private theorem pr20333 : PrimeCertificate 20333 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv17,pv23]) (by decide +kernel)
def pv20333 : PrimeValue := ⟨20333, pr20333⟩
private theorem pr20341 : PrimeCertificate 20341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv113]) (by decide +kernel)
def pv20341 : PrimeValue := ⟨20341, pr20341⟩
private theorem pr20347 : PrimeCertificate 20347 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3391]) (by decide +kernel)
def pv20347 : PrimeValue := ⟨20347, pr20347⟩
private theorem pr20353 : PrimeCertificate 20353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53]) (by decide +kernel)
def pv20353 : PrimeValue := ⟨20353, pr20353⟩
private theorem pr20357 : PrimeCertificate 20357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv727]) (by decide +kernel)
def pv20357 : PrimeValue := ⟨20357, pr20357⟩
private theorem pr20359 : PrimeCertificate 20359 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv29]) (by decide +kernel)
def pv20359 : PrimeValue := ⟨20359, pr20359⟩
private theorem pr20369 : PrimeCertificate 20369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv67]) (by decide +kernel)
def pv20369 : PrimeValue := ⟨20369, pr20369⟩
private theorem pr20389 : PrimeCertificate 20389 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1699]) (by decide +kernel)
def pv20389 : PrimeValue := ⟨20389, pr20389⟩
private theorem pr20393 : PrimeCertificate 20393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2549]) (by decide +kernel)
def pv20393 : PrimeValue := ⟨20393, pr20393⟩
private theorem pr20399 : PrimeCertificate 20399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv31,pv47]) (by decide +kernel)
def pv20399 : PrimeValue := ⟨20399, pr20399⟩
private theorem pr20407 : PrimeCertificate 20407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv179]) (by decide +kernel)
def pv20407 : PrimeValue := ⟨20407, pr20407⟩
private theorem pr20411 : PrimeCertificate 20411 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv157]) (by decide +kernel)
def pv20411 : PrimeValue := ⟨20411, pr20411⟩
private theorem pr20431 : PrimeCertificate 20431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv227]) (by decide +kernel)
def pv20431 : PrimeValue := ⟨20431, pr20431⟩
private theorem pr20441 : PrimeCertificate 20441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv73]) (by decide +kernel)
def pv20441 : PrimeValue := ⟨20441, pr20441⟩
private theorem pr20443 : PrimeCertificate 20443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3407]) (by decide +kernel)
def pv20443 : PrimeValue := ⟨20443, pr20443⟩
private theorem pr20477 : PrimeCertificate 20477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5119]) (by decide +kernel)
def pv20477 : PrimeValue := ⟨20477, pr20477⟩
private theorem pr20479 : PrimeCertificate 20479 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3413]) (by decide +kernel)
def pv20479 : PrimeValue := ⟨20479, pr20479⟩
private theorem pr20483 : PrimeCertificate 20483 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv19]) (by decide +kernel)
def pv20483 : PrimeValue := ⟨20483, pr20483⟩
private theorem pr20507 : PrimeCertificate 20507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10253]) (by decide +kernel)
def pv20507 : PrimeValue := ⟨20507, pr20507⟩
private theorem pr20509 : PrimeCertificate 20509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1709]) (by decide +kernel)
def pv20509 : PrimeValue := ⟨20509, pr20509⟩
private theorem pr20521 : PrimeCertificate 20521 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv20521 : PrimeValue := ⟨20521, pr20521⟩
private theorem pr20533 : PrimeCertificate 20533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv59]) (by decide +kernel)
def pv20533 : PrimeValue := ⟨20533, pr20533⟩
private theorem pr20543 : PrimeCertificate 20543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv10271]) (by decide +kernel)
def pv20543 : PrimeValue := ⟨20543, pr20543⟩
private theorem pr20549 : PrimeCertificate 20549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv467]) (by decide +kernel)
def pv20549 : PrimeValue := ⟨20549, pr20549⟩
private theorem pr20551 : PrimeCertificate 20551 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv137]) (by decide +kernel)
def pv20551 : PrimeValue := ⟨20551, pr20551⟩
private theorem pr20563 : PrimeCertificate 20563 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv149]) (by decide +kernel)
def pv20563 : PrimeValue := ⟨20563, pr20563⟩
private theorem pr20593 : PrimeCertificate 20593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv20593 : PrimeValue := ⟨20593, pr20593⟩
private theorem pr20599 : PrimeCertificate 20599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3433]) (by decide +kernel)
def pv20599 : PrimeValue := ⟨20599, pr20599⟩
private theorem pr20611 : PrimeCertificate 20611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv229]) (by decide +kernel)
def pv20611 : PrimeValue := ⟨20611, pr20611⟩
private theorem pr20627 : PrimeCertificate 20627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10313]) (by decide +kernel)
def pv20627 : PrimeValue := ⟨20627, pr20627⟩
private theorem pr20639 : PrimeCertificate 20639 :=
  certifyPrime (q := pv11) (ls := [pv2,pv17,pv607]) (by decide +kernel)
def pv20639 : PrimeValue := ⟨20639, pr20639⟩
private theorem pr20641 : PrimeCertificate 20641 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv20641 : PrimeValue := ⟨20641, pr20641⟩
private theorem pr20663 : PrimeCertificate 20663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv10331]) (by decide +kernel)
def pv20663 : PrimeValue := ⟨20663, pr20663⟩
private theorem pr20681 : PrimeCertificate 20681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv47]) (by decide +kernel)
def pv20681 : PrimeValue := ⟨20681, pr20681⟩
private theorem pr20693 : PrimeCertificate 20693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv739]) (by decide +kernel)
def pv20693 : PrimeValue := ⟨20693, pr20693⟩
private theorem pr20707 : PrimeCertificate 20707 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv29]) (by decide +kernel)
def pv20707 : PrimeValue := ⟨20707, pr20707⟩
private theorem pr20717 : PrimeCertificate 20717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5179]) (by decide +kernel)
def pv20717 : PrimeValue := ⟨20717, pr20717⟩
private theorem pr20719 : PrimeCertificate 20719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1151]) (by decide +kernel)
def pv20719 : PrimeValue := ⟨20719, pr20719⟩
private theorem pr20731 : PrimeCertificate 20731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv691]) (by decide +kernel)
def pv20731 : PrimeValue := ⟨20731, pr20731⟩
private theorem pr20743 : PrimeCertificate 20743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3457]) (by decide +kernel)
def pv20743 : PrimeValue := ⟨20743, pr20743⟩
private theorem pr20747 : PrimeCertificate 20747 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv23,pv41]) (by decide +kernel)
def pv20747 : PrimeValue := ⟨20747, pr20747⟩
private theorem pr20749 : PrimeCertificate 20749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv19]) (by decide +kernel)
def pv20749 : PrimeValue := ⟨20749, pr20749⟩
private theorem pr20753 : PrimeCertificate 20753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1297]) (by decide +kernel)
def pv20753 : PrimeValue := ⟨20753, pr20753⟩
private theorem pr20759 : PrimeCertificate 20759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv97,pv107]) (by decide +kernel)
def pv20759 : PrimeValue := ⟨20759, pr20759⟩
private theorem pr20771 : PrimeCertificate 20771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv67]) (by decide +kernel)
def pv20771 : PrimeValue := ⟨20771, pr20771⟩
private theorem pr20773 : PrimeCertificate 20773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv577]) (by decide +kernel)
def pv20773 : PrimeValue := ⟨20773, pr20773⟩
private theorem pr20789 : PrimeCertificate 20789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5197]) (by decide +kernel)
def pv20789 : PrimeValue := ⟨20789, pr20789⟩
private theorem pr20807 : PrimeCertificate 20807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv101,pv103]) (by decide +kernel)
def pv20807 : PrimeValue := ⟨20807, pr20807⟩
private theorem pr20809 : PrimeCertificate 20809 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv20809 : PrimeValue := ⟨20809, pr20809⟩
private theorem pr20849 : PrimeCertificate 20849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1303]) (by decide +kernel)
def pv20849 : PrimeValue := ⟨20849, pr20849⟩
private theorem pr20857 : PrimeCertificate 20857 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv79]) (by decide +kernel)
def pv20857 : PrimeValue := ⟨20857, pr20857⟩
private theorem pr20873 : PrimeCertificate 20873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2609]) (by decide +kernel)
def pv20873 : PrimeValue := ⟨20873, pr20873⟩
private theorem pr20879 : PrimeCertificate 20879 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv13,pv73]) (by decide +kernel)
def pv20879 : PrimeValue := ⟨20879, pr20879⟩
private theorem pr20887 : PrimeCertificate 20887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv20887 : PrimeValue := ⟨20887, pr20887⟩
private theorem pr20897 : PrimeCertificate 20897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv653]) (by decide +kernel)
def pv20897 : PrimeValue := ⟨20897, pr20897⟩
private theorem pr20899 : PrimeCertificate 20899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv20899 : PrimeValue := ⟨20899, pr20899⟩
private theorem pr20903 : PrimeCertificate 20903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv1493]) (by decide +kernel)
def pv20903 : PrimeValue := ⟨20903, pr20903⟩
private theorem pr20921 : PrimeCertificate 20921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv523]) (by decide +kernel)
def pv20921 : PrimeValue := ⟨20921, pr20921⟩
private theorem pr20929 : PrimeCertificate 20929 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv109]) (by decide +kernel)
def pv20929 : PrimeValue := ⟨20929, pr20929⟩
private theorem pr20939 : PrimeCertificate 20939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv29]) (by decide +kernel)
def pv20939 : PrimeValue := ⟨20939, pr20939⟩
private theorem pr20947 : PrimeCertificate 20947 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3491]) (by decide +kernel)
def pv20947 : PrimeValue := ⟨20947, pr20947⟩
private theorem pr20959 : PrimeCertificate 20959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv499]) (by decide +kernel)
def pv20959 : PrimeValue := ⟨20959, pr20959⟩
private theorem pr20963 : PrimeCertificate 20963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv223]) (by decide +kernel)
def pv20963 : PrimeValue := ⟨20963, pr20963⟩
private theorem pr20981 : PrimeCertificate 20981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1049]) (by decide +kernel)
def pv20981 : PrimeValue := ⟨20981, pr20981⟩
private theorem pr20983 : PrimeCertificate 20983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv269]) (by decide +kernel)
def pv20983 : PrimeValue := ⟨20983, pr20983⟩
private theorem pr21001 : PrimeCertificate 21001 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv21001 : PrimeValue := ⟨21001, pr21001⟩
private theorem pr21011 : PrimeCertificate 21011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv191]) (by decide +kernel)
def pv21011 : PrimeValue := ⟨21011, pr21011⟩
private theorem pr21013 : PrimeCertificate 21013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv103]) (by decide +kernel)
def pv21013 : PrimeValue := ⟨21013, pr21013⟩
private theorem pr21017 : PrimeCertificate 21017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv71]) (by decide +kernel)
def pv21017 : PrimeValue := ⟨21017, pr21017⟩
private theorem pr21019 : PrimeCertificate 21019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv113]) (by decide +kernel)
def pv21019 : PrimeValue := ⟨21019, pr21019⟩
private theorem pr21023 : PrimeCertificate 21023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv457]) (by decide +kernel)
def pv21023 : PrimeValue := ⟨21023, pr21023⟩
private theorem pr21031 : PrimeCertificate 21031 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv701]) (by decide +kernel)
def pv21031 : PrimeValue := ⟨21031, pr21031⟩
private theorem pr21059 : PrimeCertificate 21059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10529]) (by decide +kernel)
def pv21059 : PrimeValue := ⟨21059, pr21059⟩
private theorem pr21061 : PrimeCertificate 21061 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv21061 : PrimeValue := ⟨21061, pr21061⟩
private theorem pr21067 : PrimeCertificate 21067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3511]) (by decide +kernel)
def pv21067 : PrimeValue := ⟨21067, pr21067⟩
private theorem pr21089 : PrimeCertificate 21089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv659]) (by decide +kernel)
def pv21089 : PrimeValue := ⟨21089, pr21089⟩
private theorem pr21101 : PrimeCertificate 21101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv211]) (by decide +kernel)
def pv21101 : PrimeValue := ⟨21101, pr21101⟩
private theorem pr21107 : PrimeCertificate 21107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv173]) (by decide +kernel)
def pv21107 : PrimeValue := ⟨21107, pr21107⟩
private theorem pr21121 : PrimeCertificate 21121 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv21121 : PrimeValue := ⟨21121, pr21121⟩
private theorem pr21139 : PrimeCertificate 21139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv271]) (by decide +kernel)
def pv21139 : PrimeValue := ⟨21139, pr21139⟩
private theorem pr21143 : PrimeCertificate 21143 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv31]) (by decide +kernel)
def pv21143 : PrimeValue := ⟨21143, pr21143⟩
private theorem pr21149 : PrimeCertificate 21149 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv311]) (by decide +kernel)
def pv21149 : PrimeValue := ⟨21149, pr21149⟩
private theorem pr21157 : PrimeCertificate 21157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv43]) (by decide +kernel)
def pv21157 : PrimeValue := ⟨21157, pr21157⟩
private theorem pr21163 : PrimeCertificate 21163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3527]) (by decide +kernel)
def pv21163 : PrimeValue := ⟨21163, pr21163⟩
private theorem pr21169 : PrimeCertificate 21169 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv21169 : PrimeValue := ⟨21169, pr21169⟩
private theorem pr21179 : PrimeCertificate 21179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10589]) (by decide +kernel)
def pv21179 : PrimeValue := ⟨21179, pr21179⟩
private theorem pr21187 : PrimeCertificate 21187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv107]) (by decide +kernel)
def pv21187 : PrimeValue := ⟨21187, pr21187⟩
private theorem pr21191 : PrimeCertificate 21191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv163]) (by decide +kernel)
def pv21191 : PrimeValue := ⟨21191, pr21191⟩
private theorem pr21193 : PrimeCertificate 21193 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv883]) (by decide +kernel)
def pv21193 : PrimeValue := ⟨21193, pr21193⟩
private theorem pr21211 : PrimeCertificate 21211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv101]) (by decide +kernel)
def pv21211 : PrimeValue := ⟨21211, pr21211⟩
private theorem pr21221 : PrimeCertificate 21221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1061]) (by decide +kernel)
def pv21221 : PrimeValue := ⟨21221, pr21221⟩
private theorem pr21227 : PrimeCertificate 21227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10613]) (by decide +kernel)
def pv21227 : PrimeValue := ⟨21227, pr21227⟩
private theorem pr21247 : PrimeCertificate 21247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3541]) (by decide +kernel)
def pv21247 : PrimeValue := ⟨21247, pr21247⟩
private theorem pr21269 : PrimeCertificate 21269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv409]) (by decide +kernel)
def pv21269 : PrimeValue := ⟨21269, pr21269⟩
private theorem pr21277 : PrimeCertificate 21277 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv197]) (by decide +kernel)
def pv21277 : PrimeValue := ⟨21277, pr21277⟩
private theorem pr21283 : PrimeCertificate 21283 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv3547]) (by decide +kernel)
def pv21283 : PrimeValue := ⟨21283, pr21283⟩
private theorem pr21313 : PrimeCertificate 21313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv21313 : PrimeValue := ⟨21313, pr21313⟩
private theorem pr21317 : PrimeCertificate 21317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73]) (by decide +kernel)
def pv21317 : PrimeValue := ⟨21317, pr21317⟩
private theorem pr21319 : PrimeCertificate 21319 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv17,pv19]) (by decide +kernel)
def pv21319 : PrimeValue := ⟨21319, pr21319⟩
private theorem pr21323 : PrimeCertificate 21323 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv1523]) (by decide +kernel)
def pv21323 : PrimeValue := ⟨21323, pr21323⟩
private theorem pr21341 : PrimeCertificate 21341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv97]) (by decide +kernel)
def pv21341 : PrimeValue := ⟨21341, pr21341⟩
private theorem pr21347 : PrimeCertificate 21347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv821]) (by decide +kernel)
def pv21347 : PrimeValue := ⟨21347, pr21347⟩
private theorem pr21377 : PrimeCertificate 21377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv167]) (by decide +kernel)
def pv21377 : PrimeValue := ⟨21377, pr21377⟩
private theorem pr21379 : PrimeCertificate 21379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv509]) (by decide +kernel)
def pv21379 : PrimeValue := ⟨21379, pr21379⟩
private theorem pr21383 : PrimeCertificate 21383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv10691]) (by decide +kernel)
def pv21383 : PrimeValue := ⟨21383, pr21383⟩
private theorem pr21391 : PrimeCertificate 21391 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv23,pv31]) (by decide +kernel)
def pv21391 : PrimeValue := ⟨21391, pr21391⟩
private theorem pr21397 : PrimeCertificate 21397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1783]) (by decide +kernel)
def pv21397 : PrimeValue := ⟨21397, pr21397⟩
private theorem pr21401 : PrimeCertificate 21401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv107]) (by decide +kernel)
def pv21401 : PrimeValue := ⟨21401, pr21401⟩
private theorem pr21407 : PrimeCertificate 21407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv139]) (by decide +kernel)
def pv21407 : PrimeValue := ⟨21407, pr21407⟩
private theorem pr21419 : PrimeCertificate 21419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10709]) (by decide +kernel)
def pv21419 : PrimeValue := ⟨21419, pr21419⟩
private theorem pr21433 : PrimeCertificate 21433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv47]) (by decide +kernel)
def pv21433 : PrimeValue := ⟨21433, pr21433⟩
private theorem pr21467 : PrimeCertificate 21467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10733]) (by decide +kernel)
def pv21467 : PrimeValue := ⟨21467, pr21467⟩
private theorem pr21481 : PrimeCertificate 21481 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv179]) (by decide +kernel)
def pv21481 : PrimeValue := ⟨21481, pr21481⟩
private theorem pr21487 : PrimeCertificate 21487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3581]) (by decide +kernel)
def pv21487 : PrimeValue := ⟨21487, pr21487⟩
private theorem pr21491 : PrimeCertificate 21491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv307]) (by decide +kernel)
def pv21491 : PrimeValue := ⟨21491, pr21491⟩
private theorem pr21493 : PrimeCertificate 21493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv199]) (by decide +kernel)
def pv21493 : PrimeValue := ⟨21493, pr21493⟩
private theorem pr21499 : PrimeCertificate 21499 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3583]) (by decide +kernel)
def pv21499 : PrimeValue := ⟨21499, pr21499⟩
private theorem pr21503 : PrimeCertificate 21503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv827]) (by decide +kernel)
def pv21503 : PrimeValue := ⟨21503, pr21503⟩
private theorem pr21517 : PrimeCertificate 21517 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv163]) (by decide +kernel)
def pv21517 : PrimeValue := ⟨21517, pr21517⟩
private theorem pr21521 : PrimeCertificate 21521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv269]) (by decide +kernel)
def pv21521 : PrimeValue := ⟨21521, pr21521⟩
private theorem pr21523 : PrimeCertificate 21523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv211]) (by decide +kernel)
def pv21523 : PrimeValue := ⟨21523, pr21523⟩
private theorem pr21529 : PrimeCertificate 21529 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv23]) (by decide +kernel)
def pv21529 : PrimeValue := ⟨21529, pr21529⟩
private theorem pr21557 : PrimeCertificate 21557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv317]) (by decide +kernel)
def pv21557 : PrimeValue := ⟨21557, pr21557⟩
private theorem pr21559 : PrimeCertificate 21559 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv3593]) (by decide +kernel)
def pv21559 : PrimeValue := ⟨21559, pr21559⟩
private theorem pr21563 : PrimeCertificate 21563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10781]) (by decide +kernel)
def pv21563 : PrimeValue := ⟨21563, pr21563⟩
private theorem pr21569 : PrimeCertificate 21569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv337]) (by decide +kernel)
def pv21569 : PrimeValue := ⟨21569, pr21569⟩
private theorem pr21577 : PrimeCertificate 21577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv31]) (by decide +kernel)
def pv21577 : PrimeValue := ⟨21577, pr21577⟩
private theorem pr21587 : PrimeCertificate 21587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv251]) (by decide +kernel)
def pv21587 : PrimeValue := ⟨21587, pr21587⟩
private theorem pr21589 : PrimeCertificate 21589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv257]) (by decide +kernel)
def pv21589 : PrimeValue := ⟨21589, pr21589⟩
private theorem pr21599 : PrimeCertificate 21599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv10799]) (by decide +kernel)
def pv21599 : PrimeValue := ⟨21599, pr21599⟩
private theorem pr21601 : PrimeCertificate 21601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv21601 : PrimeValue := ⟨21601, pr21601⟩
private theorem pr21611 : PrimeCertificate 21611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2161]) (by decide +kernel)
def pv21611 : PrimeValue := ⟨21611, pr21611⟩
private theorem pr21613 : PrimeCertificate 21613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1801]) (by decide +kernel)
def pv21613 : PrimeValue := ⟨21613, pr21613⟩
private theorem pr21617 : PrimeCertificate 21617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv193]) (by decide +kernel)
def pv21617 : PrimeValue := ⟨21617, pr21617⟩
private theorem pr21647 : PrimeCertificate 21647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv79,pv137]) (by decide +kernel)
def pv21647 : PrimeValue := ⟨21647, pr21647⟩
private theorem pr21649 : PrimeCertificate 21649 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv41]) (by decide +kernel)
def pv21649 : PrimeValue := ⟨21649, pr21649⟩
private theorem pr21661 : PrimeCertificate 21661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv21661 : PrimeValue := ⟨21661, pr21661⟩
private theorem pr21673 : PrimeCertificate 21673 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv21673 : PrimeValue := ⟨21673, pr21673⟩
private theorem pr21683 : PrimeCertificate 21683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv293]) (by decide +kernel)
def pv21683 : PrimeValue := ⟨21683, pr21683⟩
private theorem pr21701 : PrimeCertificate 21701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv31]) (by decide +kernel)
def pv21701 : PrimeValue := ⟨21701, pr21701⟩
private theorem pr21713 : PrimeCertificate 21713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv59]) (by decide +kernel)
def pv21713 : PrimeValue := ⟨21713, pr21713⟩
private theorem pr21727 : PrimeCertificate 21727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv71]) (by decide +kernel)
def pv21727 : PrimeValue := ⟨21727, pr21727⟩
private theorem pr21737 : PrimeCertificate 21737 :=
  certifyPrime (q := pv31) (ls := [pv2,pv11,pv13,pv19]) (by decide +kernel)
def pv21737 : PrimeValue := ⟨21737, pr21737⟩
private theorem pr21739 : PrimeCertificate 21739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3623]) (by decide +kernel)
def pv21739 : PrimeValue := ⟨21739, pr21739⟩
private theorem pr21751 : PrimeCertificate 21751 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv21751 : PrimeValue := ⟨21751, pr21751⟩
private theorem pr21757 : PrimeCertificate 21757 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv21757 : PrimeValue := ⟨21757, pr21757⟩
private theorem pr21767 : PrimeCertificate 21767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv10883]) (by decide +kernel)
def pv21767 : PrimeValue := ⟨21767, pr21767⟩
private theorem pr21773 : PrimeCertificate 21773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5443]) (by decide +kernel)
def pv21773 : PrimeValue := ⟨21773, pr21773⟩
private theorem pr21787 : PrimeCertificate 21787 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv3631]) (by decide +kernel)
def pv21787 : PrimeValue := ⟨21787, pr21787⟩
private theorem pr21799 : PrimeCertificate 21799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv173]) (by decide +kernel)
def pv21799 : PrimeValue := ⟨21799, pr21799⟩
private theorem pr21803 : PrimeCertificate 21803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv991]) (by decide +kernel)
def pv21803 : PrimeValue := ⟨21803, pr21803⟩
private theorem pr21817 : PrimeCertificate 21817 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv21817 : PrimeValue := ⟨21817, pr21817⟩
private theorem pr21821 : PrimeCertificate 21821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1091]) (by decide +kernel)
def pv21821 : PrimeValue := ⟨21821, pr21821⟩
private theorem pr21839 : PrimeCertificate 21839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv61,pv179]) (by decide +kernel)
def pv21839 : PrimeValue := ⟨21839, pr21839⟩
private theorem pr21841 : PrimeCertificate 21841 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv21841 : PrimeValue := ⟨21841, pr21841⟩
private theorem pr21851 : PrimeCertificate 21851 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv23]) (by decide +kernel)
def pv21851 : PrimeValue := ⟨21851, pr21851⟩
private theorem pr21859 : PrimeCertificate 21859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3643]) (by decide +kernel)
def pv21859 : PrimeValue := ⟨21859, pr21859⟩
private theorem pr21863 : PrimeCertificate 21863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv643]) (by decide +kernel)
def pv21863 : PrimeValue := ⟨21863, pr21863⟩
private theorem pr21871 : PrimeCertificate 21871 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv21871 : PrimeValue := ⟨21871, pr21871⟩
private theorem pr21881 : PrimeCertificate 21881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv547]) (by decide +kernel)
def pv21881 : PrimeValue := ⟨21881, pr21881⟩
private theorem pr21893 : PrimeCertificate 21893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv421]) (by decide +kernel)
def pv21893 : PrimeValue := ⟨21893, pr21893⟩
private theorem pr21911 : PrimeCertificate 21911 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv313]) (by decide +kernel)
def pv21911 : PrimeValue := ⟨21911, pr21911⟩
private theorem pr21929 : PrimeCertificate 21929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2741]) (by decide +kernel)
def pv21929 : PrimeValue := ⟨21929, pr21929⟩
private theorem pr21937 : PrimeCertificate 21937 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv457]) (by decide +kernel)
def pv21937 : PrimeValue := ⟨21937, pr21937⟩
private theorem pr21943 : PrimeCertificate 21943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv53]) (by decide +kernel)
def pv21943 : PrimeValue := ⟨21943, pr21943⟩
private theorem pr21961 : PrimeCertificate 21961 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv21961 : PrimeValue := ⟨21961, pr21961⟩
private theorem pr21977 : PrimeCertificate 21977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv67]) (by decide +kernel)
def pv21977 : PrimeValue := ⟨21977, pr21977⟩
private theorem pr21991 : PrimeCertificate 21991 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv733]) (by decide +kernel)
def pv21991 : PrimeValue := ⟨21991, pr21991⟩
private theorem pr21997 : PrimeCertificate 21997 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv47]) (by decide +kernel)
def pv21997 : PrimeValue := ⟨21997, pr21997⟩
private theorem pr22003 : PrimeCertificate 22003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv193]) (by decide +kernel)
def pv22003 : PrimeValue := ⟨22003, pr22003⟩
private theorem pr22013 : PrimeCertificate 22013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5503]) (by decide +kernel)
def pv22013 : PrimeValue := ⟨22013, pr22013⟩
private theorem pr22027 : PrimeCertificate 22027 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3671]) (by decide +kernel)
def pv22027 : PrimeValue := ⟨22027, pr22027⟩
private theorem pr22031 : PrimeCertificate 22031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv2203]) (by decide +kernel)
def pv22031 : PrimeValue := ⟨22031, pr22031⟩
private theorem pr22037 : PrimeCertificate 22037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv787]) (by decide +kernel)
def pv22037 : PrimeValue := ⟨22037, pr22037⟩
private theorem pr22039 : PrimeCertificate 22039 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv3673]) (by decide +kernel)
def pv22039 : PrimeValue := ⟨22039, pr22039⟩
private theorem pr22051 : PrimeCertificate 22051 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv22051 : PrimeValue := ⟨22051, pr22051⟩
private theorem pr22063 : PrimeCertificate 22063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3677]) (by decide +kernel)
def pv22063 : PrimeValue := ⟨22063, pr22063⟩
private theorem pr22067 : PrimeCertificate 22067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv59]) (by decide +kernel)
def pv22067 : PrimeValue := ⟨22067, pr22067⟩
private theorem pr22073 : PrimeCertificate 22073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv89]) (by decide +kernel)
def pv22073 : PrimeValue := ⟨22073, pr22073⟩
private theorem pr22079 : PrimeCertificate 22079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv19,pv83]) (by decide +kernel)
def pv22079 : PrimeValue := ⟨22079, pr22079⟩
private theorem pr22091 : PrimeCertificate 22091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47]) (by decide +kernel)
def pv22091 : PrimeValue := ⟨22091, pr22091⟩
private theorem pr22093 : PrimeCertificate 22093 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv263]) (by decide +kernel)
def pv22093 : PrimeValue := ⟨22093, pr22093⟩
private theorem pr22109 : PrimeCertificate 22109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5527]) (by decide +kernel)
def pv22109 : PrimeValue := ⟨22109, pr22109⟩
private theorem pr22111 : PrimeCertificate 22111 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv67]) (by decide +kernel)
def pv22111 : PrimeValue := ⟨22111, pr22111⟩
private theorem pr22123 : PrimeCertificate 22123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1229]) (by decide +kernel)
def pv22123 : PrimeValue := ⟨22123, pr22123⟩
private theorem pr22129 : PrimeCertificate 22129 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv461]) (by decide +kernel)
def pv22129 : PrimeValue := ⟨22129, pr22129⟩
private theorem pr22133 : PrimeCertificate 22133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv503]) (by decide +kernel)
def pv22133 : PrimeValue := ⟨22133, pr22133⟩
private theorem pr22147 : PrimeCertificate 22147 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3691]) (by decide +kernel)
def pv22147 : PrimeValue := ⟨22147, pr22147⟩
private theorem pr22153 : PrimeCertificate 22153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv71]) (by decide +kernel)
def pv22153 : PrimeValue := ⟨22153, pr22153⟩
private theorem pr22157 : PrimeCertificate 22157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv191]) (by decide +kernel)
def pv22157 : PrimeValue := ⟨22157, pr22157⟩
private theorem pr22159 : PrimeCertificate 22159 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1231]) (by decide +kernel)
def pv22159 : PrimeValue := ⟨22159, pr22159⟩
private theorem pr22171 : PrimeCertificate 22171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv739]) (by decide +kernel)
def pv22171 : PrimeValue := ⟨22171, pr22171⟩
private theorem pr22189 : PrimeCertificate 22189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv22189 : PrimeValue := ⟨22189, pr22189⟩
private theorem pr22193 : PrimeCertificate 22193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv73]) (by decide +kernel)
def pv22193 : PrimeValue := ⟨22193, pr22193⟩
private theorem pr22229 : PrimeCertificate 22229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5557]) (by decide +kernel)
def pv22229 : PrimeValue := ⟨22229, pr22229⟩
private theorem pr22247 : PrimeCertificate 22247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv227]) (by decide +kernel)
def pv22247 : PrimeValue := ⟨22247, pr22247⟩
private theorem pr22259 : PrimeCertificate 22259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv359]) (by decide +kernel)
def pv22259 : PrimeValue := ⟨22259, pr22259⟩
private theorem pr22271 : PrimeCertificate 22271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv131]) (by decide +kernel)
def pv22271 : PrimeValue := ⟨22271, pr22271⟩
private theorem pr22273 : PrimeCertificate 22273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv22273 : PrimeValue := ⟨22273, pr22273⟩
private theorem pr22277 : PrimeCertificate 22277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5569]) (by decide +kernel)
def pv22277 : PrimeValue := ⟨22277, pr22277⟩
private theorem pr22279 : PrimeCertificate 22279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv79]) (by decide +kernel)
def pv22279 : PrimeValue := ⟨22279, pr22279⟩
private theorem pr22283 : PrimeCertificate 22283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv857]) (by decide +kernel)
def pv22283 : PrimeValue := ⟨22283, pr22283⟩
private theorem pr22291 : PrimeCertificate 22291 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv743]) (by decide +kernel)
def pv22291 : PrimeValue := ⟨22291, pr22291⟩
private theorem pr22303 : PrimeCertificate 22303 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv59]) (by decide +kernel)
def pv22303 : PrimeValue := ⟨22303, pr22303⟩
private theorem pr22307 : PrimeCertificate 22307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv587]) (by decide +kernel)
def pv22307 : PrimeValue := ⟨22307, pr22307⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
