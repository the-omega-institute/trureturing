/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table104
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table104.pv437861
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table069
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table070

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr437861 : PrimeCertificate 437861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv21893]) (by decide +kernel)
def pv437861 : PrimeValue := ⟨437861, pr437861⟩
private theorem pr437867 : PrimeCertificate 437867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv1531]) (by decide +kernel)
def pv437867 : PrimeValue := ⟨437867, pr437867⟩
private theorem pr437923 : PrimeCertificate 437923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24329]) (by decide +kernel)
def pv437923 : PrimeValue := ⟨437923, pr437923⟩
private theorem pr437959 : PrimeCertificate 437959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv839]) (by decide +kernel)
def pv437959 : PrimeValue := ⟨437959, pr437959⟩
private theorem pr438017 : PrimeCertificate 438017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv59]) (by decide +kernel)
def pv438017 : PrimeValue := ⟨438017, pr438017⟩
private theorem pr438049 : PrimeCertificate 438049 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv438049 : PrimeValue := ⟨438049, pr438049⟩
private theorem pr438131 : PrimeCertificate 438131 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv569]) (by decide +kernel)
def pv438131 : PrimeValue := ⟨438131, pr438131⟩
private theorem pr438143 : PrimeCertificate 438143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv219071]) (by decide +kernel)
def pv438143 : PrimeValue := ⟨438143, pr438143⟩
private theorem pr438211 : PrimeCertificate 438211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv541]) (by decide +kernel)
def pv438211 : PrimeValue := ⟨438211, pr438211⟩
private theorem pr438223 : PrimeCertificate 438223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73037]) (by decide +kernel)
def pv438223 : PrimeValue := ⟨438223, pr438223⟩
private theorem pr438241 : PrimeCertificate 438241 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv83]) (by decide +kernel)
def pv438241 : PrimeValue := ⟨438241, pr438241⟩
private theorem pr438253 : PrimeCertificate 438253 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv59,pv619]) (by decide +kernel)
def pv438253 : PrimeValue := ⟨438253, pr438253⟩
private theorem pr438281 : PrimeCertificate 438281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv10957]) (by decide +kernel)
def pv438281 : PrimeValue := ⟨438281, pr438281⟩
private theorem pr438287 : PrimeCertificate 438287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv219143]) (by decide +kernel)
def pv438287 : PrimeValue := ⟨438287, pr438287⟩
private theorem pr438409 : PrimeCertificate 438409 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv6089]) (by decide +kernel)
def pv438409 : PrimeValue := ⟨438409, pr438409⟩
private theorem pr438517 : PrimeCertificate 438517 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv937]) (by decide +kernel)
def pv438517 : PrimeValue := ⟨438517, pr438517⟩
private theorem pr438521 : PrimeCertificate 438521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv577]) (by decide +kernel)
def pv438521 : PrimeValue := ⟨438521, pr438521⟩
private theorem pr438611 : PrimeCertificate 438611 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv23,pv1907]) (by decide +kernel)
def pv438611 : PrimeValue := ⟨438611, pr438611⟩
private theorem pr438637 : PrimeCertificate 438637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv3323]) (by decide +kernel)
def pv438637 : PrimeValue := ⟨438637, pr438637⟩
private theorem pr438671 : PrimeCertificate 438671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv43867]) (by decide +kernel)
def pv438671 : PrimeValue := ⟨438671, pr438671⟩
private theorem pr438701 : PrimeCertificate 438701 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv41,pv107]) (by decide +kernel)
def pv438701 : PrimeValue := ⟨438701, pr438701⟩
private theorem pr438793 : PrimeCertificate 438793 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv47,pv389]) (by decide +kernel)
def pv438793 : PrimeValue := ⟨438793, pr438793⟩
private theorem pr438833 : PrimeCertificate 438833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv27427]) (by decide +kernel)
def pv438833 : PrimeValue := ⟨438833, pr438833⟩
private theorem pr438847 : PrimeCertificate 438847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73141]) (by decide +kernel)
def pv438847 : PrimeValue := ⟨438847, pr438847⟩
private theorem pr438869 : PrimeCertificate 438869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109717]) (by decide +kernel)
def pv438869 : PrimeValue := ⟨438869, pr438869⟩
private theorem pr438877 : PrimeCertificate 438877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv167]) (by decide +kernel)
def pv438877 : PrimeValue := ⟨438877, pr438877⟩
private theorem pr438913 : PrimeCertificate 438913 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv127]) (by decide +kernel)
def pv438913 : PrimeValue := ⟨438913, pr438913⟩
private theorem pr438937 : PrimeCertificate 438937 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv18289]) (by decide +kernel)
def pv438937 : PrimeValue := ⟨438937, pr438937⟩
private theorem pr438941 : PrimeCertificate 438941 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv1291]) (by decide +kernel)
def pv438941 : PrimeValue := ⟨438941, pr438941⟩
private theorem pr438953 : PrimeCertificate 438953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv54869]) (by decide +kernel)
def pv438953 : PrimeValue := ⟨438953, pr438953⟩
private theorem pr438983 : PrimeCertificate 438983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv219491]) (by decide +kernel)
def pv438983 : PrimeValue := ⟨438983, pr438983⟩
private theorem pr439081 : PrimeCertificate 439081 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv3659]) (by decide +kernel)
def pv439081 : PrimeValue := ⟨439081, pr439081⟩
private theorem pr439157 : PrimeCertificate 439157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109789]) (by decide +kernel)
def pv439157 : PrimeValue := ⟨439157, pr439157⟩
private theorem pr439183 : PrimeCertificate 439183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2711]) (by decide +kernel)
def pv439183 : PrimeValue := ⟨439183, pr439183⟩
private theorem pr439303 : PrimeCertificate 439303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv211,pv347]) (by decide +kernel)
def pv439303 : PrimeValue := ⟨439303, pr439303⟩
private theorem pr439349 : PrimeCertificate 439349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv17,pv71]) (by decide +kernel)
def pv439349 : PrimeValue := ⟨439349, pr439349⟩
private theorem pr439357 : PrimeCertificate 439357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv41,pv47]) (by decide +kernel)
def pv439357 : PrimeValue := ⟨439357, pr439357⟩
private theorem pr439367 : PrimeCertificate 439367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv219683]) (by decide +kernel)
def pv439367 : PrimeValue := ⟨439367, pr439367⟩
private theorem pr439421 : PrimeCertificate 439421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv127,pv173]) (by decide +kernel)
def pv439421 : PrimeValue := ⟨439421, pr439421⟩
private theorem pr439463 : PrimeCertificate 439463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv219731]) (by decide +kernel)
def pv439463 : PrimeValue := ⟨439463, pr439463⟩
private theorem pr439493 : PrimeCertificate 439493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109873]) (by decide +kernel)
def pv439493 : PrimeValue := ⟨439493, pr439493⟩
private theorem pr439511 : PrimeCertificate 439511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv43951]) (by decide +kernel)
def pv439511 : PrimeValue := ⟨439511, pr439511⟩
private theorem pr439559 : PrimeCertificate 439559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv31397]) (by decide +kernel)
def pv439559 : PrimeValue := ⟨439559, pr439559⟩
private theorem pr439567 : PrimeCertificate 439567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv1201]) (by decide +kernel)
def pv439567 : PrimeValue := ⟨439567, pr439567⟩
private theorem pr439583 : PrimeCertificate 439583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv29,pv53]) (by decide +kernel)
def pv439583 : PrimeValue := ⟨439583, pr439583⟩
private theorem pr439613 : PrimeCertificate 439613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109903]) (by decide +kernel)
def pv439613 : PrimeValue := ⟨439613, pr439613⟩
private theorem pr439631 : PrimeCertificate 439631 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv43963]) (by decide +kernel)
def pv439631 : PrimeValue := ⟨439631, pr439631⟩
private theorem pr439667 : PrimeCertificate 439667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv367,pv599]) (by decide +kernel)
def pv439667 : PrimeValue := ⟨439667, pr439667⟩
private theorem pr439723 : PrimeCertificate 439723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv479]) (by decide +kernel)
def pv439723 : PrimeValue := ⟨439723, pr439723⟩
private theorem pr439763 : PrimeCertificate 439763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv219881]) (by decide +kernel)
def pv439763 : PrimeValue := ⟨439763, pr439763⟩
private theorem pr439781 : PrimeCertificate 439781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1999]) (by decide +kernel)
def pv439781 : PrimeValue := ⟨439781, pr439781⟩
private theorem pr439811 : PrimeCertificate 439811 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv61,pv103]) (by decide +kernel)
def pv439811 : PrimeValue := ⟨439811, pr439811⟩
private theorem pr439849 : PrimeCertificate 439849 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv41,pv149]) (by decide +kernel)
def pv439849 : PrimeValue := ⟨439849, pr439849⟩
private theorem pr439853 : PrimeCertificate 439853 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23,pv683]) (by decide +kernel)
def pv439853 : PrimeValue := ⟨439853, pr439853⟩
private theorem pr439867 : PrimeCertificate 439867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv3491]) (by decide +kernel)
def pv439867 : PrimeValue := ⟨439867, pr439867⟩
private theorem pr439903 : PrimeCertificate 439903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv24439]) (by decide +kernel)
def pv439903 : PrimeValue := ⟨439903, pr439903⟩
private theorem pr439919 : PrimeCertificate 439919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv219959]) (by decide +kernel)
def pv439919 : PrimeValue := ⟨439919, pr439919⟩
private theorem pr439981 : PrimeCertificate 439981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7333]) (by decide +kernel)
def pv439981 : PrimeValue := ⟨439981, pr439981⟩
private theorem pr440023 : PrimeCertificate 440023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv59,pv113]) (by decide +kernel)
def pv440023 : PrimeValue := ⟨440023, pr440023⟩
private theorem pr440171 : PrimeCertificate 440171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv44017]) (by decide +kernel)
def pv440171 : PrimeValue := ⟨440171, pr440171⟩
private theorem pr440177 : PrimeCertificate 440177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv41,pv61]) (by decide +kernel)
def pv440177 : PrimeValue := ⟨440177, pr440177⟩
private theorem pr440183 : PrimeCertificate 440183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv127,pv1733]) (by decide +kernel)
def pv440183 : PrimeValue := ⟨440183, pr440183⟩
private theorem pr440203 : PrimeCertificate 440203 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv47,pv223]) (by decide +kernel)
def pv440203 : PrimeValue := ⟨440203, pr440203⟩
private theorem pr440227 : PrimeCertificate 440227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv661]) (by decide +kernel)
def pv440227 : PrimeValue := ⟨440227, pr440227⟩
private theorem pr440261 : PrimeCertificate 440261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv22013]) (by decide +kernel)
def pv440261 : PrimeValue := ⟨440261, pr440261⟩
private theorem pr440269 : PrimeCertificate 440269 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv1931]) (by decide +kernel)
def pv440269 : PrimeValue := ⟨440269, pr440269⟩
private theorem pr440281 : PrimeCertificate 440281 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv1223]) (by decide +kernel)
def pv440281 : PrimeValue := ⟨440281, pr440281⟩
private theorem pr440333 : PrimeCertificate 440333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv110083]) (by decide +kernel)
def pv440333 : PrimeValue := ⟨440333, pr440333⟩
private theorem pr440393 : PrimeCertificate 440393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv55049]) (by decide +kernel)
def pv440393 : PrimeValue := ⟨440393, pr440393⟩
private theorem pr440399 : PrimeCertificate 440399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv83,pv379]) (by decide +kernel)
def pv440399 : PrimeValue := ⟨440399, pr440399⟩
private theorem pr440431 : PrimeCertificate 440431 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv53,pv277]) (by decide +kernel)
def pv440431 : PrimeValue := ⟨440431, pr440431⟩
private theorem pr440441 : PrimeCertificate 440441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv13]) (by decide +kernel)
def pv440441 : PrimeValue := ⟨440441, pr440441⟩
private theorem pr440497 : PrimeCertificate 440497 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv7,pv19,pv23]) (by decide +kernel)
def pv440497 : PrimeValue := ⟨440497, pr440497⟩
private theorem pr440501 : PrimeCertificate 440501 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv881]) (by decide +kernel)
def pv440501 : PrimeValue := ⟨440501, pr440501⟩
private theorem pr440549 : PrimeCertificate 440549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv241,pv457]) (by decide +kernel)
def pv440549 : PrimeValue := ⟨440549, pr440549⟩
private theorem pr440551 : PrimeCertificate 440551 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv89]) (by decide +kernel)
def pv440551 : PrimeValue := ⟨440551, pr440551⟩
private theorem pr440579 : PrimeCertificate 440579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv47,pv109]) (by decide +kernel)
def pv440579 : PrimeValue := ⟨440579, pr440579⟩
private theorem pr440677 : PrimeCertificate 440677 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv12241]) (by decide +kernel)
def pv440677 : PrimeValue := ⟨440677, pr440677⟩
private theorem pr440723 : PrimeCertificate 440723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv220361]) (by decide +kernel)
def pv440723 : PrimeValue := ⟨440723, pr440723⟩
private theorem pr440731 : PrimeCertificate 440731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv59,pv83]) (by decide +kernel)
def pv440731 : PrimeValue := ⟨440731, pr440731⟩
private theorem pr440773 : PrimeCertificate 440773 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1597]) (by decide +kernel)
def pv440773 : PrimeValue := ⟨440773, pr440773⟩
private theorem pr440821 : PrimeCertificate 440821 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv31,pv79]) (by decide +kernel)
def pv440821 : PrimeValue := ⟨440821, pr440821⟩
private theorem pr440831 : PrimeCertificate 440831 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv13,pv3391]) (by decide +kernel)
def pv440831 : PrimeValue := ⟨440831, pr440831⟩
private theorem pr440863 : PrimeCertificate 440863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73477]) (by decide +kernel)
def pv440863 : PrimeValue := ⟨440863, pr440863⟩
private theorem pr440893 : PrimeCertificate 440893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv331]) (by decide +kernel)
def pv440893 : PrimeValue := ⟨440893, pr440893⟩
private theorem pr440941 : PrimeCertificate 440941 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7349]) (by decide +kernel)
def pv440941 : PrimeValue := ⟨440941, pr440941⟩
private theorem pr440953 : PrimeCertificate 440953 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv19,pv967]) (by decide +kernel)
def pv440953 : PrimeValue := ⟨440953, pr440953⟩
private theorem pr440983 : PrimeCertificate 440983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv24499]) (by decide +kernel)
def pv440983 : PrimeValue := ⟨440983, pr440983⟩
private theorem pr441041 : PrimeCertificate 441041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv149]) (by decide +kernel)
def pv441041 : PrimeValue := ⟨441041, pr441041⟩
private theorem pr441043 : PrimeCertificate 441043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv10501]) (by decide +kernel)
def pv441043 : PrimeValue := ⟨441043, pr441043⟩
private theorem pr441073 : PrimeCertificate 441073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1021]) (by decide +kernel)
def pv441073 : PrimeValue := ⟨441073, pr441073⟩
private theorem pr441109 : PrimeCertificate 441109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12253]) (by decide +kernel)
def pv441109 : PrimeValue := ⟨441109, pr441109⟩
private theorem pr441179 : PrimeCertificate 441179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv220589]) (by decide +kernel)
def pv441179 : PrimeValue := ⟨441179, pr441179⟩
private theorem pr441193 : PrimeCertificate 441193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv593]) (by decide +kernel)
def pv441193 : PrimeValue := ⟨441193, pr441193⟩
private theorem pr441319 : PrimeCertificate 441319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv73553]) (by decide +kernel)
def pv441319 : PrimeValue := ⟨441319, pr441319⟩
private theorem pr441359 : PrimeCertificate 441359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv73,pv3023]) (by decide +kernel)
def pv441359 : PrimeValue := ⟨441359, pr441359⟩
private theorem pr441361 : PrimeCertificate 441361 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv613]) (by decide +kernel)
def pv441361 : PrimeValue := ⟨441361, pr441361⟩
private theorem pr441403 : PrimeCertificate 441403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv5659]) (by decide +kernel)
def pv441403 : PrimeValue := ⟨441403, pr441403⟩
private theorem pr441461 : PrimeCertificate 441461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv22073]) (by decide +kernel)
def pv441461 : PrimeValue := ⟨441461, pr441461⟩
private theorem pr441499 : PrimeCertificate 441499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73583]) (by decide +kernel)
def pv441499 : PrimeValue := ⟨441499, pr441499⟩
private theorem pr441523 : PrimeCertificate 441523 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv1291]) (by decide +kernel)
def pv441523 : PrimeValue := ⟨441523, pr441523⟩
private theorem pr441613 : PrimeCertificate 441613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv47]) (by decide +kernel)
def pv441613 : PrimeValue := ⟨441613, pr441613⟩
private theorem pr441697 : PrimeCertificate 441697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv107]) (by decide +kernel)
def pv441697 : PrimeValue := ⟨441697, pr441697⟩
private theorem pr441787 : PrimeCertificate 441787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv2539]) (by decide +kernel)
def pv441787 : PrimeValue := ⟨441787, pr441787⟩
private theorem pr441797 : PrimeCertificate 441797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv73,pv89]) (by decide +kernel)
def pv441797 : PrimeValue := ⟨441797, pr441797⟩
private theorem pr441829 : PrimeCertificate 441829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4091]) (by decide +kernel)
def pv441829 : PrimeValue := ⟨441829, pr441829⟩
private theorem pr441877 : PrimeCertificate 441877 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv1601]) (by decide +kernel)
def pv441877 : PrimeValue := ⟨441877, pr441877⟩
private theorem pr441907 : PrimeCertificate 441907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73651]) (by decide +kernel)
def pv441907 : PrimeValue := ⟨441907, pr441907⟩
private theorem pr442007 : PrimeCertificate 442007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv3623]) (by decide +kernel)
def pv442007 : PrimeValue := ⟨442007, pr442007⟩
private theorem pr442009 : PrimeCertificate 442009 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv877]) (by decide +kernel)
def pv442009 : PrimeValue := ⟨442009, pr442009⟩
private theorem pr442061 : PrimeCertificate 442061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv31]) (by decide +kernel)
def pv442061 : PrimeValue := ⟨442061, pr442061⟩
private theorem pr442121 : PrimeCertificate 442121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv1579]) (by decide +kernel)
def pv442121 : PrimeValue := ⟨442121, pr442121⟩
private theorem pr442147 : PrimeCertificate 442147 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv59,pv1249]) (by decide +kernel)
def pv442147 : PrimeValue := ⟨442147, pr442147⟩
private theorem pr442157 : PrimeCertificate 442157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv773]) (by decide +kernel)
def pv442157 : PrimeValue := ⟨442157, pr442157⟩
private theorem pr442177 : PrimeCertificate 442177 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv47]) (by decide +kernel)
def pv442177 : PrimeValue := ⟨442177, pr442177⟩
private theorem pr442181 : PrimeCertificate 442181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv22109]) (by decide +kernel)
def pv442181 : PrimeValue := ⟨442181, pr442181⟩
private theorem pr442243 : PrimeCertificate 442243 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv79,pv311]) (by decide +kernel)
def pv442243 : PrimeValue := ⟨442243, pr442243⟩
private theorem pr442283 : PrimeCertificate 442283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv103,pv113]) (by decide +kernel)
def pv442283 : PrimeValue := ⟨442283, pr442283⟩
private theorem pr442333 : PrimeCertificate 442333 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv1117]) (by decide +kernel)
def pv442333 : PrimeValue := ⟨442333, pr442333⟩
private theorem pr442397 : PrimeCertificate 442397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv5821]) (by decide +kernel)
def pv442397 : PrimeValue := ⟨442397, pr442397⟩
private theorem pr442499 : PrimeCertificate 442499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31607]) (by decide +kernel)
def pv442499 : PrimeValue := ⟨442499, pr442499⟩
private theorem pr442573 : PrimeCertificate 442573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv2837]) (by decide +kernel)
def pv442573 : PrimeValue := ⟨442573, pr442573⟩
private theorem pr442577 : PrimeCertificate 442577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv139,pv199]) (by decide +kernel)
def pv442577 : PrimeValue := ⟨442577, pr442577⟩
private theorem pr442601 : PrimeCertificate 442601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2213]) (by decide +kernel)
def pv442601 : PrimeValue := ⟨442601, pr442601⟩
private theorem pr442609 : PrimeCertificate 442609 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv9221]) (by decide +kernel)
def pv442609 : PrimeValue := ⟨442609, pr442609⟩
private theorem pr442619 : PrimeCertificate 442619 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv31,pv59]) (by decide +kernel)
def pv442619 : PrimeValue := ⟨442619, pr442619⟩
private theorem pr442633 : PrimeCertificate 442633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv18443]) (by decide +kernel)
def pv442633 : PrimeValue := ⟨442633, pr442633⟩
private theorem pr442691 : PrimeCertificate 442691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv44269]) (by decide +kernel)
def pv442691 : PrimeValue := ⟨442691, pr442691⟩
private theorem pr442733 : PrimeCertificate 442733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv151,pv733]) (by decide +kernel)
def pv442733 : PrimeValue := ⟨442733, pr442733⟩
private theorem pr442777 : PrimeCertificate 442777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv971]) (by decide +kernel)
def pv442777 : PrimeValue := ⟨442777, pr442777⟩
private theorem pr442789 : PrimeCertificate 442789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv36899]) (by decide +kernel)
def pv442789 : PrimeValue := ⟨442789, pr442789⟩
private theorem pr442831 : PrimeCertificate 442831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv29,pv509]) (by decide +kernel)
def pv442831 : PrimeValue := ⟨442831, pr442831⟩
private theorem pr442837 : PrimeCertificate 442837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12301]) (by decide +kernel)
def pv442837 : PrimeValue := ⟨442837, pr442837⟩
private theorem pr442843 : PrimeCertificate 442843 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv23,pv3209]) (by decide +kernel)
def pv442843 : PrimeValue := ⟨442843, pr442843⟩
private theorem pr442903 : PrimeCertificate 442903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv97,pv761]) (by decide +kernel)
def pv442903 : PrimeValue := ⟨442903, pr442903⟩
private theorem pr442919 : PrimeCertificate 442919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17,pv1861]) (by decide +kernel)
def pv442919 : PrimeValue := ⟨442919, pr442919⟩
private theorem pr442961 : PrimeCertificate 442961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv113]) (by decide +kernel)
def pv442961 : PrimeValue := ⟨442961, pr442961⟩
private theorem pr442963 : PrimeCertificate 442963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv631]) (by decide +kernel)
def pv442963 : PrimeValue := ⟨442963, pr442963⟩
private theorem pr442973 : PrimeCertificate 442973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv1877]) (by decide +kernel)
def pv442973 : PrimeValue := ⟨442973, pr442973⟩
private theorem pr442979 : PrimeCertificate 442979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv221489]) (by decide +kernel)
def pv442979 : PrimeValue := ⟨442979, pr442979⟩
private theorem pr442991 : PrimeCertificate 442991 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv31,pv1429]) (by decide +kernel)
def pv442991 : PrimeValue := ⟨442991, pr442991⟩
private theorem pr443011 : PrimeCertificate 443011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv14767]) (by decide +kernel)
def pv443011 : PrimeValue := ⟨443011, pr443011⟩
private theorem pr443041 : PrimeCertificate 443041 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv71]) (by decide +kernel)
def pv443041 : PrimeValue := ⟨443041, pr443041⟩
private theorem pr443059 : PrimeCertificate 443059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv137]) (by decide +kernel)
def pv443059 : PrimeValue := ⟨443059, pr443059⟩
private theorem pr443063 : PrimeCertificate 443063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv7639]) (by decide +kernel)
def pv443063 : PrimeValue := ⟨443063, pr443063⟩
private theorem pr443077 : PrimeCertificate 443077 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv36923]) (by decide +kernel)
def pv443077 : PrimeValue := ⟨443077, pr443077⟩
private theorem pr443117 : PrimeCertificate 443117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv2357]) (by decide +kernel)
def pv443117 : PrimeValue := ⟨443117, pr443117⟩
private theorem pr443123 : PrimeCertificate 443123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv13033]) (by decide +kernel)
def pv443123 : PrimeValue := ⟨443123, pr443123⟩
private theorem pr443147 : PrimeCertificate 443147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv20143]) (by decide +kernel)
def pv443147 : PrimeValue := ⟨443147, pr443147⟩
private theorem pr443153 : PrimeCertificate 443153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv27697]) (by decide +kernel)
def pv443153 : PrimeValue := ⟨443153, pr443153⟩
private theorem pr443231 : PrimeCertificate 443231 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv127,pv349]) (by decide +kernel)
def pv443231 : PrimeValue := ⟨443231, pr443231⟩
private theorem pr443273 : PrimeCertificate 443273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv827]) (by decide +kernel)
def pv443273 : PrimeValue := ⟨443273, pr443273⟩
private theorem pr443281 : PrimeCertificate 443281 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv1847]) (by decide +kernel)
def pv443281 : PrimeValue := ⟨443281, pr443281⟩
private theorem pr443291 : PrimeCertificate 443291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv97,pv457]) (by decide +kernel)
def pv443291 : PrimeValue := ⟨443291, pr443291⟩
private theorem pr443293 : PrimeCertificate 443293 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv41,pv53]) (by decide +kernel)
def pv443293 : PrimeValue := ⟨443293, pr443293⟩
private theorem pr443353 : PrimeCertificate 443353 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv13,pv29]) (by decide +kernel)
def pv443353 : PrimeValue := ⟨443353, pr443353⟩
private theorem pr443363 : PrimeCertificate 443363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv7151]) (by decide +kernel)
def pv443363 : PrimeValue := ⟨443363, pr443363⟩
private theorem pr443419 : PrimeCertificate 443419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv263,pv281]) (by decide +kernel)
def pv443419 : PrimeValue := ⟨443419, pr443419⟩
private theorem pr443431 : PrimeCertificate 443431 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv13,pv379]) (by decide +kernel)
def pv443431 : PrimeValue := ⟨443431, pr443431⟩
private theorem pr443437 : PrimeCertificate 443437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv5279]) (by decide +kernel)
def pv443437 : PrimeValue := ⟨443437, pr443437⟩
private theorem pr443453 : PrimeCertificate 443453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv110863]) (by decide +kernel)
def pv443453 : PrimeValue := ⟨443453, pr443453⟩
private theorem pr443467 : PrimeCertificate 443467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv347]) (by decide +kernel)
def pv443467 : PrimeValue := ⟨443467, pr443467⟩
private theorem pr443489 : PrimeCertificate 443489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13859]) (by decide +kernel)
def pv443489 : PrimeValue := ⟨443489, pr443489⟩
private theorem pr443533 : PrimeCertificate 443533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1607]) (by decide +kernel)
def pv443533 : PrimeValue := ⟨443533, pr443533⟩
private theorem pr443567 : PrimeCertificate 443567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv131,pv1693]) (by decide +kernel)
def pv443567 : PrimeValue := ⟨443567, pr443567⟩
private theorem pr443587 : PrimeCertificate 443587 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv47]) (by decide +kernel)
def pv443587 : PrimeValue := ⟨443587, pr443587⟩
private theorem pr443629 : PrimeCertificate 443629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12323]) (by decide +kernel)
def pv443629 : PrimeValue := ⟨443629, pr443629⟩
private theorem pr443659 : PrimeCertificate 443659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73943]) (by decide +kernel)
def pv443659 : PrimeValue := ⟨443659, pr443659⟩
private theorem pr443687 : PrimeCertificate 443687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv163,pv1361]) (by decide +kernel)
def pv443687 : PrimeValue := ⟨443687, pr443687⟩
private theorem pr443689 : PrimeCertificate 443689 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv19,pv139]) (by decide +kernel)
def pv443689 : PrimeValue := ⟨443689, pr443689⟩
private theorem pr443701 : PrimeCertificate 443701 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv29]) (by decide +kernel)
def pv443701 : PrimeValue := ⟨443701, pr443701⟩
private theorem pr443711 : PrimeCertificate 443711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv44371]) (by decide +kernel)
def pv443711 : PrimeValue := ⟨443711, pr443711⟩
private theorem pr443761 : PrimeCertificate 443761 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv443761 : PrimeValue := ⟨443761, pr443761⟩
private theorem pr443771 : PrimeCertificate 443771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv199,pv223]) (by decide +kernel)
def pv443771 : PrimeValue := ⟨443771, pr443771⟩
private theorem pr443851 : PrimeCertificate 443851 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv269]) (by decide +kernel)
def pv443851 : PrimeValue := ⟨443851, pr443851⟩
private theorem pr443879 : PrimeCertificate 443879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv19,pv11681]) (by decide +kernel)
def pv443879 : PrimeValue := ⟨443879, pr443879⟩
private theorem pr443893 : PrimeCertificate 443893 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv71,pv521]) (by decide +kernel)
def pv443893 : PrimeValue := ⟨443893, pr443893⟩
private theorem pr443899 : PrimeCertificate 443899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv271]) (by decide +kernel)
def pv443899 : PrimeValue := ⟨443899, pr443899⟩
private theorem pr443909 : PrimeCertificate 443909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv110977]) (by decide +kernel)
def pv443909 : PrimeValue := ⟨443909, pr443909⟩
private theorem pr443983 : PrimeCertificate 443983 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv11,pv31]) (by decide +kernel)
def pv443983 : PrimeValue := ⟨443983, pr443983⟩
private theorem pr444007 : PrimeCertificate 444007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv1451]) (by decide +kernel)
def pv444007 : PrimeValue := ⟨444007, pr444007⟩
private theorem pr444029 : PrimeCertificate 444029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv8539]) (by decide +kernel)
def pv444029 : PrimeValue := ⟨444029, pr444029⟩
private theorem pr444079 : PrimeCertificate 444079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv24671]) (by decide +kernel)
def pv444079 : PrimeValue := ⟨444079, pr444079⟩
private theorem pr444089 : PrimeCertificate 444089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv55511]) (by decide +kernel)
def pv444089 : PrimeValue := ⟨444089, pr444089⟩
private theorem pr444127 : PrimeCertificate 444127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv74021]) (by decide +kernel)
def pv444127 : PrimeValue := ⟨444127, pr444127⟩
private theorem pr444131 : PrimeCertificate 444131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv1931]) (by decide +kernel)
def pv444131 : PrimeValue := ⟨444131, pr444131⟩
private theorem pr444179 : PrimeCertificate 444179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31727]) (by decide +kernel)
def pv444179 : PrimeValue := ⟨444179, pr444179⟩
private theorem pr444271 : PrimeCertificate 444271 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv59,pv251]) (by decide +kernel)
def pv444271 : PrimeValue := ⟨444271, pr444271⟩
private theorem pr444281 : PrimeCertificate 444281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv383]) (by decide +kernel)
def pv444281 : PrimeValue := ⟨444281, pr444281⟩
private theorem pr444307 : PrimeCertificate 444307 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv74051]) (by decide +kernel)
def pv444307 : PrimeValue := ⟨444307, pr444307⟩
private theorem pr444341 : PrimeCertificate 444341 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv1709]) (by decide +kernel)
def pv444341 : PrimeValue := ⟨444341, pr444341⟩
private theorem pr444443 : PrimeCertificate 444443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv359,pv619]) (by decide +kernel)
def pv444443 : PrimeValue := ⟨444443, pr444443⟩
private theorem pr444463 : PrimeCertificate 444463 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv74077]) (by decide +kernel)
def pv444463 : PrimeValue := ⟨444463, pr444463⟩
private theorem pr444517 : PrimeCertificate 444517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv2179]) (by decide +kernel)
def pv444517 : PrimeValue := ⟨444517, pr444517⟩
private theorem pr444553 : PrimeCertificate 444553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv18523]) (by decide +kernel)
def pv444553 : PrimeValue := ⟨444553, pr444553⟩
private theorem pr444569 : PrimeCertificate 444569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61,pv911]) (by decide +kernel)
def pv444569 : PrimeValue := ⟨444569, pr444569⟩
private theorem pr444623 : PrimeCertificate 444623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv222311]) (by decide +kernel)
def pv444623 : PrimeValue := ⟨444623, pr444623⟩
private theorem pr444637 : PrimeCertificate 444637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv179]) (by decide +kernel)
def pv444637 : PrimeValue := ⟨444637, pr444637⟩
private theorem pr444649 : PrimeCertificate 444649 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv97,pv191]) (by decide +kernel)
def pv444649 : PrimeValue := ⟨444649, pr444649⟩
private theorem pr444671 : PrimeCertificate 444671 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv53,pv839]) (by decide +kernel)
def pv444671 : PrimeValue := ⟨444671, pr444671⟩
private theorem pr444677 : PrimeCertificate 444677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv5851]) (by decide +kernel)
def pv444677 : PrimeValue := ⟨444677, pr444677⟩
private theorem pr444817 : PrimeCertificate 444817 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv3089]) (by decide +kernel)
def pv444817 : PrimeValue := ⟨444817, pr444817⟩
private theorem pr444833 : PrimeCertificate 444833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13901]) (by decide +kernel)
def pv444833 : PrimeValue := ⟨444833, pr444833⟩
private theorem pr444841 : PrimeCertificate 444841 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv337]) (by decide +kernel)
def pv444841 : PrimeValue := ⟨444841, pr444841⟩
private theorem pr444863 : PrimeCertificate 444863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv73,pv277]) (by decide +kernel)
def pv444863 : PrimeValue := ⟨444863, pr444863⟩
private theorem pr444877 : PrimeCertificate 444877 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv131,pv283]) (by decide +kernel)
def pv444877 : PrimeValue := ⟨444877, pr444877⟩
private theorem pr444953 : PrimeCertificate 444953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv55619]) (by decide +kernel)
def pv444953 : PrimeValue := ⟨444953, pr444953⟩
private theorem pr444967 : PrimeCertificate 444967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv74161]) (by decide +kernel)
def pv444967 : PrimeValue := ⟨444967, pr444967⟩
private theorem pr445001 : PrimeCertificate 445001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv89]) (by decide +kernel)
def pv445001 : PrimeValue := ⟨445001, pr445001⟩
private theorem pr445031 : PrimeCertificate 445031 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv191,pv233]) (by decide +kernel)
def pv445031 : PrimeValue := ⟨445031, pr445031⟩
private theorem pr445033 : PrimeCertificate 445033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv883]) (by decide +kernel)
def pv445033 : PrimeValue := ⟨445033, pr445033⟩
private theorem pr445069 : PrimeCertificate 445069 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv13,pv317]) (by decide +kernel)
def pv445069 : PrimeValue := ⟨445069, pr445069⟩
private theorem pr445087 : PrimeCertificate 445087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv313]) (by decide +kernel)
def pv445087 : PrimeValue := ⟨445087, pr445087⟩
private theorem pr445229 : PrimeCertificate 445229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv15901]) (by decide +kernel)
def pv445229 : PrimeValue := ⟨445229, pr445229⟩
private theorem pr445271 : PrimeCertificate 445271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv6361]) (by decide +kernel)
def pv445271 : PrimeValue := ⟨445271, pr445271⟩
private theorem pr445307 : PrimeCertificate 445307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv4201]) (by decide +kernel)
def pv445307 : PrimeValue := ⟨445307, pr445307⟩
private theorem pr445321 : PrimeCertificate 445321 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1237]) (by decide +kernel)
def pv445321 : PrimeValue := ⟨445321, pr445321⟩
private theorem pr445339 : PrimeCertificate 445339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2749]) (by decide +kernel)
def pv445339 : PrimeValue := ⟨445339, pr445339⟩
private theorem pr445363 : PrimeCertificate 445363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv199,pv373]) (by decide +kernel)
def pv445363 : PrimeValue := ⟨445363, pr445363⟩
private theorem pr445433 : PrimeCertificate 445433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv4283]) (by decide +kernel)
def pv445433 : PrimeValue := ⟨445433, pr445433⟩
private theorem pr445463 : PrimeCertificate 445463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv222731]) (by decide +kernel)
def pv445463 : PrimeValue := ⟨445463, pr445463⟩
private theorem pr445499 : PrimeCertificate 445499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv7681]) (by decide +kernel)
def pv445499 : PrimeValue := ⟨445499, pr445499⟩
private theorem pr445567 : PrimeCertificate 445567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv43,pv157]) (by decide +kernel)
def pv445567 : PrimeValue := ⟨445567, pr445567⟩
private theorem pr445583 : PrimeCertificate 445583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv222791]) (by decide +kernel)
def pv445583 : PrimeValue := ⟨445583, pr445583⟩
private theorem pr445589 : PrimeCertificate 445589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv19,pv41]) (by decide +kernel)
def pv445589 : PrimeValue := ⟨445589, pr445589⟩
private theorem pr445619 : PrimeCertificate 445619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv2297]) (by decide +kernel)
def pv445619 : PrimeValue := ⟨445619, pr445619⟩
private theorem pr445631 : PrimeCertificate 445631 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv44563]) (by decide +kernel)
def pv445631 : PrimeValue := ⟨445631, pr445631⟩
private theorem pr445633 : PrimeCertificate 445633 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv211]) (by decide +kernel)
def pv445633 : PrimeValue := ⟨445633, pr445633⟩
private theorem pr445657 : PrimeCertificate 445657 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv31,pv599]) (by decide +kernel)
def pv445657 : PrimeValue := ⟨445657, pr445657⟩
private theorem pr445699 : PrimeCertificate 445699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv2251]) (by decide +kernel)
def pv445699 : PrimeValue := ⟨445699, pr445699⟩
private theorem pr445807 : PrimeCertificate 445807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv24767]) (by decide +kernel)
def pv445807 : PrimeValue := ⟨445807, pr445807⟩
private theorem pr445829 : PrimeCertificate 445829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv491]) (by decide +kernel)
def pv445829 : PrimeValue := ⟨445829, pr445829⟩
private theorem pr445853 : PrimeCertificate 445853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv10133]) (by decide +kernel)
def pv445853 : PrimeValue := ⟨445853, pr445853⟩
private theorem pr445871 : PrimeCertificate 445871 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv44587]) (by decide +kernel)
def pv445871 : PrimeValue := ⟨445871, pr445871⟩
private theorem pr445883 : PrimeCertificate 445883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv222941]) (by decide +kernel)
def pv445883 : PrimeValue := ⟨445883, pr445883⟩
private theorem pr445891 : PrimeCertificate 445891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv89,pv167]) (by decide +kernel)
def pv445891 : PrimeValue := ⟨445891, pr445891⟩
private theorem pr445931 : PrimeCertificate 445931 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv19,pv2347]) (by decide +kernel)
def pv445931 : PrimeValue := ⟨445931, pr445931⟩
private theorem pr445943 : PrimeCertificate 445943 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv53,pv601]) (by decide +kernel)
def pv445943 : PrimeValue := ⟨445943, pr445943⟩
private theorem pr446009 : PrimeCertificate 446009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv197,pv283]) (by decide +kernel)
def pv446009 : PrimeValue := ⟨446009, pr446009⟩
private theorem pr446053 : PrimeCertificate 446053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37171]) (by decide +kernel)
def pv446053 : PrimeValue := ⟨446053, pr446053⟩
private theorem pr446087 : PrimeCertificate 446087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv67,pv3329]) (by decide +kernel)
def pv446087 : PrimeValue := ⟨446087, pr446087⟩
private theorem pr446141 : PrimeCertificate 446141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv22307]) (by decide +kernel)
def pv446141 : PrimeValue := ⟨446141, pr446141⟩
private theorem pr446197 : PrimeCertificate 446197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv103]) (by decide +kernel)
def pv446197 : PrimeValue := ⟨446197, pr446197⟩
private theorem pr446261 : PrimeCertificate 446261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv421]) (by decide +kernel)
def pv446261 : PrimeValue := ⟨446261, pr446261⟩
private theorem pr446273 : PrimeCertificate 446273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv367]) (by decide +kernel)
def pv446273 : PrimeValue := ⟨446273, pr446273⟩
private theorem pr446279 : PrimeCertificate 446279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv127,pv251]) (by decide +kernel)
def pv446279 : PrimeValue := ⟨446279, pr446279⟩
private theorem pr446323 : PrimeCertificate 446323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv1019]) (by decide +kernel)
def pv446323 : PrimeValue := ⟨446323, pr446323⟩
private theorem pr446333 : PrimeCertificate 446333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv241,pv463]) (by decide +kernel)
def pv446333 : PrimeValue := ⟨446333, pr446333⟩
private theorem pr446353 : PrimeCertificate 446353 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv547]) (by decide +kernel)
def pv446353 : PrimeValue := ⟨446353, pr446353⟩
private theorem pr446387 : PrimeCertificate 446387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv19,pv691]) (by decide +kernel)
def pv446387 : PrimeValue := ⟨446387, pr446387⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
