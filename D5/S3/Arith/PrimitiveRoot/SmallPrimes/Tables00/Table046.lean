/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table046
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table046.pv125897
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table006
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr125897 : PrimeCertificate 125897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv15737]) (by decide +kernel)
def pv125897 : PrimeValue := ⟨125897, pr125897⟩
private theorem pr125899 : PrimeCertificate 125899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20983]) (by decide +kernel)
def pv125899 : PrimeValue := ⟨125899, pr125899⟩
private theorem pr125921 : PrimeCertificate 125921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv787]) (by decide +kernel)
def pv125921 : PrimeValue := ⟨125921, pr125921⟩
private theorem pr125927 : PrimeCertificate 125927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv79,pv797]) (by decide +kernel)
def pv125927 : PrimeValue := ⟨125927, pr125927⟩
private theorem pr125929 : PrimeCertificate 125929 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv53]) (by decide +kernel)
def pv125929 : PrimeValue := ⟨125929, pr125929⟩
private theorem pr125959 : PrimeCertificate 125959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv2999]) (by decide +kernel)
def pv125959 : PrimeValue := ⟨125959, pr125959⟩
private theorem pr125963 : PrimeCertificate 125963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv62981]) (by decide +kernel)
def pv125963 : PrimeValue := ⟨125963, pr125963⟩
private theorem pr126001 : PrimeCertificate 126001 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv126001 : PrimeValue := ⟨126001, pr126001⟩
private theorem pr126011 : PrimeCertificate 126011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv12601]) (by decide +kernel)
def pv126011 : PrimeValue := ⟨126011, pr126011⟩
private theorem pr126013 : PrimeCertificate 126013 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv10501]) (by decide +kernel)
def pv126013 : PrimeValue := ⟨126013, pr126013⟩
private theorem pr126019 : PrimeCertificate 126019 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7001]) (by decide +kernel)
def pv126019 : PrimeValue := ⟨126019, pr126019⟩
private theorem pr126023 : PrimeCertificate 126023 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv37,pv131]) (by decide +kernel)
def pv126023 : PrimeValue := ⟨126023, pr126023⟩
private theorem pr126037 : PrimeCertificate 126037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv389]) (by decide +kernel)
def pv126037 : PrimeValue := ⟨126037, pr126037⟩
private theorem pr126041 : PrimeCertificate 126041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv137]) (by decide +kernel)
def pv126041 : PrimeValue := ⟨126041, pr126041⟩
private theorem pr126047 : PrimeCertificate 126047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv31,pv107]) (by decide +kernel)
def pv126047 : PrimeValue := ⟨126047, pr126047⟩
private theorem pr126067 : PrimeCertificate 126067 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv21011]) (by decide +kernel)
def pv126067 : PrimeValue := ⟨126067, pr126067⟩
private theorem pr126097 : PrimeCertificate 126097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv71]) (by decide +kernel)
def pv126097 : PrimeValue := ⟨126097, pr126097⟩
private theorem pr126107 : PrimeCertificate 126107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv3709]) (by decide +kernel)
def pv126107 : PrimeValue := ⟨126107, pr126107⟩
private theorem pr126131 : PrimeCertificate 126131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv12613]) (by decide +kernel)
def pv126131 : PrimeValue := ⟨126131, pr126131⟩
private theorem pr126143 : PrimeCertificate 126143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv59,pv1069]) (by decide +kernel)
def pv126143 : PrimeValue := ⟨126143, pr126143⟩
private theorem pr126151 : PrimeCertificate 126151 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv126151 : PrimeValue := ⟨126151, pr126151⟩
private theorem pr126173 : PrimeCertificate 126173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31543]) (by decide +kernel)
def pv126173 : PrimeValue := ⟨126173, pr126173⟩
private theorem pr126199 : PrimeCertificate 126199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv41]) (by decide +kernel)
def pv126199 : PrimeValue := ⟨126199, pr126199⟩
private theorem pr126211 : PrimeCertificate 126211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv601]) (by decide +kernel)
def pv126211 : PrimeValue := ⟨126211, pr126211⟩
private theorem pr126223 : PrimeCertificate 126223 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv109,pv193]) (by decide +kernel)
def pv126223 : PrimeValue := ⟨126223, pr126223⟩
private theorem pr126227 : PrimeCertificate 126227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv63113]) (by decide +kernel)
def pv126227 : PrimeValue := ⟨126227, pr126227⟩
private theorem pr126229 : PrimeCertificate 126229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv157]) (by decide +kernel)
def pv126229 : PrimeValue := ⟨126229, pr126229⟩
private theorem pr126233 : PrimeCertificate 126233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv509]) (by decide +kernel)
def pv126233 : PrimeValue := ⟨126233, pr126233⟩
private theorem pr126241 : PrimeCertificate 126241 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv263]) (by decide +kernel)
def pv126241 : PrimeValue := ⟨126241, pr126241⟩
private theorem pr126257 : PrimeCertificate 126257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv607]) (by decide +kernel)
def pv126257 : PrimeValue := ⟨126257, pr126257⟩
private theorem pr126271 : PrimeCertificate 126271 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv61]) (by decide +kernel)
def pv126271 : PrimeValue := ⟨126271, pr126271⟩
private theorem pr126307 : PrimeCertificate 126307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2339]) (by decide +kernel)
def pv126307 : PrimeValue := ⟨126307, pr126307⟩
private theorem pr126311 : PrimeCertificate 126311 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv17,pv743]) (by decide +kernel)
def pv126311 : PrimeValue := ⟨126311, pr126311⟩
private theorem pr126317 : PrimeCertificate 126317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv1373]) (by decide +kernel)
def pv126317 : PrimeValue := ⟨126317, pr126317⟩
private theorem pr126323 : PrimeCertificate 126323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1289]) (by decide +kernel)
def pv126323 : PrimeValue := ⟨126323, pr126323⟩
private theorem pr126337 : PrimeCertificate 126337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv47]) (by decide +kernel)
def pv126337 : PrimeValue := ⟨126337, pr126337⟩
private theorem pr126341 : PrimeCertificate 126341 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6317]) (by decide +kernel)
def pv126341 : PrimeValue := ⟨126341, pr126341⟩
private theorem pr126349 : PrimeCertificate 126349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10529]) (by decide +kernel)
def pv126349 : PrimeValue := ⟨126349, pr126349⟩
private theorem pr126359 : PrimeCertificate 126359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv63179]) (by decide +kernel)
def pv126359 : PrimeValue := ⟨126359, pr126359⟩
private theorem pr126397 : PrimeCertificate 126397 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3511]) (by decide +kernel)
def pv126397 : PrimeValue := ⟨126397, pr126397⟩
private theorem pr126421 : PrimeCertificate 126421 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv43]) (by decide +kernel)
def pv126421 : PrimeValue := ⟨126421, pr126421⟩
private theorem pr126433 : PrimeCertificate 126433 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv439]) (by decide +kernel)
def pv126433 : PrimeValue := ⟨126433, pr126433⟩
private theorem pr126443 : PrimeCertificate 126443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv191,pv331]) (by decide +kernel)
def pv126443 : PrimeValue := ⟨126443, pr126443⟩
private theorem pr126457 : PrimeCertificate 126457 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv479]) (by decide +kernel)
def pv126457 : PrimeValue := ⟨126457, pr126457⟩
private theorem pr126461 : PrimeCertificate 126461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6323]) (by decide +kernel)
def pv126461 : PrimeValue := ⟨126461, pr126461⟩
private theorem pr126481 : PrimeCertificate 126481 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv17,pv31]) (by decide +kernel)
def pv126481 : PrimeValue := ⟨126481, pr126481⟩
private theorem pr126487 : PrimeCertificate 126487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7027]) (by decide +kernel)
def pv126487 : PrimeValue := ⟨126487, pr126487⟩
private theorem pr126491 : PrimeCertificate 126491 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv139]) (by decide +kernel)
def pv126491 : PrimeValue := ⟨126491, pr126491⟩
private theorem pr126493 : PrimeCertificate 126493 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv83,pv127]) (by decide +kernel)
def pv126493 : PrimeValue := ⟨126493, pr126493⟩
private theorem pr126517 : PrimeCertificate 126517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv811]) (by decide +kernel)
def pv126517 : PrimeValue := ⟨126517, pr126517⟩
private theorem pr126547 : PrimeCertificate 126547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv131]) (by decide +kernel)
def pv126547 : PrimeValue := ⟨126547, pr126547⟩
private theorem pr126551 : PrimeCertificate 126551 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv2531]) (by decide +kernel)
def pv126551 : PrimeValue := ⟨126551, pr126551⟩
private theorem pr126583 : PrimeCertificate 126583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv73]) (by decide +kernel)
def pv126583 : PrimeValue := ⟨126583, pr126583⟩
private theorem pr126601 : PrimeCertificate 126601 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv211]) (by decide +kernel)
def pv126601 : PrimeValue := ⟨126601, pr126601⟩
private theorem pr126611 : PrimeCertificate 126611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1151]) (by decide +kernel)
def pv126611 : PrimeValue := ⟨126611, pr126611⟩
private theorem pr126613 : PrimeCertificate 126613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3517]) (by decide +kernel)
def pv126613 : PrimeValue := ⟨126613, pr126613⟩
private theorem pr126641 : PrimeCertificate 126641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1583]) (by decide +kernel)
def pv126641 : PrimeValue := ⟨126641, pr126641⟩
private theorem pr126653 : PrimeCertificate 126653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31663]) (by decide +kernel)
def pv126653 : PrimeValue := ⟨126653, pr126653⟩
private theorem pr126683 : PrimeCertificate 126683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv653]) (by decide +kernel)
def pv126683 : PrimeValue := ⟨126683, pr126683⟩
private theorem pr126691 : PrimeCertificate 126691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv41,pv103]) (by decide +kernel)
def pv126691 : PrimeValue := ⟨126691, pr126691⟩
private theorem pr126713 : PrimeCertificate 126713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv337]) (by decide +kernel)
def pv126713 : PrimeValue := ⟨126713, pr126713⟩
private theorem pr126719 : PrimeCertificate 126719 :=
  certifyPrime (q := pv13) (ls := [pv2,pv17,pv3727]) (by decide +kernel)
def pv126719 : PrimeValue := ⟨126719, pr126719⟩
private theorem pr126743 : PrimeCertificate 126743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv823]) (by decide +kernel)
def pv126743 : PrimeValue := ⟨126743, pr126743⟩
private theorem pr126751 : PrimeCertificate 126751 :=
  certifyPrime (q := pv61) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv126751 : PrimeValue := ⟨126751, pr126751⟩
private theorem pr126757 : PrimeCertificate 126757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv503]) (by decide +kernel)
def pv126757 : PrimeValue := ⟨126757, pr126757⟩
private theorem pr126761 : PrimeCertificate 126761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3169]) (by decide +kernel)
def pv126761 : PrimeValue := ⟨126761, pr126761⟩
private theorem pr126823 : PrimeCertificate 126823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv919]) (by decide +kernel)
def pv126823 : PrimeValue := ⟨126823, pr126823⟩
private theorem pr126827 : PrimeCertificate 126827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv9059]) (by decide +kernel)
def pv126827 : PrimeValue := ⟨126827, pr126827⟩
private theorem pr126839 : PrimeCertificate 126839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv63419]) (by decide +kernel)
def pv126839 : PrimeValue := ⟨126839, pr126839⟩
private theorem pr126851 : PrimeCertificate 126851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv59]) (by decide +kernel)
def pv126851 : PrimeValue := ⟨126851, pr126851⟩
private theorem pr126857 : PrimeCertificate 126857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101,pv157]) (by decide +kernel)
def pv126857 : PrimeValue := ⟨126857, pr126857⟩
private theorem pr126913 : PrimeCertificate 126913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv661]) (by decide +kernel)
def pv126913 : PrimeValue := ⟨126913, pr126913⟩
private theorem pr126923 : PrimeCertificate 126923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv3733]) (by decide +kernel)
def pv126923 : PrimeValue := ⟨126923, pr126923⟩
private theorem pr126943 : PrimeCertificate 126943 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv21157]) (by decide +kernel)
def pv126943 : PrimeValue := ⟨126943, pr126943⟩
private theorem pr126949 : PrimeCertificate 126949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv149]) (by decide +kernel)
def pv126949 : PrimeValue := ⟨126949, pr126949⟩
private theorem pr126967 : PrimeCertificate 126967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv3023]) (by decide +kernel)
def pv126967 : PrimeValue := ⟨126967, pr126967⟩
private theorem pr126989 : PrimeCertificate 126989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv599]) (by decide +kernel)
def pv126989 : PrimeValue := ⟨126989, pr126989⟩
private theorem pr127031 : PrimeCertificate 127031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv12703]) (by decide +kernel)
def pv127031 : PrimeValue := ⟨127031, pr127031⟩
private theorem pr127033 : PrimeCertificate 127033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv67,pv79]) (by decide +kernel)
def pv127033 : PrimeValue := ⟨127033, pr127033⟩
private theorem pr127051 : PrimeCertificate 127051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv127051 : PrimeValue := ⟨127051, pr127051⟩
private theorem pr127079 : PrimeCertificate 127079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv29,pv313]) (by decide +kernel)
def pv127079 : PrimeValue := ⟨127079, pr127079⟩
private theorem pr127103 : PrimeCertificate 127103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv103,pv617]) (by decide +kernel)
def pv127103 : PrimeValue := ⟨127103, pr127103⟩
private theorem pr127123 : PrimeCertificate 127123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv21187]) (by decide +kernel)
def pv127123 : PrimeValue := ⟨127123, pr127123⟩
private theorem pr127133 : PrimeCertificate 127133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv859]) (by decide +kernel)
def pv127133 : PrimeValue := ⟨127133, pr127133⟩
private theorem pr127139 : PrimeCertificate 127139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv5779]) (by decide +kernel)
def pv127139 : PrimeValue := ⟨127139, pr127139⟩
private theorem pr127157 : PrimeCertificate 127157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv383]) (by decide +kernel)
def pv127157 : PrimeValue := ⟨127157, pr127157⟩
private theorem pr127163 : PrimeCertificate 127163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv293]) (by decide +kernel)
def pv127163 : PrimeValue := ⟨127163, pr127163⟩
private theorem pr127189 : PrimeCertificate 127189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3533]) (by decide +kernel)
def pv127189 : PrimeValue := ⟨127189, pr127189⟩
private theorem pr127207 : PrimeCertificate 127207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv191]) (by decide +kernel)
def pv127207 : PrimeValue := ⟨127207, pr127207⟩
private theorem pr127217 : PrimeCertificate 127217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7951]) (by decide +kernel)
def pv127217 : PrimeValue := ⟨127217, pr127217⟩
private theorem pr127219 : PrimeCertificate 127219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv233]) (by decide +kernel)
def pv127219 : PrimeValue := ⟨127219, pr127219⟩
private theorem pr127241 : PrimeCertificate 127241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3181]) (by decide +kernel)
def pv127241 : PrimeValue := ⟨127241, pr127241⟩
private theorem pr127247 : PrimeCertificate 127247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv61,pv149]) (by decide +kernel)
def pv127247 : PrimeValue := ⟨127247, pr127247⟩
private theorem pr127261 : PrimeCertificate 127261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv101]) (by decide +kernel)
def pv127261 : PrimeValue := ⟨127261, pr127261⟩
private theorem pr127271 : PrimeCertificate 127271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv13,pv89]) (by decide +kernel)
def pv127271 : PrimeValue := ⟨127271, pr127271⟩
private theorem pr127277 : PrimeCertificate 127277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv677]) (by decide +kernel)
def pv127277 : PrimeValue := ⟨127277, pr127277⟩
private theorem pr127289 : PrimeCertificate 127289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2273]) (by decide +kernel)
def pv127289 : PrimeValue := ⟨127289, pr127289⟩
private theorem pr127291 : PrimeCertificate 127291 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv4243]) (by decide +kernel)
def pv127291 : PrimeValue := ⟨127291, pr127291⟩
private theorem pr127297 : PrimeCertificate 127297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv127297 : PrimeValue := ⟨127297, pr127297⟩
private theorem pr127301 : PrimeCertificate 127301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv67]) (by decide +kernel)
def pv127301 : PrimeValue := ⟨127301, pr127301⟩
private theorem pr127321 : PrimeCertificate 127321 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1061]) (by decide +kernel)
def pv127321 : PrimeValue := ⟨127321, pr127321⟩
private theorem pr127331 : PrimeCertificate 127331 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv17,pv107]) (by decide +kernel)
def pv127331 : PrimeValue := ⟨127331, pr127331⟩
private theorem pr127343 : PrimeCertificate 127343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv63671]) (by decide +kernel)
def pv127343 : PrimeValue := ⟨127343, pr127343⟩
private theorem pr127363 : PrimeCertificate 127363 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv21227]) (by decide +kernel)
def pv127363 : PrimeValue := ⟨127363, pr127363⟩
private theorem pr127373 : PrimeCertificate 127373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4549]) (by decide +kernel)
def pv127373 : PrimeValue := ⟨127373, pr127373⟩
private theorem pr127399 : PrimeCertificate 127399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv1249]) (by decide +kernel)
def pv127399 : PrimeValue := ⟨127399, pr127399⟩
private theorem pr127403 : PrimeCertificate 127403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv5791]) (by decide +kernel)
def pv127403 : PrimeValue := ⟨127403, pr127403⟩
private theorem pr127423 : PrimeCertificate 127423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7079]) (by decide +kernel)
def pv127423 : PrimeValue := ⟨127423, pr127423⟩
private theorem pr127447 : PrimeCertificate 127447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1931]) (by decide +kernel)
def pv127447 : PrimeValue := ⟨127447, pr127447⟩
private theorem pr127453 : PrimeCertificate 127453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv19,pv43]) (by decide +kernel)
def pv127453 : PrimeValue := ⟨127453, pr127453⟩
private theorem pr127481 : PrimeCertificate 127481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3187]) (by decide +kernel)
def pv127481 : PrimeValue := ⟨127481, pr127481⟩
private theorem pr127487 : PrimeCertificate 127487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv63743]) (by decide +kernel)
def pv127487 : PrimeValue := ⟨127487, pr127487⟩
private theorem pr127493 : PrimeCertificate 127493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31873]) (by decide +kernel)
def pv127493 : PrimeValue := ⟨127493, pr127493⟩
private theorem pr127507 : PrimeCertificate 127507 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv79,pv269]) (by decide +kernel)
def pv127507 : PrimeValue := ⟨127507, pr127507⟩
private theorem pr127529 : PrimeCertificate 127529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv839]) (by decide +kernel)
def pv127529 : PrimeValue := ⟨127529, pr127529⟩
private theorem pr127541 : PrimeCertificate 127541 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv911]) (by decide +kernel)
def pv127541 : PrimeValue := ⟨127541, pr127541⟩
private theorem pr127549 : PrimeCertificate 127549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1181]) (by decide +kernel)
def pv127549 : PrimeValue := ⟨127549, pr127549⟩
private theorem pr127579 : PrimeCertificate 127579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1933]) (by decide +kernel)
def pv127579 : PrimeValue := ⟨127579, pr127579⟩
private theorem pr127591 : PrimeCertificate 127591 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4253]) (by decide +kernel)
def pv127591 : PrimeValue := ⟨127591, pr127591⟩
private theorem pr127597 : PrimeCertificate 127597 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv127597 : PrimeValue := ⟨127597, pr127597⟩
private theorem pr127601 : PrimeCertificate 127601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv29]) (by decide +kernel)
def pv127601 : PrimeValue := ⟨127601, pr127601⟩
private theorem pr127609 : PrimeCertificate 127609 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv409]) (by decide +kernel)
def pv127609 : PrimeValue := ⟨127609, pr127609⟩
private theorem pr127637 : PrimeCertificate 127637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1877]) (by decide +kernel)
def pv127637 : PrimeValue := ⟨127637, pr127637⟩
private theorem pr127643 : PrimeCertificate 127643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv3359]) (by decide +kernel)
def pv127643 : PrimeValue := ⟨127643, pr127643⟩
private theorem pr127649 : PrimeCertificate 127649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3989]) (by decide +kernel)
def pv127649 : PrimeValue := ⟨127649, pr127649⟩
private theorem pr127657 : PrimeCertificate 127657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv197]) (by decide +kernel)
def pv127657 : PrimeValue := ⟨127657, pr127657⟩
private theorem pr127663 : PrimeCertificate 127663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv21277]) (by decide +kernel)
def pv127663 : PrimeValue := ⟨127663, pr127663⟩
private theorem pr127669 : PrimeCertificate 127669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10639]) (by decide +kernel)
def pv127669 : PrimeValue := ⟨127669, pr127669⟩
private theorem pr127679 : PrimeCertificate 127679 :=
  certifyPrime (q := pv13) (ls := [pv2,pv63839]) (by decide +kernel)
def pv127679 : PrimeValue := ⟨127679, pr127679⟩
private theorem pr127681 : PrimeCertificate 127681 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv127681 : PrimeValue := ⟨127681, pr127681⟩
private theorem pr127691 : PrimeCertificate 127691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv113]) (by decide +kernel)
def pv127691 : PrimeValue := ⟨127691, pr127691⟩
private theorem pr127709 : PrimeCertificate 127709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4561]) (by decide +kernel)
def pv127709 : PrimeValue := ⟨127709, pr127709⟩
private theorem pr127711 : PrimeCertificate 127711 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv43]) (by decide +kernel)
def pv127711 : PrimeValue := ⟨127711, pr127711⟩
private theorem pr127727 : PrimeCertificate 127727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv63863]) (by decide +kernel)
def pv127727 : PrimeValue := ⟨127727, pr127727⟩
private theorem pr127733 : PrimeCertificate 127733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2903]) (by decide +kernel)
def pv127733 : PrimeValue := ⟨127733, pr127733⟩
private theorem pr127739 : PrimeCertificate 127739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17]) (by decide +kernel)
def pv127739 : PrimeValue := ⟨127739, pr127739⟩
private theorem pr127747 : PrimeCertificate 127747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv151]) (by decide +kernel)
def pv127747 : PrimeValue := ⟨127747, pr127747⟩
private theorem pr127763 : PrimeCertificate 127763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv503]) (by decide +kernel)
def pv127763 : PrimeValue := ⟨127763, pr127763⟩
private theorem pr127781 : PrimeCertificate 127781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6389]) (by decide +kernel)
def pv127781 : PrimeValue := ⟨127781, pr127781⟩
private theorem pr127807 : PrimeCertificate 127807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv179]) (by decide +kernel)
def pv127807 : PrimeValue := ⟨127807, pr127807⟩
private theorem pr127817 : PrimeCertificate 127817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1229]) (by decide +kernel)
def pv127817 : PrimeValue := ⟨127817, pr127817⟩
private theorem pr127819 : PrimeCertificate 127819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv263]) (by decide +kernel)
def pv127819 : PrimeValue := ⟨127819, pr127819⟩
private theorem pr127837 : PrimeCertificate 127837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv67]) (by decide +kernel)
def pv127837 : PrimeValue := ⟨127837, pr127837⟩
private theorem pr127849 : PrimeCertificate 127849 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv761]) (by decide +kernel)
def pv127849 : PrimeValue := ⟨127849, pr127849⟩
private theorem pr127867 : PrimeCertificate 127867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv211]) (by decide +kernel)
def pv127867 : PrimeValue := ⟨127867, pr127867⟩
private theorem pr127873 : PrimeCertificate 127873 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv127873 : PrimeValue := ⟨127873, pr127873⟩
private theorem pr127877 : PrimeCertificate 127877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4567]) (by decide +kernel)
def pv127877 : PrimeValue := ⟨127877, pr127877⟩
private theorem pr127913 : PrimeCertificate 127913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv271]) (by decide +kernel)
def pv127913 : PrimeValue := ⟨127913, pr127913⟩
private theorem pr127921 : PrimeCertificate 127921 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv41]) (by decide +kernel)
def pv127921 : PrimeValue := ⟨127921, pr127921⟩
private theorem pr127931 : PrimeCertificate 127931 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv1163]) (by decide +kernel)
def pv127931 : PrimeValue := ⟨127931, pr127931⟩
private theorem pr127951 : PrimeCertificate 127951 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv853]) (by decide +kernel)
def pv127951 : PrimeValue := ⟨127951, pr127951⟩
private theorem pr127973 : PrimeCertificate 127973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv107]) (by decide +kernel)
def pv127973 : PrimeValue := ⟨127973, pr127973⟩
private theorem pr127979 : PrimeCertificate 127979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv1049]) (by decide +kernel)
def pv127979 : PrimeValue := ⟨127979, pr127979⟩
private theorem pr127997 : PrimeCertificate 127997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2909]) (by decide +kernel)
def pv127997 : PrimeValue := ⟨127997, pr127997⟩
private theorem pr128021 : PrimeCertificate 128021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv173]) (by decide +kernel)
def pv128021 : PrimeValue := ⟨128021, pr128021⟩
private theorem pr128033 : PrimeCertificate 128033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4001]) (by decide +kernel)
def pv128033 : PrimeValue := ⟨128033, pr128033⟩
private theorem pr128053 : PrimeCertificate 128053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3557]) (by decide +kernel)
def pv128053 : PrimeValue := ⟨128053, pr128053⟩
private theorem pr128099 : PrimeCertificate 128099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv3371]) (by decide +kernel)
def pv128099 : PrimeValue := ⟨128099, pr128099⟩
private theorem pr128113 : PrimeCertificate 128113 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv157]) (by decide +kernel)
def pv128113 : PrimeValue := ⟨128113, pr128113⟩
private theorem pr128119 : PrimeCertificate 128119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv131,pv163]) (by decide +kernel)
def pv128119 : PrimeValue := ⟨128119, pr128119⟩
private theorem pr128147 : PrimeCertificate 128147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv3769]) (by decide +kernel)
def pv128147 : PrimeValue := ⟨128147, pr128147⟩
private theorem pr128153 : PrimeCertificate 128153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv193]) (by decide +kernel)
def pv128153 : PrimeValue := ⟨128153, pr128153⟩
private theorem pr128159 : PrimeCertificate 128159 :=
  certifyPrime (q := pv11) (ls := [pv2,pv139,pv461]) (by decide +kernel)
def pv128159 : PrimeValue := ⟨128159, pr128159⟩
private theorem pr128173 : PrimeCertificate 128173 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv971]) (by decide +kernel)
def pv128173 : PrimeValue := ⟨128173, pr128173⟩
private theorem pr128189 : PrimeCertificate 128189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv439]) (by decide +kernel)
def pv128189 : PrimeValue := ⟨128189, pr128189⟩
private theorem pr128201 : PrimeCertificate 128201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv641]) (by decide +kernel)
def pv128201 : PrimeValue := ⟨128201, pr128201⟩
private theorem pr128203 : PrimeCertificate 128203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv929]) (by decide +kernel)
def pv128203 : PrimeValue := ⟨128203, pr128203⟩
private theorem pr128213 : PrimeCertificate 128213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv241]) (by decide +kernel)
def pv128213 : PrimeValue := ⟨128213, pr128213⟩
private theorem pr128221 : PrimeCertificate 128221 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv2137]) (by decide +kernel)
def pv128221 : PrimeValue := ⟨128221, pr128221⟩
private theorem pr128237 : PrimeCertificate 128237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32059]) (by decide +kernel)
def pv128237 : PrimeValue := ⟨128237, pr128237⟩
private theorem pr128257 : PrimeCertificate 128257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv167]) (by decide +kernel)
def pv128257 : PrimeValue := ⟨128257, pr128257⟩
private theorem pr128273 : PrimeCertificate 128273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8017]) (by decide +kernel)
def pv128273 : PrimeValue := ⟨128273, pr128273⟩
private theorem pr128287 : PrimeCertificate 128287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7127]) (by decide +kernel)
def pv128287 : PrimeValue := ⟨128287, pr128287⟩
private theorem pr128291 : PrimeCertificate 128291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv12829]) (by decide +kernel)
def pv128291 : PrimeValue := ⟨128291, pr128291⟩
private theorem pr128311 : PrimeCertificate 128311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv13,pv47]) (by decide +kernel)
def pv128311 : PrimeValue := ⟨128311, pr128311⟩
private theorem pr128321 : PrimeCertificate 128321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv401]) (by decide +kernel)
def pv128321 : PrimeValue := ⟨128321, pr128321⟩
private theorem pr128327 : PrimeCertificate 128327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv19,pv307]) (by decide +kernel)
def pv128327 : PrimeValue := ⟨128327, pr128327⟩
private theorem pr128341 : PrimeCertificate 128341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv31]) (by decide +kernel)
def pv128341 : PrimeValue := ⟨128341, pr128341⟩
private theorem pr128347 : PrimeCertificate 128347 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv21391]) (by decide +kernel)
def pv128347 : PrimeValue := ⟨128347, pr128347⟩
private theorem pr128377 : PrimeCertificate 128377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1783]) (by decide +kernel)
def pv128377 : PrimeValue := ⟨128377, pr128377⟩
private theorem pr128393 : PrimeCertificate 128393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1459]) (by decide +kernel)
def pv128393 : PrimeValue := ⟨128393, pr128393⟩
private theorem pr128399 : PrimeCertificate 128399 :=
  certifyPrime (q := pv13) (ls := [pv2,pv43,pv1493]) (by decide +kernel)
def pv128399 : PrimeValue := ⟨128399, pr128399⟩
private theorem pr128411 : PrimeCertificate 128411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv12841]) (by decide +kernel)
def pv128411 : PrimeValue := ⟨128411, pr128411⟩
private theorem pr128413 : PrimeCertificate 128413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv41]) (by decide +kernel)
def pv128413 : PrimeValue := ⟨128413, pr128413⟩
private theorem pr128431 : PrimeCertificate 128431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1427]) (by decide +kernel)
def pv128431 : PrimeValue := ⟨128431, pr128431⟩
private theorem pr128437 : PrimeCertificate 128437 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv139]) (by decide +kernel)
def pv128437 : PrimeValue := ⟨128437, pr128437⟩
private theorem pr128449 : PrimeCertificate 128449 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv223]) (by decide +kernel)
def pv128449 : PrimeValue := ⟨128449, pr128449⟩
private theorem pr128461 : PrimeCertificate 128461 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv2141]) (by decide +kernel)
def pv128461 : PrimeValue := ⟨128461, pr128461⟩
private theorem pr128467 : PrimeCertificate 128467 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv61]) (by decide +kernel)
def pv128467 : PrimeValue := ⟨128467, pr128467⟩
private theorem pr128473 : PrimeCertificate 128473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv101]) (by decide +kernel)
def pv128473 : PrimeValue := ⟨128473, pr128473⟩
private theorem pr128477 : PrimeCertificate 128477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32119]) (by decide +kernel)
def pv128477 : PrimeValue := ⟨128477, pr128477⟩
private theorem pr128483 : PrimeCertificate 128483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv283]) (by decide +kernel)
def pv128483 : PrimeValue := ⟨128483, pr128483⟩
private theorem pr128489 : PrimeCertificate 128489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16061]) (by decide +kernel)
def pv128489 : PrimeValue := ⟨128489, pr128489⟩
private theorem pr128509 : PrimeCertificate 128509 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv10709]) (by decide +kernel)
def pv128509 : PrimeValue := ⟨128509, pr128509⟩
private theorem pr128521 : PrimeCertificate 128521 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv128521 : PrimeValue := ⟨128521, pr128521⟩
private theorem pr128549 : PrimeCertificate 128549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4591]) (by decide +kernel)
def pv128549 : PrimeValue := ⟨128549, pr128549⟩
private theorem pr128551 : PrimeCertificate 128551 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv857]) (by decide +kernel)
def pv128551 : PrimeValue := ⟨128551, pr128551⟩
private theorem pr128563 : PrimeCertificate 128563 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv3061]) (by decide +kernel)
def pv128563 : PrimeValue := ⟨128563, pr128563⟩
private theorem pr128603 : PrimeCertificate 128603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv64301]) (by decide +kernel)
def pv128603 : PrimeValue := ⟨128603, pr128603⟩
private theorem pr128621 : PrimeCertificate 128621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv109]) (by decide +kernel)
def pv128621 : PrimeValue := ⟨128621, pr128621⟩
private theorem pr128629 : PrimeCertificate 128629 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv397]) (by decide +kernel)
def pv128629 : PrimeValue := ⟨128629, pr128629⟩
private theorem pr128657 : PrimeCertificate 128657 :=
  certifyPrime (q := pv19) (ls := [pv2,pv11,pv17,pv43]) (by decide +kernel)
def pv128657 : PrimeValue := ⟨128657, pr128657⟩
private theorem pr128659 : PrimeCertificate 128659 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv41,pv523]) (by decide +kernel)
def pv128659 : PrimeValue := ⟨128659, pr128659⟩
private theorem pr128663 : PrimeCertificate 128663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv2797]) (by decide +kernel)
def pv128663 : PrimeValue := ⟨128663, pr128663⟩
private theorem pr128669 : PrimeCertificate 128669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv1693]) (by decide +kernel)
def pv128669 : PrimeValue := ⟨128669, pr128669⟩
private theorem pr128683 : PrimeCertificate 128683 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2383]) (by decide +kernel)
def pv128683 : PrimeValue := ⟨128683, pr128683⟩
private theorem pr128693 : PrimeCertificate 128693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32173]) (by decide +kernel)
def pv128693 : PrimeValue := ⟨128693, pr128693⟩
private theorem pr128717 : PrimeCertificate 128717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4597]) (by decide +kernel)
def pv128717 : PrimeValue := ⟨128717, pr128717⟩
private theorem pr128747 : PrimeCertificate 128747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv64373]) (by decide +kernel)
def pv128747 : PrimeValue := ⟨128747, pr128747⟩
private theorem pr128749 : PrimeCertificate 128749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10729]) (by decide +kernel)
def pv128749 : PrimeValue := ⟨128749, pr128749⟩
private theorem pr128761 : PrimeCertificate 128761 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv5,pv29,pv37]) (by decide +kernel)
def pv128761 : PrimeValue := ⟨128761, pr128761⟩
private theorem pr128767 : PrimeCertificate 128767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1951]) (by decide +kernel)
def pv128767 : PrimeValue := ⟨128767, pr128767⟩
private theorem pr128813 : PrimeCertificate 128813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32203]) (by decide +kernel)
def pv128813 : PrimeValue := ⟨128813, pr128813⟩
private theorem pr128819 : PrimeCertificate 128819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv2221]) (by decide +kernel)
def pv128819 : PrimeValue := ⟨128819, pr128819⟩
private theorem pr128831 : PrimeCertificate 128831 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv991]) (by decide +kernel)
def pv128831 : PrimeValue := ⟨128831, pr128831⟩
private theorem pr128837 : PrimeCertificate 128837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1039]) (by decide +kernel)
def pv128837 : PrimeValue := ⟨128837, pr128837⟩
private theorem pr128857 : PrimeCertificate 128857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv59]) (by decide +kernel)
def pv128857 : PrimeValue := ⟨128857, pr128857⟩
private theorem pr128861 : PrimeCertificate 128861 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv379]) (by decide +kernel)
def pv128861 : PrimeValue := ⟨128861, pr128861⟩
private theorem pr128873 : PrimeCertificate 128873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv181]) (by decide +kernel)
def pv128873 : PrimeValue := ⟨128873, pr128873⟩
private theorem pr128879 : PrimeCertificate 128879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv64439]) (by decide +kernel)
def pv128879 : PrimeValue := ⟨128879, pr128879⟩
private theorem pr128903 : PrimeCertificate 128903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv64451]) (by decide +kernel)
def pv128903 : PrimeValue := ⟨128903, pr128903⟩
private theorem pr128923 : PrimeCertificate 128923 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv21487]) (by decide +kernel)
def pv128923 : PrimeValue := ⟨128923, pr128923⟩
private theorem pr128939 : PrimeCertificate 128939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2803]) (by decide +kernel)
def pv128939 : PrimeValue := ⟨128939, pr128939⟩
private theorem pr128941 : PrimeCertificate 128941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv307]) (by decide +kernel)
def pv128941 : PrimeValue := ⟨128941, pr128941⟩
private theorem pr128951 : PrimeCertificate 128951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv2579]) (by decide +kernel)
def pv128951 : PrimeValue := ⟨128951, pr128951⟩
private theorem pr128969 : PrimeCertificate 128969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv47]) (by decide +kernel)
def pv128969 : PrimeValue := ⟨128969, pr128969⟩
private theorem pr128971 : PrimeCertificate 128971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1433]) (by decide +kernel)
def pv128971 : PrimeValue := ⟨128971, pr128971⟩
private theorem pr128981 : PrimeCertificate 128981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6449]) (by decide +kernel)
def pv128981 : PrimeValue := ⟨128981, pr128981⟩
private theorem pr128983 : PrimeCertificate 128983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv37,pv83]) (by decide +kernel)
def pv128983 : PrimeValue := ⟨128983, pr128983⟩
private theorem pr128987 : PrimeCertificate 128987 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv41]) (by decide +kernel)
def pv128987 : PrimeValue := ⟨128987, pr128987⟩
private theorem pr128993 : PrimeCertificate 128993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv139]) (by decide +kernel)
def pv128993 : PrimeValue := ⟨128993, pr128993⟩
private theorem pr129001 : PrimeCertificate 129001 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv129001 : PrimeValue := ⟨129001, pr129001⟩
private theorem pr129011 : PrimeCertificate 129011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv97]) (by decide +kernel)
def pv129011 : PrimeValue := ⟨129011, pr129011⟩
private theorem pr129023 : PrimeCertificate 129023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv2081]) (by decide +kernel)
def pv129023 : PrimeValue := ⟨129023, pr129023⟩
private theorem pr129037 : PrimeCertificate 129037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10753]) (by decide +kernel)
def pv129037 : PrimeValue := ⟨129037, pr129037⟩
private theorem pr129049 : PrimeCertificate 129049 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv283]) (by decide +kernel)
def pv129049 : PrimeValue := ⟨129049, pr129049⟩
private theorem pr129061 : PrimeCertificate 129061 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv239]) (by decide +kernel)
def pv129061 : PrimeValue := ⟨129061, pr129061⟩
private theorem pr129083 : PrimeCertificate 129083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv233,pv277]) (by decide +kernel)
def pv129083 : PrimeValue := ⟨129083, pr129083⟩
private theorem pr129097 : PrimeCertificate 129097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv163]) (by decide +kernel)
def pv129097 : PrimeValue := ⟨129097, pr129097⟩
private theorem pr129113 : PrimeCertificate 129113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16139]) (by decide +kernel)
def pv129113 : PrimeValue := ⟨129113, pr129113⟩
private theorem pr129119 : PrimeCertificate 129119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv5869]) (by decide +kernel)
def pv129119 : PrimeValue := ⟨129119, pr129119⟩
private theorem pr129121 : PrimeCertificate 129121 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv269]) (by decide +kernel)
def pv129121 : PrimeValue := ⟨129121, pr129121⟩
private theorem pr129127 : PrimeCertificate 129127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv21521]) (by decide +kernel)
def pv129127 : PrimeValue := ⟨129127, pr129127⟩
private theorem pr129169 : PrimeCertificate 129169 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv23]) (by decide +kernel)
def pv129169 : PrimeValue := ⟨129169, pr129169⟩
private theorem pr129187 : PrimeCertificate 129187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7177]) (by decide +kernel)
def pv129187 : PrimeValue := ⟨129187, pr129187⟩
private theorem pr129193 : PrimeCertificate 129193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv769]) (by decide +kernel)
def pv129193 : PrimeValue := ⟨129193, pr129193⟩
private theorem pr129209 : PrimeCertificate 129209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv521]) (by decide +kernel)
def pv129209 : PrimeValue := ⟨129209, pr129209⟩
private theorem pr129221 : PrimeCertificate 129221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv71]) (by decide +kernel)
def pv129221 : PrimeValue := ⟨129221, pr129221⟩
private theorem pr129223 : PrimeCertificate 129223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2393]) (by decide +kernel)
def pv129223 : PrimeValue := ⟨129223, pr129223⟩
private theorem pr129229 : PrimeCertificate 129229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv89]) (by decide +kernel)
def pv129229 : PrimeValue := ⟨129229, pr129229⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
