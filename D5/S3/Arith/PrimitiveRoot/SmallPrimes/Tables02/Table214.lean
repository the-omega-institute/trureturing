/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table214
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table214.pv782497
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table047
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table098

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr782497 : PrimeCertificate 782497 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv11,pv13,pv19]) (by decide +kernel)
def pv782497 : PrimeValue := ⟨782497, pr782497⟩
private theorem pr782581 : PrimeCertificate 782581 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13043]) (by decide +kernel)
def pv782581 : PrimeValue := ⟨782581, pr782581⟩
private theorem pr782723 : PrimeCertificate 782723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv229,pv1709]) (by decide +kernel)
def pv782723 : PrimeValue := ⟨782723, pr782723⟩
private theorem pr782891 : PrimeCertificate 782891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv79,pv991]) (by decide +kernel)
def pv782891 : PrimeValue := ⟨782891, pr782891⟩
private theorem pr782911 : PrimeCertificate 782911 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv8699]) (by decide +kernel)
def pv782911 : PrimeValue := ⟨782911, pr782911⟩
private theorem pr782921 : PrimeCertificate 782921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv37]) (by decide +kernel)
def pv782921 : PrimeValue := ⟨782921, pr782921⟩
private theorem pr783043 : PrimeCertificate 783043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv10039]) (by decide +kernel)
def pv783043 : PrimeValue := ⟨783043, pr783043⟩
private theorem pr783191 : PrimeCertificate 783191 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv271]) (by decide +kernel)
def pv783191 : PrimeValue := ⟨783191, pr783191⟩
private theorem pr783193 : PrimeCertificate 783193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv32633]) (by decide +kernel)
def pv783193 : PrimeValue := ⟨783193, pr783193⟩
private theorem pr783197 : PrimeCertificate 783197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv8513]) (by decide +kernel)
def pv783197 : PrimeValue := ⟨783197, pr783197⟩
private theorem pr783337 : PrimeCertificate 783337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv127,pv257]) (by decide +kernel)
def pv783337 : PrimeValue := ⟨783337, pr783337⟩
private theorem pr783361 : PrimeCertificate 783361 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv783361 : PrimeValue := ⟨783361, pr783361⟩
private theorem pr783557 : PrimeCertificate 783557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv71,pv89]) (by decide +kernel)
def pv783557 : PrimeValue := ⟨783557, pr783557⟩
private theorem pr783647 : PrimeCertificate 783647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv391823]) (by decide +kernel)
def pv783647 : PrimeValue := ⟨783647, pr783647⟩
private theorem pr783701 : PrimeCertificate 783701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv461]) (by decide +kernel)
def pv783701 : PrimeValue := ⟨783701, pr783701⟩
private theorem pr783787 : PrimeCertificate 783787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv130631]) (by decide +kernel)
def pv783787 : PrimeValue := ⟨783787, pr783787⟩
private theorem pr783877 : PrimeCertificate 783877 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv65323]) (by decide +kernel)
def pv783877 : PrimeValue := ⟨783877, pr783877⟩
private theorem pr784081 : PrimeCertificate 784081 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv784081 : PrimeValue := ⟨784081, pr784081⟩
private theorem pr784153 : PrimeCertificate 784153 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv10891]) (by decide +kernel)
def pv784153 : PrimeValue := ⟨784153, pr784153⟩
private theorem pr784283 : PrimeCertificate 784283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv20639]) (by decide +kernel)
def pv784283 : PrimeValue := ⟨784283, pr784283⟩
private theorem pr784423 : PrimeCertificate 784423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43579]) (by decide +kernel)
def pv784423 : PrimeValue := ⟨784423, pr784423⟩
private theorem pr784471 : PrimeCertificate 784471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv79,pv331]) (by decide +kernel)
def pv784471 : PrimeValue := ⟨784471, pr784471⟩
private theorem pr784501 : PrimeCertificate 784501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv523]) (by decide +kernel)
def pv784501 : PrimeValue := ⟨784501, pr784501⟩
private theorem pr784541 : PrimeCertificate 784541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv39227]) (by decide +kernel)
def pv784541 : PrimeValue := ⟨784541, pr784541⟩
private theorem pr784583 : PrimeCertificate 784583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv59,pv61,pv109]) (by decide +kernel)
def pv784583 : PrimeValue := ⟨784583, pr784583⟩
private theorem pr784697 : PrimeCertificate 784697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv37,pv241]) (by decide +kernel)
def pv784697 : PrimeValue := ⟨784697, pr784697⟩
private theorem pr784913 : PrimeCertificate 784913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv49057]) (by decide +kernel)
def pv784913 : PrimeValue := ⟨784913, pr784913⟩
private theorem pr785053 : PrimeCertificate 785053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2423]) (by decide +kernel)
def pv785053 : PrimeValue := ⟨785053, pr785053⟩
private theorem pr785153 : PrimeCertificate 785153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3067]) (by decide +kernel)
def pv785153 : PrimeValue := ⟨785153, pr785153⟩
private theorem pr785353 : PrimeCertificate 785353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv761]) (by decide +kernel)
def pv785353 : PrimeValue := ⟨785353, pr785353⟩
private theorem pr785413 : PrimeCertificate 785413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv21817]) (by decide +kernel)
def pv785413 : PrimeValue := ⟨785413, pr785413⟩
private theorem pr785573 : PrimeCertificate 785573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv277,pv709]) (by decide +kernel)
def pv785573 : PrimeValue := ⟨785573, pr785573⟩
private theorem pr785753 : PrimeCertificate 785753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv8929]) (by decide +kernel)
def pv785753 : PrimeValue := ⟨785753, pr785753⟩
private theorem pr785773 : PrimeCertificate 785773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv23,pv73]) (by decide +kernel)
def pv785773 : PrimeValue := ⟨785773, pr785773⟩
private theorem pr785803 : PrimeCertificate 785803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv61,pv113]) (by decide +kernel)
def pv785803 : PrimeValue := ⟨785803, pr785803⟩
private theorem pr785861 : PrimeCertificate 785861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv39293]) (by decide +kernel)
def pv785861 : PrimeValue := ⟨785861, pr785861⟩
private theorem pr785951 : PrimeCertificate 785951 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv1429]) (by decide +kernel)
def pv785951 : PrimeValue := ⟨785951, pr785951⟩
private theorem pr786001 : PrimeCertificate 786001 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv131]) (by decide +kernel)
def pv786001 : PrimeValue := ⟨786001, pr786001⟩
private theorem pr786053 : PrimeCertificate 786053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv4793]) (by decide +kernel)
def pv786053 : PrimeValue := ⟨786053, pr786053⟩
private theorem pr786061 : PrimeCertificate 786061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv397]) (by decide +kernel)
def pv786061 : PrimeValue := ⟨786061, pr786061⟩
private theorem pr786173 : PrimeCertificate 786173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv196543]) (by decide +kernel)
def pv786173 : PrimeValue := ⟨786173, pr786173⟩
private theorem pr786197 : PrimeCertificate 786197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv196549]) (by decide +kernel)
def pv786197 : PrimeValue := ⟨786197, pr786197⟩
private theorem pr786407 : PrimeCertificate 786407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv393203]) (by decide +kernel)
def pv786407 : PrimeValue := ⟨786407, pr786407⟩
private theorem pr786491 : PrimeCertificate 786491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv78649]) (by decide +kernel)
def pv786491 : PrimeValue := ⟨786491, pr786491⟩
private theorem pr786551 : PrimeCertificate 786551 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv15731]) (by decide +kernel)
def pv786551 : PrimeValue := ⟨786551, pr786551⟩
private theorem pr786613 : PrimeCertificate 786613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv65551]) (by decide +kernel)
def pv786613 : PrimeValue := ⟨786613, pr786613⟩
private theorem pr786673 : PrimeCertificate 786673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv607]) (by decide +kernel)
def pv786673 : PrimeValue := ⟨786673, pr786673⟩
private theorem pr786691 : PrimeCertificate 786691 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv8741]) (by decide +kernel)
def pv786691 : PrimeValue := ⟨786691, pr786691⟩
private theorem pr786887 : PrimeCertificate 786887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv13567]) (by decide +kernel)
def pv786887 : PrimeValue := ⟨786887, pr786887⟩
private theorem pr786901 : PrimeCertificate 786901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv43,pv61]) (by decide +kernel)
def pv786901 : PrimeValue := ⟨786901, pr786901⟩
private theorem pr787057 : PrimeCertificate 787057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv863]) (by decide +kernel)
def pv787057 : PrimeValue := ⟨787057, pr787057⟩
private theorem pr787091 : PrimeCertificate 787091 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv31,pv2539]) (by decide +kernel)
def pv787091 : PrimeValue := ⟨787091, pr787091⟩
private theorem pr787153 : PrimeCertificate 787153 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv31]) (by decide +kernel)
def pv787153 : PrimeValue := ⟨787153, pr787153⟩
private theorem pr787331 : PrimeCertificate 787331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv1831]) (by decide +kernel)
def pv787331 : PrimeValue := ⟨787331, pr787331⟩
private theorem pr787537 : PrimeCertificate 787537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1823]) (by decide +kernel)
def pv787537 : PrimeValue := ⟨787537, pr787537⟩
private theorem pr787547 : PrimeCertificate 787547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv449,pv877]) (by decide +kernel)
def pv787547 : PrimeValue := ⟨787547, pr787547⟩
private theorem pr787601 : PrimeCertificate 787601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv179]) (by decide +kernel)
def pv787601 : PrimeValue := ⟨787601, pr787601⟩
private theorem pr787621 : PrimeCertificate 787621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13127]) (by decide +kernel)
def pv787621 : PrimeValue := ⟨787621, pr787621⟩
private theorem pr787747 : PrimeCertificate 787747 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv7723]) (by decide +kernel)
def pv787747 : PrimeValue := ⟨787747, pr787747⟩
private theorem pr787757 : PrimeCertificate 787757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv6791]) (by decide +kernel)
def pv787757 : PrimeValue := ⟨787757, pr787757⟩
private theorem pr787793 : PrimeCertificate 787793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv929]) (by decide +kernel)
def pv787793 : PrimeValue := ⟨787793, pr787793⟩
private theorem pr788261 : PrimeCertificate 788261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv3583]) (by decide +kernel)
def pv788261 : PrimeValue := ⟨788261, pr788261⟩
private theorem pr788267 : PrimeCertificate 788267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv9613]) (by decide +kernel)
def pv788267 : PrimeValue := ⟨788267, pr788267⟩
private theorem pr788317 : PrimeCertificate 788317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv179,pv367]) (by decide +kernel)
def pv788317 : PrimeValue := ⟨788317, pr788317⟩
private theorem pr788363 : PrimeCertificate 788363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv89,pv103]) (by decide +kernel)
def pv788363 : PrimeValue := ⟨788363, pr788363⟩
private theorem pr788393 : PrimeCertificate 788393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17,pv31]) (by decide +kernel)
def pv788393 : PrimeValue := ⟨788393, pr788393⟩
private theorem pr788527 : PrimeCertificate 788527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv617]) (by decide +kernel)
def pv788527 : PrimeValue := ⟨788527, pr788527⟩
private theorem pr788561 : PrimeCertificate 788561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv9857]) (by decide +kernel)
def pv788561 : PrimeValue := ⟨788561, pr788561⟩
private theorem pr788651 : PrimeCertificate 788651 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv15773]) (by decide +kernel)
def pv788651 : PrimeValue := ⟨788651, pr788651⟩
private theorem pr788867 : PrimeCertificate 788867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv30341]) (by decide +kernel)
def pv788867 : PrimeValue := ⟨788867, pr788867⟩
private theorem pr788891 : PrimeCertificate 788891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv78889]) (by decide +kernel)
def pv788891 : PrimeValue := ⟨788891, pr788891⟩
private theorem pr788903 : PrimeCertificate 788903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv23203]) (by decide +kernel)
def pv788903 : PrimeValue := ⟨788903, pr788903⟩
private theorem pr788927 : PrimeCertificate 788927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv433,pv911]) (by decide +kernel)
def pv788927 : PrimeValue := ⟨788927, pr788927⟩
private theorem pr788941 : PrimeCertificate 788941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv487]) (by decide +kernel)
def pv788941 : PrimeValue := ⟨788941, pr788941⟩
private theorem pr789077 : PrimeCertificate 789077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197269]) (by decide +kernel)
def pv789077 : PrimeValue := ⟨789077, pr789077⟩
private theorem pr789091 : PrimeCertificate 789091 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv5,pv29,pv907]) (by decide +kernel)
def pv789091 : PrimeValue := ⟨789091, pr789091⟩
private theorem pr789121 : PrimeCertificate 789121 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv137]) (by decide +kernel)
def pv789121 : PrimeValue := ⟨789121, pr789121⟩
private theorem pr789227 : PrimeCertificate 789227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv2281]) (by decide +kernel)
def pv789227 : PrimeValue := ⟨789227, pr789227⟩
private theorem pr789311 : PrimeCertificate 789311 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv17,pv4643]) (by decide +kernel)
def pv789311 : PrimeValue := ⟨789311, pr789311⟩
private theorem pr789331 : PrimeCertificate 789331 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv83,pv317]) (by decide +kernel)
def pv789331 : PrimeValue := ⟨789331, pr789331⟩
private theorem pr789473 : PrimeCertificate 789473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv24671]) (by decide +kernel)
def pv789473 : PrimeValue := ⟨789473, pr789473⟩
private theorem pr789527 : PrimeCertificate 789527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv79,pv263]) (by decide +kernel)
def pv789527 : PrimeValue := ⟨789527, pr789527⟩
private theorem pr789631 : PrimeCertificate 789631 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv26321]) (by decide +kernel)
def pv789631 : PrimeValue := ⟨789631, pr789631⟩
private theorem pr789857 : PrimeCertificate 789857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv24683]) (by decide +kernel)
def pv789857 : PrimeValue := ⟨789857, pr789857⟩
private theorem pr789967 : PrimeCertificate 789967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv14629]) (by decide +kernel)
def pv789967 : PrimeValue := ⟨789967, pr789967⟩
private theorem pr790033 : PrimeCertificate 790033 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv109,pv151]) (by decide +kernel)
def pv790033 : PrimeValue := ⟨790033, pr790033⟩
private theorem pr790087 : PrimeCertificate 790087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv11971]) (by decide +kernel)
def pv790087 : PrimeValue := ⟨790087, pr790087⟩
private theorem pr790093 : PrimeCertificate 790093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv1291]) (by decide +kernel)
def pv790093 : PrimeValue := ⟨790093, pr790093⟩
private theorem pr790121 : PrimeCertificate 790121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19753]) (by decide +kernel)
def pv790121 : PrimeValue := ⟨790121, pr790121⟩
private theorem pr790201 : PrimeCertificate 790201 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv439]) (by decide +kernel)
def pv790201 : PrimeValue := ⟨790201, pr790201⟩
private theorem pr790291 : PrimeCertificate 790291 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv2927]) (by decide +kernel)
def pv790291 : PrimeValue := ⟨790291, pr790291⟩
private theorem pr790351 : PrimeCertificate 790351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv479]) (by decide +kernel)
def pv790351 : PrimeValue := ⟨790351, pr790351⟩
private theorem pr790397 : PrimeCertificate 790397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197599]) (by decide +kernel)
def pv790397 : PrimeValue := ⟨790397, pr790397⟩
private theorem pr790451 : PrimeCertificate 790451 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv15809]) (by decide +kernel)
def pv790451 : PrimeValue := ⟨790451, pr790451⟩
private theorem pr790481 : PrimeCertificate 790481 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv41,pv241]) (by decide +kernel)
def pv790481 : PrimeValue := ⟨790481, pr790481⟩
private theorem pr790501 : PrimeCertificate 790501 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv31]) (by decide +kernel)
def pv790501 : PrimeValue := ⟨790501, pr790501⟩
private theorem pr790523 : PrimeCertificate 790523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv395261]) (by decide +kernel)
def pv790523 : PrimeValue := ⟨790523, pr790523⟩
private theorem pr790547 : PrimeCertificate 790547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv395273]) (by decide +kernel)
def pv790547 : PrimeValue := ⟨790547, pr790547⟩
private theorem pr790697 : PrimeCertificate 790697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv98837]) (by decide +kernel)
def pv790697 : PrimeValue := ⟨790697, pr790697⟩
private theorem pr790703 : PrimeCertificate 790703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv127,pv283]) (by decide +kernel)
def pv790703 : PrimeValue := ⟨790703, pr790703⟩
private theorem pr790957 : PrimeCertificate 790957 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv127,pv173]) (by decide +kernel)
def pv790957 : PrimeValue := ⟨790957, pr790957⟩
private theorem pr791093 : PrimeCertificate 791093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197773]) (by decide +kernel)
def pv791093 : PrimeValue := ⟨791093, pr791093⟩
private theorem pr791111 : PrimeCertificate 791111 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv79111]) (by decide +kernel)
def pv791111 : PrimeValue := ⟨791111, pr791111⟩
private theorem pr791321 : PrimeCertificate 791321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv73,pv271]) (by decide +kernel)
def pv791321 : PrimeValue := ⟨791321, pr791321⟩
private theorem pr791411 : PrimeCertificate 791411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv2729]) (by decide +kernel)
def pv791411 : PrimeValue := ⟨791411, pr791411⟩
private theorem pr791431 : PrimeCertificate 791431 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv23,pv31,pv37]) (by decide +kernel)
def pv791431 : PrimeValue := ⟨791431, pr791431⟩
private theorem pr791447 : PrimeCertificate 791447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv307,pv1289]) (by decide +kernel)
def pv791447 : PrimeValue := ⟨791447, pr791447⟩
private theorem pr791627 : PrimeCertificate 791627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv35983]) (by decide +kernel)
def pv791627 : PrimeValue := ⟨791627, pr791627⟩
private theorem pr791677 : PrimeCertificate 791677 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv21991]) (by decide +kernel)
def pv791677 : PrimeValue := ⟨791677, pr791677⟩
private theorem pr791773 : PrimeCertificate 791773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv65981]) (by decide +kernel)
def pv791773 : PrimeValue := ⟨791773, pr791773⟩
private theorem pr791783 : PrimeCertificate 791783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv395891]) (by decide +kernel)
def pv791783 : PrimeValue := ⟨791783, pr791783⟩
private theorem pr791803 : PrimeCertificate 791803 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv31,pv43]) (by decide +kernel)
def pv791803 : PrimeValue := ⟨791803, pr791803⟩
private theorem pr792257 : PrimeCertificate 792257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12379]) (by decide +kernel)
def pv792257 : PrimeValue := ⟨792257, pr792257⟩
private theorem pr792593 : PrimeCertificate 792593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv49537]) (by decide +kernel)
def pv792593 : PrimeValue := ⟨792593, pr792593⟩
private theorem pr792697 : PrimeCertificate 792697 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv33029]) (by decide +kernel)
def pv792697 : PrimeValue := ⟨792697, pr792697⟩
private theorem pr792893 : PrimeCertificate 792893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv198223]) (by decide +kernel)
def pv792893 : PrimeValue := ⟨792893, pr792893⟩
private theorem pr792941 : PrimeCertificate 792941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv967]) (by decide +kernel)
def pv792941 : PrimeValue := ⟨792941, pr792941⟩
private theorem pr793103 : PrimeCertificate 793103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv257,pv1543]) (by decide +kernel)
def pv793103 : PrimeValue := ⟨793103, pr793103⟩
private theorem pr793187 : PrimeCertificate 793187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv41,pv569]) (by decide +kernel)
def pv793187 : PrimeValue := ⟨793187, pr793187⟩
private theorem pr793337 : PrimeCertificate 793337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv131,pv757]) (by decide +kernel)
def pv793337 : PrimeValue := ⟨793337, pr793337⟩
private theorem pr793537 : PrimeCertificate 793537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4133]) (by decide +kernel)
def pv793537 : PrimeValue := ⟨793537, pr793537⟩
private theorem pr793547 : PrimeCertificate 793547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv1327]) (by decide +kernel)
def pv793547 : PrimeValue := ⟨793547, pr793547⟩
private theorem pr793553 : PrimeCertificate 793553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv49597]) (by decide +kernel)
def pv793553 : PrimeValue := ⟨793553, pr793553⟩
private theorem pr793607 : PrimeCertificate 793607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv36073]) (by decide +kernel)
def pv793607 : PrimeValue := ⟨793607, pr793607⟩
private theorem pr793621 : PrimeCertificate 793621 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv4409]) (by decide +kernel)
def pv793621 : PrimeValue := ⟨793621, pr793621⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
