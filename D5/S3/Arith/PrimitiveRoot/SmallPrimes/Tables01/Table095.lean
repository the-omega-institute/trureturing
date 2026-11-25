/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table095
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table095.pv364801
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table061
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table062

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr364801 : PrimeCertificate 364801 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv364801 : PrimeValue := ⟨364801, pr364801⟩
private theorem pr364879 : PrimeCertificate 364879 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29,pv233]) (by decide +kernel)
def pv364879 : PrimeValue := ⟨364879, pr364879⟩
private theorem pr364919 : PrimeCertificate 364919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv23,pv7933]) (by decide +kernel)
def pv364919 : PrimeValue := ⟨364919, pr364919⟩
private theorem pr364961 : PrimeCertificate 364961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2281]) (by decide +kernel)
def pv364961 : PrimeValue := ⟨364961, pr364961⟩
private theorem pr365017 : PrimeCertificate 365017 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv67,pv227]) (by decide +kernel)
def pv365017 : PrimeValue := ⟨365017, pr365017⟩
private theorem pr365069 : PrimeCertificate 365069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv8297]) (by decide +kernel)
def pv365069 : PrimeValue := ⟨365069, pr365069⟩
private theorem pr365107 : PrimeCertificate 365107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv8693]) (by decide +kernel)
def pv365107 : PrimeValue := ⟨365107, pr365107⟩
private theorem pr365137 : PrimeCertificate 365137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7607]) (by decide +kernel)
def pv365137 : PrimeValue := ⟨365137, pr365137⟩
private theorem pr365159 : PrimeCertificate 365159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv182579]) (by decide +kernel)
def pv365159 : PrimeValue := ⟨365159, pr365159⟩
private theorem pr365251 : PrimeCertificate 365251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv487]) (by decide +kernel)
def pv365251 : PrimeValue := ⟨365251, pr365251⟩
private theorem pr365357 : PrimeCertificate 365357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv241,pv379]) (by decide +kernel)
def pv365357 : PrimeValue := ⟨365357, pr365357⟩
private theorem pr365411 : PrimeCertificate 365411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv36541]) (by decide +kernel)
def pv365411 : PrimeValue := ⟨365411, pr365411⟩
private theorem pr365471 : PrimeCertificate 365471 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv23,pv227]) (by decide +kernel)
def pv365471 : PrimeValue := ⟨365471, pr365471⟩
private theorem pr365509 : PrimeCertificate 365509 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv11,pv13,pv71]) (by decide +kernel)
def pv365509 : PrimeValue := ⟨365509, pr365509⟩
private theorem pr365537 : PrimeCertificate 365537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11423]) (by decide +kernel)
def pv365537 : PrimeValue := ⟨365537, pr365537⟩
private theorem pr365557 : PrimeCertificate 365557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv743]) (by decide +kernel)
def pv365557 : PrimeValue := ⟨365557, pr365557⟩
private theorem pr365587 : PrimeCertificate 365587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv43,pv109]) (by decide +kernel)
def pv365587 : PrimeValue := ⟨365587, pr365587⟩
private theorem pr365591 : PrimeCertificate 365591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv36559]) (by decide +kernel)
def pv365591 : PrimeValue := ⟨365591, pr365591⟩
private theorem pr365639 : PrimeCertificate 365639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv41]) (by decide +kernel)
def pv365639 : PrimeValue := ⟨365639, pr365639⟩
private theorem pr365641 : PrimeCertificate 365641 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv277]) (by decide +kernel)
def pv365641 : PrimeValue := ⟨365641, pr365641⟩
private theorem pr365669 : PrimeCertificate 365669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv809]) (by decide +kernel)
def pv365669 : PrimeValue := ⟨365669, pr365669⟩
private theorem pr365747 : PrimeCertificate 365747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv7951]) (by decide +kernel)
def pv365747 : PrimeValue := ⟨365747, pr365747⟩
private theorem pr365773 : PrimeCertificate 365773 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv17,pv163]) (by decide +kernel)
def pv365773 : PrimeValue := ⟨365773, pr365773⟩
private theorem pr365779 : PrimeCertificate 365779 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv2903]) (by decide +kernel)
def pv365779 : PrimeValue := ⟨365779, pr365779⟩
private theorem pr365903 : PrimeCertificate 365903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv9629]) (by decide +kernel)
def pv365903 : PrimeValue := ⟨365903, pr365903⟩
private theorem pr365983 : PrimeCertificate 365983 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv181,pv337]) (by decide +kernel)
def pv365983 : PrimeValue := ⟨365983, pr365983⟩
private theorem pr366013 : PrimeCertificate 366013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3389]) (by decide +kernel)
def pv366013 : PrimeValue := ⟨366013, pr366013⟩
private theorem pr366097 : PrimeCertificate 366097 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv29,pv263]) (by decide +kernel)
def pv366097 : PrimeValue := ⟨366097, pr366097⟩
private theorem pr366103 : PrimeCertificate 366103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv43]) (by decide +kernel)
def pv366103 : PrimeValue := ⟨366103, pr366103⟩
private theorem pr366127 : PrimeCertificate 366127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv139,pv439]) (by decide +kernel)
def pv366127 : PrimeValue := ⟨366127, pr366127⟩
private theorem pr366161 : PrimeCertificate 366161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv199]) (by decide +kernel)
def pv366161 : PrimeValue := ⟨366161, pr366161⟩
private theorem pr366167 : PrimeCertificate 366167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv223,pv821]) (by decide +kernel)
def pv366167 : PrimeValue := ⟨366167, pr366167⟩
private theorem pr366181 : PrimeCertificate 366181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv359]) (by decide +kernel)
def pv366181 : PrimeValue := ⟨366181, pr366181⟩
private theorem pr366193 : PrimeCertificate 366193 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv2543]) (by decide +kernel)
def pv366193 : PrimeValue := ⟨366193, pr366193⟩
private theorem pr366269 : PrimeCertificate 366269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv103,pv127]) (by decide +kernel)
def pv366269 : PrimeValue := ⟨366269, pr366269⟩
private theorem pr366293 : PrimeCertificate 366293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv91573]) (by decide +kernel)
def pv366293 : PrimeValue := ⟨366293, pr366293⟩
private theorem pr366307 : PrimeCertificate 366307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61051]) (by decide +kernel)
def pv366307 : PrimeValue := ⟨366307, pr366307⟩
private theorem pr366313 : PrimeCertificate 366313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv15263]) (by decide +kernel)
def pv366313 : PrimeValue := ⟨366313, pr366313⟩
private theorem pr366329 : PrimeCertificate 366329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv1579]) (by decide +kernel)
def pv366329 : PrimeValue := ⟨366329, pr366329⟩
private theorem pr366347 : PrimeCertificate 366347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv1621]) (by decide +kernel)
def pv366347 : PrimeValue := ⟨366347, pr366347⟩
private theorem pr366409 : PrimeCertificate 366409 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv727]) (by decide +kernel)
def pv366409 : PrimeValue := ⟨366409, pr366409⟩
private theorem pr366461 : PrimeCertificate 366461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv73,pv251]) (by decide +kernel)
def pv366461 : PrimeValue := ⟨366461, pr366461⟩
private theorem pr366463 : PrimeCertificate 366463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv20359]) (by decide +kernel)
def pv366463 : PrimeValue := ⟨366463, pr366463⟩
private theorem pr366479 : PrimeCertificate 366479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv26177]) (by decide +kernel)
def pv366479 : PrimeValue := ⟨366479, pr366479⟩
private theorem pr366521 : PrimeCertificate 366521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv17]) (by decide +kernel)
def pv366521 : PrimeValue := ⟨366521, pr366521⟩
private theorem pr366599 : PrimeCertificate 366599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv183299]) (by decide +kernel)
def pv366599 : PrimeValue := ⟨366599, pr366599⟩
private theorem pr366607 : PrimeCertificate 366607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv73]) (by decide +kernel)
def pv366607 : PrimeValue := ⟨366607, pr366607⟩
private theorem pr366701 : PrimeCertificate 366701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv193]) (by decide +kernel)
def pv366701 : PrimeValue := ⟨366701, pr366701⟩
private theorem pr366713 : PrimeCertificate 366713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv1993]) (by decide +kernel)
def pv366713 : PrimeValue := ⟨366713, pr366713⟩
private theorem pr366787 : PrimeCertificate 366787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv71]) (by decide +kernel)
def pv366787 : PrimeValue := ⟨366787, pr366787⟩
private theorem pr366791 : PrimeCertificate 366791 :=
  certifyPrime (q := pv43) (ls := [pv2,pv5,pv43,pv853]) (by decide +kernel)
def pv366791 : PrimeValue := ⟨366791, pr366791⟩
private theorem pr366811 : PrimeCertificate 366811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv12227]) (by decide +kernel)
def pv366811 : PrimeValue := ⟨366811, pr366811⟩
private theorem pr366829 : PrimeCertificate 366829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv397]) (by decide +kernel)
def pv366829 : PrimeValue := ⟨366829, pr366829⟩
private theorem pr366851 : PrimeCertificate 366851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv23,pv29]) (by decide +kernel)
def pv366851 : PrimeValue := ⟨366851, pr366851⟩
private theorem pr366853 : PrimeCertificate 366853 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv1609]) (by decide +kernel)
def pv366853 : PrimeValue := ⟨366853, pr366853⟩
private theorem pr366907 : PrimeCertificate 366907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61151]) (by decide +kernel)
def pv366907 : PrimeValue := ⟨366907, pr366907⟩
private theorem pr366923 : PrimeCertificate 366923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv183461]) (by decide +kernel)
def pv366923 : PrimeValue := ⟨366923, pr366923⟩
private theorem pr366941 : PrimeCertificate 366941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2621]) (by decide +kernel)
def pv366941 : PrimeValue := ⟨366941, pr366941⟩
private theorem pr366973 : PrimeCertificate 366973 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv53,pv577]) (by decide +kernel)
def pv366973 : PrimeValue := ⟨366973, pr366973⟩
private theorem pr366997 : PrimeCertificate 366997 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv17,pv257]) (by decide +kernel)
def pv366997 : PrimeValue := ⟨366997, pr366997⟩
private theorem pr367001 : PrimeCertificate 367001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv367]) (by decide +kernel)
def pv367001 : PrimeValue := ⟨367001, pr367001⟩
private theorem pr367027 : PrimeCertificate 367027 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv67,pv83]) (by decide +kernel)
def pv367027 : PrimeValue := ⟨367027, pr367027⟩
private theorem pr367069 : PrimeCertificate 367069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv181]) (by decide +kernel)
def pv367069 : PrimeValue := ⟨367069, pr367069⟩
private theorem pr367097 : PrimeCertificate 367097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv45887]) (by decide +kernel)
def pv367097 : PrimeValue := ⟨367097, pr367097⟩
private theorem pr367127 : PrimeCertificate 367127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv347]) (by decide +kernel)
def pv367127 : PrimeValue := ⟨367127, pr367127⟩
private theorem pr367139 : PrimeCertificate 367139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv183569]) (by decide +kernel)
def pv367139 : PrimeValue := ⟨367139, pr367139⟩
private theorem pr367181 : PrimeCertificate 367181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1669]) (by decide +kernel)
def pv367181 : PrimeValue := ⟨367181, pr367181⟩
private theorem pr367219 : PrimeCertificate 367219 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv887]) (by decide +kernel)
def pv367219 : PrimeValue := ⟨367219, pr367219⟩
private theorem pr367259 : PrimeCertificate 367259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv3907]) (by decide +kernel)
def pv367259 : PrimeValue := ⟨367259, pr367259⟩
private theorem pr367307 : PrimeCertificate 367307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv4271]) (by decide +kernel)
def pv367307 : PrimeValue := ⟨367307, pr367307⟩
private theorem pr367313 : PrimeCertificate 367313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv2087]) (by decide +kernel)
def pv367313 : PrimeValue := ⟨367313, pr367313⟩
private theorem pr367357 : PrimeCertificate 367357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv367357 : PrimeValue := ⟨367357, pr367357⟩
private theorem pr367369 : PrimeCertificate 367369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv15307]) (by decide +kernel)
def pv367369 : PrimeValue := ⟨367369, pr367369⟩
private theorem pr367397 : PrimeCertificate 367397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv1733]) (by decide +kernel)
def pv367397 : PrimeValue := ⟨367397, pr367397⟩
private theorem pr367469 : PrimeCertificate 367469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv91867]) (by decide +kernel)
def pv367469 : PrimeValue := ⟨367469, pr367469⟩
private theorem pr367531 : PrimeCertificate 367531 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv12251]) (by decide +kernel)
def pv367531 : PrimeValue := ⟨367531, pr367531⟩
private theorem pr367541 : PrimeCertificate 367541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv23,pv47]) (by decide +kernel)
def pv367541 : PrimeValue := ⟨367541, pr367541⟩
private theorem pr367547 : PrimeCertificate 367547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv6337]) (by decide +kernel)
def pv367547 : PrimeValue := ⟨367547, pr367547⟩
private theorem pr367637 : PrimeCertificate 367637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv91909]) (by decide +kernel)
def pv367637 : PrimeValue := ⟨367637, pr367637⟩
private theorem pr367687 : PrimeCertificate 367687 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv619]) (by decide +kernel)
def pv367687 : PrimeValue := ⟨367687, pr367687⟩
private theorem pr367699 : PrimeCertificate 367699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61283]) (by decide +kernel)
def pv367699 : PrimeValue := ⟨367699, pr367699⟩
private theorem pr367721 : PrimeCertificate 367721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv317]) (by decide +kernel)
def pv367721 : PrimeValue := ⟨367721, pr367721⟩
private theorem pr367733 : PrimeCertificate 367733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv149,pv617]) (by decide +kernel)
def pv367733 : PrimeValue := ⟨367733, pr367733⟩
private theorem pr367739 : PrimeCertificate 367739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv26267]) (by decide +kernel)
def pv367739 : PrimeValue := ⟨367739, pr367739⟩
private theorem pr367751 : PrimeCertificate 367751 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv1471]) (by decide +kernel)
def pv367751 : PrimeValue := ⟨367751, pr367751⟩
private theorem pr367771 : PrimeCertificate 367771 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv23,pv41]) (by decide +kernel)
def pv367771 : PrimeValue := ⟨367771, pr367771⟩
private theorem pr367777 : PrimeCertificate 367777 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv1277]) (by decide +kernel)
def pv367777 : PrimeValue := ⟨367777, pr367777⟩
private theorem pr367781 : PrimeCertificate 367781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv37,pv71]) (by decide +kernel)
def pv367781 : PrimeValue := ⟨367781, pr367781⟩
private theorem pr367819 : PrimeCertificate 367819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv5573]) (by decide +kernel)
def pv367819 : PrimeValue := ⟨367819, pr367819⟩
private theorem pr367841 : PrimeCertificate 367841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv19]) (by decide +kernel)
def pv367841 : PrimeValue := ⟨367841, pr367841⟩
private theorem pr367849 : PrimeCertificate 367849 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv131]) (by decide +kernel)
def pv367849 : PrimeValue := ⟨367849, pr367849⟩
private theorem pr367853 : PrimeCertificate 367853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv2243]) (by decide +kernel)
def pv367853 : PrimeValue := ⟨367853, pr367853⟩
private theorem pr367867 : PrimeCertificate 367867 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107,pv191]) (by decide +kernel)
def pv367867 : PrimeValue := ⟨367867, pr367867⟩
private theorem pr367883 : PrimeCertificate 367883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv419,pv439]) (by decide +kernel)
def pv367883 : PrimeValue := ⟨367883, pr367883⟩
private theorem pr367889 : PrimeCertificate 367889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22993]) (by decide +kernel)
def pv367889 : PrimeValue := ⟨367889, pr367889⟩
private theorem pr367957 : PrimeCertificate 367957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3407]) (by decide +kernel)
def pv367957 : PrimeValue := ⟨367957, pr367957⟩
private theorem pr368021 : PrimeCertificate 368021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv18401]) (by decide +kernel)
def pv368021 : PrimeValue := ⟨368021, pr368021⟩
private theorem pr368029 : PrimeCertificate 368029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10223]) (by decide +kernel)
def pv368029 : PrimeValue := ⟨368029, pr368029⟩
private theorem pr368077 : PrimeCertificate 368077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv829]) (by decide +kernel)
def pv368077 : PrimeValue := ⟨368077, pr368077⟩
private theorem pr368083 : PrimeCertificate 368083 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv368083 : PrimeValue := ⟨368083, pr368083⟩
private theorem pr368107 : PrimeCertificate 368107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv3229]) (by decide +kernel)
def pv368107 : PrimeValue := ⟨368107, pr368107⟩
private theorem pr368117 : PrimeCertificate 368117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13147]) (by decide +kernel)
def pv368117 : PrimeValue := ⟨368117, pr368117⟩
private theorem pr368129 : PrimeCertificate 368129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv719]) (by decide +kernel)
def pv368129 : PrimeValue := ⟨368129, pr368129⟩
private theorem pr368141 : PrimeCertificate 368141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv79,pv233]) (by decide +kernel)
def pv368141 : PrimeValue := ⟨368141, pr368141⟩
private theorem pr368171 : PrimeCertificate 368171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv3347]) (by decide +kernel)
def pv368171 : PrimeValue := ⟨368171, pr368171⟩
private theorem pr368197 : PrimeCertificate 368197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv503]) (by decide +kernel)
def pv368197 : PrimeValue := ⟨368197, pr368197⟩
private theorem pr368227 : PrimeCertificate 368227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2273]) (by decide +kernel)
def pv368227 : PrimeValue := ⟨368227, pr368227⟩
private theorem pr368273 : PrimeCertificate 368273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23017]) (by decide +kernel)
def pv368273 : PrimeValue := ⟨368273, pr368273⟩
private theorem pr368287 : PrimeCertificate 368287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61381]) (by decide +kernel)
def pv368287 : PrimeValue := ⟨368287, pr368287⟩
private theorem pr368293 : PrimeCertificate 368293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv653]) (by decide +kernel)
def pv368293 : PrimeValue := ⟨368293, pr368293⟩
private theorem pr368323 : PrimeCertificate 368323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv23,pv157]) (by decide +kernel)
def pv368323 : PrimeValue := ⟨368323, pr368323⟩
private theorem pr368363 : PrimeCertificate 368363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv184181]) (by decide +kernel)
def pv368363 : PrimeValue := ⟨368363, pr368363⟩
private theorem pr368411 : PrimeCertificate 368411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv277]) (by decide +kernel)
def pv368411 : PrimeValue := ⟨368411, pr368411⟩
private theorem pr368491 : PrimeCertificate 368491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv71,pv173]) (by decide +kernel)
def pv368491 : PrimeValue := ⟨368491, pr368491⟩
private theorem pr368521 : PrimeCertificate 368521 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv37,pv83]) (by decide +kernel)
def pv368521 : PrimeValue := ⟨368521, pr368521⟩
private theorem pr368579 : PrimeCertificate 368579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv3761]) (by decide +kernel)
def pv368579 : PrimeValue := ⟨368579, pr368579⟩
private theorem pr368609 : PrimeCertificate 368609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11519]) (by decide +kernel)
def pv368609 : PrimeValue := ⟨368609, pr368609⟩
private theorem pr368647 : PrimeCertificate 368647 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv61441]) (by decide +kernel)
def pv368647 : PrimeValue := ⟨368647, pr368647⟩
private theorem pr368651 : PrimeCertificate 368651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv73,pv101]) (by decide +kernel)
def pv368651 : PrimeValue := ⟨368651, pr368651⟩
private theorem pr368653 : PrimeCertificate 368653 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31,pv991]) (by decide +kernel)
def pv368653 : PrimeValue := ⟨368653, pr368653⟩
private theorem pr368689 : PrimeCertificate 368689 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7681]) (by decide +kernel)
def pv368689 : PrimeValue := ⟨368689, pr368689⟩
private theorem pr368783 : PrimeCertificate 368783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv8017]) (by decide +kernel)
def pv368783 : PrimeValue := ⟨368783, pr368783⟩
private theorem pr368791 : PrimeCertificate 368791 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv647]) (by decide +kernel)
def pv368791 : PrimeValue := ⟨368791, pr368791⟩
private theorem pr368803 : PrimeCertificate 368803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2927]) (by decide +kernel)
def pv368803 : PrimeValue := ⟨368803, pr368803⟩
private theorem pr368857 : PrimeCertificate 368857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv109]) (by decide +kernel)
def pv368857 : PrimeValue := ⟨368857, pr368857⟩
private theorem pr368873 : PrimeCertificate 368873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv941]) (by decide +kernel)
def pv368873 : PrimeValue := ⟨368873, pr368873⟩
private theorem pr368939 : PrimeCertificate 368939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv6361]) (by decide +kernel)
def pv368939 : PrimeValue := ⟨368939, pr368939⟩
private theorem pr368957 : PrimeCertificate 368957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13177]) (by decide +kernel)
def pv368957 : PrimeValue := ⟨368957, pr368957⟩
private theorem pr369071 : PrimeCertificate 369071 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv13,pv17,pv167]) (by decide +kernel)
def pv369071 : PrimeValue := ⟨369071, pr369071⟩
private theorem pr369077 : PrimeCertificate 369077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv92269]) (by decide +kernel)
def pv369077 : PrimeValue := ⟨369077, pr369077⟩
private theorem pr369119 : PrimeCertificate 369119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv184559]) (by decide +kernel)
def pv369119 : PrimeValue := ⟨369119, pr369119⟩
private theorem pr369169 : PrimeCertificate 369169 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7691]) (by decide +kernel)
def pv369169 : PrimeValue := ⟨369169, pr369169⟩
private theorem pr369191 : PrimeCertificate 369191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv36919]) (by decide +kernel)
def pv369191 : PrimeValue := ⟨369191, pr369191⟩
private theorem pr369247 : PrimeCertificate 369247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv41,pv79]) (by decide +kernel)
def pv369247 : PrimeValue := ⟨369247, pr369247⟩
private theorem pr369269 : PrimeCertificate 369269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv92317]) (by decide +kernel)
def pv369269 : PrimeValue := ⟨369269, pr369269⟩
private theorem pr369283 : PrimeCertificate 369283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61547]) (by decide +kernel)
def pv369283 : PrimeValue := ⟨369283, pr369283⟩
private theorem pr369331 : PrimeCertificate 369331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv947]) (by decide +kernel)
def pv369331 : PrimeValue := ⟨369331, pr369331⟩
private theorem pr369353 : PrimeCertificate 369353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv137,pv337]) (by decide +kernel)
def pv369353 : PrimeValue := ⟨369353, pr369353⟩
private theorem pr369361 : PrimeCertificate 369361 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv369361 : PrimeValue := ⟨369361, pr369361⟩
private theorem pr369407 : PrimeCertificate 369407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv184703]) (by decide +kernel)
def pv369407 : PrimeValue := ⟨369407, pr369407⟩
private theorem pr369419 : PrimeCertificate 369419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv26387]) (by decide +kernel)
def pv369419 : PrimeValue := ⟨369419, pr369419⟩
private theorem pr369491 : PrimeCertificate 369491 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv3359]) (by decide +kernel)
def pv369491 : PrimeValue := ⟨369491, pr369491⟩
private theorem pr369557 : PrimeCertificate 369557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv37,pv227]) (by decide +kernel)
def pv369557 : PrimeValue := ⟨369557, pr369557⟩
private theorem pr369581 : PrimeCertificate 369581 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv1087]) (by decide +kernel)
def pv369581 : PrimeValue := ⟨369581, pr369581⟩
private theorem pr369637 : PrimeCertificate 369637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30803]) (by decide +kernel)
def pv369637 : PrimeValue := ⟨369637, pr369637⟩
private theorem pr369647 : PrimeCertificate 369647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv184823]) (by decide +kernel)
def pv369647 : PrimeValue := ⟨369647, pr369647⟩
private theorem pr369661 : PrimeCertificate 369661 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv61,pv101]) (by decide +kernel)
def pv369661 : PrimeValue := ⟨369661, pr369661⟩
private theorem pr369703 : PrimeCertificate 369703 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv23,pv47]) (by decide +kernel)
def pv369703 : PrimeValue := ⟨369703, pr369703⟩
private theorem pr369709 : PrimeCertificate 369709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30809]) (by decide +kernel)
def pv369709 : PrimeValue := ⟨369709, pr369709⟩
private theorem pr369731 : PrimeCertificate 369731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv36973]) (by decide +kernel)
def pv369731 : PrimeValue := ⟨369731, pr369731⟩
private theorem pr369739 : PrimeCertificate 369739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv167]) (by decide +kernel)
def pv369739 : PrimeValue := ⟨369739, pr369739⟩
private theorem pr369793 : PrimeCertificate 369793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv369793 : PrimeValue := ⟨369793, pr369793⟩
private theorem pr369821 : PrimeCertificate 369821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv41]) (by decide +kernel)
def pv369821 : PrimeValue := ⟨369821, pr369821⟩
private theorem pr369833 : PrimeCertificate 369833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv46229]) (by decide +kernel)
def pv369833 : PrimeValue := ⟨369833, pr369833⟩
private theorem pr369893 : PrimeCertificate 369893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv31,pv157]) (by decide +kernel)
def pv369893 : PrimeValue := ⟨369893, pr369893⟩
private theorem pr369947 : PrimeCertificate 369947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv1697]) (by decide +kernel)
def pv369947 : PrimeValue := ⟨369947, pr369947⟩
private theorem pr369959 : PrimeCertificate 369959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv97,pv1907]) (by decide +kernel)
def pv369959 : PrimeValue := ⟨369959, pr369959⟩
private theorem pr369983 : PrimeCertificate 369983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv6379]) (by decide +kernel)
def pv369983 : PrimeValue := ⟨369983, pr369983⟩
private theorem pr369991 : PrimeCertificate 369991 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4111]) (by decide +kernel)
def pv369991 : PrimeValue := ⟨369991, pr369991⟩
private theorem pr370003 : PrimeCertificate 370003 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv61667]) (by decide +kernel)
def pv370003 : PrimeValue := ⟨370003, pr370003⟩
private theorem pr370033 : PrimeCertificate 370033 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv593]) (by decide +kernel)
def pv370033 : PrimeValue := ⟨370033, pr370033⟩
private theorem pr370057 : PrimeCertificate 370057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv907]) (by decide +kernel)
def pv370057 : PrimeValue := ⟨370057, pr370057⟩
private theorem pr370061 : PrimeCertificate 370061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv18503]) (by decide +kernel)
def pv370061 : PrimeValue := ⟨370061, pr370061⟩
private theorem pr370067 : PrimeCertificate 370067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv4513]) (by decide +kernel)
def pv370067 : PrimeValue := ⟨370067, pr370067⟩
private theorem pr370091 : PrimeCertificate 370091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv17,pv311]) (by decide +kernel)
def pv370091 : PrimeValue := ⟨370091, pr370091⟩
private theorem pr370193 : PrimeCertificate 370193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1361]) (by decide +kernel)
def pv370193 : PrimeValue := ⟨370193, pr370193⟩
private theorem pr370199 : PrimeCertificate 370199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv185099]) (by decide +kernel)
def pv370199 : PrimeValue := ⟨370199, pr370199⟩
private theorem pr370217 : PrimeCertificate 370217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv601]) (by decide +kernel)
def pv370217 : PrimeValue := ⟨370217, pr370217⟩
private theorem pr370241 : PrimeCertificate 370241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv89]) (by decide +kernel)
def pv370241 : PrimeValue := ⟨370241, pr370241⟩
private theorem pr370261 : PrimeCertificate 370261 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv17]) (by decide +kernel)
def pv370261 : PrimeValue := ⟨370261, pr370261⟩
private theorem pr370373 : PrimeCertificate 370373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv92593]) (by decide +kernel)
def pv370373 : PrimeValue := ⟨370373, pr370373⟩
private theorem pr370421 : PrimeCertificate 370421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv18521]) (by decide +kernel)
def pv370421 : PrimeValue := ⟨370421, pr370421⟩
private theorem pr370423 : PrimeCertificate 370423 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv1583]) (by decide +kernel)
def pv370423 : PrimeValue := ⟨370423, pr370423⟩
private theorem pr370427 : PrimeCertificate 370427 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv26459]) (by decide +kernel)
def pv370427 : PrimeValue := ⟨370427, pr370427⟩
private theorem pr370451 : PrimeCertificate 370451 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv31,pv239]) (by decide +kernel)
def pv370451 : PrimeValue := ⟨370451, pr370451⟩
private theorem pr370511 : PrimeCertificate 370511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv67,pv79]) (by decide +kernel)
def pv370511 : PrimeValue := ⟨370511, pr370511⟩
private theorem pr370529 : PrimeCertificate 370529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11579]) (by decide +kernel)
def pv370529 : PrimeValue := ⟨370529, pr370529⟩
private theorem pr370547 : PrimeCertificate 370547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv16843]) (by decide +kernel)
def pv370547 : PrimeValue := ⟨370547, pr370547⟩
private theorem pr370603 : PrimeCertificate 370603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6863]) (by decide +kernel)
def pv370603 : PrimeValue := ⟨370603, pr370603⟩
private theorem pr370613 : PrimeCertificate 370613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv8423]) (by decide +kernel)
def pv370613 : PrimeValue := ⟨370613, pr370613⟩
private theorem pr370661 : PrimeCertificate 370661 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv43,pv431]) (by decide +kernel)
def pv370661 : PrimeValue := ⟨370661, pr370661⟩
private theorem pr370673 : PrimeCertificate 370673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23167]) (by decide +kernel)
def pv370673 : PrimeValue := ⟨370673, pr370673⟩
private theorem pr370693 : PrimeCertificate 370693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1471]) (by decide +kernel)
def pv370693 : PrimeValue := ⟨370693, pr370693⟩
private theorem pr370813 : PrimeCertificate 370813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv2377]) (by decide +kernel)
def pv370813 : PrimeValue := ⟨370813, pr370813⟩
private theorem pr370919 : PrimeCertificate 370919 :=
  certifyPrime (q := pv19) (ls := [pv2,pv19,pv43,pv227]) (by decide +kernel)
def pv370919 : PrimeValue := ⟨370919, pr370919⟩
private theorem pr371027 : PrimeCertificate 371027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv6397]) (by decide +kernel)
def pv371027 : PrimeValue := ⟨371027, pr371027⟩
private theorem pr371057 : PrimeCertificate 371057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv3313]) (by decide +kernel)
def pv371057 : PrimeValue := ⟨371057, pr371057⟩
private theorem pr371087 : PrimeCertificate 371087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv185543]) (by decide +kernel)
def pv371087 : PrimeValue := ⟨371087, pr371087⟩
private theorem pr371099 : PrimeCertificate 371099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv2039]) (by decide +kernel)
def pv371099 : PrimeValue := ⟨371099, pr371099⟩
private theorem pr371131 : PrimeCertificate 371131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv89,pv139]) (by decide +kernel)
def pv371131 : PrimeValue := ⟨371131, pr371131⟩
private theorem pr371141 : PrimeCertificate 371141 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv11,pv241]) (by decide +kernel)
def pv371141 : PrimeValue := ⟨371141, pr371141⟩
private theorem pr371143 : PrimeCertificate 371143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv79]) (by decide +kernel)
def pv371143 : PrimeValue := ⟨371143, pr371143⟩
private theorem pr371153 : PrimeCertificate 371153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23197]) (by decide +kernel)
def pv371153 : PrimeValue := ⟨371153, pr371153⟩
private theorem pr371177 : PrimeCertificate 371177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv43,pv83]) (by decide +kernel)
def pv371177 : PrimeValue := ⟨371177, pr371177⟩
private theorem pr371233 : PrimeCertificate 371233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1289]) (by decide +kernel)
def pv371233 : PrimeValue := ⟨371233, pr371233⟩
private theorem pr371249 : PrimeCertificate 371249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23203]) (by decide +kernel)
def pv371249 : PrimeValue := ⟨371249, pr371249⟩
private theorem pr371251 : PrimeCertificate 371251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv371251 : PrimeValue := ⟨371251, pr371251⟩
private theorem pr371257 : PrimeCertificate 371257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv499]) (by decide +kernel)
def pv371257 : PrimeValue := ⟨371257, pr371257⟩
private theorem pr371291 : PrimeCertificate 371291 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv107,pv347]) (by decide +kernel)
def pv371291 : PrimeValue := ⟨371291, pr371291⟩
private theorem pr371303 : PrimeCertificate 371303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv185651]) (by decide +kernel)
def pv371303 : PrimeValue := ⟨371303, pr371303⟩
private theorem pr371353 : PrimeCertificate 371353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv15473]) (by decide +kernel)
def pv371353 : PrimeValue := ⟨371353, pr371353⟩
private theorem pr371383 : PrimeCertificate 371383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv331]) (by decide +kernel)
def pv371383 : PrimeValue := ⟨371383, pr371383⟩
private theorem pr371387 : PrimeCertificate 371387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv185693]) (by decide +kernel)
def pv371387 : PrimeValue := ⟨371387, pr371387⟩
private theorem pr371389 : PrimeCertificate 371389 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv30949]) (by decide +kernel)
def pv371389 : PrimeValue := ⟨371389, pr371389⟩
private theorem pr371417 : PrimeCertificate 371417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv2731]) (by decide +kernel)
def pv371417 : PrimeValue := ⟨371417, pr371417⟩
private theorem pr371471 : PrimeCertificate 371471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv307]) (by decide +kernel)
def pv371471 : PrimeValue := ⟨371471, pr371471⟩
private theorem pr371479 : PrimeCertificate 371479 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv101,pv613]) (by decide +kernel)
def pv371479 : PrimeValue := ⟨371479, pr371479⟩
private theorem pr371513 : PrimeCertificate 371513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv46439]) (by decide +kernel)
def pv371513 : PrimeValue := ⟨371513, pr371513⟩
private theorem pr371561 : PrimeCertificate 371561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv1327]) (by decide +kernel)
def pv371561 : PrimeValue := ⟨371561, pr371561⟩
private theorem pr371587 : PrimeCertificate 371587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv3643]) (by decide +kernel)
def pv371587 : PrimeValue := ⟨371587, pr371587⟩
private theorem pr371627 : PrimeCertificate 371627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv185813]) (by decide +kernel)
def pv371627 : PrimeValue := ⟨371627, pr371627⟩
private theorem pr371639 : PrimeCertificate 371639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv185819]) (by decide +kernel)
def pv371639 : PrimeValue := ⟨371639, pr371639⟩
private theorem pr371669 : PrimeCertificate 371669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv8447]) (by decide +kernel)
def pv371669 : PrimeValue := ⟨371669, pr371669⟩
private theorem pr371779 : PrimeCertificate 371779 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv43,pv131]) (by decide +kernel)
def pv371779 : PrimeValue := ⟨371779, pr371779⟩
private theorem pr371797 : PrimeCertificate 371797 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv30983]) (by decide +kernel)
def pv371797 : PrimeValue := ⟨371797, pr371797⟩
private theorem pr371831 : PrimeCertificate 371831 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv103]) (by decide +kernel)
def pv371831 : PrimeValue := ⟨371831, pr371831⟩
private theorem pr371843 : PrimeCertificate 371843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv2089]) (by decide +kernel)
def pv371843 : PrimeValue := ⟨371843, pr371843⟩
private theorem pr371851 : PrimeCertificate 371851 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv37,pv67]) (by decide +kernel)
def pv371851 : PrimeValue := ⟨371851, pr371851⟩
private theorem pr371857 : PrimeCertificate 371857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61,pv127]) (by decide +kernel)
def pv371857 : PrimeValue := ⟨371857, pr371857⟩
private theorem pr371873 : PrimeCertificate 371873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11621]) (by decide +kernel)
def pv371873 : PrimeValue := ⟨371873, pr371873⟩
private theorem pr371927 : PrimeCertificate 371927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv10939]) (by decide +kernel)
def pv371927 : PrimeValue := ⟨371927, pr371927⟩
private theorem pr371939 : PrimeCertificate 371939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv857]) (by decide +kernel)
def pv371939 : PrimeValue := ⟨371939, pr371939⟩
private theorem pr371951 : PrimeCertificate 371951 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv43,pv173]) (by decide +kernel)
def pv371951 : PrimeValue := ⟨371951, pr371951⟩
private theorem pr371981 : PrimeCertificate 371981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2657]) (by decide +kernel)
def pv371981 : PrimeValue := ⟨371981, pr371981⟩
private theorem pr372131 : PrimeCertificate 372131 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv17,pv199]) (by decide +kernel)
def pv372131 : PrimeValue := ⟨372131, pr372131⟩
private theorem pr372167 : PrimeCertificate 372167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv3511]) (by decide +kernel)
def pv372167 : PrimeValue := ⟨372167, pr372167⟩
private theorem pr372173 : PrimeCertificate 372173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv59,pv83]) (by decide +kernel)
def pv372173 : PrimeValue := ⟨372173, pr372173⟩
private theorem pr372269 : PrimeCertificate 372269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv7159]) (by decide +kernel)
def pv372269 : PrimeValue := ⟨372269, pr372269⟩
private theorem pr372277 : PrimeCertificate 372277 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv383]) (by decide +kernel)
def pv372277 : PrimeValue := ⟨372277, pr372277⟩
private theorem pr372289 : PrimeCertificate 372289 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv277]) (by decide +kernel)
def pv372289 : PrimeValue := ⟨372289, pr372289⟩
private theorem pr372299 : PrimeCertificate 372299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv186149]) (by decide +kernel)
def pv372299 : PrimeValue := ⟨372299, pr372299⟩
private theorem pr372311 : PrimeCertificate 372311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv31,pv1201]) (by decide +kernel)
def pv372311 : PrimeValue := ⟨372311, pr372311⟩
private theorem pr372313 : PrimeCertificate 372313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5171]) (by decide +kernel)
def pv372313 : PrimeValue := ⟨372313, pr372313⟩
private theorem pr372353 : PrimeCertificate 372353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2909]) (by decide +kernel)
def pv372353 : PrimeValue := ⟨372353, pr372353⟩
private theorem pr372371 : PrimeCertificate 372371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv1619]) (by decide +kernel)
def pv372371 : PrimeValue := ⟨372371, pr372371⟩
private theorem pr372377 : PrimeCertificate 372377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv523]) (by decide +kernel)
def pv372377 : PrimeValue := ⟨372377, pr372377⟩
private theorem pr372397 : PrimeCertificate 372397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31033]) (by decide +kernel)
def pv372397 : PrimeValue := ⟨372397, pr372397⟩
private theorem pr372409 : PrimeCertificate 372409 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv59,pv263]) (by decide +kernel)
def pv372409 : PrimeValue := ⟨372409, pr372409⟩
private theorem pr372451 : PrimeCertificate 372451 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv191]) (by decide +kernel)
def pv372451 : PrimeValue := ⟨372451, pr372451⟩
private theorem pr372497 : PrimeCertificate 372497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv751]) (by decide +kernel)
def pv372497 : PrimeValue := ⟨372497, pr372497⟩
private theorem pr372511 : PrimeCertificate 372511 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv4139]) (by decide +kernel)
def pv372511 : PrimeValue := ⟨372511, pr372511⟩
private theorem pr372523 : PrimeCertificate 372523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv1321]) (by decide +kernel)
def pv372523 : PrimeValue := ⟨372523, pr372523⟩
private theorem pr372607 : PrimeCertificate 372607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv281]) (by decide +kernel)
def pv372607 : PrimeValue := ⟨372607, pr372607⟩
private theorem pr372653 : PrimeCertificate 372653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13309]) (by decide +kernel)
def pv372653 : PrimeValue := ⟨372653, pr372653⟩
private theorem pr372667 : PrimeCertificate 372667 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv19,pv467]) (by decide +kernel)
def pv372667 : PrimeValue := ⟨372667, pr372667⟩
private theorem pr372677 : PrimeCertificate 372677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv93169]) (by decide +kernel)
def pv372677 : PrimeValue := ⟨372677, pr372677⟩
private theorem pr372689 : PrimeCertificate 372689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23293]) (by decide +kernel)
def pv372689 : PrimeValue := ⟨372689, pr372689⟩
private theorem pr372719 : PrimeCertificate 372719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv157,pv1187]) (by decide +kernel)
def pv372719 : PrimeValue := ⟨372719, pr372719⟩
private theorem pr372733 : PrimeCertificate 372733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv349]) (by decide +kernel)
def pv372733 : PrimeValue := ⟨372733, pr372733⟩
private theorem pr372797 : PrimeCertificate 372797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv93199]) (by decide +kernel)
def pv372797 : PrimeValue := ⟨372797, pr372797⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
