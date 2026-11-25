/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table043
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table043.pv115861
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr115861 : PrimeCertificate 115861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1931]) (by decide +kernel)
def pv115861 : PrimeValue := ⟨115861, pr115861⟩
private theorem pr115873 : PrimeCertificate 115873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv71]) (by decide +kernel)
def pv115873 : PrimeValue := ⟨115873, pr115873⟩
private theorem pr115877 : PrimeCertificate 115877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv491]) (by decide +kernel)
def pv115877 : PrimeValue := ⟨115877, pr115877⟩
private theorem pr115879 : PrimeCertificate 115879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv31,pv89]) (by decide +kernel)
def pv115879 : PrimeValue := ⟨115879, pr115879⟩
private theorem pr115883 : PrimeCertificate 115883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv4457]) (by decide +kernel)
def pv115883 : PrimeValue := ⟨115883, pr115883⟩
private theorem pr115891 : PrimeCertificate 115891 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3863]) (by decide +kernel)
def pv115891 : PrimeValue := ⟨115891, pr115891⟩
private theorem pr115901 : PrimeCertificate 115901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv61]) (by decide +kernel)
def pv115901 : PrimeValue := ⟨115901, pr115901⟩
private theorem pr115903 : PrimeCertificate 115903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv137]) (by decide +kernel)
def pv115903 : PrimeValue := ⟨115903, pr115903⟩
private theorem pr115931 : PrimeCertificate 115931 :=
  certifyPrime (q := pv41) (ls := [pv2,pv5,pv11593]) (by decide +kernel)
def pv115931 : PrimeValue := ⟨115931, pr115931⟩
private theorem pr115933 : PrimeCertificate 115933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9661]) (by decide +kernel)
def pv115933 : PrimeValue := ⟨115933, pr115933⟩
private theorem pr115963 : PrimeCertificate 115963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv251]) (by decide +kernel)
def pv115963 : PrimeValue := ⟨115963, pr115963⟩
private theorem pr115979 : PrimeCertificate 115979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv563]) (by decide +kernel)
def pv115979 : PrimeValue := ⟨115979, pr115979⟩
private theorem pr115981 : PrimeCertificate 115981 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1933]) (by decide +kernel)
def pv115981 : PrimeValue := ⟨115981, pr115981⟩
private theorem pr115987 : PrimeCertificate 115987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1487]) (by decide +kernel)
def pv115987 : PrimeValue := ⟨115987, pr115987⟩
private theorem pr116009 : PrimeCertificate 116009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv853]) (by decide +kernel)
def pv116009 : PrimeValue := ⟨116009, pr116009⟩
private theorem pr116027 : PrimeCertificate 116027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv58013]) (by decide +kernel)
def pv116027 : PrimeValue := ⟨116027, pr116027⟩
private theorem pr116041 : PrimeCertificate 116041 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv967]) (by decide +kernel)
def pv116041 : PrimeValue := ⟨116041, pr116041⟩
private theorem pr116047 : PrimeCertificate 116047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv307]) (by decide +kernel)
def pv116047 : PrimeValue := ⟨116047, pr116047⟩
private theorem pr116089 : PrimeCertificate 116089 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv691]) (by decide +kernel)
def pv116089 : PrimeValue := ⟨116089, pr116089⟩
private theorem pr116099 : PrimeCertificate 116099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv58049]) (by decide +kernel)
def pv116099 : PrimeValue := ⟨116099, pr116099⟩
private theorem pr116101 : PrimeCertificate 116101 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv116101 : PrimeValue := ⟨116101, pr116101⟩
private theorem pr116107 : PrimeCertificate 116107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv523]) (by decide +kernel)
def pv116107 : PrimeValue := ⟨116107, pr116107⟩
private theorem pr116113 : PrimeCertificate 116113 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv41,pv59]) (by decide +kernel)
def pv116113 : PrimeValue := ⟨116113, pr116113⟩
private theorem pr116141 : PrimeCertificate 116141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5807]) (by decide +kernel)
def pv116141 : PrimeValue := ⟨116141, pr116141⟩
private theorem pr116159 : PrimeCertificate 116159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv8297]) (by decide +kernel)
def pv116159 : PrimeValue := ⟨116159, pr116159⟩
private theorem pr116167 : PrimeCertificate 116167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv1019]) (by decide +kernel)
def pv116167 : PrimeValue := ⟨116167, pr116167⟩
private theorem pr116177 : PrimeCertificate 116177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv137]) (by decide +kernel)
def pv116177 : PrimeValue := ⟨116177, pr116177⟩
private theorem pr116189 : PrimeCertificate 116189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv937]) (by decide +kernel)
def pv116189 : PrimeValue := ⟨116189, pr116189⟩
private theorem pr116191 : PrimeCertificate 116191 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1291]) (by decide +kernel)
def pv116191 : PrimeValue := ⟨116191, pr116191⟩
private theorem pr116201 : PrimeCertificate 116201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv83]) (by decide +kernel)
def pv116201 : PrimeValue := ⟨116201, pr116201⟩
private theorem pr116239 : PrimeCertificate 116239 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19373]) (by decide +kernel)
def pv116239 : PrimeValue := ⟨116239, pr116239⟩
private theorem pr116243 : PrimeCertificate 116243 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv19,pv23]) (by decide +kernel)
def pv116243 : PrimeValue := ⟨116243, pr116243⟩
private theorem pr116257 : PrimeCertificate 116257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv173]) (by decide +kernel)
def pv116257 : PrimeValue := ⟨116257, pr116257⟩
private theorem pr116269 : PrimeCertificate 116269 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv9689]) (by decide +kernel)
def pv116269 : PrimeValue := ⟨116269, pr116269⟩
private theorem pr116293 : PrimeCertificate 116293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv881]) (by decide +kernel)
def pv116293 : PrimeValue := ⟨116293, pr116293⟩
private theorem pr116329 : PrimeCertificate 116329 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv37,pv131]) (by decide +kernel)
def pv116329 : PrimeValue := ⟨116329, pr116329⟩
private theorem pr116341 : PrimeCertificate 116341 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv7,pv277]) (by decide +kernel)
def pv116341 : PrimeValue := ⟨116341, pr116341⟩
private theorem pr116359 : PrimeCertificate 116359 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv41,pv43]) (by decide +kernel)
def pv116359 : PrimeValue := ⟨116359, pr116359⟩
private theorem pr116371 : PrimeCertificate 116371 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv431]) (by decide +kernel)
def pv116371 : PrimeValue := ⟨116371, pr116371⟩
private theorem pr116381 : PrimeCertificate 116381 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv23]) (by decide +kernel)
def pv116381 : PrimeValue := ⟨116381, pr116381⟩
private theorem pr116387 : PrimeCertificate 116387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv58193]) (by decide +kernel)
def pv116387 : PrimeValue := ⟨116387, pr116387⟩
private theorem pr116411 : PrimeCertificate 116411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1663]) (by decide +kernel)
def pv116411 : PrimeValue := ⟨116411, pr116411⟩
private theorem pr116423 : PrimeCertificate 116423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv58211]) (by decide +kernel)
def pv116423 : PrimeValue := ⟨116423, pr116423⟩
private theorem pr116437 : PrimeCertificate 116437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv313]) (by decide +kernel)
def pv116437 : PrimeValue := ⟨116437, pr116437⟩
private theorem pr116443 : PrimeCertificate 116443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6469]) (by decide +kernel)
def pv116443 : PrimeValue := ⟨116443, pr116443⟩
private theorem pr116447 : PrimeCertificate 116447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv67,pv79]) (by decide +kernel)
def pv116447 : PrimeValue := ⟨116447, pr116447⟩
private theorem pr116461 : PrimeCertificate 116461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv647]) (by decide +kernel)
def pv116461 : PrimeValue := ⟨116461, pr116461⟩
private theorem pr116471 : PrimeCertificate 116471 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv613]) (by decide +kernel)
def pv116471 : PrimeValue := ⟨116471, pr116471⟩
private theorem pr116483 : PrimeCertificate 116483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139,pv419]) (by decide +kernel)
def pv116483 : PrimeValue := ⟨116483, pr116483⟩
private theorem pr116491 : PrimeCertificate 116491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv353]) (by decide +kernel)
def pv116491 : PrimeValue := ⟨116491, pr116491⟩
private theorem pr116507 : PrimeCertificate 116507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv4481]) (by decide +kernel)
def pv116507 : PrimeValue := ⟨116507, pr116507⟩
private theorem pr116531 : PrimeCertificate 116531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv271]) (by decide +kernel)
def pv116531 : PrimeValue := ⟨116531, pr116531⟩
private theorem pr116533 : PrimeCertificate 116533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv83]) (by decide +kernel)
def pv116533 : PrimeValue := ⟨116533, pr116533⟩
private theorem pr116537 : PrimeCertificate 116537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2081]) (by decide +kernel)
def pv116537 : PrimeValue := ⟨116537, pr116537⟩
private theorem pr116539 : PrimeCertificate 116539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19423]) (by decide +kernel)
def pv116539 : PrimeValue := ⟨116539, pr116539⟩
private theorem pr116549 : PrimeCertificate 116549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29137]) (by decide +kernel)
def pv116549 : PrimeValue := ⟨116549, pr116549⟩
private theorem pr116579 : PrimeCertificate 116579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv757]) (by decide +kernel)
def pv116579 : PrimeValue := ⟨116579, pr116579⟩
private theorem pr116593 : PrimeCertificate 116593 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv347]) (by decide +kernel)
def pv116593 : PrimeValue := ⟨116593, pr116593⟩
private theorem pr116639 : PrimeCertificate 116639 :=
  certifyPrime (q := pv19) (ls := [pv2,pv29,pv2011]) (by decide +kernel)
def pv116639 : PrimeValue := ⟨116639, pr116639⟩
private theorem pr116657 : PrimeCertificate 116657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv317]) (by decide +kernel)
def pv116657 : PrimeValue := ⟨116657, pr116657⟩
private theorem pr116663 : PrimeCertificate 116663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv641]) (by decide +kernel)
def pv116663 : PrimeValue := ⟨116663, pr116663⟩
private theorem pr116681 : PrimeCertificate 116681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2917]) (by decide +kernel)
def pv116681 : PrimeValue := ⟨116681, pr116681⟩
private theorem pr116687 : PrimeCertificate 116687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv1423]) (by decide +kernel)
def pv116687 : PrimeValue := ⟨116687, pr116687⟩
private theorem pr116689 : PrimeCertificate 116689 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv13,pv17]) (by decide +kernel)
def pv116689 : PrimeValue := ⟨116689, pr116689⟩
private theorem pr116707 : PrimeCertificate 116707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv367]) (by decide +kernel)
def pv116707 : PrimeValue := ⟨116707, pr116707⟩
private theorem pr116719 : PrimeCertificate 116719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv397]) (by decide +kernel)
def pv116719 : PrimeValue := ⟨116719, pr116719⟩
private theorem pr116731 : PrimeCertificate 116731 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1297]) (by decide +kernel)
def pv116731 : PrimeValue := ⟨116731, pr116731⟩
private theorem pr116747 : PrimeCertificate 116747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv269]) (by decide +kernel)
def pv116747 : PrimeValue := ⟨116747, pr116747⟩
private theorem pr116797 : PrimeCertificate 116797 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9733]) (by decide +kernel)
def pv116797 : PrimeValue := ⟨116797, pr116797⟩
private theorem pr116803 : PrimeCertificate 116803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv103]) (by decide +kernel)
def pv116803 : PrimeValue := ⟨116803, pr116803⟩
private theorem pr116819 : PrimeCertificate 116819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv4493]) (by decide +kernel)
def pv116819 : PrimeValue := ⟨116819, pr116819⟩
private theorem pr116827 : PrimeCertificate 116827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19471]) (by decide +kernel)
def pv116827 : PrimeValue := ⟨116827, pr116827⟩
private theorem pr116833 : PrimeCertificate 116833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1217]) (by decide +kernel)
def pv116833 : PrimeValue := ⟨116833, pr116833⟩
private theorem pr116849 : PrimeCertificate 116849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv109]) (by decide +kernel)
def pv116849 : PrimeValue := ⟨116849, pr116849⟩
private theorem pr116867 : PrimeCertificate 116867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv823]) (by decide +kernel)
def pv116867 : PrimeValue := ⟨116867, pr116867⟩
private theorem pr116881 : PrimeCertificate 116881 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv487]) (by decide +kernel)
def pv116881 : PrimeValue := ⟨116881, pr116881⟩
private theorem pr116903 : PrimeCertificate 116903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv58451]) (by decide +kernel)
def pv116903 : PrimeValue := ⟨116903, pr116903⟩
private theorem pr116911 : PrimeCertificate 116911 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv433]) (by decide +kernel)
def pv116911 : PrimeValue := ⟨116911, pr116911⟩
private theorem pr116923 : PrimeCertificate 116923 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1499]) (by decide +kernel)
def pv116923 : PrimeValue := ⟨116923, pr116923⟩
private theorem pr116927 : PrimeCertificate 116927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv19,pv181]) (by decide +kernel)
def pv116927 : PrimeValue := ⟨116927, pr116927⟩
private theorem pr116929 : PrimeCertificate 116929 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv116929 : PrimeValue := ⟨116929, pr116929⟩
private theorem pr116953 : PrimeCertificate 116953 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv443]) (by decide +kernel)
def pv116953 : PrimeValue := ⟨116953, pr116953⟩
private theorem pr116959 : PrimeCertificate 116959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv101,pv193]) (by decide +kernel)
def pv116959 : PrimeValue := ⟨116959, pr116959⟩
private theorem pr116969 : PrimeCertificate 116969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14621]) (by decide +kernel)
def pv116969 : PrimeValue := ⟨116969, pr116969⟩
private theorem pr116989 : PrimeCertificate 116989 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv9749]) (by decide +kernel)
def pv116989 : PrimeValue := ⟨116989, pr116989⟩
private theorem pr116993 : PrimeCertificate 116993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv457]) (by decide +kernel)
def pv116993 : PrimeValue := ⟨116993, pr116993⟩
private theorem pr117017 : PrimeCertificate 117017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14627]) (by decide +kernel)
def pv117017 : PrimeValue := ⟨117017, pr117017⟩
private theorem pr117023 : PrimeCertificate 117023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv58511]) (by decide +kernel)
def pv117023 : PrimeValue := ⟨117023, pr117023⟩
private theorem pr117041 : PrimeCertificate 117041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv19]) (by decide +kernel)
def pv117041 : PrimeValue := ⟨117041, pr117041⟩
private theorem pr117043 : PrimeCertificate 117043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19507]) (by decide +kernel)
def pv117043 : PrimeValue := ⟨117043, pr117043⟩
private theorem pr117053 : PrimeCertificate 117053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2251]) (by decide +kernel)
def pv117053 : PrimeValue := ⟨117053, pr117053⟩
private theorem pr117071 : PrimeCertificate 117071 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv23,pv509]) (by decide +kernel)
def pv117071 : PrimeValue := ⟨117071, pr117071⟩
private theorem pr117101 : PrimeCertificate 117101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1171]) (by decide +kernel)
def pv117101 : PrimeValue := ⟨117101, pr117101⟩
private theorem pr117109 : PrimeCertificate 117109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3253]) (by decide +kernel)
def pv117109 : PrimeValue := ⟨117109, pr117109⟩
private theorem pr117119 : PrimeCertificate 117119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv31,pv1889]) (by decide +kernel)
def pv117119 : PrimeValue := ⟨117119, pr117119⟩
private theorem pr117127 : PrimeCertificate 117127 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv241]) (by decide +kernel)
def pv117127 : PrimeValue := ⟨117127, pr117127⟩
private theorem pr117133 : PrimeCertificate 117133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv227]) (by decide +kernel)
def pv117133 : PrimeValue := ⟨117133, pr117133⟩
private theorem pr117163 : PrimeCertificate 117163 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv23,pv283]) (by decide +kernel)
def pv117163 : PrimeValue := ⟨117163, pr117163⟩
private theorem pr117167 : PrimeCertificate 117167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv8369]) (by decide +kernel)
def pv117167 : PrimeValue := ⟨117167, pr117167⟩
private theorem pr117191 : PrimeCertificate 117191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11719]) (by decide +kernel)
def pv117191 : PrimeValue := ⟨117191, pr117191⟩
private theorem pr117193 : PrimeCertificate 117193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv257]) (by decide +kernel)
def pv117193 : PrimeValue := ⟨117193, pr117193⟩
private theorem pr117209 : PrimeCertificate 117209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv23]) (by decide +kernel)
def pv117209 : PrimeValue := ⟨117209, pr117209⟩
private theorem pr117223 : PrimeCertificate 117223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv2791]) (by decide +kernel)
def pv117223 : PrimeValue := ⟨117223, pr117223⟩
private theorem pr117239 : PrimeCertificate 117239 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv73]) (by decide +kernel)
def pv117239 : PrimeValue := ⟨117239, pr117239⟩
private theorem pr117241 : PrimeCertificate 117241 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv977]) (by decide +kernel)
def pv117241 : PrimeValue := ⟨117241, pr117241⟩
private theorem pr117251 : PrimeCertificate 117251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv67]) (by decide +kernel)
def pv117251 : PrimeValue := ⟨117251, pr117251⟩
private theorem pr117259 : PrimeCertificate 117259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19543]) (by decide +kernel)
def pv117259 : PrimeValue := ⟨117259, pr117259⟩
private theorem pr117269 : PrimeCertificate 117269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv1543]) (by decide +kernel)
def pv117269 : PrimeValue := ⟨117269, pr117269⟩
private theorem pr117281 : PrimeCertificate 117281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv733]) (by decide +kernel)
def pv117281 : PrimeValue := ⟨117281, pr117281⟩
private theorem pr117307 : PrimeCertificate 117307 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv117307 : PrimeValue := ⟨117307, pr117307⟩
private theorem pr117319 : PrimeCertificate 117319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19553]) (by decide +kernel)
def pv117319 : PrimeValue := ⟨117319, pr117319⟩
private theorem pr117329 : PrimeCertificate 117329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7333]) (by decide +kernel)
def pv117329 : PrimeValue := ⟨117329, pr117329⟩
private theorem pr117331 : PrimeCertificate 117331 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3911]) (by decide +kernel)
def pv117331 : PrimeValue := ⟨117331, pr117331⟩
private theorem pr117353 : PrimeCertificate 117353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14669]) (by decide +kernel)
def pv117353 : PrimeValue := ⟨117353, pr117353⟩
private theorem pr117361 : PrimeCertificate 117361 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv163]) (by decide +kernel)
def pv117361 : PrimeValue := ⟨117361, pr117361⟩
private theorem pr117371 : PrimeCertificate 117371 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv97]) (by decide +kernel)
def pv117371 : PrimeValue := ⟨117371, pr117371⟩
private theorem pr117373 : PrimeCertificate 117373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9781]) (by decide +kernel)
def pv117373 : PrimeValue := ⟨117373, pr117373⟩
private theorem pr117389 : PrimeCertificate 117389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29347]) (by decide +kernel)
def pv117389 : PrimeValue := ⟨117389, pr117389⟩
private theorem pr117413 : PrimeCertificate 117413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv149,pv197]) (by decide +kernel)
def pv117413 : PrimeValue := ⟨117413, pr117413⟩
private theorem pr117427 : PrimeCertificate 117427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19571]) (by decide +kernel)
def pv117427 : PrimeValue := ⟨117427, pr117427⟩
private theorem pr117431 : PrimeCertificate 117431 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11743]) (by decide +kernel)
def pv117431 : PrimeValue := ⟨117431, pr117431⟩
private theorem pr117437 : PrimeCertificate 117437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv157]) (by decide +kernel)
def pv117437 : PrimeValue := ⟨117437, pr117437⟩
private theorem pr117443 : PrimeCertificate 117443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv4517]) (by decide +kernel)
def pv117443 : PrimeValue := ⟨117443, pr117443⟩
private theorem pr117497 : PrimeCertificate 117497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv773]) (by decide +kernel)
def pv117497 : PrimeValue := ⟨117497, pr117497⟩
private theorem pr117499 : PrimeCertificate 117499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19583]) (by decide +kernel)
def pv117499 : PrimeValue := ⟨117499, pr117499⟩
private theorem pr117503 : PrimeCertificate 117503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv109]) (by decide +kernel)
def pv117503 : PrimeValue := ⟨117503, pr117503⟩
private theorem pr117511 : PrimeCertificate 117511 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv3917]) (by decide +kernel)
def pv117511 : PrimeValue := ⟨117511, pr117511⟩
private theorem pr117517 : PrimeCertificate 117517 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv1399]) (by decide +kernel)
def pv117517 : PrimeValue := ⟨117517, pr117517⟩
private theorem pr117529 : PrimeCertificate 117529 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv59,pv83]) (by decide +kernel)
def pv117529 : PrimeValue := ⟨117529, pr117529⟩
private theorem pr117539 : PrimeCertificate 117539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv3457]) (by decide +kernel)
def pv117539 : PrimeValue := ⟨117539, pr117539⟩
private theorem pr117541 : PrimeCertificate 117541 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv653]) (by decide +kernel)
def pv117541 : PrimeValue := ⟨117541, pr117541⟩
private theorem pr117563 : PrimeCertificate 117563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv1367]) (by decide +kernel)
def pv117563 : PrimeValue := ⟨117563, pr117563⟩
private theorem pr117571 : PrimeCertificate 117571 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3919]) (by decide +kernel)
def pv117571 : PrimeValue := ⟨117571, pr117571⟩
private theorem pr117577 : PrimeCertificate 117577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv71]) (by decide +kernel)
def pv117577 : PrimeValue := ⟨117577, pr117577⟩
private theorem pr117619 : PrimeCertificate 117619 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19603]) (by decide +kernel)
def pv117619 : PrimeValue := ⟨117619, pr117619⟩
private theorem pr117659 : PrimeCertificate 117659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv661]) (by decide +kernel)
def pv117659 : PrimeValue := ⟨117659, pr117659⟩
private theorem pr117671 : PrimeCertificate 117671 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv41]) (by decide +kernel)
def pv117671 : PrimeValue := ⟨117671, pr117671⟩
private theorem pr117673 : PrimeCertificate 117673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4903]) (by decide +kernel)
def pv117673 : PrimeValue := ⟨117673, pr117673⟩
private theorem pr117679 : PrimeCertificate 117679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1783]) (by decide +kernel)
def pv117679 : PrimeValue := ⟨117679, pr117679⟩
private theorem pr117701 : PrimeCertificate 117701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv107]) (by decide +kernel)
def pv117701 : PrimeValue := ⟨117701, pr117701⟩
private theorem pr117709 : PrimeCertificate 117709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv577]) (by decide +kernel)
def pv117709 : PrimeValue := ⟨117709, pr117709⟩
private theorem pr117727 : PrimeCertificate 117727 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv2803]) (by decide +kernel)
def pv117727 : PrimeValue := ⟨117727, pr117727⟩
private theorem pr117731 : PrimeCertificate 117731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61,pv193]) (by decide +kernel)
def pv117731 : PrimeValue := ⟨117731, pr117731⟩
private theorem pr117751 : PrimeCertificate 117751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv157]) (by decide +kernel)
def pv117751 : PrimeValue := ⟨117751, pr117751⟩
private theorem pr117757 : PrimeCertificate 117757 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3271]) (by decide +kernel)
def pv117757 : PrimeValue := ⟨117757, pr117757⟩
private theorem pr117763 : PrimeCertificate 117763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1033]) (by decide +kernel)
def pv117763 : PrimeValue := ⟨117763, pr117763⟩
private theorem pr117773 : PrimeCertificate 117773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29443]) (by decide +kernel)
def pv117773 : PrimeValue := ⟨117773, pr117773⟩
private theorem pr117779 : PrimeCertificate 117779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv58889]) (by decide +kernel)
def pv117779 : PrimeValue := ⟨117779, pr117779⟩
private theorem pr117787 : PrimeCertificate 117787 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv67,pv293]) (by decide +kernel)
def pv117787 : PrimeValue := ⟨117787, pr117787⟩
private theorem pr117797 : PrimeCertificate 117797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv601]) (by decide +kernel)
def pv117797 : PrimeValue := ⟨117797, pr117797⟩
private theorem pr117809 : PrimeCertificate 117809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv199]) (by decide +kernel)
def pv117809 : PrimeValue := ⟨117809, pr117809⟩
private theorem pr117811 : PrimeCertificate 117811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv11,pv17]) (by decide +kernel)
def pv117811 : PrimeValue := ⟨117811, pr117811⟩
private theorem pr117833 : PrimeCertificate 117833 :=
  certifyPrime (q := pv19) (ls := [pv2,pv11,pv13,pv103]) (by decide +kernel)
def pv117833 : PrimeValue := ⟨117833, pr117833⟩
private theorem pr117839 : PrimeCertificate 117839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv19,pv443]) (by decide +kernel)
def pv117839 : PrimeValue := ⟨117839, pr117839⟩
private theorem pr117877 : PrimeCertificate 117877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv47]) (by decide +kernel)
def pv117877 : PrimeValue := ⟨117877, pr117877⟩
private theorem pr117881 : PrimeCertificate 117881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv421]) (by decide +kernel)
def pv117881 : PrimeValue := ⟨117881, pr117881⟩
private theorem pr117883 : PrimeCertificate 117883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv59]) (by decide +kernel)
def pv117883 : PrimeValue := ⟨117883, pr117883⟩
private theorem pr117911 : PrimeCertificate 117911 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv13,pv907]) (by decide +kernel)
def pv117911 : PrimeValue := ⟨117911, pr117911⟩
private theorem pr117917 : PrimeCertificate 117917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv719]) (by decide +kernel)
def pv117917 : PrimeValue := ⟨117917, pr117917⟩
private theorem pr117937 : PrimeCertificate 117937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv117937 : PrimeValue := ⟨117937, pr117937⟩
private theorem pr117959 : PrimeCertificate 117959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv58979]) (by decide +kernel)
def pv117959 : PrimeValue := ⟨117959, pr117959⟩
private theorem pr117973 : PrimeCertificate 117973 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv113]) (by decide +kernel)
def pv117973 : PrimeValue := ⟨117973, pr117973⟩
private theorem pr117977 : PrimeCertificate 117977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14747]) (by decide +kernel)
def pv117977 : PrimeValue := ⟨117977, pr117977⟩
private theorem pr117979 : PrimeCertificate 117979 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv53]) (by decide +kernel)
def pv117979 : PrimeValue := ⟨117979, pr117979⟩
private theorem pr117989 : PrimeCertificate 117989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2269]) (by decide +kernel)
def pv117989 : PrimeValue := ⟨117989, pr117989⟩
private theorem pr117991 : PrimeCertificate 117991 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv23]) (by decide +kernel)
def pv117991 : PrimeValue := ⟨117991, pr117991⟩
private theorem pr118033 : PrimeCertificate 118033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2459]) (by decide +kernel)
def pv118033 : PrimeValue := ⟨118033, pr118033⟩
private theorem pr118037 : PrimeCertificate 118037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv1283]) (by decide +kernel)
def pv118037 : PrimeValue := ⟨118037, pr118037⟩
private theorem pr118043 : PrimeCertificate 118043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59021]) (by decide +kernel)
def pv118043 : PrimeValue := ⟨118043, pr118043⟩
private theorem pr118051 : PrimeCertificate 118051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv787]) (by decide +kernel)
def pv118051 : PrimeValue := ⟨118051, pr118051⟩
private theorem pr118057 : PrimeCertificate 118057 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv4919]) (by decide +kernel)
def pv118057 : PrimeValue := ⟨118057, pr118057⟩
private theorem pr118061 : PrimeCertificate 118061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5903]) (by decide +kernel)
def pv118061 : PrimeValue := ⟨118061, pr118061⟩
private theorem pr118081 : PrimeCertificate 118081 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv118081 : PrimeValue := ⟨118081, pr118081⟩
private theorem pr118093 : PrimeCertificate 118093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv757]) (by decide +kernel)
def pv118093 : PrimeValue := ⟨118093, pr118093⟩
private theorem pr118147 : PrimeCertificate 118147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv97]) (by decide +kernel)
def pv118147 : PrimeValue := ⟨118147, pr118147⟩
private theorem pr118163 : PrimeCertificate 118163 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv41,pv131]) (by decide +kernel)
def pv118163 : PrimeValue := ⟨118163, pr118163⟩
private theorem pr118169 : PrimeCertificate 118169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14771]) (by decide +kernel)
def pv118169 : PrimeValue := ⟨118169, pr118169⟩
private theorem pr118211 : PrimeCertificate 118211 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11821]) (by decide +kernel)
def pv118211 : PrimeValue := ⟨118211, pr118211⟩
private theorem pr118213 : PrimeCertificate 118213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9851]) (by decide +kernel)
def pv118213 : PrimeValue := ⟨118213, pr118213⟩
private theorem pr118219 : PrimeCertificate 118219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv19,pv61]) (by decide +kernel)
def pv118219 : PrimeValue := ⟨118219, pr118219⟩
private theorem pr118247 : PrimeCertificate 118247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv59123]) (by decide +kernel)
def pv118247 : PrimeValue := ⟨118247, pr118247⟩
private theorem pr118249 : PrimeCertificate 118249 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv379]) (by decide +kernel)
def pv118249 : PrimeValue := ⟨118249, pr118249⟩
private theorem pr118253 : PrimeCertificate 118253 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv37,pv47]) (by decide +kernel)
def pv118253 : PrimeValue := ⟨118253, pr118253⟩
private theorem pr118259 : PrimeCertificate 118259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8447]) (by decide +kernel)
def pv118259 : PrimeValue := ⟨118259, pr118259⟩
private theorem pr118273 : PrimeCertificate 118273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv118273 : PrimeValue := ⟨118273, pr118273⟩
private theorem pr118277 : PrimeCertificate 118277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29569]) (by decide +kernel)
def pv118277 : PrimeValue := ⟨118277, pr118277⟩
private theorem pr118297 : PrimeCertificate 118297 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv31,pv53]) (by decide +kernel)
def pv118297 : PrimeValue := ⟨118297, pr118297⟩
private theorem pr118361 : PrimeCertificate 118361 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv11,pv269]) (by decide +kernel)
def pv118361 : PrimeValue := ⟨118361, pr118361⟩
private theorem pr118369 : PrimeCertificate 118369 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv137]) (by decide +kernel)
def pv118369 : PrimeValue := ⟨118369, pr118369⟩
private theorem pr118387 : PrimeCertificate 118387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6577]) (by decide +kernel)
def pv118387 : PrimeValue := ⟨118387, pr118387⟩
private theorem pr118399 : PrimeCertificate 118399 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv2819]) (by decide +kernel)
def pv118399 : PrimeValue := ⟨118399, pr118399⟩
private theorem pr118409 : PrimeCertificate 118409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv41]) (by decide +kernel)
def pv118409 : PrimeValue := ⟨118409, pr118409⟩
private theorem pr118411 : PrimeCertificate 118411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3947]) (by decide +kernel)
def pv118411 : PrimeValue := ⟨118411, pr118411⟩
private theorem pr118429 : PrimeCertificate 118429 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv71,pv139]) (by decide +kernel)
def pv118429 : PrimeValue := ⟨118429, pr118429⟩
private theorem pr118453 : PrimeCertificate 118453 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9871]) (by decide +kernel)
def pv118453 : PrimeValue := ⟨118453, pr118453⟩
private theorem pr118463 : PrimeCertificate 118463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv971]) (by decide +kernel)
def pv118463 : PrimeValue := ⟨118463, pr118463⟩
private theorem pr118471 : PrimeCertificate 118471 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv359]) (by decide +kernel)
def pv118471 : PrimeValue := ⟨118471, pr118471⟩
private theorem pr118493 : PrimeCertificate 118493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2693]) (by decide +kernel)
def pv118493 : PrimeValue := ⟨118493, pr118493⟩
private theorem pr118529 : PrimeCertificate 118529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv463]) (by decide +kernel)
def pv118529 : PrimeValue := ⟨118529, pr118529⟩
private theorem pr118543 : PrimeCertificate 118543 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv23,pv859]) (by decide +kernel)
def pv118543 : PrimeValue := ⟨118543, pr118543⟩
private theorem pr118549 : PrimeCertificate 118549 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv37,pv89]) (by decide +kernel)
def pv118549 : PrimeValue := ⟨118549, pr118549⟩
private theorem pr118571 : PrimeCertificate 118571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv71,pv167]) (by decide +kernel)
def pv118571 : PrimeValue := ⟨118571, pr118571⟩
private theorem pr118583 : PrimeCertificate 118583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv211,pv281]) (by decide +kernel)
def pv118583 : PrimeValue := ⟨118583, pr118583⟩
private theorem pr118589 : PrimeCertificate 118589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv1289]) (by decide +kernel)
def pv118589 : PrimeValue := ⟨118589, pr118589⟩
private theorem pr118603 : PrimeCertificate 118603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv599]) (by decide +kernel)
def pv118603 : PrimeValue := ⟨118603, pr118603⟩
private theorem pr118619 : PrimeCertificate 118619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv467]) (by decide +kernel)
def pv118619 : PrimeValue := ⟨118619, pr118619⟩
private theorem pr118621 : PrimeCertificate 118621 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv659]) (by decide +kernel)
def pv118621 : PrimeValue := ⟨118621, pr118621⟩
private theorem pr118633 : PrimeCertificate 118633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4943]) (by decide +kernel)
def pv118633 : PrimeValue := ⟨118633, pr118633⟩
private theorem pr118661 : PrimeCertificate 118661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv349]) (by decide +kernel)
def pv118661 : PrimeValue := ⟨118661, pr118661⟩
private theorem pr118669 : PrimeCertificate 118669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv29,pv31]) (by decide +kernel)
def pv118669 : PrimeValue := ⟨118669, pr118669⟩
private theorem pr118673 : PrimeCertificate 118673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7417]) (by decide +kernel)
def pv118673 : PrimeValue := ⟨118673, pr118673⟩
private theorem pr118681 : PrimeCertificate 118681 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv23,pv43]) (by decide +kernel)
def pv118681 : PrimeValue := ⟨118681, pr118681⟩
private theorem pr118691 : PrimeCertificate 118691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv83]) (by decide +kernel)
def pv118691 : PrimeValue := ⟨118691, pr118691⟩
private theorem pr118709 : PrimeCertificate 118709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv503]) (by decide +kernel)
def pv118709 : PrimeValue := ⟨118709, pr118709⟩
private theorem pr118717 : PrimeCertificate 118717 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv761]) (by decide +kernel)
def pv118717 : PrimeValue := ⟨118717, pr118717⟩
private theorem pr118739 : PrimeCertificate 118739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59369]) (by decide +kernel)
def pv118739 : PrimeValue := ⟨118739, pr118739⟩
private theorem pr118747 : PrimeCertificate 118747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv733]) (by decide +kernel)
def pv118747 : PrimeValue := ⟨118747, pr118747⟩
private theorem pr118751 : PrimeCertificate 118751 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv118751 : PrimeValue := ⟨118751, pr118751⟩
private theorem pr118757 : PrimeCertificate 118757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2699]) (by decide +kernel)
def pv118757 : PrimeValue := ⟨118757, pr118757⟩
private theorem pr118787 : PrimeCertificate 118787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59393]) (by decide +kernel)
def pv118787 : PrimeValue := ⟨118787, pr118787⟩
private theorem pr118799 : PrimeCertificate 118799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv59399]) (by decide +kernel)
def pv118799 : PrimeValue := ⟨118799, pr118799⟩
private theorem pr118801 : PrimeCertificate 118801 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv118801 : PrimeValue := ⟨118801, pr118801⟩
private theorem pr118819 : PrimeCertificate 118819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv41]) (by decide +kernel)
def pv118819 : PrimeValue := ⟨118819, pr118819⟩
private theorem pr118831 : PrimeCertificate 118831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv233]) (by decide +kernel)
def pv118831 : PrimeValue := ⟨118831, pr118831⟩
private theorem pr118843 : PrimeCertificate 118843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv683]) (by decide +kernel)
def pv118843 : PrimeValue := ⟨118843, pr118843⟩
private theorem pr118861 : PrimeCertificate 118861 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv283]) (by decide +kernel)
def pv118861 : PrimeValue := ⟨118861, pr118861⟩
private theorem pr118873 : PrimeCertificate 118873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv127]) (by decide +kernel)
def pv118873 : PrimeValue := ⟨118873, pr118873⟩
private theorem pr118891 : PrimeCertificate 118891 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv1321]) (by decide +kernel)
def pv118891 : PrimeValue := ⟨118891, pr118891⟩
private theorem pr118901 : PrimeCertificate 118901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv41]) (by decide +kernel)
def pv118901 : PrimeValue := ⟨118901, pr118901⟩
private theorem pr118903 : PrimeCertificate 118903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv149]) (by decide +kernel)
def pv118903 : PrimeValue := ⟨118903, pr118903⟩
private theorem pr118913 : PrimeCertificate 118913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv929]) (by decide +kernel)
def pv118913 : PrimeValue := ⟨118913, pr118913⟩
private theorem pr118927 : PrimeCertificate 118927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6607]) (by decide +kernel)
def pv118927 : PrimeValue := ⟨118927, pr118927⟩
private theorem pr118931 : PrimeCertificate 118931 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv1699]) (by decide +kernel)
def pv118931 : PrimeValue := ⟨118931, pr118931⟩
private theorem pr118967 : PrimeCertificate 118967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv3499]) (by decide +kernel)
def pv118967 : PrimeValue := ⟨118967, pr118967⟩
private theorem pr118973 : PrimeCertificate 118973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv607]) (by decide +kernel)
def pv118973 : PrimeValue := ⟨118973, pr118973⟩
private theorem pr119027 : PrimeCertificate 119027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59513]) (by decide +kernel)
def pv119027 : PrimeValue := ⟨119027, pr119027⟩
private theorem pr119033 : PrimeCertificate 119033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14879]) (by decide +kernel)
def pv119033 : PrimeValue := ⟨119033, pr119033⟩
private theorem pr119039 : PrimeCertificate 119039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv53,pv1123]) (by decide +kernel)
def pv119039 : PrimeValue := ⟨119039, pr119039⟩
private theorem pr119047 : PrimeCertificate 119047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19841]) (by decide +kernel)
def pv119047 : PrimeValue := ⟨119047, pr119047⟩
private theorem pr119057 : PrimeCertificate 119057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv1063]) (by decide +kernel)
def pv119057 : PrimeValue := ⟨119057, pr119057⟩
private theorem pr119069 : PrimeCertificate 119069 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv103]) (by decide +kernel)
def pv119069 : PrimeValue := ⟨119069, pr119069⟩
private theorem pr119083 : PrimeCertificate 119083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv223]) (by decide +kernel)
def pv119083 : PrimeValue := ⟨119083, pr119083⟩
private theorem pr119087 : PrimeCertificate 119087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv5413]) (by decide +kernel)
def pv119087 : PrimeValue := ⟨119087, pr119087⟩
private theorem pr119089 : PrimeCertificate 119089 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv827]) (by decide +kernel)
def pv119089 : PrimeValue := ⟨119089, pr119089⟩
private theorem pr119101 : PrimeCertificate 119101 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv397]) (by decide +kernel)
def pv119101 : PrimeValue := ⟨119101, pr119101⟩
private theorem pr119107 : PrimeCertificate 119107 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv509]) (by decide +kernel)
def pv119107 : PrimeValue := ⟨119107, pr119107⟩
private theorem pr119129 : PrimeCertificate 119129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14891]) (by decide +kernel)
def pv119129 : PrimeValue := ⟨119129, pr119129⟩
private theorem pr119131 : PrimeCertificate 119131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv19]) (by decide +kernel)
def pv119131 : PrimeValue := ⟨119131, pr119131⟩
private theorem pr119159 : PrimeCertificate 119159 :=
  certifyPrime (q := pv17) (ls := [pv2,pv13,pv4583]) (by decide +kernel)
def pv119159 : PrimeValue := ⟨119159, pr119159⟩
private theorem pr119173 : PrimeCertificate 119173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9931]) (by decide +kernel)
def pv119173 : PrimeValue := ⟨119173, pr119173⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
