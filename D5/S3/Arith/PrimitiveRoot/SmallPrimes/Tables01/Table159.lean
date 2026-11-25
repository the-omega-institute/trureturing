/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table159
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table159.pv130729
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr130729 : PrimeCertificate 130729 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv13,pv419]) (by decide +kernel)
def pv130729 : PrimeValue := ⟨130729, pr130729⟩
private theorem pr130769 : PrimeCertificate 130769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv743]) (by decide +kernel)
def pv130769 : PrimeValue := ⟨130769, pr130769⟩
private theorem pr130817 : PrimeCertificate 130817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv73]) (by decide +kernel)
def pv130817 : PrimeValue := ⟨130817, pr130817⟩
private theorem pr130859 : PrimeCertificate 130859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv719]) (by decide +kernel)
def pv130859 : PrimeValue := ⟨130859, pr130859⟩
private theorem pr131011 : PrimeCertificate 131011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv397]) (by decide +kernel)
def pv131011 : PrimeValue := ⟨131011, pr131011⟩
private theorem pr131023 : PrimeCertificate 131023 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv251]) (by decide +kernel)
def pv131023 : PrimeValue := ⟨131023, pr131023⟩
private theorem pr131479 : PrimeCertificate 131479 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv17,pv1289]) (by decide +kernel)
def pv131479 : PrimeValue := ⟨131479, pr131479⟩
private theorem pr131507 : PrimeCertificate 131507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1399]) (by decide +kernel)
def pv131507 : PrimeValue := ⟨131507, pr131507⟩
private theorem pr131581 : PrimeCertificate 131581 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv43]) (by decide +kernel)
def pv131581 : PrimeValue := ⟨131581, pr131581⟩
private theorem pr132833 : PrimeCertificate 132833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv593]) (by decide +kernel)
def pv132833 : PrimeValue := ⟨132833, pr132833⟩
private theorem pr133103 : PrimeCertificate 133103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv1091]) (by decide +kernel)
def pv133103 : PrimeValue := ⟨133103, pr133103⟩
private theorem pr133117 : PrimeCertificate 133117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11093]) (by decide +kernel)
def pv133117 : PrimeValue := ⟨133117, pr133117⟩
private theorem pr133153 : PrimeCertificate 133153 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv73]) (by decide +kernel)
def pv133153 : PrimeValue := ⟨133153, pr133153⟩
private theorem pr133201 : PrimeCertificate 133201 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv133201 : PrimeValue := ⟨133201, pr133201⟩
private theorem pr133283 : PrimeCertificate 133283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv647]) (by decide +kernel)
def pv133283 : PrimeValue := ⟨133283, pr133283⟩
private theorem pr133417 : PrimeCertificate 133417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv109]) (by decide +kernel)
def pv133417 : PrimeValue := ⟨133417, pr133417⟩
private theorem pr133801 : PrimeCertificate 133801 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv223]) (by decide +kernel)
def pv133801 : PrimeValue := ⟨133801, pr133801⟩
private theorem pr134177 : PrimeCertificate 134177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv599]) (by decide +kernel)
def pv134177 : PrimeValue := ⟨134177, pr134177⟩
private theorem pr134341 : PrimeCertificate 134341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2239]) (by decide +kernel)
def pv134341 : PrimeValue := ⟨134341, pr134341⟩
private theorem pr134731 : PrimeCertificate 134731 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv499]) (by decide +kernel)
def pv134731 : PrimeValue := ⟨134731, pr134731⟩
private theorem pr134741 : PrimeCertificate 134741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6737]) (by decide +kernel)
def pv134741 : PrimeValue := ⟨134741, pr134741⟩
private theorem pr134839 : PrimeCertificate 134839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv227]) (by decide +kernel)
def pv134839 : PrimeValue := ⟨134839, pr134839⟩
private theorem pr134917 : PrimeCertificate 134917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11243]) (by decide +kernel)
def pv134917 : PrimeValue := ⟨134917, pr134917⟩
private theorem pr135077 : PrimeCertificate 135077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33769]) (by decide +kernel)
def pv135077 : PrimeValue := ⟨135077, pr135077⟩
private theorem pr135181 : PrimeCertificate 135181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv751]) (by decide +kernel)
def pv135181 : PrimeValue := ⟨135181, pr135181⟩
private theorem pr135607 : PrimeCertificate 135607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv97,pv233]) (by decide +kernel)
def pv135607 : PrimeValue := ⟨135607, pr135607⟩
private theorem pr135623 : PrimeCertificate 135623 :=
  certifyPrime (q := pv11) (ls := [pv2,pv19,pv43,pv83]) (by decide +kernel)
def pv135623 : PrimeValue := ⟨135623, pr135623⟩
private theorem pr135829 : PrimeCertificate 135829 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv135829 : PrimeValue := ⟨135829, pr135829⟩
private theorem pr135979 : PrimeCertificate 135979 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv131,pv173]) (by decide +kernel)
def pv135979 : PrimeValue := ⟨135979, pr135979⟩
private theorem pr136043 : PrimeCertificate 136043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv251,pv271]) (by decide +kernel)
def pv136043 : PrimeValue := ⟨136043, pr136043⟩
private theorem pr136099 : PrimeCertificate 136099 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7561]) (by decide +kernel)
def pv136099 : PrimeValue := ⟨136099, pr136099⟩
private theorem pr136163 : PrimeCertificate 136163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv5237]) (by decide +kernel)
def pv136163 : PrimeValue := ⟨136163, pr136163⟩
private theorem pr136177 : PrimeCertificate 136177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2837]) (by decide +kernel)
def pv136177 : PrimeValue := ⟨136177, pr136177⟩
private theorem pr136309 : PrimeCertificate 136309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv307]) (by decide +kernel)
def pv136309 : PrimeValue := ⟨136309, pr136309⟩
private theorem pr136621 : PrimeCertificate 136621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv23]) (by decide +kernel)
def pv136621 : PrimeValue := ⟨136621, pr136621⟩
private theorem pr136711 : PrimeCertificate 136711 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv136711 : PrimeValue := ⟨136711, pr136711⟩
private theorem pr136777 : PrimeCertificate 136777 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv41,pv139]) (by decide +kernel)
def pv136777 : PrimeValue := ⟨136777, pr136777⟩
private theorem pr137117 : PrimeCertificate 137117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv59,pv83]) (by decide +kernel)
def pv137117 : PrimeValue := ⟨137117, pr137117⟩
private theorem pr137131 : PrimeCertificate 137131 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv653]) (by decide +kernel)
def pv137131 : PrimeValue := ⟨137131, pr137131⟩
private theorem pr137183 : PrimeCertificate 137183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv113,pv607]) (by decide +kernel)
def pv137183 : PrimeValue := ⟨137183, pr137183⟩
private theorem pr137537 : PrimeCertificate 137537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv307]) (by decide +kernel)
def pv137537 : PrimeValue := ⟨137537, pr137537⟩
private theorem pr137713 : PrimeCertificate 137713 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv19,pv151]) (by decide +kernel)
def pv137713 : PrimeValue := ⟨137713, pr137713⟩
private theorem pr138077 : PrimeCertificate 138077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv34519]) (by decide +kernel)
def pv138077 : PrimeValue := ⟨138077, pr138077⟩
private theorem pr138401 : PrimeCertificate 138401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv173]) (by decide +kernel)
def pv138401 : PrimeValue := ⟨138401, pr138401⟩
private theorem pr138637 : PrimeCertificate 138637 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv3851]) (by decide +kernel)
def pv138637 : PrimeValue := ⟨138637, pr138637⟩
private theorem pr138647 : PrimeCertificate 138647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv181,pv383]) (by decide +kernel)
def pv138647 : PrimeValue := ⟨138647, pr138647⟩
private theorem pr138679 : PrimeCertificate 138679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv797]) (by decide +kernel)
def pv138679 : PrimeValue := ⟨138679, pr138679⟩
private theorem pr138829 : PrimeCertificate 138829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv503]) (by decide +kernel)
def pv138829 : PrimeValue := ⟨138829, pr138829⟩
private theorem pr138967 : PrimeCertificate 138967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv23,pv53]) (by decide +kernel)
def pv138967 : PrimeValue := ⟨138967, pr138967⟩
private theorem pr139199 : PrimeCertificate 139199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv79,pv881]) (by decide +kernel)
def pv139199 : PrimeValue := ⟨139199, pr139199⟩
private theorem pr139241 : PrimeCertificate 139241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv59]) (by decide +kernel)
def pv139241 : PrimeValue := ⟨139241, pr139241⟩
private theorem pr139309 : PrimeCertificate 139309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv19,pv47]) (by decide +kernel)
def pv139309 : PrimeValue := ⟨139309, pr139309⟩
private theorem pr139361 : PrimeCertificate 139361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv67]) (by decide +kernel)
def pv139361 : PrimeValue := ⟨139361, pr139361⟩
private theorem pr139369 : PrimeCertificate 139369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5807]) (by decide +kernel)
def pv139369 : PrimeValue := ⟨139369, pr139369⟩
private theorem pr139609 : PrimeCertificate 139609 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv277]) (by decide +kernel)
def pv139609 : PrimeValue := ⟨139609, pr139609⟩
private theorem pr139901 : PrimeCertificate 139901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1399]) (by decide +kernel)
def pv139901 : PrimeValue := ⟨139901, pr139901⟩
private theorem pr139921 : PrimeCertificate 139921 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv53]) (by decide +kernel)
def pv139921 : PrimeValue := ⟨139921, pr139921⟩
private theorem pr139999 : PrimeCertificate 139999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23333]) (by decide +kernel)
def pv139999 : PrimeValue := ⟨139999, pr139999⟩
private theorem pr140333 : PrimeCertificate 140333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv35083]) (by decide +kernel)
def pv140333 : PrimeValue := ⟨140333, pr140333⟩
private theorem pr140381 : PrimeCertificate 140381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7019]) (by decide +kernel)
def pv140381 : PrimeValue := ⟨140381, pr140381⟩
private theorem pr140411 : PrimeCertificate 140411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv739]) (by decide +kernel)
def pv140411 : PrimeValue := ⟨140411, pr140411⟩
private theorem pr140527 : PrimeCertificate 140527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv211]) (by decide +kernel)
def pv140527 : PrimeValue := ⟨140527, pr140527⟩
private theorem pr140827 : PrimeCertificate 140827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv479]) (by decide +kernel)
def pv140827 : PrimeValue := ⟨140827, pr140827⟩
private theorem pr140893 : PrimeCertificate 140893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv199]) (by decide +kernel)
def pv140893 : PrimeValue := ⟨140893, pr140893⟩
private theorem pr141233 : PrimeCertificate 141233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv97]) (by decide +kernel)
def pv141233 : PrimeValue := ⟨141233, pr141233⟩
private theorem pr141269 : PrimeCertificate 141269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv35317]) (by decide +kernel)
def pv141269 : PrimeValue := ⟨141269, pr141269⟩
private theorem pr141301 : PrimeCertificate 141301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv157]) (by decide +kernel)
def pv141301 : PrimeValue := ⟨141301, pr141301⟩
private theorem pr141311 : PrimeCertificate 141311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv1087]) (by decide +kernel)
def pv141311 : PrimeValue := ⟨141311, pr141311⟩
private theorem pr141697 : PrimeCertificate 141697 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv141697 : PrimeValue := ⟨141697, pr141697⟩
private theorem pr141829 : PrimeCertificate 141829 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv53,pv223]) (by decide +kernel)
def pv141829 : PrimeValue := ⟨141829, pr141829⟩
private theorem pr141851 : PrimeCertificate 141851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2837]) (by decide +kernel)
def pv141851 : PrimeValue := ⟨141851, pr141851⟩
private theorem pr141863 : PrimeCertificate 141863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv10133]) (by decide +kernel)
def pv141863 : PrimeValue := ⟨141863, pr141863⟩
private theorem pr141971 : PrimeCertificate 141971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv14197]) (by decide +kernel)
def pv141971 : PrimeValue := ⟨141971, pr141971⟩
private theorem pr142183 : PrimeCertificate 142183 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv2633]) (by decide +kernel)
def pv142183 : PrimeValue := ⟨142183, pr142183⟩
private theorem pr142217 : PrimeCertificate 142217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv613]) (by decide +kernel)
def pv142217 : PrimeValue := ⟨142217, pr142217⟩
private theorem pr142237 : PrimeCertificate 142237 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv439]) (by decide +kernel)
def pv142237 : PrimeValue := ⟨142237, pr142237⟩
private theorem pr142357 : PrimeCertificate 142357 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11863]) (by decide +kernel)
def pv142357 : PrimeValue := ⟨142357, pr142357⟩
private theorem pr142567 : PrimeCertificate 142567 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv23761]) (by decide +kernel)
def pv142567 : PrimeValue := ⟨142567, pr142567⟩
private theorem pr142697 : PrimeCertificate 142697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17837]) (by decide +kernel)
def pv142697 : PrimeValue := ⟨142697, pr142697⟩
private theorem pr142787 : PrimeCertificate 142787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv47]) (by decide +kernel)
def pv142787 : PrimeValue := ⟨142787, pr142787⟩
private theorem pr143197 : PrimeCertificate 143197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11933]) (by decide +kernel)
def pv143197 : PrimeValue := ⟨143197, pr143197⟩
private theorem pr143257 : PrimeCertificate 143257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv127]) (by decide +kernel)
def pv143257 : PrimeValue := ⟨143257, pr143257⟩
private theorem pr143779 : PrimeCertificate 143779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv773]) (by decide +kernel)
def pv143779 : PrimeValue := ⟨143779, pr143779⟩
private theorem pr143791 : PrimeCertificate 143791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv4793]) (by decide +kernel)
def pv143791 : PrimeValue := ⟨143791, pr143791⟩
private theorem pr144173 : PrimeCertificate 144173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv271]) (by decide +kernel)
def pv144173 : PrimeValue := ⟨144173, pr144173⟩
private theorem pr145009 : PrimeCertificate 145009 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv53]) (by decide +kernel)
def pv145009 : PrimeValue := ⟨145009, pr145009⟩
private theorem pr145219 : PrimeCertificate 145219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24203]) (by decide +kernel)
def pv145219 : PrimeValue := ⟨145219, pr145219⟩
private theorem pr145259 : PrimeCertificate 145259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv1231]) (by decide +kernel)
def pv145259 : PrimeValue := ⟨145259, pr145259⟩
private theorem pr145303 : PrimeCertificate 145303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61,pv397]) (by decide +kernel)
def pv145303 : PrimeValue := ⟨145303, pr145303⟩
private theorem pr145361 : PrimeCertificate 145361 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv23,pv79]) (by decide +kernel)
def pv145361 : PrimeValue := ⟨145361, pr145361⟩
private theorem pr145391 : PrimeCertificate 145391 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv31,pv67]) (by decide +kernel)
def pv145391 : PrimeValue := ⟨145391, pr145391⟩
private theorem pr145463 : PrimeCertificate 145463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv257,pv283]) (by decide +kernel)
def pv145463 : PrimeValue := ⟨145463, pr145463⟩
private theorem pr145517 : PrimeCertificate 145517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv5197]) (by decide +kernel)
def pv145517 : PrimeValue := ⟨145517, pr145517⟩
private theorem pr145687 : PrimeCertificate 145687 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv24281]) (by decide +kernel)
def pv145687 : PrimeValue := ⟨145687, pr145687⟩
private theorem pr145777 : PrimeCertificate 145777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3037]) (by decide +kernel)
def pv145777 : PrimeValue := ⟨145777, pr145777⟩
private theorem pr145819 : PrimeCertificate 145819 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv8101]) (by decide +kernel)
def pv145819 : PrimeValue := ⟨145819, pr145819⟩
private theorem pr145861 : PrimeCertificate 145861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv13,pv17]) (by decide +kernel)
def pv145861 : PrimeValue := ⟨145861, pr145861⟩
private theorem pr146059 : PrimeCertificate 146059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv2213]) (by decide +kernel)
def pv146059 : PrimeValue := ⟨146059, pr146059⟩
private theorem pr146239 : PrimeCertificate 146239 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv24373]) (by decide +kernel)
def pv146239 : PrimeValue := ⟨146239, pr146239⟩
private theorem pr146273 : PrimeCertificate 146273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv653]) (by decide +kernel)
def pv146273 : PrimeValue := ⟨146273, pr146273⟩
private theorem pr146299 : PrimeCertificate 146299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv659]) (by decide +kernel)
def pv146299 : PrimeValue := ⟨146299, pr146299⟩
private theorem pr146389 : PrimeCertificate 146389 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv1109]) (by decide +kernel)
def pv146389 : PrimeValue := ⟨146389, pr146389⟩
private theorem pr146417 : PrimeCertificate 146417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9151]) (by decide +kernel)
def pv146417 : PrimeValue := ⟨146417, pr146417⟩
private theorem pr146449 : PrimeCertificate 146449 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv113]) (by decide +kernel)
def pv146449 : PrimeValue := ⟨146449, pr146449⟩
private theorem pr146719 : PrimeCertificate 146719 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv13,pv19]) (by decide +kernel)
def pv146719 : PrimeValue := ⟨146719, pr146719⟩
private theorem pr146749 : PrimeCertificate 146749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1747]) (by decide +kernel)
def pv146749 : PrimeValue := ⟨146749, pr146749⟩
private theorem pr146777 : PrimeCertificate 146777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2621]) (by decide +kernel)
def pv146777 : PrimeValue := ⟨146777, pr146777⟩
private theorem pr146843 : PrimeCertificate 146843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73421]) (by decide +kernel)
def pv146843 : PrimeValue := ⟨146843, pr146843⟩
private theorem pr146933 : PrimeCertificate 146933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv337]) (by decide +kernel)
def pv146933 : PrimeValue := ⟨146933, pr146933⟩
private theorem pr146941 : PrimeCertificate 146941 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv31,pv79]) (by decide +kernel)
def pv146941 : PrimeValue := ⟨146941, pr146941⟩
private theorem pr146977 : PrimeCertificate 146977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1531]) (by decide +kernel)
def pv146977 : PrimeValue := ⟨146977, pr146977⟩
private theorem pr146987 : PrimeCertificate 146987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv10499]) (by decide +kernel)
def pv146987 : PrimeValue := ⟨146987, pr146987⟩
private theorem pr147139 : PrimeCertificate 147139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137,pv179]) (by decide +kernel)
def pv147139 : PrimeValue := ⟨147139, pr147139⟩
private theorem pr147391 : PrimeCertificate 147391 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv147391 : PrimeValue := ⟨147391, pr147391⟩
private theorem pr147709 : PrimeCertificate 147709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv373]) (by decide +kernel)
def pv147709 : PrimeValue := ⟨147709, pr147709⟩
private theorem pr147727 : PrimeCertificate 147727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv283]) (by decide +kernel)
def pv147727 : PrimeValue := ⟨147727, pr147727⟩
private theorem pr147761 : PrimeCertificate 147761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1847]) (by decide +kernel)
def pv147761 : PrimeValue := ⟨147761, pr147761⟩
private theorem pr147853 : PrimeCertificate 147853 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv147853 : PrimeValue := ⟨147853, pr147853⟩
private theorem pr147949 : PrimeCertificate 147949 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv12329]) (by decide +kernel)
def pv147949 : PrimeValue := ⟨147949, pr147949⟩
private theorem pr148387 : PrimeCertificate 148387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv3533]) (by decide +kernel)
def pv148387 : PrimeValue := ⟨148387, pr148387⟩
private theorem pr148513 : PrimeCertificate 148513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv148513 : PrimeValue := ⟨148513, pr148513⟩
private theorem pr148727 : PrimeCertificate 148727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv74363]) (by decide +kernel)
def pv148727 : PrimeValue := ⟨148727, pr148727⟩
private theorem pr148793 : PrimeCertificate 148793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2657]) (by decide +kernel)
def pv148793 : PrimeValue := ⟨148793, pr148793⟩
private theorem pr148817 : PrimeCertificate 148817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv131]) (by decide +kernel)
def pv148817 : PrimeValue := ⟨148817, pr148817⟩
private theorem pr148961 : PrimeCertificate 148961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv19]) (by decide +kernel)
def pv148961 : PrimeValue := ⟨148961, pr148961⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
