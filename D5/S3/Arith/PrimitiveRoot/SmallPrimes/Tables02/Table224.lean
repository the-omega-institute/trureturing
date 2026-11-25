/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table224
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table224.pv981697
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table056
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table057

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr981697 : PrimeCertificate 981697 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5113]) (by decide +kernel)
def pv981697 : PrimeValue := ⟨981697, pr981697⟩
private theorem pr981817 : PrimeCertificate 981817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv3719]) (by decide +kernel)
def pv981817 : PrimeValue := ⟨981817, pr981817⟩
private theorem pr981823 : PrimeCertificate 981823 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv163637]) (by decide +kernel)
def pv981823 : PrimeValue := ⟨981823, pr981823⟩
private theorem pr982057 : PrimeCertificate 982057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv29,pv83]) (by decide +kernel)
def pv982057 : PrimeValue := ⟨982057, pr982057⟩
private theorem pr982183 : PrimeCertificate 982183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv163697]) (by decide +kernel)
def pv982183 : PrimeValue := ⟨982183, pr982183⟩
private theorem pr982339 : PrimeCertificate 982339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv1231]) (by decide +kernel)
def pv982339 : PrimeValue := ⟨982339, pr982339⟩
private theorem pr982489 : PrimeCertificate 982489 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv47,pv67]) (by decide +kernel)
def pv982489 : PrimeValue := ⟨982489, pr982489⟩
private theorem pr982573 : PrimeCertificate 982573 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv37,pv2213]) (by decide +kernel)
def pv982573 : PrimeValue := ⟨982573, pr982573⟩
private theorem pr982843 : PrimeCertificate 982843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv3343]) (by decide +kernel)
def pv982843 : PrimeValue := ⟨982843, pr982843⟩
private theorem pr982867 : PrimeCertificate 982867 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv163811]) (by decide +kernel)
def pv982867 : PrimeValue := ⟨982867, pr982867⟩
private theorem pr982939 : PrimeCertificate 982939 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv53,pv281]) (by decide +kernel)
def pv982939 : PrimeValue := ⟨982939, pr982939⟩
private theorem pr983179 : PrimeCertificate 983179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv983179 : PrimeValue := ⟨983179, pr983179⟩
private theorem pr983299 : PrimeCertificate 983299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv163883]) (by decide +kernel)
def pv983299 : PrimeValue := ⟨983299, pr983299⟩
private theorem pr983317 : PrimeCertificate 983317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv81943]) (by decide +kernel)
def pv983317 : PrimeValue := ⟨983317, pr983317⟩
private theorem pr983377 : PrimeCertificate 983377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6829]) (by decide +kernel)
def pv983377 : PrimeValue := ⟨983377, pr983377⟩
private theorem pr983443 : PrimeCertificate 983443 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv2687]) (by decide +kernel)
def pv983443 : PrimeValue := ⟨983443, pr983443⟩
private theorem pr983527 : PrimeCertificate 983527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv7127]) (by decide +kernel)
def pv983527 : PrimeValue := ⟨983527, pr983527⟩
private theorem pr983863 : PrimeCertificate 983863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv4969]) (by decide +kernel)
def pv983863 : PrimeValue := ⟨983863, pr983863⟩
private theorem pr984127 : PrimeCertificate 984127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv31,pv37]) (by decide +kernel)
def pv984127 : PrimeValue := ⟨984127, pr984127⟩
private theorem pr984307 : PrimeCertificate 984307 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv164051]) (by decide +kernel)
def pv984307 : PrimeValue := ⟨984307, pr984307⟩
private theorem pr984349 : PrimeCertificate 984349 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv37,pv739]) (by decide +kernel)
def pv984349 : PrimeValue := ⟨984349, pr984349⟩
private theorem pr984367 : PrimeCertificate 984367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv18229]) (by decide +kernel)
def pv984367 : PrimeValue := ⟨984367, pr984367⟩
private theorem pr984427 : PrimeCertificate 984427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv164071]) (by decide +kernel)
def pv984427 : PrimeValue := ⟨984427, pr984427⟩
private theorem pr984817 : PrimeCertificate 984817 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv7,pv977]) (by decide +kernel)
def pv984817 : PrimeValue := ⟨984817, pr984817⟩
private theorem pr985063 : PrimeCertificate 985063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv73,pv173]) (by decide +kernel)
def pv985063 : PrimeValue := ⟨985063, pr985063⟩
private theorem pr985279 : PrimeCertificate 985279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23459]) (by decide +kernel)
def pv985279 : PrimeValue := ⟨985279, pr985279⟩
private theorem pr985417 : PrimeCertificate 985417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv2161]) (by decide +kernel)
def pv985417 : PrimeValue := ⟨985417, pr985417⟩
private theorem pr985483 : PrimeCertificate 985483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv1033]) (by decide +kernel)
def pv985483 : PrimeValue := ⟨985483, pr985483⟩
private theorem pr985903 : PrimeCertificate 985903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv4441]) (by decide +kernel)
def pv985903 : PrimeValue := ⟨985903, pr985903⟩
private theorem pr986047 : PrimeCertificate 986047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv164341]) (by decide +kernel)
def pv986047 : PrimeValue := ⟨986047, pr986047⟩
private theorem pr986149 : PrimeCertificate 986149 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv397]) (by decide +kernel)
def pv986149 : PrimeValue := ⟨986149, pr986149⟩
private theorem pr986197 : PrimeCertificate 986197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv82183]) (by decide +kernel)
def pv986197 : PrimeValue := ⟨986197, pr986197⟩
private theorem pr986509 : PrimeCertificate 986509 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv67,pv409]) (by decide +kernel)
def pv986509 : PrimeValue := ⟨986509, pr986509⟩
private theorem pr986617 : PrimeCertificate 986617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71,pv193]) (by decide +kernel)
def pv986617 : PrimeValue := ⟨986617, pr986617⟩
private theorem pr986707 : PrimeCertificate 986707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv191]) (by decide +kernel)
def pv986707 : PrimeValue := ⟨986707, pr986707⟩
private theorem pr986749 : PrimeCertificate 986749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv691]) (by decide +kernel)
def pv986749 : PrimeValue := ⟨986749, pr986749⟩
private theorem pr987043 : PrimeCertificate 987043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv71,pv331]) (by decide +kernel)
def pv987043 : PrimeValue := ⟨987043, pr987043⟩
private theorem pr987079 : PrimeCertificate 987079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv164513]) (by decide +kernel)
def pv987079 : PrimeValue := ⟨987079, pr987079⟩
private theorem pr987433 : PrimeCertificate 987433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41143]) (by decide +kernel)
def pv987433 : PrimeValue := ⟨987433, pr987433⟩
private theorem pr987793 : PrimeCertificate 987793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv1583]) (by decide +kernel)
def pv987793 : PrimeValue := ⟨987793, pr987793⟩
private theorem pr987997 : PrimeCertificate 987997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv281,pv293]) (by decide +kernel)
def pv987997 : PrimeValue := ⟨987997, pr987997⟩
private theorem pr988297 : PrimeCertificate 988297 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv41179]) (by decide +kernel)
def pv988297 : PrimeValue := ⟨988297, pr988297⟩
private theorem pr988417 : PrimeCertificate 988417 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv988417 : PrimeValue := ⟨988417, pr988417⟩
private theorem pr988453 : PrimeCertificate 988453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv27457]) (by decide +kernel)
def pv988453 : PrimeValue := ⟨988453, pr988453⟩
private theorem pr988579 : PrimeCertificate 988579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18307]) (by decide +kernel)
def pv988579 : PrimeValue := ⟨988579, pr988579⟩
private theorem pr988789 : PrimeCertificate 988789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv37,pv131]) (by decide +kernel)
def pv988789 : PrimeValue := ⟨988789, pr988789⟩
private theorem pr989239 : PrimeCertificate 989239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv2087]) (by decide +kernel)
def pv989239 : PrimeValue := ⟨989239, pr989239⟩
private theorem pr989347 : PrimeCertificate 989347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv181,pv911]) (by decide +kernel)
def pv989347 : PrimeValue := ⟨989347, pr989347⟩
private theorem pr989377 : PrimeCertificate 989377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5153]) (by decide +kernel)
def pv989377 : PrimeValue := ⟨989377, pr989377⟩
private theorem pr989647 : PrimeCertificate 989647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv23563]) (by decide +kernel)
def pv989647 : PrimeValue := ⟨989647, pr989647⟩
private theorem pr989839 : PrimeCertificate 989839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv127,pv433]) (by decide +kernel)
def pv989839 : PrimeValue := ⟨989839, pr989839⟩
private theorem pr989869 : PrimeCertificate 989869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv7499]) (by decide +kernel)
def pv989869 : PrimeValue := ⟨989869, pr989869⟩
private theorem pr990013 : PrimeCertificate 990013 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv23,pv211]) (by decide +kernel)
def pv990013 : PrimeValue := ⟨990013, pr990013⟩
private theorem pr990307 : PrimeCertificate 990307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6113]) (by decide +kernel)
def pv990307 : PrimeValue := ⟨990307, pr990307⟩
private theorem pr990469 : PrimeCertificate 990469 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv1019]) (by decide +kernel)
def pv990469 : PrimeValue := ⟨990469, pr990469⟩
private theorem pr990487 : PrimeCertificate 990487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1123]) (by decide +kernel)
def pv990487 : PrimeValue := ⟨990487, pr990487⟩
private theorem pr990523 : PrimeCertificate 990523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv17,pv83]) (by decide +kernel)
def pv990523 : PrimeValue := ⟨990523, pr990523⟩
private theorem pr990559 : PrimeCertificate 990559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv113,pv487]) (by decide +kernel)
def pv990559 : PrimeValue := ⟨990559, pr990559⟩
private theorem pr990637 : PrimeCertificate 990637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv2663]) (by decide +kernel)
def pv990637 : PrimeValue := ⟨990637, pr990637⟩
private theorem pr990973 : PrimeCertificate 990973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv27527]) (by decide +kernel)
def pv990973 : PrimeValue := ⟨990973, pr990973⟩
private theorem pr991057 : PrimeCertificate 991057 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv1877]) (by decide +kernel)
def pv991057 : PrimeValue := ⟨991057, pr991057⟩
private theorem pr991069 : PrimeCertificate 991069 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv6353]) (by decide +kernel)
def pv991069 : PrimeValue := ⟨991069, pr991069⟩
private theorem pr991129 : PrimeCertificate 991129 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv61,pv677]) (by decide +kernel)
def pv991129 : PrimeValue := ⟨991129, pr991129⟩
private theorem pr991147 : PrimeCertificate 991147 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv97,pv131]) (by decide +kernel)
def pv991147 : PrimeValue := ⟨991147, pr991147⟩
private theorem pr991327 : PrimeCertificate 991327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23603]) (by decide +kernel)
def pv991327 : PrimeValue := ⟨991327, pr991327⟩
private theorem pr991447 : PrimeCertificate 991447 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv149,pv1109]) (by decide +kernel)
def pv991447 : PrimeValue := ⟨991447, pr991447⟩
private theorem pr991693 : PrimeCertificate 991693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv163]) (by decide +kernel)
def pv991693 : PrimeValue := ⟨991693, pr991693⟩
private theorem pr991873 : PrimeCertificate 991873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv41]) (by decide +kernel)
def pv991873 : PrimeValue := ⟨991873, pr991873⟩
private theorem pr991957 : PrimeCertificate 991957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv241]) (by decide +kernel)
def pv991957 : PrimeValue := ⟨991957, pr991957⟩
private theorem pr992113 : PrimeCertificate 992113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1879]) (by decide +kernel)
def pv992113 : PrimeValue := ⟨992113, pr992113⟩
private theorem pr992179 : PrimeCertificate 992179 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv5011]) (by decide +kernel)
def pv992179 : PrimeValue := ⟨992179, pr992179⟩
private theorem pr992317 : PrimeCertificate 992317 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv6361]) (by decide +kernel)
def pv992317 : PrimeValue := ⟨992317, pr992317⟩
private theorem pr992359 : PrimeCertificate 992359 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv23,pv47]) (by decide +kernel)
def pv992359 : PrimeValue := ⟨992359, pr992359⟩
private theorem pr992539 : PrimeCertificate 992539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv823]) (by decide +kernel)
def pv992539 : PrimeValue := ⟨992539, pr992539⟩
private theorem pr992623 : PrimeCertificate 992623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv165437]) (by decide +kernel)
def pv992623 : PrimeValue := ⟨992623, pr992623⟩
private theorem pr992737 : PrimeCertificate 992737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv383]) (by decide +kernel)
def pv992737 : PrimeValue := ⟨992737, pr992737⟩
private theorem pr993103 : PrimeCertificate 993103 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv41,pv367]) (by decide +kernel)
def pv993103 : PrimeValue := ⟨993103, pr993103⟩
private theorem pr993283 : PrimeCertificate 993283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv8713]) (by decide +kernel)
def pv993283 : PrimeValue := ⟨993283, pr993283⟩
private theorem pr993367 : PrimeCertificate 993367 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv29,pv173]) (by decide +kernel)
def pv993367 : PrimeValue := ⟨993367, pr993367⟩
private theorem pr993493 : PrimeCertificate 993493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9199]) (by decide +kernel)
def pv993493 : PrimeValue := ⟨993493, pr993493⟩
private theorem pr993589 : PrimeCertificate 993589 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv82799]) (by decide +kernel)
def pv993589 : PrimeValue := ⟨993589, pr993589⟩
private theorem pr993679 : PrimeCertificate 993679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv59,pv401]) (by decide +kernel)
def pv993679 : PrimeValue := ⟨993679, pr993679⟩
private theorem pr993793 : PrimeCertificate 993793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv647]) (by decide +kernel)
def pv993793 : PrimeValue := ⟨993793, pr993793⟩
private theorem pr993919 : PrimeCertificate 993919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv165653]) (by decide +kernel)
def pv993919 : PrimeValue := ⟨993919, pr993919⟩
private theorem pr994183 : PrimeCertificate 994183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23671]) (by decide +kernel)
def pv994183 : PrimeValue := ⟨994183, pr994183⟩
private theorem pr994237 : PrimeCertificate 994237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv2857]) (by decide +kernel)
def pv994237 : PrimeValue := ⟨994237, pr994237⟩
private theorem pr994363 : PrimeCertificate 994363 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103,pv1609]) (by decide +kernel)
def pv994363 : PrimeValue := ⟨994363, pr994363⟩
private theorem pr994393 : PrimeCertificate 994393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1973]) (by decide +kernel)
def pv994393 : PrimeValue := ⟨994393, pr994393⟩
private theorem pr994549 : PrimeCertificate 994549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv1237]) (by decide +kernel)
def pv994549 : PrimeValue := ⟨994549, pr994549⟩
private theorem pr994723 : PrimeCertificate 994723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv193,pv859]) (by decide +kernel)
def pv994723 : PrimeValue := ⟨994723, pr994723⟩
private theorem pr994879 : PrimeCertificate 994879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv2909]) (by decide +kernel)
def pv994879 : PrimeValue := ⟨994879, pr994879⟩
private theorem pr995173 : PrimeCertificate 995173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv127,pv653]) (by decide +kernel)
def pv995173 : PrimeValue := ⟨995173, pr995173⟩
private theorem pr995347 : PrimeCertificate 995347 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv457]) (by decide +kernel)
def pv995347 : PrimeValue := ⟨995347, pr995347⟩
private theorem pr995539 : PrimeCertificate 995539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv277,pv599]) (by decide +kernel)
def pv995539 : PrimeValue := ⟨995539, pr995539⟩
private theorem pr995593 : PrimeCertificate 995593 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv13,pv3191]) (by decide +kernel)
def pv995593 : PrimeValue := ⟨995593, pr995593⟩
private theorem pr995623 : PrimeCertificate 995623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv43,pv227]) (by decide +kernel)
def pv995623 : PrimeValue := ⟨995623, pr995623⟩
private theorem pr995719 : PrimeCertificate 995719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv263,pv631]) (by decide +kernel)
def pv995719 : PrimeValue := ⟨995719, pr995719⟩
private theorem pr995833 : PrimeCertificate 995833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13831]) (by decide +kernel)
def pv995833 : PrimeValue := ⟨995833, pr995833⟩
private theorem pr996067 : PrimeCertificate 996067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv55337]) (by decide +kernel)
def pv996067 : PrimeValue := ⟨996067, pr996067⟩
private theorem pr996169 : PrimeCertificate 996169 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv41507]) (by decide +kernel)
def pv996169 : PrimeValue := ⟨996169, pr996169⟩
private theorem pr996253 : PrimeCertificate 996253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv1361]) (by decide +kernel)
def pv996253 : PrimeValue := ⟨996253, pr996253⟩
private theorem pr996367 : PrimeCertificate 996367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv3389]) (by decide +kernel)
def pv996367 : PrimeValue := ⟨996367, pr996367⟩
private theorem pr996409 : PrimeCertificate 996409 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv659]) (by decide +kernel)
def pv996409 : PrimeValue := ⟨996409, pr996409⟩
private theorem pr996649 : PrimeCertificate 996649 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv131,pv317]) (by decide +kernel)
def pv996649 : PrimeValue := ⟨996649, pr996649⟩
private theorem pr996703 : PrimeCertificate 996703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv1249]) (by decide +kernel)
def pv996703 : PrimeValue := ⟨996703, pr996703⟩
private theorem pr997069 : PrimeCertificate 997069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83089]) (by decide +kernel)
def pv997069 : PrimeValue := ⟨997069, pr997069⟩
private theorem pr997219 : PrimeCertificate 997219 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv59,pv313]) (by decide +kernel)
def pv997219 : PrimeValue := ⟨997219, pr997219⟩
private theorem pr997273 : PrimeCertificate 997273 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv997273 : PrimeValue := ⟨997273, pr997273⟩
private theorem pr997333 : PrimeCertificate 997333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv383]) (by decide +kernel)
def pv997333 : PrimeValue := ⟨997333, pr997333⟩
private theorem pr997357 : PrimeCertificate 997357 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv4889]) (by decide +kernel)
def pv997357 : PrimeValue := ⟨997357, pr997357⟩
private theorem pr997369 : PrimeCertificate 997369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv29,pv1433]) (by decide +kernel)
def pv997369 : PrimeValue := ⟨997369, pr997369⟩
private theorem pr997627 : PrimeCertificate 997627 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23753]) (by decide +kernel)
def pv997627 : PrimeValue := ⟨997627, pr997627⟩
private theorem pr997693 : PrimeCertificate 997693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv1171]) (by decide +kernel)
def pv997693 : PrimeValue := ⟨997693, pr997693⟩
private theorem pr997879 : PrimeCertificate 997879 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv1033]) (by decide +kernel)
def pv997879 : PrimeValue := ⟨997879, pr997879⟩
private theorem pr997963 : PrimeCertificate 997963 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv23761]) (by decide +kernel)
def pv997963 : PrimeValue := ⟨997963, pr997963⟩
private theorem pr998017 : PrimeCertificate 998017 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv23,pv113]) (by decide +kernel)
def pv998017 : PrimeValue := ⟨998017, pr998017⟩
private theorem pr998077 : PrimeCertificate 998077 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31,pv2683]) (by decide +kernel)
def pv998077 : PrimeValue := ⟨998077, pr998077⟩
private theorem pr998083 : PrimeCertificate 998083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv101]) (by decide +kernel)
def pv998083 : PrimeValue := ⟨998083, pr998083⟩
private theorem pr998623 : PrimeCertificate 998623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv18493]) (by decide +kernel)
def pv998623 : PrimeValue := ⟨998623, pr998623⟩
private theorem pr998857 : PrimeCertificate 998857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13873]) (by decide +kernel)
def pv998857 : PrimeValue := ⟨998857, pr998857⟩
private theorem pr998983 : PrimeCertificate 998983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv23,pv127]) (by decide +kernel)
def pv998983 : PrimeValue := ⟨998983, pr998983⟩
private theorem pr999217 : PrimeCertificate 999217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv257]) (by decide +kernel)
def pv999217 : PrimeValue := ⟨999217, pr999217⟩
private theorem pr999499 : PrimeCertificate 999499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv41,pv239]) (by decide +kernel)
def pv999499 : PrimeValue := ⟨999499, pr999499⟩
private theorem pr999667 : PrimeCertificate 999667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv37,pv79]) (by decide +kernel)
def pv999667 : PrimeValue := ⟨999667, pr999667⟩
private theorem pr999763 : PrimeCertificate 999763 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv166627]) (by decide +kernel)
def pv999763 : PrimeValue := ⟨999763, pr999763⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
