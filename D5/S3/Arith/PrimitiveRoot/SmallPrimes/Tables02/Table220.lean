/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table220
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table220.pv903109
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table053
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table054

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr903109 : PrimeCertificate 903109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv19,pv233]) (by decide +kernel)
def pv903109 : PrimeValue := ⟨903109, pr903109⟩
private theorem pr903223 : PrimeCertificate 903223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv139]) (by decide +kernel)
def pv903223 : PrimeValue := ⟨903223, pr903223⟩
private theorem pr903337 : PrimeCertificate 903337 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv19,pv283]) (by decide +kernel)
def pv903337 : PrimeValue := ⟨903337, pr903337⟩
private theorem pr904093 : PrimeCertificate 904093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv47,pv229]) (by decide +kernel)
def pv904093 : PrimeValue := ⟨904093, pr904093⟩
private theorem pr904207 : PrimeCertificate 904207 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv37,pv4073]) (by decide +kernel)
def pv904207 : PrimeValue := ⟨904207, pr904207⟩
private theorem pr904369 : PrimeCertificate 904369 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv83,pv227]) (by decide +kernel)
def pv904369 : PrimeValue := ⟨904369, pr904369⟩
private theorem pr904399 : PrimeCertificate 904399 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv71,pv193]) (by decide +kernel)
def pv904399 : PrimeValue := ⟨904399, pr904399⟩
private theorem pr904627 : PrimeCertificate 904627 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv29,pv1733]) (by decide +kernel)
def pv904627 : PrimeValue := ⟨904627, pr904627⟩
private theorem pr904663 : PrimeCertificate 904663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1523]) (by decide +kernel)
def pv904663 : PrimeValue := ⟨904663, pr904663⟩
private theorem pr904759 : PrimeCertificate 904759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv101,pv1493]) (by decide +kernel)
def pv904759 : PrimeValue := ⟨904759, pr904759⟩
private theorem pr904903 : PrimeCertificate 904903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv2251]) (by decide +kernel)
def pv904903 : PrimeValue := ⟨904903, pr904903⟩
private theorem pr905197 : PrimeCertificate 905197 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv241,pv313]) (by decide +kernel)
def pv905197 : PrimeValue := ⟨905197, pr905197⟩
private theorem pr905227 : PrimeCertificate 905227 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv3079]) (by decide +kernel)
def pv905227 : PrimeValue := ⟨905227, pr905227⟩
private theorem pr905449 : PrimeCertificate 905449 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31,pv1217]) (by decide +kernel)
def pv905449 : PrimeValue := ⟨905449, pr905449⟩
private theorem pr905617 : PrimeCertificate 905617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv331]) (by decide +kernel)
def pv905617 : PrimeValue := ⟨905617, pr905617⟩
private theorem pr905629 : PrimeCertificate 905629 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv163,pv463]) (by decide +kernel)
def pv905629 : PrimeValue := ⟨905629, pr905629⟩
private theorem pr905647 : PrimeCertificate 905647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv21563]) (by decide +kernel)
def pv905647 : PrimeValue := ⟨905647, pr905647⟩
private theorem pr905683 : PrimeCertificate 905683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv271,pv557]) (by decide +kernel)
def pv905683 : PrimeValue := ⟨905683, pr905683⟩
private theorem pr905767 : PrimeCertificate 905767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv150961]) (by decide +kernel)
def pv905767 : PrimeValue := ⟨905767, pr905767⟩
private theorem pr906229 : PrimeCertificate 906229 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv2797]) (by decide +kernel)
def pv906229 : PrimeValue := ⟨906229, pr906229⟩
private theorem pr906349 : PrimeCertificate 906349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv1607]) (by decide +kernel)
def pv906349 : PrimeValue := ⟨906349, pr906349⟩
private theorem pr906613 : PrimeCertificate 906613 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv43,pv251]) (by decide +kernel)
def pv906613 : PrimeValue := ⟨906613, pr906613⟩
private theorem pr906679 : PrimeCertificate 906679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv2963]) (by decide +kernel)
def pv906679 : PrimeValue := ⟨906679, pr906679⟩
private theorem pr906817 : PrimeCertificate 906817 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv4723]) (by decide +kernel)
def pv906817 : PrimeValue := ⟨906817, pr906817⟩
private theorem pr906973 : PrimeCertificate 906973 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv6871]) (by decide +kernel)
def pv906973 : PrimeValue := ⟨906973, pr906973⟩
private theorem pr907099 : PrimeCertificate 907099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv73,pv109]) (by decide +kernel)
def pv907099 : PrimeValue := ⟨907099, pr907099⟩
private theorem pr907213 : PrimeCertificate 907213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv23,pv173]) (by decide +kernel)
def pv907213 : PrimeValue := ⟨907213, pr907213⟩
private theorem pr907237 : PrimeCertificate 907237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv29,pv79]) (by decide +kernel)
def pv907237 : PrimeValue := ⟨907237, pr907237⟩
private theorem pr907279 : PrimeCertificate 907279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv151213]) (by decide +kernel)
def pv907279 : PrimeValue := ⟨907279, pr907279⟩
private theorem pr907369 : PrimeCertificate 907369 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7,pv11,pv491]) (by decide +kernel)
def pv907369 : PrimeValue := ⟨907369, pr907369⟩
private theorem pr907399 : PrimeCertificate 907399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv50411]) (by decide +kernel)
def pv907399 : PrimeValue := ⟨907399, pr907399⟩
private theorem pr907567 : PrimeCertificate 907567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13751]) (by decide +kernel)
def pv907567 : PrimeValue := ⟨907567, pr907567⟩
private theorem pr907657 : PrimeCertificate 907657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv641]) (by decide +kernel)
def pv907657 : PrimeValue := ⟨907657, pr907657⟩
private theorem pr907909 : PrimeCertificate 907909 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv75659]) (by decide +kernel)
def pv907909 : PrimeValue := ⟨907909, pr907909⟩
private theorem pr907969 : PrimeCertificate 907969 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4729]) (by decide +kernel)
def pv907969 : PrimeValue := ⟨907969, pr907969⟩
private theorem pr908197 : PrimeCertificate 908197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv75683]) (by decide +kernel)
def pv908197 : PrimeValue := ⟨908197, pr908197⟩
private theorem pr908317 : PrimeCertificate 908317 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1097]) (by decide +kernel)
def pv908317 : PrimeValue := ⟨908317, pr908317⟩
private theorem pr908449 : PrimeCertificate 908449 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv9463]) (by decide +kernel)
def pv908449 : PrimeValue := ⟨908449, pr908449⟩
private theorem pr908797 : PrimeCertificate 908797 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv31,pv349]) (by decide +kernel)
def pv908797 : PrimeValue := ⟨908797, pr908797⟩
private theorem pr908863 : PrimeCertificate 908863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv151477]) (by decide +kernel)
def pv908863 : PrimeValue := ⟨908863, pr908863⟩
private theorem pr909019 : PrimeCertificate 909019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv4591]) (by decide +kernel)
def pv909019 : PrimeValue := ⟨909019, pr909019⟩
private theorem pr909289 : PrimeCertificate 909289 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv73,pv173]) (by decide +kernel)
def pv909289 : PrimeValue := ⟨909289, pr909289⟩
private theorem pr909409 : PrimeCertificate 909409 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv9473]) (by decide +kernel)
def pv909409 : PrimeValue := ⟨909409, pr909409⟩
private theorem pr909637 : PrimeCertificate 909637 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv909637 : PrimeValue := ⟨909637, pr909637⟩
private theorem pr909877 : PrimeCertificate 909877 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv61,pv113]) (by decide +kernel)
def pv909877 : PrimeValue := ⟨909877, pr909877⟩
private theorem pr910207 : PrimeCertificate 910207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv4597]) (by decide +kernel)
def pv910207 : PrimeValue := ⟨910207, pr910207⟩
private theorem pr911077 : PrimeCertificate 911077 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv3301]) (by decide +kernel)
def pv911077 : PrimeValue := ⟨911077, pr911077⟩
private theorem pr911089 : PrimeCertificate 911089 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv19,pv37]) (by decide +kernel)
def pv911089 : PrimeValue := ⟨911089, pr911089⟩
private theorem pr911269 : PrimeCertificate 911269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv1489]) (by decide +kernel)
def pv911269 : PrimeValue := ⟨911269, pr911269⟩
private theorem pr911437 : PrimeCertificate 911437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv151,pv503]) (by decide +kernel)
def pv911437 : PrimeValue := ⟨911437, pr911437⟩
private theorem pr911707 : PrimeCertificate 911707 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv47,pv53,pv61]) (by decide +kernel)
def pv911707 : PrimeValue := ⟨911707, pr911707⟩
private theorem pr911749 : PrimeCertificate 911749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv75979]) (by decide +kernel)
def pv911749 : PrimeValue := ⟨911749, pr911749⟩
private theorem pr911773 : PrimeCertificate 911773 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv31,pv43]) (by decide +kernel)
def pv911773 : PrimeValue := ⟨911773, pr911773⟩
private theorem pr911893 : PrimeCertificate 911893 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv75991]) (by decide +kernel)
def pv911893 : PrimeValue := ⟨911893, pr911893⟩
private theorem pr911899 : PrimeCertificate 911899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv433]) (by decide +kernel)
def pv911899 : PrimeValue := ⟨911899, pr911899⟩
private theorem pr912103 : PrimeCertificate 912103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv152017]) (by decide +kernel)
def pv912103 : PrimeValue := ⟨912103, pr912103⟩
private theorem pr912349 : PrimeCertificate 912349 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv25343]) (by decide +kernel)
def pv912349 : PrimeValue := ⟨912349, pr912349⟩
private theorem pr912367 : PrimeCertificate 912367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv557]) (by decide +kernel)
def pv912367 : PrimeValue := ⟨912367, pr912367⟩
private theorem pr912409 : PrimeCertificate 912409 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv5431]) (by decide +kernel)
def pv912409 : PrimeValue := ⟨912409, pr912409⟩
private theorem pr912487 : PrimeCertificate 912487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv152081]) (by decide +kernel)
def pv912487 : PrimeValue := ⟨912487, pr912487⟩
private theorem pr912559 : PrimeCertificate 912559 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv152093]) (by decide +kernel)
def pv912559 : PrimeValue := ⟨912559, pr912559⟩
private theorem pr912823 : PrimeCertificate 912823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv167,pv911]) (by decide +kernel)
def pv912823 : PrimeValue := ⟨912823, pr912823⟩
private theorem pr913417 : PrimeCertificate 913417 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv5437]) (by decide +kernel)
def pv913417 : PrimeValue := ⟨913417, pr913417⟩
private theorem pr913579 : PrimeCertificate 913579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv3541]) (by decide +kernel)
def pv913579 : PrimeValue := ⟨913579, pr913579⟩
private theorem pr913639 : PrimeCertificate 913639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv109,pv127]) (by decide +kernel)
def pv913639 : PrimeValue := ⟨913639, pr913639⟩
private theorem pr914257 : PrimeCertificate 914257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv907]) (by decide +kernel)
def pv914257 : PrimeValue := ⟨914257, pr914257⟩
private theorem pr914827 : PrimeCertificate 914827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv83,pv167]) (by decide +kernel)
def pv914827 : PrimeValue := ⟨914827, pr914827⟩
private theorem pr915067 : PrimeCertificate 915067 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv1753]) (by decide +kernel)
def pv915067 : PrimeValue := ⟨915067, pr915067⟩
private theorem pr915223 : PrimeCertificate 915223 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv11,pv283]) (by decide +kernel)
def pv915223 : PrimeValue := ⟨915223, pr915223⟩
private theorem pr915379 : PrimeCertificate 915379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv152563]) (by decide +kernel)
def pv915379 : PrimeValue := ⟨915379, pr915379⟩
private theorem pr915487 : PrimeCertificate 915487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv97]) (by decide +kernel)
def pv915487 : PrimeValue := ⟨915487, pr915487⟩
private theorem pr915613 : PrimeCertificate 915613 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv41,pv1861]) (by decide +kernel)
def pv915613 : PrimeValue := ⟨915613, pr915613⟩
private theorem pr915727 : PrimeCertificate 915727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv21803]) (by decide +kernel)
def pv915727 : PrimeValue := ⟨915727, pr915727⟩
private theorem pr915799 : PrimeCertificate 915799 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv59,pv199]) (by decide +kernel)
def pv915799 : PrimeValue := ⟨915799, pr915799⟩
private theorem pr915973 : PrimeCertificate 915973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv2063]) (by decide +kernel)
def pv915973 : PrimeValue := ⟨915973, pr915973⟩
private theorem pr916177 : PrimeCertificate 916177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19087]) (by decide +kernel)
def pv916177 : PrimeValue := ⟨916177, pr916177⟩
private theorem pr916339 : PrimeCertificate 916339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv152723]) (by decide +kernel)
def pv916339 : PrimeValue := ⟨916339, pr916339⟩
private theorem pr916537 : PrimeCertificate 916537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv38189]) (by decide +kernel)
def pv916537 : PrimeValue := ⟨916537, pr916537⟩
private theorem pr916999 : PrimeCertificate 916999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv152833]) (by decide +kernel)
def pv916999 : PrimeValue := ⟨916999, pr916999⟩
private theorem pr917053 : PrimeCertificate 917053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv76421]) (by decide +kernel)
def pv917053 : PrimeValue := ⟨917053, pr917053⟩
private theorem pr917209 : PrimeCertificate 917209 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv12739]) (by decide +kernel)
def pv917209 : PrimeValue := ⟨917209, pr917209⟩
private theorem pr917227 : PrimeCertificate 917227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv50957]) (by decide +kernel)
def pv917227 : PrimeValue := ⟨917227, pr917227⟩
private theorem pr917503 : PrimeCertificate 917503 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29,pv5273]) (by decide +kernel)
def pv917503 : PrimeValue := ⟨917503, pr917503⟩
private theorem pr917629 : PrimeCertificate 917629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv1627]) (by decide +kernel)
def pv917629 : PrimeValue := ⟨917629, pr917629⟩
private theorem pr917659 : PrimeCertificate 917659 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv7283]) (by decide +kernel)
def pv917659 : PrimeValue := ⟨917659, pr917659⟩
private theorem pr917689 : PrimeCertificate 917689 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv38237]) (by decide +kernel)
def pv917689 : PrimeValue := ⟨917689, pr917689⟩
private theorem pr917737 : PrimeCertificate 917737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv38239]) (by decide +kernel)
def pv917737 : PrimeValue := ⟨917737, pr917737⟩
private theorem pr917767 : PrimeCertificate 917767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv761]) (by decide +kernel)
def pv917767 : PrimeValue := ⟨917767, pr917767⟩
private theorem pr917827 : PrimeCertificate 917827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv41]) (by decide +kernel)
def pv917827 : PrimeValue := ⟨917827, pr917827⟩
private theorem pr917869 : PrimeCertificate 917869 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv223]) (by decide +kernel)
def pv917869 : PrimeValue := ⟨917869, pr917869⟩
private theorem pr917893 : PrimeCertificate 917893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2833]) (by decide +kernel)
def pv917893 : PrimeValue := ⟨917893, pr917893⟩
private theorem pr918103 : PrimeCertificate 918103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv9001]) (by decide +kernel)
def pv918103 : PrimeValue := ⟨918103, pr918103⟩
private theorem pr918109 : PrimeCertificate 918109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8501]) (by decide +kernel)
def pv918109 : PrimeValue := ⟨918109, pr918109⟩
private theorem pr918283 : PrimeCertificate 918283 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv4937]) (by decide +kernel)
def pv918283 : PrimeValue := ⟨918283, pr918283⟩
private theorem pr918319 : PrimeCertificate 918319 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv41,pv3733]) (by decide +kernel)
def pv918319 : PrimeValue := ⟨918319, pr918319⟩
private theorem pr918613 : PrimeCertificate 918613 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv19,pv79]) (by decide +kernel)
def pv918613 : PrimeValue := ⟨918613, pr918613⟩
private theorem pr918763 : PrimeCertificate 918763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv11779]) (by decide +kernel)
def pv918763 : PrimeValue := ⟨918763, pr918763⟩
private theorem pr918787 : PrimeCertificate 918787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13921]) (by decide +kernel)
def pv918787 : PrimeValue := ⟨918787, pr918787⟩
private theorem pr918877 : PrimeCertificate 918877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv10939]) (by decide +kernel)
def pv918877 : PrimeValue := ⟨918877, pr918877⟩
private theorem pr919183 : PrimeCertificate 919183 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv19,pv733]) (by decide +kernel)
def pv919183 : PrimeValue := ⟨919183, pr919183⟩
private theorem pr919393 : PrimeCertificate 919393 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv61,pv157]) (by decide +kernel)
def pv919393 : PrimeValue := ⟨919393, pr919393⟩
private theorem pr919447 : PrimeCertificate 919447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13931]) (by decide +kernel)
def pv919447 : PrimeValue := ⟨919447, pr919447⟩
private theorem pr919939 : PrimeCertificate 919939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv29,pv311]) (by decide +kernel)
def pv919939 : PrimeValue := ⟨919939, pr919939⟩
private theorem pr919969 : PrimeCertificate 919969 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv919969 : PrimeValue := ⟨919969, pr919969⟩
private theorem pr920053 : PrimeCertificate 920053 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1217]) (by decide +kernel)
def pv920053 : PrimeValue := ⟨920053, pr920053⟩
private theorem pr920137 : PrimeCertificate 920137 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv5477]) (by decide +kernel)
def pv920137 : PrimeValue := ⟨920137, pr920137⟩
private theorem pr920167 : PrimeCertificate 920167 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv13,pv47,pv251]) (by decide +kernel)
def pv920167 : PrimeValue := ⟨920167, pr920167⟩
private theorem pr920209 : PrimeCertificate 920209 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv1009]) (by decide +kernel)
def pv920209 : PrimeValue := ⟨920209, pr920209⟩
private theorem pr920509 : PrimeCertificate 920509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79,pv971]) (by decide +kernel)
def pv920509 : PrimeValue := ⟨920509, pr920509⟩
private theorem pr920677 : PrimeCertificate 920677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv1051]) (by decide +kernel)
def pv920677 : PrimeValue := ⟨920677, pr920677⟩
private theorem pr920833 : PrimeCertificate 920833 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv11,pv109]) (by decide +kernel)
def pv920833 : PrimeValue := ⟨920833, pr920833⟩
private theorem pr920863 : PrimeCertificate 920863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17053]) (by decide +kernel)
def pv920863 : PrimeValue := ⟨920863, pr920863⟩
private theorem pr921007 : PrimeCertificate 921007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv2693]) (by decide +kernel)
def pv921007 : PrimeValue := ⟨921007, pr921007⟩
private theorem pr921073 : PrimeCertificate 921073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv619]) (by decide +kernel)
def pv921073 : PrimeValue := ⟨921073, pr921073⟩
private theorem pr921169 : PrimeCertificate 921169 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv6397]) (by decide +kernel)
def pv921169 : PrimeValue := ⟨921169, pr921169⟩
private theorem pr921589 : PrimeCertificate 921589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv1259]) (by decide +kernel)
def pv921589 : PrimeValue := ⟨921589, pr921589⟩
private theorem pr921637 : PrimeCertificate 921637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25601]) (by decide +kernel)
def pv921637 : PrimeValue := ⟨921637, pr921637⟩
private theorem pr921889 : PrimeCertificate 921889 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv11,pv97]) (by decide +kernel)
def pv921889 : PrimeValue := ⟨921889, pr921889⟩
private theorem pr922069 : PrimeCertificate 922069 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv3659]) (by decide +kernel)
def pv922069 : PrimeValue := ⟨922069, pr922069⟩
private theorem pr922309 : PrimeCertificate 922309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv151,pv509]) (by decide +kernel)
def pv922309 : PrimeValue := ⟨922309, pr922309⟩
private theorem pr922513 : PrimeCertificate 922513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19219]) (by decide +kernel)
def pv922513 : PrimeValue := ⟨922513, pr922513⟩
private theorem pr922813 : PrimeCertificate 922813 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv6991]) (by decide +kernel)
def pv922813 : PrimeValue := ⟨922813, pr922813⟩
private theorem pr923719 : PrimeCertificate 923719 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv153953]) (by decide +kernel)
def pv923719 : PrimeValue := ⟨923719, pr923719⟩
private theorem pr923917 : PrimeCertificate 923917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv647]) (by decide +kernel)
def pv923917 : PrimeValue := ⟨923917, pr923917⟩
private theorem pr923929 : PrimeCertificate 923929 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv137,pv281]) (by decide +kernel)
def pv923929 : PrimeValue := ⟨923929, pr923929⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
