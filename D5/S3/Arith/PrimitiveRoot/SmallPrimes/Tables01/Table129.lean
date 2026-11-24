/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table129
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table129.pv770233
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table047
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table097
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table098

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr770233 : Nat.Prime 770233 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv67,pv479]) (by decide +kernel)
def pv770233 : PrimeValue := ⟨770233, pr770233⟩
private theorem pr770309 : Nat.Prime 770309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv41,pv61]) (by decide +kernel)
def pv770309 : PrimeValue := ⟨770309, pr770309⟩
private theorem pr770353 : Nat.Prime 770353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1459]) (by decide +kernel)
def pv770353 : PrimeValue := ⟨770353, pr770353⟩
private theorem pr770449 : Nat.Prime 770449 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv2293]) (by decide +kernel)
def pv770449 : PrimeValue := ⟨770449, pr770449⟩
private theorem pr770639 : Nat.Prime 770639 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv23,pv1523]) (by decide +kernel)
def pv770639 : PrimeValue := ⟨770639, pr770639⟩
private theorem pr770909 : Nat.Prime 770909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv6217]) (by decide +kernel)
def pv770909 : PrimeValue := ⟨770909, pr770909⟩
private theorem pr770981 : Nat.Prime 770981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv5507]) (by decide +kernel)
def pv770981 : PrimeValue := ⟨770981, pr770981⟩
private theorem pr770993 : Nat.Prime 770993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv48187]) (by decide +kernel)
def pv770993 : PrimeValue := ⟨770993, pr770993⟩
private theorem pr771037 : Nat.Prime 771037 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv67,pv137]) (by decide +kernel)
def pv771037 : PrimeValue := ⟨771037, pr771037⟩
private theorem pr771079 : Nat.Prime 771079 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv1669]) (by decide +kernel)
def pv771079 : PrimeValue := ⟨771079, pr771079⟩
private theorem pr771109 : Nat.Prime 771109 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13,pv4943]) (by decide +kernel)
def pv771109 : PrimeValue := ⟨771109, pr771109⟩
private theorem pr771217 : Nat.Prime 771217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv16067]) (by decide +kernel)
def pv771217 : PrimeValue := ⟨771217, pr771217⟩
private theorem pr771299 : Nat.Prime 771299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv35059]) (by decide +kernel)
def pv771299 : PrimeValue := ⟨771299, pr771299⟩
private theorem pr771403 : Nat.Prime 771403 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv83,pv1549]) (by decide +kernel)
def pv771403 : PrimeValue := ⟨771403, pr771403⟩
private theorem pr771503 : Nat.Prime 771503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv109,pv3539]) (by decide +kernel)
def pv771503 : PrimeValue := ⟨771503, pr771503⟩
private theorem pr771509 : Nat.Prime 771509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv192877]) (by decide +kernel)
def pv771509 : PrimeValue := ⟨771509, pr771509⟩
private theorem pr771629 : Nat.Prime 771629 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv11,pv13,pv19,pv71]) (by decide +kernel)
def pv771629 : PrimeValue := ⟨771629, pr771629⟩
private theorem pr771637 : Nat.Prime 771637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv64303]) (by decide +kernel)
def pv771637 : PrimeValue := ⟨771637, pr771637⟩
private theorem pr771679 : Nat.Prime 771679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv997]) (by decide +kernel)
def pv771679 : PrimeValue := ⟨771679, pr771679⟩
private theorem pr771703 : Nat.Prime 771703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv3137]) (by decide +kernel)
def pv771703 : PrimeValue := ⟨771703, pr771703⟩
private theorem pr771739 : Nat.Prime 771739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1063]) (by decide +kernel)
def pv771739 : PrimeValue := ⟨771739, pr771739⟩
private theorem pr771763 : Nat.Prime 771763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv293,pv439]) (by decide +kernel)
def pv771763 : PrimeValue := ⟨771763, pr771763⟩
private theorem pr771877 : Nat.Prime 771877 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1021]) (by decide +kernel)
def pv771877 : PrimeValue := ⟨771877, pr771877⟩
private theorem pr771973 : Nat.Prime 771973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv2797]) (by decide +kernel)
def pv771973 : PrimeValue := ⟨771973, pr771973⟩
private theorem pr771997 : Nat.Prime 771997 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv64333]) (by decide +kernel)
def pv771997 : PrimeValue := ⟨771997, pr771997⟩
private theorem pr772001 : Nat.Prime 772001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv193]) (by decide +kernel)
def pv772001 : PrimeValue := ⟨772001, pr772001⟩
private theorem pr772181 : Nat.Prime 772181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv38609]) (by decide +kernel)
def pv772181 : PrimeValue := ⟨772181, pr772181⟩
private theorem pr772279 : Nat.Prime 772279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv9901]) (by decide +kernel)
def pv772279 : PrimeValue := ⟨772279, pr772279⟩
private theorem pr772451 : Nat.Prime 772451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv2207]) (by decide +kernel)
def pv772451 : PrimeValue := ⟨772451, pr772451⟩
private theorem pr772477 : Nat.Prime 772477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv64373]) (by decide +kernel)
def pv772477 : PrimeValue := ⟨772477, pr772477⟩
private theorem pr772493 : Nat.Prime 772493 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv47,pv587]) (by decide +kernel)
def pv772493 : PrimeValue := ⟨772493, pr772493⟩
private theorem pr772571 : Nat.Prime 772571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv3359]) (by decide +kernel)
def pv772571 : PrimeValue := ⟨772571, pr772571⟩
private theorem pr772619 : Nat.Prime 772619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv29,pv173]) (by decide +kernel)
def pv772619 : PrimeValue := ⟨772619, pr772619⟩
private theorem pr772663 : Nat.Prime 772663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv23,pv509]) (by decide +kernel)
def pv772663 : PrimeValue := ⟨772663, pr772663⟩
private theorem pr772843 : Nat.Prime 772843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv18401]) (by decide +kernel)
def pv772843 : PrimeValue := ⟨772843, pr772843⟩
private theorem pr772963 : Nat.Prime 772963 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv2741]) (by decide +kernel)
def pv772963 : PrimeValue := ⟨772963, pr772963⟩
private theorem pr772991 : Nat.Prime 772991 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv4547]) (by decide +kernel)
def pv772991 : PrimeValue := ⟨772991, pr772991⟩
private theorem pr773023 : Nat.Prime 773023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv128837]) (by decide +kernel)
def pv773023 : PrimeValue := ⟨773023, pr773023⟩
private theorem pr773231 : Nat.Prime 773231 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv77323]) (by decide +kernel)
def pv773231 : PrimeValue := ⟨773231, pr773231⟩
private theorem pr773249 : Nat.Prime 773249 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv7,pv863]) (by decide +kernel)
def pv773249 : PrimeValue := ⟨773249, pr773249⟩
private theorem pr773273 : Nat.Prime 773273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv163,pv593]) (by decide +kernel)
def pv773273 : PrimeValue := ⟨773273, pr773273⟩
private theorem pr773299 : Nat.Prime 773299 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv42961]) (by decide +kernel)
def pv773299 : PrimeValue := ⟨773299, pr773299⟩
private theorem pr773453 : Nat.Prime 773453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv10177]) (by decide +kernel)
def pv773453 : PrimeValue := ⟨773453, pr773453⟩
private theorem pr773497 : Nat.Prime 773497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3581]) (by decide +kernel)
def pv773497 : PrimeValue := ⟨773497, pr773497⟩
private theorem pr773569 : Nat.Prime 773569 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv17,pv79]) (by decide +kernel)
def pv773569 : PrimeValue := ⟨773569, pr773569⟩
private theorem pr773603 : Nat.Prime 773603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv61,pv373]) (by decide +kernel)
def pv773603 : PrimeValue := ⟨773603, pr773603⟩
private theorem pr773719 : Nat.Prime 773719 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv19,pv617]) (by decide +kernel)
def pv773719 : PrimeValue := ⟨773719, pr773719⟩
private theorem pr773767 : Nat.Prime 773767 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv23,pv89]) (by decide +kernel)
def pv773767 : PrimeValue := ⟨773767, pr773767⟩
private theorem pr773863 : Nat.Prime 773863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv101,pv1277]) (by decide +kernel)
def pv773863 : PrimeValue := ⟨773863, pr773863⟩
private theorem pr773939 : Nat.Prime 773939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv127,pv277]) (by decide +kernel)
def pv773939 : PrimeValue := ⟨773939, pr773939⟩
private theorem pr774071 : Nat.Prime 774071 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv31,pv227]) (by decide +kernel)
def pv774071 : PrimeValue := ⟨774071, pr774071⟩
private theorem pr774173 : Nat.Prime 774173 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv43,pv643]) (by decide +kernel)
def pv774173 : PrimeValue := ⟨774173, pr774173⟩
private theorem pr774229 : Nat.Prime 774229 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv7,pv13,pv709]) (by decide +kernel)
def pv774229 : PrimeValue := ⟨774229, pr774229⟩
private theorem pr774491 : Nat.Prime 774491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv1889]) (by decide +kernel)
def pv774491 : PrimeValue := ⟨774491, pr774491⟩
private theorem pr774679 : Nat.Prime 774679 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv129113]) (by decide +kernel)
def pv774679 : PrimeValue := ⟨774679, pr774679⟩
private theorem pr774757 : Nat.Prime 774757 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv21521]) (by decide +kernel)
def pv774757 : PrimeValue := ⟨774757, pr774757⟩
private theorem pr774773 : Nat.Prime 774773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109,pv1777]) (by decide +kernel)
def pv774773 : PrimeValue := ⟨774773, pr774773⟩
private theorem pr775121 : Nat.Prime 775121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv9689]) (by decide +kernel)
def pv775121 : PrimeValue := ⟨775121, pr775121⟩
private theorem pr775163 : Nat.Prime 775163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv20399]) (by decide +kernel)
def pv775163 : PrimeValue := ⟨775163, pr775163⟩
private theorem pr775193 : Nat.Prime 775193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv23,pv383]) (by decide +kernel)
def pv775193 : PrimeValue := ⟨775193, pr775193⟩
private theorem pr775237 : Nat.Prime 775237 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv839]) (by decide +kernel)
def pv775237 : PrimeValue := ⟨775237, pr775237⟩
private theorem pr775267 : Nat.Prime 775267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv157,pv823]) (by decide +kernel)
def pv775267 : PrimeValue := ⟨775267, pr775267⟩
private theorem pr775417 : Nat.Prime 775417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv32309]) (by decide +kernel)
def pv775417 : PrimeValue := ⟨775417, pr775417⟩
private theorem pr775553 : Nat.Prime 775553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv73,pv83]) (by decide +kernel)
def pv775553 : PrimeValue := ⟨775553, pr775553⟩
private theorem pr775573 : Nat.Prime 775573 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1319]) (by decide +kernel)
def pv775573 : PrimeValue := ⟨775573, pr775573⟩
private theorem pr775601 : Nat.Prime 775601 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv277]) (by decide +kernel)
def pv775601 : PrimeValue := ⟨775601, pr775601⟩
private theorem pr775627 : Nat.Prime 775627 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv257,pv503]) (by decide +kernel)
def pv775627 : PrimeValue := ⟨775627, pr775627⟩
private theorem pr775639 : Nat.Prime 775639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv1051]) (by decide +kernel)
def pv775639 : PrimeValue := ⟨775639, pr775639⟩
private theorem pr775729 : Nat.Prime 775729 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5387]) (by decide +kernel)
def pv775729 : PrimeValue := ⟨775729, pr775729⟩
private theorem pr775739 : Nat.Prime 775739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv397,pv977]) (by decide +kernel)
def pv775739 : PrimeValue := ⟨775739, pr775739⟩
private theorem pr775777 : Nat.Prime 775777 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv8081]) (by decide +kernel)
def pv775777 : PrimeValue := ⟨775777, pr775777⟩
private theorem pr775811 : Nat.Prime 775811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11083]) (by decide +kernel)
def pv775811 : PrimeValue := ⟨775811, pr775811⟩
private theorem pr775823 : Nat.Prime 775823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv387911]) (by decide +kernel)
def pv775823 : PrimeValue := ⟨775823, pr775823⟩
private theorem pr775939 : Nat.Prime 775939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv1637]) (by decide +kernel)
def pv775939 : PrimeValue := ⟨775939, pr775939⟩
private theorem pr775949 : Nat.Prime 775949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv11411]) (by decide +kernel)
def pv775949 : PrimeValue := ⟨775949, pr775949⟩
private theorem pr775987 : Nat.Prime 775987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv283,pv457]) (by decide +kernel)
def pv775987 : PrimeValue := ⟨775987, pr775987⟩
private theorem pr776003 : Nat.Prime 776003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103,pv3767]) (by decide +kernel)
def pv776003 : PrimeValue := ⟨776003, pr776003⟩
private theorem pr776059 : Nat.Prime 776059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv211,pv613]) (by decide +kernel)
def pv776059 : PrimeValue := ⟨776059, pr776059⟩
private theorem pr776119 : Nat.Prime 776119 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv1087]) (by decide +kernel)
def pv776119 : PrimeValue := ⟨776119, pr776119⟩
private theorem pr776143 : Nat.Prime 776143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1597]) (by decide +kernel)
def pv776143 : PrimeValue := ⟨776143, pr776143⟩
private theorem pr776183 : Nat.Prime 776183 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv35281]) (by decide +kernel)
def pv776183 : PrimeValue := ⟨776183, pr776183⟩
private theorem pr776201 : Nat.Prime 776201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv3881]) (by decide +kernel)
def pv776201 : PrimeValue := ⟨776201, pr776201⟩
private theorem pr776317 : Nat.Prime 776317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv64693]) (by decide +kernel)
def pv776317 : PrimeValue := ⟨776317, pr776317⟩
private theorem pr776719 : Nat.Prime 776719 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43151]) (by decide +kernel)
def pv776719 : PrimeValue := ⟨776719, pr776719⟩
private theorem pr776753 : Nat.Prime 776753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv1129]) (by decide +kernel)
def pv776753 : PrimeValue := ⟨776753, pr776753⟩
private theorem pr776861 : Nat.Prime 776861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv31,pv179]) (by decide +kernel)
def pv776861 : PrimeValue := ⟨776861, pr776861⟩
private theorem pr776899 : Nat.Prime 776899 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv14387]) (by decide +kernel)
def pv776899 : PrimeValue := ⟨776899, pr776899⟩
private theorem pr776947 : Nat.Prime 776947 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv129491]) (by decide +kernel)
def pv776947 : PrimeValue := ⟨776947, pr776947⟩
private theorem pr776983 : Nat.Prime 776983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv129497]) (by decide +kernel)
def pv776983 : PrimeValue := ⟨776983, pr776983⟩
private theorem pr777041 : Nat.Prime 777041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv883]) (by decide +kernel)
def pv777041 : PrimeValue := ⟨777041, pr777041⟩
private theorem pr777173 : Nat.Prime 777173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv1039]) (by decide +kernel)
def pv777173 : PrimeValue := ⟨777173, pr777173⟩
private theorem pr777191 : Nat.Prime 777191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv77719]) (by decide +kernel)
def pv777191 : PrimeValue := ⟨777191, pr777191⟩
private theorem pr777199 : Nat.Prime 777199 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv129533]) (by decide +kernel)
def pv777199 : PrimeValue := ⟨777199, pr777199⟩
private theorem pr777209 : Nat.Prime 777209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv97151]) (by decide +kernel)
def pv777209 : PrimeValue := ⟨777209, pr777209⟩
private theorem pr777349 : Nat.Prime 777349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv151]) (by decide +kernel)
def pv777349 : PrimeValue := ⟨777349, pr777349⟩
private theorem pr777389 : Nat.Prime 777389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109,pv1783]) (by decide +kernel)
def pv777389 : PrimeValue := ⟨777389, pr777389⟩
private theorem pr777431 : Nat.Prime 777431 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv77743]) (by decide +kernel)
def pv777431 : PrimeValue := ⟨777431, pr777431⟩
private theorem pr777619 : Nat.Prime 777619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43201]) (by decide +kernel)
def pv777619 : PrimeValue := ⟨777619, pr777619⟩
private theorem pr777671 : Nat.Prime 777671 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv19,pv4093]) (by decide +kernel)
def pv777671 : PrimeValue := ⟨777671, pr777671⟩
private theorem pr777761 : Nat.Prime 777761 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv4861]) (by decide +kernel)
def pv777761 : PrimeValue := ⟨777761, pr777761⟩
private theorem pr777769 : Nat.Prime 777769 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv1409]) (by decide +kernel)
def pv777769 : PrimeValue := ⟨777769, pr777769⟩
private theorem pr777839 : Nat.Prime 777839 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv29,pv13411]) (by decide +kernel)
def pv777839 : PrimeValue := ⟨777839, pr777839⟩
private theorem pr777863 : Nat.Prime 777863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv388931]) (by decide +kernel)
def pv777863 : PrimeValue := ⟨777863, pr777863⟩
private theorem pr777919 : Nat.Prime 777919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv317,pv409]) (by decide +kernel)
def pv777919 : PrimeValue := ⟨777919, pr777919⟩
private theorem pr778163 : Nat.Prime 778163 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11,pv31,pv163]) (by decide +kernel)
def pv778163 : PrimeValue := ⟨778163, pr778163⟩
private theorem pr778333 : Nat.Prime 778333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv1753]) (by decide +kernel)
def pv778333 : PrimeValue := ⟨778333, pr778333⟩
private theorem pr778507 : Nat.Prime 778507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv6829]) (by decide +kernel)
def pv778507 : PrimeValue := ⟨778507, pr778507⟩
private theorem pr778559 : Nat.Prime 778559 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv43,pv823]) (by decide +kernel)
def pv778559 : PrimeValue := ⟨778559, pr778559⟩
private theorem pr778579 : Nat.Prime 778579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv129763]) (by decide +kernel)
def pv778579 : PrimeValue := ⟨778579, pr778579⟩
private theorem pr778597 : Nat.Prime 778597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv23,pv31]) (by decide +kernel)
def pv778597 : PrimeValue := ⟨778597, pr778597⟩
private theorem pr778643 : Nat.Prime 778643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv16927]) (by decide +kernel)
def pv778643 : PrimeValue := ⟨778643, pr778643⟩
private theorem pr778709 : Nat.Prime 778709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv137]) (by decide +kernel)
def pv778709 : PrimeValue := ⟨778709, pr778709⟩
private theorem pr778717 : Nat.Prime 778717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv97,pv223]) (by decide +kernel)
def pv778717 : PrimeValue := ⟨778717, pr778717⟩
private theorem pr778777 : Nat.Prime 778777 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv877]) (by decide +kernel)
def pv778777 : PrimeValue := ⟨778777, pr778777⟩
private theorem pr778873 : Nat.Prime 778873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv23,pv83]) (by decide +kernel)
def pv778873 : PrimeValue := ⟨778873, pr778873⟩
private theorem pr779039 : Nat.Prime 779039 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv13,pv19,pv83]) (by decide +kernel)
def pv779039 : PrimeValue := ⟨779039, pr779039⟩
private theorem pr779111 : Nat.Prime 779111 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv4583]) (by decide +kernel)
def pv779111 : PrimeValue := ⟨779111, pr779111⟩
private theorem pr779137 : Nat.Prime 779137 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv2029]) (by decide +kernel)
def pv779137 : PrimeValue := ⟨779137, pr779137⟩
private theorem pr779173 : Nat.Prime 779173 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv29,pv2239]) (by decide +kernel)
def pv779173 : PrimeValue := ⟨779173, pr779173⟩
private theorem pr779489 : Nat.Prime 779489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv24359]) (by decide +kernel)
def pv779489 : PrimeValue := ⟨779489, pr779489⟩
private theorem pr779561 : Nat.Prime 779561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19489]) (by decide +kernel)
def pv779561 : PrimeValue := ⟨779561, pr779561⟩
private theorem pr779563 : Nat.Prime 779563 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv23,pv269]) (by decide +kernel)
def pv779563 : PrimeValue := ⟨779563, pr779563⟩
private theorem pr779591 : Nat.Prime 779591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv37,pv43]) (by decide +kernel)
def pv779591 : PrimeValue := ⟨779591, pr779591⟩
private theorem pr779617 : Nat.Prime 779617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2707]) (by decide +kernel)
def pv779617 : PrimeValue := ⟨779617, pr779617⟩
private theorem pr779659 : Nat.Prime 779659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv11813]) (by decide +kernel)
def pv779659 : PrimeValue := ⟨779659, pr779659⟩
private theorem pr779699 : Nat.Prime 779699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv389849]) (by decide +kernel)
def pv779699 : PrimeValue := ⟨779699, pr779699⟩
private theorem pr779767 : Nat.Prime 779767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv769]) (by decide +kernel)
def pv779767 : PrimeValue := ⟨779767, pr779767⟩
private theorem pr779827 : Nat.Prime 779827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv129971]) (by decide +kernel)
def pv779827 : PrimeValue := ⟨779827, pr779827⟩
private theorem pr779879 : Nat.Prime 779879 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv35449]) (by decide +kernel)
def pv779879 : PrimeValue := ⟨779879, pr779879⟩
private theorem pr779939 : Nat.Prime 779939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv271,pv1439]) (by decide +kernel)
def pv779939 : PrimeValue := ⟨779939, pr779939⟩
private theorem pr779981 : Nat.Prime 779981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv661]) (by decide +kernel)
def pv779981 : PrimeValue := ⟨779981, pr779981⟩
private theorem pr780029 : Nat.Prime 780029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv11471]) (by decide +kernel)
def pv780029 : PrimeValue := ⟨780029, pr780029⟩
private theorem pr780119 : Nat.Prime 780119 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv163,pv2393]) (by decide +kernel)
def pv780119 : PrimeValue := ⟨780119, pr780119⟩
private theorem pr780163 : Nat.Prime 780163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv130027]) (by decide +kernel)
def pv780163 : PrimeValue := ⟨780163, pr780163⟩
private theorem pr780371 : Nat.Prime 780371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv73,pv1069]) (by decide +kernel)
def pv780371 : PrimeValue := ⟨780371, pr780371⟩
private theorem pr780613 : Nat.Prime 780613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv9293]) (by decide +kernel)
def pv780613 : PrimeValue := ⟨780613, pr780613⟩
private theorem pr780649 : Nat.Prime 780649 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv11,pv2957]) (by decide +kernel)
def pv780649 : PrimeValue := ⟨780649, pr780649⟩
private theorem pr780683 : Nat.Prime 780683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv55763]) (by decide +kernel)
def pv780683 : PrimeValue := ⟨780683, pr780683⟩
private theorem pr780803 : Nat.Prime 780803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv35491]) (by decide +kernel)
def pv780803 : PrimeValue := ⟨780803, pr780803⟩
private theorem pr780853 : Nat.Prime 780853 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv65071]) (by decide +kernel)
def pv780853 : PrimeValue := ⟨780853, pr780853⟩
private theorem pr780877 : Nat.Prime 780877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv109,pv199]) (by decide +kernel)
def pv780877 : PrimeValue := ⟨780877, pr780877⟩
private theorem pr780889 : Nat.Prime 780889 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv32537]) (by decide +kernel)
def pv780889 : PrimeValue := ⟨780889, pr780889⟩
private theorem pr780973 : Nat.Prime 780973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv151,pv431]) (by decide +kernel)
def pv780973 : PrimeValue := ⟨780973, pr780973⟩
private theorem pr781003 : Nat.Prime 781003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1607]) (by decide +kernel)
def pv781003 : PrimeValue := ⟨781003, pr781003⟩
private theorem pr781043 : Nat.Prime 781043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv6619]) (by decide +kernel)
def pv781043 : PrimeValue := ⟨781043, pr781043⟩
private theorem pr781117 : Nat.Prime 781117 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv547]) (by decide +kernel)
def pv781117 : PrimeValue := ⟨781117, pr781117⟩
private theorem pr781139 : Nat.Prime 781139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv43,pv293]) (by decide +kernel)
def pv781139 : PrimeValue := ⟨781139, pr781139⟩
private theorem pr781211 : Nat.Prime 781211 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv78121]) (by decide +kernel)
def pv781211 : PrimeValue := ⟨781211, pr781211⟩
private theorem pr781271 : Nat.Prime 781271 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv11161]) (by decide +kernel)
def pv781271 : PrimeValue := ⟨781271, pr781271⟩
private theorem pr781283 : Nat.Prime 781283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv3457]) (by decide +kernel)
def pv781283 : PrimeValue := ⟨781283, pr781283⟩
private theorem pr781433 : Nat.Prime 781433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv53,pv97]) (by decide +kernel)
def pv781433 : PrimeValue := ⟨781433, pr781433⟩
private theorem pr781519 : Nat.Prime 781519 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv130253]) (by decide +kernel)
def pv781519 : PrimeValue := ⟨781519, pr781519⟩
private theorem pr781523 : Nat.Prime 781523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv55823]) (by decide +kernel)
def pv781523 : PrimeValue := ⟨781523, pr781523⟩
private theorem pr781559 : Nat.Prime 781559 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv17,pv127,pv181]) (by decide +kernel)
def pv781559 : PrimeValue := ⟨781559, pr781559⟩
private theorem pr781567 : Nat.Prime 781567 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv130261]) (by decide +kernel)
def pv781567 : PrimeValue := ⟨781567, pr781567⟩
private theorem pr781619 : Nat.Prime 781619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv390809]) (by decide +kernel)
def pv781619 : PrimeValue := ⟨781619, pr781619⟩
private theorem pr781633 : Nat.Prime 781633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv59]) (by decide +kernel)
def pv781633 : PrimeValue := ⟨781633, pr781633⟩
private theorem pr781733 : Nat.Prime 781733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv27919]) (by decide +kernel)
def pv781733 : PrimeValue := ⟨781733, pr781733⟩
private theorem pr781799 : Nat.Prime 781799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv47,pv8317]) (by decide +kernel)
def pv781799 : PrimeValue := ⟨781799, pr781799⟩
private theorem pr781853 : Nat.Prime 781853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv2753]) (by decide +kernel)
def pv781853 : PrimeValue := ⟨781853, pr781853⟩
private theorem pr781867 : Nat.Prime 781867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14479]) (by decide +kernel)
def pv781867 : PrimeValue := ⟨781867, pr781867⟩
private theorem pr781969 : Nat.Prime 781969 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv1481]) (by decide +kernel)
def pv781969 : PrimeValue := ⟨781969, pr781969⟩
private theorem pr781999 : Nat.Prime 781999 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv43,pv433]) (by decide +kernel)
def pv781999 : PrimeValue := ⟨781999, pr781999⟩
private theorem pr782003 : Nat.Prime 782003 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv19,pv1583]) (by decide +kernel)
def pv782003 : PrimeValue := ⟨782003, pr782003⟩
private theorem pr782113 : Nat.Prime 782113 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv8147]) (by decide +kernel)
def pv782113 : PrimeValue := ⟨782113, pr782113⟩
private theorem pr782189 : Nat.Prime 782189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv29,pv613]) (by decide +kernel)
def pv782189 : PrimeValue := ⟨782189, pr782189⟩
private theorem pr782339 : Nat.Prime 782339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv443,pv883]) (by decide +kernel)
def pv782339 : PrimeValue := ⟨782339, pr782339⟩
private theorem pr782389 : Nat.Prime 782389 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv103,pv211]) (by decide +kernel)
def pv782389 : PrimeValue := ⟨782389, pr782389⟩
private theorem pr782839 : Nat.Prime 782839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv109]) (by decide +kernel)
def pv782839 : PrimeValue := ⟨782839, pr782839⟩
private theorem pr782993 : Nat.Prime 782993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv6991]) (by decide +kernel)
def pv782993 : PrimeValue := ⟨782993, pr782993⟩
private theorem pr783089 : Nat.Prime 783089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv2879]) (by decide +kernel)
def pv783089 : PrimeValue := ⟨783089, pr783089⟩
private theorem pr783119 : Nat.Prime 783119 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv61,pv131]) (by decide +kernel)
def pv783119 : PrimeValue := ⟨783119, pr783119⟩
private theorem pr783131 : Nat.Prime 783131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv71,pv1103]) (by decide +kernel)
def pv783131 : PrimeValue := ⟨783131, pr783131⟩
private theorem pr783329 : Nat.Prime 783329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv269]) (by decide +kernel)
def pv783329 : PrimeValue := ⟨783329, pr783329⟩
private theorem pr783413 : Nat.Prime 783413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv571]) (by decide +kernel)
def pv783413 : PrimeValue := ⟨783413, pr783413⟩
private theorem pr783533 : Nat.Prime 783533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv195883]) (by decide +kernel)
def pv783533 : PrimeValue := ⟨783533, pr783533⟩
private theorem pr783553 : Nat.Prime 783553 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv53]) (by decide +kernel)
def pv783553 : PrimeValue := ⟨783553, pr783553⟩
private theorem pr783743 : Nat.Prime 783743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv12641]) (by decide +kernel)
def pv783743 : PrimeValue := ⟨783743, pr783743⟩
private theorem pr783749 : Nat.Prime 783749 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv23,pv1217]) (by decide +kernel)
def pv783749 : PrimeValue := ⟨783749, pr783749⟩
private theorem pr783803 : Nat.Prime 783803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv23053]) (by decide +kernel)
def pv783803 : PrimeValue := ⟨783803, pr783803⟩
private theorem pr783829 : Nat.Prime 783829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv21773]) (by decide +kernel)
def pv783829 : PrimeValue := ⟨783829, pr783829⟩
private theorem pr784009 : Nat.Prime 784009 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv10889]) (by decide +kernel)
def pv784009 : PrimeValue := ⟨784009, pr784009⟩
private theorem pr784061 : Nat.Prime 784061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv197,pv199]) (by decide +kernel)
def pv784061 : PrimeValue := ⟨784061, pr784061⟩
private theorem pr784103 : Nat.Prime 784103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv29,pv1229]) (by decide +kernel)
def pv784103 : PrimeValue := ⟨784103, pr784103⟩
private theorem pr784211 : Nat.Prime 784211 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv17,pv659]) (by decide +kernel)
def pv784211 : PrimeValue := ⟨784211, pr784211⟩
private theorem pr784219 : Nat.Prime 784219 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv4507]) (by decide +kernel)
def pv784219 : PrimeValue := ⟨784219, pr784219⟩
private theorem pr784229 : Nat.Prime 784229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv3323]) (by decide +kernel)
def pv784229 : PrimeValue := ⟨784229, pr784229⟩
private theorem pr784463 : Nat.Prime 784463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv137,pv409]) (by decide +kernel)
def pv784463 : PrimeValue := ⟨784463, pr784463⟩
private theorem pr784717 : Nat.Prime 784717 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv65393]) (by decide +kernel)
def pv784717 : PrimeValue := ⟨784717, pr784717⟩
private theorem pr784723 : Nat.Prime 784723 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv130787]) (by decide +kernel)
def pv784723 : PrimeValue := ⟨784723, pr784723⟩
private theorem pr784799 : Nat.Prime 784799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv29,pv1933]) (by decide +kernel)
def pv784799 : PrimeValue := ⟨784799, pr784799⟩
private theorem pr784919 : Nat.Prime 784919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv37,pv10607]) (by decide +kernel)
def pv784919 : PrimeValue := ⟨784919, pr784919⟩
private theorem pr784939 : Nat.Prime 784939 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv1699]) (by decide +kernel)
def pv784939 : PrimeValue := ⟨784939, pr784939⟩
private theorem pr784961 : Nat.Prime 784961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv223]) (by decide +kernel)
def pv784961 : PrimeValue := ⟨784961, pr784961⟩
private theorem pr785003 : Nat.Prime 785003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv389,pv1009]) (by decide +kernel)
def pv785003 : PrimeValue := ⟨785003, pr785003⟩
private theorem pr785017 : Nat.Prime 785017 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv10903]) (by decide +kernel)
def pv785017 : PrimeValue := ⟨785017, pr785017⟩
private theorem pr785033 : Nat.Prime 785033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv98129]) (by decide +kernel)
def pv785033 : PrimeValue := ⟨785033, pr785033⟩
private theorem pr785159 : Nat.Prime 785159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv89,pv401]) (by decide +kernel)
def pv785159 : PrimeValue := ⟨785159, pr785159⟩
private theorem pr785299 : Nat.Prime 785299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv7699]) (by decide +kernel)
def pv785299 : PrimeValue := ⟨785299, pr785299⟩
private theorem pr785303 : Nat.Prime 785303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv56093]) (by decide +kernel)
def pv785303 : PrimeValue := ⟨785303, pr785303⟩
private theorem pr785347 : Nat.Prime 785347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv83]) (by decide +kernel)
def pv785347 : PrimeValue := ⟨785347, pr785347⟩
private theorem pr785423 : Nat.Prime 785423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv19,pv1879]) (by decide +kernel)
def pv785423 : PrimeValue := ⟨785423, pr785423⟩
private theorem pr785483 : Nat.Prime 785483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv392741]) (by decide +kernel)
def pv785483 : PrimeValue := ⟨785483, pr785483⟩
private theorem pr785591 : Nat.Prime 785591 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv6043]) (by decide +kernel)
def pv785591 : PrimeValue := ⟨785591, pr785591⟩
private theorem pr785623 : Nat.Prime 785623 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv127,pv1031]) (by decide +kernel)
def pv785623 : PrimeValue := ⟨785623, pr785623⟩
private theorem pr785693 : Nat.Prime 785693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv2207]) (by decide +kernel)
def pv785693 : PrimeValue := ⟨785693, pr785693⟩
private theorem pr785737 : Nat.Prime 785737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1559]) (by decide +kernel)
def pv785737 : PrimeValue := ⟨785737, pr785737⟩
private theorem pr785779 : Nat.Prime 785779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv53,pv353]) (by decide +kernel)
def pv785779 : PrimeValue := ⟨785779, pr785779⟩
private theorem pr785903 : Nat.Prime 785903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv167,pv181]) (by decide +kernel)
def pv785903 : PrimeValue := ⟨785903, pr785903⟩
private theorem pr786127 : Nat.Prime 786127 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv43,pv277]) (by decide +kernel)
def pv786127 : PrimeValue := ⟨786127, pr786127⟩
private theorem pr786179 : Nat.Prime 786179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv5867]) (by decide +kernel)
def pv786179 : PrimeValue := ⟨786179, pr786179⟩
private theorem pr786223 : Nat.Prime 786223 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv31,pv1409]) (by decide +kernel)
def pv786223 : PrimeValue := ⟨786223, pr786223⟩
private theorem pr786833 : Nat.Prime 786833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv49177]) (by decide +kernel)
def pv786833 : PrimeValue := ⟨786833, pr786833⟩
private theorem pr786949 : Nat.Prime 786949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv65579]) (by decide +kernel)
def pv786949 : PrimeValue := ⟨786949, pr786949⟩
private theorem pr787079 : Nat.Prime 787079 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv393539]) (by decide +kernel)
def pv787079 : PrimeValue := ⟨787079, pr787079⟩
private theorem pr787207 : Nat.Prime 787207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv18743]) (by decide +kernel)
def pv787207 : PrimeValue := ⟨787207, pr787207⟩
private theorem pr787243 : Nat.Prime 787243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv179,pv733]) (by decide +kernel)
def pv787243 : PrimeValue := ⟨787243, pr787243⟩
private theorem pr787289 : Nat.Prime 787289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv98411]) (by decide +kernel)
def pv787289 : PrimeValue := ⟨787289, pr787289⟩
private theorem pr787469 : Nat.Prime 787469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1627]) (by decide +kernel)
def pv787469 : PrimeValue := ⟨787469, pr787469⟩
private theorem pr787513 : Nat.Prime 787513 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv11,pv19,pv157]) (by decide +kernel)
def pv787513 : PrimeValue := ⟨787513, pr787513⟩
private theorem pr787541 : Nat.Prime 787541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv233]) (by decide +kernel)
def pv787541 : PrimeValue := ⟨787541, pr787541⟩
private theorem pr787573 : Nat.Prime 787573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv131,pv167]) (by decide +kernel)
def pv787573 : PrimeValue := ⟨787573, pr787573⟩
private theorem pr787639 : Nat.Prime 787639 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv251,pv523]) (by decide +kernel)
def pv787639 : PrimeValue := ⟨787639, pr787639⟩
private theorem pr787783 : Nat.Prime 787783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv131297]) (by decide +kernel)
def pv787783 : PrimeValue := ⟨787783, pr787783⟩
private theorem pr787807 : Nat.Prime 787807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1621]) (by decide +kernel)
def pv787807 : PrimeValue := ⟨787807, pr787807⟩
private theorem pr787823 : Nat.Prime 787823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv8039]) (by decide +kernel)
def pv787823 : PrimeValue := ⟨787823, pr787823⟩
private theorem pr787883 : Nat.Prime 787883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv23173]) (by decide +kernel)
def pv787883 : PrimeValue := ⟨787883, pr787883⟩
private theorem pr788173 : Nat.Prime 788173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv853]) (by decide +kernel)
def pv788173 : PrimeValue := ⟨788173, pr788173⟩
private theorem pr788287 : Nat.Prime 788287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv131381]) (by decide +kernel)
def pv788287 : PrimeValue := ⟨788287, pr788287⟩
private theorem pr788351 : Nat.Prime 788351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv15767]) (by decide +kernel)
def pv788351 : PrimeValue := ⟨788351, pr788351⟩
private theorem pr788383 : Nat.Prime 788383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv6257]) (by decide +kernel)
def pv788383 : PrimeValue := ⟨788383, pr788383⟩
private theorem pr788449 : Nat.Prime 788449 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv43,pv191]) (by decide +kernel)
def pv788449 : PrimeValue := ⟨788449, pr788449⟩
private theorem pr788497 : Nat.Prime 788497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv16427]) (by decide +kernel)
def pv788497 : PrimeValue := ⟨788497, pr788497⟩
private theorem pr788549 : Nat.Prime 788549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv197137]) (by decide +kernel)
def pv788549 : PrimeValue := ⟨788549, pr788549⟩
private theorem pr788659 : Nat.Prime 788659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv10111]) (by decide +kernel)
def pv788659 : PrimeValue := ⟨788659, pr788659⟩
private theorem pr788789 : Nat.Prime 788789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv13,pv197]) (by decide +kernel)
def pv788789 : PrimeValue := ⟨788789, pr788789⟩
private theorem pr788849 : Nat.Prime 788849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv1049]) (by decide +kernel)
def pv788849 : PrimeValue := ⟨788849, pr788849⟩
private theorem pr788959 : Nat.Prime 788959 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53,pv827]) (by decide +kernel)
def pv788959 : PrimeValue := ⟨788959, pr788959⟩
private theorem pr788993 : Nat.Prime 788993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv67]) (by decide +kernel)
def pv788993 : PrimeValue := ⟨788993, pr788993⟩
private theorem pr788999 : Nat.Prime 788999 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv83,pv97]) (by decide +kernel)
def pv788999 : PrimeValue := ⟨788999, pr788999⟩
private theorem pr789133 : Nat.Prime 789133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv65761]) (by decide +kernel)
def pv789133 : PrimeValue := ⟨789133, pr789133⟩
private theorem pr789149 : Nat.Prime 789149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv6803]) (by decide +kernel)
def pv789149 : PrimeValue := ⟨789149, pr789149⟩
private theorem pr789343 : Nat.Prime 789343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv293,pv449]) (by decide +kernel)
def pv789343 : PrimeValue := ⟨789343, pr789343⟩
private theorem pr789389 : Nat.Prime 789389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv197347]) (by decide +kernel)
def pv789389 : PrimeValue := ⟨789389, pr789389⟩
private theorem pr789419 : Nat.Prime 789419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv113,pv499]) (by decide +kernel)
def pv789419 : PrimeValue := ⟨789419, pr789419⟩
private theorem pr789671 : Nat.Prime 789671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv29,pv389]) (by decide +kernel)
def pv789671 : PrimeValue := ⟨789671, pr789671⟩
private theorem pr789683 : Nat.Prime 789683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv17167]) (by decide +kernel)
def pv789683 : PrimeValue := ⟨789683, pr789683⟩
private theorem pr789851 : Nat.Prime 789851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv15797]) (by decide +kernel)
def pv789851 : PrimeValue := ⟨789851, pr789851⟩
private theorem pr789941 : Nat.Prime 789941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv127,pv311]) (by decide +kernel)
def pv789941 : PrimeValue := ⟨789941, pr789941⟩
private theorem pr789979 : Nat.Prime 789979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2687]) (by decide +kernel)
def pv789979 : PrimeValue := ⟨789979, pr789979⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
