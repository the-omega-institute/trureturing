/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table166
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table166.pv223099
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr223099 : Nat.Prime 223099 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv103]) (by decide +kernel)
def pv223099 : PrimeValue := ⟨223099, pr223099⟩
private theorem pr223241 : Nat.Prime 223241 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv5581]) (by decide +kernel)
def pv223241 : PrimeValue := ⟨223241, pr223241⟩
private theorem pr223283 : Nat.Prime 223283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv111641]) (by decide +kernel)
def pv223283 : PrimeValue := ⟨223283, pr223283⟩
private theorem pr223337 : Nat.Prime 223337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv27917]) (by decide +kernel)
def pv223337 : PrimeValue := ⟨223337, pr223337⟩
private theorem pr223439 : Nat.Prime 223439 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv47,pv2377]) (by decide +kernel)
def pv223439 : PrimeValue := ⟨223439, pr223439⟩
private theorem pr223507 : Nat.Prime 223507 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv4139]) (by decide +kernel)
def pv223507 : PrimeValue := ⟨223507, pr223507⟩
private theorem pr223621 : Nat.Prime 223621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3727]) (by decide +kernel)
def pv223621 : PrimeValue := ⟨223621, pr223621⟩
private theorem pr223837 : Nat.Prime 223837 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv811]) (by decide +kernel)
def pv223837 : PrimeValue := ⟨223837, pr223837⟩
private theorem pr223921 : Nat.Prime 223921 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv5,pv311]) (by decide +kernel)
def pv223921 : PrimeValue := ⟨223921, pr223921⟩
private theorem pr223969 : Nat.Prime 223969 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv2333]) (by decide +kernel)
def pv223969 : PrimeValue := ⟨223969, pr223969⟩
private theorem pr224071 : Nat.Prime 224071 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv11,pv97]) (by decide +kernel)
def pv224071 : PrimeValue := ⟨224071, pr224071⟩
private theorem pr224197 : Nat.Prime 224197 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv157]) (by decide +kernel)
def pv224197 : PrimeValue := ⟨224197, pr224197⟩
private theorem pr224233 : Nat.Prime 224233 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv9343]) (by decide +kernel)
def pv224233 : PrimeValue := ⟨224233, pr224233⟩
private theorem pr224239 : Nat.Prime 224239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv19,pv281]) (by decide +kernel)
def pv224239 : PrimeValue := ⟨224239, pr224239⟩
private theorem pr224309 : Nat.Prime 224309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv8011]) (by decide +kernel)
def pv224309 : PrimeValue := ⟨224309, pr224309⟩
private theorem pr224401 : Nat.Prime 224401 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv11,pv17]) (by decide +kernel)
def pv224401 : PrimeValue := ⟨224401, pr224401⟩
private theorem pr224473 : Nat.Prime 224473 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv47,pv199]) (by decide +kernel)
def pv224473 : PrimeValue := ⟨224473, pr224473⟩
private theorem pr224591 : Nat.Prime 224591 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv37,pv607]) (by decide +kernel)
def pv224591 : PrimeValue := ⟨224591, pr224591⟩
private theorem pr224617 : Nat.Prime 224617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv191]) (by decide +kernel)
def pv224617 : PrimeValue := ⟨224617, pr224617⟩
private theorem pr224711 : Nat.Prime 224711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv23,pv977]) (by decide +kernel)
def pv224711 : PrimeValue := ⟨224711, pr224711⟩
private theorem pr224737 : Nat.Prime 224737 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv2341]) (by decide +kernel)
def pv224737 : PrimeValue := ⟨224737, pr224737⟩
private theorem pr225109 : Nat.Prime 225109 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv37]) (by decide +kernel)
def pv225109 : PrimeValue := ⟨225109, pr225109⟩
private theorem pr225287 : Nat.Prime 225287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv112643]) (by decide +kernel)
def pv225287 : PrimeValue := ⟨225287, pr225287⟩
private theorem pr225343 : Nat.Prime 225343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv107]) (by decide +kernel)
def pv225343 : PrimeValue := ⟨225343, pr225343⟩
private theorem pr225373 : Nat.Prime 225373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2683]) (by decide +kernel)
def pv225373 : PrimeValue := ⟨225373, pr225373⟩
private theorem pr225457 : Nat.Prime 225457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv61]) (by decide +kernel)
def pv225457 : PrimeValue := ⟨225457, pr225457⟩
private theorem pr225523 : Nat.Prime 225523 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv67]) (by decide +kernel)
def pv225523 : PrimeValue := ⟨225523, pr225523⟩
private theorem pr225611 : Nat.Prime 225611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv293]) (by decide +kernel)
def pv225611 : PrimeValue := ⟨225611, pr225611⟩
private theorem pr225637 : Nat.Prime 225637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18803]) (by decide +kernel)
def pv225637 : PrimeValue := ⟨225637, pr225637⟩
private theorem pr225683 : Nat.Prime 225683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv5939]) (by decide +kernel)
def pv225683 : PrimeValue := ⟨225683, pr225683⟩
private theorem pr225779 : Nat.Prime 225779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv16127]) (by decide +kernel)
def pv225779 : PrimeValue := ⟨225779, pr225779⟩
private theorem pr225829 : Nat.Prime 225829 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv41]) (by decide +kernel)
def pv225829 : PrimeValue := ⟨225829, pr225829⟩
private theorem pr225859 : Nat.Prime 225859 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv37643]) (by decide +kernel)
def pv225859 : PrimeValue := ⟨225859, pr225859⟩
private theorem pr225931 : Nat.Prime 225931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv443]) (by decide +kernel)
def pv225931 : PrimeValue := ⟨225931, pr225931⟩
private theorem pr226027 : Nat.Prime 226027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv433]) (by decide +kernel)
def pv226027 : PrimeValue := ⟨226027, pr226027⟩
private theorem pr226087 : Nat.Prime 226087 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv769]) (by decide +kernel)
def pv226087 : PrimeValue := ⟨226087, pr226087⟩
private theorem pr226123 : Nat.Prime 226123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv223]) (by decide +kernel)
def pv226123 : PrimeValue := ⟨226123, pr226123⟩
private theorem pr226217 : Nat.Prime 226217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv28277]) (by decide +kernel)
def pv226217 : PrimeValue := ⟨226217, pr226217⟩
private theorem pr226267 : Nat.Prime 226267 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv877]) (by decide +kernel)
def pv226267 : PrimeValue := ⟨226267, pr226267⟩
private theorem pr226381 : Nat.Prime 226381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv226381 : PrimeValue := ⟨226381, pr226381⟩
private theorem pr226397 : Nat.Prime 226397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv56599]) (by decide +kernel)
def pv226397 : PrimeValue := ⟨226397, pr226397⟩
private theorem pr226433 : Nat.Prime 226433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv61]) (by decide +kernel)
def pv226433 : PrimeValue := ⟨226433, pr226433⟩
private theorem pr226453 : Nat.Prime 226453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv113,pv167]) (by decide +kernel)
def pv226453 : PrimeValue := ⟨226453, pr226453⟩
private theorem pr226531 : Nat.Prime 226531 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv839]) (by decide +kernel)
def pv226531 : PrimeValue := ⟨226531, pr226531⟩
private theorem pr226601 : Nat.Prime 226601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv103]) (by decide +kernel)
def pv226601 : PrimeValue := ⟨226601, pr226601⟩
private theorem pr226609 : Nat.Prime 226609 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv4721]) (by decide +kernel)
def pv226609 : PrimeValue := ⟨226609, pr226609⟩
private theorem pr226631 : Nat.Prime 226631 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv131,pv173]) (by decide +kernel)
def pv226631 : PrimeValue := ⟨226631, pr226631⟩
private theorem pr226669 : Nat.Prime 226669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1453]) (by decide +kernel)
def pv226669 : PrimeValue := ⟨226669, pr226669⟩
private theorem pr226697 : Nat.Prime 226697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv659]) (by decide +kernel)
def pv226697 : PrimeValue := ⟨226697, pr226697⟩
private theorem pr226741 : Nat.Prime 226741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3779]) (by decide +kernel)
def pv226741 : PrimeValue := ⟨226741, pr226741⟩
private theorem pr226789 : Nat.Prime 226789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18899]) (by decide +kernel)
def pv226789 : PrimeValue := ⟨226789, pr226789⟩
private theorem pr226819 : Nat.Prime 226819 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv12601]) (by decide +kernel)
def pv226819 : PrimeValue := ⟨226819, pr226819⟩
private theorem pr227191 : Nat.Prime 227191 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7573]) (by decide +kernel)
def pv227191 : PrimeValue := ⟨227191, pr227191⟩
private theorem pr227231 : Nat.Prime 227231 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv31,pv733]) (by decide +kernel)
def pv227231 : PrimeValue := ⟨227231, pr227231⟩
private theorem pr227233 : Nat.Prime 227233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv263]) (by decide +kernel)
def pv227233 : PrimeValue := ⟨227233, pr227233⟩
private theorem pr227251 : Nat.Prime 227251 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv101]) (by decide +kernel)
def pv227251 : PrimeValue := ⟨227251, pr227251⟩
private theorem pr227299 : Nat.Prime 227299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv881]) (by decide +kernel)
def pv227299 : PrimeValue := ⟨227299, pr227299⟩
private theorem pr227371 : Nat.Prime 227371 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv13,pv53]) (by decide +kernel)
def pv227371 : PrimeValue := ⟨227371, pr227371⟩
private theorem pr227407 : Nat.Prime 227407 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv151,pv251]) (by decide +kernel)
def pv227407 : PrimeValue := ⟨227407, pr227407⟩
private theorem pr227467 : Nat.Prime 227467 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv12637]) (by decide +kernel)
def pv227467 : PrimeValue := ⟨227467, pr227467⟩
private theorem pr227473 : Nat.Prime 227473 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv677]) (by decide +kernel)
def pv227473 : PrimeValue := ⟨227473, pr227473⟩
private theorem pr227567 : Nat.Prime 227567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv113783]) (by decide +kernel)
def pv227567 : PrimeValue := ⟨227567, pr227567⟩
private theorem pr227593 : Nat.Prime 227593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv109]) (by decide +kernel)
def pv227593 : PrimeValue := ⟨227593, pr227593⟩
private theorem pr227671 : Nat.Prime 227671 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7589]) (by decide +kernel)
def pv227671 : PrimeValue := ⟨227671, pr227671⟩
private theorem pr227993 : Nat.Prime 227993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv28499]) (by decide +kernel)
def pv227993 : PrimeValue := ⟨227993, pr227993⟩
private theorem pr228049 : Nat.Prime 228049 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv4751]) (by decide +kernel)
def pv228049 : PrimeValue := ⟨228049, pr228049⟩
private theorem pr228127 : Nat.Prime 228127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv193,pv197]) (by decide +kernel)
def pv228127 : PrimeValue := ⟨228127, pr228127⟩
private theorem pr228211 : Nat.Prime 228211 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7607]) (by decide +kernel)
def pv228211 : PrimeValue := ⟨228211, pr228211⟩
private theorem pr228257 : Nat.Prime 228257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1019]) (by decide +kernel)
def pv228257 : PrimeValue := ⟨228257, pr228257⟩
private theorem pr228281 : Nat.Prime 228281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv439]) (by decide +kernel)
def pv228281 : PrimeValue := ⟨228281, pr228281⟩
private theorem pr228299 : Nat.Prime 228299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv709]) (by decide +kernel)
def pv228299 : PrimeValue := ⟨228299, pr228299⟩
private theorem pr228337 : Nat.Prime 228337 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv67,pv71]) (by decide +kernel)
def pv228337 : PrimeValue := ⟨228337, pr228337⟩
private theorem pr228353 : Nat.Prime 228353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv223]) (by decide +kernel)
def pv228353 : PrimeValue := ⟨228353, pr228353⟩
private theorem pr228419 : Nat.Prime 228419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv6011]) (by decide +kernel)
def pv228419 : PrimeValue := ⟨228419, pr228419⟩
private theorem pr228451 : Nat.Prime 228451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1523]) (by decide +kernel)
def pv228451 : PrimeValue := ⟨228451, pr228451⟩
private theorem pr228587 : Nat.Prime 228587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv3089]) (by decide +kernel)
def pv228587 : PrimeValue := ⟨228587, pr228587⟩
private theorem pr228751 : Nat.Prime 228751 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv228751 : PrimeValue := ⟨228751, pr228751⟩
private theorem pr228841 : Nat.Prime 228841 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv1907]) (by decide +kernel)
def pv228841 : PrimeValue := ⟨228841, pr228841⟩
private theorem pr228853 : Nat.Prime 228853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv163]) (by decide +kernel)
def pv228853 : PrimeValue := ⟨228853, pr228853⟩
private theorem pr228881 : Nat.Prime 228881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2861]) (by decide +kernel)
def pv228881 : PrimeValue := ⟨228881, pr228881⟩
private theorem pr228929 : Nat.Prime 228929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv73]) (by decide +kernel)
def pv228929 : PrimeValue := ⟨228929, pr228929⟩
private theorem pr228961 : Nat.Prime 228961 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv53]) (by decide +kernel)
def pv228961 : PrimeValue := ⟨228961, pr228961⟩
private theorem pr229189 : Nat.Prime 229189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv269]) (by decide +kernel)
def pv229189 : PrimeValue := ⟨229189, pr229189⟩
private theorem pr229267 : Nat.Prime 229267 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv271]) (by decide +kernel)
def pv229267 : PrimeValue := ⟨229267, pr229267⟩
private theorem pr229553 : Nat.Prime 229553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv14347]) (by decide +kernel)
def pv229553 : PrimeValue := ⟨229553, pr229553⟩
private theorem pr229681 : Nat.Prime 229681 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv11,pv29]) (by decide +kernel)
def pv229681 : PrimeValue := ⟨229681, pr229681⟩
private theorem pr229717 : Nat.Prime 229717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv709]) (by decide +kernel)
def pv229717 : PrimeValue := ⟨229717, pr229717⟩
private theorem pr229751 : Nat.Prime 229751 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv919]) (by decide +kernel)
def pv229751 : PrimeValue := ⟨229751, pr229751⟩
private theorem pr229781 : Nat.Prime 229781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11489]) (by decide +kernel)
def pv229781 : PrimeValue := ⟨229781, pr229781⟩
private theorem pr229799 : Nat.Prime 229799 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv89,pv1291]) (by decide +kernel)
def pv229799 : PrimeValue := ⟨229799, pr229799⟩
private theorem pr230003 : Nat.Prime 230003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv115001]) (by decide +kernel)
def pv230003 : PrimeValue := ⟨230003, pr230003⟩
private theorem pr230117 : Nat.Prime 230117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv57529]) (by decide +kernel)
def pv230117 : PrimeValue := ⟨230117, pr230117⟩
private theorem pr230227 : Nat.Prime 230227 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv38371]) (by decide +kernel)
def pv230227 : PrimeValue := ⟨230227, pr230227⟩
private theorem pr230311 : Nat.Prime 230311 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv853]) (by decide +kernel)
def pv230311 : PrimeValue := ⟨230311, pr230311⟩
private theorem pr230341 : Nat.Prime 230341 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv349]) (by decide +kernel)
def pv230341 : PrimeValue := ⟨230341, pr230341⟩
private theorem pr230449 : Nat.Prime 230449 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv4801]) (by decide +kernel)
def pv230449 : PrimeValue := ⟨230449, pr230449⟩
private theorem pr230467 : Nat.Prime 230467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv541]) (by decide +kernel)
def pv230467 : PrimeValue := ⟨230467, pr230467⟩
private theorem pr230539 : Nat.Prime 230539 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv11,pv499]) (by decide +kernel)
def pv230539 : PrimeValue := ⟨230539, pr230539⟩
private theorem pr230551 : Nat.Prime 230551 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv29,pv53]) (by decide +kernel)
def pv230551 : PrimeValue := ⟨230551, pr230551⟩
private theorem pr230647 : Nat.Prime 230647 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv13,pv2957]) (by decide +kernel)
def pv230647 : PrimeValue := ⟨230647, pr230647⟩
private theorem pr230999 : Nat.Prime 230999 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv115499]) (by decide +kernel)
def pv230999 : PrimeValue := ⟨230999, pr230999⟩
private theorem pr231001 : Nat.Prime 231001 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv231001 : PrimeValue := ⟨231001, pr231001⟩
private theorem pr231317 : Nat.Prime 231317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv57829]) (by decide +kernel)
def pv231317 : PrimeValue := ⟨231317, pr231317⟩
private theorem pr231461 : Nat.Prime 231461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv71,pv163]) (by decide +kernel)
def pv231461 : PrimeValue := ⟨231461, pr231461⟩
private theorem pr231529 : Nat.Prime 231529 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv877]) (by decide +kernel)
def pv231529 : PrimeValue := ⟨231529, pr231529⟩
private theorem pr231559 : Nat.Prime 231559 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv38593]) (by decide +kernel)
def pv231559 : PrimeValue := ⟨231559, pr231559⟩
private theorem pr231571 : Nat.Prime 231571 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv31,pv83]) (by decide +kernel)
def pv231571 : PrimeValue := ⟨231571, pr231571⟩
private theorem pr231631 : Nat.Prime 231631 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv1103]) (by decide +kernel)
def pv231631 : PrimeValue := ⟨231631, pr231631⟩
private theorem pr231961 : Nat.Prime 231961 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv1933]) (by decide +kernel)
def pv231961 : PrimeValue := ⟨231961, pr231961⟩
private theorem pr232007 : Nat.Prime 232007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv311,pv373]) (by decide +kernel)
def pv232007 : PrimeValue := ⟨232007, pr232007⟩
private theorem pr232049 : Nat.Prime 232049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv14503]) (by decide +kernel)
def pv232049 : PrimeValue := ⟨232049, pr232049⟩
private theorem pr232189 : Nat.Prime 232189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1759]) (by decide +kernel)
def pv232189 : PrimeValue := ⟨232189, pr232189⟩
private theorem pr232259 : Nat.Prime 232259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv8933]) (by decide +kernel)
def pv232259 : PrimeValue := ⟨232259, pr232259⟩
private theorem pr232381 : Nat.Prime 232381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1291]) (by decide +kernel)
def pv232381 : PrimeValue := ⟨232381, pr232381⟩
private theorem pr232459 : Nat.Prime 232459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv43,pv53]) (by decide +kernel)
def pv232459 : PrimeValue := ⟨232459, pr232459⟩
private theorem pr232487 : Nat.Prime 232487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv116243]) (by decide +kernel)
def pv232487 : PrimeValue := ⟨232487, pr232487⟩
private theorem pr232523 : Nat.Prime 232523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv29,pv211]) (by decide +kernel)
def pv232523 : PrimeValue := ⟨232523, pr232523⟩
private theorem pr232669 : Nat.Prime 232669 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv281]) (by decide +kernel)
def pv232669 : PrimeValue := ⟨232669, pr232669⟩
private theorem pr232711 : Nat.Prime 232711 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7757]) (by decide +kernel)
def pv232711 : PrimeValue := ⟨232711, pr232711⟩
private theorem pr232877 : Nat.Prime 232877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv8317]) (by decide +kernel)
def pv232877 : PrimeValue := ⟨232877, pr232877⟩
private theorem pr232891 : Nat.Prime 232891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv1109]) (by decide +kernel)
def pv232891 : PrimeValue := ⟨232891, pr232891⟩
private theorem pr232901 : Nat.Prime 232901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv137]) (by decide +kernel)
def pv232901 : PrimeValue := ⟨232901, pr232901⟩
private theorem pr233297 : Nat.Prime 233297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv2083]) (by decide +kernel)
def pv233297 : PrimeValue := ⟨233297, pr233297⟩
private theorem pr233551 : Nat.Prime 233551 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv173]) (by decide +kernel)
def pv233551 : PrimeValue := ⟨233551, pr233551⟩
private theorem pr233609 : Nat.Prime 233609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29201]) (by decide +kernel)
def pv233609 : PrimeValue := ⟨233609, pr233609⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
