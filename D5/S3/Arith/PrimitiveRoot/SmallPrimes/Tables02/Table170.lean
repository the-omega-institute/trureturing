/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table170
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table170.pv268637
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table048
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table050

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr268637 : Nat.Prime 268637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv239,pv281]) (by decide +kernel)
def pv268637 : PrimeValue := ⟨268637, pr268637⟩
private theorem pr268757 : Nat.Prime 268757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67189]) (by decide +kernel)
def pv268757 : PrimeValue := ⟨268757, pr268757⟩
private theorem pr268771 : Nat.Prime 268771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv31]) (by decide +kernel)
def pv268771 : PrimeValue := ⟨268771, pr268771⟩
private theorem pr268811 : Nat.Prime 268811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv26881]) (by decide +kernel)
def pv268811 : PrimeValue := ⟨268811, pr268811⟩
private theorem pr268813 : Nat.Prime 268813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv131]) (by decide +kernel)
def pv268813 : PrimeValue := ⟨268813, pr268813⟩
private theorem pr268823 : Nat.Prime 268823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv257,pv523]) (by decide +kernel)
def pv268823 : PrimeValue := ⟨268823, pr268823⟩
private theorem pr268883 : Nat.Prime 268883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv233,pv577]) (by decide +kernel)
def pv268883 : PrimeValue := ⟨268883, pr268883⟩
private theorem pr268921 : Nat.Prime 268921 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv83]) (by decide +kernel)
def pv268921 : PrimeValue := ⟨268921, pr268921⟩
private theorem pr268927 : Nat.Prime 268927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv337]) (by decide +kernel)
def pv268927 : PrimeValue := ⟨268927, pr268927⟩
private theorem pr269023 : Nat.Prime 269023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv3449]) (by decide +kernel)
def pv269023 : PrimeValue := ⟨269023, pr269023⟩
private theorem pr269089 : Nat.Prime 269089 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv2803]) (by decide +kernel)
def pv269089 : PrimeValue := ⟨269089, pr269089⟩
private theorem pr269219 : Nat.Prime 269219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv134609]) (by decide +kernel)
def pv269219 : PrimeValue := ⟨269219, pr269219⟩
private theorem pr269257 : Nat.Prime 269257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv863]) (by decide +kernel)
def pv269257 : PrimeValue := ⟨269257, pr269257⟩
private theorem pr269377 : Nat.Prime 269377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv61]) (by decide +kernel)
def pv269377 : PrimeValue := ⟨269377, pr269377⟩
private theorem pr269413 : Nat.Prime 269413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv157]) (by decide +kernel)
def pv269413 : PrimeValue := ⟨269413, pr269413⟩
private theorem pr269431 : Nat.Prime 269431 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv1283]) (by decide +kernel)
def pv269431 : PrimeValue := ⟨269431, pr269431⟩
private theorem pr269597 : Nat.Prime 269597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67399]) (by decide +kernel)
def pv269597 : PrimeValue := ⟨269597, pr269597⟩
private theorem pr269761 : Nat.Prime 269761 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv281]) (by decide +kernel)
def pv269761 : PrimeValue := ⟨269761, pr269761⟩
private theorem pr269779 : Nat.Prime 269779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv44963]) (by decide +kernel)
def pv269779 : PrimeValue := ⟨269779, pr269779⟩
private theorem pr270037 : Nat.Prime 270037 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv13,pv577]) (by decide +kernel)
def pv270037 : PrimeValue := ⟨270037, pr270037⟩
private theorem pr270271 : Nat.Prime 270271 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv11,pv13]) (by decide +kernel)
def pv270271 : PrimeValue := ⟨270271, pr270271⟩
private theorem pr270337 : Nat.Prime 270337 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv270337 : PrimeValue := ⟨270337, pr270337⟩
private theorem pr270407 : Nat.Prime 270407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv2551]) (by decide +kernel)
def pv270407 : PrimeValue := ⟨270407, pr270407⟩
private theorem pr270437 : Nat.Prime 270437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv41,pv97]) (by decide +kernel)
def pv270437 : PrimeValue := ⟨270437, pr270437⟩
private theorem pr270587 : Nat.Prime 270587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv193,pv701]) (by decide +kernel)
def pv270587 : PrimeValue := ⟨270587, pr270587⟩
private theorem pr270593 : Nat.Prime 270593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv151]) (by decide +kernel)
def pv270593 : PrimeValue := ⟨270593, pr270593⟩
private theorem pr270601 : Nat.Prime 270601 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv11,pv41]) (by decide +kernel)
def pv270601 : PrimeValue := ⟨270601, pr270601⟩
private theorem pr270631 : Nat.Prime 270631 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv31,pv97]) (by decide +kernel)
def pv270631 : PrimeValue := ⟨270631, pr270631⟩
private theorem pr270659 : Nat.Prime 270659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv135329]) (by decide +kernel)
def pv270659 : PrimeValue := ⟨270659, pr270659⟩
private theorem pr270667 : Nat.Prime 270667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1367]) (by decide +kernel)
def pv270667 : PrimeValue := ⟨270667, pr270667⟩
private theorem pr270749 : Nat.Prime 270749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv599]) (by decide +kernel)
def pv270749 : PrimeValue := ⟨270749, pr270749⟩
private theorem pr270841 : Nat.Prime 270841 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv37,pv61]) (by decide +kernel)
def pv270841 : PrimeValue := ⟨270841, pr270841⟩
private theorem pr271097 : Nat.Prime 271097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv47,pv103]) (by decide +kernel)
def pv271097 : PrimeValue := ⟨271097, pr271097⟩
private theorem pr271169 : Nat.Prime 271169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv223]) (by decide +kernel)
def pv271169 : PrimeValue := ⟨271169, pr271169⟩
private theorem pr271261 : Nat.Prime 271261 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv137]) (by decide +kernel)
def pv271261 : PrimeValue := ⟨271261, pr271261⟩
private theorem pr271277 : Nat.Prime 271277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67819]) (by decide +kernel)
def pv271277 : PrimeValue := ⟨271277, pr271277⟩
private theorem pr271409 : Nat.Prime 271409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv16963]) (by decide +kernel)
def pv271409 : PrimeValue := ⟨271409, pr271409⟩
private theorem pr271637 : Nat.Prime 271637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv1151]) (by decide +kernel)
def pv271637 : PrimeValue := ⟨271637, pr271637⟩
private theorem pr271861 : Nat.Prime 271861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv197]) (by decide +kernel)
def pv271861 : PrimeValue := ⟨271861, pr271861⟩
private theorem pr271927 : Nat.Prime 271927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv15107]) (by decide +kernel)
def pv271927 : PrimeValue := ⟨271927, pr271927⟩
private theorem pr272011 : Nat.Prime 272011 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv9067]) (by decide +kernel)
def pv272011 : PrimeValue := ⟨272011, pr272011⟩
private theorem pr272029 : Nat.Prime 272029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv22669]) (by decide +kernel)
def pv272029 : PrimeValue := ⟨272029, pr272029⟩
private theorem pr272053 : Nat.Prime 272053 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv229]) (by decide +kernel)
def pv272053 : PrimeValue := ⟨272053, pr272053⟩
private theorem pr272171 : Nat.Prime 272171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv1601]) (by decide +kernel)
def pv272171 : PrimeValue := ⟨272171, pr272171⟩
private theorem pr272249 : Nat.Prime 272249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv34031]) (by decide +kernel)
def pv272249 : PrimeValue := ⟨272249, pr272249⟩
private theorem pr272369 : Nat.Prime 272369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv587]) (by decide +kernel)
def pv272369 : PrimeValue := ⟨272369, pr272369⟩
private theorem pr272383 : Nat.Prime 272383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv4127]) (by decide +kernel)
def pv272383 : PrimeValue := ⟨272383, pr272383⟩
private theorem pr272411 : Nat.Prime 272411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv27241]) (by decide +kernel)
def pv272411 : PrimeValue := ⟨272411, pr272411⟩
private theorem pr272477 : Nat.Prime 272477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv4007]) (by decide +kernel)
def pv272477 : PrimeValue := ⟨272477, pr272477⟩
private theorem pr272761 : Nat.Prime 272761 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv2273]) (by decide +kernel)
def pv272761 : PrimeValue := ⟨272761, pr272761⟩
private theorem pr272777 : Nat.Prime 272777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv4871]) (by decide +kernel)
def pv272777 : PrimeValue := ⟨272777, pr272777⟩
private theorem pr272911 : Nat.Prime 272911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv827]) (by decide +kernel)
def pv272911 : PrimeValue := ⟨272911, pr272911⟩
private theorem pr272917 : Nat.Prime 272917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv272917 : PrimeValue := ⟨272917, pr272917⟩
private theorem pr272971 : Nat.Prime 272971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv337]) (by decide +kernel)
def pv272971 : PrimeValue := ⟨272971, pr272971⟩
private theorem pr273127 : Nat.Prime 273127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv929]) (by decide +kernel)
def pv273127 : PrimeValue := ⟨273127, pr273127⟩
private theorem pr273457 : Nat.Prime 273457 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv211]) (by decide +kernel)
def pv273457 : PrimeValue := ⟨273457, pr273457⟩
private theorem pr273527 : Nat.Prime 273527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv12433]) (by decide +kernel)
def pv273527 : PrimeValue := ⟨273527, pr273527⟩
private theorem pr273641 : Nat.Prime 273641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv6841]) (by decide +kernel)
def pv273641 : PrimeValue := ⟨273641, pr273641⟩
private theorem pr273697 : Nat.Prime 273697 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2851]) (by decide +kernel)
def pv273697 : PrimeValue := ⟨273697, pr273697⟩
private theorem pr273719 : Nat.Prime 273719 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv136859]) (by decide +kernel)
def pv273719 : PrimeValue := ⟨273719, pr273719⟩
private theorem pr273979 : Nat.Prime 273979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv491]) (by decide +kernel)
def pv273979 : PrimeValue := ⟨273979, pr273979⟩
private theorem pr274163 : Nat.Prime 274163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19583]) (by decide +kernel)
def pv274163 : PrimeValue := ⟨274163, pr274163⟩
private theorem pr274177 : Nat.Prime 274177 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv274177 : PrimeValue := ⟨274177, pr274177⟩
private theorem pr274201 : Nat.Prime 274201 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv457]) (by decide +kernel)
def pv274201 : PrimeValue := ⟨274201, pr274201⟩
private theorem pr274697 : Nat.Prime 274697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv34337]) (by decide +kernel)
def pv274697 : PrimeValue := ⟨274697, pr274697⟩
private theorem pr274739 : Nat.Prime 274739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv137369]) (by decide +kernel)
def pv274739 : PrimeValue := ⟨274739, pr274739⟩
private theorem pr274777 : Nat.Prime 274777 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv274777 : PrimeValue := ⟨274777, pr274777⟩
private theorem pr274817 : Nat.Prime 274817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv113]) (by decide +kernel)
def pv274817 : PrimeValue := ⟨274817, pr274817⟩
private theorem pr274829 : Nat.Prime 274829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127,pv541]) (by decide +kernel)
def pv274829 : PrimeValue := ⟨274829, pr274829⟩
private theorem pr274847 : Nat.Prime 274847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv13,pv31]) (by decide +kernel)
def pv274847 : PrimeValue := ⟨274847, pr274847⟩
private theorem pr274861 : Nat.Prime 274861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv509]) (by decide +kernel)
def pv274861 : PrimeValue := ⟨274861, pr274861⟩
private theorem pr274889 : Nat.Prime 274889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv34361]) (by decide +kernel)
def pv274889 : PrimeValue := ⟨274889, pr274889⟩
private theorem pr275087 : Nat.Prime 275087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv401]) (by decide +kernel)
def pv275087 : PrimeValue := ⟨275087, pr275087⟩
private theorem pr275147 : Nat.Prime 275147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv137573]) (by decide +kernel)
def pv275147 : PrimeValue := ⟨275147, pr275147⟩
private theorem pr275153 : Nat.Prime 275153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv593]) (by decide +kernel)
def pv275153 : PrimeValue := ⟨275153, pr275153⟩
private theorem pr275309 : Nat.Prime 275309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv6257]) (by decide +kernel)
def pv275309 : PrimeValue := ⟨275309, pr275309⟩
private theorem pr275581 : Nat.Prime 275581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1531]) (by decide +kernel)
def pv275581 : PrimeValue := ⟨275581, pr275581⟩
private theorem pr275591 : Nat.Prime 275591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv31,pv127]) (by decide +kernel)
def pv275591 : PrimeValue := ⟨275591, pr275591⟩
private theorem pr275699 : Nat.Prime 275699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv137849]) (by decide +kernel)
def pv275699 : PrimeValue := ⟨275699, pr275699⟩
private theorem pr275881 : Nat.Prime 275881 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv11,pv19]) (by decide +kernel)
def pv275881 : PrimeValue := ⟨275881, pr275881⟩
private theorem pr275897 : Nat.Prime 275897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv34487]) (by decide +kernel)
def pv275897 : PrimeValue := ⟨275897, pr275897⟩
private theorem pr275939 : Nat.Prime 275939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv10613]) (by decide +kernel)
def pv275939 : PrimeValue := ⟨275939, pr275939⟩
private theorem pr276019 : Nat.Prime 276019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv179,pv257]) (by decide +kernel)
def pv276019 : PrimeValue := ⟨276019, pr276019⟩
private theorem pr276043 : Nat.Prime 276043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv3539]) (by decide +kernel)
def pv276043 : PrimeValue := ⟨276043, pr276043⟩
private theorem pr276049 : Nat.Prime 276049 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv276049 : PrimeValue := ⟨276049, pr276049⟩
private theorem pr276151 : Nat.Prime 276151 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv263]) (by decide +kernel)
def pv276151 : PrimeValue := ⟨276151, pr276151⟩
private theorem pr276209 : Nat.Prime 276209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61,pv283]) (by decide +kernel)
def pv276209 : PrimeValue := ⟨276209, pr276209⟩
private theorem pr276247 : Nat.Prime 276247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv103,pv149]) (by decide +kernel)
def pv276247 : PrimeValue := ⟨276247, pr276247⟩
private theorem pr276319 : Nat.Prime 276319 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv43]) (by decide +kernel)
def pv276319 : PrimeValue := ⟨276319, pr276319⟩
private theorem pr276599 : Nat.Prime 276599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv23,pv859]) (by decide +kernel)
def pv276599 : PrimeValue := ⟨276599, pr276599⟩
private theorem pr276637 : Nat.Prime 276637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23053]) (by decide +kernel)
def pv276637 : PrimeValue := ⟨276637, pr276637⟩
private theorem pr276707 : Nat.Prime 276707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv4463]) (by decide +kernel)
def pv276707 : PrimeValue := ⟨276707, pr276707⟩
private theorem pr276781 : Nat.Prime 276781 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv659]) (by decide +kernel)
def pv276781 : PrimeValue := ⟨276781, pr276781⟩
private theorem pr277087 : Nat.Prime 277087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv46181]) (by decide +kernel)
def pv277087 : PrimeValue := ⟨277087, pr277087⟩
private theorem pr277301 : Nat.Prime 277301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv59]) (by decide +kernel)
def pv277301 : PrimeValue := ⟨277301, pr277301⟩
private theorem pr277309 : Nat.Prime 277309 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7703]) (by decide +kernel)
def pv277309 : PrimeValue := ⟨277309, pr277309⟩
private theorem pr277513 : Nat.Prime 277513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv373]) (by decide +kernel)
def pv277513 : PrimeValue := ⟨277513, pr277513⟩
private theorem pr277531 : Nat.Prime 277531 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv29]) (by decide +kernel)
def pv277531 : PrimeValue := ⟨277531, pr277531⟩
private theorem pr277549 : Nat.Prime 277549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv101,pv229]) (by decide +kernel)
def pv277549 : PrimeValue := ⟨277549, pr277549⟩
private theorem pr277577 : Nat.Prime 277577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv17,pv157]) (by decide +kernel)
def pv277577 : PrimeValue := ⟨277577, pr277577⟩
private theorem pr277747 : Nat.Prime 277747 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv17,pv389]) (by decide +kernel)
def pv277747 : PrimeValue := ⟨277747, pr277747⟩
private theorem pr277757 : Nat.Prime 277757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv69439]) (by decide +kernel)
def pv277757 : PrimeValue := ⟨277757, pr277757⟩
private theorem pr277829 : Nat.Prime 277829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv69457]) (by decide +kernel)
def pv277829 : PrimeValue := ⟨277829, pr277829⟩
private theorem pr277847 : Nat.Prime 277847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv138923]) (by decide +kernel)
def pv277847 : PrimeValue := ⟨277847, pr277847⟩
private theorem pr277859 : Nat.Prime 277859 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv89,pv223]) (by decide +kernel)
def pv277859 : PrimeValue := ⟨277859, pr277859⟩
private theorem pr277897 : Nat.Prime 277897 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11579]) (by decide +kernel)
def pv277897 : PrimeValue := ⟨277897, pr277897⟩
private theorem pr278017 : Nat.Prime 278017 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv181]) (by decide +kernel)
def pv278017 : PrimeValue := ⟨278017, pr278017⟩
private theorem pr278041 : Nat.Prime 278041 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv7,pv331]) (by decide +kernel)
def pv278041 : PrimeValue := ⟨278041, pr278041⟩
private theorem pr278227 : Nat.Prime 278227 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv29,pv41]) (by decide +kernel)
def pv278227 : PrimeValue := ⟨278227, pr278227⟩
private theorem pr278627 : Nat.Prime 278627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv139313]) (by decide +kernel)
def pv278627 : PrimeValue := ⟨278627, pr278627⟩
private theorem pr278671 : Nat.Prime 278671 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv1327]) (by decide +kernel)
def pv278671 : PrimeValue := ⟨278671, pr278671⟩
private theorem pr278717 : Nat.Prime 278717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv1181]) (by decide +kernel)
def pv278717 : PrimeValue := ⟨278717, pr278717⟩
private theorem pr278903 : Nat.Prime 278903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv17,pv631]) (by decide +kernel)
def pv278903 : PrimeValue := ⟨278903, pr278903⟩
private theorem pr278909 : Nat.Prime 278909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1423]) (by decide +kernel)
def pv278909 : PrimeValue := ⟨278909, pr278909⟩
private theorem pr278917 : Nat.Prime 278917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv2113]) (by decide +kernel)
def pv278917 : PrimeValue := ⟨278917, pr278917⟩
private theorem pr279023 : Nat.Prime 279023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv139511]) (by decide +kernel)
def pv279023 : PrimeValue := ⟨279023, pr279023⟩
private theorem pr279047 : Nat.Prime 279047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv83]) (by decide +kernel)
def pv279047 : PrimeValue := ⟨279047, pr279047⟩
private theorem pr279137 : Nat.Prime 279137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13,pv61]) (by decide +kernel)
def pv279137 : PrimeValue := ⟨279137, pr279137⟩
private theorem pr279211 : Nat.Prime 279211 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv41,pv227]) (by decide +kernel)
def pv279211 : PrimeValue := ⟨279211, pr279211⟩
private theorem pr279451 : Nat.Prime 279451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv279451 : PrimeValue := ⟨279451, pr279451⟩
private theorem pr279593 : Nat.Prime 279593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv34949]) (by decide +kernel)
def pv279593 : PrimeValue := ⟨279593, pr279593⟩
private theorem pr279607 : Nat.Prime 279607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv46601]) (by decide +kernel)
def pv279607 : PrimeValue := ⟨279607, pr279607⟩
private theorem pr279967 : Nat.Prime 279967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv1609]) (by decide +kernel)
def pv279967 : PrimeValue := ⟨279967, pr279967⟩
private theorem pr280187 : Nat.Prime 280187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv6091]) (by decide +kernel)
def pv280187 : PrimeValue := ⟨280187, pr280187⟩
private theorem pr280303 : Nat.Prime 280303 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv31,pv137]) (by decide +kernel)
def pv280303 : PrimeValue := ⟨280303, pr280303⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
