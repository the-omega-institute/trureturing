/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table081
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table081.pv275039
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table050

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr275039 : PrimeCertificate 275039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv137519]) (by decide +kernel)
def pv275039 : PrimeValue := ⟨275039, pr275039⟩
private theorem pr275047 : PrimeCertificate 275047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv45841]) (by decide +kernel)
def pv275047 : PrimeValue := ⟨275047, pr275047⟩
private theorem pr275053 : PrimeCertificate 275053 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv22921]) (by decide +kernel)
def pv275053 : PrimeValue := ⟨275053, pr275053⟩
private theorem pr275083 : PrimeCertificate 275083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv127]) (by decide +kernel)
def pv275083 : PrimeValue := ⟨275083, pr275083⟩
private theorem pr275129 : PrimeCertificate 275129 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv17]) (by decide +kernel)
def pv275129 : PrimeValue := ⟨275129, pr275129⟩
private theorem pr275159 : PrimeCertificate 275159 :=
  certifyPrime (q := pv11) (ls := [pv2,pv13,pv19,pv557]) (by decide +kernel)
def pv275159 : PrimeValue := ⟨275159, pr275159⟩
private theorem pr275161 : PrimeCertificate 275161 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2293]) (by decide +kernel)
def pv275161 : PrimeValue := ⟨275161, pr275161⟩
private theorem pr275183 : PrimeCertificate 275183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv223,pv617]) (by decide +kernel)
def pv275183 : PrimeValue := ⟨275183, pr275183⟩
private theorem pr275201 : PrimeCertificate 275201 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv43]) (by decide +kernel)
def pv275201 : PrimeValue := ⟨275201, pr275201⟩
private theorem pr275227 : PrimeCertificate 275227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv6553]) (by decide +kernel)
def pv275227 : PrimeValue := ⟨275227, pr275227⟩
private theorem pr275269 : PrimeCertificate 275269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv113]) (by decide +kernel)
def pv275269 : PrimeValue := ⟨275269, pr275269⟩
private theorem pr275339 : PrimeCertificate 275339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv71,pv277]) (by decide +kernel)
def pv275339 : PrimeValue := ⟨275339, pr275339⟩
private theorem pr275357 : PrimeCertificate 275357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv41,pv73]) (by decide +kernel)
def pv275357 : PrimeValue := ⟨275357, pr275357⟩
private theorem pr275389 : PrimeCertificate 275389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv433]) (by decide +kernel)
def pv275389 : PrimeValue := ⟨275389, pr275389⟩
private theorem pr275393 : PrimeCertificate 275393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv331]) (by decide +kernel)
def pv275393 : PrimeValue := ⟨275393, pr275393⟩
private theorem pr275449 : PrimeCertificate 275449 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv499]) (by decide +kernel)
def pv275449 : PrimeValue := ⟨275449, pr275449⟩
private theorem pr275453 : PrimeCertificate 275453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv68863]) (by decide +kernel)
def pv275453 : PrimeValue := ⟨275453, pr275453⟩
private theorem pr275459 : PrimeCertificate 275459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv3203]) (by decide +kernel)
def pv275459 : PrimeValue := ⟨275459, pr275459⟩
private theorem pr275461 : PrimeCertificate 275461 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv4591]) (by decide +kernel)
def pv275461 : PrimeValue := ⟨275461, pr275461⟩
private theorem pr275491 : PrimeCertificate 275491 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv3061]) (by decide +kernel)
def pv275491 : PrimeValue := ⟨275491, pr275491⟩
private theorem pr275503 : PrimeCertificate 275503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv37,pv73]) (by decide +kernel)
def pv275503 : PrimeValue := ⟨275503, pr275503⟩
private theorem pr275521 : PrimeCertificate 275521 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv7,pv41]) (by decide +kernel)
def pv275521 : PrimeValue := ⟨275521, pr275521⟩
private theorem pr275531 : PrimeCertificate 275531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv467]) (by decide +kernel)
def pv275531 : PrimeValue := ⟨275531, pr275531⟩
private theorem pr275543 : PrimeCertificate 275543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv137771]) (by decide +kernel)
def pv275543 : PrimeValue := ⟨275543, pr275543⟩
private theorem pr275549 : PrimeCertificate 275549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv757]) (by decide +kernel)
def pv275549 : PrimeValue := ⟨275549, pr275549⟩
private theorem pr275573 : PrimeCertificate 275573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv6263]) (by decide +kernel)
def pv275573 : PrimeValue := ⟨275573, pr275573⟩
private theorem pr275599 : PrimeCertificate 275599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv251]) (by decide +kernel)
def pv275599 : PrimeValue := ⟨275599, pr275599⟩
private theorem pr275623 : PrimeCertificate 275623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv647]) (by decide +kernel)
def pv275623 : PrimeValue := ⟨275623, pr275623⟩
private theorem pr275641 : PrimeCertificate 275641 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv5,pv2297]) (by decide +kernel)
def pv275641 : PrimeValue := ⟨275641, pr275641⟩
private theorem pr275669 : PrimeCertificate 275669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv68917]) (by decide +kernel)
def pv275669 : PrimeValue := ⟨275669, pr275669⟩
private theorem pr275677 : PrimeCertificate 275677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22973]) (by decide +kernel)
def pv275677 : PrimeValue := ⟨275677, pr275677⟩
private theorem pr275711 : PrimeCertificate 275711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv79,pv349]) (by decide +kernel)
def pv275711 : PrimeValue := ⟨275711, pr275711⟩
private theorem pr275719 : PrimeCertificate 275719 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv45953]) (by decide +kernel)
def pv275719 : PrimeValue := ⟨275719, pr275719⟩
private theorem pr275729 : PrimeCertificate 275729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv907]) (by decide +kernel)
def pv275729 : PrimeValue := ⟨275729, pr275729⟩
private theorem pr275741 : PrimeCertificate 275741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv811]) (by decide +kernel)
def pv275741 : PrimeValue := ⟨275741, pr275741⟩
private theorem pr275773 : PrimeCertificate 275773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv275773 : PrimeValue := ⟨275773, pr275773⟩
private theorem pr275813 : PrimeCertificate 275813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv1301]) (by decide +kernel)
def pv275813 : PrimeValue := ⟨275813, pr275813⟩
private theorem pr275827 : PrimeCertificate 275827 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv45971]) (by decide +kernel)
def pv275827 : PrimeValue := ⟨275827, pr275827⟩
private theorem pr275837 : PrimeCertificate 275837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv6269]) (by decide +kernel)
def pv275837 : PrimeValue := ⟨275837, pr275837⟩
private theorem pr275911 : PrimeCertificate 275911 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv17,pv541]) (by decide +kernel)
def pv275911 : PrimeValue := ⟨275911, pr275911⟩
private theorem pr275917 : PrimeCertificate 275917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22993]) (by decide +kernel)
def pv275917 : PrimeValue := ⟨275917, pr275917⟩
private theorem pr275921 : PrimeCertificate 275921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3449]) (by decide +kernel)
def pv275921 : PrimeValue := ⟨275921, pr275921⟩
private theorem pr275923 : PrimeCertificate 275923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15329]) (by decide +kernel)
def pv275923 : PrimeValue := ⟨275923, pr275923⟩
private theorem pr275929 : PrimeCertificate 275929 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11497]) (by decide +kernel)
def pv275929 : PrimeValue := ⟨275929, pr275929⟩
private theorem pr275941 : PrimeCertificate 275941 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv73]) (by decide +kernel)
def pv275941 : PrimeValue := ⟨275941, pr275941⟩
private theorem pr275963 : PrimeCertificate 275963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv4451]) (by decide +kernel)
def pv275963 : PrimeValue := ⟨275963, pr275963⟩
private theorem pr275981 : PrimeCertificate 275981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13799]) (by decide +kernel)
def pv275981 : PrimeValue := ⟨275981, pr275981⟩
private theorem pr275987 : PrimeCertificate 275987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137993]) (by decide +kernel)
def pv275987 : PrimeValue := ⟨275987, pr275987⟩
private theorem pr275999 : PrimeCertificate 275999 :=
  certifyPrime (q := pv11) (ls := [pv2,pv137999]) (by decide +kernel)
def pv275999 : PrimeValue := ⟨275999, pr275999⟩
private theorem pr276007 : PrimeCertificate 276007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv157,pv293]) (by decide +kernel)
def pv276007 : PrimeValue := ⟨276007, pr276007⟩
private theorem pr276037 : PrimeCertificate 276037 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23003]) (by decide +kernel)
def pv276037 : PrimeValue := ⟨276037, pr276037⟩
private theorem pr276041 : PrimeCertificate 276041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv67,pv103]) (by decide +kernel)
def pv276041 : PrimeValue := ⟨276041, pr276041⟩
private theorem pr276047 : PrimeCertificate 276047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv23,pv353]) (by decide +kernel)
def pv276047 : PrimeValue := ⟨276047, pr276047⟩
private theorem pr276113 : PrimeCertificate 276113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17257]) (by decide +kernel)
def pv276113 : PrimeValue := ⟨276113, pr276113⟩
private theorem pr276173 : PrimeCertificate 276173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv47,pv113]) (by decide +kernel)
def pv276173 : PrimeValue := ⟨276173, pr276173⟩
private theorem pr276181 : PrimeCertificate 276181 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv4603]) (by decide +kernel)
def pv276181 : PrimeValue := ⟨276181, pr276181⟩
private theorem pr276187 : PrimeCertificate 276187 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv191,pv241]) (by decide +kernel)
def pv276187 : PrimeValue := ⟨276187, pr276187⟩
private theorem pr276239 : PrimeCertificate 276239 :=
  certifyPrime (q := pv13) (ls := [pv2,pv59,pv2341]) (by decide +kernel)
def pv276239 : PrimeValue := ⟨276239, pr276239⟩
private theorem pr276251 : PrimeCertificate 276251 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv13,pv17]) (by decide +kernel)
def pv276251 : PrimeValue := ⟨276251, pr276251⟩
private theorem pr276257 : PrimeCertificate 276257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv97]) (by decide +kernel)
def pv276257 : PrimeValue := ⟨276257, pr276257⟩
private theorem pr276277 : PrimeCertificate 276277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv13,pv23]) (by decide +kernel)
def pv276277 : PrimeValue := ⟨276277, pr276277⟩
private theorem pr276323 : PrimeCertificate 276323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv6007]) (by decide +kernel)
def pv276323 : PrimeValue := ⟨276323, pr276323⟩
private theorem pr276337 : PrimeCertificate 276337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv101]) (by decide +kernel)
def pv276337 : PrimeValue := ⟨276337, pr276337⟩
private theorem pr276347 : PrimeCertificate 276347 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv19739]) (by decide +kernel)
def pv276347 : PrimeValue := ⟨276347, pr276347⟩
private theorem pr276401 : PrimeCertificate 276401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv691]) (by decide +kernel)
def pv276401 : PrimeValue := ⟨276401, pr276401⟩
private theorem pr276439 : PrimeCertificate 276439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv46073]) (by decide +kernel)
def pv276439 : PrimeValue := ⟨276439, pr276439⟩
private theorem pr276443 : PrimeCertificate 276443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv2063]) (by decide +kernel)
def pv276443 : PrimeValue := ⟨276443, pr276443⟩
private theorem pr276449 : PrimeCertificate 276449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv163]) (by decide +kernel)
def pv276449 : PrimeValue := ⟨276449, pr276449⟩
private theorem pr276461 : PrimeCertificate 276461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv601]) (by decide +kernel)
def pv276461 : PrimeValue := ⟨276461, pr276461⟩
private theorem pr276487 : PrimeCertificate 276487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv29,pv227]) (by decide +kernel)
def pv276487 : PrimeValue := ⟨276487, pr276487⟩
private theorem pr276499 : PrimeCertificate 276499 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv15361]) (by decide +kernel)
def pv276499 : PrimeValue := ⟨276499, pr276499⟩
private theorem pr276517 : PrimeCertificate 276517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7681]) (by decide +kernel)
def pv276517 : PrimeValue := ⟨276517, pr276517⟩
private theorem pr276553 : PrimeCertificate 276553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv167]) (by decide +kernel)
def pv276553 : PrimeValue := ⟨276553, pr276553⟩
private theorem pr276589 : PrimeCertificate 276589 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv197]) (by decide +kernel)
def pv276589 : PrimeValue := ⟨276589, pr276589⟩
private theorem pr276593 : PrimeCertificate 276593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv293]) (by decide +kernel)
def pv276593 : PrimeValue := ⟨276593, pr276593⟩
private theorem pr276629 : PrimeCertificate 276629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv6287]) (by decide +kernel)
def pv276629 : PrimeValue := ⟨276629, pr276629⟩
private theorem pr276673 : PrimeCertificate 276673 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv131]) (by decide +kernel)
def pv276673 : PrimeValue := ⟨276673, pr276673⟩
private theorem pr276739 : PrimeCertificate 276739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv599]) (by decide +kernel)
def pv276739 : PrimeValue := ⟨276739, pr276739⟩
private theorem pr276763 : PrimeCertificate 276763 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv193,pv239]) (by decide +kernel)
def pv276763 : PrimeValue := ⟨276763, pr276763⟩
private theorem pr276767 : PrimeCertificate 276767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv53,pv373]) (by decide +kernel)
def pv276767 : PrimeValue := ⟨276767, pr276767⟩
private theorem pr276817 : PrimeCertificate 276817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv73,pv79]) (by decide +kernel)
def pv276817 : PrimeValue := ⟨276817, pr276817⟩
private theorem pr276821 : PrimeCertificate 276821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13841]) (by decide +kernel)
def pv276821 : PrimeValue := ⟨276821, pr276821⟩
private theorem pr276823 : PrimeCertificate 276823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv276823 : PrimeValue := ⟨276823, pr276823⟩
private theorem pr276827 : PrimeCertificate 276827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv12583]) (by decide +kernel)
def pv276827 : PrimeValue := ⟨276827, pr276827⟩
private theorem pr276833 : PrimeCertificate 276833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv211]) (by decide +kernel)
def pv276833 : PrimeValue := ⟨276833, pr276833⟩
private theorem pr276839 : PrimeCertificate 276839 :=
  certifyPrime (q := pv17) (ls := [pv2,pv97,pv1427]) (by decide +kernel)
def pv276839 : PrimeValue := ⟨276839, pr276839⟩
private theorem pr276847 : PrimeCertificate 276847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv46141]) (by decide +kernel)
def pv276847 : PrimeValue := ⟨276847, pr276847⟩
private theorem pr276917 : PrimeCertificate 276917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv647]) (by decide +kernel)
def pv276917 : PrimeValue := ⟨276917, pr276917⟩
private theorem pr276919 : PrimeCertificate 276919 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv46153]) (by decide +kernel)
def pv276919 : PrimeValue := ⟨276919, pr276919⟩
private theorem pr276949 : PrimeCertificate 276949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv157]) (by decide +kernel)
def pv276949 : PrimeValue := ⟨276949, pr276949⟩
private theorem pr277007 : PrimeCertificate 277007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv3221]) (by decide +kernel)
def pv277007 : PrimeValue := ⟨277007, pr277007⟩
private theorem pr277021 : PrimeCertificate 277021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv277021 : PrimeValue := ⟨277021, pr277021⟩
private theorem pr277051 : PrimeCertificate 277051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1847]) (by decide +kernel)
def pv277051 : PrimeValue := ⟨277051, pr277051⟩
private theorem pr277063 : PrimeCertificate 277063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv757]) (by decide +kernel)
def pv277063 : PrimeValue := ⟨277063, pr277063⟩
private theorem pr277073 : PrimeCertificate 277073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17317]) (by decide +kernel)
def pv277073 : PrimeValue := ⟨277073, pr277073⟩
private theorem pr277097 : PrimeCertificate 277097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv1823]) (by decide +kernel)
def pv277097 : PrimeValue := ⟨277097, pr277097⟩
private theorem pr277099 : PrimeCertificate 277099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv46183]) (by decide +kernel)
def pv277099 : PrimeValue := ⟨277099, pr277099⟩
private theorem pr277157 : PrimeCertificate 277157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv6299]) (by decide +kernel)
def pv277157 : PrimeValue := ⟨277157, pr277157⟩
private theorem pr277163 : PrimeCertificate 277163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv138581]) (by decide +kernel)
def pv277163 : PrimeValue := ⟨277163, pr277163⟩
private theorem pr277183 : PrimeCertificate 277183 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv59]) (by decide +kernel)
def pv277183 : PrimeValue := ⟨277183, pr277183⟩
private theorem pr277213 : PrimeCertificate 277213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1777]) (by decide +kernel)
def pv277213 : PrimeValue := ⟨277213, pr277213⟩
private theorem pr277217 : PrimeCertificate 277217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8663]) (by decide +kernel)
def pv277217 : PrimeValue := ⟨277217, pr277217⟩
private theorem pr277223 : PrimeCertificate 277223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv12601]) (by decide +kernel)
def pv277223 : PrimeValue := ⟨277223, pr277223⟩
private theorem pr277231 : PrimeCertificate 277231 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv9241]) (by decide +kernel)
def pv277231 : PrimeValue := ⟨277231, pr277231⟩
private theorem pr277279 : PrimeCertificate 277279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv1249]) (by decide +kernel)
def pv277279 : PrimeValue := ⟨277279, pr277279⟩
private theorem pr277297 : PrimeCertificate 277297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv109]) (by decide +kernel)
def pv277297 : PrimeValue := ⟨277297, pr277297⟩
private theorem pr277331 : PrimeCertificate 277331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv27733]) (by decide +kernel)
def pv277331 : PrimeValue := ⟨277331, pr277331⟩
private theorem pr277373 : PrimeCertificate 277373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv4079]) (by decide +kernel)
def pv277373 : PrimeValue := ⟨277373, pr277373⟩
private theorem pr277421 : PrimeCertificate 277421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv97]) (by decide +kernel)
def pv277421 : PrimeValue := ⟨277421, pr277421⟩
private theorem pr277427 : PrimeCertificate 277427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv37,pv163]) (by decide +kernel)
def pv277427 : PrimeValue := ⟨277427, pr277427⟩
private theorem pr277493 : PrimeCertificate 277493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv401]) (by decide +kernel)
def pv277493 : PrimeValue := ⟨277493, pr277493⟩
private theorem pr277567 : PrimeCertificate 277567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv46261]) (by decide +kernel)
def pv277567 : PrimeValue := ⟨277567, pr277567⟩
private theorem pr277579 : PrimeCertificate 277579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2203]) (by decide +kernel)
def pv277579 : PrimeValue := ⟨277579, pr277579⟩
private theorem pr277597 : PrimeCertificate 277597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv701]) (by decide +kernel)
def pv277597 : PrimeValue := ⟨277597, pr277597⟩
private theorem pr277603 : PrimeCertificate 277603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv3559]) (by decide +kernel)
def pv277603 : PrimeValue := ⟨277603, pr277603⟩
private theorem pr277637 : PrimeCertificate 277637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2239]) (by decide +kernel)
def pv277637 : PrimeValue := ⟨277637, pr277637⟩
private theorem pr277643 : PrimeCertificate 277643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv138821]) (by decide +kernel)
def pv277643 : PrimeValue := ⟨277643, pr277643⟩
private theorem pr277657 : PrimeCertificate 277657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv503]) (by decide +kernel)
def pv277657 : PrimeValue := ⟨277657, pr277657⟩
private theorem pr277663 : PrimeCertificate 277663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv601]) (by decide +kernel)
def pv277663 : PrimeValue := ⟨277663, pr277663⟩
private theorem pr277687 : PrimeCertificate 277687 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv15427]) (by decide +kernel)
def pv277687 : PrimeValue := ⟨277687, pr277687⟩
private theorem pr277691 : PrimeCertificate 277691 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv3967]) (by decide +kernel)
def pv277691 : PrimeValue := ⟨277691, pr277691⟩
private theorem pr277703 : PrimeCertificate 277703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv6037]) (by decide +kernel)
def pv277703 : PrimeValue := ⟨277703, pr277703⟩
private theorem pr277741 : PrimeCertificate 277741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1543]) (by decide +kernel)
def pv277741 : PrimeValue := ⟨277741, pr277741⟩
private theorem pr277751 : PrimeCertificate 277751 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv101]) (by decide +kernel)
def pv277751 : PrimeValue := ⟨277751, pr277751⟩
private theorem pr277789 : PrimeCertificate 277789 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv3307]) (by decide +kernel)
def pv277789 : PrimeValue := ⟨277789, pr277789⟩
private theorem pr277813 : PrimeCertificate 277813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7717]) (by decide +kernel)
def pv277813 : PrimeValue := ⟨277813, pr277813⟩
private theorem pr277883 : PrimeCertificate 277883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv743]) (by decide +kernel)
def pv277883 : PrimeValue := ⟨277883, pr277883⟩
private theorem pr277889 : PrimeCertificate 277889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv167]) (by decide +kernel)
def pv277889 : PrimeValue := ⟨277889, pr277889⟩
private theorem pr277891 : PrimeCertificate 277891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv59,pv157]) (by decide +kernel)
def pv277891 : PrimeValue := ⟨277891, pr277891⟩
private theorem pr277903 : PrimeCertificate 277903 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv15439]) (by decide +kernel)
def pv277903 : PrimeValue := ⟨277903, pr277903⟩
private theorem pr277961 : PrimeCertificate 277961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6949]) (by decide +kernel)
def pv277961 : PrimeValue := ⟨277961, pr277961⟩
private theorem pr277993 : PrimeCertificate 277993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv277993 : PrimeValue := ⟨277993, pr277993⟩
private theorem pr277999 : PrimeCertificate 277999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv6619]) (by decide +kernel)
def pv277999 : PrimeValue := ⟨277999, pr277999⟩
private theorem pr278051 : PrimeCertificate 278051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv67,pv83]) (by decide +kernel)
def pv278051 : PrimeValue := ⟨278051, pr278051⟩
private theorem pr278063 : PrimeCertificate 278063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv3391]) (by decide +kernel)
def pv278063 : PrimeValue := ⟨278063, pr278063⟩
private theorem pr278071 : PrimeCertificate 278071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv23,pv31]) (by decide +kernel)
def pv278071 : PrimeValue := ⟨278071, pr278071⟩
private theorem pr278111 : PrimeCertificate 278111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv29,pv137]) (by decide +kernel)
def pv278111 : PrimeValue := ⟨278111, pr278111⟩
private theorem pr278119 : PrimeCertificate 278119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv15451]) (by decide +kernel)
def pv278119 : PrimeValue := ⟨278119, pr278119⟩
private theorem pr278123 : PrimeCertificate 278123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv563]) (by decide +kernel)
def pv278123 : PrimeValue := ⟨278123, pr278123⟩
private theorem pr278147 : PrimeCertificate 278147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv47,pv269]) (by decide +kernel)
def pv278147 : PrimeValue := ⟨278147, pr278147⟩
private theorem pr278149 : PrimeCertificate 278149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1783]) (by decide +kernel)
def pv278149 : PrimeValue := ⟨278149, pr278149⟩
private theorem pr278191 : PrimeCertificate 278191 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv281]) (by decide +kernel)
def pv278191 : PrimeValue := ⟨278191, pr278191⟩
private theorem pr278207 : PrimeCertificate 278207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv113,pv1231]) (by decide +kernel)
def pv278207 : PrimeValue := ⟨278207, pr278207⟩
private theorem pr278219 : PrimeCertificate 278219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139109]) (by decide +kernel)
def pv278219 : PrimeValue := ⟨278219, pr278219⟩
private theorem pr278233 : PrimeCertificate 278233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11593]) (by decide +kernel)
def pv278233 : PrimeValue := ⟨278233, pr278233⟩
private theorem pr278261 : PrimeCertificate 278261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13913]) (by decide +kernel)
def pv278261 : PrimeValue := ⟨278261, pr278261⟩
private theorem pr278269 : PrimeCertificate 278269 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23189]) (by decide +kernel)
def pv278269 : PrimeValue := ⟨278269, pr278269⟩
private theorem pr278279 : PrimeCertificate 278279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv13,pv139]) (by decide +kernel)
def pv278279 : PrimeValue := ⟨278279, pr278279⟩
private theorem pr278321 : PrimeCertificate 278321 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv7,pv71]) (by decide +kernel)
def pv278321 : PrimeValue := ⟨278321, pr278321⟩
private theorem pr278329 : PrimeCertificate 278329 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11597]) (by decide +kernel)
def pv278329 : PrimeValue := ⟨278329, pr278329⟩
private theorem pr278363 : PrimeCertificate 278363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv59,pv337]) (by decide +kernel)
def pv278363 : PrimeValue := ⟨278363, pr278363⟩
private theorem pr278393 : PrimeCertificate 278393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv23,pv89]) (by decide +kernel)
def pv278393 : PrimeValue := ⟨278393, pr278393⟩
private theorem pr278437 : PrimeCertificate 278437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23203]) (by decide +kernel)
def pv278437 : PrimeValue := ⟨278437, pr278437⟩
private theorem pr278479 : PrimeCertificate 278479 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv191]) (by decide +kernel)
def pv278479 : PrimeValue := ⟨278479, pr278479⟩
private theorem pr278489 : PrimeCertificate 278489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv4973]) (by decide +kernel)
def pv278489 : PrimeValue := ⟨278489, pr278489⟩
private theorem pr278491 : PrimeCertificate 278491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv9283]) (by decide +kernel)
def pv278491 : PrimeValue := ⟨278491, pr278491⟩
private theorem pr278497 : PrimeCertificate 278497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv967]) (by decide +kernel)
def pv278497 : PrimeValue := ⟨278497, pr278497⟩
private theorem pr278503 : PrimeCertificate 278503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv349]) (by decide +kernel)
def pv278503 : PrimeValue := ⟨278503, pr278503⟩
private theorem pr278543 : PrimeCertificate 278543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv1151]) (by decide +kernel)
def pv278543 : PrimeValue := ⟨278543, pr278543⟩
private theorem pr278549 : PrimeCertificate 278549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv839]) (by decide +kernel)
def pv278549 : PrimeValue := ⟨278549, pr278549⟩
private theorem pr278557 : PrimeCertificate 278557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv139,pv167]) (by decide +kernel)
def pv278557 : PrimeValue := ⟨278557, pr278557⟩
private theorem pr278561 : PrimeCertificate 278561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1741]) (by decide +kernel)
def pv278561 : PrimeValue := ⟨278561, pr278561⟩
private theorem pr278563 : PrimeCertificate 278563 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv2731]) (by decide +kernel)
def pv278563 : PrimeValue := ⟨278563, pr278563⟩
private theorem pr278581 : PrimeCertificate 278581 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv4643]) (by decide +kernel)
def pv278581 : PrimeValue := ⟨278581, pr278581⟩
private theorem pr278609 : PrimeCertificate 278609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1583]) (by decide +kernel)
def pv278609 : PrimeValue := ⟨278609, pr278609⟩
private theorem pr278623 : PrimeCertificate 278623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv673]) (by decide +kernel)
def pv278623 : PrimeValue := ⟨278623, pr278623⟩
private theorem pr278639 : PrimeCertificate 278639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv127,pv1097]) (by decide +kernel)
def pv278639 : PrimeValue := ⟨278639, pr278639⟩
private theorem pr278651 : PrimeCertificate 278651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5573]) (by decide +kernel)
def pv278651 : PrimeValue := ⟨278651, pr278651⟩
private theorem pr278687 : PrimeCertificate 278687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv139343]) (by decide +kernel)
def pv278687 : PrimeValue := ⟨278687, pr278687⟩
private theorem pr278741 : PrimeCertificate 278741 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv11,pv181]) (by decide +kernel)
def pv278741 : PrimeValue := ⟨278741, pr278741⟩
private theorem pr278743 : PrimeCertificate 278743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv46457]) (by decide +kernel)
def pv278743 : PrimeValue := ⟨278743, pr278743⟩
private theorem pr278753 : PrimeCertificate 278753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv281]) (by decide +kernel)
def pv278753 : PrimeValue := ⟨278753, pr278753⟩
private theorem pr278767 : PrimeCertificate 278767 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv911]) (by decide +kernel)
def pv278767 : PrimeValue := ⟨278767, pr278767⟩
private theorem pr278801 : PrimeCertificate 278801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv41]) (by decide +kernel)
def pv278801 : PrimeValue := ⟨278801, pr278801⟩
private theorem pr278807 : PrimeCertificate 278807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv19,pv23,pv29]) (by decide +kernel)
def pv278807 : PrimeValue := ⟨278807, pr278807⟩
private theorem pr278809 : PrimeCertificate 278809 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11617]) (by decide +kernel)
def pv278809 : PrimeValue := ⟨278809, pr278809⟩
private theorem pr278813 : PrimeCertificate 278813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv1621]) (by decide +kernel)
def pv278813 : PrimeValue := ⟨278813, pr278813⟩
private theorem pr278819 : PrimeCertificate 278819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139409]) (by decide +kernel)
def pv278819 : PrimeValue := ⟨278819, pr278819⟩
private theorem pr278827 : PrimeCertificate 278827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv46471]) (by decide +kernel)
def pv278827 : PrimeValue := ⟨278827, pr278827⟩
private theorem pr278879 : PrimeCertificate 278879 :=
  certifyPrime (q := pv17) (ls := [pv2,pv139439]) (by decide +kernel)
def pv278879 : PrimeValue := ⟨278879, pr278879⟩
private theorem pr278891 : PrimeCertificate 278891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv167]) (by decide +kernel)
def pv278891 : PrimeValue := ⟨278891, pr278891⟩
private theorem pr278947 : PrimeCertificate 278947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15497]) (by decide +kernel)
def pv278947 : PrimeValue := ⟨278947, pr278947⟩
private theorem pr278981 : PrimeCertificate 278981 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv29,pv37]) (by decide +kernel)
def pv278981 : PrimeValue := ⟨278981, pr278981⟩
private theorem pr279001 : PrimeCertificate 279001 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv279001 : PrimeValue := ⟨279001, pr279001⟩
private theorem pr279029 : PrimeCertificate 279029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv883]) (by decide +kernel)
def pv279029 : PrimeValue := ⟨279029, pr279029⟩
private theorem pr279109 : PrimeCertificate 279109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7753]) (by decide +kernel)
def pv279109 : PrimeValue := ⟨279109, pr279109⟩
private theorem pr279119 : PrimeCertificate 279119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv19937]) (by decide +kernel)
def pv279119 : PrimeValue := ⟨279119, pr279119⟩
private theorem pr279127 : PrimeCertificate 279127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1723]) (by decide +kernel)
def pv279127 : PrimeValue := ⟨279127, pr279127⟩
private theorem pr279131 : PrimeCertificate 279131 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv103,pv271]) (by decide +kernel)
def pv279131 : PrimeValue := ⟨279131, pr279131⟩
private theorem pr279143 : PrimeCertificate 279143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv139571]) (by decide +kernel)
def pv279143 : PrimeValue := ⟨279143, pr279143⟩
private theorem pr279173 : PrimeCertificate 279173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv983]) (by decide +kernel)
def pv279173 : PrimeValue := ⟨279173, pr279173⟩
private theorem pr279179 : PrimeCertificate 279179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139589]) (by decide +kernel)
def pv279179 : PrimeValue := ⟨279179, pr279179⟩
private theorem pr279187 : PrimeCertificate 279187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv31,pv79]) (by decide +kernel)
def pv279187 : PrimeValue := ⟨279187, pr279187⟩
private theorem pr279221 : PrimeCertificate 279221 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv607]) (by decide +kernel)
def pv279221 : PrimeValue := ⟨279221, pr279221⟩
private theorem pr279269 : PrimeCertificate 279269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv577]) (by decide +kernel)
def pv279269 : PrimeValue := ⟨279269, pr279269⟩
private theorem pr279311 : PrimeCertificate 279311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv31,pv53]) (by decide +kernel)
def pv279311 : PrimeValue := ⟨279311, pr279311⟩
private theorem pr279329 : PrimeCertificate 279329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv29,pv43]) (by decide +kernel)
def pv279329 : PrimeValue := ⟨279329, pr279329⟩
private theorem pr279337 : PrimeCertificate 279337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103,pv113]) (by decide +kernel)
def pv279337 : PrimeValue := ⟨279337, pr279337⟩
private theorem pr279397 : PrimeCertificate 279397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv199]) (by decide +kernel)
def pv279397 : PrimeValue := ⟨279397, pr279397⟩
private theorem pr279407 : PrimeCertificate 279407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv139703]) (by decide +kernel)
def pv279407 : PrimeValue := ⟨279407, pr279407⟩
private theorem pr279413 : PrimeCertificate 279413 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv17,pv587]) (by decide +kernel)
def pv279413 : PrimeValue := ⟨279413, pr279413⟩
private theorem pr279431 : PrimeCertificate 279431 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv27943]) (by decide +kernel)
def pv279431 : PrimeValue := ⟨279431, pr279431⟩
private theorem pr279481 : PrimeCertificate 279481 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv137]) (by decide +kernel)
def pv279481 : PrimeValue := ⟨279481, pr279481⟩
private theorem pr279511 : PrimeCertificate 279511 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv279511 : PrimeValue := ⟨279511, pr279511⟩
private theorem pr279541 : PrimeCertificate 279541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1553]) (by decide +kernel)
def pv279541 : PrimeValue := ⟨279541, pr279541⟩
private theorem pr279551 : PrimeCertificate 279551 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv5591]) (by decide +kernel)
def pv279551 : PrimeValue := ⟨279551, pr279551⟩
private theorem pr279557 : PrimeCertificate 279557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1487]) (by decide +kernel)
def pv279557 : PrimeValue := ⟨279557, pr279557⟩
private theorem pr279571 : PrimeCertificate 279571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv9319]) (by decide +kernel)
def pv279571 : PrimeValue := ⟨279571, pr279571⟩
private theorem pr279577 : PrimeCertificate 279577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv353]) (by decide +kernel)
def pv279577 : PrimeValue := ⟨279577, pr279577⟩
private theorem pr279583 : PrimeCertificate 279583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv2741]) (by decide +kernel)
def pv279583 : PrimeValue := ⟨279583, pr279583⟩
private theorem pr279613 : PrimeCertificate 279613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv863]) (by decide +kernel)
def pv279613 : PrimeValue := ⟨279613, pr279613⟩
private theorem pr279641 : PrimeCertificate 279641 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv6991]) (by decide +kernel)
def pv279641 : PrimeValue := ⟨279641, pr279641⟩
private theorem pr279659 : PrimeCertificate 279659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv2087]) (by decide +kernel)
def pv279659 : PrimeValue := ⟨279659, pr279659⟩
private theorem pr279679 : PrimeCertificate 279679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv6659]) (by decide +kernel)
def pv279679 : PrimeValue := ⟨279679, pr279679⟩
private theorem pr279709 : PrimeCertificate 279709 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv13,pv163]) (by decide +kernel)
def pv279709 : PrimeValue := ⟨279709, pr279709⟩
private theorem pr279751 : PrimeCertificate 279751 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv373]) (by decide +kernel)
def pv279751 : PrimeValue := ⟨279751, pr279751⟩
private theorem pr279761 : PrimeCertificate 279761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv269]) (by decide +kernel)
def pv279761 : PrimeValue := ⟨279761, pr279761⟩
private theorem pr279767 : PrimeCertificate 279767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv139883]) (by decide +kernel)
def pv279767 : PrimeValue := ⟨279767, pr279767⟩
private theorem pr279779 : PrimeCertificate 279779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv2371]) (by decide +kernel)
def pv279779 : PrimeValue := ⟨279779, pr279779⟩
private theorem pr279817 : PrimeCertificate 279817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv89,pv131]) (by decide +kernel)
def pv279817 : PrimeValue := ⟨279817, pr279817⟩
private theorem pr279823 : PrimeCertificate 279823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv149,pv313]) (by decide +kernel)
def pv279823 : PrimeValue := ⟨279823, pr279823⟩
private theorem pr279847 : PrimeCertificate 279847 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv2221]) (by decide +kernel)
def pv279847 : PrimeValue := ⟨279847, pr279847⟩
private theorem pr279857 : PrimeCertificate 279857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17491]) (by decide +kernel)
def pv279857 : PrimeValue := ⟨279857, pr279857⟩
private theorem pr279863 : PrimeCertificate 279863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv12721]) (by decide +kernel)
def pv279863 : PrimeValue := ⟨279863, pr279863⟩
private theorem pr279913 : PrimeCertificate 279913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv107,pv109]) (by decide +kernel)
def pv279913 : PrimeValue := ⟨279913, pr279913⟩
private theorem pr279941 : PrimeCertificate 279941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13997]) (by decide +kernel)
def pv279941 : PrimeValue := ⟨279941, pr279941⟩
private theorem pr279977 : PrimeCertificate 279977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79,pv443]) (by decide +kernel)
def pv279977 : PrimeValue := ⟨279977, pr279977⟩
private theorem pr279991 : PrimeCertificate 279991 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv17,pv61]) (by decide +kernel)
def pv279991 : PrimeValue := ⟨279991, pr279991⟩
private theorem pr280001 : PrimeCertificate 280001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv280001 : PrimeValue := ⟨280001, pr280001⟩
private theorem pr280013 : PrimeCertificate 280013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70003]) (by decide +kernel)
def pv280013 : PrimeValue := ⟨280013, pr280013⟩
private theorem pr280061 : PrimeCertificate 280061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv19,pv67]) (by decide +kernel)
def pv280061 : PrimeValue := ⟨280061, pr280061⟩
private theorem pr280069 : PrimeCertificate 280069 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23339]) (by decide +kernel)
def pv280069 : PrimeValue := ⟨280069, pr280069⟩
private theorem pr280097 : PrimeCertificate 280097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8753]) (by decide +kernel)
def pv280097 : PrimeValue := ⟨280097, pr280097⟩
private theorem pr280099 : PrimeCertificate 280099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv19]) (by decide +kernel)
def pv280099 : PrimeValue := ⟨280099, pr280099⟩
private theorem pr280103 : PrimeCertificate 280103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv3257]) (by decide +kernel)
def pv280103 : PrimeValue := ⟨280103, pr280103⟩
private theorem pr280121 : PrimeCertificate 280121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47,pv149]) (by decide +kernel)
def pv280121 : PrimeValue := ⟨280121, pr280121⟩
private theorem pr280129 : PrimeCertificate 280129 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1459]) (by decide +kernel)
def pv280129 : PrimeValue := ⟨280129, pr280129⟩
private theorem pr280223 : PrimeCertificate 280223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv140111]) (by decide +kernel)
def pv280223 : PrimeValue := ⟨280223, pr280223⟩
private theorem pr280229 : PrimeCertificate 280229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv317]) (by decide +kernel)
def pv280229 : PrimeValue := ⟨280229, pr280229⟩
private theorem pr280243 : PrimeCertificate 280243 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv15569]) (by decide +kernel)
def pv280243 : PrimeValue := ⟨280243, pr280243⟩
private theorem pr280277 : PrimeCertificate 280277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv1709]) (by decide +kernel)
def pv280277 : PrimeValue := ⟨280277, pr280277⟩
private theorem pr280297 : PrimeCertificate 280297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv229]) (by decide +kernel)
def pv280297 : PrimeValue := ⟨280297, pr280297⟩
private theorem pr280321 : PrimeCertificate 280321 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv280321 : PrimeValue := ⟨280321, pr280321⟩
private theorem pr280337 : PrimeCertificate 280337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2503]) (by decide +kernel)
def pv280337 : PrimeValue := ⟨280337, pr280337⟩
private theorem pr280339 : PrimeCertificate 280339 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv46723]) (by decide +kernel)
def pv280339 : PrimeValue := ⟨280339, pr280339⟩
private theorem pr280351 : PrimeCertificate 280351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv89]) (by decide +kernel)
def pv280351 : PrimeValue := ⟨280351, pr280351⟩
private theorem pr280411 : PrimeCertificate 280411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv719]) (by decide +kernel)
def pv280411 : PrimeValue := ⟨280411, pr280411⟩
private theorem pr280507 : PrimeCertificate 280507 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv46751]) (by decide +kernel)
def pv280507 : PrimeValue := ⟨280507, pr280507⟩
private theorem pr280513 : PrimeCertificate 280513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv487]) (by decide +kernel)
def pv280513 : PrimeValue := ⟨280513, pr280513⟩
private theorem pr280537 : PrimeCertificate 280537 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11689]) (by decide +kernel)
def pv280537 : PrimeValue := ⟨280537, pr280537⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
