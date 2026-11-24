/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table203
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table203.pv651863
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table057
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table089

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr651863 : Nat.Prime 651863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv11239]) (by decide +kernel)
def pv651863 : PrimeValue := ⟨651863, pr651863⟩
private theorem pr652033 : Nat.Prime 652033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv283]) (by decide +kernel)
def pv652033 : PrimeValue := ⟨652033, pr652033⟩
private theorem pr652081 : Nat.Prime 652081 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv11,pv13,pv19]) (by decide +kernel)
def pv652081 : PrimeValue := ⟨652081, pr652081⟩
private theorem pr652153 : Nat.Prime 652153 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv29,pv937]) (by decide +kernel)
def pv652153 : PrimeValue := ⟨652153, pr652153⟩
private theorem pr652291 : Nat.Prime 652291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv1279]) (by decide +kernel)
def pv652291 : PrimeValue := ⟨652291, pr652291⟩
private theorem pr652357 : Nat.Prime 652357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18121]) (by decide +kernel)
def pv652357 : PrimeValue := ⟨652357, pr652357⟩
private theorem pr652411 : Nat.Prime 652411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv659]) (by decide +kernel)
def pv652411 : PrimeValue := ⟨652411, pr652411⟩
private theorem pr652417 : Nat.Prime 652417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1699]) (by decide +kernel)
def pv652417 : PrimeValue := ⟨652417, pr652417⟩
private theorem pr652543 : Nat.Prime 652543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv9887]) (by decide +kernel)
def pv652543 : PrimeValue := ⟨652543, pr652543⟩
private theorem pr652567 : Nat.Prime 652567 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv108761]) (by decide +kernel)
def pv652567 : PrimeValue := ⟨652567, pr652567⟩
private theorem pr652651 : Nat.Prime 652651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv229]) (by decide +kernel)
def pv652651 : PrimeValue := ⟨652651, pr652651⟩
private theorem pr652853 : Nat.Prime 652853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv227,pv719]) (by decide +kernel)
def pv652853 : PrimeValue := ⟨652853, pr652853⟩
private theorem pr652913 : Nat.Prime 652913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv43,pv73]) (by decide +kernel)
def pv652913 : PrimeValue := ⟨652913, pr652913⟩
private theorem pr652921 : Nat.Prime 652921 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv5441]) (by decide +kernel)
def pv652921 : PrimeValue := ⟨652921, pr652921⟩
private theorem pr652931 : Nat.Prime 652931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv65293]) (by decide +kernel)
def pv652931 : PrimeValue := ⟨652931, pr652931⟩
private theorem pr652937 : Nat.Prime 652937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv4801]) (by decide +kernel)
def pv652937 : PrimeValue := ⟨652937, pr652937⟩
private theorem pr653153 : Nat.Prime 653153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv20411]) (by decide +kernel)
def pv653153 : PrimeValue := ⟨653153, pr653153⟩
private theorem pr653203 : Nat.Prime 653203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv3299]) (by decide +kernel)
def pv653203 : PrimeValue := ⟨653203, pr653203⟩
private theorem pr653207 : Nat.Prime 653207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv6949]) (by decide +kernel)
def pv653207 : PrimeValue := ⟨653207, pr653207⟩
private theorem pr653267 : Nat.Prime 653267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv326633]) (by decide +kernel)
def pv653267 : PrimeValue := ⟨653267, pr653267⟩
private theorem pr653281 : Nat.Prime 653281 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1361]) (by decide +kernel)
def pv653281 : PrimeValue := ⟨653281, pr653281⟩
private theorem pr653363 : Nat.Prime 653363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv326681]) (by decide +kernel)
def pv653363 : PrimeValue := ⟨653363, pr653363⟩
private theorem pr653491 : Nat.Prime 653491 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv53,pv137]) (by decide +kernel)
def pv653491 : PrimeValue := ⟨653491, pr653491⟩
private theorem pr653687 : Nat.Prime 653687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv43,pv691]) (by decide +kernel)
def pv653687 : PrimeValue := ⟨653687, pr653687⟩
private theorem pr653711 : Nat.Prime 653711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv65371]) (by decide +kernel)
def pv653711 : PrimeValue := ⟨653711, pr653711⟩
private theorem pr653743 : Nat.Prime 653743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv36319]) (by decide +kernel)
def pv653743 : PrimeValue := ⟨653743, pr653743⟩
private theorem pr653881 : Nat.Prime 653881 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv5449]) (by decide +kernel)
def pv653881 : PrimeValue := ⟨653881, pr653881⟩
private theorem pr653977 : Nat.Prime 653977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv293]) (by decide +kernel)
def pv653977 : PrimeValue := ⟨653977, pr653977⟩
private theorem pr654023 : Nat.Prime 654023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv327011]) (by decide +kernel)
def pv654023 : PrimeValue := ⟨654023, pr654023⟩
private theorem pr654301 : Nat.Prime 654301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv727]) (by decide +kernel)
def pv654301 : PrimeValue := ⟨654301, pr654301⟩
private theorem pr654307 : Nat.Prime 654307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv167,pv653]) (by decide +kernel)
def pv654307 : PrimeValue := ⟨654307, pr654307⟩
private theorem pr654371 : Nat.Prime 654371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv65437]) (by decide +kernel)
def pv654371 : PrimeValue := ⟨654371, pr654371⟩
private theorem pr654413 : Nat.Prime 654413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv107,pv139]) (by decide +kernel)
def pv654413 : PrimeValue := ⟨654413, pr654413⟩
private theorem pr654587 : Nat.Prime 654587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv137,pv2389]) (by decide +kernel)
def pv654587 : PrimeValue := ⟨654587, pr654587⟩
private theorem pr654593 : Nat.Prime 654593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2557]) (by decide +kernel)
def pv654593 : PrimeValue := ⟨654593, pr654593⟩
private theorem pr654611 : Nat.Prime 654611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv541]) (by decide +kernel)
def pv654611 : PrimeValue := ⟨654611, pr654611⟩
private theorem pr654623 : Nat.Prime 654623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv327311]) (by decide +kernel)
def pv654623 : PrimeValue := ⟨654623, pr654623⟩
private theorem pr654671 : Nat.Prime 654671 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv17,pv3851]) (by decide +kernel)
def pv654671 : PrimeValue := ⟨654671, pr654671⟩
private theorem pr654917 : Nat.Prime 654917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163729]) (by decide +kernel)
def pv654917 : PrimeValue := ⟨654917, pr654917⟩
private theorem pr655121 : Nat.Prime 655121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv431]) (by decide +kernel)
def pv655121 : PrimeValue := ⟨655121, pr655121⟩
private theorem pr655261 : Nat.Prime 655261 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv67,pv163]) (by decide +kernel)
def pv655261 : PrimeValue := ⟨655261, pr655261⟩
private theorem pr655273 : Nat.Prime 655273 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv479]) (by decide +kernel)
def pv655273 : PrimeValue := ⟨655273, pr655273⟩
private theorem pr655373 : Nat.Prime 655373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv2777]) (by decide +kernel)
def pv655373 : PrimeValue := ⟨655373, pr655373⟩
private theorem pr655471 : Nat.Prime 655471 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv7283]) (by decide +kernel)
def pv655471 : PrimeValue := ⟨655471, pr655471⟩
private theorem pr655561 : Nat.Prime 655561 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv607]) (by decide +kernel)
def pv655561 : PrimeValue := ⟨655561, pr655561⟩
private theorem pr655597 : Nat.Prime 655597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18211]) (by decide +kernel)
def pv655597 : PrimeValue := ⟨655597, pr655597⟩
private theorem pr655637 : Nat.Prime 655637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163909]) (by decide +kernel)
def pv655637 : PrimeValue := ⟨655637, pr655637⟩
private theorem pr655651 : Nat.Prime 655651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv31,pv47]) (by decide +kernel)
def pv655651 : PrimeValue := ⟨655651, pr655651⟩
private theorem pr655723 : Nat.Prime 655723 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv12143]) (by decide +kernel)
def pv655723 : PrimeValue := ⟨655723, pr655723⟩
private theorem pr655727 : Nat.Prime 655727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv59,pv5557]) (by decide +kernel)
def pv655727 : PrimeValue := ⟨655727, pr655727⟩
private theorem pr655913 : Nat.Prime 655913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv163,pv503]) (by decide +kernel)
def pv655913 : PrimeValue := ⟨655913, pr655913⟩
private theorem pr655927 : Nat.Prime 655927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv109321]) (by decide +kernel)
def pv655927 : PrimeValue := ⟨655927, pr655927⟩
private theorem pr656023 : Nat.Prime 656023 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv31,pv3527]) (by decide +kernel)
def pv656023 : PrimeValue := ⟨656023, pr656023⟩
private theorem pr656147 : Nat.Prime 656147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv31,pv557]) (by decide +kernel)
def pv656147 : PrimeValue := ⟨656147, pr656147⟩
private theorem pr656297 : Nat.Prime 656297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv82037]) (by decide +kernel)
def pv656297 : PrimeValue := ⟨656297, pr656297⟩
private theorem pr656303 : Nat.Prime 656303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv97,pv199]) (by decide +kernel)
def pv656303 : PrimeValue := ⟨656303, pr656303⟩
private theorem pr656471 : Nat.Prime 656471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv65647]) (by decide +kernel)
def pv656471 : PrimeValue := ⟨656471, pr656471⟩
private theorem pr656561 : Nat.Prime 656561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv283]) (by decide +kernel)
def pv656561 : PrimeValue := ⟨656561, pr656561⟩
private theorem pr656603 : Nat.Prime 656603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv37,pv467]) (by decide +kernel)
def pv656603 : PrimeValue := ⟨656603, pr656603⟩
private theorem pr656651 : Nat.Prime 656651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv571]) (by decide +kernel)
def pv656651 : PrimeValue := ⟨656651, pr656651⟩
private theorem pr656683 : Nat.Prime 656683 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv8419]) (by decide +kernel)
def pv656683 : PrimeValue := ⟨656683, pr656683⟩
private theorem pr656701 : Nat.Prime 656701 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv199]) (by decide +kernel)
def pv656701 : PrimeValue := ⟨656701, pr656701⟩
private theorem pr656791 : Nat.Prime 656791 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv21893]) (by decide +kernel)
def pv656791 : PrimeValue := ⟨656791, pr656791⟩
private theorem pr657121 : Nat.Prime 657121 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv657121 : PrimeValue := ⟨657121, pr657121⟩
private theorem pr657233 : Nat.Prime 657233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41077]) (by decide +kernel)
def pv657233 : PrimeValue := ⟨657233, pr657233⟩
private theorem pr657257 : Nat.Prime 657257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv2833]) (by decide +kernel)
def pv657257 : PrimeValue := ⟨657257, pr657257⟩
private theorem pr657323 : Nat.Prime 657323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19333]) (by decide +kernel)
def pv657323 : PrimeValue := ⟨657323, pr657323⟩
private theorem pr657473 : Nat.Prime 657473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10273]) (by decide +kernel)
def pv657473 : PrimeValue := ⟨657473, pr657473⟩
private theorem pr657617 : Nat.Prime 657617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv1787]) (by decide +kernel)
def pv657617 : PrimeValue := ⟨657617, pr657617⟩
private theorem pr657653 : Nat.Prime 657653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv164413]) (by decide +kernel)
def pv657653 : PrimeValue := ⟨657653, pr657653⟩
private theorem pr657703 : Nat.Prime 657703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv61,pv599]) (by decide +kernel)
def pv657703 : PrimeValue := ⟨657703, pr657703⟩
private theorem pr658111 : Nat.Prime 658111 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv21937]) (by decide +kernel)
def pv658111 : PrimeValue := ⟨658111, pr658111⟩
private theorem pr658303 : Nat.Prime 658303 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv109717]) (by decide +kernel)
def pv658303 : PrimeValue := ⟨658303, pr658303⟩
private theorem pr658367 : Nat.Prime 658367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv6211]) (by decide +kernel)
def pv658367 : PrimeValue := ⟨658367, pr658367⟩
private theorem pr658433 : Nat.Prime 658433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv643]) (by decide +kernel)
def pv658433 : PrimeValue := ⟨658433, pr658433⟩
private theorem pr658703 : Nat.Prime 658703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv79,pv379]) (by decide +kernel)
def pv658703 : PrimeValue := ⟨658703, pr658703⟩
private theorem pr658753 : Nat.Prime 658753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv73]) (by decide +kernel)
def pv658753 : PrimeValue := ⟨658753, pr658753⟩
private theorem pr658913 : Nat.Prime 658913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv349]) (by decide +kernel)
def pv658913 : PrimeValue := ⟨658913, pr658913⟩
private theorem pr658963 : Nat.Prime 658963 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12203]) (by decide +kernel)
def pv658963 : PrimeValue := ⟨658963, pr658963⟩
private theorem pr659047 : Nat.Prime 659047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv109841]) (by decide +kernel)
def pv659047 : PrimeValue := ⟨659047, pr659047⟩
private theorem pr659171 : Nat.Prime 659171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv2273]) (by decide +kernel)
def pv659171 : PrimeValue := ⟨659171, pr659171⟩
private theorem pr659333 : Nat.Prime 659333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv191,pv863]) (by decide +kernel)
def pv659333 : PrimeValue := ⟨659333, pr659333⟩
private theorem pr659353 : Nat.Prime 659353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv83,pv331]) (by decide +kernel)
def pv659353 : PrimeValue := ⟨659353, pr659353⟩
private theorem pr659467 : Nat.Prime 659467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv36637]) (by decide +kernel)
def pv659467 : PrimeValue := ⟨659467, pr659467⟩
private theorem pr659497 : Nat.Prime 659497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv27479]) (by decide +kernel)
def pv659497 : PrimeValue := ⟨659497, pr659497⟩
private theorem pr659501 : Nat.Prime 659501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1319]) (by decide +kernel)
def pv659501 : PrimeValue := ⟨659501, pr659501⟩
private theorem pr659881 : Nat.Prime 659881 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv47]) (by decide +kernel)
def pv659881 : PrimeValue := ⟨659881, pr659881⟩
private theorem pr659951 : Nat.Prime 659951 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv67,pv197]) (by decide +kernel)
def pv659951 : PrimeValue := ⟨659951, pr659951⟩
private theorem pr659983 : Nat.Prime 659983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv3793]) (by decide +kernel)
def pv659983 : PrimeValue := ⟨659983, pr659983⟩
private theorem pr660001 : Nat.Prime 660001 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv660001 : PrimeValue := ⟨660001, pr660001⟩
private theorem pr660047 : Nat.Prime 660047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv401,pv823]) (by decide +kernel)
def pv660047 : PrimeValue := ⟨660047, pr660047⟩
private theorem pr660061 : Nat.Prime 660061 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv19,pv193]) (by decide +kernel)
def pv660061 : PrimeValue := ⟨660061, pr660061⟩
private theorem pr660067 : Nat.Prime 660067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv73,pv137]) (by decide +kernel)
def pv660067 : PrimeValue := ⟨660067, pr660067⟩
private theorem pr660071 : Nat.Prime 660071 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv149,pv443]) (by decide +kernel)
def pv660071 : PrimeValue := ⟨660071, pr660071⟩
private theorem pr660547 : Nat.Prime 660547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv36697]) (by decide +kernel)
def pv660547 : PrimeValue := ⟨660547, pr660547⟩
private theorem pr660593 : Nat.Prime 660593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv41,pv53]) (by decide +kernel)
def pv660593 : PrimeValue := ⟨660593, pr660593⟩
private theorem pr660601 : Nat.Prime 660601 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv367]) (by decide +kernel)
def pv660601 : PrimeValue := ⟨660601, pr660601⟩
private theorem pr660607 : Nat.Prime 660607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv4787]) (by decide +kernel)
def pv660607 : PrimeValue := ⟨660607, pr660607⟩
private theorem pr660811 : Nat.Prime 660811 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv22027]) (by decide +kernel)
def pv660811 : PrimeValue := ⟨660811, pr660811⟩
private theorem pr660817 : Nat.Prime 660817 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv353]) (by decide +kernel)
def pv660817 : PrimeValue := ⟨660817, pr660817⟩
private theorem pr660893 : Nat.Prime 660893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv9719]) (by decide +kernel)
def pv660893 : PrimeValue := ⟨660893, pr660893⟩
private theorem pr660973 : Nat.Prime 660973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv19,pv223]) (by decide +kernel)
def pv660973 : PrimeValue := ⟨660973, pr660973⟩
private theorem pr661097 : Nat.Prime 661097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv4861]) (by decide +kernel)
def pv661097 : PrimeValue := ⟨661097, pr661097⟩
private theorem pr661121 : Nat.Prime 661121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1033]) (by decide +kernel)
def pv661121 : PrimeValue := ⟨661121, pr661121⟩
private theorem pr661187 : Nat.Prime 661187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv311,pv1063]) (by decide +kernel)
def pv661187 : PrimeValue := ⟨661187, pr661187⟩
private theorem pr661201 : Nat.Prime 661201 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv29]) (by decide +kernel)
def pv661201 : PrimeValue := ⟨661201, pr661201⟩
private theorem pr661327 : Nat.Prime 661327 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv110221]) (by decide +kernel)
def pv661327 : PrimeValue := ⟨661327, pr661327⟩
private theorem pr661477 : Nat.Prime 661477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv199,pv277]) (by decide +kernel)
def pv661477 : PrimeValue := ⟨661477, pr661477⟩
private theorem pr661541 : Nat.Prime 661541 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv31,pv97]) (by decide +kernel)
def pv661541 : PrimeValue := ⟨661541, pr661541⟩
private theorem pr661673 : Nat.Prime 661673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv73,pv103]) (by decide +kernel)
def pv661673 : PrimeValue := ⟨661673, pr661673⟩
private theorem pr661873 : Nat.Prime 661873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13789]) (by decide +kernel)
def pv661873 : PrimeValue := ⟨661873, pr661873⟩
private theorem pr661877 : Nat.Prime 661877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv165469]) (by decide +kernel)
def pv661877 : PrimeValue := ⟨661877, pr661877⟩
private theorem pr661883 : Nat.Prime 661883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv25457]) (by decide +kernel)
def pv661883 : PrimeValue := ⟨661883, pr661883⟩
private theorem pr661931 : Nat.Prime 661931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv1789]) (by decide +kernel)
def pv661931 : PrimeValue := ⟨661931, pr661931⟩
private theorem pr662083 : Nat.Prime 662083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv6491]) (by decide +kernel)
def pv662083 : PrimeValue := ⟨662083, pr662083⟩
private theorem pr662107 : Nat.Prime 662107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv163,pv677]) (by decide +kernel)
def pv662107 : PrimeValue := ⟨662107, pr662107⟩
private theorem pr662177 : Nat.Prime 662177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv20693]) (by decide +kernel)
def pv662177 : PrimeValue := ⟨662177, pr662177⟩
private theorem pr662357 : Nat.Prime 662357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv165589]) (by decide +kernel)
def pv662357 : PrimeValue := ⟨662357, pr662357⟩
private theorem pr662527 : Nat.Prime 662527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12269]) (by decide +kernel)
def pv662527 : PrimeValue := ⟨662527, pr662527⟩
private theorem pr662617 : Nat.Prime 662617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv9203]) (by decide +kernel)
def pv662617 : PrimeValue := ⟨662617, pr662617⟩
private theorem pr662681 : Nat.Prime 662681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv16567]) (by decide +kernel)
def pv662681 : PrimeValue := ⟨662681, pr662681⟩
private theorem pr662743 : Nat.Prime 662743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4091]) (by decide +kernel)
def pv662743 : PrimeValue := ⟨662743, pr662743⟩
private theorem pr662843 : Nat.Prime 662843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv10691]) (by decide +kernel)
def pv662843 : PrimeValue := ⟨662843, pr662843⟩
private theorem pr662867 : Nat.Prime 662867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv271,pv1223]) (by decide +kernel)
def pv662867 : PrimeValue := ⟨662867, pr662867⟩
private theorem pr662941 : Nat.Prime 662941 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv29,pv127]) (by decide +kernel)
def pv662941 : PrimeValue := ⟨662941, pr662941⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
