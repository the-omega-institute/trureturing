/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table065
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table065.pv196873
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table037
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table038

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr196873 : Nat.Prime 196873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv631]) (by decide +kernel)
def pv196873 : PrimeValue := ⟨196873, pr196873⟩
private theorem pr196879 : Nat.Prime 196879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv19,pv157]) (by decide +kernel)
def pv196879 : PrimeValue := ⟨196879, pr196879⟩
private theorem pr196901 : Nat.Prime 196901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv179]) (by decide +kernel)
def pv196901 : PrimeValue := ⟨196901, pr196901⟩
private theorem pr196907 : Nat.Prime 196907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv98453]) (by decide +kernel)
def pv196907 : PrimeValue := ⟨196907, pr196907⟩
private theorem pr196919 : Nat.Prime 196919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv98459]) (by decide +kernel)
def pv196919 : PrimeValue := ⟨196919, pr196919⟩
private theorem pr196927 : Nat.Prime 196927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv1427]) (by decide +kernel)
def pv196927 : PrimeValue := ⟨196927, pr196927⟩
private theorem pr196961 : Nat.Prime 196961 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv1231]) (by decide +kernel)
def pv196961 : PrimeValue := ⟨196961, pr196961⟩
private theorem pr196993 : Nat.Prime 196993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv196993 : PrimeValue := ⟨196993, pr196993⟩
private theorem pr197003 : Nat.Prime 197003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv7577]) (by decide +kernel)
def pv197003 : PrimeValue := ⟨197003, pr197003⟩
private theorem pr197009 : Nat.Prime 197009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1759]) (by decide +kernel)
def pv197009 : PrimeValue := ⟨197009, pr197009⟩
private theorem pr197023 : Nat.Prime 197023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv4691]) (by decide +kernel)
def pv197023 : PrimeValue := ⟨197023, pr197023⟩
private theorem pr197059 : Nat.Prime 197059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv32843]) (by decide +kernel)
def pv197059 : PrimeValue := ⟨197059, pr197059⟩
private theorem pr197077 : Nat.Prime 197077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1493]) (by decide +kernel)
def pv197077 : PrimeValue := ⟨197077, pr197077⟩
private theorem pr197089 : Nat.Prime 197089 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv2053]) (by decide +kernel)
def pv197089 : PrimeValue := ⟨197089, pr197089⟩
private theorem pr197101 : Nat.Prime 197101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv197101 : PrimeValue := ⟨197101, pr197101⟩
private theorem pr197117 : Nat.Prime 197117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv49279]) (by decide +kernel)
def pv197117 : PrimeValue := ⟨197117, pr197117⟩
private theorem pr197123 : Nat.Prime 197123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv98561]) (by decide +kernel)
def pv197123 : PrimeValue := ⟨197123, pr197123⟩
private theorem pr197137 : Nat.Prime 197137 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv197137 : PrimeValue := ⟨197137, pr197137⟩
private theorem pr197159 : Nat.Prime 197159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv7583]) (by decide +kernel)
def pv197159 : PrimeValue := ⟨197159, pr197159⟩
private theorem pr197161 : Nat.Prime 197161 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv31,pv53]) (by decide +kernel)
def pv197161 : PrimeValue := ⟨197161, pr197161⟩
private theorem pr197203 : Nat.Prime 197203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv1429]) (by decide +kernel)
def pv197203 : PrimeValue := ⟨197203, pr197203⟩
private theorem pr197207 : Nat.Prime 197207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv151,pv653]) (by decide +kernel)
def pv197207 : PrimeValue := ⟨197207, pr197207⟩
private theorem pr197221 : Nat.Prime 197221 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv19,pv173]) (by decide +kernel)
def pv197221 : PrimeValue := ⟨197221, pr197221⟩
private theorem pr197233 : Nat.Prime 197233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv587]) (by decide +kernel)
def pv197233 : PrimeValue := ⟨197233, pr197233⟩
private theorem pr197257 : Nat.Prime 197257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv8219]) (by decide +kernel)
def pv197257 : PrimeValue := ⟨197257, pr197257⟩
private theorem pr197261 : Nat.Prime 197261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv1409]) (by decide +kernel)
def pv197261 : PrimeValue := ⟨197261, pr197261⟩
private theorem pr197269 : Nat.Prime 197269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv967]) (by decide +kernel)
def pv197269 : PrimeValue := ⟨197269, pr197269⟩
private theorem pr197279 : Nat.Prime 197279 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv98639]) (by decide +kernel)
def pv197279 : PrimeValue := ⟨197279, pr197279⟩
private theorem pr197293 : Nat.Prime 197293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv401]) (by decide +kernel)
def pv197293 : PrimeValue := ⟨197293, pr197293⟩
private theorem pr197297 : Nat.Prime 197297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv19,pv59]) (by decide +kernel)
def pv197297 : PrimeValue := ⟨197297, pr197297⟩
private theorem pr197311 : Nat.Prime 197311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv6577]) (by decide +kernel)
def pv197311 : PrimeValue := ⟨197311, pr197311⟩
private theorem pr197339 : Nat.Prime 197339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv98669]) (by decide +kernel)
def pv197339 : PrimeValue := ⟨197339, pr197339⟩
private theorem pr197341 : Nat.Prime 197341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv13,pv23]) (by decide +kernel)
def pv197341 : PrimeValue := ⟨197341, pr197341⟩
private theorem pr197347 : Nat.Prime 197347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv1061]) (by decide +kernel)
def pv197347 : PrimeValue := ⟨197347, pr197347⟩
private theorem pr197359 : Nat.Prime 197359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv37,pv127]) (by decide +kernel)
def pv197359 : PrimeValue := ⟨197359, pr197359⟩
private theorem pr197369 : Nat.Prime 197369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv24671]) (by decide +kernel)
def pv197369 : PrimeValue := ⟨197369, pr197369⟩
private theorem pr197383 : Nat.Prime 197383 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv67,pv491]) (by decide +kernel)
def pv197383 : PrimeValue := ⟨197383, pr197383⟩
private theorem pr197389 : Nat.Prime 197389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5483]) (by decide +kernel)
def pv197389 : PrimeValue := ⟨197389, pr197389⟩
private theorem pr197423 : Nat.Prime 197423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv98711]) (by decide +kernel)
def pv197423 : PrimeValue := ⟨197423, pr197423⟩
private theorem pr197507 : Nat.Prime 197507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv37,pv157]) (by decide +kernel)
def pv197507 : PrimeValue := ⟨197507, pr197507⟩
private theorem pr197521 : Nat.Prime 197521 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv823]) (by decide +kernel)
def pv197521 : PrimeValue := ⟨197521, pr197521⟩
private theorem pr197539 : Nat.Prime 197539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv41,pv73]) (by decide +kernel)
def pv197539 : PrimeValue := ⟨197539, pr197539⟩
private theorem pr197551 : Nat.Prime 197551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv439]) (by decide +kernel)
def pv197551 : PrimeValue := ⟨197551, pr197551⟩
private theorem pr197567 : Nat.Prime 197567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv173,pv571]) (by decide +kernel)
def pv197567 : PrimeValue := ⟨197567, pr197567⟩
private theorem pr197569 : Nat.Prime 197569 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv197569 : PrimeValue := ⟨197569, pr197569⟩
private theorem pr197573 : Nat.Prime 197573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv49393]) (by decide +kernel)
def pv197573 : PrimeValue := ⟨197573, pr197573⟩
private theorem pr197599 : Nat.Prime 197599 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv32933]) (by decide +kernel)
def pv197599 : PrimeValue := ⟨197599, pr197599⟩
private theorem pr197609 : Nat.Prime 197609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv1453]) (by decide +kernel)
def pv197609 : PrimeValue := ⟨197609, pr197609⟩
private theorem pr197621 : Nat.Prime 197621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv241]) (by decide +kernel)
def pv197621 : PrimeValue := ⟨197621, pr197621⟩
private theorem pr197641 : Nat.Prime 197641 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv197641 : PrimeValue := ⟨197641, pr197641⟩
private theorem pr197647 : Nat.Prime 197647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv32941]) (by decide +kernel)
def pv197647 : PrimeValue := ⟨197647, pr197647⟩
private theorem pr197651 : Nat.Prime 197651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv67]) (by decide +kernel)
def pv197651 : PrimeValue := ⟨197651, pr197651⟩
private theorem pr197677 : Nat.Prime 197677 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv19]) (by decide +kernel)
def pv197677 : PrimeValue := ⟨197677, pr197677⟩
private theorem pr197683 : Nat.Prime 197683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv701]) (by decide +kernel)
def pv197683 : PrimeValue := ⟨197683, pr197683⟩
private theorem pr197713 : Nat.Prime 197713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1373]) (by decide +kernel)
def pv197713 : PrimeValue := ⟨197713, pr197713⟩
private theorem pr197741 : Nat.Prime 197741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9887]) (by decide +kernel)
def pv197741 : PrimeValue := ⟨197741, pr197741⟩
private theorem pr197753 : Nat.Prime 197753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv1301]) (by decide +kernel)
def pv197753 : PrimeValue := ⟨197753, pr197753⟩
private theorem pr197759 : Nat.Prime 197759 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv89,pv101]) (by decide +kernel)
def pv197759 : PrimeValue := ⟨197759, pr197759⟩
private theorem pr197773 : Nat.Prime 197773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16481]) (by decide +kernel)
def pv197773 : PrimeValue := ⟨197773, pr197773⟩
private theorem pr197779 : Nat.Prime 197779 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv277]) (by decide +kernel)
def pv197779 : PrimeValue := ⟨197779, pr197779⟩
private theorem pr197837 : Nat.Prime 197837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv49459]) (by decide +kernel)
def pv197837 : PrimeValue := ⟨197837, pr197837⟩
private theorem pr197887 : Nat.Prime 197887 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv43,pv59]) (by decide +kernel)
def pv197887 : PrimeValue := ⟨197887, pr197887⟩
private theorem pr197893 : Nat.Prime 197893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv239]) (by decide +kernel)
def pv197893 : PrimeValue := ⟨197893, pr197893⟩
private theorem pr197909 : Nat.Prime 197909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv49477]) (by decide +kernel)
def pv197909 : PrimeValue := ⟨197909, pr197909⟩
private theorem pr197921 : Nat.Prime 197921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1237]) (by decide +kernel)
def pv197921 : PrimeValue := ⟨197921, pr197921⟩
private theorem pr197947 : Nat.Prime 197947 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1571]) (by decide +kernel)
def pv197947 : PrimeValue := ⟨197947, pr197947⟩
private theorem pr197957 : Nat.Prime 197957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv409]) (by decide +kernel)
def pv197957 : PrimeValue := ⟨197957, pr197957⟩
private theorem pr197963 : Nat.Prime 197963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv98981]) (by decide +kernel)
def pv197963 : PrimeValue := ⟨197963, pr197963⟩
private theorem pr197969 : Nat.Prime 197969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12373]) (by decide +kernel)
def pv197969 : PrimeValue := ⟨197969, pr197969⟩
private theorem pr198017 : Nat.Prime 198017 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv13,pv17]) (by decide +kernel)
def pv198017 : PrimeValue := ⟨198017, pr198017⟩
private theorem pr198043 : Nat.Prime 198043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2539]) (by decide +kernel)
def pv198043 : PrimeValue := ⟨198043, pr198043⟩
private theorem pr198073 : Nat.Prime 198073 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv131]) (by decide +kernel)
def pv198073 : PrimeValue := ⟨198073, pr198073⟩
private theorem pr198091 : Nat.Prime 198091 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv31,pv71]) (by decide +kernel)
def pv198091 : PrimeValue := ⟨198091, pr198091⟩
private theorem pr198127 : Nat.Prime 198127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1223]) (by decide +kernel)
def pv198127 : PrimeValue := ⟨198127, pr198127⟩
private theorem pr198193 : Nat.Prime 198193 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv4129]) (by decide +kernel)
def pv198193 : PrimeValue := ⟨198193, pr198193⟩
private theorem pr198221 : Nat.Prime 198221 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv11,pv17,pv53]) (by decide +kernel)
def pv198221 : PrimeValue := ⟨198221, pr198221⟩
private theorem pr198223 : Nat.Prime 198223 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv33037]) (by decide +kernel)
def pv198223 : PrimeValue := ⟨198223, pr198223⟩
private theorem pr198257 : Nat.Prime 198257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12391]) (by decide +kernel)
def pv198257 : PrimeValue := ⟨198257, pr198257⟩
private theorem pr198281 : Nat.Prime 198281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4957]) (by decide +kernel)
def pv198281 : PrimeValue := ⟨198281, pr198281⟩
private theorem pr198301 : Nat.Prime 198301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv661]) (by decide +kernel)
def pv198301 : PrimeValue := ⟨198301, pr198301⟩
private theorem pr198313 : Nat.Prime 198313 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv8263]) (by decide +kernel)
def pv198313 : PrimeValue := ⟨198313, pr198313⟩
private theorem pr198323 : Nat.Prime 198323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19,pv307]) (by decide +kernel)
def pv198323 : PrimeValue := ⟨198323, pr198323⟩
private theorem pr198337 : Nat.Prime 198337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1033]) (by decide +kernel)
def pv198337 : PrimeValue := ⟨198337, pr198337⟩
private theorem pr198347 : Nat.Prime 198347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv99173]) (by decide +kernel)
def pv198347 : PrimeValue := ⟨198347, pr198347⟩
private theorem pr198349 : Nat.Prime 198349 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv16529]) (by decide +kernel)
def pv198349 : PrimeValue := ⟨198349, pr198349⟩
private theorem pr198377 : Nat.Prime 198377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv137,pv181]) (by decide +kernel)
def pv198377 : PrimeValue := ⟨198377, pr198377⟩
private theorem pr198391 : Nat.Prime 198391 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv389]) (by decide +kernel)
def pv198391 : PrimeValue := ⟨198391, pr198391⟩
private theorem pr198409 : Nat.Prime 198409 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv1181]) (by decide +kernel)
def pv198409 : PrimeValue := ⟨198409, pr198409⟩
private theorem pr198413 : Nat.Prime 198413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv49603]) (by decide +kernel)
def pv198413 : PrimeValue := ⟨198413, pr198413⟩
private theorem pr198427 : Nat.Prime 198427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv33071]) (by decide +kernel)
def pv198427 : PrimeValue := ⟨198427, pr198427⟩
private theorem pr198439 : Nat.Prime 198439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv33073]) (by decide +kernel)
def pv198439 : PrimeValue := ⟨198439, pr198439⟩
private theorem pr198463 : Nat.Prime 198463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv31,pv97]) (by decide +kernel)
def pv198463 : PrimeValue := ⟨198463, pr198463⟩
private theorem pr198469 : Nat.Prime 198469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv149]) (by decide +kernel)
def pv198469 : PrimeValue := ⟨198469, pr198469⟩
private theorem pr198479 : Nat.Prime 198479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv14177]) (by decide +kernel)
def pv198479 : PrimeValue := ⟨198479, pr198479⟩
private theorem pr198491 : Nat.Prime 198491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv863]) (by decide +kernel)
def pv198491 : PrimeValue := ⟨198491, pr198491⟩
private theorem pr198503 : Nat.Prime 198503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv99251]) (by decide +kernel)
def pv198503 : PrimeValue := ⟨198503, pr198503⟩
private theorem pr198533 : Nat.Prime 198533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv49633]) (by decide +kernel)
def pv198533 : PrimeValue := ⟨198533, pr198533⟩
private theorem pr198553 : Nat.Prime 198553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv8273]) (by decide +kernel)
def pv198553 : PrimeValue := ⟨198553, pr198553⟩
private theorem pr198571 : Nat.Prime 198571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv6619]) (by decide +kernel)
def pv198571 : PrimeValue := ⟨198571, pr198571⟩
private theorem pr198593 : Nat.Prime 198593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv107]) (by decide +kernel)
def pv198593 : PrimeValue := ⟨198593, pr198593⟩
private theorem pr198599 : Nat.Prime 198599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv109,pv911]) (by decide +kernel)
def pv198599 : PrimeValue := ⟨198599, pr198599⟩
private theorem pr198613 : Nat.Prime 198613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv613]) (by decide +kernel)
def pv198613 : PrimeValue := ⟨198613, pr198613⟩
private theorem pr198623 : Nat.Prime 198623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv2113]) (by decide +kernel)
def pv198623 : PrimeValue := ⟨198623, pr198623⟩
private theorem pr198637 : Nat.Prime 198637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16553]) (by decide +kernel)
def pv198637 : PrimeValue := ⟨198637, pr198637⟩
private theorem pr198641 : Nat.Prime 198641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv191]) (by decide +kernel)
def pv198641 : PrimeValue := ⟨198641, pr198641⟩
private theorem pr198647 : Nat.Prime 198647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv2027]) (by decide +kernel)
def pv198647 : PrimeValue := ⟨198647, pr198647⟩
private theorem pr198673 : Nat.Prime 198673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4139]) (by decide +kernel)
def pv198673 : PrimeValue := ⟨198673, pr198673⟩
private theorem pr198689 : Nat.Prime 198689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv887]) (by decide +kernel)
def pv198689 : PrimeValue := ⟨198689, pr198689⟩
private theorem pr198701 : Nat.Prime 198701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1987]) (by decide +kernel)
def pv198701 : PrimeValue := ⟨198701, pr198701⟩
private theorem pr198733 : Nat.Prime 198733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16561]) (by decide +kernel)
def pv198733 : PrimeValue := ⟨198733, pr198733⟩
private theorem pr198769 : Nat.Prime 198769 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv41,pv101]) (by decide +kernel)
def pv198769 : PrimeValue := ⟨198769, pr198769⟩
private theorem pr198817 : Nat.Prime 198817 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv109]) (by decide +kernel)
def pv198817 : PrimeValue := ⟨198817, pr198817⟩
private theorem pr198823 : Nat.Prime 198823 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv2549]) (by decide +kernel)
def pv198823 : PrimeValue := ⟨198823, pr198823⟩
private theorem pr198827 : Nat.Prime 198827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv1117]) (by decide +kernel)
def pv198827 : PrimeValue := ⟨198827, pr198827⟩
private theorem pr198829 : Nat.Prime 198829 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv263]) (by decide +kernel)
def pv198829 : PrimeValue := ⟨198829, pr198829⟩
private theorem pr198833 : Nat.Prime 198833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv43]) (by decide +kernel)
def pv198833 : PrimeValue := ⟨198833, pr198833⟩
private theorem pr198839 : Nat.Prime 198839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv37,pv2687]) (by decide +kernel)
def pv198839 : PrimeValue := ⟨198839, pr198839⟩
private theorem pr198841 : Nat.Prime 198841 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1657]) (by decide +kernel)
def pv198841 : PrimeValue := ⟨198841, pr198841⟩
private theorem pr198851 : Nat.Prime 198851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv97]) (by decide +kernel)
def pv198851 : PrimeValue := ⟨198851, pr198851⟩
private theorem pr198859 : Nat.Prime 198859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv131]) (by decide +kernel)
def pv198859 : PrimeValue := ⟨198859, pr198859⟩
private theorem pr198899 : Nat.Prime 198899 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv14207]) (by decide +kernel)
def pv198899 : PrimeValue := ⟨198899, pr198899⟩
private theorem pr198929 : Nat.Prime 198929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12433]) (by decide +kernel)
def pv198929 : PrimeValue := ⟨198929, pr198929⟩
private theorem pr198953 : Nat.Prime 198953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv1913]) (by decide +kernel)
def pv198953 : PrimeValue := ⟨198953, pr198953⟩
private theorem pr198967 : Nat.Prime 198967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv33161]) (by decide +kernel)
def pv198967 : PrimeValue := ⟨198967, pr198967⟩
private theorem pr198997 : Nat.Prime 198997 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv23,pv103]) (by decide +kernel)
def pv198997 : PrimeValue := ⟨198997, pr198997⟩
private theorem pr199021 : Nat.Prime 199021 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv31,pv107]) (by decide +kernel)
def pv199021 : PrimeValue := ⟨199021, pr199021⟩
private theorem pr199033 : Nat.Prime 199033 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv8293]) (by decide +kernel)
def pv199033 : PrimeValue := ⟨199033, pr199033⟩
private theorem pr199103 : Nat.Prime 199103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv99551]) (by decide +kernel)
def pv199103 : PrimeValue := ⟨199103, pr199103⟩
private theorem pr199109 : Nat.Prime 199109 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv547]) (by decide +kernel)
def pv199109 : PrimeValue := ⟨199109, pr199109⟩
private theorem pr199151 : Nat.Prime 199151 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv569]) (by decide +kernel)
def pv199151 : PrimeValue := ⟨199151, pr199151⟩
private theorem pr199211 : Nat.Prime 199211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv1811]) (by decide +kernel)
def pv199211 : PrimeValue := ⟨199211, pr199211⟩
private theorem pr199247 : Nat.Prime 199247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv99623]) (by decide +kernel)
def pv199247 : PrimeValue := ⟨199247, pr199247⟩
private theorem pr199261 : Nat.Prime 199261 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv199261 : PrimeValue := ⟨199261, pr199261⟩
private theorem pr199289 : Nat.Prime 199289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv859]) (by decide +kernel)
def pv199289 : PrimeValue := ⟨199289, pr199289⟩
private theorem pr199313 : Nat.Prime 199313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12457]) (by decide +kernel)
def pv199313 : PrimeValue := ⟨199313, pr199313⟩
private theorem pr199321 : Nat.Prime 199321 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv11,pv151]) (by decide +kernel)
def pv199321 : PrimeValue := ⟨199321, pr199321⟩
private theorem pr199343 : Nat.Prime 199343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv13,pv17,pv41]) (by decide +kernel)
def pv199343 : PrimeValue := ⟨199343, pr199343⟩
private theorem pr199357 : Nat.Prime 199357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv449]) (by decide +kernel)
def pv199357 : PrimeValue := ⟨199357, pr199357⟩
private theorem pr199379 : Nat.Prime 199379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv99689]) (by decide +kernel)
def pv199379 : PrimeValue := ⟨199379, pr199379⟩
private theorem pr199399 : Nat.Prime 199399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv167,pv199]) (by decide +kernel)
def pv199399 : PrimeValue := ⟨199399, pr199399⟩
private theorem pr199417 : Nat.Prime 199417 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv1187]) (by decide +kernel)
def pv199417 : PrimeValue := ⟨199417, pr199417⟩
private theorem pr199447 : Nat.Prime 199447 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13,pv2557]) (by decide +kernel)
def pv199447 : PrimeValue := ⟨199447, pr199447⟩
private theorem pr199453 : Nat.Prime 199453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1511]) (by decide +kernel)
def pv199453 : PrimeValue := ⟨199453, pr199453⟩
private theorem pr199457 : Nat.Prime 199457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv271]) (by decide +kernel)
def pv199457 : PrimeValue := ⟨199457, pr199457⟩
private theorem pr199483 : Nat.Prime 199483 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv33247]) (by decide +kernel)
def pv199483 : PrimeValue := ⟨199483, pr199483⟩
private theorem pr199489 : Nat.Prime 199489 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv1039]) (by decide +kernel)
def pv199489 : PrimeValue := ⟨199489, pr199489⟩
private theorem pr199499 : Nat.Prime 199499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv7673]) (by decide +kernel)
def pv199499 : PrimeValue := ⟨199499, pr199499⟩
private theorem pr199501 : Nat.Prime 199501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv199501 : PrimeValue := ⟨199501, pr199501⟩
private theorem pr199583 : Nat.Prime 199583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv73,pv1367]) (by decide +kernel)
def pv199583 : PrimeValue := ⟨199583, pr199583⟩
private theorem pr199601 : Nat.Prime 199601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv499]) (by decide +kernel)
def pv199601 : PrimeValue := ⟨199601, pr199601⟩
private theorem pr199603 : Nat.Prime 199603 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv853]) (by decide +kernel)
def pv199603 : PrimeValue := ⟨199603, pr199603⟩
private theorem pr199621 : Nat.Prime 199621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1109]) (by decide +kernel)
def pv199621 : PrimeValue := ⟨199621, pr199621⟩
private theorem pr199669 : Nat.Prime 199669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2377]) (by decide +kernel)
def pv199669 : PrimeValue := ⟨199669, pr199669⟩
private theorem pr199673 : Nat.Prime 199673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv2269]) (by decide +kernel)
def pv199673 : PrimeValue := ⟨199673, pr199673⟩
private theorem pr199679 : Nat.Prime 199679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv99839]) (by decide +kernel)
def pv199679 : PrimeValue := ⟨199679, pr199679⟩
private theorem pr199687 : Nat.Prime 199687 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv1447]) (by decide +kernel)
def pv199687 : PrimeValue := ⟨199687, pr199687⟩
private theorem pr199739 : Nat.Prime 199739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv1297]) (by decide +kernel)
def pv199739 : PrimeValue := ⟨199739, pr199739⟩
private theorem pr199741 : Nat.Prime 199741 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv3329]) (by decide +kernel)
def pv199741 : PrimeValue := ⟨199741, pr199741⟩
private theorem pr199753 : Nat.Prime 199753 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv29,pv41]) (by decide +kernel)
def pv199753 : PrimeValue := ⟨199753, pr199753⟩
private theorem pr199777 : Nat.Prime 199777 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv2081]) (by decide +kernel)
def pv199777 : PrimeValue := ⟨199777, pr199777⟩
private theorem pr199783 : Nat.Prime 199783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv1009]) (by decide +kernel)
def pv199783 : PrimeValue := ⟨199783, pr199783⟩
private theorem pr199807 : Nat.Prime 199807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv33301]) (by decide +kernel)
def pv199807 : PrimeValue := ⟨199807, pr199807⟩
private theorem pr199811 : Nat.Prime 199811 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv29,pv53]) (by decide +kernel)
def pv199811 : PrimeValue := ⟨199811, pr199811⟩
private theorem pr199813 : Nat.Prime 199813 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv16651]) (by decide +kernel)
def pv199813 : PrimeValue := ⟨199813, pr199813⟩
private theorem pr199873 : Nat.Prime 199873 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv347]) (by decide +kernel)
def pv199873 : PrimeValue := ⟨199873, pr199873⟩
private theorem pr199909 : Nat.Prime 199909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv617]) (by decide +kernel)
def pv199909 : PrimeValue := ⟨199909, pr199909⟩
private theorem pr199921 : Nat.Prime 199921 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv199921 : PrimeValue := ⟨199921, pr199921⟩
private theorem pr199931 : Nat.Prime 199931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19993]) (by decide +kernel)
def pv199931 : PrimeValue := ⟨199931, pr199931⟩
private theorem pr199933 : Nat.Prime 199933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16661]) (by decide +kernel)
def pv199933 : PrimeValue := ⟨199933, pr199933⟩
private theorem pr199961 : Nat.Prime 199961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4999]) (by decide +kernel)
def pv199961 : PrimeValue := ⟨199961, pr199961⟩
private theorem pr199967 : Nat.Prime 199967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv7691]) (by decide +kernel)
def pv199967 : PrimeValue := ⟨199967, pr199967⟩
private theorem pr200003 : Nat.Prime 200003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv9091]) (by decide +kernel)
def pv200003 : PrimeValue := ⟨200003, pr200003⟩
private theorem pr200009 : Nat.Prime 200009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv1087]) (by decide +kernel)
def pv200009 : PrimeValue := ⟨200009, pr200009⟩
private theorem pr200023 : Nat.Prime 200023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv37,pv53]) (by decide +kernel)
def pv200023 : PrimeValue := ⟨200023, pr200023⟩
private theorem pr200029 : Nat.Prime 200029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv211]) (by decide +kernel)
def pv200029 : PrimeValue := ⟨200029, pr200029⟩
private theorem pr200033 : Nat.Prime 200033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv47]) (by decide +kernel)
def pv200033 : PrimeValue := ⟨200033, pr200033⟩
private theorem pr200063 : Nat.Prime 200063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv67,pv1493]) (by decide +kernel)
def pv200063 : PrimeValue := ⟨200063, pr200063⟩
private theorem pr200087 : Nat.Prime 200087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv100043]) (by decide +kernel)
def pv200087 : PrimeValue := ⟨200087, pr200087⟩
private theorem pr200131 : Nat.Prime 200131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv953]) (by decide +kernel)
def pv200131 : PrimeValue := ⟨200131, pr200131⟩
private theorem pr200153 : Nat.Prime 200153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv127,pv197]) (by decide +kernel)
def pv200153 : PrimeValue := ⟨200153, pr200153⟩
private theorem pr200159 : Nat.Prime 200159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv17,pv29]) (by decide +kernel)
def pv200159 : PrimeValue := ⟨200159, pr200159⟩
private theorem pr200171 : Nat.Prime 200171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv541]) (by decide +kernel)
def pv200171 : PrimeValue := ⟨200171, pr200171⟩
private theorem pr200177 : Nat.Prime 200177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12511]) (by decide +kernel)
def pv200177 : PrimeValue := ⟨200177, pr200177⟩
private theorem pr200191 : Nat.Prime 200191 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv6673]) (by decide +kernel)
def pv200191 : PrimeValue := ⟨200191, pr200191⟩
private theorem pr200201 : Nat.Prime 200201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv13]) (by decide +kernel)
def pv200201 : PrimeValue := ⟨200201, pr200201⟩
private theorem pr200227 : Nat.Prime 200227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv17,pv151]) (by decide +kernel)
def pv200227 : PrimeValue := ⟨200227, pr200227⟩
private theorem pr200231 : Nat.Prime 200231 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv20023]) (by decide +kernel)
def pv200231 : PrimeValue := ⟨200231, pr200231⟩
private theorem pr200273 : Nat.Prime 200273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12517]) (by decide +kernel)
def pv200273 : PrimeValue := ⟨200273, pr200273⟩
private theorem pr200293 : Nat.Prime 200293 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv16691]) (by decide +kernel)
def pv200293 : PrimeValue := ⟨200293, pr200293⟩
private theorem pr200323 : Nat.Prime 200323 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv359]) (by decide +kernel)
def pv200323 : PrimeValue := ⟨200323, pr200323⟩
private theorem pr200341 : Nat.Prime 200341 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv7,pv53]) (by decide +kernel)
def pv200341 : PrimeValue := ⟨200341, pr200341⟩
private theorem pr200351 : Nat.Prime 200351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv4007]) (by decide +kernel)
def pv200351 : PrimeValue := ⟨200351, pr200351⟩
private theorem pr200357 : Nat.Prime 200357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv3853]) (by decide +kernel)
def pv200357 : PrimeValue := ⟨200357, pr200357⟩
private theorem pr200363 : Nat.Prime 200363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv71,pv83]) (by decide +kernel)
def pv200363 : PrimeValue := ⟨200363, pr200363⟩
private theorem pr200401 : Nat.Prime 200401 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv167]) (by decide +kernel)
def pv200401 : PrimeValue := ⟨200401, pr200401⟩
private theorem pr200437 : Nat.Prime 200437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16703]) (by decide +kernel)
def pv200437 : PrimeValue := ⟨200437, pr200437⟩
private theorem pr200461 : Nat.Prime 200461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv257]) (by decide +kernel)
def pv200461 : PrimeValue := ⟨200461, pr200461⟩
private theorem pr200467 : Nat.Prime 200467 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv37,pv43]) (by decide +kernel)
def pv200467 : PrimeValue := ⟨200467, pr200467⟩
private theorem pr200483 : Nat.Prime 200483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv1699]) (by decide +kernel)
def pv200483 : PrimeValue := ⟨200483, pr200483⟩
private theorem pr200573 : Nat.Prime 200573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv1223]) (by decide +kernel)
def pv200573 : PrimeValue := ⟨200573, pr200573⟩
private theorem pr200579 : Nat.Prime 200579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv14327]) (by decide +kernel)
def pv200579 : PrimeValue := ⟨200579, pr200579⟩
private theorem pr200597 : Nat.Prime 200597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv47,pv97]) (by decide +kernel)
def pv200597 : PrimeValue := ⟨200597, pr200597⟩
private theorem pr200609 : Nat.Prime 200609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6269]) (by decide +kernel)
def pv200609 : PrimeValue := ⟨200609, pr200609⟩
private theorem pr200639 : Nat.Prime 200639 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv43,pv2333]) (by decide +kernel)
def pv200639 : PrimeValue := ⟨200639, pr200639⟩
private theorem pr200657 : Nat.Prime 200657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12541]) (by decide +kernel)
def pv200657 : PrimeValue := ⟨200657, pr200657⟩
private theorem pr200689 : Nat.Prime 200689 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv37,pv113]) (by decide +kernel)
def pv200689 : PrimeValue := ⟨200689, pr200689⟩
private theorem pr200699 : Nat.Prime 200699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv4363]) (by decide +kernel)
def pv200699 : PrimeValue := ⟨200699, pr200699⟩
private theorem pr200713 : Nat.Prime 200713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv8363]) (by decide +kernel)
def pv200713 : PrimeValue := ⟨200713, pr200713⟩
private theorem pr200731 : Nat.Prime 200731 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv6691]) (by decide +kernel)
def pv200731 : PrimeValue := ⟨200731, pr200731⟩
private theorem pr200779 : Nat.Prime 200779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv109,pv307]) (by decide +kernel)
def pv200779 : PrimeValue := ⟨200779, pr200779⟩
private theorem pr200789 : Nat.Prime 200789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv71,pv101]) (by decide +kernel)
def pv200789 : PrimeValue := ⟨200789, pr200789⟩
private theorem pr200797 : Nat.Prime 200797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv577]) (by decide +kernel)
def pv200797 : PrimeValue := ⟨200797, pr200797⟩
private theorem pr200807 : Nat.Prime 200807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv100403]) (by decide +kernel)
def pv200807 : PrimeValue := ⟨200807, pr200807⟩
private theorem pr200843 : Nat.Prime 200843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv137,pv733]) (by decide +kernel)
def pv200843 : PrimeValue := ⟨200843, pr200843⟩
private theorem pr200861 : Nat.Prime 200861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv83]) (by decide +kernel)
def pv200861 : PrimeValue := ⟨200861, pr200861⟩
private theorem pr200869 : Nat.Prime 200869 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv19,pv881]) (by decide +kernel)
def pv200869 : PrimeValue := ⟨200869, pr200869⟩
private theorem pr200881 : Nat.Prime 200881 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv200881 : PrimeValue := ⟨200881, pr200881⟩
private theorem pr200891 : Nat.Prime 200891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv20089]) (by decide +kernel)
def pv200891 : PrimeValue := ⟨200891, pr200891⟩
private theorem pr200903 : Nat.Prime 200903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv7727]) (by decide +kernel)
def pv200903 : PrimeValue := ⟨200903, pr200903⟩
private theorem pr200909 : Nat.Prime 200909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv50227]) (by decide +kernel)
def pv200909 : PrimeValue := ⟨200909, pr200909⟩
private theorem pr200927 : Nat.Prime 200927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv9133]) (by decide +kernel)
def pv200927 : PrimeValue := ⟨200927, pr200927⟩
private theorem pr200929 : Nat.Prime 200929 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv13,pv23]) (by decide +kernel)
def pv200929 : PrimeValue := ⟨200929, pr200929⟩
private theorem pr200983 : Nat.Prime 200983 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv41,pv43]) (by decide +kernel)
def pv200983 : PrimeValue := ⟨200983, pr200983⟩
private theorem pr200987 : Nat.Prime 200987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv100493]) (by decide +kernel)
def pv200987 : PrimeValue := ⟨200987, pr200987⟩
private theorem pr200989 : Nat.Prime 200989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1861]) (by decide +kernel)
def pv200989 : PrimeValue := ⟨200989, pr200989⟩
private theorem pr201007 : Nat.Prime 201007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv859]) (by decide +kernel)
def pv201007 : PrimeValue := ⟨201007, pr201007⟩
private theorem pr201011 : Nat.Prime 201011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv20101]) (by decide +kernel)
def pv201011 : PrimeValue := ⟨201011, pr201011⟩
private theorem pr201031 : Nat.Prime 201031 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv6701]) (by decide +kernel)
def pv201031 : PrimeValue := ⟨201031, pr201031⟩
private theorem pr201037 : Nat.Prime 201037 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1523]) (by decide +kernel)
def pv201037 : PrimeValue := ⟨201037, pr201037⟩
private theorem pr201049 : Nat.Prime 201049 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv8377]) (by decide +kernel)
def pv201049 : PrimeValue := ⟨201049, pr201049⟩
private theorem pr201073 : Nat.Prime 201073 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv59,pv71]) (by decide +kernel)
def pv201073 : PrimeValue := ⟨201073, pr201073⟩
private theorem pr201119 : Nat.Prime 201119 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv100559]) (by decide +kernel)
def pv201119 : PrimeValue := ⟨201119, pr201119⟩
private theorem pr201121 : Nat.Prime 201121 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv419]) (by decide +kernel)
def pv201121 : PrimeValue := ⟨201121, pr201121⟩
private theorem pr201139 : Nat.Prime 201139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv4789]) (by decide +kernel)
def pv201139 : PrimeValue := ⟨201139, pr201139⟩
private theorem pr201151 : Nat.Prime 201151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv149]) (by decide +kernel)
def pv201151 : PrimeValue := ⟨201151, pr201151⟩
private theorem pr201163 : Nat.Prime 201163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2579]) (by decide +kernel)
def pv201163 : PrimeValue := ⟨201163, pr201163⟩
private theorem pr201193 : Nat.Prime 201193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv83,pv101]) (by decide +kernel)
def pv201193 : PrimeValue := ⟨201193, pr201193⟩
private theorem pr201209 : Nat.Prime 201209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3593]) (by decide +kernel)
def pv201209 : PrimeValue := ⟨201209, pr201209⟩
private theorem pr201211 : Nat.Prime 201211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv353]) (by decide +kernel)
def pv201211 : PrimeValue := ⟨201211, pr201211⟩
private theorem pr201247 : Nat.Prime 201247 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv1973]) (by decide +kernel)
def pv201247 : PrimeValue := ⟨201247, pr201247⟩
private theorem pr201251 : Nat.Prime 201251 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv23]) (by decide +kernel)
def pv201251 : PrimeValue := ⟨201251, pr201251⟩
private theorem pr201307 : Nat.Prime 201307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv4793]) (by decide +kernel)
def pv201307 : PrimeValue := ⟨201307, pr201307⟩
private theorem pr201337 : Nat.Prime 201337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv8389]) (by decide +kernel)
def pv201337 : PrimeValue := ⟨201337, pr201337⟩
private theorem pr201401 : Nat.Prime 201401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv53]) (by decide +kernel)
def pv201401 : PrimeValue := ⟨201401, pr201401⟩
private theorem pr201403 : Nat.Prime 201403 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv67,pv167]) (by decide +kernel)
def pv201403 : PrimeValue := ⟨201403, pr201403⟩
private theorem pr201413 : Nat.Prime 201413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv1171]) (by decide +kernel)
def pv201413 : PrimeValue := ⟨201413, pr201413⟩
private theorem pr201437 : Nat.Prime 201437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv50359]) (by decide +kernel)
def pv201437 : PrimeValue := ⟨201437, pr201437⟩
private theorem pr201449 : Nat.Prime 201449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv149]) (by decide +kernel)
def pv201449 : PrimeValue := ⟨201449, pr201449⟩
private theorem pr201451 : Nat.Prime 201451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv79]) (by decide +kernel)
def pv201451 : PrimeValue := ⟨201451, pr201451⟩
private theorem pr201473 : Nat.Prime 201473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv787]) (by decide +kernel)
def pv201473 : PrimeValue := ⟨201473, pr201473⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
