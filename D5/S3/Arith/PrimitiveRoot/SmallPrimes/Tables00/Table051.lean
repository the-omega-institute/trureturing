/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table051
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table051.pv142867
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table006
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr142867 : Nat.Prime 142867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7937]) (by decide +kernel)
def pv142867 : PrimeValue := ⟨142867, pr142867⟩
private theorem pr142871 : Nat.Prime 142871 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv13,pv157]) (by decide +kernel)
def pv142871 : PrimeValue := ⟨142871, pr142871⟩
private theorem pr142873 : Nat.Prime 142873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5953]) (by decide +kernel)
def pv142873 : PrimeValue := ⟨142873, pr142873⟩
private theorem pr142897 : Nat.Prime 142897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv229]) (by decide +kernel)
def pv142897 : PrimeValue := ⟨142897, pr142897⟩
private theorem pr142903 : Nat.Prime 142903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv467]) (by decide +kernel)
def pv142903 : PrimeValue := ⟨142903, pr142903⟩
private theorem pr142907 : Nat.Prime 142907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71453]) (by decide +kernel)
def pv142907 : PrimeValue := ⟨142907, pr142907⟩
private theorem pr142939 : Nat.Prime 142939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2647]) (by decide +kernel)
def pv142939 : PrimeValue := ⟨142939, pr142939⟩
private theorem pr142949 : Nat.Prime 142949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv2749]) (by decide +kernel)
def pv142949 : PrimeValue := ⟨142949, pr142949⟩
private theorem pr142963 : Nat.Prime 142963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23827]) (by decide +kernel)
def pv142963 : PrimeValue := ⟨142963, pr142963⟩
private theorem pr142969 : Nat.Prime 142969 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv23,pv37]) (by decide +kernel)
def pv142969 : PrimeValue := ⟨142969, pr142969⟩
private theorem pr142973 : Nat.Prime 142973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv1153]) (by decide +kernel)
def pv142973 : PrimeValue := ⟨142973, pr142973⟩
private theorem pr142979 : Nat.Prime 142979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv67,pv97]) (by decide +kernel)
def pv142979 : PrimeValue := ⟨142979, pr142979⟩
private theorem pr142981 : Nat.Prime 142981 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2383]) (by decide +kernel)
def pv142981 : PrimeValue := ⟨142981, pr142981⟩
private theorem pr142993 : Nat.Prime 142993 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv331]) (by decide +kernel)
def pv142993 : PrimeValue := ⟨142993, pr142993⟩
private theorem pr143053 : Nat.Prime 143053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv131]) (by decide +kernel)
def pv143053 : PrimeValue := ⟨143053, pr143053⟩
private theorem pr143063 : Nat.Prime 143063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv233,pv307]) (by decide +kernel)
def pv143063 : PrimeValue := ⟨143063, pr143063⟩
private theorem pr143093 : Nat.Prime 143093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv431]) (by decide +kernel)
def pv143093 : PrimeValue := ⟨143093, pr143093⟩
private theorem pr143107 : Nat.Prime 143107 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv23,pv61]) (by decide +kernel)
def pv143107 : PrimeValue := ⟨143107, pr143107⟩
private theorem pr143111 : Nat.Prime 143111 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv1301]) (by decide +kernel)
def pv143111 : PrimeValue := ⟨143111, pr143111⟩
private theorem pr143113 : Nat.Prime 143113 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv67,pv89]) (by decide +kernel)
def pv143113 : PrimeValue := ⟨143113, pr143113⟩
private theorem pr143137 : Nat.Prime 143137 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv71]) (by decide +kernel)
def pv143137 : PrimeValue := ⟨143137, pr143137⟩
private theorem pr143141 : Nat.Prime 143141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv421]) (by decide +kernel)
def pv143141 : PrimeValue := ⟨143141, pr143141⟩
private theorem pr143159 : Nat.Prime 143159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv31,pv2309]) (by decide +kernel)
def pv143159 : PrimeValue := ⟨143159, pr143159⟩
private theorem pr143177 : Nat.Prime 143177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv1627]) (by decide +kernel)
def pv143177 : PrimeValue := ⟨143177, pr143177⟩
private theorem pr143239 : Nat.Prime 143239 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23873]) (by decide +kernel)
def pv143239 : PrimeValue := ⟨143239, pr143239⟩
private theorem pr143243 : Nat.Prime 143243 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv17,pv383]) (by decide +kernel)
def pv143243 : PrimeValue := ⟨143243, pr143243⟩
private theorem pr143249 : Nat.Prime 143249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1279]) (by decide +kernel)
def pv143249 : PrimeValue := ⟨143249, pr143249⟩
private theorem pr143261 : Nat.Prime 143261 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv19,pv29]) (by decide +kernel)
def pv143261 : PrimeValue := ⟨143261, pr143261⟩
private theorem pr143263 : Nat.Prime 143263 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv379]) (by decide +kernel)
def pv143263 : PrimeValue := ⟨143263, pr143263⟩
private theorem pr143281 : Nat.Prime 143281 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv199]) (by decide +kernel)
def pv143281 : PrimeValue := ⟨143281, pr143281⟩
private theorem pr143287 : Nat.Prime 143287 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv13,pv167]) (by decide +kernel)
def pv143287 : PrimeValue := ⟨143287, pr143287⟩
private theorem pr143291 : Nat.Prime 143291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv23,pv89]) (by decide +kernel)
def pv143291 : PrimeValue := ⟨143291, pr143291⟩
private theorem pr143329 : Nat.Prime 143329 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv1493]) (by decide +kernel)
def pv143329 : PrimeValue := ⟨143329, pr143329⟩
private theorem pr143357 : Nat.Prime 143357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv35839]) (by decide +kernel)
def pv143357 : PrimeValue := ⟨143357, pr143357⟩
private theorem pr143387 : Nat.Prime 143387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71693]) (by decide +kernel)
def pv143387 : PrimeValue := ⟨143387, pr143387⟩
private theorem pr143401 : Nat.Prime 143401 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv239]) (by decide +kernel)
def pv143401 : PrimeValue := ⟨143401, pr143401⟩
private theorem pr143413 : Nat.Prime 143413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv19,pv37]) (by decide +kernel)
def pv143413 : PrimeValue := ⟨143413, pr143413⟩
private theorem pr143443 : Nat.Prime 143443 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv613]) (by decide +kernel)
def pv143443 : PrimeValue := ⟨143443, pr143443⟩
private theorem pr143467 : Nat.Prime 143467 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23911]) (by decide +kernel)
def pv143467 : PrimeValue := ⟨143467, pr143467⟩
private theorem pr143477 : Nat.Prime 143477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv35869]) (by decide +kernel)
def pv143477 : PrimeValue := ⟨143477, pr143477⟩
private theorem pr143483 : Nat.Prime 143483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71741]) (by decide +kernel)
def pv143483 : PrimeValue := ⟨143483, pr143483⟩
private theorem pr143489 : Nat.Prime 143489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv59]) (by decide +kernel)
def pv143489 : PrimeValue := ⟨143489, pr143489⟩
private theorem pr143501 : Nat.Prime 143501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv41]) (by decide +kernel)
def pv143501 : PrimeValue := ⟨143501, pr143501⟩
private theorem pr143503 : Nat.Prime 143503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23917]) (by decide +kernel)
def pv143503 : PrimeValue := ⟨143503, pr143503⟩
private theorem pr143509 : Nat.Prime 143509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11959]) (by decide +kernel)
def pv143509 : PrimeValue := ⟨143509, pr143509⟩
private theorem pr143513 : Nat.Prime 143513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17939]) (by decide +kernel)
def pv143513 : PrimeValue := ⟨143513, pr143513⟩
private theorem pr143527 : Nat.Prime 143527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv1259]) (by decide +kernel)
def pv143527 : PrimeValue := ⟨143527, pr143527⟩
private theorem pr143537 : Nat.Prime 143537 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv8971]) (by decide +kernel)
def pv143537 : PrimeValue := ⟨143537, pr143537⟩
private theorem pr143551 : Nat.Prime 143551 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv29]) (by decide +kernel)
def pv143551 : PrimeValue := ⟨143551, pr143551⟩
private theorem pr143567 : Nat.Prime 143567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv3121]) (by decide +kernel)
def pv143567 : PrimeValue := ⟨143567, pr143567⟩
private theorem pr143569 : Nat.Prime 143569 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv997]) (by decide +kernel)
def pv143569 : PrimeValue := ⟨143569, pr143569⟩
private theorem pr143573 : Nat.Prime 143573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv251]) (by decide +kernel)
def pv143573 : PrimeValue := ⟨143573, pr143573⟩
private theorem pr143593 : Nat.Prime 143593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv193]) (by decide +kernel)
def pv143593 : PrimeValue := ⟨143593, pr143593⟩
private theorem pr143609 : Nat.Prime 143609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv619]) (by decide +kernel)
def pv143609 : PrimeValue := ⟨143609, pr143609⟩
private theorem pr143617 : Nat.Prime 143617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv143617 : PrimeValue := ⟨143617, pr143617⟩
private theorem pr143629 : Nat.Prime 143629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11969]) (by decide +kernel)
def pv143629 : PrimeValue := ⟨143629, pr143629⟩
private theorem pr143651 : Nat.Prime 143651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv17]) (by decide +kernel)
def pv143651 : PrimeValue := ⟨143651, pr143651⟩
private theorem pr143653 : Nat.Prime 143653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11971]) (by decide +kernel)
def pv143653 : PrimeValue := ⟨143653, pr143653⟩
private theorem pr143669 : Nat.Prime 143669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv733]) (by decide +kernel)
def pv143669 : PrimeValue := ⟨143669, pr143669⟩
private theorem pr143677 : Nat.Prime 143677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv307]) (by decide +kernel)
def pv143677 : PrimeValue := ⟨143677, pr143677⟩
private theorem pr143687 : Nat.Prime 143687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv71843]) (by decide +kernel)
def pv143687 : PrimeValue := ⟨143687, pr143687⟩
private theorem pr143699 : Nat.Prime 143699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71849]) (by decide +kernel)
def pv143699 : PrimeValue := ⟨143699, pr143699⟩
private theorem pr143711 : Nat.Prime 143711 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv2053]) (by decide +kernel)
def pv143711 : PrimeValue := ⟨143711, pr143711⟩
private theorem pr143719 : Nat.Prime 143719 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv17,pv1409]) (by decide +kernel)
def pv143719 : PrimeValue := ⟨143719, pr143719⟩
private theorem pr143729 : Nat.Prime 143729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv691]) (by decide +kernel)
def pv143729 : PrimeValue := ⟨143729, pr143729⟩
private theorem pr143743 : Nat.Prime 143743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23957]) (by decide +kernel)
def pv143743 : PrimeValue := ⟨143743, pr143743⟩
private theorem pr143797 : Nat.Prime 143797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv521]) (by decide +kernel)
def pv143797 : PrimeValue := ⟨143797, pr143797⟩
private theorem pr143807 : Nat.Prime 143807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv5531]) (by decide +kernel)
def pv143807 : PrimeValue := ⟨143807, pr143807⟩
private theorem pr143813 : Nat.Prime 143813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv229]) (by decide +kernel)
def pv143813 : PrimeValue := ⟨143813, pr143813⟩
private theorem pr143821 : Nat.Prime 143821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv47]) (by decide +kernel)
def pv143821 : PrimeValue := ⟨143821, pr143821⟩
private theorem pr143827 : Nat.Prime 143827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23971]) (by decide +kernel)
def pv143827 : PrimeValue := ⟨143827, pr143827⟩
private theorem pr143831 : Nat.Prime 143831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv757]) (by decide +kernel)
def pv143831 : PrimeValue := ⟨143831, pr143831⟩
private theorem pr143833 : Nat.Prime 143833 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv461]) (by decide +kernel)
def pv143833 : PrimeValue := ⟨143833, pr143833⟩
private theorem pr143873 : Nat.Prime 143873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv281]) (by decide +kernel)
def pv143873 : PrimeValue := ⟨143873, pr143873⟩
private theorem pr143879 : Nat.Prime 143879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv43,pv239]) (by decide +kernel)
def pv143879 : PrimeValue := ⟨143879, pr143879⟩
private theorem pr143881 : Nat.Prime 143881 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv109]) (by decide +kernel)
def pv143881 : PrimeValue := ⟨143881, pr143881⟩
private theorem pr143909 : Nat.Prime 143909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv35977]) (by decide +kernel)
def pv143909 : PrimeValue := ⟨143909, pr143909⟩
private theorem pr143947 : Nat.Prime 143947 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv727]) (by decide +kernel)
def pv143947 : PrimeValue := ⟨143947, pr143947⟩
private theorem pr143953 : Nat.Prime 143953 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2999]) (by decide +kernel)
def pv143953 : PrimeValue := ⟨143953, pr143953⟩
private theorem pr143971 : Nat.Prime 143971 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv4799]) (by decide +kernel)
def pv143971 : PrimeValue := ⟨143971, pr143971⟩
private theorem pr143977 : Nat.Prime 143977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv857]) (by decide +kernel)
def pv143977 : PrimeValue := ⟨143977, pr143977⟩
private theorem pr143981 : Nat.Prime 143981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv313]) (by decide +kernel)
def pv143981 : PrimeValue := ⟨143981, pr143981⟩
private theorem pr143999 : Nat.Prime 143999 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv71999]) (by decide +kernel)
def pv143999 : PrimeValue := ⟨143999, pr143999⟩
private theorem pr144013 : Nat.Prime 144013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1091]) (by decide +kernel)
def pv144013 : PrimeValue := ⟨144013, pr144013⟩
private theorem pr144037 : Nat.Prime 144037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4001]) (by decide +kernel)
def pv144037 : PrimeValue := ⟨144037, pr144037⟩
private theorem pr144061 : Nat.Prime 144061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv144061 : PrimeValue := ⟨144061, pr144061⟩
private theorem pr144071 : Nat.Prime 144071 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv14407]) (by decide +kernel)
def pv144071 : PrimeValue := ⟨144071, pr144071⟩
private theorem pr144073 : Nat.Prime 144073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv29]) (by decide +kernel)
def pv144073 : PrimeValue := ⟨144073, pr144073⟩
private theorem pr144103 : Nat.Prime 144103 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv47,pv73]) (by decide +kernel)
def pv144103 : PrimeValue := ⟨144103, pr144103⟩
private theorem pr144139 : Nat.Prime 144139 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv24023]) (by decide +kernel)
def pv144139 : PrimeValue := ⟨144139, pr144139⟩
private theorem pr144161 : Nat.Prime 144161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv53]) (by decide +kernel)
def pv144161 : PrimeValue := ⟨144161, pr144161⟩
private theorem pr144163 : Nat.Prime 144163 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8009]) (by decide +kernel)
def pv144163 : PrimeValue := ⟨144163, pr144163⟩
private theorem pr144167 : Nat.Prime 144167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv6553]) (by decide +kernel)
def pv144167 : PrimeValue := ⟨144167, pr144167⟩
private theorem pr144169 : Nat.Prime 144169 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv6007]) (by decide +kernel)
def pv144169 : PrimeValue := ⟨144169, pr144169⟩
private theorem pr144203 : Nat.Prime 144203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv72101]) (by decide +kernel)
def pv144203 : PrimeValue := ⟨144203, pr144203⟩
private theorem pr144223 : Nat.Prime 144223 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv43]) (by decide +kernel)
def pv144223 : PrimeValue := ⟨144223, pr144223⟩
private theorem pr144241 : Nat.Prime 144241 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv601]) (by decide +kernel)
def pv144241 : PrimeValue := ⟨144241, pr144241⟩
private theorem pr144247 : Nat.Prime 144247 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv829]) (by decide +kernel)
def pv144247 : PrimeValue := ⟨144247, pr144247⟩
private theorem pr144253 : Nat.Prime 144253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4007]) (by decide +kernel)
def pv144253 : PrimeValue := ⟨144253, pr144253⟩
private theorem pr144259 : Nat.Prime 144259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24043]) (by decide +kernel)
def pv144259 : PrimeValue := ⟨144259, pr144259⟩
private theorem pr144271 : Nat.Prime 144271 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv7,pv229]) (by decide +kernel)
def pv144271 : PrimeValue := ⟨144271, pr144271⟩
private theorem pr144289 : Nat.Prime 144289 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv167]) (by decide +kernel)
def pv144289 : PrimeValue := ⟨144289, pr144289⟩
private theorem pr144299 : Nat.Prime 144299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv937]) (by decide +kernel)
def pv144299 : PrimeValue := ⟨144299, pr144299⟩
private theorem pr144307 : Nat.Prime 144307 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8017]) (by decide +kernel)
def pv144307 : PrimeValue := ⟨144307, pr144307⟩
private theorem pr144311 : Nat.Prime 144311 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv14431]) (by decide +kernel)
def pv144311 : PrimeValue := ⟨144311, pr144311⟩
private theorem pr144323 : Nat.Prime 144323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv72161]) (by decide +kernel)
def pv144323 : PrimeValue := ⟨144323, pr144323⟩
private theorem pr144341 : Nat.Prime 144341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv1031]) (by decide +kernel)
def pv144341 : PrimeValue := ⟨144341, pr144341⟩
private theorem pr144349 : Nat.Prime 144349 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv23,pv523]) (by decide +kernel)
def pv144349 : PrimeValue := ⟨144349, pr144349⟩
private theorem pr144379 : Nat.Prime 144379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv617]) (by decide +kernel)
def pv144379 : PrimeValue := ⟨144379, pr144379⟩
private theorem pr144383 : Nat.Prime 144383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv10313]) (by decide +kernel)
def pv144383 : PrimeValue := ⟨144383, pr144383⟩
private theorem pr144407 : Nat.Prime 144407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv103,pv701]) (by decide +kernel)
def pv144407 : PrimeValue := ⟨144407, pr144407⟩
private theorem pr144409 : Nat.Prime 144409 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv547]) (by decide +kernel)
def pv144409 : PrimeValue := ⟨144409, pr144409⟩
private theorem pr144413 : Nat.Prime 144413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv457]) (by decide +kernel)
def pv144413 : PrimeValue := ⟨144413, pr144413⟩
private theorem pr144427 : Nat.Prime 144427 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv24071]) (by decide +kernel)
def pv144427 : PrimeValue := ⟨144427, pr144427⟩
private theorem pr144439 : Nat.Prime 144439 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv19,pv181]) (by decide +kernel)
def pv144439 : PrimeValue := ⟨144439, pr144439⟩
private theorem pr144451 : Nat.Prime 144451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv144451 : PrimeValue := ⟨144451, pr144451⟩
private theorem pr144461 : Nat.Prime 144461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv233]) (by decide +kernel)
def pv144461 : PrimeValue := ⟨144461, pr144461⟩
private theorem pr144479 : Nat.Prime 144479 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv29,pv47,pv53]) (by decide +kernel)
def pv144479 : PrimeValue := ⟨144479, pr144479⟩
private theorem pr144481 : Nat.Prime 144481 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv43]) (by decide +kernel)
def pv144481 : PrimeValue := ⟨144481, pr144481⟩
private theorem pr144497 : Nat.Prime 144497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv821]) (by decide +kernel)
def pv144497 : PrimeValue := ⟨144497, pr144497⟩
private theorem pr144511 : Nat.Prime 144511 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv4817]) (by decide +kernel)
def pv144511 : PrimeValue := ⟨144511, pr144511⟩
private theorem pr144539 : Nat.Prime 144539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv72269]) (by decide +kernel)
def pv144539 : PrimeValue := ⟨144539, pr144539⟩
private theorem pr144563 : Nat.Prime 144563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv6571]) (by decide +kernel)
def pv144563 : PrimeValue := ⟨144563, pr144563⟩
private theorem pr144569 : Nat.Prime 144569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv1063]) (by decide +kernel)
def pv144569 : PrimeValue := ⟨144569, pr144569⟩
private theorem pr144577 : Nat.Prime 144577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv251]) (by decide +kernel)
def pv144577 : PrimeValue := ⟨144577, pr144577⟩
private theorem pr144583 : Nat.Prime 144583 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv24097]) (by decide +kernel)
def pv144583 : PrimeValue := ⟨144583, pr144583⟩
private theorem pr144589 : Nat.Prime 144589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12049]) (by decide +kernel)
def pv144589 : PrimeValue := ⟨144589, pr144589⟩
private theorem pr144593 : Nat.Prime 144593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1291]) (by decide +kernel)
def pv144593 : PrimeValue := ⟨144593, pr144593⟩
private theorem pr144611 : Nat.Prime 144611 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv14461]) (by decide +kernel)
def pv144611 : PrimeValue := ⟨144611, pr144611⟩
private theorem pr144629 : Nat.Prime 144629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv173]) (by decide +kernel)
def pv144629 : PrimeValue := ⟨144629, pr144629⟩
private theorem pr144659 : Nat.Prime 144659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv479]) (by decide +kernel)
def pv144659 : PrimeValue := ⟨144659, pr144659⟩
private theorem pr144667 : Nat.Prime 144667 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv47]) (by decide +kernel)
def pv144667 : PrimeValue := ⟨144667, pr144667⟩
private theorem pr144671 : Nat.Prime 144671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv23,pv37]) (by decide +kernel)
def pv144671 : PrimeValue := ⟨144671, pr144671⟩
private theorem pr144701 : Nat.Prime 144701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1447]) (by decide +kernel)
def pv144701 : PrimeValue := ⟨144701, pr144701⟩
private theorem pr144709 : Nat.Prime 144709 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv31,pv389]) (by decide +kernel)
def pv144709 : PrimeValue := ⟨144709, pr144709⟩
private theorem pr144719 : Nat.Prime 144719 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv10337]) (by decide +kernel)
def pv144719 : PrimeValue := ⟨144719, pr144719⟩
private theorem pr144731 : Nat.Prime 144731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv353]) (by decide +kernel)
def pv144731 : PrimeValue := ⟨144731, pr144731⟩
private theorem pr144737 : Nat.Prime 144737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4523]) (by decide +kernel)
def pv144737 : PrimeValue := ⟨144737, pr144737⟩
private theorem pr144757 : Nat.Prime 144757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4021]) (by decide +kernel)
def pv144757 : PrimeValue := ⟨144757, pr144757⟩
private theorem pr144763 : Nat.Prime 144763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv1049]) (by decide +kernel)
def pv144763 : PrimeValue := ⟨144763, pr144763⟩
private theorem pr144773 : Nat.Prime 144773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv2129]) (by decide +kernel)
def pv144773 : PrimeValue := ⟨144773, pr144773⟩
private theorem pr144779 : Nat.Prime 144779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv191,pv379]) (by decide +kernel)
def pv144779 : PrimeValue := ⟨144779, pr144779⟩
private theorem pr144791 : Nat.Prime 144791 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv14479]) (by decide +kernel)
def pv144791 : PrimeValue := ⟨144791, pr144791⟩
private theorem pr144817 : Nat.Prime 144817 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv431]) (by decide +kernel)
def pv144817 : PrimeValue := ⟨144817, pr144817⟩
private theorem pr144829 : Nat.Prime 144829 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv149]) (by decide +kernel)
def pv144829 : PrimeValue := ⟨144829, pr144829⟩
private theorem pr144839 : Nat.Prime 144839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv139,pv521]) (by decide +kernel)
def pv144839 : PrimeValue := ⟨144839, pr144839⟩
private theorem pr144883 : Nat.Prime 144883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2683]) (by decide +kernel)
def pv144883 : PrimeValue := ⟨144883, pr144883⟩
private theorem pr144887 : Nat.Prime 144887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv79,pv131]) (by decide +kernel)
def pv144887 : PrimeValue := ⟨144887, pr144887⟩
private theorem pr144889 : Nat.Prime 144889 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv6037]) (by decide +kernel)
def pv144889 : PrimeValue := ⟨144889, pr144889⟩
private theorem pr144899 : Nat.Prime 144899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv5573]) (by decide +kernel)
def pv144899 : PrimeValue := ⟨144899, pr144899⟩
private theorem pr144917 : Nat.Prime 144917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv36229]) (by decide +kernel)
def pv144917 : PrimeValue := ⟨144917, pr144917⟩
private theorem pr144931 : Nat.Prime 144931 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv4831]) (by decide +kernel)
def pv144931 : PrimeValue := ⟨144931, pr144931⟩
private theorem pr144941 : Nat.Prime 144941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7247]) (by decide +kernel)
def pv144941 : PrimeValue := ⟨144941, pr144941⟩
private theorem pr144961 : Nat.Prime 144961 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv151]) (by decide +kernel)
def pv144961 : PrimeValue := ⟨144961, pr144961⟩
private theorem pr144967 : Nat.Prime 144967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv653]) (by decide +kernel)
def pv144967 : PrimeValue := ⟨144967, pr144967⟩
private theorem pr144973 : Nat.Prime 144973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4027]) (by decide +kernel)
def pv144973 : PrimeValue := ⟨144973, pr144973⟩
private theorem pr144983 : Nat.Prime 144983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv71,pv1021]) (by decide +kernel)
def pv144983 : PrimeValue := ⟨144983, pr144983⟩
private theorem pr145007 : Nat.Prime 145007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv72503]) (by decide +kernel)
def pv145007 : PrimeValue := ⟨145007, pr145007⟩
private theorem pr145021 : Nat.Prime 145021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2417]) (by decide +kernel)
def pv145021 : PrimeValue := ⟨145021, pr145021⟩
private theorem pr145031 : Nat.Prime 145031 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv14503]) (by decide +kernel)
def pv145031 : PrimeValue := ⟨145031, pr145031⟩
private theorem pr145037 : Nat.Prime 145037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv359]) (by decide +kernel)
def pv145037 : PrimeValue := ⟨145037, pr145037⟩
private theorem pr145063 : Nat.Prime 145063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8059]) (by decide +kernel)
def pv145063 : PrimeValue := ⟨145063, pr145063⟩
private theorem pr145069 : Nat.Prime 145069 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv11,pv157]) (by decide +kernel)
def pv145069 : PrimeValue := ⟨145069, pr145069⟩
private theorem pr145091 : Nat.Prime 145091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv1319]) (by decide +kernel)
def pv145091 : PrimeValue := ⟨145091, pr145091⟩
private theorem pr145109 : Nat.Prime 145109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv36277]) (by decide +kernel)
def pv145109 : PrimeValue := ⟨145109, pr145109⟩
private theorem pr145121 : Nat.Prime 145121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv907]) (by decide +kernel)
def pv145121 : PrimeValue := ⟨145121, pr145121⟩
private theorem pr145133 : Nat.Prime 145133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv2791]) (by decide +kernel)
def pv145133 : PrimeValue := ⟨145133, pr145133⟩
private theorem pr145139 : Nat.Prime 145139 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv1481]) (by decide +kernel)
def pv145139 : PrimeValue := ⟨145139, pr145139⟩
private theorem pr145177 : Nat.Prime 145177 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv23,pv263]) (by decide +kernel)
def pv145177 : PrimeValue := ⟨145177, pr145177⟩
private theorem pr145193 : Nat.Prime 145193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv18149]) (by decide +kernel)
def pv145193 : PrimeValue := ⟨145193, pr145193⟩
private theorem pr145207 : Nat.Prime 145207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2689]) (by decide +kernel)
def pv145207 : PrimeValue := ⟨145207, pr145207⟩
private theorem pr145213 : Nat.Prime 145213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12101]) (by decide +kernel)
def pv145213 : PrimeValue := ⟨145213, pr145213⟩
private theorem pr145253 : Nat.Prime 145253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv36313]) (by decide +kernel)
def pv145253 : PrimeValue := ⟨145253, pr145253⟩
private theorem pr145267 : Nat.Prime 145267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv31,pv71]) (by decide +kernel)
def pv145267 : PrimeValue := ⟨145267, pr145267⟩
private theorem pr145283 : Nat.Prime 145283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv4273]) (by decide +kernel)
def pv145283 : PrimeValue := ⟨145283, pr145283⟩
private theorem pr145289 : Nat.Prime 145289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13,pv127]) (by decide +kernel)
def pv145289 : PrimeValue := ⟨145289, pr145289⟩
private theorem pr145307 : Nat.Prime 145307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv97,pv107]) (by decide +kernel)
def pv145307 : PrimeValue := ⟨145307, pr145307⟩
private theorem pr145349 : Nat.Prime 145349 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv29,pv179]) (by decide +kernel)
def pv145349 : PrimeValue := ⟨145349, pr145349⟩
private theorem pr145381 : Nat.Prime 145381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2423]) (by decide +kernel)
def pv145381 : PrimeValue := ⟨145381, pr145381⟩
private theorem pr145399 : Nat.Prime 145399 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv2203]) (by decide +kernel)
def pv145399 : PrimeValue := ⟨145399, pr145399⟩
private theorem pr145417 : Nat.Prime 145417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv73,pv83]) (by decide +kernel)
def pv145417 : PrimeValue := ⟨145417, pr145417⟩
private theorem pr145423 : Nat.Prime 145423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2693]) (by decide +kernel)
def pv145423 : PrimeValue := ⟨145423, pr145423⟩
private theorem pr145433 : Nat.Prime 145433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv53]) (by decide +kernel)
def pv145433 : PrimeValue := ⟨145433, pr145433⟩
private theorem pr145441 : Nat.Prime 145441 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv101]) (by decide +kernel)
def pv145441 : PrimeValue := ⟨145441, pr145441⟩
private theorem pr145451 : Nat.Prime 145451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2909]) (by decide +kernel)
def pv145451 : PrimeValue := ⟨145451, pr145451⟩
private theorem pr145459 : Nat.Prime 145459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8081]) (by decide +kernel)
def pv145459 : PrimeValue := ⟨145459, pr145459⟩
private theorem pr145471 : Nat.Prime 145471 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv373]) (by decide +kernel)
def pv145471 : PrimeValue := ⟨145471, pr145471⟩
private theorem pr145477 : Nat.Prime 145477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv449]) (by decide +kernel)
def pv145477 : PrimeValue := ⟨145477, pr145477⟩
private theorem pr145487 : Nat.Prime 145487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv17,pv389]) (by decide +kernel)
def pv145487 : PrimeValue := ⟨145487, pr145487⟩
private theorem pr145501 : Nat.Prime 145501 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv97]) (by decide +kernel)
def pv145501 : PrimeValue := ⟨145501, pr145501⟩
private theorem pr145513 : Nat.Prime 145513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv47]) (by decide +kernel)
def pv145513 : PrimeValue := ⟨145513, pr145513⟩
private theorem pr145531 : Nat.Prime 145531 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv145531 : PrimeValue := ⟨145531, pr145531⟩
private theorem pr145543 : Nat.Prime 145543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv127,pv191]) (by decide +kernel)
def pv145543 : PrimeValue := ⟨145543, pr145543⟩
private theorem pr145547 : Nat.Prime 145547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv1193]) (by decide +kernel)
def pv145547 : PrimeValue := ⟨145547, pr145547⟩
private theorem pr145549 : Nat.Prime 145549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv311]) (by decide +kernel)
def pv145549 : PrimeValue := ⟨145549, pr145549⟩
private theorem pr145577 : Nat.Prime 145577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv587]) (by decide +kernel)
def pv145577 : PrimeValue := ⟨145577, pr145577⟩
private theorem pr145589 : Nat.Prime 145589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv2141]) (by decide +kernel)
def pv145589 : PrimeValue := ⟨145589, pr145589⟩
private theorem pr145601 : Nat.Prime 145601 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv7,pv13]) (by decide +kernel)
def pv145601 : PrimeValue := ⟨145601, pr145601⟩
private theorem pr145603 : Nat.Prime 145603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8089]) (by decide +kernel)
def pv145603 : PrimeValue := ⟨145603, pr145603⟩
private theorem pr145633 : Nat.Prime 145633 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv37,pv41]) (by decide +kernel)
def pv145633 : PrimeValue := ⟨145633, pr145633⟩
private theorem pr145637 : Nat.Prime 145637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv1583]) (by decide +kernel)
def pv145637 : PrimeValue := ⟨145637, pr145637⟩
private theorem pr145643 : Nat.Prime 145643 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv101,pv103]) (by decide +kernel)
def pv145643 : PrimeValue := ⟨145643, pr145643⟩
private theorem pr145679 : Nat.Prime 145679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv431]) (by decide +kernel)
def pv145679 : PrimeValue := ⟨145679, pr145679⟩
private theorem pr145681 : Nat.Prime 145681 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv607]) (by decide +kernel)
def pv145681 : PrimeValue := ⟨145681, pr145681⟩
private theorem pr145709 : Nat.Prime 145709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv499]) (by decide +kernel)
def pv145709 : PrimeValue := ⟨145709, pr145709⟩
private theorem pr145721 : Nat.Prime 145721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3643]) (by decide +kernel)
def pv145721 : PrimeValue := ⟨145721, pr145721⟩
private theorem pr145723 : Nat.Prime 145723 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv149,pv163]) (by decide +kernel)
def pv145723 : PrimeValue := ⟨145723, pr145723⟩
private theorem pr145753 : Nat.Prime 145753 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv6073]) (by decide +kernel)
def pv145753 : PrimeValue := ⟨145753, pr145753⟩
private theorem pr145757 : Nat.Prime 145757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv2803]) (by decide +kernel)
def pv145757 : PrimeValue := ⟨145757, pr145757⟩
private theorem pr145799 : Nat.Prime 145799 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv269,pv271]) (by decide +kernel)
def pv145799 : PrimeValue := ⟨145799, pr145799⟩
private theorem pr145807 : Nat.Prime 145807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv1279]) (by decide +kernel)
def pv145807 : PrimeValue := ⟨145807, pr145807⟩
private theorem pr145823 : Nat.Prime 145823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv72911]) (by decide +kernel)
def pv145823 : PrimeValue := ⟨145823, pr145823⟩
private theorem pr145829 : Nat.Prime 145829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv36457]) (by decide +kernel)
def pv145829 : PrimeValue := ⟨145829, pr145829⟩
private theorem pr145879 : Nat.Prime 145879 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv41,pv593]) (by decide +kernel)
def pv145879 : PrimeValue := ⟨145879, pr145879⟩
private theorem pr145897 : Nat.Prime 145897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6079]) (by decide +kernel)
def pv145897 : PrimeValue := ⟨145897, pr145897⟩
private theorem pr145903 : Nat.Prime 145903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv24317]) (by decide +kernel)
def pv145903 : PrimeValue := ⟨145903, pr145903⟩
private theorem pr145931 : Nat.Prime 145931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv14593]) (by decide +kernel)
def pv145931 : PrimeValue := ⟨145931, pr145931⟩
private theorem pr145933 : Nat.Prime 145933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12161]) (by decide +kernel)
def pv145933 : PrimeValue := ⟨145933, pr145933⟩
private theorem pr145949 : Nat.Prime 145949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv31,pv107]) (by decide +kernel)
def pv145949 : PrimeValue := ⟨145949, pr145949⟩
private theorem pr145963 : Nat.Prime 145963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv53]) (by decide +kernel)
def pv145963 : PrimeValue := ⟨145963, pr145963⟩
private theorem pr145967 : Nat.Prime 145967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv59,pv1237]) (by decide +kernel)
def pv145967 : PrimeValue := ⟨145967, pr145967⟩
private theorem pr145969 : Nat.Prime 145969 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv3041]) (by decide +kernel)
def pv145969 : PrimeValue := ⟨145969, pr145969⟩
private theorem pr145987 : Nat.Prime 145987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv839]) (by decide +kernel)
def pv145987 : PrimeValue := ⟨145987, pr145987⟩
private theorem pr145991 : Nat.Prime 145991 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv1123]) (by decide +kernel)
def pv145991 : PrimeValue := ⟨145991, pr145991⟩
private theorem pr146009 : Nat.Prime 146009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv18251]) (by decide +kernel)
def pv146009 : PrimeValue := ⟨146009, pr146009⟩
private theorem pr146011 : Nat.Prime 146011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv31,pv157]) (by decide +kernel)
def pv146011 : PrimeValue := ⟨146011, pr146011⟩
private theorem pr146021 : Nat.Prime 146021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv149]) (by decide +kernel)
def pv146021 : PrimeValue := ⟨146021, pr146021⟩
private theorem pr146033 : Nat.Prime 146033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9127]) (by decide +kernel)
def pv146033 : PrimeValue := ⟨146033, pr146033⟩
private theorem pr146051 : Nat.Prime 146051 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv23,pv127]) (by decide +kernel)
def pv146051 : PrimeValue := ⟨146051, pr146051⟩
private theorem pr146063 : Nat.Prime 146063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv10433]) (by decide +kernel)
def pv146063 : PrimeValue := ⟨146063, pr146063⟩
private theorem pr146077 : Nat.Prime 146077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv37,pv47]) (by decide +kernel)
def pv146077 : PrimeValue := ⟨146077, pr146077⟩
private theorem pr146093 : Nat.Prime 146093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv36523]) (by decide +kernel)
def pv146093 : PrimeValue := ⟨146093, pr146093⟩
private theorem pr146099 : Nat.Prime 146099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv4297]) (by decide +kernel)
def pv146099 : PrimeValue := ⟨146099, pr146099⟩
private theorem pr146117 : Nat.Prime 146117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv36529]) (by decide +kernel)
def pv146117 : PrimeValue := ⟨146117, pr146117⟩
private theorem pr146141 : Nat.Prime 146141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7307]) (by decide +kernel)
def pv146141 : PrimeValue := ⟨146141, pr146141⟩
private theorem pr146161 : Nat.Prime 146161 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv29]) (by decide +kernel)
def pv146161 : PrimeValue := ⟨146161, pr146161⟩
private theorem pr146173 : Nat.Prime 146173 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv937]) (by decide +kernel)
def pv146173 : PrimeValue := ⟨146173, pr146173⟩
private theorem pr146191 : Nat.Prime 146191 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv443]) (by decide +kernel)
def pv146191 : PrimeValue := ⟨146191, pr146191⟩
private theorem pr146197 : Nat.Prime 146197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv131]) (by decide +kernel)
def pv146197 : PrimeValue := ⟨146197, pr146197⟩
private theorem pr146203 : Nat.Prime 146203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv59]) (by decide +kernel)
def pv146203 : PrimeValue := ⟨146203, pr146203⟩
private theorem pr146213 : Nat.Prime 146213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv3323]) (by decide +kernel)
def pv146213 : PrimeValue := ⟨146213, pr146213⟩
private theorem pr146221 : Nat.Prime 146221 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2437]) (by decide +kernel)
def pv146221 : PrimeValue := ⟨146221, pr146221⟩
private theorem pr146291 : Nat.Prime 146291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv14629]) (by decide +kernel)
def pv146291 : PrimeValue := ⟨146291, pr146291⟩
private theorem pr146297 : Nat.Prime 146297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv18287]) (by decide +kernel)
def pv146297 : PrimeValue := ⟨146297, pr146297⟩
private theorem pr146309 : Nat.Prime 146309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv463]) (by decide +kernel)
def pv146309 : PrimeValue := ⟨146309, pr146309⟩
private theorem pr146317 : Nat.Prime 146317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv89,pv137]) (by decide +kernel)
def pv146317 : PrimeValue := ⟨146317, pr146317⟩
private theorem pr146323 : Nat.Prime 146323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv739]) (by decide +kernel)
def pv146323 : PrimeValue := ⟨146323, pr146323⟩
private theorem pr146347 : Nat.Prime 146347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24391]) (by decide +kernel)
def pv146347 : PrimeValue := ⟨146347, pr146347⟩
private theorem pr146359 : Nat.Prime 146359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv173]) (by decide +kernel)
def pv146359 : PrimeValue := ⟨146359, pr146359⟩
private theorem pr146369 : Nat.Prime 146369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2287]) (by decide +kernel)
def pv146369 : PrimeValue := ⟨146369, pr146369⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
