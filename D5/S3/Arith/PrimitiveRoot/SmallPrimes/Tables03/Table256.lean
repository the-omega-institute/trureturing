/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables03/Table256
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables03/Table256.pv2128319
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table037
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table053
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table068
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table069
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table139

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr2128319 : Nat.Prime 2128319 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv1064159]) (by decide +kernel)
def pv2128319 : PrimeValue := ⟨2128319, pr2128319⟩
private theorem pr2128403 : Nat.Prime 2128403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1064201]) (by decide +kernel)
def pv2128403 : PrimeValue := ⟨2128403, pr2128403⟩
private theorem pr2128463 : Nat.Prime 2128463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv37,pv587]) (by decide +kernel)
def pv2128463 : PrimeValue := ⟨2128463, pr2128463⟩
private theorem pr2128481 : Nat.Prime 2128481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv53,pv251]) (by decide +kernel)
def pv2128481 : PrimeValue := ⟨2128481, pr2128481⟩
private theorem pr2128601 : Nat.Prime 2128601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv367]) (by decide +kernel)
def pv2128601 : PrimeValue := ⟨2128601, pr2128601⟩
private theorem pr2128733 : Nat.Prime 2128733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv532183]) (by decide +kernel)
def pv2128733 : PrimeValue := ⟨2128733, pr2128733⟩
private theorem pr2128751 : Nat.Prime 2128751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv131]) (by decide +kernel)
def pv2128751 : PrimeValue := ⟨2128751, pr2128751⟩
private theorem pr2128823 : Nat.Prime 2128823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv1064411]) (by decide +kernel)
def pv2128823 : PrimeValue := ⟨2128823, pr2128823⟩
private theorem pr2129051 : Nat.Prime 2129051 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv11,pv79]) (by decide +kernel)
def pv2129051 : PrimeValue := ⟨2129051, pr2129051⟩
private theorem pr2129069 : Nat.Prime 2129069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv532267]) (by decide +kernel)
def pv2129069 : PrimeValue := ⟨2129069, pr2129069⟩
private theorem pr2129321 : Nat.Prime 2129321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv53233]) (by decide +kernel)
def pv2129321 : PrimeValue := ⟨2129321, pr2129321⟩
private theorem pr2129579 : Nat.Prime 2129579 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv96799]) (by decide +kernel)
def pv2129579 : PrimeValue := ⟨2129579, pr2129579⟩
private theorem pr2129741 : Nat.Prime 2129741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv106487]) (by decide +kernel)
def pv2129741 : PrimeValue := ⟨2129741, pr2129741⟩
private theorem pr2129951 : Nat.Prime 2129951 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv41,pv1039]) (by decide +kernel)
def pv2129951 : PrimeValue := ⟨2129951, pr2129951⟩
private theorem pr2130239 : Nat.Prime 2130239 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv37,pv2617]) (by decide +kernel)
def pv2130239 : PrimeValue := ⟨2130239, pr2130239⟩
private theorem pr2130371 : Nat.Prime 2130371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv107,pv181]) (by decide +kernel)
def pv2130371 : PrimeValue := ⟨2130371, pr2130371⟩
private theorem pr2130539 : Nat.Prime 2130539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1065269]) (by decide +kernel)
def pv2130539 : PrimeValue := ⟨2130539, pr2130539⟩
private theorem pr2131133 : Nat.Prime 2131133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv532783]) (by decide +kernel)
def pv2131133 : PrimeValue := ⟨2131133, pr2131133⟩
private theorem pr2131193 : Nat.Prime 2131193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv2003]) (by decide +kernel)
def pv2131193 : PrimeValue := ⟨2131193, pr2131193⟩
private theorem pr2131319 : Nat.Prime 2131319 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv23,pv6619]) (by decide +kernel)
def pv2131319 : PrimeValue := ⟨2131319, pr2131319⟩
private theorem pr2131793 : Nat.Prime 2131793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv37,pv277]) (by decide +kernel)
def pv2131793 : PrimeValue := ⟨2131793, pr2131793⟩
private theorem pr2132033 : Nat.Prime 2132033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv4759]) (by decide +kernel)
def pv2132033 : PrimeValue := ⟨2132033, pr2132033⟩
private theorem pr2132129 : Nat.Prime 2132129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv66629]) (by decide +kernel)
def pv2132129 : PrimeValue := ⟨2132129, pr2132129⟩
private theorem pr2132153 : Nat.Prime 2132153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv24229]) (by decide +kernel)
def pv2132153 : PrimeValue := ⟨2132153, pr2132153⟩
private theorem pr2132309 : Nat.Prime 2132309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv533077]) (by decide +kernel)
def pv2132309 : PrimeValue := ⟨2132309, pr2132309⟩
private theorem pr2132411 : Nat.Prime 2132411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv41,pv743]) (by decide +kernel)
def pv2132411 : PrimeValue := ⟨2132411, pr2132411⟩
private theorem pr2132699 : Nat.Prime 2132699 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv23,pv71,pv653]) (by decide +kernel)
def pv2132699 : PrimeValue := ⟨2132699, pr2132699⟩
private theorem pr2132783 : Nat.Prime 2132783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv313,pv3407]) (by decide +kernel)
def pv2132783 : PrimeValue := ⟨2132783, pr2132783⟩
private theorem pr2132849 : Nat.Prime 2132849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv133303]) (by decide +kernel)
def pv2132849 : PrimeValue := ⟨2132849, pr2132849⟩
private theorem pr2132891 : Nat.Prime 2132891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv213289]) (by decide +kernel)
def pv2132891 : PrimeValue := ⟨2132891, pr2132891⟩
private theorem pr2133413 : Nat.Prime 2133413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv533353]) (by decide +kernel)
def pv2133413 : PrimeValue := ⟨2133413, pr2133413⟩
private theorem pr2133539 : Nat.Prime 2133539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv96979]) (by decide +kernel)
def pv2133539 : PrimeValue := ⟨2133539, pr2133539⟩
private theorem pr2133713 : Nat.Prime 2133713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv19051]) (by decide +kernel)
def pv2133713 : PrimeValue := ⟨2133713, pr2133713⟩
private theorem pr2134019 : Nat.Prime 2134019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1067009]) (by decide +kernel)
def pv2134019 : PrimeValue := ⟨2134019, pr2134019⟩
private theorem pr2134109 : Nat.Prime 2134109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127,pv4201]) (by decide +kernel)
def pv2134109 : PrimeValue := ⟨2134109, pr2134109⟩
private theorem pr2134589 : Nat.Prime 2134589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv31391]) (by decide +kernel)
def pv2134589 : PrimeValue := ⟨2134589, pr2134589⟩
private theorem pr2134943 : Nat.Prime 2134943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv1067471]) (by decide +kernel)
def pv2134943 : PrimeValue := ⟨2134943, pr2134943⟩
private theorem pr2134949 : Nat.Prime 2134949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv533737]) (by decide +kernel)
def pv2134949 : PrimeValue := ⟨2134949, pr2134949⟩
private theorem pr2134991 : Nat.Prime 2134991 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv11,pv13,pv1493]) (by decide +kernel)
def pv2134991 : PrimeValue := ⟨2134991, pr2134991⟩
private theorem pr2135051 : Nat.Prime 2135051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv42701]) (by decide +kernel)
def pv2135051 : PrimeValue := ⟨2135051, pr2135051⟩
private theorem pr2135099 : Nat.Prime 2135099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv8971]) (by decide +kernel)
def pv2135099 : PrimeValue := ⟨2135099, pr2135099⟩
private theorem pr2135141 : Nat.Prime 2135141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv101,pv151]) (by decide +kernel)
def pv2135141 : PrimeValue := ⟨2135141, pr2135141⟩
private theorem pr2135279 : Nat.Prime 2135279 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv1067639]) (by decide +kernel)
def pv2135279 : PrimeValue := ⟨2135279, pr2135279⟩
private theorem pr2135333 : Nat.Prime 2135333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv359,pv1487]) (by decide +kernel)
def pv2135333 : PrimeValue := ⟨2135333, pr2135333⟩
private theorem pr2135453 : Nat.Prime 2135453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv48533]) (by decide +kernel)
def pv2135453 : PrimeValue := ⟨2135453, pr2135453⟩
private theorem pr2135519 : Nat.Prime 2135519 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv7,pv11,pv283]) (by decide +kernel)
def pv2135519 : PrimeValue := ⟨2135519, pr2135519⟩
private theorem pr2135663 : Nat.Prime 2135663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv1067831]) (by decide +kernel)
def pv2135663 : PrimeValue := ⟨2135663, pr2135663⟩
private theorem pr2135921 : Nat.Prime 2135921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv26699]) (by decide +kernel)
def pv2135921 : PrimeValue := ⟨2135921, pr2135921⟩
private theorem pr2136083 : Nat.Prime 2136083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv29,pv2833]) (by decide +kernel)
def pv2136083 : PrimeValue := ⟨2136083, pr2136083⟩
private theorem pr2136119 : Nat.Prime 2136119 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv17,pv62827]) (by decide +kernel)
def pv2136119 : PrimeValue := ⟨2136119, pr2136119⟩
private theorem pr2136131 : Nat.Prime 2136131 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv213613]) (by decide +kernel)
def pv2136131 : PrimeValue := ⟨2136131, pr2136131⟩
private theorem pr2136209 : Nat.Prime 2136209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv7027]) (by decide +kernel)
def pv2136209 : PrimeValue := ⟨2136209, pr2136209⟩
private theorem pr2136353 : Nat.Prime 2136353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv101,pv661]) (by decide +kernel)
def pv2136353 : PrimeValue := ⟨2136353, pr2136353⟩
private theorem pr2136371 : Nat.Prime 2136371 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv213637]) (by decide +kernel)
def pv2136371 : PrimeValue := ⟨2136371, pr2136371⟩
private theorem pr2136383 : Nat.Prime 2136383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv1068191]) (by decide +kernel)
def pv2136383 : PrimeValue := ⟨2136383, pr2136383⟩
private theorem pr2136593 : Nat.Prime 2136593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv3257]) (by decide +kernel)
def pv2136593 : PrimeValue := ⟨2136593, pr2136593⟩
private theorem pr2136833 : Nat.Prime 2136833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv491]) (by decide +kernel)
def pv2136833 : PrimeValue := ⟨2136833, pr2136833⟩
private theorem pr2136839 : Nat.Prime 2136839 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv23,pv41,pv103]) (by decide +kernel)
def pv2136839 : PrimeValue := ⟨2136839, pr2136839⟩
private theorem pr2136983 : Nat.Prime 2136983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv1068491]) (by decide +kernel)
def pv2136983 : PrimeValue := ⟨2136983, pr2136983⟩
private theorem pr2137049 : Nat.Prime 2137049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv267131]) (by decide +kernel)
def pv2137049 : PrimeValue := ⟨2137049, pr2137049⟩
private theorem pr2137073 : Nat.Prime 2137073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19081]) (by decide +kernel)
def pv2137073 : PrimeValue := ⟨2137073, pr2137073⟩
private theorem pr2137211 : Nat.Prime 2137211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv213721]) (by decide +kernel)
def pv2137211 : PrimeValue := ⟨2137211, pr2137211⟩
private theorem pr2138033 : Nat.Prime 2138033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv19,pv541]) (by decide +kernel)
def pv2138033 : PrimeValue := ⟨2138033, pr2138033⟩
private theorem pr2138249 : Nat.Prime 2138249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv38183]) (by decide +kernel)
def pv2138249 : PrimeValue := ⟨2138249, pr2138249⟩
private theorem pr2138291 : Nat.Prime 2138291 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv11,pv2777]) (by decide +kernel)
def pv2138291 : PrimeValue := ⟨2138291, pr2138291⟩
private theorem pr2138399 : Nat.Prime 2138399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv1069199]) (by decide +kernel)
def pv2138399 : PrimeValue := ⟨2138399, pr2138399⟩
private theorem pr2138483 : Nat.Prime 2138483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv317,pv3373]) (by decide +kernel)
def pv2138483 : PrimeValue := ⟨2138483, pr2138483⟩
private theorem pr2138789 : Nat.Prime 2138789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv534697]) (by decide +kernel)
def pv2138789 : PrimeValue := ⟨2138789, pr2138789⟩
private theorem pr2138861 : Nat.Prime 2138861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv229,pv467]) (by decide +kernel)
def pv2138861 : PrimeValue := ⟨2138861, pr2138861⟩
private theorem pr2138879 : Nat.Prime 2138879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv152777]) (by decide +kernel)
def pv2138879 : PrimeValue := ⟨2138879, pr2138879⟩
private theorem pr2139233 : Nat.Prime 2139233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv66851]) (by decide +kernel)
def pv2139233 : PrimeValue := ⟨2139233, pr2139233⟩
private theorem pr2139521 : Nat.Prime 2139521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3343]) (by decide +kernel)
def pv2139521 : PrimeValue := ⟨2139521, pr2139521⟩
private theorem pr2139743 : Nat.Prime 2139743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv19,pv5119]) (by decide +kernel)
def pv2139743 : PrimeValue := ⟨2139743, pr2139743⟩
private theorem pr2140091 : Nat.Prime 2140091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv214009]) (by decide +kernel)
def pv2140091 : PrimeValue := ⟨2140091, pr2140091⟩
private theorem pr2140199 : Nat.Prime 2140199 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv17,pv19,pv3313]) (by decide +kernel)
def pv2140199 : PrimeValue := ⟨2140199, pr2140199⟩
private theorem pr2140601 : Nat.Prime 2140601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv139]) (by decide +kernel)
def pv2140601 : PrimeValue := ⟨2140601, pr2140601⟩
private theorem pr2140769 : Nat.Prime 2140769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv503]) (by decide +kernel)
def pv2140769 : PrimeValue := ⟨2140769, pr2140769⟩
private theorem pr2141159 : Nat.Prime 2141159 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv1070579]) (by decide +kernel)
def pv2141159 : PrimeValue := ⟨2141159, pr2141159⟩
private theorem pr2141189 : Nat.Prime 2141189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv76471]) (by decide +kernel)
def pv2141189 : PrimeValue := ⟨2141189, pr2141189⟩
private theorem pr2141543 : Nat.Prime 2141543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv31,pv2657]) (by decide +kernel)
def pv2141543 : PrimeValue := ⟨2141543, pr2141543⟩
private theorem pr2141591 : Nat.Prime 2141591 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv19469]) (by decide +kernel)
def pv2141591 : PrimeValue := ⟨2141591, pr2141591⟩
private theorem pr2142149 : Nat.Prime 2142149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv5521]) (by decide +kernel)
def pv2142149 : PrimeValue := ⟨2142149, pr2142149⟩
private theorem pr2142251 : Nat.Prime 2142251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv19,pv41]) (by decide +kernel)
def pv2142251 : PrimeValue := ⟨2142251, pr2142251⟩
private theorem pr2142713 : Nat.Prime 2142713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13,pv1873]) (by decide +kernel)
def pv2142713 : PrimeValue := ⟨2142713, pr2142713⟩
private theorem pr2142923 : Nat.Prime 2142923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv15091]) (by decide +kernel)
def pv2142923 : PrimeValue := ⟨2142923, pr2142923⟩
private theorem pr2143073 : Nat.Prime 2143073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv193,pv347]) (by decide +kernel)
def pv2143073 : PrimeValue := ⟨2143073, pr2143073⟩
private theorem pr2143331 : Nat.Prime 2143331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv67,pv457]) (by decide +kernel)
def pv2143331 : PrimeValue := ⟨2143331, pr2143331⟩
private theorem pr2143451 : Nat.Prime 2143451 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv163,pv263]) (by decide +kernel)
def pv2143451 : PrimeValue := ⟨2143451, pr2143451⟩
private theorem pr2143733 : Nat.Prime 2143733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv67,pv421]) (by decide +kernel)
def pv2143733 : PrimeValue := ⟨2143733, pr2143733⟩
private theorem pr2143859 : Nat.Prime 2143859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv22807]) (by decide +kernel)
def pv2143859 : PrimeValue := ⟨2143859, pr2143859⟩
private theorem pr2143943 : Nat.Prime 2143943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv59,pv18169]) (by decide +kernel)
def pv2143943 : PrimeValue := ⟨2143943, pr2143943⟩
private theorem pr2144063 : Nat.Prime 2144063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv113,pv179]) (by decide +kernel)
def pv2144063 : PrimeValue := ⟨2144063, pr2144063⟩
private theorem pr2144309 : Nat.Prime 2144309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv239,pv2243]) (by decide +kernel)
def pv2144309 : PrimeValue := ⟨2144309, pr2144309⟩
private theorem pr2144399 : Nat.Prime 2144399 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv1072199]) (by decide +kernel)
def pv2144399 : PrimeValue := ⟨2144399, pr2144399⟩
private theorem pr2144489 : Nat.Prime 2144489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv181,pv1481]) (by decide +kernel)
def pv2144489 : PrimeValue := ⟨2144489, pr2144489⟩
private theorem pr2144801 : Nat.Prime 2144801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv383]) (by decide +kernel)
def pv2144801 : PrimeValue := ⟨2144801, pr2144801⟩
private theorem pr2145023 : Nat.Prime 2145023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv97501]) (by decide +kernel)
def pv2145023 : PrimeValue := ⟨2145023, pr2145023⟩
private theorem pr2145089 : Nat.Prime 2145089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv277]) (by decide +kernel)
def pv2145089 : PrimeValue := ⟨2145089, pr2145089⟩
private theorem pr2145443 : Nat.Prime 2145443 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv19,pv43,pv101]) (by decide +kernel)
def pv2145443 : PrimeValue := ⟨2145443, pr2145443⟩
private theorem pr2145551 : Nat.Prime 2145551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv47,pv83]) (by decide +kernel)
def pv2145551 : PrimeValue := ⟨2145551, pr2145551⟩
private theorem pr2145779 : Nat.Prime 2145779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv107,pv271]) (by decide +kernel)
def pv2145779 : PrimeValue := ⟨2145779, pr2145779⟩
private theorem pr2146169 : Nat.Prime 2146169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv268271]) (by decide +kernel)
def pv2146169 : PrimeValue := ⟨2146169, pr2146169⟩
private theorem pr2146181 : Nat.Prime 2146181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv107309]) (by decide +kernel)
def pv2146181 : PrimeValue := ⟨2146181, pr2146181⟩
private theorem pr2146253 : Nat.Prime 2146253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv536563]) (by decide +kernel)
def pv2146253 : PrimeValue := ⟨2146253, pr2146253⟩
private theorem pr2146283 : Nat.Prime 2146283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1073141]) (by decide +kernel)
def pv2146283 : PrimeValue := ⟨2146283, pr2146283⟩
private theorem pr2146289 : Nat.Prime 2146289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53,pv2531]) (by decide +kernel)
def pv2146289 : PrimeValue := ⟨2146289, pr2146289⟩
private theorem pr2146433 : Nat.Prime 2146433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv409]) (by decide +kernel)
def pv2146433 : PrimeValue := ⟨2146433, pr2146433⟩
private theorem pr2146619 : Nat.Prime 2146619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv167,pv6427]) (by decide +kernel)
def pv2146619 : PrimeValue := ⟨2146619, pr2146619⟩
private theorem pr2146673 : Nat.Prime 2146673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv12197]) (by decide +kernel)
def pv2146673 : PrimeValue := ⟨2146673, pr2146673⟩
private theorem pr2147081 : Nat.Prime 2147081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv4129]) (by decide +kernel)
def pv2147081 : PrimeValue := ⟨2147081, pr2147081⟩
private theorem pr2147273 : Nat.Prime 2147273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv139,pv1931]) (by decide +kernel)
def pv2147273 : PrimeValue := ⟨2147273, pr2147273⟩
private theorem pr2147279 : Nat.Prime 2147279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv21911]) (by decide +kernel)
def pv2147279 : PrimeValue := ⟨2147279, pr2147279⟩
private theorem pr2147753 : Nat.Prime 2147753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv67,pv4007]) (by decide +kernel)
def pv2147753 : PrimeValue := ⟨2147753, pr2147753⟩
private theorem pr2147861 : Nat.Prime 2147861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv751]) (by decide +kernel)
def pv2147861 : PrimeValue := ⟨2147861, pr2147861⟩
private theorem pr2148011 : Nat.Prime 2148011 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv79,pv2719]) (by decide +kernel)
def pv2148011 : PrimeValue := ⟨2148011, pr2148011⟩
private theorem pr2148449 : Nat.Prime 2148449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv67139]) (by decide +kernel)
def pv2148449 : PrimeValue := ⟨2148449, pr2148449⟩
private theorem pr2148599 : Nat.Prime 2148599 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv1074299]) (by decide +kernel)
def pv2148599 : PrimeValue := ⟨2148599, pr2148599⟩
private theorem pr2148761 : Nat.Prime 2148761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv53719]) (by decide +kernel)
def pv2148761 : PrimeValue := ⟨2148761, pr2148761⟩
private theorem pr2149139 : Nat.Prime 2149139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv26209]) (by decide +kernel)
def pv2149139 : PrimeValue := ⟨2149139, pr2149139⟩
private theorem pr2149211 : Nat.Prime 2149211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv30703]) (by decide +kernel)
def pv2149211 : PrimeValue := ⟨2149211, pr2149211⟩
private theorem pr2149331 : Nat.Prime 2149331 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv37,pv157]) (by decide +kernel)
def pv2149331 : PrimeValue := ⟨2149331, pr2149331⟩
private theorem pr2149379 : Nat.Prime 2149379 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv11,pv17,pv821]) (by decide +kernel)
def pv2149379 : PrimeValue := ⟨2149379, pr2149379⟩
private theorem pr2149391 : Nat.Prime 2149391 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv214939]) (by decide +kernel)
def pv2149391 : PrimeValue := ⟨2149391, pr2149391⟩
private theorem pr2149421 : Nat.Prime 2149421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv1181]) (by decide +kernel)
def pv2149421 : PrimeValue := ⟨2149421, pr2149421⟩
private theorem pr2149781 : Nat.Prime 2149781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv2287]) (by decide +kernel)
def pv2149781 : PrimeValue := ⟨2149781, pr2149781⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
