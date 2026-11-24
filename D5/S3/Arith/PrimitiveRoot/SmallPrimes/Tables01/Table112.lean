/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table112
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table112.pv515653
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table077
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table078

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr515653 : Nat.Prime 515653 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv97,pv443]) (by decide +kernel)
def pv515653 : PrimeValue := ⟨515653, pr515653⟩
private theorem pr515687 : Nat.Prime 515687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv401,pv643]) (by decide +kernel)
def pv515687 : PrimeValue := ⟨515687, pr515687⟩
private theorem pr515737 : Nat.Prime 515737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv29]) (by decide +kernel)
def pv515737 : PrimeValue := ⟨515737, pr515737⟩
private theorem pr515741 : Nat.Prime 515741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv107,pv241]) (by decide +kernel)
def pv515741 : PrimeValue := ⟨515741, pr515741⟩
private theorem pr515803 : Nat.Prime 515803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv12281]) (by decide +kernel)
def pv515803 : PrimeValue := ⟨515803, pr515803⟩
private theorem pr515857 : Nat.Prime 515857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv977]) (by decide +kernel)
def pv515857 : PrimeValue := ⟨515857, pr515857⟩
private theorem pr515887 : Nat.Prime 515887 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv71,pv173]) (by decide +kernel)
def pv515887 : PrimeValue := ⟨515887, pr515887⟩
private theorem pr515917 : Nat.Prime 515917 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv281]) (by decide +kernel)
def pv515917 : PrimeValue := ⟨515917, pr515917⟩
private theorem pr515923 : Nat.Prime 515923 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv7817]) (by decide +kernel)
def pv515923 : PrimeValue := ⟨515923, pr515923⟩
private theorem pr515941 : Nat.Prime 515941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv8599]) (by decide +kernel)
def pv515941 : PrimeValue := ⟨515941, pr515941⟩
private theorem pr515951 : Nat.Prime 515951 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv607]) (by decide +kernel)
def pv515951 : PrimeValue := ⟨515951, pr515951⟩
private theorem pr515993 : Nat.Prime 515993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv64499]) (by decide +kernel)
def pv515993 : PrimeValue := ⟨515993, pr515993⟩
private theorem pr516017 : Nat.Prime 516017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv32251]) (by decide +kernel)
def pv516017 : PrimeValue := ⟨516017, pr516017⟩
private theorem pr516023 : Nat.Prime 516023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv89,pv223]) (by decide +kernel)
def pv516023 : PrimeValue := ⟨516023, pr516023⟩
private theorem pr516053 : Nat.Prime 516053 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv7589]) (by decide +kernel)
def pv516053 : PrimeValue := ⟨516053, pr516053⟩
private theorem pr516077 : Nat.Prime 516077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv37,pv317]) (by decide +kernel)
def pv516077 : PrimeValue := ⟨516077, pr516077⟩
private theorem pr516091 : Nat.Prime 516091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17203]) (by decide +kernel)
def pv516091 : PrimeValue := ⟨516091, pr516091⟩
private theorem pr516161 : Nat.Prime 516161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1613]) (by decide +kernel)
def pv516161 : PrimeValue := ⟨516161, pr516161⟩
private theorem pr516163 : Nat.Prime 516163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv86027]) (by decide +kernel)
def pv516163 : PrimeValue := ⟨516163, pr516163⟩
private theorem pr516209 : Nat.Prime 516209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv419]) (by decide +kernel)
def pv516209 : PrimeValue := ⟨516209, pr516209⟩
private theorem pr516227 : Nat.Prime 516227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv258113]) (by decide +kernel)
def pv516227 : PrimeValue := ⟨516227, pr516227⟩
private theorem pr516233 : Nat.Prime 516233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv173,pv373]) (by decide +kernel)
def pv516233 : PrimeValue := ⟨516233, pr516233⟩
private theorem pr516247 : Nat.Prime 516247 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv139,pv619]) (by decide +kernel)
def pv516247 : PrimeValue := ⟨516247, pr516247⟩
private theorem pr516349 : Nat.Prime 516349 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv683]) (by decide +kernel)
def pv516349 : PrimeValue := ⟨516349, pr516349⟩
private theorem pr516407 : Nat.Prime 516407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv23473]) (by decide +kernel)
def pv516407 : PrimeValue := ⟨516407, pr516407⟩
private theorem pr516433 : Nat.Prime 516433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv29,pv53]) (by decide +kernel)
def pv516433 : PrimeValue := ⟨516433, pr516433⟩
private theorem pr516457 : Nat.Prime 516457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv797]) (by decide +kernel)
def pv516457 : PrimeValue := ⟨516457, pr516457⟩
private theorem pr516493 : Nat.Prime 516493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14347]) (by decide +kernel)
def pv516493 : PrimeValue := ⟨516493, pr516493⟩
private theorem pr516499 : Nat.Prime 516499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv86083]) (by decide +kernel)
def pv516499 : PrimeValue := ⟨516499, pr516499⟩
private theorem pr516517 : Nat.Prime 516517 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv13,pv43]) (by decide +kernel)
def pv516517 : PrimeValue := ⟨516517, pr516517⟩
private theorem pr516521 : Nat.Prime 516521 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv37,pv349]) (by decide +kernel)
def pv516521 : PrimeValue := ⟨516521, pr516521⟩
private theorem pr516539 : Nat.Prime 516539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv53,pv443]) (by decide +kernel)
def pv516539 : PrimeValue := ⟨516539, pr516539⟩
private theorem pr516563 : Nat.Prime 516563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv15193]) (by decide +kernel)
def pv516563 : PrimeValue := ⟨516563, pr516563⟩
private theorem pr516611 : Nat.Prime 516611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv2719]) (by decide +kernel)
def pv516611 : PrimeValue := ⟨516611, pr516611⟩
private theorem pr516673 : Nat.Prime 516673 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv23]) (by decide +kernel)
def pv516673 : PrimeValue := ⟨516673, pr516673⟩
private theorem pr516679 : Nat.Prime 516679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv86113]) (by decide +kernel)
def pv516679 : PrimeValue := ⟨516679, pr516679⟩
private theorem pr516713 : Nat.Prime 516713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv9227]) (by decide +kernel)
def pv516713 : PrimeValue := ⟨516713, pr516713⟩
private theorem pr516721 : Nat.Prime 516721 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv2153]) (by decide +kernel)
def pv516721 : PrimeValue := ⟨516721, pr516721⟩
private theorem pr516821 : Nat.Prime 516821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv25841]) (by decide +kernel)
def pv516821 : PrimeValue := ⟨516821, pr516821⟩
private theorem pr516839 : Nat.Prime 516839 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv19,pv29,pv67]) (by decide +kernel)
def pv516839 : PrimeValue := ⟨516839, pr516839⟩
private theorem pr516883 : Nat.Prime 516883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv277,pv311]) (by decide +kernel)
def pv516883 : PrimeValue := ⟨516883, pr516883⟩
private theorem pr516949 : Nat.Prime 516949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv1873]) (by decide +kernel)
def pv516949 : PrimeValue := ⟨516949, pr516949⟩
private theorem pr516977 : Nat.Prime 516977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79,pv409]) (by decide +kernel)
def pv516977 : PrimeValue := ⟨516977, pr516977⟩
private theorem pr516991 : Nat.Prime 516991 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv19,pv907]) (by decide +kernel)
def pv516991 : PrimeValue := ⟨516991, pr516991⟩
private theorem pr517043 : Nat.Prime 517043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv258521]) (by decide +kernel)
def pv517043 : PrimeValue := ⟨517043, pr517043⟩
private theorem pr517061 : Nat.Prime 517061 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv103,pv251]) (by decide +kernel)
def pv517061 : PrimeValue := ⟨517061, pr517061⟩
private theorem pr517073 : Nat.Prime 517073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv1901]) (by decide +kernel)
def pv517073 : PrimeValue := ⟨517073, pr517073⟩
private theorem pr517087 : Nat.Prime 517087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv1249]) (by decide +kernel)
def pv517087 : PrimeValue := ⟨517087, pr517087⟩
private theorem pr517091 : Nat.Prime 517091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv83,pv89]) (by decide +kernel)
def pv517091 : PrimeValue := ⟨517091, pr517091⟩
private theorem pr517169 : Nat.Prime 517169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv32323]) (by decide +kernel)
def pv517169 : PrimeValue := ⟨517169, pr517169⟩
private theorem pr517177 : Nat.Prime 517177 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv653]) (by decide +kernel)
def pv517177 : PrimeValue := ⟨517177, pr517177⟩
private theorem pr517189 : Nat.Prime 517189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv47,pv131]) (by decide +kernel)
def pv517189 : PrimeValue := ⟨517189, pr517189⟩
private theorem pr517243 : Nat.Prime 517243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv461]) (by decide +kernel)
def pv517243 : PrimeValue := ⟨517243, pr517243⟩
private theorem pr517267 : Nat.Prime 517267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv103]) (by decide +kernel)
def pv517267 : PrimeValue := ⟨517267, pr517267⟩
private theorem pr517303 : Nat.Prime 517303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv991]) (by decide +kernel)
def pv517303 : PrimeValue := ⟨517303, pr517303⟩
private theorem pr517417 : Nat.Prime 517417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv21559]) (by decide +kernel)
def pv517417 : PrimeValue := ⟨517417, pr517417⟩
private theorem pr517481 : Nat.Prime 517481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv761]) (by decide +kernel)
def pv517481 : PrimeValue := ⟨517481, pr517481⟩
private theorem pr517501 : Nat.Prime 517501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv517501 : PrimeValue := ⟨517501, pr517501⟩
private theorem pr517513 : Nat.Prime 517513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv21563]) (by decide +kernel)
def pv517513 : PrimeValue := ⟨517513, pr517513⟩
private theorem pr517547 : Nat.Prime 517547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv11251]) (by decide +kernel)
def pv517547 : PrimeValue := ⟨517547, pr517547⟩
private theorem pr517553 : Nat.Prime 517553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv4621]) (by decide +kernel)
def pv517553 : PrimeValue := ⟨517553, pr517553⟩
private theorem pr517733 : Nat.Prime 517733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv1823]) (by decide +kernel)
def pv517733 : PrimeValue := ⟨517733, pr517733⟩
private theorem pr517739 : Nat.Prime 517739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv19913]) (by decide +kernel)
def pv517739 : PrimeValue := ⟨517739, pr517739⟩
private theorem pr517873 : Nat.Prime 517873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv10789]) (by decide +kernel)
def pv517873 : PrimeValue := ⟨517873, pr517873⟩
private theorem pr517967 : Nat.Prime 517967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv258983]) (by decide +kernel)
def pv517967 : PrimeValue := ⟨517967, pr517967⟩
private theorem pr517991 : Nat.Prime 517991 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv17,pv277]) (by decide +kernel)
def pv517991 : PrimeValue := ⟨517991, pr517991⟩
private theorem pr517999 : Nat.Prime 517999 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv29,pv229]) (by decide +kernel)
def pv517999 : PrimeValue := ⟨517999, pr517999⟩
private theorem pr518017 : Nat.Prime 518017 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv71]) (by decide +kernel)
def pv518017 : PrimeValue := ⟨518017, pr518017⟩
private theorem pr518047 : Nat.Prime 518047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv86341]) (by decide +kernel)
def pv518047 : PrimeValue := ⟨518047, pr518047⟩
private theorem pr518101 : Nat.Prime 518101 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv5,pv11,pv157]) (by decide +kernel)
def pv518101 : PrimeValue := ⟨518101, pr518101⟩
private theorem pr518123 : Nat.Prime 518123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv2141]) (by decide +kernel)
def pv518123 : PrimeValue := ⟨518123, pr518123⟩
private theorem pr518137 : Nat.Prime 518137 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv21589]) (by decide +kernel)
def pv518137 : PrimeValue := ⟨518137, pr518137⟩
private theorem pr518153 : Nat.Prime 518153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv239,pv271]) (by decide +kernel)
def pv518153 : PrimeValue := ⟨518153, pr518153⟩
private theorem pr518159 : Nat.Prime 518159 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv41,pv71,pv89]) (by decide +kernel)
def pv518159 : PrimeValue := ⟨518159, pr518159⟩
private theorem pr518233 : Nat.Prime 518233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv151]) (by decide +kernel)
def pv518233 : PrimeValue := ⟨518233, pr518233⟩
private theorem pr518249 : Nat.Prime 518249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv64781]) (by decide +kernel)
def pv518249 : PrimeValue := ⟨518249, pr518249⟩
private theorem pr518291 : Nat.Prime 518291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv51829]) (by decide +kernel)
def pv518291 : PrimeValue := ⟨518291, pr518291⟩
private theorem pr518311 : Nat.Prime 518311 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv443]) (by decide +kernel)
def pv518311 : PrimeValue := ⟨518311, pr518311⟩
private theorem pr518447 : Nat.Prime 518447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv67,pv73]) (by decide +kernel)
def pv518447 : PrimeValue := ⟨518447, pr518447⟩
private theorem pr518467 : Nat.Prime 518467 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv23]) (by decide +kernel)
def pv518467 : PrimeValue := ⟨518467, pr518467⟩
private theorem pr518471 : Nat.Prime 518471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv139,pv373]) (by decide +kernel)
def pv518471 : PrimeValue := ⟨518471, pr518471⟩
private theorem pr518473 : Nat.Prime 518473 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv379]) (by decide +kernel)
def pv518473 : PrimeValue := ⟨518473, pr518473⟩
private theorem pr518543 : Nat.Prime 518543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv259271]) (by decide +kernel)
def pv518543 : PrimeValue := ⟨518543, pr518543⟩
private theorem pr518587 : Nat.Prime 518587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv4549]) (by decide +kernel)
def pv518587 : PrimeValue := ⟨518587, pr518587⟩
private theorem pr518621 : Nat.Prime 518621 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv25931]) (by decide +kernel)
def pv518621 : PrimeValue := ⟨518621, pr518621⟩
private theorem pr518717 : Nat.Prime 518717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv11789]) (by decide +kernel)
def pv518717 : PrimeValue := ⟨518717, pr518717⟩
private theorem pr518737 : Nat.Prime 518737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv101,pv107]) (by decide +kernel)
def pv518737 : PrimeValue := ⟨518737, pr518737⟩
private theorem pr518801 : Nat.Prime 518801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1297]) (by decide +kernel)
def pv518801 : PrimeValue := ⟨518801, pr518801⟩
private theorem pr518813 : Nat.Prime 518813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2647]) (by decide +kernel)
def pv518813 : PrimeValue := ⟨518813, pr518813⟩
private theorem pr518831 : Nat.Prime 518831 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv307]) (by decide +kernel)
def pv518831 : PrimeValue := ⟨518831, pr518831⟩
private theorem pr518863 : Nat.Prime 518863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv86477]) (by decide +kernel)
def pv518863 : PrimeValue := ⟨518863, pr518863⟩
private theorem pr518893 : Nat.Prime 518893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv3931]) (by decide +kernel)
def pv518893 : PrimeValue := ⟨518893, pr518893⟩
private theorem pr518953 : Nat.Prime 518953 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv3089]) (by decide +kernel)
def pv518953 : PrimeValue := ⟨518953, pr518953⟩
private theorem pr518981 : Nat.Prime 518981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv337]) (by decide +kernel)
def pv518981 : PrimeValue := ⟨518981, pr518981⟩
private theorem pr518983 : Nat.Prime 518983 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv67,pv1291]) (by decide +kernel)
def pv518983 : PrimeValue := ⟨518983, pr518983⟩
private theorem pr519067 : Nat.Prime 519067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv28837]) (by decide +kernel)
def pv519067 : PrimeValue := ⟨519067, pr519067⟩
private theorem pr519131 : Nat.Prime 519131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv51913]) (by decide +kernel)
def pv519131 : PrimeValue := ⟨519131, pr519131⟩
private theorem pr519161 : Nat.Prime 519161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv12979]) (by decide +kernel)
def pv519161 : PrimeValue := ⟨519161, pr519161⟩
private theorem pr519217 : Nat.Prime 519217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv373]) (by decide +kernel)
def pv519217 : PrimeValue := ⟨519217, pr519217⟩
private theorem pr519229 : Nat.Prime 519229 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv14423]) (by decide +kernel)
def pv519229 : PrimeValue := ⟨519229, pr519229⟩
private theorem pr519269 : Nat.Prime 519269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv3019]) (by decide +kernel)
def pv519269 : PrimeValue := ⟨519269, pr519269⟩
private theorem pr519283 : Nat.Prime 519283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv1697]) (by decide +kernel)
def pv519283 : PrimeValue := ⟨519283, pr519283⟩
private theorem pr519353 : Nat.Prime 519353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv64919]) (by decide +kernel)
def pv519353 : PrimeValue := ⟨519353, pr519353⟩
private theorem pr519371 : Nat.Prime 519371 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv167,pv311]) (by decide +kernel)
def pv519371 : PrimeValue := ⟨519371, pr519371⟩
private theorem pr519383 : Nat.Prime 519383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv259691]) (by decide +kernel)
def pv519383 : PrimeValue := ⟨519383, pr519383⟩
private theorem pr519413 : Nat.Prime 519413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv129853]) (by decide +kernel)
def pv519413 : PrimeValue := ⟨519413, pr519413⟩
private theorem pr519427 : Nat.Prime 519427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9619]) (by decide +kernel)
def pv519427 : PrimeValue := ⟨519427, pr519427⟩
private theorem pr519487 : Nat.Prime 519487 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv463]) (by decide +kernel)
def pv519487 : PrimeValue := ⟨519487, pr519487⟩
private theorem pr519499 : Nat.Prime 519499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv31]) (by decide +kernel)
def pv519499 : PrimeValue := ⟨519499, pr519499⟩
private theorem pr519521 : Nat.Prime 519521 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv191]) (by decide +kernel)
def pv519521 : PrimeValue := ⟨519521, pr519521⟩
private theorem pr519523 : Nat.Prime 519523 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv86587]) (by decide +kernel)
def pv519523 : PrimeValue := ⟨519523, pr519523⟩
private theorem pr519577 : Nat.Prime 519577 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv21649]) (by decide +kernel)
def pv519577 : PrimeValue := ⟨519577, pr519577⟩
private theorem pr519581 : Nat.Prime 519581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv83,pv313]) (by decide +kernel)
def pv519581 : PrimeValue := ⟨519581, pr519581⟩
private theorem pr519587 : Nat.Prime 519587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv239,pv1087]) (by decide +kernel)
def pv519587 : PrimeValue := ⟨519587, pr519587⟩
private theorem pr519683 : Nat.Prime 519683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv259841]) (by decide +kernel)
def pv519683 : PrimeValue := ⟨519683, pr519683⟩
private theorem pr519713 : Nat.Prime 519713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv109,pv149]) (by decide +kernel)
def pv519713 : PrimeValue := ⟨519713, pr519713⟩
private theorem pr519733 : Nat.Prime 519733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14437]) (by decide +kernel)
def pv519733 : PrimeValue := ⟨519733, pr519733⟩
private theorem pr519787 : Nat.Prime 519787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv431]) (by decide +kernel)
def pv519787 : PrimeValue := ⟨519787, pr519787⟩
private theorem pr519793 : Nat.Prime 519793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv519793 : PrimeValue := ⟨519793, pr519793⟩
private theorem pr519803 : Nat.Prime 519803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv13679]) (by decide +kernel)
def pv519803 : PrimeValue := ⟨519803, pr519803⟩
private theorem pr519881 : Nat.Prime 519881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv41,pv317]) (by decide +kernel)
def pv519881 : PrimeValue := ⟨519881, pr519881⟩
private theorem pr519889 : Nat.Prime 519889 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv10831]) (by decide +kernel)
def pv519889 : PrimeValue := ⟨519889, pr519889⟩
private theorem pr519907 : Nat.Prime 519907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73,pv1187]) (by decide +kernel)
def pv519907 : PrimeValue := ⟨519907, pr519907⟩
private theorem pr519943 : Nat.Prime 519943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv193,pv449]) (by decide +kernel)
def pv519943 : PrimeValue := ⟨519943, pr519943⟩
private theorem pr519971 : Nat.Prime 519971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv29,pv163]) (by decide +kernel)
def pv519971 : PrimeValue := ⟨519971, pr519971⟩
private theorem pr519989 : Nat.Prime 519989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv379]) (by decide +kernel)
def pv519989 : PrimeValue := ⟨519989, pr519989⟩
private theorem pr520021 : Nat.Prime 520021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv520021 : PrimeValue := ⟨520021, pr520021⟩
private theorem pr520103 : Nat.Prime 520103 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv47,pv503]) (by decide +kernel)
def pv520103 : PrimeValue := ⟨520103, pr520103⟩
private theorem pr520151 : Nat.Prime 520151 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv101,pv103]) (by decide +kernel)
def pv520151 : PrimeValue := ⟨520151, pr520151⟩
private theorem pr520193 : Nat.Prime 520193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv127]) (by decide +kernel)
def pv520193 : PrimeValue := ⟨520193, pr520193⟩
private theorem pr520241 : Nat.Prime 520241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv929]) (by decide +kernel)
def pv520241 : PrimeValue := ⟨520241, pr520241⟩
private theorem pr520291 : Nat.Prime 520291 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv41,pv47]) (by decide +kernel)
def pv520291 : PrimeValue := ⟨520291, pr520291⟩
private theorem pr520309 : Nat.Prime 520309 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv97,pv149]) (by decide +kernel)
def pv520309 : PrimeValue := ⟨520309, pr520309⟩
private theorem pr520357 : Nat.Prime 520357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103,pv421]) (by decide +kernel)
def pv520357 : PrimeValue := ⟨520357, pr520357⟩
private theorem pr520363 : Nat.Prime 520363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv28909]) (by decide +kernel)
def pv520363 : PrimeValue := ⟨520363, pr520363⟩
private theorem pr520427 : Nat.Prime 520427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv260213]) (by decide +kernel)
def pv520427 : PrimeValue := ⟨520427, pr520427⟩
private theorem pr520567 : Nat.Prime 520567 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53,pv1637]) (by decide +kernel)
def pv520567 : PrimeValue := ⟨520567, pr520567⟩
private theorem pr520607 : Nat.Prime 520607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv149,pv1747]) (by decide +kernel)
def pv520607 : PrimeValue := ⟨520607, pr520607⟩
private theorem pr520621 : Nat.Prime 520621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv8677]) (by decide +kernel)
def pv520621 : PrimeValue := ⟨520621, pr520621⟩
private theorem pr520717 : Nat.Prime 520717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv6199]) (by decide +kernel)
def pv520717 : PrimeValue := ⟨520717, pr520717⟩
private theorem pr520763 : Nat.Prime 520763 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv23671]) (by decide +kernel)
def pv520763 : PrimeValue := ⟨520763, pr520763⟩
private theorem pr520889 : Nat.Prime 520889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv65111]) (by decide +kernel)
def pv520889 : PrimeValue := ⟨520889, pr520889⟩
private theorem pr520921 : Nat.Prime 520921 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv1447]) (by decide +kernel)
def pv520921 : PrimeValue := ⟨520921, pr520921⟩
private theorem pr520943 : Nat.Prime 520943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv13709]) (by decide +kernel)
def pv520943 : PrimeValue := ⟨520943, pr520943⟩
private theorem pr520963 : Nat.Prime 520963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv6679]) (by decide +kernel)
def pv520963 : PrimeValue := ⟨520963, pr520963⟩
private theorem pr520967 : Nat.Prime 520967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv260483]) (by decide +kernel)
def pv520967 : PrimeValue := ⟨520967, pr520967⟩
private theorem pr521021 : Nat.Prime 521021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv109,pv239]) (by decide +kernel)
def pv521021 : PrimeValue := ⟨521021, pr521021⟩
private theorem pr521023 : Nat.Prime 521023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv86837]) (by decide +kernel)
def pv521023 : PrimeValue := ⟨521023, pr521023⟩
private theorem pr521051 : Nat.Prime 521051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv613]) (by decide +kernel)
def pv521051 : PrimeValue := ⟨521051, pr521051⟩
private theorem pr521063 : Nat.Prime 521063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv61,pv4271]) (by decide +kernel)
def pv521063 : PrimeValue := ⟨521063, pr521063⟩
private theorem pr521231 : Nat.Prime 521231 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv47,pv1109]) (by decide +kernel)
def pv521231 : PrimeValue := ⟨521231, pr521231⟩
private theorem pr521243 : Nat.Prime 521243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv3299]) (by decide +kernel)
def pv521243 : PrimeValue := ⟨521243, pr521243⟩
private theorem pr521281 : Nat.Prime 521281 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv181]) (by decide +kernel)
def pv521281 : PrimeValue := ⟨521281, pr521281⟩
private theorem pr521299 : Nat.Prime 521299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv28961]) (by decide +kernel)
def pv521299 : PrimeValue := ⟨521299, pr521299⟩
private theorem pr521309 : Nat.Prime 521309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv2459]) (by decide +kernel)
def pv521309 : PrimeValue := ⟨521309, pr521309⟩
private theorem pr521317 : Nat.Prime 521317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1609]) (by decide +kernel)
def pv521317 : PrimeValue := ⟨521317, pr521317⟩
private theorem pr521399 : Nat.Prime 521399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv19,pv13721]) (by decide +kernel)
def pv521399 : PrimeValue := ⟨521399, pr521399⟩
private theorem pr521497 : Nat.Prime 521497 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7243]) (by decide +kernel)
def pv521497 : PrimeValue := ⟨521497, pr521497⟩
private theorem pr521503 : Nat.Prime 521503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv3779]) (by decide +kernel)
def pv521503 : PrimeValue := ⟨521503, pr521503⟩
private theorem pr521527 : Nat.Prime 521527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv5113]) (by decide +kernel)
def pv521527 : PrimeValue := ⟨521527, pr521527⟩
private theorem pr521533 : Nat.Prime 521533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv439]) (by decide +kernel)
def pv521533 : PrimeValue := ⟨521533, pr521533⟩
private theorem pr521537 : Nat.Prime 521537 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv281]) (by decide +kernel)
def pv521537 : PrimeValue := ⟨521537, pr521537⟩
private theorem pr521581 : Nat.Prime 521581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv8693]) (by decide +kernel)
def pv521581 : PrimeValue := ⟨521581, pr521581⟩
private theorem pr521603 : Nat.Prime 521603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv6361]) (by decide +kernel)
def pv521603 : PrimeValue := ⟨521603, pr521603⟩
private theorem pr521657 : Nat.Prime 521657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv197,pv331]) (by decide +kernel)
def pv521657 : PrimeValue := ⟨521657, pr521657⟩
private theorem pr521671 : Nat.Prime 521671 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv17389]) (by decide +kernel)
def pv521671 : PrimeValue := ⟨521671, pr521671⟩
private theorem pr521707 : Nat.Prime 521707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv86951]) (by decide +kernel)
def pv521707 : PrimeValue := ⟨521707, pr521707⟩
private theorem pr521767 : Nat.Prime 521767 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv41,pv101]) (by decide +kernel)
def pv521767 : PrimeValue := ⟨521767, pr521767⟩
private theorem pr521777 : Nat.Prime 521777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv32611]) (by decide +kernel)
def pv521777 : PrimeValue := ⟨521777, pr521777⟩
private theorem pr521819 : Nat.Prime 521819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv23719]) (by decide +kernel)
def pv521819 : PrimeValue := ⟨521819, pr521819⟩
private theorem pr521831 : Nat.Prime 521831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv52183]) (by decide +kernel)
def pv521831 : PrimeValue := ⟨521831, pr521831⟩
private theorem pr521861 : Nat.Prime 521861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv97,pv269]) (by decide +kernel)
def pv521861 : PrimeValue := ⟨521861, pr521861⟩
private theorem pr521879 : Nat.Prime 521879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv37277]) (by decide +kernel)
def pv521879 : PrimeValue := ⟨521879, pr521879⟩
private theorem pr521903 : Nat.Prime 521903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv260951]) (by decide +kernel)
def pv521903 : PrimeValue := ⟨521903, pr521903⟩
private theorem pr521929 : Nat.Prime 521929 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv659]) (by decide +kernel)
def pv521929 : PrimeValue := ⟨521929, pr521929⟩
private theorem pr522073 : Nat.Prime 522073 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2417]) (by decide +kernel)
def pv522073 : PrimeValue := ⟨522073, pr522073⟩
private theorem pr522083 : Nat.Prime 522083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv1249]) (by decide +kernel)
def pv522083 : PrimeValue := ⟨522083, pr522083⟩
private theorem pr522113 : Nat.Prime 522113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4079]) (by decide +kernel)
def pv522113 : PrimeValue := ⟨522113, pr522113⟩
private theorem pr522127 : Nat.Prime 522127 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv293]) (by decide +kernel)
def pv522127 : PrimeValue := ⟨522127, pr522127⟩
private theorem pr522191 : Nat.Prime 522191 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv79,pv661]) (by decide +kernel)
def pv522191 : PrimeValue := ⟨522191, pr522191⟩
private theorem pr522233 : Nat.Prime 522233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv2251]) (by decide +kernel)
def pv522233 : PrimeValue := ⟨522233, pr522233⟩
private theorem pr522239 : Nat.Prime 522239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv23,pv11353]) (by decide +kernel)
def pv522239 : PrimeValue := ⟨522239, pr522239⟩
private theorem pr522259 : Nat.Prime 522259 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv41,pv193]) (by decide +kernel)
def pv522259 : PrimeValue := ⟨522259, pr522259⟩
private theorem pr522283 : Nat.Prime 522283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv1427]) (by decide +kernel)
def pv522283 : PrimeValue := ⟨522283, pr522283⟩
private theorem pr522323 : Nat.Prime 522323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv179,pv1459]) (by decide +kernel)
def pv522323 : PrimeValue := ⟨522323, pr522323⟩
private theorem pr522337 : Nat.Prime 522337 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5441]) (by decide +kernel)
def pv522337 : PrimeValue := ⟨522337, pr522337⟩
private theorem pr522383 : Nat.Prime 522383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv37313]) (by decide +kernel)
def pv522383 : PrimeValue := ⟨522383, pr522383⟩
private theorem pr522391 : Nat.Prime 522391 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv11,pv1583]) (by decide +kernel)
def pv522391 : PrimeValue := ⟨522391, pr522391⟩
private theorem pr522413 : Nat.Prime 522413 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv31,pv383]) (by decide +kernel)
def pv522413 : PrimeValue := ⟨522413, pr522413⟩
private theorem pr522517 : Nat.Prime 522517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43543]) (by decide +kernel)
def pv522517 : PrimeValue := ⟨522517, pr522517⟩
private theorem pr522521 : Nat.Prime 522521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13063]) (by decide +kernel)
def pv522521 : PrimeValue := ⟨522521, pr522521⟩
private theorem pr522553 : Nat.Prime 522553 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv21773]) (by decide +kernel)
def pv522553 : PrimeValue := ⟨522553, pr522553⟩
private theorem pr522601 : Nat.Prime 522601 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv13,pv67]) (by decide +kernel)
def pv522601 : PrimeValue := ⟨522601, pr522601⟩
private theorem pr522623 : Nat.Prime 522623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv59,pv103]) (by decide +kernel)
def pv522623 : PrimeValue := ⟨522623, pr522623⟩
private theorem pr522679 : Nat.Prime 522679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv6701]) (by decide +kernel)
def pv522679 : PrimeValue := ⟨522679, pr522679⟩
private theorem pr522737 : Nat.Prime 522737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv883]) (by decide +kernel)
def pv522737 : PrimeValue := ⟨522737, pr522737⟩
private theorem pr522757 : Nat.Prime 522757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1117]) (by decide +kernel)
def pv522757 : PrimeValue := ⟨522757, pr522757⟩
private theorem pr522761 : Nat.Prime 522761 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv1867]) (by decide +kernel)
def pv522761 : PrimeValue := ⟨522761, pr522761⟩
private theorem pr522763 : Nat.Prime 522763 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv151,pv577]) (by decide +kernel)
def pv522763 : PrimeValue := ⟨522763, pr522763⟩
private theorem pr522787 : Nat.Prime 522787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv89]) (by decide +kernel)
def pv522787 : PrimeValue := ⟨522787, pr522787⟩
private theorem pr522811 : Nat.Prime 522811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv37,pv157]) (by decide +kernel)
def pv522811 : PrimeValue := ⟨522811, pr522811⟩
private theorem pr522829 : Nat.Prime 522829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv103]) (by decide +kernel)
def pv522829 : PrimeValue := ⟨522829, pr522829⟩
private theorem pr522839 : Nat.Prime 522839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv197,pv1327]) (by decide +kernel)
def pv522839 : PrimeValue := ⟨522839, pr522839⟩
private theorem pr522857 : Nat.Prime 522857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv65357]) (by decide +kernel)
def pv522857 : PrimeValue := ⟨522857, pr522857⟩
private theorem pr522881 : Nat.Prime 522881 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv19,pv43]) (by decide +kernel)
def pv522881 : PrimeValue := ⟨522881, pr522881⟩
private theorem pr522943 : Nat.Prime 522943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv12451]) (by decide +kernel)
def pv522943 : PrimeValue := ⟨522943, pr522943⟩
private theorem pr523021 : Nat.Prime 523021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv379]) (by decide +kernel)
def pv523021 : PrimeValue := ⟨523021, pr523021⟩
private theorem pr523093 : Nat.Prime 523093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43591]) (by decide +kernel)
def pv523093 : PrimeValue := ⟨523093, pr523093⟩
private theorem pr523207 : Nat.Prime 523207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv9689]) (by decide +kernel)
def pv523207 : PrimeValue := ⟨523207, pr523207⟩
private theorem pr523351 : Nat.Prime 523351 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1163]) (by decide +kernel)
def pv523351 : PrimeValue := ⟨523351, pr523351⟩
private theorem pr523403 : Nat.Prime 523403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv37,pv643]) (by decide +kernel)
def pv523403 : PrimeValue := ⟨523403, pr523403⟩
private theorem pr523433 : Nat.Prime 523433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv719]) (by decide +kernel)
def pv523433 : PrimeValue := ⟨523433, pr523433⟩
private theorem pr523459 : Nat.Prime 523459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2237]) (by decide +kernel)
def pv523459 : PrimeValue := ⟨523459, pr523459⟩
private theorem pr523493 : Nat.Prime 523493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv130873]) (by decide +kernel)
def pv523493 : PrimeValue := ⟨523493, pr523493⟩
private theorem pr523511 : Nat.Prime 523511 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv4027]) (by decide +kernel)
def pv523511 : PrimeValue := ⟨523511, pr523511⟩
private theorem pr523541 : Nat.Prime 523541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv26177]) (by decide +kernel)
def pv523541 : PrimeValue := ⟨523541, pr523541⟩
private theorem pr523553 : Nat.Prime 523553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv16361]) (by decide +kernel)
def pv523553 : PrimeValue := ⟨523553, pr523553⟩
private theorem pr523603 : Nat.Prime 523603 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv1531]) (by decide +kernel)
def pv523603 : PrimeValue := ⟨523603, pr523603⟩
private theorem pr523717 : Nat.Prime 523717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv2297]) (by decide +kernel)
def pv523717 : PrimeValue := ⟨523717, pr523717⟩
private theorem pr523771 : Nat.Prime 523771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv17,pv79]) (by decide +kernel)
def pv523771 : PrimeValue := ⟨523771, pr523771⟩
private theorem pr523777 : Nat.Prime 523777 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv31]) (by decide +kernel)
def pv523777 : PrimeValue := ⟨523777, pr523777⟩
private theorem pr523793 : Nat.Prime 523793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv1723]) (by decide +kernel)
def pv523793 : PrimeValue := ⟨523793, pr523793⟩
private theorem pr523877 : Nat.Prime 523877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv130969]) (by decide +kernel)
def pv523877 : PrimeValue := ⟨523877, pr523877⟩
private theorem pr523927 : Nat.Prime 523927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv2239]) (by decide +kernel)
def pv523927 : PrimeValue := ⟨523927, pr523927⟩
private theorem pr524047 : Nat.Prime 524047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv167,pv523]) (by decide +kernel)
def pv524047 : PrimeValue := ⟨524047, pr524047⟩
private theorem pr524057 : Nat.Prime 524057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv5039]) (by decide +kernel)
def pv524057 : PrimeValue := ⟨524057, pr524057⟩
private theorem pr524063 : Nat.Prime 524063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11,pv41,pv83]) (by decide +kernel)
def pv524063 : PrimeValue := ⟨524063, pr524063⟩
private theorem pr524149 : Nat.Prime 524149 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv31,pv1409]) (by decide +kernel)
def pv524149 : PrimeValue := ⟨524149, pr524149⟩
private theorem pr524171 : Nat.Prime 524171 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv23,pv43,pv53]) (by decide +kernel)
def pv524171 : PrimeValue := ⟨524171, pr524171⟩
private theorem pr524197 : Nat.Prime 524197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14561]) (by decide +kernel)
def pv524197 : PrimeValue := ⟨524197, pr524197⟩
private theorem pr524221 : Nat.Prime 524221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv8737]) (by decide +kernel)
def pv524221 : PrimeValue := ⟨524221, pr524221⟩
private theorem pr524351 : Nat.Prime 524351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv10487]) (by decide +kernel)
def pv524351 : PrimeValue := ⟨524351, pr524351⟩
private theorem pr524411 : Nat.Prime 524411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv229]) (by decide +kernel)
def pv524411 : PrimeValue := ⟨524411, pr524411⟩
private theorem pr524413 : Nat.Prime 524413 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv2081]) (by decide +kernel)
def pv524413 : PrimeValue := ⟨524413, pr524413⟩
private theorem pr524453 : Nat.Prime 524453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv131113]) (by decide +kernel)
def pv524453 : PrimeValue := ⟨524453, pr524453⟩
private theorem pr524497 : Nat.Prime 524497 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv223]) (by decide +kernel)
def pv524497 : PrimeValue := ⟨524497, pr524497⟩
private theorem pr524519 : Nat.Prime 524519 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv17,pv15427]) (by decide +kernel)
def pv524519 : PrimeValue := ⟨524519, pr524519⟩
private theorem pr524591 : Nat.Prime 524591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv19,pv251]) (by decide +kernel)
def pv524591 : PrimeValue := ⟨524591, pr524591⟩
private theorem pr524669 : Nat.Prime 524669 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv4523]) (by decide +kernel)
def pv524669 : PrimeValue := ⟨524669, pr524669⟩
private theorem pr524683 : Nat.Prime 524683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103,pv283]) (by decide +kernel)
def pv524683 : PrimeValue := ⟨524683, pr524683⟩
private theorem pr524743 : Nat.Prime 524743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv4603]) (by decide +kernel)
def pv524743 : PrimeValue := ⟨524743, pr524743⟩
private theorem pr524801 : Nat.Prime 524801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv41]) (by decide +kernel)
def pv524801 : PrimeValue := ⟨524801, pr524801⟩
private theorem pr524803 : Nat.Prime 524803 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv1861]) (by decide +kernel)
def pv524803 : PrimeValue := ⟨524803, pr524803⟩
private theorem pr524827 : Nat.Prime 524827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9719]) (by decide +kernel)
def pv524827 : PrimeValue := ⟨524827, pr524827⟩
private theorem pr524831 : Nat.Prime 524831 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv31,pv1693]) (by decide +kernel)
def pv524831 : PrimeValue := ⟨524831, pr524831⟩
private theorem pr524857 : Nat.Prime 524857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv1151]) (by decide +kernel)
def pv524857 : PrimeValue := ⟨524857, pr524857⟩
private theorem pr524863 : Nat.Prime 524863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv2243]) (by decide +kernel)
def pv524863 : PrimeValue := ⟨524863, pr524863⟩
private theorem pr524869 : Nat.Prime 524869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv191,pv229]) (by decide +kernel)
def pv524869 : PrimeValue := ⟨524869, pr524869⟩
private theorem pr524873 : Nat.Prime 524873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv65609]) (by decide +kernel)
def pv524873 : PrimeValue := ⟨524873, pr524873⟩
private theorem pr524893 : Nat.Prime 524893 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv31,pv83]) (by decide +kernel)
def pv524893 : PrimeValue := ⟨524893, pr524893⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
