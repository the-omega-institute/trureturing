/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table063
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table063.pv188303
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table006
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr188303 : PrimeCertificate 188303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv94151]) (by decide +kernel)
def pv188303 : PrimeValue := ⟨188303, pr188303⟩
private theorem pr188333 : PrimeCertificate 188333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197,pv239]) (by decide +kernel)
def pv188333 : PrimeValue := ⟨188333, pr188333⟩
private theorem pr188351 : PrimeCertificate 188351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv3767]) (by decide +kernel)
def pv188351 : PrimeValue := ⟨188351, pr188351⟩
private theorem pr188359 : PrimeCertificate 188359 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31393]) (by decide +kernel)
def pv188359 : PrimeValue := ⟨188359, pr188359⟩
private theorem pr188369 : PrimeCertificate 188369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61,pv193]) (by decide +kernel)
def pv188369 : PrimeValue := ⟨188369, pr188369⟩
private theorem pr188401 : PrimeCertificate 188401 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv157]) (by decide +kernel)
def pv188401 : PrimeValue := ⟨188401, pr188401⟩
private theorem pr188407 : PrimeCertificate 188407 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1163]) (by decide +kernel)
def pv188407 : PrimeValue := ⟨188407, pr188407⟩
private theorem pr188431 : PrimeCertificate 188431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv571]) (by decide +kernel)
def pv188431 : PrimeValue := ⟨188431, pr188431⟩
private theorem pr188443 : PrimeCertificate 188443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv29]) (by decide +kernel)
def pv188443 : PrimeValue := ⟨188443, pr188443⟩
private theorem pr188459 : PrimeCertificate 188459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv94229]) (by decide +kernel)
def pv188459 : PrimeValue := ⟨188459, pr188459⟩
private theorem pr188473 : PrimeCertificate 188473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7853]) (by decide +kernel)
def pv188473 : PrimeValue := ⟨188473, pr188473⟩
private theorem pr188491 : PrimeCertificate 188491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv61,pv103]) (by decide +kernel)
def pv188491 : PrimeValue := ⟨188491, pr188491⟩
private theorem pr188519 : PrimeCertificate 188519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv19,pv41]) (by decide +kernel)
def pv188519 : PrimeValue := ⟨188519, pr188519⟩
private theorem pr188527 : PrimeCertificate 188527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv2417]) (by decide +kernel)
def pv188527 : PrimeValue := ⟨188527, pr188527⟩
private theorem pr188533 : PrimeCertificate 188533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5237]) (by decide +kernel)
def pv188533 : PrimeValue := ⟨188533, pr188533⟩
private theorem pr188563 : PrimeCertificate 188563 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv2857]) (by decide +kernel)
def pv188563 : PrimeValue := ⟨188563, pr188563⟩
private theorem pr188603 : PrimeCertificate 188603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181,pv521]) (by decide +kernel)
def pv188603 : PrimeValue := ⟨188603, pr188603⟩
private theorem pr188609 : PrimeCertificate 188609 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv421]) (by decide +kernel)
def pv188609 : PrimeValue := ⟨188609, pr188609⟩
private theorem pr188621 : PrimeCertificate 188621 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv9431]) (by decide +kernel)
def pv188621 : PrimeValue := ⟨188621, pr188621⟩
private theorem pr188633 : PrimeCertificate 188633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv19,pv73]) (by decide +kernel)
def pv188633 : PrimeValue := ⟨188633, pr188633⟩
private theorem pr188653 : PrimeCertificate 188653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79,pv199]) (by decide +kernel)
def pv188653 : PrimeValue := ⟨188653, pr188653⟩
private theorem pr188677 : PrimeCertificate 188677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1747]) (by decide +kernel)
def pv188677 : PrimeValue := ⟨188677, pr188677⟩
private theorem pr188681 : PrimeCertificate 188681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv53,pv89]) (by decide +kernel)
def pv188681 : PrimeValue := ⟨188681, pr188681⟩
private theorem pr188687 : PrimeCertificate 188687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv94343]) (by decide +kernel)
def pv188687 : PrimeValue := ⟨188687, pr188687⟩
private theorem pr188693 : PrimeCertificate 188693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv293]) (by decide +kernel)
def pv188693 : PrimeValue := ⟨188693, pr188693⟩
private theorem pr188701 : PrimeCertificate 188701 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv17,pv37]) (by decide +kernel)
def pv188701 : PrimeValue := ⟨188701, pr188701⟩
private theorem pr188707 : PrimeCertificate 188707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4493]) (by decide +kernel)
def pv188707 : PrimeValue := ⟨188707, pr188707⟩
private theorem pr188719 : PrimeCertificate 188719 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv71,pv443]) (by decide +kernel)
def pv188719 : PrimeValue := ⟨188719, pr188719⟩
private theorem pr188729 : PrimeCertificate 188729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv761]) (by decide +kernel)
def pv188729 : PrimeValue := ⟨188729, pr188729⟩
private theorem pr188753 : PrimeCertificate 188753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv251]) (by decide +kernel)
def pv188753 : PrimeValue := ⟨188753, pr188753⟩
private theorem pr188767 : PrimeCertificate 188767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10487]) (by decide +kernel)
def pv188767 : PrimeValue := ⟨188767, pr188767⟩
private theorem pr188791 : PrimeCertificate 188791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv29,pv31]) (by decide +kernel)
def pv188791 : PrimeValue := ⟨188791, pr188791⟩
private theorem pr188827 : PrimeCertificate 188827 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2861]) (by decide +kernel)
def pv188827 : PrimeValue := ⟨188827, pr188827⟩
private theorem pr188831 : PrimeCertificate 188831 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv23,pv821]) (by decide +kernel)
def pv188831 : PrimeValue := ⟨188831, pr188831⟩
private theorem pr188833 : PrimeCertificate 188833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv281]) (by decide +kernel)
def pv188833 : PrimeValue := ⟨188833, pr188833⟩
private theorem pr188843 : PrimeCertificate 188843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv94421]) (by decide +kernel)
def pv188843 : PrimeValue := ⟨188843, pr188843⟩
private theorem pr188857 : PrimeCertificate 188857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv61]) (by decide +kernel)
def pv188857 : PrimeValue := ⟨188857, pr188857⟩
private theorem pr188861 : PrimeCertificate 188861 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv7,pv19,pv71]) (by decide +kernel)
def pv188861 : PrimeValue := ⟨188861, pr188861⟩
private theorem pr188891 : PrimeCertificate 188891 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv13,pv1453]) (by decide +kernel)
def pv188891 : PrimeValue := ⟨188891, pr188891⟩
private theorem pr188911 : PrimeCertificate 188911 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2099]) (by decide +kernel)
def pv188911 : PrimeValue := ⟨188911, pr188911⟩
private theorem pr188933 : PrimeCertificate 188933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv149,pv317]) (by decide +kernel)
def pv188933 : PrimeValue := ⟨188933, pr188933⟩
private theorem pr188941 : PrimeCertificate 188941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv47,pv67]) (by decide +kernel)
def pv188941 : PrimeValue := ⟨188941, pr188941⟩
private theorem pr188953 : PrimeCertificate 188953 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7873]) (by decide +kernel)
def pv188953 : PrimeValue := ⟨188953, pr188953⟩
private theorem pr188957 : PrimeCertificate 188957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv487]) (by decide +kernel)
def pv188957 : PrimeValue := ⟨188957, pr188957⟩
private theorem pr188983 : PrimeCertificate 188983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10499]) (by decide +kernel)
def pv188983 : PrimeValue := ⟨188983, pr188983⟩
private theorem pr188999 : PrimeCertificate 188999 :=
  certifyPrime (q := pv13) (ls := [pv2,pv53,pv1783]) (by decide +kernel)
def pv188999 : PrimeValue := ⟨188999, pr188999⟩
private theorem pr189011 : PrimeCertificate 189011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv461]) (by decide +kernel)
def pv189011 : PrimeValue := ⟨189011, pr189011⟩
private theorem pr189017 : PrimeCertificate 189017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23627]) (by decide +kernel)
def pv189017 : PrimeValue := ⟨189017, pr189017⟩
private theorem pr189019 : PrimeCertificate 189019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10501]) (by decide +kernel)
def pv189019 : PrimeValue := ⟨189019, pr189019⟩
private theorem pr189041 : PrimeCertificate 189041 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv17,pv139]) (by decide +kernel)
def pv189041 : PrimeValue := ⟨189041, pr189041⟩
private theorem pr189043 : PrimeCertificate 189043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv643]) (by decide +kernel)
def pv189043 : PrimeValue := ⟨189043, pr189043⟩
private theorem pr189061 : PrimeCertificate 189061 :=
  certifyPrime (q := pv79) (ls := [pv2,pv3,pv5,pv23,pv137]) (by decide +kernel)
def pv189061 : PrimeValue := ⟨189061, pr189061⟩
private theorem pr189067 : PrimeCertificate 189067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31511]) (by decide +kernel)
def pv189067 : PrimeValue := ⟨189067, pr189067⟩
private theorem pr189139 : PrimeCertificate 189139 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv29,pv1087]) (by decide +kernel)
def pv189139 : PrimeValue := ⟨189139, pr189139⟩
private theorem pr189149 : PrimeCertificate 189149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47287]) (by decide +kernel)
def pv189149 : PrimeValue := ⟨189149, pr189149⟩
private theorem pr189151 : PrimeCertificate 189151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv97]) (by decide +kernel)
def pv189151 : PrimeValue := ⟨189151, pr189151⟩
private theorem pr189199 : PrimeCertificate 189199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv457]) (by decide +kernel)
def pv189199 : PrimeValue := ⟨189199, pr189199⟩
private theorem pr189223 : PrimeCertificate 189223 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv47,pv61]) (by decide +kernel)
def pv189223 : PrimeValue := ⟨189223, pr189223⟩
private theorem pr189239 : PrimeCertificate 189239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv1931]) (by decide +kernel)
def pv189239 : PrimeValue := ⟨189239, pr189239⟩
private theorem pr189251 : PrimeCertificate 189251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv757]) (by decide +kernel)
def pv189251 : PrimeValue := ⟨189251, pr189251⟩
private theorem pr189253 : PrimeCertificate 189253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv751]) (by decide +kernel)
def pv189253 : PrimeValue := ⟨189253, pr189253⟩
private theorem pr189307 : PrimeCertificate 189307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv809]) (by decide +kernel)
def pv189307 : PrimeValue := ⟨189307, pr189307⟩
private theorem pr189311 : PrimeCertificate 189311 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv1721]) (by decide +kernel)
def pv189311 : PrimeValue := ⟨189311, pr189311⟩
private theorem pr189337 : PrimeCertificate 189337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv189337 : PrimeValue := ⟨189337, pr189337⟩
private theorem pr189347 : PrimeCertificate 189347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv5569]) (by decide +kernel)
def pv189347 : PrimeValue := ⟨189347, pr189347⟩
private theorem pr189353 : PrimeCertificate 189353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23669]) (by decide +kernel)
def pv189353 : PrimeValue := ⟨189353, pr189353⟩
private theorem pr189377 : PrimeCertificate 189377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv269]) (by decide +kernel)
def pv189377 : PrimeValue := ⟨189377, pr189377⟩
private theorem pr189389 : PrimeCertificate 189389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv419]) (by decide +kernel)
def pv189389 : PrimeValue := ⟨189389, pr189389⟩
private theorem pr189391 : PrimeCertificate 189391 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv59,pv107]) (by decide +kernel)
def pv189391 : PrimeValue := ⟨189391, pr189391⟩
private theorem pr189407 : PrimeCertificate 189407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv83,pv163]) (by decide +kernel)
def pv189407 : PrimeValue := ⟨189407, pr189407⟩
private theorem pr189421 : PrimeCertificate 189421 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv11,pv41]) (by decide +kernel)
def pv189421 : PrimeValue := ⟨189421, pr189421⟩
private theorem pr189437 : PrimeCertificate 189437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv3643]) (by decide +kernel)
def pv189437 : PrimeValue := ⟨189437, pr189437⟩
private theorem pr189463 : PrimeCertificate 189463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv347]) (by decide +kernel)
def pv189463 : PrimeValue := ⟨189463, pr189463⟩
private theorem pr189473 : PrimeCertificate 189473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv191]) (by decide +kernel)
def pv189473 : PrimeValue := ⟨189473, pr189473⟩
private theorem pr189491 : PrimeCertificate 189491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2707]) (by decide +kernel)
def pv189491 : PrimeValue := ⟨189491, pr189491⟩
private theorem pr189493 : PrimeCertificate 189493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15791]) (by decide +kernel)
def pv189493 : PrimeValue := ⟨189493, pr189493⟩
private theorem pr189509 : PrimeCertificate 189509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv59,pv73]) (by decide +kernel)
def pv189509 : PrimeValue := ⟨189509, pr189509⟩
private theorem pr189523 : PrimeCertificate 189523 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10529]) (by decide +kernel)
def pv189523 : PrimeValue := ⟨189523, pr189523⟩
private theorem pr189529 : PrimeCertificate 189529 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv53,pv149]) (by decide +kernel)
def pv189529 : PrimeValue := ⟨189529, pr189529⟩
private theorem pr189547 : PrimeCertificate 189547 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4513]) (by decide +kernel)
def pv189547 : PrimeValue := ⟨189547, pr189547⟩
private theorem pr189559 : PrimeCertificate 189559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10531]) (by decide +kernel)
def pv189559 : PrimeValue := ⟨189559, pr189559⟩
private theorem pr189593 : PrimeCertificate 189593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv1823]) (by decide +kernel)
def pv189593 : PrimeValue := ⟨189593, pr189593⟩
private theorem pr189599 : PrimeCertificate 189599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv47,pv2017]) (by decide +kernel)
def pv189599 : PrimeValue := ⟨189599, pr189599⟩
private theorem pr189613 : PrimeCertificate 189613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv229]) (by decide +kernel)
def pv189613 : PrimeValue := ⟨189613, pr189613⟩
private theorem pr189643 : PrimeCertificate 189643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31607]) (by decide +kernel)
def pv189643 : PrimeValue := ⟨189643, pr189643⟩
private theorem pr189653 : PrimeCertificate 189653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2789]) (by decide +kernel)
def pv189653 : PrimeValue := ⟨189653, pr189653⟩
private theorem pr189671 : PrimeCertificate 189671 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv1459]) (by decide +kernel)
def pv189671 : PrimeValue := ⟨189671, pr189671⟩
private theorem pr189691 : PrimeCertificate 189691 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv6323]) (by decide +kernel)
def pv189691 : PrimeValue := ⟨189691, pr189691⟩
private theorem pr189697 : PrimeCertificate 189697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv189697 : PrimeValue := ⟨189697, pr189697⟩
private theorem pr189713 : PrimeCertificate 189713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv167]) (by decide +kernel)
def pv189713 : PrimeValue := ⟨189713, pr189713⟩
private theorem pr189757 : PrimeCertificate 189757 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv251]) (by decide +kernel)
def pv189757 : PrimeValue := ⟨189757, pr189757⟩
private theorem pr189767 : PrimeCertificate 189767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv239,pv397]) (by decide +kernel)
def pv189767 : PrimeValue := ⟨189767, pr189767⟩
private theorem pr189797 : PrimeCertificate 189797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2063]) (by decide +kernel)
def pv189797 : PrimeValue := ⟨189797, pr189797⟩
private theorem pr189799 : PrimeCertificate 189799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4519]) (by decide +kernel)
def pv189799 : PrimeValue := ⟨189799, pr189799⟩
private theorem pr189823 : PrimeCertificate 189823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv1861]) (by decide +kernel)
def pv189823 : PrimeValue := ⟨189823, pr189823⟩
private theorem pr189851 : PrimeCertificate 189851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3797]) (by decide +kernel)
def pv189851 : PrimeValue := ⟨189851, pr189851⟩
private theorem pr189859 : PrimeCertificate 189859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31643]) (by decide +kernel)
def pv189859 : PrimeValue := ⟨189859, pr189859⟩
private theorem pr189877 : PrimeCertificate 189877 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv15823]) (by decide +kernel)
def pv189877 : PrimeValue := ⟨189877, pr189877⟩
private theorem pr189881 : PrimeCertificate 189881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47,pv101]) (by decide +kernel)
def pv189881 : PrimeValue := ⟨189881, pr189881⟩
private theorem pr189887 : PrimeCertificate 189887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv263]) (by decide +kernel)
def pv189887 : PrimeValue := ⟨189887, pr189887⟩
private theorem pr189901 : PrimeCertificate 189901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv211]) (by decide +kernel)
def pv189901 : PrimeValue := ⟨189901, pr189901⟩
private theorem pr189913 : PrimeCertificate 189913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv193]) (by decide +kernel)
def pv189913 : PrimeValue := ⟨189913, pr189913⟩
private theorem pr189929 : PrimeCertificate 189929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23741]) (by decide +kernel)
def pv189929 : PrimeValue := ⟨189929, pr189929⟩
private theorem pr189947 : PrimeCertificate 189947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv1301]) (by decide +kernel)
def pv189947 : PrimeValue := ⟨189947, pr189947⟩
private theorem pr189949 : PrimeCertificate 189949 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv1439]) (by decide +kernel)
def pv189949 : PrimeValue := ⟨189949, pr189949⟩
private theorem pr189967 : PrimeCertificate 189967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4523]) (by decide +kernel)
def pv189967 : PrimeValue := ⟨189967, pr189967⟩
private theorem pr189977 : PrimeCertificate 189977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23747]) (by decide +kernel)
def pv189977 : PrimeValue := ⟨189977, pr189977⟩
private theorem pr189983 : PrimeCertificate 189983 :=
  certifyPrime (q := pv23) (ls := [pv2,pv13,pv7307]) (by decide +kernel)
def pv189983 : PrimeValue := ⟨189983, pr189983⟩
private theorem pr189989 : PrimeCertificate 189989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47497]) (by decide +kernel)
def pv189989 : PrimeValue := ⟨189989, pr189989⟩
private theorem pr190027 : PrimeCertificate 190027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv23]) (by decide +kernel)
def pv190027 : PrimeValue := ⟨190027, pr190027⟩
private theorem pr190051 : PrimeCertificate 190051 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv181]) (by decide +kernel)
def pv190051 : PrimeValue := ⟨190051, pr190051⟩
private theorem pr190063 : PrimeCertificate 190063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv10559]) (by decide +kernel)
def pv190063 : PrimeValue := ⟨190063, pr190063⟩
private theorem pr190093 : PrimeCertificate 190093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv73]) (by decide +kernel)
def pv190093 : PrimeValue := ⟨190093, pr190093⟩
private theorem pr190097 : PrimeCertificate 190097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv109]) (by decide +kernel)
def pv190097 : PrimeValue := ⟨190097, pr190097⟩
private theorem pr190121 : PrimeCertificate 190121 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv97]) (by decide +kernel)
def pv190121 : PrimeValue := ⟨190121, pr190121⟩
private theorem pr190129 : PrimeCertificate 190129 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv17,pv233]) (by decide +kernel)
def pv190129 : PrimeValue := ⟨190129, pr190129⟩
private theorem pr190147 : PrimeCertificate 190147 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv43,pv67]) (by decide +kernel)
def pv190147 : PrimeValue := ⟨190147, pr190147⟩
private theorem pr190159 : PrimeCertificate 190159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv773]) (by decide +kernel)
def pv190159 : PrimeValue := ⟨190159, pr190159⟩
private theorem pr190181 : PrimeCertificate 190181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv257]) (by decide +kernel)
def pv190181 : PrimeValue := ⟨190181, pr190181⟩
private theorem pr190207 : PrimeCertificate 190207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv10567]) (by decide +kernel)
def pv190207 : PrimeValue := ⟨190207, pr190207⟩
private theorem pr190243 : PrimeCertificate 190243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv271]) (by decide +kernel)
def pv190243 : PrimeValue := ⟨190243, pr190243⟩
private theorem pr190249 : PrimeCertificate 190249 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7927]) (by decide +kernel)
def pv190249 : PrimeValue := ⟨190249, pr190249⟩
private theorem pr190261 : PrimeCertificate 190261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv151]) (by decide +kernel)
def pv190261 : PrimeValue := ⟨190261, pr190261⟩
private theorem pr190271 : PrimeCertificate 190271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv53,pv359]) (by decide +kernel)
def pv190271 : PrimeValue := ⟨190271, pr190271⟩
private theorem pr190297 : PrimeCertificate 190297 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv881]) (by decide +kernel)
def pv190297 : PrimeValue := ⟨190297, pr190297⟩
private theorem pr190301 : PrimeCertificate 190301 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv173]) (by decide +kernel)
def pv190301 : PrimeValue := ⟨190301, pr190301⟩
private theorem pr190339 : PrimeCertificate 190339 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31723]) (by decide +kernel)
def pv190339 : PrimeValue := ⟨190339, pr190339⟩
private theorem pr190357 : PrimeCertificate 190357 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv547]) (by decide +kernel)
def pv190357 : PrimeValue := ⟨190357, pr190357⟩
private theorem pr190367 : PrimeCertificate 190367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv17,pv509]) (by decide +kernel)
def pv190367 : PrimeValue := ⟨190367, pr190367⟩
private theorem pr190369 : PrimeCertificate 190369 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv661]) (by decide +kernel)
def pv190369 : PrimeValue := ⟨190369, pr190369⟩
private theorem pr190387 : PrimeCertificate 190387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1511]) (by decide +kernel)
def pv190387 : PrimeValue := ⟨190387, pr190387⟩
private theorem pr190403 : PrimeCertificate 190403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv37,pv83]) (by decide +kernel)
def pv190403 : PrimeValue := ⟨190403, pr190403⟩
private theorem pr190409 : PrimeCertificate 190409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23801]) (by decide +kernel)
def pv190409 : PrimeValue := ⟨190409, pr190409⟩
private theorem pr190471 : PrimeCertificate 190471 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv907]) (by decide +kernel)
def pv190471 : PrimeValue := ⟨190471, pr190471⟩
private theorem pr190523 : PrimeCertificate 190523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv95261]) (by decide +kernel)
def pv190523 : PrimeValue := ⟨190523, pr190523⟩
private theorem pr190529 : PrimeCertificate 190529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv229]) (by decide +kernel)
def pv190529 : PrimeValue := ⟨190529, pr190529⟩
private theorem pr190537 : PrimeCertificate 190537 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv17,pv467]) (by decide +kernel)
def pv190537 : PrimeValue := ⟨190537, pr190537⟩
private theorem pr190573 : PrimeCertificate 190573 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv15881]) (by decide +kernel)
def pv190573 : PrimeValue := ⟨190573, pr190573⟩
private theorem pr190577 : PrimeCertificate 190577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv277]) (by decide +kernel)
def pv190577 : PrimeValue := ⟨190577, pr190577⟩
private theorem pr190579 : PrimeCertificate 190579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1381]) (by decide +kernel)
def pv190579 : PrimeValue := ⟨190579, pr190579⟩
private theorem pr190583 : PrimeCertificate 190583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13613]) (by decide +kernel)
def pv190583 : PrimeValue := ⟨190583, pr190583⟩
private theorem pr190591 : PrimeCertificate 190591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv6353]) (by decide +kernel)
def pv190591 : PrimeValue := ⟨190591, pr190591⟩
private theorem pr190607 : PrimeCertificate 190607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv7331]) (by decide +kernel)
def pv190607 : PrimeValue := ⟨190607, pr190607⟩
private theorem pr190613 : PrimeCertificate 190613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47653]) (by decide +kernel)
def pv190613 : PrimeValue := ⟨190613, pr190613⟩
private theorem pr190633 : PrimeCertificate 190633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv47]) (by decide +kernel)
def pv190633 : PrimeValue := ⟨190633, pr190633⟩
private theorem pr190639 : PrimeCertificate 190639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv89]) (by decide +kernel)
def pv190639 : PrimeValue := ⟨190639, pr190639⟩
private theorem pr190657 : PrimeCertificate 190657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv331]) (by decide +kernel)
def pv190657 : PrimeValue := ⟨190657, pr190657⟩
private theorem pr190667 : PrimeCertificate 190667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13619]) (by decide +kernel)
def pv190667 : PrimeValue := ⟨190667, pr190667⟩
private theorem pr190669 : PrimeCertificate 190669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15889]) (by decide +kernel)
def pv190669 : PrimeValue := ⟨190669, pr190669⟩
private theorem pr190709 : PrimeCertificate 190709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv139]) (by decide +kernel)
def pv190709 : PrimeValue := ⟨190709, pr190709⟩
private theorem pr190711 : PrimeCertificate 190711 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv163]) (by decide +kernel)
def pv190711 : PrimeValue := ⟨190711, pr190711⟩
private theorem pr190717 : PrimeCertificate 190717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv691]) (by decide +kernel)
def pv190717 : PrimeValue := ⟨190717, pr190717⟩
private theorem pr190753 : PrimeCertificate 190753 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1987]) (by decide +kernel)
def pv190753 : PrimeValue := ⟨190753, pr190753⟩
private theorem pr190763 : PrimeCertificate 190763 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv13,pv23,pv29]) (by decide +kernel)
def pv190763 : PrimeValue := ⟨190763, pr190763⟩
private theorem pr190783 : PrimeCertificate 190783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3533]) (by decide +kernel)
def pv190783 : PrimeValue := ⟨190783, pr190783⟩
private theorem pr190787 : PrimeCertificate 190787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv95393]) (by decide +kernel)
def pv190787 : PrimeValue := ⟨190787, pr190787⟩
private theorem pr190811 : PrimeCertificate 190811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19081]) (by decide +kernel)
def pv190811 : PrimeValue := ⟨190811, pr190811⟩
private theorem pr190823 : PrimeCertificate 190823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv73,pv1307]) (by decide +kernel)
def pv190823 : PrimeValue := ⟨190823, pr190823⟩
private theorem pr190829 : PrimeCertificate 190829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4337]) (by decide +kernel)
def pv190829 : PrimeValue := ⟨190829, pr190829⟩
private theorem pr190837 : PrimeCertificate 190837 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv31]) (by decide +kernel)
def pv190837 : PrimeValue := ⟨190837, pr190837⟩
private theorem pr190843 : PrimeCertificate 190843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv1871]) (by decide +kernel)
def pv190843 : PrimeValue := ⟨190843, pr190843⟩
private theorem pr190871 : PrimeCertificate 190871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19087]) (by decide +kernel)
def pv190871 : PrimeValue := ⟨190871, pr190871⟩
private theorem pr190889 : PrimeCertificate 190889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107,pv223]) (by decide +kernel)
def pv190889 : PrimeValue := ⟨190889, pr190889⟩
private theorem pr190909 : PrimeCertificate 190909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5303]) (by decide +kernel)
def pv190909 : PrimeValue := ⟨190909, pr190909⟩
private theorem pr190913 : PrimeCertificate 190913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv157]) (by decide +kernel)
def pv190913 : PrimeValue := ⟨190913, pr190913⟩
private theorem pr190979 : PrimeCertificate 190979 :=
  certifyPrime (q := pv29) (ls := [pv2,pv17,pv41,pv137]) (by decide +kernel)
def pv190979 : PrimeValue := ⟨190979, pr190979⟩
private theorem pr190997 : PrimeCertificate 190997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv3673]) (by decide +kernel)
def pv190997 : PrimeValue := ⟨190997, pr190997⟩
private theorem pr191021 : PrimeCertificate 191021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9551]) (by decide +kernel)
def pv191021 : PrimeValue := ⟨191021, pr191021⟩
private theorem pr191039 : PrimeCertificate 191039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv23,pv4153]) (by decide +kernel)
def pv191039 : PrimeValue := ⟨191039, pr191039⟩
private theorem pr191047 : PrimeCertificate 191047 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv17,pv1873]) (by decide +kernel)
def pv191047 : PrimeValue := ⟨191047, pr191047⟩
private theorem pr191089 : PrimeCertificate 191089 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1327]) (by decide +kernel)
def pv191089 : PrimeValue := ⟨191089, pr191089⟩
private theorem pr191137 : PrimeCertificate 191137 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv181]) (by decide +kernel)
def pv191137 : PrimeValue := ⟨191137, pr191137⟩
private theorem pr191141 : PrimeCertificate 191141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv503]) (by decide +kernel)
def pv191141 : PrimeValue := ⟨191141, pr191141⟩
private theorem pr191161 : PrimeCertificate 191161 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv59]) (by decide +kernel)
def pv191161 : PrimeValue := ⟨191161, pr191161⟩
private theorem pr191173 : PrimeCertificate 191173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv179]) (by decide +kernel)
def pv191173 : PrimeValue := ⟨191173, pr191173⟩
private theorem pr191189 : PrimeCertificate 191189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47797]) (by decide +kernel)
def pv191189 : PrimeValue := ⟨191189, pr191189⟩
private theorem pr191227 : PrimeCertificate 191227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv157]) (by decide +kernel)
def pv191227 : PrimeValue := ⟨191227, pr191227⟩
private theorem pr191231 : PrimeCertificate 191231 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv13,pv1471]) (by decide +kernel)
def pv191231 : PrimeValue := ⟨191231, pr191231⟩
private theorem pr191237 : PrimeCertificate 191237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47809]) (by decide +kernel)
def pv191237 : PrimeValue := ⟨191237, pr191237⟩
private theorem pr191251 : PrimeCertificate 191251 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv191251 : PrimeValue := ⟨191251, pr191251⟩
private theorem pr191281 : PrimeCertificate 191281 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv797]) (by decide +kernel)
def pv191281 : PrimeValue := ⟨191281, pr191281⟩
private theorem pr191297 : PrimeCertificate 191297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv61]) (by decide +kernel)
def pv191297 : PrimeValue := ⟨191297, pr191297⟩
private theorem pr191299 : PrimeCertificate 191299 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31883]) (by decide +kernel)
def pv191299 : PrimeValue := ⟨191299, pr191299⟩
private theorem pr191339 : PrimeCertificate 191339 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv79,pv173]) (by decide +kernel)
def pv191339 : PrimeValue := ⟨191339, pr191339⟩
private theorem pr191341 : PrimeCertificate 191341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1063]) (by decide +kernel)
def pv191341 : PrimeValue := ⟨191341, pr191341⟩
private theorem pr191353 : PrimeCertificate 191353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv67]) (by decide +kernel)
def pv191353 : PrimeValue := ⟨191353, pr191353⟩
private theorem pr191413 : PrimeCertificate 191413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv409]) (by decide +kernel)
def pv191413 : PrimeValue := ⟨191413, pr191413⟩
private theorem pr191441 : PrimeCertificate 191441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2393]) (by decide +kernel)
def pv191441 : PrimeValue := ⟨191441, pr191441⟩
private theorem pr191453 : PrimeCertificate 191453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2081]) (by decide +kernel)
def pv191453 : PrimeValue := ⟨191453, pr191453⟩
private theorem pr191459 : PrimeCertificate 191459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv3301]) (by decide +kernel)
def pv191459 : PrimeValue := ⟨191459, pr191459⟩
private theorem pr191461 : PrimeCertificate 191461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3191]) (by decide +kernel)
def pv191461 : PrimeValue := ⟨191461, pr191461⟩
private theorem pr191473 : PrimeCertificate 191473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3989]) (by decide +kernel)
def pv191473 : PrimeValue := ⟨191473, pr191473⟩
private theorem pr191497 : PrimeCertificate 191497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv79,pv101]) (by decide +kernel)
def pv191497 : PrimeValue := ⟨191497, pr191497⟩
private theorem pr191519 : PrimeCertificate 191519 :=
  certifyPrime (q := pv11) (ls := [pv2,pv31,pv3089]) (by decide +kernel)
def pv191519 : PrimeValue := ⟨191519, pr191519⟩
private theorem pr191531 : PrimeCertificate 191531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv107,pv179]) (by decide +kernel)
def pv191531 : PrimeValue := ⟨191531, pr191531⟩
private theorem pr191533 : PrimeCertificate 191533 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1451]) (by decide +kernel)
def pv191533 : PrimeValue := ⟨191533, pr191533⟩
private theorem pr191551 : PrimeCertificate 191551 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1277]) (by decide +kernel)
def pv191551 : PrimeValue := ⟨191551, pr191551⟩
private theorem pr191579 : PrimeCertificate 191579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv95789]) (by decide +kernel)
def pv191579 : PrimeValue := ⟨191579, pr191579⟩
private theorem pr191599 : PrimeCertificate 191599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2903]) (by decide +kernel)
def pv191599 : PrimeValue := ⟨191599, pr191599⟩
private theorem pr191621 : PrimeCertificate 191621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv67]) (by decide +kernel)
def pv191621 : PrimeValue := ⟨191621, pr191621⟩
private theorem pr191657 : PrimeCertificate 191657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23957]) (by decide +kernel)
def pv191657 : PrimeValue := ⟨191657, pr191657⟩
private theorem pr191669 : PrimeCertificate 191669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47917]) (by decide +kernel)
def pv191669 : PrimeValue := ⟨191669, pr191669⟩
private theorem pr191671 : PrimeCertificate 191671 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv6389]) (by decide +kernel)
def pv191671 : PrimeValue := ⟨191671, pr191671⟩
private theorem pr191677 : PrimeCertificate 191677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15973]) (by decide +kernel)
def pv191677 : PrimeValue := ⟨191677, pr191677⟩
private theorem pr191689 : PrimeCertificate 191689 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv163]) (by decide +kernel)
def pv191689 : PrimeValue := ⟨191689, pr191689⟩
private theorem pr191693 : PrimeCertificate 191693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2819]) (by decide +kernel)
def pv191693 : PrimeValue := ⟨191693, pr191693⟩
private theorem pr191699 : PrimeCertificate 191699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv73,pv101]) (by decide +kernel)
def pv191699 : PrimeValue := ⟨191699, pr191699⟩
private theorem pr191707 : PrimeCertificate 191707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv359]) (by decide +kernel)
def pv191707 : PrimeValue := ⟨191707, pr191707⟩
private theorem pr191747 : PrimeCertificate 191747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv95873]) (by decide +kernel)
def pv191747 : PrimeValue := ⟨191747, pr191747⟩
private theorem pr191773 : PrimeCertificate 191773 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv761]) (by decide +kernel)
def pv191773 : PrimeValue := ⟨191773, pr191773⟩
private theorem pr191791 : PrimeCertificate 191791 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv2131]) (by decide +kernel)
def pv191791 : PrimeValue := ⟨191791, pr191791⟩
private theorem pr191827 : PrimeCertificate 191827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10657]) (by decide +kernel)
def pv191827 : PrimeValue := ⟨191827, pr191827⟩
private theorem pr191831 : PrimeCertificate 191831 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv19183]) (by decide +kernel)
def pv191831 : PrimeValue := ⟨191831, pr191831⟩
private theorem pr191833 : PrimeCertificate 191833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7993]) (by decide +kernel)
def pv191833 : PrimeValue := ⟨191833, pr191833⟩
private theorem pr191861 : PrimeCertificate 191861 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv53,pv181]) (by decide +kernel)
def pv191861 : PrimeValue := ⟨191861, pr191861⟩
private theorem pr191899 : PrimeCertificate 191899 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1523]) (by decide +kernel)
def pv191899 : PrimeValue := ⟨191899, pr191899⟩
private theorem pr191903 : PrimeCertificate 191903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv229,pv419]) (by decide +kernel)
def pv191903 : PrimeValue := ⟨191903, pr191903⟩
private theorem pr191953 : PrimeCertificate 191953 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv31,pv43]) (by decide +kernel)
def pv191953 : PrimeValue := ⟨191953, pr191953⟩
private theorem pr191969 : PrimeCertificate 191969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv857]) (by decide +kernel)
def pv191969 : PrimeValue := ⟨191969, pr191969⟩
private theorem pr191977 : PrimeCertificate 191977 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv421]) (by decide +kernel)
def pv191977 : PrimeValue := ⟨191977, pr191977⟩
private theorem pr191999 : PrimeCertificate 191999 :=
  certifyPrime (q := pv11) (ls := [pv2,pv17,pv5647]) (by decide +kernel)
def pv191999 : PrimeValue := ⟨191999, pr191999⟩
private theorem pr192007 : PrimeCertificate 192007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10667]) (by decide +kernel)
def pv192007 : PrimeValue := ⟨192007, pr192007⟩
private theorem pr192013 : PrimeCertificate 192013 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv16001]) (by decide +kernel)
def pv192013 : PrimeValue := ⟨192013, pr192013⟩
private theorem pr192029 : PrimeCertificate 192029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv787]) (by decide +kernel)
def pv192029 : PrimeValue := ⟨192029, pr192029⟩
private theorem pr192037 : PrimeCertificate 192037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1231]) (by decide +kernel)
def pv192037 : PrimeValue := ⟨192037, pr192037⟩
private theorem pr192047 : PrimeCertificate 192047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv131,pv733]) (by decide +kernel)
def pv192047 : PrimeValue := ⟨192047, pr192047⟩
private theorem pr192053 : PrimeCertificate 192053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19]) (by decide +kernel)
def pv192053 : PrimeValue := ⟨192053, pr192053⟩
private theorem pr192091 : PrimeCertificate 192091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv337]) (by decide +kernel)
def pv192091 : PrimeValue := ⟨192091, pr192091⟩
private theorem pr192097 : PrimeCertificate 192097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv29]) (by decide +kernel)
def pv192097 : PrimeValue := ⟨192097, pr192097⟩
private theorem pr192113 : PrimeCertificate 192113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12007]) (by decide +kernel)
def pv192113 : PrimeValue := ⟨192113, pr192113⟩
private theorem pr192121 : PrimeCertificate 192121 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1601]) (by decide +kernel)
def pv192121 : PrimeValue := ⟨192121, pr192121⟩
private theorem pr192133 : PrimeCertificate 192133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv593]) (by decide +kernel)
def pv192133 : PrimeValue := ⟨192133, pr192133⟩
private theorem pr192149 : PrimeCertificate 192149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv397]) (by decide +kernel)
def pv192149 : PrimeValue := ⟨192149, pr192149⟩
private theorem pr192187 : PrimeCertificate 192187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3559]) (by decide +kernel)
def pv192187 : PrimeValue := ⟨192187, pr192187⟩
private theorem pr192191 : PrimeCertificate 192191 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv19219]) (by decide +kernel)
def pv192191 : PrimeValue := ⟨192191, pr192191⟩
private theorem pr192193 : PrimeCertificate 192193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv13]) (by decide +kernel)
def pv192193 : PrimeValue := ⟨192193, pr192193⟩
private theorem pr192233 : PrimeCertificate 192233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv24029]) (by decide +kernel)
def pv192233 : PrimeValue := ⟨192233, pr192233⟩
private theorem pr192239 : PrimeCertificate 192239 :=
  certifyPrime (q := pv11) (ls := [pv2,pv277,pv347]) (by decide +kernel)
def pv192239 : PrimeValue := ⟨192239, pr192239⟩
private theorem pr192259 : PrimeCertificate 192259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv971]) (by decide +kernel)
def pv192259 : PrimeValue := ⟨192259, pr192259⟩
private theorem pr192263 : PrimeCertificate 192263 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv31,pv443]) (by decide +kernel)
def pv192263 : PrimeValue := ⟨192263, pr192263⟩
private theorem pr192317 : PrimeCertificate 192317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv48079]) (by decide +kernel)
def pv192317 : PrimeValue := ⟨192317, pr192317⟩
private theorem pr192341 : PrimeCertificate 192341 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv59,pv163]) (by decide +kernel)
def pv192341 : PrimeValue := ⟨192341, pr192341⟩
private theorem pr192343 : PrimeCertificate 192343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv32057]) (by decide +kernel)
def pv192343 : PrimeValue := ⟨192343, pr192343⟩
private theorem pr192347 : PrimeCertificate 192347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv1249]) (by decide +kernel)
def pv192347 : PrimeValue := ⟨192347, pr192347⟩
private theorem pr192373 : PrimeCertificate 192373 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv23,pv41]) (by decide +kernel)
def pv192373 : PrimeValue := ⟨192373, pr192373⟩
private theorem pr192377 : PrimeCertificate 192377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv139,pv173]) (by decide +kernel)
def pv192377 : PrimeValue := ⟨192377, pr192377⟩
private theorem pr192383 : PrimeCertificate 192383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv2237]) (by decide +kernel)
def pv192383 : PrimeValue := ⟨192383, pr192383⟩
private theorem pr192391 : PrimeCertificate 192391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv53]) (by decide +kernel)
def pv192391 : PrimeValue := ⟨192391, pr192391⟩
private theorem pr192407 : PrimeCertificate 192407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv5659]) (by decide +kernel)
def pv192407 : PrimeValue := ⟨192407, pr192407⟩
private theorem pr192431 : PrimeCertificate 192431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv2749]) (by decide +kernel)
def pv192431 : PrimeValue := ⟨192431, pr192431⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
