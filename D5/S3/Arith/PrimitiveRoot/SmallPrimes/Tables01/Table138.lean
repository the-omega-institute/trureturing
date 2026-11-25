/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table138
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table138.pv1011509
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table038
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table111
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table112
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table113

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1011509 : PrimeCertificate 1011509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv252877]) (by decide +kernel)
def pv1011509 : PrimeValue := ⟨1011509, pr1011509⟩
private theorem pr1011641 : PrimeCertificate 1011641 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv3613]) (by decide +kernel)
def pv1011641 : PrimeValue := ⟨1011641, pr1011641⟩
private theorem pr1012031 : PrimeCertificate 1012031 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv101203]) (by decide +kernel)
def pv1012031 : PrimeValue := ⟨1012031, pr1012031⟩
private theorem pr1012421 : PrimeCertificate 1012421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv223,pv227]) (by decide +kernel)
def pv1012421 : PrimeValue := ⟨1012421, pr1012421⟩
private theorem pr1012601 : PrimeCertificate 1012601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv61,pv83]) (by decide +kernel)
def pv1012601 : PrimeValue := ⟨1012601, pr1012601⟩
private theorem pr1012733 : PrimeCertificate 1012733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv5167]) (by decide +kernel)
def pv1012733 : PrimeValue := ⟨1012733, pr1012733⟩
private theorem pr1012751 : PrimeCertificate 1012751 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv4051]) (by decide +kernel)
def pv1012751 : PrimeValue := ⟨1012751, pr1012751⟩
private theorem pr1012769 : PrimeCertificate 1012769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31649]) (by decide +kernel)
def pv1012769 : PrimeValue := ⟨1012769, pr1012769⟩
private theorem pr1012811 : PrimeCertificate 1012811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv101281]) (by decide +kernel)
def pv1012811 : PrimeValue := ⟨1012811, pr1012811⟩
private theorem pr1012829 : PrimeCertificate 1012829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv101,pv109]) (by decide +kernel)
def pv1012829 : PrimeValue := ⟨1012829, pr1012829⟩
private theorem pr1013399 : PrimeCertificate 1013399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv506699]) (by decide +kernel)
def pv1013399 : PrimeValue := ⟨1013399, pr1013399⟩
private theorem pr1013711 : PrimeCertificate 1013711 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv17,pv67,pv89]) (by decide +kernel)
def pv1013711 : PrimeValue := ⟨1013711, pr1013711⟩
private theorem pr1013819 : PrimeCertificate 1013819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv38993]) (by decide +kernel)
def pv1013819 : PrimeValue := ⟨1013819, pr1013819⟩
private theorem pr1013879 : PrimeCertificate 1013879 :=
  certifyPrime (q := pv11) (ls := [pv2,pv19,pv26681]) (by decide +kernel)
def pv1013879 : PrimeValue := ⟨1013879, pr1013879⟩
private theorem pr1013891 : PrimeCertificate 1013891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv1913]) (by decide +kernel)
def pv1013891 : PrimeValue := ⟨1013891, pr1013891⟩
private theorem pr1013921 : PrimeCertificate 1013921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6337]) (by decide +kernel)
def pv1013921 : PrimeValue := ⟨1013921, pr1013921⟩
private theorem pr1014089 : PrimeCertificate 1014089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv126761]) (by decide +kernel)
def pv1014089 : PrimeValue := ⟨1014089, pr1014089⟩
private theorem pr1014113 : PrimeCertificate 1014113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv43,pv67]) (by decide +kernel)
def pv1014113 : PrimeValue := ⟨1014113, pr1014113⟩
private theorem pr1014131 : PrimeCertificate 1014131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv29,pv269]) (by decide +kernel)
def pv1014131 : PrimeValue := ⟨1014131, pr1014131⟩
private theorem pr1014263 : PrimeCertificate 1014263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv73,pv6947]) (by decide +kernel)
def pv1014263 : PrimeValue := ⟨1014263, pr1014263⟩
private theorem pr1014389 : PrimeCertificate 1014389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv367,pv691]) (by decide +kernel)
def pv1014389 : PrimeValue := ⟨1014389, pr1014389⟩
private theorem pr1014641 : PrimeCertificate 1014641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv1153]) (by decide +kernel)
def pv1014641 : PrimeValue := ⟨1014641, pr1014641⟩
private theorem pr1014719 : PrimeCertificate 1014719 :=
  certifyPrime (q := pv17) (ls := [pv2,pv507359]) (by decide +kernel)
def pv1014719 : PrimeValue := ⟨1014719, pr1014719⟩
private theorem pr1014749 : PrimeCertificate 1014749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv36241]) (by decide +kernel)
def pv1014749 : PrimeValue := ⟨1014749, pr1014749⟩
private theorem pr1014833 : PrimeCertificate 1014833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv17,pv41]) (by decide +kernel)
def pv1014833 : PrimeValue := ⟨1014833, pr1014833⟩
private theorem pr1015499 : PrimeCertificate 1015499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv31,pv1489]) (by decide +kernel)
def pv1015499 : PrimeValue := ⟨1015499, pr1015499⟩
private theorem pr1015919 : PrimeCertificate 1015919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv43,pv11813]) (by decide +kernel)
def pv1015919 : PrimeValue := ⟨1015919, pr1015919⟩
private theorem pr1015991 : PrimeCertificate 1015991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv101599]) (by decide +kernel)
def pv1015991 : PrimeValue := ⟨1015991, pr1015991⟩
private theorem pr1016033 : PrimeCertificate 1016033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31751]) (by decide +kernel)
def pv1016033 : PrimeValue := ⟨1016033, pr1016033⟩
private theorem pr1016051 : PrimeCertificate 1016051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2903]) (by decide +kernel)
def pv1016051 : PrimeValue := ⟨1016051, pr1016051⟩
private theorem pr1016153 : PrimeCertificate 1016153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv1789]) (by decide +kernel)
def pv1016153 : PrimeValue := ⟨1016153, pr1016153⟩
private theorem pr1016201 : PrimeCertificate 1016201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv5081]) (by decide +kernel)
def pv1016201 : PrimeValue := ⟨1016201, pr1016201⟩
private theorem pr1016231 : PrimeCertificate 1016231 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv151,pv673]) (by decide +kernel)
def pv1016231 : PrimeValue := ⟨1016231, pr1016231⟩
private theorem pr1016303 : PrimeCertificate 1016303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv229,pv317]) (by decide +kernel)
def pv1016303 : PrimeValue := ⟨1016303, pr1016303⟩
private theorem pr1016399 : PrimeCertificate 1016399 :=
  certifyPrime (q := pv13) (ls := [pv2,pv619,pv821]) (by decide +kernel)
def pv1016399 : PrimeValue := ⟨1016399, pr1016399⟩
private theorem pr1016621 : PrimeCertificate 1016621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv4621]) (by decide +kernel)
def pv1016621 : PrimeValue := ⟨1016621, pr1016621⟩
private theorem pr1016663 : PrimeCertificate 1016663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv508331]) (by decide +kernel)
def pv1016663 : PrimeValue := ⟨1016663, pr1016663⟩
private theorem pr1016681 : PrimeCertificate 1016681 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv3631]) (by decide +kernel)
def pv1016681 : PrimeValue := ⟨1016681, pr1016681⟩
private theorem pr1016789 : PrimeCertificate 1016789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv254197]) (by decide +kernel)
def pv1016789 : PrimeValue := ⟨1016789, pr1016789⟩
private theorem pr1016843 : PrimeCertificate 1016843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv26759]) (by decide +kernel)
def pv1016843 : PrimeValue := ⟨1016843, pr1016843⟩
private theorem pr1016849 : PrimeCertificate 1016849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1297]) (by decide +kernel)
def pv1016849 : PrimeValue := ⟨1016849, pr1016849⟩
private theorem pr1016891 : PrimeCertificate 1016891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv73,pv199]) (by decide +kernel)
def pv1016891 : PrimeValue := ⟨1016891, pr1016891⟩
private theorem pr1017011 : PrimeCertificate 1017011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv101701]) (by decide +kernel)
def pv1017011 : PrimeValue := ⟨1017011, pr1017011⟩
private theorem pr1017119 : PrimeCertificate 1017119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv508559]) (by decide +kernel)
def pv1017119 : PrimeValue := ⟨1017119, pr1017119⟩
private theorem pr1017179 : PrimeCertificate 1017179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv29917]) (by decide +kernel)
def pv1017179 : PrimeValue := ⟨1017179, pr1017179⟩
private theorem pr1017371 : PrimeCertificate 1017371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv101737]) (by decide +kernel)
def pv1017371 : PrimeValue := ⟨1017371, pr1017371⟩
private theorem pr1017473 : PrimeCertificate 1017473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7949]) (by decide +kernel)
def pv1017473 : PrimeValue := ⟨1017473, pr1017473⟩
private theorem pr1017881 : PrimeCertificate 1017881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv25447]) (by decide +kernel)
def pv1017881 : PrimeValue := ⟨1017881, pr1017881⟩
private theorem pr1017959 : PrimeCertificate 1017959 :=
  certifyPrime (q := pv13) (ls := [pv2,pv29,pv17551]) (by decide +kernel)
def pv1017959 : PrimeValue := ⟨1017959, pr1017959⟩
private theorem pr1018109 : PrimeCertificate 1018109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv2797]) (by decide +kernel)
def pv1018109 : PrimeValue := ⟨1018109, pr1018109⟩
private theorem pr1018301 : PrimeCertificate 1018301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv599]) (by decide +kernel)
def pv1018301 : PrimeValue := ⟨1018301, pr1018301⟩
private theorem pr1018709 : PrimeCertificate 1018709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv71,pv211]) (by decide +kernel)
def pv1018709 : PrimeValue := ⟨1018709, pr1018709⟩
private theorem pr1018859 : PrimeCertificate 1018859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv509429]) (by decide +kernel)
def pv1018859 : PrimeValue := ⟨1018859, pr1018859⟩
private theorem pr1019069 : PrimeCertificate 1019069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv2381]) (by decide +kernel)
def pv1019069 : PrimeValue := ⟨1019069, pr1019069⟩
private theorem pr1019129 : PrimeCertificate 1019129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv37,pv313]) (by decide +kernel)
def pv1019129 : PrimeValue := ⟨1019129, pr1019129⟩
private theorem pr1019261 : PrimeCertificate 1019261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv41,pv113]) (by decide +kernel)
def pv1019261 : PrimeValue := ⟨1019261, pr1019261⟩
private theorem pr1019351 : PrimeCertificate 1019351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv29,pv37]) (by decide +kernel)
def pv1019351 : PrimeValue := ⟨1019351, pr1019351⟩
private theorem pr1019471 : PrimeCertificate 1019471 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv97,pv1051]) (by decide +kernel)
def pv1019471 : PrimeValue := ⟨1019471, pr1019471⟩
private theorem pr1019783 : PrimeCertificate 1019783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv373,pv1367]) (by decide +kernel)
def pv1019783 : PrimeValue := ⟨1019783, pr1019783⟩
private theorem pr1019801 : PrimeCertificate 1019801 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv5099]) (by decide +kernel)
def pv1019801 : PrimeValue := ⟨1019801, pr1019801⟩
private theorem pr1020023 : PrimeCertificate 1020023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv109,pv4679]) (by decide +kernel)
def pv1020023 : PrimeValue := ⟨1020023, pr1020023⟩
private theorem pr1020143 : PrimeCertificate 1020143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv67,pv331]) (by decide +kernel)
def pv1020143 : PrimeValue := ⟨1020143, pr1020143⟩
private theorem pr1020269 : PrimeCertificate 1020269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv379,pv673]) (by decide +kernel)
def pv1020269 : PrimeValue := ⟨1020269, pr1020269⟩
private theorem pr1020401 : PrimeCertificate 1020401 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv2551]) (by decide +kernel)
def pv1020401 : PrimeValue := ⟨1020401, pr1020401⟩
private theorem pr1020413 : PrimeCertificate 1020413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv3593]) (by decide +kernel)
def pv1020413 : PrimeValue := ⟨1020413, pr1020413⟩
private theorem pr1020599 : PrimeCertificate 1020599 :=
  certifyPrime (q := pv13) (ls := [pv2,pv510299]) (by decide +kernel)
def pv1020599 : PrimeValue := ⟨1020599, pr1020599⟩
private theorem pr1020821 : PrimeCertificate 1020821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv1187]) (by decide +kernel)
def pv1020821 : PrimeValue := ⟨1020821, pr1020821⟩
private theorem pr1021019 : PrimeCertificate 1021019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv8369]) (by decide +kernel)
def pv1021019 : PrimeValue := ⟨1021019, pr1021019⟩
private theorem pr1021199 : PrimeCertificate 1021199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv137,pv3727]) (by decide +kernel)
def pv1021199 : PrimeValue := ⟨1021199, pr1021199⟩
private theorem pr1021301 : PrimeCertificate 1021301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1459]) (by decide +kernel)
def pv1021301 : PrimeValue := ⟨1021301, pr1021301⟩
private theorem pr1021661 : PrimeCertificate 1021661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv2221]) (by decide +kernel)
def pv1021661 : PrimeValue := ⟨1021661, pr1021661⟩
private theorem pr1021799 : PrimeCertificate 1021799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv23,pv97,pv229]) (by decide +kernel)
def pv1021799 : PrimeValue := ⟨1021799, pr1021799⟩
private theorem pr1022033 : PrimeCertificate 1022033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv5807]) (by decide +kernel)
def pv1022033 : PrimeValue := ⟨1022033, pr1022033⟩
private theorem pr1022243 : PrimeCertificate 1022243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv39317]) (by decide +kernel)
def pv1022243 : PrimeValue := ⟨1022243, pr1022243⟩
private theorem pr1022249 : PrimeCertificate 1022249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv127781]) (by decide +kernel)
def pv1022249 : PrimeValue := ⟨1022249, pr1022249⟩
private theorem pr1022849 : PrimeCertificate 1022849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61,pv131]) (by decide +kernel)
def pv1022849 : PrimeValue := ⟨1022849, pr1022849⟩
private theorem pr1022981 : PrimeCertificate 1022981 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv7307]) (by decide +kernel)
def pv1022981 : PrimeValue := ⟨1022981, pr1022981⟩
private theorem pr1023101 : PrimeCertificate 1023101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv787]) (by decide +kernel)
def pv1023101 : PrimeValue := ⟨1023101, pr1023101⟩
private theorem pr1023413 : PrimeCertificate 1023413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19681]) (by decide +kernel)
def pv1023413 : PrimeValue := ⟨1023413, pr1023413⟩
private theorem pr1023521 : PrimeCertificate 1023521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6397]) (by decide +kernel)
def pv1023521 : PrimeValue := ⟨1023521, pr1023521⟩
private theorem pr1023719 : PrimeCertificate 1023719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv511859]) (by decide +kernel)
def pv1023719 : PrimeValue := ⟨1023719, pr1023719⟩
private theorem pr1023941 : PrimeCertificate 1023941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv51197]) (by decide +kernel)
def pv1023941 : PrimeValue := ⟨1023941, pr1023941⟩
private theorem pr1024031 : PrimeCertificate 1024031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv14629]) (by decide +kernel)
def pv1024031 : PrimeValue := ⟨1024031, pr1024031⟩
private theorem pr1024319 : PrimeCertificate 1024319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv47,pv641]) (by decide +kernel)
def pv1024319 : PrimeValue := ⟨1024319, pr1024319⟩
private theorem pr1024421 : PrimeCertificate 1024421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv23,pv131]) (by decide +kernel)
def pv1024421 : PrimeValue := ⟨1024421, pr1024421⟩
private theorem pr1024433 : PrimeCertificate 1024433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv1489]) (by decide +kernel)
def pv1024433 : PrimeValue := ⟨1024433, pr1024433⟩
private theorem pr1024559 : PrimeCertificate 1024559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv23,pv22273]) (by decide +kernel)
def pv1024559 : PrimeValue := ⟨1024559, pr1024559⟩
private theorem pr1024703 : PrimeCertificate 1024703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv53,pv1381]) (by decide +kernel)
def pv1024703 : PrimeValue := ⟨1024703, pr1024703⟩
private theorem pr1024823 : PrimeCertificate 1024823 :=
  certifyPrime (q := pv7) (ls := [pv2,pv19,pv149,pv181]) (by decide +kernel)
def pv1024823 : PrimeValue := ⟨1024823, pr1024823⟩
private theorem pr1024931 : PrimeCertificate 1024931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv6029]) (by decide +kernel)
def pv1024931 : PrimeValue := ⟨1024931, pr1024931⟩
private theorem pr1025039 : PrimeCertificate 1025039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv211,pv347]) (by decide +kernel)
def pv1025039 : PrimeValue := ⟨1025039, pr1025039⟩
private theorem pr1025081 : PrimeCertificate 1025081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv523]) (by decide +kernel)
def pv1025081 : PrimeValue := ⟨1025081, pr1025081⟩
private theorem pr1025273 : PrimeCertificate 1025273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv128159]) (by decide +kernel)
def pv1025273 : PrimeValue := ⟨1025273, pr1025273⟩
private theorem pr1025393 : PrimeCertificate 1025393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv3373]) (by decide +kernel)
def pv1025393 : PrimeValue := ⟨1025393, pr1025393⟩
private theorem pr1025543 : PrimeCertificate 1025543 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17,pv31,pv139]) (by decide +kernel)
def pv1025543 : PrimeValue := ⟨1025543, pr1025543⟩
private theorem pr1025561 : PrimeCertificate 1025561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv25639]) (by decide +kernel)
def pv1025561 : PrimeValue := ⟨1025561, pr1025561⟩
private theorem pr1026029 : PrimeCertificate 1026029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179,pv1433]) (by decide +kernel)
def pv1026029 : PrimeValue := ⟨1026029, pr1026029⟩
private theorem pr1026251 : PrimeCertificate 1026251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv821]) (by decide +kernel)
def pv1026251 : PrimeValue := ⟨1026251, pr1026251⟩
private theorem pr1026293 : PrimeCertificate 1026293 :=
  certifyPrime (q := pv5) (ls := [pv2,pv47,pv53,pv103]) (by decide +kernel)
def pv1026293 : PrimeValue := ⟨1026293, pr1026293⟩
private theorem pr1026401 : PrimeCertificate 1026401 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv1283]) (by decide +kernel)
def pv1026401 : PrimeValue := ⟨1026401, pr1026401⟩
private theorem pr1026449 : PrimeCertificate 1026449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv64153]) (by decide +kernel)
def pv1026449 : PrimeValue := ⟨1026449, pr1026449⟩
private theorem pr1026479 : PrimeCertificate 1026479 :=
  certifyPrime (q := pv11) (ls := [pv2,pv513239]) (by decide +kernel)
def pv1026479 : PrimeValue := ⟨1026479, pr1026479⟩
private theorem pr1026563 : PrimeCertificate 1026563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv109,pv277]) (by decide +kernel)
def pv1026563 : PrimeValue := ⟨1026563, pr1026563⟩
private theorem pr1026989 : PrimeCertificate 1026989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv13513]) (by decide +kernel)
def pv1026989 : PrimeValue := ⟨1026989, pr1026989⟩
private theorem pr1027241 : PrimeCertificate 1027241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv61,pv421]) (by decide +kernel)
def pv1027241 : PrimeValue := ⟨1027241, pr1027241⟩
private theorem pr1027289 : PrimeCertificate 1027289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv128411]) (by decide +kernel)
def pv1027289 : PrimeValue := ⟨1027289, pr1027289⟩
private theorem pr1027319 : PrimeCertificate 1027319 :=
  certifyPrime (q := pv13) (ls := [pv2,pv23,pv971]) (by decide +kernel)
def pv1027319 : PrimeValue := ⟨1027319, pr1027319⟩
private theorem pr1027739 : PrimeCertificate 1027739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv389,pv1321]) (by decide +kernel)
def pv1027739 : PrimeValue := ⟨1027739, pr1027739⟩
private theorem pr1027751 : PrimeCertificate 1027751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv4111]) (by decide +kernel)
def pv1027751 : PrimeValue := ⟨1027751, pr1027751⟩
private theorem pr1027853 : PrimeCertificate 1027853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv36709]) (by decide +kernel)
def pv1027853 : PrimeValue := ⟨1027853, pr1027853⟩
private theorem pr1028003 : PrimeCertificate 1028003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv514001]) (by decide +kernel)
def pv1028003 : PrimeValue := ⟨1028003, pr1028003⟩
private theorem pr1028201 : PrimeCertificate 1028201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv53,pv97]) (by decide +kernel)
def pv1028201 : PrimeValue := ⟨1028201, pr1028201⟩
private theorem pr1028231 : PrimeCertificate 1028231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv37,pv397]) (by decide +kernel)
def pv1028231 : PrimeValue := ⟨1028231, pr1028231⟩
private theorem pr1028273 : PrimeCertificate 1028273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv9181]) (by decide +kernel)
def pv1028273 : PrimeValue := ⟨1028273, pr1028273⟩
private theorem pr1028333 : PrimeCertificate 1028333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv8293]) (by decide +kernel)
def pv1028333 : PrimeValue := ⟨1028333, pr1028333⟩
private theorem pr1028393 : PrimeCertificate 1028393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv128549]) (by decide +kernel)
def pv1028393 : PrimeValue := ⟨1028393, pr1028393⟩
private theorem pr1028873 : PrimeCertificate 1028873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv761]) (by decide +kernel)
def pv1028873 : PrimeValue := ⟨1028873, pr1028873⟩
private theorem pr1028903 : PrimeCertificate 1028903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv10499]) (by decide +kernel)
def pv1028903 : PrimeValue := ⟨1028903, pr1028903⟩
private theorem pr1028999 : PrimeCertificate 1028999 :=
  certifyPrime (q := pv11) (ls := [pv2,pv514499]) (by decide +kernel)
def pv1028999 : PrimeValue := ⟨1028999, pr1028999⟩
private theorem pr1029023 : PrimeCertificate 1029023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv281,pv1831]) (by decide +kernel)
def pv1029023 : PrimeValue := ⟨1029023, pr1029023⟩
private theorem pr1029191 : PrimeCertificate 1029191 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv101,pv1019]) (by decide +kernel)
def pv1029191 : PrimeValue := ⟨1029191, pr1029191⟩
private theorem pr1029383 : PrimeCertificate 1029383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv103,pv263]) (by decide +kernel)
def pv1029383 : PrimeValue := ⟨1029383, pr1029383⟩
private theorem pr1029881 : PrimeCertificate 1029881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv25747]) (by decide +kernel)
def pv1029881 : PrimeValue := ⟨1029881, pr1029881⟩
private theorem pr1029929 : PrimeCertificate 1029929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv7573]) (by decide +kernel)
def pv1029929 : PrimeValue := ⟨1029929, pr1029929⟩
private theorem pr1029989 : PrimeCertificate 1029989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv257497]) (by decide +kernel)
def pv1029989 : PrimeValue := ⟨1029989, pr1029989⟩
private theorem pr1030031 : PrimeCertificate 1030031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv73,pv83]) (by decide +kernel)
def pv1030031 : PrimeValue := ⟨1030031, pr1030031⟩
private theorem pr1030049 : PrimeCertificate 1030049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv32189]) (by decide +kernel)
def pv1030049 : PrimeValue := ⟨1030049, pr1030049⟩
private theorem pr1030121 : PrimeCertificate 1030121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv283]) (by decide +kernel)
def pv1030121 : PrimeValue := ⟨1030121, pr1030121⟩
private theorem pr1030439 : PrimeCertificate 1030439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv30307]) (by decide +kernel)
def pv1030439 : PrimeValue := ⟨1030439, pr1030439⟩
private theorem pr1030619 : PrimeCertificate 1030619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv5003]) (by decide +kernel)
def pv1030619 : PrimeValue := ⟨1030619, pr1030619⟩
private theorem pr1030643 : PrimeCertificate 1030643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv30313]) (by decide +kernel)
def pv1030643 : PrimeValue := ⟨1030643, pr1030643⟩
private theorem pr1030751 : PrimeCertificate 1030751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv19,pv31]) (by decide +kernel)
def pv1030751 : PrimeValue := ⟨1030751, pr1030751⟩
private theorem pr1030811 : PrimeCertificate 1030811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv9371]) (by decide +kernel)
def pv1030811 : PrimeValue := ⟨1030811, pr1030811⟩
private theorem pr1031003 : PrimeCertificate 1031003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv73643]) (by decide +kernel)
def pv1031003 : PrimeValue := ⟨1031003, pr1031003⟩
private theorem pr1031489 : PrimeCertificate 1031489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv227]) (by decide +kernel)
def pv1031489 : PrimeValue := ⟨1031489, pr1031489⟩
private theorem pr1031669 : PrimeCertificate 1031669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23447]) (by decide +kernel)
def pv1031669 : PrimeValue := ⟨1031669, pr1031669⟩
private theorem pr1031729 : PrimeCertificate 1031729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv64483]) (by decide +kernel)
def pv1031729 : PrimeValue := ⟨1031729, pr1031729⟩
private theorem pr1031741 : PrimeCertificate 1031741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv79,pv653]) (by decide +kernel)
def pv1031741 : PrimeValue := ⟨1031741, pr1031741⟩
private theorem pr1031753 : PrimeCertificate 1031753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv128969]) (by decide +kernel)
def pv1031753 : PrimeValue := ⟨1031753, pr1031753⟩
private theorem pr1031813 : PrimeCertificate 1031813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv257953]) (by decide +kernel)
def pv1031813 : PrimeValue := ⟨1031813, pr1031813⟩
private theorem pr1032071 : PrimeCertificate 1032071 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv13,pv17,pv467]) (by decide +kernel)
def pv1032071 : PrimeValue := ⟨1032071, pr1032071⟩
private theorem pr1032131 : PrimeCertificate 1032131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv853]) (by decide +kernel)
def pv1032131 : PrimeValue := ⟨1032131, pr1032131⟩
private theorem pr1032221 : PrimeCertificate 1032221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv73,pv101]) (by decide +kernel)
def pv1032221 : PrimeValue := ⟨1032221, pr1032221⟩
private theorem pr1032491 : PrimeCertificate 1032491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv223,pv463]) (by decide +kernel)
def pv1032491 : PrimeValue := ⟨1032491, pr1032491⟩
private theorem pr1032833 : PrimeCertificate 1032833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8069]) (by decide +kernel)
def pv1032833 : PrimeValue := ⟨1032833, pr1032833⟩
private theorem pr1033061 : PrimeCertificate 1033061 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv47,pv157]) (by decide +kernel)
def pv1033061 : PrimeValue := ⟨1033061, pr1033061⟩
private theorem pr1033223 : PrimeCertificate 1033223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv516611]) (by decide +kernel)
def pv1033223 : PrimeValue := ⟨1033223, pr1033223⟩
private theorem pr1033289 : PrimeCertificate 1033289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv2437]) (by decide +kernel)
def pv1033289 : PrimeValue := ⟨1033289, pr1033289⟩
private theorem pr1033349 : PrimeCertificate 1033349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv258337]) (by decide +kernel)
def pv1033349 : PrimeValue := ⟨1033349, pr1033349⟩
private theorem pr1033451 : PrimeCertificate 1033451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1879]) (by decide +kernel)
def pv1033451 : PrimeValue := ⟨1033451, pr1033451⟩
private theorem pr1033541 : PrimeCertificate 1033541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv1667]) (by decide +kernel)
def pv1033541 : PrimeValue := ⟨1033541, pr1033541⟩
private theorem pr1033559 : PrimeCertificate 1033559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv37,pv13967]) (by decide +kernel)
def pv1033559 : PrimeValue := ⟨1033559, pr1033559⟩
private theorem pr1033793 : PrimeCertificate 1033793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv557]) (by decide +kernel)
def pv1033793 : PrimeValue := ⟨1033793, pr1033793⟩
private theorem pr1034069 : PrimeCertificate 1034069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv36931]) (by decide +kernel)
def pv1034069 : PrimeValue := ⟨1034069, pr1034069⟩
private theorem pr1034219 : PrimeCertificate 1034219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv22483]) (by decide +kernel)
def pv1034219 : PrimeValue := ⟨1034219, pr1034219⟩
private theorem pr1034249 : PrimeCertificate 1034249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv129281]) (by decide +kernel)
def pv1034249 : PrimeValue := ⟨1034249, pr1034249⟩
private theorem pr1034381 : PrimeCertificate 1034381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv51719]) (by decide +kernel)
def pv1034381 : PrimeValue := ⟨1034381, pr1034381⟩
private theorem pr1034591 : PrimeCertificate 1034591 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv307,pv337]) (by decide +kernel)
def pv1034591 : PrimeValue := ⟨1034591, pr1034591⟩
private theorem pr1034861 : PrimeCertificate 1034861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv877]) (by decide +kernel)
def pv1034861 : PrimeValue := ⟨1034861, pr1034861⟩
private theorem pr1034903 : PrimeCertificate 1034903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv47041]) (by decide +kernel)
def pv1034903 : PrimeValue := ⟨1034903, pr1034903⟩
private theorem pr1034993 : PrimeCertificate 1034993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv9241]) (by decide +kernel)
def pv1034993 : PrimeValue := ⟨1034993, pr1034993⟩
private theorem pr1035263 : PrimeCertificate 1035263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv431,pv1201]) (by decide +kernel)
def pv1035263 : PrimeValue := ⟨1035263, pr1035263⟩
private theorem pr1035473 : PrimeCertificate 1035473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv64717]) (by decide +kernel)
def pv1035473 : PrimeValue := ⟨1035473, pr1035473⟩
private theorem pr1035659 : PrimeCertificate 1035659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv61,pv653]) (by decide +kernel)
def pv1035659 : PrimeValue := ⟨1035659, pr1035659⟩
private theorem pr1035791 : PrimeCertificate 1035791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv14797]) (by decide +kernel)
def pv1035791 : PrimeValue := ⟨1035791, pr1035791⟩
private theorem pr1036001 : PrimeCertificate 1036001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv37]) (by decide +kernel)
def pv1036001 : PrimeValue := ⟨1036001, pr1036001⟩
private theorem pr1036163 : PrimeCertificate 1036163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv73,pv151]) (by decide +kernel)
def pv1036163 : PrimeValue := ⟨1036163, pr1036163⟩
private theorem pr1036331 : PrimeCertificate 1036331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv3343]) (by decide +kernel)
def pv1036331 : PrimeValue := ⟨1036331, pr1036331⟩
private theorem pr1036349 : PrimeCertificate 1036349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv2671]) (by decide +kernel)
def pv1036349 : PrimeValue := ⟨1036349, pr1036349⟩
private theorem pr1036631 : PrimeCertificate 1036631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv59,pv251]) (by decide +kernel)
def pv1036631 : PrimeValue := ⟨1036631, pr1036631⟩
private theorem pr1036853 : PrimeCertificate 1036853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv259213]) (by decide +kernel)
def pv1036853 : PrimeValue := ⟨1036853, pr1036853⟩
private theorem pr1037273 : PrimeCertificate 1037273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv29,pv263]) (by decide +kernel)
def pv1037273 : PrimeValue := ⟨1037273, pr1037273⟩
private theorem pr1037411 : PrimeCertificate 1037411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv9431]) (by decide +kernel)
def pv1037411 : PrimeValue := ⟨1037411, pr1037411⟩
private theorem pr1037681 : PrimeCertificate 1037681 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv17,pv109]) (by decide +kernel)
def pv1037681 : PrimeValue := ⟨1037681, pr1037681⟩
private theorem pr1037741 : PrimeCertificate 1037741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv53,pv89]) (by decide +kernel)
def pv1037741 : PrimeValue := ⟨1037741, pr1037741⟩
private theorem pr1037801 : PrimeCertificate 1037801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv5189]) (by decide +kernel)
def pv1037801 : PrimeValue := ⟨1037801, pr1037801⟩
private theorem pr1038029 : PrimeCertificate 1038029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv259507]) (by decide +kernel)
def pv1038029 : PrimeValue := ⟨1038029, pr1038029⟩
private theorem pr1038203 : PrimeCertificate 1038203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv41,pv1151]) (by decide +kernel)
def pv1038203 : PrimeValue := ⟨1038203, pr1038203⟩
private theorem pr1038209 : PrimeCertificate 1038209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8111]) (by decide +kernel)
def pv1038209 : PrimeValue := ⟨1038209, pr1038209⟩
private theorem pr1038269 : PrimeCertificate 1038269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv3371]) (by decide +kernel)
def pv1038269 : PrimeValue := ⟨1038269, pr1038269⟩
private theorem pr1038503 : PrimeCertificate 1038503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv27329]) (by decide +kernel)
def pv1038503 : PrimeValue := ⟨1038503, pr1038503⟩
private theorem pr1038671 : PrimeCertificate 1038671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv103867]) (by decide +kernel)
def pv1038671 : PrimeValue := ⟨1038671, pr1038671⟩
private theorem pr1038833 : PrimeCertificate 1038833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv64927]) (by decide +kernel)
def pv1038833 : PrimeValue := ⟨1038833, pr1038833⟩
private theorem pr1039169 : PrimeCertificate 1039169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1249]) (by decide +kernel)
def pv1039169 : PrimeValue := ⟨1039169, pr1039169⟩
private theorem pr1039463 : PrimeCertificate 1039463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv59,pv383]) (by decide +kernel)
def pv1039463 : PrimeValue := ⟨1039463, pr1039463⟩
private theorem pr1039469 : PrimeCertificate 1039469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv259867]) (by decide +kernel)
def pv1039469 : PrimeValue := ⟨1039469, pr1039469⟩
private theorem pr1039481 : PrimeCertificate 1039481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv1999]) (by decide +kernel)
def pv1039481 : PrimeValue := ⟨1039481, pr1039481⟩
private theorem pr1039799 : PrimeCertificate 1039799 :=
  certifyPrime (q := pv13) (ls := [pv2,pv79,pv6581]) (by decide +kernel)
def pv1039799 : PrimeValue := ⟨1039799, pr1039799⟩
private theorem pr1039823 : PrimeCertificate 1039823 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17,pv257]) (by decide +kernel)
def pv1039823 : PrimeValue := ⟨1039823, pr1039823⟩
private theorem pr1039931 : PrimeCertificate 1039931 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv103993]) (by decide +kernel)
def pv1039931 : PrimeValue := ⟨1039931, pr1039931⟩
private theorem pr1040219 : PrimeCertificate 1040219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv14057]) (by decide +kernel)
def pv1040219 : PrimeValue := ⟨1040219, pr1040219⟩
private theorem pr1040339 : PrimeCertificate 1040339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv40013]) (by decide +kernel)
def pv1040339 : PrimeValue := ⟨1040339, pr1040339⟩
private theorem pr1040381 : PrimeCertificate 1040381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv4729]) (by decide +kernel)
def pv1040381 : PrimeValue := ⟨1040381, pr1040381⟩
private theorem pr1040489 : PrimeCertificate 1040489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv1567]) (by decide +kernel)
def pv1040489 : PrimeValue := ⟨1040489, pr1040489⟩
private theorem pr1040579 : PrimeCertificate 1040579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv29,pv233]) (by decide +kernel)
def pv1040579 : PrimeValue := ⟨1040579, pr1040579⟩
private theorem pr1040813 : PrimeCertificate 1040813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv367,pv709]) (by decide +kernel)
def pv1040813 : PrimeValue := ⟨1040813, pr1040813⟩
private theorem pr1040951 : PrimeCertificate 1040951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv109,pv191]) (by decide +kernel)
def pv1040951 : PrimeValue := ⟨1040951, pr1040951⟩
private theorem pr1041269 : PrimeCertificate 1041269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv260317]) (by decide +kernel)
def pv1041269 : PrimeValue := ⟨1041269, pr1041269⟩
private theorem pr1041329 : PrimeCertificate 1041329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv1759]) (by decide +kernel)
def pv1041329 : PrimeValue := ⟨1041329, pr1041329⟩
private theorem pr1041563 : PrimeCertificate 1041563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv239,pv2179]) (by decide +kernel)
def pv1041563 : PrimeValue := ⟨1041563, pr1041563⟩
private theorem pr1041671 : PrimeCertificate 1041671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv23,pv647]) (by decide +kernel)
def pv1041671 : PrimeValue := ⟨1041671, pr1041671⟩
private theorem pr1041983 : PrimeCertificate 1041983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv83,pv6277]) (by decide +kernel)
def pv1041983 : PrimeValue := ⟨1041983, pr1041983⟩
private theorem pr1042001 : PrimeCertificate 1042001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv521]) (by decide +kernel)
def pv1042001 : PrimeValue := ⟨1042001, pr1042001⟩
private theorem pr1042109 : PrimeCertificate 1042109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv260527]) (by decide +kernel)
def pv1042109 : PrimeValue := ⟨1042109, pr1042109⟩
private theorem pr1042451 : PrimeCertificate 1042451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv20849]) (by decide +kernel)
def pv1042451 : PrimeValue := ⟨1042451, pr1042451⟩
private theorem pr1042529 : PrimeCertificate 1042529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv32579]) (by decide +kernel)
def pv1042529 : PrimeValue := ⟨1042529, pr1042529⟩
private theorem pr1042571 : PrimeCertificate 1042571 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv137,pv761]) (by decide +kernel)
def pv1042571 : PrimeValue := ⟨1042571, pr1042571⟩
private theorem pr1042799 : PrimeCertificate 1042799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv521399]) (by decide +kernel)
def pv1042799 : PrimeValue := ⟨1042799, pr1042799⟩
private theorem pr1042829 : PrimeCertificate 1042829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv4919]) (by decide +kernel)
def pv1042829 : PrimeValue := ⟨1042829, pr1042829⟩
private theorem pr1042901 : PrimeCertificate 1042901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv10429]) (by decide +kernel)
def pv1042901 : PrimeValue := ⟨1042901, pr1042901⟩
private theorem pr1042949 : PrimeCertificate 1042949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv13723]) (by decide +kernel)
def pv1042949 : PrimeValue := ⟨1042949, pr1042949⟩
private theorem pr1043369 : PrimeCertificate 1043369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv3181]) (by decide +kernel)
def pv1043369 : PrimeValue := ⟨1043369, pr1043369⟩
private theorem pr1043453 : PrimeCertificate 1043453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv260863]) (by decide +kernel)
def pv1043453 : PrimeValue := ⟨1043453, pr1043453⟩
private theorem pr1043513 : PrimeCertificate 1043513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv130439]) (by decide +kernel)
def pv1043513 : PrimeValue := ⟨1043513, pr1043513⟩
private theorem pr1043951 : PrimeCertificate 1043951 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv20879]) (by decide +kernel)
def pv1043951 : PrimeValue := ⟨1043951, pr1043951⟩
private theorem pr1044209 : PrimeCertificate 1044209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17,pv349]) (by decide +kernel)
def pv1044209 : PrimeValue := ⟨1044209, pr1044209⟩
private theorem pr1044299 : PrimeCertificate 1044299 :=
  certifyPrime (q := pv7) (ls := [pv2,pv43,pv12143]) (by decide +kernel)
def pv1044299 : PrimeValue := ⟨1044299, pr1044299⟩
private theorem pr1044689 : PrimeCertificate 1044689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv65293]) (by decide +kernel)
def pv1044689 : PrimeValue := ⟨1044689, pr1044689⟩
private theorem pr1044761 : PrimeCertificate 1044761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv26119]) (by decide +kernel)
def pv1044761 : PrimeValue := ⟨1044761, pr1044761⟩
private theorem pr1044779 : PrimeCertificate 1044779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1523]) (by decide +kernel)
def pv1044779 : PrimeValue := ⟨1044779, pr1044779⟩
private theorem pr1045799 : PrimeCertificate 1045799 :=
  certifyPrime (q := pv17) (ls := [pv2,pv13,pv19,pv29,pv73]) (by decide +kernel)
def pv1045799 : PrimeValue := ⟨1045799, pr1045799⟩
private theorem pr1045829 : PrimeCertificate 1045829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv41,pv911]) (by decide +kernel)
def pv1045829 : PrimeValue := ⟨1045829, pr1045829⟩
private theorem pr1046081 : PrimeCertificate 1046081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv467]) (by decide +kernel)
def pv1046081 : PrimeValue := ⟨1046081, pr1046081⟩
private theorem pr1046399 : PrimeCertificate 1046399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv71,pv7369]) (by decide +kernel)
def pv1046399 : PrimeValue := ⟨1046399, pr1046399⟩
private theorem pr1046459 : PrimeCertificate 1046459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv74747]) (by decide +kernel)
def pv1046459 : PrimeValue := ⟨1046459, pr1046459⟩
private theorem pr1046849 : PrimeCertificate 1046849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1487]) (by decide +kernel)
def pv1046849 : PrimeValue := ⟨1046849, pr1046849⟩
private theorem pr1047311 : PrimeCertificate 1047311 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv9521]) (by decide +kernel)
def pv1047311 : PrimeValue := ⟨1047311, pr1047311⟩
private theorem pr1047323 : PrimeCertificate 1047323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv14153]) (by decide +kernel)
def pv1047323 : PrimeValue := ⟨1047323, pr1047323⟩
private theorem pr1047341 : PrimeCertificate 1047341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv7481]) (by decide +kernel)
def pv1047341 : PrimeValue := ⟨1047341, pr1047341⟩
private theorem pr1047671 : PrimeCertificate 1047671 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv8059]) (by decide +kernel)
def pv1047671 : PrimeValue := ⟨1047671, pr1047671⟩
private theorem pr1047773 : PrimeCertificate 1047773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23813]) (by decide +kernel)
def pv1047773 : PrimeValue := ⟨1047773, pr1047773⟩
private theorem pr1047971 : PrimeCertificate 1047971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv1361]) (by decide +kernel)
def pv1047971 : PrimeValue := ⟨1047971, pr1047971⟩
private theorem pr1048343 : PrimeCertificate 1048343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv524171]) (by decide +kernel)
def pv1048343 : PrimeValue := ⟨1048343, pr1048343⟩
private theorem pr1048433 : PrimeCertificate 1048433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv23,pv37]) (by decide +kernel)
def pv1048433 : PrimeValue := ⟨1048433, pr1048433⟩
private theorem pr1048571 : PrimeCertificate 1048571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv47,pv97]) (by decide +kernel)
def pv1048571 : PrimeValue := ⟨1048571, pr1048571⟩
private theorem pr1048889 : PrimeCertificate 1048889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv131111]) (by decide +kernel)
def pv1048889 : PrimeValue := ⟨1048889, pr1048889⟩
private theorem pr1048991 : PrimeCertificate 1048991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv5521]) (by decide +kernel)
def pv1048991 : PrimeValue := ⟨1048991, pr1048991⟩
private theorem pr1049039 : PrimeCertificate 1049039 :=
  certifyPrime (q := pv17) (ls := [pv2,pv524519]) (by decide +kernel)
def pv1049039 : PrimeValue := ⟨1049039, pr1049039⟩
private theorem pr1049201 : PrimeCertificate 1049201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv43,pv61]) (by decide +kernel)
def pv1049201 : PrimeValue := ⟨1049201, pr1049201⟩
private theorem pr1049663 : PrimeCertificate 1049663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv524831]) (by decide +kernel)
def pv1049663 : PrimeValue := ⟨1049663, pr1049663⟩
private theorem pr1049963 : PrimeCertificate 1049963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv524981]) (by decide +kernel)
def pv1049963 : PrimeValue := ⟨1049963, pr1049963⟩
private theorem pr1050083 : PrimeCertificate 1050083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv59,pv809]) (by decide +kernel)
def pv1050083 : PrimeValue := ⟨1050083, pr1050083⟩
private theorem pr1050281 : PrimeCertificate 1050281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv31]) (by decide +kernel)
def pv1050281 : PrimeValue := ⟨1050281, pr1050281⟩
private theorem pr1050449 : PrimeCertificate 1050449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv83,pv113]) (by decide +kernel)
def pv1050449 : PrimeValue := ⟨1050449, pr1050449⟩
private theorem pr1050503 : PrimeCertificate 1050503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv41,pv557]) (by decide +kernel)
def pv1050503 : PrimeValue := ⟨1050503, pr1050503⟩
private theorem pr1050509 : PrimeCertificate 1050509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv262627]) (by decide +kernel)
def pv1050509 : PrimeValue := ⟨1050509, pr1050509⟩
private theorem pr1050611 : PrimeCertificate 1050611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv9551]) (by decide +kernel)
def pv1050611 : PrimeValue := ⟨1050611, pr1050611⟩
private theorem pr1050851 : PrimeCertificate 1050851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv21017]) (by decide +kernel)
def pv1050851 : PrimeValue := ⟨1050851, pr1050851⟩
private theorem pr1051139 : PrimeCertificate 1051139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv47779]) (by decide +kernel)
def pv1051139 : PrimeValue := ⟨1051139, pr1051139⟩
private theorem pr1051283 : PrimeCertificate 1051283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv525641]) (by decide +kernel)
def pv1051283 : PrimeValue := ⟨1051283, pr1051283⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
