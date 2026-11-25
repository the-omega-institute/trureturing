/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table094
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table094.pv356737
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table061

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr356737 : PrimeCertificate 356737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv929]) (by decide +kernel)
def pv356737 : PrimeValue := ⟨356737, pr356737⟩
private theorem pr356831 : PrimeCertificate 356831 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv2099]) (by decide +kernel)
def pv356831 : PrimeValue := ⟨356831, pr356831⟩
private theorem pr356969 : PrimeCertificate 356969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv44621]) (by decide +kernel)
def pv356969 : PrimeValue := ⟨356969, pr356969⟩
private theorem pr356977 : PrimeCertificate 356977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv67]) (by decide +kernel)
def pv356977 : PrimeValue := ⟨356977, pr356977⟩
private theorem pr356989 : PrimeCertificate 356989 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv71,pv419]) (by decide +kernel)
def pv356989 : PrimeValue := ⟨356989, pr356989⟩
private theorem pr357047 : PrimeCertificate 357047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv167,pv1069]) (by decide +kernel)
def pv357047 : PrimeValue := ⟨357047, pr357047⟩
private theorem pr357083 : PrimeCertificate 357083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv16231]) (by decide +kernel)
def pv357083 : PrimeValue := ⟨357083, pr357083⟩
private theorem pr357107 : PrimeCertificate 357107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv47,pv131]) (by decide +kernel)
def pv357107 : PrimeValue := ⟨357107, pr357107⟩
private theorem pr357169 : PrimeCertificate 357169 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv1063]) (by decide +kernel)
def pv357169 : PrimeValue := ⟨357169, pr357169⟩
private theorem pr357179 : PrimeCertificate 357179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv271,pv659]) (by decide +kernel)
def pv357179 : PrimeValue := ⟨357179, pr357179⟩
private theorem pr357239 : PrimeCertificate 357239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17,pv19,pv79]) (by decide +kernel)
def pv357239 : PrimeValue := ⟨357239, pr357239⟩
private theorem pr357263 : PrimeCertificate 357263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv73,pv2447]) (by decide +kernel)
def pv357263 : PrimeValue := ⟨357263, pr357263⟩
private theorem pr357271 : PrimeCertificate 357271 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11909]) (by decide +kernel)
def pv357271 : PrimeValue := ⟨357271, pr357271⟩
private theorem pr357281 : PrimeCertificate 357281 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv11,pv29]) (by decide +kernel)
def pv357281 : PrimeValue := ⟨357281, pr357281⟩
private theorem pr357283 : PrimeCertificate 357283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv863]) (by decide +kernel)
def pv357283 : PrimeValue := ⟨357283, pr357283⟩
private theorem pr357293 : PrimeCertificate 357293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv6871]) (by decide +kernel)
def pv357293 : PrimeValue := ⟨357293, pr357293⟩
private theorem pr357347 : PrimeCertificate 357347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv37,pv439]) (by decide +kernel)
def pv357347 : PrimeValue := ⟨357347, pr357347⟩
private theorem pr357349 : PrimeCertificate 357349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv307]) (by decide +kernel)
def pv357349 : PrimeValue := ⟨357349, pr357349⟩
private theorem pr357359 : PrimeCertificate 357359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv197,pv907]) (by decide +kernel)
def pv357359 : PrimeValue := ⟨357359, pr357359⟩
private theorem pr357473 : PrimeCertificate 357473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11171]) (by decide +kernel)
def pv357473 : PrimeValue := ⟨357473, pr357473⟩
private theorem pr357509 : PrimeCertificate 357509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139,pv643]) (by decide +kernel)
def pv357509 : PrimeValue := ⟨357509, pr357509⟩
private theorem pr357517 : PrimeCertificate 357517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9931]) (by decide +kernel)
def pv357517 : PrimeValue := ⟨357517, pr357517⟩
private theorem pr357551 : PrimeCertificate 357551 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7151]) (by decide +kernel)
def pv357551 : PrimeValue := ⟨357551, pr357551⟩
private theorem pr357559 : PrimeCertificate 357559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv2591]) (by decide +kernel)
def pv357559 : PrimeValue := ⟨357559, pr357559⟩
private theorem pr357563 : PrimeCertificate 357563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv178781]) (by decide +kernel)
def pv357563 : PrimeValue := ⟨357563, pr357563⟩
private theorem pr357569 : PrimeCertificate 357569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv151]) (by decide +kernel)
def pv357569 : PrimeValue := ⟨357569, pr357569⟩
private theorem pr357611 : PrimeCertificate 357611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv3251]) (by decide +kernel)
def pv357611 : PrimeValue := ⟨357611, pr357611⟩
private theorem pr357667 : PrimeCertificate 357667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59611]) (by decide +kernel)
def pv357667 : PrimeValue := ⟨357667, pr357667⟩
private theorem pr357703 : PrimeCertificate 357703 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv59617]) (by decide +kernel)
def pv357703 : PrimeValue := ⟨357703, pr357703⟩
private theorem pr357737 : PrimeCertificate 357737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97,pv461]) (by decide +kernel)
def pv357737 : PrimeValue := ⟨357737, pr357737⟩
private theorem pr357781 : PrimeCertificate 357781 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv67,pv89]) (by decide +kernel)
def pv357781 : PrimeValue := ⟨357781, pr357781⟩
private theorem pr357787 : PrimeCertificate 357787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv139]) (by decide +kernel)
def pv357787 : PrimeValue := ⟨357787, pr357787⟩
private theorem pr357793 : PrimeCertificate 357793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3727]) (by decide +kernel)
def pv357793 : PrimeValue := ⟨357793, pr357793⟩
private theorem pr357823 : PrimeCertificate 357823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv103,pv193]) (by decide +kernel)
def pv357823 : PrimeValue := ⟨357823, pr357823⟩
private theorem pr357829 : PrimeCertificate 357829 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29819]) (by decide +kernel)
def pv357829 : PrimeValue := ⟨357829, pr357829⟩
private theorem pr357839 : PrimeCertificate 357839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv13,pv13763]) (by decide +kernel)
def pv357839 : PrimeValue := ⟨357839, pr357839⟩
private theorem pr357967 : PrimeCertificate 357967 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv947]) (by decide +kernel)
def pv357967 : PrimeValue := ⟨357967, pr357967⟩
private theorem pr357977 : PrimeCertificate 357977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv1543]) (by decide +kernel)
def pv357977 : PrimeValue := ⟨357977, pr357977⟩
private theorem pr358031 : PrimeCertificate 358031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv35803]) (by decide +kernel)
def pv358031 : PrimeValue := ⟨358031, pr358031⟩
private theorem pr358079 : PrimeCertificate 358079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv25577]) (by decide +kernel)
def pv358079 : PrimeValue := ⟨358079, pr358079⟩
private theorem pr358159 : PrimeCertificate 358159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59693]) (by decide +kernel)
def pv358159 : PrimeValue := ⟨358159, pr358159⟩
private theorem pr358181 : PrimeCertificate 358181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17909]) (by decide +kernel)
def pv358181 : PrimeValue := ⟨358181, pr358181⟩
private theorem pr358201 : PrimeCertificate 358201 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv199]) (by decide +kernel)
def pv358201 : PrimeValue := ⟨358201, pr358201⟩
private theorem pr358223 : PrimeCertificate 358223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv179111]) (by decide +kernel)
def pv358223 : PrimeValue := ⟨358223, pr358223⟩
private theorem pr358229 : PrimeCertificate 358229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv83]) (by decide +kernel)
def pv358229 : PrimeValue := ⟨358229, pr358229⟩
private theorem pr358327 : PrimeCertificate 358327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv1171]) (by decide +kernel)
def pv358327 : PrimeValue := ⟨358327, pr358327⟩
private theorem pr358331 : PrimeCertificate 358331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv5119]) (by decide +kernel)
def pv358331 : PrimeValue := ⟨358331, pr358331⟩
private theorem pr358349 : PrimeCertificate 358349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv887]) (by decide +kernel)
def pv358349 : PrimeValue := ⟨358349, pr358349⟩
private theorem pr358373 : PrimeCertificate 358373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv12799]) (by decide +kernel)
def pv358373 : PrimeValue := ⟨358373, pr358373⟩
private theorem pr358417 : PrimeCertificate 358417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv131]) (by decide +kernel)
def pv358417 : PrimeValue := ⟨358417, pr358417⟩
private theorem pr358429 : PrimeCertificate 358429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv251]) (by decide +kernel)
def pv358429 : PrimeValue := ⟨358429, pr358429⟩
private theorem pr358447 : PrimeCertificate 358447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv5431]) (by decide +kernel)
def pv358447 : PrimeValue := ⟨358447, pr358447⟩
private theorem pr358487 : PrimeCertificate 358487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv179243]) (by decide +kernel)
def pv358487 : PrimeValue := ⟨358487, pr358487⟩
private theorem pr358601 : PrimeCertificate 358601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv163]) (by decide +kernel)
def pv358601 : PrimeValue := ⟨358601, pr358601⟩
private theorem pr358607 : PrimeCertificate 358607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv9437]) (by decide +kernel)
def pv358607 : PrimeValue := ⟨358607, pr358607⟩
private theorem pr358669 : PrimeCertificate 358669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv358669 : PrimeValue := ⟨358669, pr358669⟩
private theorem pr358703 : PrimeCertificate 358703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv179351]) (by decide +kernel)
def pv358703 : PrimeValue := ⟨358703, pr358703⟩
private theorem pr358733 : PrimeCertificate 358733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv31,pv263]) (by decide +kernel)
def pv358733 : PrimeValue := ⟨358733, pr358733⟩
private theorem pr358747 : PrimeCertificate 358747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59791]) (by decide +kernel)
def pv358747 : PrimeValue := ⟨358747, pr358747⟩
private theorem pr358769 : PrimeCertificate 358769 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv1319]) (by decide +kernel)
def pv358769 : PrimeValue := ⟨358769, pr358769⟩
private theorem pr358811 : PrimeCertificate 358811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv677]) (by decide +kernel)
def pv358811 : PrimeValue := ⟨358811, pr358811⟩
private theorem pr358829 : PrimeCertificate 358829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv823]) (by decide +kernel)
def pv358829 : PrimeValue := ⟨358829, pr358829⟩
private theorem pr358847 : PrimeCertificate 358847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv29,pv269]) (by decide +kernel)
def pv358847 : PrimeValue := ⟨358847, pr358847⟩
private theorem pr358859 : PrimeCertificate 358859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179429]) (by decide +kernel)
def pv358859 : PrimeValue := ⟨358859, pr358859⟩
private theorem pr358901 : PrimeCertificate 358901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv97]) (by decide +kernel)
def pv358901 : PrimeValue := ⟨358901, pr358901⟩
private theorem pr358903 : PrimeCertificate 358903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv127,pv157]) (by decide +kernel)
def pv358903 : PrimeValue := ⟨358903, pr358903⟩
private theorem pr358907 : PrimeCertificate 358907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179453]) (by decide +kernel)
def pv358907 : PrimeValue := ⟨358907, pr358907⟩
private theorem pr358973 : PrimeCertificate 358973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv5279]) (by decide +kernel)
def pv358973 : PrimeValue := ⟨358973, pr358973⟩
private theorem pr358979 : PrimeCertificate 358979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv239,pv751]) (by decide +kernel)
def pv358979 : PrimeValue := ⟨358979, pr358979⟩
private theorem pr358993 : PrimeCertificate 358993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv277]) (by decide +kernel)
def pv358993 : PrimeValue := ⟨358993, pr358993⟩
private theorem pr358999 : PrimeCertificate 358999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59833]) (by decide +kernel)
def pv358999 : PrimeValue := ⟨358999, pr358999⟩
private theorem pr359003 : PrimeCertificate 359003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv25643]) (by decide +kernel)
def pv359003 : PrimeValue := ⟨359003, pr359003⟩
private theorem pr359017 : PrimeCertificate 359017 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv2137]) (by decide +kernel)
def pv359017 : PrimeValue := ⟨359017, pr359017⟩
private theorem pr359069 : PrimeCertificate 359069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89767]) (by decide +kernel)
def pv359069 : PrimeValue := ⟨359069, pr359069⟩
private theorem pr359111 : PrimeCertificate 359111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv35911]) (by decide +kernel)
def pv359111 : PrimeValue := ⟨359111, pr359111⟩
private theorem pr359129 : PrimeCertificate 359129 :=
  certifyPrime (q := pv19) (ls := [pv2,pv7,pv11,pv53]) (by decide +kernel)
def pv359129 : PrimeValue := ⟨359129, pr359129⟩
private theorem pr359147 : PrimeCertificate 359147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179573]) (by decide +kernel)
def pv359147 : PrimeValue := ⟨359147, pr359147⟩
private theorem pr359167 : PrimeCertificate 359167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv1931]) (by decide +kernel)
def pv359167 : PrimeValue := ⟨359167, pr359167⟩
private theorem pr359171 : PrimeCertificate 359171 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv733]) (by decide +kernel)
def pv359171 : PrimeValue := ⟨359171, pr359171⟩
private theorem pr359207 : PrimeCertificate 359207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv179603]) (by decide +kernel)
def pv359207 : PrimeValue := ⟨359207, pr359207⟩
private theorem pr359231 : PrimeCertificate 359231 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv35923]) (by decide +kernel)
def pv359231 : PrimeValue := ⟨359231, pr359231⟩
private theorem pr359263 : PrimeCertificate 359263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6653]) (by decide +kernel)
def pv359263 : PrimeValue := ⟨359263, pr359263⟩
private theorem pr359267 : PrimeCertificate 359267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179633]) (by decide +kernel)
def pv359267 : PrimeValue := ⟨359267, pr359267⟩
private theorem pr359279 : PrimeCertificate 359279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv10567]) (by decide +kernel)
def pv359279 : PrimeValue := ⟨359279, pr359279⟩
private theorem pr359327 : PrimeCertificate 359327 :=
  certifyPrime (q := pv13) (ls := [pv2,pv11,pv16333]) (by decide +kernel)
def pv359327 : PrimeValue := ⟨359327, pr359327⟩
private theorem pr359407 : PrimeCertificate 359407 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv487]) (by decide +kernel)
def pv359407 : PrimeValue := ⟨359407, pr359407⟩
private theorem pr359417 : PrimeCertificate 359417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv44927]) (by decide +kernel)
def pv359417 : PrimeValue := ⟨359417, pr359417⟩
private theorem pr359441 : PrimeCertificate 359441 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv4493]) (by decide +kernel)
def pv359441 : PrimeValue := ⟨359441, pr359441⟩
private theorem pr359449 : PrimeCertificate 359449 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv881]) (by decide +kernel)
def pv359449 : PrimeValue := ⟨359449, pr359449⟩
private theorem pr359501 : PrimeCertificate 359501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv719]) (by decide +kernel)
def pv359501 : PrimeValue := ⟨359501, pr359501⟩
private theorem pr359563 : PrimeCertificate 359563 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1223]) (by decide +kernel)
def pv359563 : PrimeValue := ⟨359563, pr359563⟩
private theorem pr359587 : PrimeCertificate 359587 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6659]) (by decide +kernel)
def pv359587 : PrimeValue := ⟨359587, pr359587⟩
private theorem pr359633 : PrimeCertificate 359633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv19]) (by decide +kernel)
def pv359633 : PrimeValue := ⟨359633, pr359633⟩
private theorem pr359747 : PrimeCertificate 359747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv9467]) (by decide +kernel)
def pv359747 : PrimeValue := ⟨359747, pr359747⟩
private theorem pr359761 : PrimeCertificate 359761 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1499]) (by decide +kernel)
def pv359761 : PrimeValue := ⟨359761, pr359761⟩
private theorem pr359767 : PrimeCertificate 359767 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv23,pv79]) (by decide +kernel)
def pv359767 : PrimeValue := ⟨359767, pr359767⟩
private theorem pr359783 : PrimeCertificate 359783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv59,pv3049]) (by decide +kernel)
def pv359783 : PrimeValue := ⟨359783, pr359783⟩
private theorem pr359837 : PrimeCertificate 359837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89959]) (by decide +kernel)
def pv359837 : PrimeValue := ⟨359837, pr359837⟩
private theorem pr359897 : PrimeCertificate 359897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv44987]) (by decide +kernel)
def pv359897 : PrimeValue := ⟨359897, pr359897⟩
private theorem pr359929 : PrimeCertificate 359929 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv4999]) (by decide +kernel)
def pv359929 : PrimeValue := ⟨359929, pr359929⟩
private theorem pr359981 : PrimeCertificate 359981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv439]) (by decide +kernel)
def pv359981 : PrimeValue := ⟨359981, pr359981⟩
private theorem pr359987 : PrimeCertificate 359987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv16363]) (by decide +kernel)
def pv359987 : PrimeValue := ⟨359987, pr359987⟩
private theorem pr360071 : PrimeCertificate 360071 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv36007]) (by decide +kernel)
def pv360071 : PrimeValue := ⟨360071, pr360071⟩
private theorem pr360089 : PrimeCertificate 360089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv23,pv103]) (by decide +kernel)
def pv360089 : PrimeValue := ⟨360089, pr360089⟩
private theorem pr360167 : PrimeCertificate 360167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv101,pv1783]) (by decide +kernel)
def pv360167 : PrimeValue := ⟨360167, pr360167⟩
private theorem pr360181 : PrimeCertificate 360181 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv29]) (by decide +kernel)
def pv360181 : PrimeValue := ⟨360181, pr360181⟩
private theorem pr360193 : PrimeCertificate 360193 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv360193 : PrimeValue := ⟨360193, pr360193⟩
private theorem pr360257 : PrimeCertificate 360257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv433]) (by decide +kernel)
def pv360257 : PrimeValue := ⟨360257, pr360257⟩
private theorem pr360293 : PrimeCertificate 360293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv90073]) (by decide +kernel)
def pv360293 : PrimeValue := ⟨360293, pr360293⟩
private theorem pr360307 : PrimeCertificate 360307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv541]) (by decide +kernel)
def pv360307 : PrimeValue := ⟨360307, pr360307⟩
private theorem pr360317 : PrimeCertificate 360317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv431]) (by decide +kernel)
def pv360317 : PrimeValue := ⟨360317, pr360317⟩
private theorem pr360439 : PrimeCertificate 360439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv4621]) (by decide +kernel)
def pv360439 : PrimeValue := ⟨360439, pr360439⟩
private theorem pr360509 : PrimeCertificate 360509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv90127]) (by decide +kernel)
def pv360509 : PrimeValue := ⟨360509, pr360509⟩
private theorem pr360511 : PrimeCertificate 360511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv61,pv197]) (by decide +kernel)
def pv360511 : PrimeValue := ⟨360511, pr360511⟩
private theorem pr360541 : PrimeCertificate 360541 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv2003]) (by decide +kernel)
def pv360541 : PrimeValue := ⟨360541, pr360541⟩
private theorem pr360551 : PrimeCertificate 360551 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7211]) (by decide +kernel)
def pv360551 : PrimeValue := ⟨360551, pr360551⟩
private theorem pr360611 : PrimeCertificate 360611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv36061]) (by decide +kernel)
def pv360611 : PrimeValue := ⟨360611, pr360611⟩
private theorem pr360637 : PrimeCertificate 360637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv733]) (by decide +kernel)
def pv360637 : PrimeValue := ⟨360637, pr360637⟩
private theorem pr360653 : PrimeCertificate 360653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv90163]) (by decide +kernel)
def pv360653 : PrimeValue := ⟨360653, pr360653⟩
private theorem pr360749 : PrimeCertificate 360749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv90187]) (by decide +kernel)
def pv360749 : PrimeValue := ⟨360749, pr360749⟩
private theorem pr360821 : PrimeCertificate 360821 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv18041]) (by decide +kernel)
def pv360821 : PrimeValue := ⟨360821, pr360821⟩
private theorem pr360823 : PrimeCertificate 360823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv71]) (by decide +kernel)
def pv360823 : PrimeValue := ⟨360823, pr360823⟩
private theorem pr360827 : PrimeCertificate 360827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv180413]) (by decide +kernel)
def pv360827 : PrimeValue := ⟨360827, pr360827⟩
private theorem pr360851 : PrimeCertificate 360851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1031]) (by decide +kernel)
def pv360851 : PrimeValue := ⟨360851, pr360851⟩
private theorem pr360869 : PrimeCertificate 360869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv90217]) (by decide +kernel)
def pv360869 : PrimeValue := ⟨360869, pr360869⟩
private theorem pr360949 : PrimeCertificate 360949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv4297]) (by decide +kernel)
def pv360949 : PrimeValue := ⟨360949, pr360949⟩
private theorem pr360977 : PrimeCertificate 360977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv293]) (by decide +kernel)
def pv360977 : PrimeValue := ⟨360977, pr360977⟩
private theorem pr360989 : PrimeCertificate 360989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv90247]) (by decide +kernel)
def pv360989 : PrimeValue := ⟨360989, pr360989⟩
private theorem pr361001 : PrimeCertificate 361001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv361001 : PrimeValue := ⟨361001, pr361001⟩
private theorem pr361013 : PrimeCertificate 361013 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv5309]) (by decide +kernel)
def pv361013 : PrimeValue := ⟨361013, pr361013⟩
private theorem pr361091 : PrimeCertificate 361091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv36109]) (by decide +kernel)
def pv361091 : PrimeValue := ⟨361091, pr361091⟩
private theorem pr361223 : PrimeCertificate 361223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv179,pv1009]) (by decide +kernel)
def pv361223 : PrimeValue := ⟨361223, pr361223⟩
private theorem pr361241 : PrimeCertificate 361241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv821]) (by decide +kernel)
def pv361241 : PrimeValue := ⟨361241, pr361241⟩
private theorem pr361279 : PrimeCertificate 361279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv20071]) (by decide +kernel)
def pv361279 : PrimeValue := ⟨361279, pr361279⟩
private theorem pr361351 : PrimeCertificate 361351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv73]) (by decide +kernel)
def pv361351 : PrimeValue := ⟨361351, pr361351⟩
private theorem pr361357 : PrimeCertificate 361357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30113]) (by decide +kernel)
def pv361357 : PrimeValue := ⟨361357, pr361357⟩
private theorem pr361363 : PrimeCertificate 361363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv229,pv263]) (by decide +kernel)
def pv361363 : PrimeValue := ⟨361363, pr361363⟩
private theorem pr361373 : PrimeCertificate 361373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv43,pv191]) (by decide +kernel)
def pv361373 : PrimeValue := ⟨361373, pr361373⟩
private theorem pr361409 : PrimeCertificate 361409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5647]) (by decide +kernel)
def pv361409 : PrimeValue := ⟨361409, pr361409⟩
private theorem pr361433 : PrimeCertificate 361433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv45179]) (by decide +kernel)
def pv361433 : PrimeValue := ⟨361433, pr361433⟩
private theorem pr361451 : PrimeCertificate 361451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7229]) (by decide +kernel)
def pv361451 : PrimeValue := ⟨361451, pr361451⟩
private theorem pr361481 : PrimeCertificate 361481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv1291]) (by decide +kernel)
def pv361481 : PrimeValue := ⟨361481, pr361481⟩
private theorem pr361549 : PrimeCertificate 361549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv83]) (by decide +kernel)
def pv361549 : PrimeValue := ⟨361549, pr361549⟩
private theorem pr361637 : PrimeCertificate 361637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv8219]) (by decide +kernel)
def pv361637 : PrimeValue := ⟨361637, pr361637⟩
private theorem pr361643 : PrimeCertificate 361643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv2477]) (by decide +kernel)
def pv361643 : PrimeValue := ⟨361643, pr361643⟩
private theorem pr361769 : PrimeCertificate 361769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv4111]) (by decide +kernel)
def pv361769 : PrimeValue := ⟨361769, pr361769⟩
private theorem pr361787 : PrimeCertificate 361787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv4889]) (by decide +kernel)
def pv361787 : PrimeValue := ⟨361787, pr361787⟩
private theorem pr361793 : PrimeCertificate 361793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5653]) (by decide +kernel)
def pv361793 : PrimeValue := ⟨361793, pr361793⟩
private theorem pr361843 : PrimeCertificate 361843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv4639]) (by decide +kernel)
def pv361843 : PrimeValue := ⟨361843, pr361843⟩
private theorem pr361901 : PrimeCertificate 361901 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv11,pv47]) (by decide +kernel)
def pv361901 : PrimeValue := ⟨361901, pr361901⟩
private theorem pr361919 : PrimeCertificate 361919 :=
  certifyPrime (q := pv17) (ls := [pv2,pv180959]) (by decide +kernel)
def pv361919 : PrimeValue := ⟨361919, pr361919⟩
private theorem pr361961 : PrimeCertificate 361961 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv9049]) (by decide +kernel)
def pv361961 : PrimeValue := ⟨361961, pr361961⟩
private theorem pr361979 : PrimeCertificate 361979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv79]) (by decide +kernel)
def pv361979 : PrimeValue := ⟨361979, pr361979⟩
private theorem pr361993 : PrimeCertificate 361993 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv15083]) (by decide +kernel)
def pv361993 : PrimeValue := ⟨361993, pr361993⟩
private theorem pr362003 : PrimeCertificate 362003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181001]) (by decide +kernel)
def pv362003 : PrimeValue := ⟨362003, pr362003⟩
private theorem pr362093 : PrimeCertificate 362093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv90523]) (by decide +kernel)
def pv362093 : PrimeValue := ⟨362093, pr362093⟩
private theorem pr362099 : PrimeCertificate 362099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv109,pv151]) (by decide +kernel)
def pv362099 : PrimeValue := ⟨362099, pr362099⟩
private theorem pr362137 : PrimeCertificate 362137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv79,pv191]) (by decide +kernel)
def pv362137 : PrimeValue := ⟨362137, pr362137⟩
private theorem pr362161 : PrimeCertificate 362161 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv503]) (by decide +kernel)
def pv362161 : PrimeValue := ⟨362161, pr362161⟩
private theorem pr362177 : PrimeCertificate 362177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5659]) (by decide +kernel)
def pv362177 : PrimeValue := ⟨362177, pr362177⟩
private theorem pr362203 : PrimeCertificate 362203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv53,pv67]) (by decide +kernel)
def pv362203 : PrimeValue := ⟨362203, pr362203⟩
private theorem pr362237 : PrimeCertificate 362237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv761]) (by decide +kernel)
def pv362237 : PrimeValue := ⟨362237, pr362237⟩
private theorem pr362291 : PrimeCertificate 362291 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv36229]) (by decide +kernel)
def pv362291 : PrimeValue := ⟨362291, pr362291⟩
private theorem pr362303 : PrimeCertificate 362303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv107,pv1693]) (by decide +kernel)
def pv362303 : PrimeValue := ⟨362303, pr362303⟩
private theorem pr362347 : PrimeCertificate 362347 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv131,pv461]) (by decide +kernel)
def pv362347 : PrimeValue := ⟨362347, pr362347⟩
private theorem pr362353 : PrimeCertificate 362353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7549]) (by decide +kernel)
def pv362353 : PrimeValue := ⟨362353, pr362353⟩
private theorem pr362377 : PrimeCertificate 362377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv719]) (by decide +kernel)
def pv362377 : PrimeValue := ⟨362377, pr362377⟩
private theorem pr362381 : PrimeCertificate 362381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv18119]) (by decide +kernel)
def pv362381 : PrimeValue := ⟨362381, pr362381⟩
private theorem pr362429 : PrimeCertificate 362429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv8237]) (by decide +kernel)
def pv362429 : PrimeValue := ⟨362429, pr362429⟩
private theorem pr362431 : PrimeCertificate 362431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4027]) (by decide +kernel)
def pv362431 : PrimeValue := ⟨362431, pr362431⟩
private theorem pr362473 : PrimeCertificate 362473 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv1373]) (by decide +kernel)
def pv362473 : PrimeValue := ⟨362473, pr362473⟩
private theorem pr362521 : PrimeCertificate 362521 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv19,pv53]) (by decide +kernel)
def pv362521 : PrimeValue := ⟨362521, pr362521⟩
private theorem pr362569 : PrimeCertificate 362569 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv15107]) (by decide +kernel)
def pv362569 : PrimeValue := ⟨362569, pr362569⟩
private theorem pr362707 : PrimeCertificate 362707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv991]) (by decide +kernel)
def pv362707 : PrimeValue := ⟨362707, pr362707⟩
private theorem pr362723 : PrimeCertificate 362723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181361]) (by decide +kernel)
def pv362723 : PrimeValue := ⟨362723, pr362723⟩
private theorem pr362753 : PrimeCertificate 362753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv109]) (by decide +kernel)
def pv362753 : PrimeValue := ⟨362753, pr362753⟩
private theorem pr362759 : PrimeCertificate 362759 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv1499]) (by decide +kernel)
def pv362759 : PrimeValue := ⟨362759, pr362759⟩
private theorem pr362801 : PrimeCertificate 362801 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv907]) (by decide +kernel)
def pv362801 : PrimeValue := ⟨362801, pr362801⟩
private theorem pr362903 : PrimeCertificate 362903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv421,pv431]) (by decide +kernel)
def pv362903 : PrimeValue := ⟨362903, pr362903⟩
private theorem pr362911 : PrimeCertificate 362911 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv12097]) (by decide +kernel)
def pv362911 : PrimeValue := ⟨362911, pr362911⟩
private theorem pr362969 : PrimeCertificate 362969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv769]) (by decide +kernel)
def pv362969 : PrimeValue := ⟨362969, pr362969⟩
private theorem pr362977 : PrimeCertificate 362977 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv19,pv199]) (by decide +kernel)
def pv362977 : PrimeValue := ⟨362977, pr362977⟩
private theorem pr362983 : PrimeCertificate 362983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv60497]) (by decide +kernel)
def pv362983 : PrimeValue := ⟨362983, pr362983⟩
private theorem pr362987 : PrimeCertificate 362987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv607]) (by decide +kernel)
def pv362987 : PrimeValue := ⟨362987, pr362987⟩
private theorem pr363017 : PrimeCertificate 363017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv45377]) (by decide +kernel)
def pv363017 : PrimeValue := ⟨363017, pr363017⟩
private theorem pr363037 : PrimeCertificate 363037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30253]) (by decide +kernel)
def pv363037 : PrimeValue := ⟨363037, pr363037⟩
private theorem pr363043 : PrimeCertificate 363043 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv363043 : PrimeValue := ⟨363043, pr363043⟩
private theorem pr363047 : PrimeCertificate 363047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv181523]) (by decide +kernel)
def pv363047 : PrimeValue := ⟨363047, pr363047⟩
private theorem pr363061 : PrimeCertificate 363061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2017]) (by decide +kernel)
def pv363061 : PrimeValue := ⟨363061, pr363061⟩
private theorem pr363149 : PrimeCertificate 363149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv90787]) (by decide +kernel)
def pv363149 : PrimeValue := ⟨363149, pr363149⟩
private theorem pr363173 : PrimeCertificate 363173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv90793]) (by decide +kernel)
def pv363173 : PrimeValue := ⟨363173, pr363173⟩
private theorem pr363179 : PrimeCertificate 363179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv43,pv103]) (by decide +kernel)
def pv363179 : PrimeValue := ⟨363179, pr363179⟩
private theorem pr363257 : PrimeCertificate 363257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv2671]) (by decide +kernel)
def pv363257 : PrimeValue := ⟨363257, pr363257⟩
private theorem pr363269 : PrimeCertificate 363269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197,pv461]) (by decide +kernel)
def pv363269 : PrimeValue := ⟨363269, pr363269⟩
private theorem pr363317 : PrimeCertificate 363317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv1489]) (by decide +kernel)
def pv363317 : PrimeValue := ⟨363317, pr363317⟩
private theorem pr363329 : PrimeCertificate 363329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv811]) (by decide +kernel)
def pv363329 : PrimeValue := ⟨363329, pr363329⟩
private theorem pr363367 : PrimeCertificate 363367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2243]) (by decide +kernel)
def pv363367 : PrimeValue := ⟨363367, pr363367⟩
private theorem pr363373 : PrimeCertificate 363373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv107,pv283]) (by decide +kernel)
def pv363373 : PrimeValue := ⟨363373, pr363373⟩
private theorem pr363431 : PrimeCertificate 363431 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv36343]) (by decide +kernel)
def pv363431 : PrimeValue := ⟨363431, pr363431⟩
private theorem pr363491 : PrimeCertificate 363491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv163,pv223]) (by decide +kernel)
def pv363491 : PrimeValue := ⟨363491, pr363491⟩
private theorem pr363497 : PrimeCertificate 363497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv6491]) (by decide +kernel)
def pv363497 : PrimeValue := ⟨363497, pr363497⟩
private theorem pr363523 : PrimeCertificate 363523 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv1409]) (by decide +kernel)
def pv363523 : PrimeValue := ⟨363523, pr363523⟩
private theorem pr363541 : PrimeCertificate 363541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv73,pv83]) (by decide +kernel)
def pv363541 : PrimeValue := ⟨363541, pr363541⟩
private theorem pr363563 : PrimeCertificate 363563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv37]) (by decide +kernel)
def pv363563 : PrimeValue := ⟨363563, pr363563⟩
private theorem pr363577 : PrimeCertificate 363577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv15149]) (by decide +kernel)
def pv363577 : PrimeValue := ⟨363577, pr363577⟩
private theorem pr363611 : PrimeCertificate 363611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv2797]) (by decide +kernel)
def pv363611 : PrimeValue := ⟨363611, pr363611⟩
private theorem pr363619 : PrimeCertificate 363619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20201]) (by decide +kernel)
def pv363619 : PrimeValue := ⟨363619, pr363619⟩
private theorem pr363683 : PrimeCertificate 363683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv61,pv271]) (by decide +kernel)
def pv363683 : PrimeValue := ⟨363683, pr363683⟩
private theorem pr363731 : PrimeCertificate 363731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv36373]) (by decide +kernel)
def pv363731 : PrimeValue := ⟨363731, pr363731⟩
private theorem pr363757 : PrimeCertificate 363757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30313]) (by decide +kernel)
def pv363757 : PrimeValue := ⟨363757, pr363757⟩
private theorem pr363761 : PrimeCertificate 363761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv4547]) (by decide +kernel)
def pv363761 : PrimeValue := ⟨363761, pr363761⟩
private theorem pr363767 : PrimeCertificate 363767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv17,pv823]) (by decide +kernel)
def pv363767 : PrimeValue := ⟨363767, pr363767⟩
private theorem pr363773 : PrimeCertificate 363773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv199,pv457]) (by decide +kernel)
def pv363773 : PrimeValue := ⟨363773, pr363773⟩
private theorem pr363799 : PrimeCertificate 363799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6737]) (by decide +kernel)
def pv363799 : PrimeValue := ⟨363799, pr363799⟩
private theorem pr363829 : PrimeCertificate 363829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30319]) (by decide +kernel)
def pv363829 : PrimeValue := ⟨363829, pr363829⟩
private theorem pr363833 : PrimeCertificate 363833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv73,pv89]) (by decide +kernel)
def pv363833 : PrimeValue := ⟨363833, pr363833⟩
private theorem pr363871 : PrimeCertificate 363871 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv311]) (by decide +kernel)
def pv363871 : PrimeValue := ⟨363871, pr363871⟩
private theorem pr363911 : PrimeCertificate 363911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv151,pv241]) (by decide +kernel)
def pv363911 : PrimeValue := ⟨363911, pr363911⟩
private theorem pr363947 : PrimeCertificate 363947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv71,pv233]) (by decide +kernel)
def pv363947 : PrimeValue := ⟨363947, pr363947⟩
private theorem pr364031 : PrimeCertificate 364031 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv59,pv617]) (by decide +kernel)
def pv364031 : PrimeValue := ⟨364031, pr364031⟩
private theorem pr364103 : PrimeCertificate 364103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv307,pv593]) (by decide +kernel)
def pv364103 : PrimeValue := ⟨364103, pr364103⟩
private theorem pr364129 : PrimeCertificate 364129 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv3793]) (by decide +kernel)
def pv364129 : PrimeValue := ⟨364129, pr364129⟩
private theorem pr364187 : PrimeCertificate 364187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211,pv863]) (by decide +kernel)
def pv364187 : PrimeValue := ⟨364187, pr364187⟩
private theorem pr364213 : PrimeCertificate 364213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv151]) (by decide +kernel)
def pv364213 : PrimeValue := ⟨364213, pr364213⟩
private theorem pr364241 : PrimeCertificate 364241 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv29,pv157]) (by decide +kernel)
def pv364241 : PrimeValue := ⟨364241, pr364241⟩
private theorem pr364267 : PrimeCertificate 364267 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv59]) (by decide +kernel)
def pv364267 : PrimeValue := ⟨364267, pr364267⟩
private theorem pr364289 : PrimeCertificate 364289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1423]) (by decide +kernel)
def pv364289 : PrimeValue := ⟨364289, pr364289⟩
private theorem pr364291 : PrimeCertificate 364291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv12143]) (by decide +kernel)
def pv364291 : PrimeValue := ⟨364291, pr364291⟩
private theorem pr364303 : PrimeCertificate 364303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv547]) (by decide +kernel)
def pv364303 : PrimeValue := ⟨364303, pr364303⟩
private theorem pr364313 : PrimeCertificate 364313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv31,pv113]) (by decide +kernel)
def pv364313 : PrimeValue := ⟨364313, pr364313⟩
private theorem pr364333 : PrimeCertificate 364333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv313]) (by decide +kernel)
def pv364333 : PrimeValue := ⟨364333, pr364333⟩
private theorem pr364337 : PrimeCertificate 364337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv3253]) (by decide +kernel)
def pv364337 : PrimeValue := ⟨364337, pr364337⟩
private theorem pr364349 : PrimeCertificate 364349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv1153]) (by decide +kernel)
def pv364349 : PrimeValue := ⟨364349, pr364349⟩
private theorem pr364373 : PrimeCertificate 364373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv1283]) (by decide +kernel)
def pv364373 : PrimeValue := ⟨364373, pr364373⟩
private theorem pr364411 : PrimeCertificate 364411 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4049]) (by decide +kernel)
def pv364411 : PrimeValue := ⟨364411, pr364411⟩
private theorem pr364433 : PrimeCertificate 364433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22777]) (by decide +kernel)
def pv364433 : PrimeValue := ⟨364433, pr364433⟩
private theorem pr364447 : PrimeCertificate 364447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv397]) (by decide +kernel)
def pv364447 : PrimeValue := ⟨364447, pr364447⟩
private theorem pr364451 : PrimeCertificate 364451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv197]) (by decide +kernel)
def pv364451 : PrimeValue := ⟨364451, pr364451⟩
private theorem pr364471 : PrimeCertificate 364471 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv12149]) (by decide +kernel)
def pv364471 : PrimeValue := ⟨364471, pr364471⟩
private theorem pr364513 : PrimeCertificate 364513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3797]) (by decide +kernel)
def pv364513 : PrimeValue := ⟨364513, pr364513⟩
private theorem pr364541 : PrimeCertificate 364541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1657]) (by decide +kernel)
def pv364541 : PrimeValue := ⟨364541, pr364541⟩
private theorem pr364543 : PrimeCertificate 364543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv60757]) (by decide +kernel)
def pv364543 : PrimeValue := ⟨364543, pr364543⟩
private theorem pr364571 : PrimeCertificate 364571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv36457]) (by decide +kernel)
def pv364571 : PrimeValue := ⟨364571, pr364571⟩
private theorem pr364601 : PrimeCertificate 364601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv1823]) (by decide +kernel)
def pv364601 : PrimeValue := ⟨364601, pr364601⟩
private theorem pr364621 : PrimeCertificate 364621 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv59,pv103]) (by decide +kernel)
def pv364621 : PrimeValue := ⟨364621, pr364621⟩
private theorem pr364657 : PrimeCertificate 364657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71,pv107]) (by decide +kernel)
def pv364657 : PrimeValue := ⟨364657, pr364657⟩
private theorem pr364687 : PrimeCertificate 364687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv457]) (by decide +kernel)
def pv364687 : PrimeValue := ⟨364687, pr364687⟩
private theorem pr364691 : PrimeCertificate 364691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv36469]) (by decide +kernel)
def pv364691 : PrimeValue := ⟨364691, pr364691⟩
private theorem pr364739 : PrimeCertificate 364739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv59,pv281]) (by decide +kernel)
def pv364739 : PrimeValue := ⟨364739, pr364739⟩
private theorem pr364751 : PrimeCertificate 364751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv1459]) (by decide +kernel)
def pv364751 : PrimeValue := ⟨364751, pr364751⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
