/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table073
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table073.pv234191
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table044

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr234191 : PrimeCertificate 234191 :=
  certifyPrime (q := pv43) (ls := [pv2,pv5,pv11,pv2129]) (by decide +kernel)
def pv234191 : PrimeValue := ⟨234191, pr234191⟩
private theorem pr234193 : PrimeCertificate 234193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv41]) (by decide +kernel)
def pv234193 : PrimeValue := ⟨234193, pr234193⟩
private theorem pr234211 : PrimeCertificate 234211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv37,pv211]) (by decide +kernel)
def pv234211 : PrimeValue := ⟨234211, pr234211⟩
private theorem pr234217 : PrimeCertificate 234217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3253]) (by decide +kernel)
def pv234217 : PrimeValue := ⟨234217, pr234217⟩
private theorem pr234293 : PrimeCertificate 234293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv58573]) (by decide +kernel)
def pv234293 : PrimeValue := ⟨234293, pr234293⟩
private theorem pr234323 : PrimeCertificate 234323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv10651]) (by decide +kernel)
def pv234323 : PrimeValue := ⟨234323, pr234323⟩
private theorem pr234331 : PrimeCertificate 234331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv73,pv107]) (by decide +kernel)
def pv234331 : PrimeValue := ⟨234331, pr234331⟩
private theorem pr234341 : PrimeCertificate 234341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11717]) (by decide +kernel)
def pv234341 : PrimeValue := ⟨234341, pr234341⟩
private theorem pr234343 : PrimeCertificate 234343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv277]) (by decide +kernel)
def pv234343 : PrimeValue := ⟨234343, pr234343⟩
private theorem pr234361 : PrimeCertificate 234361 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv234361 : PrimeValue := ⟨234361, pr234361⟩
private theorem pr234383 : PrimeCertificate 234383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv117191]) (by decide +kernel)
def pv234383 : PrimeValue := ⟨234383, pr234383⟩
private theorem pr234431 : PrimeCertificate 234431 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv17,pv197]) (by decide +kernel)
def pv234431 : PrimeValue := ⟨234431, pr234431⟩
private theorem pr234457 : PrimeCertificate 234457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9769]) (by decide +kernel)
def pv234457 : PrimeValue := ⟨234457, pr234457⟩
private theorem pr234463 : PrimeCertificate 234463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1699]) (by decide +kernel)
def pv234463 : PrimeValue := ⟨234463, pr234463⟩
private theorem pr234467 : PrimeCertificate 234467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv1987]) (by decide +kernel)
def pv234467 : PrimeValue := ⟨234467, pr234467⟩
private theorem pr234473 : PrimeCertificate 234473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv53,pv79]) (by decide +kernel)
def pv234473 : PrimeValue := ⟨234473, pr234473⟩
private theorem pr234499 : PrimeCertificate 234499 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv11,pv17,pv19]) (by decide +kernel)
def pv234499 : PrimeValue := ⟨234499, pr234499⟩
private theorem pr234529 : PrimeCertificate 234529 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv349]) (by decide +kernel)
def pv234529 : PrimeValue := ⟨234529, pr234529⟩
private theorem pr234541 : PrimeCertificate 234541 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1303]) (by decide +kernel)
def pv234541 : PrimeValue := ⟨234541, pr234541⟩
private theorem pr234587 : PrimeCertificate 234587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv10663]) (by decide +kernel)
def pv234587 : PrimeValue := ⟨234587, pr234587⟩
private theorem pr234589 : PrimeCertificate 234589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv113,pv173]) (by decide +kernel)
def pv234589 : PrimeValue := ⟨234589, pr234589⟩
private theorem pr234613 : PrimeCertificate 234613 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv234613 : PrimeValue := ⟨234613, pr234613⟩
private theorem pr234629 : PrimeCertificate 234629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv58657]) (by decide +kernel)
def pv234629 : PrimeValue := ⟨234629, pr234629⟩
private theorem pr234683 : PrimeCertificate 234683 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv16763]) (by decide +kernel)
def pv234683 : PrimeValue := ⟨234683, pr234683⟩
private theorem pr234713 : PrimeCertificate 234713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29339]) (by decide +kernel)
def pv234713 : PrimeValue := ⟨234713, pr234713⟩
private theorem pr234727 : PrimeCertificate 234727 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv29,pv71]) (by decide +kernel)
def pv234727 : PrimeValue := ⟨234727, pr234727⟩
private theorem pr234743 : PrimeCertificate 234743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv117371]) (by decide +kernel)
def pv234743 : PrimeValue := ⟨234743, pr234743⟩
private theorem pr234769 : PrimeCertificate 234769 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv67,pv73]) (by decide +kernel)
def pv234769 : PrimeValue := ⟨234769, pr234769⟩
private theorem pr234791 : PrimeCertificate 234791 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv53,pv443]) (by decide +kernel)
def pv234791 : PrimeValue := ⟨234791, pr234791⟩
private theorem pr234799 : PrimeCertificate 234799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv39133]) (by decide +kernel)
def pv234799 : PrimeValue := ⟨234799, pr234799⟩
private theorem pr234809 : PrimeCertificate 234809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv599]) (by decide +kernel)
def pv234809 : PrimeValue := ⟨234809, pr234809⟩
private theorem pr234811 : PrimeCertificate 234811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2609]) (by decide +kernel)
def pv234811 : PrimeValue := ⟨234811, pr234811⟩
private theorem pr234833 : PrimeCertificate 234833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1129]) (by decide +kernel)
def pv234833 : PrimeValue := ⟨234833, pr234833⟩
private theorem pr234847 : PrimeCertificate 234847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4349]) (by decide +kernel)
def pv234847 : PrimeValue := ⟨234847, pr234847⟩
private theorem pr234863 : PrimeCertificate 234863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv117431]) (by decide +kernel)
def pv234863 : PrimeValue := ⟨234863, pr234863⟩
private theorem pr234869 : PrimeCertificate 234869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv827]) (by decide +kernel)
def pv234869 : PrimeValue := ⟨234869, pr234869⟩
private theorem pr234893 : PrimeCertificate 234893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8389]) (by decide +kernel)
def pv234893 : PrimeValue := ⟨234893, pr234893⟩
private theorem pr234907 : PrimeCertificate 234907 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv17,pv47]) (by decide +kernel)
def pv234907 : PrimeValue := ⟨234907, pr234907⟩
private theorem pr234917 : PrimeCertificate 234917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv281]) (by decide +kernel)
def pv234917 : PrimeValue := ⟨234917, pr234917⟩
private theorem pr234931 : PrimeCertificate 234931 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv41,pv191]) (by decide +kernel)
def pv234931 : PrimeValue := ⟨234931, pr234931⟩
private theorem pr234947 : PrimeCertificate 234947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv1487]) (by decide +kernel)
def pv234947 : PrimeValue := ⟨234947, pr234947⟩
private theorem pr234959 : PrimeCertificate 234959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv29,pv4051]) (by decide +kernel)
def pv234959 : PrimeValue := ⟨234959, pr234959⟩
private theorem pr234967 : PrimeCertificate 234967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv39161]) (by decide +kernel)
def pv234967 : PrimeValue := ⟨234967, pr234967⟩
private theorem pr234977 : PrimeCertificate 234977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1049]) (by decide +kernel)
def pv234977 : PrimeValue := ⟨234977, pr234977⟩
private theorem pr234979 : PrimeCertificate 234979 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv39163]) (by decide +kernel)
def pv234979 : PrimeValue := ⟨234979, pr234979⟩
private theorem pr234989 : PrimeCertificate 234989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv4519]) (by decide +kernel)
def pv234989 : PrimeValue := ⟨234989, pr234989⟩
private theorem pr235003 : PrimeCertificate 235003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv739]) (by decide +kernel)
def pv235003 : PrimeValue := ⟨235003, pr235003⟩
private theorem pr235007 : PrimeCertificate 235007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv117503]) (by decide +kernel)
def pv235007 : PrimeValue := ⟨235007, pr235007⟩
private theorem pr235009 : PrimeCertificate 235009 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv235009 : PrimeValue := ⟨235009, pr235009⟩
private theorem pr235043 : PrimeCertificate 235043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv31,pv223]) (by decide +kernel)
def pv235043 : PrimeValue := ⟨235043, pr235043⟩
private theorem pr235051 : PrimeCertificate 235051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1567]) (by decide +kernel)
def pv235051 : PrimeValue := ⟨235051, pr235051⟩
private theorem pr235057 : PrimeCertificate 235057 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv59,pv83]) (by decide +kernel)
def pv235057 : PrimeValue := ⟨235057, pr235057⟩
private theorem pr235091 : PrimeCertificate 235091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23509]) (by decide +kernel)
def pv235091 : PrimeValue := ⟨235091, pr235091⟩
private theorem pr235117 : PrimeCertificate 235117 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv311]) (by decide +kernel)
def pv235117 : PrimeValue := ⟨235117, pr235117⟩
private theorem pr235159 : PrimeCertificate 235159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv509]) (by decide +kernel)
def pv235159 : PrimeValue := ⟨235159, pr235159⟩
private theorem pr235177 : PrimeCertificate 235177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv239]) (by decide +kernel)
def pv235177 : PrimeValue := ⟨235177, pr235177⟩
private theorem pr235199 : PrimeCertificate 235199 :=
  certifyPrime (q := pv19) (ls := [pv2,pv23,pv5113]) (by decide +kernel)
def pv235199 : PrimeValue := ⟨235199, pr235199⟩
private theorem pr235231 : PrimeCertificate 235231 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7841]) (by decide +kernel)
def pv235231 : PrimeValue := ⟨235231, pr235231⟩
private theorem pr235241 : PrimeCertificate 235241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv5881]) (by decide +kernel)
def pv235241 : PrimeValue := ⟨235241, pr235241⟩
private theorem pr235243 : PrimeCertificate 235243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1867]) (by decide +kernel)
def pv235243 : PrimeValue := ⟨235243, pr235243⟩
private theorem pr235273 : PrimeCertificate 235273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9803]) (by decide +kernel)
def pv235273 : PrimeValue := ⟨235273, pr235273⟩
private theorem pr235289 : PrimeCertificate 235289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29411]) (by decide +kernel)
def pv235289 : PrimeValue := ⟨235289, pr235289⟩
private theorem pr235307 : PrimeCertificate 235307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv4057]) (by decide +kernel)
def pv235307 : PrimeValue := ⟨235307, pr235307⟩
private theorem pr235349 : PrimeCertificate 235349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv3461]) (by decide +kernel)
def pv235349 : PrimeValue := ⟨235349, pr235349⟩
private theorem pr235369 : PrimeCertificate 235369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv467]) (by decide +kernel)
def pv235369 : PrimeValue := ⟨235369, pr235369⟩
private theorem pr235397 : PrimeCertificate 235397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1201]) (by decide +kernel)
def pv235397 : PrimeValue := ⟨235397, pr235397⟩
private theorem pr235439 : PrimeCertificate 235439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv67,pv251]) (by decide +kernel)
def pv235439 : PrimeValue := ⟨235439, pr235439⟩
private theorem pr235441 : PrimeCertificate 235441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv109]) (by decide +kernel)
def pv235441 : PrimeValue := ⟨235441, pr235441⟩
private theorem pr235483 : PrimeCertificate 235483 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv3019]) (by decide +kernel)
def pv235483 : PrimeValue := ⟨235483, pr235483⟩
private theorem pr235489 : PrimeCertificate 235489 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv223]) (by decide +kernel)
def pv235489 : PrimeValue := ⟨235489, pr235489⟩
private theorem pr235493 : PrimeCertificate 235493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv521]) (by decide +kernel)
def pv235493 : PrimeValue := ⟨235493, pr235493⟩
private theorem pr235513 : PrimeCertificate 235513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3271]) (by decide +kernel)
def pv235513 : PrimeValue := ⟨235513, pr235513⟩
private theorem pr235519 : PrimeCertificate 235519 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv2309]) (by decide +kernel)
def pv235519 : PrimeValue := ⟨235519, pr235519⟩
private theorem pr235523 : PrimeCertificate 235523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv16823]) (by decide +kernel)
def pv235523 : PrimeValue := ⟨235523, pr235523⟩
private theorem pr235553 : PrimeCertificate 235553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv433]) (by decide +kernel)
def pv235553 : PrimeValue := ⟨235553, pr235553⟩
private theorem pr235601 : PrimeCertificate 235601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv31]) (by decide +kernel)
def pv235601 : PrimeValue := ⟨235601, pr235601⟩
private theorem pr235663 : PrimeCertificate 235663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv31,pv181]) (by decide +kernel)
def pv235663 : PrimeValue := ⟨235663, pr235663⟩
private theorem pr235699 : PrimeCertificate 235699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv163,pv241]) (by decide +kernel)
def pv235699 : PrimeValue := ⟨235699, pr235699⟩
private theorem pr235723 : PrimeCertificate 235723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv2311]) (by decide +kernel)
def pv235723 : PrimeValue := ⟨235723, pr235723⟩
private theorem pr235751 : PrimeCertificate 235751 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv23,pv41]) (by decide +kernel)
def pv235751 : PrimeValue := ⟨235751, pr235751⟩
private theorem pr235783 : PrimeCertificate 235783 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13099]) (by decide +kernel)
def pv235783 : PrimeValue := ⟨235783, pr235783⟩
private theorem pr235787 : PrimeCertificate 235787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv3803]) (by decide +kernel)
def pv235787 : PrimeValue := ⟨235787, pr235787⟩
private theorem pr235789 : PrimeCertificate 235789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv401]) (by decide +kernel)
def pv235789 : PrimeValue := ⟨235789, pr235789⟩
private theorem pr235877 : PrimeCertificate 235877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv541]) (by decide +kernel)
def pv235877 : PrimeValue := ⟨235877, pr235877⟩
private theorem pr235889 : PrimeCertificate 235889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv641]) (by decide +kernel)
def pv235889 : PrimeValue := ⟨235889, pr235889⟩
private theorem pr235891 : PrimeCertificate 235891 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2621]) (by decide +kernel)
def pv235891 : PrimeValue := ⟨235891, pr235891⟩
private theorem pr235901 : PrimeCertificate 235901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv337]) (by decide +kernel)
def pv235901 : PrimeValue := ⟨235901, pr235901⟩
private theorem pr235951 : PrimeCertificate 235951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv235951 : PrimeValue := ⟨235951, pr235951⟩
private theorem pr235967 : PrimeCertificate 235967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv127,pv929]) (by decide +kernel)
def pv235967 : PrimeValue := ⟨235967, pr235967⟩
private theorem pr235979 : PrimeCertificate 235979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv117989]) (by decide +kernel)
def pv235979 : PrimeValue := ⟨235979, pr235979⟩
private theorem pr236021 : PrimeCertificate 236021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11801]) (by decide +kernel)
def pv236021 : PrimeValue := ⟨236021, pr236021⟩
private theorem pr236053 : PrimeCertificate 236053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79,pv83]) (by decide +kernel)
def pv236053 : PrimeValue := ⟨236053, pr236053⟩
private theorem pr236063 : PrimeCertificate 236063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv53,pv131]) (by decide +kernel)
def pv236063 : PrimeValue := ⟨236063, pr236063⟩
private theorem pr236069 : PrimeCertificate 236069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8431]) (by decide +kernel)
def pv236069 : PrimeValue := ⟨236069, pr236069⟩
private theorem pr236077 : PrimeCertificate 236077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103,pv191]) (by decide +kernel)
def pv236077 : PrimeValue := ⟨236077, pr236077⟩
private theorem pr236107 : PrimeCertificate 236107 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1009]) (by decide +kernel)
def pv236107 : PrimeValue := ⟨236107, pr236107⟩
private theorem pr236111 : PrimeCertificate 236111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv3373]) (by decide +kernel)
def pv236111 : PrimeValue := ⟨236111, pr236111⟩
private theorem pr236129 : PrimeCertificate 236129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv157]) (by decide +kernel)
def pv236129 : PrimeValue := ⟨236129, pr236129⟩
private theorem pr236143 : PrimeCertificate 236143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4373]) (by decide +kernel)
def pv236143 : PrimeValue := ⟨236143, pr236143⟩
private theorem pr236153 : PrimeCertificate 236153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv4217]) (by decide +kernel)
def pv236153 : PrimeValue := ⟨236153, pr236153⟩
private theorem pr236209 : PrimeCertificate 236209 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv19,pv37]) (by decide +kernel)
def pv236209 : PrimeValue := ⟨236209, pr236209⟩
private theorem pr236219 : PrimeCertificate 236219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv1423]) (by decide +kernel)
def pv236219 : PrimeValue := ⟨236219, pr236219⟩
private theorem pr236261 : PrimeCertificate 236261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11813]) (by decide +kernel)
def pv236261 : PrimeValue := ⟨236261, pr236261⟩
private theorem pr236293 : PrimeCertificate 236293 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv29,pv97]) (by decide +kernel)
def pv236293 : PrimeValue := ⟨236293, pr236293⟩
private theorem pr236323 : PrimeCertificate 236323 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv691]) (by decide +kernel)
def pv236323 : PrimeValue := ⟨236323, pr236323⟩
private theorem pr236333 : PrimeCertificate 236333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59083]) (by decide +kernel)
def pv236333 : PrimeValue := ⟨236333, pr236333⟩
private theorem pr236339 : PrimeCertificate 236339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv118169]) (by decide +kernel)
def pv236339 : PrimeValue := ⟨236339, pr236339⟩
private theorem pr236381 : PrimeCertificate 236381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv223]) (by decide +kernel)
def pv236381 : PrimeValue := ⟨236381, pr236381⟩
private theorem pr236399 : PrimeCertificate 236399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv19,pv6221]) (by decide +kernel)
def pv236399 : PrimeValue := ⟨236399, pr236399⟩
private theorem pr236407 : PrimeCertificate 236407 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv41]) (by decide +kernel)
def pv236407 : PrimeValue := ⟨236407, pr236407⟩
private theorem pr236429 : PrimeCertificate 236429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59107]) (by decide +kernel)
def pv236429 : PrimeValue := ⟨236429, pr236429⟩
private theorem pr236449 : PrimeCertificate 236449 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv821]) (by decide +kernel)
def pv236449 : PrimeValue := ⟨236449, pr236449⟩
private theorem pr236461 : PrimeCertificate 236461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv563]) (by decide +kernel)
def pv236461 : PrimeValue := ⟨236461, pr236461⟩
private theorem pr236503 : PrimeCertificate 236503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1877]) (by decide +kernel)
def pv236503 : PrimeValue := ⟨236503, pr236503⟩
private theorem pr236507 : PrimeCertificate 236507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv118253]) (by decide +kernel)
def pv236507 : PrimeValue := ⟨236507, pr236507⟩
private theorem pr236527 : PrimeCertificate 236527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv499]) (by decide +kernel)
def pv236527 : PrimeValue := ⟨236527, pr236527⟩
private theorem pr236563 : PrimeCertificate 236563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv443]) (by decide +kernel)
def pv236563 : PrimeValue := ⟨236563, pr236563⟩
private theorem pr236573 : PrimeCertificate 236573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv71]) (by decide +kernel)
def pv236573 : PrimeValue := ⟨236573, pr236573⟩
private theorem pr236609 : PrimeCertificate 236609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3697]) (by decide +kernel)
def pv236609 : PrimeValue := ⟨236609, pr236609⟩
private theorem pr236627 : PrimeCertificate 236627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv479]) (by decide +kernel)
def pv236627 : PrimeValue := ⟨236627, pr236627⟩
private theorem pr236653 : PrimeCertificate 236653 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv37,pv41]) (by decide +kernel)
def pv236653 : PrimeValue := ⟨236653, pr236653⟩
private theorem pr236699 : PrimeCertificate 236699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv29,pv53]) (by decide +kernel)
def pv236699 : PrimeValue := ⟨236699, pr236699⟩
private theorem pr236701 : PrimeCertificate 236701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv263]) (by decide +kernel)
def pv236701 : PrimeValue := ⟨236701, pr236701⟩
private theorem pr236713 : PrimeCertificate 236713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1409]) (by decide +kernel)
def pv236713 : PrimeValue := ⟨236713, pr236713⟩
private theorem pr236737 : PrimeCertificate 236737 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv137]) (by decide +kernel)
def pv236737 : PrimeValue := ⟨236737, pr236737⟩
private theorem pr236749 : PrimeCertificate 236749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv109,pv181]) (by decide +kernel)
def pv236749 : PrimeValue := ⟨236749, pr236749⟩
private theorem pr236773 : PrimeCertificate 236773 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv6577]) (by decide +kernel)
def pv236773 : PrimeValue := ⟨236773, pr236773⟩
private theorem pr236783 : PrimeCertificate 236783 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv1301]) (by decide +kernel)
def pv236783 : PrimeValue := ⟨236783, pr236783⟩
private theorem pr236813 : PrimeCertificate 236813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv811]) (by decide +kernel)
def pv236813 : PrimeValue := ⟨236813, pr236813⟩
private theorem pr236881 : PrimeCertificate 236881 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv47]) (by decide +kernel)
def pv236881 : PrimeValue := ⟨236881, pr236881⟩
private theorem pr236891 : PrimeCertificate 236891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23689]) (by decide +kernel)
def pv236891 : PrimeValue := ⟨236891, pr236891⟩
private theorem pr236893 : PrimeCertificate 236893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1039]) (by decide +kernel)
def pv236893 : PrimeValue := ⟨236893, pr236893⟩
private theorem pr236897 : PrimeCertificate 236897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv673]) (by decide +kernel)
def pv236897 : PrimeValue := ⟨236897, pr236897⟩
private theorem pr236909 : PrimeCertificate 236909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8461]) (by decide +kernel)
def pv236909 : PrimeValue := ⟨236909, pr236909⟩
private theorem pr236983 : PrimeCertificate 236983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv127,pv311]) (by decide +kernel)
def pv236983 : PrimeValue := ⟨236983, pr236983⟩
private theorem pr236993 : PrimeCertificate 236993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23]) (by decide +kernel)
def pv236993 : PrimeValue := ⟨236993, pr236993⟩
private theorem pr237011 : PrimeCertificate 237011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv137,pv173]) (by decide +kernel)
def pv237011 : PrimeValue := ⟨237011, pr237011⟩
private theorem pr237019 : PrimeCertificate 237019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv39503]) (by decide +kernel)
def pv237019 : PrimeValue := ⟨237019, pr237019⟩
private theorem pr237043 : PrimeCertificate 237043 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1013]) (by decide +kernel)
def pv237043 : PrimeValue := ⟨237043, pr237043⟩
private theorem pr237067 : PrimeCertificate 237067 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv39511]) (by decide +kernel)
def pv237067 : PrimeValue := ⟨237067, pr237067⟩
private theorem pr237071 : PrimeCertificate 237071 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv151,pv157]) (by decide +kernel)
def pv237071 : PrimeValue := ⟨237071, pr237071⟩
private theorem pr237073 : PrimeCertificate 237073 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv11,pv449]) (by decide +kernel)
def pv237073 : PrimeValue := ⟨237073, pr237073⟩
private theorem pr237137 : PrimeCertificate 237137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14821]) (by decide +kernel)
def pv237137 : PrimeValue := ⟨237137, pr237137⟩
private theorem pr237151 : PrimeCertificate 237151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv31]) (by decide +kernel)
def pv237151 : PrimeValue := ⟨237151, pr237151⟩
private theorem pr237163 : PrimeCertificate 237163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv47]) (by decide +kernel)
def pv237163 : PrimeValue := ⟨237163, pr237163⟩
private theorem pr237173 : PrimeCertificate 237173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv4561]) (by decide +kernel)
def pv237173 : PrimeValue := ⟨237173, pr237173⟩
private theorem pr237179 : PrimeCertificate 237179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv118589]) (by decide +kernel)
def pv237179 : PrimeValue := ⟨237179, pr237179⟩
private theorem pr237233 : PrimeCertificate 237233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14827]) (by decide +kernel)
def pv237233 : PrimeValue := ⟨237233, pr237233⟩
private theorem pr237271 : PrimeCertificate 237271 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv719]) (by decide +kernel)
def pv237271 : PrimeValue := ⟨237271, pr237271⟩
private theorem pr237277 : PrimeCertificate 237277 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv237277 : PrimeValue := ⟨237277, pr237277⟩
private theorem pr237287 : PrimeCertificate 237287 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17,pv997]) (by decide +kernel)
def pv237287 : PrimeValue := ⟨237287, pr237287⟩
private theorem pr237313 : PrimeCertificate 237313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv237313 : PrimeValue := ⟨237313, pr237313⟩
private theorem pr237331 : PrimeCertificate 237331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv293]) (by decide +kernel)
def pv237331 : PrimeValue := ⟨237331, pr237331⟩
private theorem pr237343 : PrimeCertificate 237343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv5651]) (by decide +kernel)
def pv237343 : PrimeValue := ⟨237343, pr237343⟩
private theorem pr237361 : PrimeCertificate 237361 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv23,pv43]) (by decide +kernel)
def pv237361 : PrimeValue := ⟨237361, pr237361⟩
private theorem pr237373 : PrimeCertificate 237373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv131,pv151]) (by decide +kernel)
def pv237373 : PrimeValue := ⟨237373, pr237373⟩
private theorem pr237379 : PrimeCertificate 237379 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv39563]) (by decide +kernel)
def pv237379 : PrimeValue := ⟨237379, pr237379⟩
private theorem pr237401 : PrimeCertificate 237401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1187]) (by decide +kernel)
def pv237401 : PrimeValue := ⟨237401, pr237401⟩
private theorem pr237467 : PrimeCertificate 237467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv3209]) (by decide +kernel)
def pv237467 : PrimeValue := ⟨237467, pr237467⟩
private theorem pr237571 : PrimeCertificate 237571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7919]) (by decide +kernel)
def pv237571 : PrimeValue := ⟨237571, pr237571⟩
private theorem pr237619 : PrimeCertificate 237619 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv43,pv307]) (by decide +kernel)
def pv237619 : PrimeValue := ⟨237619, pr237619⟩
private theorem pr237673 : PrimeCertificate 237673 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv3301]) (by decide +kernel)
def pv237673 : PrimeValue := ⟨237673, pr237673⟩
private theorem pr237683 : PrimeCertificate 237683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv5167]) (by decide +kernel)
def pv237683 : PrimeValue := ⟨237683, pr237683⟩
private theorem pr237689 : PrimeCertificate 237689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv37,pv73]) (by decide +kernel)
def pv237689 : PrimeValue := ⟨237689, pr237689⟩
private theorem pr237701 : PrimeCertificate 237701 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2377]) (by decide +kernel)
def pv237701 : PrimeValue := ⟨237701, pr237701⟩
private theorem pr237733 : PrimeCertificate 237733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1801]) (by decide +kernel)
def pv237733 : PrimeValue := ⟨237733, pr237733⟩
private theorem pr237737 : PrimeCertificate 237737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29717]) (by decide +kernel)
def pv237737 : PrimeValue := ⟨237737, pr237737⟩
private theorem pr237749 : PrimeCertificate 237749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1213]) (by decide +kernel)
def pv237749 : PrimeValue := ⟨237749, pr237749⟩
private theorem pr237763 : PrimeCertificate 237763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv37]) (by decide +kernel)
def pv237763 : PrimeValue := ⟨237763, pr237763⟩
private theorem pr237767 : PrimeCertificate 237767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv6257]) (by decide +kernel)
def pv237767 : PrimeValue := ⟨237767, pr237767⟩
private theorem pr237781 : PrimeCertificate 237781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1321]) (by decide +kernel)
def pv237781 : PrimeValue := ⟨237781, pr237781⟩
private theorem pr237791 : PrimeCertificate 237791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv43,pv79]) (by decide +kernel)
def pv237791 : PrimeValue := ⟨237791, pr237791⟩
private theorem pr237821 : PrimeCertificate 237821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv23,pv47]) (by decide +kernel)
def pv237821 : PrimeValue := ⟨237821, pr237821⟩
private theorem pr237857 : PrimeCertificate 237857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7433]) (by decide +kernel)
def pv237857 : PrimeValue := ⟨237857, pr237857⟩
private theorem pr237859 : PrimeCertificate 237859 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29,pv1367]) (by decide +kernel)
def pv237859 : PrimeValue := ⟨237859, pr237859⟩
private theorem pr237877 : PrimeCertificate 237877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv461]) (by decide +kernel)
def pv237877 : PrimeValue := ⟨237877, pr237877⟩
private theorem pr237901 : PrimeCertificate 237901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv61]) (by decide +kernel)
def pv237901 : PrimeValue := ⟨237901, pr237901⟩
private theorem pr237911 : PrimeCertificate 237911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv37,pv643]) (by decide +kernel)
def pv237911 : PrimeValue := ⟨237911, pr237911⟩
private theorem pr237929 : PrimeCertificate 237929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29741]) (by decide +kernel)
def pv237929 : PrimeValue := ⟨237929, pr237929⟩
private theorem pr237959 : PrimeCertificate 237959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv23,pv739]) (by decide +kernel)
def pv237959 : PrimeValue := ⟨237959, pr237959⟩
private theorem pr237971 : PrimeCertificate 237971 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv53,pv449]) (by decide +kernel)
def pv237971 : PrimeValue := ⟨237971, pr237971⟩
private theorem pr237973 : PrimeCertificate 237973 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv2833]) (by decide +kernel)
def pv237973 : PrimeValue := ⟨237973, pr237973⟩
private theorem pr237977 : PrimeCertificate 237977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv151,pv197]) (by decide +kernel)
def pv237977 : PrimeValue := ⟨237977, pr237977⟩
private theorem pr238009 : PrimeCertificate 238009 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv47,pv211]) (by decide +kernel)
def pv238009 : PrimeValue := ⟨238009, pr238009⟩
private theorem pr238019 : PrimeCertificate 238019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv31,pv349]) (by decide +kernel)
def pv238019 : PrimeValue := ⟨238019, pr238019⟩
private theorem pr238031 : PrimeCertificate 238031 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv1831]) (by decide +kernel)
def pv238031 : PrimeValue := ⟨238031, pr238031⟩
private theorem pr238037 : PrimeCertificate 238037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59509]) (by decide +kernel)
def pv238037 : PrimeValue := ⟨238037, pr238037⟩
private theorem pr238081 : PrimeCertificate 238081 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv238081 : PrimeValue := ⟨238081, pr238081⟩
private theorem pr238099 : PrimeCertificate 238099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv5669]) (by decide +kernel)
def pv238099 : PrimeValue := ⟨238099, pr238099⟩
private theorem pr238103 : PrimeCertificate 238103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv47,pv149]) (by decide +kernel)
def pv238103 : PrimeValue := ⟨238103, pr238103⟩
private theorem pr238109 : PrimeCertificate 238109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv241]) (by decide +kernel)
def pv238109 : PrimeValue := ⟨238109, pr238109⟩
private theorem pr238141 : PrimeCertificate 238141 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv238141 : PrimeValue := ⟨238141, pr238141⟩
private theorem pr238157 : PrimeCertificate 238157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59539]) (by decide +kernel)
def pv238157 : PrimeValue := ⟨238157, pr238157⟩
private theorem pr238159 : PrimeCertificate 238159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv101,pv131]) (by decide +kernel)
def pv238159 : PrimeValue := ⟨238159, pr238159⟩
private theorem pr238163 : PrimeCertificate 238163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193,pv617]) (by decide +kernel)
def pv238163 : PrimeValue := ⟨238163, pr238163⟩
private theorem pr238171 : PrimeCertificate 238171 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv467]) (by decide +kernel)
def pv238171 : PrimeValue := ⟨238171, pr238171⟩
private theorem pr238181 : PrimeCertificate 238181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11909]) (by decide +kernel)
def pv238181 : PrimeValue := ⟨238181, pr238181⟩
private theorem pr238207 : PrimeCertificate 238207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv37]) (by decide +kernel)
def pv238207 : PrimeValue := ⟨238207, pr238207⟩
private theorem pr238213 : PrimeCertificate 238213 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv509]) (by decide +kernel)
def pv238213 : PrimeValue := ⟨238213, pr238213⟩
private theorem pr238229 : PrimeCertificate 238229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59557]) (by decide +kernel)
def pv238229 : PrimeValue := ⟨238229, pr238229⟩
private theorem pr238237 : PrimeCertificate 238237 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv19853]) (by decide +kernel)
def pv238237 : PrimeValue := ⟨238237, pr238237⟩
private theorem pr238261 : PrimeCertificate 238261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv19]) (by decide +kernel)
def pv238261 : PrimeValue := ⟨238261, pr238261⟩
private theorem pr238267 : PrimeCertificate 238267 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv31,pv61]) (by decide +kernel)
def pv238267 : PrimeValue := ⟨238267, pr238267⟩
private theorem pr238307 : PrimeCertificate 238307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv43,pv163]) (by decide +kernel)
def pv238307 : PrimeValue := ⟨238307, pr238307⟩
private theorem pr238313 : PrimeCertificate 238313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29789]) (by decide +kernel)
def pv238313 : PrimeValue := ⟨238313, pr238313⟩
private theorem pr238321 : PrimeCertificate 238321 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv331]) (by decide +kernel)
def pv238321 : PrimeValue := ⟨238321, pr238321⟩
private theorem pr238361 : PrimeCertificate 238361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv59,pv101]) (by decide +kernel)
def pv238361 : PrimeValue := ⟨238361, pr238361⟩
private theorem pr238363 : PrimeCertificate 238363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv39727]) (by decide +kernel)
def pv238363 : PrimeValue := ⟨238363, pr238363⟩
private theorem pr238373 : PrimeCertificate 238373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2591]) (by decide +kernel)
def pv238373 : PrimeValue := ⟨238373, pr238373⟩
private theorem pr238417 : PrimeCertificate 238417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4967]) (by decide +kernel)
def pv238417 : PrimeValue := ⟨238417, pr238417⟩
private theorem pr238439 : PrimeCertificate 238439 :=
  certifyPrime (q := pv11) (ls := [pv2,pv29,pv4111]) (by decide +kernel)
def pv238439 : PrimeValue := ⟨238439, pr238439⟩
private theorem pr238451 : PrimeCertificate 238451 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv251]) (by decide +kernel)
def pv238451 : PrimeValue := ⟨238451, pr238451⟩
private theorem pr238463 : PrimeCertificate 238463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv17033]) (by decide +kernel)
def pv238463 : PrimeValue := ⟨238463, pr238463⟩
private theorem pr238477 : PrimeCertificate 238477 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv167]) (by decide +kernel)
def pv238477 : PrimeValue := ⟨238477, pr238477⟩
private theorem pr238481 : PrimeCertificate 238481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv271]) (by decide +kernel)
def pv238481 : PrimeValue := ⟨238481, pr238481⟩
private theorem pr238499 : PrimeCertificate 238499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv9173]) (by decide +kernel)
def pv238499 : PrimeValue := ⟨238499, pr238499⟩
private theorem pr238519 : PrimeCertificate 238519 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv631]) (by decide +kernel)
def pv238519 : PrimeValue := ⟨238519, pr238519⟩
private theorem pr238529 : PrimeCertificate 238529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3727]) (by decide +kernel)
def pv238529 : PrimeValue := ⟨238529, pr238529⟩
private theorem pr238547 : PrimeCertificate 238547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv1549]) (by decide +kernel)
def pv238547 : PrimeValue := ⟨238547, pr238547⟩
private theorem pr238573 : PrimeCertificate 238573 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv238573 : PrimeValue := ⟨238573, pr238573⟩
private theorem pr238627 : PrimeCertificate 238627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv491]) (by decide +kernel)
def pv238627 : PrimeValue := ⟨238627, pr238627⟩
private theorem pr238673 : PrimeCertificate 238673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2131]) (by decide +kernel)
def pv238673 : PrimeValue := ⟨238673, pr238673⟩
private theorem pr238691 : PrimeCertificate 238691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23869]) (by decide +kernel)
def pv238691 : PrimeValue := ⟨238691, pr238691⟩
private theorem pr238723 : PrimeCertificate 238723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv3617]) (by decide +kernel)
def pv238723 : PrimeValue := ⟨238723, pr238723⟩
private theorem pr238727 : PrimeCertificate 238727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv119363]) (by decide +kernel)
def pv238727 : PrimeValue := ⟨238727, pr238727⟩
private theorem pr238729 : PrimeCertificate 238729 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv238729 : PrimeValue := ⟨238729, pr238729⟩
private theorem pr238759 : PrimeCertificate 238759 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv3061]) (by decide +kernel)
def pv238759 : PrimeValue := ⟨238759, pr238759⟩
private theorem pr238801 : PrimeCertificate 238801 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv199]) (by decide +kernel)
def pv238801 : PrimeValue := ⟨238801, pr238801⟩
private theorem pr238829 : PrimeCertificate 238829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59707]) (by decide +kernel)
def pv238829 : PrimeValue := ⟨238829, pr238829⟩
private theorem pr238837 : PrimeCertificate 238837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1531]) (by decide +kernel)
def pv238837 : PrimeValue := ⟨238837, pr238837⟩
private theorem pr238841 : PrimeCertificate 238841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv853]) (by decide +kernel)
def pv238841 : PrimeValue := ⟨238841, pr238841⟩
private theorem pr238853 : PrimeCertificate 238853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211,pv283]) (by decide +kernel)
def pv238853 : PrimeValue := ⟨238853, pr238853⟩
private theorem pr238859 : PrimeCertificate 238859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv119429]) (by decide +kernel)
def pv238859 : PrimeValue := ⟨238859, pr238859⟩
private theorem pr238877 : PrimeCertificate 238877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv61,pv89]) (by decide +kernel)
def pv238877 : PrimeValue := ⟨238877, pr238877⟩
private theorem pr238883 : PrimeCertificate 238883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv113,pv151]) (by decide +kernel)
def pv238883 : PrimeValue := ⟨238883, pr238883⟩
private theorem pr238919 : PrimeCertificate 238919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv7027]) (by decide +kernel)
def pv238919 : PrimeValue := ⟨238919, pr238919⟩
private theorem pr238921 : PrimeCertificate 238921 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv181]) (by decide +kernel)
def pv238921 : PrimeValue := ⟨238921, pr238921⟩
private theorem pr238939 : PrimeCertificate 238939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv5689]) (by decide +kernel)
def pv238939 : PrimeValue := ⟨238939, pr238939⟩
private theorem pr238949 : PrimeCertificate 238949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv41,pv47]) (by decide +kernel)
def pv238949 : PrimeValue := ⟨238949, pr238949⟩
private theorem pr238991 : PrimeCertificate 238991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv23899]) (by decide +kernel)
def pv238991 : PrimeValue := ⟨238991, pr238991⟩
private theorem pr239069 : PrimeCertificate 239069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv1013]) (by decide +kernel)
def pv239069 : PrimeValue := ⟨239069, pr239069⟩
private theorem pr239119 : PrimeCertificate 239119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv3623]) (by decide +kernel)
def pv239119 : PrimeValue := ⟨239119, pr239119⟩
private theorem pr239147 : PrimeCertificate 239147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv1097]) (by decide +kernel)
def pv239147 : PrimeValue := ⟨239147, pr239147⟩
private theorem pr239167 : PrimeCertificate 239167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv103]) (by decide +kernel)
def pv239167 : PrimeValue := ⟨239167, pr239167⟩
private theorem pr239171 : PrimeCertificate 239171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23917]) (by decide +kernel)
def pv239171 : PrimeValue := ⟨239171, pr239171⟩
private theorem pr239201 : PrimeCertificate 239201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv23]) (by decide +kernel)
def pv239201 : PrimeValue := ⟨239201, pr239201⟩
private theorem pr239243 : PrimeCertificate 239243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv53,pv61]) (by decide +kernel)
def pv239243 : PrimeValue := ⟨239243, pr239243⟩
private theorem pr239251 : PrimeCertificate 239251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv29]) (by decide +kernel)
def pv239251 : PrimeValue := ⟨239251, pr239251⟩
private theorem pr239297 : PrimeCertificate 239297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3739]) (by decide +kernel)
def pv239297 : PrimeValue := ⟨239297, pr239297⟩
private theorem pr239329 : PrimeCertificate 239329 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv277]) (by decide +kernel)
def pv239329 : PrimeValue := ⟨239329, pr239329⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
