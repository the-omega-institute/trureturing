/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table100
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table100.pv404483
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table066
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table067

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr404483 : PrimeCertificate 404483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv47,pv331]) (by decide +kernel)
def pv404483 : PrimeValue := ⟨404483, pr404483⟩
private theorem pr404497 : PrimeCertificate 404497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53]) (by decide +kernel)
def pv404497 : PrimeValue := ⟨404497, pr404497⟩
private theorem pr404507 : PrimeCertificate 404507 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv4933]) (by decide +kernel)
def pv404507 : PrimeValue := ⟨404507, pr404507⟩
private theorem pr404531 : PrimeCertificate 404531 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv5779]) (by decide +kernel)
def pv404531 : PrimeValue := ⟨404531, pr404531⟩
private theorem pr404693 : PrimeCertificate 404693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101173]) (by decide +kernel)
def pv404693 : PrimeValue := ⟨404693, pr404693⟩
private theorem pr404699 : PrimeCertificate 404699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv137,pv211]) (by decide +kernel)
def pv404699 : PrimeValue := ⟨404699, pr404699⟩
private theorem pr404713 : PrimeCertificate 404713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv73]) (by decide +kernel)
def pv404713 : PrimeValue := ⟨404713, pr404713⟩
private theorem pr404819 : PrimeCertificate 404819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv202409]) (by decide +kernel)
def pv404819 : PrimeValue := ⟨404819, pr404819⟩
private theorem pr404837 : PrimeCertificate 404837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101209]) (by decide +kernel)
def pv404837 : PrimeValue := ⟨404837, pr404837⟩
private theorem pr404843 : PrimeCertificate 404843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv2851]) (by decide +kernel)
def pv404843 : PrimeValue := ⟨404843, pr404843⟩
private theorem pr404851 : PrimeCertificate 404851 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv2699]) (by decide +kernel)
def pv404851 : PrimeValue := ⟨404851, pr404851⟩
private theorem pr404951 : PrimeCertificate 404951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv89]) (by decide +kernel)
def pv404951 : PrimeValue := ⟨404951, pr404951⟩
private theorem pr404959 : PrimeCertificate 404959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67493]) (by decide +kernel)
def pv404959 : PrimeValue := ⟨404959, pr404959⟩
private theorem pr404977 : PrimeCertificate 404977 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv13,pv59]) (by decide +kernel)
def pv404977 : PrimeValue := ⟨404977, pr404977⟩
private theorem pr404983 : PrimeCertificate 404983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv149,pv151]) (by decide +kernel)
def pv404983 : PrimeValue := ⟨404983, pr404983⟩
private theorem pr405001 : PrimeCertificate 405001 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv405001 : PrimeValue := ⟨405001, pr405001⟩
private theorem pr405011 : PrimeCertificate 405011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv101,pv401]) (by decide +kernel)
def pv405011 : PrimeValue := ⟨405011, pr405011⟩
private theorem pr405029 : PrimeCertificate 405029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv7789]) (by decide +kernel)
def pv405029 : PrimeValue := ⟨405029, pr405029⟩
private theorem pr405037 : PrimeCertificate 405037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11251]) (by decide +kernel)
def pv405037 : PrimeValue := ⟨405037, pr405037⟩
private theorem pr405071 : PrimeCertificate 405071 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv40507]) (by decide +kernel)
def pv405071 : PrimeValue := ⟨405071, pr405071⟩
private theorem pr405157 : PrimeCertificate 405157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1777]) (by decide +kernel)
def pv405157 : PrimeValue := ⟨405157, pr405157⟩
private theorem pr405221 : PrimeCertificate 405221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv20261]) (by decide +kernel)
def pv405221 : PrimeValue := ⟨405221, pr405221⟩
private theorem pr405227 : PrimeCertificate 405227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv202613]) (by decide +kernel)
def pv405227 : PrimeValue := ⟨405227, pr405227⟩
private theorem pr405247 : PrimeCertificate 405247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv29,pv137]) (by decide +kernel)
def pv405247 : PrimeValue := ⟨405247, pr405247⟩
private theorem pr405253 : PrimeCertificate 405253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11257]) (by decide +kernel)
def pv405253 : PrimeValue := ⟨405253, pr405253⟩
private theorem pr405269 : PrimeCertificate 405269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv1427]) (by decide +kernel)
def pv405269 : PrimeValue := ⟨405269, pr405269⟩
private theorem pr405347 : PrimeCertificate 405347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv10667]) (by decide +kernel)
def pv405347 : PrimeValue := ⟨405347, pr405347⟩
private theorem pr405373 : PrimeCertificate 405373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv37,pv83]) (by decide +kernel)
def pv405373 : PrimeValue := ⟨405373, pr405373⟩
private theorem pr405437 : PrimeCertificate 405437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101359]) (by decide +kernel)
def pv405437 : PrimeValue := ⟨405437, pr405437⟩
private theorem pr405487 : PrimeCertificate 405487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2503]) (by decide +kernel)
def pv405487 : PrimeValue := ⟨405487, pr405487⟩
private theorem pr405521 : PrimeCertificate 405521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv137]) (by decide +kernel)
def pv405521 : PrimeValue := ⟨405521, pr405521⟩
private theorem pr405541 : PrimeCertificate 405541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv751]) (by decide +kernel)
def pv405541 : PrimeValue := ⟨405541, pr405541⟩
private theorem pr405599 : PrimeCertificate 405599 :=
  certifyPrime (q := pv19) (ls := [pv2,pv202799]) (by decide +kernel)
def pv405599 : PrimeValue := ⟨405599, pr405599⟩
private theorem pr405611 : PrimeCertificate 405611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47,pv863]) (by decide +kernel)
def pv405611 : PrimeValue := ⟨405611, pr405611⟩
private theorem pr405667 : PrimeCertificate 405667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv727]) (by decide +kernel)
def pv405667 : PrimeValue := ⟨405667, pr405667⟩
private theorem pr405677 : PrimeCertificate 405677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101419]) (by decide +kernel)
def pv405677 : PrimeValue := ⟨405677, pr405677⟩
private theorem pr405683 : PrimeCertificate 405683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv202841]) (by decide +kernel)
def pv405683 : PrimeValue := ⟨405683, pr405683⟩
private theorem pr405689 : PrimeCertificate 405689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv19,pv157]) (by decide +kernel)
def pv405689 : PrimeValue := ⟨405689, pr405689⟩
private theorem pr405701 : PrimeCertificate 405701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4057]) (by decide +kernel)
def pv405701 : PrimeValue := ⟨405701, pr405701⟩
private theorem pr405703 : PrimeCertificate 405703 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv683]) (by decide +kernel)
def pv405703 : PrimeValue := ⟨405703, pr405703⟩
private theorem pr405731 : PrimeCertificate 405731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv3121]) (by decide +kernel)
def pv405731 : PrimeValue := ⟨405731, pr405731⟩
private theorem pr405763 : PrimeCertificate 405763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv9661]) (by decide +kernel)
def pv405763 : PrimeValue := ⟨405763, pr405763⟩
private theorem pr405767 : PrimeCertificate 405767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv8821]) (by decide +kernel)
def pv405767 : PrimeValue := ⟨405767, pr405767⟩
private theorem pr405781 : PrimeCertificate 405781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv6763]) (by decide +kernel)
def pv405781 : PrimeValue := ⟨405781, pr405781⟩
private theorem pr405799 : PrimeCertificate 405799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv1439]) (by decide +kernel)
def pv405799 : PrimeValue := ⟨405799, pr405799⟩
private theorem pr405817 : PrimeCertificate 405817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv457]) (by decide +kernel)
def pv405817 : PrimeValue := ⟨405817, pr405817⟩
private theorem pr405827 : PrimeCertificate 405827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv6997]) (by decide +kernel)
def pv405827 : PrimeValue := ⟨405827, pr405827⟩
private theorem pr405857 : PrimeCertificate 405857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv1153]) (by decide +kernel)
def pv405857 : PrimeValue := ⟨405857, pr405857⟩
private theorem pr405863 : PrimeCertificate 405863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv202931]) (by decide +kernel)
def pv405863 : PrimeValue := ⟨405863, pr405863⟩
private theorem pr405917 : PrimeCertificate 405917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv109]) (by decide +kernel)
def pv405917 : PrimeValue := ⟨405917, pr405917⟩
private theorem pr405959 : PrimeCertificate 405959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv107,pv271]) (by decide +kernel)
def pv405959 : PrimeValue := ⟨405959, pr405959⟩
private theorem pr405967 : PrimeCertificate 405967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv6151]) (by decide +kernel)
def pv405967 : PrimeValue := ⟨405967, pr405967⟩
private theorem pr405997 : PrimeCertificate 405997 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1471]) (by decide +kernel)
def pv405997 : PrimeValue := ⟨405997, pr405997⟩
private theorem pr406027 : PrimeCertificate 406027 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73,pv103]) (by decide +kernel)
def pv406027 : PrimeValue := ⟨406027, pr406027⟩
private theorem pr406093 : PrimeCertificate 406093 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv43,pv787]) (by decide +kernel)
def pv406093 : PrimeValue := ⟨406093, pr406093⟩
private theorem pr406117 : PrimeCertificate 406117 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv389]) (by decide +kernel)
def pv406117 : PrimeValue := ⟨406117, pr406117⟩
private theorem pr406123 : PrimeCertificate 406123 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv113,pv599]) (by decide +kernel)
def pv406123 : PrimeValue := ⟨406123, pr406123⟩
private theorem pr406207 : PrimeCertificate 406207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv22567]) (by decide +kernel)
def pv406207 : PrimeValue := ⟨406207, pr406207⟩
private theorem pr406247 : PrimeCertificate 406247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv229,pv887]) (by decide +kernel)
def pv406247 : PrimeValue := ⟨406247, pr406247⟩
private theorem pr406313 : PrimeCertificate 406313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv50789]) (by decide +kernel)
def pv406313 : PrimeValue := ⟨406313, pr406313⟩
private theorem pr406349 : PrimeCertificate 406349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv31,pv113]) (by decide +kernel)
def pv406349 : PrimeValue := ⟨406349, pr406349⟩
private theorem pr406397 : PrimeCertificate 406397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101599]) (by decide +kernel)
def pv406397 : PrimeValue := ⟨406397, pr406397⟩
private theorem pr406403 : PrimeCertificate 406403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv11953]) (by decide +kernel)
def pv406403 : PrimeValue := ⟨406403, pr406403⟩
private theorem pr406481 : PrimeCertificate 406481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv5081]) (by decide +kernel)
def pv406481 : PrimeValue := ⟨406481, pr406481⟩
private theorem pr406507 : PrimeCertificate 406507 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67751]) (by decide +kernel)
def pv406507 : PrimeValue := ⟨406507, pr406507⟩
private theorem pr406547 : PrimeCertificate 406547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv71,pv409]) (by decide +kernel)
def pv406547 : PrimeValue := ⟨406547, pr406547⟩
private theorem pr406577 : PrimeCertificate 406577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv25411]) (by decide +kernel)
def pv406577 : PrimeValue := ⟨406577, pr406577⟩
private theorem pr406583 : PrimeCertificate 406583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv18481]) (by decide +kernel)
def pv406583 : PrimeValue := ⟨406583, pr406583⟩
private theorem pr406649 : PrimeCertificate 406649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv4621]) (by decide +kernel)
def pv406649 : PrimeValue := ⟨406649, pr406649⟩
private theorem pr406811 : PrimeCertificate 406811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv2393]) (by decide +kernel)
def pv406811 : PrimeValue := ⟨406811, pr406811⟩
private theorem pr406883 : PrimeCertificate 406883 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv29063]) (by decide +kernel)
def pv406883 : PrimeValue := ⟨406883, pr406883⟩
private theorem pr406969 : PrimeCertificate 406969 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31,pv547]) (by decide +kernel)
def pv406969 : PrimeValue := ⟨406969, pr406969⟩
private theorem pr407023 : PrimeCertificate 407023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv881]) (by decide +kernel)
def pv407023 : PrimeValue := ⟨407023, pr407023⟩
private theorem pr407083 : PrimeCertificate 407083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv17,pv307]) (by decide +kernel)
def pv407083 : PrimeValue := ⟨407083, pr407083⟩
private theorem pr407119 : PrimeCertificate 407119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67853]) (by decide +kernel)
def pv407119 : PrimeValue := ⟨407119, pr407119⟩
private theorem pr407203 : PrimeCertificate 407203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67867]) (by decide +kernel)
def pv407203 : PrimeValue := ⟨407203, pr407203⟩
private theorem pr407219 : PrimeCertificate 407219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv29,pv59]) (by decide +kernel)
def pv407219 : PrimeValue := ⟨407219, pr407219⟩
private theorem pr407233 : PrimeCertificate 407233 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv101]) (by decide +kernel)
def pv407233 : PrimeValue := ⟨407233, pr407233⟩
private theorem pr407287 : PrimeCertificate 407287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv407287 : PrimeValue := ⟨407287, pr407287⟩
private theorem pr407291 : PrimeCertificate 407291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv241]) (by decide +kernel)
def pv407291 : PrimeValue := ⟨407291, pr407291⟩
private theorem pr407299 : PrimeCertificate 407299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67883]) (by decide +kernel)
def pv407299 : PrimeValue := ⟨407299, pr407299⟩
private theorem pr407311 : PrimeCertificate 407311 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13577]) (by decide +kernel)
def pv407311 : PrimeValue := ⟨407311, pr407311⟩
private theorem pr407321 : PrimeCertificate 407321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv599]) (by decide +kernel)
def pv407321 : PrimeValue := ⟨407321, pr407321⟩
private theorem pr407347 : PrimeCertificate 407347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67891]) (by decide +kernel)
def pv407347 : PrimeValue := ⟨407347, pr407347⟩
private theorem pr407369 : PrimeCertificate 407369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv3917]) (by decide +kernel)
def pv407369 : PrimeValue := ⟨407369, pr407369⟩
private theorem pr407377 : PrimeCertificate 407377 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv41]) (by decide +kernel)
def pv407377 : PrimeValue := ⟨407377, pr407377⟩
private theorem pr407471 : PrimeCertificate 407471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv5821]) (by decide +kernel)
def pv407471 : PrimeValue := ⟨407471, pr407471⟩
private theorem pr407483 : PrimeCertificate 407483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv2579]) (by decide +kernel)
def pv407483 : PrimeValue := ⟨407483, pr407483⟩
private theorem pr407579 : PrimeCertificate 407579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv203789]) (by decide +kernel)
def pv407579 : PrimeValue := ⟨407579, pr407579⟩
private theorem pr407587 : PrimeCertificate 407587 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67931]) (by decide +kernel)
def pv407587 : PrimeValue := ⟨407587, pr407587⟩
private theorem pr407621 : PrimeCertificate 407621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv89,pv229]) (by decide +kernel)
def pv407621 : PrimeValue := ⟨407621, pr407621⟩
private theorem pr407633 : PrimeCertificate 407633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv349]) (by decide +kernel)
def pv407633 : PrimeValue := ⟨407633, pr407633⟩
private theorem pr407639 : PrimeCertificate 407639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv2647]) (by decide +kernel)
def pv407639 : PrimeValue := ⟨407639, pr407639⟩
private theorem pr407651 : PrimeCertificate 407651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv263]) (by decide +kernel)
def pv407651 : PrimeValue := ⟨407651, pr407651⟩
private theorem pr407657 : PrimeCertificate 407657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv50957]) (by decide +kernel)
def pv407657 : PrimeValue := ⟨407657, pr407657⟩
private theorem pr407669 : PrimeCertificate 407669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101917]) (by decide +kernel)
def pv407669 : PrimeValue := ⟨407669, pr407669⟩
private theorem pr407707 : PrimeCertificate 407707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv5227]) (by decide +kernel)
def pv407707 : PrimeValue := ⟨407707, pr407707⟩
private theorem pr407717 : PrimeCertificate 407717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101929]) (by decide +kernel)
def pv407717 : PrimeValue := ⟨407717, pr407717⟩
private theorem pr407789 : PrimeCertificate 407789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv1051]) (by decide +kernel)
def pv407789 : PrimeValue := ⟨407789, pr407789⟩
private theorem pr407791 : PrimeCertificate 407791 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv197]) (by decide +kernel)
def pv407791 : PrimeValue := ⟨407791, pr407791⟩
private theorem pr407843 : PrimeCertificate 407843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv203921]) (by decide +kernel)
def pv407843 : PrimeValue := ⟨407843, pr407843⟩
private theorem pr407893 : PrimeCertificate 407893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1789]) (by decide +kernel)
def pv407893 : PrimeValue := ⟨407893, pr407893⟩
private theorem pr407923 : PrimeCertificate 407923 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67987]) (by decide +kernel)
def pv407923 : PrimeValue := ⟨407923, pr407923⟩
private theorem pr407959 : PrimeCertificate 407959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67993]) (by decide +kernel)
def pv407959 : PrimeValue := ⟨407959, pr407959⟩
private theorem pr407969 : PrimeCertificate 407969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv19,pv61]) (by decide +kernel)
def pv407969 : PrimeValue := ⟨407969, pr407969⟩
private theorem pr408011 : PrimeCertificate 408011 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv40801]) (by decide +kernel)
def pv408011 : PrimeValue := ⟨408011, pr408011⟩
private theorem pr408071 : PrimeCertificate 408071 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv43,pv73]) (by decide +kernel)
def pv408071 : PrimeValue := ⟨408071, pr408071⟩
private theorem pr408127 : PrimeCertificate 408127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv251,pv271]) (by decide +kernel)
def pv408127 : PrimeValue := ⟨408127, pr408127⟩
private theorem pr408131 : PrimeCertificate 408131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv40813]) (by decide +kernel)
def pv408131 : PrimeValue := ⟨408131, pr408131⟩
private theorem pr408173 : PrimeCertificate 408173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv102043]) (by decide +kernel)
def pv408173 : PrimeValue := ⟨408173, pr408173⟩
private theorem pr408203 : PrimeCertificate 408203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv204101]) (by decide +kernel)
def pv408203 : PrimeValue := ⟨408203, pr408203⟩
private theorem pr408209 : PrimeCertificate 408209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv823]) (by decide +kernel)
def pv408209 : PrimeValue := ⟨408209, pr408209⟩
private theorem pr408217 : PrimeCertificate 408217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv73,pv233]) (by decide +kernel)
def pv408217 : PrimeValue := ⟨408217, pr408217⟩
private theorem pr408223 : PrimeCertificate 408223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv22679]) (by decide +kernel)
def pv408223 : PrimeValue := ⟨408223, pr408223⟩
private theorem pr408283 : PrimeCertificate 408283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv9721]) (by decide +kernel)
def pv408283 : PrimeValue := ⟨408283, pr408283⟩
private theorem pr408341 : PrimeCertificate 408341 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv1201]) (by decide +kernel)
def pv408341 : PrimeValue := ⟨408341, pr408341⟩
private theorem pr408347 : PrimeCertificate 408347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv204173]) (by decide +kernel)
def pv408347 : PrimeValue := ⟨408347, pr408347⟩
private theorem pr408389 : PrimeCertificate 408389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv193]) (by decide +kernel)
def pv408389 : PrimeValue := ⟨408389, pr408389⟩
private theorem pr408433 : PrimeCertificate 408433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv67,pv127]) (by decide +kernel)
def pv408433 : PrimeValue := ⟨408433, pr408433⟩
private theorem pr408437 : PrimeCertificate 408437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv503]) (by decide +kernel)
def pv408437 : PrimeValue := ⟨408437, pr408437⟩
private theorem pr408491 : PrimeCertificate 408491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv40849]) (by decide +kernel)
def pv408491 : PrimeValue := ⟨408491, pr408491⟩
private theorem pr408563 : PrimeCertificate 408563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv379]) (by decide +kernel)
def pv408563 : PrimeValue := ⟨408563, pr408563⟩
private theorem pr408607 : PrimeCertificate 408607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv41,pv151]) (by decide +kernel)
def pv408607 : PrimeValue := ⟨408607, pr408607⟩
private theorem pr408659 : PrimeCertificate 408659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv204329]) (by decide +kernel)
def pv408659 : PrimeValue := ⟨408659, pr408659⟩
private theorem pr408689 : PrimeCertificate 408689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv41,pv89]) (by decide +kernel)
def pv408689 : PrimeValue := ⟨408689, pr408689⟩
private theorem pr408691 : PrimeCertificate 408691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv239]) (by decide +kernel)
def pv408691 : PrimeValue := ⟨408691, pr408691⟩
private theorem pr408701 : PrimeCertificate 408701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61,pv67]) (by decide +kernel)
def pv408701 : PrimeValue := ⟨408701, pr408701⟩
private theorem pr408719 : PrimeCertificate 408719 :=
  certifyPrime (q := pv11) (ls := [pv2,pv204359]) (by decide +kernel)
def pv408719 : PrimeValue := ⟨408719, pr408719⟩
private theorem pr408743 : PrimeCertificate 408743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv204371]) (by decide +kernel)
def pv408743 : PrimeValue := ⟨408743, pr408743⟩
private theorem pr408817 : PrimeCertificate 408817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv167]) (by decide +kernel)
def pv408817 : PrimeValue := ⟨408817, pr408817⟩
private theorem pr408911 : PrimeCertificate 408911 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv103,pv397]) (by decide +kernel)
def pv408911 : PrimeValue := ⟨408911, pr408911⟩
private theorem pr408943 : PrimeCertificate 408943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7573]) (by decide +kernel)
def pv408943 : PrimeValue := ⟨408943, pr408943⟩
private theorem pr408953 : PrimeCertificate 408953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv31,pv97]) (by decide +kernel)
def pv408953 : PrimeValue := ⟨408953, pr408953⟩
private theorem pr408959 : PrimeCertificate 408959 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv29,pv641]) (by decide +kernel)
def pv408959 : PrimeValue := ⟨408959, pr408959⟩
private theorem pr408971 : PrimeCertificate 408971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv40897]) (by decide +kernel)
def pv408971 : PrimeValue := ⟨408971, pr408971⟩
private theorem pr409007 : PrimeCertificate 409007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv15731]) (by decide +kernel)
def pv409007 : PrimeValue := ⟨409007, pr409007⟩
private theorem pr409069 : PrimeCertificate 409069 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv1033]) (by decide +kernel)
def pv409069 : PrimeValue := ⟨409069, pr409069⟩
private theorem pr409163 : PrimeCertificate 409163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv15737]) (by decide +kernel)
def pv409163 : PrimeValue := ⟨409163, pr409163⟩
private theorem pr409217 : PrimeCertificate 409217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv139]) (by decide +kernel)
def pv409217 : PrimeValue := ⟨409217, pr409217⟩
private theorem pr409237 : PrimeCertificate 409237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv509]) (by decide +kernel)
def pv409237 : PrimeValue := ⟨409237, pr409237⟩
private theorem pr409271 : PrimeCertificate 409271 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv40927]) (by decide +kernel)
def pv409271 : PrimeValue := ⟨409271, pr409271⟩
private theorem pr409289 : PrimeCertificate 409289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv4651]) (by decide +kernel)
def pv409289 : PrimeValue := ⟨409289, pr409289⟩
private theorem pr409337 : PrimeCertificate 409337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv2693]) (by decide +kernel)
def pv409337 : PrimeValue := ⟨409337, pr409337⟩
private theorem pr409351 : PrimeCertificate 409351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2729]) (by decide +kernel)
def pv409351 : PrimeValue := ⟨409351, pr409351⟩
private theorem pr409397 : PrimeCertificate 409397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv7873]) (by decide +kernel)
def pv409397 : PrimeValue := ⟨409397, pr409397⟩
private theorem pr409441 : PrimeCertificate 409441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv853]) (by decide +kernel)
def pv409441 : PrimeValue := ⟨409441, pr409441⟩
private theorem pr409499 : PrimeCertificate 409499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv204749]) (by decide +kernel)
def pv409499 : PrimeValue := ⟨409499, pr409499⟩
private theorem pr409523 : PrimeCertificate 409523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv2467]) (by decide +kernel)
def pv409523 : PrimeValue := ⟨409523, pr409523⟩
private theorem pr409573 : PrimeCertificate 409573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv367]) (by decide +kernel)
def pv409573 : PrimeValue := ⟨409573, pr409573⟩
private theorem pr409657 : PrimeCertificate 409657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv101]) (by decide +kernel)
def pv409657 : PrimeValue := ⟨409657, pr409657⟩
private theorem pr409709 : PrimeCertificate 409709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv7879]) (by decide +kernel)
def pv409709 : PrimeValue := ⟨409709, pr409709⟩
private theorem pr409777 : PrimeCertificate 409777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8537]) (by decide +kernel)
def pv409777 : PrimeValue := ⟨409777, pr409777⟩
private theorem pr409781 : PrimeCertificate 409781 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv2927]) (by decide +kernel)
def pv409781 : PrimeValue := ⟨409781, pr409781⟩
private theorem pr409813 : PrimeCertificate 409813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv37,pv71]) (by decide +kernel)
def pv409813 : PrimeValue := ⟨409813, pr409813⟩
private theorem pr409817 : PrimeCertificate 409817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv4657]) (by decide +kernel)
def pv409817 : PrimeValue := ⟨409817, pr409817⟩
private theorem pr409823 : PrimeCertificate 409823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv73,pv401]) (by decide +kernel)
def pv409823 : PrimeValue := ⟨409823, pr409823⟩
private theorem pr409897 : PrimeCertificate 409897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5693]) (by decide +kernel)
def pv409897 : PrimeValue := ⟨409897, pr409897⟩
private theorem pr409901 : PrimeCertificate 409901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4099]) (by decide +kernel)
def pv409901 : PrimeValue := ⟨409901, pr409901⟩
private theorem pr409933 : PrimeCertificate 409933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv193]) (by decide +kernel)
def pv409933 : PrimeValue := ⟨409933, pr409933⟩
private theorem pr409943 : PrimeCertificate 409943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv15767]) (by decide +kernel)
def pv409943 : PrimeValue := ⟨409943, pr409943⟩
private theorem pr409951 : PrimeCertificate 409951 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv911]) (by decide +kernel)
def pv409951 : PrimeValue := ⟨409951, pr409951⟩
private theorem pr409961 : PrimeCertificate 409961 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv37,pv277]) (by decide +kernel)
def pv409961 : PrimeValue := ⟨409961, pr409961⟩
private theorem pr409967 : PrimeCertificate 409967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv204983]) (by decide +kernel)
def pv409967 : PrimeValue := ⟨409967, pr409967⟩
private theorem pr409987 : PrimeCertificate 409987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22777]) (by decide +kernel)
def pv409987 : PrimeValue := ⟨409987, pr409987⟩
private theorem pr410009 : PrimeCertificate 410009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv967]) (by decide +kernel)
def pv410009 : PrimeValue := ⟨410009, pr410009⟩
private theorem pr410093 : PrimeCertificate 410093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv102523]) (by decide +kernel)
def pv410093 : PrimeValue := ⟨410093, pr410093⟩
private theorem pr410143 : PrimeCertificate 410143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv4021]) (by decide +kernel)
def pv410143 : PrimeValue := ⟨410143, pr410143⟩
private theorem pr410171 : PrimeCertificate 410171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41017]) (by decide +kernel)
def pv410171 : PrimeValue := ⟨410171, pr410171⟩
private theorem pr410231 : PrimeCertificate 410231 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv41023]) (by decide +kernel)
def pv410231 : PrimeValue := ⟨410231, pr410231⟩
private theorem pr410233 : PrimeCertificate 410233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17093]) (by decide +kernel)
def pv410233 : PrimeValue := ⟨410233, pr410233⟩
private theorem pr410279 : PrimeCertificate 410279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv17,pv1097]) (by decide +kernel)
def pv410279 : PrimeValue := ⟨410279, pr410279⟩
private theorem pr410339 : PrimeCertificate 410339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv199,pv1031]) (by decide +kernel)
def pv410339 : PrimeValue := ⟨410339, pr410339⟩
private theorem pr410387 : PrimeCertificate 410387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv449,pv457]) (by decide +kernel)
def pv410387 : PrimeValue := ⟨410387, pr410387⟩
private theorem pr410393 : PrimeCertificate 410393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv1193]) (by decide +kernel)
def pv410393 : PrimeValue := ⟨410393, pr410393⟩
private theorem pr410411 : PrimeCertificate 410411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv13,pv41]) (by decide +kernel)
def pv410411 : PrimeValue := ⟨410411, pr410411⟩
private theorem pr410413 : PrimeCertificate 410413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1487]) (by decide +kernel)
def pv410413 : PrimeValue := ⟨410413, pr410413⟩
private theorem pr410453 : PrimeCertificate 410453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv107,pv137]) (by decide +kernel)
def pv410453 : PrimeValue := ⟨410453, pr410453⟩
private theorem pr410477 : PrimeCertificate 410477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv491]) (by decide +kernel)
def pv410477 : PrimeValue := ⟨410477, pr410477⟩
private theorem pr410489 : PrimeCertificate 410489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv3947]) (by decide +kernel)
def pv410489 : PrimeValue := ⟨410489, pr410489⟩
private theorem pr410513 : PrimeCertificate 410513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv25657]) (by decide +kernel)
def pv410513 : PrimeValue := ⟨410513, pr410513⟩
private theorem pr410519 : PrimeCertificate 410519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv83,pv2473]) (by decide +kernel)
def pv410519 : PrimeValue := ⟨410519, pr410519⟩
private theorem pr410561 : PrimeCertificate 410561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1283]) (by decide +kernel)
def pv410561 : PrimeValue := ⟨410561, pr410561⟩
private theorem pr410629 : PrimeCertificate 410629 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv1801]) (by decide +kernel)
def pv410629 : PrimeValue := ⟨410629, pr410629⟩
private theorem pr410651 : PrimeCertificate 410651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv191]) (by decide +kernel)
def pv410651 : PrimeValue := ⟨410651, pr410651⟩
private theorem pr410687 : PrimeCertificate 410687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv47,pv257]) (by decide +kernel)
def pv410687 : PrimeValue := ⟨410687, pr410687⟩
private theorem pr410701 : PrimeCertificate 410701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv410701 : PrimeValue := ⟨410701, pr410701⟩
private theorem pr410741 : PrimeCertificate 410741 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv1867]) (by decide +kernel)
def pv410741 : PrimeValue := ⟨410741, pr410741⟩
private theorem pr410749 : PrimeCertificate 410749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv2633]) (by decide +kernel)
def pv410749 : PrimeValue := ⟨410749, pr410749⟩
private theorem pr410759 : PrimeCertificate 410759 :=
  certifyPrime (q := pv13) (ls := [pv2,pv59]) (by decide +kernel)
def pv410759 : PrimeValue := ⟨410759, pr410759⟩
private theorem pr410801 : PrimeCertificate 410801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv79]) (by decide +kernel)
def pv410801 : PrimeValue := ⟨410801, pr410801⟩
private theorem pr410819 : PrimeCertificate 410819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv569]) (by decide +kernel)
def pv410819 : PrimeValue := ⟨410819, pr410819⟩
private theorem pr410857 : PrimeCertificate 410857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv19,pv53]) (by decide +kernel)
def pv410857 : PrimeValue := ⟨410857, pr410857⟩
private theorem pr410899 : PrimeCertificate 410899 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv68483]) (by decide +kernel)
def pv410899 : PrimeValue := ⟨410899, pr410899⟩
private theorem pr410929 : PrimeCertificate 410929 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv1223]) (by decide +kernel)
def pv410929 : PrimeValue := ⟨410929, pr410929⟩
private theorem pr410999 : PrimeCertificate 410999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv31,pv947]) (by decide +kernel)
def pv410999 : PrimeValue := ⟨410999, pr410999⟩
private theorem pr411031 : PrimeCertificate 411031 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4567]) (by decide +kernel)
def pv411031 : PrimeValue := ⟨411031, pr411031⟩
private theorem pr411049 : PrimeCertificate 411049 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv173]) (by decide +kernel)
def pv411049 : PrimeValue := ⟨411049, pr411049⟩
private theorem pr411071 : PrimeCertificate 411071 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv37,pv101]) (by decide +kernel)
def pv411071 : PrimeValue := ⟨411071, pr411071⟩
private theorem pr411083 : PrimeCertificate 411083 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv29363]) (by decide +kernel)
def pv411083 : PrimeValue := ⟨411083, pr411083⟩
private theorem pr411119 : PrimeCertificate 411119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv205559]) (by decide +kernel)
def pv411119 : PrimeValue := ⟨411119, pr411119⟩
private theorem pr411241 : PrimeCertificate 411241 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv149]) (by decide +kernel)
def pv411241 : PrimeValue := ⟨411241, pr411241⟩
private theorem pr411251 : PrimeCertificate 411251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv47]) (by decide +kernel)
def pv411251 : PrimeValue := ⟨411251, pr411251⟩
private theorem pr411253 : PrimeCertificate 411253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv797]) (by decide +kernel)
def pv411253 : PrimeValue := ⟨411253, pr411253⟩
private theorem pr411311 : PrimeCertificate 411311 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv41131]) (by decide +kernel)
def pv411311 : PrimeValue := ⟨411311, pr411311⟩
private theorem pr411337 : PrimeCertificate 411337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv197]) (by decide +kernel)
def pv411337 : PrimeValue := ⟨411337, pr411337⟩
private theorem pr411371 : PrimeCertificate 411371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv1327]) (by decide +kernel)
def pv411371 : PrimeValue := ⟨411371, pr411371⟩
private theorem pr411421 : PrimeCertificate 411421 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv6857]) (by decide +kernel)
def pv411421 : PrimeValue := ⟨411421, pr411421⟩
private theorem pr411449 : PrimeCertificate 411449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv51431]) (by decide +kernel)
def pv411449 : PrimeValue := ⟨411449, pr411449⟩
private theorem pr411491 : PrimeCertificate 411491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41149]) (by decide +kernel)
def pv411491 : PrimeValue := ⟨411491, pr411491⟩
private theorem pr411527 : PrimeCertificate 411527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv205763]) (by decide +kernel)
def pv411527 : PrimeValue := ⟨411527, pr411527⟩
private theorem pr411563 : PrimeCertificate 411563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv389]) (by decide +kernel)
def pv411563 : PrimeValue := ⟨411563, pr411563⟩
private theorem pr411589 : PrimeCertificate 411589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv103]) (by decide +kernel)
def pv411589 : PrimeValue := ⟨411589, pr411589⟩
private theorem pr411613 : PrimeCertificate 411613 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv34301]) (by decide +kernel)
def pv411613 : PrimeValue := ⟨411613, pr411613⟩
private theorem pr411641 : PrimeCertificate 411641 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv41,pv251]) (by decide +kernel)
def pv411641 : PrimeValue := ⟨411641, pr411641⟩
private theorem pr411667 : PrimeCertificate 411667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv68611]) (by decide +kernel)
def pv411667 : PrimeValue := ⟨411667, pr411667⟩
private theorem pr411679 : PrimeCertificate 411679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv22871]) (by decide +kernel)
def pv411679 : PrimeValue := ⟨411679, pr411679⟩
private theorem pr411683 : PrimeCertificate 411683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv4787]) (by decide +kernel)
def pv411683 : PrimeValue := ⟨411683, pr411683⟩
private theorem pr411707 : PrimeCertificate 411707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv12109]) (by decide +kernel)
def pv411707 : PrimeValue := ⟨411707, pr411707⟩
private theorem pr411721 : PrimeCertificate 411721 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv47,pv73]) (by decide +kernel)
def pv411721 : PrimeValue := ⟨411721, pr411721⟩
private theorem pr411779 : PrimeCertificate 411779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv907]) (by decide +kernel)
def pv411779 : PrimeValue := ⟨411779, pr411779⟩
private theorem pr411809 : PrimeCertificate 411809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv757]) (by decide +kernel)
def pv411809 : PrimeValue := ⟨411809, pr411809⟩
private theorem pr411821 : PrimeCertificate 411821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv349]) (by decide +kernel)
def pv411821 : PrimeValue := ⟨411821, pr411821⟩
private theorem pr411823 : PrimeCertificate 411823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv137,pv167]) (by decide +kernel)
def pv411823 : PrimeValue := ⟨411823, pr411823⟩
private theorem pr411841 : PrimeCertificate 411841 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv411841 : PrimeValue := ⟨411841, pr411841⟩
private theorem pr411883 : PrimeCertificate 411883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv3613]) (by decide +kernel)
def pv411883 : PrimeValue := ⟨411883, pr411883⟩
private theorem pr411919 : PrimeCertificate 411919 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv13,pv5281]) (by decide +kernel)
def pv411919 : PrimeValue := ⟨411919, pr411919⟩
private theorem pr411991 : PrimeCertificate 411991 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv31,pv443]) (by decide +kernel)
def pv411991 : PrimeValue := ⟨411991, pr411991⟩
private theorem pr412019 : PrimeCertificate 412019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv206009]) (by decide +kernel)
def pv412019 : PrimeValue := ⟨412019, pr412019⟩
private theorem pr412031 : PrimeCertificate 412031 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv41203]) (by decide +kernel)
def pv412031 : PrimeValue := ⟨412031, pr412031⟩
private theorem pr412067 : PrimeCertificate 412067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv206033]) (by decide +kernel)
def pv412067 : PrimeValue := ⟨412067, pr412067⟩
private theorem pr412073 : PrimeCertificate 412073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv2711]) (by decide +kernel)
def pv412073 : PrimeValue := ⟨412073, pr412073⟩
private theorem pr412127 : PrimeCertificate 412127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv131]) (by decide +kernel)
def pv412127 : PrimeValue := ⟨412127, pr412127⟩
private theorem pr412147 : PrimeCertificate 412147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv3271]) (by decide +kernel)
def pv412147 : PrimeValue := ⟨412147, pr412147⟩
private theorem pr412171 : PrimeCertificate 412171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv1249]) (by decide +kernel)
def pv412171 : PrimeValue := ⟨412171, pr412171⟩
private theorem pr412277 : PrimeCertificate 412277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103069]) (by decide +kernel)
def pv412277 : PrimeValue := ⟨412277, pr412277⟩
private theorem pr412289 : PrimeCertificate 412289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3221]) (by decide +kernel)
def pv412289 : PrimeValue := ⟨412289, pr412289⟩
private theorem pr412303 : PrimeCertificate 412303 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv6247]) (by decide +kernel)
def pv412303 : PrimeValue := ⟨412303, pr412303⟩
private theorem pr412397 : PrimeCertificate 412397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103099]) (by decide +kernel)
def pv412397 : PrimeValue := ⟨412397, pr412397⟩
private theorem pr412457 : PrimeCertificate 412457 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv43,pv109]) (by decide +kernel)
def pv412457 : PrimeValue := ⟨412457, pr412457⟩
private theorem pr412537 : PrimeCertificate 412537 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17189]) (by decide +kernel)
def pv412537 : PrimeValue := ⟨412537, pr412537⟩
private theorem pr412561 : PrimeCertificate 412561 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv191]) (by decide +kernel)
def pv412561 : PrimeValue := ⟨412561, pr412561⟩
private theorem pr412571 : PrimeCertificate 412571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41257]) (by decide +kernel)
def pv412571 : PrimeValue := ⟨412571, pr412571⟩
private theorem pr412591 : PrimeCertificate 412591 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv809]) (by decide +kernel)
def pv412591 : PrimeValue := ⟨412591, pr412591⟩
private theorem pr412603 : PrimeCertificate 412603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv68767]) (by decide +kernel)
def pv412603 : PrimeValue := ⟨412603, pr412603⟩
private theorem pr412609 : PrimeCertificate 412609 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv307]) (by decide +kernel)
def pv412609 : PrimeValue := ⟨412609, pr412609⟩
private theorem pr412619 : PrimeCertificate 412619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv2003]) (by decide +kernel)
def pv412619 : PrimeValue := ⟨412619, pr412619⟩
private theorem pr412639 : PrimeCertificate 412639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv97,pv709]) (by decide +kernel)
def pv412639 : PrimeValue := ⟨412639, pr412639⟩
private theorem pr412717 : PrimeCertificate 412717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv163,pv211]) (by decide +kernel)
def pv412717 : PrimeValue := ⟨412717, pr412717⟩
private theorem pr412739 : PrimeCertificate 412739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv206369]) (by decide +kernel)
def pv412739 : PrimeValue := ⟨412739, pr412739⟩
private theorem pr412807 : PrimeCertificate 412807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107,pv643]) (by decide +kernel)
def pv412807 : PrimeValue := ⟨412807, pr412807⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
