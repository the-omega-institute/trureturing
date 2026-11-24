/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table184
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table184.pv405709
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table066

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr405709 : Nat.Prime 405709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv33809]) (by decide +kernel)
def pv405709 : PrimeValue := ⟨405709, pr405709⟩
private theorem pr405989 : Nat.Prime 405989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv9227]) (by decide +kernel)
def pv405989 : PrimeValue := ⟨405989, pr405989⟩
private theorem pr406013 : Nat.Prime 406013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101503]) (by decide +kernel)
def pv406013 : PrimeValue := ⟨406013, pr406013⟩
private theorem pr406073 : Nat.Prime 406073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv193,pv263]) (by decide +kernel)
def pv406073 : PrimeValue := ⟨406073, pr406073⟩
private theorem pr406183 : Nat.Prime 406183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv509]) (by decide +kernel)
def pv406183 : PrimeValue := ⟨406183, pr406183⟩
private theorem pr406253 : Nat.Prime 406253 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv1319]) (by decide +kernel)
def pv406253 : PrimeValue := ⟨406253, pr406253⟩
private theorem pr406267 : Nat.Prime 406267 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv569]) (by decide +kernel)
def pv406267 : PrimeValue := ⟨406267, pr406267⟩
private theorem pr406271 : Nat.Prime 406271 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv40627]) (by decide +kernel)
def pv406271 : PrimeValue := ⟨406271, pr406271⟩
private theorem pr406309 : Nat.Prime 406309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv691]) (by decide +kernel)
def pv406309 : PrimeValue := ⟨406309, pr406309⟩
private theorem pr406423 : Nat.Prime 406423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv67,pv337]) (by decide +kernel)
def pv406423 : PrimeValue := ⟨406423, pr406423⟩
private theorem pr406531 : Nat.Prime 406531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4517]) (by decide +kernel)
def pv406531 : PrimeValue := ⟨406531, pr406531⟩
private theorem pr406573 : Nat.Prime 406573 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv1993]) (by decide +kernel)
def pv406573 : PrimeValue := ⟨406573, pr406573⟩
private theorem pr406699 : Nat.Prime 406699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67783]) (by decide +kernel)
def pv406699 : PrimeValue := ⟨406699, pr406699⟩
private theorem pr406717 : Nat.Prime 406717 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv33893]) (by decide +kernel)
def pv406717 : PrimeValue := ⟨406717, pr406717⟩
private theorem pr406729 : Nat.Prime 406729 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv269]) (by decide +kernel)
def pv406729 : PrimeValue := ⟨406729, pr406729⟩
private theorem pr406789 : Nat.Prime 406789 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv109,pv311]) (by decide +kernel)
def pv406789 : PrimeValue := ⟨406789, pr406789⟩
private theorem pr406873 : Nat.Prime 406873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5651]) (by decide +kernel)
def pv406873 : PrimeValue := ⟨406873, pr406873⟩
private theorem pr406951 : Nat.Prime 406951 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv2713]) (by decide +kernel)
def pv406951 : PrimeValue := ⟨406951, pr406951⟩
private theorem pr406993 : Nat.Prime 406993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv61,pv139]) (by decide +kernel)
def pv406993 : PrimeValue := ⟨406993, pr406993⟩
private theorem pr407137 : Nat.Prime 407137 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv4241]) (by decide +kernel)
def pv407137 : PrimeValue := ⟨407137, pr407137⟩
private theorem pr407249 : Nat.Prime 407249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv25453]) (by decide +kernel)
def pv407249 : PrimeValue := ⟨407249, pr407249⟩
private theorem pr407317 : Nat.Prime 407317 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv373]) (by decide +kernel)
def pv407317 : PrimeValue := ⟨407317, pr407317⟩
private theorem pr407359 : Nat.Prime 407359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv53,pv61]) (by decide +kernel)
def pv407359 : PrimeValue := ⟨407359, pr407359⟩
private theorem pr407383 : Nat.Prime 407383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv1579]) (by decide +kernel)
def pv407383 : PrimeValue := ⟨407383, pr407383⟩
private theorem pr407401 : Nat.Prime 407401 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv7,pv97]) (by decide +kernel)
def pv407401 : PrimeValue := ⟨407401, pr407401⟩
private theorem pr407501 : Nat.Prime 407501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv163]) (by decide +kernel)
def pv407501 : PrimeValue := ⟨407501, pr407501⟩
private theorem pr407503 : Nat.Prime 407503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv22639]) (by decide +kernel)
def pv407503 : PrimeValue := ⟨407503, pr407503⟩
private theorem pr407509 : Nat.Prime 407509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv1171]) (by decide +kernel)
def pv407509 : PrimeValue := ⟨407509, pr407509⟩
private theorem pr407527 : Nat.Prime 407527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv31,pv313]) (by decide +kernel)
def pv407527 : PrimeValue := ⟨407527, pr407527⟩
private theorem pr407741 : Nat.Prime 407741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv29,pv37]) (by decide +kernel)
def pv407741 : PrimeValue := ⟨407741, pr407741⟩
private theorem pr407783 : Nat.Prime 407783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv3847]) (by decide +kernel)
def pv407783 : PrimeValue := ⟨407783, pr407783⟩
private theorem pr407821 : Nat.Prime 407821 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv971]) (by decide +kernel)
def pv407821 : PrimeValue := ⟨407821, pr407821⟩
private theorem pr407977 : Nat.Prime 407977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv89,pv191]) (by decide +kernel)
def pv407977 : PrimeValue := ⟨407977, pr407977⟩
private theorem pr408019 : Nat.Prime 408019 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv13,pv5231]) (by decide +kernel)
def pv408019 : PrimeValue := ⟨408019, pr408019⟩
private theorem pr408091 : Nat.Prime 408091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv61,pv223]) (by decide +kernel)
def pv408091 : PrimeValue := ⟨408091, pr408091⟩
private theorem pr408263 : Nat.Prime 408263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv7039]) (by decide +kernel)
def pv408263 : PrimeValue := ⟨408263, pr408263⟩
private theorem pr408271 : Nat.Prime 408271 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv31,pv439]) (by decide +kernel)
def pv408271 : PrimeValue := ⟨408271, pr408271⟩
private theorem pr408311 : Nat.Prime 408311 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv19,pv307]) (by decide +kernel)
def pv408311 : PrimeValue := ⟨408311, pr408311⟩
private theorem pr408337 : Nat.Prime 408337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv181]) (by decide +kernel)
def pv408337 : PrimeValue := ⟨408337, pr408337⟩
private theorem pr408413 : Nat.Prime 408413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv102103]) (by decide +kernel)
def pv408413 : PrimeValue := ⟨408413, pr408413⟩
private theorem pr408479 : Nat.Prime 408479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv163,pv179]) (by decide +kernel)
def pv408479 : PrimeValue := ⟨408479, pr408479⟩
private theorem pr408553 : Nat.Prime 408553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv587]) (by decide +kernel)
def pv408553 : PrimeValue := ⟨408553, pr408553⟩
private theorem pr408643 : Nat.Prime 408643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv408643 : PrimeValue := ⟨408643, pr408643⟩
private theorem pr408703 : Nat.Prime 408703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv37,pv263]) (by decide +kernel)
def pv408703 : PrimeValue := ⟨408703, pr408703⟩
private theorem pr408763 : Nat.Prime 408763 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv22709]) (by decide +kernel)
def pv408763 : PrimeValue := ⟨408763, pr408763⟩
private theorem pr409099 : Nat.Prime 409099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv1663]) (by decide +kernel)
def pv409099 : PrimeValue := ⟨409099, pr409099⟩
private theorem pr409153 : Nat.Prime 409153 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2131]) (by decide +kernel)
def pv409153 : PrimeValue := ⟨409153, pr409153⟩
private theorem pr409177 : Nat.Prime 409177 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5683]) (by decide +kernel)
def pv409177 : PrimeValue := ⟨409177, pr409177⟩
private theorem pr409391 : Nat.Prime 409391 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv40939]) (by decide +kernel)
def pv409391 : PrimeValue := ⟨409391, pr409391⟩
private theorem pr409433 : Nat.Prime 409433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61,pv839]) (by decide +kernel)
def pv409433 : PrimeValue := ⟨409433, pr409433⟩
private theorem pr409693 : Nat.Prime 409693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv34141]) (by decide +kernel)
def pv409693 : PrimeValue := ⟨409693, pr409693⟩
private theorem pr409711 : Nat.Prime 409711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv1951]) (by decide +kernel)
def pv409711 : PrimeValue := ⟨409711, pr409711⟩
private theorem pr409723 : Nat.Prime 409723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv2969]) (by decide +kernel)
def pv409723 : PrimeValue := ⟨409723, pr409723⟩
private theorem pr409831 : Nat.Prime 409831 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv719]) (by decide +kernel)
def pv409831 : PrimeValue := ⟨409831, pr409831⟩
private theorem pr409879 : Nat.Prime 409879 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7,pv3253]) (by decide +kernel)
def pv409879 : PrimeValue := ⟨409879, pr409879⟩
private theorem pr409891 : Nat.Prime 409891 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv1051]) (by decide +kernel)
def pv409891 : PrimeValue := ⟨409891, pr409891⟩
private theorem pr409999 : Nat.Prime 409999 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv2971]) (by decide +kernel)
def pv409999 : PrimeValue := ⟨409999, pr409999⟩
private theorem pr410063 : Nat.Prime 410063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv205031]) (by decide +kernel)
def pv410063 : PrimeValue := ⟨410063, pr410063⟩
private theorem pr410119 : Nat.Prime 410119 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv2357]) (by decide +kernel)
def pv410119 : PrimeValue := ⟨410119, pr410119⟩
private theorem pr410149 : Nat.Prime 410149 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11393]) (by decide +kernel)
def pv410149 : PrimeValue := ⟨410149, pr410149⟩
private theorem pr410243 : Nat.Prime 410243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29303]) (by decide +kernel)
def pv410243 : PrimeValue := ⟨410243, pr410243⟩
private theorem pr410299 : Nat.Prime 410299 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv9769]) (by decide +kernel)
def pv410299 : PrimeValue := ⟨410299, pr410299⟩
private theorem pr410383 : Nat.Prime 410383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv3257]) (by decide +kernel)
def pv410383 : PrimeValue := ⟨410383, pr410383⟩
private theorem pr410401 : Nat.Prime 410401 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv410401 : PrimeValue := ⟨410401, pr410401⟩
private theorem pr410461 : Nat.Prime 410461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv6841]) (by decide +kernel)
def pv410461 : PrimeValue := ⟨410461, pr410461⟩
private theorem pr410621 : Nat.Prime 410621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv419]) (by decide +kernel)
def pv410621 : PrimeValue := ⟨410621, pr410621⟩
private theorem pr410731 : Nat.Prime 410731 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv13691]) (by decide +kernel)
def pv410731 : PrimeValue := ⟨410731, pr410731⟩
private theorem pr410789 : Nat.Prime 410789 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv17,pv863]) (by decide +kernel)
def pv410789 : PrimeValue := ⟨410789, pr410789⟩
private theorem pr410833 : Nat.Prime 410833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv317]) (by decide +kernel)
def pv410833 : PrimeValue := ⟨410833, pr410833⟩
private theorem pr410903 : Nat.Prime 410903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv5011]) (by decide +kernel)
def pv410903 : PrimeValue := ⟨410903, pr410903⟩
private theorem pr410953 : Nat.Prime 410953 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv17123]) (by decide +kernel)
def pv410953 : PrimeValue := ⟨410953, pr410953⟩
private theorem pr411013 : Nat.Prime 411013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv233]) (by decide +kernel)
def pv411013 : PrimeValue := ⟨411013, pr411013⟩
private theorem pr411041 : Nat.Prime 411041 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv367]) (by decide +kernel)
def pv411041 : PrimeValue := ⟨411041, pr411041⟩
private theorem pr411127 : Nat.Prime 411127 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv68521]) (by decide +kernel)
def pv411127 : PrimeValue := ⟨411127, pr411127⟩
private theorem pr411193 : Nat.Prime 411193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5711]) (by decide +kernel)
def pv411193 : PrimeValue := ⟨411193, pr411193⟩
private theorem pr411211 : Nat.Prime 411211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1523]) (by decide +kernel)
def pv411211 : PrimeValue := ⟨411211, pr411211⟩
private theorem pr411361 : Nat.Prime 411361 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv857]) (by decide +kernel)
def pv411361 : PrimeValue := ⟨411361, pr411361⟩
private theorem pr411379 : Nat.Prime 411379 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv23,pv271]) (by decide +kernel)
def pv411379 : PrimeValue := ⟨411379, pr411379⟩
private theorem pr411409 : Nat.Prime 411409 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2857]) (by decide +kernel)
def pv411409 : PrimeValue := ⟨411409, pr411409⟩
private theorem pr411473 : Nat.Prime 411473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv25717]) (by decide +kernel)
def pv411473 : PrimeValue := ⟨411473, pr411473⟩
private theorem pr411703 : Nat.Prime 411703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59,pv1163]) (by decide +kernel)
def pv411703 : PrimeValue := ⟨411703, pr411703⟩
private theorem pr411727 : Nat.Prime 411727 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv9803]) (by decide +kernel)
def pv411727 : PrimeValue := ⟨411727, pr411727⟩
private theorem pr411751 : Nat.Prime 411751 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv411751 : PrimeValue := ⟨411751, pr411751⟩
private theorem pr411799 : Nat.Prime 411799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv68633]) (by decide +kernel)
def pv411799 : PrimeValue := ⟨411799, pr411799⟩
private theorem pr411923 : Nat.Prime 411923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29423]) (by decide +kernel)
def pv411923 : PrimeValue := ⟨411923, pr411923⟩
private theorem pr412033 : Nat.Prime 412033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv37]) (by decide +kernel)
def pv412033 : PrimeValue := ⟨412033, pr412033⟩
private theorem pr412123 : Nat.Prime 412123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv68687]) (by decide +kernel)
def pv412123 : PrimeValue := ⟨412123, pr412123⟩
private theorem pr412133 : Nat.Prime 412133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv41,pv359]) (by decide +kernel)
def pv412133 : PrimeValue := ⟨412133, pr412133⟩
private theorem pr412189 : Nat.Prime 412189 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv701]) (by decide +kernel)
def pv412189 : PrimeValue := ⟨412189, pr412189⟩
private theorem pr412201 : Nat.Prime 412201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv229]) (by decide +kernel)
def pv412201 : PrimeValue := ⟨412201, pr412201⟩
private theorem pr412249 : Nat.Prime 412249 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv89,pv193]) (by decide +kernel)
def pv412249 : PrimeValue := ⟨412249, pr412249⟩
private theorem pr412273 : Nat.Prime 412273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv409]) (by decide +kernel)
def pv412273 : PrimeValue := ⟨412273, pr412273⟩
private theorem pr412343 : Nat.Prime 412343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv29453]) (by decide +kernel)
def pv412343 : PrimeValue := ⟨412343, pr412343⟩
private theorem pr412387 : Nat.Prime 412387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv17,pv311]) (by decide +kernel)
def pv412387 : PrimeValue := ⟨412387, pr412387⟩
private theorem pr412651 : Nat.Prime 412651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv131]) (by decide +kernel)
def pv412651 : PrimeValue := ⟨412651, pr412651⟩
private theorem pr412891 : Nat.Prime 412891 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13763]) (by decide +kernel)
def pv412891 : PrimeValue := ⟨412891, pr412891⟩
private theorem pr412903 : Nat.Prime 412903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv29,pv113]) (by decide +kernel)
def pv412903 : PrimeValue := ⟨412903, pr412903⟩
private theorem pr412987 : Nat.Prime 412987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv9833]) (by decide +kernel)
def pv412987 : PrimeValue := ⟨412987, pr412987⟩
private theorem pr413069 : Nat.Prime 413069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv2791]) (by decide +kernel)
def pv413069 : PrimeValue := ⟨413069, pr413069⟩
private theorem pr413111 : Nat.Prime 413111 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv109,pv379]) (by decide +kernel)
def pv413111 : PrimeValue := ⟨413111, pr413111⟩
private theorem pr413443 : Nat.Prime 413443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103,pv223]) (by decide +kernel)
def pv413443 : PrimeValue := ⟨413443, pr413443⟩
private theorem pr413521 : Nat.Prime 413521 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1723]) (by decide +kernel)
def pv413521 : PrimeValue := ⟨413521, pr413521⟩
private theorem pr413681 : Nat.Prime 413681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv5171]) (by decide +kernel)
def pv413681 : PrimeValue := ⟨413681, pr413681⟩
private theorem pr413779 : Nat.Prime 413779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv68963]) (by decide +kernel)
def pv413779 : PrimeValue := ⟨413779, pr413779⟩
private theorem pr413783 : Nat.Prime 413783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv10889]) (by decide +kernel)
def pv413783 : PrimeValue := ⟨413783, pr413783⟩
private theorem pr413869 : Nat.Prime 413869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv379]) (by decide +kernel)
def pv413869 : PrimeValue := ⟨413869, pr413869⟩
private theorem pr413911 : Nat.Prime 413911 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv73]) (by decide +kernel)
def pv413911 : PrimeValue := ⟨413911, pr413911⟩
private theorem pr414013 : Nat.Prime 414013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv34501]) (by decide +kernel)
def pv414013 : PrimeValue := ⟨414013, pr414013⟩
private theorem pr414031 : Nat.Prime 414031 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv37,pv373]) (by decide +kernel)
def pv414031 : PrimeValue := ⟨414031, pr414031⟩
private theorem pr414049 : Nat.Prime 414049 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv227]) (by decide +kernel)
def pv414049 : PrimeValue := ⟨414049, pr414049⟩
private theorem pr414061 : Nat.Prime 414061 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv67,pv103]) (by decide +kernel)
def pv414061 : PrimeValue := ⟨414061, pr414061⟩
private theorem pr414109 : Nat.Prime 414109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11503]) (by decide +kernel)
def pv414109 : PrimeValue := ⟨414109, pr414109⟩
private theorem pr414269 : Nat.Prime 414269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103567]) (by decide +kernel)
def pv414269 : PrimeValue := ⟨414269, pr414269⟩
private theorem pr414283 : Nat.Prime 414283 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv6277]) (by decide +kernel)
def pv414283 : PrimeValue := ⟨414283, pr414283⟩
private theorem pr414433 : Nat.Prime 414433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1439]) (by decide +kernel)
def pv414433 : PrimeValue := ⟨414433, pr414433⟩
private theorem pr414571 : Nat.Prime 414571 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv1063]) (by decide +kernel)
def pv414571 : PrimeValue := ⟨414571, pr414571⟩
private theorem pr414653 : Nat.Prime 414653 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv59,pv251]) (by decide +kernel)
def pv414653 : PrimeValue := ⟨414653, pr414653⟩
private theorem pr414679 : Nat.Prime 414679 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv61,pv103]) (by decide +kernel)
def pv414679 : PrimeValue := ⟨414679, pr414679⟩
private theorem pr414763 : Nat.Prime 414763 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv69127]) (by decide +kernel)
def pv414763 : PrimeValue := ⟨414763, pr414763⟩
private theorem pr414793 : Nat.Prime 414793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv823]) (by decide +kernel)
def pv414793 : PrimeValue := ⟨414793, pr414793⟩
private theorem pr414871 : Nat.Prime 414871 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13829]) (by decide +kernel)
def pv414871 : PrimeValue := ⟨414871, pr414871⟩
private theorem pr414889 : Nat.Prime 414889 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv59,pv293]) (by decide +kernel)
def pv414889 : PrimeValue := ⟨414889, pr414889⟩
private theorem pr415069 : Nat.Prime 415069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv34589]) (by decide +kernel)
def pv415069 : PrimeValue := ⟨415069, pr415069⟩
private theorem pr415147 : Nat.Prime 415147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv69191]) (by decide +kernel)
def pv415147 : PrimeValue := ⟨415147, pr415147⟩
private theorem pr415153 : Nat.Prime 415153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv415153 : PrimeValue := ⟨415153, pr415153⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
