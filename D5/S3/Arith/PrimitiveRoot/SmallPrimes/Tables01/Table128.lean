/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table128
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table128.pv752483
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table096
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table097

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr752483 : Nat.Prime 752483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv376241]) (by decide +kernel)
def pv752483 : PrimeValue := ⟨752483, pr752483⟩
private theorem pr752503 : Nat.Prime 752503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv167,pv751]) (by decide +kernel)
def pv752503 : PrimeValue := ⟨752503, pr752503⟩
private theorem pr752639 : Nat.Prime 752639 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv107,pv3517]) (by decide +kernel)
def pv752639 : PrimeValue := ⟨752639, pr752639⟩
private theorem pr752797 : Nat.Prime 752797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1901]) (by decide +kernel)
def pv752797 : PrimeValue := ⟨752797, pr752797⟩
private theorem pr752803 : Nat.Prime 752803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv3391]) (by decide +kernel)
def pv752803 : PrimeValue := ⟨752803, pr752803⟩
private theorem pr752809 : Nat.Prime 752809 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv4481]) (by decide +kernel)
def pv752809 : PrimeValue := ⟨752809, pr752809⟩
private theorem pr752861 : Nat.Prime 752861 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv37643]) (by decide +kernel)
def pv752861 : PrimeValue := ⟨752861, pr752861⟩
private theorem pr752977 : Nat.Prime 752977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv83]) (by decide +kernel)
def pv752977 : PrimeValue := ⟨752977, pr752977⟩
private theorem pr753127 : Nat.Prime 753127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv11411]) (by decide +kernel)
def pv753127 : PrimeValue := ⟨753127, pr753127⟩
private theorem pr753133 : Nat.Prime 753133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv62761]) (by decide +kernel)
def pv753133 : PrimeValue := ⟨753133, pr753133⟩
private theorem pr753143 : Nat.Prime 753143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv83,pv349]) (by decide +kernel)
def pv753143 : PrimeValue := ⟨753143, pr753143⟩
private theorem pr753463 : Nat.Prime 753463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4651]) (by decide +kernel)
def pv753463 : PrimeValue := ⟨753463, pr753463⟩
private theorem pr753547 : Nat.Prime 753547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv125591]) (by decide +kernel)
def pv753547 : PrimeValue := ⟨753547, pr753547⟩
private theorem pr753569 : Nat.Prime 753569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23549]) (by decide +kernel)
def pv753569 : PrimeValue := ⟨753569, pr753569⟩
private theorem pr753689 : Nat.Prime 753689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv7247]) (by decide +kernel)
def pv753689 : PrimeValue := ⟨753689, pr753689⟩
private theorem pr753719 : Nat.Prime 753719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv7691]) (by decide +kernel)
def pv753719 : PrimeValue := ⟨753719, pr753719⟩
private theorem pr753743 : Nat.Prime 753743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv34261]) (by decide +kernel)
def pv753743 : PrimeValue := ⟨753743, pr753743⟩
private theorem pr753799 : Nat.Prime 753799 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv73,pv1721]) (by decide +kernel)
def pv753799 : PrimeValue := ⟨753799, pr753799⟩
private theorem pr753803 : Nat.Prime 753803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv2341]) (by decide +kernel)
def pv753803 : PrimeValue := ⟨753803, pr753803⟩
private theorem pr753859 : Nat.Prime 753859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv193]) (by decide +kernel)
def pv753859 : PrimeValue := ⟨753859, pr753859⟩
private theorem pr754057 : Nat.Prime 754057 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3491]) (by decide +kernel)
def pv754057 : PrimeValue := ⟨754057, pr754057⟩
private theorem pr754073 : Nat.Prime 754073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv19,pv41]) (by decide +kernel)
def pv754073 : PrimeValue := ⟨754073, pr754073⟩
private theorem pr754109 : Nat.Prime 754109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv188527]) (by decide +kernel)
def pv754109 : PrimeValue := ⟨754109, pr754109⟩
private theorem pr754153 : Nat.Prime 754153 :=
  checkPrime_prime (q := pv61) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv754153 : PrimeValue := ⟨754153, pr754153⟩
private theorem pr754249 : Nat.Prime 754249 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv2857]) (by decide +kernel)
def pv754249 : PrimeValue := ⟨754249, pr754249⟩
private theorem pr754289 : Nat.Prime 754289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47143]) (by decide +kernel)
def pv754289 : PrimeValue := ⟨754289, pr754289⟩
private theorem pr754343 : Nat.Prime 754343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv377171]) (by decide +kernel)
def pv754343 : PrimeValue := ⟨754343, pr754343⟩
private theorem pr754489 : Nat.Prime 754489 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv499]) (by decide +kernel)
def pv754489 : PrimeValue := ⟨754489, pr754489⟩
private theorem pr754703 : Nat.Prime 754703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv29027]) (by decide +kernel)
def pv754703 : PrimeValue := ⟨754703, pr754703⟩
private theorem pr754811 : Nat.Prime 754811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv41,pv263]) (by decide +kernel)
def pv754811 : PrimeValue := ⟨754811, pr754811⟩
private theorem pr754829 : Nat.Prime 754829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv188707]) (by decide +kernel)
def pv754829 : PrimeValue := ⟨754829, pr754829⟩
private theorem pr754931 : Nat.Prime 754931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv6863]) (by decide +kernel)
def pv754931 : PrimeValue := ⟨754931, pr754931⟩
private theorem pr754973 : Nat.Prime 754973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv173,pv1091]) (by decide +kernel)
def pv754973 : PrimeValue := ⟨754973, pr754973⟩
private theorem pr755077 : Nat.Prime 755077 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv89,pv101]) (by decide +kernel)
def pv755077 : PrimeValue := ⟨755077, pr755077⟩
private theorem pr755081 : Nat.Prime 755081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43,pv439]) (by decide +kernel)
def pv755081 : PrimeValue := ⟨755081, pr755081⟩
private theorem pr755171 : Nat.Prime 755171 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv37,pv157]) (by decide +kernel)
def pv755171 : PrimeValue := ⟨755171, pr755171⟩
private theorem pr755213 : Nat.Prime 755213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv523]) (by decide +kernel)
def pv755213 : PrimeValue := ⟨755213, pr755213⟩
private theorem pr755239 : Nat.Prime 755239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv11443]) (by decide +kernel)
def pv755239 : PrimeValue := ⟨755239, pr755239⟩
private theorem pr755351 : Nat.Prime 755351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv15107]) (by decide +kernel)
def pv755351 : PrimeValue := ⟨755351, pr755351⟩
private theorem pr755399 : Nat.Prime 755399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv79,pv683]) (by decide +kernel)
def pv755399 : PrimeValue := ⟨755399, pr755399⟩
private theorem pr755449 : Nat.Prime 755449 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv31477]) (by decide +kernel)
def pv755449 : PrimeValue := ⟨755449, pr755449⟩
private theorem pr755483 : Nat.Prime 755483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv593]) (by decide +kernel)
def pv755483 : PrimeValue := ⟨755483, pr755483⟩
private theorem pr755593 : Nat.Prime 755593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv1657]) (by decide +kernel)
def pv755593 : PrimeValue := ⟨755593, pr755593⟩
private theorem pr755663 : Nat.Prime 755663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv377831]) (by decide +kernel)
def pv755663 : PrimeValue := ⟨755663, pr755663⟩
private theorem pr755737 : Nat.Prime 755737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31489]) (by decide +kernel)
def pv755737 : PrimeValue := ⟨755737, pr755737⟩
private theorem pr755861 : Nat.Prime 755861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv5399]) (by decide +kernel)
def pv755861 : PrimeValue := ⟨755861, pr755861⟩
private theorem pr755869 : Nat.Prime 755869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv62989]) (by decide +kernel)
def pv755869 : PrimeValue := ⟨755869, pr755869⟩
private theorem pr756011 : Nat.Prime 756011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv23,pv173]) (by decide +kernel)
def pv756011 : PrimeValue := ⟨756011, pr756011⟩
private theorem pr756149 : Nat.Prime 756149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv8219]) (by decide +kernel)
def pv756149 : PrimeValue := ⟨756149, pr756149⟩
private theorem pr756191 : Nat.Prime 756191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv75619]) (by decide +kernel)
def pv756191 : PrimeValue := ⟨756191, pr756191⟩
private theorem pr756199 : Nat.Prime 756199 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv977]) (by decide +kernel)
def pv756199 : PrimeValue := ⟨756199, pr756199⟩
private theorem pr756319 : Nat.Prime 756319 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv233,pv541]) (by decide +kernel)
def pv756319 : PrimeValue := ⟨756319, pr756319⟩
private theorem pr756533 : Nat.Prime 756533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv41,pv659]) (by decide +kernel)
def pv756533 : PrimeValue := ⟨756533, pr756533⟩
private theorem pr756667 : Nat.Prime 756667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv127,pv331]) (by decide +kernel)
def pv756667 : PrimeValue := ⟨756667, pr756667⟩
private theorem pr756683 : Nat.Prime 756683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv397,pv953]) (by decide +kernel)
def pv756683 : PrimeValue := ⟨756683, pr756683⟩
private theorem pr756739 : Nat.Prime 756739 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv2473]) (by decide +kernel)
def pv756739 : PrimeValue := ⟨756739, pr756739⟩
private theorem pr756869 : Nat.Prime 756869 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv27031]) (by decide +kernel)
def pv756869 : PrimeValue := ⟨756869, pr756869⟩
private theorem pr757019 : Nat.Prime 757019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv378509]) (by decide +kernel)
def pv757019 : PrimeValue := ⟨757019, pr757019⟩
private theorem pr757181 : Nat.Prime 757181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv131]) (by decide +kernel)
def pv757181 : PrimeValue := ⟨757181, pr757181⟩
private theorem pr757243 : Nat.Prime 757243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv379]) (by decide +kernel)
def pv757243 : PrimeValue := ⟨757243, pr757243⟩
private theorem pr757327 : Nat.Prime 757327 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv113,pv1117]) (by decide +kernel)
def pv757327 : PrimeValue := ⟨757327, pr757327⟩
private theorem pr757433 : Nat.Prime 757433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv7283]) (by decide +kernel)
def pv757433 : PrimeValue := ⟨757433, pr757433⟩
private theorem pr757481 : Nat.Prime 757481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv653]) (by decide +kernel)
def pv757481 : PrimeValue := ⟨757481, pr757481⟩
private theorem pr757579 : Nat.Prime 757579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv4073]) (by decide +kernel)
def pv757579 : PrimeValue := ⟨757579, pr757579⟩
private theorem pr757709 : Nat.Prime 757709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv27061]) (by decide +kernel)
def pv757709 : PrimeValue := ⟨757709, pr757709⟩
private theorem pr757811 : Nat.Prime 757811 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv75781]) (by decide +kernel)
def pv757811 : PrimeValue := ⟨757811, pr757811⟩
private theorem pr758003 : Nat.Prime 758003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv1867]) (by decide +kernel)
def pv758003 : PrimeValue := ⟨758003, pr758003⟩
private theorem pr758053 : Nat.Prime 758053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7019]) (by decide +kernel)
def pv758053 : PrimeValue := ⟨758053, pr758053⟩
private theorem pr758083 : Nat.Prime 758083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv9719]) (by decide +kernel)
def pv758083 : PrimeValue := ⟨758083, pr758083⟩
private theorem pr758099 : Nat.Prime 758099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv2027]) (by decide +kernel)
def pv758099 : PrimeValue := ⟨758099, pr758099⟩
private theorem pr758179 : Nat.Prime 758179 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv73,pv577]) (by decide +kernel)
def pv758179 : PrimeValue := ⟨758179, pr758179⟩
private theorem pr758273 : Nat.Prime 758273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1481]) (by decide +kernel)
def pv758273 : PrimeValue := ⟨758273, pr758273⟩
private theorem pr758383 : Nat.Prime 758383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv126397]) (by decide +kernel)
def pv758383 : PrimeValue := ⟨758383, pr758383⟩
private theorem pr758441 : Nat.Prime 758441 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv67,pv283]) (by decide +kernel)
def pv758441 : PrimeValue := ⟨758441, pr758441⟩
private theorem pr758503 : Nat.Prime 758503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv42139]) (by decide +kernel)
def pv758503 : PrimeValue := ⟨758503, pr758503⟩
private theorem pr758519 : Nat.Prime 758519 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv19,pv19961]) (by decide +kernel)
def pv758519 : PrimeValue := ⟨758519, pr758519⟩
private theorem pr758711 : Nat.Prime 758711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv4463]) (by decide +kernel)
def pv758711 : PrimeValue := ⟨758711, pr758711⟩
private theorem pr758713 : Nat.Prime 758713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv101,pv313]) (by decide +kernel)
def pv758713 : PrimeValue := ⟨758713, pr758713⟩
private theorem pr758743 : Nat.Prime 758743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv126457]) (by decide +kernel)
def pv758743 : PrimeValue := ⟨758743, pr758743⟩
private theorem pr758753 : Nat.Prime 758753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv131,pv181]) (by decide +kernel)
def pv758753 : PrimeValue := ⟨758753, pr758753⟩
private theorem pr758783 : Nat.Prime 758783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv379391]) (by decide +kernel)
def pv758783 : PrimeValue := ⟨758783, pr758783⟩
private theorem pr758819 : Nat.Prime 758819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv12239]) (by decide +kernel)
def pv758819 : PrimeValue := ⟨758819, pr758819⟩
private theorem pr758929 : Nat.Prime 758929 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv97,pv163]) (by decide +kernel)
def pv758929 : PrimeValue := ⟨758929, pr758929⟩
private theorem pr758963 : Nat.Prime 758963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv6221]) (by decide +kernel)
def pv758963 : PrimeValue := ⟨758963, pr758963⟩
private theorem pr758969 : Nat.Prime 758969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13553]) (by decide +kernel)
def pv758969 : PrimeValue := ⟨758969, pr758969⟩
private theorem pr759131 : Nat.Prime 759131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv75913]) (by decide +kernel)
def pv759131 : PrimeValue := ⟨759131, pr759131⟩
private theorem pr759179 : Nat.Prime 759179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv211,pv257]) (by decide +kernel)
def pv759179 : PrimeValue := ⟨759179, pr759179⟩
private theorem pr759371 : Nat.Prime 759371 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv75937]) (by decide +kernel)
def pv759371 : PrimeValue := ⟨759371, pr759371⟩
private theorem pr759431 : Nat.Prime 759431 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv19,pv571]) (by decide +kernel)
def pv759431 : PrimeValue := ⟨759431, pr759431⟩
private theorem pr759457 : Nat.Prime 759457 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv293]) (by decide +kernel)
def pv759457 : PrimeValue := ⟨759457, pr759457⟩
private theorem pr759553 : Nat.Prime 759553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv43]) (by decide +kernel)
def pv759553 : PrimeValue := ⟨759553, pr759553⟩
private theorem pr759581 : Nat.Prime 759581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv163,pv233]) (by decide +kernel)
def pv759581 : PrimeValue := ⟨759581, pr759581⟩
private theorem pr759641 : Nat.Prime 759641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv2713]) (by decide +kernel)
def pv759641 : PrimeValue := ⟨759641, pr759641⟩
private theorem pr759719 : Nat.Prime 759719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv379859]) (by decide +kernel)
def pv759719 : PrimeValue := ⟨759719, pr759719⟩
private theorem pr759833 : Nat.Prime 759833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv37,pv151]) (by decide +kernel)
def pv759833 : PrimeValue := ⟨759833, pr759833⟩
private theorem pr759953 : Nat.Prime 759953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47497]) (by decide +kernel)
def pv759953 : PrimeValue := ⟨759953, pr759953⟩
private theorem pr760079 : Nat.Prime 760079 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv34549]) (by decide +kernel)
def pv760079 : PrimeValue := ⟨760079, pr760079⟩
private theorem pr760117 : Nat.Prime 760117 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv9049]) (by decide +kernel)
def pv760117 : PrimeValue := ⟨760117, pr760117⟩
private theorem pr760129 : Nat.Prime 760129 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv37,pv107]) (by decide +kernel)
def pv760129 : PrimeValue := ⟨760129, pr760129⟩
private theorem pr760153 : Nat.Prime 760153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv1667]) (by decide +kernel)
def pv760153 : PrimeValue := ⟨760153, pr760153⟩
private theorem pr760169 : Nat.Prime 760169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv95021]) (by decide +kernel)
def pv760169 : PrimeValue := ⟨760169, pr760169⟩
private theorem pr760183 : Nat.Prime 760183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv61,pv67]) (by decide +kernel)
def pv760183 : PrimeValue := ⟨760183, pr760183⟩
private theorem pr760211 : Nat.Prime 760211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv6911]) (by decide +kernel)
def pv760211 : PrimeValue := ⟨760211, pr760211⟩
private theorem pr760237 : Nat.Prime 760237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv63353]) (by decide +kernel)
def pv760237 : PrimeValue := ⟨760237, pr760237⟩
private theorem pr760241 : Nat.Prime 760241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv17,pv43]) (by decide +kernel)
def pv760241 : PrimeValue := ⟨760241, pr760241⟩
private theorem pr760289 : Nat.Prime 760289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv1033]) (by decide +kernel)
def pv760289 : PrimeValue := ⟨760289, pr760289⟩
private theorem pr760297 : Nat.Prime 760297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv79,pv401]) (by decide +kernel)
def pv760297 : PrimeValue := ⟨760297, pr760297⟩
private theorem pr760373 : Nat.Prime 760373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv190093]) (by decide +kernel)
def pv760373 : PrimeValue := ⟨760373, pr760373⟩
private theorem pr760447 : Nat.Prime 760447 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv83,pv509]) (by decide +kernel)
def pv760447 : PrimeValue := ⟨760447, pr760447⟩
private theorem pr760579 : Nat.Prime 760579 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv199]) (by decide +kernel)
def pv760579 : PrimeValue := ⟨760579, pr760579⟩
private theorem pr760657 : Nat.Prime 760657 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv23,pv53]) (by decide +kernel)
def pv760657 : PrimeValue := ⟨760657, pr760657⟩
private theorem pr760759 : Nat.Prime 760759 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv103,pv1231]) (by decide +kernel)
def pv760759 : PrimeValue := ⟨760759, pr760759⟩
private theorem pr760783 : Nat.Prime 760783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv11527]) (by decide +kernel)
def pv760783 : PrimeValue := ⟨760783, pr760783⟩
private theorem pr760901 : Nat.Prime 760901 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv1087]) (by decide +kernel)
def pv760901 : PrimeValue := ⟨760901, pr760901⟩
private theorem pr760993 : Nat.Prime 760993 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7927]) (by decide +kernel)
def pv760993 : PrimeValue := ⟨760993, pr760993⟩
private theorem pr761009 : Nat.Prime 761009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47563]) (by decide +kernel)
def pv761009 : PrimeValue := ⟨761009, pr761009⟩
private theorem pr761213 : Nat.Prime 761213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv4049]) (by decide +kernel)
def pv761213 : PrimeValue := ⟨761213, pr761213⟩
private theorem pr761363 : Nat.Prime 761363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv457]) (by decide +kernel)
def pv761363 : PrimeValue := ⟨761363, pr761363⟩
private theorem pr761399 : Nat.Prime 761399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv53,pv653]) (by decide +kernel)
def pv761399 : PrimeValue := ⟨761399, pr761399⟩
private theorem pr761443 : Nat.Prime 761443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv83,pv139]) (by decide +kernel)
def pv761443 : PrimeValue := ⟨761443, pr761443⟩
private theorem pr761531 : Nat.Prime 761531 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv11,pv23,pv43]) (by decide +kernel)
def pv761531 : PrimeValue := ⟨761531, pr761531⟩
private theorem pr761533 : Nat.Prime 761533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv3733]) (by decide +kernel)
def pv761533 : PrimeValue := ⟨761533, pr761533⟩
private theorem pr761543 : Nat.Prime 761543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv503,pv757]) (by decide +kernel)
def pv761543 : PrimeValue := ⟨761543, pr761543⟩
private theorem pr761669 : Nat.Prime 761669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv23,pv487]) (by decide +kernel)
def pv761669 : PrimeValue := ⟨761669, pr761669⟩
private theorem pr761809 : Nat.Prime 761809 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv59,pv269]) (by decide +kernel)
def pv761809 : PrimeValue := ⟨761809, pr761809⟩
private theorem pr761833 : Nat.Prime 761833 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv3527]) (by decide +kernel)
def pv761833 : PrimeValue := ⟨761833, pr761833⟩
private theorem pr761977 : Nat.Prime 761977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv557]) (by decide +kernel)
def pv761977 : PrimeValue := ⟨761977, pr761977⟩
private theorem pr761993 : Nat.Prime 761993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv1237]) (by decide +kernel)
def pv761993 : PrimeValue := ⟨761993, pr761993⟩
private theorem pr762049 : Nat.Prime 762049 :=
  checkPrime_prime (q := pv61) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv762049 : PrimeValue := ⟨762049, pr762049⟩
private theorem pr762367 : Nat.Prime 762367 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv11551]) (by decide +kernel)
def pv762367 : PrimeValue := ⟨762367, pr762367⟩
private theorem pr762397 : Nat.Prime 762397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv63533]) (by decide +kernel)
def pv762397 : PrimeValue := ⟨762397, pr762397⟩
private theorem pr762893 : Nat.Prime 762893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17,pv863]) (by decide +kernel)
def pv762893 : PrimeValue := ⟨762893, pr762893⟩
private theorem pr762919 : Nat.Prime 762919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv9781]) (by decide +kernel)
def pv762919 : PrimeValue := ⟨762919, pr762919⟩
private theorem pr762967 : Nat.Prime 762967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv71,pv199]) (by decide +kernel)
def pv762967 : PrimeValue := ⟨762967, pr762967⟩
private theorem pr763039 : Nat.Prime 763039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv42391]) (by decide +kernel)
def pv763039 : PrimeValue := ⟨763039, pr763039⟩
private theorem pr763043 : Nat.Prime 763043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv54503]) (by decide +kernel)
def pv763043 : PrimeValue := ⟨763043, pr763043⟩
private theorem pr763093 : Nat.Prime 763093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv41,pv47]) (by decide +kernel)
def pv763093 : PrimeValue := ⟨763093, pr763093⟩
private theorem pr763183 : Nat.Prime 763183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv673]) (by decide +kernel)
def pv763183 : PrimeValue := ⟨763183, pr763183⟩
private theorem pr763237 : Nat.Prime 763237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv191]) (by decide +kernel)
def pv763237 : PrimeValue := ⟨763237, pr763237⟩
private theorem pr763403 : Nat.Prime 763403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv22453]) (by decide +kernel)
def pv763403 : PrimeValue := ⟨763403, pr763403⟩
private theorem pr763417 : Nat.Prime 763417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv461]) (by decide +kernel)
def pv763417 : PrimeValue := ⟨763417, pr763417⟩
private theorem pr763447 : Nat.Prime 763447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv127241]) (by decide +kernel)
def pv763447 : PrimeValue := ⟨763447, pr763447⟩
private theorem pr763523 : Nat.Prime 763523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv381761]) (by decide +kernel)
def pv763523 : PrimeValue := ⟨763523, pr763523⟩
private theorem pr763549 : Nat.Prime 763549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv63629]) (by decide +kernel)
def pv763549 : PrimeValue := ⟨763549, pr763549⟩
private theorem pr763601 : Nat.Prime 763601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv83]) (by decide +kernel)
def pv763601 : PrimeValue := ⟨763601, pr763601⟩
private theorem pr763649 : Nat.Prime 763649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv157]) (by decide +kernel)
def pv763649 : PrimeValue := ⟨763649, pr763649⟩
private theorem pr763673 : Nat.Prime 763673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv1049]) (by decide +kernel)
def pv763673 : PrimeValue := ⟨763673, pr763673⟩
private theorem pr763843 : Nat.Prime 763843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv2087]) (by decide +kernel)
def pv763843 : PrimeValue := ⟨763843, pr763843⟩
private theorem pr763897 : Nat.Prime 763897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv4547]) (by decide +kernel)
def pv763897 : PrimeValue := ⟨763897, pr763897⟩
private theorem pr763901 : Nat.Prime 763901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7639]) (by decide +kernel)
def pv763901 : PrimeValue := ⟨763901, pr763901⟩
private theorem pr763943 : Nat.Prime 763943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv7207]) (by decide +kernel)
def pv763943 : PrimeValue := ⟨763943, pr763943⟩
private theorem pr764017 : Nat.Prime 764017 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1447]) (by decide +kernel)
def pv764017 : PrimeValue := ⟨764017, pr764017⟩
private theorem pr764051 : Nat.Prime 764051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv37,pv59]) (by decide +kernel)
def pv764051 : PrimeValue := ⟨764051, pr764051⟩
private theorem pr764053 : Nat.Prime 764053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv63671]) (by decide +kernel)
def pv764053 : PrimeValue := ⟨764053, pr764053⟩
private theorem pr764089 : Nat.Prime 764089 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv31,pv79]) (by decide +kernel)
def pv764089 : PrimeValue := ⟨764089, pr764089⟩
private theorem pr764111 : Nat.Prime 764111 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv43,pv1777]) (by decide +kernel)
def pv764111 : PrimeValue := ⟨764111, pr764111⟩
private theorem pr764149 : Nat.Prime 764149 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv7,pv11,pv827]) (by decide +kernel)
def pv764149 : PrimeValue := ⟨764149, pr764149⟩
private theorem pr764321 : Nat.Prime 764321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv281]) (by decide +kernel)
def pv764321 : PrimeValue := ⟨764321, pr764321⟩
private theorem pr764399 : Nat.Prime 764399 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv31,pv12329]) (by decide +kernel)
def pv764399 : PrimeValue := ⟨764399, pr764399⟩
private theorem pr764539 : Nat.Prime 764539 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv127423]) (by decide +kernel)
def pv764539 : PrimeValue := ⟨764539, pr764539⟩
private theorem pr764623 : Nat.Prime 764623 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv107,pv397]) (by decide +kernel)
def pv764623 : PrimeValue := ⟨764623, pr764623⟩
private theorem pr764719 : Nat.Prime 764719 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv127453]) (by decide +kernel)
def pv764719 : PrimeValue := ⟨764719, pr764719⟩
private theorem pr764887 : Nat.Prime 764887 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv127481]) (by decide +kernel)
def pv764887 : PrimeValue := ⟨764887, pr764887⟩
private theorem pr764899 : Nat.Prime 764899 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv7499]) (by decide +kernel)
def pv764899 : PrimeValue := ⟨764899, pr764899⟩
private theorem pr764903 : Nat.Prime 764903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv20129]) (by decide +kernel)
def pv764903 : PrimeValue := ⟨764903, pr764903⟩
private theorem pr765139 : Nat.Prime 765139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv11593]) (by decide +kernel)
def pv765139 : PrimeValue := ⟨765139, pr765139⟩
private theorem pr765229 : Nat.Prime 765229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv1483]) (by decide +kernel)
def pv765229 : PrimeValue := ⟨765229, pr765229⟩
private theorem pr765283 : Nat.Prime 765283 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv137]) (by decide +kernel)
def pv765283 : PrimeValue := ⟨765283, pr765283⟩
private theorem pr765307 : Nat.Prime 765307 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv41,pv61]) (by decide +kernel)
def pv765307 : PrimeValue := ⟨765307, pr765307⟩
private theorem pr765379 : Nat.Prime 765379 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv101,pv421]) (by decide +kernel)
def pv765379 : PrimeValue := ⟨765379, pr765379⟩
private theorem pr765389 : Nat.Prime 765389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv41,pv359]) (by decide +kernel)
def pv765389 : PrimeValue := ⟨765389, pr765389⟩
private theorem pr765409 : Nat.Prime 765409 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv17,pv67]) (by decide +kernel)
def pv765409 : PrimeValue := ⟨765409, pr765409⟩
private theorem pr765673 : Nat.Prime 765673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv61,pv523]) (by decide +kernel)
def pv765673 : PrimeValue := ⟨765673, pr765673⟩
private theorem pr765749 : Nat.Prime 765749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv11261]) (by decide +kernel)
def pv765749 : PrimeValue := ⟨765749, pr765749⟩
private theorem pr765907 : Nat.Prime 765907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv107,pv1193]) (by decide +kernel)
def pv765907 : PrimeValue := ⟨765907, pr765907⟩
private theorem pr765913 : Nat.Prime 765913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv47,pv97]) (by decide +kernel)
def pv765913 : PrimeValue := ⟨765913, pr765913⟩
private theorem pr766039 : Nat.Prime 766039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv23,pv61]) (by decide +kernel)
def pv766039 : PrimeValue := ⟨766039, pr766039⟩
private theorem pr766091 : Nat.Prime 766091 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv71,pv83]) (by decide +kernel)
def pv766091 : PrimeValue := ⟨766091, pr766091⟩
private theorem pr766163 : Nat.Prime 766163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv383081]) (by decide +kernel)
def pv766163 : PrimeValue := ⟨766163, pr766163⟩
private theorem pr766237 : Nat.Prime 766237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv63853]) (by decide +kernel)
def pv766237 : PrimeValue := ⟨766237, pr766237⟩
private theorem pr766301 : Nat.Prime 766301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv79,pv97]) (by decide +kernel)
def pv766301 : PrimeValue := ⟨766301, pr766301⟩
private theorem pr766313 : Nat.Prime 766313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv95789]) (by decide +kernel)
def pv766313 : PrimeValue := ⟨766313, pr766313⟩
private theorem pr766333 : Nat.Prime 766333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv3041]) (by decide +kernel)
def pv766333 : PrimeValue := ⟨766333, pr766333⟩
private theorem pr766361 : Nat.Prime 766361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv17,pv23]) (by decide +kernel)
def pv766361 : PrimeValue := ⟨766361, pr766361⟩
private theorem pr766369 : Nat.Prime 766369 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv887]) (by decide +kernel)
def pv766369 : PrimeValue := ⟨766369, pr766369⟩
private theorem pr766387 : Nat.Prime 766387 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv42577]) (by decide +kernel)
def pv766387 : PrimeValue := ⟨766387, pr766387⟩
private theorem pr766453 : Nat.Prime 766453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv2777]) (by decide +kernel)
def pv766453 : PrimeValue := ⟨766453, pr766453⟩
private theorem pr766541 : Nat.Prime 766541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv38327]) (by decide +kernel)
def pv766541 : PrimeValue := ⟨766541, pr766541⟩
private theorem pr766553 : Nat.Prime 766553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv95819]) (by decide +kernel)
def pv766553 : PrimeValue := ⟨766553, pr766553⟩
private theorem pr766721 : Nat.Prime 766721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv599]) (by decide +kernel)
def pv766721 : PrimeValue := ⟨766721, pr766721⟩
private theorem pr766763 : Nat.Prime 766763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv3583]) (by decide +kernel)
def pv766763 : PrimeValue := ⟨766763, pr766763⟩
private theorem pr766957 : Nat.Prime 766957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv63913]) (by decide +kernel)
def pv766957 : PrimeValue := ⟨766957, pr766957⟩
private theorem pr767017 : Nat.Prime 767017 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv53,pv67]) (by decide +kernel)
def pv767017 : PrimeValue := ⟨767017, pr767017⟩
private theorem pr767051 : Nat.Prime 767051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv29]) (by decide +kernel)
def pv767051 : PrimeValue := ⟨767051, pr767051⟩
private theorem pr767111 : Nat.Prime 767111 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv41,pv1871]) (by decide +kernel)
def pv767111 : PrimeValue := ⟨767111, pr767111⟩
private theorem pr767293 : Nat.Prime 767293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv1487]) (by decide +kernel)
def pv767293 : PrimeValue := ⟨767293, pr767293⟩
private theorem pr767489 : Nat.Prime 767489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1499]) (by decide +kernel)
def pv767489 : PrimeValue := ⟨767489, pr767489⟩
private theorem pr767509 : Nat.Prime 767509 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv9137]) (by decide +kernel)
def pv767509 : PrimeValue := ⟨767509, pr767509⟩
private theorem pr767587 : Nat.Prime 767587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv127931]) (by decide +kernel)
def pv767587 : PrimeValue := ⟨767587, pr767587⟩
private theorem pr767617 : Nat.Prime 767617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1999]) (by decide +kernel)
def pv767617 : PrimeValue := ⟨767617, pr767617⟩
private theorem pr767677 : Nat.Prime 767677 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv19,pv37]) (by decide +kernel)
def pv767677 : PrimeValue := ⟨767677, pr767677⟩
private theorem pr767681 : Nat.Prime 767681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2399]) (by decide +kernel)
def pv767681 : PrimeValue := ⟨767681, pr767681⟩
private theorem pr767729 : Nat.Prime 767729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv3691]) (by decide +kernel)
def pv767729 : PrimeValue := ⟨767729, pr767729⟩
private theorem pr767749 : Nat.Prime 767749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv137,pv467]) (by decide +kernel)
def pv767749 : PrimeValue := ⟨767749, pr767749⟩
private theorem pr767773 : Nat.Prime 767773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7109]) (by decide +kernel)
def pv767773 : PrimeValue := ⟨767773, pr767773⟩
private theorem pr767831 : Nat.Prime 767831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv1567]) (by decide +kernel)
def pv767831 : PrimeValue := ⟨767831, pr767831⟩
private theorem pr767857 : Nat.Prime 767857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv941]) (by decide +kernel)
def pv767857 : PrimeValue := ⟨767857, pr767857⟩
private theorem pr768041 : Nat.Prime 768041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv211]) (by decide +kernel)
def pv768041 : PrimeValue := ⟨768041, pr768041⟩
private theorem pr768049 : Nat.Prime 768049 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv16001]) (by decide +kernel)
def pv768049 : PrimeValue := ⟨768049, pr768049⟩
private theorem pr768133 : Nat.Prime 768133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1123]) (by decide +kernel)
def pv768133 : PrimeValue := ⟨768133, pr768133⟩
private theorem pr768139 : Nat.Prime 768139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv18289]) (by decide +kernel)
def pv768139 : PrimeValue := ⟨768139, pr768139⟩
private theorem pr768169 : Nat.Prime 768169 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv47,pv227]) (by decide +kernel)
def pv768169 : PrimeValue := ⟨768169, pr768169⟩
private theorem pr768263 : Nat.Prime 768263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv47,pv743]) (by decide +kernel)
def pv768263 : PrimeValue := ⟨768263, pr768263⟩
private theorem pr768329 : Nat.Prime 768329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv8731]) (by decide +kernel)
def pv768329 : PrimeValue := ⟨768329, pr768329⟩
private theorem pr768359 : Nat.Prime 768359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv157,pv2447]) (by decide +kernel)
def pv768359 : PrimeValue := ⟨768359, pr768359⟩
private theorem pr768373 : Nat.Prime 768373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv5821]) (by decide +kernel)
def pv768373 : PrimeValue := ⟨768373, pr768373⟩
private theorem pr768419 : Nat.Prime 768419 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv7841]) (by decide +kernel)
def pv768419 : PrimeValue := ⟨768419, pr768419⟩
private theorem pr768479 : Nat.Prime 768479 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv61,pv6299]) (by decide +kernel)
def pv768479 : PrimeValue := ⟨768479, pr768479⟩
private theorem pr768503 : Nat.Prime 768503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv17,pv3229]) (by decide +kernel)
def pv768503 : PrimeValue := ⟨768503, pr768503⟩
private theorem pr768623 : Nat.Prime 768623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv227,pv1693]) (by decide +kernel)
def pv768623 : PrimeValue := ⟨768623, pr768623⟩
private theorem pr768793 : Nat.Prime 768793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv103,pv311]) (by decide +kernel)
def pv768793 : PrimeValue := ⟨768793, pr768793⟩
private theorem pr768923 : Nat.Prime 768923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv4993]) (by decide +kernel)
def pv768923 : PrimeValue := ⟨768923, pr768923⟩
private theorem pr768941 : Nat.Prime 768941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv38447]) (by decide +kernel)
def pv768941 : PrimeValue := ⟨768941, pr768941⟩
private theorem pr768983 : Nat.Prime 768983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv73,pv229]) (by decide +kernel)
def pv768983 : PrimeValue := ⟨768983, pr768983⟩
private theorem pr769003 : Nat.Prime 769003 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv13,pv9859]) (by decide +kernel)
def pv769003 : PrimeValue := ⟨769003, pr769003⟩
private theorem pr769019 : Nat.Prime 769019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv384509]) (by decide +kernel)
def pv769019 : PrimeValue := ⟨769019, pr769019⟩
private theorem pr769147 : Nat.Prime 769147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv18313]) (by decide +kernel)
def pv769147 : PrimeValue := ⟨769147, pr769147⟩
private theorem pr769243 : Nat.Prime 769243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv53,pv59]) (by decide +kernel)
def pv769243 : PrimeValue := ⟨769243, pr769243⟩
private theorem pr769259 : Nat.Prime 769259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv2389]) (by decide +kernel)
def pv769259 : PrimeValue := ⟨769259, pr769259⟩
private theorem pr769273 : Nat.Prime 769273 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv19,pv241]) (by decide +kernel)
def pv769273 : PrimeValue := ⟨769273, pr769273⟩
private theorem pr769357 : Nat.Prime 769357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv43,pv71]) (by decide +kernel)
def pv769357 : PrimeValue := ⟨769357, pr769357⟩
private theorem pr769423 : Nat.Prime 769423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv128237]) (by decide +kernel)
def pv769423 : PrimeValue := ⟨769423, pr769423⟩
private theorem pr769429 : Nat.Prime 769429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv29,pv67]) (by decide +kernel)
def pv769429 : PrimeValue := ⟨769429, pr769429⟩
private theorem pr769453 : Nat.Prime 769453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv1733]) (by decide +kernel)
def pv769453 : PrimeValue := ⟨769453, pr769453⟩
private theorem pr769469 : Nat.Prime 769469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv27481]) (by decide +kernel)
def pv769469 : PrimeValue := ⟨769469, pr769469⟩
private theorem pr769663 : Nat.Prime 769663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4751]) (by decide +kernel)
def pv769663 : PrimeValue := ⟨769663, pr769663⟩
private theorem pr769673 : Nat.Prime 769673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv47,pv89]) (by decide +kernel)
def pv769673 : PrimeValue := ⟨769673, pr769673⟩
private theorem pr769687 : Nat.Prime 769687 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv163,pv787]) (by decide +kernel)
def pv769687 : PrimeValue := ⟨769687, pr769687⟩
private theorem pr769733 : Nat.Prime 769733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv199,pv967]) (by decide +kernel)
def pv769733 : PrimeValue := ⟨769733, pr769733⟩
private theorem pr769739 : Nat.Prime 769739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv409,pv941]) (by decide +kernel)
def pv769739 : PrimeValue := ⟨769739, pr769739⟩
private theorem pr769781 : Nat.Prime 769781 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv11,pv3499]) (by decide +kernel)
def pv769781 : PrimeValue := ⟨769781, pr769781⟩
private theorem pr769789 : Nat.Prime 769789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv21383]) (by decide +kernel)
def pv769789 : PrimeValue := ⟨769789, pr769789⟩
private theorem pr769807 : Nat.Prime 769807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv42767]) (by decide +kernel)
def pv769807 : PrimeValue := ⟨769807, pr769807⟩
private theorem pr769903 : Nat.Prime 769903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv797]) (by decide +kernel)
def pv769903 : PrimeValue := ⟨769903, pr769903⟩
private theorem pr769943 : Nat.Prime 769943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv61,pv6311]) (by decide +kernel)
def pv769943 : PrimeValue := ⟨769943, pr769943⟩
private theorem pr770039 : Nat.Prime 770039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv521,pv739]) (by decide +kernel)
def pv770039 : PrimeValue := ⟨770039, pr770039⟩
private theorem pr770059 : Nat.Prime 770059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv179,pv239]) (by decide +kernel)
def pv770059 : PrimeValue := ⟨770059, pr770059⟩
private theorem pr770111 : Nat.Prime 770111 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv7001]) (by decide +kernel)
def pv770111 : PrimeValue := ⟨770111, pr770111⟩
private theorem pr770167 : Nat.Prime 770167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv42787]) (by decide +kernel)
def pv770167 : PrimeValue := ⟨770167, pr770167⟩
private theorem pr770183 : Nat.Prime 770183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv29,pv271]) (by decide +kernel)
def pv770183 : PrimeValue := ⟨770183, pr770183⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
