/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table128
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table128.pv752483
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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr752483 : PrimeCertificate 752483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv376241]) (by decide +kernel)
def pv752483 : PrimeValue := ⟨752483, pr752483⟩
private theorem pr752503 : PrimeCertificate 752503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv167,pv751]) (by decide +kernel)
def pv752503 : PrimeValue := ⟨752503, pr752503⟩
private theorem pr752639 : PrimeCertificate 752639 :=
  certifyPrime (q := pv19) (ls := [pv2,pv107,pv3517]) (by decide +kernel)
def pv752639 : PrimeValue := ⟨752639, pr752639⟩
private theorem pr752797 : PrimeCertificate 752797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1901]) (by decide +kernel)
def pv752797 : PrimeValue := ⟨752797, pr752797⟩
private theorem pr752803 : PrimeCertificate 752803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv3391]) (by decide +kernel)
def pv752803 : PrimeValue := ⟨752803, pr752803⟩
private theorem pr752809 : PrimeCertificate 752809 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv4481]) (by decide +kernel)
def pv752809 : PrimeValue := ⟨752809, pr752809⟩
private theorem pr752861 : PrimeCertificate 752861 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv37643]) (by decide +kernel)
def pv752861 : PrimeValue := ⟨752861, pr752861⟩
private theorem pr752977 : PrimeCertificate 752977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv83]) (by decide +kernel)
def pv752977 : PrimeValue := ⟨752977, pr752977⟩
private theorem pr753127 : PrimeCertificate 753127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv11411]) (by decide +kernel)
def pv753127 : PrimeValue := ⟨753127, pr753127⟩
private theorem pr753133 : PrimeCertificate 753133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv62761]) (by decide +kernel)
def pv753133 : PrimeValue := ⟨753133, pr753133⟩
private theorem pr753143 : PrimeCertificate 753143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv83,pv349]) (by decide +kernel)
def pv753143 : PrimeValue := ⟨753143, pr753143⟩
private theorem pr753463 : PrimeCertificate 753463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4651]) (by decide +kernel)
def pv753463 : PrimeValue := ⟨753463, pr753463⟩
private theorem pr753547 : PrimeCertificate 753547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv125591]) (by decide +kernel)
def pv753547 : PrimeValue := ⟨753547, pr753547⟩
private theorem pr753569 : PrimeCertificate 753569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23549]) (by decide +kernel)
def pv753569 : PrimeValue := ⟨753569, pr753569⟩
private theorem pr753689 : PrimeCertificate 753689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv7247]) (by decide +kernel)
def pv753689 : PrimeValue := ⟨753689, pr753689⟩
private theorem pr753719 : PrimeCertificate 753719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv7691]) (by decide +kernel)
def pv753719 : PrimeValue := ⟨753719, pr753719⟩
private theorem pr753743 : PrimeCertificate 753743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv34261]) (by decide +kernel)
def pv753743 : PrimeValue := ⟨753743, pr753743⟩
private theorem pr753799 : PrimeCertificate 753799 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv73,pv1721]) (by decide +kernel)
def pv753799 : PrimeValue := ⟨753799, pr753799⟩
private theorem pr753803 : PrimeCertificate 753803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv2341]) (by decide +kernel)
def pv753803 : PrimeValue := ⟨753803, pr753803⟩
private theorem pr753859 : PrimeCertificate 753859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv193]) (by decide +kernel)
def pv753859 : PrimeValue := ⟨753859, pr753859⟩
private theorem pr754057 : PrimeCertificate 754057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3491]) (by decide +kernel)
def pv754057 : PrimeValue := ⟨754057, pr754057⟩
private theorem pr754073 : PrimeCertificate 754073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv19,pv41]) (by decide +kernel)
def pv754073 : PrimeValue := ⟨754073, pr754073⟩
private theorem pr754109 : PrimeCertificate 754109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv188527]) (by decide +kernel)
def pv754109 : PrimeValue := ⟨754109, pr754109⟩
private theorem pr754153 : PrimeCertificate 754153 :=
  certifyPrime (q := pv61) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv754153 : PrimeValue := ⟨754153, pr754153⟩
private theorem pr754249 : PrimeCertificate 754249 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv2857]) (by decide +kernel)
def pv754249 : PrimeValue := ⟨754249, pr754249⟩
private theorem pr754289 : PrimeCertificate 754289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47143]) (by decide +kernel)
def pv754289 : PrimeValue := ⟨754289, pr754289⟩
private theorem pr754343 : PrimeCertificate 754343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv377171]) (by decide +kernel)
def pv754343 : PrimeValue := ⟨754343, pr754343⟩
private theorem pr754489 : PrimeCertificate 754489 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv499]) (by decide +kernel)
def pv754489 : PrimeValue := ⟨754489, pr754489⟩
private theorem pr754703 : PrimeCertificate 754703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv29027]) (by decide +kernel)
def pv754703 : PrimeValue := ⟨754703, pr754703⟩
private theorem pr754811 : PrimeCertificate 754811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv41,pv263]) (by decide +kernel)
def pv754811 : PrimeValue := ⟨754811, pr754811⟩
private theorem pr754829 : PrimeCertificate 754829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv188707]) (by decide +kernel)
def pv754829 : PrimeValue := ⟨754829, pr754829⟩
private theorem pr754931 : PrimeCertificate 754931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv6863]) (by decide +kernel)
def pv754931 : PrimeValue := ⟨754931, pr754931⟩
private theorem pr754973 : PrimeCertificate 754973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv1091]) (by decide +kernel)
def pv754973 : PrimeValue := ⟨754973, pr754973⟩
private theorem pr755077 : PrimeCertificate 755077 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv89,pv101]) (by decide +kernel)
def pv755077 : PrimeValue := ⟨755077, pr755077⟩
private theorem pr755081 : PrimeCertificate 755081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv43,pv439]) (by decide +kernel)
def pv755081 : PrimeValue := ⟨755081, pr755081⟩
private theorem pr755171 : PrimeCertificate 755171 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv37,pv157]) (by decide +kernel)
def pv755171 : PrimeValue := ⟨755171, pr755171⟩
private theorem pr755213 : PrimeCertificate 755213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv523]) (by decide +kernel)
def pv755213 : PrimeValue := ⟨755213, pr755213⟩
private theorem pr755239 : PrimeCertificate 755239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv11443]) (by decide +kernel)
def pv755239 : PrimeValue := ⟨755239, pr755239⟩
private theorem pr755351 : PrimeCertificate 755351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv15107]) (by decide +kernel)
def pv755351 : PrimeValue := ⟨755351, pr755351⟩
private theorem pr755399 : PrimeCertificate 755399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv79,pv683]) (by decide +kernel)
def pv755399 : PrimeValue := ⟨755399, pr755399⟩
private theorem pr755449 : PrimeCertificate 755449 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv31477]) (by decide +kernel)
def pv755449 : PrimeValue := ⟨755449, pr755449⟩
private theorem pr755483 : PrimeCertificate 755483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv593]) (by decide +kernel)
def pv755483 : PrimeValue := ⟨755483, pr755483⟩
private theorem pr755593 : PrimeCertificate 755593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv1657]) (by decide +kernel)
def pv755593 : PrimeValue := ⟨755593, pr755593⟩
private theorem pr755663 : PrimeCertificate 755663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv377831]) (by decide +kernel)
def pv755663 : PrimeValue := ⟨755663, pr755663⟩
private theorem pr755737 : PrimeCertificate 755737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31489]) (by decide +kernel)
def pv755737 : PrimeValue := ⟨755737, pr755737⟩
private theorem pr755861 : PrimeCertificate 755861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv5399]) (by decide +kernel)
def pv755861 : PrimeValue := ⟨755861, pr755861⟩
private theorem pr755869 : PrimeCertificate 755869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv62989]) (by decide +kernel)
def pv755869 : PrimeValue := ⟨755869, pr755869⟩
private theorem pr756011 : PrimeCertificate 756011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv23,pv173]) (by decide +kernel)
def pv756011 : PrimeValue := ⟨756011, pr756011⟩
private theorem pr756149 : PrimeCertificate 756149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv8219]) (by decide +kernel)
def pv756149 : PrimeValue := ⟨756149, pr756149⟩
private theorem pr756191 : PrimeCertificate 756191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv75619]) (by decide +kernel)
def pv756191 : PrimeValue := ⟨756191, pr756191⟩
private theorem pr756199 : PrimeCertificate 756199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv977]) (by decide +kernel)
def pv756199 : PrimeValue := ⟨756199, pr756199⟩
private theorem pr756319 : PrimeCertificate 756319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv233,pv541]) (by decide +kernel)
def pv756319 : PrimeValue := ⟨756319, pr756319⟩
private theorem pr756533 : PrimeCertificate 756533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv41,pv659]) (by decide +kernel)
def pv756533 : PrimeValue := ⟨756533, pr756533⟩
private theorem pr756667 : PrimeCertificate 756667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv127,pv331]) (by decide +kernel)
def pv756667 : PrimeValue := ⟨756667, pr756667⟩
private theorem pr756683 : PrimeCertificate 756683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv397,pv953]) (by decide +kernel)
def pv756683 : PrimeValue := ⟨756683, pr756683⟩
private theorem pr756739 : PrimeCertificate 756739 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv2473]) (by decide +kernel)
def pv756739 : PrimeValue := ⟨756739, pr756739⟩
private theorem pr756869 : PrimeCertificate 756869 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv27031]) (by decide +kernel)
def pv756869 : PrimeValue := ⟨756869, pr756869⟩
private theorem pr757019 : PrimeCertificate 757019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv378509]) (by decide +kernel)
def pv757019 : PrimeValue := ⟨757019, pr757019⟩
private theorem pr757181 : PrimeCertificate 757181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv131]) (by decide +kernel)
def pv757181 : PrimeValue := ⟨757181, pr757181⟩
private theorem pr757243 : PrimeCertificate 757243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv379]) (by decide +kernel)
def pv757243 : PrimeValue := ⟨757243, pr757243⟩
private theorem pr757327 : PrimeCertificate 757327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv113,pv1117]) (by decide +kernel)
def pv757327 : PrimeValue := ⟨757327, pr757327⟩
private theorem pr757433 : PrimeCertificate 757433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv7283]) (by decide +kernel)
def pv757433 : PrimeValue := ⟨757433, pr757433⟩
private theorem pr757481 : PrimeCertificate 757481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv653]) (by decide +kernel)
def pv757481 : PrimeValue := ⟨757481, pr757481⟩
private theorem pr757579 : PrimeCertificate 757579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv4073]) (by decide +kernel)
def pv757579 : PrimeValue := ⟨757579, pr757579⟩
private theorem pr757709 : PrimeCertificate 757709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv27061]) (by decide +kernel)
def pv757709 : PrimeValue := ⟨757709, pr757709⟩
private theorem pr757811 : PrimeCertificate 757811 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv75781]) (by decide +kernel)
def pv757811 : PrimeValue := ⟨757811, pr757811⟩
private theorem pr758003 : PrimeCertificate 758003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv1867]) (by decide +kernel)
def pv758003 : PrimeValue := ⟨758003, pr758003⟩
private theorem pr758053 : PrimeCertificate 758053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7019]) (by decide +kernel)
def pv758053 : PrimeValue := ⟨758053, pr758053⟩
private theorem pr758083 : PrimeCertificate 758083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv9719]) (by decide +kernel)
def pv758083 : PrimeValue := ⟨758083, pr758083⟩
private theorem pr758099 : PrimeCertificate 758099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv2027]) (by decide +kernel)
def pv758099 : PrimeValue := ⟨758099, pr758099⟩
private theorem pr758179 : PrimeCertificate 758179 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv73,pv577]) (by decide +kernel)
def pv758179 : PrimeValue := ⟨758179, pr758179⟩
private theorem pr758273 : PrimeCertificate 758273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1481]) (by decide +kernel)
def pv758273 : PrimeValue := ⟨758273, pr758273⟩
private theorem pr758383 : PrimeCertificate 758383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv126397]) (by decide +kernel)
def pv758383 : PrimeValue := ⟨758383, pr758383⟩
private theorem pr758441 : PrimeCertificate 758441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv67,pv283]) (by decide +kernel)
def pv758441 : PrimeValue := ⟨758441, pr758441⟩
private theorem pr758503 : PrimeCertificate 758503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv42139]) (by decide +kernel)
def pv758503 : PrimeValue := ⟨758503, pr758503⟩
private theorem pr758519 : PrimeCertificate 758519 :=
  certifyPrime (q := pv11) (ls := [pv2,pv19,pv19961]) (by decide +kernel)
def pv758519 : PrimeValue := ⟨758519, pr758519⟩
private theorem pr758711 : PrimeCertificate 758711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv4463]) (by decide +kernel)
def pv758711 : PrimeValue := ⟨758711, pr758711⟩
private theorem pr758713 : PrimeCertificate 758713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv101,pv313]) (by decide +kernel)
def pv758713 : PrimeValue := ⟨758713, pr758713⟩
private theorem pr758743 : PrimeCertificate 758743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv126457]) (by decide +kernel)
def pv758743 : PrimeValue := ⟨758743, pr758743⟩
private theorem pr758753 : PrimeCertificate 758753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv131,pv181]) (by decide +kernel)
def pv758753 : PrimeValue := ⟨758753, pr758753⟩
private theorem pr758783 : PrimeCertificate 758783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv379391]) (by decide +kernel)
def pv758783 : PrimeValue := ⟨758783, pr758783⟩
private theorem pr758819 : PrimeCertificate 758819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv12239]) (by decide +kernel)
def pv758819 : PrimeValue := ⟨758819, pr758819⟩
private theorem pr758929 : PrimeCertificate 758929 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv97,pv163]) (by decide +kernel)
def pv758929 : PrimeValue := ⟨758929, pr758929⟩
private theorem pr758963 : PrimeCertificate 758963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv6221]) (by decide +kernel)
def pv758963 : PrimeValue := ⟨758963, pr758963⟩
private theorem pr758969 : PrimeCertificate 758969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13553]) (by decide +kernel)
def pv758969 : PrimeValue := ⟨758969, pr758969⟩
private theorem pr759131 : PrimeCertificate 759131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv75913]) (by decide +kernel)
def pv759131 : PrimeValue := ⟨759131, pr759131⟩
private theorem pr759179 : PrimeCertificate 759179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv211,pv257]) (by decide +kernel)
def pv759179 : PrimeValue := ⟨759179, pr759179⟩
private theorem pr759371 : PrimeCertificate 759371 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv75937]) (by decide +kernel)
def pv759371 : PrimeValue := ⟨759371, pr759371⟩
private theorem pr759431 : PrimeCertificate 759431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv19,pv571]) (by decide +kernel)
def pv759431 : PrimeValue := ⟨759431, pr759431⟩
private theorem pr759457 : PrimeCertificate 759457 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv293]) (by decide +kernel)
def pv759457 : PrimeValue := ⟨759457, pr759457⟩
private theorem pr759553 : PrimeCertificate 759553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv43]) (by decide +kernel)
def pv759553 : PrimeValue := ⟨759553, pr759553⟩
private theorem pr759581 : PrimeCertificate 759581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv163,pv233]) (by decide +kernel)
def pv759581 : PrimeValue := ⟨759581, pr759581⟩
private theorem pr759641 : PrimeCertificate 759641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv2713]) (by decide +kernel)
def pv759641 : PrimeValue := ⟨759641, pr759641⟩
private theorem pr759719 : PrimeCertificate 759719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv379859]) (by decide +kernel)
def pv759719 : PrimeValue := ⟨759719, pr759719⟩
private theorem pr759833 : PrimeCertificate 759833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv37,pv151]) (by decide +kernel)
def pv759833 : PrimeValue := ⟨759833, pr759833⟩
private theorem pr759953 : PrimeCertificate 759953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47497]) (by decide +kernel)
def pv759953 : PrimeValue := ⟨759953, pr759953⟩
private theorem pr760079 : PrimeCertificate 760079 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv34549]) (by decide +kernel)
def pv760079 : PrimeValue := ⟨760079, pr760079⟩
private theorem pr760117 : PrimeCertificate 760117 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv9049]) (by decide +kernel)
def pv760117 : PrimeValue := ⟨760117, pr760117⟩
private theorem pr760129 : PrimeCertificate 760129 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv37,pv107]) (by decide +kernel)
def pv760129 : PrimeValue := ⟨760129, pr760129⟩
private theorem pr760153 : PrimeCertificate 760153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv1667]) (by decide +kernel)
def pv760153 : PrimeValue := ⟨760153, pr760153⟩
private theorem pr760169 : PrimeCertificate 760169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv95021]) (by decide +kernel)
def pv760169 : PrimeValue := ⟨760169, pr760169⟩
private theorem pr760183 : PrimeCertificate 760183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv61,pv67]) (by decide +kernel)
def pv760183 : PrimeValue := ⟨760183, pr760183⟩
private theorem pr760211 : PrimeCertificate 760211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv6911]) (by decide +kernel)
def pv760211 : PrimeValue := ⟨760211, pr760211⟩
private theorem pr760237 : PrimeCertificate 760237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv63353]) (by decide +kernel)
def pv760237 : PrimeValue := ⟨760237, pr760237⟩
private theorem pr760241 : PrimeCertificate 760241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv17,pv43]) (by decide +kernel)
def pv760241 : PrimeValue := ⟨760241, pr760241⟩
private theorem pr760289 : PrimeCertificate 760289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv1033]) (by decide +kernel)
def pv760289 : PrimeValue := ⟨760289, pr760289⟩
private theorem pr760297 : PrimeCertificate 760297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv79,pv401]) (by decide +kernel)
def pv760297 : PrimeValue := ⟨760297, pr760297⟩
private theorem pr760373 : PrimeCertificate 760373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv190093]) (by decide +kernel)
def pv760373 : PrimeValue := ⟨760373, pr760373⟩
private theorem pr760447 : PrimeCertificate 760447 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv83,pv509]) (by decide +kernel)
def pv760447 : PrimeValue := ⟨760447, pr760447⟩
private theorem pr760579 : PrimeCertificate 760579 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv199]) (by decide +kernel)
def pv760579 : PrimeValue := ⟨760579, pr760579⟩
private theorem pr760657 : PrimeCertificate 760657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv23,pv53]) (by decide +kernel)
def pv760657 : PrimeValue := ⟨760657, pr760657⟩
private theorem pr760759 : PrimeCertificate 760759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv103,pv1231]) (by decide +kernel)
def pv760759 : PrimeValue := ⟨760759, pr760759⟩
private theorem pr760783 : PrimeCertificate 760783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv11527]) (by decide +kernel)
def pv760783 : PrimeValue := ⟨760783, pr760783⟩
private theorem pr760901 : PrimeCertificate 760901 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv1087]) (by decide +kernel)
def pv760901 : PrimeValue := ⟨760901, pr760901⟩
private theorem pr760993 : PrimeCertificate 760993 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7927]) (by decide +kernel)
def pv760993 : PrimeValue := ⟨760993, pr760993⟩
private theorem pr761009 : PrimeCertificate 761009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47563]) (by decide +kernel)
def pv761009 : PrimeValue := ⟨761009, pr761009⟩
private theorem pr761213 : PrimeCertificate 761213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv4049]) (by decide +kernel)
def pv761213 : PrimeValue := ⟨761213, pr761213⟩
private theorem pr761363 : PrimeCertificate 761363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv457]) (by decide +kernel)
def pv761363 : PrimeValue := ⟨761363, pr761363⟩
private theorem pr761399 : PrimeCertificate 761399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv53,pv653]) (by decide +kernel)
def pv761399 : PrimeValue := ⟨761399, pr761399⟩
private theorem pr761443 : PrimeCertificate 761443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv83,pv139]) (by decide +kernel)
def pv761443 : PrimeValue := ⟨761443, pr761443⟩
private theorem pr761531 : PrimeCertificate 761531 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv11,pv23,pv43]) (by decide +kernel)
def pv761531 : PrimeValue := ⟨761531, pr761531⟩
private theorem pr761533 : PrimeCertificate 761533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv3733]) (by decide +kernel)
def pv761533 : PrimeValue := ⟨761533, pr761533⟩
private theorem pr761543 : PrimeCertificate 761543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv503,pv757]) (by decide +kernel)
def pv761543 : PrimeValue := ⟨761543, pr761543⟩
private theorem pr761669 : PrimeCertificate 761669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv23,pv487]) (by decide +kernel)
def pv761669 : PrimeValue := ⟨761669, pr761669⟩
private theorem pr761809 : PrimeCertificate 761809 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv59,pv269]) (by decide +kernel)
def pv761809 : PrimeValue := ⟨761809, pr761809⟩
private theorem pr761833 : PrimeCertificate 761833 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv3527]) (by decide +kernel)
def pv761833 : PrimeValue := ⟨761833, pr761833⟩
private theorem pr761977 : PrimeCertificate 761977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv557]) (by decide +kernel)
def pv761977 : PrimeValue := ⟨761977, pr761977⟩
private theorem pr761993 : PrimeCertificate 761993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv1237]) (by decide +kernel)
def pv761993 : PrimeValue := ⟨761993, pr761993⟩
private theorem pr762049 : PrimeCertificate 762049 :=
  certifyPrime (q := pv61) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv762049 : PrimeValue := ⟨762049, pr762049⟩
private theorem pr762367 : PrimeCertificate 762367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv11551]) (by decide +kernel)
def pv762367 : PrimeValue := ⟨762367, pr762367⟩
private theorem pr762397 : PrimeCertificate 762397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv63533]) (by decide +kernel)
def pv762397 : PrimeValue := ⟨762397, pr762397⟩
private theorem pr762893 : PrimeCertificate 762893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv863]) (by decide +kernel)
def pv762893 : PrimeValue := ⟨762893, pr762893⟩
private theorem pr762919 : PrimeCertificate 762919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv9781]) (by decide +kernel)
def pv762919 : PrimeValue := ⟨762919, pr762919⟩
private theorem pr762967 : PrimeCertificate 762967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71,pv199]) (by decide +kernel)
def pv762967 : PrimeValue := ⟨762967, pr762967⟩
private theorem pr763039 : PrimeCertificate 763039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv42391]) (by decide +kernel)
def pv763039 : PrimeValue := ⟨763039, pr763039⟩
private theorem pr763043 : PrimeCertificate 763043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv54503]) (by decide +kernel)
def pv763043 : PrimeValue := ⟨763043, pr763043⟩
private theorem pr763093 : PrimeCertificate 763093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv41,pv47]) (by decide +kernel)
def pv763093 : PrimeValue := ⟨763093, pr763093⟩
private theorem pr763183 : PrimeCertificate 763183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv673]) (by decide +kernel)
def pv763183 : PrimeValue := ⟨763183, pr763183⟩
private theorem pr763237 : PrimeCertificate 763237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv191]) (by decide +kernel)
def pv763237 : PrimeValue := ⟨763237, pr763237⟩
private theorem pr763403 : PrimeCertificate 763403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv22453]) (by decide +kernel)
def pv763403 : PrimeValue := ⟨763403, pr763403⟩
private theorem pr763417 : PrimeCertificate 763417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv461]) (by decide +kernel)
def pv763417 : PrimeValue := ⟨763417, pr763417⟩
private theorem pr763447 : PrimeCertificate 763447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv127241]) (by decide +kernel)
def pv763447 : PrimeValue := ⟨763447, pr763447⟩
private theorem pr763523 : PrimeCertificate 763523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv381761]) (by decide +kernel)
def pv763523 : PrimeValue := ⟨763523, pr763523⟩
private theorem pr763549 : PrimeCertificate 763549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv63629]) (by decide +kernel)
def pv763549 : PrimeValue := ⟨763549, pr763549⟩
private theorem pr763601 : PrimeCertificate 763601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv83]) (by decide +kernel)
def pv763601 : PrimeValue := ⟨763601, pr763601⟩
private theorem pr763649 : PrimeCertificate 763649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv157]) (by decide +kernel)
def pv763649 : PrimeValue := ⟨763649, pr763649⟩
private theorem pr763673 : PrimeCertificate 763673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv1049]) (by decide +kernel)
def pv763673 : PrimeValue := ⟨763673, pr763673⟩
private theorem pr763843 : PrimeCertificate 763843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv2087]) (by decide +kernel)
def pv763843 : PrimeValue := ⟨763843, pr763843⟩
private theorem pr763897 : PrimeCertificate 763897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv4547]) (by decide +kernel)
def pv763897 : PrimeValue := ⟨763897, pr763897⟩
private theorem pr763901 : PrimeCertificate 763901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7639]) (by decide +kernel)
def pv763901 : PrimeValue := ⟨763901, pr763901⟩
private theorem pr763943 : PrimeCertificate 763943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv7207]) (by decide +kernel)
def pv763943 : PrimeValue := ⟨763943, pr763943⟩
private theorem pr764017 : PrimeCertificate 764017 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1447]) (by decide +kernel)
def pv764017 : PrimeValue := ⟨764017, pr764017⟩
private theorem pr764051 : PrimeCertificate 764051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv37,pv59]) (by decide +kernel)
def pv764051 : PrimeValue := ⟨764051, pr764051⟩
private theorem pr764053 : PrimeCertificate 764053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv63671]) (by decide +kernel)
def pv764053 : PrimeValue := ⟨764053, pr764053⟩
private theorem pr764089 : PrimeCertificate 764089 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv31,pv79]) (by decide +kernel)
def pv764089 : PrimeValue := ⟨764089, pr764089⟩
private theorem pr764111 : PrimeCertificate 764111 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv43,pv1777]) (by decide +kernel)
def pv764111 : PrimeValue := ⟨764111, pr764111⟩
private theorem pr764149 : PrimeCertificate 764149 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv7,pv11,pv827]) (by decide +kernel)
def pv764149 : PrimeValue := ⟨764149, pr764149⟩
private theorem pr764321 : PrimeCertificate 764321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv281]) (by decide +kernel)
def pv764321 : PrimeValue := ⟨764321, pr764321⟩
private theorem pr764399 : PrimeCertificate 764399 :=
  certifyPrime (q := pv11) (ls := [pv2,pv31,pv12329]) (by decide +kernel)
def pv764399 : PrimeValue := ⟨764399, pr764399⟩
private theorem pr764539 : PrimeCertificate 764539 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv127423]) (by decide +kernel)
def pv764539 : PrimeValue := ⟨764539, pr764539⟩
private theorem pr764623 : PrimeCertificate 764623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107,pv397]) (by decide +kernel)
def pv764623 : PrimeValue := ⟨764623, pr764623⟩
private theorem pr764719 : PrimeCertificate 764719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv127453]) (by decide +kernel)
def pv764719 : PrimeValue := ⟨764719, pr764719⟩
private theorem pr764887 : PrimeCertificate 764887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv127481]) (by decide +kernel)
def pv764887 : PrimeValue := ⟨764887, pr764887⟩
private theorem pr764899 : PrimeCertificate 764899 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv7499]) (by decide +kernel)
def pv764899 : PrimeValue := ⟨764899, pr764899⟩
private theorem pr764903 : PrimeCertificate 764903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv20129]) (by decide +kernel)
def pv764903 : PrimeValue := ⟨764903, pr764903⟩
private theorem pr765139 : PrimeCertificate 765139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv11593]) (by decide +kernel)
def pv765139 : PrimeValue := ⟨765139, pr765139⟩
private theorem pr765229 : PrimeCertificate 765229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv1483]) (by decide +kernel)
def pv765229 : PrimeValue := ⟨765229, pr765229⟩
private theorem pr765283 : PrimeCertificate 765283 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv137]) (by decide +kernel)
def pv765283 : PrimeValue := ⟨765283, pr765283⟩
private theorem pr765307 : PrimeCertificate 765307 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv41,pv61]) (by decide +kernel)
def pv765307 : PrimeValue := ⟨765307, pr765307⟩
private theorem pr765379 : PrimeCertificate 765379 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv101,pv421]) (by decide +kernel)
def pv765379 : PrimeValue := ⟨765379, pr765379⟩
private theorem pr765389 : PrimeCertificate 765389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv41,pv359]) (by decide +kernel)
def pv765389 : PrimeValue := ⟨765389, pr765389⟩
private theorem pr765409 : PrimeCertificate 765409 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv17,pv67]) (by decide +kernel)
def pv765409 : PrimeValue := ⟨765409, pr765409⟩
private theorem pr765673 : PrimeCertificate 765673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61,pv523]) (by decide +kernel)
def pv765673 : PrimeValue := ⟨765673, pr765673⟩
private theorem pr765749 : PrimeCertificate 765749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv11261]) (by decide +kernel)
def pv765749 : PrimeValue := ⟨765749, pr765749⟩
private theorem pr765907 : PrimeCertificate 765907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv107,pv1193]) (by decide +kernel)
def pv765907 : PrimeValue := ⟨765907, pr765907⟩
private theorem pr765913 : PrimeCertificate 765913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv47,pv97]) (by decide +kernel)
def pv765913 : PrimeValue := ⟨765913, pr765913⟩
private theorem pr766039 : PrimeCertificate 766039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv23,pv61]) (by decide +kernel)
def pv766039 : PrimeValue := ⟨766039, pr766039⟩
private theorem pr766091 : PrimeCertificate 766091 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv71,pv83]) (by decide +kernel)
def pv766091 : PrimeValue := ⟨766091, pr766091⟩
private theorem pr766163 : PrimeCertificate 766163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv383081]) (by decide +kernel)
def pv766163 : PrimeValue := ⟨766163, pr766163⟩
private theorem pr766237 : PrimeCertificate 766237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv63853]) (by decide +kernel)
def pv766237 : PrimeValue := ⟨766237, pr766237⟩
private theorem pr766301 : PrimeCertificate 766301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv79,pv97]) (by decide +kernel)
def pv766301 : PrimeValue := ⟨766301, pr766301⟩
private theorem pr766313 : PrimeCertificate 766313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv95789]) (by decide +kernel)
def pv766313 : PrimeValue := ⟨766313, pr766313⟩
private theorem pr766333 : PrimeCertificate 766333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv3041]) (by decide +kernel)
def pv766333 : PrimeValue := ⟨766333, pr766333⟩
private theorem pr766361 : PrimeCertificate 766361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv17,pv23]) (by decide +kernel)
def pv766361 : PrimeValue := ⟨766361, pr766361⟩
private theorem pr766369 : PrimeCertificate 766369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv887]) (by decide +kernel)
def pv766369 : PrimeValue := ⟨766369, pr766369⟩
private theorem pr766387 : PrimeCertificate 766387 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv42577]) (by decide +kernel)
def pv766387 : PrimeValue := ⟨766387, pr766387⟩
private theorem pr766453 : PrimeCertificate 766453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv2777]) (by decide +kernel)
def pv766453 : PrimeValue := ⟨766453, pr766453⟩
private theorem pr766541 : PrimeCertificate 766541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv38327]) (by decide +kernel)
def pv766541 : PrimeValue := ⟨766541, pr766541⟩
private theorem pr766553 : PrimeCertificate 766553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv95819]) (by decide +kernel)
def pv766553 : PrimeValue := ⟨766553, pr766553⟩
private theorem pr766721 : PrimeCertificate 766721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv599]) (by decide +kernel)
def pv766721 : PrimeValue := ⟨766721, pr766721⟩
private theorem pr766763 : PrimeCertificate 766763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv3583]) (by decide +kernel)
def pv766763 : PrimeValue := ⟨766763, pr766763⟩
private theorem pr766957 : PrimeCertificate 766957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv63913]) (by decide +kernel)
def pv766957 : PrimeValue := ⟨766957, pr766957⟩
private theorem pr767017 : PrimeCertificate 767017 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv53,pv67]) (by decide +kernel)
def pv767017 : PrimeValue := ⟨767017, pr767017⟩
private theorem pr767051 : PrimeCertificate 767051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv29]) (by decide +kernel)
def pv767051 : PrimeValue := ⟨767051, pr767051⟩
private theorem pr767111 : PrimeCertificate 767111 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv41,pv1871]) (by decide +kernel)
def pv767111 : PrimeValue := ⟨767111, pr767111⟩
private theorem pr767293 : PrimeCertificate 767293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv1487]) (by decide +kernel)
def pv767293 : PrimeValue := ⟨767293, pr767293⟩
private theorem pr767489 : PrimeCertificate 767489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1499]) (by decide +kernel)
def pv767489 : PrimeValue := ⟨767489, pr767489⟩
private theorem pr767509 : PrimeCertificate 767509 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv9137]) (by decide +kernel)
def pv767509 : PrimeValue := ⟨767509, pr767509⟩
private theorem pr767587 : PrimeCertificate 767587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv127931]) (by decide +kernel)
def pv767587 : PrimeValue := ⟨767587, pr767587⟩
private theorem pr767617 : PrimeCertificate 767617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1999]) (by decide +kernel)
def pv767617 : PrimeValue := ⟨767617, pr767617⟩
private theorem pr767677 : PrimeCertificate 767677 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv19,pv37]) (by decide +kernel)
def pv767677 : PrimeValue := ⟨767677, pr767677⟩
private theorem pr767681 : PrimeCertificate 767681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2399]) (by decide +kernel)
def pv767681 : PrimeValue := ⟨767681, pr767681⟩
private theorem pr767729 : PrimeCertificate 767729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv3691]) (by decide +kernel)
def pv767729 : PrimeValue := ⟨767729, pr767729⟩
private theorem pr767749 : PrimeCertificate 767749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137,pv467]) (by decide +kernel)
def pv767749 : PrimeValue := ⟨767749, pr767749⟩
private theorem pr767773 : PrimeCertificate 767773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7109]) (by decide +kernel)
def pv767773 : PrimeValue := ⟨767773, pr767773⟩
private theorem pr767831 : PrimeCertificate 767831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv1567]) (by decide +kernel)
def pv767831 : PrimeValue := ⟨767831, pr767831⟩
private theorem pr767857 : PrimeCertificate 767857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv941]) (by decide +kernel)
def pv767857 : PrimeValue := ⟨767857, pr767857⟩
private theorem pr768041 : PrimeCertificate 768041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv211]) (by decide +kernel)
def pv768041 : PrimeValue := ⟨768041, pr768041⟩
private theorem pr768049 : PrimeCertificate 768049 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv16001]) (by decide +kernel)
def pv768049 : PrimeValue := ⟨768049, pr768049⟩
private theorem pr768133 : PrimeCertificate 768133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1123]) (by decide +kernel)
def pv768133 : PrimeValue := ⟨768133, pr768133⟩
private theorem pr768139 : PrimeCertificate 768139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv18289]) (by decide +kernel)
def pv768139 : PrimeValue := ⟨768139, pr768139⟩
private theorem pr768169 : PrimeCertificate 768169 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv47,pv227]) (by decide +kernel)
def pv768169 : PrimeValue := ⟨768169, pr768169⟩
private theorem pr768263 : PrimeCertificate 768263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv47,pv743]) (by decide +kernel)
def pv768263 : PrimeValue := ⟨768263, pr768263⟩
private theorem pr768329 : PrimeCertificate 768329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv8731]) (by decide +kernel)
def pv768329 : PrimeValue := ⟨768329, pr768329⟩
private theorem pr768359 : PrimeCertificate 768359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv157,pv2447]) (by decide +kernel)
def pv768359 : PrimeValue := ⟨768359, pr768359⟩
private theorem pr768373 : PrimeCertificate 768373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv5821]) (by decide +kernel)
def pv768373 : PrimeValue := ⟨768373, pr768373⟩
private theorem pr768419 : PrimeCertificate 768419 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv7841]) (by decide +kernel)
def pv768419 : PrimeValue := ⟨768419, pr768419⟩
private theorem pr768479 : PrimeCertificate 768479 :=
  certifyPrime (q := pv17) (ls := [pv2,pv61,pv6299]) (by decide +kernel)
def pv768479 : PrimeValue := ⟨768479, pr768479⟩
private theorem pr768503 : PrimeCertificate 768503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv17,pv3229]) (by decide +kernel)
def pv768503 : PrimeValue := ⟨768503, pr768503⟩
private theorem pr768623 : PrimeCertificate 768623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv227,pv1693]) (by decide +kernel)
def pv768623 : PrimeValue := ⟨768623, pr768623⟩
private theorem pr768793 : PrimeCertificate 768793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103,pv311]) (by decide +kernel)
def pv768793 : PrimeValue := ⟨768793, pr768793⟩
private theorem pr768923 : PrimeCertificate 768923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv4993]) (by decide +kernel)
def pv768923 : PrimeValue := ⟨768923, pr768923⟩
private theorem pr768941 : PrimeCertificate 768941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv38447]) (by decide +kernel)
def pv768941 : PrimeValue := ⟨768941, pr768941⟩
private theorem pr768983 : PrimeCertificate 768983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv73,pv229]) (by decide +kernel)
def pv768983 : PrimeValue := ⟨768983, pr768983⟩
private theorem pr769003 : PrimeCertificate 769003 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv13,pv9859]) (by decide +kernel)
def pv769003 : PrimeValue := ⟨769003, pr769003⟩
private theorem pr769019 : PrimeCertificate 769019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv384509]) (by decide +kernel)
def pv769019 : PrimeValue := ⟨769019, pr769019⟩
private theorem pr769147 : PrimeCertificate 769147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv18313]) (by decide +kernel)
def pv769147 : PrimeValue := ⟨769147, pr769147⟩
private theorem pr769243 : PrimeCertificate 769243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv53,pv59]) (by decide +kernel)
def pv769243 : PrimeValue := ⟨769243, pr769243⟩
private theorem pr769259 : PrimeCertificate 769259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv2389]) (by decide +kernel)
def pv769259 : PrimeValue := ⟨769259, pr769259⟩
private theorem pr769273 : PrimeCertificate 769273 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv19,pv241]) (by decide +kernel)
def pv769273 : PrimeValue := ⟨769273, pr769273⟩
private theorem pr769357 : PrimeCertificate 769357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv43,pv71]) (by decide +kernel)
def pv769357 : PrimeValue := ⟨769357, pr769357⟩
private theorem pr769423 : PrimeCertificate 769423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv128237]) (by decide +kernel)
def pv769423 : PrimeValue := ⟨769423, pr769423⟩
private theorem pr769429 : PrimeCertificate 769429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv29,pv67]) (by decide +kernel)
def pv769429 : PrimeValue := ⟨769429, pr769429⟩
private theorem pr769453 : PrimeCertificate 769453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv1733]) (by decide +kernel)
def pv769453 : PrimeValue := ⟨769453, pr769453⟩
private theorem pr769469 : PrimeCertificate 769469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv27481]) (by decide +kernel)
def pv769469 : PrimeValue := ⟨769469, pr769469⟩
private theorem pr769663 : PrimeCertificate 769663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4751]) (by decide +kernel)
def pv769663 : PrimeValue := ⟨769663, pr769663⟩
private theorem pr769673 : PrimeCertificate 769673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv47,pv89]) (by decide +kernel)
def pv769673 : PrimeValue := ⟨769673, pr769673⟩
private theorem pr769687 : PrimeCertificate 769687 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv163,pv787]) (by decide +kernel)
def pv769687 : PrimeValue := ⟨769687, pr769687⟩
private theorem pr769733 : PrimeCertificate 769733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv199,pv967]) (by decide +kernel)
def pv769733 : PrimeValue := ⟨769733, pr769733⟩
private theorem pr769739 : PrimeCertificate 769739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv409,pv941]) (by decide +kernel)
def pv769739 : PrimeValue := ⟨769739, pr769739⟩
private theorem pr769781 : PrimeCertificate 769781 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv11,pv3499]) (by decide +kernel)
def pv769781 : PrimeValue := ⟨769781, pr769781⟩
private theorem pr769789 : PrimeCertificate 769789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv21383]) (by decide +kernel)
def pv769789 : PrimeValue := ⟨769789, pr769789⟩
private theorem pr769807 : PrimeCertificate 769807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv42767]) (by decide +kernel)
def pv769807 : PrimeValue := ⟨769807, pr769807⟩
private theorem pr769903 : PrimeCertificate 769903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv797]) (by decide +kernel)
def pv769903 : PrimeValue := ⟨769903, pr769903⟩
private theorem pr769943 : PrimeCertificate 769943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv6311]) (by decide +kernel)
def pv769943 : PrimeValue := ⟨769943, pr769943⟩
private theorem pr770039 : PrimeCertificate 770039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv521,pv739]) (by decide +kernel)
def pv770039 : PrimeValue := ⟨770039, pr770039⟩
private theorem pr770059 : PrimeCertificate 770059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv179,pv239]) (by decide +kernel)
def pv770059 : PrimeValue := ⟨770059, pr770059⟩
private theorem pr770111 : PrimeCertificate 770111 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv7001]) (by decide +kernel)
def pv770111 : PrimeValue := ⟨770111, pr770111⟩
private theorem pr770167 : PrimeCertificate 770167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv42787]) (by decide +kernel)
def pv770167 : PrimeValue := ⟨770167, pr770167⟩
private theorem pr770183 : PrimeCertificate 770183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv29,pv271]) (by decide +kernel)
def pv770183 : PrimeValue := ⟨770183, pr770183⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
