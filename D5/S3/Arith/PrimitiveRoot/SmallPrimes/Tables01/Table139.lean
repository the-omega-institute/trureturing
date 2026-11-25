/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table139
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table139.pv1051499
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table113
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table114

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1051499 : PrimeCertificate 1051499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv59,pv67]) (by decide +kernel)
def pv1051499 : PrimeValue := ⟨1051499, pr1051499⟩
private theorem pr1051553 : PrimeCertificate 1051553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1933]) (by decide +kernel)
def pv1051553 : PrimeValue := ⟨1051553, pr1051553⟩
private theorem pr1051559 : PrimeCertificate 1051559 :=
  certifyPrime (q := pv11) (ls := [pv2,pv449,pv1171]) (by decide +kernel)
def pv1051559 : PrimeValue := ⟨1051559, pr1051559⟩
private theorem pr1051619 : PrimeCertificate 1051619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv525809]) (by decide +kernel)
def pv1051619 : PrimeValue := ⟨1051619, pr1051619⟩
private theorem pr1052321 : PrimeCertificate 1052321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6577]) (by decide +kernel)
def pv1052321 : PrimeValue := ⟨1052321, pr1052321⟩
private theorem pr1052981 : PrimeCertificate 1052981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv19,pv163]) (by decide +kernel)
def pv1052981 : PrimeValue := ⟨1052981, pr1052981⟩
private theorem pr1053029 : PrimeCertificate 1053029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv263257]) (by decide +kernel)
def pv1053029 : PrimeValue := ⟨1053029, pr1053029⟩
private theorem pr1053191 : PrimeCertificate 1053191 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv105319]) (by decide +kernel)
def pv1053191 : PrimeValue := ⟨1053191, pr1053191⟩
private theorem pr1053491 : PrimeCertificate 1053491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv6197]) (by decide +kernel)
def pv1053491 : PrimeValue := ⟨1053491, pr1053491⟩
private theorem pr1053551 : PrimeCertificate 1053551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv1109]) (by decide +kernel)
def pv1053551 : PrimeValue := ⟨1053551, pr1053551⟩
private theorem pr1053989 : PrimeCertificate 1053989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv20269]) (by decide +kernel)
def pv1053989 : PrimeValue := ⟨1053989, pr1053989⟩
private theorem pr1054043 : PrimeCertificate 1054043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv47911]) (by decide +kernel)
def pv1054043 : PrimeValue := ⟨1054043, pr1054043⟩
private theorem pr1054061 : PrimeCertificate 1054061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv7529]) (by decide +kernel)
def pv1054061 : PrimeValue := ⟨1054061, pr1054061⟩
private theorem pr1054169 : PrimeCertificate 1054169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv131771]) (by decide +kernel)
def pv1054169 : PrimeValue := ⟨1054169, pr1054169⟩
private theorem pr1054181 : PrimeCertificate 1054181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv52709]) (by decide +kernel)
def pv1054181 : PrimeValue := ⟨1054181, pr1054181⟩
private theorem pr1054439 : PrimeCertificate 1054439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv41,pv167]) (by decide +kernel)
def pv1054439 : PrimeValue := ⟨1054439, pr1054439⟩
private theorem pr1054583 : PrimeCertificate 1054583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv527291]) (by decide +kernel)
def pv1054583 : PrimeValue := ⟨1054583, pr1054583⟩
private theorem pr1054853 : PrimeCertificate 1054853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv307,pv859]) (by decide +kernel)
def pv1054853 : PrimeValue := ⟨1054853, pr1054853⟩
private theorem pr1055261 : PrimeCertificate 1055261 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv19,pv2777]) (by decide +kernel)
def pv1055261 : PrimeValue := ⟨1055261, pr1055261⟩
private theorem pr1055423 : PrimeCertificate 1055423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv61,pv211]) (by decide +kernel)
def pv1055423 : PrimeValue := ⟨1055423, pr1055423⟩
private theorem pr1055429 : PrimeCertificate 1055429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv83]) (by decide +kernel)
def pv1055429 : PrimeValue := ⟨1055429, pr1055429⟩
private theorem pr1055783 : PrimeCertificate 1055783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv5801]) (by decide +kernel)
def pv1055783 : PrimeValue := ⟨1055783, pr1055783⟩
private theorem pr1055969 : PrimeCertificate 1055969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv32999]) (by decide +kernel)
def pv1055969 : PrimeValue := ⟨1055969, pr1055969⟩
private theorem pr1056053 : PrimeCertificate 1056053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv264013]) (by decide +kernel)
def pv1056053 : PrimeValue := ⟨1056053, pr1056053⟩
private theorem pr1056161 : PrimeCertificate 1056161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv23,pv41]) (by decide +kernel)
def pv1056161 : PrimeValue := ⟨1056161, pr1056161⟩
private theorem pr1056173 : PrimeCertificate 1056173 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv19,pv1069]) (by decide +kernel)
def pv1056173 : PrimeValue := ⟨1056173, pr1056173⟩
private theorem pr1056353 : PrimeCertificate 1056353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv3001]) (by decide +kernel)
def pv1056353 : PrimeValue := ⟨1056353, pr1056353⟩
private theorem pr1056521 : PrimeCertificate 1056521 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv61,pv433]) (by decide +kernel)
def pv1056521 : PrimeValue := ⟨1056521, pr1056521⟩
private theorem pr1056641 : PrimeCertificate 1056641 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv127]) (by decide +kernel)
def pv1056641 : PrimeValue := ⟨1056641, pr1056641⟩
private theorem pr1056833 : PrimeCertificate 1056833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv337]) (by decide +kernel)
def pv1056833 : PrimeValue := ⟨1056833, pr1056833⟩
private theorem pr1056911 : PrimeCertificate 1056911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv105691]) (by decide +kernel)
def pv1056911 : PrimeValue := ⟨1056911, pr1056911⟩
private theorem pr1057013 : PrimeCertificate 1057013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv24023]) (by decide +kernel)
def pv1057013 : PrimeValue := ⟨1057013, pr1057013⟩
private theorem pr1057019 : PrimeCertificate 1057019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv528509]) (by decide +kernel)
def pv1057019 : PrimeValue := ⟨1057019, pr1057019⟩
private theorem pr1057163 : PrimeCertificate 1057163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv31,pv59]) (by decide +kernel)
def pv1057163 : PrimeValue := ⟨1057163, pr1057163⟩
private theorem pr1057181 : PrimeCertificate 1057181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv52859]) (by decide +kernel)
def pv1057181 : PrimeValue := ⟨1057181, pr1057181⟩
private theorem pr1057541 : PrimeCertificate 1057541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv19,pv23]) (by decide +kernel)
def pv1057541 : PrimeValue := ⟨1057541, pr1057541⟩
private theorem pr1057613 : PrimeCertificate 1057613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv264403]) (by decide +kernel)
def pv1057613 : PrimeValue := ⟨1057613, pr1057613⟩
private theorem pr1057883 : PrimeCertificate 1057883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv41,pv97]) (by decide +kernel)
def pv1057883 : PrimeValue := ⟨1057883, pr1057883⟩
private theorem pr1058009 : PrimeCertificate 1058009 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv2699]) (by decide +kernel)
def pv1058009 : PrimeValue := ⟨1058009, pr1058009⟩
private theorem pr1058093 : PrimeCertificate 1058093 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv23,pv31,pv53]) (by decide +kernel)
def pv1058093 : PrimeValue := ⟨1058093, pr1058093⟩
private theorem pr1058153 : PrimeCertificate 1058153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv4561]) (by decide +kernel)
def pv1058153 : PrimeValue := ⟨1058153, pr1058153⟩
private theorem pr1058303 : PrimeCertificate 1058303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv10799]) (by decide +kernel)
def pv1058303 : PrimeValue := ⟨1058303, pr1058303⟩
private theorem pr1058339 : PrimeCertificate 1058339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv27851]) (by decide +kernel)
def pv1058339 : PrimeValue := ⟨1058339, pr1058339⟩
private theorem pr1058549 : PrimeCertificate 1058549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv264637]) (by decide +kernel)
def pv1058549 : PrimeValue := ⟨1058549, pr1058549⟩
private theorem pr1058723 : PrimeCertificate 1058723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv47,pv1609]) (by decide +kernel)
def pv1058723 : PrimeValue := ⟨1058723, pr1058723⟩
private theorem pr1058861 : PrimeCertificate 1058861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv4813]) (by decide +kernel)
def pv1058861 : PrimeValue := ⟨1058861, pr1058861⟩
private theorem pr1058951 : PrimeCertificate 1058951 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv21179]) (by decide +kernel)
def pv1058951 : PrimeValue := ⟨1058951, pr1058951⟩
private theorem pr1059029 : PrimeCertificate 1059029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv264757]) (by decide +kernel)
def pv1059029 : PrimeValue := ⟨1059029, pr1059029⟩
private theorem pr1059059 : PrimeCertificate 1059059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv13,pv23]) (by decide +kernel)
def pv1059059 : PrimeValue := ⟨1059059, pr1059059⟩
private theorem pr1059119 : PrimeCertificate 1059119 :=
  certifyPrime (q := pv29) (ls := [pv2,pv433,pv1223]) (by decide +kernel)
def pv1059119 : PrimeValue := ⟨1059119, pr1059119⟩
private theorem pr1059209 : PrimeCertificate 1059209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv4271]) (by decide +kernel)
def pv1059209 : PrimeValue := ⟨1059209, pr1059209⟩
private theorem pr1059251 : PrimeCertificate 1059251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv223]) (by decide +kernel)
def pv1059251 : PrimeValue := ⟨1059251, pr1059251⟩
private theorem pr1059263 : PrimeCertificate 1059263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv109,pv113]) (by decide +kernel)
def pv1059263 : PrimeValue := ⟨1059263, pr1059263⟩
private theorem pr1059293 : PrimeCertificate 1059293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1567]) (by decide +kernel)
def pv1059293 : PrimeValue := ⟨1059293, pr1059293⟩
private theorem pr1059479 : PrimeCertificate 1059479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv19,pv569]) (by decide +kernel)
def pv1059479 : PrimeValue := ⟨1059479, pr1059479⟩
private theorem pr1059599 : PrimeCertificate 1059599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv523,pv1013]) (by decide +kernel)
def pv1059599 : PrimeValue := ⟨1059599, pr1059599⟩
private theorem pr1059683 : PrimeCertificate 1059683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv53,pv769]) (by decide +kernel)
def pv1059683 : PrimeValue := ⟨1059683, pr1059683⟩
private theorem pr1059743 : PrimeCertificate 1059743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv529871]) (by decide +kernel)
def pv1059743 : PrimeValue := ⟨1059743, pr1059743⟩
private theorem pr1060151 : PrimeCertificate 1060151 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv13,pv233]) (by decide +kernel)
def pv1060151 : PrimeValue := ⟨1060151, pr1060151⟩
private theorem pr1060373 : PrimeCertificate 1060373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv265093]) (by decide +kernel)
def pv1060373 : PrimeValue := ⟨1060373, pr1060373⟩
private theorem pr1060421 : PrimeCertificate 1060421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv1433]) (by decide +kernel)
def pv1060421 : PrimeValue := ⟨1060421, pr1060421⟩
private theorem pr1060571 : PrimeCertificate 1060571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv109,pv139]) (by decide +kernel)
def pv1060571 : PrimeValue := ⟨1060571, pr1060571⟩
private theorem pr1060721 : PrimeCertificate 1060721 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13259]) (by decide +kernel)
def pv1060721 : PrimeValue := ⟨1060721, pr1060721⟩
private theorem pr1060739 : PrimeCertificate 1060739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv75767]) (by decide +kernel)
def pv1060739 : PrimeValue := ⟨1060739, pr1060739⟩
private theorem pr1060883 : PrimeCertificate 1060883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv71,pv241]) (by decide +kernel)
def pv1060883 : PrimeValue := ⟨1060883, pr1060883⟩
private theorem pr1061069 : PrimeCertificate 1061069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv43,pv199]) (by decide +kernel)
def pv1061069 : PrimeValue := ⟨1061069, pr1061069⟩
private theorem pr1061129 : PrimeCertificate 1061129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv73,pv79]) (by decide +kernel)
def pv1061129 : PrimeValue := ⟨1061129, pr1061129⟩
private theorem pr1061513 : PrimeCertificate 1061513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv132689]) (by decide +kernel)
def pv1061513 : PrimeValue := ⟨1061513, pr1061513⟩
private theorem pr1061561 : PrimeCertificate 1061561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv26539]) (by decide +kernel)
def pv1061561 : PrimeValue := ⟨1061561, pr1061561⟩
private theorem pr1061831 : PrimeCertificate 1061831 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv11,pv197]) (by decide +kernel)
def pv1061831 : PrimeValue := ⟨1061831, pr1061831⟩
private theorem pr1061969 : PrimeCertificate 1061969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv66373]) (by decide +kernel)
def pv1061969 : PrimeValue := ⟨1061969, pr1061969⟩
private theorem pr1062443 : PrimeCertificate 1062443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv73,pv383]) (by decide +kernel)
def pv1062443 : PrimeValue := ⟨1062443, pr1062443⟩
private theorem pr1062521 : PrimeCertificate 1062521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv101,pv263]) (by decide +kernel)
def pv1062521 : PrimeValue := ⟨1062521, pr1062521⟩
private theorem pr1062731 : PrimeCertificate 1062731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv106273]) (by decide +kernel)
def pv1062731 : PrimeValue := ⟨1062731, pr1062731⟩
private theorem pr1062779 : PrimeCertificate 1062779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv641,pv829]) (by decide +kernel)
def pv1062779 : PrimeValue := ⟨1062779, pr1062779⟩
private theorem pr1063019 : PrimeCertificate 1063019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv211,pv229]) (by decide +kernel)
def pv1063019 : PrimeValue := ⟨1063019, pr1063019⟩
private theorem pr1063043 : PrimeCertificate 1063043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv531521]) (by decide +kernel)
def pv1063043 : PrimeValue := ⟨1063043, pr1063043⟩
private theorem pr1063151 : PrimeCertificate 1063151 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv1933]) (by decide +kernel)
def pv1063151 : PrimeValue := ⟨1063151, pr1063151⟩
private theorem pr1063193 : PrimeCertificate 1063193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv10223]) (by decide +kernel)
def pv1063193 : PrimeValue := ⟨1063193, pr1063193⟩
private theorem pr1063319 : PrimeCertificate 1063319 :=
  certifyPrime (q := pv11) (ls := [pv2,pv73,pv7283]) (by decide +kernel)
def pv1063319 : PrimeValue := ⟨1063319, pr1063319⟩
private theorem pr1063649 : PrimeCertificate 1063649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv773]) (by decide +kernel)
def pv1063649 : PrimeValue := ⟨1063649, pr1063649⟩
private theorem pr1063721 : PrimeCertificate 1063721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv29,pv131]) (by decide +kernel)
def pv1063721 : PrimeValue := ⟨1063721, pr1063721⟩
private theorem pr1063823 : PrimeCertificate 1063823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv531911]) (by decide +kernel)
def pv1063823 : PrimeValue := ⟨1063823, pr1063823⟩
private theorem pr1063973 : PrimeCertificate 1063973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv37,pv79]) (by decide +kernel)
def pv1063973 : PrimeValue := ⟨1063973, pr1063973⟩
private theorem pr1064159 : PrimeCertificate 1064159 :=
  certifyPrime (q := pv13) (ls := [pv2,pv149,pv3571]) (by decide +kernel)
def pv1064159 : PrimeValue := ⟨1064159, pr1064159⟩
private theorem pr1064201 : PrimeCertificate 1064201 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv313]) (by decide +kernel)
def pv1064201 : PrimeValue := ⟨1064201, pr1064201⟩
private theorem pr1064243 : PrimeCertificate 1064243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv59,pv311]) (by decide +kernel)
def pv1064243 : PrimeValue := ⟨1064243, pr1064243⟩
private theorem pr1064333 : PrimeCertificate 1064333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv266083]) (by decide +kernel)
def pv1064333 : PrimeValue := ⟨1064333, pr1064333⟩
private theorem pr1064411 : PrimeCertificate 1064411 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv106441]) (by decide +kernel)
def pv1064411 : PrimeValue := ⟨1064411, pr1064411⟩
private theorem pr1064699 : PrimeCertificate 1064699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv532349]) (by decide +kernel)
def pv1064699 : PrimeValue := ⟨1064699, pr1064699⟩
private theorem pr1064753 : PrimeCertificate 1064753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv5119]) (by decide +kernel)
def pv1064753 : PrimeValue := ⟨1064753, pr1064753⟩
private theorem pr1064813 : PrimeCertificate 1064813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv2237]) (by decide +kernel)
def pv1064813 : PrimeValue := ⟨1064813, pr1064813⟩
private theorem pr1064933 : PrimeCertificate 1064933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv24203]) (by decide +kernel)
def pv1064933 : PrimeValue := ⟨1064933, pr1064933⟩
private theorem pr1064951 : PrimeCertificate 1064951 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv19,pv59]) (by decide +kernel)
def pv1064951 : PrimeValue := ⟨1064951, pr1064951⟩
private theorem pr1065173 : PrimeCertificate 1065173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv266293]) (by decide +kernel)
def pv1065173 : PrimeValue := ⟨1065173, pr1065173⟩
private theorem pr1065269 : PrimeCertificate 1065269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv11579]) (by decide +kernel)
def pv1065269 : PrimeValue := ⟨1065269, pr1065269⟩
private theorem pr1065479 : PrimeCertificate 1065479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv532739]) (by decide +kernel)
def pv1065479 : PrimeValue := ⟨1065479, pr1065479⟩
private theorem pr1065899 : PrimeCertificate 1065899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv532949]) (by decide +kernel)
def pv1065899 : PrimeValue := ⟨1065899, pr1065899⟩
private theorem pr1066001 : PrimeCertificate 1066001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv41]) (by decide +kernel)
def pv1066001 : PrimeValue := ⟨1066001, pr1066001⟩
private theorem pr1066031 : PrimeCertificate 1066031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv97,pv157]) (by decide +kernel)
def pv1066031 : PrimeValue := ⟨1066031, pr1066031⟩
private theorem pr1066133 : PrimeCertificate 1066133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193,pv1381]) (by decide +kernel)
def pv1066133 : PrimeValue := ⟨1066133, pr1066133⟩
private theorem pr1066139 : PrimeCertificate 1066139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv31357]) (by decide +kernel)
def pv1066139 : PrimeValue := ⟨1066139, pr1066139⟩
private theorem pr1066283 : PrimeCertificate 1066283 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv76163]) (by decide +kernel)
def pv1066283 : PrimeValue := ⟨1066283, pr1066283⟩
private theorem pr1066319 : PrimeCertificate 1066319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv19,pv2551]) (by decide +kernel)
def pv1066319 : PrimeValue := ⟨1066319, pr1066319⟩
private theorem pr1066379 : PrimeCertificate 1066379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv533189]) (by decide +kernel)
def pv1066379 : PrimeValue := ⟨1066379, pr1066379⟩
private theorem pr1066511 : PrimeCertificate 1066511 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv23,pv4637]) (by decide +kernel)
def pv1066511 : PrimeValue := ⟨1066511, pr1066511⟩
private theorem pr1067009 : PrimeCertificate 1067009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv521]) (by decide +kernel)
def pv1067009 : PrimeValue := ⟨1067009, pr1067009⟩
private theorem pr1067351 : PrimeCertificate 1067351 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv21347]) (by decide +kernel)
def pv1067351 : PrimeValue := ⟨1067351, pr1067351⟩
private theorem pr1067471 : PrimeCertificate 1067471 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv106747]) (by decide +kernel)
def pv1067471 : PrimeValue := ⟨1067471, pr1067471⟩
private theorem pr1067639 : PrimeCertificate 1067639 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv13,pv3733]) (by decide +kernel)
def pv1067639 : PrimeValue := ⟨1067639, pr1067639⟩
private theorem pr1067831 : PrimeCertificate 1067831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv106783]) (by decide +kernel)
def pv1067831 : PrimeValue := ⟨1067831, pr1067831⟩
private theorem pr1067849 : PrimeCertificate 1067849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv133481]) (by decide +kernel)
def pv1067849 : PrimeValue := ⟨1067849, pr1067849⟩
private theorem pr1068191 : PrimeCertificate 1068191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv37,pv2887]) (by decide +kernel)
def pv1068191 : PrimeValue := ⟨1068191, pr1068191⟩
private theorem pr1068491 : PrimeCertificate 1068491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv1811]) (by decide +kernel)
def pv1068491 : PrimeValue := ⟨1068491, pr1068491⟩
private theorem pr1068629 : PrimeCertificate 1068629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv149,pv163]) (by decide +kernel)
def pv1068629 : PrimeValue := ⟨1068629, pr1068629⟩
private theorem pr1068989 : PrimeCertificate 1068989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179,pv1493]) (by decide +kernel)
def pv1068989 : PrimeValue := ⟨1068989, pr1068989⟩
private theorem pr1069193 : PrimeCertificate 1069193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv133649]) (by decide +kernel)
def pv1069193 : PrimeValue := ⟨1069193, pr1069193⟩
private theorem pr1069199 : PrimeCertificate 1069199 :=
  certifyPrime (q := pv29) (ls := [pv2,pv13,pv17,pv41,pv59]) (by decide +kernel)
def pv1069199 : PrimeValue := ⟨1069199, pr1069199⟩
private theorem pr1069499 : PrimeCertificate 1069499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv661,pv809]) (by decide +kernel)
def pv1069499 : PrimeValue := ⟨1069499, pr1069499⟩
private theorem pr1069553 : PrimeCertificate 1069553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv59,pv103]) (by decide +kernel)
def pv1069553 : PrimeValue := ⟨1069553, pr1069553⟩
private theorem pr1069571 : PrimeCertificate 1069571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv106957]) (by decide +kernel)
def pv1069571 : PrimeValue := ⟨1069571, pr1069571⟩
private theorem pr1069583 : PrimeCertificate 1069583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv12437]) (by decide +kernel)
def pv1069583 : PrimeValue := ⟨1069583, pr1069583⟩
private theorem pr1069973 : PrimeCertificate 1069973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv267493]) (by decide +kernel)
def pv1069973 : PrimeValue := ⟨1069973, pr1069973⟩
private theorem pr1069979 : PrimeCertificate 1069979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv5879]) (by decide +kernel)
def pv1069979 : PrimeValue := ⟨1069979, pr1069979⟩
private theorem pr1070081 : PrimeCertificate 1070081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv19]) (by decide +kernel)
def pv1070081 : PrimeValue := ⟨1070081, pr1070081⟩
private theorem pr1070411 : PrimeCertificate 1070411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv37,pv263]) (by decide +kernel)
def pv1070411 : PrimeValue := ⟨1070411, pr1070411⟩
private theorem pr1070423 : PrimeCertificate 1070423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv19,pv1657]) (by decide +kernel)
def pv1070423 : PrimeValue := ⟨1070423, pr1070423⟩
private theorem pr1070453 : PrimeCertificate 1070453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv267613]) (by decide +kernel)
def pv1070453 : PrimeValue := ⟨1070453, pr1070453⟩
private theorem pr1070561 : PrimeCertificate 1070561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6691]) (by decide +kernel)
def pv1070561 : PrimeValue := ⟨1070561, pr1070561⟩
private theorem pr1070579 : PrimeCertificate 1070579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139,pv3851]) (by decide +kernel)
def pv1070579 : PrimeValue := ⟨1070579, pr1070579⟩
private theorem pr1070843 : PrimeCertificate 1070843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv347,pv1543]) (by decide +kernel)
def pv1070843 : PrimeValue := ⟨1070843, pr1070843⟩
private theorem pr1070939 : PrimeCertificate 1070939 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv48679]) (by decide +kernel)
def pv1070939 : PrimeValue := ⟨1070939, pr1070939⟩
private theorem pr1071149 : PrimeCertificate 1071149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv20599]) (by decide +kernel)
def pv1071149 : PrimeValue := ⟨1071149, pr1071149⟩
private theorem pr1071359 : PrimeCertificate 1071359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv535679]) (by decide +kernel)
def pv1071359 : PrimeValue := ⟨1071359, pr1071359⟩
private theorem pr1071659 : PrimeCertificate 1071659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv41,pv1867]) (by decide +kernel)
def pv1071659 : PrimeValue := ⟨1071659, pr1071659⟩
private theorem pr1071743 : PrimeCertificate 1071743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv37,pv2069]) (by decide +kernel)
def pv1071743 : PrimeValue := ⟨1071743, pr1071743⟩
private theorem pr1072199 : PrimeCertificate 1072199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv536099]) (by decide +kernel)
def pv1072199 : PrimeValue := ⟨1072199, pr1072199⟩
private theorem pr1072229 : PrimeCertificate 1072229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv8647]) (by decide +kernel)
def pv1072229 : PrimeValue := ⟨1072229, pr1072229⟩
private theorem pr1072433 : PrimeCertificate 1072433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97,pv691]) (by decide +kernel)
def pv1072433 : PrimeValue := ⟨1072433, pr1072433⟩
private theorem pr1072919 : PrimeCertificate 1072919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv6967]) (by decide +kernel)
def pv1072919 : PrimeValue := ⟨1072919, pr1072919⟩
private theorem pr1073069 : PrimeCertificate 1073069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv268267]) (by decide +kernel)
def pv1073069 : PrimeValue := ⟨1073069, pr1073069⟩
private theorem pr1073141 : PrimeCertificate 1073141 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv53657]) (by decide +kernel)
def pv1073141 : PrimeValue := ⟨1073141, pr1073141⟩
private theorem pr1073153 : PrimeCertificate 1073153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv131]) (by decide +kernel)
def pv1073153 : PrimeValue := ⟨1073153, pr1073153⟩
private theorem pr1073183 : PrimeCertificate 1073183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv48781]) (by decide +kernel)
def pv1073183 : PrimeValue := ⟨1073183, pr1073183⟩
private theorem pr1073381 : PrimeCertificate 1073381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv17,pv41]) (by decide +kernel)
def pv1073381 : PrimeValue := ⟨1073381, pr1073381⟩
private theorem pr1073393 : PrimeCertificate 1073393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv919]) (by decide +kernel)
def pv1073393 : PrimeValue := ⟨1073393, pr1073393⟩
private theorem pr1073921 : PrimeCertificate 1073921 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv839]) (by decide +kernel)
def pv1073921 : PrimeValue := ⟨1073921, pr1073921⟩
private theorem pr1073951 : PrimeCertificate 1073951 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv47,pv457]) (by decide +kernel)
def pv1073951 : PrimeValue := ⟨1073951, pr1073951⟩
private theorem pr1074113 : PrimeCertificate 1074113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1291]) (by decide +kernel)
def pv1074113 : PrimeValue := ⟨1074113, pr1074113⟩
private theorem pr1074299 : PrimeCertificate 1074299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv19,pv1663]) (by decide +kernel)
def pv1074299 : PrimeValue := ⟨1074299, pr1074299⟩
private theorem pr1074329 : PrimeCertificate 1074329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv134291]) (by decide +kernel)
def pv1074329 : PrimeValue := ⟨1074329, pr1074329⟩
private theorem pr1074473 : PrimeCertificate 1074473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv2741]) (by decide +kernel)
def pv1074473 : PrimeValue := ⟨1074473, pr1074473⟩
private theorem pr1074533 : PrimeCertificate 1074533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv353,pv761]) (by decide +kernel)
def pv1074533 : PrimeValue := ⟨1074533, pr1074533⟩
private theorem pr1074641 : PrimeCertificate 1074641 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv19,pv101]) (by decide +kernel)
def pv1074641 : PrimeValue := ⟨1074641, pr1074641⟩
private theorem pr1074701 : PrimeCertificate 1074701 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv977]) (by decide +kernel)
def pv1074701 : PrimeValue := ⟨1074701, pr1074701⟩
private theorem pr1074851 : PrimeCertificate 1074851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv37,pv83]) (by decide +kernel)
def pv1074851 : PrimeValue := ⟨1074851, pr1074851⟩
private theorem pr1074929 : PrimeCertificate 1074929 :=
  certifyPrime (q := pv13) (ls := [pv2,pv23,pv127]) (by decide +kernel)
def pv1074929 : PrimeValue := ⟨1074929, pr1074929⟩
private theorem pr1075103 : PrimeCertificate 1075103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv41,pv1873]) (by decide +kernel)
def pv1075103 : PrimeValue := ⟨1075103, pr1075103⟩
private theorem pr1075391 : PrimeCertificate 1075391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv31,pv3469]) (by decide +kernel)
def pv1075391 : PrimeValue := ⟨1075391, pr1075391⟩
private theorem pr1075433 : PrimeCertificate 1075433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv179,pv751]) (by decide +kernel)
def pv1075433 : PrimeValue := ⟨1075433, pr1075433⟩
private theorem pr1075601 : PrimeCertificate 1075601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2689]) (by decide +kernel)
def pv1075601 : PrimeValue := ⟨1075601, pr1075601⟩
private theorem pr1076039 : PrimeCertificate 1076039 :=
  certifyPrime (q := pv17) (ls := [pv2,pv538019]) (by decide +kernel)
def pv1076039 : PrimeValue := ⟨1076039, pr1076039⟩
private theorem pr1076051 : PrimeCertificate 1076051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv21521]) (by decide +kernel)
def pv1076051 : PrimeValue := ⟨1076051, pr1076051⟩
private theorem pr1076063 : PrimeCertificate 1076063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv41387]) (by decide +kernel)
def pv1076063 : PrimeValue := ⟨1076063, pr1076063⟩
private theorem pr1076123 : PrimeCertificate 1076123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv28319]) (by decide +kernel)
def pv1076123 : PrimeValue := ⟨1076123, pr1076123⟩
private theorem pr1076171 : PrimeCertificate 1076171 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv23,pv4679]) (by decide +kernel)
def pv1076171 : PrimeValue := ⟨1076171, pr1076171⟩
private theorem pr1076213 : PrimeCertificate 1076213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv2381]) (by decide +kernel)
def pv1076213 : PrimeValue := ⟨1076213, pr1076213⟩
private theorem pr1076279 : PrimeCertificate 1076279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv59,pv1303]) (by decide +kernel)
def pv1076279 : PrimeValue := ⟨1076279, pr1076279⟩
private theorem pr1076303 : PrimeCertificate 1076303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv538151]) (by decide +kernel)
def pv1076303 : PrimeValue := ⟨1076303, pr1076303⟩
private theorem pr1076753 : PrimeCertificate 1076753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv173,pv389]) (by decide +kernel)
def pv1076753 : PrimeValue := ⟨1076753, pr1076753⟩
private theorem pr1077353 : PrimeCertificate 1077353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv134669]) (by decide +kernel)
def pv1077353 : PrimeValue := ⟨1077353, pr1077353⟩
private theorem pr1077371 : PrimeCertificate 1077371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv15391]) (by decide +kernel)
def pv1077371 : PrimeValue := ⟨1077371, pr1077371⟩
private theorem pr1077449 : PrimeCertificate 1077449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv134681]) (by decide +kernel)
def pv1077449 : PrimeValue := ⟨1077449, pr1077449⟩
private theorem pr1077533 : PrimeCertificate 1077533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv269383]) (by decide +kernel)
def pv1077533 : PrimeValue := ⟨1077533, pr1077533⟩
private theorem pr1077539 : PrimeCertificate 1077539 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv11,pv6997]) (by decide +kernel)
def pv1077539 : PrimeValue := ⟨1077539, pr1077539⟩
private theorem pr1077743 : PrimeCertificate 1077743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv538871]) (by decide +kernel)
def pv1077743 : PrimeValue := ⟨1077743, pr1077743⟩
private theorem pr1078019 : PrimeCertificate 1078019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv539009]) (by decide +kernel)
def pv1078019 : PrimeValue := ⟨1078019, pr1078019⟩
private theorem pr1078043 : PrimeCertificate 1078043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv77003]) (by decide +kernel)
def pv1078043 : PrimeValue := ⟨1078043, pr1078043⟩
private theorem pr1078151 : PrimeCertificate 1078151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv21563]) (by decide +kernel)
def pv1078151 : PrimeValue := ⟨1078151, pr1078151⟩
private theorem pr1078169 : PrimeCertificate 1078169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv1481]) (by decide +kernel)
def pv1078169 : PrimeValue := ⟨1078169, pr1078169⟩
private theorem pr1078559 : PrimeCertificate 1078559 :=
  certifyPrime (q := pv11) (ls := [pv2,pv13,pv3191]) (by decide +kernel)
def pv1078559 : PrimeValue := ⟨1078559, pr1078559⟩
private theorem pr1078919 : PrimeCertificate 1078919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv139,pv3881]) (by decide +kernel)
def pv1078919 : PrimeValue := ⟨1078919, pr1078919⟩
private theorem pr1079009 : PrimeCertificate 1079009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv4817]) (by decide +kernel)
def pv1079009 : PrimeValue := ⟨1079009, pr1079009⟩
private theorem pr1079069 : PrimeCertificate 1079069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv37,pv317]) (by decide +kernel)
def pv1079069 : PrimeValue := ⟨1079069, pr1079069⟩
private theorem pr1079153 : PrimeCertificate 1079153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67447]) (by decide +kernel)
def pv1079153 : PrimeValue := ⟨1079153, pr1079153⟩
private theorem pr1079213 : PrimeCertificate 1079213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv4423]) (by decide +kernel)
def pv1079213 : PrimeValue := ⟨1079213, pr1079213⟩
private theorem pr1079339 : PrimeCertificate 1079339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv41513]) (by decide +kernel)
def pv1079339 : PrimeValue := ⟨1079339, pr1079339⟩
private theorem pr1079531 : PrimeCertificate 1079531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv2633]) (by decide +kernel)
def pv1079531 : PrimeValue := ⟨1079531, pr1079531⟩
private theorem pr1079651 : PrimeCertificate 1079651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv151]) (by decide +kernel)
def pv1079651 : PrimeValue := ⟨1079651, pr1079651⟩
private theorem pr1079681 : PrimeCertificate 1079681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv241]) (by decide +kernel)
def pv1079681 : PrimeValue := ⟨1079681, pr1079681⟩
private theorem pr1080263 : PrimeCertificate 1080263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv127,pv4253]) (by decide +kernel)
def pv1080263 : PrimeValue := ⟨1080263, pr1080263⟩
private theorem pr1080281 : PrimeCertificate 1080281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv113,pv239]) (by decide +kernel)
def pv1080281 : PrimeValue := ⟨1080281, pr1080281⟩
private theorem pr1080713 : PrimeCertificate 1080713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv135089]) (by decide +kernel)
def pv1080713 : PrimeValue := ⟨1080713, pr1080713⟩
private theorem pr1080941 : PrimeCertificate 1080941 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv1103]) (by decide +kernel)
def pv1080941 : PrimeValue := ⟨1080941, pr1080941⟩
private theorem pr1080983 : PrimeCertificate 1080983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv77213]) (by decide +kernel)
def pv1080983 : PrimeValue := ⟨1080983, pr1080983⟩
private theorem pr1081331 : PrimeCertificate 1081331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv71,pv1523]) (by decide +kernel)
def pv1081331 : PrimeValue := ⟨1081331, pr1081331⟩
private theorem pr1081403 : PrimeCertificate 1081403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv77243]) (by decide +kernel)
def pv1081403 : PrimeValue := ⟨1081403, pr1081403⟩
private theorem pr1081583 : PrimeCertificate 1081583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv479,pv1129]) (by decide +kernel)
def pv1081583 : PrimeValue := ⟨1081583, pr1081583⟩
private theorem pr1081631 : PrimeCertificate 1081631 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv9833]) (by decide +kernel)
def pv1081631 : PrimeValue := ⟨1081631, pr1081631⟩
private theorem pr1081721 : PrimeCertificate 1081721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv27043]) (by decide +kernel)
def pv1081721 : PrimeValue := ⟨1081721, pr1081721⟩
private theorem pr1081733 : PrimeCertificate 1081733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv7309]) (by decide +kernel)
def pv1081733 : PrimeValue := ⟨1081733, pr1081733⟩
private theorem pr1081763 : PrimeCertificate 1081763 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv49171]) (by decide +kernel)
def pv1081763 : PrimeValue := ⟨1081763, pr1081763⟩
private theorem pr1082153 : PrimeCertificate 1082153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv73,pv109]) (by decide +kernel)
def pv1082153 : PrimeValue := ⟨1082153, pr1082153⟩
private theorem pr1082369 : PrimeCertificate 1082369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv151]) (by decide +kernel)
def pv1082369 : PrimeValue := ⟨1082369, pr1082369⟩
private theorem pr1082429 : PrimeCertificate 1082429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv461,pv587]) (by decide +kernel)
def pv1082429 : PrimeValue := ⟨1082429, pr1082429⟩
private theorem pr1082531 : PrimeCertificate 1082531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv103,pv1051]) (by decide +kernel)
def pv1082531 : PrimeValue := ⟨1082531, pr1082531⟩
private theorem pr1082573 : PrimeCertificate 1082573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv241,pv1123]) (by decide +kernel)
def pv1082573 : PrimeValue := ⟨1082573, pr1082573⟩
private theorem pr1082579 : PrimeCertificate 1082579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv53,pv1459]) (by decide +kernel)
def pv1082579 : PrimeValue := ⟨1082579, pr1082579⟩
private theorem pr1083059 : PrimeCertificate 1083059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv541529]) (by decide +kernel)
def pv1083059 : PrimeValue := ⟨1083059, pr1083059⟩
private theorem pr1083083 : PrimeCertificate 1083083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv13,pv541]) (by decide +kernel)
def pv1083083 : PrimeValue := ⟨1083083, pr1083083⟩
private theorem pr1083473 : PrimeCertificate 1083473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv5209]) (by decide +kernel)
def pv1083473 : PrimeValue := ⟨1083473, pr1083473⟩
private theorem pr1083851 : PrimeCertificate 1083851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv409]) (by decide +kernel)
def pv1083851 : PrimeValue := ⟨1083851, pr1083851⟩
private theorem pr1083941 : PrimeCertificate 1083941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv379]) (by decide +kernel)
def pv1083941 : PrimeValue := ⟨1083941, pr1083941⟩
private theorem pr1084403 : PrimeCertificate 1084403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4481]) (by decide +kernel)
def pv1084403 : PrimeValue := ⟨1084403, pr1084403⟩
private theorem pr1084493 : PrimeCertificate 1084493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv1979]) (by decide +kernel)
def pv1084493 : PrimeValue := ⟨1084493, pr1084493⟩
private theorem pr1084613 : PrimeCertificate 1084613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv263,pv1031]) (by decide +kernel)
def pv1084613 : PrimeValue := ⟨1084613, pr1084613⟩
private theorem pr1085141 : PrimeCertificate 1085141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv23,pv337]) (by decide +kernel)
def pv1085141 : PrimeValue := ⟨1085141, pr1085141⟩
private theorem pr1085153 : PrimeCertificate 1085153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv33911]) (by decide +kernel)
def pv1085153 : PrimeValue := ⟨1085153, pr1085153⟩
private theorem pr1085351 : PrimeCertificate 1085351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv443]) (by decide +kernel)
def pv1085351 : PrimeValue := ⟨1085351, pr1085351⟩
private theorem pr1085459 : PrimeCertificate 1085459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv49339]) (by decide +kernel)
def pv1085459 : PrimeValue := ⟨1085459, pr1085459⟩
private theorem pr1085813 : PrimeCertificate 1085813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv19,pv157]) (by decide +kernel)
def pv1085813 : PrimeValue := ⟨1085813, pr1085813⟩
private theorem pr1086089 : PrimeCertificate 1086089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv349,pv389]) (by decide +kernel)
def pv1086089 : PrimeValue := ⟨1086089, pr1086089⟩
private theorem pr1086119 : PrimeCertificate 1086119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv49369]) (by decide +kernel)
def pv1086119 : PrimeValue := ⟨1086119, pr1086119⟩
private theorem pr1086161 : PrimeCertificate 1086161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13577]) (by decide +kernel)
def pv1086161 : PrimeValue := ⟨1086161, pr1086161⟩
private theorem pr1086191 : PrimeCertificate 1086191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv59,pv263]) (by decide +kernel)
def pv1086191 : PrimeValue := ⟨1086191, pr1086191⟩
private theorem pr1086413 : PrimeCertificate 1086413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv271603]) (by decide +kernel)
def pv1086413 : PrimeValue := ⟨1086413, pr1086413⟩
private theorem pr1086443 : PrimeCertificate 1086443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv71,pv1093]) (by decide +kernel)
def pv1086443 : PrimeValue := ⟨1086443, pr1086443⟩
private theorem pr1086749 : PrimeCertificate 1086749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv20899]) (by decide +kernel)
def pv1086749 : PrimeValue := ⟨1086749, pr1086749⟩
private theorem pr1086863 : PrimeCertificate 1086863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv29,pv2677]) (by decide +kernel)
def pv1086863 : PrimeValue := ⟨1086863, pr1086863⟩
private theorem pr1086881 : PrimeCertificate 1086881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6793]) (by decide +kernel)
def pv1086881 : PrimeValue := ⟨1086881, pr1086881⟩
private theorem pr1087241 : PrimeCertificate 1087241 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv11,pv353]) (by decide +kernel)
def pv1087241 : PrimeValue := ⟨1087241, pr1087241⟩
private theorem pr1087301 : PrimeCertificate 1087301 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv83,pv131]) (by decide +kernel)
def pv1087301 : PrimeValue := ⟨1087301, pr1087301⟩
private theorem pr1087349 : PrimeCertificate 1087349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv53,pv223]) (by decide +kernel)
def pv1087349 : PrimeValue := ⟨1087349, pr1087349⟩
private theorem pr1087631 : PrimeCertificate 1087631 :=
  certifyPrime (q := pv41) (ls := [pv2,pv5,pv61,pv1783]) (by decide +kernel)
def pv1087631 : PrimeValue := ⟨1087631, pr1087631⟩
private theorem pr1087799 : PrimeCertificate 1087799 :=
  certifyPrime (q := pv11) (ls := [pv2,pv83,pv6553]) (by decide +kernel)
def pv1087799 : PrimeValue := ⟨1087799, pr1087799⟩
private theorem pr1087829 : PrimeCertificate 1087829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv38851]) (by decide +kernel)
def pv1087829 : PrimeValue := ⟨1087829, pr1087829⟩
private theorem pr1087841 : PrimeCertificate 1087841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv523]) (by decide +kernel)
def pv1087841 : PrimeValue := ⟨1087841, pr1087841⟩
private theorem pr1087973 : PrimeCertificate 1087973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv2693]) (by decide +kernel)
def pv1087973 : PrimeValue := ⟨1087973, pr1087973⟩
private theorem pr1088273 : PrimeCertificate 1088273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv4001]) (by decide +kernel)
def pv1088273 : PrimeValue := ⟨1088273, pr1088273⟩
private theorem pr1088309 : PrimeCertificate 1088309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv20929]) (by decide +kernel)
def pv1088309 : PrimeValue := ⟨1088309, pr1088309⟩
private theorem pr1088621 : PrimeCertificate 1088621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv53,pv79]) (by decide +kernel)
def pv1088621 : PrimeValue := ⟨1088621, pr1088621⟩
private theorem pr1088723 : PrimeCertificate 1088723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv7457]) (by decide +kernel)
def pv1088723 : PrimeValue := ⟨1088723, pr1088723⟩
private theorem pr1088753 : PrimeCertificate 1088753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv9721]) (by decide +kernel)
def pv1088753 : PrimeValue := ⟨1088753, pr1088753⟩
private theorem pr1088903 : PrimeCertificate 1088903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv544451]) (by decide +kernel)
def pv1088903 : PrimeValue := ⟨1088903, pr1088903⟩
private theorem pr1089191 : PrimeCertificate 1089191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv17,pv43,pv149]) (by decide +kernel)
def pv1089191 : PrimeValue := ⟨1089191, pr1089191⟩
private theorem pr1089239 : PrimeCertificate 1089239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv733,pv743]) (by decide +kernel)
def pv1089239 : PrimeValue := ⟨1089239, pr1089239⟩
private theorem pr1089299 : PrimeCertificate 1089299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv2683]) (by decide +kernel)
def pv1089299 : PrimeValue := ⟨1089299, pr1089299⟩
private theorem pr1089359 : PrimeCertificate 1089359 :=
  certifyPrime (q := pv13) (ls := [pv2,pv353,pv1543]) (by decide +kernel)
def pv1089359 : PrimeValue := ⟨1089359, pr1089359⟩
private theorem pr1089503 : PrimeCertificate 1089503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv14723]) (by decide +kernel)
def pv1089503 : PrimeValue := ⟨1089503, pr1089503⟩
private theorem pr1089611 : PrimeCertificate 1089611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv108961]) (by decide +kernel)
def pv1089611 : PrimeValue := ⟨1089611, pr1089611⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
