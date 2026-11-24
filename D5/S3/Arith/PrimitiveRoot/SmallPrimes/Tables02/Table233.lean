/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table233
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table233.pv1156387
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1156387 : Nat.Prime 1156387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv2503]) (by decide +kernel)
def pv1156387 : PrimeValue := ⟨1156387, pr1156387⟩
private theorem pr1156567 : Nat.Prime 1156567 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53,pv3637]) (by decide +kernel)
def pv1156567 : PrimeValue := ⟨1156567, pr1156567⟩
private theorem pr1156807 : Nat.Prime 1156807 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv9181]) (by decide +kernel)
def pv1156807 : PrimeValue := ⟨1156807, pr1156807⟩
private theorem pr1157017 : Nat.Prime 1157017 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv71,pv97]) (by decide +kernel)
def pv1157017 : PrimeValue := ⟨1157017, pr1157017⟩
private theorem pr1157293 : Nat.Prime 1157293 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv31,pv61]) (by decide +kernel)
def pv1157293 : PrimeValue := ⟨1157293, pr1157293⟩
private theorem pr1157503 : Nat.Prime 1157503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv192917]) (by decide +kernel)
def pv1157503 : PrimeValue := ⟨1157503, pr1157503⟩
private theorem pr1157773 : Nat.Prime 1157773 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv11,pv179]) (by decide +kernel)
def pv1157773 : PrimeValue := ⟨1157773, pr1157773⟩
private theorem pr1157869 : Nat.Prime 1157869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv151]) (by decide +kernel)
def pv1157869 : PrimeValue := ⟨1157869, pr1157869⟩
private theorem pr1157899 : Nat.Prime 1157899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv1451]) (by decide +kernel)
def pv1157899 : PrimeValue := ⟨1157899, pr1157899⟩
private theorem pr1157953 : Nat.Prime 1157953 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv163]) (by decide +kernel)
def pv1157953 : PrimeValue := ⟨1157953, pr1157953⟩
private theorem pr1158217 : Nat.Prime 1158217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv48259]) (by decide +kernel)
def pv1158217 : PrimeValue := ⟨1158217, pr1158217⟩
private theorem pr1158247 : Nat.Prime 1158247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv89,pv241]) (by decide +kernel)
def pv1158247 : PrimeValue := ⟨1158247, pr1158247⟩
private theorem pr1158427 : Nat.Prime 1158427 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv139,pv463]) (by decide +kernel)
def pv1158427 : PrimeValue := ⟨1158427, pr1158427⟩
private theorem pr1158523 : Nat.Prime 1158523 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv293,pv659]) (by decide +kernel)
def pv1158523 : PrimeValue := ⟨1158523, pr1158523⟩
private theorem pr1158529 : Nat.Prime 1158529 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv431]) (by decide +kernel)
def pv1158529 : PrimeValue := ⟨1158529, pr1158529⟩
private theorem pr1158607 : Nat.Prime 1158607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv191,pv337]) (by decide +kernel)
def pv1158607 : PrimeValue := ⟨1158607, pr1158607⟩
private theorem pr1159153 : Nat.Prime 1159153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv31,pv41]) (by decide +kernel)
def pv1159153 : PrimeValue := ⟨1159153, pr1159153⟩
private theorem pr1159393 : Nat.Prime 1159393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv929]) (by decide +kernel)
def pv1159393 : PrimeValue := ⟨1159393, pr1159393⟩
private theorem pr1159633 : Nat.Prime 1159633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv8053]) (by decide +kernel)
def pv1159633 : PrimeValue := ⟨1159633, pr1159633⟩
private theorem pr1159843 : Nat.Prime 1159843 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv83,pv137]) (by decide +kernel)
def pv1159843 : PrimeValue := ⟨1159843, pr1159843⟩
private theorem pr1160179 : Nat.Prime 1160179 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19,pv10177]) (by decide +kernel)
def pv1160179 : PrimeValue := ⟨1160179, pr1160179⟩
private theorem pr1160359 : Nat.Prime 1160359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv193393]) (by decide +kernel)
def pv1160359 : PrimeValue := ⟨1160359, pr1160359⟩
private theorem pr1160443 : Nat.Prime 1160443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv2803]) (by decide +kernel)
def pv1160443 : PrimeValue := ⟨1160443, pr1160443⟩
private theorem pr1160503 : Nat.Prime 1160503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv27631]) (by decide +kernel)
def pv1160503 : PrimeValue := ⟨1160503, pr1160503⟩
private theorem pr1160749 : Nat.Prime 1160749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1697]) (by decide +kernel)
def pv1160749 : PrimeValue := ⟨1160749, pr1160749⟩
private theorem pr1160839 : Nat.Prime 1160839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv37,pv83]) (by decide +kernel)
def pv1160839 : PrimeValue := ⟨1160839, pr1160839⟩
private theorem pr1160977 : Nat.Prime 1160977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv67]) (by decide +kernel)
def pv1160977 : PrimeValue := ⟨1160977, pr1160977⟩
private theorem pr1161037 : Nat.Prime 1161037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv32251]) (by decide +kernel)
def pv1161037 : PrimeValue := ⟨1161037, pr1161037⟩
private theorem pr1161169 : Nat.Prime 1161169 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv17,pv1423]) (by decide +kernel)
def pv1161169 : PrimeValue := ⟨1161169, pr1161169⟩
private theorem pr1161757 : Nat.Prime 1161757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv347]) (by decide +kernel)
def pv1161757 : PrimeValue := ⟨1161757, pr1161757⟩
private theorem pr1161829 : Nat.Prime 1161829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv547]) (by decide +kernel)
def pv1161829 : PrimeValue := ⟨1161829, pr1161829⟩
private theorem pr1161877 : Nat.Prime 1161877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv96823]) (by decide +kernel)
def pv1161877 : PrimeValue := ⟨1161877, pr1161877⟩
private theorem pr1162009 : Nat.Prime 1162009 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv16139]) (by decide +kernel)
def pv1162009 : PrimeValue := ⟨1162009, pr1162009⟩
private theorem pr1162093 : Nat.Prime 1162093 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv113,pv857]) (by decide +kernel)
def pv1162093 : PrimeValue := ⟨1162093, pr1162093⟩
private theorem pr1162297 : Nat.Prime 1162297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5381]) (by decide +kernel)
def pv1162297 : PrimeValue := ⟨1162297, pr1162297⟩
private theorem pr1162423 : Nat.Prime 1162423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv64579]) (by decide +kernel)
def pv1162423 : PrimeValue := ⟨1162423, pr1162423⟩
private theorem pr1162507 : Nat.Prime 1162507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv193751]) (by decide +kernel)
def pv1162507 : PrimeValue := ⟨1162507, pr1162507⟩
private theorem pr1162597 : Nat.Prime 1162597 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv41,pv139]) (by decide +kernel)
def pv1162597 : PrimeValue := ⟨1162597, pr1162597⟩
private theorem pr1162669 : Nat.Prime 1162669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv29,pv257]) (by decide +kernel)
def pv1162669 : PrimeValue := ⟨1162669, pr1162669⟩
private theorem pr1162687 : Nat.Prime 1162687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv31,pv47]) (by decide +kernel)
def pv1162687 : PrimeValue := ⟨1162687, pr1162687⟩
private theorem pr1162867 : Nat.Prime 1162867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv193811]) (by decide +kernel)
def pv1162867 : PrimeValue := ⟨1162867, pr1162867⟩
private theorem pr1162927 : Nat.Prime 1162927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv53]) (by decide +kernel)
def pv1162927 : PrimeValue := ⟨1162927, pr1162927⟩
private theorem pr1163077 : Nat.Prime 1163077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103,pv941]) (by decide +kernel)
def pv1163077 : PrimeValue := ⟨1163077, pr1163077⟩
private theorem pr1163233 : Nat.Prime 1163233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv577]) (by decide +kernel)
def pv1163233 : PrimeValue := ⟨1163233, pr1163233⟩
private theorem pr1163353 : Nat.Prime 1163353 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv48473]) (by decide +kernel)
def pv1163353 : PrimeValue := ⟨1163353, pr1163353⟩
private theorem pr1163557 : Nat.Prime 1163557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv32321]) (by decide +kernel)
def pv1163557 : PrimeValue := ⟨1163557, pr1163557⟩
private theorem pr1163947 : Nat.Prime 1163947 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv37,pv107]) (by decide +kernel)
def pv1163947 : PrimeValue := ⟨1163947, pr1163947⟩
private theorem pr1163989 : Nat.Prime 1163989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv149]) (by decide +kernel)
def pv1163989 : PrimeValue := ⟨1163989, pr1163989⟩
private theorem pr1164043 : Nat.Prime 1164043 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv5879]) (by decide +kernel)
def pv1164043 : PrimeValue := ⟨1164043, pr1164043⟩
private theorem pr1164199 : Nat.Prime 1164199 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv53,pv523]) (by decide +kernel)
def pv1164199 : PrimeValue := ⟨1164199, pr1164199⟩
private theorem pr1164799 : Nat.Prime 1164799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv163,pv397]) (by decide +kernel)
def pv1164799 : PrimeValue := ⟨1164799, pr1164799⟩
private theorem pr1165069 : Nat.Prime 1165069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv32363]) (by decide +kernel)
def pv1165069 : PrimeValue := ⟨1165069, pr1165069⟩
private theorem pr1165147 : Nat.Prime 1165147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv11423]) (by decide +kernel)
def pv1165147 : PrimeValue := ⟨1165147, pr1165147⟩
private theorem pr1165273 : Nat.Prime 1165273 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv23,pv2111]) (by decide +kernel)
def pv1165273 : PrimeValue := ⟨1165273, pr1165273⟩
private theorem pr1165279 : Nat.Prime 1165279 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv29,pv37,pv181]) (by decide +kernel)
def pv1165279 : PrimeValue := ⟨1165279, pr1165279⟩
private theorem pr1165357 : Nat.Prime 1165357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv32371]) (by decide +kernel)
def pv1165357 : PrimeValue := ⟨1165357, pr1165357⟩
private theorem pr1165789 : Nat.Prime 1165789 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv13,pv47,pv53]) (by decide +kernel)
def pv1165789 : PrimeValue := ⟨1165789, pr1165789⟩
private theorem pr1165819 : Nat.Prime 1165819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv2341]) (by decide +kernel)
def pv1165819 : PrimeValue := ⟨1165819, pr1165819⟩
private theorem pr1165837 : Nat.Prime 1165837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13879]) (by decide +kernel)
def pv1165837 : PrimeValue := ⟨1165837, pr1165837⟩
private theorem pr1165903 : Nat.Prime 1165903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv4519]) (by decide +kernel)
def pv1165903 : PrimeValue := ⟨1165903, pr1165903⟩
private theorem pr1165993 : Nat.Prime 1165993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv2557]) (by decide +kernel)
def pv1165993 : PrimeValue := ⟨1165993, pr1165993⟩
private theorem pr1166089 : Nat.Prime 1166089 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv11,pv631]) (by decide +kernel)
def pv1166089 : PrimeValue := ⟨1166089, pr1166089⟩
private theorem pr1166227 : Nat.Prime 1166227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv194371]) (by decide +kernel)
def pv1166227 : PrimeValue := ⟨1166227, pr1166227⟩
private theorem pr1166287 : Nat.Prime 1166287 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv41,pv431]) (by decide +kernel)
def pv1166287 : PrimeValue := ⟨1166287, pr1166287⟩
private theorem pr1166383 : Nat.Prime 1166383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv9257]) (by decide +kernel)
def pv1166383 : PrimeValue := ⟨1166383, pr1166383⟩
private theorem pr1166413 : Nat.Prime 1166413 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv7477]) (by decide +kernel)
def pv1166413 : PrimeValue := ⟨1166413, pr1166413⟩
private theorem pr1166479 : Nat.Prime 1166479 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv194413]) (by decide +kernel)
def pv1166479 : PrimeValue := ⟨1166479, pr1166479⟩
private theorem pr1166563 : Nat.Prime 1166563 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv379]) (by decide +kernel)
def pv1166563 : PrimeValue := ⟨1166563, pr1166563⟩
private theorem pr1166827 : Nat.Prime 1166827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv194471]) (by decide +kernel)
def pv1166827 : PrimeValue := ⟨1166827, pr1166827⟩
private theorem pr1166953 : Nat.Prime 1166953 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv48623]) (by decide +kernel)
def pv1166953 : PrimeValue := ⟨1166953, pr1166953⟩
private theorem pr1167193 : Nat.Prime 1167193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv29,pv43]) (by decide +kernel)
def pv1167193 : PrimeValue := ⟨1167193, pr1167193⟩
private theorem pr1167277 : Nat.Prime 1167277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv37,pv239]) (by decide +kernel)
def pv1167277 : PrimeValue := ⟨1167277, pr1167277⟩
private theorem pr1167289 : Nat.Prime 1167289 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv2861]) (by decide +kernel)
def pv1167289 : PrimeValue := ⟨1167289, pr1167289⟩
private theorem pr1167307 : Nat.Prime 1167307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv27793]) (by decide +kernel)
def pv1167307 : PrimeValue := ⟨1167307, pr1167307⟩
private theorem pr1167847 : Nat.Prime 1167847 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59,pv3299]) (by decide +kernel)
def pv1167847 : PrimeValue := ⟨1167847, pr1167847⟩
private theorem pr1167919 : Nat.Prime 1167919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv194653]) (by decide +kernel)
def pv1167919 : PrimeValue := ⟨1167919, pr1167919⟩
private theorem pr1167937 : Nat.Prime 1167937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv79]) (by decide +kernel)
def pv1167937 : PrimeValue := ⟨1167937, pr1167937⟩
private theorem pr1167973 : Nat.Prime 1167973 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv7487]) (by decide +kernel)
def pv1167973 : PrimeValue := ⟨1167973, pr1167973⟩
private theorem pr1168093 : Nat.Prime 1168093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv457]) (by decide +kernel)
def pv1168093 : PrimeValue := ⟨1168093, pr1168093⟩
private theorem pr1168327 : Nat.Prime 1168327 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv1381]) (by decide +kernel)
def pv1168327 : PrimeValue := ⟨1168327, pr1168327⟩
private theorem pr1168357 : Nat.Prime 1168357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1987]) (by decide +kernel)
def pv1168357 : PrimeValue := ⟨1168357, pr1168357⟩
private theorem pr1168477 : Nat.Prime 1168477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv97373]) (by decide +kernel)
def pv1168477 : PrimeValue := ⟨1168477, pr1168477⟩
private theorem pr1168639 : Nat.Prime 1168639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv61,pv103]) (by decide +kernel)
def pv1168639 : PrimeValue := ⟨1168639, pr1168639⟩
private theorem pr1168789 : Nat.Prime 1168789 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv173,pv563]) (by decide +kernel)
def pv1168789 : PrimeValue := ⟨1168789, pr1168789⟩
private theorem pr1168819 : Nat.Prime 1168819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv1637]) (by decide +kernel)
def pv1168819 : PrimeValue := ⟨1168819, pr1168819⟩
private theorem pr1168927 : Nat.Prime 1168927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv89,pv199]) (by decide +kernel)
def pv1168927 : PrimeValue := ⟨1168927, pr1168927⟩
private theorem pr1168933 : Nat.Prime 1168933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv3359]) (by decide +kernel)
def pv1168933 : PrimeValue := ⟨1168933, pr1168933⟩
private theorem pr1169023 : Nat.Prime 1169023 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv73,pv157]) (by decide +kernel)
def pv1169023 : PrimeValue := ⟨1169023, pr1169023⟩
private theorem pr1169029 : Nat.Prime 1169029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv4639]) (by decide +kernel)
def pv1169029 : PrimeValue := ⟨1169029, pr1169029⟩
private theorem pr1169059 : Nat.Prime 1169059 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv17713]) (by decide +kernel)
def pv1169059 : PrimeValue := ⟨1169059, pr1169059⟩
private theorem pr1169347 : Nat.Prime 1169347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv194891]) (by decide +kernel)
def pv1169347 : PrimeValue := ⟨1169347, pr1169347⟩
private theorem pr1169419 : Nat.Prime 1169419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv2909]) (by decide +kernel)
def pv1169419 : PrimeValue := ⟨1169419, pr1169419⟩
private theorem pr1169767 : Nat.Prime 1169767 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv4999]) (by decide +kernel)
def pv1169767 : PrimeValue := ⟨1169767, pr1169767⟩
private theorem pr1170193 : Nat.Prime 1170193 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv24379]) (by decide +kernel)
def pv1170193 : PrimeValue := ⟨1170193, pr1170193⟩
private theorem pr1170649 : Nat.Prime 1170649 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv71,pv229]) (by decide +kernel)
def pv1170649 : PrimeValue := ⟨1170649, pr1170649⟩
private theorem pr1170787 : Nat.Prime 1170787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv195131]) (by decide +kernel)
def pv1170787 : PrimeValue := ⟨1170787, pr1170787⟩
private theorem pr1171243 : Nat.Prime 1171243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv2099]) (by decide +kernel)
def pv1171243 : PrimeValue := ⟨1171243, pr1171243⟩
private theorem pr1171447 : Nat.Prime 1171447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv195241]) (by decide +kernel)
def pv1171447 : PrimeValue := ⟨1171447, pr1171447⟩
private theorem pr1171579 : Nat.Prime 1171579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv43,pv239]) (by decide +kernel)
def pv1171579 : PrimeValue := ⟨1171579, pr1171579⟩
private theorem pr1171633 : Nat.Prime 1171633 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv11,pv317]) (by decide +kernel)
def pv1171633 : PrimeValue := ⟨1171633, pr1171633⟩
private theorem pr1171669 : Nat.Prime 1171669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv251,pv389]) (by decide +kernel)
def pv1171669 : PrimeValue := ⟨1171669, pr1171669⟩
private theorem pr1171747 : Nat.Prime 1171747 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2411]) (by decide +kernel)
def pv1171747 : PrimeValue := ⟨1171747, pr1171747⟩
private theorem pr1171957 : Nat.Prime 1171957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv127,pv769]) (by decide +kernel)
def pv1171957 : PrimeValue := ⟨1171957, pr1171957⟩
private theorem pr1172233 : Nat.Prime 1172233 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv1172233 : PrimeValue := ⟨1172233, pr1172233⟩
private theorem pr1172467 : Nat.Prime 1172467 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53,pv1229]) (by decide +kernel)
def pv1172467 : PrimeValue := ⟨1172467, pr1172467⟩
private theorem pr1172803 : Nat.Prime 1172803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv3313]) (by decide +kernel)
def pv1172803 : PrimeValue := ⟨1172803, pr1172803⟩
private theorem pr1172929 : Nat.Prime 1172929 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv41,pv149]) (by decide +kernel)
def pv1172929 : PrimeValue := ⟨1172929, pr1172929⟩
private theorem pr1172959 : Nat.Prime 1172959 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv195493]) (by decide +kernel)
def pv1172959 : PrimeValue := ⟨1172959, pr1172959⟩
private theorem pr1173013 : Nat.Prime 1173013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv239,pv409]) (by decide +kernel)
def pv1173013 : PrimeValue := ⟨1173013, pr1173013⟩
private theorem pr1173043 : Nat.Prime 1173043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv557]) (by decide +kernel)
def pv1173043 : PrimeValue := ⟨1173043, pr1173043⟩
private theorem pr1173127 : Nat.Prime 1173127 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv4547]) (by decide +kernel)
def pv1173127 : PrimeValue := ⟨1173127, pr1173127⟩
private theorem pr1173199 : Nat.Prime 1173199 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv89]) (by decide +kernel)
def pv1173199 : PrimeValue := ⟨1173199, pr1173199⟩
private theorem pr1173787 : Nat.Prime 1173787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv2357]) (by decide +kernel)
def pv1173787 : PrimeValue := ⟨1173787, pr1173787⟩
private theorem pr1173883 : Nat.Prime 1173883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv179,pv1093]) (by decide +kernel)
def pv1173883 : PrimeValue := ⟨1173883, pr1173883⟩
private theorem pr1173979 : Nat.Prime 1173979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv29,pv173]) (by decide +kernel)
def pv1173979 : PrimeValue := ⟨1173979, pr1173979⟩
private theorem pr1174273 : Nat.Prime 1174273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv139]) (by decide +kernel)
def pv1174273 : PrimeValue := ⟨1174273, pr1174273⟩
private theorem pr1174477 : Nat.Prime 1174477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv97,pv1009]) (by decide +kernel)
def pv1174477 : PrimeValue := ⟨1174477, pr1174477⟩
private theorem pr1174669 : Nat.Prime 1174669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv809]) (by decide +kernel)
def pv1174669 : PrimeValue := ⟨1174669, pr1174669⟩
private theorem pr1175143 : Nat.Prime 1175143 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv41,pv281]) (by decide +kernel)
def pv1175143 : PrimeValue := ⟨1175143, pr1175143⟩
private theorem pr1175173 : Nat.Prime 1175173 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv97931]) (by decide +kernel)
def pv1175173 : PrimeValue := ⟨1175173, pr1175173⟩
private theorem pr1175257 : Nat.Prime 1175257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5441]) (by decide +kernel)
def pv1175257 : PrimeValue := ⟨1175257, pr1175257⟩
private theorem pr1175467 : Nat.Prime 1175467 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv409,pv479]) (by decide +kernel)
def pv1175467 : PrimeValue := ⟨1175467, pr1175467⟩
private theorem pr1175509 : Nat.Prime 1175509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv32653]) (by decide +kernel)
def pv1175509 : PrimeValue := ⟨1175509, pr1175509⟩
private theorem pr1175569 : Nat.Prime 1175569 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv1289]) (by decide +kernel)
def pv1175569 : PrimeValue := ⟨1175569, pr1175569⟩
private theorem pr1175617 : Nat.Prime 1175617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv157]) (by decide +kernel)
def pv1175617 : PrimeValue := ⟨1175617, pr1175617⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
