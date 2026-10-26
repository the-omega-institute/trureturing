/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart16
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart16
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart16.traversal_1120,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart16.traversal_1121,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart16.traversal_1136,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart16.traversal_1137
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart12
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart13
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart15
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1072 (fuel : Nat) (hf : 1072 < fuel) :
    walk nodes fuel 1072 = List.range' 1032 41 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1072).rule = .split 0 (1/1280) 1070 1071 := by rfl
      simp only [walk, hr]
      rw [traversal_1070 f (by omega), traversal_1071 f (by omega)]
      change (List.range' 1032 39 ++ List.range' (1032+39) 1) ++
        [1032+(39+1)] = List.range' 1032 ((39+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1032) (n := 39+1)).symm

private theorem traversal_1073 (fuel : Nat) (hf : 1073 < fuel) :
    walk nodes fuel 1073 = List.range' 1073 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1073).rule = .bound .leftEnd 1 (1621/3072) (496795/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1074 (fuel : Nat) (hf : 1074 < fuel) :
    walk nodes fuel 1074 = List.range' 1074 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1074).rule = .bound .leftEnd 3 (1621/3072) (496795/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1075 (fuel : Nat) (hf : 1075 < fuel) :
    walk nodes fuel 1075 = List.range' 1073 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1075).rule = .split 2 (18331/8192) 1073 1074 := by rfl
      simp only [walk, hr]
      rw [traversal_1073 f (by omega), traversal_1074 f (by omega)]
      change (List.range' 1073 1 ++ List.range' (1073+1) 1) ++
        [1073+(1+1)] = List.range' 1073 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1073) (n := 1+1)).symm

private theorem traversal_1076 (fuel : Nat) (hf : 1076 < fuel) :
    walk nodes fuel 1076 = List.range' 1076 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1076).rule = .bound .leftEnd 1 (1621/3072) (496795/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1077 (fuel : Nat) (hf : 1077 < fuel) :
    walk nodes fuel 1077 = List.range' 1073 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1077).rule = .split 1 (4685/2048) 1075 1076 := by rfl
      simp only [walk, hr]
      rw [traversal_1075 f (by omega), traversal_1076 f (by omega)]
      change (List.range' 1073 3 ++ List.range' (1073+3) 1) ++
        [1073+(3+1)] = List.range' 1073 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1073) (n := 3+1)).symm

private theorem traversal_1078 (fuel : Nat) (hf : 1078 < fuel) :
    walk nodes fuel 1078 = List.range' 1078 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1078).rule = .bound .leftEnd 1 (1621/3072) (496795/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1079 (fuel : Nat) (hf : 1079 < fuel) :
    walk nodes fuel 1079 = List.range' 1073 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1079).rule = .split 0 (1/2560) 1077 1078 := by rfl
      simp only [walk, hr]
      rw [traversal_1077 f (by omega), traversal_1078 f (by omega)]
      change (List.range' 1073 5 ++ List.range' (1073+5) 1) ++
        [1073+(5+1)] = List.range' 1073 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1073) (n := 5+1)).symm

private theorem traversal_1080 (fuel : Nat) (hf : 1080 < fuel) :
    walk nodes fuel 1080 = List.range' 1080 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1080).rule = .bound .leftEnd 1 (809/1536) (124429/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1081 (fuel : Nat) (hf : 1081 < fuel) :
    walk nodes fuel 1081 = List.range' 1073 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1081).rule = .split 3 (921/1024) 1079 1080 := by rfl
      simp only [walk, hr]
      rw [traversal_1079 f (by omega), traversal_1080 f (by omega)]
      change (List.range' 1073 7 ++ List.range' (1073+7) 1) ++
        [1073+(7+1)] = List.range' 1073 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1073) (n := 7+1)).symm

private theorem traversal_1082 (fuel : Nat) (hf : 1082 < fuel) :
    walk nodes fuel 1082 = List.range' 1082 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1082).rule = .bound .leftEnd 3 (3239/6144) (248627/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1083 (fuel : Nat) (hf : 1083 < fuel) :
    walk nodes fuel 1083 = List.range' 1073 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1083).rule = .split 2 (9175/4096) 1081 1082 := by rfl
      simp only [walk, hr]
      rw [traversal_1081 f (by omega), traversal_1082 f (by omega)]
      change (List.range' 1073 9 ++ List.range' (1073+9) 1) ++
        [1073+(9+1)] = List.range' 1073 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1073) (n := 9+1)).symm

private theorem traversal_1084 (fuel : Nat) (hf : 1084 < fuel) :
    walk nodes fuel 1084 = List.range' 1084 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1084).rule = .bound .leftEnd 3 (3239/6144) (248627/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1085 (fuel : Nat) (hf : 1085 < fuel) :
    walk nodes fuel 1085 = List.range' 1073 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1085).rule = .split 1 (2345/1024) 1083 1084 := by rfl
      simp only [walk, hr]
      rw [traversal_1083 f (by omega), traversal_1084 f (by omega)]
      change (List.range' 1073 11 ++ List.range' (1073+11) 1) ++
        [1073+(11+1)] = List.range' 1073 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1073) (n := 11+1)).symm

private theorem traversal_1086 (fuel : Nat) (hf : 1086 < fuel) :
    walk nodes fuel 1086 = List.range' 1086 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1086).rule = .bound .leftEnd 1 (3239/6144) (248627/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1087 (fuel : Nat) (hf : 1087 < fuel) :
    walk nodes fuel 1087 = List.range' 1073 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1087).rule = .split 0 (1/1280) 1085 1086 := by rfl
      simp only [walk, hr]
      rw [traversal_1085 f (by omega), traversal_1086 f (by omega)]
      change (List.range' 1073 13 ++ List.range' (1073+13) 1) ++
        [1073+(13+1)] = List.range' 1073 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1073) (n := 13+1)).symm

private theorem traversal_1088 (fuel : Nat) (hf : 1088 < fuel) :
    walk nodes fuel 1088 = List.range' 1032 57 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1088).rule = .split 3 (459/512) 1072 1087 := by rfl
      simp only [walk, hr]
      rw [traversal_1072 f (by omega), traversal_1087 f (by omega)]
      change (List.range' 1032 41 ++ List.range' (1032+41) 15) ++
        [1032+(41+15)] = List.range' 1032 ((41+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1032) (n := 41+15)).symm

private theorem traversal_1089 (fuel : Nat) (hf : 1089 < fuel) :
    walk nodes fuel 1089 = List.range' 1089 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1089).rule = .bound .leftEnd 3 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1090 (fuel : Nat) (hf : 1090 < fuel) :
    walk nodes fuel 1090 = List.range' 1032 59 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1090).rule = .split 2 (4597/2048) 1088 1089 := by rfl
      simp only [walk, hr]
      rw [traversal_1088 f (by omega), traversal_1089 f (by omega)]
      change (List.range' 1032 57 ++ List.range' (1032+57) 1) ++
        [1032+(57+1)] = List.range' 1032 ((57+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1032) (n := 57+1)).symm

private theorem traversal_1091 (fuel : Nat) (hf : 1091 < fuel) :
    walk nodes fuel 1091 = List.range' 1091 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1091).rule = .bound .leftEnd 3 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1092 (fuel : Nat) (hf : 1092 < fuel) :
    walk nodes fuel 1092 = List.range' 1032 61 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1092).rule = .split 1 (1175/512) 1090 1091 := by rfl
      simp only [walk, hr]
      rw [traversal_1090 f (by omega), traversal_1091 f (by omega)]
      change (List.range' 1032 59 ++ List.range' (1032+59) 1) ++
        [1032+(59+1)] = List.range' 1032 ((59+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1032) (n := 59+1)).symm

private theorem traversal_1093 (fuel : Nat) (hf : 1093 < fuel) :
    walk nodes fuel 1093 = List.range' 1093 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1093).rule = .bound .leftEnd 3 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1094 (fuel : Nat) (hf : 1094 < fuel) :
    walk nodes fuel 1094 = List.range' 1032 63 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1094).rule = .split 0 (1/640) 1092 1093 := by rfl
      simp only [walk, hr]
      rw [traversal_1092 f (by omega), traversal_1093 f (by omega)]
      change (List.range' 1032 61 ++ List.range' (1032+61) 1) ++
        [1032+(61+1)] = List.range' 1032 ((61+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1032) (n := 61+1)).symm

private theorem traversal_1095 (fuel : Nat) (hf : 1095 < fuel) :
    walk nodes fuel 1095 = List.range' 1095 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1095).rule = .bound .leftEnd 1 (403/768) (124891/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1096 (fuel : Nat) (hf : 1096 < fuel) :
    walk nodes fuel 1096 = List.range' 1096 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1096).rule = .bound .leftEnd 3 (403/768) (124891/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1097 (fuel : Nat) (hf : 1097 < fuel) :
    walk nodes fuel 1097 = List.range' 1095 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1097).rule = .split 2 (4597/2048) 1095 1096 := by rfl
      simp only [walk, hr]
      rw [traversal_1095 f (by omega), traversal_1096 f (by omega)]
      change (List.range' 1095 1 ++ List.range' (1095+1) 1) ++
        [1095+(1+1)] = List.range' 1095 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1095) (n := 1+1)).symm

private theorem traversal_1098 (fuel : Nat) (hf : 1098 < fuel) :
    walk nodes fuel 1098 = List.range' 1098 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1098).rule = .bound .leftEnd 1 (403/768) (124891/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1099 (fuel : Nat) (hf : 1099 < fuel) :
    walk nodes fuel 1099 = List.range' 1095 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1099).rule = .split 1 (1175/512) 1097 1098 := by rfl
      simp only [walk, hr]
      rw [traversal_1097 f (by omega), traversal_1098 f (by omega)]
      change (List.range' 1095 3 ++ List.range' (1095+3) 1) ++
        [1095+(3+1)] = List.range' 1095 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1095) (n := 3+1)).symm

private theorem traversal_1100 (fuel : Nat) (hf : 1100 < fuel) :
    walk nodes fuel 1100 = List.range' 1100 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1100).rule = .bound .leftEnd 1 (403/768) (124891/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1101 (fuel : Nat) (hf : 1101 < fuel) :
    walk nodes fuel 1101 = List.range' 1095 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1101).rule = .split 0 (1/640) 1099 1100 := by rfl
      simp only [walk, hr]
      rw [traversal_1099 f (by omega), traversal_1100 f (by omega)]
      change (List.range' 1095 5 ++ List.range' (1095+5) 1) ++
        [1095+(5+1)] = List.range' 1095 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1095) (n := 5+1)).symm

private theorem traversal_1102 (fuel : Nat) (hf : 1102 < fuel) :
    walk nodes fuel 1102 = List.range' 1032 71 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1102).rule = .split 3 (231/256) 1094 1101 := by rfl
      simp only [walk, hr]
      rw [traversal_1094 f (by omega), traversal_1101 f (by omega)]
      change (List.range' 1032 63 ++ List.range' (1032+63) 7) ++
        [1032+(63+7)] = List.range' 1032 ((63+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1032) (n := 63+7)).symm

private theorem traversal_1103 (fuel : Nat) (hf : 1103 < fuel) :
    walk nodes fuel 1103 = List.range' 907 197 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1103).rule = .split 2 (2289/1024) 1031 1102 := by rfl
      simp only [walk, hr]
      rw [traversal_1031 f (by omega), traversal_1102 f (by omega)]
      change (List.range' 907 125 ++ List.range' (907+125) 71) ++
        [907+(125+71)] = List.range' 907 ((125+71)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 907) (n := 125+71)).symm

private theorem traversal_1104 (fuel : Nat) (hf : 1104 < fuel) :
    walk nodes fuel 1104 = List.range' 828 277 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1104).rule = .split 1 (585/256) 906 1103 := by rfl
      simp only [walk, hr]
      rw [traversal_906 f (by omega), traversal_1103 f (by omega)]
      change (List.range' 828 79 ++ List.range' (828+79) 197) ++
        [828+(79+197)] = List.range' 828 ((79+197)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 828) (n := 79+197)).symm

private theorem traversal_1105 (fuel : Nat) (hf : 1105 < fuel) :
    walk nodes fuel 1105 = List.range' 1105 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1105).rule = .bound .leftEnd 1 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1106 (fuel : Nat) (hf : 1106 < fuel) :
    walk nodes fuel 1106 = List.range' 1106 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1106).rule = .bound .leftEnd 3 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1107 (fuel : Nat) (hf : 1107 < fuel) :
    walk nodes fuel 1107 = List.range' 1105 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1107).rule = .split 2 (2289/1024) 1105 1106 := by rfl
      simp only [walk, hr]
      rw [traversal_1105 f (by omega), traversal_1106 f (by omega)]
      change (List.range' 1105 1 ++ List.range' (1105+1) 1) ++
        [1105+(1+1)] = List.range' 1105 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1105) (n := 1+1)).symm

private theorem traversal_1108 (fuel : Nat) (hf : 1108 < fuel) :
    walk nodes fuel 1108 = List.range' 1108 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1108).rule = .bound .leftEnd 1 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1109 (fuel : Nat) (hf : 1109 < fuel) :
    walk nodes fuel 1109 = List.range' 1105 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1109).rule = .split 1 (585/256) 1107 1108 := by rfl
      simp only [walk, hr]
      rw [traversal_1107 f (by omega), traversal_1108 f (by omega)]
      change (List.range' 1105 3 ++ List.range' (1105+3) 1) ++
        [1105+(3+1)] = List.range' 1105 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1105) (n := 3+1)).symm

private theorem traversal_1110 (fuel : Nat) (hf : 1110 < fuel) :
    walk nodes fuel 1110 = List.range' 828 283 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1110).rule = .split 0 (1/320) 1104 1109 := by rfl
      simp only [walk, hr]
      rw [traversal_1104 f (by omega), traversal_1109 f (by omega)]
      change (List.range' 828 277 ++ List.range' (828+277) 5) ++
        [828+(277+5)] = List.range' 828 ((277+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 828) (n := 277+5)).symm

private theorem traversal_1111 (fuel : Nat) (hf : 1111 < fuel) :
    walk nodes fuel 1111 = List.range' 1111 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1111).rule = .bound .leftEnd 1 (4257/8192) (504439/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1112 (fuel : Nat) (hf : 1112 < fuel) :
    walk nodes fuel 1112 = List.range' 828 285 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1112).rule = .split 3 (117/128) 1110 1111 := by rfl
      simp only [walk, hr]
      rw [traversal_1110 f (by omega), traversal_1111 f (by omega)]
      change (List.range' 828 283 ++ List.range' (828+283) 1) ++
        [828+(283+1)] = List.range' 828 ((283+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 828) (n := 283+1)).symm

private theorem traversal_1113 (fuel : Nat) (hf : 1113 < fuel) :
    walk nodes fuel 1113 = List.range' 821 293 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1113).rule = .split 2 (1135/512) 827 1112 := by rfl
      simp only [walk, hr]
      rw [traversal_827 f (by omega), traversal_1112 f (by omega)]
      change (List.range' 821 7 ++ List.range' (821+7) 285) ++
        [821+(7+285)] = List.range' 821 ((7+285)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 821) (n := 7+285)).symm

private theorem traversal_1114 (fuel : Nat) (hf : 1114 < fuel) :
    walk nodes fuel 1114 = List.range' 1114 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1114).rule = .bound .leftEnd 1 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1115 (fuel : Nat) (hf : 1115 < fuel) :
    walk nodes fuel 1115 = List.range' 1115 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1115).rule = .bound .leftEnd 3 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1116 (fuel : Nat) (hf : 1116 < fuel) :
    walk nodes fuel 1116 = List.range' 1114 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1116).rule = .split 2 (1135/512) 1114 1115 := by rfl
      simp only [walk, hr]
      rw [traversal_1114 f (by omega), traversal_1115 f (by omega)]
      change (List.range' 1114 1 ++ List.range' (1114+1) 1) ++
        [1114+(1+1)] = List.range' 1114 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1114) (n := 1+1)).symm

private theorem traversal_1117 (fuel : Nat) (hf : 1117 < fuel) :
    walk nodes fuel 1117 = List.range' 821 297 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1117).rule = .split 1 (295/128) 1113 1116 := by rfl
      simp only [walk, hr]
      rw [traversal_1113 f (by omega), traversal_1116 f (by omega)]
      change (List.range' 821 293 ++ List.range' (821+293) 3) ++
        [821+(293+3)] = List.range' 821 ((293+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 821) (n := 293+3)).symm

private theorem traversal_1118 (fuel : Nat) (hf : 1118 < fuel) :
    walk nodes fuel 1118 = List.range' 1118 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1118).rule = .bound .leftEnd 1 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1119 (fuel : Nat) (hf : 1119 < fuel) :
    walk nodes fuel 1119 = List.range' 821 299 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1119).rule = .split 0 (1/160) 1117 1118 := by rfl
      simp only [walk, hr]
      rw [traversal_1117 f (by omega), traversal_1118 f (by omega)]
      change (List.range' 821 297 ++ List.range' (821+297) 1) ++
        [821+(297+1)] = List.range' 821 ((297+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 821) (n := 297+1)).symm

theorem traversal_1120 (fuel : Nat) (hf : 1120 < fuel) :
    walk nodes fuel 1120 = List.range' 602 519 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1120).rule = .split 3 (57/64) 820 1119 := by rfl
      simp only [walk, hr]
      rw [traversal_820 f (by omega), traversal_1119 f (by omega)]
      change (List.range' 602 219 ++ List.range' (602+219) 299) ++
        [602+(219+299)] = List.range' 602 ((219+299)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 602) (n := 219+299)).symm

theorem traversal_1121 (fuel : Nat) (hf : 1121 < fuel) :
    walk nodes fuel 1121 = List.range' 1121 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1121).rule = .bound .leftEnd 2 (26393/49152) (61013/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1122 (fuel : Nat) (hf : 1122 < fuel) :
    walk nodes fuel 1122 = List.range' 1122 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1122).rule = .bound .leftEnd 8 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1123 (fuel : Nat) (hf : 1123 < fuel) :
    walk nodes fuel 1123 = List.range' 1123 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1123).rule = .bound .leftEnd 3 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1124 (fuel : Nat) (hf : 1124 < fuel) :
    walk nodes fuel 1124 = List.range' 1122 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1124).rule = .split 2 (4635/2048) 1122 1123 := by rfl
      simp only [walk, hr]
      rw [traversal_1122 f (by omega), traversal_1123 f (by omega)]
      change (List.range' 1122 1 ++ List.range' (1122+1) 1) ++
        [1122+(1+1)] = List.range' 1122 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1122) (n := 1+1)).symm

private theorem traversal_1125 (fuel : Nat) (hf : 1125 < fuel) :
    walk nodes fuel 1125 = List.range' 1125 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1125).rule = .bound .leftEnd 3 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1126 (fuel : Nat) (hf : 1126 < fuel) :
    walk nodes fuel 1126 = List.range' 1122 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1126).rule = .split 1 (1165/512) 1124 1125 := by rfl
      simp only [walk, hr]
      rw [traversal_1124 f (by omega), traversal_1125 f (by omega)]
      change (List.range' 1122 3 ++ List.range' (1122+3) 1) ++
        [1122+(3+1)] = List.range' 1122 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1122) (n := 3+1)).symm

private theorem traversal_1127 (fuel : Nat) (hf : 1127 < fuel) :
    walk nodes fuel 1127 = List.range' 1127 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1127).rule = .bound .leftEnd 3 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1128 (fuel : Nat) (hf : 1128 < fuel) :
    walk nodes fuel 1128 = List.range' 1122 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1128).rule = .split 0 (1/640) 1126 1127 := by rfl
      simp only [walk, hr]
      rw [traversal_1126 f (by omega), traversal_1127 f (by omega)]
      change (List.range' 1122 5 ++ List.range' (1122+5) 1) ++
        [1122+(5+1)] = List.range' 1122 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1122) (n := 5+1)).symm

private theorem traversal_1129 (fuel : Nat) (hf : 1129 < fuel) :
    walk nodes fuel 1129 = List.range' 1129 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1129).rule = .bound .leftEnd 8 (403/768) (124891/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1130 (fuel : Nat) (hf : 1130 < fuel) :
    walk nodes fuel 1130 = List.range' 1130 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1130).rule = .bound .leftEnd 3 (403/768) (124891/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1131 (fuel : Nat) (hf : 1131 < fuel) :
    walk nodes fuel 1131 = List.range' 1129 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1131).rule = .split 1 (1165/512) 1129 1130 := by rfl
      simp only [walk, hr]
      rw [traversal_1129 f (by omega), traversal_1130 f (by omega)]
      change (List.range' 1129 1 ++ List.range' (1129+1) 1) ++
        [1129+(1+1)] = List.range' 1129 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1129) (n := 1+1)).symm

private theorem traversal_1132 (fuel : Nat) (hf : 1132 < fuel) :
    walk nodes fuel 1132 = List.range' 1132 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1132).rule = .bound .leftEnd 3 (403/768) (124891/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1133 (fuel : Nat) (hf : 1133 < fuel) :
    walk nodes fuel 1133 = List.range' 1129 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1133).rule = .split 0 (1/640) 1131 1132 := by rfl
      simp only [walk, hr]
      rw [traversal_1131 f (by omega), traversal_1132 f (by omega)]
      change (List.range' 1129 3 ++ List.range' (1129+3) 1) ++
        [1129+(3+1)] = List.range' 1129 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1129) (n := 3+1)).symm

private theorem traversal_1134 (fuel : Nat) (hf : 1134 < fuel) :
    walk nodes fuel 1134 = List.range' 1122 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1134).rule = .split 3 (231/256) 1128 1133 := by rfl
      simp only [walk, hr]
      rw [traversal_1128 f (by omega), traversal_1133 f (by omega)]
      change (List.range' 1122 7 ++ List.range' (1122+7) 5) ++
        [1122+(7+5)] = List.range' 1122 ((7+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1122) (n := 7+5)).symm

private theorem traversal_1135 (fuel : Nat) (hf : 1135 < fuel) :
    walk nodes fuel 1135 = List.range' 1135 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1135).rule = .bound .leftEnd 3 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1136 (fuel : Nat) (hf : 1136 < fuel) :
    walk nodes fuel 1136 = List.range' 1122 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1136).rule = .split 2 (2327/1024) 1134 1135 := by rfl
      simp only [walk, hr]
      rw [traversal_1134 f (by omega), traversal_1135 f (by omega)]
      change (List.range' 1122 13 ++ List.range' (1122+13) 1) ++
        [1122+(13+1)] = List.range' 1122 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1122) (n := 13+1)).symm

theorem traversal_1137 (fuel : Nat) (hf : 1137 < fuel) :
    walk nodes fuel 1137 = List.range' 1137 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1137).rule = .bound .leftEnd 3 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
