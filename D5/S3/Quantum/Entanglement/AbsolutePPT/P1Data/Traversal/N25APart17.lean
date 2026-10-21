/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart17
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart17
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart17.traversal_1203
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart08
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart16
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1138 (fuel : Nat) (hf : 1138 < fuel) :
    walk nodes fuel 1138 = List.range' 1122 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1138).rule = .split 1 (585/256) 1136 1137 := by rfl
      simp only [walk, hr]
      rw [traversal_1136 f (by omega), traversal_1137 f (by omega)]
      change (List.range' 1122 15 ++ List.range' (1122+15) 1) ++
        [1122+(15+1)] = List.range' 1122 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1122) (n := 15+1)).symm

private theorem traversal_1139 (fuel : Nat) (hf : 1139 < fuel) :
    walk nodes fuel 1139 = List.range' 1139 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1139).rule = .bound .leftEnd 3 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1140 (fuel : Nat) (hf : 1140 < fuel) :
    walk nodes fuel 1140 = List.range' 1122 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1140).rule = .split 0 (1/320) 1138 1139 := by rfl
      simp only [walk, hr]
      rw [traversal_1138 f (by omega), traversal_1139 f (by omega)]
      change (List.range' 1122 17 ++ List.range' (1122+17) 1) ++
        [1122+(17+1)] = List.range' 1122 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1122) (n := 17+1)).symm

private theorem traversal_1141 (fuel : Nat) (hf : 1141 < fuel) :
    walk nodes fuel 1141 = List.range' 1141 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1141).rule = .bound .leftEnd 8 (2135/4096) (251459/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1142 (fuel : Nat) (hf : 1142 < fuel) :
    walk nodes fuel 1142 = List.range' 1142 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1142).rule = .bound .leftEnd 3 (2135/4096) (251459/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1143 (fuel : Nat) (hf : 1143 < fuel) :
    walk nodes fuel 1143 = List.range' 1141 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1143).rule = .split 1 (1165/512) 1141 1142 := by rfl
      simp only [walk, hr]
      rw [traversal_1141 f (by omega), traversal_1142 f (by omega)]
      change (List.range' 1141 1 ++ List.range' (1141+1) 1) ++
        [1141+(1+1)] = List.range' 1141 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1141) (n := 1+1)).symm

private theorem traversal_1144 (fuel : Nat) (hf : 1144 < fuel) :
    walk nodes fuel 1144 = List.range' 1144 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1144).rule = .bound .leftEnd 3 (2135/4096) (251459/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1145 (fuel : Nat) (hf : 1145 < fuel) :
    walk nodes fuel 1145 = List.range' 1141 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1145).rule = .split 0 (1/640) 1143 1144 := by rfl
      simp only [walk, hr]
      rw [traversal_1143 f (by omega), traversal_1144 f (by omega)]
      change (List.range' 1141 3 ++ List.range' (1141+3) 1) ++
        [1141+(3+1)] = List.range' 1141 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1141) (n := 3+1)).symm

private theorem traversal_1146 (fuel : Nat) (hf : 1146 < fuel) :
    walk nodes fuel 1146 = List.range' 1146 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1146).rule = .bound .leftEnd 1 (1061/2048) (505999/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1147 (fuel : Nat) (hf : 1147 < fuel) :
    walk nodes fuel 1147 = List.range' 1141 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1147).rule = .split 3 (237/256) 1145 1146 := by rfl
      simp only [walk, hr]
      rw [traversal_1145 f (by omega), traversal_1146 f (by omega)]
      change (List.range' 1141 5 ++ List.range' (1141+5) 1) ++
        [1141+(5+1)] = List.range' 1141 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1141) (n := 5+1)).symm

private theorem traversal_1148 (fuel : Nat) (hf : 1148 < fuel) :
    walk nodes fuel 1148 = List.range' 1148 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1148).rule = .bound .leftEnd 3 (4257/8192) (504439/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1149 (fuel : Nat) (hf : 1149 < fuel) :
    walk nodes fuel 1149 = List.range' 1141 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1149).rule = .split 2 (2327/1024) 1147 1148 := by rfl
      simp only [walk, hr]
      rw [traversal_1147 f (by omega), traversal_1148 f (by omega)]
      change (List.range' 1141 7 ++ List.range' (1141+7) 1) ++
        [1141+(7+1)] = List.range' 1141 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1141) (n := 7+1)).symm

private theorem traversal_1150 (fuel : Nat) (hf : 1150 < fuel) :
    walk nodes fuel 1150 = List.range' 1150 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1150).rule = .bound .leftEnd 3 (4257/8192) (504439/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1151 (fuel : Nat) (hf : 1151 < fuel) :
    walk nodes fuel 1151 = List.range' 1141 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1151).rule = .split 1 (585/256) 1149 1150 := by rfl
      simp only [walk, hr]
      rw [traversal_1149 f (by omega), traversal_1150 f (by omega)]
      change (List.range' 1141 9 ++ List.range' (1141+9) 1) ++
        [1141+(9+1)] = List.range' 1141 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1141) (n := 9+1)).symm

private theorem traversal_1152 (fuel : Nat) (hf : 1152 < fuel) :
    walk nodes fuel 1152 = List.range' 1152 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1152).rule = .bound .leftEnd 3 (4257/8192) (504439/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1153 (fuel : Nat) (hf : 1153 < fuel) :
    walk nodes fuel 1153 = List.range' 1141 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1153).rule = .split 0 (1/320) 1151 1152 := by rfl
      simp only [walk, hr]
      rw [traversal_1151 f (by omega), traversal_1152 f (by omega)]
      change (List.range' 1141 11 ++ List.range' (1141+11) 1) ++
        [1141+(11+1)] = List.range' 1141 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1141) (n := 11+1)).symm

private theorem traversal_1154 (fuel : Nat) (hf : 1154 < fuel) :
    walk nodes fuel 1154 = List.range' 1122 33 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1154).rule = .split 3 (117/128) 1140 1153 := by rfl
      simp only [walk, hr]
      rw [traversal_1140 f (by omega), traversal_1153 f (by omega)]
      change (List.range' 1122 19 ++ List.range' (1122+19) 13) ++
        [1122+(19+13)] = List.range' 1122 ((19+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1122) (n := 19+13)).symm

private theorem traversal_1155 (fuel : Nat) (hf : 1155 < fuel) :
    walk nodes fuel 1155 = List.range' 1155 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1155).rule = .bound .leftEnd 3 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1156 (fuel : Nat) (hf : 1156 < fuel) :
    walk nodes fuel 1156 = List.range' 1122 35 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1156).rule = .split 2 (1173/512) 1154 1155 := by rfl
      simp only [walk, hr]
      rw [traversal_1154 f (by omega), traversal_1155 f (by omega)]
      change (List.range' 1122 33 ++ List.range' (1122+33) 1) ++
        [1122+(33+1)] = List.range' 1122 ((33+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1122) (n := 33+1)).symm

private theorem traversal_1157 (fuel : Nat) (hf : 1157 < fuel) :
    walk nodes fuel 1157 = List.range' 1157 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1157).rule = .bound .leftEnd 3 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1158 (fuel : Nat) (hf : 1158 < fuel) :
    walk nodes fuel 1158 = List.range' 1122 37 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1158).rule = .split 1 (295/128) 1156 1157 := by rfl
      simp only [walk, hr]
      rw [traversal_1156 f (by omega), traversal_1157 f (by omega)]
      change (List.range' 1122 35 ++ List.range' (1122+35) 1) ++
        [1122+(35+1)] = List.range' 1122 ((35+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1122) (n := 35+1)).symm

private theorem traversal_1159 (fuel : Nat) (hf : 1159 < fuel) :
    walk nodes fuel 1159 = List.range' 1159 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1159).rule = .bound .leftEnd 3 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1160 (fuel : Nat) (hf : 1160 < fuel) :
    walk nodes fuel 1160 = List.range' 1122 39 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1160).rule = .split 0 (1/160) 1158 1159 := by rfl
      simp only [walk, hr]
      rw [traversal_1158 f (by omega), traversal_1159 f (by omega)]
      change (List.range' 1122 37 ++ List.range' (1122+37) 1) ++
        [1122+(37+1)] = List.range' 1122 ((37+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1122) (n := 37+1)).symm

private theorem traversal_1161 (fuel : Nat) (hf : 1161 < fuel) :
    walk nodes fuel 1161 = List.range' 1121 41 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1161).rule = .split 3 (57/64) 1121 1160 := by rfl
      simp only [walk, hr]
      rw [traversal_1121 f (by omega), traversal_1160 f (by omega)]
      change (List.range' 1121 1 ++ List.range' (1121+1) 39) ++
        [1121+(1+39)] = List.range' 1121 ((1+39)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1121) (n := 1+39)).symm

private theorem traversal_1162 (fuel : Nat) (hf : 1162 < fuel) :
    walk nodes fuel 1162 = List.range' 602 561 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1162).rule = .split 2 (577/256) 1120 1161 := by rfl
      simp only [walk, hr]
      rw [traversal_1120 f (by omega), traversal_1161 f (by omega)]
      change (List.range' 602 519 ++ List.range' (602+519) 41) ++
        [602+(519+41)] = List.range' 602 ((519+41)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 602) (n := 519+41)).symm

private theorem traversal_1163 (fuel : Nat) (hf : 1163 < fuel) :
    walk nodes fuel 1163 = List.range' 565 599 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1163).rule = .split 1 (145/64) 601 1162 := by rfl
      simp only [walk, hr]
      rw [traversal_601 f (by omega), traversal_1162 f (by omega)]
      change (List.range' 565 37 ++ List.range' (565+37) 561) ++
        [565+(37+561)] = List.range' 565 ((37+561)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 565) (n := 37+561)).symm

private theorem traversal_1164 (fuel : Nat) (hf : 1164 < fuel) :
    walk nodes fuel 1164 = List.range' 1164 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1164).rule = .bound .leftEnd 8 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1165 (fuel : Nat) (hf : 1165 < fuel) :
    walk nodes fuel 1165 = List.range' 1165 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1165).rule = .bound .leftEnd 3 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1166 (fuel : Nat) (hf : 1166 < fuel) :
    walk nodes fuel 1166 = List.range' 1164 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1166).rule = .split 2 (577/256) 1164 1165 := by rfl
      simp only [walk, hr]
      rw [traversal_1164 f (by omega), traversal_1165 f (by omega)]
      change (List.range' 1164 1 ++ List.range' (1164+1) 1) ++
        [1164+(1+1)] = List.range' 1164 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1164) (n := 1+1)).symm

private theorem traversal_1167 (fuel : Nat) (hf : 1167 < fuel) :
    walk nodes fuel 1167 = List.range' 1167 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1167).rule = .bound .leftEnd 3 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1168 (fuel : Nat) (hf : 1168 < fuel) :
    walk nodes fuel 1168 = List.range' 1164 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1168).rule = .split 1 (145/64) 1166 1167 := by rfl
      simp only [walk, hr]
      rw [traversal_1166 f (by omega), traversal_1167 f (by omega)]
      change (List.range' 1164 3 ++ List.range' (1164+3) 1) ++
        [1164+(3+1)] = List.range' 1164 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1164) (n := 3+1)).symm

private theorem traversal_1169 (fuel : Nat) (hf : 1169 < fuel) :
    walk nodes fuel 1169 = List.range' 565 605 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1169).rule = .split 0 (1/80) 1163 1168 := by rfl
      simp only [walk, hr]
      rw [traversal_1163 f (by omega), traversal_1168 f (by omega)]
      change (List.range' 565 599 ++ List.range' (565+599) 5) ++
        [565+(599+5)] = List.range' 565 ((599+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 565) (n := 599+5)).symm

private theorem traversal_1170 (fuel : Nat) (hf : 1170 < fuel) :
    walk nodes fuel 1170 = List.range' 564 607 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1170).rule = .split 3 (27/32) 564 1169 := by rfl
      simp only [walk, hr]
      rw [traversal_564 f (by omega), traversal_1169 f (by omega)]
      change (List.range' 564 1 ++ List.range' (564+1) 605) ++
        [564+(1+605)] = List.range' 564 ((1+605)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 564) (n := 1+605)).symm

private theorem traversal_1171 (fuel : Nat) (hf : 1171 < fuel) :
    walk nodes fuel 1171 = List.range' 435 737 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1171).rule = .split 2 (279/128) 563 1170 := by rfl
      simp only [walk, hr]
      rw [traversal_563 f (by omega), traversal_1170 f (by omega)]
      change (List.range' 435 129 ++ List.range' (435+129) 607) ++
        [435+(129+607)] = List.range' 435 ((129+607)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 435) (n := 129+607)).symm

private theorem traversal_1172 (fuel : Nat) (hf : 1172 < fuel) :
    walk nodes fuel 1172 = List.range' 1172 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1172).rule = .bound .leftEnd 2 (2329/4096) (460925/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1173 (fuel : Nat) (hf : 1173 < fuel) :
    walk nodes fuel 1173 = List.range' 1173 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1173).rule = .bound .leftEnd 1 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1174 (fuel : Nat) (hf : 1174 < fuel) :
    walk nodes fuel 1174 = List.range' 1174 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1174).rule = .bound .leftEnd 2 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1175 (fuel : Nat) (hf : 1175 < fuel) :
    walk nodes fuel 1175 = List.range' 1173 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1175).rule = .split 2 (1059/512) 1173 1174 := by rfl
      simp only [walk, hr]
      rw [traversal_1173 f (by omega), traversal_1174 f (by omega)]
      change (List.range' 1173 1 ++ List.range' (1173+1) 1) ++
        [1173+(1+1)] = List.range' 1173 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1173) (n := 1+1)).symm

private theorem traversal_1176 (fuel : Nat) (hf : 1176 < fuel) :
    walk nodes fuel 1176 = List.range' 1176 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1176).rule = .bound .leftEnd 1 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1177 (fuel : Nat) (hf : 1177 < fuel) :
    walk nodes fuel 1177 = List.range' 1173 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1177).rule = .split 1 (305/128) 1175 1176 := by rfl
      simp only [walk, hr]
      rw [traversal_1175 f (by omega), traversal_1176 f (by omega)]
      change (List.range' 1173 3 ++ List.range' (1173+3) 1) ++
        [1173+(3+1)] = List.range' 1173 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1173) (n := 3+1)).symm

private theorem traversal_1178 (fuel : Nat) (hf : 1178 < fuel) :
    walk nodes fuel 1178 = List.range' 1178 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1178).rule = .bound .leftEnd 1 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1179 (fuel : Nat) (hf : 1179 < fuel) :
    walk nodes fuel 1179 = List.range' 1173 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1179).rule = .split 0 (1/160) 1177 1178 := by rfl
      simp only [walk, hr]
      rw [traversal_1177 f (by omega), traversal_1178 f (by omega)]
      change (List.range' 1173 5 ++ List.range' (1173+5) 1) ++
        [1173+(5+1)] = List.range' 1173 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1173) (n := 5+1)).symm

private theorem traversal_1180 (fuel : Nat) (hf : 1180 < fuel) :
    walk nodes fuel 1180 = List.range' 1172 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1180).rule = .split 3 (51/64) 1172 1179 := by rfl
      simp only [walk, hr]
      rw [traversal_1172 f (by omega), traversal_1179 f (by omega)]
      change (List.range' 1172 1 ++ List.range' (1172+1) 7) ++
        [1172+(1+7)] = List.range' 1172 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1172) (n := 1+7)).symm

private theorem traversal_1181 (fuel : Nat) (hf : 1181 < fuel) :
    walk nodes fuel 1181 = List.range' 1181 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1181).rule = .bound .leftEnd 2 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1182 (fuel : Nat) (hf : 1182 < fuel) :
    walk nodes fuel 1182 = List.range' 1172 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1182).rule = .split 2 (539/256) 1180 1181 := by rfl
      simp only [walk, hr]
      rw [traversal_1180 f (by omega), traversal_1181 f (by omega)]
      change (List.range' 1172 9 ++ List.range' (1172+9) 1) ++
        [1172+(9+1)] = List.range' 1172 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1172) (n := 9+1)).symm

private theorem traversal_1183 (fuel : Nat) (hf : 1183 < fuel) :
    walk nodes fuel 1183 = List.range' 1183 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1183).rule = .bound .leftEnd 2 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1184 (fuel : Nat) (hf : 1184 < fuel) :
    walk nodes fuel 1184 = List.range' 1172 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1184).rule = .split 1 (155/64) 1182 1183 := by rfl
      simp only [walk, hr]
      rw [traversal_1182 f (by omega), traversal_1183 f (by omega)]
      change (List.range' 1172 11 ++ List.range' (1172+11) 1) ++
        [1172+(11+1)] = List.range' 1172 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1172) (n := 11+1)).symm

private theorem traversal_1185 (fuel : Nat) (hf : 1185 < fuel) :
    walk nodes fuel 1185 = List.range' 1185 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1185).rule = .bound .leftEnd 2 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1186 (fuel : Nat) (hf : 1186 < fuel) :
    walk nodes fuel 1186 = List.range' 1172 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1186).rule = .split 0 (1/80) 1184 1185 := by rfl
      simp only [walk, hr]
      rw [traversal_1184 f (by omega), traversal_1185 f (by omega)]
      change (List.range' 1172 13 ++ List.range' (1172+13) 1) ++
        [1172+(13+1)] = List.range' 1172 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1172) (n := 13+1)).symm

private theorem traversal_1187 (fuel : Nat) (hf : 1187 < fuel) :
    walk nodes fuel 1187 = List.range' 1187 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1187).rule = .bound .leftEnd 1 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1188 (fuel : Nat) (hf : 1188 < fuel) :
    walk nodes fuel 1188 = List.range' 1172 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1188).rule = .split 3 (27/32) 1186 1187 := by rfl
      simp only [walk, hr]
      rw [traversal_1186 f (by omega), traversal_1187 f (by omega)]
      change (List.range' 1172 15 ++ List.range' (1172+15) 1) ++
        [1172+(15+1)] = List.range' 1172 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1172) (n := 15+1)).symm

private theorem traversal_1189 (fuel : Nat) (hf : 1189 < fuel) :
    walk nodes fuel 1189 = List.range' 1189 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1189).rule = .bound .leftEnd 2 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1190 (fuel : Nat) (hf : 1190 < fuel) :
    walk nodes fuel 1190 = List.range' 1190 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1190).rule = .bound .leftEnd 3 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1191 (fuel : Nat) (hf : 1191 < fuel) :
    walk nodes fuel 1191 = List.range' 1191 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1191).rule = .bound .leftEnd 3 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1192 (fuel : Nat) (hf : 1192 < fuel) :
    walk nodes fuel 1192 = List.range' 1190 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1192).rule = .split 0 (1/80) 1190 1191 := by rfl
      simp only [walk, hr]
      rw [traversal_1190 f (by omega), traversal_1191 f (by omega)]
      change (List.range' 1190 1 ++ List.range' (1190+1) 1) ++
        [1190+(1+1)] = List.range' 1190 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1190) (n := 1+1)).symm

private theorem traversal_1193 (fuel : Nat) (hf : 1193 < fuel) :
    walk nodes fuel 1193 = List.range' 1189 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1193).rule = .split 3 (27/32) 1189 1192 := by rfl
      simp only [walk, hr]
      rw [traversal_1189 f (by omega), traversal_1192 f (by omega)]
      change (List.range' 1189 1 ++ List.range' (1189+1) 3) ++
        [1189+(1+3)] = List.range' 1189 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1189) (n := 1+3)).symm

private theorem traversal_1194 (fuel : Nat) (hf : 1194 < fuel) :
    walk nodes fuel 1194 = List.range' 1172 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1194).rule = .split 2 (279/128) 1188 1193 := by rfl
      simp only [walk, hr]
      rw [traversal_1188 f (by omega), traversal_1193 f (by omega)]
      change (List.range' 1172 17 ++ List.range' (1172+17) 5) ++
        [1172+(17+5)] = List.range' 1172 ((17+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1172) (n := 17+5)).symm

private theorem traversal_1195 (fuel : Nat) (hf : 1195 < fuel) :
    walk nodes fuel 1195 = List.range' 435 761 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1195).rule = .split 1 (75/32) 1171 1194 := by rfl
      simp only [walk, hr]
      rw [traversal_1171 f (by omega), traversal_1194 f (by omega)]
      change (List.range' 435 737 ++ List.range' (435+737) 23) ++
        [435+(737+23)] = List.range' 435 ((737+23)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 435) (n := 737+23)).symm

private theorem traversal_1196 (fuel : Nat) (hf : 1196 < fuel) :
    walk nodes fuel 1196 = List.range' 1196 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1196).rule = .bound .leftEnd 2 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1197 (fuel : Nat) (hf : 1197 < fuel) :
    walk nodes fuel 1197 = List.range' 1197 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1197).rule = .bound .leftEnd 1 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1198 (fuel : Nat) (hf : 1198 < fuel) :
    walk nodes fuel 1198 = List.range' 1196 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1198).rule = .split 3 (27/32) 1196 1197 := by rfl
      simp only [walk, hr]
      rw [traversal_1196 f (by omega), traversal_1197 f (by omega)]
      change (List.range' 1196 1 ++ List.range' (1196+1) 1) ++
        [1196+(1+1)] = List.range' 1196 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1196) (n := 1+1)).symm

private theorem traversal_1199 (fuel : Nat) (hf : 1199 < fuel) :
    walk nodes fuel 1199 = List.range' 1199 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1199).rule = .bound .leftEnd 3 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1200 (fuel : Nat) (hf : 1200 < fuel) :
    walk nodes fuel 1200 = List.range' 1196 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1200).rule = .split 2 (279/128) 1198 1199 := by rfl
      simp only [walk, hr]
      rw [traversal_1198 f (by omega), traversal_1199 f (by omega)]
      change (List.range' 1196 3 ++ List.range' (1196+3) 1) ++
        [1196+(3+1)] = List.range' 1196 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1196) (n := 3+1)).symm

private theorem traversal_1201 (fuel : Nat) (hf : 1201 < fuel) :
    walk nodes fuel 1201 = List.range' 1201 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1201).rule = .bound .leftEnd 3 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1202 (fuel : Nat) (hf : 1202 < fuel) :
    walk nodes fuel 1202 = List.range' 1196 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1202).rule = .split 1 (75/32) 1200 1201 := by rfl
      simp only [walk, hr]
      rw [traversal_1200 f (by omega), traversal_1201 f (by omega)]
      change (List.range' 1196 5 ++ List.range' (1196+5) 1) ++
        [1196+(5+1)] = List.range' 1196 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1196) (n := 5+1)).symm

theorem traversal_1203 (fuel : Nat) (hf : 1203 < fuel) :
    walk nodes fuel 1203 = List.range' 435 769 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1203).rule = .split 0 (1/40) 1195 1202 := by rfl
      simp only [walk, hr]
      rw [traversal_1195 f (by omega), traversal_1202 f (by omega)]
      change (List.range' 435 761 ++ List.range' (435+761) 7) ++
        [435+(761+7)] = List.range' 435 ((761+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 435) (n := 761+7)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
