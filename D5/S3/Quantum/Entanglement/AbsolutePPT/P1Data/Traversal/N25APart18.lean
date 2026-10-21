/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart18
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart18
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart18.traversal_1227,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart18.traversal_1248,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart18.traversal_1265,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart18.traversal_1270,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart18.traversal_1271
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart17
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1204 (fuel : Nat) (hf : 1204 < fuel) :
    walk nodes fuel 1204 = List.range' 1204 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1204).rule = .bound .leftEnd 1 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1205 (fuel : Nat) (hf : 1205 < fuel) :
    walk nodes fuel 1205 = List.range' 1205 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1205).rule = .bound .leftEnd 8 (8259/16384) (519739/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1206 (fuel : Nat) (hf : 1206 < fuel) :
    walk nodes fuel 1206 = List.range' 1206 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1206).rule = .bound .leftEnd 1 (8259/16384) (519739/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1207 (fuel : Nat) (hf : 1207 < fuel) :
    walk nodes fuel 1207 = List.range' 1207 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1207).rule = .bound .leftEnd 1 (1567/3072) (513839/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1208 (fuel : Nat) (hf : 1208 < fuel) :
    walk nodes fuel 1208 = List.range' 1208 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1208).rule = .bound .leftEnd 3 (1567/3072) (513839/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1209 (fuel : Nat) (hf : 1209 < fuel) :
    walk nodes fuel 1209 = List.range' 1207 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1209).rule = .split 2 (1173/512) 1207 1208 := by rfl
      simp only [walk, hr]
      rw [traversal_1207 f (by omega), traversal_1208 f (by omega)]
      change (List.range' 1207 1 ++ List.range' (1207+1) 1) ++
        [1207+(1+1)] = List.range' 1207 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1207) (n := 1+1)).symm

private theorem traversal_1210 (fuel : Nat) (hf : 1210 < fuel) :
    walk nodes fuel 1210 = List.range' 1210 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1210).rule = .bound .leftEnd 1 (1567/3072) (513839/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1211 (fuel : Nat) (hf : 1211 < fuel) :
    walk nodes fuel 1211 = List.range' 1207 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1211).rule = .split 1 (295/128) 1209 1210 := by rfl
      simp only [walk, hr]
      rw [traversal_1209 f (by omega), traversal_1210 f (by omega)]
      change (List.range' 1207 3 ++ List.range' (1207+3) 1) ++
        [1207+(3+1)] = List.range' 1207 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1207) (n := 3+1)).symm

private theorem traversal_1212 (fuel : Nat) (hf : 1212 < fuel) :
    walk nodes fuel 1212 = List.range' 1212 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1212).rule = .bound .leftEnd 1 (1567/3072) (513839/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1213 (fuel : Nat) (hf : 1213 < fuel) :
    walk nodes fuel 1213 = List.range' 1207 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1213).rule = .split 0 (1/160) 1211 1212 := by rfl
      simp only [walk, hr]
      rw [traversal_1211 f (by omega), traversal_1212 f (by omega)]
      change (List.range' 1207 5 ++ List.range' (1207+5) 1) ++
        [1207+(5+1)] = List.range' 1207 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1207) (n := 5+1)).symm

private theorem traversal_1214 (fuel : Nat) (hf : 1214 < fuel) :
    walk nodes fuel 1214 = List.range' 1214 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1214).rule = .bound .leftEnd 1 (12241/24576) (526229/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1215 (fuel : Nat) (hf : 1215 < fuel) :
    walk nodes fuel 1215 = List.range' 1207 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1215).rule = .split 3 (63/64) 1213 1214 := by rfl
      simp only [walk, hr]
      rw [traversal_1213 f (by omega), traversal_1214 f (by omega)]
      change (List.range' 1207 7 ++ List.range' (1207+7) 1) ++
        [1207+(7+1)] = List.range' 1207 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1207) (n := 7+1)).symm

private theorem traversal_1216 (fuel : Nat) (hf : 1216 < fuel) :
    walk nodes fuel 1216 = List.range' 1206 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1216).rule = .split 2 (577/256) 1206 1215 := by rfl
      simp only [walk, hr]
      rw [traversal_1206 f (by omega), traversal_1215 f (by omega)]
      change (List.range' 1206 1 ++ List.range' (1206+1) 9) ++
        [1206+(1+9)] = List.range' 1206 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1206) (n := 1+9)).symm

private theorem traversal_1217 (fuel : Nat) (hf : 1217 < fuel) :
    walk nodes fuel 1217 = List.range' 1205 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1217).rule = .split 1 (145/64) 1205 1216 := by rfl
      simp only [walk, hr]
      rw [traversal_1205 f (by omega), traversal_1216 f (by omega)]
      change (List.range' 1205 1 ++ List.range' (1205+1) 11) ++
        [1205+(1+11)] = List.range' 1205 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1205) (n := 1+11)).symm

private theorem traversal_1218 (fuel : Nat) (hf : 1218 < fuel) :
    walk nodes fuel 1218 = List.range' 1218 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1218).rule = .bound .leftEnd 1 (8259/16384) (519739/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1219 (fuel : Nat) (hf : 1219 < fuel) :
    walk nodes fuel 1219 = List.range' 1205 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1219).rule = .split 0 (1/80) 1217 1218 := by rfl
      simp only [walk, hr]
      rw [traversal_1217 f (by omega), traversal_1218 f (by omega)]
      change (List.range' 1205 13 ++ List.range' (1205+13) 1) ++
        [1205+(13+1)] = List.range' 1205 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1205) (n := 13+1)).symm

private theorem traversal_1220 (fuel : Nat) (hf : 1220 < fuel) :
    walk nodes fuel 1220 = List.range' 1220 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1220).rule = .bound .leftEnd 1 (15783/32768) (271997/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1221 (fuel : Nat) (hf : 1221 < fuel) :
    walk nodes fuel 1221 = List.range' 1205 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1221).rule = .split 3 (33/32) 1219 1220 := by rfl
      simp only [walk, hr]
      rw [traversal_1219 f (by omega), traversal_1220 f (by omega)]
      change (List.range' 1205 15 ++ List.range' (1205+15) 1) ++
        [1205+(15+1)] = List.range' 1205 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1205) (n := 15+1)).symm

private theorem traversal_1222 (fuel : Nat) (hf : 1222 < fuel) :
    walk nodes fuel 1222 = List.range' 1204 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1222).rule = .split 2 (279/128) 1204 1221 := by rfl
      simp only [walk, hr]
      rw [traversal_1204 f (by omega), traversal_1221 f (by omega)]
      change (List.range' 1204 1 ++ List.range' (1204+1) 17) ++
        [1204+(1+17)] = List.range' 1204 ((1+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1204) (n := 1+17)).symm

private theorem traversal_1223 (fuel : Nat) (hf : 1223 < fuel) :
    walk nodes fuel 1223 = List.range' 1223 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1223).rule = .bound .leftEnd 1 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1224 (fuel : Nat) (hf : 1224 < fuel) :
    walk nodes fuel 1224 = List.range' 1204 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1224).rule = .split 1 (75/32) 1222 1223 := by rfl
      simp only [walk, hr]
      rw [traversal_1222 f (by omega), traversal_1223 f (by omega)]
      change (List.range' 1204 19 ++ List.range' (1204+19) 1) ++
        [1204+(19+1)] = List.range' 1204 ((19+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1204) (n := 19+1)).symm

private theorem traversal_1225 (fuel : Nat) (hf : 1225 < fuel) :
    walk nodes fuel 1225 = List.range' 1225 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1225).rule = .bound .leftEnd 1 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1226 (fuel : Nat) (hf : 1226 < fuel) :
    walk nodes fuel 1226 = List.range' 1204 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1226).rule = .split 0 (1/40) 1224 1225 := by rfl
      simp only [walk, hr]
      rw [traversal_1224 f (by omega), traversal_1225 f (by omega)]
      change (List.range' 1204 21 ++ List.range' (1204+21) 1) ++
        [1204+(21+1)] = List.range' 1204 ((21+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1204) (n := 21+1)).symm

theorem traversal_1227 (fuel : Nat) (hf : 1227 < fuel) :
    walk nodes fuel 1227 = List.range' 435 793 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1227).rule = .split 3 (15/16) 1203 1226 := by rfl
      simp only [walk, hr]
      rw [traversal_1203 f (by omega), traversal_1226 f (by omega)]
      change (List.range' 435 769 ++ List.range' (435+769) 23) ++
        [435+(769+23)] = List.range' 435 ((769+23)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 435) (n := 769+23)).symm

private theorem traversal_1228 (fuel : Nat) (hf : 1228 < fuel) :
    walk nodes fuel 1228 = List.range' 1228 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1228).rule = .bound .leftEnd 2 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1229 (fuel : Nat) (hf : 1229 < fuel) :
    walk nodes fuel 1229 = List.range' 1229 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1229).rule = .bound .leftEnd 2 (26393/49152) (61013/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1230 (fuel : Nat) (hf : 1230 < fuel) :
    walk nodes fuel 1230 = List.range' 1230 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1230).rule = .bound .leftEnd 8 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1231 (fuel : Nat) (hf : 1231 < fuel) :
    walk nodes fuel 1231 = List.range' 1231 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1231).rule = .bound .leftEnd 3 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1232 (fuel : Nat) (hf : 1232 < fuel) :
    walk nodes fuel 1232 = List.range' 1230 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1232).rule = .split 1 (285/128) 1230 1231 := by rfl
      simp only [walk, hr]
      rw [traversal_1230 f (by omega), traversal_1231 f (by omega)]
      change (List.range' 1230 1 ++ List.range' (1230+1) 1) ++
        [1230+(1+1)] = List.range' 1230 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1230) (n := 1+1)).symm

private theorem traversal_1233 (fuel : Nat) (hf : 1233 < fuel) :
    walk nodes fuel 1233 = List.range' 1233 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1233).rule = .bound .leftEnd 3 (6427/12288) (501119/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1234 (fuel : Nat) (hf : 1234 < fuel) :
    walk nodes fuel 1234 = List.range' 1230 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1234).rule = .split 0 (1/160) 1232 1233 := by rfl
      simp only [walk, hr]
      rw [traversal_1232 f (by omega), traversal_1233 f (by omega)]
      change (List.range' 1230 3 ++ List.range' (1230+3) 1) ++
        [1230+(3+1)] = List.range' 1230 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1230) (n := 3+1)).symm

private theorem traversal_1235 (fuel : Nat) (hf : 1235 < fuel) :
    walk nodes fuel 1235 = List.range' 1229 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1235).rule = .split 3 (57/64) 1229 1234 := by rfl
      simp only [walk, hr]
      rw [traversal_1229 f (by omega), traversal_1234 f (by omega)]
      change (List.range' 1229 1 ++ List.range' (1229+1) 5) ++
        [1229+(1+5)] = List.range' 1229 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1229) (n := 1+5)).symm

private theorem traversal_1236 (fuel : Nat) (hf : 1236 < fuel) :
    walk nodes fuel 1236 = List.range' 1236 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1236).rule = .bound .leftEnd 3 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1237 (fuel : Nat) (hf : 1237 < fuel) :
    walk nodes fuel 1237 = List.range' 1229 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1237).rule = .split 2 (615/256) 1235 1236 := by rfl
      simp only [walk, hr]
      rw [traversal_1235 f (by omega), traversal_1236 f (by omega)]
      change (List.range' 1229 7 ++ List.range' (1229+7) 1) ++
        [1229+(7+1)] = List.range' 1229 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1229) (n := 7+1)).symm

private theorem traversal_1238 (fuel : Nat) (hf : 1238 < fuel) :
    walk nodes fuel 1238 = List.range' 1238 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1238).rule = .bound .leftEnd 3 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1239 (fuel : Nat) (hf : 1239 < fuel) :
    walk nodes fuel 1239 = List.range' 1229 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1239).rule = .split 1 (145/64) 1237 1238 := by rfl
      simp only [walk, hr]
      rw [traversal_1237 f (by omega), traversal_1238 f (by omega)]
      change (List.range' 1229 9 ++ List.range' (1229+9) 1) ++
        [1229+(9+1)] = List.range' 1229 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1229) (n := 9+1)).symm

private theorem traversal_1240 (fuel : Nat) (hf : 1240 < fuel) :
    walk nodes fuel 1240 = List.range' 1240 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1240).rule = .bound .leftEnd 3 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1241 (fuel : Nat) (hf : 1241 < fuel) :
    walk nodes fuel 1241 = List.range' 1229 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1241).rule = .split 0 (1/80) 1239 1240 := by rfl
      simp only [walk, hr]
      rw [traversal_1239 f (by omega), traversal_1240 f (by omega)]
      change (List.range' 1229 11 ++ List.range' (1229+11) 1) ++
        [1229+(11+1)] = List.range' 1229 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1229) (n := 11+1)).symm

private theorem traversal_1242 (fuel : Nat) (hf : 1242 < fuel) :
    walk nodes fuel 1242 = List.range' 1228 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1242).rule = .split 3 (27/32) 1228 1241 := by rfl
      simp only [walk, hr]
      rw [traversal_1228 f (by omega), traversal_1241 f (by omega)]
      change (List.range' 1228 1 ++ List.range' (1228+1) 13) ++
        [1228+(1+13)] = List.range' 1228 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1228) (n := 1+13)).symm

private theorem traversal_1243 (fuel : Nat) (hf : 1243 < fuel) :
    walk nodes fuel 1243 = List.range' 1243 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1243).rule = .bound .leftEnd 2 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1244 (fuel : Nat) (hf : 1244 < fuel) :
    walk nodes fuel 1244 = List.range' 1228 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1244).rule = .split 2 (317/128) 1242 1243 := by rfl
      simp only [walk, hr]
      rw [traversal_1242 f (by omega), traversal_1243 f (by omega)]
      change (List.range' 1228 15 ++ List.range' (1228+15) 1) ++
        [1228+(15+1)] = List.range' 1228 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1228) (n := 15+1)).symm

private theorem traversal_1245 (fuel : Nat) (hf : 1245 < fuel) :
    walk nodes fuel 1245 = List.range' 1245 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1245).rule = .bound .leftEnd 2 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1246 (fuel : Nat) (hf : 1246 < fuel) :
    walk nodes fuel 1246 = List.range' 1228 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1246).rule = .split 1 (75/32) 1244 1245 := by rfl
      simp only [walk, hr]
      rw [traversal_1244 f (by omega), traversal_1245 f (by omega)]
      change (List.range' 1228 17 ++ List.range' (1228+17) 1) ++
        [1228+(17+1)] = List.range' 1228 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1228) (n := 17+1)).symm

private theorem traversal_1247 (fuel : Nat) (hf : 1247 < fuel) :
    walk nodes fuel 1247 = List.range' 1247 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1247).rule = .bound .leftEnd 2 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1248 (fuel : Nat) (hf : 1248 < fuel) :
    walk nodes fuel 1248 = List.range' 1228 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1248).rule = .split 0 (1/40) 1246 1247 := by rfl
      simp only [walk, hr]
      rw [traversal_1246 f (by omega), traversal_1247 f (by omega)]
      change (List.range' 1228 19 ++ List.range' (1228+19) 1) ++
        [1228+(19+1)] = List.range' 1228 ((19+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1228) (n := 19+1)).symm

private theorem traversal_1249 (fuel : Nat) (hf : 1249 < fuel) :
    walk nodes fuel 1249 = List.range' 1249 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1249).rule = .bound .leftEnd 8 (1567/3072) (513839/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1250 (fuel : Nat) (hf : 1250 < fuel) :
    walk nodes fuel 1250 = List.range' 1250 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1250).rule = .bound .leftEnd 3 (1567/3072) (513839/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1251 (fuel : Nat) (hf : 1251 < fuel) :
    walk nodes fuel 1251 = List.range' 1249 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1251).rule = .split 1 (285/128) 1249 1250 := by rfl
      simp only [walk, hr]
      rw [traversal_1249 f (by omega), traversal_1250 f (by omega)]
      change (List.range' 1249 1 ++ List.range' (1249+1) 1) ++
        [1249+(1+1)] = List.range' 1249 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1249) (n := 1+1)).symm

private theorem traversal_1252 (fuel : Nat) (hf : 1252 < fuel) :
    walk nodes fuel 1252 = List.range' 1252 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1252).rule = .bound .leftEnd 3 (1567/3072) (513839/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1253 (fuel : Nat) (hf : 1253 < fuel) :
    walk nodes fuel 1253 = List.range' 1249 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1253).rule = .split 0 (1/160) 1251 1252 := by rfl
      simp only [walk, hr]
      rw [traversal_1251 f (by omega), traversal_1252 f (by omega)]
      change (List.range' 1249 3 ++ List.range' (1249+3) 1) ++
        [1249+(3+1)] = List.range' 1249 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1249) (n := 3+1)).symm

private theorem traversal_1254 (fuel : Nat) (hf : 1254 < fuel) :
    walk nodes fuel 1254 = List.range' 1254 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1254).rule = .bound .leftEnd 8 (12241/24576) (526229/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1255 (fuel : Nat) (hf : 1255 < fuel) :
    walk nodes fuel 1255 = List.range' 1255 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1255).rule = .bound .leftEnd 3 (12241/24576) (526229/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1256 (fuel : Nat) (hf : 1256 < fuel) :
    walk nodes fuel 1256 = List.range' 1254 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1256).rule = .split 1 (285/128) 1254 1255 := by rfl
      simp only [walk, hr]
      rw [traversal_1254 f (by omega), traversal_1255 f (by omega)]
      change (List.range' 1254 1 ++ List.range' (1254+1) 1) ++
        [1254+(1+1)] = List.range' 1254 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1254) (n := 1+1)).symm

private theorem traversal_1257 (fuel : Nat) (hf : 1257 < fuel) :
    walk nodes fuel 1257 = List.range' 1257 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1257).rule = .bound .leftEnd 3 (12241/24576) (526229/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1258 (fuel : Nat) (hf : 1258 < fuel) :
    walk nodes fuel 1258 = List.range' 1254 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1258).rule = .split 0 (1/160) 1256 1257 := by rfl
      simp only [walk, hr]
      rw [traversal_1256 f (by omega), traversal_1257 f (by omega)]
      change (List.range' 1254 3 ++ List.range' (1254+3) 1) ++
        [1254+(3+1)] = List.range' 1254 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1254) (n := 3+1)).symm

private theorem traversal_1259 (fuel : Nat) (hf : 1259 < fuel) :
    walk nodes fuel 1259 = List.range' 1249 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1259).rule = .split 3 (63/64) 1253 1258 := by rfl
      simp only [walk, hr]
      rw [traversal_1253 f (by omega), traversal_1258 f (by omega)]
      change (List.range' 1249 5 ++ List.range' (1249+5) 5) ++
        [1249+(5+5)] = List.range' 1249 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1249) (n := 5+5)).symm

private theorem traversal_1260 (fuel : Nat) (hf : 1260 < fuel) :
    walk nodes fuel 1260 = List.range' 1260 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1260).rule = .bound .leftEnd 3 (8259/16384) (519739/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1261 (fuel : Nat) (hf : 1261 < fuel) :
    walk nodes fuel 1261 = List.range' 1249 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1261).rule = .split 2 (615/256) 1259 1260 := by rfl
      simp only [walk, hr]
      rw [traversal_1259 f (by omega), traversal_1260 f (by omega)]
      change (List.range' 1249 11 ++ List.range' (1249+11) 1) ++
        [1249+(11+1)] = List.range' 1249 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1249) (n := 11+1)).symm

private theorem traversal_1262 (fuel : Nat) (hf : 1262 < fuel) :
    walk nodes fuel 1262 = List.range' 1262 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1262).rule = .bound .leftEnd 3 (8259/16384) (519739/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1263 (fuel : Nat) (hf : 1263 < fuel) :
    walk nodes fuel 1263 = List.range' 1249 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1263).rule = .split 1 (145/64) 1261 1262 := by rfl
      simp only [walk, hr]
      rw [traversal_1261 f (by omega), traversal_1262 f (by omega)]
      change (List.range' 1249 13 ++ List.range' (1249+13) 1) ++
        [1249+(13+1)] = List.range' 1249 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1249) (n := 13+1)).symm

private theorem traversal_1264 (fuel : Nat) (hf : 1264 < fuel) :
    walk nodes fuel 1264 = List.range' 1264 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1264).rule = .bound .leftEnd 3 (8259/16384) (519739/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1265 (fuel : Nat) (hf : 1265 < fuel) :
    walk nodes fuel 1265 = List.range' 1249 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1265).rule = .split 0 (1/80) 1263 1264 := by rfl
      simp only [walk, hr]
      rw [traversal_1263 f (by omega), traversal_1264 f (by omega)]
      change (List.range' 1249 15 ++ List.range' (1249+15) 1) ++
        [1249+(15+1)] = List.range' 1249 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1249) (n := 15+1)).symm

private theorem traversal_1266 (fuel : Nat) (hf : 1266 < fuel) :
    walk nodes fuel 1266 = List.range' 1266 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1266).rule = .bound .leftEnd 1 (15783/32768) (271997/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1267 (fuel : Nat) (hf : 1267 < fuel) :
    walk nodes fuel 1267 = List.range' 1267 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1267).rule = .bound .leftEnd 3 (15783/32768) (271997/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1268 (fuel : Nat) (hf : 1268 < fuel) :
    walk nodes fuel 1268 = List.range' 1266 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1268).rule = .split 2 (615/256) 1266 1267 := by rfl
      simp only [walk, hr]
      rw [traversal_1266 f (by omega), traversal_1267 f (by omega)]
      change (List.range' 1266 1 ++ List.range' (1266+1) 1) ++
        [1266+(1+1)] = List.range' 1266 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1266) (n := 1+1)).symm

private theorem traversal_1269 (fuel : Nat) (hf : 1269 < fuel) :
    walk nodes fuel 1269 = List.range' 1269 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1269).rule = .bound .leftEnd 1 (15783/32768) (271997/524288) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1270 (fuel : Nat) (hf : 1270 < fuel) :
    walk nodes fuel 1270 = List.range' 1266 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1270).rule = .split 1 (145/64) 1268 1269 := by rfl
      simp only [walk, hr]
      rw [traversal_1268 f (by omega), traversal_1269 f (by omega)]
      change (List.range' 1266 3 ++ List.range' (1266+3) 1) ++
        [1266+(3+1)] = List.range' 1266 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1266) (n := 3+1)).symm

theorem traversal_1271 (fuel : Nat) (hf : 1271 < fuel) :
    walk nodes fuel 1271 = List.range' 1271 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1271).rule = .bound .leftEnd 1 (15783/32768) (271997/524288) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
