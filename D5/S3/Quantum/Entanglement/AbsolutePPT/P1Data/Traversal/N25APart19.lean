/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart19
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart19
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart19.traversal_1321,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart19.traversal_1326,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart19.traversal_1327,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart19.traversal_1336,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart19.traversal_1337
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart00
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart03
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart05
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart06
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart18
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1272 (fuel : Nat) (hf : 1272 < fuel) :
    walk nodes fuel 1272 = List.range' 1266 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1272).rule = .split 0 (1/80) 1270 1271 := by rfl
      simp only [walk, hr]
      rw [traversal_1270 f (by omega), traversal_1271 f (by omega)]
      change (List.range' 1266 5 ++ List.range' (1266+5) 1) ++
        [1266+(5+1)] = List.range' 1266 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1266) (n := 5+1)).symm

private theorem traversal_1273 (fuel : Nat) (hf : 1273 < fuel) :
    walk nodes fuel 1273 = List.range' 1249 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1273).rule = .split 3 (33/32) 1265 1272 := by rfl
      simp only [walk, hr]
      rw [traversal_1265 f (by omega), traversal_1272 f (by omega)]
      change (List.range' 1249 17 ++ List.range' (1249+17) 7) ++
        [1249+(17+7)] = List.range' 1249 ((17+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1249) (n := 17+7)).symm

private theorem traversal_1274 (fuel : Nat) (hf : 1274 < fuel) :
    walk nodes fuel 1274 = List.range' 1274 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1274).rule = .bound .leftEnd 3 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1275 (fuel : Nat) (hf : 1275 < fuel) :
    walk nodes fuel 1275 = List.range' 1249 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1275).rule = .split 2 (317/128) 1273 1274 := by rfl
      simp only [walk, hr]
      rw [traversal_1273 f (by omega), traversal_1274 f (by omega)]
      change (List.range' 1249 25 ++ List.range' (1249+25) 1) ++
        [1249+(25+1)] = List.range' 1249 ((25+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1249) (n := 25+1)).symm

private theorem traversal_1276 (fuel : Nat) (hf : 1276 < fuel) :
    walk nodes fuel 1276 = List.range' 1276 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1276).rule = .bound .leftEnd 3 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1277 (fuel : Nat) (hf : 1277 < fuel) :
    walk nodes fuel 1277 = List.range' 1249 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1277).rule = .split 1 (75/32) 1275 1276 := by rfl
      simp only [walk, hr]
      rw [traversal_1275 f (by omega), traversal_1276 f (by omega)]
      change (List.range' 1249 27 ++ List.range' (1249+27) 1) ++
        [1249+(27+1)] = List.range' 1249 ((27+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1249) (n := 27+1)).symm

private theorem traversal_1278 (fuel : Nat) (hf : 1278 < fuel) :
    walk nodes fuel 1278 = List.range' 1278 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1278).rule = .bound .leftEnd 3 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1279 (fuel : Nat) (hf : 1279 < fuel) :
    walk nodes fuel 1279 = List.range' 1249 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1279).rule = .split 0 (1/40) 1277 1278 := by rfl
      simp only [walk, hr]
      rw [traversal_1277 f (by omega), traversal_1278 f (by omega)]
      change (List.range' 1249 29 ++ List.range' (1249+29) 1) ++
        [1249+(29+1)] = List.range' 1249 ((29+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1249) (n := 29+1)).symm

private theorem traversal_1280 (fuel : Nat) (hf : 1280 < fuel) :
    walk nodes fuel 1280 = List.range' 1228 53 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1280).rule = .split 3 (15/16) 1248 1279 := by rfl
      simp only [walk, hr]
      rw [traversal_1248 f (by omega), traversal_1279 f (by omega)]
      change (List.range' 1228 21 ++ List.range' (1228+21) 31) ++
        [1228+(21+31)] = List.range' 1228 ((21+31)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1228) (n := 21+31)).symm

private theorem traversal_1281 (fuel : Nat) (hf : 1281 < fuel) :
    walk nodes fuel 1281 = List.range' 435 847 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1281).rule = .split 2 (149/64) 1227 1280 := by rfl
      simp only [walk, hr]
      rw [traversal_1227 f (by omega), traversal_1280 f (by omega)]
      change (List.range' 435 793 ++ List.range' (435+793) 53) ++
        [435+(793+53)] = List.range' 435 ((793+53)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 435) (n := 793+53)).symm

private theorem traversal_1282 (fuel : Nat) (hf : 1282 < fuel) :
    walk nodes fuel 1282 = List.range' 398 885 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1282).rule = .split 1 (35/16) 434 1281 := by rfl
      simp only [walk, hr]
      rw [traversal_434 f (by omega), traversal_1281 f (by omega)]
      change (List.range' 398 37 ++ List.range' (398+37) 847) ++
        [398+(37+847)] = List.range' 398 ((37+847)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 398) (n := 37+847)).symm

private theorem traversal_1283 (fuel : Nat) (hf : 1283 < fuel) :
    walk nodes fuel 1283 = List.range' 1283 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1283).rule = .bound .leftEnd 8 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1284 (fuel : Nat) (hf : 1284 < fuel) :
    walk nodes fuel 1284 = List.range' 1284 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1284).rule = .bound .leftEnd 3 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1285 (fuel : Nat) (hf : 1285 < fuel) :
    walk nodes fuel 1285 = List.range' 1283 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1285).rule = .split 2 (149/64) 1283 1284 := by rfl
      simp only [walk, hr]
      rw [traversal_1283 f (by omega), traversal_1284 f (by omega)]
      change (List.range' 1283 1 ++ List.range' (1283+1) 1) ++
        [1283+(1+1)] = List.range' 1283 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1283) (n := 1+1)).symm

private theorem traversal_1286 (fuel : Nat) (hf : 1286 < fuel) :
    walk nodes fuel 1286 = List.range' 1286 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1286).rule = .bound .leftEnd 3 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1287 (fuel : Nat) (hf : 1287 < fuel) :
    walk nodes fuel 1287 = List.range' 1283 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1287).rule = .split 1 (35/16) 1285 1286 := by rfl
      simp only [walk, hr]
      rw [traversal_1285 f (by omega), traversal_1286 f (by omega)]
      change (List.range' 1283 3 ++ List.range' (1283+3) 1) ++
        [1283+(3+1)] = List.range' 1283 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1283) (n := 3+1)).symm

private theorem traversal_1288 (fuel : Nat) (hf : 1288 < fuel) :
    walk nodes fuel 1288 = List.range' 398 891 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1288).rule = .split 0 (1/20) 1282 1287 := by rfl
      simp only [walk, hr]
      rw [traversal_1282 f (by omega), traversal_1287 f (by omega)]
      change (List.range' 398 885 ++ List.range' (398+885) 5) ++
        [398+(885+5)] = List.range' 398 ((885+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 398) (n := 885+5)).symm

private theorem traversal_1289 (fuel : Nat) (hf : 1289 < fuel) :
    walk nodes fuel 1289 = List.range' 1289 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1289).rule = .bound .leftEnd 8 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1290 (fuel : Nat) (hf : 1290 < fuel) :
    walk nodes fuel 1290 = List.range' 1290 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1290).rule = .bound .leftEnd 8 (3713/8192) (288755/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1291 (fuel : Nat) (hf : 1291 < fuel) :
    walk nodes fuel 1291 = List.range' 1291 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1291).rule = .bound .leftEnd 8 (3713/8192) (288755/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1292 (fuel : Nat) (hf : 1292 < fuel) :
    walk nodes fuel 1292 = List.range' 1290 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1292).rule = .split 1 (65/32) 1290 1291 := by rfl
      simp only [walk, hr]
      rw [traversal_1290 f (by omega), traversal_1291 f (by omega)]
      change (List.range' 1290 1 ++ List.range' (1290+1) 1) ++
        [1290+(1+1)] = List.range' 1290 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1290) (n := 1+1)).symm

private theorem traversal_1293 (fuel : Nat) (hf : 1293 < fuel) :
    walk nodes fuel 1293 = List.range' 1293 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1293).rule = .bound .leftEnd 8 (3713/8192) (288755/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1294 (fuel : Nat) (hf : 1294 < fuel) :
    walk nodes fuel 1294 = List.range' 1294 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1294).rule = .bound .leftEnd 1 (3713/8192) (288755/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1295 (fuel : Nat) (hf : 1295 < fuel) :
    walk nodes fuel 1295 = List.range' 1293 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1295).rule = .split 1 (65/32) 1293 1294 := by rfl
      simp only [walk, hr]
      rw [traversal_1293 f (by omega), traversal_1294 f (by omega)]
      change (List.range' 1293 1 ++ List.range' (1293+1) 1) ++
        [1293+(1+1)] = List.range' 1293 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1293) (n := 1+1)).symm

private theorem traversal_1296 (fuel : Nat) (hf : 1296 < fuel) :
    walk nodes fuel 1296 = List.range' 1290 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1296).rule = .split 0 (1/40) 1292 1295 := by rfl
      simp only [walk, hr]
      rw [traversal_1292 f (by omega), traversal_1295 f (by omega)]
      change (List.range' 1290 3 ++ List.range' (1290+3) 3) ++
        [1290+(3+3)] = List.range' 1290 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1290) (n := 3+3)).symm

private theorem traversal_1297 (fuel : Nat) (hf : 1297 < fuel) :
    walk nodes fuel 1297 = List.range' 1297 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1297).rule = .bound .leftEnd 8 (27/64) (310343/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1298 (fuel : Nat) (hf : 1298 < fuel) :
    walk nodes fuel 1298 = List.range' 1298 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1298).rule = .bound .leftEnd 1 (27/64) (310343/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1299 (fuel : Nat) (hf : 1299 < fuel) :
    walk nodes fuel 1299 = List.range' 1297 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1299).rule = .split 1 (65/32) 1297 1298 := by rfl
      simp only [walk, hr]
      rw [traversal_1297 f (by omega), traversal_1298 f (by omega)]
      change (List.range' 1297 1 ++ List.range' (1297+1) 1) ++
        [1297+(1+1)] = List.range' 1297 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1297) (n := 1+1)).symm

private theorem traversal_1300 (fuel : Nat) (hf : 1300 < fuel) :
    walk nodes fuel 1300 = List.range' 1300 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1300).rule = .bound .leftEnd 1 (27/64) (310343/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1301 (fuel : Nat) (hf : 1301 < fuel) :
    walk nodes fuel 1301 = List.range' 1297 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1301).rule = .split 0 (1/40) 1299 1300 := by rfl
      simp only [walk, hr]
      rw [traversal_1299 f (by omega), traversal_1300 f (by omega)]
      change (List.range' 1297 3 ++ List.range' (1297+3) 1) ++
        [1297+(3+1)] = List.range' 1297 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1297) (n := 3+1)).symm

private theorem traversal_1302 (fuel : Nat) (hf : 1302 < fuel) :
    walk nodes fuel 1302 = List.range' 1290 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1302).rule = .split 3 (21/16) 1296 1301 := by rfl
      simp only [walk, hr]
      rw [traversal_1296 f (by omega), traversal_1301 f (by omega)]
      change (List.range' 1290 7 ++ List.range' (1290+7) 5) ++
        [1290+(7+5)] = List.range' 1290 ((7+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1290) (n := 7+5)).symm

private theorem traversal_1303 (fuel : Nat) (hf : 1303 < fuel) :
    walk nodes fuel 1303 = List.range' 1289 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1303).rule = .split 2 (149/64) 1289 1302 := by rfl
      simp only [walk, hr]
      rw [traversal_1289 f (by omega), traversal_1302 f (by omega)]
      change (List.range' 1289 1 ++ List.range' (1289+1) 13) ++
        [1289+(1+13)] = List.range' 1289 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1289) (n := 1+13)).symm

private theorem traversal_1304 (fuel : Nat) (hf : 1304 < fuel) :
    walk nodes fuel 1304 = List.range' 1304 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1304).rule = .bound .leftEnd 1 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1305 (fuel : Nat) (hf : 1305 < fuel) :
    walk nodes fuel 1305 = List.range' 1305 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1305).rule = .bound .leftEnd 3 (3713/8192) (288755/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1306 (fuel : Nat) (hf : 1306 < fuel) :
    walk nodes fuel 1306 = List.range' 1306 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1306).rule = .bound .leftEnd 1 (3713/8192) (288755/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1307 (fuel : Nat) (hf : 1307 < fuel) :
    walk nodes fuel 1307 = List.range' 1305 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1307).rule = .split 1 (75/32) 1305 1306 := by rfl
      simp only [walk, hr]
      rw [traversal_1305 f (by omega), traversal_1306 f (by omega)]
      change (List.range' 1305 1 ++ List.range' (1305+1) 1) ++
        [1305+(1+1)] = List.range' 1305 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1305) (n := 1+1)).symm

private theorem traversal_1308 (fuel : Nat) (hf : 1308 < fuel) :
    walk nodes fuel 1308 = List.range' 1308 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1308).rule = .bound .leftEnd 1 (3713/8192) (288755/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1309 (fuel : Nat) (hf : 1309 < fuel) :
    walk nodes fuel 1309 = List.range' 1305 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1309).rule = .split 0 (1/40) 1307 1308 := by rfl
      simp only [walk, hr]
      rw [traversal_1307 f (by omega), traversal_1308 f (by omega)]
      change (List.range' 1305 3 ++ List.range' (1305+3) 1) ++
        [1305+(3+1)] = List.range' 1305 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1305) (n := 3+1)).symm

private theorem traversal_1310 (fuel : Nat) (hf : 1310 < fuel) :
    walk nodes fuel 1310 = List.range' 1310 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1310).rule = .bound .leftEnd 1 (27/64) (310343/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1311 (fuel : Nat) (hf : 1311 < fuel) :
    walk nodes fuel 1311 = List.range' 1305 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1311).rule = .split 3 (21/16) 1309 1310 := by rfl
      simp only [walk, hr]
      rw [traversal_1309 f (by omega), traversal_1310 f (by omega)]
      change (List.range' 1305 5 ++ List.range' (1305+5) 1) ++
        [1305+(5+1)] = List.range' 1305 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1305) (n := 5+1)).symm

private theorem traversal_1312 (fuel : Nat) (hf : 1312 < fuel) :
    walk nodes fuel 1312 = List.range' 1304 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1312).rule = .split 2 (149/64) 1304 1311 := by rfl
      simp only [walk, hr]
      rw [traversal_1304 f (by omega), traversal_1311 f (by omega)]
      change (List.range' 1304 1 ++ List.range' (1304+1) 7) ++
        [1304+(1+7)] = List.range' 1304 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1304) (n := 1+7)).symm

private theorem traversal_1313 (fuel : Nat) (hf : 1313 < fuel) :
    walk nodes fuel 1313 = List.range' 1289 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1313).rule = .split 1 (35/16) 1303 1312 := by rfl
      simp only [walk, hr]
      rw [traversal_1303 f (by omega), traversal_1312 f (by omega)]
      change (List.range' 1289 15 ++ List.range' (1289+15) 9) ++
        [1289+(15+9)] = List.range' 1289 ((15+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1289) (n := 15+9)).symm

private theorem traversal_1314 (fuel : Nat) (hf : 1314 < fuel) :
    walk nodes fuel 1314 = List.range' 1314 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1314).rule = .bound .leftEnd 1 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1315 (fuel : Nat) (hf : 1315 < fuel) :
    walk nodes fuel 1315 = List.range' 1289 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1315).rule = .split 0 (1/20) 1313 1314 := by rfl
      simp only [walk, hr]
      rw [traversal_1313 f (by omega), traversal_1314 f (by omega)]
      change (List.range' 1289 25 ++ List.range' (1289+25) 1) ++
        [1289+(25+1)] = List.range' 1289 ((25+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1289) (n := 25+1)).symm

private theorem traversal_1316 (fuel : Nat) (hf : 1316 < fuel) :
    walk nodes fuel 1316 = List.range' 398 919 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1316).rule = .split 3 (9/8) 1288 1315 := by rfl
      simp only [walk, hr]
      rw [traversal_1288 f (by omega), traversal_1315 f (by omega)]
      change (List.range' 398 891 ++ List.range' (398+891) 27) ++
        [398+(891+27)] = List.range' 398 ((891+27)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 398) (n := 891+27)).symm

private theorem traversal_1317 (fuel : Nat) (hf : 1317 < fuel) :
    walk nodes fuel 1317 = List.range' 337 981 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1317).rule = .split 2 (65/32) 397 1316 := by rfl
      simp only [walk, hr]
      rw [traversal_397 f (by omega), traversal_1316 f (by omega)]
      change (List.range' 337 61 ++ List.range' (337+61) 919) ++
        [337+(61+919)] = List.range' 337 ((61+919)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 337) (n := 61+919)).symm

private theorem traversal_1318 (fuel : Nat) (hf : 1318 < fuel) :
    walk nodes fuel 1318 = List.range' 336 983 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1318).rule = .split 1 (15/8) 336 1317 := by rfl
      simp only [walk, hr]
      rw [traversal_336 f (by omega), traversal_1317 f (by omega)]
      change (List.range' 336 1 ++ List.range' (336+1) 981) ++
        [336+(1+981)] = List.range' 336 ((1+981)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 336) (n := 1+981)).symm

private theorem traversal_1319 (fuel : Nat) (hf : 1319 < fuel) :
    walk nodes fuel 1319 = List.range' 217 1103 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1319).rule = .split 3 (3/4) 335 1318 := by rfl
      simp only [walk, hr]
      rw [traversal_335 f (by omega), traversal_1318 f (by omega)]
      change (List.range' 217 119 ++ List.range' (217+119) 983) ++
        [217+(119+983)] = List.range' 217 ((119+983)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 217) (n := 119+983)).symm

private theorem traversal_1320 (fuel : Nat) (hf : 1320 < fuel) :
    walk nodes fuel 1320 = List.range' 2 1319 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1320).rule = .split 2 (23/16) 216 1319 := by rfl
      simp only [walk, hr]
      rw [traversal_216 f (by omega), traversal_1319 f (by omega)]
      change (List.range' 2 215 ++ List.range' (2+215) 1103) ++
        [2+(215+1103)] = List.range' 2 ((215+1103)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2) (n := 215+1103)).symm

theorem traversal_1321 (fuel : Nat) (hf : 1321 < fuel) :
    walk nodes fuel 1321 = List.range' 1 1321 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1321).rule = .split 1 (5/4) 1 1320 := by rfl
      simp only [walk, hr]
      rw [traversal_1 f (by omega), traversal_1320 f (by omega)]
      change (List.range' 1 1 ++ List.range' (1+1) 1319) ++
        [1+(1+1319)] = List.range' 1 ((1+1319)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1) (n := 1+1319)).symm

private theorem traversal_1322 (fuel : Nat) (hf : 1322 < fuel) :
    walk nodes fuel 1322 = List.range' 1322 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1322).rule = .infeasible 3 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1323 (fuel : Nat) (hf : 1323 < fuel) :
    walk nodes fuel 1323 = List.range' 1323 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1323).rule = .bound .leftEnd 8 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1324 (fuel : Nat) (hf : 1324 < fuel) :
    walk nodes fuel 1324 = List.range' 1324 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1324).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1325 (fuel : Nat) (hf : 1325 < fuel) :
    walk nodes fuel 1325 = List.range' 1323 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1325).rule = .split 3 (9/4) 1323 1324 := by rfl
      simp only [walk, hr]
      rw [traversal_1323 f (by omega), traversal_1324 f (by omega)]
      change (List.range' 1323 1 ++ List.range' (1323+1) 1) ++
        [1323+(1+1)] = List.range' 1323 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1323) (n := 1+1)).symm

theorem traversal_1326 (fuel : Nat) (hf : 1326 < fuel) :
    walk nodes fuel 1326 = List.range' 1322 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1326).rule = .split 2 (23/16) 1322 1325 := by rfl
      simp only [walk, hr]
      rw [traversal_1322 f (by omega), traversal_1325 f (by omega)]
      change (List.range' 1322 1 ++ List.range' (1322+1) 3) ++
        [1322+(1+3)] = List.range' 1322 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1322) (n := 1+3)).symm

theorem traversal_1327 (fuel : Nat) (hf : 1327 < fuel) :
    walk nodes fuel 1327 = List.range' 1327 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1327).rule = .infeasible 3 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1328 (fuel : Nat) (hf : 1328 < fuel) :
    walk nodes fuel 1328 = List.range' 1328 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1328).rule = .bound .leftEnd 1 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1329 (fuel : Nat) (hf : 1329 < fuel) :
    walk nodes fuel 1329 = List.range' 1329 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1329).rule = .bound .leftEnd 8 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1330 (fuel : Nat) (hf : 1330 < fuel) :
    walk nodes fuel 1330 = List.range' 1330 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1330).rule = .bound .leftEnd 8 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1331 (fuel : Nat) (hf : 1331 < fuel) :
    walk nodes fuel 1331 = List.range' 1331 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1331).rule = .bound .leftEnd 1 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1332 (fuel : Nat) (hf : 1332 < fuel) :
    walk nodes fuel 1332 = List.range' 1330 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1332).rule = .split 1 (25/16) 1330 1331 := by rfl
      simp only [walk, hr]
      rw [traversal_1330 f (by omega), traversal_1331 f (by omega)]
      change (List.range' 1330 1 ++ List.range' (1330+1) 1) ++
        [1330+(1+1)] = List.range' 1330 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1330) (n := 1+1)).symm

private theorem traversal_1333 (fuel : Nat) (hf : 1333 < fuel) :
    walk nodes fuel 1333 = List.range' 1333 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1333).rule = .bound .leftEnd 1 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1334 (fuel : Nat) (hf : 1334 < fuel) :
    walk nodes fuel 1334 = List.range' 1330 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1334).rule = .split 0 (1/20) 1332 1333 := by rfl
      simp only [walk, hr]
      rw [traversal_1332 f (by omega), traversal_1333 f (by omega)]
      change (List.range' 1330 3 ++ List.range' (1330+3) 1) ++
        [1330+(3+1)] = List.range' 1330 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1330) (n := 3+1)).symm

private theorem traversal_1335 (fuel : Nat) (hf : 1335 < fuel) :
    walk nodes fuel 1335 = List.range' 1329 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1335).rule = .split 3 (15/8) 1329 1334 := by rfl
      simp only [walk, hr]
      rw [traversal_1329 f (by omega), traversal_1334 f (by omega)]
      change (List.range' 1329 1 ++ List.range' (1329+1) 5) ++
        [1329+(1+5)] = List.range' 1329 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1329) (n := 1+5)).symm

theorem traversal_1336 (fuel : Nat) (hf : 1336 < fuel) :
    walk nodes fuel 1336 = List.range' 1328 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1336).rule = .split 2 (65/32) 1328 1335 := by rfl
      simp only [walk, hr]
      rw [traversal_1328 f (by omega), traversal_1335 f (by omega)]
      change (List.range' 1328 1 ++ List.range' (1328+1) 7) ++
        [1328+(1+7)] = List.range' 1328 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1328) (n := 1+7)).symm

theorem traversal_1337 (fuel : Nat) (hf : 1337 < fuel) :
    walk nodes fuel 1337 = List.range' 1337 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1337).rule = .bound .leftEnd 1 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
