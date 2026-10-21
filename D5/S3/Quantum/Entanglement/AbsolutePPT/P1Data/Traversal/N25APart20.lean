/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart20
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart20
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart20.traversal_1343,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart20.traversal_1402,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart20.traversal_1403,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart20.traversal_1404
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart19
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1338 (fuel : Nat) (hf : 1338 < fuel) :
    walk nodes fuel 1338 = List.range' 1328 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1338).rule = .split 1 (15/8) 1336 1337 := by rfl
      simp only [walk, hr]
      rw [traversal_1336 f (by omega), traversal_1337 f (by omega)]
      change (List.range' 1328 9 ++ List.range' (1328+9) 1) ++
        [1328+(9+1)] = List.range' 1328 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1328) (n := 9+1)).symm

private theorem traversal_1339 (fuel : Nat) (hf : 1339 < fuel) :
    walk nodes fuel 1339 = List.range' 1339 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1339).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1340 (fuel : Nat) (hf : 1340 < fuel) :
    walk nodes fuel 1340 = List.range' 1328 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1340).rule = .split 3 (9/4) 1338 1339 := by rfl
      simp only [walk, hr]
      rw [traversal_1338 f (by omega), traversal_1339 f (by omega)]
      change (List.range' 1328 11 ++ List.range' (1328+11) 1) ++
        [1328+(11+1)] = List.range' 1328 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1328) (n := 11+1)).symm

private theorem traversal_1341 (fuel : Nat) (hf : 1341 < fuel) :
    walk nodes fuel 1341 = List.range' 1327 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1341).rule = .split 2 (23/16) 1327 1340 := by rfl
      simp only [walk, hr]
      rw [traversal_1327 f (by omega), traversal_1340 f (by omega)]
      change (List.range' 1327 1 ++ List.range' (1327+1) 13) ++
        [1327+(1+13)] = List.range' 1327 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1327) (n := 1+13)).symm

private theorem traversal_1342 (fuel : Nat) (hf : 1342 < fuel) :
    walk nodes fuel 1342 = List.range' 1322 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1342).rule = .split 1 (5/4) 1326 1341 := by rfl
      simp only [walk, hr]
      rw [traversal_1326 f (by omega), traversal_1341 f (by omega)]
      change (List.range' 1322 5 ++ List.range' (1322+5) 15) ++
        [1322+(5+15)] = List.range' 1322 ((5+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1322) (n := 5+15)).symm

theorem traversal_1343 (fuel : Nat) (hf : 1343 < fuel) :
    walk nodes fuel 1343 = List.range' 1 1343 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1343).rule = .split 3 (3/2) 1321 1342 := by rfl
      simp only [walk, hr]
      rw [traversal_1321 f (by omega), traversal_1342 f (by omega)]
      change (List.range' 1 1321 ++ List.range' (1+1321) 21) ++
        [1+(1321+21)] = List.range' 1 ((1321+21)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1) (n := 1321+21)).symm

private theorem traversal_1344 (fuel : Nat) (hf : 1344 < fuel) :
    walk nodes fuel 1344 = List.range' 1344 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1344).rule = .bound .vertex 8 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1345 (fuel : Nat) (hf : 1345 < fuel) :
    walk nodes fuel 1345 = List.range' 1345 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1345).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1346 (fuel : Nat) (hf : 1346 < fuel) :
    walk nodes fuel 1346 = List.range' 1346 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1346).rule = .bound .leftEnd 8 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1347 (fuel : Nat) (hf : 1347 < fuel) :
    walk nodes fuel 1347 = List.range' 1347 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1347).rule = .bound .leftEnd 8 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1348 (fuel : Nat) (hf : 1348 < fuel) :
    walk nodes fuel 1348 = List.range' 1348 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1348).rule = .bound .leftEnd 8 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1349 (fuel : Nat) (hf : 1349 < fuel) :
    walk nodes fuel 1349 = List.range' 1349 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1349).rule = .bound .leftEnd 3 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1350 (fuel : Nat) (hf : 1350 < fuel) :
    walk nodes fuel 1350 = List.range' 1348 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1350).rule = .split 1 (25/16) 1348 1349 := by rfl
      simp only [walk, hr]
      rw [traversal_1348 f (by omega), traversal_1349 f (by omega)]
      change (List.range' 1348 1 ++ List.range' (1348+1) 1) ++
        [1348+(1+1)] = List.range' 1348 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1348) (n := 1+1)).symm

private theorem traversal_1351 (fuel : Nat) (hf : 1351 < fuel) :
    walk nodes fuel 1351 = List.range' 1347 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1351).rule = .split 0 (1/20) 1347 1350 := by rfl
      simp only [walk, hr]
      rw [traversal_1347 f (by omega), traversal_1350 f (by omega)]
      change (List.range' 1347 1 ++ List.range' (1347+1) 3) ++
        [1347+(1+3)] = List.range' 1347 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1347) (n := 1+3)).symm

private theorem traversal_1352 (fuel : Nat) (hf : 1352 < fuel) :
    walk nodes fuel 1352 = List.range' 1346 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1352).rule = .split 3 (9/8) 1346 1351 := by rfl
      simp only [walk, hr]
      rw [traversal_1346 f (by omega), traversal_1351 f (by omega)]
      change (List.range' 1346 1 ++ List.range' (1346+1) 5) ++
        [1346+(1+5)] = List.range' 1346 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1346) (n := 1+5)).symm

private theorem traversal_1353 (fuel : Nat) (hf : 1353 < fuel) :
    walk nodes fuel 1353 = List.range' 1353 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1353).rule = .bound .leftEnd 8 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1354 (fuel : Nat) (hf : 1354 < fuel) :
    walk nodes fuel 1354 = List.range' 1354 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1354).rule = .bound .leftEnd 2 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1355 (fuel : Nat) (hf : 1355 < fuel) :
    walk nodes fuel 1355 = List.range' 1353 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1355).rule = .split 1 (25/16) 1353 1354 := by rfl
      simp only [walk, hr]
      rw [traversal_1353 f (by omega), traversal_1354 f (by omega)]
      change (List.range' 1353 1 ++ List.range' (1353+1) 1) ++
        [1353+(1+1)] = List.range' 1353 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1353) (n := 1+1)).symm

private theorem traversal_1356 (fuel : Nat) (hf : 1356 < fuel) :
    walk nodes fuel 1356 = List.range' 1356 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1356).rule = .bound .leftEnd 2 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1357 (fuel : Nat) (hf : 1357 < fuel) :
    walk nodes fuel 1357 = List.range' 1353 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1357).rule = .split 0 (1/20) 1355 1356 := by rfl
      simp only [walk, hr]
      rw [traversal_1355 f (by omega), traversal_1356 f (by omega)]
      change (List.range' 1353 3 ++ List.range' (1353+3) 1) ++
        [1353+(3+1)] = List.range' 1353 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1353) (n := 3+1)).symm

private theorem traversal_1358 (fuel : Nat) (hf : 1358 < fuel) :
    walk nodes fuel 1358 = List.range' 1358 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1358).rule = .bound .leftEnd 8 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1359 (fuel : Nat) (hf : 1359 < fuel) :
    walk nodes fuel 1359 = List.range' 1359 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1359).rule = .bound .leftEnd 3 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1360 (fuel : Nat) (hf : 1360 < fuel) :
    walk nodes fuel 1360 = List.range' 1358 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1360).rule = .split 1 (25/16) 1358 1359 := by rfl
      simp only [walk, hr]
      rw [traversal_1358 f (by omega), traversal_1359 f (by omega)]
      change (List.range' 1358 1 ++ List.range' (1358+1) 1) ++
        [1358+(1+1)] = List.range' 1358 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1358) (n := 1+1)).symm

private theorem traversal_1361 (fuel : Nat) (hf : 1361 < fuel) :
    walk nodes fuel 1361 = List.range' 1361 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1361).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1362 (fuel : Nat) (hf : 1362 < fuel) :
    walk nodes fuel 1362 = List.range' 1358 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1362).rule = .split 0 (1/20) 1360 1361 := by rfl
      simp only [walk, hr]
      rw [traversal_1360 f (by omega), traversal_1361 f (by omega)]
      change (List.range' 1358 3 ++ List.range' (1358+3) 1) ++
        [1358+(3+1)] = List.range' 1358 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1358) (n := 3+1)).symm

private theorem traversal_1363 (fuel : Nat) (hf : 1363 < fuel) :
    walk nodes fuel 1363 = List.range' 1353 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1363).rule = .split 3 (9/8) 1357 1362 := by rfl
      simp only [walk, hr]
      rw [traversal_1357 f (by omega), traversal_1362 f (by omega)]
      change (List.range' 1353 5 ++ List.range' (1353+5) 5) ++
        [1353+(5+5)] = List.range' 1353 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1353) (n := 5+5)).symm

private theorem traversal_1364 (fuel : Nat) (hf : 1364 < fuel) :
    walk nodes fuel 1364 = List.range' 1346 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1364).rule = .split 2 (103/32) 1352 1363 := by rfl
      simp only [walk, hr]
      rw [traversal_1352 f (by omega), traversal_1363 f (by omega)]
      change (List.range' 1346 7 ++ List.range' (1346+7) 11) ++
        [1346+(7+11)] = List.range' 1346 ((7+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1346) (n := 7+11)).symm

private theorem traversal_1365 (fuel : Nat) (hf : 1365 < fuel) :
    walk nodes fuel 1365 = List.range' 1365 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1365).rule = .bound .leftEnd 2 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1366 (fuel : Nat) (hf : 1366 < fuel) :
    walk nodes fuel 1366 = List.range' 1366 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1366).rule = .bound .leftEnd 8 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1367 (fuel : Nat) (hf : 1367 < fuel) :
    walk nodes fuel 1367 = List.range' 1367 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1367).rule = .bound .leftEnd 3 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1368 (fuel : Nat) (hf : 1368 < fuel) :
    walk nodes fuel 1368 = List.range' 1366 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1368).rule = .split 1 (65/32) 1366 1367 := by rfl
      simp only [walk, hr]
      rw [traversal_1366 f (by omega), traversal_1367 f (by omega)]
      change (List.range' 1366 1 ++ List.range' (1366+1) 1) ++
        [1366+(1+1)] = List.range' 1366 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1366) (n := 1+1)).symm

private theorem traversal_1369 (fuel : Nat) (hf : 1369 < fuel) :
    walk nodes fuel 1369 = List.range' 1369 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1369).rule = .bound .leftEnd 3 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1370 (fuel : Nat) (hf : 1370 < fuel) :
    walk nodes fuel 1370 = List.range' 1366 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1370).rule = .split 0 (1/40) 1368 1369 := by rfl
      simp only [walk, hr]
      rw [traversal_1368 f (by omega), traversal_1369 f (by omega)]
      change (List.range' 1366 3 ++ List.range' (1366+3) 1) ++
        [1366+(3+1)] = List.range' 1366 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1366) (n := 3+1)).symm

private theorem traversal_1371 (fuel : Nat) (hf : 1371 < fuel) :
    walk nodes fuel 1371 = List.range' 1365 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1371).rule = .split 3 (15/16) 1365 1370 := by rfl
      simp only [walk, hr]
      rw [traversal_1365 f (by omega), traversal_1370 f (by omega)]
      change (List.range' 1365 1 ++ List.range' (1365+1) 5) ++
        [1365+(1+5)] = List.range' 1365 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1365) (n := 1+5)).symm

private theorem traversal_1372 (fuel : Nat) (hf : 1372 < fuel) :
    walk nodes fuel 1372 = List.range' 1372 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1372).rule = .bound .leftEnd 3 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1373 (fuel : Nat) (hf : 1373 < fuel) :
    walk nodes fuel 1373 = List.range' 1365 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1373).rule = .split 2 (187/64) 1371 1372 := by rfl
      simp only [walk, hr]
      rw [traversal_1371 f (by omega), traversal_1372 f (by omega)]
      change (List.range' 1365 7 ++ List.range' (1365+7) 1) ++
        [1365+(7+1)] = List.range' 1365 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1365) (n := 7+1)).symm

private theorem traversal_1374 (fuel : Nat) (hf : 1374 < fuel) :
    walk nodes fuel 1374 = List.range' 1374 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1374).rule = .bound .leftEnd 3 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1375 (fuel : Nat) (hf : 1375 < fuel) :
    walk nodes fuel 1375 = List.range' 1365 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1375).rule = .split 1 (35/16) 1373 1374 := by rfl
      simp only [walk, hr]
      rw [traversal_1373 f (by omega), traversal_1374 f (by omega)]
      change (List.range' 1365 9 ++ List.range' (1365+9) 1) ++
        [1365+(9+1)] = List.range' 1365 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1365) (n := 9+1)).symm

private theorem traversal_1376 (fuel : Nat) (hf : 1376 < fuel) :
    walk nodes fuel 1376 = List.range' 1376 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1376).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1377 (fuel : Nat) (hf : 1377 < fuel) :
    walk nodes fuel 1377 = List.range' 1365 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1377).rule = .split 0 (1/20) 1375 1376 := by rfl
      simp only [walk, hr]
      rw [traversal_1375 f (by omega), traversal_1376 f (by omega)]
      change (List.range' 1365 11 ++ List.range' (1365+11) 1) ++
        [1365+(11+1)] = List.range' 1365 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1365) (n := 11+1)).symm

private theorem traversal_1378 (fuel : Nat) (hf : 1378 < fuel) :
    walk nodes fuel 1378 = List.range' 1378 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1378).rule = .bound .leftEnd 8 (3713/8192) (288755/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1379 (fuel : Nat) (hf : 1379 < fuel) :
    walk nodes fuel 1379 = List.range' 1379 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1379).rule = .bound .leftEnd 3 (3713/8192) (288755/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1380 (fuel : Nat) (hf : 1380 < fuel) :
    walk nodes fuel 1380 = List.range' 1378 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1380).rule = .split 1 (65/32) 1378 1379 := by rfl
      simp only [walk, hr]
      rw [traversal_1378 f (by omega), traversal_1379 f (by omega)]
      change (List.range' 1378 1 ++ List.range' (1378+1) 1) ++
        [1378+(1+1)] = List.range' 1378 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1378) (n := 1+1)).symm

private theorem traversal_1381 (fuel : Nat) (hf : 1381 < fuel) :
    walk nodes fuel 1381 = List.range' 1381 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1381).rule = .bound .leftEnd 3 (3713/8192) (288755/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1382 (fuel : Nat) (hf : 1382 < fuel) :
    walk nodes fuel 1382 = List.range' 1378 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1382).rule = .split 0 (1/40) 1380 1381 := by rfl
      simp only [walk, hr]
      rw [traversal_1380 f (by omega), traversal_1381 f (by omega)]
      change (List.range' 1378 3 ++ List.range' (1378+3) 1) ++
        [1378+(3+1)] = List.range' 1378 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1378) (n := 3+1)).symm

private theorem traversal_1383 (fuel : Nat) (hf : 1383 < fuel) :
    walk nodes fuel 1383 = List.range' 1383 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1383).rule = .bound .leftEnd 8 (27/64) (310343/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1384 (fuel : Nat) (hf : 1384 < fuel) :
    walk nodes fuel 1384 = List.range' 1384 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1384).rule = .bound .leftEnd 3 (27/64) (310343/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1385 (fuel : Nat) (hf : 1385 < fuel) :
    walk nodes fuel 1385 = List.range' 1383 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1385).rule = .split 1 (65/32) 1383 1384 := by rfl
      simp only [walk, hr]
      rw [traversal_1383 f (by omega), traversal_1384 f (by omega)]
      change (List.range' 1383 1 ++ List.range' (1383+1) 1) ++
        [1383+(1+1)] = List.range' 1383 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1383) (n := 1+1)).symm

private theorem traversal_1386 (fuel : Nat) (hf : 1386 < fuel) :
    walk nodes fuel 1386 = List.range' 1386 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1386).rule = .bound .leftEnd 3 (27/64) (310343/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1387 (fuel : Nat) (hf : 1387 < fuel) :
    walk nodes fuel 1387 = List.range' 1383 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1387).rule = .split 0 (1/40) 1385 1386 := by rfl
      simp only [walk, hr]
      rw [traversal_1385 f (by omega), traversal_1386 f (by omega)]
      change (List.range' 1383 3 ++ List.range' (1383+3) 1) ++
        [1383+(3+1)] = List.range' 1383 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1383) (n := 3+1)).symm

private theorem traversal_1388 (fuel : Nat) (hf : 1388 < fuel) :
    walk nodes fuel 1388 = List.range' 1378 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1388).rule = .split 3 (21/16) 1382 1387 := by rfl
      simp only [walk, hr]
      rw [traversal_1382 f (by omega), traversal_1387 f (by omega)]
      change (List.range' 1378 5 ++ List.range' (1378+5) 5) ++
        [1378+(5+5)] = List.range' 1378 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1378) (n := 5+5)).symm

private theorem traversal_1389 (fuel : Nat) (hf : 1389 < fuel) :
    walk nodes fuel 1389 = List.range' 1389 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1389).rule = .bound .leftEnd 3 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1390 (fuel : Nat) (hf : 1390 < fuel) :
    walk nodes fuel 1390 = List.range' 1378 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1390).rule = .split 2 (187/64) 1388 1389 := by rfl
      simp only [walk, hr]
      rw [traversal_1388 f (by omega), traversal_1389 f (by omega)]
      change (List.range' 1378 11 ++ List.range' (1378+11) 1) ++
        [1378+(11+1)] = List.range' 1378 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1378) (n := 11+1)).symm

private theorem traversal_1391 (fuel : Nat) (hf : 1391 < fuel) :
    walk nodes fuel 1391 = List.range' 1391 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1391).rule = .bound .leftEnd 3 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1392 (fuel : Nat) (hf : 1392 < fuel) :
    walk nodes fuel 1392 = List.range' 1378 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1392).rule = .split 1 (35/16) 1390 1391 := by rfl
      simp only [walk, hr]
      rw [traversal_1390 f (by omega), traversal_1391 f (by omega)]
      change (List.range' 1378 13 ++ List.range' (1378+13) 1) ++
        [1378+(13+1)] = List.range' 1378 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1378) (n := 13+1)).symm

private theorem traversal_1393 (fuel : Nat) (hf : 1393 < fuel) :
    walk nodes fuel 1393 = List.range' 1393 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1393).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1394 (fuel : Nat) (hf : 1394 < fuel) :
    walk nodes fuel 1394 = List.range' 1378 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1394).rule = .split 0 (1/20) 1392 1393 := by rfl
      simp only [walk, hr]
      rw [traversal_1392 f (by omega), traversal_1393 f (by omega)]
      change (List.range' 1378 15 ++ List.range' (1378+15) 1) ++
        [1378+(15+1)] = List.range' 1378 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1378) (n := 15+1)).symm

private theorem traversal_1395 (fuel : Nat) (hf : 1395 < fuel) :
    walk nodes fuel 1395 = List.range' 1365 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1395).rule = .split 3 (9/8) 1377 1394 := by rfl
      simp only [walk, hr]
      rw [traversal_1377 f (by omega), traversal_1394 f (by omega)]
      change (List.range' 1365 13 ++ List.range' (1365+13) 17) ++
        [1365+(13+17)] = List.range' 1365 ((13+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1365) (n := 13+17)).symm

private theorem traversal_1396 (fuel : Nat) (hf : 1396 < fuel) :
    walk nodes fuel 1396 = List.range' 1396 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1396).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1397 (fuel : Nat) (hf : 1397 < fuel) :
    walk nodes fuel 1397 = List.range' 1365 33 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1397).rule = .split 2 (103/32) 1395 1396 := by rfl
      simp only [walk, hr]
      rw [traversal_1395 f (by omega), traversal_1396 f (by omega)]
      change (List.range' 1365 31 ++ List.range' (1365+31) 1) ++
        [1365+(31+1)] = List.range' 1365 ((31+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1365) (n := 31+1)).symm

private theorem traversal_1398 (fuel : Nat) (hf : 1398 < fuel) :
    walk nodes fuel 1398 = List.range' 1346 53 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1398).rule = .split 1 (15/8) 1364 1397 := by rfl
      simp only [walk, hr]
      rw [traversal_1364 f (by omega), traversal_1397 f (by omega)]
      change (List.range' 1346 19 ++ List.range' (1346+19) 33) ++
        [1346+(19+33)] = List.range' 1346 ((19+33)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1346) (n := 19+33)).symm

private theorem traversal_1399 (fuel : Nat) (hf : 1399 < fuel) :
    walk nodes fuel 1399 = List.range' 1345 55 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1399).rule = .split 3 (3/4) 1345 1398 := by rfl
      simp only [walk, hr]
      rw [traversal_1345 f (by omega), traversal_1398 f (by omega)]
      change (List.range' 1345 1 ++ List.range' (1345+1) 53) ++
        [1345+(1+53)] = List.range' 1345 ((1+53)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1345) (n := 1+53)).symm

private theorem traversal_1400 (fuel : Nat) (hf : 1400 < fuel) :
    walk nodes fuel 1400 = List.range' 1400 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1400).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1401 (fuel : Nat) (hf : 1401 < fuel) :
    walk nodes fuel 1401 = List.range' 1345 57 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1401).rule = .split 2 (61/16) 1399 1400 := by rfl
      simp only [walk, hr]
      rw [traversal_1399 f (by omega), traversal_1400 f (by omega)]
      change (List.range' 1345 55 ++ List.range' (1345+55) 1) ++
        [1345+(55+1)] = List.range' 1345 ((55+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1345) (n := 55+1)).symm

theorem traversal_1402 (fuel : Nat) (hf : 1402 < fuel) :
    walk nodes fuel 1402 = List.range' 1344 59 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1402).rule = .split 1 (5/4) 1344 1401 := by rfl
      simp only [walk, hr]
      rw [traversal_1344 f (by omega), traversal_1401 f (by omega)]
      change (List.range' 1344 1 ++ List.range' (1344+1) 57) ++
        [1344+(1+57)] = List.range' 1344 ((1+57)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1344) (n := 1+57)).symm

theorem traversal_1403 (fuel : Nat) (hf : 1403 < fuel) :
    walk nodes fuel 1403 = List.range' 1403 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1403).rule = .bound .vertex 0 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1404 (fuel : Nat) (hf : 1404 < fuel) :
    walk nodes fuel 1404 = List.range' 1404 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1404).rule = .bound .leftEnd 8 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
