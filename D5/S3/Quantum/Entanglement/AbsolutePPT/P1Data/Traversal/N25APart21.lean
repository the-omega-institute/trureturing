/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart21
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart21
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart21.traversal_1433,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart21.traversal_1438,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart21.traversal_1439,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart21.traversal_1442,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart21.traversal_1443,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart21.traversal_1462,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart21.traversal_1469,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart21.traversal_1470,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart21.traversal_1471,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart21.traversal_1472
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart20
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1405 (fuel : Nat) (hf : 1405 < fuel) :
    walk nodes fuel 1405 = List.range' 1405 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1405).rule = .bound .leftEnd 8 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1406 (fuel : Nat) (hf : 1406 < fuel) :
    walk nodes fuel 1406 = List.range' 1406 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1406).rule = .bound .leftEnd 6 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1407 (fuel : Nat) (hf : 1407 < fuel) :
    walk nodes fuel 1407 = List.range' 1407 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1407).rule = .bound .leftEnd 8 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1408 (fuel : Nat) (hf : 1408 < fuel) :
    walk nodes fuel 1408 = List.range' 1408 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1408).rule = .bound .leftEnd 8 (70081/196608) (735011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1409 (fuel : Nat) (hf : 1409 < fuel) :
    walk nodes fuel 1409 = List.range' 1409 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1409).rule = .bound .leftEnd 8 (33481/98304) (96165/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1410 (fuel : Nat) (hf : 1410 < fuel) :
    walk nodes fuel 1410 = List.range' 1410 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1410).rule = .bound .leftEnd 3 (33481/98304) (96165/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1411 (fuel : Nat) (hf : 1411 < fuel) :
    walk nodes fuel 1411 = List.range' 1409 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1411).rule = .split 0 (3/40) 1409 1410 := by rfl
      simp only [walk, hr]
      rw [traversal_1409 f (by omega), traversal_1410 f (by omega)]
      change (List.range' 1409 1 ++ List.range' (1409+1) 1) ++
        [1409+(1+1)] = List.range' 1409 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1409) (n := 1+1)).symm

private theorem traversal_1412 (fuel : Nat) (hf : 1412 < fuel) :
    walk nodes fuel 1412 = List.range' 1408 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1412).rule = .split 3 (33/16) 1408 1411 := by rfl
      simp only [walk, hr]
      rw [traversal_1408 f (by omega), traversal_1411 f (by omega)]
      change (List.range' 1408 1 ++ List.range' (1408+1) 3) ++
        [1408+(1+3)] = List.range' 1408 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1408) (n := 1+3)).symm

private theorem traversal_1413 (fuel : Nat) (hf : 1413 < fuel) :
    walk nodes fuel 1413 = List.range' 1407 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1413).rule = .split 2 (187/64) 1407 1412 := by rfl
      simp only [walk, hr]
      rw [traversal_1407 f (by omega), traversal_1412 f (by omega)]
      change (List.range' 1407 1 ++ List.range' (1407+1) 5) ++
        [1407+(1+5)] = List.range' 1407 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1407) (n := 1+5)).symm

private theorem traversal_1414 (fuel : Nat) (hf : 1414 < fuel) :
    walk nodes fuel 1414 = List.range' 1406 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1414).rule = .split 1 (15/16) 1406 1413 := by rfl
      simp only [walk, hr]
      rw [traversal_1406 f (by omega), traversal_1413 f (by omega)]
      change (List.range' 1406 1 ++ List.range' (1406+1) 7) ++
        [1406+(1+7)] = List.range' 1406 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1406) (n := 1+7)).symm

private theorem traversal_1415 (fuel : Nat) (hf : 1415 < fuel) :
    walk nodes fuel 1415 = List.range' 1405 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1415).rule = .split 0 (1/20) 1405 1414 := by rfl
      simp only [walk, hr]
      rw [traversal_1405 f (by omega), traversal_1414 f (by omega)]
      change (List.range' 1405 1 ++ List.range' (1405+1) 9) ++
        [1405+(1+9)] = List.range' 1405 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1405) (n := 1+9)).symm

private theorem traversal_1416 (fuel : Nat) (hf : 1416 < fuel) :
    walk nodes fuel 1416 = List.range' 1404 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1416).rule = .split 3 (15/8) 1404 1415 := by rfl
      simp only [walk, hr]
      rw [traversal_1404 f (by omega), traversal_1415 f (by omega)]
      change (List.range' 1404 1 ++ List.range' (1404+1) 11) ++
        [1404+(1+11)] = List.range' 1404 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1404) (n := 1+11)).symm

private theorem traversal_1417 (fuel : Nat) (hf : 1417 < fuel) :
    walk nodes fuel 1417 = List.range' 1417 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1417).rule = .bound .vertex 8 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1418 (fuel : Nat) (hf : 1418 < fuel) :
    walk nodes fuel 1418 = List.range' 1418 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1418).rule = .bound .vertex 8 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1419 (fuel : Nat) (hf : 1419 < fuel) :
    walk nodes fuel 1419 = List.range' 1419 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1419).rule = .bound .leftEnd 8 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1420 (fuel : Nat) (hf : 1420 < fuel) :
    walk nodes fuel 1420 = List.range' 1420 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1420).rule = .bound .vertex 8 (70081/196608) (735011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1421 (fuel : Nat) (hf : 1421 < fuel) :
    walk nodes fuel 1421 = List.range' 1421 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1421).rule = .bound .leftEnd 8 (33481/98304) (96165/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1422 (fuel : Nat) (hf : 1422 < fuel) :
    walk nodes fuel 1422 = List.range' 1422 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1422).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1423 (fuel : Nat) (hf : 1423 < fuel) :
    walk nodes fuel 1423 = List.range' 1421 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1423).rule = .split 0 (1/40) 1421 1422 := by rfl
      simp only [walk, hr]
      rw [traversal_1421 f (by omega), traversal_1422 f (by omega)]
      change (List.range' 1421 1 ++ List.range' (1421+1) 1) ++
        [1421+(1+1)] = List.range' 1421 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1421) (n := 1+1)).symm

private theorem traversal_1424 (fuel : Nat) (hf : 1424 < fuel) :
    walk nodes fuel 1424 = List.range' 1420 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1424).rule = .split 3 (33/16) 1420 1423 := by rfl
      simp only [walk, hr]
      rw [traversal_1420 f (by omega), traversal_1423 f (by omega)]
      change (List.range' 1420 1 ++ List.range' (1420+1) 3) ++
        [1420+(1+3)] = List.range' 1420 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1420) (n := 1+3)).symm

private theorem traversal_1425 (fuel : Nat) (hf : 1425 < fuel) :
    walk nodes fuel 1425 = List.range' 1419 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1425).rule = .split 2 (225/64) 1419 1424 := by rfl
      simp only [walk, hr]
      rw [traversal_1419 f (by omega), traversal_1424 f (by omega)]
      change (List.range' 1419 1 ++ List.range' (1419+1) 5) ++
        [1419+(1+5)] = List.range' 1419 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1419) (n := 1+5)).symm

private theorem traversal_1426 (fuel : Nat) (hf : 1426 < fuel) :
    walk nodes fuel 1426 = List.range' 1418 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1426).rule = .split 1 (15/16) 1418 1425 := by rfl
      simp only [walk, hr]
      rw [traversal_1418 f (by omega), traversal_1425 f (by omega)]
      change (List.range' 1418 1 ++ List.range' (1418+1) 7) ++
        [1418+(1+7)] = List.range' 1418 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1418) (n := 1+7)).symm

private theorem traversal_1427 (fuel : Nat) (hf : 1427 < fuel) :
    walk nodes fuel 1427 = List.range' 1427 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1427).rule = .bound .vertex 8 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1428 (fuel : Nat) (hf : 1428 < fuel) :
    walk nodes fuel 1428 = List.range' 1428 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1428).rule = .bound .vertex 3 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1429 (fuel : Nat) (hf : 1429 < fuel) :
    walk nodes fuel 1429 = List.range' 1427 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1429).rule = .split 1 (15/16) 1427 1428 := by rfl
      simp only [walk, hr]
      rw [traversal_1427 f (by omega), traversal_1428 f (by omega)]
      change (List.range' 1427 1 ++ List.range' (1427+1) 1) ++
        [1427+(1+1)] = List.range' 1427 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1427) (n := 1+1)).symm

private theorem traversal_1430 (fuel : Nat) (hf : 1430 < fuel) :
    walk nodes fuel 1430 = List.range' 1418 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1430).rule = .split 0 (1/20) 1426 1429 := by rfl
      simp only [walk, hr]
      rw [traversal_1426 f (by omega), traversal_1429 f (by omega)]
      change (List.range' 1418 9 ++ List.range' (1418+9) 3) ++
        [1418+(9+3)] = List.range' 1418 ((9+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1418) (n := 9+3)).symm

private theorem traversal_1431 (fuel : Nat) (hf : 1431 < fuel) :
    walk nodes fuel 1431 = List.range' 1417 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1431).rule = .split 3 (15/8) 1417 1430 := by rfl
      simp only [walk, hr]
      rw [traversal_1417 f (by omega), traversal_1430 f (by omega)]
      change (List.range' 1417 1 ++ List.range' (1417+1) 13) ++
        [1417+(1+13)] = List.range' 1417 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1417) (n := 1+13)).symm

private theorem traversal_1432 (fuel : Nat) (hf : 1432 < fuel) :
    walk nodes fuel 1432 = List.range' 1404 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1432).rule = .split 2 (103/32) 1416 1431 := by rfl
      simp only [walk, hr]
      rw [traversal_1416 f (by omega), traversal_1431 f (by omega)]
      change (List.range' 1404 13 ++ List.range' (1404+13) 15) ++
        [1404+(13+15)] = List.range' 1404 ((13+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1404) (n := 13+15)).symm

theorem traversal_1433 (fuel : Nat) (hf : 1433 < fuel) :
    walk nodes fuel 1433 = List.range' 1403 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1433).rule = .split 1 (5/8) 1403 1432 := by rfl
      simp only [walk, hr]
      rw [traversal_1403 f (by omega), traversal_1432 f (by omega)]
      change (List.range' 1403 1 ++ List.range' (1403+1) 29) ++
        [1403+(1+29)] = List.range' 1403 ((1+29)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1403) (n := 1+29)).symm

private theorem traversal_1434 (fuel : Nat) (hf : 1434 < fuel) :
    walk nodes fuel 1434 = List.range' 1434 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1434).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1435 (fuel : Nat) (hf : 1435 < fuel) :
    walk nodes fuel 1435 = List.range' 1435 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1435).rule = .bound .vertex 6 (126023/393216) (408363/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1436 (fuel : Nat) (hf : 1436 < fuel) :
    walk nodes fuel 1436 = List.range' 1436 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1436).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1437 (fuel : Nat) (hf : 1437 < fuel) :
    walk nodes fuel 1437 = List.range' 1435 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1437).rule = .split 3 (21/8) 1435 1436 := by rfl
      simp only [walk, hr]
      rw [traversal_1435 f (by omega), traversal_1436 f (by omega)]
      change (List.range' 1435 1 ++ List.range' (1435+1) 1) ++
        [1435+(1+1)] = List.range' 1435 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1435) (n := 1+1)).symm

theorem traversal_1438 (fuel : Nat) (hf : 1438 < fuel) :
    walk nodes fuel 1438 = List.range' 1434 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1438).rule = .split 2 (103/32) 1434 1437 := by rfl
      simp only [walk, hr]
      rw [traversal_1434 f (by omega), traversal_1437 f (by omega)]
      change (List.range' 1434 1 ++ List.range' (1434+1) 3) ++
        [1434+(1+3)] = List.range' 1434 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1434) (n := 1+3)).symm

theorem traversal_1439 (fuel : Nat) (hf : 1439 < fuel) :
    walk nodes fuel 1439 = List.range' 1439 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1439).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1440 (fuel : Nat) (hf : 1440 < fuel) :
    walk nodes fuel 1440 = List.range' 1440 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1440).rule = .bound .vertex 8 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1441 (fuel : Nat) (hf : 1441 < fuel) :
    walk nodes fuel 1441 = List.range' 1441 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1441).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1442 (fuel : Nat) (hf : 1442 < fuel) :
    walk nodes fuel 1442 = List.range' 1440 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1442).rule = .split 3 (39/16) 1440 1441 := by rfl
      simp only [walk, hr]
      rw [traversal_1440 f (by omega), traversal_1441 f (by omega)]
      change (List.range' 1440 1 ++ List.range' (1440+1) 1) ++
        [1440+(1+1)] = List.range' 1440 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1440) (n := 1+1)).symm

theorem traversal_1443 (fuel : Nat) (hf : 1443 < fuel) :
    walk nodes fuel 1443 = List.range' 1443 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1443).rule = .bound .vertex 8 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1444 (fuel : Nat) (hf : 1444 < fuel) :
    walk nodes fuel 1444 = List.range' 1444 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1444).rule = .bound .vertex 6 (15593/49152) (206563/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1445 (fuel : Nat) (hf : 1445 < fuel) :
    walk nodes fuel 1445 = List.range' 1445 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1445).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1446 (fuel : Nat) (hf : 1446 < fuel) :
    walk nodes fuel 1446 = List.range' 1444 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1446).rule = .split 3 (81/32) 1444 1445 := by rfl
      simp only [walk, hr]
      rw [traversal_1444 f (by omega), traversal_1445 f (by omega)]
      change (List.range' 1444 1 ++ List.range' (1444+1) 1) ++
        [1444+(1+1)] = List.range' 1444 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1444) (n := 1+1)).symm

private theorem traversal_1447 (fuel : Nat) (hf : 1447 < fuel) :
    walk nodes fuel 1447 = List.range' 1447 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1447).rule = .bound .vertex 6 (15593/49152) (206563/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1448 (fuel : Nat) (hf : 1448 < fuel) :
    walk nodes fuel 1448 = List.range' 1448 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1448).rule = .bound .rightEnd 6 (30613/98304) (841723/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1449 (fuel : Nat) (hf : 1449 < fuel) :
    walk nodes fuel 1449 = List.range' 1449 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1449).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1450 (fuel : Nat) (hf : 1450 < fuel) :
    walk nodes fuel 1450 = List.range' 1450 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1450).rule = .bound .rightEnd 6 (961/3072) (418985/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1451 (fuel : Nat) (hf : 1451 < fuel) :
    walk nodes fuel 1451 = List.range' 1451 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1451).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1452 (fuel : Nat) (hf : 1452 < fuel) :
    walk nodes fuel 1452 = List.range' 1450 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1452).rule = .split 3 (165/64) 1450 1451 := by rfl
      simp only [walk, hr]
      rw [traversal_1450 f (by omega), traversal_1451 f (by omega)]
      change (List.range' 1450 1 ++ List.range' (1450+1) 1) ++
        [1450+(1+1)] = List.range' 1450 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1450) (n := 1+1)).symm

private theorem traversal_1453 (fuel : Nat) (hf : 1453 < fuel) :
    walk nodes fuel 1453 = List.range' 1449 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1453).rule = .split 2 (957/256) 1449 1452 := by rfl
      simp only [walk, hr]
      rw [traversal_1449 f (by omega), traversal_1452 f (by omega)]
      change (List.range' 1449 1 ++ List.range' (1449+1) 3) ++
        [1449+(1+3)] = List.range' 1449 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1449) (n := 1+3)).symm

private theorem traversal_1454 (fuel : Nat) (hf : 1454 < fuel) :
    walk nodes fuel 1454 = List.range' 1448 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1454).rule = .split 1 (45/64) 1448 1453 := by rfl
      simp only [walk, hr]
      rw [traversal_1448 f (by omega), traversal_1453 f (by omega)]
      change (List.range' 1448 1 ++ List.range' (1448+1) 5) ++
        [1448+(1+5)] = List.range' 1448 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1448) (n := 1+5)).symm

private theorem traversal_1455 (fuel : Nat) (hf : 1455 < fuel) :
    walk nodes fuel 1455 = List.range' 1455 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1455).rule = .bound .rightEnd 6 (30613/98304) (841723/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1456 (fuel : Nat) (hf : 1456 < fuel) :
    walk nodes fuel 1456 = List.range' 1456 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1456).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1457 (fuel : Nat) (hf : 1457 < fuel) :
    walk nodes fuel 1457 = List.range' 1457 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1457).rule = .bound .rightEnd 3 (30613/98304) (841723/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1458 (fuel : Nat) (hf : 1458 < fuel) :
    walk nodes fuel 1458 = List.range' 1456 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1458).rule = .split 2 (957/256) 1456 1457 := by rfl
      simp only [walk, hr]
      rw [traversal_1456 f (by omega), traversal_1457 f (by omega)]
      change (List.range' 1456 1 ++ List.range' (1456+1) 1) ++
        [1456+(1+1)] = List.range' 1456 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1456) (n := 1+1)).symm

private theorem traversal_1459 (fuel : Nat) (hf : 1459 < fuel) :
    walk nodes fuel 1459 = List.range' 1455 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1459).rule = .split 1 (45/64) 1455 1458 := by rfl
      simp only [walk, hr]
      rw [traversal_1455 f (by omega), traversal_1458 f (by omega)]
      change (List.range' 1455 1 ++ List.range' (1455+1) 3) ++
        [1455+(1+3)] = List.range' 1455 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1455) (n := 1+3)).symm

private theorem traversal_1460 (fuel : Nat) (hf : 1460 < fuel) :
    walk nodes fuel 1460 = List.range' 1448 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1460).rule = .split 0 (1/80) 1454 1459 := by rfl
      simp only [walk, hr]
      rw [traversal_1454 f (by omega), traversal_1459 f (by omega)]
      change (List.range' 1448 7 ++ List.range' (1448+7) 5) ++
        [1448+(7+5)] = List.range' 1448 ((7+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1448) (n := 7+5)).symm

private theorem traversal_1461 (fuel : Nat) (hf : 1461 < fuel) :
    walk nodes fuel 1461 = List.range' 1447 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1461).rule = .split 3 (81/32) 1447 1460 := by rfl
      simp only [walk, hr]
      rw [traversal_1447 f (by omega), traversal_1460 f (by omega)]
      change (List.range' 1447 1 ++ List.range' (1447+1) 13) ++
        [1447+(1+13)] = List.range' 1447 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1447) (n := 1+13)).symm

theorem traversal_1462 (fuel : Nat) (hf : 1462 < fuel) :
    walk nodes fuel 1462 = List.range' 1444 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1462).rule = .split 2 (469/128) 1446 1461 := by rfl
      simp only [walk, hr]
      rw [traversal_1446 f (by omega), traversal_1461 f (by omega)]
      change (List.range' 1444 3 ++ List.range' (1444+3) 15) ++
        [1444+(3+15)] = List.range' 1444 ((3+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1444) (n := 3+15)).symm

private theorem traversal_1463 (fuel : Nat) (hf : 1463 < fuel) :
    walk nodes fuel 1463 = List.range' 1463 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1463).rule = .bound .leftEnd 8 (15593/49152) (206563/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1464 (fuel : Nat) (hf : 1464 < fuel) :
    walk nodes fuel 1464 = List.range' 1464 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1464).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1465 (fuel : Nat) (hf : 1465 < fuel) :
    walk nodes fuel 1465 = List.range' 1465 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1465).rule = .bound .leftEnd 8 (15667/49152) (205601/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1466 (fuel : Nat) (hf : 1466 < fuel) :
    walk nodes fuel 1466 = List.range' 1466 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1466).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1467 (fuel : Nat) (hf : 1467 < fuel) :
    walk nodes fuel 1467 = List.range' 1465 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1467).rule = .split 3 (159/64) 1465 1466 := by rfl
      simp only [walk, hr]
      rw [traversal_1465 f (by omega), traversal_1466 f (by omega)]
      change (List.range' 1465 1 ++ List.range' (1465+1) 1) ++
        [1465+(1+1)] = List.range' 1465 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1465) (n := 1+1)).symm

private theorem traversal_1468 (fuel : Nat) (hf : 1468 < fuel) :
    walk nodes fuel 1468 = List.range' 1464 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1468).rule = .split 2 (919/256) 1464 1467 := by rfl
      simp only [walk, hr]
      rw [traversal_1464 f (by omega), traversal_1467 f (by omega)]
      change (List.range' 1464 1 ++ List.range' (1464+1) 3) ++
        [1464+(1+3)] = List.range' 1464 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1464) (n := 1+3)).symm

theorem traversal_1469 (fuel : Nat) (hf : 1469 < fuel) :
    walk nodes fuel 1469 = List.range' 1463 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1469).rule = .split 1 (55/64) 1463 1468 := by rfl
      simp only [walk, hr]
      rw [traversal_1463 f (by omega), traversal_1468 f (by omega)]
      change (List.range' 1463 1 ++ List.range' (1463+1) 5) ++
        [1463+(1+5)] = List.range' 1463 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1463) (n := 1+5)).symm

theorem traversal_1470 (fuel : Nat) (hf : 1470 < fuel) :
    walk nodes fuel 1470 = List.range' 1470 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1470).rule = .bound .leftEnd 8 (15593/49152) (206563/262144) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1471 (fuel : Nat) (hf : 1471 < fuel) :
    walk nodes fuel 1471 = List.range' 1471 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1471).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1472 (fuel : Nat) (hf : 1472 < fuel) :
    walk nodes fuel 1472 = List.range' 1472 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1472).rule = .bound .leftEnd 3 (15593/49152) (206563/262144) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
