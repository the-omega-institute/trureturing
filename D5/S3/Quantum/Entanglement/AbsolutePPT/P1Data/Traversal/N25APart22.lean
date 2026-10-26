/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart22
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart22
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart22.traversal_1508,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart22.traversal_1523,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart22.traversal_1538
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart21
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1473 (fuel : Nat) (hf : 1473 < fuel) :
    walk nodes fuel 1473 = List.range' 1471 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1473).rule = .split 2 (919/256) 1471 1472 := by rfl
      simp only [walk, hr]
      rw [traversal_1471 f (by omega), traversal_1472 f (by omega)]
      change (List.range' 1471 1 ++ List.range' (1471+1) 1) ++
        [1471+(1+1)] = List.range' 1471 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1471) (n := 1+1)).symm

private theorem traversal_1474 (fuel : Nat) (hf : 1474 < fuel) :
    walk nodes fuel 1474 = List.range' 1470 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1474).rule = .split 1 (55/64) 1470 1473 := by rfl
      simp only [walk, hr]
      rw [traversal_1470 f (by omega), traversal_1473 f (by omega)]
      change (List.range' 1470 1 ++ List.range' (1470+1) 3) ++
        [1470+(1+3)] = List.range' 1470 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1470) (n := 1+3)).symm

private theorem traversal_1475 (fuel : Nat) (hf : 1475 < fuel) :
    walk nodes fuel 1475 = List.range' 1463 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1475).rule = .split 0 (1/80) 1469 1474 := by rfl
      simp only [walk, hr]
      rw [traversal_1469 f (by omega), traversal_1474 f (by omega)]
      change (List.range' 1463 7 ++ List.range' (1463+7) 5) ++
        [1463+(7+5)] = List.range' 1463 ((7+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1463) (n := 7+5)).symm

private theorem traversal_1476 (fuel : Nat) (hf : 1476 < fuel) :
    walk nodes fuel 1476 = List.range' 1476 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1476).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1477 (fuel : Nat) (hf : 1477 < fuel) :
    walk nodes fuel 1477 = List.range' 1463 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1477).rule = .split 3 (81/32) 1475 1476 := by rfl
      simp only [walk, hr]
      rw [traversal_1475 f (by omega), traversal_1476 f (by omega)]
      change (List.range' 1463 13 ++ List.range' (1463+13) 1) ++
        [1463+(13+1)] = List.range' 1463 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1463) (n := 13+1)).symm

private theorem traversal_1478 (fuel : Nat) (hf : 1478 < fuel) :
    walk nodes fuel 1478 = List.range' 1478 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1478).rule = .bound .vertex 8 (15593/49152) (206563/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1479 (fuel : Nat) (hf : 1479 < fuel) :
    walk nodes fuel 1479 = List.range' 1479 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1479).rule = .bound .leftEnd 8 (15667/49152) (205601/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1480 (fuel : Nat) (hf : 1480 < fuel) :
    walk nodes fuel 1480 = List.range' 1480 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1480).rule = .bound .leftEnd 3 (5173/16384) (103781/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1481 (fuel : Nat) (hf : 1481 < fuel) :
    walk nodes fuel 1481 = List.range' 1479 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1481).rule = .split 3 (159/64) 1479 1480 := by rfl
      simp only [walk, hr]
      rw [traversal_1479 f (by omega), traversal_1480 f (by omega)]
      change (List.range' 1479 1 ++ List.range' (1479+1) 1) ++
        [1479+(1+1)] = List.range' 1479 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1479) (n := 1+1)).symm

private theorem traversal_1482 (fuel : Nat) (hf : 1482 < fuel) :
    walk nodes fuel 1482 = List.range' 1482 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1482).rule = .bound .vertex 3 (15593/49152) (206563/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1483 (fuel : Nat) (hf : 1483 < fuel) :
    walk nodes fuel 1483 = List.range' 1479 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1483).rule = .split 2 (957/256) 1481 1482 := by rfl
      simp only [walk, hr]
      rw [traversal_1481 f (by omega), traversal_1482 f (by omega)]
      change (List.range' 1479 3 ++ List.range' (1479+3) 1) ++
        [1479+(3+1)] = List.range' 1479 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1479) (n := 3+1)).symm

private theorem traversal_1484 (fuel : Nat) (hf : 1484 < fuel) :
    walk nodes fuel 1484 = List.range' 1478 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1484).rule = .split 1 (55/64) 1478 1483 := by rfl
      simp only [walk, hr]
      rw [traversal_1478 f (by omega), traversal_1483 f (by omega)]
      change (List.range' 1478 1 ++ List.range' (1478+1) 5) ++
        [1478+(1+5)] = List.range' 1478 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1478) (n := 1+5)).symm

private theorem traversal_1485 (fuel : Nat) (hf : 1485 < fuel) :
    walk nodes fuel 1485 = List.range' 1485 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1485).rule = .bound .vertex 3 (15593/49152) (206563/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1486 (fuel : Nat) (hf : 1486 < fuel) :
    walk nodes fuel 1486 = List.range' 1478 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1486).rule = .split 0 (1/80) 1484 1485 := by rfl
      simp only [walk, hr]
      rw [traversal_1484 f (by omega), traversal_1485 f (by omega)]
      change (List.range' 1478 7 ++ List.range' (1478+7) 1) ++
        [1478+(7+1)] = List.range' 1478 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1478) (n := 7+1)).symm

private theorem traversal_1487 (fuel : Nat) (hf : 1487 < fuel) :
    walk nodes fuel 1487 = List.range' 1487 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1487).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1488 (fuel : Nat) (hf : 1488 < fuel) :
    walk nodes fuel 1488 = List.range' 1488 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1488).rule = .bound .rightEnd 8 (961/3072) (418985/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1489 (fuel : Nat) (hf : 1489 < fuel) :
    walk nodes fuel 1489 = List.range' 1489 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1489).rule = .bound .vertex 3 (961/3072) (418985/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1490 (fuel : Nat) (hf : 1490 < fuel) :
    walk nodes fuel 1490 = List.range' 1488 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1490).rule = .split 1 (105/128) 1488 1489 := by rfl
      simp only [walk, hr]
      rw [traversal_1488 f (by omega), traversal_1489 f (by omega)]
      change (List.range' 1488 1 ++ List.range' (1488+1) 1) ++
        [1488+(1+1)] = List.range' 1488 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1488) (n := 1+1)).symm

private theorem traversal_1491 (fuel : Nat) (hf : 1491 < fuel) :
    walk nodes fuel 1491 = List.range' 1491 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1491).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1492 (fuel : Nat) (hf : 1492 < fuel) :
    walk nodes fuel 1492 = List.range' 1488 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1492).rule = .split 0 (1/160) 1490 1491 := by rfl
      simp only [walk, hr]
      rw [traversal_1490 f (by omega), traversal_1491 f (by omega)]
      change (List.range' 1488 3 ++ List.range' (1488+3) 1) ++
        [1488+(3+1)] = List.range' 1488 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1488) (n := 3+1)).symm

private theorem traversal_1493 (fuel : Nat) (hf : 1493 < fuel) :
    walk nodes fuel 1493 = List.range' 1493 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1493).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1494 (fuel : Nat) (hf : 1494 < fuel) :
    walk nodes fuel 1494 = List.range' 1488 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1494).rule = .split 3 (165/64) 1492 1493 := by rfl
      simp only [walk, hr]
      rw [traversal_1492 f (by omega), traversal_1493 f (by omega)]
      change (List.range' 1488 5 ++ List.range' (1488+5) 1) ++
        [1488+(5+1)] = List.range' 1488 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1488) (n := 5+1)).symm

private theorem traversal_1495 (fuel : Nat) (hf : 1495 < fuel) :
    walk nodes fuel 1495 = List.range' 1487 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1495).rule = .split 2 (957/256) 1487 1494 := by rfl
      simp only [walk, hr]
      rw [traversal_1487 f (by omega), traversal_1494 f (by omega)]
      change (List.range' 1487 1 ++ List.range' (1487+1) 7) ++
        [1487+(1+7)] = List.range' 1487 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1487) (n := 1+7)).symm

private theorem traversal_1496 (fuel : Nat) (hf : 1496 < fuel) :
    walk nodes fuel 1496 = List.range' 1496 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1496).rule = .bound .vertex 3 (30613/98304) (841723/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1497 (fuel : Nat) (hf : 1497 < fuel) :
    walk nodes fuel 1497 = List.range' 1487 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1497).rule = .split 1 (55/64) 1495 1496 := by rfl
      simp only [walk, hr]
      rw [traversal_1495 f (by omega), traversal_1496 f (by omega)]
      change (List.range' 1487 9 ++ List.range' (1487+9) 1) ++
        [1487+(9+1)] = List.range' 1487 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1487) (n := 9+1)).symm

private theorem traversal_1498 (fuel : Nat) (hf : 1498 < fuel) :
    walk nodes fuel 1498 = List.range' 1498 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1498).rule = .bound .vertex 3 (30613/98304) (841723/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1499 (fuel : Nat) (hf : 1499 < fuel) :
    walk nodes fuel 1499 = List.range' 1487 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1499).rule = .split 0 (1/80) 1497 1498 := by rfl
      simp only [walk, hr]
      rw [traversal_1497 f (by omega), traversal_1498 f (by omega)]
      change (List.range' 1487 11 ++ List.range' (1487+11) 1) ++
        [1487+(11+1)] = List.range' 1487 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1487) (n := 11+1)).symm

private theorem traversal_1500 (fuel : Nat) (hf : 1500 < fuel) :
    walk nodes fuel 1500 = List.range' 1478 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1500).rule = .split 3 (81/32) 1486 1499 := by rfl
      simp only [walk, hr]
      rw [traversal_1486 f (by omega), traversal_1499 f (by omega)]
      change (List.range' 1478 9 ++ List.range' (1478+9) 13) ++
        [1478+(9+13)] = List.range' 1478 ((9+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1478) (n := 9+13)).symm

private theorem traversal_1501 (fuel : Nat) (hf : 1501 < fuel) :
    walk nodes fuel 1501 = List.range' 1463 39 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1501).rule = .split 2 (469/128) 1477 1500 := by rfl
      simp only [walk, hr]
      rw [traversal_1477 f (by omega), traversal_1500 f (by omega)]
      change (List.range' 1463 15 ++ List.range' (1463+15) 23) ++
        [1463+(15+23)] = List.range' 1463 ((15+23)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1463) (n := 15+23)).symm

private theorem traversal_1502 (fuel : Nat) (hf : 1502 < fuel) :
    walk nodes fuel 1502 = List.range' 1444 59 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1502).rule = .split 1 (25/32) 1462 1501 := by rfl
      simp only [walk, hr]
      rw [traversal_1462 f (by omega), traversal_1501 f (by omega)]
      change (List.range' 1444 19 ++ List.range' (1444+19) 39) ++
        [1444+(19+39)] = List.range' 1444 ((19+39)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1444) (n := 19+39)).symm

private theorem traversal_1503 (fuel : Nat) (hf : 1503 < fuel) :
    walk nodes fuel 1503 = List.range' 1503 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1503).rule = .bound .vertex 6 (61799/196608) (833701/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1504 (fuel : Nat) (hf : 1504 < fuel) :
    walk nodes fuel 1504 = List.range' 1504 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1504).rule = .bound .vertex 3 (61799/196608) (833701/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1505 (fuel : Nat) (hf : 1505 < fuel) :
    walk nodes fuel 1505 = List.range' 1503 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1505).rule = .split 1 (25/32) 1503 1504 := by rfl
      simp only [walk, hr]
      rw [traversal_1503 f (by omega), traversal_1504 f (by omega)]
      change (List.range' 1503 1 ++ List.range' (1503+1) 1) ++
        [1503+(1+1)] = List.range' 1503 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1503) (n := 1+1)).symm

private theorem traversal_1506 (fuel : Nat) (hf : 1506 < fuel) :
    walk nodes fuel 1506 = List.range' 1444 63 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1506).rule = .split 0 (1/40) 1502 1505 := by rfl
      simp only [walk, hr]
      rw [traversal_1502 f (by omega), traversal_1505 f (by omega)]
      change (List.range' 1444 59 ++ List.range' (1444+59) 3) ++
        [1444+(59+3)] = List.range' 1444 ((59+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1444) (n := 59+3)).symm

private theorem traversal_1507 (fuel : Nat) (hf : 1507 < fuel) :
    walk nodes fuel 1507 = List.range' 1443 65 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1507).rule = .split 3 (39/16) 1443 1506 := by rfl
      simp only [walk, hr]
      rw [traversal_1443 f (by omega), traversal_1506 f (by omega)]
      change (List.range' 1443 1 ++ List.range' (1443+1) 63) ++
        [1443+(1+63)] = List.range' 1443 ((1+63)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1443) (n := 1+63)).symm

theorem traversal_1508 (fuel : Nat) (hf : 1508 < fuel) :
    walk nodes fuel 1508 = List.range' 1440 69 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1508).rule = .split 2 (225/64) 1442 1507 := by rfl
      simp only [walk, hr]
      rw [traversal_1442 f (by omega), traversal_1507 f (by omega)]
      change (List.range' 1440 3 ++ List.range' (1440+3) 65) ++
        [1440+(3+65)] = List.range' 1440 ((3+65)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1440) (n := 3+65)).symm

private theorem traversal_1509 (fuel : Nat) (hf : 1509 < fuel) :
    walk nodes fuel 1509 = List.range' 1509 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1509).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1510 (fuel : Nat) (hf : 1510 < fuel) :
    walk nodes fuel 1510 = List.range' 1510 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1510).rule = .bound .leftEnd 8 (10811/32768) (99309/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1511 (fuel : Nat) (hf : 1511 < fuel) :
    walk nodes fuel 1511 = List.range' 1511 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1511).rule = .bound .leftEnd 8 (10597/32768) (405261/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1512 (fuel : Nat) (hf : 1512 < fuel) :
    walk nodes fuel 1512 = List.range' 1512 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1512).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1513 (fuel : Nat) (hf : 1513 < fuel) :
    walk nodes fuel 1513 = List.range' 1513 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1513).rule = .bound .leftEnd 8 (7987/24576) (806597/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1514 (fuel : Nat) (hf : 1514 < fuel) :
    walk nodes fuel 1514 = List.range' 1514 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1514).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1515 (fuel : Nat) (hf : 1515 < fuel) :
    walk nodes fuel 1515 = List.range' 1513 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1515).rule = .split 3 (153/64) 1513 1514 := by rfl
      simp only [walk, hr]
      rw [traversal_1513 f (by omega), traversal_1514 f (by omega)]
      change (List.range' 1513 1 ++ List.range' (1513+1) 1) ++
        [1513+(1+1)] = List.range' 1513 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1513) (n := 1+1)).symm

private theorem traversal_1516 (fuel : Nat) (hf : 1516 < fuel) :
    walk nodes fuel 1516 = List.range' 1512 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1516).rule = .split 2 (881/256) 1512 1515 := by rfl
      simp only [walk, hr]
      rw [traversal_1512 f (by omega), traversal_1515 f (by omega)]
      change (List.range' 1512 1 ++ List.range' (1512+1) 3) ++
        [1512+(1+3)] = List.range' 1512 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1512) (n := 1+3)).symm

private theorem traversal_1517 (fuel : Nat) (hf : 1517 < fuel) :
    walk nodes fuel 1517 = List.range' 1511 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1517).rule = .split 1 (65/64) 1511 1516 := by rfl
      simp only [walk, hr]
      rw [traversal_1511 f (by omega), traversal_1516 f (by omega)]
      change (List.range' 1511 1 ++ List.range' (1511+1) 5) ++
        [1511+(1+5)] = List.range' 1511 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1511) (n := 1+5)).symm

private theorem traversal_1518 (fuel : Nat) (hf : 1518 < fuel) :
    walk nodes fuel 1518 = List.range' 1518 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1518).rule = .bound .leftEnd 8 (10597/32768) (405261/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1519 (fuel : Nat) (hf : 1519 < fuel) :
    walk nodes fuel 1519 = List.range' 1519 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1519).rule = .bound .leftEnd 3 (10597/32768) (405261/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1520 (fuel : Nat) (hf : 1520 < fuel) :
    walk nodes fuel 1520 = List.range' 1518 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1520).rule = .split 1 (65/64) 1518 1519 := by rfl
      simp only [walk, hr]
      rw [traversal_1518 f (by omega), traversal_1519 f (by omega)]
      change (List.range' 1518 1 ++ List.range' (1518+1) 1) ++
        [1518+(1+1)] = List.range' 1518 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1518) (n := 1+1)).symm

private theorem traversal_1521 (fuel : Nat) (hf : 1521 < fuel) :
    walk nodes fuel 1521 = List.range' 1511 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1521).rule = .split 0 (1/80) 1517 1520 := by rfl
      simp only [walk, hr]
      rw [traversal_1517 f (by omega), traversal_1520 f (by omega)]
      change (List.range' 1511 7 ++ List.range' (1511+7) 3) ++
        [1511+(7+3)] = List.range' 1511 ((7+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1511) (n := 7+3)).symm

private theorem traversal_1522 (fuel : Nat) (hf : 1522 < fuel) :
    walk nodes fuel 1522 = List.range' 1510 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1522).rule = .split 3 (75/32) 1510 1521 := by rfl
      simp only [walk, hr]
      rw [traversal_1510 f (by omega), traversal_1521 f (by omega)]
      change (List.range' 1510 1 ++ List.range' (1510+1) 11) ++
        [1510+(1+11)] = List.range' 1510 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1510) (n := 1+11)).symm

theorem traversal_1523 (fuel : Nat) (hf : 1523 < fuel) :
    walk nodes fuel 1523 = List.range' 1509 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1523).rule = .split 2 (431/128) 1509 1522 := by rfl
      simp only [walk, hr]
      rw [traversal_1509 f (by omega), traversal_1522 f (by omega)]
      change (List.range' 1509 1 ++ List.range' (1509+1) 13) ++
        [1509+(1+13)] = List.range' 1509 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1509) (n := 1+13)).symm

private theorem traversal_1524 (fuel : Nat) (hf : 1524 < fuel) :
    walk nodes fuel 1524 = List.range' 1524 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1524).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1525 (fuel : Nat) (hf : 1525 < fuel) :
    walk nodes fuel 1525 = List.range' 1525 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1525).rule = .bound .leftEnd 8 (10811/32768) (99309/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1526 (fuel : Nat) (hf : 1526 < fuel) :
    walk nodes fuel 1526 = List.range' 1526 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1526).rule = .bound .leftEnd 3 (10811/32768) (99309/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1527 (fuel : Nat) (hf : 1527 < fuel) :
    walk nodes fuel 1527 = List.range' 1525 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1527).rule = .split 1 (75/64) 1525 1526 := by rfl
      simp only [walk, hr]
      rw [traversal_1525 f (by omega), traversal_1526 f (by omega)]
      change (List.range' 1525 1 ++ List.range' (1525+1) 1) ++
        [1525+(1+1)] = List.range' 1525 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1525) (n := 1+1)).symm

private theorem traversal_1528 (fuel : Nat) (hf : 1528 < fuel) :
    walk nodes fuel 1528 = List.range' 1528 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1528).rule = .bound .leftEnd 3 (10811/32768) (99309/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1529 (fuel : Nat) (hf : 1529 < fuel) :
    walk nodes fuel 1529 = List.range' 1525 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1529).rule = .split 0 (1/80) 1527 1528 := by rfl
      simp only [walk, hr]
      rw [traversal_1527 f (by omega), traversal_1528 f (by omega)]
      change (List.range' 1525 3 ++ List.range' (1525+3) 1) ++
        [1525+(3+1)] = List.range' 1525 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1525) (n := 3+1)).symm

private theorem traversal_1530 (fuel : Nat) (hf : 1530 < fuel) :
    walk nodes fuel 1530 = List.range' 1530 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1530).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1531 (fuel : Nat) (hf : 1531 < fuel) :
    walk nodes fuel 1531 = List.range' 1531 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1531).rule = .bound .leftEnd 3 (10597/32768) (405261/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1532 (fuel : Nat) (hf : 1532 < fuel) :
    walk nodes fuel 1532 = List.range' 1530 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1532).rule = .split 2 (881/256) 1530 1531 := by rfl
      simp only [walk, hr]
      rw [traversal_1530 f (by omega), traversal_1531 f (by omega)]
      change (List.range' 1530 1 ++ List.range' (1530+1) 1) ++
        [1530+(1+1)] = List.range' 1530 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1530) (n := 1+1)).symm

private theorem traversal_1533 (fuel : Nat) (hf : 1533 < fuel) :
    walk nodes fuel 1533 = List.range' 1533 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1533).rule = .bound .leftEnd 3 (10597/32768) (405261/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1534 (fuel : Nat) (hf : 1534 < fuel) :
    walk nodes fuel 1534 = List.range' 1530 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1534).rule = .split 1 (75/64) 1532 1533 := by rfl
      simp only [walk, hr]
      rw [traversal_1532 f (by omega), traversal_1533 f (by omega)]
      change (List.range' 1530 3 ++ List.range' (1530+3) 1) ++
        [1530+(3+1)] = List.range' 1530 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1530) (n := 3+1)).symm

private theorem traversal_1535 (fuel : Nat) (hf : 1535 < fuel) :
    walk nodes fuel 1535 = List.range' 1535 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1535).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1536 (fuel : Nat) (hf : 1536 < fuel) :
    walk nodes fuel 1536 = List.range' 1530 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1536).rule = .split 0 (1/80) 1534 1535 := by rfl
      simp only [walk, hr]
      rw [traversal_1534 f (by omega), traversal_1535 f (by omega)]
      change (List.range' 1530 5 ++ List.range' (1530+5) 1) ++
        [1530+(5+1)] = List.range' 1530 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1530) (n := 5+1)).symm

private theorem traversal_1537 (fuel : Nat) (hf : 1537 < fuel) :
    walk nodes fuel 1537 = List.range' 1525 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1537).rule = .split 3 (75/32) 1529 1536 := by rfl
      simp only [walk, hr]
      rw [traversal_1529 f (by omega), traversal_1536 f (by omega)]
      change (List.range' 1525 5 ++ List.range' (1525+5) 7) ++
        [1525+(5+7)] = List.range' 1525 ((5+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1525) (n := 5+7)).symm

theorem traversal_1538 (fuel : Nat) (hf : 1538 < fuel) :
    walk nodes fuel 1538 = List.range' 1524 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1538).rule = .split 2 (431/128) 1524 1537 := by rfl
      simp only [walk, hr]
      rw [traversal_1524 f (by omega), traversal_1537 f (by omega)]
      change (List.range' 1524 1 ++ List.range' (1524+1) 13) ++
        [1524+(1+13)] = List.range' 1524 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1524) (n := 1+13)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
