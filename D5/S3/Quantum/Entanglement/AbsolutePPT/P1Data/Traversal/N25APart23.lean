/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart23
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart23
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart23.traversal_1595,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart23.traversal_1596,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart23.traversal_1603,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart23.traversal_1604
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart21
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart22
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1539 (fuel : Nat) (hf : 1539 < fuel) :
    walk nodes fuel 1539 = List.range' 1509 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1539).rule = .split 1 (35/32) 1523 1538 := by rfl
      simp only [walk, hr]
      rw [traversal_1523 f (by omega), traversal_1538 f (by omega)]
      change (List.range' 1509 15 ++ List.range' (1509+15) 15) ++
        [1509+(15+15)] = List.range' 1509 ((15+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1509) (n := 15+15)).symm

private theorem traversal_1540 (fuel : Nat) (hf : 1540 < fuel) :
    walk nodes fuel 1540 = List.range' 1540 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1540).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1541 (fuel : Nat) (hf : 1541 < fuel) :
    walk nodes fuel 1541 = List.range' 1541 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1541).rule = .bound .leftEnd 3 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1542 (fuel : Nat) (hf : 1542 < fuel) :
    walk nodes fuel 1542 = List.range' 1540 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1542).rule = .split 2 (431/128) 1540 1541 := by rfl
      simp only [walk, hr]
      rw [traversal_1540 f (by omega), traversal_1541 f (by omega)]
      change (List.range' 1540 1 ++ List.range' (1540+1) 1) ++
        [1540+(1+1)] = List.range' 1540 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1540) (n := 1+1)).symm

private theorem traversal_1543 (fuel : Nat) (hf : 1543 < fuel) :
    walk nodes fuel 1543 = List.range' 1543 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1543).rule = .bound .leftEnd 3 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1544 (fuel : Nat) (hf : 1544 < fuel) :
    walk nodes fuel 1544 = List.range' 1540 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1544).rule = .split 1 (35/32) 1542 1543 := by rfl
      simp only [walk, hr]
      rw [traversal_1542 f (by omega), traversal_1543 f (by omega)]
      change (List.range' 1540 3 ++ List.range' (1540+3) 1) ++
        [1540+(3+1)] = List.range' 1540 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1540) (n := 3+1)).symm

private theorem traversal_1545 (fuel : Nat) (hf : 1545 < fuel) :
    walk nodes fuel 1545 = List.range' 1509 37 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1545).rule = .split 0 (1/40) 1539 1544 := by rfl
      simp only [walk, hr]
      rw [traversal_1539 f (by omega), traversal_1544 f (by omega)]
      change (List.range' 1509 31 ++ List.range' (1509+31) 5) ++
        [1509+(31+5)] = List.range' 1509 ((31+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1509) (n := 31+5)).symm

private theorem traversal_1546 (fuel : Nat) (hf : 1546 < fuel) :
    walk nodes fuel 1546 = List.range' 1546 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1546).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1547 (fuel : Nat) (hf : 1547 < fuel) :
    walk nodes fuel 1547 = List.range' 1509 39 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1547).rule = .split 3 (39/16) 1545 1546 := by rfl
      simp only [walk, hr]
      rw [traversal_1545 f (by omega), traversal_1546 f (by omega)]
      change (List.range' 1509 37 ++ List.range' (1509+37) 1) ++
        [1509+(37+1)] = List.range' 1509 ((37+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1509) (n := 37+1)).symm

private theorem traversal_1548 (fuel : Nat) (hf : 1548 < fuel) :
    walk nodes fuel 1548 = List.range' 1548 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1548).rule = .bound .leftEnd 8 (10811/32768) (99309/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1549 (fuel : Nat) (hf : 1549 < fuel) :
    walk nodes fuel 1549 = List.range' 1549 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1549).rule = .bound .leftEnd 8 (10597/32768) (405261/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1550 (fuel : Nat) (hf : 1550 < fuel) :
    walk nodes fuel 1550 = List.range' 1550 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1550).rule = .bound .leftEnd 3 (10597/32768) (405261/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1551 (fuel : Nat) (hf : 1551 < fuel) :
    walk nodes fuel 1551 = List.range' 1549 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1551).rule = .split 1 (65/64) 1549 1550 := by rfl
      simp only [walk, hr]
      rw [traversal_1549 f (by omega), traversal_1550 f (by omega)]
      change (List.range' 1549 1 ++ List.range' (1549+1) 1) ++
        [1549+(1+1)] = List.range' 1549 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1549) (n := 1+1)).symm

private theorem traversal_1552 (fuel : Nat) (hf : 1552 < fuel) :
    walk nodes fuel 1552 = List.range' 1552 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1552).rule = .bound .leftEnd 3 (10597/32768) (405261/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1553 (fuel : Nat) (hf : 1553 < fuel) :
    walk nodes fuel 1553 = List.range' 1549 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1553).rule = .split 0 (1/80) 1551 1552 := by rfl
      simp only [walk, hr]
      rw [traversal_1551 f (by omega), traversal_1552 f (by omega)]
      change (List.range' 1549 3 ++ List.range' (1549+3) 1) ++
        [1549+(3+1)] = List.range' 1549 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1549) (n := 3+1)).symm

private theorem traversal_1554 (fuel : Nat) (hf : 1554 < fuel) :
    walk nodes fuel 1554 = List.range' 1548 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1554).rule = .split 3 (75/32) 1548 1553 := by rfl
      simp only [walk, hr]
      rw [traversal_1548 f (by omega), traversal_1553 f (by omega)]
      change (List.range' 1548 1 ++ List.range' (1548+1) 5) ++
        [1548+(1+5)] = List.range' 1548 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1548) (n := 1+5)).symm

private theorem traversal_1555 (fuel : Nat) (hf : 1555 < fuel) :
    walk nodes fuel 1555 = List.range' 1555 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1555).rule = .bound .leftEnd 3 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1556 (fuel : Nat) (hf : 1556 < fuel) :
    walk nodes fuel 1556 = List.range' 1548 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1556).rule = .split 2 (469/128) 1554 1555 := by rfl
      simp only [walk, hr]
      rw [traversal_1554 f (by omega), traversal_1555 f (by omega)]
      change (List.range' 1548 7 ++ List.range' (1548+7) 1) ++
        [1548+(7+1)] = List.range' 1548 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1548) (n := 7+1)).symm

private theorem traversal_1557 (fuel : Nat) (hf : 1557 < fuel) :
    walk nodes fuel 1557 = List.range' 1557 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1557).rule = .bound .leftEnd 3 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1558 (fuel : Nat) (hf : 1558 < fuel) :
    walk nodes fuel 1558 = List.range' 1548 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1558).rule = .split 1 (35/32) 1556 1557 := by rfl
      simp only [walk, hr]
      rw [traversal_1556 f (by omega), traversal_1557 f (by omega)]
      change (List.range' 1548 9 ++ List.range' (1548+9) 1) ++
        [1548+(9+1)] = List.range' 1548 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1548) (n := 9+1)).symm

private theorem traversal_1559 (fuel : Nat) (hf : 1559 < fuel) :
    walk nodes fuel 1559 = List.range' 1559 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1559).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1560 (fuel : Nat) (hf : 1560 < fuel) :
    walk nodes fuel 1560 = List.range' 1548 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1560).rule = .split 0 (1/40) 1558 1559 := by rfl
      simp only [walk, hr]
      rw [traversal_1558 f (by omega), traversal_1559 f (by omega)]
      change (List.range' 1548 11 ++ List.range' (1548+11) 1) ++
        [1548+(11+1)] = List.range' 1548 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1548) (n := 11+1)).symm

private theorem traversal_1561 (fuel : Nat) (hf : 1561 < fuel) :
    walk nodes fuel 1561 = List.range' 1561 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1561).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1562 (fuel : Nat) (hf : 1562 < fuel) :
    walk nodes fuel 1562 = List.range' 1562 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1562).rule = .bound .leftEnd 3 (15593/49152) (206563/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1563 (fuel : Nat) (hf : 1563 < fuel) :
    walk nodes fuel 1563 = List.range' 1561 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1563).rule = .split 2 (919/256) 1561 1562 := by rfl
      simp only [walk, hr]
      rw [traversal_1561 f (by omega), traversal_1562 f (by omega)]
      change (List.range' 1561 1 ++ List.range' (1561+1) 1) ++
        [1561+(1+1)] = List.range' 1561 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1561) (n := 1+1)).symm

private theorem traversal_1564 (fuel : Nat) (hf : 1564 < fuel) :
    walk nodes fuel 1564 = List.range' 1564 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1564).rule = .bound .leftEnd 3 (15593/49152) (206563/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1565 (fuel : Nat) (hf : 1565 < fuel) :
    walk nodes fuel 1565 = List.range' 1561 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1565).rule = .split 1 (65/64) 1563 1564 := by rfl
      simp only [walk, hr]
      rw [traversal_1563 f (by omega), traversal_1564 f (by omega)]
      change (List.range' 1561 3 ++ List.range' (1561+3) 1) ++
        [1561+(3+1)] = List.range' 1561 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1561) (n := 3+1)).symm

private theorem traversal_1566 (fuel : Nat) (hf : 1566 < fuel) :
    walk nodes fuel 1566 = List.range' 1566 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1566).rule = .bound .leftEnd 3 (15593/49152) (206563/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1567 (fuel : Nat) (hf : 1567 < fuel) :
    walk nodes fuel 1567 = List.range' 1561 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1567).rule = .split 0 (1/80) 1565 1566 := by rfl
      simp only [walk, hr]
      rw [traversal_1565 f (by omega), traversal_1566 f (by omega)]
      change (List.range' 1561 5 ++ List.range' (1561+5) 1) ++
        [1561+(5+1)] = List.range' 1561 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1561) (n := 5+1)).symm

private theorem traversal_1568 (fuel : Nat) (hf : 1568 < fuel) :
    walk nodes fuel 1568 = List.range' 1568 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1568).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1569 (fuel : Nat) (hf : 1569 < fuel) :
    walk nodes fuel 1569 = List.range' 1561 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1569).rule = .split 3 (81/32) 1567 1568 := by rfl
      simp only [walk, hr]
      rw [traversal_1567 f (by omega), traversal_1568 f (by omega)]
      change (List.range' 1561 7 ++ List.range' (1561+7) 1) ++
        [1561+(7+1)] = List.range' 1561 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1561) (n := 7+1)).symm

private theorem traversal_1570 (fuel : Nat) (hf : 1570 < fuel) :
    walk nodes fuel 1570 = List.range' 1570 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1570).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1571 (fuel : Nat) (hf : 1571 < fuel) :
    walk nodes fuel 1571 = List.range' 1561 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1571).rule = .split 2 (469/128) 1569 1570 := by rfl
      simp only [walk, hr]
      rw [traversal_1569 f (by omega), traversal_1570 f (by omega)]
      change (List.range' 1561 9 ++ List.range' (1561+9) 1) ++
        [1561+(9+1)] = List.range' 1561 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1561) (n := 9+1)).symm

private theorem traversal_1572 (fuel : Nat) (hf : 1572 < fuel) :
    walk nodes fuel 1572 = List.range' 1572 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1572).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1573 (fuel : Nat) (hf : 1573 < fuel) :
    walk nodes fuel 1573 = List.range' 1561 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1573).rule = .split 1 (35/32) 1571 1572 := by rfl
      simp only [walk, hr]
      rw [traversal_1571 f (by omega), traversal_1572 f (by omega)]
      change (List.range' 1561 11 ++ List.range' (1561+11) 1) ++
        [1561+(11+1)] = List.range' 1561 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1561) (n := 11+1)).symm

private theorem traversal_1574 (fuel : Nat) (hf : 1574 < fuel) :
    walk nodes fuel 1574 = List.range' 1574 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1574).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1575 (fuel : Nat) (hf : 1575 < fuel) :
    walk nodes fuel 1575 = List.range' 1561 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1575).rule = .split 0 (1/40) 1573 1574 := by rfl
      simp only [walk, hr]
      rw [traversal_1573 f (by omega), traversal_1574 f (by omega)]
      change (List.range' 1561 13 ++ List.range' (1561+13) 1) ++
        [1561+(13+1)] = List.range' 1561 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1561) (n := 13+1)).symm

private theorem traversal_1576 (fuel : Nat) (hf : 1576 < fuel) :
    walk nodes fuel 1576 = List.range' 1548 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1576).rule = .split 3 (39/16) 1560 1575 := by rfl
      simp only [walk, hr]
      rw [traversal_1560 f (by omega), traversal_1575 f (by omega)]
      change (List.range' 1548 13 ++ List.range' (1548+13) 15) ++
        [1548+(13+15)] = List.range' 1548 ((13+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1548) (n := 13+15)).symm

private theorem traversal_1577 (fuel : Nat) (hf : 1577 < fuel) :
    walk nodes fuel 1577 = List.range' 1509 69 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1577).rule = .split 2 (225/64) 1547 1576 := by rfl
      simp only [walk, hr]
      rw [traversal_1547 f (by omega), traversal_1576 f (by omega)]
      change (List.range' 1509 39 ++ List.range' (1509+39) 29) ++
        [1509+(39+29)] = List.range' 1509 ((39+29)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1509) (n := 39+29)).symm

private theorem traversal_1578 (fuel : Nat) (hf : 1578 < fuel) :
    walk nodes fuel 1578 = List.range' 1440 139 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1578).rule = .split 1 (15/16) 1508 1577 := by rfl
      simp only [walk, hr]
      rw [traversal_1508 f (by omega), traversal_1577 f (by omega)]
      change (List.range' 1440 69 ++ List.range' (1440+69) 69) ++
        [1440+(69+69)] = List.range' 1440 ((69+69)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1440) (n := 69+69)).symm

private theorem traversal_1579 (fuel : Nat) (hf : 1579 < fuel) :
    walk nodes fuel 1579 = List.range' 1579 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1579).rule = .bound .vertex 6 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1580 (fuel : Nat) (hf : 1580 < fuel) :
    walk nodes fuel 1580 = List.range' 1580 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1580).rule = .bound .leftEnd 3 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1581 (fuel : Nat) (hf : 1581 < fuel) :
    walk nodes fuel 1581 = List.range' 1579 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1581).rule = .split 1 (25/32) 1579 1580 := by rfl
      simp only [walk, hr]
      rw [traversal_1579 f (by omega), traversal_1580 f (by omega)]
      change (List.range' 1579 1 ++ List.range' (1579+1) 1) ++
        [1579+(1+1)] = List.range' 1579 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1579) (n := 1+1)).symm

private theorem traversal_1582 (fuel : Nat) (hf : 1582 < fuel) :
    walk nodes fuel 1582 = List.range' 1582 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1582).rule = .bound .vertex 3 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1583 (fuel : Nat) (hf : 1583 < fuel) :
    walk nodes fuel 1583 = List.range' 1579 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1583).rule = .split 0 (3/40) 1581 1582 := by rfl
      simp only [walk, hr]
      rw [traversal_1581 f (by omega), traversal_1582 f (by omega)]
      change (List.range' 1579 3 ++ List.range' (1579+3) 1) ++
        [1579+(3+1)] = List.range' 1579 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1579) (n := 3+1)).symm

private theorem traversal_1584 (fuel : Nat) (hf : 1584 < fuel) :
    walk nodes fuel 1584 = List.range' 1584 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1584).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1585 (fuel : Nat) (hf : 1585 < fuel) :
    walk nodes fuel 1585 = List.range' 1579 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1585).rule = .split 3 (39/16) 1583 1584 := by rfl
      simp only [walk, hr]
      rw [traversal_1583 f (by omega), traversal_1584 f (by omega)]
      change (List.range' 1579 5 ++ List.range' (1579+5) 1) ++
        [1579+(5+1)] = List.range' 1579 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1579) (n := 5+1)).symm

private theorem traversal_1586 (fuel : Nat) (hf : 1586 < fuel) :
    walk nodes fuel 1586 = List.range' 1586 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1586).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1587 (fuel : Nat) (hf : 1587 < fuel) :
    walk nodes fuel 1587 = List.range' 1579 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1587).rule = .split 2 (225/64) 1585 1586 := by rfl
      simp only [walk, hr]
      rw [traversal_1585 f (by omega), traversal_1586 f (by omega)]
      change (List.range' 1579 7 ++ List.range' (1579+7) 1) ++
        [1579+(7+1)] = List.range' 1579 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1579) (n := 7+1)).symm

private theorem traversal_1588 (fuel : Nat) (hf : 1588 < fuel) :
    walk nodes fuel 1588 = List.range' 1588 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1588).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1589 (fuel : Nat) (hf : 1589 < fuel) :
    walk nodes fuel 1589 = List.range' 1579 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1589).rule = .split 1 (15/16) 1587 1588 := by rfl
      simp only [walk, hr]
      rw [traversal_1587 f (by omega), traversal_1588 f (by omega)]
      change (List.range' 1579 9 ++ List.range' (1579+9) 1) ++
        [1579+(9+1)] = List.range' 1579 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1579) (n := 9+1)).symm

private theorem traversal_1590 (fuel : Nat) (hf : 1590 < fuel) :
    walk nodes fuel 1590 = List.range' 1440 151 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1590).rule = .split 0 (1/20) 1578 1589 := by rfl
      simp only [walk, hr]
      rw [traversal_1578 f (by omega), traversal_1589 f (by omega)]
      change (List.range' 1440 139 ++ List.range' (1440+139) 11) ++
        [1440+(139+11)] = List.range' 1440 ((139+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1440) (n := 139+11)).symm

private theorem traversal_1591 (fuel : Nat) (hf : 1591 < fuel) :
    walk nodes fuel 1591 = List.range' 1591 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1591).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1592 (fuel : Nat) (hf : 1592 < fuel) :
    walk nodes fuel 1592 = List.range' 1440 153 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1592).rule = .split 3 (21/8) 1590 1591 := by rfl
      simp only [walk, hr]
      rw [traversal_1590 f (by omega), traversal_1591 f (by omega)]
      change (List.range' 1440 151 ++ List.range' (1440+151) 1) ++
        [1440+(151+1)] = List.range' 1440 ((151+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1440) (n := 151+1)).symm

private theorem traversal_1593 (fuel : Nat) (hf : 1593 < fuel) :
    walk nodes fuel 1593 = List.range' 1439 155 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1593).rule = .split 2 (103/32) 1439 1592 := by rfl
      simp only [walk, hr]
      rw [traversal_1439 f (by omega), traversal_1592 f (by omega)]
      change (List.range' 1439 1 ++ List.range' (1439+1) 153) ++
        [1439+(1+153)] = List.range' 1439 ((1+153)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1439) (n := 1+153)).symm

private theorem traversal_1594 (fuel : Nat) (hf : 1594 < fuel) :
    walk nodes fuel 1594 = List.range' 1434 161 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1594).rule = .split 1 (5/8) 1438 1593 := by rfl
      simp only [walk, hr]
      rw [traversal_1438 f (by omega), traversal_1593 f (by omega)]
      change (List.range' 1434 5 ++ List.range' (1434+5) 155) ++
        [1434+(5+155)] = List.range' 1434 ((5+155)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1434) (n := 5+155)).symm

theorem traversal_1595 (fuel : Nat) (hf : 1595 < fuel) :
    walk nodes fuel 1595 = List.range' 1403 193 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1595).rule = .split 3 (9/4) 1433 1594 := by rfl
      simp only [walk, hr]
      rw [traversal_1433 f (by omega), traversal_1594 f (by omega)]
      change (List.range' 1403 31 ++ List.range' (1403+31) 161) ++
        [1403+(31+161)] = List.range' 1403 ((31+161)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1403) (n := 31+161)).symm

theorem traversal_1596 (fuel : Nat) (hf : 1596 < fuel) :
    walk nodes fuel 1596 = List.range' 1596 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1596).rule = .bound .rightEnd 0 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1597 (fuel : Nat) (hf : 1597 < fuel) :
    walk nodes fuel 1597 = List.range' 1597 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1597).rule = .bound .vertex 8 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1598 (fuel : Nat) (hf : 1598 < fuel) :
    walk nodes fuel 1598 = List.range' 1598 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1598).rule = .bound .vertex 8 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1599 (fuel : Nat) (hf : 1599 < fuel) :
    walk nodes fuel 1599 = List.range' 1599 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1599).rule = .bound .vertex 3 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1600 (fuel : Nat) (hf : 1600 < fuel) :
    walk nodes fuel 1600 = List.range' 1598 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1600).rule = .split 1 (15/16) 1598 1599 := by rfl
      simp only [walk, hr]
      rw [traversal_1598 f (by omega), traversal_1599 f (by omega)]
      change (List.range' 1598 1 ++ List.range' (1598+1) 1) ++
        [1598+(1+1)] = List.range' 1598 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1598) (n := 1+1)).symm

private theorem traversal_1601 (fuel : Nat) (hf : 1601 < fuel) :
    walk nodes fuel 1601 = List.range' 1601 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1601).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1602 (fuel : Nat) (hf : 1602 < fuel) :
    walk nodes fuel 1602 = List.range' 1598 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1602).rule = .split 0 (1/20) 1600 1601 := by rfl
      simp only [walk, hr]
      rw [traversal_1600 f (by omega), traversal_1601 f (by omega)]
      change (List.range' 1598 3 ++ List.range' (1598+3) 1) ++
        [1598+(3+1)] = List.range' 1598 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1598) (n := 3+1)).symm

theorem traversal_1603 (fuel : Nat) (hf : 1603 < fuel) :
    walk nodes fuel 1603 = List.range' 1597 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1603).rule = .split 3 (15/8) 1597 1602 := by rfl
      simp only [walk, hr]
      rw [traversal_1597 f (by omega), traversal_1602 f (by omega)]
      change (List.range' 1597 1 ++ List.range' (1597+1) 5) ++
        [1597+(1+5)] = List.range' 1597 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1597) (n := 1+5)).symm

theorem traversal_1604 (fuel : Nat) (hf : 1604 < fuel) :
    walk nodes fuel 1604 = List.range' 1604 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1604).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
