/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart24
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart24
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart24.traversal_1606,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart24.traversal_1607,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart24.traversal_1610,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart24.traversal_1611,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart24.traversal_1642,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart24.traversal_1653,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart24.traversal_1654,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart24.traversal_1667,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart24.traversal_1672
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart23
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1605 (fuel : Nat) (hf : 1605 < fuel) :
    walk nodes fuel 1605 = List.range' 1597 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1605).rule = .split 2 (141/32) 1603 1604 := by rfl
      simp only [walk, hr]
      rw [traversal_1603 f (by omega), traversal_1604 f (by omega)]
      change (List.range' 1597 7 ++ List.range' (1597+7) 1) ++
        [1597+(7+1)] = List.range' 1597 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1597) (n := 7+1)).symm

theorem traversal_1606 (fuel : Nat) (hf : 1606 < fuel) :
    walk nodes fuel 1606 = List.range' 1596 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1606).rule = .split 1 (5/8) 1596 1605 := by rfl
      simp only [walk, hr]
      rw [traversal_1596 f (by omega), traversal_1605 f (by omega)]
      change (List.range' 1596 1 ++ List.range' (1596+1) 9) ++
        [1596+(1+9)] = List.range' 1596 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1596) (n := 1+9)).symm

theorem traversal_1607 (fuel : Nat) (hf : 1607 < fuel) :
    walk nodes fuel 1607 = List.range' 1607 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1607).rule = .bound .rightEnd 6 (126023/393216) (408363/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1608 (fuel : Nat) (hf : 1608 < fuel) :
    walk nodes fuel 1608 = List.range' 1608 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1608).rule = .bound .rightEnd 6 (4969/16384) (864095/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1609 (fuel : Nat) (hf : 1609 < fuel) :
    walk nodes fuel 1609 = List.range' 1609 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1609).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1610 (fuel : Nat) (hf : 1610 < fuel) :
    walk nodes fuel 1610 = List.range' 1608 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1610).rule = .split 3 (45/16) 1608 1609 := by rfl
      simp only [walk, hr]
      rw [traversal_1608 f (by omega), traversal_1609 f (by omega)]
      change (List.range' 1608 1 ++ List.range' (1608+1) 1) ++
        [1608+(1+1)] = List.range' 1608 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1608) (n := 1+1)).symm

theorem traversal_1611 (fuel : Nat) (hf : 1611 < fuel) :
    walk nodes fuel 1611 = List.range' 1611 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1611).rule = .bound .rightEnd 6 (4969/16384) (864095/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1612 (fuel : Nat) (hf : 1612 < fuel) :
    walk nodes fuel 1612 = List.range' 1612 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1612).rule = .bound .rightEnd 6 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1613 (fuel : Nat) (hf : 1613 < fuel) :
    walk nodes fuel 1613 = List.range' 1613 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1613).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1614 (fuel : Nat) (hf : 1614 < fuel) :
    walk nodes fuel 1614 = List.range' 1612 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1614).rule = .split 3 (93/32) 1612 1613 := by rfl
      simp only [walk, hr]
      rw [traversal_1612 f (by omega), traversal_1613 f (by omega)]
      change (List.range' 1612 1 ++ List.range' (1612+1) 1) ++
        [1612+(1+1)] = List.range' 1612 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1612) (n := 1+1)).symm

private theorem traversal_1615 (fuel : Nat) (hf : 1615 < fuel) :
    walk nodes fuel 1615 = List.range' 1615 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1615).rule = .bound .rightEnd 0 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1616 (fuel : Nat) (hf : 1616 < fuel) :
    walk nodes fuel 1616 = List.range' 1616 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1616).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1617 (fuel : Nat) (hf : 1617 < fuel) :
    walk nodes fuel 1617 = List.range' 1617 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1617).rule = .bound .rightEnd 0 (14359/49152) (897325/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1618 (fuel : Nat) (hf : 1618 < fuel) :
    walk nodes fuel 1618 = List.range' 1618 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1618).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1619 (fuel : Nat) (hf : 1619 < fuel) :
    walk nodes fuel 1619 = List.range' 1617 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1619).rule = .split 3 (189/64) 1617 1618 := by rfl
      simp only [walk, hr]
      rw [traversal_1617 f (by omega), traversal_1618 f (by omega)]
      change (List.range' 1617 1 ++ List.range' (1617+1) 1) ++
        [1617+(1+1)] = List.range' 1617 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1617) (n := 1+1)).symm

private theorem traversal_1620 (fuel : Nat) (hf : 1620 < fuel) :
    walk nodes fuel 1620 = List.range' 1616 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1620).rule = .split 2 (1109/256) 1616 1619 := by rfl
      simp only [walk, hr]
      rw [traversal_1616 f (by omega), traversal_1619 f (by omega)]
      change (List.range' 1616 1 ++ List.range' (1616+1) 3) ++
        [1616+(1+3)] = List.range' 1616 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1616) (n := 1+3)).symm

private theorem traversal_1621 (fuel : Nat) (hf : 1621 < fuel) :
    walk nodes fuel 1621 = List.range' 1621 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1621).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1622 (fuel : Nat) (hf : 1622 < fuel) :
    walk nodes fuel 1622 = List.range' 1622 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1622).rule = .bound .rightEnd 6 (14359/49152) (897325/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1623 (fuel : Nat) (hf : 1623 < fuel) :
    walk nodes fuel 1623 = List.range' 1623 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1623).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1624 (fuel : Nat) (hf : 1624 < fuel) :
    walk nodes fuel 1624 = List.range' 1622 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1624).rule = .split 3 (189/64) 1622 1623 := by rfl
      simp only [walk, hr]
      rw [traversal_1622 f (by omega), traversal_1623 f (by omega)]
      change (List.range' 1622 1 ++ List.range' (1622+1) 1) ++
        [1622+(1+1)] = List.range' 1622 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1622) (n := 1+1)).symm

private theorem traversal_1625 (fuel : Nat) (hf : 1625 < fuel) :
    walk nodes fuel 1625 = List.range' 1621 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1625).rule = .split 2 (1109/256) 1621 1624 := by rfl
      simp only [walk, hr]
      rw [traversal_1621 f (by omega), traversal_1624 f (by omega)]
      change (List.range' 1621 1 ++ List.range' (1621+1) 3) ++
        [1621+(1+3)] = List.range' 1621 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1621) (n := 1+3)).symm

private theorem traversal_1626 (fuel : Nat) (hf : 1626 < fuel) :
    walk nodes fuel 1626 = List.range' 1616 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1626).rule = .split 1 (5/64) 1620 1625 := by rfl
      simp only [walk, hr]
      rw [traversal_1620 f (by omega), traversal_1625 f (by omega)]
      change (List.range' 1616 5 ++ List.range' (1616+5) 5) ++
        [1616+(5+5)] = List.range' 1616 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1616) (n := 5+5)).symm

private theorem traversal_1627 (fuel : Nat) (hf : 1627 < fuel) :
    walk nodes fuel 1627 = List.range' 1627 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1627).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1628 (fuel : Nat) (hf : 1628 < fuel) :
    walk nodes fuel 1628 = List.range' 1628 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1628).rule = .bound .rightEnd 6 (14359/49152) (897325/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1629 (fuel : Nat) (hf : 1629 < fuel) :
    walk nodes fuel 1629 = List.range' 1629 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1629).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1630 (fuel : Nat) (hf : 1630 < fuel) :
    walk nodes fuel 1630 = List.range' 1628 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1630).rule = .split 3 (189/64) 1628 1629 := by rfl
      simp only [walk, hr]
      rw [traversal_1628 f (by omega), traversal_1629 f (by omega)]
      change (List.range' 1628 1 ++ List.range' (1628+1) 1) ++
        [1628+(1+1)] = List.range' 1628 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1628) (n := 1+1)).symm

private theorem traversal_1631 (fuel : Nat) (hf : 1631 < fuel) :
    walk nodes fuel 1631 = List.range' 1627 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1631).rule = .split 2 (1109/256) 1627 1630 := by rfl
      simp only [walk, hr]
      rw [traversal_1627 f (by omega), traversal_1630 f (by omega)]
      change (List.range' 1627 1 ++ List.range' (1627+1) 3) ++
        [1627+(1+3)] = List.range' 1627 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1627) (n := 1+3)).symm

private theorem traversal_1632 (fuel : Nat) (hf : 1632 < fuel) :
    walk nodes fuel 1632 = List.range' 1632 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1632).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1633 (fuel : Nat) (hf : 1633 < fuel) :
    walk nodes fuel 1633 = List.range' 1633 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1633).rule = .bound .rightEnd 6 (14359/49152) (897325/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1634 (fuel : Nat) (hf : 1634 < fuel) :
    walk nodes fuel 1634 = List.range' 1634 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1634).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1635 (fuel : Nat) (hf : 1635 < fuel) :
    walk nodes fuel 1635 = List.range' 1633 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1635).rule = .split 0 (3/160) 1633 1634 := by rfl
      simp only [walk, hr]
      rw [traversal_1633 f (by omega), traversal_1634 f (by omega)]
      change (List.range' 1633 1 ++ List.range' (1633+1) 1) ++
        [1633+(1+1)] = List.range' 1633 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1633) (n := 1+1)).symm

private theorem traversal_1636 (fuel : Nat) (hf : 1636 < fuel) :
    walk nodes fuel 1636 = List.range' 1636 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1636).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1637 (fuel : Nat) (hf : 1637 < fuel) :
    walk nodes fuel 1637 = List.range' 1633 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1637).rule = .split 3 (189/64) 1635 1636 := by rfl
      simp only [walk, hr]
      rw [traversal_1635 f (by omega), traversal_1636 f (by omega)]
      change (List.range' 1633 3 ++ List.range' (1633+3) 1) ++
        [1633+(3+1)] = List.range' 1633 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1633) (n := 3+1)).symm

private theorem traversal_1638 (fuel : Nat) (hf : 1638 < fuel) :
    walk nodes fuel 1638 = List.range' 1632 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1638).rule = .split 2 (1109/256) 1632 1637 := by rfl
      simp only [walk, hr]
      rw [traversal_1632 f (by omega), traversal_1637 f (by omega)]
      change (List.range' 1632 1 ++ List.range' (1632+1) 5) ++
        [1632+(1+5)] = List.range' 1632 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1632) (n := 1+5)).symm

private theorem traversal_1639 (fuel : Nat) (hf : 1639 < fuel) :
    walk nodes fuel 1639 = List.range' 1627 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1639).rule = .split 1 (5/64) 1631 1638 := by rfl
      simp only [walk, hr]
      rw [traversal_1631 f (by omega), traversal_1638 f (by omega)]
      change (List.range' 1627 5 ++ List.range' (1627+5) 7) ++
        [1627+(5+7)] = List.range' 1627 ((5+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1627) (n := 5+7)).symm

private theorem traversal_1640 (fuel : Nat) (hf : 1640 < fuel) :
    walk nodes fuel 1640 = List.range' 1616 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1640).rule = .split 0 (1/80) 1626 1639 := by rfl
      simp only [walk, hr]
      rw [traversal_1626 f (by omega), traversal_1639 f (by omega)]
      change (List.range' 1616 11 ++ List.range' (1616+11) 13) ++
        [1616+(11+13)] = List.range' 1616 ((11+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1616) (n := 11+13)).symm

private theorem traversal_1641 (fuel : Nat) (hf : 1641 < fuel) :
    walk nodes fuel 1641 = List.range' 1615 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1641).rule = .split 3 (93/32) 1615 1640 := by rfl
      simp only [walk, hr]
      rw [traversal_1615 f (by omega), traversal_1640 f (by omega)]
      change (List.range' 1615 1 ++ List.range' (1615+1) 25) ++
        [1615+(1+25)] = List.range' 1615 ((1+25)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1615) (n := 1+25)).symm

theorem traversal_1642 (fuel : Nat) (hf : 1642 < fuel) :
    walk nodes fuel 1642 = List.range' 1612 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1642).rule = .split 2 (545/128) 1614 1641 := by rfl
      simp only [walk, hr]
      rw [traversal_1614 f (by omega), traversal_1641 f (by omega)]
      change (List.range' 1612 3 ++ List.range' (1612+3) 27) ++
        [1612+(3+27)] = List.range' 1612 ((3+27)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1612) (n := 3+27)).symm

private theorem traversal_1643 (fuel : Nat) (hf : 1643 < fuel) :
    walk nodes fuel 1643 = List.range' 1643 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1643).rule = .bound .rightEnd 6 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1644 (fuel : Nat) (hf : 1644 < fuel) :
    walk nodes fuel 1644 = List.range' 1644 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1644).rule = .bound .rightEnd 6 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1645 (fuel : Nat) (hf : 1645 < fuel) :
    walk nodes fuel 1645 = List.range' 1645 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1645).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1646 (fuel : Nat) (hf : 1646 < fuel) :
    walk nodes fuel 1646 = List.range' 1646 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1646).rule = .bound .rightEnd 6 (7297/24576) (882875/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1647 (fuel : Nat) (hf : 1647 < fuel) :
    walk nodes fuel 1647 = List.range' 1647 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1647).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1648 (fuel : Nat) (hf : 1648 < fuel) :
    walk nodes fuel 1648 = List.range' 1646 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1648).rule = .split 3 (183/64) 1646 1647 := by rfl
      simp only [walk, hr]
      rw [traversal_1646 f (by omega), traversal_1647 f (by omega)]
      change (List.range' 1646 1 ++ List.range' (1646+1) 1) ++
        [1646+(1+1)] = List.range' 1646 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1646) (n := 1+1)).symm

private theorem traversal_1649 (fuel : Nat) (hf : 1649 < fuel) :
    walk nodes fuel 1649 = List.range' 1645 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1649).rule = .split 2 (1071/256) 1645 1648 := by rfl
      simp only [walk, hr]
      rw [traversal_1645 f (by omega), traversal_1648 f (by omega)]
      change (List.range' 1645 1 ++ List.range' (1645+1) 3) ++
        [1645+(1+3)] = List.range' 1645 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1645) (n := 1+3)).symm

private theorem traversal_1650 (fuel : Nat) (hf : 1650 < fuel) :
    walk nodes fuel 1650 = List.range' 1644 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1650).rule = .split 1 (15/64) 1644 1649 := by rfl
      simp only [walk, hr]
      rw [traversal_1644 f (by omega), traversal_1649 f (by omega)]
      change (List.range' 1644 1 ++ List.range' (1644+1) 5) ++
        [1644+(1+5)] = List.range' 1644 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1644) (n := 1+5)).symm

private theorem traversal_1651 (fuel : Nat) (hf : 1651 < fuel) :
    walk nodes fuel 1651 = List.range' 1643 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1651).rule = .split 0 (1/80) 1643 1650 := by rfl
      simp only [walk, hr]
      rw [traversal_1643 f (by omega), traversal_1650 f (by omega)]
      change (List.range' 1643 1 ++ List.range' (1643+1) 7) ++
        [1643+(1+7)] = List.range' 1643 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1643) (n := 1+7)).symm

private theorem traversal_1652 (fuel : Nat) (hf : 1652 < fuel) :
    walk nodes fuel 1652 = List.range' 1652 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1652).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1653 (fuel : Nat) (hf : 1653 < fuel) :
    walk nodes fuel 1653 = List.range' 1643 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1653).rule = .split 3 (93/32) 1651 1652 := by rfl
      simp only [walk, hr]
      rw [traversal_1651 f (by omega), traversal_1652 f (by omega)]
      change (List.range' 1643 9 ++ List.range' (1643+9) 1) ++
        [1643+(9+1)] = List.range' 1643 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1643) (n := 9+1)).symm

theorem traversal_1654 (fuel : Nat) (hf : 1654 < fuel) :
    walk nodes fuel 1654 = List.range' 1654 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1654).rule = .bound .rightEnd 6 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1655 (fuel : Nat) (hf : 1655 < fuel) :
    walk nodes fuel 1655 = List.range' 1655 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1655).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1656 (fuel : Nat) (hf : 1656 < fuel) :
    walk nodes fuel 1656 = List.range' 1656 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1656).rule = .bound .rightEnd 6 (14359/49152) (897325/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1657 (fuel : Nat) (hf : 1657 < fuel) :
    walk nodes fuel 1657 = List.range' 1657 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1657).rule = .bound .rightEnd 6 (14359/49152) (897325/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1658 (fuel : Nat) (hf : 1658 < fuel) :
    walk nodes fuel 1658 = List.range' 1658 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1658).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1659 (fuel : Nat) (hf : 1659 < fuel) :
    walk nodes fuel 1659 = List.range' 1657 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1659).rule = .split 1 (25/128) 1657 1658 := by rfl
      simp only [walk, hr]
      rw [traversal_1657 f (by omega), traversal_1658 f (by omega)]
      change (List.range' 1657 1 ++ List.range' (1657+1) 1) ++
        [1657+(1+1)] = List.range' 1657 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1657) (n := 1+1)).symm

private theorem traversal_1660 (fuel : Nat) (hf : 1660 < fuel) :
    walk nodes fuel 1660 = List.range' 1656 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1660).rule = .split 0 (1/160) 1656 1659 := by rfl
      simp only [walk, hr]
      rw [traversal_1656 f (by omega), traversal_1659 f (by omega)]
      change (List.range' 1656 1 ++ List.range' (1656+1) 3) ++
        [1656+(1+3)] = List.range' 1656 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1656) (n := 1+3)).symm

private theorem traversal_1661 (fuel : Nat) (hf : 1661 < fuel) :
    walk nodes fuel 1661 = List.range' 1661 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1661).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1662 (fuel : Nat) (hf : 1662 < fuel) :
    walk nodes fuel 1662 = List.range' 1656 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1662).rule = .split 3 (189/64) 1660 1661 := by rfl
      simp only [walk, hr]
      rw [traversal_1660 f (by omega), traversal_1661 f (by omega)]
      change (List.range' 1656 5 ++ List.range' (1656+5) 1) ++
        [1656+(5+1)] = List.range' 1656 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1656) (n := 5+1)).symm

private theorem traversal_1663 (fuel : Nat) (hf : 1663 < fuel) :
    walk nodes fuel 1663 = List.range' 1655 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1663).rule = .split 2 (1109/256) 1655 1662 := by rfl
      simp only [walk, hr]
      rw [traversal_1655 f (by omega), traversal_1662 f (by omega)]
      change (List.range' 1655 1 ++ List.range' (1655+1) 7) ++
        [1655+(1+7)] = List.range' 1655 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1655) (n := 1+7)).symm

private theorem traversal_1664 (fuel : Nat) (hf : 1664 < fuel) :
    walk nodes fuel 1664 = List.range' 1664 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1664).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1665 (fuel : Nat) (hf : 1665 < fuel) :
    walk nodes fuel 1665 = List.range' 1665 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1665).rule = .bound .rightEnd 3 (28603/98304) (450445/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1666 (fuel : Nat) (hf : 1666 < fuel) :
    walk nodes fuel 1666 = List.range' 1664 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1666).rule = .split 2 (1109/256) 1664 1665 := by rfl
      simp only [walk, hr]
      rw [traversal_1664 f (by omega), traversal_1665 f (by omega)]
      change (List.range' 1664 1 ++ List.range' (1664+1) 1) ++
        [1664+(1+1)] = List.range' 1664 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1664) (n := 1+1)).symm

theorem traversal_1667 (fuel : Nat) (hf : 1667 < fuel) :
    walk nodes fuel 1667 = List.range' 1655 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1667).rule = .split 1 (15/64) 1663 1666 := by rfl
      simp only [walk, hr]
      rw [traversal_1663 f (by omega), traversal_1666 f (by omega)]
      change (List.range' 1655 9 ++ List.range' (1655+9) 3) ++
        [1655+(9+3)] = List.range' 1655 ((9+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1655) (n := 9+3)).symm

private theorem traversal_1668 (fuel : Nat) (hf : 1668 < fuel) :
    walk nodes fuel 1668 = List.range' 1668 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1668).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1669 (fuel : Nat) (hf : 1669 < fuel) :
    walk nodes fuel 1669 = List.range' 1669 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1669).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1670 (fuel : Nat) (hf : 1670 < fuel) :
    walk nodes fuel 1670 = List.range' 1668 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1670).rule = .split 2 (1109/256) 1668 1669 := by rfl
      simp only [walk, hr]
      rw [traversal_1668 f (by omega), traversal_1669 f (by omega)]
      change (List.range' 1668 1 ++ List.range' (1668+1) 1) ++
        [1668+(1+1)] = List.range' 1668 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1668) (n := 1+1)).symm

private theorem traversal_1671 (fuel : Nat) (hf : 1671 < fuel) :
    walk nodes fuel 1671 = List.range' 1671 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1671).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1672 (fuel : Nat) (hf : 1672 < fuel) :
    walk nodes fuel 1672 = List.range' 1668 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1672).rule = .split 1 (15/64) 1670 1671 := by rfl
      simp only [walk, hr]
      rw [traversal_1670 f (by omega), traversal_1671 f (by omega)]
      change (List.range' 1668 3 ++ List.range' (1668+3) 1) ++
        [1668+(3+1)] = List.range' 1668 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1668) (n := 3+1)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
