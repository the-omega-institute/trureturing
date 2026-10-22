/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart25
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart25
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart25.traversal_1716,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart25.traversal_1737,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart25.traversal_1738
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart24
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1673 (fuel : Nat) (hf : 1673 < fuel) :
    walk nodes fuel 1673 = List.range' 1655 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1673).rule = .split 0 (1/80) 1667 1672 := by rfl
      simp only [walk, hr]
      rw [traversal_1667 f (by omega), traversal_1672 f (by omega)]
      change (List.range' 1655 13 ++ List.range' (1655+13) 5) ++
        [1655+(13+5)] = List.range' 1655 ((13+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1655) (n := 13+5)).symm

private theorem traversal_1674 (fuel : Nat) (hf : 1674 < fuel) :
    walk nodes fuel 1674 = List.range' 1654 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1674).rule = .split 3 (93/32) 1654 1673 := by rfl
      simp only [walk, hr]
      rw [traversal_1654 f (by omega), traversal_1673 f (by omega)]
      change (List.range' 1654 1 ++ List.range' (1654+1) 19) ++
        [1654+(1+19)] = List.range' 1654 ((1+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1654) (n := 1+19)).symm

private theorem traversal_1675 (fuel : Nat) (hf : 1675 < fuel) :
    walk nodes fuel 1675 = List.range' 1643 33 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1675).rule = .split 2 (545/128) 1653 1674 := by rfl
      simp only [walk, hr]
      rw [traversal_1653 f (by omega), traversal_1674 f (by omega)]
      change (List.range' 1643 11 ++ List.range' (1643+11) 21) ++
        [1643+(11+21)] = List.range' 1643 ((11+21)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1643) (n := 11+21)).symm

private theorem traversal_1676 (fuel : Nat) (hf : 1676 < fuel) :
    walk nodes fuel 1676 = List.range' 1612 65 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1676).rule = .split 1 (5/32) 1642 1675 := by rfl
      simp only [walk, hr]
      rw [traversal_1642 f (by omega), traversal_1675 f (by omega)]
      change (List.range' 1612 31 ++ List.range' (1612+31) 33) ++
        [1612+(31+33)] = List.range' 1612 ((31+33)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1612) (n := 31+33)).symm

private theorem traversal_1677 (fuel : Nat) (hf : 1677 < fuel) :
    walk nodes fuel 1677 = List.range' 1677 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1677).rule = .bound .rightEnd 0 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1678 (fuel : Nat) (hf : 1678 < fuel) :
    walk nodes fuel 1678 = List.range' 1678 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1678).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1679 (fuel : Nat) (hf : 1679 < fuel) :
    walk nodes fuel 1679 = List.range' 1679 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1679).rule = .bound .rightEnd 6 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1680 (fuel : Nat) (hf : 1680 < fuel) :
    walk nodes fuel 1680 = List.range' 1678 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1680).rule = .split 2 (1071/256) 1678 1679 := by rfl
      simp only [walk, hr]
      rw [traversal_1678 f (by omega), traversal_1679 f (by omega)]
      change (List.range' 1678 1 ++ List.range' (1678+1) 1) ++
        [1678+(1+1)] = List.range' 1678 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1678) (n := 1+1)).symm

private theorem traversal_1681 (fuel : Nat) (hf : 1681 < fuel) :
    walk nodes fuel 1681 = List.range' 1677 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1681).rule = .split 1 (5/64) 1677 1680 := by rfl
      simp only [walk, hr]
      rw [traversal_1677 f (by omega), traversal_1680 f (by omega)]
      change (List.range' 1677 1 ++ List.range' (1677+1) 3) ++
        [1677+(1+3)] = List.range' 1677 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1677) (n := 1+3)).symm

private theorem traversal_1682 (fuel : Nat) (hf : 1682 < fuel) :
    walk nodes fuel 1682 = List.range' 1682 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1682).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1683 (fuel : Nat) (hf : 1683 < fuel) :
    walk nodes fuel 1683 = List.range' 1683 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1683).rule = .bound .rightEnd 3 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1684 (fuel : Nat) (hf : 1684 < fuel) :
    walk nodes fuel 1684 = List.range' 1682 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1684).rule = .split 2 (1071/256) 1682 1683 := by rfl
      simp only [walk, hr]
      rw [traversal_1682 f (by omega), traversal_1683 f (by omega)]
      change (List.range' 1682 1 ++ List.range' (1682+1) 1) ++
        [1682+(1+1)] = List.range' 1682 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1682) (n := 1+1)).symm

private theorem traversal_1685 (fuel : Nat) (hf : 1685 < fuel) :
    walk nodes fuel 1685 = List.range' 1685 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1685).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1686 (fuel : Nat) (hf : 1686 < fuel) :
    walk nodes fuel 1686 = List.range' 1682 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1686).rule = .split 1 (5/64) 1684 1685 := by rfl
      simp only [walk, hr]
      rw [traversal_1684 f (by omega), traversal_1685 f (by omega)]
      change (List.range' 1682 3 ++ List.range' (1682+3) 1) ++
        [1682+(3+1)] = List.range' 1682 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1682) (n := 3+1)).symm

private theorem traversal_1687 (fuel : Nat) (hf : 1687 < fuel) :
    walk nodes fuel 1687 = List.range' 1677 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1687).rule = .split 0 (3/80) 1681 1686 := by rfl
      simp only [walk, hr]
      rw [traversal_1681 f (by omega), traversal_1686 f (by omega)]
      change (List.range' 1677 5 ++ List.range' (1677+5) 5) ++
        [1677+(5+5)] = List.range' 1677 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1677) (n := 5+5)).symm

private theorem traversal_1688 (fuel : Nat) (hf : 1688 < fuel) :
    walk nodes fuel 1688 = List.range' 1688 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1688).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1689 (fuel : Nat) (hf : 1689 < fuel) :
    walk nodes fuel 1689 = List.range' 1677 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1689).rule = .split 3 (93/32) 1687 1688 := by rfl
      simp only [walk, hr]
      rw [traversal_1687 f (by omega), traversal_1688 f (by omega)]
      change (List.range' 1677 11 ++ List.range' (1677+11) 1) ++
        [1677+(11+1)] = List.range' 1677 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1677) (n := 11+1)).symm

private theorem traversal_1690 (fuel : Nat) (hf : 1690 < fuel) :
    walk nodes fuel 1690 = List.range' 1690 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1690).rule = .bound .rightEnd 6 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1691 (fuel : Nat) (hf : 1691 < fuel) :
    walk nodes fuel 1691 = List.range' 1691 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1691).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1692 (fuel : Nat) (hf : 1692 < fuel) :
    walk nodes fuel 1692 = List.range' 1690 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1692).rule = .split 0 (3/80) 1690 1691 := by rfl
      simp only [walk, hr]
      rw [traversal_1690 f (by omega), traversal_1691 f (by omega)]
      change (List.range' 1690 1 ++ List.range' (1690+1) 1) ++
        [1690+(1+1)] = List.range' 1690 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1690) (n := 1+1)).symm

private theorem traversal_1693 (fuel : Nat) (hf : 1693 < fuel) :
    walk nodes fuel 1693 = List.range' 1693 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1693).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1694 (fuel : Nat) (hf : 1694 < fuel) :
    walk nodes fuel 1694 = List.range' 1694 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1694).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1695 (fuel : Nat) (hf : 1695 < fuel) :
    walk nodes fuel 1695 = List.range' 1693 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1695).rule = .split 2 (1109/256) 1693 1694 := by rfl
      simp only [walk, hr]
      rw [traversal_1693 f (by omega), traversal_1694 f (by omega)]
      change (List.range' 1693 1 ++ List.range' (1693+1) 1) ++
        [1693+(1+1)] = List.range' 1693 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1693) (n := 1+1)).symm

private theorem traversal_1696 (fuel : Nat) (hf : 1696 < fuel) :
    walk nodes fuel 1696 = List.range' 1696 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1696).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1697 (fuel : Nat) (hf : 1697 < fuel) :
    walk nodes fuel 1697 = List.range' 1693 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1697).rule = .split 1 (5/64) 1695 1696 := by rfl
      simp only [walk, hr]
      rw [traversal_1695 f (by omega), traversal_1696 f (by omega)]
      change (List.range' 1693 3 ++ List.range' (1693+3) 1) ++
        [1693+(3+1)] = List.range' 1693 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1693) (n := 3+1)).symm

private theorem traversal_1698 (fuel : Nat) (hf : 1698 < fuel) :
    walk nodes fuel 1698 = List.range' 1698 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1698).rule = .infeasible 4 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1699 (fuel : Nat) (hf : 1699 < fuel) :
    walk nodes fuel 1699 = List.range' 1693 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1699).rule = .split 0 (3/80) 1697 1698 := by rfl
      simp only [walk, hr]
      rw [traversal_1697 f (by omega), traversal_1698 f (by omega)]
      change (List.range' 1693 5 ++ List.range' (1693+5) 1) ++
        [1693+(5+1)] = List.range' 1693 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1693) (n := 5+1)).symm

private theorem traversal_1700 (fuel : Nat) (hf : 1700 < fuel) :
    walk nodes fuel 1700 = List.range' 1690 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1700).rule = .split 3 (93/32) 1692 1699 := by rfl
      simp only [walk, hr]
      rw [traversal_1692 f (by omega), traversal_1699 f (by omega)]
      change (List.range' 1690 3 ++ List.range' (1690+3) 7) ++
        [1690+(3+7)] = List.range' 1690 ((3+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1690) (n := 3+7)).symm

private theorem traversal_1701 (fuel : Nat) (hf : 1701 < fuel) :
    walk nodes fuel 1701 = List.range' 1677 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1701).rule = .split 2 (545/128) 1689 1700 := by rfl
      simp only [walk, hr]
      rw [traversal_1689 f (by omega), traversal_1700 f (by omega)]
      change (List.range' 1677 13 ++ List.range' (1677+13) 11) ++
        [1677+(13+11)] = List.range' 1677 ((13+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1677) (n := 13+11)).symm

private theorem traversal_1702 (fuel : Nat) (hf : 1702 < fuel) :
    walk nodes fuel 1702 = List.range' 1702 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1702).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1703 (fuel : Nat) (hf : 1703 < fuel) :
    walk nodes fuel 1703 = List.range' 1703 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1703).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1704 (fuel : Nat) (hf : 1704 < fuel) :
    walk nodes fuel 1704 = List.range' 1702 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1704).rule = .split 2 (1071/256) 1702 1703 := by rfl
      simp only [walk, hr]
      rw [traversal_1702 f (by omega), traversal_1703 f (by omega)]
      change (List.range' 1702 1 ++ List.range' (1702+1) 1) ++
        [1702+(1+1)] = List.range' 1702 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1702) (n := 1+1)).symm

private theorem traversal_1705 (fuel : Nat) (hf : 1705 < fuel) :
    walk nodes fuel 1705 = List.range' 1705 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1705).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1706 (fuel : Nat) (hf : 1706 < fuel) :
    walk nodes fuel 1706 = List.range' 1702 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1706).rule = .split 1 (15/64) 1704 1705 := by rfl
      simp only [walk, hr]
      rw [traversal_1704 f (by omega), traversal_1705 f (by omega)]
      change (List.range' 1702 3 ++ List.range' (1702+3) 1) ++
        [1702+(3+1)] = List.range' 1702 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1702) (n := 3+1)).symm

private theorem traversal_1707 (fuel : Nat) (hf : 1707 < fuel) :
    walk nodes fuel 1707 = List.range' 1707 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1707).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1708 (fuel : Nat) (hf : 1708 < fuel) :
    walk nodes fuel 1708 = List.range' 1702 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1708).rule = .split 0 (3/80) 1706 1707 := by rfl
      simp only [walk, hr]
      rw [traversal_1706 f (by omega), traversal_1707 f (by omega)]
      change (List.range' 1702 5 ++ List.range' (1702+5) 1) ++
        [1702+(5+1)] = List.range' 1702 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1702) (n := 5+1)).symm

private theorem traversal_1709 (fuel : Nat) (hf : 1709 < fuel) :
    walk nodes fuel 1709 = List.range' 1709 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1709).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1710 (fuel : Nat) (hf : 1710 < fuel) :
    walk nodes fuel 1710 = List.range' 1702 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1710).rule = .split 3 (93/32) 1708 1709 := by rfl
      simp only [walk, hr]
      rw [traversal_1708 f (by omega), traversal_1709 f (by omega)]
      change (List.range' 1702 7 ++ List.range' (1702+7) 1) ++
        [1702+(7+1)] = List.range' 1702 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1702) (n := 7+1)).symm

private theorem traversal_1711 (fuel : Nat) (hf : 1711 < fuel) :
    walk nodes fuel 1711 = List.range' 1711 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1711).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1712 (fuel : Nat) (hf : 1712 < fuel) :
    walk nodes fuel 1712 = List.range' 1702 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1712).rule = .split 2 (545/128) 1710 1711 := by rfl
      simp only [walk, hr]
      rw [traversal_1710 f (by omega), traversal_1711 f (by omega)]
      change (List.range' 1702 9 ++ List.range' (1702+9) 1) ++
        [1702+(9+1)] = List.range' 1702 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1702) (n := 9+1)).symm

private theorem traversal_1713 (fuel : Nat) (hf : 1713 < fuel) :
    walk nodes fuel 1713 = List.range' 1677 37 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1713).rule = .split 1 (5/32) 1701 1712 := by rfl
      simp only [walk, hr]
      rw [traversal_1701 f (by omega), traversal_1712 f (by omega)]
      change (List.range' 1677 25 ++ List.range' (1677+25) 11) ++
        [1677+(25+11)] = List.range' 1677 ((25+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1677) (n := 25+11)).symm

private theorem traversal_1714 (fuel : Nat) (hf : 1714 < fuel) :
    walk nodes fuel 1714 = List.range' 1612 103 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1714).rule = .split 0 (1/40) 1676 1713 := by rfl
      simp only [walk, hr]
      rw [traversal_1676 f (by omega), traversal_1713 f (by omega)]
      change (List.range' 1612 65 ++ List.range' (1612+65) 37) ++
        [1612+(65+37)] = List.range' 1612 ((65+37)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1612) (n := 65+37)).symm

private theorem traversal_1715 (fuel : Nat) (hf : 1715 < fuel) :
    walk nodes fuel 1715 = List.range' 1611 105 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1715).rule = .split 3 (45/16) 1611 1714 := by rfl
      simp only [walk, hr]
      rw [traversal_1611 f (by omega), traversal_1714 f (by omega)]
      change (List.range' 1611 1 ++ List.range' (1611+1) 103) ++
        [1611+(1+103)] = List.range' 1611 ((1+103)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1611) (n := 1+103)).symm

theorem traversal_1716 (fuel : Nat) (hf : 1716 < fuel) :
    walk nodes fuel 1716 = List.range' 1608 109 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1716).rule = .split 2 (263/64) 1610 1715 := by rfl
      simp only [walk, hr]
      rw [traversal_1610 f (by omega), traversal_1715 f (by omega)]
      change (List.range' 1608 3 ++ List.range' (1608+3) 105) ++
        [1608+(3+105)] = List.range' 1608 ((3+105)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1608) (n := 3+105)).symm

private theorem traversal_1717 (fuel : Nat) (hf : 1717 < fuel) :
    walk nodes fuel 1717 = List.range' 1717 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1717).rule = .bound .rightEnd 6 (4969/16384) (864095/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1718 (fuel : Nat) (hf : 1718 < fuel) :
    walk nodes fuel 1718 = List.range' 1718 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1718).rule = .bound .rightEnd 6 (30071/98304) (856899/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1719 (fuel : Nat) (hf : 1719 < fuel) :
    walk nodes fuel 1719 = List.range' 1719 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1719).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1720 (fuel : Nat) (hf : 1720 < fuel) :
    walk nodes fuel 1720 = List.range' 1718 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1720).rule = .split 3 (87/32) 1718 1719 := by rfl
      simp only [walk, hr]
      rw [traversal_1718 f (by omega), traversal_1719 f (by omega)]
      change (List.range' 1718 1 ++ List.range' (1718+1) 1) ++
        [1718+(1+1)] = List.range' 1718 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1718) (n := 1+1)).symm

private theorem traversal_1721 (fuel : Nat) (hf : 1721 < fuel) :
    walk nodes fuel 1721 = List.range' 1721 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1721).rule = .bound .rightEnd 6 (30071/98304) (856899/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1722 (fuel : Nat) (hf : 1722 < fuel) :
    walk nodes fuel 1722 = List.range' 1722 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1722).rule = .bound .rightEnd 6 (29557/98304) (871805/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1723 (fuel : Nat) (hf : 1723 < fuel) :
    walk nodes fuel 1723 = List.range' 1723 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1723).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1724 (fuel : Nat) (hf : 1724 < fuel) :
    walk nodes fuel 1724 = List.range' 1724 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1724).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1725 (fuel : Nat) (hf : 1725 < fuel) :
    walk nodes fuel 1725 = List.range' 1723 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1725).rule = .split 2 (1033/256) 1723 1724 := by rfl
      simp only [walk, hr]
      rw [traversal_1723 f (by omega), traversal_1724 f (by omega)]
      change (List.range' 1723 1 ++ List.range' (1723+1) 1) ++
        [1723+(1+1)] = List.range' 1723 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1723) (n := 1+1)).symm

private theorem traversal_1726 (fuel : Nat) (hf : 1726 < fuel) :
    walk nodes fuel 1726 = List.range' 1722 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1726).rule = .split 1 (35/64) 1722 1725 := by rfl
      simp only [walk, hr]
      rw [traversal_1722 f (by omega), traversal_1725 f (by omega)]
      change (List.range' 1722 1 ++ List.range' (1722+1) 3) ++
        [1722+(1+3)] = List.range' 1722 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1722) (n := 1+3)).symm

private theorem traversal_1727 (fuel : Nat) (hf : 1727 < fuel) :
    walk nodes fuel 1727 = List.range' 1727 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1727).rule = .bound .rightEnd 3 (29557/98304) (871805/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1728 (fuel : Nat) (hf : 1728 < fuel) :
    walk nodes fuel 1728 = List.range' 1722 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1728).rule = .split 0 (1/80) 1726 1727 := by rfl
      simp only [walk, hr]
      rw [traversal_1726 f (by omega), traversal_1727 f (by omega)]
      change (List.range' 1722 5 ++ List.range' (1722+5) 1) ++
        [1722+(5+1)] = List.range' 1722 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1722) (n := 5+1)).symm

private theorem traversal_1729 (fuel : Nat) (hf : 1729 < fuel) :
    walk nodes fuel 1729 = List.range' 1721 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1729).rule = .split 3 (87/32) 1721 1728 := by rfl
      simp only [walk, hr]
      rw [traversal_1721 f (by omega), traversal_1728 f (by omega)]
      change (List.range' 1721 1 ++ List.range' (1721+1) 7) ++
        [1721+(1+7)] = List.range' 1721 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1721) (n := 1+7)).symm

private theorem traversal_1730 (fuel : Nat) (hf : 1730 < fuel) :
    walk nodes fuel 1730 = List.range' 1718 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1730).rule = .split 2 (507/128) 1720 1729 := by rfl
      simp only [walk, hr]
      rw [traversal_1720 f (by omega), traversal_1729 f (by omega)]
      change (List.range' 1718 3 ++ List.range' (1718+3) 9) ++
        [1718+(3+9)] = List.range' 1718 ((3+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1718) (n := 3+9)).symm

private theorem traversal_1731 (fuel : Nat) (hf : 1731 < fuel) :
    walk nodes fuel 1731 = List.range' 1717 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1731).rule = .split 1 (15/32) 1717 1730 := by rfl
      simp only [walk, hr]
      rw [traversal_1717 f (by omega), traversal_1730 f (by omega)]
      change (List.range' 1717 1 ++ List.range' (1717+1) 13) ++
        [1717+(1+13)] = List.range' 1717 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1717) (n := 1+13)).symm

private theorem traversal_1732 (fuel : Nat) (hf : 1732 < fuel) :
    walk nodes fuel 1732 = List.range' 1732 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1732).rule = .bound .rightEnd 6 (4969/16384) (864095/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1733 (fuel : Nat) (hf : 1733 < fuel) :
    walk nodes fuel 1733 = List.range' 1733 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1733).rule = .bound .rightEnd 3 (4969/16384) (864095/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1734 (fuel : Nat) (hf : 1734 < fuel) :
    walk nodes fuel 1734 = List.range' 1732 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1734).rule = .split 1 (15/32) 1732 1733 := by rfl
      simp only [walk, hr]
      rw [traversal_1732 f (by omega), traversal_1733 f (by omega)]
      change (List.range' 1732 1 ++ List.range' (1732+1) 1) ++
        [1732+(1+1)] = List.range' 1732 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1732) (n := 1+1)).symm

private theorem traversal_1735 (fuel : Nat) (hf : 1735 < fuel) :
    walk nodes fuel 1735 = List.range' 1717 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1735).rule = .split 0 (1/40) 1731 1734 := by rfl
      simp only [walk, hr]
      rw [traversal_1731 f (by omega), traversal_1734 f (by omega)]
      change (List.range' 1717 15 ++ List.range' (1717+15) 3) ++
        [1717+(15+3)] = List.range' 1717 ((15+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1717) (n := 15+3)).symm

private theorem traversal_1736 (fuel : Nat) (hf : 1736 < fuel) :
    walk nodes fuel 1736 = List.range' 1736 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1736).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1737 (fuel : Nat) (hf : 1737 < fuel) :
    walk nodes fuel 1737 = List.range' 1717 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1737).rule = .split 3 (45/16) 1735 1736 := by rfl
      simp only [walk, hr]
      rw [traversal_1735 f (by omega), traversal_1736 f (by omega)]
      change (List.range' 1717 19 ++ List.range' (1717+19) 1) ++
        [1717+(19+1)] = List.range' 1717 ((19+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1717) (n := 19+1)).symm

theorem traversal_1738 (fuel : Nat) (hf : 1738 < fuel) :
    walk nodes fuel 1738 = List.range' 1738 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1738).rule = .bound .rightEnd 6 (4969/16384) (864095/1048576) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
