/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart26
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart26
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart26.traversal_1775,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart26.traversal_1776,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart26.traversal_1777,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart26.traversal_1778,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart26.traversal_1779,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart26.traversal_1802,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart26.traversal_1805,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart26.traversal_1806
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart24
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart25
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1739 (fuel : Nat) (hf : 1739 < fuel) :
    walk nodes fuel 1739 = List.range' 1739 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1739).rule = .bound .rightEnd 3 (4969/16384) (864095/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1740 (fuel : Nat) (hf : 1740 < fuel) :
    walk nodes fuel 1740 = List.range' 1738 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1740).rule = .split 1 (15/32) 1738 1739 := by rfl
      simp only [walk, hr]
      rw [traversal_1738 f (by omega), traversal_1739 f (by omega)]
      change (List.range' 1738 1 ++ List.range' (1738+1) 1) ++
        [1738+(1+1)] = List.range' 1738 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1738) (n := 1+1)).symm

private theorem traversal_1741 (fuel : Nat) (hf : 1741 < fuel) :
    walk nodes fuel 1741 = List.range' 1741 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1741).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1742 (fuel : Nat) (hf : 1742 < fuel) :
    walk nodes fuel 1742 = List.range' 1738 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1742).rule = .split 0 (1/40) 1740 1741 := by rfl
      simp only [walk, hr]
      rw [traversal_1740 f (by omega), traversal_1741 f (by omega)]
      change (List.range' 1738 3 ++ List.range' (1738+3) 1) ++
        [1738+(3+1)] = List.range' 1738 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1738) (n := 3+1)).symm

private theorem traversal_1743 (fuel : Nat) (hf : 1743 < fuel) :
    walk nodes fuel 1743 = List.range' 1743 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1743).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1744 (fuel : Nat) (hf : 1744 < fuel) :
    walk nodes fuel 1744 = List.range' 1744 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1744).rule = .bound .rightEnd 6 (7297/24576) (882875/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1745 (fuel : Nat) (hf : 1745 < fuel) :
    walk nodes fuel 1745 = List.range' 1745 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1745).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1746 (fuel : Nat) (hf : 1746 < fuel) :
    walk nodes fuel 1746 = List.range' 1744 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1746).rule = .split 3 (183/64) 1744 1745 := by rfl
      simp only [walk, hr]
      rw [traversal_1744 f (by omega), traversal_1745 f (by omega)]
      change (List.range' 1744 1 ++ List.range' (1744+1) 1) ++
        [1744+(1+1)] = List.range' 1744 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1744) (n := 1+1)).symm

private theorem traversal_1747 (fuel : Nat) (hf : 1747 < fuel) :
    walk nodes fuel 1747 = List.range' 1743 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1747).rule = .split 2 (1071/256) 1743 1746 := by rfl
      simp only [walk, hr]
      rw [traversal_1743 f (by omega), traversal_1746 f (by omega)]
      change (List.range' 1743 1 ++ List.range' (1743+1) 3) ++
        [1743+(1+3)] = List.range' 1743 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1743) (n := 1+3)).symm

private theorem traversal_1748 (fuel : Nat) (hf : 1748 < fuel) :
    walk nodes fuel 1748 = List.range' 1748 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1748).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1749 (fuel : Nat) (hf : 1749 < fuel) :
    walk nodes fuel 1749 = List.range' 1749 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1749).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1750 (fuel : Nat) (hf : 1750 < fuel) :
    walk nodes fuel 1750 = List.range' 1748 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1750).rule = .split 2 (1071/256) 1748 1749 := by rfl
      simp only [walk, hr]
      rw [traversal_1748 f (by omega), traversal_1749 f (by omega)]
      change (List.range' 1748 1 ++ List.range' (1748+1) 1) ++
        [1748+(1+1)] = List.range' 1748 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1748) (n := 1+1)).symm

private theorem traversal_1751 (fuel : Nat) (hf : 1751 < fuel) :
    walk nodes fuel 1751 = List.range' 1743 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1751).rule = .split 1 (25/64) 1747 1750 := by rfl
      simp only [walk, hr]
      rw [traversal_1747 f (by omega), traversal_1750 f (by omega)]
      change (List.range' 1743 5 ++ List.range' (1743+5) 3) ++
        [1743+(5+3)] = List.range' 1743 ((5+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1743) (n := 5+3)).symm

private theorem traversal_1752 (fuel : Nat) (hf : 1752 < fuel) :
    walk nodes fuel 1752 = List.range' 1752 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1752).rule = .bound .rightEnd 3 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1753 (fuel : Nat) (hf : 1753 < fuel) :
    walk nodes fuel 1753 = List.range' 1743 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1753).rule = .split 0 (1/80) 1751 1752 := by rfl
      simp only [walk, hr]
      rw [traversal_1751 f (by omega), traversal_1752 f (by omega)]
      change (List.range' 1743 9 ++ List.range' (1743+9) 1) ++
        [1743+(9+1)] = List.range' 1743 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1743) (n := 9+1)).symm

private theorem traversal_1754 (fuel : Nat) (hf : 1754 < fuel) :
    walk nodes fuel 1754 = List.range' 1754 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1754).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1755 (fuel : Nat) (hf : 1755 < fuel) :
    walk nodes fuel 1755 = List.range' 1743 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1755).rule = .split 3 (93/32) 1753 1754 := by rfl
      simp only [walk, hr]
      rw [traversal_1753 f (by omega), traversal_1754 f (by omega)]
      change (List.range' 1743 11 ++ List.range' (1743+11) 1) ++
        [1743+(11+1)] = List.range' 1743 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1743) (n := 11+1)).symm

private theorem traversal_1756 (fuel : Nat) (hf : 1756 < fuel) :
    walk nodes fuel 1756 = List.range' 1756 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1756).rule = .bound .rightEnd 3 (57671/196608) (446725/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1757 (fuel : Nat) (hf : 1757 < fuel) :
    walk nodes fuel 1757 = List.range' 1743 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1757).rule = .split 2 (545/128) 1755 1756 := by rfl
      simp only [walk, hr]
      rw [traversal_1755 f (by omega), traversal_1756 f (by omega)]
      change (List.range' 1743 13 ++ List.range' (1743+13) 1) ++
        [1743+(13+1)] = List.range' 1743 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1743) (n := 13+1)).symm

private theorem traversal_1758 (fuel : Nat) (hf : 1758 < fuel) :
    walk nodes fuel 1758 = List.range' 1758 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1758).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1759 (fuel : Nat) (hf : 1759 < fuel) :
    walk nodes fuel 1759 = List.range' 1743 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1759).rule = .split 1 (15/32) 1757 1758 := by rfl
      simp only [walk, hr]
      rw [traversal_1757 f (by omega), traversal_1758 f (by omega)]
      change (List.range' 1743 15 ++ List.range' (1743+15) 1) ++
        [1743+(15+1)] = List.range' 1743 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1743) (n := 15+1)).symm

private theorem traversal_1760 (fuel : Nat) (hf : 1760 < fuel) :
    walk nodes fuel 1760 = List.range' 1760 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1760).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1761 (fuel : Nat) (hf : 1761 < fuel) :
    walk nodes fuel 1761 = List.range' 1743 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1761).rule = .split 0 (1/40) 1759 1760 := by rfl
      simp only [walk, hr]
      rw [traversal_1759 f (by omega), traversal_1760 f (by omega)]
      change (List.range' 1743 17 ++ List.range' (1743+17) 1) ++
        [1743+(17+1)] = List.range' 1743 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1743) (n := 17+1)).symm

private theorem traversal_1762 (fuel : Nat) (hf : 1762 < fuel) :
    walk nodes fuel 1762 = List.range' 1738 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1762).rule = .split 3 (45/16) 1742 1761 := by rfl
      simp only [walk, hr]
      rw [traversal_1742 f (by omega), traversal_1761 f (by omega)]
      change (List.range' 1738 5 ++ List.range' (1738+5) 19) ++
        [1738+(5+19)] = List.range' 1738 ((5+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1738) (n := 5+19)).symm

private theorem traversal_1763 (fuel : Nat) (hf : 1763 < fuel) :
    walk nodes fuel 1763 = List.range' 1717 47 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1763).rule = .split 2 (263/64) 1737 1762 := by rfl
      simp only [walk, hr]
      rw [traversal_1737 f (by omega), traversal_1762 f (by omega)]
      change (List.range' 1717 21 ++ List.range' (1717+21) 25) ++
        [1717+(21+25)] = List.range' 1717 ((21+25)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1717) (n := 21+25)).symm

private theorem traversal_1764 (fuel : Nat) (hf : 1764 < fuel) :
    walk nodes fuel 1764 = List.range' 1608 157 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1764).rule = .split 1 (5/16) 1716 1763 := by rfl
      simp only [walk, hr]
      rw [traversal_1716 f (by omega), traversal_1763 f (by omega)]
      change (List.range' 1608 109 ++ List.range' (1608+109) 47) ++
        [1608+(109+47)] = List.range' 1608 ((109+47)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1608) (n := 109+47)).symm

private theorem traversal_1765 (fuel : Nat) (hf : 1765 < fuel) :
    walk nodes fuel 1765 = List.range' 1765 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1765).rule = .bound .rightEnd 6 (4969/16384) (864095/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1766 (fuel : Nat) (hf : 1766 < fuel) :
    walk nodes fuel 1766 = List.range' 1766 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1766).rule = .bound .rightEnd 3 (4969/16384) (864095/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1767 (fuel : Nat) (hf : 1767 < fuel) :
    walk nodes fuel 1767 = List.range' 1765 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1767).rule = .split 0 (3/40) 1765 1766 := by rfl
      simp only [walk, hr]
      rw [traversal_1765 f (by omega), traversal_1766 f (by omega)]
      change (List.range' 1765 1 ++ List.range' (1765+1) 1) ++
        [1765+(1+1)] = List.range' 1765 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1765) (n := 1+1)).symm

private theorem traversal_1768 (fuel : Nat) (hf : 1768 < fuel) :
    walk nodes fuel 1768 = List.range' 1768 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1768).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1769 (fuel : Nat) (hf : 1769 < fuel) :
    walk nodes fuel 1769 = List.range' 1765 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1769).rule = .split 3 (45/16) 1767 1768 := by rfl
      simp only [walk, hr]
      rw [traversal_1767 f (by omega), traversal_1768 f (by omega)]
      change (List.range' 1765 3 ++ List.range' (1765+3) 1) ++
        [1765+(3+1)] = List.range' 1765 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1765) (n := 3+1)).symm

private theorem traversal_1770 (fuel : Nat) (hf : 1770 < fuel) :
    walk nodes fuel 1770 = List.range' 1770 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1770).rule = .bound .rightEnd 3 (117299/393216) (438897/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1771 (fuel : Nat) (hf : 1771 < fuel) :
    walk nodes fuel 1771 = List.range' 1765 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1771).rule = .split 2 (263/64) 1769 1770 := by rfl
      simp only [walk, hr]
      rw [traversal_1769 f (by omega), traversal_1770 f (by omega)]
      change (List.range' 1765 5 ++ List.range' (1765+5) 1) ++
        [1765+(5+1)] = List.range' 1765 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1765) (n := 5+1)).symm

private theorem traversal_1772 (fuel : Nat) (hf : 1772 < fuel) :
    walk nodes fuel 1772 = List.range' 1772 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1772).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1773 (fuel : Nat) (hf : 1773 < fuel) :
    walk nodes fuel 1773 = List.range' 1765 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1773).rule = .split 1 (5/16) 1771 1772 := by rfl
      simp only [walk, hr]
      rw [traversal_1771 f (by omega), traversal_1772 f (by omega)]
      change (List.range' 1765 7 ++ List.range' (1765+7) 1) ++
        [1765+(7+1)] = List.range' 1765 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1765) (n := 7+1)).symm

private theorem traversal_1774 (fuel : Nat) (hf : 1774 < fuel) :
    walk nodes fuel 1774 = List.range' 1608 167 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1774).rule = .split 0 (1/20) 1764 1773 := by rfl
      simp only [walk, hr]
      rw [traversal_1764 f (by omega), traversal_1773 f (by omega)]
      change (List.range' 1608 157 ++ List.range' (1608+157) 9) ++
        [1608+(157+9)] = List.range' 1608 ((157+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1608) (n := 157+9)).symm

theorem traversal_1775 (fuel : Nat) (hf : 1775 < fuel) :
    walk nodes fuel 1775 = List.range' 1607 169 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1775).rule = .split 3 (21/8) 1607 1774 := by rfl
      simp only [walk, hr]
      rw [traversal_1607 f (by omega), traversal_1774 f (by omega)]
      change (List.range' 1607 1 ++ List.range' (1607+1) 167) ++
        [1607+(1+167)] = List.range' 1607 ((1+167)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1607) (n := 1+167)).symm

theorem traversal_1776 (fuel : Nat) (hf : 1776 < fuel) :
    walk nodes fuel 1776 = List.range' 1776 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1776).rule = .bound .rightEnd 6 (126023/393216) (408363/524288) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1777 (fuel : Nat) (hf : 1777 < fuel) :
    walk nodes fuel 1777 = List.range' 1777 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1777).rule = .bound .rightEnd 6 (4969/16384) (864095/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1778 (fuel : Nat) (hf : 1778 < fuel) :
    walk nodes fuel 1778 = List.range' 1778 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1778).rule = .bound .rightEnd 0 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1779 (fuel : Nat) (hf : 1779 < fuel) :
    walk nodes fuel 1779 = List.range' 1779 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1779).rule = .bound .rightEnd 0 (14359/49152) (897325/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1780 (fuel : Nat) (hf : 1780 < fuel) :
    walk nodes fuel 1780 = List.range' 1780 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1780).rule = .bound .rightEnd 0 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1781 (fuel : Nat) (hf : 1781 < fuel) :
    walk nodes fuel 1781 = List.range' 1781 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1781).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1782 (fuel : Nat) (hf : 1782 < fuel) :
    walk nodes fuel 1782 = List.range' 1780 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1782).rule = .split 3 (381/128) 1780 1781 := by rfl
      simp only [walk, hr]
      rw [traversal_1780 f (by omega), traversal_1781 f (by omega)]
      change (List.range' 1780 1 ++ List.range' (1780+1) 1) ++
        [1780+(1+1)] = List.range' 1780 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1780) (n := 1+1)).symm

private theorem traversal_1783 (fuel : Nat) (hf : 1783 < fuel) :
    walk nodes fuel 1783 = List.range' 1783 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1783).rule = .bound .rightEnd 6 (1187/4096) (452285/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1784 (fuel : Nat) (hf : 1784 < fuel) :
    walk nodes fuel 1784 = List.range' 1780 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1784).rule = .split 2 (2275/512) 1782 1783 := by rfl
      simp only [walk, hr]
      rw [traversal_1782 f (by omega), traversal_1783 f (by omega)]
      change (List.range' 1780 3 ++ List.range' (1780+3) 1) ++
        [1780+(3+1)] = List.range' 1780 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1780) (n := 3+1)).symm

private theorem traversal_1785 (fuel : Nat) (hf : 1785 < fuel) :
    walk nodes fuel 1785 = List.range' 1785 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1785).rule = .bound .rightEnd 0 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1786 (fuel : Nat) (hf : 1786 < fuel) :
    walk nodes fuel 1786 = List.range' 1786 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1786).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1787 (fuel : Nat) (hf : 1787 < fuel) :
    walk nodes fuel 1787 = List.range' 1785 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1787).rule = .split 3 (381/128) 1785 1786 := by rfl
      simp only [walk, hr]
      rw [traversal_1785 f (by omega), traversal_1786 f (by omega)]
      change (List.range' 1785 1 ++ List.range' (1785+1) 1) ++
        [1785+(1+1)] = List.range' 1785 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1785) (n := 1+1)).symm

private theorem traversal_1788 (fuel : Nat) (hf : 1788 < fuel) :
    walk nodes fuel 1788 = List.range' 1788 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1788).rule = .bound .rightEnd 0 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1789 (fuel : Nat) (hf : 1789 < fuel) :
    walk nodes fuel 1789 = List.range' 1789 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1789).rule = .bound .rightEnd 6 (1777/6144) (453181/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1790 (fuel : Nat) (hf : 1790 < fuel) :
    walk nodes fuel 1790 = List.range' 1790 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1790).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1791 (fuel : Nat) (hf : 1791 < fuel) :
    walk nodes fuel 1791 = List.range' 1791 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1791).rule = .bound .rightEnd 6 (1777/6144) (453181/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1792 (fuel : Nat) (hf : 1792 < fuel) :
    walk nodes fuel 1792 = List.range' 1790 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1792).rule = .split 2 (4569/1024) 1790 1791 := by rfl
      simp only [walk, hr]
      rw [traversal_1790 f (by omega), traversal_1791 f (by omega)]
      change (List.range' 1790 1 ++ List.range' (1790+1) 1) ++
        [1790+(1+1)] = List.range' 1790 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1790) (n := 1+1)).symm

private theorem traversal_1793 (fuel : Nat) (hf : 1793 < fuel) :
    walk nodes fuel 1793 = List.range' 1793 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1793).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1794 (fuel : Nat) (hf : 1794 < fuel) :
    walk nodes fuel 1794 = List.range' 1794 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1794).rule = .bound .rightEnd 0 (593/2048) (452673/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1795 (fuel : Nat) (hf : 1795 < fuel) :
    walk nodes fuel 1795 = List.range' 1795 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1795).rule = .infeasible 13 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1796 (fuel : Nat) (hf : 1796 < fuel) :
    walk nodes fuel 1796 = List.range' 1794 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1796).rule = .split 3 (765/256) 1794 1795 := by rfl
      simp only [walk, hr]
      rw [traversal_1794 f (by omega), traversal_1795 f (by omega)]
      change (List.range' 1794 1 ++ List.range' (1794+1) 1) ++
        [1794+(1+1)] = List.range' 1794 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1794) (n := 1+1)).symm

private theorem traversal_1797 (fuel : Nat) (hf : 1797 < fuel) :
    walk nodes fuel 1797 = List.range' 1793 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1797).rule = .split 2 (4569/1024) 1793 1796 := by rfl
      simp only [walk, hr]
      rw [traversal_1793 f (by omega), traversal_1796 f (by omega)]
      change (List.range' 1793 1 ++ List.range' (1793+1) 3) ++
        [1793+(1+3)] = List.range' 1793 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1793) (n := 1+3)).symm

private theorem traversal_1798 (fuel : Nat) (hf : 1798 < fuel) :
    walk nodes fuel 1798 = List.range' 1790 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1798).rule = .split 1 (15/256) 1792 1797 := by rfl
      simp only [walk, hr]
      rw [traversal_1792 f (by omega), traversal_1797 f (by omega)]
      change (List.range' 1790 3 ++ List.range' (1790+3) 5) ++
        [1790+(3+5)] = List.range' 1790 ((3+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1790) (n := 3+5)).symm

private theorem traversal_1799 (fuel : Nat) (hf : 1799 < fuel) :
    walk nodes fuel 1799 = List.range' 1789 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1799).rule = .split 0 (1/320) 1789 1798 := by rfl
      simp only [walk, hr]
      rw [traversal_1789 f (by omega), traversal_1798 f (by omega)]
      change (List.range' 1789 1 ++ List.range' (1789+1) 9) ++
        [1789+(1+9)] = List.range' 1789 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1789) (n := 1+9)).symm

private theorem traversal_1800 (fuel : Nat) (hf : 1800 < fuel) :
    walk nodes fuel 1800 = List.range' 1788 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1800).rule = .split 3 (381/128) 1788 1799 := by rfl
      simp only [walk, hr]
      rw [traversal_1788 f (by omega), traversal_1799 f (by omega)]
      change (List.range' 1788 1 ++ List.range' (1788+1) 11) ++
        [1788+(1+11)] = List.range' 1788 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1788) (n := 1+11)).symm

private theorem traversal_1801 (fuel : Nat) (hf : 1801 < fuel) :
    walk nodes fuel 1801 = List.range' 1785 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1801).rule = .split 2 (2275/512) 1787 1800 := by rfl
      simp only [walk, hr]
      rw [traversal_1787 f (by omega), traversal_1800 f (by omega)]
      change (List.range' 1785 3 ++ List.range' (1785+3) 13) ++
        [1785+(3+13)] = List.range' 1785 ((3+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1785) (n := 3+13)).symm

theorem traversal_1802 (fuel : Nat) (hf : 1802 < fuel) :
    walk nodes fuel 1802 = List.range' 1780 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1802).rule = .split 1 (5/128) 1784 1801 := by rfl
      simp only [walk, hr]
      rw [traversal_1784 f (by omega), traversal_1801 f (by omega)]
      change (List.range' 1780 5 ++ List.range' (1780+5) 17) ++
        [1780+(5+17)] = List.range' 1780 ((5+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1780) (n := 5+17)).symm

private theorem traversal_1803 (fuel : Nat) (hf : 1803 < fuel) :
    walk nodes fuel 1803 = List.range' 1803 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1803).rule = .bound .rightEnd 0 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1804 (fuel : Nat) (hf : 1804 < fuel) :
    walk nodes fuel 1804 = List.range' 1804 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1804).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1805 (fuel : Nat) (hf : 1805 < fuel) :
    walk nodes fuel 1805 = List.range' 1803 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1805).rule = .split 3 (381/128) 1803 1804 := by rfl
      simp only [walk, hr]
      rw [traversal_1803 f (by omega), traversal_1804 f (by omega)]
      change (List.range' 1803 1 ++ List.range' (1803+1) 1) ++
        [1803+(1+1)] = List.range' 1803 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1803) (n := 1+1)).symm

theorem traversal_1806 (fuel : Nat) (hf : 1806 < fuel) :
    walk nodes fuel 1806 = List.range' 1806 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1806).rule = .bound .rightEnd 0 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
