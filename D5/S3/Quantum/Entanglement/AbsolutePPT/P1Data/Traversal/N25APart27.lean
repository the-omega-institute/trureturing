/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart27
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart27
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart27.traversal_1851,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart27.traversal_1852,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart27.traversal_1873
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart26
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1807 (fuel : Nat) (hf : 1807 < fuel) :
    walk nodes fuel 1807 = List.range' 1807 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1807).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1808 (fuel : Nat) (hf : 1808 < fuel) :
    walk nodes fuel 1808 = List.range' 1808 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1808).rule = .bound .rightEnd 0 (1777/6144) (453181/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1809 (fuel : Nat) (hf : 1809 < fuel) :
    walk nodes fuel 1809 = List.range' 1807 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1809).rule = .split 2 (4569/1024) 1807 1808 := by rfl
      simp only [walk, hr]
      rw [traversal_1807 f (by omega), traversal_1808 f (by omega)]
      change (List.range' 1807 1 ++ List.range' (1807+1) 1) ++
        [1807+(1+1)] = List.range' 1807 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1807) (n := 1+1)).symm

private theorem traversal_1810 (fuel : Nat) (hf : 1810 < fuel) :
    walk nodes fuel 1810 = List.range' 1810 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1810).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1811 (fuel : Nat) (hf : 1811 < fuel) :
    walk nodes fuel 1811 = List.range' 1811 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1811).rule = .bound .rightEnd 0 (593/2048) (452673/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1812 (fuel : Nat) (hf : 1812 < fuel) :
    walk nodes fuel 1812 = List.range' 1812 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1812).rule = .infeasible 4 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1813 (fuel : Nat) (hf : 1813 < fuel) :
    walk nodes fuel 1813 = List.range' 1811 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1813).rule = .split 3 (765/256) 1811 1812 := by rfl
      simp only [walk, hr]
      rw [traversal_1811 f (by omega), traversal_1812 f (by omega)]
      change (List.range' 1811 1 ++ List.range' (1811+1) 1) ++
        [1811+(1+1)] = List.range' 1811 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1811) (n := 1+1)).symm

private theorem traversal_1814 (fuel : Nat) (hf : 1814 < fuel) :
    walk nodes fuel 1814 = List.range' 1810 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1814).rule = .split 2 (4569/1024) 1810 1813 := by rfl
      simp only [walk, hr]
      rw [traversal_1810 f (by omega), traversal_1813 f (by omega)]
      change (List.range' 1810 1 ++ List.range' (1810+1) 3) ++
        [1810+(1+3)] = List.range' 1810 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1810) (n := 1+3)).symm

private theorem traversal_1815 (fuel : Nat) (hf : 1815 < fuel) :
    walk nodes fuel 1815 = List.range' 1807 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1815).rule = .split 1 (5/256) 1809 1814 := by rfl
      simp only [walk, hr]
      rw [traversal_1809 f (by omega), traversal_1814 f (by omega)]
      change (List.range' 1807 3 ++ List.range' (1807+3) 5) ++
        [1807+(3+5)] = List.range' 1807 ((3+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1807) (n := 3+5)).symm

private theorem traversal_1816 (fuel : Nat) (hf : 1816 < fuel) :
    walk nodes fuel 1816 = List.range' 1816 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1816).rule = .infeasible 4 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1817 (fuel : Nat) (hf : 1817 < fuel) :
    walk nodes fuel 1817 = List.range' 1807 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1817).rule = .split 0 (3/320) 1815 1816 := by rfl
      simp only [walk, hr]
      rw [traversal_1815 f (by omega), traversal_1816 f (by omega)]
      change (List.range' 1807 9 ++ List.range' (1807+9) 1) ++
        [1807+(9+1)] = List.range' 1807 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1807) (n := 9+1)).symm

private theorem traversal_1818 (fuel : Nat) (hf : 1818 < fuel) :
    walk nodes fuel 1818 = List.range' 1806 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1818).rule = .split 3 (381/128) 1806 1817 := by rfl
      simp only [walk, hr]
      rw [traversal_1806 f (by omega), traversal_1817 f (by omega)]
      change (List.range' 1806 1 ++ List.range' (1806+1) 11) ++
        [1806+(1+11)] = List.range' 1806 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1806) (n := 1+11)).symm

private theorem traversal_1819 (fuel : Nat) (hf : 1819 < fuel) :
    walk nodes fuel 1819 = List.range' 1803 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1819).rule = .split 2 (2275/512) 1805 1818 := by rfl
      simp only [walk, hr]
      rw [traversal_1805 f (by omega), traversal_1818 f (by omega)]
      change (List.range' 1803 3 ++ List.range' (1803+3) 13) ++
        [1803+(3+13)] = List.range' 1803 ((3+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1803) (n := 3+13)).symm

private theorem traversal_1820 (fuel : Nat) (hf : 1820 < fuel) :
    walk nodes fuel 1820 = List.range' 1820 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1820).rule = .bound .rightEnd 6 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1821 (fuel : Nat) (hf : 1821 < fuel) :
    walk nodes fuel 1821 = List.range' 1821 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1821).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1822 (fuel : Nat) (hf : 1822 < fuel) :
    walk nodes fuel 1822 = List.range' 1820 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1822).rule = .split 3 (381/128) 1820 1821 := by rfl
      simp only [walk, hr]
      rw [traversal_1820 f (by omega), traversal_1821 f (by omega)]
      change (List.range' 1820 1 ++ List.range' (1820+1) 1) ++
        [1820+(1+1)] = List.range' 1820 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1820) (n := 1+1)).symm

private theorem traversal_1823 (fuel : Nat) (hf : 1823 < fuel) :
    walk nodes fuel 1823 = List.range' 1823 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1823).rule = .bound .rightEnd 0 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1824 (fuel : Nat) (hf : 1824 < fuel) :
    walk nodes fuel 1824 = List.range' 1824 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1824).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1825 (fuel : Nat) (hf : 1825 < fuel) :
    walk nodes fuel 1825 = List.range' 1825 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1825).rule = .bound .rightEnd 0 (593/2048) (452673/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1826 (fuel : Nat) (hf : 1826 < fuel) :
    walk nodes fuel 1826 = List.range' 1826 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1826).rule = .infeasible 4 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1827 (fuel : Nat) (hf : 1827 < fuel) :
    walk nodes fuel 1827 = List.range' 1825 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1827).rule = .split 3 (765/256) 1825 1826 := by rfl
      simp only [walk, hr]
      rw [traversal_1825 f (by omega), traversal_1826 f (by omega)]
      change (List.range' 1825 1 ++ List.range' (1825+1) 1) ++
        [1825+(1+1)] = List.range' 1825 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1825) (n := 1+1)).symm

private theorem traversal_1828 (fuel : Nat) (hf : 1828 < fuel) :
    walk nodes fuel 1828 = List.range' 1824 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1828).rule = .split 2 (4569/1024) 1824 1827 := by rfl
      simp only [walk, hr]
      rw [traversal_1824 f (by omega), traversal_1827 f (by omega)]
      change (List.range' 1824 1 ++ List.range' (1824+1) 3) ++
        [1824+(1+3)] = List.range' 1824 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1824) (n := 1+3)).symm

private theorem traversal_1829 (fuel : Nat) (hf : 1829 < fuel) :
    walk nodes fuel 1829 = List.range' 1829 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1829).rule = .infeasible 13 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1830 (fuel : Nat) (hf : 1830 < fuel) :
    walk nodes fuel 1830 = List.range' 1824 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1830).rule = .split 1 (15/256) 1828 1829 := by rfl
      simp only [walk, hr]
      rw [traversal_1828 f (by omega), traversal_1829 f (by omega)]
      change (List.range' 1824 5 ++ List.range' (1824+5) 1) ++
        [1824+(5+1)] = List.range' 1824 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1824) (n := 5+1)).symm

private theorem traversal_1831 (fuel : Nat) (hf : 1831 < fuel) :
    walk nodes fuel 1831 = List.range' 1831 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1831).rule = .infeasible 4 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1832 (fuel : Nat) (hf : 1832 < fuel) :
    walk nodes fuel 1832 = List.range' 1824 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1832).rule = .split 0 (3/320) 1830 1831 := by rfl
      simp only [walk, hr]
      rw [traversal_1830 f (by omega), traversal_1831 f (by omega)]
      change (List.range' 1824 7 ++ List.range' (1824+7) 1) ++
        [1824+(7+1)] = List.range' 1824 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1824) (n := 7+1)).symm

private theorem traversal_1833 (fuel : Nat) (hf : 1833 < fuel) :
    walk nodes fuel 1833 = List.range' 1823 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1833).rule = .split 3 (381/128) 1823 1832 := by rfl
      simp only [walk, hr]
      rw [traversal_1823 f (by omega), traversal_1832 f (by omega)]
      change (List.range' 1823 1 ++ List.range' (1823+1) 9) ++
        [1823+(1+9)] = List.range' 1823 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1823) (n := 1+9)).symm

private theorem traversal_1834 (fuel : Nat) (hf : 1834 < fuel) :
    walk nodes fuel 1834 = List.range' 1820 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1834).rule = .split 2 (2275/512) 1822 1833 := by rfl
      simp only [walk, hr]
      rw [traversal_1822 f (by omega), traversal_1833 f (by omega)]
      change (List.range' 1820 3 ++ List.range' (1820+3) 11) ++
        [1820+(3+11)] = List.range' 1820 ((3+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1820) (n := 3+11)).symm

private theorem traversal_1835 (fuel : Nat) (hf : 1835 < fuel) :
    walk nodes fuel 1835 = List.range' 1803 33 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1835).rule = .split 1 (5/128) 1819 1834 := by rfl
      simp only [walk, hr]
      rw [traversal_1819 f (by omega), traversal_1834 f (by omega)]
      change (List.range' 1803 17 ++ List.range' (1803+17) 15) ++
        [1803+(17+15)] = List.range' 1803 ((17+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1803) (n := 17+15)).symm

private theorem traversal_1836 (fuel : Nat) (hf : 1836 < fuel) :
    walk nodes fuel 1836 = List.range' 1780 57 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1836).rule = .split 0 (1/160) 1802 1835 := by rfl
      simp only [walk, hr]
      rw [traversal_1802 f (by omega), traversal_1835 f (by omega)]
      change (List.range' 1780 23 ++ List.range' (1780+23) 33) ++
        [1780+(23+33)] = List.range' 1780 ((23+33)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1780) (n := 23+33)).symm

private theorem traversal_1837 (fuel : Nat) (hf : 1837 < fuel) :
    walk nodes fuel 1837 = List.range' 1779 59 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1837).rule = .split 3 (189/64) 1779 1836 := by rfl
      simp only [walk, hr]
      rw [traversal_1779 f (by omega), traversal_1836 f (by omega)]
      change (List.range' 1779 1 ++ List.range' (1779+1) 57) ++
        [1779+(1+57)] = List.range' 1779 ((1+57)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1779) (n := 1+57)).symm

private theorem traversal_1838 (fuel : Nat) (hf : 1838 < fuel) :
    walk nodes fuel 1838 = List.range' 1838 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1838).rule = .bound .rightEnd 0 (14359/49152) (897325/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1839 (fuel : Nat) (hf : 1839 < fuel) :
    walk nodes fuel 1839 = List.range' 1839 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1839).rule = .bound .rightEnd 6 (1187/4096) (452285/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1840 (fuel : Nat) (hf : 1840 < fuel) :
    walk nodes fuel 1840 = List.range' 1840 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1840).rule = .bound .rightEnd 0 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1841 (fuel : Nat) (hf : 1841 < fuel) :
    walk nodes fuel 1841 = List.range' 1841 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1841).rule = .bound .rightEnd 6 (1777/6144) (453181/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1842 (fuel : Nat) (hf : 1842 < fuel) :
    walk nodes fuel 1842 = List.range' 1842 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1842).rule = .infeasible 4 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1843 (fuel : Nat) (hf : 1843 < fuel) :
    walk nodes fuel 1843 = List.range' 1841 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1843).rule = .split 0 (3/320) 1841 1842 := by rfl
      simp only [walk, hr]
      rw [traversal_1841 f (by omega), traversal_1842 f (by omega)]
      change (List.range' 1841 1 ++ List.range' (1841+1) 1) ++
        [1841+(1+1)] = List.range' 1841 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1841) (n := 1+1)).symm

private theorem traversal_1844 (fuel : Nat) (hf : 1844 < fuel) :
    walk nodes fuel 1844 = List.range' 1840 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1844).rule = .split 3 (381/128) 1840 1843 := by rfl
      simp only [walk, hr]
      rw [traversal_1840 f (by omega), traversal_1843 f (by omega)]
      change (List.range' 1840 1 ++ List.range' (1840+1) 3) ++
        [1840+(1+3)] = List.range' 1840 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1840) (n := 1+3)).symm

private theorem traversal_1845 (fuel : Nat) (hf : 1845 < fuel) :
    walk nodes fuel 1845 = List.range' 1845 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1845).rule = .bound .rightEnd 3 (1187/4096) (452285/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1846 (fuel : Nat) (hf : 1846 < fuel) :
    walk nodes fuel 1846 = List.range' 1840 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1846).rule = .split 2 (2313/512) 1844 1845 := by rfl
      simp only [walk, hr]
      rw [traversal_1844 f (by omega), traversal_1845 f (by omega)]
      change (List.range' 1840 5 ++ List.range' (1840+5) 1) ++
        [1840+(5+1)] = List.range' 1840 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1840) (n := 5+1)).symm

private theorem traversal_1847 (fuel : Nat) (hf : 1847 < fuel) :
    walk nodes fuel 1847 = List.range' 1847 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1847).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1848 (fuel : Nat) (hf : 1848 < fuel) :
    walk nodes fuel 1848 = List.range' 1840 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1848).rule = .split 1 (5/128) 1846 1847 := by rfl
      simp only [walk, hr]
      rw [traversal_1846 f (by omega), traversal_1847 f (by omega)]
      change (List.range' 1840 7 ++ List.range' (1840+7) 1) ++
        [1840+(7+1)] = List.range' 1840 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1840) (n := 7+1)).symm

private theorem traversal_1849 (fuel : Nat) (hf : 1849 < fuel) :
    walk nodes fuel 1849 = List.range' 1839 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1849).rule = .split 0 (1/160) 1839 1848 := by rfl
      simp only [walk, hr]
      rw [traversal_1839 f (by omega), traversal_1848 f (by omega)]
      change (List.range' 1839 1 ++ List.range' (1839+1) 9) ++
        [1839+(1+9)] = List.range' 1839 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1839) (n := 1+9)).symm

private theorem traversal_1850 (fuel : Nat) (hf : 1850 < fuel) :
    walk nodes fuel 1850 = List.range' 1838 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1850).rule = .split 3 (189/64) 1838 1849 := by rfl
      simp only [walk, hr]
      rw [traversal_1838 f (by omega), traversal_1849 f (by omega)]
      change (List.range' 1838 1 ++ List.range' (1838+1) 11) ++
        [1838+(1+11)] = List.range' 1838 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1838) (n := 1+11)).symm

theorem traversal_1851 (fuel : Nat) (hf : 1851 < fuel) :
    walk nodes fuel 1851 = List.range' 1779 73 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1851).rule = .split 2 (1147/256) 1837 1850 := by rfl
      simp only [walk, hr]
      rw [traversal_1837 f (by omega), traversal_1850 f (by omega)]
      change (List.range' 1779 59 ++ List.range' (1779+59) 13) ++
        [1779+(59+13)] = List.range' 1779 ((59+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1779) (n := 59+13)).symm

theorem traversal_1852 (fuel : Nat) (hf : 1852 < fuel) :
    walk nodes fuel 1852 = List.range' 1852 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1852).rule = .bound .rightEnd 6 (14359/49152) (897325/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1853 (fuel : Nat) (hf : 1853 < fuel) :
    walk nodes fuel 1853 = List.range' 1853 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1853).rule = .bound .rightEnd 6 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1854 (fuel : Nat) (hf : 1854 < fuel) :
    walk nodes fuel 1854 = List.range' 1854 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1854).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1855 (fuel : Nat) (hf : 1855 < fuel) :
    walk nodes fuel 1855 = List.range' 1853 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1855).rule = .split 3 (381/128) 1853 1854 := by rfl
      simp only [walk, hr]
      rw [traversal_1853 f (by omega), traversal_1854 f (by omega)]
      change (List.range' 1853 1 ++ List.range' (1853+1) 1) ++
        [1853+(1+1)] = List.range' 1853 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1853) (n := 1+1)).symm

private theorem traversal_1856 (fuel : Nat) (hf : 1856 < fuel) :
    walk nodes fuel 1856 = List.range' 1856 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1856).rule = .bound .rightEnd 6 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1857 (fuel : Nat) (hf : 1857 < fuel) :
    walk nodes fuel 1857 = List.range' 1857 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1857).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1858 (fuel : Nat) (hf : 1858 < fuel) :
    walk nodes fuel 1858 = List.range' 1858 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1858).rule = .bound .rightEnd 6 (1777/6144) (453181/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1859 (fuel : Nat) (hf : 1859 < fuel) :
    walk nodes fuel 1859 = List.range' 1857 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1859).rule = .split 2 (4569/1024) 1857 1858 := by rfl
      simp only [walk, hr]
      rw [traversal_1857 f (by omega), traversal_1858 f (by omega)]
      change (List.range' 1857 1 ++ List.range' (1857+1) 1) ++
        [1857+(1+1)] = List.range' 1857 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1857) (n := 1+1)).symm

private theorem traversal_1860 (fuel : Nat) (hf : 1860 < fuel) :
    walk nodes fuel 1860 = List.range' 1860 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1860).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1861 (fuel : Nat) (hf : 1861 < fuel) :
    walk nodes fuel 1861 = List.range' 1861 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1861).rule = .bound .rightEnd 6 (593/2048) (452673/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1862 (fuel : Nat) (hf : 1862 < fuel) :
    walk nodes fuel 1862 = List.range' 1862 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1862).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1863 (fuel : Nat) (hf : 1863 < fuel) :
    walk nodes fuel 1863 = List.range' 1861 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1863).rule = .split 3 (765/256) 1861 1862 := by rfl
      simp only [walk, hr]
      rw [traversal_1861 f (by omega), traversal_1862 f (by omega)]
      change (List.range' 1861 1 ++ List.range' (1861+1) 1) ++
        [1861+(1+1)] = List.range' 1861 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1861) (n := 1+1)).symm

private theorem traversal_1864 (fuel : Nat) (hf : 1864 < fuel) :
    walk nodes fuel 1864 = List.range' 1860 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1864).rule = .split 2 (4569/1024) 1860 1863 := by rfl
      simp only [walk, hr]
      rw [traversal_1860 f (by omega), traversal_1863 f (by omega)]
      change (List.range' 1860 1 ++ List.range' (1860+1) 3) ++
        [1860+(1+3)] = List.range' 1860 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1860) (n := 1+3)).symm

private theorem traversal_1865 (fuel : Nat) (hf : 1865 < fuel) :
    walk nodes fuel 1865 = List.range' 1857 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1865).rule = .split 1 (25/256) 1859 1864 := by rfl
      simp only [walk, hr]
      rw [traversal_1859 f (by omega), traversal_1864 f (by omega)]
      change (List.range' 1857 3 ++ List.range' (1857+3) 5) ++
        [1857+(3+5)] = List.range' 1857 ((3+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1857) (n := 3+5)).symm

private theorem traversal_1866 (fuel : Nat) (hf : 1866 < fuel) :
    walk nodes fuel 1866 = List.range' 1866 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1866).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1867 (fuel : Nat) (hf : 1867 < fuel) :
    walk nodes fuel 1867 = List.range' 1867 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1867).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1868 (fuel : Nat) (hf : 1868 < fuel) :
    walk nodes fuel 1868 = List.range' 1866 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1868).rule = .split 2 (4569/1024) 1866 1867 := by rfl
      simp only [walk, hr]
      rw [traversal_1866 f (by omega), traversal_1867 f (by omega)]
      change (List.range' 1866 1 ++ List.range' (1866+1) 1) ++
        [1866+(1+1)] = List.range' 1866 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1866) (n := 1+1)).symm

private theorem traversal_1869 (fuel : Nat) (hf : 1869 < fuel) :
    walk nodes fuel 1869 = List.range' 1869 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1869).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1870 (fuel : Nat) (hf : 1870 < fuel) :
    walk nodes fuel 1870 = List.range' 1866 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1870).rule = .split 1 (25/256) 1868 1869 := by rfl
      simp only [walk, hr]
      rw [traversal_1868 f (by omega), traversal_1869 f (by omega)]
      change (List.range' 1866 3 ++ List.range' (1866+3) 1) ++
        [1866+(3+1)] = List.range' 1866 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1866) (n := 3+1)).symm

private theorem traversal_1871 (fuel : Nat) (hf : 1871 < fuel) :
    walk nodes fuel 1871 = List.range' 1857 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1871).rule = .split 0 (1/320) 1865 1870 := by rfl
      simp only [walk, hr]
      rw [traversal_1865 f (by omega), traversal_1870 f (by omega)]
      change (List.range' 1857 9 ++ List.range' (1857+9) 5) ++
        [1857+(9+5)] = List.range' 1857 ((9+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1857) (n := 9+5)).symm

private theorem traversal_1872 (fuel : Nat) (hf : 1872 < fuel) :
    walk nodes fuel 1872 = List.range' 1856 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1872).rule = .split 3 (381/128) 1856 1871 := by rfl
      simp only [walk, hr]
      rw [traversal_1856 f (by omega), traversal_1871 f (by omega)]
      change (List.range' 1856 1 ++ List.range' (1856+1) 15) ++
        [1856+(1+15)] = List.range' 1856 ((1+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1856) (n := 1+15)).symm

theorem traversal_1873 (fuel : Nat) (hf : 1873 < fuel) :
    walk nodes fuel 1873 = List.range' 1853 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1873).rule = .split 2 (2275/512) 1855 1872 := by rfl
      simp only [walk, hr]
      rw [traversal_1855 f (by omega), traversal_1872 f (by omega)]
      change (List.range' 1853 3 ++ List.range' (1853+3) 17) ++
        [1853+(3+17)] = List.range' 1853 ((3+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1853) (n := 3+17)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
