/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart28
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart28
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart28.traversal_1936,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart28.traversal_1937,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart28.traversal_1940
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart26
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart27
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1874 (fuel : Nat) (hf : 1874 < fuel) :
    walk nodes fuel 1874 = List.range' 1874 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1874).rule = .bound .rightEnd 6 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1875 (fuel : Nat) (hf : 1875 < fuel) :
    walk nodes fuel 1875 = List.range' 1875 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1875).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1876 (fuel : Nat) (hf : 1876 < fuel) :
    walk nodes fuel 1876 = List.range' 1874 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1876).rule = .split 3 (381/128) 1874 1875 := by rfl
      simp only [walk, hr]
      rw [traversal_1874 f (by omega), traversal_1875 f (by omega)]
      change (List.range' 1874 1 ++ List.range' (1874+1) 1) ++
        [1874+(1+1)] = List.range' 1874 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1874) (n := 1+1)).symm

private theorem traversal_1877 (fuel : Nat) (hf : 1877 < fuel) :
    walk nodes fuel 1877 = List.range' 1877 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1877).rule = .bound .rightEnd 6 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1878 (fuel : Nat) (hf : 1878 < fuel) :
    walk nodes fuel 1878 = List.range' 1878 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1878).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1879 (fuel : Nat) (hf : 1879 < fuel) :
    walk nodes fuel 1879 = List.range' 1879 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1879).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1880 (fuel : Nat) (hf : 1880 < fuel) :
    walk nodes fuel 1880 = List.range' 1878 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1880).rule = .split 2 (4569/1024) 1878 1879 := by rfl
      simp only [walk, hr]
      rw [traversal_1878 f (by omega), traversal_1879 f (by omega)]
      change (List.range' 1878 1 ++ List.range' (1878+1) 1) ++
        [1878+(1+1)] = List.range' 1878 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1878) (n := 1+1)).symm

private theorem traversal_1881 (fuel : Nat) (hf : 1881 < fuel) :
    walk nodes fuel 1881 = List.range' 1881 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1881).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1882 (fuel : Nat) (hf : 1882 < fuel) :
    walk nodes fuel 1882 = List.range' 1878 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1882).rule = .split 1 (35/256) 1880 1881 := by rfl
      simp only [walk, hr]
      rw [traversal_1880 f (by omega), traversal_1881 f (by omega)]
      change (List.range' 1878 3 ++ List.range' (1878+3) 1) ++
        [1878+(3+1)] = List.range' 1878 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1878) (n := 3+1)).symm

private theorem traversal_1883 (fuel : Nat) (hf : 1883 < fuel) :
    walk nodes fuel 1883 = List.range' 1883 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1883).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1884 (fuel : Nat) (hf : 1884 < fuel) :
    walk nodes fuel 1884 = List.range' 1878 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1884).rule = .split 0 (1/320) 1882 1883 := by rfl
      simp only [walk, hr]
      rw [traversal_1882 f (by omega), traversal_1883 f (by omega)]
      change (List.range' 1878 5 ++ List.range' (1878+5) 1) ++
        [1878+(5+1)] = List.range' 1878 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1878) (n := 5+1)).symm

private theorem traversal_1885 (fuel : Nat) (hf : 1885 < fuel) :
    walk nodes fuel 1885 = List.range' 1877 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1885).rule = .split 3 (381/128) 1877 1884 := by rfl
      simp only [walk, hr]
      rw [traversal_1877 f (by omega), traversal_1884 f (by omega)]
      change (List.range' 1877 1 ++ List.range' (1877+1) 7) ++
        [1877+(1+7)] = List.range' 1877 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1877) (n := 1+7)).symm

private theorem traversal_1886 (fuel : Nat) (hf : 1886 < fuel) :
    walk nodes fuel 1886 = List.range' 1874 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1886).rule = .split 2 (2275/512) 1876 1885 := by rfl
      simp only [walk, hr]
      rw [traversal_1876 f (by omega), traversal_1885 f (by omega)]
      change (List.range' 1874 3 ++ List.range' (1874+3) 9) ++
        [1874+(3+9)] = List.range' 1874 ((3+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1874) (n := 3+9)).symm

private theorem traversal_1887 (fuel : Nat) (hf : 1887 < fuel) :
    walk nodes fuel 1887 = List.range' 1853 35 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1887).rule = .split 1 (15/128) 1873 1886 := by rfl
      simp only [walk, hr]
      rw [traversal_1873 f (by omega), traversal_1886 f (by omega)]
      change (List.range' 1853 21 ++ List.range' (1853+21) 13) ++
        [1853+(21+13)] = List.range' 1853 ((21+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1853) (n := 21+13)).symm

private theorem traversal_1888 (fuel : Nat) (hf : 1888 < fuel) :
    walk nodes fuel 1888 = List.range' 1888 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1888).rule = .bound .rightEnd 6 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1889 (fuel : Nat) (hf : 1889 < fuel) :
    walk nodes fuel 1889 = List.range' 1889 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1889).rule = .infeasible 13 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1890 (fuel : Nat) (hf : 1890 < fuel) :
    walk nodes fuel 1890 = List.range' 1888 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1890).rule = .split 3 (381/128) 1888 1889 := by rfl
      simp only [walk, hr]
      rw [traversal_1888 f (by omega), traversal_1889 f (by omega)]
      change (List.range' 1888 1 ++ List.range' (1888+1) 1) ++
        [1888+(1+1)] = List.range' 1888 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1888) (n := 1+1)).symm

private theorem traversal_1891 (fuel : Nat) (hf : 1891 < fuel) :
    walk nodes fuel 1891 = List.range' 1891 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1891).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1892 (fuel : Nat) (hf : 1892 < fuel) :
    walk nodes fuel 1892 = List.range' 1888 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1892).rule = .split 2 (2275/512) 1890 1891 := by rfl
      simp only [walk, hr]
      rw [traversal_1890 f (by omega), traversal_1891 f (by omega)]
      change (List.range' 1888 3 ++ List.range' (1888+3) 1) ++
        [1888+(3+1)] = List.range' 1888 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1888) (n := 3+1)).symm

private theorem traversal_1893 (fuel : Nat) (hf : 1893 < fuel) :
    walk nodes fuel 1893 = List.range' 1893 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1893).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1894 (fuel : Nat) (hf : 1894 < fuel) :
    walk nodes fuel 1894 = List.range' 1888 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1894).rule = .split 1 (15/128) 1892 1893 := by rfl
      simp only [walk, hr]
      rw [traversal_1892 f (by omega), traversal_1893 f (by omega)]
      change (List.range' 1888 5 ++ List.range' (1888+5) 1) ++
        [1888+(5+1)] = List.range' 1888 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1888) (n := 5+1)).symm

private theorem traversal_1895 (fuel : Nat) (hf : 1895 < fuel) :
    walk nodes fuel 1895 = List.range' 1853 43 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1895).rule = .split 0 (1/160) 1887 1894 := by rfl
      simp only [walk, hr]
      rw [traversal_1887 f (by omega), traversal_1894 f (by omega)]
      change (List.range' 1853 35 ++ List.range' (1853+35) 7) ++
        [1853+(35+7)] = List.range' 1853 ((35+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1853) (n := 35+7)).symm

private theorem traversal_1896 (fuel : Nat) (hf : 1896 < fuel) :
    walk nodes fuel 1896 = List.range' 1852 45 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1896).rule = .split 3 (189/64) 1852 1895 := by rfl
      simp only [walk, hr]
      rw [traversal_1852 f (by omega), traversal_1895 f (by omega)]
      change (List.range' 1852 1 ++ List.range' (1852+1) 43) ++
        [1852+(1+43)] = List.range' 1852 ((1+43)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1852) (n := 1+43)).symm

private theorem traversal_1897 (fuel : Nat) (hf : 1897 < fuel) :
    walk nodes fuel 1897 = List.range' 1897 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1897).rule = .bound .rightEnd 0 (14359/49152) (897325/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1898 (fuel : Nat) (hf : 1898 < fuel) :
    walk nodes fuel 1898 = List.range' 1898 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1898).rule = .bound .rightEnd 0 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1899 (fuel : Nat) (hf : 1899 < fuel) :
    walk nodes fuel 1899 = List.range' 1899 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1899).rule = .bound .rightEnd 6 (1777/6144) (453181/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1900 (fuel : Nat) (hf : 1900 < fuel) :
    walk nodes fuel 1900 = List.range' 1900 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1900).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1901 (fuel : Nat) (hf : 1901 < fuel) :
    walk nodes fuel 1901 = List.range' 1899 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1901).rule = .split 0 (1/320) 1899 1900 := by rfl
      simp only [walk, hr]
      rw [traversal_1899 f (by omega), traversal_1900 f (by omega)]
      change (List.range' 1899 1 ++ List.range' (1899+1) 1) ++
        [1899+(1+1)] = List.range' 1899 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1899) (n := 1+1)).symm

private theorem traversal_1902 (fuel : Nat) (hf : 1902 < fuel) :
    walk nodes fuel 1902 = List.range' 1898 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1902).rule = .split 3 (381/128) 1898 1901 := by rfl
      simp only [walk, hr]
      rw [traversal_1898 f (by omega), traversal_1901 f (by omega)]
      change (List.range' 1898 1 ++ List.range' (1898+1) 3) ++
        [1898+(1+3)] = List.range' 1898 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1898) (n := 1+3)).symm

private theorem traversal_1903 (fuel : Nat) (hf : 1903 < fuel) :
    walk nodes fuel 1903 = List.range' 1903 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1903).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1904 (fuel : Nat) (hf : 1904 < fuel) :
    walk nodes fuel 1904 = List.range' 1898 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1904).rule = .split 2 (2313/512) 1902 1903 := by rfl
      simp only [walk, hr]
      rw [traversal_1902 f (by omega), traversal_1903 f (by omega)]
      change (List.range' 1898 5 ++ List.range' (1898+5) 1) ++
        [1898+(5+1)] = List.range' 1898 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1898) (n := 5+1)).symm

private theorem traversal_1905 (fuel : Nat) (hf : 1905 < fuel) :
    walk nodes fuel 1905 = List.range' 1905 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1905).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1906 (fuel : Nat) (hf : 1906 < fuel) :
    walk nodes fuel 1906 = List.range' 1898 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1906).rule = .split 1 (15/128) 1904 1905 := by rfl
      simp only [walk, hr]
      rw [traversal_1904 f (by omega), traversal_1905 f (by omega)]
      change (List.range' 1898 7 ++ List.range' (1898+7) 1) ++
        [1898+(7+1)] = List.range' 1898 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1898) (n := 7+1)).symm

private theorem traversal_1907 (fuel : Nat) (hf : 1907 < fuel) :
    walk nodes fuel 1907 = List.range' 1907 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1907).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1908 (fuel : Nat) (hf : 1908 < fuel) :
    walk nodes fuel 1908 = List.range' 1898 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1908).rule = .split 0 (1/160) 1906 1907 := by rfl
      simp only [walk, hr]
      rw [traversal_1906 f (by omega), traversal_1907 f (by omega)]
      change (List.range' 1898 9 ++ List.range' (1898+9) 1) ++
        [1898+(9+1)] = List.range' 1898 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1898) (n := 9+1)).symm

private theorem traversal_1909 (fuel : Nat) (hf : 1909 < fuel) :
    walk nodes fuel 1909 = List.range' 1897 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1909).rule = .split 3 (189/64) 1897 1908 := by rfl
      simp only [walk, hr]
      rw [traversal_1897 f (by omega), traversal_1908 f (by omega)]
      change (List.range' 1897 1 ++ List.range' (1897+1) 11) ++
        [1897+(1+11)] = List.range' 1897 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1897) (n := 1+11)).symm

private theorem traversal_1910 (fuel : Nat) (hf : 1910 < fuel) :
    walk nodes fuel 1910 = List.range' 1852 59 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1910).rule = .split 2 (1147/256) 1896 1909 := by rfl
      simp only [walk, hr]
      rw [traversal_1896 f (by omega), traversal_1909 f (by omega)]
      change (List.range' 1852 45 ++ List.range' (1852+45) 13) ++
        [1852+(45+13)] = List.range' 1852 ((45+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1852) (n := 45+13)).symm

private theorem traversal_1911 (fuel : Nat) (hf : 1911 < fuel) :
    walk nodes fuel 1911 = List.range' 1779 133 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1911).rule = .split 1 (5/64) 1851 1910 := by rfl
      simp only [walk, hr]
      rw [traversal_1851 f (by omega), traversal_1910 f (by omega)]
      change (List.range' 1779 73 ++ List.range' (1779+73) 59) ++
        [1779+(73+59)] = List.range' 1779 ((73+59)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1779) (n := 73+59)).symm

private theorem traversal_1912 (fuel : Nat) (hf : 1912 < fuel) :
    walk nodes fuel 1912 = List.range' 1912 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1912).rule = .bound .rightEnd 0 (14359/49152) (897325/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1913 (fuel : Nat) (hf : 1913 < fuel) :
    walk nodes fuel 1913 = List.range' 1913 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1913).rule = .bound .rightEnd 6 (223/768) (451403/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1914 (fuel : Nat) (hf : 1914 < fuel) :
    walk nodes fuel 1914 = List.range' 1914 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1914).rule = .infeasible 4 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1915 (fuel : Nat) (hf : 1915 < fuel) :
    walk nodes fuel 1915 = List.range' 1913 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1915).rule = .split 3 (381/128) 1913 1914 := by rfl
      simp only [walk, hr]
      rw [traversal_1913 f (by omega), traversal_1914 f (by omega)]
      change (List.range' 1913 1 ++ List.range' (1913+1) 1) ++
        [1913+(1+1)] = List.range' 1913 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1913) (n := 1+1)).symm

private theorem traversal_1916 (fuel : Nat) (hf : 1916 < fuel) :
    walk nodes fuel 1916 = List.range' 1916 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1916).rule = .bound .rightEnd 3 (1187/4096) (452285/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1917 (fuel : Nat) (hf : 1917 < fuel) :
    walk nodes fuel 1917 = List.range' 1913 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1917).rule = .split 2 (2275/512) 1915 1916 := by rfl
      simp only [walk, hr]
      rw [traversal_1915 f (by omega), traversal_1916 f (by omega)]
      change (List.range' 1913 3 ++ List.range' (1913+3) 1) ++
        [1913+(3+1)] = List.range' 1913 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1913) (n := 3+1)).symm

private theorem traversal_1918 (fuel : Nat) (hf : 1918 < fuel) :
    walk nodes fuel 1918 = List.range' 1918 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1918).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1919 (fuel : Nat) (hf : 1919 < fuel) :
    walk nodes fuel 1919 = List.range' 1913 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1919).rule = .split 1 (5/128) 1917 1918 := by rfl
      simp only [walk, hr]
      rw [traversal_1917 f (by omega), traversal_1918 f (by omega)]
      change (List.range' 1913 5 ++ List.range' (1913+5) 1) ++
        [1913+(5+1)] = List.range' 1913 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1913) (n := 5+1)).symm

private theorem traversal_1920 (fuel : Nat) (hf : 1920 < fuel) :
    walk nodes fuel 1920 = List.range' 1920 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1920).rule = .infeasible 4 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1921 (fuel : Nat) (hf : 1921 < fuel) :
    walk nodes fuel 1921 = List.range' 1913 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1921).rule = .split 0 (3/160) 1919 1920 := by rfl
      simp only [walk, hr]
      rw [traversal_1919 f (by omega), traversal_1920 f (by omega)]
      change (List.range' 1913 7 ++ List.range' (1913+7) 1) ++
        [1913+(7+1)] = List.range' 1913 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1913) (n := 7+1)).symm

private theorem traversal_1922 (fuel : Nat) (hf : 1922 < fuel) :
    walk nodes fuel 1922 = List.range' 1912 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1922).rule = .split 3 (189/64) 1912 1921 := by rfl
      simp only [walk, hr]
      rw [traversal_1912 f (by omega), traversal_1921 f (by omega)]
      change (List.range' 1912 1 ++ List.range' (1912+1) 9) ++
        [1912+(1+9)] = List.range' 1912 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1912) (n := 1+9)).symm

private theorem traversal_1923 (fuel : Nat) (hf : 1923 < fuel) :
    walk nodes fuel 1923 = List.range' 1923 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1923).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1924 (fuel : Nat) (hf : 1924 < fuel) :
    walk nodes fuel 1924 = List.range' 1912 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1924).rule = .split 2 (1147/256) 1922 1923 := by rfl
      simp only [walk, hr]
      rw [traversal_1922 f (by omega), traversal_1923 f (by omega)]
      change (List.range' 1912 11 ++ List.range' (1912+11) 1) ++
        [1912+(11+1)] = List.range' 1912 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1912) (n := 11+1)).symm

private theorem traversal_1925 (fuel : Nat) (hf : 1925 < fuel) :
    walk nodes fuel 1925 = List.range' 1925 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1925).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1926 (fuel : Nat) (hf : 1926 < fuel) :
    walk nodes fuel 1926 = List.range' 1912 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1926).rule = .split 1 (5/64) 1924 1925 := by rfl
      simp only [walk, hr]
      rw [traversal_1924 f (by omega), traversal_1925 f (by omega)]
      change (List.range' 1912 13 ++ List.range' (1912+13) 1) ++
        [1912+(13+1)] = List.range' 1912 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1912) (n := 13+1)).symm

private theorem traversal_1927 (fuel : Nat) (hf : 1927 < fuel) :
    walk nodes fuel 1927 = List.range' 1779 149 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1927).rule = .split 0 (1/80) 1911 1926 := by rfl
      simp only [walk, hr]
      rw [traversal_1911 f (by omega), traversal_1926 f (by omega)]
      change (List.range' 1779 133 ++ List.range' (1779+133) 15) ++
        [1779+(133+15)] = List.range' 1779 ((133+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1779) (n := 133+15)).symm

private theorem traversal_1928 (fuel : Nat) (hf : 1928 < fuel) :
    walk nodes fuel 1928 = List.range' 1778 151 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1928).rule = .split 3 (93/32) 1778 1927 := by rfl
      simp only [walk, hr]
      rw [traversal_1778 f (by omega), traversal_1927 f (by omega)]
      change (List.range' 1778 1 ++ List.range' (1778+1) 149) ++
        [1778+(1+149)] = List.range' 1778 ((1+149)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1778) (n := 1+149)).symm

private theorem traversal_1929 (fuel : Nat) (hf : 1929 < fuel) :
    walk nodes fuel 1929 = List.range' 1929 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1929).rule = .bound .rightEnd 0 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1930 (fuel : Nat) (hf : 1930 < fuel) :
    walk nodes fuel 1930 = List.range' 1930 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1930).rule = .bound .rightEnd 6 (28603/98304) (450445/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1931 (fuel : Nat) (hf : 1931 < fuel) :
    walk nodes fuel 1931 = List.range' 1931 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1931).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1932 (fuel : Nat) (hf : 1932 < fuel) :
    walk nodes fuel 1932 = List.range' 1930 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1932).rule = .split 1 (5/64) 1930 1931 := by rfl
      simp only [walk, hr]
      rw [traversal_1930 f (by omega), traversal_1931 f (by omega)]
      change (List.range' 1930 1 ++ List.range' (1930+1) 1) ++
        [1930+(1+1)] = List.range' 1930 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1930) (n := 1+1)).symm

private theorem traversal_1933 (fuel : Nat) (hf : 1933 < fuel) :
    walk nodes fuel 1933 = List.range' 1933 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1933).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1934 (fuel : Nat) (hf : 1934 < fuel) :
    walk nodes fuel 1934 = List.range' 1930 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1934).rule = .split 0 (1/80) 1932 1933 := by rfl
      simp only [walk, hr]
      rw [traversal_1932 f (by omega), traversal_1933 f (by omega)]
      change (List.range' 1930 3 ++ List.range' (1930+3) 1) ++
        [1930+(3+1)] = List.range' 1930 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1930) (n := 3+1)).symm

private theorem traversal_1935 (fuel : Nat) (hf : 1935 < fuel) :
    walk nodes fuel 1935 = List.range' 1929 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1935).rule = .split 3 (93/32) 1929 1934 := by rfl
      simp only [walk, hr]
      rw [traversal_1929 f (by omega), traversal_1934 f (by omega)]
      change (List.range' 1929 1 ++ List.range' (1929+1) 5) ++
        [1929+(1+5)] = List.range' 1929 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1929) (n := 1+5)).symm

theorem traversal_1936 (fuel : Nat) (hf : 1936 < fuel) :
    walk nodes fuel 1936 = List.range' 1778 159 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1936).rule = .split 2 (583/128) 1928 1935 := by rfl
      simp only [walk, hr]
      rw [traversal_1928 f (by omega), traversal_1935 f (by omega)]
      change (List.range' 1778 151 ++ List.range' (1778+151) 7) ++
        [1778+(151+7)] = List.range' 1778 ((151+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1778) (n := 151+7)).symm

theorem traversal_1937 (fuel : Nat) (hf : 1937 < fuel) :
    walk nodes fuel 1937 = List.range' 1937 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1937).rule = .bound .rightEnd 6 (7267/24576) (886475/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1938 (fuel : Nat) (hf : 1938 < fuel) :
    walk nodes fuel 1938 = List.range' 1938 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1938).rule = .bound .rightEnd 6 (14359/49152) (897325/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1939 (fuel : Nat) (hf : 1939 < fuel) :
    walk nodes fuel 1939 = List.range' 1939 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1939).rule = .bound .rightEnd 3 (1187/4096) (452285/524288) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1940 (fuel : Nat) (hf : 1940 < fuel) :
    walk nodes fuel 1940 = List.range' 1938 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1940).rule = .split 3 (189/64) 1938 1939 := by rfl
      simp only [walk, hr]
      rw [traversal_1938 f (by omega), traversal_1939 f (by omega)]
      change (List.range' 1938 1 ++ List.range' (1938+1) 1) ++
        [1938+(1+1)] = List.range' 1938 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1938) (n := 1+1)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
