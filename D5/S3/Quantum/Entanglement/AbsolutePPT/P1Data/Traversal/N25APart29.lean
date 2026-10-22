/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart29
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart29
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart29.traversal_1961,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart29.traversal_1992,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart29.traversal_2005,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart29.traversal_2006
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart26
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart28
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1941 (fuel : Nat) (hf : 1941 < fuel) :
    walk nodes fuel 1941 = List.range' 1941 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1941).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1942 (fuel : Nat) (hf : 1942 < fuel) :
    walk nodes fuel 1942 = List.range' 1938 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1942).rule = .split 2 (1147/256) 1940 1941 := by rfl
      simp only [walk, hr]
      rw [traversal_1940 f (by omega), traversal_1941 f (by omega)]
      change (List.range' 1938 3 ++ List.range' (1938+3) 1) ++
        [1938+(3+1)] = List.range' 1938 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1938) (n := 3+1)).symm

private theorem traversal_1943 (fuel : Nat) (hf : 1943 < fuel) :
    walk nodes fuel 1943 = List.range' 1943 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1943).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1944 (fuel : Nat) (hf : 1944 < fuel) :
    walk nodes fuel 1944 = List.range' 1938 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1944).rule = .split 1 (15/64) 1942 1943 := by rfl
      simp only [walk, hr]
      rw [traversal_1942 f (by omega), traversal_1943 f (by omega)]
      change (List.range' 1938 5 ++ List.range' (1938+5) 1) ++
        [1938+(5+1)] = List.range' 1938 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1938) (n := 5+1)).symm

private theorem traversal_1945 (fuel : Nat) (hf : 1945 < fuel) :
    walk nodes fuel 1945 = List.range' 1945 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1945).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1946 (fuel : Nat) (hf : 1946 < fuel) :
    walk nodes fuel 1946 = List.range' 1938 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1946).rule = .split 0 (1/80) 1944 1945 := by rfl
      simp only [walk, hr]
      rw [traversal_1944 f (by omega), traversal_1945 f (by omega)]
      change (List.range' 1938 7 ++ List.range' (1938+7) 1) ++
        [1938+(7+1)] = List.range' 1938 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1938) (n := 7+1)).symm

private theorem traversal_1947 (fuel : Nat) (hf : 1947 < fuel) :
    walk nodes fuel 1947 = List.range' 1937 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1947).rule = .split 3 (93/32) 1937 1946 := by rfl
      simp only [walk, hr]
      rw [traversal_1937 f (by omega), traversal_1946 f (by omega)]
      change (List.range' 1937 1 ++ List.range' (1937+1) 9) ++
        [1937+(1+9)] = List.range' 1937 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1937) (n := 1+9)).symm

private theorem traversal_1948 (fuel : Nat) (hf : 1948 < fuel) :
    walk nodes fuel 1948 = List.range' 1948 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1948).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1949 (fuel : Nat) (hf : 1949 < fuel) :
    walk nodes fuel 1949 = List.range' 1937 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1949).rule = .split 2 (583/128) 1947 1948 := by rfl
      simp only [walk, hr]
      rw [traversal_1947 f (by omega), traversal_1948 f (by omega)]
      change (List.range' 1937 11 ++ List.range' (1937+11) 1) ++
        [1937+(11+1)] = List.range' 1937 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1937) (n := 11+1)).symm

private theorem traversal_1950 (fuel : Nat) (hf : 1950 < fuel) :
    walk nodes fuel 1950 = List.range' 1778 173 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1950).rule = .split 1 (5/32) 1936 1949 := by rfl
      simp only [walk, hr]
      rw [traversal_1936 f (by omega), traversal_1949 f (by omega)]
      change (List.range' 1778 159 ++ List.range' (1778+159) 13) ++
        [1778+(159+13)] = List.range' 1778 ((159+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1778) (n := 159+13)).symm

private theorem traversal_1951 (fuel : Nat) (hf : 1951 < fuel) :
    walk nodes fuel 1951 = List.range' 1951 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1951).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1952 (fuel : Nat) (hf : 1952 < fuel) :
    walk nodes fuel 1952 = List.range' 1778 175 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1952).rule = .split 0 (1/40) 1950 1951 := by rfl
      simp only [walk, hr]
      rw [traversal_1950 f (by omega), traversal_1951 f (by omega)]
      change (List.range' 1778 173 ++ List.range' (1778+173) 1) ++
        [1778+(173+1)] = List.range' 1778 ((173+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1778) (n := 173+1)).symm

private theorem traversal_1953 (fuel : Nat) (hf : 1953 < fuel) :
    walk nodes fuel 1953 = List.range' 1777 177 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1953).rule = .split 3 (45/16) 1777 1952 := by rfl
      simp only [walk, hr]
      rw [traversal_1777 f (by omega), traversal_1952 f (by omega)]
      change (List.range' 1777 1 ++ List.range' (1777+1) 175) ++
        [1777+(1+175)] = List.range' 1777 ((1+175)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1777) (n := 1+175)).symm

private theorem traversal_1954 (fuel : Nat) (hf : 1954 < fuel) :
    walk nodes fuel 1954 = List.range' 1954 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1954).rule = .bound .rightEnd 3 (117299/393216) (438897/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1955 (fuel : Nat) (hf : 1955 < fuel) :
    walk nodes fuel 1955 = List.range' 1777 179 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1955).rule = .split 2 (301/64) 1953 1954 := by rfl
      simp only [walk, hr]
      rw [traversal_1953 f (by omega), traversal_1954 f (by omega)]
      change (List.range' 1777 177 ++ List.range' (1777+177) 1) ++
        [1777+(177+1)] = List.range' 1777 ((177+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1777) (n := 177+1)).symm

private theorem traversal_1956 (fuel : Nat) (hf : 1956 < fuel) :
    walk nodes fuel 1956 = List.range' 1956 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1956).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1957 (fuel : Nat) (hf : 1957 < fuel) :
    walk nodes fuel 1957 = List.range' 1777 181 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1957).rule = .split 1 (5/16) 1955 1956 := by rfl
      simp only [walk, hr]
      rw [traversal_1955 f (by omega), traversal_1956 f (by omega)]
      change (List.range' 1777 179 ++ List.range' (1777+179) 1) ++
        [1777+(179+1)] = List.range' 1777 ((179+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1777) (n := 179+1)).symm

private theorem traversal_1958 (fuel : Nat) (hf : 1958 < fuel) :
    walk nodes fuel 1958 = List.range' 1958 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1958).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1959 (fuel : Nat) (hf : 1959 < fuel) :
    walk nodes fuel 1959 = List.range' 1777 183 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1959).rule = .split 0 (1/20) 1957 1958 := by rfl
      simp only [walk, hr]
      rw [traversal_1957 f (by omega), traversal_1958 f (by omega)]
      change (List.range' 1777 181 ++ List.range' (1777+181) 1) ++
        [1777+(181+1)] = List.range' 1777 ((181+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1777) (n := 181+1)).symm

private theorem traversal_1960 (fuel : Nat) (hf : 1960 < fuel) :
    walk nodes fuel 1960 = List.range' 1776 185 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1960).rule = .split 3 (21/8) 1776 1959 := by rfl
      simp only [walk, hr]
      rw [traversal_1776 f (by omega), traversal_1959 f (by omega)]
      change (List.range' 1776 1 ++ List.range' (1776+1) 183) ++
        [1776+(1+183)] = List.range' 1776 ((1+183)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1776) (n := 1+183)).symm

theorem traversal_1961 (fuel : Nat) (hf : 1961 < fuel) :
    walk nodes fuel 1961 = List.range' 1607 355 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1961).rule = .split 2 (141/32) 1775 1960 := by rfl
      simp only [walk, hr]
      rw [traversal_1775 f (by omega), traversal_1960 f (by omega)]
      change (List.range' 1607 169 ++ List.range' (1607+169) 185) ++
        [1607+(169+185)] = List.range' 1607 ((169+185)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1607) (n := 169+185)).symm

private theorem traversal_1962 (fuel : Nat) (hf : 1962 < fuel) :
    walk nodes fuel 1962 = List.range' 1962 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1962).rule = .bound .vertex 8 (669/2048) (6267/8192) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1963 (fuel : Nat) (hf : 1963 < fuel) :
    walk nodes fuel 1963 = List.range' 1963 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1963).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1964 (fuel : Nat) (hf : 1964 < fuel) :
    walk nodes fuel 1964 = List.range' 1962 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1964).rule = .split 0 (1/40) 1962 1963 := by rfl
      simp only [walk, hr]
      rw [traversal_1962 f (by omega), traversal_1963 f (by omega)]
      change (List.range' 1962 1 ++ List.range' (1962+1) 1) ++
        [1962+(1+1)] = List.range' 1962 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1962) (n := 1+1)).symm

private theorem traversal_1965 (fuel : Nat) (hf : 1965 < fuel) :
    walk nodes fuel 1965 = List.range' 1965 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1965).rule = .bound .rightEnd 6 (15593/49152) (206563/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1966 (fuel : Nat) (hf : 1966 < fuel) :
    walk nodes fuel 1966 = List.range' 1966 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1966).rule = .bound .rightEnd 6 (30613/98304) (841723/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1967 (fuel : Nat) (hf : 1967 < fuel) :
    walk nodes fuel 1967 = List.range' 1967 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1967).rule = .bound .rightEnd 6 (961/3072) (418985/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1968 (fuel : Nat) (hf : 1968 < fuel) :
    walk nodes fuel 1968 = List.range' 1968 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1968).rule = .bound .rightEnd 6 (5079/16384) (845615/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1969 (fuel : Nat) (hf : 1969 < fuel) :
    walk nodes fuel 1969 = List.range' 1969 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1969).rule = .bound .rightEnd 3 (5079/16384) (845615/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1970 (fuel : Nat) (hf : 1970 < fuel) :
    walk nodes fuel 1970 = List.range' 1968 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1970).rule = .split 1 (95/128) 1968 1969 := by rfl
      simp only [walk, hr]
      rw [traversal_1968 f (by omega), traversal_1969 f (by omega)]
      change (List.range' 1968 1 ++ List.range' (1968+1) 1) ++
        [1968+(1+1)] = List.range' 1968 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1968) (n := 1+1)).symm

private theorem traversal_1971 (fuel : Nat) (hf : 1971 < fuel) :
    walk nodes fuel 1971 = List.range' 1971 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1971).rule = .bound .rightEnd 3 (5079/16384) (845615/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1972 (fuel : Nat) (hf : 1972 < fuel) :
    walk nodes fuel 1972 = List.range' 1968 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1972).rule = .split 0 (1/160) 1970 1971 := by rfl
      simp only [walk, hr]
      rw [traversal_1970 f (by omega), traversal_1971 f (by omega)]
      change (List.range' 1968 3 ++ List.range' (1968+3) 1) ++
        [1968+(3+1)] = List.range' 1968 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1968) (n := 3+1)).symm

private theorem traversal_1973 (fuel : Nat) (hf : 1973 < fuel) :
    walk nodes fuel 1973 = List.range' 1967 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1973).rule = .split 3 (165/64) 1967 1972 := by rfl
      simp only [walk, hr]
      rw [traversal_1967 f (by omega), traversal_1972 f (by omega)]
      change (List.range' 1967 1 ++ List.range' (1967+1) 5) ++
        [1967+(1+5)] = List.range' 1967 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1967) (n := 1+5)).symm

private theorem traversal_1974 (fuel : Nat) (hf : 1974 < fuel) :
    walk nodes fuel 1974 = List.range' 1974 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1974).rule = .bound .rightEnd 3 (30613/98304) (841723/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1975 (fuel : Nat) (hf : 1975 < fuel) :
    walk nodes fuel 1975 = List.range' 1967 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1975).rule = .split 2 (995/256) 1973 1974 := by rfl
      simp only [walk, hr]
      rw [traversal_1973 f (by omega), traversal_1974 f (by omega)]
      change (List.range' 1967 7 ++ List.range' (1967+7) 1) ++
        [1967+(7+1)] = List.range' 1967 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1967) (n := 7+1)).symm

private theorem traversal_1976 (fuel : Nat) (hf : 1976 < fuel) :
    walk nodes fuel 1976 = List.range' 1966 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1976).rule = .split 1 (45/64) 1966 1975 := by rfl
      simp only [walk, hr]
      rw [traversal_1966 f (by omega), traversal_1975 f (by omega)]
      change (List.range' 1966 1 ++ List.range' (1966+1) 9) ++
        [1966+(1+9)] = List.range' 1966 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1966) (n := 1+9)).symm

private theorem traversal_1977 (fuel : Nat) (hf : 1977 < fuel) :
    walk nodes fuel 1977 = List.range' 1977 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1977).rule = .bound .rightEnd 3 (30613/98304) (841723/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1978 (fuel : Nat) (hf : 1978 < fuel) :
    walk nodes fuel 1978 = List.range' 1966 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1978).rule = .split 0 (1/80) 1976 1977 := by rfl
      simp only [walk, hr]
      rw [traversal_1976 f (by omega), traversal_1977 f (by omega)]
      change (List.range' 1966 11 ++ List.range' (1966+11) 1) ++
        [1966+(11+1)] = List.range' 1966 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1966) (n := 11+1)).symm

private theorem traversal_1979 (fuel : Nat) (hf : 1979 < fuel) :
    walk nodes fuel 1979 = List.range' 1965 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1979).rule = .split 3 (81/32) 1965 1978 := by rfl
      simp only [walk, hr]
      rw [traversal_1965 f (by omega), traversal_1978 f (by omega)]
      change (List.range' 1965 1 ++ List.range' (1965+1) 13) ++
        [1965+(1+13)] = List.range' 1965 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1965) (n := 1+13)).symm

private theorem traversal_1980 (fuel : Nat) (hf : 1980 < fuel) :
    walk nodes fuel 1980 = List.range' 1980 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1980).rule = .bound .rightEnd 3 (61799/196608) (833701/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1981 (fuel : Nat) (hf : 1981 < fuel) :
    walk nodes fuel 1981 = List.range' 1965 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1981).rule = .split 2 (507/128) 1979 1980 := by rfl
      simp only [walk, hr]
      rw [traversal_1979 f (by omega), traversal_1980 f (by omega)]
      change (List.range' 1965 15 ++ List.range' (1965+15) 1) ++
        [1965+(15+1)] = List.range' 1965 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1965) (n := 15+1)).symm

private theorem traversal_1982 (fuel : Nat) (hf : 1982 < fuel) :
    walk nodes fuel 1982 = List.range' 1982 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1982).rule = .bound .vertex 3 (61799/196608) (833701/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1983 (fuel : Nat) (hf : 1983 < fuel) :
    walk nodes fuel 1983 = List.range' 1965 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1983).rule = .split 1 (25/32) 1981 1982 := by rfl
      simp only [walk, hr]
      rw [traversal_1981 f (by omega), traversal_1982 f (by omega)]
      change (List.range' 1965 17 ++ List.range' (1965+17) 1) ++
        [1965+(17+1)] = List.range' 1965 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1965) (n := 17+1)).symm

private theorem traversal_1984 (fuel : Nat) (hf : 1984 < fuel) :
    walk nodes fuel 1984 = List.range' 1984 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1984).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1985 (fuel : Nat) (hf : 1985 < fuel) :
    walk nodes fuel 1985 = List.range' 1965 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1985).rule = .split 0 (1/40) 1983 1984 := by rfl
      simp only [walk, hr]
      rw [traversal_1983 f (by omega), traversal_1984 f (by omega)]
      change (List.range' 1965 19 ++ List.range' (1965+19) 1) ++
        [1965+(19+1)] = List.range' 1965 ((19+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1965) (n := 19+1)).symm

private theorem traversal_1986 (fuel : Nat) (hf : 1986 < fuel) :
    walk nodes fuel 1986 = List.range' 1962 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1986).rule = .split 3 (39/16) 1964 1985 := by rfl
      simp only [walk, hr]
      rw [traversal_1964 f (by omega), traversal_1985 f (by omega)]
      change (List.range' 1962 3 ++ List.range' (1962+3) 21) ++
        [1962+(3+21)] = List.range' 1962 ((3+21)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1962) (n := 3+21)).symm

private theorem traversal_1987 (fuel : Nat) (hf : 1987 < fuel) :
    walk nodes fuel 1987 = List.range' 1987 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1987).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1988 (fuel : Nat) (hf : 1988 < fuel) :
    walk nodes fuel 1988 = List.range' 1962 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1988).rule = .split 2 (263/64) 1986 1987 := by rfl
      simp only [walk, hr]
      rw [traversal_1986 f (by omega), traversal_1987 f (by omega)]
      change (List.range' 1962 25 ++ List.range' (1962+25) 1) ++
        [1962+(25+1)] = List.range' 1962 ((25+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1962) (n := 25+1)).symm

private theorem traversal_1989 (fuel : Nat) (hf : 1989 < fuel) :
    walk nodes fuel 1989 = List.range' 1989 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1989).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1990 (fuel : Nat) (hf : 1990 < fuel) :
    walk nodes fuel 1990 = List.range' 1962 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1990).rule = .split 1 (15/16) 1988 1989 := by rfl
      simp only [walk, hr]
      rw [traversal_1988 f (by omega), traversal_1989 f (by omega)]
      change (List.range' 1962 27 ++ List.range' (1962+27) 1) ++
        [1962+(27+1)] = List.range' 1962 ((27+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1962) (n := 27+1)).symm

private theorem traversal_1991 (fuel : Nat) (hf : 1991 < fuel) :
    walk nodes fuel 1991 = List.range' 1991 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1991).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1992 (fuel : Nat) (hf : 1992 < fuel) :
    walk nodes fuel 1992 = List.range' 1962 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1992).rule = .split 0 (1/20) 1990 1991 := by rfl
      simp only [walk, hr]
      rw [traversal_1990 f (by omega), traversal_1991 f (by omega)]
      change (List.range' 1962 29 ++ List.range' (1962+29) 1) ++
        [1962+(29+1)] = List.range' 1962 ((29+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1962) (n := 29+1)).symm

private theorem traversal_1993 (fuel : Nat) (hf : 1993 < fuel) :
    walk nodes fuel 1993 = List.range' 1993 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1993).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1994 (fuel : Nat) (hf : 1994 < fuel) :
    walk nodes fuel 1994 = List.range' 1994 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1994).rule = .bound .rightEnd 6 (15101/49152) (853231/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1995 (fuel : Nat) (hf : 1995 < fuel) :
    walk nodes fuel 1995 = List.range' 1995 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1995).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1996 (fuel : Nat) (hf : 1996 < fuel) :
    walk nodes fuel 1996 = List.range' 1994 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1996).rule = .split 3 (171/64) 1994 1995 := by rfl
      simp only [walk, hr]
      rw [traversal_1994 f (by omega), traversal_1995 f (by omega)]
      change (List.range' 1994 1 ++ List.range' (1994+1) 1) ++
        [1994+(1+1)] = List.range' 1994 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1994) (n := 1+1)).symm

private theorem traversal_1997 (fuel : Nat) (hf : 1997 < fuel) :
    walk nodes fuel 1997 = List.range' 1993 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1997).rule = .split 2 (995/256) 1993 1996 := by rfl
      simp only [walk, hr]
      rw [traversal_1993 f (by omega), traversal_1996 f (by omega)]
      change (List.range' 1993 1 ++ List.range' (1993+1) 3) ++
        [1993+(1+3)] = List.range' 1993 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1993) (n := 1+3)).symm

private theorem traversal_1998 (fuel : Nat) (hf : 1998 < fuel) :
    walk nodes fuel 1998 = List.range' 1998 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1998).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1999 (fuel : Nat) (hf : 1999 < fuel) :
    walk nodes fuel 1999 = List.range' 1999 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1999).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2000 (fuel : Nat) (hf : 2000 < fuel) :
    walk nodes fuel 2000 = List.range' 1998 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2000).rule = .split 2 (995/256) 1998 1999 := by rfl
      simp only [walk, hr]
      rw [traversal_1998 f (by omega), traversal_1999 f (by omega)]
      change (List.range' 1998 1 ++ List.range' (1998+1) 1) ++
        [1998+(1+1)] = List.range' 1998 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1998) (n := 1+1)).symm

private theorem traversal_2001 (fuel : Nat) (hf : 2001 < fuel) :
    walk nodes fuel 2001 = List.range' 1993 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2001).rule = .split 1 (45/64) 1997 2000 := by rfl
      simp only [walk, hr]
      rw [traversal_1997 f (by omega), traversal_2000 f (by omega)]
      change (List.range' 1993 5 ++ List.range' (1993+5) 3) ++
        [1993+(5+3)] = List.range' 1993 ((5+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1993) (n := 5+3)).symm

private theorem traversal_2002 (fuel : Nat) (hf : 2002 < fuel) :
    walk nodes fuel 2002 = List.range' 2002 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2002).rule = .bound .rightEnd 3 (30071/98304) (856899/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2003 (fuel : Nat) (hf : 2003 < fuel) :
    walk nodes fuel 2003 = List.range' 1993 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2003).rule = .split 0 (1/80) 2001 2002 := by rfl
      simp only [walk, hr]
      rw [traversal_2001 f (by omega), traversal_2002 f (by omega)]
      change (List.range' 1993 9 ++ List.range' (1993+9) 1) ++
        [1993+(9+1)] = List.range' 1993 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1993) (n := 9+1)).symm

private theorem traversal_2004 (fuel : Nat) (hf : 2004 < fuel) :
    walk nodes fuel 2004 = List.range' 2004 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2004).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2005 (fuel : Nat) (hf : 2005 < fuel) :
    walk nodes fuel 2005 = List.range' 1993 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2005).rule = .split 3 (87/32) 2003 2004 := by rfl
      simp only [walk, hr]
      rw [traversal_2003 f (by omega), traversal_2004 f (by omega)]
      change (List.range' 1993 11 ++ List.range' (1993+11) 1) ++
        [1993+(11+1)] = List.range' 1993 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1993) (n := 11+1)).symm

theorem traversal_2006 (fuel : Nat) (hf : 2006 < fuel) :
    walk nodes fuel 2006 = List.range' 2006 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2006).rule = .bound .rightEnd 3 (4969/16384) (864095/1048576) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
