/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart31
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart31
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart31.traversal_2112,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart31.traversal_2117,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart31.traversal_2138,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart31.traversal_2139
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart30
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_2074 (fuel : Nat) (hf : 2074 < fuel) :
    walk nodes fuel 2074 = List.range' 2072 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2074).rule = .split 2 (393/128) 2072 2073 := by rfl
      simp only [walk, hr]
      rw [traversal_2072 f (by omega), traversal_2073 f (by omega)]
      change (List.range' 2072 1 ++ List.range' (2072+1) 1) ++
        [2072+(1+1)] = List.range' 2072 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2072) (n := 1+1)).symm

private theorem traversal_2075 (fuel : Nat) (hf : 2075 < fuel) :
    walk nodes fuel 2075 = List.range' 2075 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2075).rule = .bound .leftEnd 3 (33481/98304) (96165/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2076 (fuel : Nat) (hf : 2076 < fuel) :
    walk nodes fuel 2076 = List.range' 2072 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2076).rule = .split 1 (45/32) 2074 2075 := by rfl
      simp only [walk, hr]
      rw [traversal_2074 f (by omega), traversal_2075 f (by omega)]
      change (List.range' 2072 3 ++ List.range' (2072+3) 1) ++
        [2072+(3+1)] = List.range' 2072 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2072) (n := 3+1)).symm

private theorem traversal_2077 (fuel : Nat) (hf : 2077 < fuel) :
    walk nodes fuel 2077 = List.range' 2057 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2077).rule = .split 0 (1/40) 2071 2076 := by rfl
      simp only [walk, hr]
      rw [traversal_2071 f (by omega), traversal_2076 f (by omega)]
      change (List.range' 2057 15 ++ List.range' (2057+15) 5) ++
        [2057+(15+5)] = List.range' 2057 ((15+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2057) (n := 15+5)).symm

private theorem traversal_2078 (fuel : Nat) (hf : 2078 < fuel) :
    walk nodes fuel 2078 = List.range' 2052 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2078).rule = .split 3 (33/16) 2056 2077 := by rfl
      simp only [walk, hr]
      rw [traversal_2056 f (by omega), traversal_2077 f (by omega)]
      change (List.range' 2052 5 ++ List.range' (2052+5) 21) ++
        [2052+(5+21)] = List.range' 2052 ((5+21)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2052) (n := 5+21)).symm

private theorem traversal_2079 (fuel : Nat) (hf : 2079 < fuel) :
    walk nodes fuel 2079 = List.range' 2049 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2079).rule = .split 2 (187/64) 2051 2078 := by rfl
      simp only [walk, hr]
      rw [traversal_2051 f (by omega), traversal_2078 f (by omega)]
      change (List.range' 2049 3 ++ List.range' (2049+3) 27) ++
        [2049+(3+27)] = List.range' 2049 ((3+27)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2049) (n := 3+27)).symm

private theorem traversal_2080 (fuel : Nat) (hf : 2080 < fuel) :
    walk nodes fuel 2080 = List.range' 2080 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2080).rule = .bound .leftEnd 1 (70081/196608) (735011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2081 (fuel : Nat) (hf : 2081 < fuel) :
    walk nodes fuel 2081 = List.range' 2081 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2081).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2082 (fuel : Nat) (hf : 2082 < fuel) :
    walk nodes fuel 2082 = List.range' 2080 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2082).rule = .split 3 (33/16) 2080 2081 := by rfl
      simp only [walk, hr]
      rw [traversal_2080 f (by omega), traversal_2081 f (by omega)]
      change (List.range' 2080 1 ++ List.range' (2080+1) 1) ++
        [2080+(1+1)] = List.range' 2080 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2080) (n := 1+1)).symm

private theorem traversal_2083 (fuel : Nat) (hf : 2083 < fuel) :
    walk nodes fuel 2083 = List.range' 2083 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2083).rule = .bound .leftEnd 8 (17729/49152) (726661/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2084 (fuel : Nat) (hf : 2084 < fuel) :
    walk nodes fuel 2084 = List.range' 2084 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2084).rule = .bound .leftEnd 8 (11541/32768) (186049/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2085 (fuel : Nat) (hf : 2085 < fuel) :
    walk nodes fuel 2085 = List.range' 2085 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2085).rule = .bound .leftEnd 1 (11541/32768) (186049/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2086 (fuel : Nat) (hf : 2086 < fuel) :
    walk nodes fuel 2086 = List.range' 2084 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2086).rule = .split 1 (105/64) 2084 2085 := by rfl
      simp only [walk, hr]
      rw [traversal_2084 f (by omega), traversal_2085 f (by omega)]
      change (List.range' 2084 1 ++ List.range' (2084+1) 1) ++
        [2084+(1+1)] = List.range' 2084 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2084) (n := 1+1)).symm

private theorem traversal_2087 (fuel : Nat) (hf : 2087 < fuel) :
    walk nodes fuel 2087 = List.range' 2087 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2087).rule = .bound .leftEnd 1 (11541/32768) (186049/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2088 (fuel : Nat) (hf : 2088 < fuel) :
    walk nodes fuel 2088 = List.range' 2084 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2088).rule = .split 0 (1/80) 2086 2087 := by rfl
      simp only [walk, hr]
      rw [traversal_2086 f (by omega), traversal_2087 f (by omega)]
      change (List.range' 2084 3 ++ List.range' (2084+3) 1) ++
        [2084+(3+1)] = List.range' 2084 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2084) (n := 3+1)).symm

private theorem traversal_2089 (fuel : Nat) (hf : 2089 < fuel) :
    walk nodes fuel 2089 = List.range' 2083 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2089).rule = .split 3 (63/32) 2083 2088 := by rfl
      simp only [walk, hr]
      rw [traversal_2083 f (by omega), traversal_2088 f (by omega)]
      change (List.range' 2083 1 ++ List.range' (2083+1) 5) ++
        [2083+(1+5)] = List.range' 2083 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2083) (n := 1+5)).symm

private theorem traversal_2090 (fuel : Nat) (hf : 2090 < fuel) :
    walk nodes fuel 2090 = List.range' 2090 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2090).rule = .bound .leftEnd 3 (70081/196608) (735011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2091 (fuel : Nat) (hf : 2091 < fuel) :
    walk nodes fuel 2091 = List.range' 2083 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2091).rule = .split 2 (393/128) 2089 2090 := by rfl
      simp only [walk, hr]
      rw [traversal_2089 f (by omega), traversal_2090 f (by omega)]
      change (List.range' 2083 7 ++ List.range' (2083+7) 1) ++
        [2083+(7+1)] = List.range' 2083 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2083) (n := 7+1)).symm

private theorem traversal_2092 (fuel : Nat) (hf : 2092 < fuel) :
    walk nodes fuel 2092 = List.range' 2092 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2092).rule = .bound .leftEnd 3 (70081/196608) (735011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2093 (fuel : Nat) (hf : 2093 < fuel) :
    walk nodes fuel 2093 = List.range' 2083 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2093).rule = .split 1 (55/32) 2091 2092 := by rfl
      simp only [walk, hr]
      rw [traversal_2091 f (by omega), traversal_2092 f (by omega)]
      change (List.range' 2083 9 ++ List.range' (2083+9) 1) ++
        [2083+(9+1)] = List.range' 2083 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2083) (n := 9+1)).symm

private theorem traversal_2094 (fuel : Nat) (hf : 2094 < fuel) :
    walk nodes fuel 2094 = List.range' 2094 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2094).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2095 (fuel : Nat) (hf : 2095 < fuel) :
    walk nodes fuel 2095 = List.range' 2083 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2095).rule = .split 0 (1/40) 2093 2094 := by rfl
      simp only [walk, hr]
      rw [traversal_2093 f (by omega), traversal_2094 f (by omega)]
      change (List.range' 2083 11 ++ List.range' (2083+11) 1) ++
        [2083+(11+1)] = List.range' 2083 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2083) (n := 11+1)).symm

private theorem traversal_2096 (fuel : Nat) (hf : 2096 < fuel) :
    walk nodes fuel 2096 = List.range' 2096 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2096).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2097 (fuel : Nat) (hf : 2097 < fuel) :
    walk nodes fuel 2097 = List.range' 2097 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2097).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2098 (fuel : Nat) (hf : 2098 < fuel) :
    walk nodes fuel 2098 = List.range' 2096 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2098).rule = .split 2 (393/128) 2096 2097 := by rfl
      simp only [walk, hr]
      rw [traversal_2096 f (by omega), traversal_2097 f (by omega)]
      change (List.range' 2096 1 ++ List.range' (2096+1) 1) ++
        [2096+(1+1)] = List.range' 2096 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2096) (n := 1+1)).symm

private theorem traversal_2099 (fuel : Nat) (hf : 2099 < fuel) :
    walk nodes fuel 2099 = List.range' 2099 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2099).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2100 (fuel : Nat) (hf : 2100 < fuel) :
    walk nodes fuel 2100 = List.range' 2096 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2100).rule = .split 1 (55/32) 2098 2099 := by rfl
      simp only [walk, hr]
      rw [traversal_2098 f (by omega), traversal_2099 f (by omega)]
      change (List.range' 2096 3 ++ List.range' (2096+3) 1) ++
        [2096+(3+1)] = List.range' 2096 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2096) (n := 3+1)).symm

private theorem traversal_2101 (fuel : Nat) (hf : 2101 < fuel) :
    walk nodes fuel 2101 = List.range' 2101 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2101).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2102 (fuel : Nat) (hf : 2102 < fuel) :
    walk nodes fuel 2102 = List.range' 2096 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2102).rule = .split 0 (1/40) 2100 2101 := by rfl
      simp only [walk, hr]
      rw [traversal_2100 f (by omega), traversal_2101 f (by omega)]
      change (List.range' 2096 5 ++ List.range' (2096+5) 1) ++
        [2096+(5+1)] = List.range' 2096 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2096) (n := 5+1)).symm

private theorem traversal_2103 (fuel : Nat) (hf : 2103 < fuel) :
    walk nodes fuel 2103 = List.range' 2083 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2103).rule = .split 3 (33/16) 2095 2102 := by rfl
      simp only [walk, hr]
      rw [traversal_2095 f (by omega), traversal_2102 f (by omega)]
      change (List.range' 2083 13 ++ List.range' (2083+13) 7) ++
        [2083+(13+7)] = List.range' 2083 ((13+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2083) (n := 13+7)).symm

private theorem traversal_2104 (fuel : Nat) (hf : 2104 < fuel) :
    walk nodes fuel 2104 = List.range' 2080 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2104).rule = .split 2 (187/64) 2082 2103 := by rfl
      simp only [walk, hr]
      rw [traversal_2082 f (by omega), traversal_2103 f (by omega)]
      change (List.range' 2080 3 ++ List.range' (2080+3) 21) ++
        [2080+(3+21)] = List.range' 2080 ((3+21)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2080) (n := 3+21)).symm

private theorem traversal_2105 (fuel : Nat) (hf : 2105 < fuel) :
    walk nodes fuel 2105 = List.range' 2049 57 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2105).rule = .split 1 (25/16) 2079 2104 := by rfl
      simp only [walk, hr]
      rw [traversal_2079 f (by omega), traversal_2104 f (by omega)]
      change (List.range' 2049 31 ++ List.range' (2049+31) 25) ++
        [2049+(31+25)] = List.range' 2049 ((31+25)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2049) (n := 31+25)).symm

private theorem traversal_2106 (fuel : Nat) (hf : 2106 < fuel) :
    walk nodes fuel 2106 = List.range' 2106 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2106).rule = .bound .leftEnd 1 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2107 (fuel : Nat) (hf : 2107 < fuel) :
    walk nodes fuel 2107 = List.range' 2107 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2107).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2108 (fuel : Nat) (hf : 2108 < fuel) :
    walk nodes fuel 2108 = List.range' 2106 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2108).rule = .split 2 (187/64) 2106 2107 := by rfl
      simp only [walk, hr]
      rw [traversal_2106 f (by omega), traversal_2107 f (by omega)]
      change (List.range' 2106 1 ++ List.range' (2106+1) 1) ++
        [2106+(1+1)] = List.range' 2106 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2106) (n := 1+1)).symm

private theorem traversal_2109 (fuel : Nat) (hf : 2109 < fuel) :
    walk nodes fuel 2109 = List.range' 2109 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2109).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2110 (fuel : Nat) (hf : 2110 < fuel) :
    walk nodes fuel 2110 = List.range' 2106 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2110).rule = .split 1 (25/16) 2108 2109 := by rfl
      simp only [walk, hr]
      rw [traversal_2108 f (by omega), traversal_2109 f (by omega)]
      change (List.range' 2106 3 ++ List.range' (2106+3) 1) ++
        [2106+(3+1)] = List.range' 2106 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2106) (n := 3+1)).symm

private theorem traversal_2111 (fuel : Nat) (hf : 2111 < fuel) :
    walk nodes fuel 2111 = List.range' 2049 63 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2111).rule = .split 0 (1/20) 2105 2110 := by rfl
      simp only [walk, hr]
      rw [traversal_2105 f (by omega), traversal_2110 f (by omega)]
      change (List.range' 2049 57 ++ List.range' (2049+57) 5) ++
        [2049+(57+5)] = List.range' 2049 ((57+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2049) (n := 57+5)).symm

theorem traversal_2112 (fuel : Nat) (hf : 2112 < fuel) :
    walk nodes fuel 2112 = List.range' 2026 87 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2112).rule = .split 3 (15/8) 2048 2111 := by rfl
      simp only [walk, hr]
      rw [traversal_2048 f (by omega), traversal_2111 f (by omega)]
      change (List.range' 2026 23 ++ List.range' (2026+23) 63) ++
        [2026+(23+63)] = List.range' 2026 ((23+63)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2026) (n := 23+63)).symm

private theorem traversal_2113 (fuel : Nat) (hf : 2113 < fuel) :
    walk nodes fuel 2113 = List.range' 2113 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2113).rule = .bound .leftEnd 8 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2114 (fuel : Nat) (hf : 2114 < fuel) :
    walk nodes fuel 2114 = List.range' 2114 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2114).rule = .bound .leftEnd 3 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2115 (fuel : Nat) (hf : 2115 < fuel) :
    walk nodes fuel 2115 = List.range' 2113 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2115).rule = .split 1 (25/16) 2113 2114 := by rfl
      simp only [walk, hr]
      rw [traversal_2113 f (by omega), traversal_2114 f (by omega)]
      change (List.range' 2113 1 ++ List.range' (2113+1) 1) ++
        [2113+(1+1)] = List.range' 2113 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2113) (n := 1+1)).symm

private theorem traversal_2116 (fuel : Nat) (hf : 2116 < fuel) :
    walk nodes fuel 2116 = List.range' 2116 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2116).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2117 (fuel : Nat) (hf : 2117 < fuel) :
    walk nodes fuel 2117 = List.range' 2113 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2117).rule = .split 0 (1/20) 2115 2116 := by rfl
      simp only [walk, hr]
      rw [traversal_2115 f (by omega), traversal_2116 f (by omega)]
      change (List.range' 2113 3 ++ List.range' (2113+3) 1) ++
        [2113+(3+1)] = List.range' 2113 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2113) (n := 3+1)).symm

private theorem traversal_2118 (fuel : Nat) (hf : 2118 < fuel) :
    walk nodes fuel 2118 = List.range' 2118 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2118).rule = .bound .leftEnd 8 (70081/196608) (735011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2119 (fuel : Nat) (hf : 2119 < fuel) :
    walk nodes fuel 2119 = List.range' 2119 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2119).rule = .bound .leftEnd 3 (70081/196608) (735011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2120 (fuel : Nat) (hf : 2120 < fuel) :
    walk nodes fuel 2120 = List.range' 2118 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2120).rule = .split 1 (45/32) 2118 2119 := by rfl
      simp only [walk, hr]
      rw [traversal_2118 f (by omega), traversal_2119 f (by omega)]
      change (List.range' 2118 1 ++ List.range' (2118+1) 1) ++
        [2118+(1+1)] = List.range' 2118 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2118) (n := 1+1)).symm

private theorem traversal_2121 (fuel : Nat) (hf : 2121 < fuel) :
    walk nodes fuel 2121 = List.range' 2121 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2121).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2122 (fuel : Nat) (hf : 2122 < fuel) :
    walk nodes fuel 2122 = List.range' 2118 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2122).rule = .split 0 (1/40) 2120 2121 := by rfl
      simp only [walk, hr]
      rw [traversal_2120 f (by omega), traversal_2121 f (by omega)]
      change (List.range' 2118 3 ++ List.range' (2118+3) 1) ++
        [2118+(3+1)] = List.range' 2118 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2118) (n := 3+1)).symm

private theorem traversal_2123 (fuel : Nat) (hf : 2123 < fuel) :
    walk nodes fuel 2123 = List.range' 2123 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2123).rule = .bound .leftEnd 8 (33845/98304) (23791/32768) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2124 (fuel : Nat) (hf : 2124 < fuel) :
    walk nodes fuel 2124 = List.range' 2124 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2124).rule = .bound .leftEnd 8 (11039/32768) (97257/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2125 (fuel : Nat) (hf : 2125 < fuel) :
    walk nodes fuel 2125 = List.range' 2125 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2125).rule = .bound .leftEnd 3 (11039/32768) (97257/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2126 (fuel : Nat) (hf : 2126 < fuel) :
    walk nodes fuel 2126 = List.range' 2124 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2126).rule = .split 1 (85/64) 2124 2125 := by rfl
      simp only [walk, hr]
      rw [traversal_2124 f (by omega), traversal_2125 f (by omega)]
      change (List.range' 2124 1 ++ List.range' (2124+1) 1) ++
        [2124+(1+1)] = List.range' 2124 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2124) (n := 1+1)).symm

private theorem traversal_2127 (fuel : Nat) (hf : 2127 < fuel) :
    walk nodes fuel 2127 = List.range' 2127 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2127).rule = .bound .leftEnd 3 (11039/32768) (97257/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2128 (fuel : Nat) (hf : 2128 < fuel) :
    walk nodes fuel 2128 = List.range' 2124 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2128).rule = .split 0 (1/80) 2126 2127 := by rfl
      simp only [walk, hr]
      rw [traversal_2126 f (by omega), traversal_2127 f (by omega)]
      change (List.range' 2124 3 ++ List.range' (2124+3) 1) ++
        [2124+(3+1)] = List.range' 2124 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2124) (n := 3+1)).symm

private theorem traversal_2129 (fuel : Nat) (hf : 2129 < fuel) :
    walk nodes fuel 2129 = List.range' 2123 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2129).rule = .split 3 (69/32) 2123 2128 := by rfl
      simp only [walk, hr]
      rw [traversal_2123 f (by omega), traversal_2128 f (by omega)]
      change (List.range' 2123 1 ++ List.range' (2123+1) 5) ++
        [2123+(1+5)] = List.range' 2123 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2123) (n := 1+5)).symm

private theorem traversal_2130 (fuel : Nat) (hf : 2130 < fuel) :
    walk nodes fuel 2130 = List.range' 2130 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2130).rule = .bound .leftEnd 3 (33481/98304) (96165/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2131 (fuel : Nat) (hf : 2131 < fuel) :
    walk nodes fuel 2131 = List.range' 2123 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2131).rule = .split 2 (431/128) 2129 2130 := by rfl
      simp only [walk, hr]
      rw [traversal_2129 f (by omega), traversal_2130 f (by omega)]
      change (List.range' 2123 7 ++ List.range' (2123+7) 1) ++
        [2123+(7+1)] = List.range' 2123 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2123) (n := 7+1)).symm

private theorem traversal_2132 (fuel : Nat) (hf : 2132 < fuel) :
    walk nodes fuel 2132 = List.range' 2132 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2132).rule = .bound .leftEnd 3 (33481/98304) (96165/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2133 (fuel : Nat) (hf : 2133 < fuel) :
    walk nodes fuel 2133 = List.range' 2123 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2133).rule = .split 1 (45/32) 2131 2132 := by rfl
      simp only [walk, hr]
      rw [traversal_2131 f (by omega), traversal_2132 f (by omega)]
      change (List.range' 2123 9 ++ List.range' (2123+9) 1) ++
        [2123+(9+1)] = List.range' 2123 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2123) (n := 9+1)).symm

private theorem traversal_2134 (fuel : Nat) (hf : 2134 < fuel) :
    walk nodes fuel 2134 = List.range' 2134 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2134).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2135 (fuel : Nat) (hf : 2135 < fuel) :
    walk nodes fuel 2135 = List.range' 2123 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2135).rule = .split 0 (1/40) 2133 2134 := by rfl
      simp only [walk, hr]
      rw [traversal_2133 f (by omega), traversal_2134 f (by omega)]
      change (List.range' 2123 11 ++ List.range' (2123+11) 1) ++
        [2123+(11+1)] = List.range' 2123 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2123) (n := 11+1)).symm

private theorem traversal_2136 (fuel : Nat) (hf : 2136 < fuel) :
    walk nodes fuel 2136 = List.range' 2118 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2136).rule = .split 3 (33/16) 2122 2135 := by rfl
      simp only [walk, hr]
      rw [traversal_2122 f (by omega), traversal_2135 f (by omega)]
      change (List.range' 2118 5 ++ List.range' (2118+5) 13) ++
        [2118+(5+13)] = List.range' 2118 ((5+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2118) (n := 5+13)).symm

private theorem traversal_2137 (fuel : Nat) (hf : 2137 < fuel) :
    walk nodes fuel 2137 = List.range' 2137 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2137).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2138 (fuel : Nat) (hf : 2138 < fuel) :
    walk nodes fuel 2138 = List.range' 2118 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2138).rule = .split 2 (225/64) 2136 2137 := by rfl
      simp only [walk, hr]
      rw [traversal_2136 f (by omega), traversal_2137 f (by omega)]
      change (List.range' 2118 19 ++ List.range' (2118+19) 1) ++
        [2118+(19+1)] = List.range' 2118 ((19+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2118) (n := 19+1)).symm

theorem traversal_2139 (fuel : Nat) (hf : 2139 < fuel) :
    walk nodes fuel 2139 = List.range' 2139 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2139).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
