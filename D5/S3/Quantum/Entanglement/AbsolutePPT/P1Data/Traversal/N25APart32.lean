/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart32
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart32
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart32.traversal_2191,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart32.traversal_2202,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart32.traversal_2203,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart32.traversal_2204,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart32.traversal_2205,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart32.traversal_2206
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart20
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart30
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart31
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_2140 (fuel : Nat) (hf : 2140 < fuel) :
    walk nodes fuel 2140 = List.range' 2118 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2140).rule = .split 1 (25/16) 2138 2139 := by rfl
      simp only [walk, hr]
      rw [traversal_2138 f (by omega), traversal_2139 f (by omega)]
      change (List.range' 2118 21 ++ List.range' (2118+21) 1) ++
        [2118+(21+1)] = List.range' 2118 ((21+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2118) (n := 21+1)).symm

private theorem traversal_2141 (fuel : Nat) (hf : 2141 < fuel) :
    walk nodes fuel 2141 = List.range' 2141 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2141).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2142 (fuel : Nat) (hf : 2142 < fuel) :
    walk nodes fuel 2142 = List.range' 2118 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2142).rule = .split 0 (1/20) 2140 2141 := by rfl
      simp only [walk, hr]
      rw [traversal_2140 f (by omega), traversal_2141 f (by omega)]
      change (List.range' 2118 23 ++ List.range' (2118+23) 1) ++
        [2118+(23+1)] = List.range' 2118 ((23+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2118) (n := 23+1)).symm

private theorem traversal_2143 (fuel : Nat) (hf : 2143 < fuel) :
    walk nodes fuel 2143 = List.range' 2113 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2143).rule = .split 3 (15/8) 2117 2142 := by rfl
      simp only [walk, hr]
      rw [traversal_2117 f (by omega), traversal_2142 f (by omega)]
      change (List.range' 2113 5 ++ List.range' (2113+5) 25) ++
        [2113+(5+25)] = List.range' 2113 ((5+25)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2113) (n := 5+25)).symm

private theorem traversal_2144 (fuel : Nat) (hf : 2144 < fuel) :
    walk nodes fuel 2144 = List.range' 2026 119 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2144).rule = .split 2 (103/32) 2112 2143 := by rfl
      simp only [walk, hr]
      rw [traversal_2112 f (by omega), traversal_2143 f (by omega)]
      change (List.range' 2026 87 ++ List.range' (2026+87) 31) ++
        [2026+(87+31)] = List.range' 2026 ((87+31)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2026) (n := 87+31)).symm

private theorem traversal_2145 (fuel : Nat) (hf : 2145 < fuel) :
    walk nodes fuel 2145 = List.range' 2145 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2145).rule = .bound .leftEnd 1 (38951/98304) (330511/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2146 (fuel : Nat) (hf : 2146 < fuel) :
    walk nodes fuel 2146 = List.range' 2146 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2146).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2147 (fuel : Nat) (hf : 2147 < fuel) :
    walk nodes fuel 2147 = List.range' 2145 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2147).rule = .split 0 (1/40) 2145 2146 := by rfl
      simp only [walk, hr]
      rw [traversal_2145 f (by omega), traversal_2146 f (by omega)]
      change (List.range' 2145 1 ++ List.range' (2145+1) 1) ++
        [2145+(1+1)] = List.range' 2145 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2145) (n := 1+1)).symm

private theorem traversal_2148 (fuel : Nat) (hf : 2148 < fuel) :
    walk nodes fuel 2148 = List.range' 2148 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2148).rule = .bound .leftEnd 1 (73681/196608) (699011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2149 (fuel : Nat) (hf : 2149 < fuel) :
    walk nodes fuel 2149 = List.range' 2145 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2149).rule = .split 3 (27/16) 2147 2148 := by rfl
      simp only [walk, hr]
      rw [traversal_2147 f (by omega), traversal_2148 f (by omega)]
      change (List.range' 2145 3 ++ List.range' (2145+3) 1) ++
        [2145+(3+1)] = List.range' 2145 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2145) (n := 3+1)).symm

private theorem traversal_2150 (fuel : Nat) (hf : 2150 < fuel) :
    walk nodes fuel 2150 = List.range' 2150 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2150).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2151 (fuel : Nat) (hf : 2151 < fuel) :
    walk nodes fuel 2151 = List.range' 2145 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2151).rule = .split 2 (187/64) 2149 2150 := by rfl
      simp only [walk, hr]
      rw [traversal_2149 f (by omega), traversal_2150 f (by omega)]
      change (List.range' 2145 5 ++ List.range' (2145+5) 1) ++
        [2145+(5+1)] = List.range' 2145 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2145) (n := 5+1)).symm

private theorem traversal_2152 (fuel : Nat) (hf : 2152 < fuel) :
    walk nodes fuel 2152 = List.range' 2152 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2152).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2153 (fuel : Nat) (hf : 2153 < fuel) :
    walk nodes fuel 2153 = List.range' 2145 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2153).rule = .split 1 (35/16) 2151 2152 := by rfl
      simp only [walk, hr]
      rw [traversal_2151 f (by omega), traversal_2152 f (by omega)]
      change (List.range' 2145 7 ++ List.range' (2145+7) 1) ++
        [2145+(7+1)] = List.range' 2145 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2145) (n := 7+1)).symm

private theorem traversal_2154 (fuel : Nat) (hf : 2154 < fuel) :
    walk nodes fuel 2154 = List.range' 2154 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2154).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2155 (fuel : Nat) (hf : 2155 < fuel) :
    walk nodes fuel 2155 = List.range' 2145 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2155).rule = .split 0 (1/20) 2153 2154 := by rfl
      simp only [walk, hr]
      rw [traversal_2153 f (by omega), traversal_2154 f (by omega)]
      change (List.range' 2145 9 ++ List.range' (2145+9) 1) ++
        [2145+(9+1)] = List.range' 2145 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2145) (n := 9+1)).symm

private theorem traversal_2156 (fuel : Nat) (hf : 2156 < fuel) :
    walk nodes fuel 2156 = List.range' 2156 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2156).rule = .bound .leftEnd 3 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2157 (fuel : Nat) (hf : 2157 < fuel) :
    walk nodes fuel 2157 = List.range' 2157 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2157).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2158 (fuel : Nat) (hf : 2158 < fuel) :
    walk nodes fuel 2158 = List.range' 2156 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2158).rule = .split 0 (1/20) 2156 2157 := by rfl
      simp only [walk, hr]
      rw [traversal_2156 f (by omega), traversal_2157 f (by omega)]
      change (List.range' 2156 1 ++ List.range' (2156+1) 1) ++
        [2156+(1+1)] = List.range' 2156 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2156) (n := 1+1)).symm

private theorem traversal_2159 (fuel : Nat) (hf : 2159 < fuel) :
    walk nodes fuel 2159 = List.range' 2145 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2159).rule = .split 3 (15/8) 2155 2158 := by rfl
      simp only [walk, hr]
      rw [traversal_2155 f (by omega), traversal_2158 f (by omega)]
      change (List.range' 2145 11 ++ List.range' (2145+11) 3) ++
        [2145+(11+3)] = List.range' 2145 ((11+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2145) (n := 11+3)).symm

private theorem traversal_2160 (fuel : Nat) (hf : 2160 < fuel) :
    walk nodes fuel 2160 = List.range' 2160 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2160).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2161 (fuel : Nat) (hf : 2161 < fuel) :
    walk nodes fuel 2161 = List.range' 2145 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2161).rule = .split 2 (103/32) 2159 2160 := by rfl
      simp only [walk, hr]
      rw [traversal_2159 f (by omega), traversal_2160 f (by omega)]
      change (List.range' 2145 15 ++ List.range' (2145+15) 1) ++
        [2145+(15+1)] = List.range' 2145 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2145) (n := 15+1)).symm

private theorem traversal_2162 (fuel : Nat) (hf : 2162 < fuel) :
    walk nodes fuel 2162 = List.range' 2026 137 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2162).rule = .split 1 (15/8) 2144 2161 := by rfl
      simp only [walk, hr]
      rw [traversal_2144 f (by omega), traversal_2161 f (by omega)]
      change (List.range' 2026 119 ++ List.range' (2026+119) 17) ++
        [2026+(119+17)] = List.range' 2026 ((119+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2026) (n := 119+17)).symm

private theorem traversal_2163 (fuel : Nat) (hf : 2163 < fuel) :
    walk nodes fuel 2163 = List.range' 2163 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2163).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2164 (fuel : Nat) (hf : 2164 < fuel) :
    walk nodes fuel 2164 = List.range' 2164 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2164).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2165 (fuel : Nat) (hf : 2165 < fuel) :
    walk nodes fuel 2165 = List.range' 2165 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2165).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2166 (fuel : Nat) (hf : 2166 < fuel) :
    walk nodes fuel 2166 = List.range' 2164 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2166).rule = .split 2 (431/128) 2164 2165 := by rfl
      simp only [walk, hr]
      rw [traversal_2164 f (by omega), traversal_2165 f (by omega)]
      change (List.range' 2164 1 ++ List.range' (2164+1) 1) ++
        [2164+(1+1)] = List.range' 2164 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2164) (n := 1+1)).symm

private theorem traversal_2167 (fuel : Nat) (hf : 2167 < fuel) :
    walk nodes fuel 2167 = List.range' 2167 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2167).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2168 (fuel : Nat) (hf : 2168 < fuel) :
    walk nodes fuel 2168 = List.range' 2164 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2168).rule = .split 1 (45/32) 2166 2167 := by rfl
      simp only [walk, hr]
      rw [traversal_2166 f (by omega), traversal_2167 f (by omega)]
      change (List.range' 2164 3 ++ List.range' (2164+3) 1) ++
        [2164+(3+1)] = List.range' 2164 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2164) (n := 3+1)).symm

private theorem traversal_2169 (fuel : Nat) (hf : 2169 < fuel) :
    walk nodes fuel 2169 = List.range' 2169 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2169).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2170 (fuel : Nat) (hf : 2170 < fuel) :
    walk nodes fuel 2170 = List.range' 2164 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2170).rule = .split 0 (1/40) 2168 2169 := by rfl
      simp only [walk, hr]
      rw [traversal_2168 f (by omega), traversal_2169 f (by omega)]
      change (List.range' 2164 5 ++ List.range' (2164+5) 1) ++
        [2164+(5+1)] = List.range' 2164 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2164) (n := 5+1)).symm

private theorem traversal_2171 (fuel : Nat) (hf : 2171 < fuel) :
    walk nodes fuel 2171 = List.range' 2171 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2171).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2172 (fuel : Nat) (hf : 2172 < fuel) :
    walk nodes fuel 2172 = List.range' 2164 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2172).rule = .split 3 (39/16) 2170 2171 := by rfl
      simp only [walk, hr]
      rw [traversal_2170 f (by omega), traversal_2171 f (by omega)]
      change (List.range' 2164 7 ++ List.range' (2164+7) 1) ++
        [2164+(7+1)] = List.range' 2164 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2164) (n := 7+1)).symm

private theorem traversal_2173 (fuel : Nat) (hf : 2173 < fuel) :
    walk nodes fuel 2173 = List.range' 2173 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2173).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2174 (fuel : Nat) (hf : 2174 < fuel) :
    walk nodes fuel 2174 = List.range' 2164 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2174).rule = .split 2 (225/64) 2172 2173 := by rfl
      simp only [walk, hr]
      rw [traversal_2172 f (by omega), traversal_2173 f (by omega)]
      change (List.range' 2164 9 ++ List.range' (2164+9) 1) ++
        [2164+(9+1)] = List.range' 2164 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2164) (n := 9+1)).symm

private theorem traversal_2175 (fuel : Nat) (hf : 2175 < fuel) :
    walk nodes fuel 2175 = List.range' 2175 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2175).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2176 (fuel : Nat) (hf : 2176 < fuel) :
    walk nodes fuel 2176 = List.range' 2164 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2176).rule = .split 1 (25/16) 2174 2175 := by rfl
      simp only [walk, hr]
      rw [traversal_2174 f (by omega), traversal_2175 f (by omega)]
      change (List.range' 2164 11 ++ List.range' (2164+11) 1) ++
        [2164+(11+1)] = List.range' 2164 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2164) (n := 11+1)).symm

private theorem traversal_2177 (fuel : Nat) (hf : 2177 < fuel) :
    walk nodes fuel 2177 = List.range' 2177 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2177).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2178 (fuel : Nat) (hf : 2178 < fuel) :
    walk nodes fuel 2178 = List.range' 2164 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2178).rule = .split 0 (1/20) 2176 2177 := by rfl
      simp only [walk, hr]
      rw [traversal_2176 f (by omega), traversal_2177 f (by omega)]
      change (List.range' 2164 13 ++ List.range' (2164+13) 1) ++
        [2164+(13+1)] = List.range' 2164 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2164) (n := 13+1)).symm

private theorem traversal_2179 (fuel : Nat) (hf : 2179 < fuel) :
    walk nodes fuel 2179 = List.range' 2179 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2179).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2180 (fuel : Nat) (hf : 2180 < fuel) :
    walk nodes fuel 2180 = List.range' 2164 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2180).rule = .split 3 (21/8) 2178 2179 := by rfl
      simp only [walk, hr]
      rw [traversal_2178 f (by omega), traversal_2179 f (by omega)]
      change (List.range' 2164 15 ++ List.range' (2164+15) 1) ++
        [2164+(15+1)] = List.range' 2164 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2164) (n := 15+1)).symm

private theorem traversal_2181 (fuel : Nat) (hf : 2181 < fuel) :
    walk nodes fuel 2181 = List.range' 2163 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2181).rule = .split 2 (103/32) 2163 2180 := by rfl
      simp only [walk, hr]
      rw [traversal_2163 f (by omega), traversal_2180 f (by omega)]
      change (List.range' 2163 1 ++ List.range' (2163+1) 17) ++
        [2163+(1+17)] = List.range' 2163 ((1+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2163) (n := 1+17)).symm

private theorem traversal_2182 (fuel : Nat) (hf : 2182 < fuel) :
    walk nodes fuel 2182 = List.range' 2182 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2182).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2183 (fuel : Nat) (hf : 2183 < fuel) :
    walk nodes fuel 2183 = List.range' 2183 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2183).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2184 (fuel : Nat) (hf : 2184 < fuel) :
    walk nodes fuel 2184 = List.range' 2182 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2184).rule = .split 2 (103/32) 2182 2183 := by rfl
      simp only [walk, hr]
      rw [traversal_2182 f (by omega), traversal_2183 f (by omega)]
      change (List.range' 2182 1 ++ List.range' (2182+1) 1) ++
        [2182+(1+1)] = List.range' 2182 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2182) (n := 1+1)).symm

private theorem traversal_2185 (fuel : Nat) (hf : 2185 < fuel) :
    walk nodes fuel 2185 = List.range' 2163 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2185).rule = .split 1 (15/8) 2181 2184 := by rfl
      simp only [walk, hr]
      rw [traversal_2181 f (by omega), traversal_2184 f (by omega)]
      change (List.range' 2163 19 ++ List.range' (2163+19) 3) ++
        [2163+(19+3)] = List.range' 2163 ((19+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2163) (n := 19+3)).symm

private theorem traversal_2186 (fuel : Nat) (hf : 2186 < fuel) :
    walk nodes fuel 2186 = List.range' 2026 161 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2186).rule = .split 3 (9/4) 2162 2185 := by rfl
      simp only [walk, hr]
      rw [traversal_2162 f (by omega), traversal_2185 f (by omega)]
      change (List.range' 2026 137 ++ List.range' (2026+137) 23) ++
        [2026+(137+23)] = List.range' 2026 ((137+23)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2026) (n := 137+23)).symm

private theorem traversal_2187 (fuel : Nat) (hf : 2187 < fuel) :
    walk nodes fuel 2187 = List.range' 2187 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2187).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2188 (fuel : Nat) (hf : 2188 < fuel) :
    walk nodes fuel 2188 = List.range' 2026 163 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2188).rule = .split 2 (61/16) 2186 2187 := by rfl
      simp only [walk, hr]
      rw [traversal_2186 f (by omega), traversal_2187 f (by omega)]
      change (List.range' 2026 161 ++ List.range' (2026+161) 1) ++
        [2026+(161+1)] = List.range' 2026 ((161+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2026) (n := 161+1)).symm

private theorem traversal_2189 (fuel : Nat) (hf : 2189 < fuel) :
    walk nodes fuel 2189 = List.range' 1403 787 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2189).rule = .split 1 (5/4) 2025 2188 := by rfl
      simp only [walk, hr]
      rw [traversal_2025 f (by omega), traversal_2188 f (by omega)]
      change (List.range' 1403 623 ++ List.range' (1403+623) 163) ++
        [1403+(623+163)] = List.range' 1403 ((623+163)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1403) (n := 623+163)).symm

private theorem traversal_2190 (fuel : Nat) (hf : 2190 < fuel) :
    walk nodes fuel 2190 = List.range' 1344 847 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2190).rule = .split 3 (3/2) 1402 2189 := by rfl
      simp only [walk, hr]
      rw [traversal_1402 f (by omega), traversal_2189 f (by omega)]
      change (List.range' 1344 59 ++ List.range' (1344+59) 787) ++
        [1344+(59+787)] = List.range' 1344 ((59+787)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1344) (n := 59+787)).symm

theorem traversal_2191 (fuel : Nat) (hf : 2191 < fuel) :
    walk nodes fuel 2191 = List.range' 1 2191 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2191).rule = .split 2 (21/8) 1343 2190 := by rfl
      simp only [walk, hr]
      rw [traversal_1343 f (by omega), traversal_2190 f (by omega)]
      change (List.range' 1 1343 ++ List.range' (1+1343) 847) ++
        [1+(1343+847)] = List.range' 1 ((1343+847)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1) (n := 1343+847)).symm

private theorem traversal_2192 (fuel : Nat) (hf : 2192 < fuel) :
    walk nodes fuel 2192 = List.range' 2192 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2192).rule = .bound .leftEnd 2 (227023/98304) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2193 (fuel : Nat) (hf : 2193 < fuel) :
    walk nodes fuel 2193 = List.range' 2193 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2193).rule = .bound .leftEnd 1 (62691/65536) (265973/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2194 (fuel : Nat) (hf : 2194 < fuel) :
    walk nodes fuel 2194 = List.range' 2192 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2194).rule = .split 3 (3/16) 2192 2193 := by rfl
      simp only [walk, hr]
      rw [traversal_2192 f (by omega), traversal_2193 f (by omega)]
      change (List.range' 2192 1 ++ List.range' (2192+1) 1) ++
        [2192+(1+1)] = List.range' 2192 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2192) (n := 1+1)).symm

private theorem traversal_2195 (fuel : Nat) (hf : 2195 < fuel) :
    walk nodes fuel 2195 = List.range' 2195 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2195).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2196 (fuel : Nat) (hf : 2196 < fuel) :
    walk nodes fuel 2196 = List.range' 2192 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2196).rule = .split 2 (35/64) 2194 2195 := by rfl
      simp only [walk, hr]
      rw [traversal_2194 f (by omega), traversal_2195 f (by omega)]
      change (List.range' 2192 3 ++ List.range' (2192+3) 1) ++
        [2192+(3+1)] = List.range' 2192 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2192) (n := 3+1)).symm

private theorem traversal_2197 (fuel : Nat) (hf : 2197 < fuel) :
    walk nodes fuel 2197 = List.range' 2197 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2197).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2198 (fuel : Nat) (hf : 2198 < fuel) :
    walk nodes fuel 2198 = List.range' 2192 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2198).rule = .split 1 (45/16) 2196 2197 := by rfl
      simp only [walk, hr]
      rw [traversal_2196 f (by omega), traversal_2197 f (by omega)]
      change (List.range' 2192 5 ++ List.range' (2192+5) 1) ++
        [2192+(5+1)] = List.range' 2192 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2192) (n := 5+1)).symm

private theorem traversal_2199 (fuel : Nat) (hf : 2199 < fuel) :
    walk nodes fuel 2199 = List.range' 2199 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2199).rule = .bound .leftEnd 1 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2200 (fuel : Nat) (hf : 2200 < fuel) :
    walk nodes fuel 2200 = List.range' 2192 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2200).rule = .split 0 (1/20) 2198 2199 := by rfl
      simp only [walk, hr]
      rw [traversal_2198 f (by omega), traversal_2199 f (by omega)]
      change (List.range' 2192 7 ++ List.range' (2192+7) 1) ++
        [2192+(7+1)] = List.range' 2192 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2192) (n := 7+1)).symm

private theorem traversal_2201 (fuel : Nat) (hf : 2201 < fuel) :
    walk nodes fuel 2201 = List.range' 2201 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2201).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2202 (fuel : Nat) (hf : 2202 < fuel) :
    walk nodes fuel 2202 = List.range' 2192 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2202).rule = .split 3 (3/8) 2200 2201 := by rfl
      simp only [walk, hr]
      rw [traversal_2200 f (by omega), traversal_2201 f (by omega)]
      change (List.range' 2192 9 ++ List.range' (2192+9) 1) ++
        [2192+(9+1)] = List.range' 2192 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2192) (n := 9+1)).symm

theorem traversal_2203 (fuel : Nat) (hf : 2203 < fuel) :
    walk nodes fuel 2203 = List.range' 2203 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2203).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2204 (fuel : Nat) (hf : 2204 < fuel) :
    walk nodes fuel 2204 = List.range' 2204 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2204).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2205 (fuel : Nat) (hf : 2205 < fuel) :
    walk nodes fuel 2205 = List.range' 2205 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2205).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2206 (fuel : Nat) (hf : 2206 < fuel) :
    walk nodes fuel 2206 = List.range' 2206 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2206).rule = .bound .leftEnd 1 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
