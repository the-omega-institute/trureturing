/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart33
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart33
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart33.traversal_2268,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart33.traversal_2269,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart33.traversal_2270,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart33.traversal_2271,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart33.traversal_2272
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart00
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart32
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_2207 (fuel : Nat) (hf : 2207 < fuel) :
    walk nodes fuel 2207 = List.range' 2205 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2207).rule = .split 3 (9/16) 2205 2206 := by rfl
      simp only [walk, hr]
      rw [traversal_2205 f (by omega), traversal_2206 f (by omega)]
      change (List.range' 2205 1 ++ List.range' (2205+1) 1) ++
        [2205+(1+1)] = List.range' 2205 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2205) (n := 1+1)).symm

private theorem traversal_2208 (fuel : Nat) (hf : 2208 < fuel) :
    walk nodes fuel 2208 = List.range' 2204 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2208).rule = .split 2 (73/64) 2204 2207 := by rfl
      simp only [walk, hr]
      rw [traversal_2204 f (by omega), traversal_2207 f (by omega)]
      change (List.range' 2204 1 ++ List.range' (2204+1) 3) ++
        [2204+(1+3)] = List.range' 2204 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2204) (n := 1+3)).symm

private theorem traversal_2209 (fuel : Nat) (hf : 2209 < fuel) :
    walk nodes fuel 2209 = List.range' 2209 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2209).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2210 (fuel : Nat) (hf : 2210 < fuel) :
    walk nodes fuel 2210 = List.range' 2204 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2210).rule = .split 1 (45/16) 2208 2209 := by rfl
      simp only [walk, hr]
      rw [traversal_2208 f (by omega), traversal_2209 f (by omega)]
      change (List.range' 2204 5 ++ List.range' (2204+5) 1) ++
        [2204+(5+1)] = List.range' 2204 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2204) (n := 5+1)).symm

private theorem traversal_2211 (fuel : Nat) (hf : 2211 < fuel) :
    walk nodes fuel 2211 = List.range' 2211 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2211).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2212 (fuel : Nat) (hf : 2212 < fuel) :
    walk nodes fuel 2212 = List.range' 2204 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2212).rule = .split 0 (1/20) 2210 2211 := by rfl
      simp only [walk, hr]
      rw [traversal_2210 f (by omega), traversal_2211 f (by omega)]
      change (List.range' 2204 7 ++ List.range' (2204+7) 1) ++
        [2204+(7+1)] = List.range' 2204 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2204) (n := 7+1)).symm

private theorem traversal_2213 (fuel : Nat) (hf : 2213 < fuel) :
    walk nodes fuel 2213 = List.range' 2203 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2213).rule = .split 3 (3/8) 2203 2212 := by rfl
      simp only [walk, hr]
      rw [traversal_2203 f (by omega), traversal_2212 f (by omega)]
      change (List.range' 2203 1 ++ List.range' (2203+1) 9) ++
        [2203+(1+9)] = List.range' 2203 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2203) (n := 1+9)).symm

private theorem traversal_2214 (fuel : Nat) (hf : 2214 < fuel) :
    walk nodes fuel 2214 = List.range' 2192 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2214).rule = .split 2 (27/32) 2202 2213 := by rfl
      simp only [walk, hr]
      rw [traversal_2202 f (by omega), traversal_2213 f (by omega)]
      change (List.range' 2192 11 ++ List.range' (2192+11) 11) ++
        [2192+(11+11)] = List.range' 2192 ((11+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2192) (n := 11+11)).symm

private theorem traversal_2215 (fuel : Nat) (hf : 2215 < fuel) :
    walk nodes fuel 2215 = List.range' 2215 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2215).rule = .bound .leftEnd 1 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2216 (fuel : Nat) (hf : 2216 < fuel) :
    walk nodes fuel 2216 = List.range' 2216 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2216).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2217 (fuel : Nat) (hf : 2217 < fuel) :
    walk nodes fuel 2217 = List.range' 2215 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2217).rule = .split 2 (27/32) 2215 2216 := by rfl
      simp only [walk, hr]
      rw [traversal_2215 f (by omega), traversal_2216 f (by omega)]
      change (List.range' 2215 1 ++ List.range' (2215+1) 1) ++
        [2215+(1+1)] = List.range' 2215 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2215) (n := 1+1)).symm

private theorem traversal_2218 (fuel : Nat) (hf : 2218 < fuel) :
    walk nodes fuel 2218 = List.range' 2192 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2218).rule = .split 1 (25/8) 2214 2217 := by rfl
      simp only [walk, hr]
      rw [traversal_2214 f (by omega), traversal_2217 f (by omega)]
      change (List.range' 2192 23 ++ List.range' (2192+23) 3) ++
        [2192+(23+3)] = List.range' 2192 ((23+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2192) (n := 23+3)).symm

private theorem traversal_2219 (fuel : Nat) (hf : 2219 < fuel) :
    walk nodes fuel 2219 = List.range' 2219 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2219).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2220 (fuel : Nat) (hf : 2220 < fuel) :
    walk nodes fuel 2220 = List.range' 2192 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2220).rule = .split 3 (3/4) 2218 2219 := by rfl
      simp only [walk, hr]
      rw [traversal_2218 f (by omega), traversal_2219 f (by omega)]
      change (List.range' 2192 27 ++ List.range' (2192+27) 1) ++
        [2192+(27+1)] = List.range' 2192 ((27+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2192) (n := 27+1)).symm

private theorem traversal_2221 (fuel : Nat) (hf : 2221 < fuel) :
    walk nodes fuel 2221 = List.range' 2221 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2221).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2222 (fuel : Nat) (hf : 2222 < fuel) :
    walk nodes fuel 2222 = List.range' 2222 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2222).rule = .bound .leftEnd 2 (144313/196608) (353493/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2223 (fuel : Nat) (hf : 2223 < fuel) :
    walk nodes fuel 2223 = List.range' 2223 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2223).rule = .bound .leftEnd 1 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2224 (fuel : Nat) (hf : 2224 < fuel) :
    walk nodes fuel 2224 = List.range' 2224 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2224).rule = .bound .leftEnd 1 (121661/196608) (421449/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2225 (fuel : Nat) (hf : 2225 < fuel) :
    walk nodes fuel 2225 = List.range' 2223 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2225).rule = .split 0 (1/40) 2223 2224 := by rfl
      simp only [walk, hr]
      rw [traversal_2223 f (by omega), traversal_2224 f (by omega)]
      change (List.range' 2223 1 ++ List.range' (2223+1) 1) ++
        [2223+(1+1)] = List.range' 2223 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2223) (n := 1+1)).symm

private theorem traversal_2226 (fuel : Nat) (hf : 2226 < fuel) :
    walk nodes fuel 2226 = List.range' 2222 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2226).rule = .split 3 (9/16) 2222 2225 := by rfl
      simp only [walk, hr]
      rw [traversal_2222 f (by omega), traversal_2225 f (by omega)]
      change (List.range' 2222 1 ++ List.range' (2222+1) 3) ++
        [2222+(1+3)] = List.range' 2222 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2222) (n := 1+3)).symm

private theorem traversal_2227 (fuel : Nat) (hf : 2227 < fuel) :
    walk nodes fuel 2227 = List.range' 2227 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2227).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2228 (fuel : Nat) (hf : 2228 < fuel) :
    walk nodes fuel 2228 = List.range' 2222 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2228).rule = .split 2 (111/64) 2226 2227 := by rfl
      simp only [walk, hr]
      rw [traversal_2226 f (by omega), traversal_2227 f (by omega)]
      change (List.range' 2222 5 ++ List.range' (2222+5) 1) ++
        [2222+(5+1)] = List.range' 2222 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2222) (n := 5+1)).symm

private theorem traversal_2229 (fuel : Nat) (hf : 2229 < fuel) :
    walk nodes fuel 2229 = List.range' 2229 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2229).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2230 (fuel : Nat) (hf : 2230 < fuel) :
    walk nodes fuel 2230 = List.range' 2222 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2230).rule = .split 1 (45/16) 2228 2229 := by rfl
      simp only [walk, hr]
      rw [traversal_2228 f (by omega), traversal_2229 f (by omega)]
      change (List.range' 2222 7 ++ List.range' (2222+7) 1) ++
        [2222+(7+1)] = List.range' 2222 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2222) (n := 7+1)).symm

private theorem traversal_2231 (fuel : Nat) (hf : 2231 < fuel) :
    walk nodes fuel 2231 = List.range' 2231 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2231).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2232 (fuel : Nat) (hf : 2232 < fuel) :
    walk nodes fuel 2232 = List.range' 2222 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2232).rule = .split 0 (1/20) 2230 2231 := by rfl
      simp only [walk, hr]
      rw [traversal_2230 f (by omega), traversal_2231 f (by omega)]
      change (List.range' 2222 9 ++ List.range' (2222+9) 1) ++
        [2222+(9+1)] = List.range' 2222 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2222) (n := 9+1)).symm

private theorem traversal_2233 (fuel : Nat) (hf : 2233 < fuel) :
    walk nodes fuel 2233 = List.range' 2221 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2233).rule = .split 3 (3/8) 2221 2232 := by rfl
      simp only [walk, hr]
      rw [traversal_2221 f (by omega), traversal_2232 f (by omega)]
      change (List.range' 2221 1 ++ List.range' (2221+1) 11) ++
        [2221+(1+11)] = List.range' 2221 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2221) (n := 1+11)).symm

private theorem traversal_2234 (fuel : Nat) (hf : 2234 < fuel) :
    walk nodes fuel 2234 = List.range' 2234 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2234).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2235 (fuel : Nat) (hf : 2235 < fuel) :
    walk nodes fuel 2235 = List.range' 2221 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2235).rule = .split 2 (65/32) 2233 2234 := by rfl
      simp only [walk, hr]
      rw [traversal_2233 f (by omega), traversal_2234 f (by omega)]
      change (List.range' 2221 13 ++ List.range' (2221+13) 1) ++
        [2221+(13+1)] = List.range' 2221 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2221) (n := 13+1)).symm

private theorem traversal_2236 (fuel : Nat) (hf : 2236 < fuel) :
    walk nodes fuel 2236 = List.range' 2236 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2236).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2237 (fuel : Nat) (hf : 2237 < fuel) :
    walk nodes fuel 2237 = List.range' 2221 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2237).rule = .split 1 (25/8) 2235 2236 := by rfl
      simp only [walk, hr]
      rw [traversal_2235 f (by omega), traversal_2236 f (by omega)]
      change (List.range' 2221 15 ++ List.range' (2221+15) 1) ++
        [2221+(15+1)] = List.range' 2221 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2221) (n := 15+1)).symm

private theorem traversal_2238 (fuel : Nat) (hf : 2238 < fuel) :
    walk nodes fuel 2238 = List.range' 2238 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2238).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2239 (fuel : Nat) (hf : 2239 < fuel) :
    walk nodes fuel 2239 = List.range' 2239 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2239).rule = .bound .leftEnd 3 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2240 (fuel : Nat) (hf : 2240 < fuel) :
    walk nodes fuel 2240 = List.range' 2240 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2240).rule = .bound .leftEnd 3 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2241 (fuel : Nat) (hf : 2241 < fuel) :
    walk nodes fuel 2241 = List.range' 2239 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2241).rule = .split 2 (149/64) 2239 2240 := by rfl
      simp only [walk, hr]
      rw [traversal_2239 f (by omega), traversal_2240 f (by omega)]
      change (List.range' 2239 1 ++ List.range' (2239+1) 1) ++
        [2239+(1+1)] = List.range' 2239 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2239) (n := 1+1)).symm

private theorem traversal_2242 (fuel : Nat) (hf : 2242 < fuel) :
    walk nodes fuel 2242 = List.range' 2242 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2242).rule = .bound .leftEnd 3 (204089/393216) (499915/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2243 (fuel : Nat) (hf : 2243 < fuel) :
    walk nodes fuel 2243 = List.range' 2239 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2243).rule = .split 1 (45/16) 2241 2242 := by rfl
      simp only [walk, hr]
      rw [traversal_2241 f (by omega), traversal_2242 f (by omega)]
      change (List.range' 2239 3 ++ List.range' (2239+3) 1) ++
        [2239+(3+1)] = List.range' 2239 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2239) (n := 3+1)).symm

private theorem traversal_2244 (fuel : Nat) (hf : 2244 < fuel) :
    walk nodes fuel 2244 = List.range' 2244 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2244).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2245 (fuel : Nat) (hf : 2245 < fuel) :
    walk nodes fuel 2245 = List.range' 2239 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2245).rule = .split 0 (1/20) 2243 2244 := by rfl
      simp only [walk, hr]
      rw [traversal_2243 f (by omega), traversal_2244 f (by omega)]
      change (List.range' 2239 5 ++ List.range' (2239+5) 1) ++
        [2239+(5+1)] = List.range' 2239 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2239) (n := 5+1)).symm

private theorem traversal_2246 (fuel : Nat) (hf : 2246 < fuel) :
    walk nodes fuel 2246 = List.range' 2246 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2246).rule = .bound .leftEnd 1 (7169/16384) (298007/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2247 (fuel : Nat) (hf : 2247 < fuel) :
    walk nodes fuel 2247 = List.range' 2239 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2247).rule = .split 3 (9/8) 2245 2246 := by rfl
      simp only [walk, hr]
      rw [traversal_2245 f (by omega), traversal_2246 f (by omega)]
      change (List.range' 2239 7 ++ List.range' (2239+7) 1) ++
        [2239+(7+1)] = List.range' 2239 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2239) (n := 7+1)).symm

private theorem traversal_2248 (fuel : Nat) (hf : 2248 < fuel) :
    walk nodes fuel 2248 = List.range' 2238 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2248).rule = .split 2 (65/32) 2238 2247 := by rfl
      simp only [walk, hr]
      rw [traversal_2238 f (by omega), traversal_2247 f (by omega)]
      change (List.range' 2238 1 ++ List.range' (2238+1) 9) ++
        [2238+(1+9)] = List.range' 2238 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2238) (n := 1+9)).symm

private theorem traversal_2249 (fuel : Nat) (hf : 2249 < fuel) :
    walk nodes fuel 2249 = List.range' 2249 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2249).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2250 (fuel : Nat) (hf : 2250 < fuel) :
    walk nodes fuel 2250 = List.range' 2238 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2250).rule = .split 1 (25/8) 2248 2249 := by rfl
      simp only [walk, hr]
      rw [traversal_2248 f (by omega), traversal_2249 f (by omega)]
      change (List.range' 2238 11 ++ List.range' (2238+11) 1) ++
        [2238+(11+1)] = List.range' 2238 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2238) (n := 11+1)).symm

private theorem traversal_2251 (fuel : Nat) (hf : 2251 < fuel) :
    walk nodes fuel 2251 = List.range' 2221 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2251).rule = .split 3 (3/4) 2237 2250 := by rfl
      simp only [walk, hr]
      rw [traversal_2237 f (by omega), traversal_2250 f (by omega)]
      change (List.range' 2221 17 ++ List.range' (2221+17) 13) ++
        [2221+(17+13)] = List.range' 2221 ((17+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2221) (n := 17+13)).symm

private theorem traversal_2252 (fuel : Nat) (hf : 2252 < fuel) :
    walk nodes fuel 2252 = List.range' 2192 61 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2252).rule = .split 2 (23/16) 2220 2251 := by rfl
      simp only [walk, hr]
      rw [traversal_2220 f (by omega), traversal_2251 f (by omega)]
      change (List.range' 2192 29 ++ List.range' (2192+29) 31) ++
        [2192+(29+31)] = List.range' 2192 ((29+31)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2192) (n := 29+31)).symm

private theorem traversal_2253 (fuel : Nat) (hf : 2253 < fuel) :
    walk nodes fuel 2253 = List.range' 2253 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2253).rule = .bound .leftEnd 1 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2254 (fuel : Nat) (hf : 2254 < fuel) :
    walk nodes fuel 2254 = List.range' 2254 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2254).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2255 (fuel : Nat) (hf : 2255 < fuel) :
    walk nodes fuel 2255 = List.range' 2253 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2255).rule = .split 2 (23/16) 2253 2254 := by rfl
      simp only [walk, hr]
      rw [traversal_2253 f (by omega), traversal_2254 f (by omega)]
      change (List.range' 2253 1 ++ List.range' (2253+1) 1) ++
        [2253+(1+1)] = List.range' 2253 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2253) (n := 1+1)).symm

private theorem traversal_2256 (fuel : Nat) (hf : 2256 < fuel) :
    walk nodes fuel 2256 = List.range' 2192 65 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2256).rule = .split 1 (15/4) 2252 2255 := by rfl
      simp only [walk, hr]
      rw [traversal_2252 f (by omega), traversal_2255 f (by omega)]
      change (List.range' 2192 61 ++ List.range' (2192+61) 3) ++
        [2192+(61+3)] = List.range' 2192 ((61+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2192) (n := 61+3)).symm

private theorem traversal_2257 (fuel : Nat) (hf : 2257 < fuel) :
    walk nodes fuel 2257 = List.range' 2257 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2257).rule = .infeasible 3 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2258 (fuel : Nat) (hf : 2258 < fuel) :
    walk nodes fuel 2258 = List.range' 2258 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2258).rule = .bound .leftEnd 1 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2259 (fuel : Nat) (hf : 2259 < fuel) :
    walk nodes fuel 2259 = List.range' 2259 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2259).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2260 (fuel : Nat) (hf : 2260 < fuel) :
    walk nodes fuel 2260 = List.range' 2258 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2260).rule = .split 3 (9/4) 2258 2259 := by rfl
      simp only [walk, hr]
      rw [traversal_2258 f (by omega), traversal_2259 f (by omega)]
      change (List.range' 2258 1 ++ List.range' (2258+1) 1) ++
        [2258+(1+1)] = List.range' 2258 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2258) (n := 1+1)).symm

private theorem traversal_2261 (fuel : Nat) (hf : 2261 < fuel) :
    walk nodes fuel 2261 = List.range' 2257 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2261).rule = .split 2 (23/16) 2257 2260 := by rfl
      simp only [walk, hr]
      rw [traversal_2257 f (by omega), traversal_2260 f (by omega)]
      change (List.range' 2257 1 ++ List.range' (2257+1) 3) ++
        [2257+(1+3)] = List.range' 2257 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2257) (n := 1+3)).symm

private theorem traversal_2262 (fuel : Nat) (hf : 2262 < fuel) :
    walk nodes fuel 2262 = List.range' 2262 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2262).rule = .bound .leftEnd 1 (44329/131072) (376145/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2263 (fuel : Nat) (hf : 2263 < fuel) :
    walk nodes fuel 2263 = List.range' 2257 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2263).rule = .split 1 (15/4) 2261 2262 := by rfl
      simp only [walk, hr]
      rw [traversal_2261 f (by omega), traversal_2262 f (by omega)]
      change (List.range' 2257 5 ++ List.range' (2257+5) 1) ++
        [2257+(5+1)] = List.range' 2257 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2257) (n := 5+1)).symm

private theorem traversal_2264 (fuel : Nat) (hf : 2264 < fuel) :
    walk nodes fuel 2264 = List.range' 2192 73 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2264).rule = .split 3 (3/2) 2256 2263 := by rfl
      simp only [walk, hr]
      rw [traversal_2256 f (by omega), traversal_2263 f (by omega)]
      change (List.range' 2192 65 ++ List.range' (2192+65) 7) ++
        [2192+(65+7)] = List.range' 2192 ((65+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2192) (n := 65+7)).symm

private theorem traversal_2265 (fuel : Nat) (hf : 2265 < fuel) :
    walk nodes fuel 2265 = List.range' 2265 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2265).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2266 (fuel : Nat) (hf : 2266 < fuel) :
    walk nodes fuel 2266 = List.range' 2192 75 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2266).rule = .split 2 (21/8) 2264 2265 := by rfl
      simp only [walk, hr]
      rw [traversal_2264 f (by omega), traversal_2265 f (by omega)]
      change (List.range' 2192 73 ++ List.range' (2192+73) 1) ++
        [2192+(73+1)] = List.range' 2192 ((73+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2192) (n := 73+1)).symm

private theorem traversal_2267 (fuel : Nat) (hf : 2267 < fuel) :
    walk nodes fuel 2267 = List.range' 1 2267 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2267).rule = .split 1 (5/2) 2191 2266 := by rfl
      simp only [walk, hr]
      rw [traversal_2191 f (by omega), traversal_2266 f (by omega)]
      change (List.range' 1 2191 ++ List.range' (1+2191) 75) ++
        [1+(2191+75)] = List.range' 1 ((2191+75)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1) (n := 2191+75)).symm

theorem traversal_2268 (fuel : Nat) (hf : 2268 < fuel) :
    walk nodes fuel 2268 = List.range' 0 2269 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2268).rule = .split 2 (1/4) 0 2267 := by rfl
      simp only [walk, hr]
      rw [traversal_0 f (by omega), traversal_2267 f (by omega)]
      change (List.range' 0 1 ++ List.range' (0+1) 2267) ++
        [0+(1+2267)] = List.range' 0 ((1+2267)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 0) (n := 1+2267)).symm

theorem traversal_2269 (fuel : Nat) (hf : 2269 < fuel) :
    walk nodes fuel 2269 = List.range' 2269 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2269).rule = .bound .leftEnd 8 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2270 (fuel : Nat) (hf : 2270 < fuel) :
    walk nodes fuel 2270 = List.range' 2270 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2270).rule = .bound .leftEnd 5 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2271 (fuel : Nat) (hf : 2271 < fuel) :
    walk nodes fuel 2271 = List.range' 2271 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2271).rule = .bound .leftEnd 0 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2272 (fuel : Nat) (hf : 2272 < fuel) :
    walk nodes fuel 2272 = List.range' 2272 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2272).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
