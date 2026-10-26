/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart34
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart34
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart34.traversal_2333,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart34.traversal_2334,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart34.traversal_2339
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart33
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_2273 (fuel : Nat) (hf : 2273 < fuel) :
    walk nodes fuel 2273 = List.range' 2271 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2273).rule = .split 1 (25/16) 2271 2272 := by rfl
      simp only [walk, hr]
      rw [traversal_2271 f (by omega), traversal_2272 f (by omega)]
      change (List.range' 2271 1 ++ List.range' (2271+1) 1) ++
        [2271+(1+1)] = List.range' 2271 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2271) (n := 1+1)).symm

private theorem traversal_2274 (fuel : Nat) (hf : 2274 < fuel) :
    walk nodes fuel 2274 = List.range' 2274 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2274).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2275 (fuel : Nat) (hf : 2275 < fuel) :
    walk nodes fuel 2275 = List.range' 2271 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2275).rule = .split 0 (3/20) 2273 2274 := by rfl
      simp only [walk, hr]
      rw [traversal_2273 f (by omega), traversal_2274 f (by omega)]
      change (List.range' 2271 3 ++ List.range' (2271+3) 1) ++
        [2271+(3+1)] = List.range' 2271 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2271) (n := 3+1)).symm

private theorem traversal_2276 (fuel : Nat) (hf : 2276 < fuel) :
    walk nodes fuel 2276 = List.range' 2276 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2276).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2277 (fuel : Nat) (hf : 2277 < fuel) :
    walk nodes fuel 2277 = List.range' 2271 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2277).rule = .split 3 (3/8) 2275 2276 := by rfl
      simp only [walk, hr]
      rw [traversal_2275 f (by omega), traversal_2276 f (by omega)]
      change (List.range' 2271 5 ++ List.range' (2271+5) 1) ++
        [2271+(5+1)] = List.range' 2271 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2271) (n := 5+1)).symm

private theorem traversal_2278 (fuel : Nat) (hf : 2278 < fuel) :
    walk nodes fuel 2278 = List.range' 2270 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2278).rule = .split 2 (5/8) 2270 2277 := by rfl
      simp only [walk, hr]
      rw [traversal_2270 f (by omega), traversal_2277 f (by omega)]
      change (List.range' 2270 1 ++ List.range' (2270+1) 7) ++
        [2270+(1+7)] = List.range' 2270 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2270) (n := 1+7)).symm

private theorem traversal_2279 (fuel : Nat) (hf : 2279 < fuel) :
    walk nodes fuel 2279 = List.range' 2279 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2279).rule = .bound .leftEnd 1 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2280 (fuel : Nat) (hf : 2280 < fuel) :
    walk nodes fuel 2280 = List.range' 2280 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2280).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2281 (fuel : Nat) (hf : 2281 < fuel) :
    walk nodes fuel 2281 = List.range' 2281 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2281).rule = .bound .leftEnd 1 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2282 (fuel : Nat) (hf : 2282 < fuel) :
    walk nodes fuel 2282 = List.range' 2280 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2282).rule = .split 3 (3/8) 2280 2281 := by rfl
      simp only [walk, hr]
      rw [traversal_2280 f (by omega), traversal_2281 f (by omega)]
      change (List.range' 2280 1 ++ List.range' (2280+1) 1) ++
        [2280+(1+1)] = List.range' 2280 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2280) (n := 1+1)).symm

private theorem traversal_2283 (fuel : Nat) (hf : 2283 < fuel) :
    walk nodes fuel 2283 = List.range' 2279 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2283).rule = .split 2 (5/8) 2279 2282 := by rfl
      simp only [walk, hr]
      rw [traversal_2279 f (by omega), traversal_2282 f (by omega)]
      change (List.range' 2279 1 ++ List.range' (2279+1) 3) ++
        [2279+(1+3)] = List.range' 2279 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2279) (n := 1+3)).symm

private theorem traversal_2284 (fuel : Nat) (hf : 2284 < fuel) :
    walk nodes fuel 2284 = List.range' 2270 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2284).rule = .split 1 (15/8) 2278 2283 := by rfl
      simp only [walk, hr]
      rw [traversal_2278 f (by omega), traversal_2283 f (by omega)]
      change (List.range' 2270 9 ++ List.range' (2270+9) 5) ++
        [2270+(9+5)] = List.range' 2270 ((9+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2270) (n := 9+5)).symm

private theorem traversal_2285 (fuel : Nat) (hf : 2285 < fuel) :
    walk nodes fuel 2285 = List.range' 2285 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2285).rule = .bound .leftEnd 1 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2286 (fuel : Nat) (hf : 2286 < fuel) :
    walk nodes fuel 2286 = List.range' 2286 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2286).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2287 (fuel : Nat) (hf : 2287 < fuel) :
    walk nodes fuel 2287 = List.range' 2285 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2287).rule = .split 2 (5/8) 2285 2286 := by rfl
      simp only [walk, hr]
      rw [traversal_2285 f (by omega), traversal_2286 f (by omega)]
      change (List.range' 2285 1 ++ List.range' (2285+1) 1) ++
        [2285+(1+1)] = List.range' 2285 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2285) (n := 1+1)).symm

private theorem traversal_2288 (fuel : Nat) (hf : 2288 < fuel) :
    walk nodes fuel 2288 = List.range' 2288 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2288).rule = .bound .leftEnd 1 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2289 (fuel : Nat) (hf : 2289 < fuel) :
    walk nodes fuel 2289 = List.range' 2285 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2289).rule = .split 1 (15/8) 2287 2288 := by rfl
      simp only [walk, hr]
      rw [traversal_2287 f (by omega), traversal_2288 f (by omega)]
      change (List.range' 2285 3 ++ List.range' (2285+3) 1) ++
        [2285+(3+1)] = List.range' 2285 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2285) (n := 3+1)).symm

private theorem traversal_2290 (fuel : Nat) (hf : 2290 < fuel) :
    walk nodes fuel 2290 = List.range' 2270 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2290).rule = .split 0 (1/5) 2284 2289 := by rfl
      simp only [walk, hr]
      rw [traversal_2284 f (by omega), traversal_2289 f (by omega)]
      change (List.range' 2270 15 ++ List.range' (2270+15) 5) ++
        [2270+(15+5)] = List.range' 2270 ((15+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2270) (n := 15+5)).symm

private theorem traversal_2291 (fuel : Nat) (hf : 2291 < fuel) :
    walk nodes fuel 2291 = List.range' 2291 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2291).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2292 (fuel : Nat) (hf : 2292 < fuel) :
    walk nodes fuel 2292 = List.range' 2270 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2292).rule = .split 3 (3/4) 2290 2291 := by rfl
      simp only [walk, hr]
      rw [traversal_2290 f (by omega), traversal_2291 f (by omega)]
      change (List.range' 2270 21 ++ List.range' (2270+21) 1) ++
        [2270+(21+1)] = List.range' 2270 ((21+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2270) (n := 21+1)).symm

private theorem traversal_2293 (fuel : Nat) (hf : 2293 < fuel) :
    walk nodes fuel 2293 = List.range' 2293 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2293).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2294 (fuel : Nat) (hf : 2294 < fuel) :
    walk nodes fuel 2294 = List.range' 2294 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2294).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2295 (fuel : Nat) (hf : 2295 < fuel) :
    walk nodes fuel 2295 = List.range' 2293 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2295).rule = .split 3 (3/8) 2293 2294 := by rfl
      simp only [walk, hr]
      rw [traversal_2293 f (by omega), traversal_2294 f (by omega)]
      change (List.range' 2293 1 ++ List.range' (2293+1) 1) ++
        [2293+(1+1)] = List.range' 2293 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2293) (n := 1+1)).symm

private theorem traversal_2296 (fuel : Nat) (hf : 2296 < fuel) :
    walk nodes fuel 2296 = List.range' 2296 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2296).rule = .bound .leftEnd 2 (642119/393216) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2297 (fuel : Nat) (hf : 2297 < fuel) :
    walk nodes fuel 2297 = List.range' 2297 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2297).rule = .bound .leftEnd 8 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2298 (fuel : Nat) (hf : 2298 < fuel) :
    walk nodes fuel 2298 = List.range' 2298 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2298).rule = .bound .leftEnd 2 (44329/65536) (376145/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2299 (fuel : Nat) (hf : 2299 < fuel) :
    walk nodes fuel 2299 = List.range' 2297 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2299).rule = .split 0 (3/20) 2297 2298 := by rfl
      simp only [walk, hr]
      rw [traversal_2297 f (by omega), traversal_2298 f (by omega)]
      change (List.range' 2297 1 ++ List.range' (2297+1) 1) ++
        [2297+(1+1)] = List.range' 2297 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2297) (n := 1+1)).symm

private theorem traversal_2300 (fuel : Nat) (hf : 2300 < fuel) :
    walk nodes fuel 2300 = List.range' 2296 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2300).rule = .split 3 (3/8) 2296 2299 := by rfl
      simp only [walk, hr]
      rw [traversal_2296 f (by omega), traversal_2299 f (by omega)]
      change (List.range' 2296 1 ++ List.range' (2296+1) 3) ++
        [2296+(1+3)] = List.range' 2296 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2296) (n := 1+3)).symm

private theorem traversal_2301 (fuel : Nat) (hf : 2301 < fuel) :
    walk nodes fuel 2301 = List.range' 2293 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2301).rule = .split 2 (15/8) 2295 2300 := by rfl
      simp only [walk, hr]
      rw [traversal_2295 f (by omega), traversal_2300 f (by omega)]
      change (List.range' 2293 3 ++ List.range' (2293+3) 5) ++
        [2293+(3+5)] = List.range' 2293 ((3+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2293) (n := 3+5)).symm

private theorem traversal_2302 (fuel : Nat) (hf : 2302 < fuel) :
    walk nodes fuel 2302 = List.range' 2302 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2302).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2303 (fuel : Nat) (hf : 2303 < fuel) :
    walk nodes fuel 2303 = List.range' 2293 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2303).rule = .split 1 (15/8) 2301 2302 := by rfl
      simp only [walk, hr]
      rw [traversal_2301 f (by omega), traversal_2302 f (by omega)]
      change (List.range' 2293 9 ++ List.range' (2293+9) 1) ++
        [2293+(9+1)] = List.range' 2293 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2293) (n := 9+1)).symm

private theorem traversal_2304 (fuel : Nat) (hf : 2304 < fuel) :
    walk nodes fuel 2304 = List.range' 2304 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2304).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2305 (fuel : Nat) (hf : 2305 < fuel) :
    walk nodes fuel 2305 = List.range' 2293 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2305).rule = .split 0 (1/5) 2303 2304 := by rfl
      simp only [walk, hr]
      rw [traversal_2303 f (by omega), traversal_2304 f (by omega)]
      change (List.range' 2293 11 ++ List.range' (2293+11) 1) ++
        [2293+(11+1)] = List.range' 2293 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2293) (n := 11+1)).symm

private theorem traversal_2306 (fuel : Nat) (hf : 2306 < fuel) :
    walk nodes fuel 2306 = List.range' 2306 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2306).rule = .bound .leftEnd 8 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2307 (fuel : Nat) (hf : 2307 < fuel) :
    walk nodes fuel 2307 = List.range' 2307 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2307).rule = .bound .leftEnd 8 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2308 (fuel : Nat) (hf : 2308 < fuel) :
    walk nodes fuel 2308 = List.range' 2306 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2308).rule = .split 2 (15/8) 2306 2307 := by rfl
      simp only [walk, hr]
      rw [traversal_2306 f (by omega), traversal_2307 f (by omega)]
      change (List.range' 2306 1 ++ List.range' (2306+1) 1) ++
        [2306+(1+1)] = List.range' 2306 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2306) (n := 1+1)).symm

private theorem traversal_2309 (fuel : Nat) (hf : 2309 < fuel) :
    walk nodes fuel 2309 = List.range' 2309 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2309).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2310 (fuel : Nat) (hf : 2310 < fuel) :
    walk nodes fuel 2310 = List.range' 2310 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2310).rule = .bound .leftEnd 3 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2311 (fuel : Nat) (hf : 2311 < fuel) :
    walk nodes fuel 2311 = List.range' 2309 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2311).rule = .split 2 (15/8) 2309 2310 := by rfl
      simp only [walk, hr]
      rw [traversal_2309 f (by omega), traversal_2310 f (by omega)]
      change (List.range' 2309 1 ++ List.range' (2309+1) 1) ++
        [2309+(1+1)] = List.range' 2309 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2309) (n := 1+1)).symm

private theorem traversal_2312 (fuel : Nat) (hf : 2312 < fuel) :
    walk nodes fuel 2312 = List.range' 2306 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2312).rule = .split 1 (15/8) 2308 2311 := by rfl
      simp only [walk, hr]
      rw [traversal_2308 f (by omega), traversal_2311 f (by omega)]
      change (List.range' 2306 3 ++ List.range' (2306+3) 3) ++
        [2306+(3+3)] = List.range' 2306 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2306) (n := 3+3)).symm

private theorem traversal_2313 (fuel : Nat) (hf : 2313 < fuel) :
    walk nodes fuel 2313 = List.range' 2313 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2313).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2314 (fuel : Nat) (hf : 2314 < fuel) :
    walk nodes fuel 2314 = List.range' 2306 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2314).rule = .split 0 (1/5) 2312 2313 := by rfl
      simp only [walk, hr]
      rw [traversal_2312 f (by omega), traversal_2313 f (by omega)]
      change (List.range' 2306 7 ++ List.range' (2306+7) 1) ++
        [2306+(7+1)] = List.range' 2306 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2306) (n := 7+1)).symm

private theorem traversal_2315 (fuel : Nat) (hf : 2315 < fuel) :
    walk nodes fuel 2315 = List.range' 2293 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2315).rule = .split 3 (3/4) 2305 2314 := by rfl
      simp only [walk, hr]
      rw [traversal_2305 f (by omega), traversal_2314 f (by omega)]
      change (List.range' 2293 13 ++ List.range' (2293+13) 9) ++
        [2293+(13+9)] = List.range' 2293 ((13+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2293) (n := 13+9)).symm

private theorem traversal_2316 (fuel : Nat) (hf : 2316 < fuel) :
    walk nodes fuel 2316 = List.range' 2270 47 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2316).rule = .split 2 (5/4) 2292 2315 := by rfl
      simp only [walk, hr]
      rw [traversal_2292 f (by omega), traversal_2315 f (by omega)]
      change (List.range' 2270 23 ++ List.range' (2270+23) 23) ++
        [2270+(23+23)] = List.range' 2270 ((23+23)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2270) (n := 23+23)).symm

private theorem traversal_2317 (fuel : Nat) (hf : 2317 < fuel) :
    walk nodes fuel 2317 = List.range' 2269 49 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2317).rule = .split 1 (5/4) 2269 2316 := by rfl
      simp only [walk, hr]
      rw [traversal_2269 f (by omega), traversal_2316 f (by omega)]
      change (List.range' 2269 1 ++ List.range' (2269+1) 47) ++
        [2269+(1+47)] = List.range' 2269 ((1+47)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2269) (n := 1+47)).symm

private theorem traversal_2318 (fuel : Nat) (hf : 2318 < fuel) :
    walk nodes fuel 2318 = List.range' 2318 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2318).rule = .bound .leftEnd 6 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2319 (fuel : Nat) (hf : 2319 < fuel) :
    walk nodes fuel 2319 = List.range' 2319 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2319).rule = .bound .vertex 0 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2320 (fuel : Nat) (hf : 2320 < fuel) :
    walk nodes fuel 2320 = List.range' 2320 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2320).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2321 (fuel : Nat) (hf : 2321 < fuel) :
    walk nodes fuel 2321 = List.range' 2319 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2321).rule = .split 1 (5/8) 2319 2320 := by rfl
      simp only [walk, hr]
      rw [traversal_2319 f (by omega), traversal_2320 f (by omega)]
      change (List.range' 2319 1 ++ List.range' (2319+1) 1) ++
        [2319+(1+1)] = List.range' 2319 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2319) (n := 1+1)).symm

private theorem traversal_2322 (fuel : Nat) (hf : 2322 < fuel) :
    walk nodes fuel 2322 = List.range' 2322 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2322).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2323 (fuel : Nat) (hf : 2323 < fuel) :
    walk nodes fuel 2323 = List.range' 2319 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2323).rule = .split 0 (2/5) 2321 2322 := by rfl
      simp only [walk, hr]
      rw [traversal_2321 f (by omega), traversal_2322 f (by omega)]
      change (List.range' 2319 3 ++ List.range' (2319+3) 1) ++
        [2319+(3+1)] = List.range' 2319 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2319) (n := 3+1)).symm

private theorem traversal_2324 (fuel : Nat) (hf : 2324 < fuel) :
    walk nodes fuel 2324 = List.range' 2324 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2324).rule = .bound .vertex 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2325 (fuel : Nat) (hf : 2325 < fuel) :
    walk nodes fuel 2325 = List.range' 2325 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2325).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2326 (fuel : Nat) (hf : 2326 < fuel) :
    walk nodes fuel 2326 = List.range' 2324 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2326).rule = .split 0 (2/5) 2324 2325 := by rfl
      simp only [walk, hr]
      rw [traversal_2324 f (by omega), traversal_2325 f (by omega)]
      change (List.range' 2324 1 ++ List.range' (2324+1) 1) ++
        [2324+(1+1)] = List.range' 2324 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2324) (n := 1+1)).symm

private theorem traversal_2327 (fuel : Nat) (hf : 2327 < fuel) :
    walk nodes fuel 2327 = List.range' 2319 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2327).rule = .split 3 (3/4) 2323 2326 := by rfl
      simp only [walk, hr]
      rw [traversal_2323 f (by omega), traversal_2326 f (by omega)]
      change (List.range' 2319 5 ++ List.range' (2319+5) 3) ++
        [2319+(5+3)] = List.range' 2319 ((5+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2319) (n := 5+3)).symm

private theorem traversal_2328 (fuel : Nat) (hf : 2328 < fuel) :
    walk nodes fuel 2328 = List.range' 2318 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2328).rule = .split 2 (5/4) 2318 2327 := by rfl
      simp only [walk, hr]
      rw [traversal_2318 f (by omega), traversal_2327 f (by omega)]
      change (List.range' 2318 1 ++ List.range' (2318+1) 9) ++
        [2318+(1+9)] = List.range' 2318 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2318) (n := 1+9)).symm

private theorem traversal_2329 (fuel : Nat) (hf : 2329 < fuel) :
    walk nodes fuel 2329 = List.range' 2329 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2329).rule = .bound .leftEnd 1 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2330 (fuel : Nat) (hf : 2330 < fuel) :
    walk nodes fuel 2330 = List.range' 2330 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2330).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2331 (fuel : Nat) (hf : 2331 < fuel) :
    walk nodes fuel 2331 = List.range' 2329 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2331).rule = .split 2 (5/4) 2329 2330 := by rfl
      simp only [walk, hr]
      rw [traversal_2329 f (by omega), traversal_2330 f (by omega)]
      change (List.range' 2329 1 ++ List.range' (2329+1) 1) ++
        [2329+(1+1)] = List.range' 2329 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2329) (n := 1+1)).symm

private theorem traversal_2332 (fuel : Nat) (hf : 2332 < fuel) :
    walk nodes fuel 2332 = List.range' 2318 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2332).rule = .split 1 (5/4) 2328 2331 := by rfl
      simp only [walk, hr]
      rw [traversal_2328 f (by omega), traversal_2331 f (by omega)]
      change (List.range' 2318 11 ++ List.range' (2318+11) 3) ++
        [2318+(11+3)] = List.range' 2318 ((11+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2318) (n := 11+3)).symm

theorem traversal_2333 (fuel : Nat) (hf : 2333 < fuel) :
    walk nodes fuel 2333 = List.range' 2269 65 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2333).rule = .split 0 (3/10) 2317 2332 := by rfl
      simp only [walk, hr]
      rw [traversal_2317 f (by omega), traversal_2332 f (by omega)]
      change (List.range' 2269 49 ++ List.range' (2269+49) 15) ++
        [2269+(49+15)] = List.range' 2269 ((49+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2269) (n := 49+15)).symm

theorem traversal_2334 (fuel : Nat) (hf : 2334 < fuel) :
    walk nodes fuel 2334 = List.range' 2334 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2334).rule = .infeasible 3 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2335 (fuel : Nat) (hf : 2335 < fuel) :
    walk nodes fuel 2335 = List.range' 2335 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2335).rule = .bound .leftEnd 0 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2336 (fuel : Nat) (hf : 2336 < fuel) :
    walk nodes fuel 2336 = List.range' 2336 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2336).rule = .bound .leftEnd 1 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2337 (fuel : Nat) (hf : 2337 < fuel) :
    walk nodes fuel 2337 = List.range' 2335 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2337).rule = .split 1 (5/8) 2335 2336 := by rfl
      simp only [walk, hr]
      rw [traversal_2335 f (by omega), traversal_2336 f (by omega)]
      change (List.range' 2335 1 ++ List.range' (2335+1) 1) ++
        [2335+(1+1)] = List.range' 2335 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2335) (n := 1+1)).symm

private theorem traversal_2338 (fuel : Nat) (hf : 2338 < fuel) :
    walk nodes fuel 2338 = List.range' 2338 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2338).rule = .bound .leftEnd 1 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2339 (fuel : Nat) (hf : 2339 < fuel) :
    walk nodes fuel 2339 = List.range' 2335 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2339).rule = .split 0 (1/5) 2337 2338 := by rfl
      simp only [walk, hr]
      rw [traversal_2337 f (by omega), traversal_2338 f (by omega)]
      change (List.range' 2335 3 ++ List.range' (2335+3) 1) ++
        [2335+(3+1)] = List.range' 2335 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2335) (n := 3+1)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
