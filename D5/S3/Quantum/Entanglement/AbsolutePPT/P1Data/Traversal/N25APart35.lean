/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart35
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart35
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart35.traversal_2351,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart35.traversal_2376,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart35.traversal_2393,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart35.traversal_2404,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart35.traversal_2405,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart35.traversal_2406
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart34
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_2340 (fuel : Nat) (hf : 2340 < fuel) :
    walk nodes fuel 2340 = List.range' 2340 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2340).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2341 (fuel : Nat) (hf : 2341 < fuel) :
    walk nodes fuel 2341 = List.range' 2335 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2341).rule = .split 3 (9/4) 2339 2340 := by rfl
      simp only [walk, hr]
      rw [traversal_2339 f (by omega), traversal_2340 f (by omega)]
      change (List.range' 2335 5 ++ List.range' (2335+5) 1) ++
        [2335+(5+1)] = List.range' 2335 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2335) (n := 5+1)).symm

private theorem traversal_2342 (fuel : Nat) (hf : 2342 < fuel) :
    walk nodes fuel 2342 = List.range' 2334 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2342).rule = .split 2 (5/4) 2334 2341 := by rfl
      simp only [walk, hr]
      rw [traversal_2334 f (by omega), traversal_2341 f (by omega)]
      change (List.range' 2334 1 ++ List.range' (2334+1) 7) ++
        [2334+(1+7)] = List.range' 2334 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2334) (n := 1+7)).symm

private theorem traversal_2343 (fuel : Nat) (hf : 2343 < fuel) :
    walk nodes fuel 2343 = List.range' 2343 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2343).rule = .infeasible 3 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2344 (fuel : Nat) (hf : 2344 < fuel) :
    walk nodes fuel 2344 = List.range' 2344 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2344).rule = .bound .leftEnd 1 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2345 (fuel : Nat) (hf : 2345 < fuel) :
    walk nodes fuel 2345 = List.range' 2345 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2345).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2346 (fuel : Nat) (hf : 2346 < fuel) :
    walk nodes fuel 2346 = List.range' 2344 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2346).rule = .split 3 (9/4) 2344 2345 := by rfl
      simp only [walk, hr]
      rw [traversal_2344 f (by omega), traversal_2345 f (by omega)]
      change (List.range' 2344 1 ++ List.range' (2344+1) 1) ++
        [2344+(1+1)] = List.range' 2344 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2344) (n := 1+1)).symm

private theorem traversal_2347 (fuel : Nat) (hf : 2347 < fuel) :
    walk nodes fuel 2347 = List.range' 2343 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2347).rule = .split 2 (5/4) 2343 2346 := by rfl
      simp only [walk, hr]
      rw [traversal_2343 f (by omega), traversal_2346 f (by omega)]
      change (List.range' 2343 1 ++ List.range' (2343+1) 3) ++
        [2343+(1+3)] = List.range' 2343 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2343) (n := 1+3)).symm

private theorem traversal_2348 (fuel : Nat) (hf : 2348 < fuel) :
    walk nodes fuel 2348 = List.range' 2334 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2348).rule = .split 1 (5/4) 2342 2347 := by rfl
      simp only [walk, hr]
      rw [traversal_2342 f (by omega), traversal_2347 f (by omega)]
      change (List.range' 2334 9 ++ List.range' (2334+9) 5) ++
        [2334+(9+5)] = List.range' 2334 ((9+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2334) (n := 9+5)).symm

private theorem traversal_2349 (fuel : Nat) (hf : 2349 < fuel) :
    walk nodes fuel 2349 = List.range' 2349 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2349).rule = .bound .vertex 1 (44329/131072) (376145/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2350 (fuel : Nat) (hf : 2350 < fuel) :
    walk nodes fuel 2350 = List.range' 2334 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2350).rule = .split 0 (3/10) 2348 2349 := by rfl
      simp only [walk, hr]
      rw [traversal_2348 f (by omega), traversal_2349 f (by omega)]
      change (List.range' 2334 15 ++ List.range' (2334+15) 1) ++
        [2334+(15+1)] = List.range' 2334 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2334) (n := 15+1)).symm

theorem traversal_2351 (fuel : Nat) (hf : 2351 < fuel) :
    walk nodes fuel 2351 = List.range' 2269 83 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2351).rule = .split 3 (3/2) 2333 2350 := by rfl
      simp only [walk, hr]
      rw [traversal_2333 f (by omega), traversal_2350 f (by omega)]
      change (List.range' 2269 65 ++ List.range' (2269+65) 17) ++
        [2269+(65+17)] = List.range' 2269 ((65+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2269) (n := 65+17)).symm

private theorem traversal_2352 (fuel : Nat) (hf : 2352 < fuel) :
    walk nodes fuel 2352 = List.range' 2352 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2352).rule = .bound .vertex 4 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2353 (fuel : Nat) (hf : 2353 < fuel) :
    walk nodes fuel 2353 = List.range' 2353 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2353).rule = .bound .vertex 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2354 (fuel : Nat) (hf : 2354 < fuel) :
    walk nodes fuel 2354 = List.range' 2352 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2354).rule = .split 0 (1/5) 2352 2353 := by rfl
      simp only [walk, hr]
      rw [traversal_2352 f (by omega), traversal_2353 f (by omega)]
      change (List.range' 2352 1 ++ List.range' (2352+1) 1) ++
        [2352+(1+1)] = List.range' 2352 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2352) (n := 1+1)).symm

private theorem traversal_2355 (fuel : Nat) (hf : 2355 < fuel) :
    walk nodes fuel 2355 = List.range' 2355 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2355).rule = .bound .vertex 8 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2356 (fuel : Nat) (hf : 2356 < fuel) :
    walk nodes fuel 2356 = List.range' 2356 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2356).rule = .bound .vertex 0 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2357 (fuel : Nat) (hf : 2357 < fuel) :
    walk nodes fuel 2357 = List.range' 2357 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2357).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2358 (fuel : Nat) (hf : 2358 < fuel) :
    walk nodes fuel 2358 = List.range' 2356 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2358).rule = .split 1 (5/8) 2356 2357 := by rfl
      simp only [walk, hr]
      rw [traversal_2356 f (by omega), traversal_2357 f (by omega)]
      change (List.range' 2356 1 ++ List.range' (2356+1) 1) ++
        [2356+(1+1)] = List.range' 2356 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2356) (n := 1+1)).symm

private theorem traversal_2359 (fuel : Nat) (hf : 2359 < fuel) :
    walk nodes fuel 2359 = List.range' 2355 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2359).rule = .split 0 (1/5) 2355 2358 := by rfl
      simp only [walk, hr]
      rw [traversal_2355 f (by omega), traversal_2358 f (by omega)]
      change (List.range' 2355 1 ++ List.range' (2355+1) 3) ++
        [2355+(1+3)] = List.range' 2355 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2355) (n := 1+3)).symm

private theorem traversal_2360 (fuel : Nat) (hf : 2360 < fuel) :
    walk nodes fuel 2360 = List.range' 2352 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2360).rule = .split 3 (3/4) 2354 2359 := by rfl
      simp only [walk, hr]
      rw [traversal_2354 f (by omega), traversal_2359 f (by omega)]
      change (List.range' 2352 3 ++ List.range' (2352+3) 5) ++
        [2352+(3+5)] = List.range' 2352 ((3+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2352) (n := 3+5)).symm

private theorem traversal_2361 (fuel : Nat) (hf : 2361 < fuel) :
    walk nodes fuel 2361 = List.range' 2361 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2361).rule = .infeasible 1 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2362 (fuel : Nat) (hf : 2362 < fuel) :
    walk nodes fuel 2362 = List.range' 2362 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2362).rule = .bound .rightEnd 0 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2363 (fuel : Nat) (hf : 2363 < fuel) :
    walk nodes fuel 2363 = List.range' 2363 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2363).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2364 (fuel : Nat) (hf : 2364 < fuel) :
    walk nodes fuel 2364 = List.range' 2362 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2364).rule = .split 1 (5/8) 2362 2363 := by rfl
      simp only [walk, hr]
      rw [traversal_2362 f (by omega), traversal_2363 f (by omega)]
      change (List.range' 2362 1 ++ List.range' (2362+1) 1) ++
        [2362+(1+1)] = List.range' 2362 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2362) (n := 1+1)).symm

private theorem traversal_2365 (fuel : Nat) (hf : 2365 < fuel) :
    walk nodes fuel 2365 = List.range' 2365 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2365).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2366 (fuel : Nat) (hf : 2366 < fuel) :
    walk nodes fuel 2366 = List.range' 2362 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2366).rule = .split 0 (1/5) 2364 2365 := by rfl
      simp only [walk, hr]
      rw [traversal_2364 f (by omega), traversal_2365 f (by omega)]
      change (List.range' 2362 3 ++ List.range' (2362+3) 1) ++
        [2362+(3+1)] = List.range' 2362 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2362) (n := 3+1)).symm

private theorem traversal_2367 (fuel : Nat) (hf : 2367 < fuel) :
    walk nodes fuel 2367 = List.range' 2361 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2367).rule = .split 3 (3/4) 2361 2366 := by rfl
      simp only [walk, hr]
      rw [traversal_2361 f (by omega), traversal_2366 f (by omega)]
      change (List.range' 2361 1 ++ List.range' (2361+1) 5) ++
        [2361+(1+5)] = List.range' 2361 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2361) (n := 1+5)).symm

private theorem traversal_2368 (fuel : Nat) (hf : 2368 < fuel) :
    walk nodes fuel 2368 = List.range' 2352 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2368).rule = .split 2 (15/4) 2360 2367 := by rfl
      simp only [walk, hr]
      rw [traversal_2360 f (by omega), traversal_2367 f (by omega)]
      change (List.range' 2352 9 ++ List.range' (2352+9) 7) ++
        [2352+(9+7)] = List.range' 2352 ((9+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2352) (n := 9+7)).symm

private theorem traversal_2369 (fuel : Nat) (hf : 2369 < fuel) :
    walk nodes fuel 2369 = List.range' 2369 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2369).rule = .bound .leftEnd 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2370 (fuel : Nat) (hf : 2370 < fuel) :
    walk nodes fuel 2370 = List.range' 2370 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2370).rule = .bound .leftEnd 3 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2371 (fuel : Nat) (hf : 2371 < fuel) :
    walk nodes fuel 2371 = List.range' 2369 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2371).rule = .split 3 (3/4) 2369 2370 := by rfl
      simp only [walk, hr]
      rw [traversal_2369 f (by omega), traversal_2370 f (by omega)]
      change (List.range' 2369 1 ++ List.range' (2369+1) 1) ++
        [2369+(1+1)] = List.range' 2369 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2369) (n := 1+1)).symm

private theorem traversal_2372 (fuel : Nat) (hf : 2372 < fuel) :
    walk nodes fuel 2372 = List.range' 2372 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2372).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2373 (fuel : Nat) (hf : 2373 < fuel) :
    walk nodes fuel 2373 = List.range' 2369 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2373).rule = .split 2 (15/4) 2371 2372 := by rfl
      simp only [walk, hr]
      rw [traversal_2371 f (by omega), traversal_2372 f (by omega)]
      change (List.range' 2369 3 ++ List.range' (2369+3) 1) ++
        [2369+(3+1)] = List.range' 2369 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2369) (n := 3+1)).symm

private theorem traversal_2374 (fuel : Nat) (hf : 2374 < fuel) :
    walk nodes fuel 2374 = List.range' 2352 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2374).rule = .split 1 (5/4) 2368 2373 := by rfl
      simp only [walk, hr]
      rw [traversal_2368 f (by omega), traversal_2373 f (by omega)]
      change (List.range' 2352 17 ++ List.range' (2352+17) 5) ++
        [2352+(17+5)] = List.range' 2352 ((17+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2352) (n := 17+5)).symm

private theorem traversal_2375 (fuel : Nat) (hf : 2375 < fuel) :
    walk nodes fuel 2375 = List.range' 2375 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2375).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2376 (fuel : Nat) (hf : 2376 < fuel) :
    walk nodes fuel 2376 = List.range' 2352 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2376).rule = .split 0 (3/10) 2374 2375 := by rfl
      simp only [walk, hr]
      rw [traversal_2374 f (by omega), traversal_2375 f (by omega)]
      change (List.range' 2352 23 ++ List.range' (2352+23) 1) ++
        [2352+(23+1)] = List.range' 2352 ((23+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2352) (n := 23+1)).symm

private theorem traversal_2377 (fuel : Nat) (hf : 2377 < fuel) :
    walk nodes fuel 2377 = List.range' 2377 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2377).rule = .bound .vertex 6 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2378 (fuel : Nat) (hf : 2378 < fuel) :
    walk nodes fuel 2378 = List.range' 2378 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2378).rule = .bound .leftEnd 8 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2379 (fuel : Nat) (hf : 2379 < fuel) :
    walk nodes fuel 2379 = List.range' 2379 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2379).rule = .bound .leftEnd 6 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2380 (fuel : Nat) (hf : 2380 < fuel) :
    walk nodes fuel 2380 = List.range' 2380 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2380).rule = .bound .leftEnd 1 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2381 (fuel : Nat) (hf : 2381 < fuel) :
    walk nodes fuel 2381 = List.range' 2379 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2381).rule = .split 1 (15/16) 2379 2380 := by rfl
      simp only [walk, hr]
      rw [traversal_2379 f (by omega), traversal_2380 f (by omega)]
      change (List.range' 2379 1 ++ List.range' (2379+1) 1) ++
        [2379+(1+1)] = List.range' 2379 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2379) (n := 1+1)).symm

private theorem traversal_2382 (fuel : Nat) (hf : 2382 < fuel) :
    walk nodes fuel 2382 = List.range' 2382 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2382).rule = .bound .leftEnd 1 (45681/131072) (375303/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2383 (fuel : Nat) (hf : 2383 < fuel) :
    walk nodes fuel 2383 = List.range' 2379 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2383).rule = .split 0 (3/20) 2381 2382 := by rfl
      simp only [walk, hr]
      rw [traversal_2381 f (by omega), traversal_2382 f (by omega)]
      change (List.range' 2379 3 ++ List.range' (2379+3) 1) ++
        [2379+(3+1)] = List.range' 2379 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2379) (n := 3+1)).symm

private theorem traversal_2384 (fuel : Nat) (hf : 2384 < fuel) :
    walk nodes fuel 2384 = List.range' 2378 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2384).rule = .split 3 (15/8) 2378 2383 := by rfl
      simp only [walk, hr]
      rw [traversal_2378 f (by omega), traversal_2383 f (by omega)]
      change (List.range' 2378 1 ++ List.range' (2378+1) 5) ++
        [2378+(1+5)] = List.range' 2378 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2378) (n := 1+5)).symm

private theorem traversal_2385 (fuel : Nat) (hf : 2385 < fuel) :
    walk nodes fuel 2385 = List.range' 2385 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2385).rule = .bound .vertex 3 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2386 (fuel : Nat) (hf : 2386 < fuel) :
    walk nodes fuel 2386 = List.range' 2378 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2386).rule = .split 2 (25/8) 2384 2385 := by rfl
      simp only [walk, hr]
      rw [traversal_2384 f (by omega), traversal_2385 f (by omega)]
      change (List.range' 2378 7 ++ List.range' (2378+7) 1) ++
        [2378+(7+1)] = List.range' 2378 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2378) (n := 7+1)).symm

private theorem traversal_2387 (fuel : Nat) (hf : 2387 < fuel) :
    walk nodes fuel 2387 = List.range' 2377 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2387).rule = .split 1 (5/8) 2377 2386 := by rfl
      simp only [walk, hr]
      rw [traversal_2377 f (by omega), traversal_2386 f (by omega)]
      change (List.range' 2377 1 ++ List.range' (2377+1) 9) ++
        [2377+(1+9)] = List.range' 2377 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2377) (n := 1+9)).symm

private theorem traversal_2388 (fuel : Nat) (hf : 2388 < fuel) :
    walk nodes fuel 2388 = List.range' 2388 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2388).rule = .bound .vertex 6 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2389 (fuel : Nat) (hf : 2389 < fuel) :
    walk nodes fuel 2389 = List.range' 2389 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2389).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2390 (fuel : Nat) (hf : 2390 < fuel) :
    walk nodes fuel 2390 = List.range' 2388 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2390).rule = .split 2 (25/8) 2388 2389 := by rfl
      simp only [walk, hr]
      rw [traversal_2388 f (by omega), traversal_2389 f (by omega)]
      change (List.range' 2388 1 ++ List.range' (2388+1) 1) ++
        [2388+(1+1)] = List.range' 2388 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2388) (n := 1+1)).symm

private theorem traversal_2391 (fuel : Nat) (hf : 2391 < fuel) :
    walk nodes fuel 2391 = List.range' 2391 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2391).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2392 (fuel : Nat) (hf : 2392 < fuel) :
    walk nodes fuel 2392 = List.range' 2388 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2392).rule = .split 1 (5/8) 2390 2391 := by rfl
      simp only [walk, hr]
      rw [traversal_2390 f (by omega), traversal_2391 f (by omega)]
      change (List.range' 2388 3 ++ List.range' (2388+3) 1) ++
        [2388+(3+1)] = List.range' 2388 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2388) (n := 3+1)).symm

theorem traversal_2393 (fuel : Nat) (hf : 2393 < fuel) :
    walk nodes fuel 2393 = List.range' 2377 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2393).rule = .split 0 (1/5) 2387 2392 := by rfl
      simp only [walk, hr]
      rw [traversal_2387 f (by omega), traversal_2392 f (by omega)]
      change (List.range' 2377 11 ++ List.range' (2377+11) 5) ++
        [2377+(11+5)] = List.range' 2377 ((11+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2377) (n := 11+5)).symm

private theorem traversal_2394 (fuel : Nat) (hf : 2394 < fuel) :
    walk nodes fuel 2394 = List.range' 2394 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2394).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2395 (fuel : Nat) (hf : 2395 < fuel) :
    walk nodes fuel 2395 = List.range' 2395 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2395).rule = .bound .rightEnd 6 (126023/393216) (408363/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2396 (fuel : Nat) (hf : 2396 < fuel) :
    walk nodes fuel 2396 = List.range' 2396 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2396).rule = .bound .vertex 6 (126023/393216) (408363/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2397 (fuel : Nat) (hf : 2397 < fuel) :
    walk nodes fuel 2397 = List.range' 2397 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2397).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2398 (fuel : Nat) (hf : 2398 < fuel) :
    walk nodes fuel 2398 = List.range' 2396 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2398).rule = .split 2 (55/16) 2396 2397 := by rfl
      simp only [walk, hr]
      rw [traversal_2396 f (by omega), traversal_2397 f (by omega)]
      change (List.range' 2396 1 ++ List.range' (2396+1) 1) ++
        [2396+(1+1)] = List.range' 2396 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2396) (n := 1+1)).symm

private theorem traversal_2399 (fuel : Nat) (hf : 2399 < fuel) :
    walk nodes fuel 2399 = List.range' 2395 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2399).rule = .split 1 (5/16) 2395 2398 := by rfl
      simp only [walk, hr]
      rw [traversal_2395 f (by omega), traversal_2398 f (by omega)]
      change (List.range' 2395 1 ++ List.range' (2395+1) 3) ++
        [2395+(1+3)] = List.range' 2395 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2395) (n := 1+3)).symm

private theorem traversal_2400 (fuel : Nat) (hf : 2400 < fuel) :
    walk nodes fuel 2400 = List.range' 2400 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2400).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2401 (fuel : Nat) (hf : 2401 < fuel) :
    walk nodes fuel 2401 = List.range' 2395 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2401).rule = .split 0 (3/20) 2399 2400 := by rfl
      simp only [walk, hr]
      rw [traversal_2399 f (by omega), traversal_2400 f (by omega)]
      change (List.range' 2395 5 ++ List.range' (2395+5) 1) ++
        [2395+(5+1)] = List.range' 2395 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2395) (n := 5+1)).symm

private theorem traversal_2402 (fuel : Nat) (hf : 2402 < fuel) :
    walk nodes fuel 2402 = List.range' 2402 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2402).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2403 (fuel : Nat) (hf : 2403 < fuel) :
    walk nodes fuel 2403 = List.range' 2395 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2403).rule = .split 3 (21/8) 2401 2402 := by rfl
      simp only [walk, hr]
      rw [traversal_2401 f (by omega), traversal_2402 f (by omega)]
      change (List.range' 2395 7 ++ List.range' (2395+7) 1) ++
        [2395+(7+1)] = List.range' 2395 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2395) (n := 7+1)).symm

theorem traversal_2404 (fuel : Nat) (hf : 2404 < fuel) :
    walk nodes fuel 2404 = List.range' 2394 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2404).rule = .split 2 (25/8) 2394 2403 := by rfl
      simp only [walk, hr]
      rw [traversal_2394 f (by omega), traversal_2403 f (by omega)]
      change (List.range' 2394 1 ++ List.range' (2394+1) 9) ++
        [2394+(1+9)] = List.range' 2394 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2394) (n := 1+9)).symm

theorem traversal_2405 (fuel : Nat) (hf : 2405 < fuel) :
    walk nodes fuel 2405 = List.range' 2405 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2405).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2406 (fuel : Nat) (hf : 2406 < fuel) :
    walk nodes fuel 2406 = List.range' 2406 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2406).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
