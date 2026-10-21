/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart36
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart36
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart36.traversal_2440
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart33
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart35
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_2407 (fuel : Nat) (hf : 2407 < fuel) :
    walk nodes fuel 2407 = List.range' 2405 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2407).rule = .split 2 (25/8) 2405 2406 := by rfl
      simp only [walk, hr]
      rw [traversal_2405 f (by omega), traversal_2406 f (by omega)]
      change (List.range' 2405 1 ++ List.range' (2405+1) 1) ++
        [2405+(1+1)] = List.range' 2405 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2405) (n := 1+1)).symm

private theorem traversal_2408 (fuel : Nat) (hf : 2408 < fuel) :
    walk nodes fuel 2408 = List.range' 2394 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2408).rule = .split 1 (5/8) 2404 2407 := by rfl
      simp only [walk, hr]
      rw [traversal_2404 f (by omega), traversal_2407 f (by omega)]
      change (List.range' 2394 11 ++ List.range' (2394+11) 3) ++
        [2394+(11+3)] = List.range' 2394 ((11+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2394) (n := 11+3)).symm

private theorem traversal_2409 (fuel : Nat) (hf : 2409 < fuel) :
    walk nodes fuel 2409 = List.range' 2409 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2409).rule = .bound .vertex 3 (121661/393216) (421449/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2410 (fuel : Nat) (hf : 2410 < fuel) :
    walk nodes fuel 2410 = List.range' 2410 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2410).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2411 (fuel : Nat) (hf : 2411 < fuel) :
    walk nodes fuel 2411 = List.range' 2409 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2411).rule = .split 1 (5/8) 2409 2410 := by rfl
      simp only [walk, hr]
      rw [traversal_2409 f (by omega), traversal_2410 f (by omega)]
      change (List.range' 2409 1 ++ List.range' (2409+1) 1) ++
        [2409+(1+1)] = List.range' 2409 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2409) (n := 1+1)).symm

private theorem traversal_2412 (fuel : Nat) (hf : 2412 < fuel) :
    walk nodes fuel 2412 = List.range' 2394 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2412).rule = .split 0 (1/5) 2408 2411 := by rfl
      simp only [walk, hr]
      rw [traversal_2408 f (by omega), traversal_2411 f (by omega)]
      change (List.range' 2394 15 ++ List.range' (2394+15) 3) ++
        [2394+(15+3)] = List.range' 2394 ((15+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2394) (n := 15+3)).symm

private theorem traversal_2413 (fuel : Nat) (hf : 2413 < fuel) :
    walk nodes fuel 2413 = List.range' 2377 37 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2413).rule = .split 3 (9/4) 2393 2412 := by rfl
      simp only [walk, hr]
      rw [traversal_2393 f (by omega), traversal_2412 f (by omega)]
      change (List.range' 2377 17 ++ List.range' (2377+17) 19) ++
        [2377+(17+19)] = List.range' 2377 ((17+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2377) (n := 17+19)).symm

private theorem traversal_2414 (fuel : Nat) (hf : 2414 < fuel) :
    walk nodes fuel 2414 = List.range' 2414 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2414).rule = .bound .vertex 3 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2415 (fuel : Nat) (hf : 2415 < fuel) :
    walk nodes fuel 2415 = List.range' 2415 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2415).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2416 (fuel : Nat) (hf : 2416 < fuel) :
    walk nodes fuel 2416 = List.range' 2414 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2416).rule = .split 0 (1/5) 2414 2415 := by rfl
      simp only [walk, hr]
      rw [traversal_2414 f (by omega), traversal_2415 f (by omega)]
      change (List.range' 2414 1 ++ List.range' (2414+1) 1) ++
        [2414+(1+1)] = List.range' 2414 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2414) (n := 1+1)).symm

private theorem traversal_2417 (fuel : Nat) (hf : 2417 < fuel) :
    walk nodes fuel 2417 = List.range' 2417 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2417).rule = .bound .vertex 3 (121661/393216) (421449/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2418 (fuel : Nat) (hf : 2418 < fuel) :
    walk nodes fuel 2418 = List.range' 2414 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2418).rule = .split 3 (9/4) 2416 2417 := by rfl
      simp only [walk, hr]
      rw [traversal_2416 f (by omega), traversal_2417 f (by omega)]
      change (List.range' 2414 3 ++ List.range' (2414+3) 1) ++
        [2414+(3+1)] = List.range' 2414 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2414) (n := 3+1)).symm

private theorem traversal_2419 (fuel : Nat) (hf : 2419 < fuel) :
    walk nodes fuel 2419 = List.range' 2377 43 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2419).rule = .split 2 (15/4) 2413 2418 := by rfl
      simp only [walk, hr]
      rw [traversal_2413 f (by omega), traversal_2418 f (by omega)]
      change (List.range' 2377 37 ++ List.range' (2377+37) 5) ++
        [2377+(37+5)] = List.range' 2377 ((37+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2377) (n := 37+5)).symm

private theorem traversal_2420 (fuel : Nat) (hf : 2420 < fuel) :
    walk nodes fuel 2420 = List.range' 2420 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2420).rule = .bound .leftEnd 3 (44329/131072) (376145/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2421 (fuel : Nat) (hf : 2421 < fuel) :
    walk nodes fuel 2421 = List.range' 2421 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2421).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2422 (fuel : Nat) (hf : 2422 < fuel) :
    walk nodes fuel 2422 = List.range' 2420 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2422).rule = .split 2 (15/4) 2420 2421 := by rfl
      simp only [walk, hr]
      rw [traversal_2420 f (by omega), traversal_2421 f (by omega)]
      change (List.range' 2420 1 ++ List.range' (2420+1) 1) ++
        [2420+(1+1)] = List.range' 2420 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2420) (n := 1+1)).symm

private theorem traversal_2423 (fuel : Nat) (hf : 2423 < fuel) :
    walk nodes fuel 2423 = List.range' 2377 47 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2423).rule = .split 1 (5/4) 2419 2422 := by rfl
      simp only [walk, hr]
      rw [traversal_2419 f (by omega), traversal_2422 f (by omega)]
      change (List.range' 2377 43 ++ List.range' (2377+43) 3) ++
        [2377+(43+3)] = List.range' 2377 ((43+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2377) (n := 43+3)).symm

private theorem traversal_2424 (fuel : Nat) (hf : 2424 < fuel) :
    walk nodes fuel 2424 = List.range' 2424 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2424).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2425 (fuel : Nat) (hf : 2425 < fuel) :
    walk nodes fuel 2425 = List.range' 2377 49 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2425).rule = .split 0 (3/10) 2423 2424 := by rfl
      simp only [walk, hr]
      rw [traversal_2423 f (by omega), traversal_2424 f (by omega)]
      change (List.range' 2377 47 ++ List.range' (2377+47) 1) ++
        [2377+(47+1)] = List.range' 2377 ((47+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2377) (n := 47+1)).symm

private theorem traversal_2426 (fuel : Nat) (hf : 2426 < fuel) :
    walk nodes fuel 2426 = List.range' 2352 75 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2426).rule = .split 3 (3/2) 2376 2425 := by rfl
      simp only [walk, hr]
      rw [traversal_2376 f (by omega), traversal_2425 f (by omega)]
      change (List.range' 2352 25 ++ List.range' (2352+25) 49) ++
        [2352+(25+49)] = List.range' 2352 ((25+49)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2352) (n := 25+49)).symm

private theorem traversal_2427 (fuel : Nat) (hf : 2427 < fuel) :
    walk nodes fuel 2427 = List.range' 2269 159 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2427).rule = .split 2 (5/2) 2351 2426 := by rfl
      simp only [walk, hr]
      rw [traversal_2351 f (by omega), traversal_2426 f (by omega)]
      change (List.range' 2269 83 ++ List.range' (2269+83) 75) ++
        [2269+(83+75)] = List.range' 2269 ((83+75)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2269) (n := 83+75)).symm

private theorem traversal_2428 (fuel : Nat) (hf : 2428 < fuel) :
    walk nodes fuel 2428 = List.range' 2428 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2428).rule = .bound .leftEnd 1 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2429 (fuel : Nat) (hf : 2429 < fuel) :
    walk nodes fuel 2429 = List.range' 2429 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2429).rule = .bound .leftEnd 3 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2430 (fuel : Nat) (hf : 2430 < fuel) :
    walk nodes fuel 2430 = List.range' 2428 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2430).rule = .split 2 (5/4) 2428 2429 := by rfl
      simp only [walk, hr]
      rw [traversal_2428 f (by omega), traversal_2429 f (by omega)]
      change (List.range' 2428 1 ++ List.range' (2428+1) 1) ++
        [2428+(1+1)] = List.range' 2428 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2428) (n := 1+1)).symm

private theorem traversal_2431 (fuel : Nat) (hf : 2431 < fuel) :
    walk nodes fuel 2431 = List.range' 2431 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2431).rule = .bound .leftEnd 3 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2432 (fuel : Nat) (hf : 2432 < fuel) :
    walk nodes fuel 2432 = List.range' 2428 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2432).rule = .split 1 (15/4) 2430 2431 := by rfl
      simp only [walk, hr]
      rw [traversal_2430 f (by omega), traversal_2431 f (by omega)]
      change (List.range' 2428 3 ++ List.range' (2428+3) 1) ++
        [2428+(3+1)] = List.range' 2428 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2428) (n := 3+1)).symm

private theorem traversal_2433 (fuel : Nat) (hf : 2433 < fuel) :
    walk nodes fuel 2433 = List.range' 2433 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2433).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2434 (fuel : Nat) (hf : 2434 < fuel) :
    walk nodes fuel 2434 = List.range' 2428 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2434).rule = .split 0 (3/10) 2432 2433 := by rfl
      simp only [walk, hr]
      rw [traversal_2432 f (by omega), traversal_2433 f (by omega)]
      change (List.range' 2428 5 ++ List.range' (2428+5) 1) ++
        [2428+(5+1)] = List.range' 2428 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2428) (n := 5+1)).symm

private theorem traversal_2435 (fuel : Nat) (hf : 2435 < fuel) :
    walk nodes fuel 2435 = List.range' 2435 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2435).rule = .bound .leftEnd 1 (44329/131072) (376145/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2436 (fuel : Nat) (hf : 2436 < fuel) :
    walk nodes fuel 2436 = List.range' 2428 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2436).rule = .split 3 (3/2) 2434 2435 := by rfl
      simp only [walk, hr]
      rw [traversal_2434 f (by omega), traversal_2435 f (by omega)]
      change (List.range' 2428 7 ++ List.range' (2428+7) 1) ++
        [2428+(7+1)] = List.range' 2428 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2428) (n := 7+1)).symm

private theorem traversal_2437 (fuel : Nat) (hf : 2437 < fuel) :
    walk nodes fuel 2437 = List.range' 2437 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2437).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2438 (fuel : Nat) (hf : 2438 < fuel) :
    walk nodes fuel 2438 = List.range' 2428 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2438).rule = .split 2 (5/2) 2436 2437 := by rfl
      simp only [walk, hr]
      rw [traversal_2436 f (by omega), traversal_2437 f (by omega)]
      change (List.range' 2428 9 ++ List.range' (2428+9) 1) ++
        [2428+(9+1)] = List.range' 2428 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2428) (n := 9+1)).symm

private theorem traversal_2439 (fuel : Nat) (hf : 2439 < fuel) :
    walk nodes fuel 2439 = List.range' 2269 171 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2439).rule = .split 1 (5/2) 2427 2438 := by rfl
      simp only [walk, hr]
      rw [traversal_2427 f (by omega), traversal_2438 f (by omega)]
      change (List.range' 2269 159 ++ List.range' (2269+159) 11) ++
        [2269+(159+11)] = List.range' 2269 ((159+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2269) (n := 159+11)).symm

theorem traversal_2440 (fuel : Nat) (hf : 2440 < fuel) :
    walk nodes fuel 2440 = List.range' 0 2441 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2440).rule = .split 0 (1/10) 2268 2439 := by rfl
      simp only [walk, hr]
      rw [traversal_2268 f (by omega), traversal_2439 f (by omega)]
      change (List.range' 0 2269 ++ List.range' (0+2269) 171) ++
        [0+(2269+171)] = List.range' 0 ((2269+171)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 0) (n := 2269+171)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
