/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart06
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart06
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart06.traversal_434,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart06.traversal_439,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart06.traversal_464,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart06.traversal_465,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart06.traversal_466,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart06.traversal_469,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart06.traversal_470
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart05
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_403 (fuel : Nat) (hf : 403 < fuel) :
    walk nodes fuel 403 = List.range' 403 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 403).rule = .bound .leftEnd 2 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_404 (fuel : Nat) (hf : 404 < fuel) :
    walk nodes fuel 404 = List.range' 404 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 404).rule = .bound .leftEnd 8 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_405 (fuel : Nat) (hf : 405 < fuel) :
    walk nodes fuel 405 = List.range' 405 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 405).rule = .bound .leftEnd 3 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_406 (fuel : Nat) (hf : 406 < fuel) :
    walk nodes fuel 406 = List.range' 404 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 406).rule = .split 1 (135/64) 404 405 := by rfl
      simp only [walk, hr]
      rw [traversal_404 f (by omega), traversal_405 f (by omega)]
      change (List.range' 404 1 ++ List.range' (404+1) 1) ++
        [404+(1+1)] = List.range' 404 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 404) (n := 1+1)).symm

private theorem traversal_407 (fuel : Nat) (hf : 407 < fuel) :
    walk nodes fuel 407 = List.range' 407 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 407).rule = .bound .leftEnd 2 (17367/32768) (494269/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_408 (fuel : Nat) (hf : 408 < fuel) :
    walk nodes fuel 408 = List.range' 404 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 408).rule = .split 0 (1/80) 406 407 := by rfl
      simp only [walk, hr]
      rw [traversal_406 f (by omega), traversal_407 f (by omega)]
      change (List.range' 404 3 ++ List.range' (404+3) 1) ++
        [404+(3+1)] = List.range' 404 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 404) (n := 3+1)).symm

private theorem traversal_409 (fuel : Nat) (hf : 409 < fuel) :
    walk nodes fuel 409 = List.range' 403 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 409).rule = .split 3 (27/32) 403 408 := by rfl
      simp only [walk, hr]
      rw [traversal_403 f (by omega), traversal_408 f (by omega)]
      change (List.range' 403 1 ++ List.range' (403+1) 5) ++
        [403+(1+5)] = List.range' 403 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 403) (n := 1+5)).symm

private theorem traversal_410 (fuel : Nat) (hf : 410 < fuel) :
    walk nodes fuel 410 = List.range' 400 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 410).rule = .split 2 (317/128) 402 409 := by rfl
      simp only [walk, hr]
      rw [traversal_402 f (by omega), traversal_409 f (by omega)]
      change (List.range' 400 3 ++ List.range' (400+3) 7) ++
        [400+(3+7)] = List.range' 400 ((3+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 400) (n := 3+7)).symm

private theorem traversal_411 (fuel : Nat) (hf : 411 < fuel) :
    walk nodes fuel 411 = List.range' 399 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 411).rule = .split 1 (65/32) 399 410 := by rfl
      simp only [walk, hr]
      rw [traversal_399 f (by omega), traversal_410 f (by omega)]
      change (List.range' 399 1 ++ List.range' (399+1) 11) ++
        [399+(1+11)] = List.range' 399 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 399) (n := 1+11)).symm

private theorem traversal_412 (fuel : Nat) (hf : 412 < fuel) :
    walk nodes fuel 412 = List.range' 412 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 412).rule = .bound .leftEnd 8 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_413 (fuel : Nat) (hf : 413 < fuel) :
    walk nodes fuel 413 = List.range' 413 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 413).rule = .bound .leftEnd 3 (53593/98304) (479349/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_414 (fuel : Nat) (hf : 414 < fuel) :
    walk nodes fuel 414 = List.range' 412 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 414).rule = .split 1 (65/32) 412 413 := by rfl
      simp only [walk, hr]
      rw [traversal_412 f (by omega), traversal_413 f (by omega)]
      change (List.range' 412 1 ++ List.range' (412+1) 1) ++
        [412+(1+1)] = List.range' 412 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 412) (n := 1+1)).symm

private theorem traversal_415 (fuel : Nat) (hf : 415 < fuel) :
    walk nodes fuel 415 = List.range' 399 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 415).rule = .split 0 (1/40) 411 414 := by rfl
      simp only [walk, hr]
      rw [traversal_411 f (by omega), traversal_414 f (by omega)]
      change (List.range' 399 13 ++ List.range' (399+13) 3) ++
        [399+(13+3)] = List.range' 399 ((13+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 399) (n := 13+3)).symm

private theorem traversal_416 (fuel : Nat) (hf : 416 < fuel) :
    walk nodes fuel 416 = List.range' 416 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 416).rule = .bound .leftEnd 8 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_417 (fuel : Nat) (hf : 417 < fuel) :
    walk nodes fuel 417 = List.range' 417 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 417).rule = .bound .leftEnd 8 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_418 (fuel : Nat) (hf : 418 < fuel) :
    walk nodes fuel 418 = List.range' 418 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 418).rule = .bound .leftEnd 8 (8259/16384) (519739/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_419 (fuel : Nat) (hf : 419 < fuel) :
    walk nodes fuel 419 = List.range' 419 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 419).rule = .bound .leftEnd 3 (8259/16384) (519739/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_420 (fuel : Nat) (hf : 420 < fuel) :
    walk nodes fuel 420 = List.range' 418 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 420).rule = .split 1 (135/64) 418 419 := by rfl
      simp only [walk, hr]
      rw [traversal_418 f (by omega), traversal_419 f (by omega)]
      change (List.range' 418 1 ++ List.range' (418+1) 1) ++
        [418+(1+1)] = List.range' 418 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 418) (n := 1+1)).symm

private theorem traversal_421 (fuel : Nat) (hf : 421 < fuel) :
    walk nodes fuel 421 = List.range' 421 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 421).rule = .bound .leftEnd 3 (8259/16384) (519739/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_422 (fuel : Nat) (hf : 422 < fuel) :
    walk nodes fuel 422 = List.range' 418 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 422).rule = .split 0 (1/80) 420 421 := by rfl
      simp only [walk, hr]
      rw [traversal_420 f (by omega), traversal_421 f (by omega)]
      change (List.range' 418 3 ++ List.range' (418+3) 1) ++
        [418+(3+1)] = List.range' 418 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 418) (n := 3+1)).symm

private theorem traversal_423 (fuel : Nat) (hf : 423 < fuel) :
    walk nodes fuel 423 = List.range' 423 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 423).rule = .bound .leftEnd 8 (15783/32768) (271997/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_424 (fuel : Nat) (hf : 424 < fuel) :
    walk nodes fuel 424 = List.range' 424 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 424).rule = .bound .leftEnd 3 (15783/32768) (271997/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_425 (fuel : Nat) (hf : 425 < fuel) :
    walk nodes fuel 425 = List.range' 423 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 425).rule = .split 0 (1/80) 423 424 := by rfl
      simp only [walk, hr]
      rw [traversal_423 f (by omega), traversal_424 f (by omega)]
      change (List.range' 423 1 ++ List.range' (423+1) 1) ++
        [423+(1+1)] = List.range' 423 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 423) (n := 1+1)).symm

private theorem traversal_426 (fuel : Nat) (hf : 426 < fuel) :
    walk nodes fuel 426 = List.range' 418 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 426).rule = .split 3 (33/32) 422 425 := by rfl
      simp only [walk, hr]
      rw [traversal_422 f (by omega), traversal_425 f (by omega)]
      change (List.range' 418 5 ++ List.range' (418+5) 3) ++
        [418+(5+3)] = List.range' 418 ((5+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 418) (n := 5+3)).symm

private theorem traversal_427 (fuel : Nat) (hf : 427 < fuel) :
    walk nodes fuel 427 = List.range' 417 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 427).rule = .split 2 (317/128) 417 426 := by rfl
      simp only [walk, hr]
      rw [traversal_417 f (by omega), traversal_426 f (by omega)]
      change (List.range' 417 1 ++ List.range' (417+1) 9) ++
        [417+(1+9)] = List.range' 417 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 417) (n := 1+9)).symm

private theorem traversal_428 (fuel : Nat) (hf : 428 < fuel) :
    walk nodes fuel 428 = List.range' 416 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 428).rule = .split 1 (65/32) 416 427 := by rfl
      simp only [walk, hr]
      rw [traversal_416 f (by omega), traversal_427 f (by omega)]
      change (List.range' 416 1 ++ List.range' (416+1) 11) ++
        [416+(1+11)] = List.range' 416 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 416) (n := 1+11)).symm

private theorem traversal_429 (fuel : Nat) (hf : 429 < fuel) :
    walk nodes fuel 429 = List.range' 429 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 429).rule = .bound .leftEnd 8 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_430 (fuel : Nat) (hf : 430 < fuel) :
    walk nodes fuel 430 = List.range' 430 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 430).rule = .bound .leftEnd 3 (32301/65536) (132691/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_431 (fuel : Nat) (hf : 431 < fuel) :
    walk nodes fuel 431 = List.range' 429 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 431).rule = .split 1 (65/32) 429 430 := by rfl
      simp only [walk, hr]
      rw [traversal_429 f (by omega), traversal_430 f (by omega)]
      change (List.range' 429 1 ++ List.range' (429+1) 1) ++
        [429+(1+1)] = List.range' 429 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 429) (n := 1+1)).symm

private theorem traversal_432 (fuel : Nat) (hf : 432 < fuel) :
    walk nodes fuel 432 = List.range' 416 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 432).rule = .split 0 (1/40) 428 431 := by rfl
      simp only [walk, hr]
      rw [traversal_428 f (by omega), traversal_431 f (by omega)]
      change (List.range' 416 13 ++ List.range' (416+13) 3) ++
        [416+(13+3)] = List.range' 416 ((13+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 416) (n := 13+3)).symm

private theorem traversal_433 (fuel : Nat) (hf : 433 < fuel) :
    walk nodes fuel 433 = List.range' 399 35 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 433).rule = .split 3 (15/16) 415 432 := by rfl
      simp only [walk, hr]
      rw [traversal_415 f (by omega), traversal_432 f (by omega)]
      change (List.range' 399 17 ++ List.range' (399+17) 17) ++
        [399+(17+17)] = List.range' 399 ((17+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 399) (n := 17+17)).symm

theorem traversal_434 (fuel : Nat) (hf : 434 < fuel) :
    walk nodes fuel 434 = List.range' 398 37 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 434).rule = .split 2 (149/64) 398 433 := by rfl
      simp only [walk, hr]
      rw [traversal_398 f (by omega), traversal_433 f (by omega)]
      change (List.range' 398 1 ++ List.range' (398+1) 35) ++
        [398+(1+35)] = List.range' 398 ((1+35)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 398) (n := 1+35)).symm

private theorem traversal_435 (fuel : Nat) (hf : 435 < fuel) :
    walk nodes fuel 435 = List.range' 435 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 435).rule = .bound .leftEnd 8 (55085/98304) (467413/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_436 (fuel : Nat) (hf : 436 < fuel) :
    walk nodes fuel 436 = List.range' 436 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 436).rule = .bound .leftEnd 2 (2329/4096) (460925/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_437 (fuel : Nat) (hf : 437 < fuel) :
    walk nodes fuel 437 = List.range' 437 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 437).rule = .bound .leftEnd 8 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_438 (fuel : Nat) (hf : 438 < fuel) :
    walk nodes fuel 438 = List.range' 436 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 438).rule = .split 3 (51/64) 436 437 := by rfl
      simp only [walk, hr]
      rw [traversal_436 f (by omega), traversal_437 f (by omega)]
      change (List.range' 436 1 ++ List.range' (436+1) 1) ++
        [436+(1+1)] = List.range' 436 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 436) (n := 1+1)).symm

theorem traversal_439 (fuel : Nat) (hf : 439 < fuel) :
    walk nodes fuel 439 = List.range' 435 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 439).rule = .split 2 (539/256) 435 438 := by rfl
      simp only [walk, hr]
      rw [traversal_435 f (by omega), traversal_438 f (by omega)]
      change (List.range' 435 1 ++ List.range' (435+1) 3) ++
        [435+(1+3)] = List.range' 435 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 435) (n := 1+3)).symm

private theorem traversal_440 (fuel : Nat) (hf : 440 < fuel) :
    walk nodes fuel 440 = List.range' 440 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 440).rule = .bound .leftEnd 2 (2329/4096) (460925/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_441 (fuel : Nat) (hf : 441 < fuel) :
    walk nodes fuel 441 = List.range' 441 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 441).rule = .bound .leftEnd 8 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_442 (fuel : Nat) (hf : 442 < fuel) :
    walk nodes fuel 442 = List.range' 442 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 442).rule = .bound .leftEnd 2 (4555/8192) (471431/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_443 (fuel : Nat) (hf : 443 < fuel) :
    walk nodes fuel 443 = List.range' 443 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 443).rule = .bound .leftEnd 8 (421/768) (239093/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_444 (fuel : Nat) (hf : 444 < fuel) :
    walk nodes fuel 444 = List.range' 442 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 444).rule = .split 3 (105/128) 442 443 := by rfl
      simp only [walk, hr]
      rw [traversal_442 f (by omega), traversal_443 f (by omega)]
      change (List.range' 442 1 ++ List.range' (442+1) 1) ++
        [442+(1+1)] = List.range' 442 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 442) (n := 1+1)).symm

private theorem traversal_445 (fuel : Nat) (hf : 445 < fuel) :
    walk nodes fuel 445 = List.range' 441 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 445).rule = .split 2 (1059/512) 441 444 := by rfl
      simp only [walk, hr]
      rw [traversal_441 f (by omega), traversal_444 f (by omega)]
      change (List.range' 441 1 ++ List.range' (441+1) 3) ++
        [441+(1+3)] = List.range' 441 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 441) (n := 1+3)).symm

private theorem traversal_446 (fuel : Nat) (hf : 446 < fuel) :
    walk nodes fuel 446 = List.range' 446 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 446).rule = .bound .leftEnd 2 (4555/8192) (471431/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_447 (fuel : Nat) (hf : 447 < fuel) :
    walk nodes fuel 447 = List.range' 447 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 447).rule = .bound .leftEnd 1 (421/768) (239093/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_448 (fuel : Nat) (hf : 448 < fuel) :
    walk nodes fuel 448 = List.range' 446 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 448).rule = .split 3 (105/128) 446 447 := by rfl
      simp only [walk, hr]
      rw [traversal_446 f (by omega), traversal_447 f (by omega)]
      change (List.range' 446 1 ++ List.range' (446+1) 1) ++
        [446+(1+1)] = List.range' 446 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 446) (n := 1+1)).symm

private theorem traversal_449 (fuel : Nat) (hf : 449 < fuel) :
    walk nodes fuel 449 = List.range' 449 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 449).rule = .bound .leftEnd 2 (4555/8192) (471431/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_450 (fuel : Nat) (hf : 450 < fuel) :
    walk nodes fuel 450 = List.range' 450 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 450).rule = .bound .leftEnd 1 (421/768) (239093/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_451 (fuel : Nat) (hf : 451 < fuel) :
    walk nodes fuel 451 = List.range' 451 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 451).rule = .bound .leftEnd 2 (421/768) (239093/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_452 (fuel : Nat) (hf : 452 < fuel) :
    walk nodes fuel 452 = List.range' 450 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 452).rule = .split 2 (2137/1024) 450 451 := by rfl
      simp only [walk, hr]
      rw [traversal_450 f (by omega), traversal_451 f (by omega)]
      change (List.range' 450 1 ++ List.range' (450+1) 1) ++
        [450+(1+1)] = List.range' 450 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 450) (n := 1+1)).symm

private theorem traversal_453 (fuel : Nat) (hf : 453 < fuel) :
    walk nodes fuel 453 = List.range' 453 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 453).rule = .bound .leftEnd 1 (421/768) (239093/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_454 (fuel : Nat) (hf : 454 < fuel) :
    walk nodes fuel 454 = List.range' 450 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 454).rule = .split 1 (595/256) 452 453 := by rfl
      simp only [walk, hr]
      rw [traversal_452 f (by omega), traversal_453 f (by omega)]
      change (List.range' 450 3 ++ List.range' (450+3) 1) ++
        [450+(3+1)] = List.range' 450 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 450) (n := 3+1)).symm

private theorem traversal_455 (fuel : Nat) (hf : 455 < fuel) :
    walk nodes fuel 455 = List.range' 455 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 455).rule = .bound .leftEnd 1 (421/768) (239093/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_456 (fuel : Nat) (hf : 456 < fuel) :
    walk nodes fuel 456 = List.range' 450 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 456).rule = .split 0 (1/320) 454 455 := by rfl
      simp only [walk, hr]
      rw [traversal_454 f (by omega), traversal_455 f (by omega)]
      change (List.range' 450 5 ++ List.range' (450+5) 1) ++
        [450+(5+1)] = List.range' 450 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 450) (n := 5+1)).symm

private theorem traversal_457 (fuel : Nat) (hf : 457 < fuel) :
    walk nodes fuel 457 = List.range' 449 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 457).rule = .split 3 (105/128) 449 456 := by rfl
      simp only [walk, hr]
      rw [traversal_449 f (by omega), traversal_456 f (by omega)]
      change (List.range' 449 1 ++ List.range' (449+1) 7) ++
        [449+(1+7)] = List.range' 449 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 449) (n := 1+7)).symm

private theorem traversal_458 (fuel : Nat) (hf : 458 < fuel) :
    walk nodes fuel 458 = List.range' 446 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 458).rule = .split 2 (1059/512) 448 457 := by rfl
      simp only [walk, hr]
      rw [traversal_448 f (by omega), traversal_457 f (by omega)]
      change (List.range' 446 3 ++ List.range' (446+3) 9) ++
        [446+(3+9)] = List.range' 446 ((3+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 446) (n := 3+9)).symm

private theorem traversal_459 (fuel : Nat) (hf : 459 < fuel) :
    walk nodes fuel 459 = List.range' 441 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 459).rule = .split 1 (295/128) 445 458 := by rfl
      simp only [walk, hr]
      rw [traversal_445 f (by omega), traversal_458 f (by omega)]
      change (List.range' 441 5 ++ List.range' (441+5) 13) ++
        [441+(5+13)] = List.range' 441 ((5+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 441) (n := 5+13)).symm

private theorem traversal_460 (fuel : Nat) (hf : 460 < fuel) :
    walk nodes fuel 460 = List.range' 460 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 460).rule = .bound .leftEnd 8 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_461 (fuel : Nat) (hf : 461 < fuel) :
    walk nodes fuel 461 = List.range' 461 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 461).rule = .bound .leftEnd 1 (27137/49152) (59339/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_462 (fuel : Nat) (hf : 462 < fuel) :
    walk nodes fuel 462 = List.range' 460 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 462).rule = .split 1 (295/128) 460 461 := by rfl
      simp only [walk, hr]
      rw [traversal_460 f (by omega), traversal_461 f (by omega)]
      change (List.range' 460 1 ++ List.range' (460+1) 1) ++
        [460+(1+1)] = List.range' 460 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 460) (n := 1+1)).symm

private theorem traversal_463 (fuel : Nat) (hf : 463 < fuel) :
    walk nodes fuel 463 = List.range' 441 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 463).rule = .split 0 (1/160) 459 462 := by rfl
      simp only [walk, hr]
      rw [traversal_459 f (by omega), traversal_462 f (by omega)]
      change (List.range' 441 19 ++ List.range' (441+19) 3) ++
        [441+(19+3)] = List.range' 441 ((19+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 441) (n := 19+3)).symm

theorem traversal_464 (fuel : Nat) (hf : 464 < fuel) :
    walk nodes fuel 464 = List.range' 440 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 464).rule = .split 3 (51/64) 440 463 := by rfl
      simp only [walk, hr]
      rw [traversal_440 f (by omega), traversal_463 f (by omega)]
      change (List.range' 440 1 ++ List.range' (440+1) 23) ++
        [440+(1+23)] = List.range' 440 ((1+23)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 440) (n := 1+23)).symm

theorem traversal_465 (fuel : Nat) (hf : 465 < fuel) :
    walk nodes fuel 465 = List.range' 465 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 465).rule = .bound .leftEnd 2 (2329/4096) (460925/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_466 (fuel : Nat) (hf : 466 < fuel) :
    walk nodes fuel 466 = List.range' 466 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 466).rule = .bound .leftEnd 2 (4555/8192) (471431/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_467 (fuel : Nat) (hf : 467 < fuel) :
    walk nodes fuel 467 = List.range' 467 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 467).rule = .bound .leftEnd 8 (421/768) (239093/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_468 (fuel : Nat) (hf : 468 < fuel) :
    walk nodes fuel 468 = List.range' 468 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 468).rule = .bound .leftEnd 2 (421/768) (239093/524288) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_469 (fuel : Nat) (hf : 469 < fuel) :
    walk nodes fuel 469 = List.range' 467 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 469).rule = .split 1 (585/256) 467 468 := by rfl
      simp only [walk, hr]
      rw [traversal_467 f (by omega), traversal_468 f (by omega)]
      change (List.range' 467 1 ++ List.range' (467+1) 1) ++
        [467+(1+1)] = List.range' 467 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 467) (n := 1+1)).symm

theorem traversal_470 (fuel : Nat) (hf : 470 < fuel) :
    walk nodes fuel 470 = List.range' 470 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 470).rule = .bound .leftEnd 2 (421/768) (239093/524288) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
