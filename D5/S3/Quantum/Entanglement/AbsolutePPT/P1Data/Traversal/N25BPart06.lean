/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart06
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart06
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart06.traversal_458,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart06.traversal_461,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart06.traversal_464,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart06.traversal_469,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart06.traversal_470
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart05
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_404 (fuel : Nat) (hf : 404 < fuel) :
    walk nodes fuel 404 = List.range' 404 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 404).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_405 (fuel : Nat) (hf : 405 < fuel) :
    walk nodes fuel 405 = List.range' 403 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 405).rule = .split 3 (189/64) 403 404 := by rfl
      simp only [walk, hr]
      rw [traversal_403 f (by omega), traversal_404 f (by omega)]
      change (List.range' 403 1 ++ List.range' (403+1) 1) ++
        [403+(1+1)] = List.range' 403 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 403) (n := 1+1)).symm

private theorem traversal_406 (fuel : Nat) (hf : 406 < fuel) :
    walk nodes fuel 406 = List.range' 402 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 406).rule = .split 2 (1109/256) 402 405 := by rfl
      simp only [walk, hr]
      rw [traversal_402 f (by omega), traversal_405 f (by omega)]
      change (List.range' 402 1 ++ List.range' (402+1) 3) ++
        [402+(1+3)] = List.range' 402 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 402) (n := 1+3)).symm

private theorem traversal_407 (fuel : Nat) (hf : 407 < fuel) :
    walk nodes fuel 407 = List.range' 407 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 407).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_408 (fuel : Nat) (hf : 408 < fuel) :
    walk nodes fuel 408 = List.range' 408 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 408).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_409 (fuel : Nat) (hf : 409 < fuel) :
    walk nodes fuel 409 = List.range' 409 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 409).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_410 (fuel : Nat) (hf : 410 < fuel) :
    walk nodes fuel 410 = List.range' 408 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 410).rule = .split 3 (189/64) 408 409 := by rfl
      simp only [walk, hr]
      rw [traversal_408 f (by omega), traversal_409 f (by omega)]
      change (List.range' 408 1 ++ List.range' (408+1) 1) ++
        [408+(1+1)] = List.range' 408 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 408) (n := 1+1)).symm

private theorem traversal_411 (fuel : Nat) (hf : 411 < fuel) :
    walk nodes fuel 411 = List.range' 407 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 411).rule = .split 2 (1109/256) 407 410 := by rfl
      simp only [walk, hr]
      rw [traversal_407 f (by omega), traversal_410 f (by omega)]
      change (List.range' 407 1 ++ List.range' (407+1) 3) ++
        [407+(1+3)] = List.range' 407 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 407) (n := 1+3)).symm

private theorem traversal_412 (fuel : Nat) (hf : 412 < fuel) :
    walk nodes fuel 412 = List.range' 402 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 412).rule = .split 1 (5/64) 406 411 := by rfl
      simp only [walk, hr]
      rw [traversal_406 f (by omega), traversal_411 f (by omega)]
      change (List.range' 402 5 ++ List.range' (402+5) 5) ++
        [402+(5+5)] = List.range' 402 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 402) (n := 5+5)).symm

private theorem traversal_413 (fuel : Nat) (hf : 413 < fuel) :
    walk nodes fuel 413 = List.range' 413 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 413).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_414 (fuel : Nat) (hf : 414 < fuel) :
    walk nodes fuel 414 = List.range' 414 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 414).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_415 (fuel : Nat) (hf : 415 < fuel) :
    walk nodes fuel 415 = List.range' 415 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 415).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_416 (fuel : Nat) (hf : 416 < fuel) :
    walk nodes fuel 416 = List.range' 414 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 416).rule = .split 3 (189/64) 414 415 := by rfl
      simp only [walk, hr]
      rw [traversal_414 f (by omega), traversal_415 f (by omega)]
      change (List.range' 414 1 ++ List.range' (414+1) 1) ++
        [414+(1+1)] = List.range' 414 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 414) (n := 1+1)).symm

private theorem traversal_417 (fuel : Nat) (hf : 417 < fuel) :
    walk nodes fuel 417 = List.range' 413 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 417).rule = .split 2 (1109/256) 413 416 := by rfl
      simp only [walk, hr]
      rw [traversal_413 f (by omega), traversal_416 f (by omega)]
      change (List.range' 413 1 ++ List.range' (413+1) 3) ++
        [413+(1+3)] = List.range' 413 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 413) (n := 1+3)).symm

private theorem traversal_418 (fuel : Nat) (hf : 418 < fuel) :
    walk nodes fuel 418 = List.range' 418 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 418).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_419 (fuel : Nat) (hf : 419 < fuel) :
    walk nodes fuel 419 = List.range' 419 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 419).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_420 (fuel : Nat) (hf : 420 < fuel) :
    walk nodes fuel 420 = List.range' 420 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 420).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_421 (fuel : Nat) (hf : 421 < fuel) :
    walk nodes fuel 421 = List.range' 419 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 421).rule = .split 0 (3/160) 419 420 := by rfl
      simp only [walk, hr]
      rw [traversal_419 f (by omega), traversal_420 f (by omega)]
      change (List.range' 419 1 ++ List.range' (419+1) 1) ++
        [419+(1+1)] = List.range' 419 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 419) (n := 1+1)).symm

private theorem traversal_422 (fuel : Nat) (hf : 422 < fuel) :
    walk nodes fuel 422 = List.range' 422 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 422).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_423 (fuel : Nat) (hf : 423 < fuel) :
    walk nodes fuel 423 = List.range' 419 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 423).rule = .split 3 (189/64) 421 422 := by rfl
      simp only [walk, hr]
      rw [traversal_421 f (by omega), traversal_422 f (by omega)]
      change (List.range' 419 3 ++ List.range' (419+3) 1) ++
        [419+(3+1)] = List.range' 419 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 419) (n := 3+1)).symm

private theorem traversal_424 (fuel : Nat) (hf : 424 < fuel) :
    walk nodes fuel 424 = List.range' 418 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 424).rule = .split 2 (1109/256) 418 423 := by rfl
      simp only [walk, hr]
      rw [traversal_418 f (by omega), traversal_423 f (by omega)]
      change (List.range' 418 1 ++ List.range' (418+1) 5) ++
        [418+(1+5)] = List.range' 418 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 418) (n := 1+5)).symm

private theorem traversal_425 (fuel : Nat) (hf : 425 < fuel) :
    walk nodes fuel 425 = List.range' 413 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 425).rule = .split 1 (5/64) 417 424 := by rfl
      simp only [walk, hr]
      rw [traversal_417 f (by omega), traversal_424 f (by omega)]
      change (List.range' 413 5 ++ List.range' (413+5) 7) ++
        [413+(5+7)] = List.range' 413 ((5+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 413) (n := 5+7)).symm

private theorem traversal_426 (fuel : Nat) (hf : 426 < fuel) :
    walk nodes fuel 426 = List.range' 402 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 426).rule = .split 0 (1/80) 412 425 := by rfl
      simp only [walk, hr]
      rw [traversal_412 f (by omega), traversal_425 f (by omega)]
      change (List.range' 402 11 ++ List.range' (402+11) 13) ++
        [402+(11+13)] = List.range' 402 ((11+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 402) (n := 11+13)).symm

private theorem traversal_427 (fuel : Nat) (hf : 427 < fuel) :
    walk nodes fuel 427 = List.range' 401 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 427).rule = .split 3 (93/32) 401 426 := by rfl
      simp only [walk, hr]
      rw [traversal_401 f (by omega), traversal_426 f (by omega)]
      change (List.range' 401 1 ++ List.range' (401+1) 25) ++
        [401+(1+25)] = List.range' 401 ((1+25)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 401) (n := 1+25)).symm

private theorem traversal_428 (fuel : Nat) (hf : 428 < fuel) :
    walk nodes fuel 428 = List.range' 398 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 428).rule = .split 2 (545/128) 400 427 := by rfl
      simp only [walk, hr]
      rw [traversal_400 f (by omega), traversal_427 f (by omega)]
      change (List.range' 398 3 ++ List.range' (398+3) 27) ++
        [398+(3+27)] = List.range' 398 ((3+27)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 398) (n := 3+27)).symm

private theorem traversal_429 (fuel : Nat) (hf : 429 < fuel) :
    walk nodes fuel 429 = List.range' 429 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 429).rule = .bound .rightEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_430 (fuel : Nat) (hf : 430 < fuel) :
    walk nodes fuel 430 = List.range' 430 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 430).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_431 (fuel : Nat) (hf : 431 < fuel) :
    walk nodes fuel 431 = List.range' 429 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 431).rule = .split 3 (93/32) 429 430 := by rfl
      simp only [walk, hr]
      rw [traversal_429 f (by omega), traversal_430 f (by omega)]
      change (List.range' 429 1 ++ List.range' (429+1) 1) ++
        [429+(1+1)] = List.range' 429 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 429) (n := 1+1)).symm

private theorem traversal_432 (fuel : Nat) (hf : 432 < fuel) :
    walk nodes fuel 432 = List.range' 432 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 432).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_433 (fuel : Nat) (hf : 433 < fuel) :
    walk nodes fuel 433 = List.range' 433 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 433).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_434 (fuel : Nat) (hf : 434 < fuel) :
    walk nodes fuel 434 = List.range' 434 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 434).rule = .bound .rightEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_435 (fuel : Nat) (hf : 435 < fuel) :
    walk nodes fuel 435 = List.range' 435 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 435).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_436 (fuel : Nat) (hf : 436 < fuel) :
    walk nodes fuel 436 = List.range' 434 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 436).rule = .split 3 (189/64) 434 435 := by rfl
      simp only [walk, hr]
      rw [traversal_434 f (by omega), traversal_435 f (by omega)]
      change (List.range' 434 1 ++ List.range' (434+1) 1) ++
        [434+(1+1)] = List.range' 434 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 434) (n := 1+1)).symm

private theorem traversal_437 (fuel : Nat) (hf : 437 < fuel) :
    walk nodes fuel 437 = List.range' 433 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 437).rule = .split 2 (1109/256) 433 436 := by rfl
      simp only [walk, hr]
      rw [traversal_433 f (by omega), traversal_436 f (by omega)]
      change (List.range' 433 1 ++ List.range' (433+1) 3) ++
        [433+(1+3)] = List.range' 433 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 433) (n := 1+3)).symm

private theorem traversal_438 (fuel : Nat) (hf : 438 < fuel) :
    walk nodes fuel 438 = List.range' 438 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 438).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_439 (fuel : Nat) (hf : 439 < fuel) :
    walk nodes fuel 439 = List.range' 433 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 439).rule = .split 1 (15/64) 437 438 := by rfl
      simp only [walk, hr]
      rw [traversal_437 f (by omega), traversal_438 f (by omega)]
      change (List.range' 433 5 ++ List.range' (433+5) 1) ++
        [433+(5+1)] = List.range' 433 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 433) (n := 5+1)).symm

private theorem traversal_440 (fuel : Nat) (hf : 440 < fuel) :
    walk nodes fuel 440 = List.range' 440 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 440).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_441 (fuel : Nat) (hf : 441 < fuel) :
    walk nodes fuel 441 = List.range' 433 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 441).rule = .split 0 (1/80) 439 440 := by rfl
      simp only [walk, hr]
      rw [traversal_439 f (by omega), traversal_440 f (by omega)]
      change (List.range' 433 7 ++ List.range' (433+7) 1) ++
        [433+(7+1)] = List.range' 433 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 433) (n := 7+1)).symm

private theorem traversal_442 (fuel : Nat) (hf : 442 < fuel) :
    walk nodes fuel 442 = List.range' 432 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 442).rule = .split 3 (93/32) 432 441 := by rfl
      simp only [walk, hr]
      rw [traversal_432 f (by omega), traversal_441 f (by omega)]
      change (List.range' 432 1 ++ List.range' (432+1) 9) ++
        [432+(1+9)] = List.range' 432 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 432) (n := 1+9)).symm

private theorem traversal_443 (fuel : Nat) (hf : 443 < fuel) :
    walk nodes fuel 443 = List.range' 429 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 443).rule = .split 2 (545/128) 431 442 := by rfl
      simp only [walk, hr]
      rw [traversal_431 f (by omega), traversal_442 f (by omega)]
      change (List.range' 429 3 ++ List.range' (429+3) 11) ++
        [429+(3+11)] = List.range' 429 ((3+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 429) (n := 3+11)).symm

private theorem traversal_444 (fuel : Nat) (hf : 444 < fuel) :
    walk nodes fuel 444 = List.range' 398 47 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 444).rule = .split 1 (5/32) 428 443 := by rfl
      simp only [walk, hr]
      rw [traversal_428 f (by omega), traversal_443 f (by omega)]
      change (List.range' 398 31 ++ List.range' (398+31) 15) ++
        [398+(31+15)] = List.range' 398 ((31+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 398) (n := 31+15)).symm

private theorem traversal_445 (fuel : Nat) (hf : 445 < fuel) :
    walk nodes fuel 445 = List.range' 445 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 445).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_446 (fuel : Nat) (hf : 446 < fuel) :
    walk nodes fuel 446 = List.range' 446 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 446).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_447 (fuel : Nat) (hf : 447 < fuel) :
    walk nodes fuel 447 = List.range' 447 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 447).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_448 (fuel : Nat) (hf : 448 < fuel) :
    walk nodes fuel 448 = List.range' 446 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 448).rule = .split 0 (3/80) 446 447 := by rfl
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
      have hr : (node nodes 449).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_450 (fuel : Nat) (hf : 450 < fuel) :
    walk nodes fuel 450 = List.range' 446 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 450).rule = .split 3 (93/32) 448 449 := by rfl
      simp only [walk, hr]
      rw [traversal_448 f (by omega), traversal_449 f (by omega)]
      change (List.range' 446 3 ++ List.range' (446+3) 1) ++
        [446+(3+1)] = List.range' 446 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 446) (n := 3+1)).symm

private theorem traversal_451 (fuel : Nat) (hf : 451 < fuel) :
    walk nodes fuel 451 = List.range' 445 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 451).rule = .split 2 (545/128) 445 450 := by rfl
      simp only [walk, hr]
      rw [traversal_445 f (by omega), traversal_450 f (by omega)]
      change (List.range' 445 1 ++ List.range' (445+1) 5) ++
        [445+(1+5)] = List.range' 445 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 445) (n := 1+5)).symm

private theorem traversal_452 (fuel : Nat) (hf : 452 < fuel) :
    walk nodes fuel 452 = List.range' 452 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 452).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_453 (fuel : Nat) (hf : 453 < fuel) :
    walk nodes fuel 453 = List.range' 453 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 453).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_454 (fuel : Nat) (hf : 454 < fuel) :
    walk nodes fuel 454 = List.range' 452 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 454).rule = .split 2 (545/128) 452 453 := by rfl
      simp only [walk, hr]
      rw [traversal_452 f (by omega), traversal_453 f (by omega)]
      change (List.range' 452 1 ++ List.range' (452+1) 1) ++
        [452+(1+1)] = List.range' 452 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 452) (n := 1+1)).symm

private theorem traversal_455 (fuel : Nat) (hf : 455 < fuel) :
    walk nodes fuel 455 = List.range' 445 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 455).rule = .split 1 (5/32) 451 454 := by rfl
      simp only [walk, hr]
      rw [traversal_451 f (by omega), traversal_454 f (by omega)]
      change (List.range' 445 7 ++ List.range' (445+7) 3) ++
        [445+(7+3)] = List.range' 445 ((7+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 445) (n := 7+3)).symm

private theorem traversal_456 (fuel : Nat) (hf : 456 < fuel) :
    walk nodes fuel 456 = List.range' 398 59 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 456).rule = .split 0 (1/40) 444 455 := by rfl
      simp only [walk, hr]
      rw [traversal_444 f (by omega), traversal_455 f (by omega)]
      change (List.range' 398 47 ++ List.range' (398+47) 11) ++
        [398+(47+11)] = List.range' 398 ((47+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 398) (n := 47+11)).symm

private theorem traversal_457 (fuel : Nat) (hf : 457 < fuel) :
    walk nodes fuel 457 = List.range' 397 61 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 457).rule = .split 3 (45/16) 397 456 := by rfl
      simp only [walk, hr]
      rw [traversal_397 f (by omega), traversal_456 f (by omega)]
      change (List.range' 397 1 ++ List.range' (397+1) 59) ++
        [397+(1+59)] = List.range' 397 ((1+59)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 397) (n := 1+59)).symm

theorem traversal_458 (fuel : Nat) (hf : 458 < fuel) :
    walk nodes fuel 458 = List.range' 394 65 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 458).rule = .split 2 (263/64) 396 457 := by rfl
      simp only [walk, hr]
      rw [traversal_396 f (by omega), traversal_457 f (by omega)]
      change (List.range' 394 3 ++ List.range' (394+3) 61) ++
        [394+(3+61)] = List.range' 394 ((3+61)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 394) (n := 3+61)).symm

private theorem traversal_459 (fuel : Nat) (hf : 459 < fuel) :
    walk nodes fuel 459 = List.range' 459 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 459).rule = .bound .rightEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_460 (fuel : Nat) (hf : 460 < fuel) :
    walk nodes fuel 460 = List.range' 460 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 460).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_461 (fuel : Nat) (hf : 461 < fuel) :
    walk nodes fuel 461 = List.range' 459 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 461).rule = .split 3 (45/16) 459 460 := by rfl
      simp only [walk, hr]
      rw [traversal_459 f (by omega), traversal_460 f (by omega)]
      change (List.range' 459 1 ++ List.range' (459+1) 1) ++
        [459+(1+1)] = List.range' 459 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 459) (n := 1+1)).symm

private theorem traversal_462 (fuel : Nat) (hf : 462 < fuel) :
    walk nodes fuel 462 = List.range' 462 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 462).rule = .bound .rightEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_463 (fuel : Nat) (hf : 463 < fuel) :
    walk nodes fuel 463 = List.range' 463 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 463).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_464 (fuel : Nat) (hf : 464 < fuel) :
    walk nodes fuel 464 = List.range' 462 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 464).rule = .split 0 (1/40) 462 463 := by rfl
      simp only [walk, hr]
      rw [traversal_462 f (by omega), traversal_463 f (by omega)]
      change (List.range' 462 1 ++ List.range' (462+1) 1) ++
        [462+(1+1)] = List.range' 462 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 462) (n := 1+1)).symm

private theorem traversal_465 (fuel : Nat) (hf : 465 < fuel) :
    walk nodes fuel 465 = List.range' 465 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 465).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_466 (fuel : Nat) (hf : 466 < fuel) :
    walk nodes fuel 466 = List.range' 466 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 466).rule = .bound .rightEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_467 (fuel : Nat) (hf : 467 < fuel) :
    walk nodes fuel 467 = List.range' 465 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 467).rule = .split 2 (545/128) 465 466 := by rfl
      simp only [walk, hr]
      rw [traversal_465 f (by omega), traversal_466 f (by omega)]
      change (List.range' 465 1 ++ List.range' (465+1) 1) ++
        [465+(1+1)] = List.range' 465 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 465) (n := 1+1)).symm

private theorem traversal_468 (fuel : Nat) (hf : 468 < fuel) :
    walk nodes fuel 468 = List.range' 468 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 468).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_469 (fuel : Nat) (hf : 469 < fuel) :
    walk nodes fuel 469 = List.range' 465 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 469).rule = .split 1 (15/32) 467 468 := by rfl
      simp only [walk, hr]
      rw [traversal_467 f (by omega), traversal_468 f (by omega)]
      change (List.range' 465 3 ++ List.range' (465+3) 1) ++
        [465+(3+1)] = List.range' 465 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 465) (n := 3+1)).symm

theorem traversal_470 (fuel : Nat) (hf : 470 < fuel) :
    walk nodes fuel 470 = List.range' 470 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 470).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
