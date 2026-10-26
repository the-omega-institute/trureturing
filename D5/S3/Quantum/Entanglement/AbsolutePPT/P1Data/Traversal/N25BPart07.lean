/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart07
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart07
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart07.traversal_485,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart07.traversal_486,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart07.traversal_487,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart07.traversal_488,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart07.traversal_537
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart05
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart06
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_471 (fuel : Nat) (hf : 471 < fuel) :
    walk nodes fuel 471 = List.range' 465 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 471).rule = .split 0 (1/40) 469 470 := by rfl
      simp only [walk, hr]
      rw [traversal_469 f (by omega), traversal_470 f (by omega)]
      change (List.range' 465 5 ++ List.range' (465+5) 1) ++
        [465+(5+1)] = List.range' 465 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 465) (n := 5+1)).symm

private theorem traversal_472 (fuel : Nat) (hf : 472 < fuel) :
    walk nodes fuel 472 = List.range' 462 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 472).rule = .split 3 (45/16) 464 471 := by rfl
      simp only [walk, hr]
      rw [traversal_464 f (by omega), traversal_471 f (by omega)]
      change (List.range' 462 3 ++ List.range' (462+3) 7) ++
        [462+(3+7)] = List.range' 462 ((3+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 462) (n := 3+7)).symm

private theorem traversal_473 (fuel : Nat) (hf : 473 < fuel) :
    walk nodes fuel 473 = List.range' 459 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 473).rule = .split 2 (263/64) 461 472 := by rfl
      simp only [walk, hr]
      rw [traversal_461 f (by omega), traversal_472 f (by omega)]
      change (List.range' 459 3 ++ List.range' (459+3) 11) ++
        [459+(3+11)] = List.range' 459 ((3+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 459) (n := 3+11)).symm

private theorem traversal_474 (fuel : Nat) (hf : 474 < fuel) :
    walk nodes fuel 474 = List.range' 394 81 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 474).rule = .split 1 (5/16) 458 473 := by rfl
      simp only [walk, hr]
      rw [traversal_458 f (by omega), traversal_473 f (by omega)]
      change (List.range' 394 65 ++ List.range' (394+65) 15) ++
        [394+(65+15)] = List.range' 394 ((65+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 394) (n := 65+15)).symm

private theorem traversal_475 (fuel : Nat) (hf : 475 < fuel) :
    walk nodes fuel 475 = List.range' 475 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 475).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_476 (fuel : Nat) (hf : 476 < fuel) :
    walk nodes fuel 476 = List.range' 476 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 476).rule = .bound .rightEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_477 (fuel : Nat) (hf : 477 < fuel) :
    walk nodes fuel 477 = List.range' 475 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 477).rule = .split 0 (3/40) 475 476 := by rfl
      simp only [walk, hr]
      rw [traversal_475 f (by omega), traversal_476 f (by omega)]
      change (List.range' 475 1 ++ List.range' (475+1) 1) ++
        [475+(1+1)] = List.range' 475 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 475) (n := 1+1)).symm

private theorem traversal_478 (fuel : Nat) (hf : 478 < fuel) :
    walk nodes fuel 478 = List.range' 478 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 478).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_479 (fuel : Nat) (hf : 479 < fuel) :
    walk nodes fuel 479 = List.range' 475 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 479).rule = .split 3 (45/16) 477 478 := by rfl
      simp only [walk, hr]
      rw [traversal_477 f (by omega), traversal_478 f (by omega)]
      change (List.range' 475 3 ++ List.range' (475+3) 1) ++
        [475+(3+1)] = List.range' 475 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 475) (n := 3+1)).symm

private theorem traversal_480 (fuel : Nat) (hf : 480 < fuel) :
    walk nodes fuel 480 = List.range' 480 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 480).rule = .bound .rightEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_481 (fuel : Nat) (hf : 481 < fuel) :
    walk nodes fuel 481 = List.range' 475 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 481).rule = .split 2 (263/64) 479 480 := by rfl
      simp only [walk, hr]
      rw [traversal_479 f (by omega), traversal_480 f (by omega)]
      change (List.range' 475 5 ++ List.range' (475+5) 1) ++
        [475+(5+1)] = List.range' 475 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 475) (n := 5+1)).symm

private theorem traversal_482 (fuel : Nat) (hf : 482 < fuel) :
    walk nodes fuel 482 = List.range' 482 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 482).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_483 (fuel : Nat) (hf : 483 < fuel) :
    walk nodes fuel 483 = List.range' 475 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 483).rule = .split 1 (5/16) 481 482 := by rfl
      simp only [walk, hr]
      rw [traversal_481 f (by omega), traversal_482 f (by omega)]
      change (List.range' 475 7 ++ List.range' (475+7) 1) ++
        [475+(7+1)] = List.range' 475 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 475) (n := 7+1)).symm

private theorem traversal_484 (fuel : Nat) (hf : 484 < fuel) :
    walk nodes fuel 484 = List.range' 394 91 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 484).rule = .split 0 (1/20) 474 483 := by rfl
      simp only [walk, hr]
      rw [traversal_474 f (by omega), traversal_483 f (by omega)]
      change (List.range' 394 81 ++ List.range' (394+81) 9) ++
        [394+(81+9)] = List.range' 394 ((81+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 394) (n := 81+9)).symm

theorem traversal_485 (fuel : Nat) (hf : 485 < fuel) :
    walk nodes fuel 485 = List.range' 393 93 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 485).rule = .split 3 (21/8) 393 484 := by rfl
      simp only [walk, hr]
      rw [traversal_393 f (by omega), traversal_484 f (by omega)]
      change (List.range' 393 1 ++ List.range' (393+1) 91) ++
        [393+(1+91)] = List.range' 393 ((1+91)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 393) (n := 1+91)).symm

theorem traversal_486 (fuel : Nat) (hf : 486 < fuel) :
    walk nodes fuel 486 = List.range' 486 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 486).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_487 (fuel : Nat) (hf : 487 < fuel) :
    walk nodes fuel 487 = List.range' 487 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 487).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_488 (fuel : Nat) (hf : 488 < fuel) :
    walk nodes fuel 488 = List.range' 488 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 488).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_489 (fuel : Nat) (hf : 489 < fuel) :
    walk nodes fuel 489 = List.range' 489 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 489).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_490 (fuel : Nat) (hf : 490 < fuel) :
    walk nodes fuel 490 = List.range' 490 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 490).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_491 (fuel : Nat) (hf : 491 < fuel) :
    walk nodes fuel 491 = List.range' 491 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 491).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_492 (fuel : Nat) (hf : 492 < fuel) :
    walk nodes fuel 492 = List.range' 490 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 492).rule = .split 3 (381/128) 490 491 := by rfl
      simp only [walk, hr]
      rw [traversal_490 f (by omega), traversal_491 f (by omega)]
      change (List.range' 490 1 ++ List.range' (490+1) 1) ++
        [490+(1+1)] = List.range' 490 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 490) (n := 1+1)).symm

private theorem traversal_493 (fuel : Nat) (hf : 493 < fuel) :
    walk nodes fuel 493 = List.range' 493 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 493).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_494 (fuel : Nat) (hf : 494 < fuel) :
    walk nodes fuel 494 = List.range' 490 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 494).rule = .split 2 (2275/512) 492 493 := by rfl
      simp only [walk, hr]
      rw [traversal_492 f (by omega), traversal_493 f (by omega)]
      change (List.range' 490 3 ++ List.range' (490+3) 1) ++
        [490+(3+1)] = List.range' 490 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 490) (n := 3+1)).symm

private theorem traversal_495 (fuel : Nat) (hf : 495 < fuel) :
    walk nodes fuel 495 = List.range' 495 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 495).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_496 (fuel : Nat) (hf : 496 < fuel) :
    walk nodes fuel 496 = List.range' 496 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 496).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_497 (fuel : Nat) (hf : 497 < fuel) :
    walk nodes fuel 497 = List.range' 495 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 497).rule = .split 3 (381/128) 495 496 := by rfl
      simp only [walk, hr]
      rw [traversal_495 f (by omega), traversal_496 f (by omega)]
      change (List.range' 495 1 ++ List.range' (495+1) 1) ++
        [495+(1+1)] = List.range' 495 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 495) (n := 1+1)).symm

private theorem traversal_498 (fuel : Nat) (hf : 498 < fuel) :
    walk nodes fuel 498 = List.range' 498 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 498).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_499 (fuel : Nat) (hf : 499 < fuel) :
    walk nodes fuel 499 = List.range' 499 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 499).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_500 (fuel : Nat) (hf : 500 < fuel) :
    walk nodes fuel 500 = List.range' 500 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 500).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_501 (fuel : Nat) (hf : 501 < fuel) :
    walk nodes fuel 501 = List.range' 499 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 501).rule = .split 0 (1/320) 499 500 := by rfl
      simp only [walk, hr]
      rw [traversal_499 f (by omega), traversal_500 f (by omega)]
      change (List.range' 499 1 ++ List.range' (499+1) 1) ++
        [499+(1+1)] = List.range' 499 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 499) (n := 1+1)).symm

private theorem traversal_502 (fuel : Nat) (hf : 502 < fuel) :
    walk nodes fuel 502 = List.range' 498 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 502).rule = .split 3 (381/128) 498 501 := by rfl
      simp only [walk, hr]
      rw [traversal_498 f (by omega), traversal_501 f (by omega)]
      change (List.range' 498 1 ++ List.range' (498+1) 3) ++
        [498+(1+3)] = List.range' 498 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 498) (n := 1+3)).symm

private theorem traversal_503 (fuel : Nat) (hf : 503 < fuel) :
    walk nodes fuel 503 = List.range' 495 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 503).rule = .split 2 (2275/512) 497 502 := by rfl
      simp only [walk, hr]
      rw [traversal_497 f (by omega), traversal_502 f (by omega)]
      change (List.range' 495 3 ++ List.range' (495+3) 5) ++
        [495+(3+5)] = List.range' 495 ((3+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 495) (n := 3+5)).symm

private theorem traversal_504 (fuel : Nat) (hf : 504 < fuel) :
    walk nodes fuel 504 = List.range' 490 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 504).rule = .split 1 (5/128) 494 503 := by rfl
      simp only [walk, hr]
      rw [traversal_494 f (by omega), traversal_503 f (by omega)]
      change (List.range' 490 5 ++ List.range' (490+5) 9) ++
        [490+(5+9)] = List.range' 490 ((5+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 490) (n := 5+9)).symm

private theorem traversal_505 (fuel : Nat) (hf : 505 < fuel) :
    walk nodes fuel 505 = List.range' 505 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 505).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_506 (fuel : Nat) (hf : 506 < fuel) :
    walk nodes fuel 506 = List.range' 506 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 506).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_507 (fuel : Nat) (hf : 507 < fuel) :
    walk nodes fuel 507 = List.range' 507 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 507).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_508 (fuel : Nat) (hf : 508 < fuel) :
    walk nodes fuel 508 = List.range' 508 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 508).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_509 (fuel : Nat) (hf : 509 < fuel) :
    walk nodes fuel 509 = List.range' 507 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 509).rule = .split 2 (4569/1024) 507 508 := by rfl
      simp only [walk, hr]
      rw [traversal_507 f (by omega), traversal_508 f (by omega)]
      change (List.range' 507 1 ++ List.range' (507+1) 1) ++
        [507+(1+1)] = List.range' 507 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 507) (n := 1+1)).symm

private theorem traversal_510 (fuel : Nat) (hf : 510 < fuel) :
    walk nodes fuel 510 = List.range' 510 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 510).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_511 (fuel : Nat) (hf : 511 < fuel) :
    walk nodes fuel 511 = List.range' 507 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 511).rule = .split 1 (5/256) 509 510 := by rfl
      simp only [walk, hr]
      rw [traversal_509 f (by omega), traversal_510 f (by omega)]
      change (List.range' 507 3 ++ List.range' (507+3) 1) ++
        [507+(3+1)] = List.range' 507 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 507) (n := 3+1)).symm

private theorem traversal_512 (fuel : Nat) (hf : 512 < fuel) :
    walk nodes fuel 512 = List.range' 512 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 512).rule = .infeasible 4 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_513 (fuel : Nat) (hf : 513 < fuel) :
    walk nodes fuel 513 = List.range' 507 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 513).rule = .split 0 (3/320) 511 512 := by rfl
      simp only [walk, hr]
      rw [traversal_511 f (by omega), traversal_512 f (by omega)]
      change (List.range' 507 5 ++ List.range' (507+5) 1) ++
        [507+(5+1)] = List.range' 507 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 507) (n := 5+1)).symm

private theorem traversal_514 (fuel : Nat) (hf : 514 < fuel) :
    walk nodes fuel 514 = List.range' 506 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 514).rule = .split 3 (381/128) 506 513 := by rfl
      simp only [walk, hr]
      rw [traversal_506 f (by omega), traversal_513 f (by omega)]
      change (List.range' 506 1 ++ List.range' (506+1) 7) ++
        [506+(1+7)] = List.range' 506 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 506) (n := 1+7)).symm

private theorem traversal_515 (fuel : Nat) (hf : 515 < fuel) :
    walk nodes fuel 515 = List.range' 505 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 515).rule = .split 2 (2275/512) 505 514 := by rfl
      simp only [walk, hr]
      rw [traversal_505 f (by omega), traversal_514 f (by omega)]
      change (List.range' 505 1 ++ List.range' (505+1) 9) ++
        [505+(1+9)] = List.range' 505 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 505) (n := 1+9)).symm

private theorem traversal_516 (fuel : Nat) (hf : 516 < fuel) :
    walk nodes fuel 516 = List.range' 516 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 516).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_517 (fuel : Nat) (hf : 517 < fuel) :
    walk nodes fuel 517 = List.range' 517 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 517).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_518 (fuel : Nat) (hf : 518 < fuel) :
    walk nodes fuel 518 = List.range' 518 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 518).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_519 (fuel : Nat) (hf : 519 < fuel) :
    walk nodes fuel 519 = List.range' 517 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 519).rule = .split 3 (381/128) 517 518 := by rfl
      simp only [walk, hr]
      rw [traversal_517 f (by omega), traversal_518 f (by omega)]
      change (List.range' 517 1 ++ List.range' (517+1) 1) ++
        [517+(1+1)] = List.range' 517 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 517) (n := 1+1)).symm

private theorem traversal_520 (fuel : Nat) (hf : 520 < fuel) :
    walk nodes fuel 520 = List.range' 516 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 520).rule = .split 2 (2275/512) 516 519 := by rfl
      simp only [walk, hr]
      rw [traversal_516 f (by omega), traversal_519 f (by omega)]
      change (List.range' 516 1 ++ List.range' (516+1) 3) ++
        [516+(1+3)] = List.range' 516 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 516) (n := 1+3)).symm

private theorem traversal_521 (fuel : Nat) (hf : 521 < fuel) :
    walk nodes fuel 521 = List.range' 505 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 521).rule = .split 1 (5/128) 515 520 := by rfl
      simp only [walk, hr]
      rw [traversal_515 f (by omega), traversal_520 f (by omega)]
      change (List.range' 505 11 ++ List.range' (505+11) 5) ++
        [505+(11+5)] = List.range' 505 ((11+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 505) (n := 11+5)).symm

private theorem traversal_522 (fuel : Nat) (hf : 522 < fuel) :
    walk nodes fuel 522 = List.range' 490 33 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 522).rule = .split 0 (1/160) 504 521 := by rfl
      simp only [walk, hr]
      rw [traversal_504 f (by omega), traversal_521 f (by omega)]
      change (List.range' 490 15 ++ List.range' (490+15) 17) ++
        [490+(15+17)] = List.range' 490 ((15+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 490) (n := 15+17)).symm

private theorem traversal_523 (fuel : Nat) (hf : 523 < fuel) :
    walk nodes fuel 523 = List.range' 489 35 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 523).rule = .split 3 (189/64) 489 522 := by rfl
      simp only [walk, hr]
      rw [traversal_489 f (by omega), traversal_522 f (by omega)]
      change (List.range' 489 1 ++ List.range' (489+1) 33) ++
        [489+(1+33)] = List.range' 489 ((1+33)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 489) (n := 1+33)).symm

private theorem traversal_524 (fuel : Nat) (hf : 524 < fuel) :
    walk nodes fuel 524 = List.range' 524 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 524).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_525 (fuel : Nat) (hf : 525 < fuel) :
    walk nodes fuel 525 = List.range' 525 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 525).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_526 (fuel : Nat) (hf : 526 < fuel) :
    walk nodes fuel 526 = List.range' 526 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 526).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_527 (fuel : Nat) (hf : 527 < fuel) :
    walk nodes fuel 527 = List.range' 527 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 527).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_528 (fuel : Nat) (hf : 528 < fuel) :
    walk nodes fuel 528 = List.range' 528 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 528).rule = .infeasible 4 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_529 (fuel : Nat) (hf : 529 < fuel) :
    walk nodes fuel 529 = List.range' 527 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 529).rule = .split 0 (3/320) 527 528 := by rfl
      simp only [walk, hr]
      rw [traversal_527 f (by omega), traversal_528 f (by omega)]
      change (List.range' 527 1 ++ List.range' (527+1) 1) ++
        [527+(1+1)] = List.range' 527 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 527) (n := 1+1)).symm

private theorem traversal_530 (fuel : Nat) (hf : 530 < fuel) :
    walk nodes fuel 530 = List.range' 526 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 530).rule = .split 3 (381/128) 526 529 := by rfl
      simp only [walk, hr]
      rw [traversal_526 f (by omega), traversal_529 f (by omega)]
      change (List.range' 526 1 ++ List.range' (526+1) 3) ++
        [526+(1+3)] = List.range' 526 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 526) (n := 1+3)).symm

private theorem traversal_531 (fuel : Nat) (hf : 531 < fuel) :
    walk nodes fuel 531 = List.range' 531 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 531).rule = .bound .rightEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_532 (fuel : Nat) (hf : 532 < fuel) :
    walk nodes fuel 532 = List.range' 526 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 532).rule = .split 2 (2313/512) 530 531 := by rfl
      simp only [walk, hr]
      rw [traversal_530 f (by omega), traversal_531 f (by omega)]
      change (List.range' 526 5 ++ List.range' (526+5) 1) ++
        [526+(5+1)] = List.range' 526 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 526) (n := 5+1)).symm

private theorem traversal_533 (fuel : Nat) (hf : 533 < fuel) :
    walk nodes fuel 533 = List.range' 533 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 533).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_534 (fuel : Nat) (hf : 534 < fuel) :
    walk nodes fuel 534 = List.range' 526 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 534).rule = .split 1 (5/128) 532 533 := by rfl
      simp only [walk, hr]
      rw [traversal_532 f (by omega), traversal_533 f (by omega)]
      change (List.range' 526 7 ++ List.range' (526+7) 1) ++
        [526+(7+1)] = List.range' 526 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 526) (n := 7+1)).symm

private theorem traversal_535 (fuel : Nat) (hf : 535 < fuel) :
    walk nodes fuel 535 = List.range' 525 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 535).rule = .split 0 (1/160) 525 534 := by rfl
      simp only [walk, hr]
      rw [traversal_525 f (by omega), traversal_534 f (by omega)]
      change (List.range' 525 1 ++ List.range' (525+1) 9) ++
        [525+(1+9)] = List.range' 525 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 525) (n := 1+9)).symm

private theorem traversal_536 (fuel : Nat) (hf : 536 < fuel) :
    walk nodes fuel 536 = List.range' 524 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 536).rule = .split 3 (189/64) 524 535 := by rfl
      simp only [walk, hr]
      rw [traversal_524 f (by omega), traversal_535 f (by omega)]
      change (List.range' 524 1 ++ List.range' (524+1) 11) ++
        [524+(1+11)] = List.range' 524 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 524) (n := 1+11)).symm

theorem traversal_537 (fuel : Nat) (hf : 537 < fuel) :
    walk nodes fuel 537 = List.range' 489 49 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 537).rule = .split 2 (1147/256) 523 536 := by rfl
      simp only [walk, hr]
      rw [traversal_523 f (by omega), traversal_536 f (by omega)]
      change (List.range' 489 35 ++ List.range' (489+35) 13) ++
        [489+(35+13)] = List.range' 489 ((35+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 489) (n := 35+13)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
