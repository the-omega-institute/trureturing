/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart07
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart07
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart07.traversal_495,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart07.traversal_518,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart07.traversal_527,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart07.traversal_532,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart07.traversal_535
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N30A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30APart06
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_469 (fuel : Nat) (hf : 469 < fuel) :
    walk nodes fuel 469 = List.range' 423 47 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 469).rule = .split 1 (5/4) 423 468 := by rfl
      simp only [walk, hr]
      rw [traversal_423 f (by omega), traversal_468 f (by omega)]
      change (List.range' 423 1 ++ List.range' (423+1) 45) ++
        [423+(1+45)] = List.range' 423 ((1+45)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 423) (n := 1+45)).symm

private theorem traversal_470 (fuel : Nat) (hf : 470 < fuel) :
    walk nodes fuel 470 = List.range' 470 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 470).rule = .bound .leftEnd 5 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_471 (fuel : Nat) (hf : 471 < fuel) :
    walk nodes fuel 471 = List.range' 471 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 471).rule = .bound .leftEnd 1 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_472 (fuel : Nat) (hf : 472 < fuel) :
    walk nodes fuel 472 = List.range' 470 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 472).rule = .split 0 (2/5) 470 471 := by rfl
      simp only [walk, hr]
      rw [traversal_470 f (by omega), traversal_471 f (by omega)]
      change (List.range' 470 1 ++ List.range' (470+1) 1) ++
        [470+(1+1)] = List.range' 470 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 470) (n := 1+1)).symm

private theorem traversal_473 (fuel : Nat) (hf : 473 < fuel) :
    walk nodes fuel 473 = List.range' 473 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 473).rule = .bound .leftEnd 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_474 (fuel : Nat) (hf : 474 < fuel) :
    walk nodes fuel 474 = List.range' 470 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 474).rule = .split 3 (3/4) 472 473 := by rfl
      simp only [walk, hr]
      rw [traversal_472 f (by omega), traversal_473 f (by omega)]
      change (List.range' 470 3 ++ List.range' (470+3) 1) ++
        [470+(3+1)] = List.range' 470 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 470) (n := 3+1)).symm

private theorem traversal_475 (fuel : Nat) (hf : 475 < fuel) :
    walk nodes fuel 475 = List.range' 475 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 475).rule = .bound .vertex 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_476 (fuel : Nat) (hf : 476 < fuel) :
    walk nodes fuel 476 = List.range' 476 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 476).rule = .bound .vertex 1 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_477 (fuel : Nat) (hf : 477 < fuel) :
    walk nodes fuel 477 = List.range' 475 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 477).rule = .split 3 (3/4) 475 476 := by rfl
      simp only [walk, hr]
      rw [traversal_475 f (by omega), traversal_476 f (by omega)]
      change (List.range' 475 1 ++ List.range' (475+1) 1) ++
        [475+(1+1)] = List.range' 475 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 475) (n := 1+1)).symm

private theorem traversal_478 (fuel : Nat) (hf : 478 < fuel) :
    walk nodes fuel 478 = List.range' 470 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 478).rule = .split 2 (5/4) 474 477 := by rfl
      simp only [walk, hr]
      rw [traversal_474 f (by omega), traversal_477 f (by omega)]
      change (List.range' 470 5 ++ List.range' (470+5) 3) ++
        [470+(5+3)] = List.range' 470 ((5+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 470) (n := 5+3)).symm

private theorem traversal_479 (fuel : Nat) (hf : 479 < fuel) :
    walk nodes fuel 479 = List.range' 479 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 479).rule = .bound .leftEnd 1 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_480 (fuel : Nat) (hf : 480 < fuel) :
    walk nodes fuel 480 = List.range' 480 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 480).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_481 (fuel : Nat) (hf : 481 < fuel) :
    walk nodes fuel 481 = List.range' 479 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 481).rule = .split 2 (5/4) 479 480 := by rfl
      simp only [walk, hr]
      rw [traversal_479 f (by omega), traversal_480 f (by omega)]
      change (List.range' 479 1 ++ List.range' (479+1) 1) ++
        [479+(1+1)] = List.range' 479 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 479) (n := 1+1)).symm

private theorem traversal_482 (fuel : Nat) (hf : 482 < fuel) :
    walk nodes fuel 482 = List.range' 470 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 482).rule = .split 1 (5/4) 478 481 := by rfl
      simp only [walk, hr]
      rw [traversal_478 f (by omega), traversal_481 f (by omega)]
      change (List.range' 470 9 ++ List.range' (470+9) 3) ++
        [470+(9+3)] = List.range' 470 ((9+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 470) (n := 9+3)).symm

private theorem traversal_483 (fuel : Nat) (hf : 483 < fuel) :
    walk nodes fuel 483 = List.range' 423 61 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 483).rule = .split 0 (3/10) 469 482 := by rfl
      simp only [walk, hr]
      rw [traversal_469 f (by omega), traversal_482 f (by omega)]
      change (List.range' 423 47 ++ List.range' (423+47) 13) ++
        [423+(47+13)] = List.range' 423 ((47+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 423) (n := 47+13)).symm

private theorem traversal_484 (fuel : Nat) (hf : 484 < fuel) :
    walk nodes fuel 484 = List.range' 484 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 484).rule = .infeasible 3 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_485 (fuel : Nat) (hf : 485 < fuel) :
    walk nodes fuel 485 = List.range' 485 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 485).rule = .bound .vertex 1 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_486 (fuel : Nat) (hf : 486 < fuel) :
    walk nodes fuel 486 = List.range' 486 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 486).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_487 (fuel : Nat) (hf : 487 < fuel) :
    walk nodes fuel 487 = List.range' 485 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 487).rule = .split 3 (9/4) 485 486 := by rfl
      simp only [walk, hr]
      rw [traversal_485 f (by omega), traversal_486 f (by omega)]
      change (List.range' 485 1 ++ List.range' (485+1) 1) ++
        [485+(1+1)] = List.range' 485 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 485) (n := 1+1)).symm

private theorem traversal_488 (fuel : Nat) (hf : 488 < fuel) :
    walk nodes fuel 488 = List.range' 484 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 488).rule = .split 2 (5/4) 484 487 := by rfl
      simp only [walk, hr]
      rw [traversal_484 f (by omega), traversal_487 f (by omega)]
      change (List.range' 484 1 ++ List.range' (484+1) 3) ++
        [484+(1+3)] = List.range' 484 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 484) (n := 1+3)).symm

private theorem traversal_489 (fuel : Nat) (hf : 489 < fuel) :
    walk nodes fuel 489 = List.range' 489 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 489).rule = .infeasible 3 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_490 (fuel : Nat) (hf : 490 < fuel) :
    walk nodes fuel 490 = List.range' 490 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 490).rule = .bound .leftEnd 1 (44329/131072) (376145/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_491 (fuel : Nat) (hf : 491 < fuel) :
    walk nodes fuel 491 = List.range' 489 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 491).rule = .split 2 (5/4) 489 490 := by rfl
      simp only [walk, hr]
      rw [traversal_489 f (by omega), traversal_490 f (by omega)]
      change (List.range' 489 1 ++ List.range' (489+1) 1) ++
        [489+(1+1)] = List.range' 489 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 489) (n := 1+1)).symm

private theorem traversal_492 (fuel : Nat) (hf : 492 < fuel) :
    walk nodes fuel 492 = List.range' 484 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 492).rule = .split 1 (5/4) 488 491 := by rfl
      simp only [walk, hr]
      rw [traversal_488 f (by omega), traversal_491 f (by omega)]
      change (List.range' 484 5 ++ List.range' (484+5) 3) ++
        [484+(5+3)] = List.range' 484 ((5+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 484) (n := 5+3)).symm

private theorem traversal_493 (fuel : Nat) (hf : 493 < fuel) :
    walk nodes fuel 493 = List.range' 493 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 493).rule = .bound .vertex 1 (44329/131072) (376145/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_494 (fuel : Nat) (hf : 494 < fuel) :
    walk nodes fuel 494 = List.range' 484 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 494).rule = .split 0 (3/10) 492 493 := by rfl
      simp only [walk, hr]
      rw [traversal_492 f (by omega), traversal_493 f (by omega)]
      change (List.range' 484 9 ++ List.range' (484+9) 1) ++
        [484+(9+1)] = List.range' 484 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 484) (n := 9+1)).symm

theorem traversal_495 (fuel : Nat) (hf : 495 < fuel) :
    walk nodes fuel 495 = List.range' 423 73 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 495).rule = .split 3 (3/2) 483 494 := by rfl
      simp only [walk, hr]
      rw [traversal_483 f (by omega), traversal_494 f (by omega)]
      change (List.range' 423 61 ++ List.range' (423+61) 11) ++
        [423+(61+11)] = List.range' 423 ((61+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 423) (n := 61+11)).symm

private theorem traversal_496 (fuel : Nat) (hf : 496 < fuel) :
    walk nodes fuel 496 = List.range' 496 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 496).rule = .bound .vertex 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_497 (fuel : Nat) (hf : 497 < fuel) :
    walk nodes fuel 497 = List.range' 497 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 497).rule = .bound .vertex 8 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_498 (fuel : Nat) (hf : 498 < fuel) :
    walk nodes fuel 498 = List.range' 498 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 498).rule = .bound .vertex 0 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_499 (fuel : Nat) (hf : 499 < fuel) :
    walk nodes fuel 499 = List.range' 499 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 499).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_500 (fuel : Nat) (hf : 500 < fuel) :
    walk nodes fuel 500 = List.range' 498 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 500).rule = .split 1 (5/8) 498 499 := by rfl
      simp only [walk, hr]
      rw [traversal_498 f (by omega), traversal_499 f (by omega)]
      change (List.range' 498 1 ++ List.range' (498+1) 1) ++
        [498+(1+1)] = List.range' 498 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 498) (n := 1+1)).symm

private theorem traversal_501 (fuel : Nat) (hf : 501 < fuel) :
    walk nodes fuel 501 = List.range' 497 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 501).rule = .split 0 (1/5) 497 500 := by rfl
      simp only [walk, hr]
      rw [traversal_497 f (by omega), traversal_500 f (by omega)]
      change (List.range' 497 1 ++ List.range' (497+1) 3) ++
        [497+(1+3)] = List.range' 497 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 497) (n := 1+3)).symm

private theorem traversal_502 (fuel : Nat) (hf : 502 < fuel) :
    walk nodes fuel 502 = List.range' 496 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 502).rule = .split 3 (3/4) 496 501 := by rfl
      simp only [walk, hr]
      rw [traversal_496 f (by omega), traversal_501 f (by omega)]
      change (List.range' 496 1 ++ List.range' (496+1) 5) ++
        [496+(1+5)] = List.range' 496 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 496) (n := 1+5)).symm

private theorem traversal_503 (fuel : Nat) (hf : 503 < fuel) :
    walk nodes fuel 503 = List.range' 503 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 503).rule = .infeasible 1 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_504 (fuel : Nat) (hf : 504 < fuel) :
    walk nodes fuel 504 = List.range' 504 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 504).rule = .bound .vertex 0 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_505 (fuel : Nat) (hf : 505 < fuel) :
    walk nodes fuel 505 = List.range' 505 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 505).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_506 (fuel : Nat) (hf : 506 < fuel) :
    walk nodes fuel 506 = List.range' 504 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 506).rule = .split 1 (5/8) 504 505 := by rfl
      simp only [walk, hr]
      rw [traversal_504 f (by omega), traversal_505 f (by omega)]
      change (List.range' 504 1 ++ List.range' (504+1) 1) ++
        [504+(1+1)] = List.range' 504 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 504) (n := 1+1)).symm

private theorem traversal_507 (fuel : Nat) (hf : 507 < fuel) :
    walk nodes fuel 507 = List.range' 507 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 507).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_508 (fuel : Nat) (hf : 508 < fuel) :
    walk nodes fuel 508 = List.range' 504 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 508).rule = .split 0 (1/5) 506 507 := by rfl
      simp only [walk, hr]
      rw [traversal_506 f (by omega), traversal_507 f (by omega)]
      change (List.range' 504 3 ++ List.range' (504+3) 1) ++
        [504+(3+1)] = List.range' 504 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 504) (n := 3+1)).symm

private theorem traversal_509 (fuel : Nat) (hf : 509 < fuel) :
    walk nodes fuel 509 = List.range' 503 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 509).rule = .split 3 (3/4) 503 508 := by rfl
      simp only [walk, hr]
      rw [traversal_503 f (by omega), traversal_508 f (by omega)]
      change (List.range' 503 1 ++ List.range' (503+1) 5) ++
        [503+(1+5)] = List.range' 503 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 503) (n := 1+5)).symm

private theorem traversal_510 (fuel : Nat) (hf : 510 < fuel) :
    walk nodes fuel 510 = List.range' 496 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 510).rule = .split 2 (15/4) 502 509 := by rfl
      simp only [walk, hr]
      rw [traversal_502 f (by omega), traversal_509 f (by omega)]
      change (List.range' 496 7 ++ List.range' (496+7) 7) ++
        [496+(7+7)] = List.range' 496 ((7+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 496) (n := 7+7)).symm

private theorem traversal_511 (fuel : Nat) (hf : 511 < fuel) :
    walk nodes fuel 511 = List.range' 511 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 511).rule = .bound .vertex 2 (908093/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_512 (fuel : Nat) (hf : 512 < fuel) :
    walk nodes fuel 512 = List.range' 512 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 512).rule = .bound .vertex 3 (376145/786432) (132987/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_513 (fuel : Nat) (hf : 513 < fuel) :
    walk nodes fuel 513 = List.range' 511 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 513).rule = .split 3 (3/4) 511 512 := by rfl
      simp only [walk, hr]
      rw [traversal_511 f (by omega), traversal_512 f (by omega)]
      change (List.range' 511 1 ++ List.range' (511+1) 1) ++
        [511+(1+1)] = List.range' 511 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 511) (n := 1+1)).symm

private theorem traversal_514 (fuel : Nat) (hf : 514 < fuel) :
    walk nodes fuel 514 = List.range' 514 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 514).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_515 (fuel : Nat) (hf : 515 < fuel) :
    walk nodes fuel 515 = List.range' 511 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 515).rule = .split 2 (15/4) 513 514 := by rfl
      simp only [walk, hr]
      rw [traversal_513 f (by omega), traversal_514 f (by omega)]
      change (List.range' 511 3 ++ List.range' (511+3) 1) ++
        [511+(3+1)] = List.range' 511 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 511) (n := 3+1)).symm

private theorem traversal_516 (fuel : Nat) (hf : 516 < fuel) :
    walk nodes fuel 516 = List.range' 496 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 516).rule = .split 1 (5/4) 510 515 := by rfl
      simp only [walk, hr]
      rw [traversal_510 f (by omega), traversal_515 f (by omega)]
      change (List.range' 496 15 ++ List.range' (496+15) 5) ++
        [496+(15+5)] = List.range' 496 ((15+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 496) (n := 15+5)).symm

private theorem traversal_517 (fuel : Nat) (hf : 517 < fuel) :
    walk nodes fuel 517 = List.range' 517 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 517).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_518 (fuel : Nat) (hf : 518 < fuel) :
    walk nodes fuel 518 = List.range' 496 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 518).rule = .split 0 (3/10) 516 517 := by rfl
      simp only [walk, hr]
      rw [traversal_516 f (by omega), traversal_517 f (by omega)]
      change (List.range' 496 21 ++ List.range' (496+21) 1) ++
        [496+(21+1)] = List.range' 496 ((21+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 496) (n := 21+1)).symm

private theorem traversal_519 (fuel : Nat) (hf : 519 < fuel) :
    walk nodes fuel 519 = List.range' 519 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 519).rule = .bound .vertex 6 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_520 (fuel : Nat) (hf : 520 < fuel) :
    walk nodes fuel 520 = List.range' 520 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 520).rule = .bound .vertex 1 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_521 (fuel : Nat) (hf : 521 < fuel) :
    walk nodes fuel 521 = List.range' 519 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 521).rule = .split 1 (5/8) 519 520 := by rfl
      simp only [walk, hr]
      rw [traversal_519 f (by omega), traversal_520 f (by omega)]
      change (List.range' 519 1 ++ List.range' (519+1) 1) ++
        [519+(1+1)] = List.range' 519 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 519) (n := 1+1)).symm

private theorem traversal_522 (fuel : Nat) (hf : 522 < fuel) :
    walk nodes fuel 522 = List.range' 522 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 522).rule = .bound .vertex 1 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_523 (fuel : Nat) (hf : 523 < fuel) :
    walk nodes fuel 523 = List.range' 523 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 523).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_524 (fuel : Nat) (hf : 524 < fuel) :
    walk nodes fuel 524 = List.range' 522 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 524).rule = .split 2 (25/8) 522 523 := by rfl
      simp only [walk, hr]
      rw [traversal_522 f (by omega), traversal_523 f (by omega)]
      change (List.range' 522 1 ++ List.range' (522+1) 1) ++
        [522+(1+1)] = List.range' 522 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 522) (n := 1+1)).symm

private theorem traversal_525 (fuel : Nat) (hf : 525 < fuel) :
    walk nodes fuel 525 = List.range' 525 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 525).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_526 (fuel : Nat) (hf : 526 < fuel) :
    walk nodes fuel 526 = List.range' 522 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 526).rule = .split 1 (5/8) 524 525 := by rfl
      simp only [walk, hr]
      rw [traversal_524 f (by omega), traversal_525 f (by omega)]
      change (List.range' 522 3 ++ List.range' (522+3) 1) ++
        [522+(3+1)] = List.range' 522 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 522) (n := 3+1)).symm

theorem traversal_527 (fuel : Nat) (hf : 527 < fuel) :
    walk nodes fuel 527 = List.range' 519 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 527).rule = .split 0 (1/5) 521 526 := by rfl
      simp only [walk, hr]
      rw [traversal_521 f (by omega), traversal_526 f (by omega)]
      change (List.range' 519 3 ++ List.range' (519+3) 5) ++
        [519+(3+5)] = List.range' 519 ((3+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 519) (n := 3+5)).symm

private theorem traversal_528 (fuel : Nat) (hf : 528 < fuel) :
    walk nodes fuel 528 = List.range' 528 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 528).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_529 (fuel : Nat) (hf : 529 < fuel) :
    walk nodes fuel 529 = List.range' 529 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 529).rule = .bound .vertex 6 (126023/393216) (408363/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_530 (fuel : Nat) (hf : 530 < fuel) :
    walk nodes fuel 530 = List.range' 530 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 530).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_531 (fuel : Nat) (hf : 531 < fuel) :
    walk nodes fuel 531 = List.range' 529 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 531).rule = .split 3 (21/8) 529 530 := by rfl
      simp only [walk, hr]
      rw [traversal_529 f (by omega), traversal_530 f (by omega)]
      change (List.range' 529 1 ++ List.range' (529+1) 1) ++
        [529+(1+1)] = List.range' 529 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 529) (n := 1+1)).symm

theorem traversal_532 (fuel : Nat) (hf : 532 < fuel) :
    walk nodes fuel 532 = List.range' 528 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 532).rule = .split 2 (25/8) 528 531 := by rfl
      simp only [walk, hr]
      rw [traversal_528 f (by omega), traversal_531 f (by omega)]
      change (List.range' 528 1 ++ List.range' (528+1) 3) ++
        [528+(1+3)] = List.range' 528 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 528) (n := 1+3)).symm

private theorem traversal_533 (fuel : Nat) (hf : 533 < fuel) :
    walk nodes fuel 533 = List.range' 533 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 533).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_534 (fuel : Nat) (hf : 534 < fuel) :
    walk nodes fuel 534 = List.range' 534 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 534).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_535 (fuel : Nat) (hf : 535 < fuel) :
    walk nodes fuel 535 = List.range' 533 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 535).rule = .split 2 (25/8) 533 534 := by rfl
      simp only [walk, hr]
      rw [traversal_533 f (by omega), traversal_534 f (by omega)]
      change (List.range' 533 1 ++ List.range' (533+1) 1) ++
        [533+(1+1)] = List.range' 533 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 533) (n := 1+1)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
