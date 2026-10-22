/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart08
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart08
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30APart08.traversal_566
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N30A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30APart06
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30APart07
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_536 (fuel : Nat) (hf : 536 < fuel) :
    walk nodes fuel 536 = List.range' 528 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 536).rule = .split 1 (5/8) 532 535 := by rfl
      simp only [walk, hr]
      rw [traversal_532 f (by omega), traversal_535 f (by omega)]
      change (List.range' 528 5 ++ List.range' (528+5) 3) ++
        [528+(5+3)] = List.range' 528 ((5+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 528) (n := 5+3)).symm

private theorem traversal_537 (fuel : Nat) (hf : 537 < fuel) :
    walk nodes fuel 537 = List.range' 537 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 537).rule = .bound .vertex 3 (121661/393216) (421449/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_538 (fuel : Nat) (hf : 538 < fuel) :
    walk nodes fuel 538 = List.range' 528 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 538).rule = .split 0 (1/5) 536 537 := by rfl
      simp only [walk, hr]
      rw [traversal_536 f (by omega), traversal_537 f (by omega)]
      change (List.range' 528 9 ++ List.range' (528+9) 1) ++
        [528+(9+1)] = List.range' 528 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 528) (n := 9+1)).symm

private theorem traversal_539 (fuel : Nat) (hf : 539 < fuel) :
    walk nodes fuel 539 = List.range' 519 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 539).rule = .split 3 (9/4) 527 538 := by rfl
      simp only [walk, hr]
      rw [traversal_527 f (by omega), traversal_538 f (by omega)]
      change (List.range' 519 9 ++ List.range' (519+9) 11) ++
        [519+(9+11)] = List.range' 519 ((9+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 519) (n := 9+11)).symm

private theorem traversal_540 (fuel : Nat) (hf : 540 < fuel) :
    walk nodes fuel 540 = List.range' 540 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 540).rule = .bound .vertex 3 (144313/393216) (353493/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_541 (fuel : Nat) (hf : 541 < fuel) :
    walk nodes fuel 541 = List.range' 541 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 541).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_542 (fuel : Nat) (hf : 542 < fuel) :
    walk nodes fuel 542 = List.range' 540 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 542).rule = .split 0 (1/5) 540 541 := by rfl
      simp only [walk, hr]
      rw [traversal_540 f (by omega), traversal_541 f (by omega)]
      change (List.range' 540 1 ++ List.range' (540+1) 1) ++
        [540+(1+1)] = List.range' 540 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 540) (n := 1+1)).symm

private theorem traversal_543 (fuel : Nat) (hf : 543 < fuel) :
    walk nodes fuel 543 = List.range' 543 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 543).rule = .bound .vertex 3 (121661/393216) (421449/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_544 (fuel : Nat) (hf : 544 < fuel) :
    walk nodes fuel 544 = List.range' 540 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 544).rule = .split 3 (9/4) 542 543 := by rfl
      simp only [walk, hr]
      rw [traversal_542 f (by omega), traversal_543 f (by omega)]
      change (List.range' 540 3 ++ List.range' (540+3) 1) ++
        [540+(3+1)] = List.range' 540 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 540) (n := 3+1)).symm

private theorem traversal_545 (fuel : Nat) (hf : 545 < fuel) :
    walk nodes fuel 545 = List.range' 519 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 545).rule = .split 2 (15/4) 539 544 := by rfl
      simp only [walk, hr]
      rw [traversal_539 f (by omega), traversal_544 f (by omega)]
      change (List.range' 519 21 ++ List.range' (519+21) 5) ++
        [519+(21+5)] = List.range' 519 ((21+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 519) (n := 21+5)).symm

private theorem traversal_546 (fuel : Nat) (hf : 546 < fuel) :
    walk nodes fuel 546 = List.range' 546 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 546).rule = .bound .vertex 3 (44329/131072) (376145/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_547 (fuel : Nat) (hf : 547 < fuel) :
    walk nodes fuel 547 = List.range' 547 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 547).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_548 (fuel : Nat) (hf : 548 < fuel) :
    walk nodes fuel 548 = List.range' 546 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 548).rule = .split 2 (15/4) 546 547 := by rfl
      simp only [walk, hr]
      rw [traversal_546 f (by omega), traversal_547 f (by omega)]
      change (List.range' 546 1 ++ List.range' (546+1) 1) ++
        [546+(1+1)] = List.range' 546 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 546) (n := 1+1)).symm

private theorem traversal_549 (fuel : Nat) (hf : 549 < fuel) :
    walk nodes fuel 549 = List.range' 519 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 549).rule = .split 1 (5/4) 545 548 := by rfl
      simp only [walk, hr]
      rw [traversal_545 f (by omega), traversal_548 f (by omega)]
      change (List.range' 519 27 ++ List.range' (519+27) 3) ++
        [519+(27+3)] = List.range' 519 ((27+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 519) (n := 27+3)).symm

private theorem traversal_550 (fuel : Nat) (hf : 550 < fuel) :
    walk nodes fuel 550 = List.range' 550 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 550).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_551 (fuel : Nat) (hf : 551 < fuel) :
    walk nodes fuel 551 = List.range' 519 33 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 551).rule = .split 0 (3/10) 549 550 := by rfl
      simp only [walk, hr]
      rw [traversal_549 f (by omega), traversal_550 f (by omega)]
      change (List.range' 519 31 ++ List.range' (519+31) 1) ++
        [519+(31+1)] = List.range' 519 ((31+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 519) (n := 31+1)).symm

private theorem traversal_552 (fuel : Nat) (hf : 552 < fuel) :
    walk nodes fuel 552 = List.range' 496 57 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 552).rule = .split 3 (3/2) 518 551 := by rfl
      simp only [walk, hr]
      rw [traversal_518 f (by omega), traversal_551 f (by omega)]
      change (List.range' 496 23 ++ List.range' (496+23) 33) ++
        [496+(23+33)] = List.range' 496 ((23+33)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 496) (n := 23+33)).symm

private theorem traversal_553 (fuel : Nat) (hf : 553 < fuel) :
    walk nodes fuel 553 = List.range' 423 131 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 553).rule = .split 2 (5/2) 495 552 := by rfl
      simp only [walk, hr]
      rw [traversal_495 f (by omega), traversal_552 f (by omega)]
      change (List.range' 423 73 ++ List.range' (423+73) 57) ++
        [423+(73+57)] = List.range' 423 ((73+57)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 423) (n := 73+57)).symm

private theorem traversal_554 (fuel : Nat) (hf : 554 < fuel) :
    walk nodes fuel 554 = List.range' 554 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 554).rule = .bound .leftEnd 1 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_555 (fuel : Nat) (hf : 555 < fuel) :
    walk nodes fuel 555 = List.range' 555 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 555).rule = .bound .leftEnd 3 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_556 (fuel : Nat) (hf : 556 < fuel) :
    walk nodes fuel 556 = List.range' 554 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 556).rule = .split 2 (5/4) 554 555 := by rfl
      simp only [walk, hr]
      rw [traversal_554 f (by omega), traversal_555 f (by omega)]
      change (List.range' 554 1 ++ List.range' (554+1) 1) ++
        [554+(1+1)] = List.range' 554 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 554) (n := 1+1)).symm

private theorem traversal_557 (fuel : Nat) (hf : 557 < fuel) :
    walk nodes fuel 557 = List.range' 557 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 557).rule = .bound .leftEnd 3 (642119/786432) 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_558 (fuel : Nat) (hf : 558 < fuel) :
    walk nodes fuel 558 = List.range' 554 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 558).rule = .split 1 (15/4) 556 557 := by rfl
      simp only [walk, hr]
      rw [traversal_556 f (by omega), traversal_557 f (by omega)]
      change (List.range' 554 3 ++ List.range' (554+3) 1) ++
        [554+(3+1)] = List.range' 554 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 554) (n := 3+1)).symm

private theorem traversal_559 (fuel : Nat) (hf : 559 < fuel) :
    walk nodes fuel 559 = List.range' 559 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 559).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_560 (fuel : Nat) (hf : 560 < fuel) :
    walk nodes fuel 560 = List.range' 554 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 560).rule = .split 0 (3/10) 558 559 := by rfl
      simp only [walk, hr]
      rw [traversal_558 f (by omega), traversal_559 f (by omega)]
      change (List.range' 554 5 ++ List.range' (554+5) 1) ++
        [554+(5+1)] = List.range' 554 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 554) (n := 5+1)).symm

private theorem traversal_561 (fuel : Nat) (hf : 561 < fuel) :
    walk nodes fuel 561 = List.range' 561 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 561).rule = .bound .leftEnd 1 (44329/131072) (376145/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_562 (fuel : Nat) (hf : 562 < fuel) :
    walk nodes fuel 562 = List.range' 554 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 562).rule = .split 3 (3/2) 560 561 := by rfl
      simp only [walk, hr]
      rw [traversal_560 f (by omega), traversal_561 f (by omega)]
      change (List.range' 554 7 ++ List.range' (554+7) 1) ++
        [554+(7+1)] = List.range' 554 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 554) (n := 7+1)).symm

private theorem traversal_563 (fuel : Nat) (hf : 563 < fuel) :
    walk nodes fuel 563 = List.range' 563 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 563).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_564 (fuel : Nat) (hf : 564 < fuel) :
    walk nodes fuel 564 = List.range' 554 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 564).rule = .split 2 (5/2) 562 563 := by rfl
      simp only [walk, hr]
      rw [traversal_562 f (by omega), traversal_563 f (by omega)]
      change (List.range' 554 9 ++ List.range' (554+9) 1) ++
        [554+(9+1)] = List.range' 554 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 554) (n := 9+1)).symm

private theorem traversal_565 (fuel : Nat) (hf : 565 < fuel) :
    walk nodes fuel 565 = List.range' 423 143 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 565).rule = .split 1 (5/2) 553 564 := by rfl
      simp only [walk, hr]
      rw [traversal_553 f (by omega), traversal_564 f (by omega)]
      change (List.range' 423 131 ++ List.range' (423+131) 11) ++
        [423+(131+11)] = List.range' 423 ((131+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 423) (n := 131+11)).symm

theorem traversal_566 (fuel : Nat) (hf : 566 < fuel) :
    walk nodes fuel 566 = List.range' 0 567 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 566).rule = .split 0 (1/10) 422 565 := by rfl
      simp only [walk, hr]
      rw [traversal_422 f (by omega), traversal_565 f (by omega)]
      change (List.range' 0 423 ++ List.range' (0+423) 143) ++
        [0+(423+143)] = List.range' 0 ((423+143)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 0) (n := 423+143)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
