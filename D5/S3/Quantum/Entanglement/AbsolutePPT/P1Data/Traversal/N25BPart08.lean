/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart08
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart08
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart08.traversal_594,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart08.traversal_595,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart08.traversal_604
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart07
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_538 (fuel : Nat) (hf : 538 < fuel) :
    walk nodes fuel 538 = List.range' 538 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 538).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_539 (fuel : Nat) (hf : 539 < fuel) :
    walk nodes fuel 539 = List.range' 539 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 539).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_540 (fuel : Nat) (hf : 540 < fuel) :
    walk nodes fuel 540 = List.range' 540 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 540).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_541 (fuel : Nat) (hf : 541 < fuel) :
    walk nodes fuel 541 = List.range' 541 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 541).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_542 (fuel : Nat) (hf : 542 < fuel) :
    walk nodes fuel 542 = List.range' 540 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 542).rule = .split 3 (381/128) 540 541 := by rfl
      simp only [walk, hr]
      rw [traversal_540 f (by omega), traversal_541 f (by omega)]
      change (List.range' 540 1 ++ List.range' (540+1) 1) ++
        [540+(1+1)] = List.range' 540 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 540) (n := 1+1)).symm

private theorem traversal_543 (fuel : Nat) (hf : 543 < fuel) :
    walk nodes fuel 543 = List.range' 539 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 543).rule = .split 2 (2275/512) 539 542 := by rfl
      simp only [walk, hr]
      rw [traversal_539 f (by omega), traversal_542 f (by omega)]
      change (List.range' 539 1 ++ List.range' (539+1) 3) ++
        [539+(1+3)] = List.range' 539 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 539) (n := 1+3)).symm

private theorem traversal_544 (fuel : Nat) (hf : 544 < fuel) :
    walk nodes fuel 544 = List.range' 544 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 544).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_545 (fuel : Nat) (hf : 545 < fuel) :
    walk nodes fuel 545 = List.range' 545 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 545).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_546 (fuel : Nat) (hf : 546 < fuel) :
    walk nodes fuel 546 = List.range' 546 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 546).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_547 (fuel : Nat) (hf : 547 < fuel) :
    walk nodes fuel 547 = List.range' 545 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 547).rule = .split 3 (381/128) 545 546 := by rfl
      simp only [walk, hr]
      rw [traversal_545 f (by omega), traversal_546 f (by omega)]
      change (List.range' 545 1 ++ List.range' (545+1) 1) ++
        [545+(1+1)] = List.range' 545 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 545) (n := 1+1)).symm

private theorem traversal_548 (fuel : Nat) (hf : 548 < fuel) :
    walk nodes fuel 548 = List.range' 544 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 548).rule = .split 2 (2275/512) 544 547 := by rfl
      simp only [walk, hr]
      rw [traversal_544 f (by omega), traversal_547 f (by omega)]
      change (List.range' 544 1 ++ List.range' (544+1) 3) ++
        [544+(1+3)] = List.range' 544 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 544) (n := 1+3)).symm

private theorem traversal_549 (fuel : Nat) (hf : 549 < fuel) :
    walk nodes fuel 549 = List.range' 539 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 549).rule = .split 1 (15/128) 543 548 := by rfl
      simp only [walk, hr]
      rw [traversal_543 f (by omega), traversal_548 f (by omega)]
      change (List.range' 539 5 ++ List.range' (539+5) 5) ++
        [539+(5+5)] = List.range' 539 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 539) (n := 5+5)).symm

private theorem traversal_550 (fuel : Nat) (hf : 550 < fuel) :
    walk nodes fuel 550 = List.range' 550 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 550).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_551 (fuel : Nat) (hf : 551 < fuel) :
    walk nodes fuel 551 = List.range' 551 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 551).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_552 (fuel : Nat) (hf : 552 < fuel) :
    walk nodes fuel 552 = List.range' 550 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 552).rule = .split 2 (2275/512) 550 551 := by rfl
      simp only [walk, hr]
      rw [traversal_550 f (by omega), traversal_551 f (by omega)]
      change (List.range' 550 1 ++ List.range' (550+1) 1) ++
        [550+(1+1)] = List.range' 550 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 550) (n := 1+1)).symm

private theorem traversal_553 (fuel : Nat) (hf : 553 < fuel) :
    walk nodes fuel 553 = List.range' 553 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 553).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_554 (fuel : Nat) (hf : 554 < fuel) :
    walk nodes fuel 554 = List.range' 550 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 554).rule = .split 1 (15/128) 552 553 := by rfl
      simp only [walk, hr]
      rw [traversal_552 f (by omega), traversal_553 f (by omega)]
      change (List.range' 550 3 ++ List.range' (550+3) 1) ++
        [550+(3+1)] = List.range' 550 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 550) (n := 3+1)).symm

private theorem traversal_555 (fuel : Nat) (hf : 555 < fuel) :
    walk nodes fuel 555 = List.range' 539 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 555).rule = .split 0 (1/160) 549 554 := by rfl
      simp only [walk, hr]
      rw [traversal_549 f (by omega), traversal_554 f (by omega)]
      change (List.range' 539 11 ++ List.range' (539+11) 5) ++
        [539+(11+5)] = List.range' 539 ((11+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 539) (n := 11+5)).symm

private theorem traversal_556 (fuel : Nat) (hf : 556 < fuel) :
    walk nodes fuel 556 = List.range' 538 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 556).rule = .split 3 (189/64) 538 555 := by rfl
      simp only [walk, hr]
      rw [traversal_538 f (by omega), traversal_555 f (by omega)]
      change (List.range' 538 1 ++ List.range' (538+1) 17) ++
        [538+(1+17)] = List.range' 538 ((1+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 538) (n := 1+17)).symm

private theorem traversal_557 (fuel : Nat) (hf : 557 < fuel) :
    walk nodes fuel 557 = List.range' 557 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 557).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_558 (fuel : Nat) (hf : 558 < fuel) :
    walk nodes fuel 558 = List.range' 558 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 558).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_559 (fuel : Nat) (hf : 559 < fuel) :
    walk nodes fuel 559 = List.range' 559 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 559).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_560 (fuel : Nat) (hf : 560 < fuel) :
    walk nodes fuel 560 = List.range' 560 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 560).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_561 (fuel : Nat) (hf : 561 < fuel) :
    walk nodes fuel 561 = List.range' 559 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 561).rule = .split 0 (1/320) 559 560 := by rfl
      simp only [walk, hr]
      rw [traversal_559 f (by omega), traversal_560 f (by omega)]
      change (List.range' 559 1 ++ List.range' (559+1) 1) ++
        [559+(1+1)] = List.range' 559 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 559) (n := 1+1)).symm

private theorem traversal_562 (fuel : Nat) (hf : 562 < fuel) :
    walk nodes fuel 562 = List.range' 558 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 562).rule = .split 3 (381/128) 558 561 := by rfl
      simp only [walk, hr]
      rw [traversal_558 f (by omega), traversal_561 f (by omega)]
      change (List.range' 558 1 ++ List.range' (558+1) 3) ++
        [558+(1+3)] = List.range' 558 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 558) (n := 1+3)).symm

private theorem traversal_563 (fuel : Nat) (hf : 563 < fuel) :
    walk nodes fuel 563 = List.range' 563 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 563).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_564 (fuel : Nat) (hf : 564 < fuel) :
    walk nodes fuel 564 = List.range' 558 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 564).rule = .split 2 (2313/512) 562 563 := by rfl
      simp only [walk, hr]
      rw [traversal_562 f (by omega), traversal_563 f (by omega)]
      change (List.range' 558 5 ++ List.range' (558+5) 1) ++
        [558+(5+1)] = List.range' 558 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 558) (n := 5+1)).symm

private theorem traversal_565 (fuel : Nat) (hf : 565 < fuel) :
    walk nodes fuel 565 = List.range' 565 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 565).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_566 (fuel : Nat) (hf : 566 < fuel) :
    walk nodes fuel 566 = List.range' 558 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 566).rule = .split 1 (15/128) 564 565 := by rfl
      simp only [walk, hr]
      rw [traversal_564 f (by omega), traversal_565 f (by omega)]
      change (List.range' 558 7 ++ List.range' (558+7) 1) ++
        [558+(7+1)] = List.range' 558 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 558) (n := 7+1)).symm

private theorem traversal_567 (fuel : Nat) (hf : 567 < fuel) :
    walk nodes fuel 567 = List.range' 567 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 567).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_568 (fuel : Nat) (hf : 568 < fuel) :
    walk nodes fuel 568 = List.range' 558 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 568).rule = .split 0 (1/160) 566 567 := by rfl
      simp only [walk, hr]
      rw [traversal_566 f (by omega), traversal_567 f (by omega)]
      change (List.range' 558 9 ++ List.range' (558+9) 1) ++
        [558+(9+1)] = List.range' 558 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 558) (n := 9+1)).symm

private theorem traversal_569 (fuel : Nat) (hf : 569 < fuel) :
    walk nodes fuel 569 = List.range' 557 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 569).rule = .split 3 (189/64) 557 568 := by rfl
      simp only [walk, hr]
      rw [traversal_557 f (by omega), traversal_568 f (by omega)]
      change (List.range' 557 1 ++ List.range' (557+1) 11) ++
        [557+(1+11)] = List.range' 557 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 557) (n := 1+11)).symm

private theorem traversal_570 (fuel : Nat) (hf : 570 < fuel) :
    walk nodes fuel 570 = List.range' 538 33 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 570).rule = .split 2 (1147/256) 556 569 := by rfl
      simp only [walk, hr]
      rw [traversal_556 f (by omega), traversal_569 f (by omega)]
      change (List.range' 538 19 ++ List.range' (538+19) 13) ++
        [538+(19+13)] = List.range' 538 ((19+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 538) (n := 19+13)).symm

private theorem traversal_571 (fuel : Nat) (hf : 571 < fuel) :
    walk nodes fuel 571 = List.range' 489 83 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 571).rule = .split 1 (5/64) 537 570 := by rfl
      simp only [walk, hr]
      rw [traversal_537 f (by omega), traversal_570 f (by omega)]
      change (List.range' 489 49 ++ List.range' (489+49) 33) ++
        [489+(49+33)] = List.range' 489 ((49+33)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 489) (n := 49+33)).symm

private theorem traversal_572 (fuel : Nat) (hf : 572 < fuel) :
    walk nodes fuel 572 = List.range' 572 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 572).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_573 (fuel : Nat) (hf : 573 < fuel) :
    walk nodes fuel 573 = List.range' 573 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 573).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_574 (fuel : Nat) (hf : 574 < fuel) :
    walk nodes fuel 574 = List.range' 574 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 574).rule = .bound .rightEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_575 (fuel : Nat) (hf : 575 < fuel) :
    walk nodes fuel 575 = List.range' 573 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 575).rule = .split 2 (2275/512) 573 574 := by rfl
      simp only [walk, hr]
      rw [traversal_573 f (by omega), traversal_574 f (by omega)]
      change (List.range' 573 1 ++ List.range' (573+1) 1) ++
        [573+(1+1)] = List.range' 573 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 573) (n := 1+1)).symm

private theorem traversal_576 (fuel : Nat) (hf : 576 < fuel) :
    walk nodes fuel 576 = List.range' 576 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 576).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_577 (fuel : Nat) (hf : 577 < fuel) :
    walk nodes fuel 577 = List.range' 573 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 577).rule = .split 1 (5/128) 575 576 := by rfl
      simp only [walk, hr]
      rw [traversal_575 f (by omega), traversal_576 f (by omega)]
      change (List.range' 573 3 ++ List.range' (573+3) 1) ++
        [573+(3+1)] = List.range' 573 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 573) (n := 3+1)).symm

private theorem traversal_578 (fuel : Nat) (hf : 578 < fuel) :
    walk nodes fuel 578 = List.range' 578 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 578).rule = .infeasible 4 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_579 (fuel : Nat) (hf : 579 < fuel) :
    walk nodes fuel 579 = List.range' 573 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 579).rule = .split 0 (3/160) 577 578 := by rfl
      simp only [walk, hr]
      rw [traversal_577 f (by omega), traversal_578 f (by omega)]
      change (List.range' 573 5 ++ List.range' (573+5) 1) ++
        [573+(5+1)] = List.range' 573 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 573) (n := 5+1)).symm

private theorem traversal_580 (fuel : Nat) (hf : 580 < fuel) :
    walk nodes fuel 580 = List.range' 572 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 580).rule = .split 3 (189/64) 572 579 := by rfl
      simp only [walk, hr]
      rw [traversal_572 f (by omega), traversal_579 f (by omega)]
      change (List.range' 572 1 ++ List.range' (572+1) 7) ++
        [572+(1+7)] = List.range' 572 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 572) (n := 1+7)).symm

private theorem traversal_581 (fuel : Nat) (hf : 581 < fuel) :
    walk nodes fuel 581 = List.range' 581 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 581).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_582 (fuel : Nat) (hf : 582 < fuel) :
    walk nodes fuel 582 = List.range' 572 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 582).rule = .split 2 (1147/256) 580 581 := by rfl
      simp only [walk, hr]
      rw [traversal_580 f (by omega), traversal_581 f (by omega)]
      change (List.range' 572 9 ++ List.range' (572+9) 1) ++
        [572+(9+1)] = List.range' 572 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 572) (n := 9+1)).symm

private theorem traversal_583 (fuel : Nat) (hf : 583 < fuel) :
    walk nodes fuel 583 = List.range' 583 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 583).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_584 (fuel : Nat) (hf : 584 < fuel) :
    walk nodes fuel 584 = List.range' 572 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 584).rule = .split 1 (5/64) 582 583 := by rfl
      simp only [walk, hr]
      rw [traversal_582 f (by omega), traversal_583 f (by omega)]
      change (List.range' 572 11 ++ List.range' (572+11) 1) ++
        [572+(11+1)] = List.range' 572 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 572) (n := 11+1)).symm

private theorem traversal_585 (fuel : Nat) (hf : 585 < fuel) :
    walk nodes fuel 585 = List.range' 489 97 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 585).rule = .split 0 (1/80) 571 584 := by rfl
      simp only [walk, hr]
      rw [traversal_571 f (by omega), traversal_584 f (by omega)]
      change (List.range' 489 83 ++ List.range' (489+83) 13) ++
        [489+(83+13)] = List.range' 489 ((83+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 489) (n := 83+13)).symm

private theorem traversal_586 (fuel : Nat) (hf : 586 < fuel) :
    walk nodes fuel 586 = List.range' 488 99 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 586).rule = .split 3 (93/32) 488 585 := by rfl
      simp only [walk, hr]
      rw [traversal_488 f (by omega), traversal_585 f (by omega)]
      change (List.range' 488 1 ++ List.range' (488+1) 97) ++
        [488+(1+97)] = List.range' 488 ((1+97)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 488) (n := 1+97)).symm

private theorem traversal_587 (fuel : Nat) (hf : 587 < fuel) :
    walk nodes fuel 587 = List.range' 587 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 587).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_588 (fuel : Nat) (hf : 588 < fuel) :
    walk nodes fuel 588 = List.range' 588 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 588).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_589 (fuel : Nat) (hf : 589 < fuel) :
    walk nodes fuel 589 = List.range' 589 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 589).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_590 (fuel : Nat) (hf : 590 < fuel) :
    walk nodes fuel 590 = List.range' 588 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 590).rule = .split 1 (5/64) 588 589 := by rfl
      simp only [walk, hr]
      rw [traversal_588 f (by omega), traversal_589 f (by omega)]
      change (List.range' 588 1 ++ List.range' (588+1) 1) ++
        [588+(1+1)] = List.range' 588 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 588) (n := 1+1)).symm

private theorem traversal_591 (fuel : Nat) (hf : 591 < fuel) :
    walk nodes fuel 591 = List.range' 591 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 591).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_592 (fuel : Nat) (hf : 592 < fuel) :
    walk nodes fuel 592 = List.range' 588 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 592).rule = .split 0 (1/80) 590 591 := by rfl
      simp only [walk, hr]
      rw [traversal_590 f (by omega), traversal_591 f (by omega)]
      change (List.range' 588 3 ++ List.range' (588+3) 1) ++
        [588+(3+1)] = List.range' 588 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 588) (n := 3+1)).symm

private theorem traversal_593 (fuel : Nat) (hf : 593 < fuel) :
    walk nodes fuel 593 = List.range' 587 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 593).rule = .split 3 (93/32) 587 592 := by rfl
      simp only [walk, hr]
      rw [traversal_587 f (by omega), traversal_592 f (by omega)]
      change (List.range' 587 1 ++ List.range' (587+1) 5) ++
        [587+(1+5)] = List.range' 587 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 587) (n := 1+5)).symm

theorem traversal_594 (fuel : Nat) (hf : 594 < fuel) :
    walk nodes fuel 594 = List.range' 488 107 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 594).rule = .split 2 (583/128) 586 593 := by rfl
      simp only [walk, hr]
      rw [traversal_586 f (by omega), traversal_593 f (by omega)]
      change (List.range' 488 99 ++ List.range' (488+99) 7) ++
        [488+(99+7)] = List.range' 488 ((99+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 488) (n := 99+7)).symm

theorem traversal_595 (fuel : Nat) (hf : 595 < fuel) :
    walk nodes fuel 595 = List.range' 595 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 595).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_596 (fuel : Nat) (hf : 596 < fuel) :
    walk nodes fuel 596 = List.range' 596 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 596).rule = .bound .rightEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_597 (fuel : Nat) (hf : 597 < fuel) :
    walk nodes fuel 597 = List.range' 597 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 597).rule = .bound .rightEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_598 (fuel : Nat) (hf : 598 < fuel) :
    walk nodes fuel 598 = List.range' 596 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 598).rule = .split 3 (189/64) 596 597 := by rfl
      simp only [walk, hr]
      rw [traversal_596 f (by omega), traversal_597 f (by omega)]
      change (List.range' 596 1 ++ List.range' (596+1) 1) ++
        [596+(1+1)] = List.range' 596 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 596) (n := 1+1)).symm

private theorem traversal_599 (fuel : Nat) (hf : 599 < fuel) :
    walk nodes fuel 599 = List.range' 599 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 599).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_600 (fuel : Nat) (hf : 600 < fuel) :
    walk nodes fuel 600 = List.range' 596 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 600).rule = .split 2 (1147/256) 598 599 := by rfl
      simp only [walk, hr]
      rw [traversal_598 f (by omega), traversal_599 f (by omega)]
      change (List.range' 596 3 ++ List.range' (596+3) 1) ++
        [596+(3+1)] = List.range' 596 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 596) (n := 3+1)).symm

private theorem traversal_601 (fuel : Nat) (hf : 601 < fuel) :
    walk nodes fuel 601 = List.range' 601 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 601).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_602 (fuel : Nat) (hf : 602 < fuel) :
    walk nodes fuel 602 = List.range' 596 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 602).rule = .split 1 (15/64) 600 601 := by rfl
      simp only [walk, hr]
      rw [traversal_600 f (by omega), traversal_601 f (by omega)]
      change (List.range' 596 5 ++ List.range' (596+5) 1) ++
        [596+(5+1)] = List.range' 596 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 596) (n := 5+1)).symm

private theorem traversal_603 (fuel : Nat) (hf : 603 < fuel) :
    walk nodes fuel 603 = List.range' 603 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 603).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_604 (fuel : Nat) (hf : 604 < fuel) :
    walk nodes fuel 604 = List.range' 596 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 604).rule = .split 0 (1/80) 602 603 := by rfl
      simp only [walk, hr]
      rw [traversal_602 f (by omega), traversal_603 f (by omega)]
      change (List.range' 596 7 ++ List.range' (596+7) 1) ++
        [596+(7+1)] = List.range' 596 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 596) (n := 7+1)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
