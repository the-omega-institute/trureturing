/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart09
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart09
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart09.traversal_663,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart09.traversal_668,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart09.traversal_669
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart04
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart05
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart07
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart08
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_605 (fuel : Nat) (hf : 605 < fuel) :
    walk nodes fuel 605 = List.range' 595 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 605).rule = .split 3 (93/32) 595 604 := by rfl
      simp only [walk, hr]
      rw [traversal_595 f (by omega), traversal_604 f (by omega)]
      change (List.range' 595 1 ++ List.range' (595+1) 9) ++
        [595+(1+9)] = List.range' 595 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 595) (n := 1+9)).symm

private theorem traversal_606 (fuel : Nat) (hf : 606 < fuel) :
    walk nodes fuel 606 = List.range' 606 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 606).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_607 (fuel : Nat) (hf : 607 < fuel) :
    walk nodes fuel 607 = List.range' 595 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 607).rule = .split 2 (583/128) 605 606 := by rfl
      simp only [walk, hr]
      rw [traversal_605 f (by omega), traversal_606 f (by omega)]
      change (List.range' 595 11 ++ List.range' (595+11) 1) ++
        [595+(11+1)] = List.range' 595 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 595) (n := 11+1)).symm

private theorem traversal_608 (fuel : Nat) (hf : 608 < fuel) :
    walk nodes fuel 608 = List.range' 488 121 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 608).rule = .split 1 (5/32) 594 607 := by rfl
      simp only [walk, hr]
      rw [traversal_594 f (by omega), traversal_607 f (by omega)]
      change (List.range' 488 107 ++ List.range' (488+107) 13) ++
        [488+(107+13)] = List.range' 488 ((107+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 488) (n := 107+13)).symm

private theorem traversal_609 (fuel : Nat) (hf : 609 < fuel) :
    walk nodes fuel 609 = List.range' 609 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 609).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_610 (fuel : Nat) (hf : 610 < fuel) :
    walk nodes fuel 610 = List.range' 488 123 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 610).rule = .split 0 (1/40) 608 609 := by rfl
      simp only [walk, hr]
      rw [traversal_608 f (by omega), traversal_609 f (by omega)]
      change (List.range' 488 121 ++ List.range' (488+121) 1) ++
        [488+(121+1)] = List.range' 488 ((121+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 488) (n := 121+1)).symm

private theorem traversal_611 (fuel : Nat) (hf : 611 < fuel) :
    walk nodes fuel 611 = List.range' 487 125 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 611).rule = .split 3 (45/16) 487 610 := by rfl
      simp only [walk, hr]
      rw [traversal_487 f (by omega), traversal_610 f (by omega)]
      change (List.range' 487 1 ++ List.range' (487+1) 123) ++
        [487+(1+123)] = List.range' 487 ((1+123)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 487) (n := 1+123)).symm

private theorem traversal_612 (fuel : Nat) (hf : 612 < fuel) :
    walk nodes fuel 612 = List.range' 612 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 612).rule = .bound .rightEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_613 (fuel : Nat) (hf : 613 < fuel) :
    walk nodes fuel 613 = List.range' 487 127 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 613).rule = .split 2 (301/64) 611 612 := by rfl
      simp only [walk, hr]
      rw [traversal_611 f (by omega), traversal_612 f (by omega)]
      change (List.range' 487 125 ++ List.range' (487+125) 1) ++
        [487+(125+1)] = List.range' 487 ((125+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 487) (n := 125+1)).symm

private theorem traversal_614 (fuel : Nat) (hf : 614 < fuel) :
    walk nodes fuel 614 = List.range' 614 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 614).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_615 (fuel : Nat) (hf : 615 < fuel) :
    walk nodes fuel 615 = List.range' 487 129 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 615).rule = .split 1 (5/16) 613 614 := by rfl
      simp only [walk, hr]
      rw [traversal_613 f (by omega), traversal_614 f (by omega)]
      change (List.range' 487 127 ++ List.range' (487+127) 1) ++
        [487+(127+1)] = List.range' 487 ((127+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 487) (n := 127+1)).symm

private theorem traversal_616 (fuel : Nat) (hf : 616 < fuel) :
    walk nodes fuel 616 = List.range' 616 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 616).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_617 (fuel : Nat) (hf : 617 < fuel) :
    walk nodes fuel 617 = List.range' 487 131 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 617).rule = .split 0 (1/20) 615 616 := by rfl
      simp only [walk, hr]
      rw [traversal_615 f (by omega), traversal_616 f (by omega)]
      change (List.range' 487 129 ++ List.range' (487+129) 1) ++
        [487+(129+1)] = List.range' 487 ((129+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 487) (n := 129+1)).symm

private theorem traversal_618 (fuel : Nat) (hf : 618 < fuel) :
    walk nodes fuel 618 = List.range' 486 133 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 618).rule = .split 3 (21/8) 486 617 := by rfl
      simp only [walk, hr]
      rw [traversal_486 f (by omega), traversal_617 f (by omega)]
      change (List.range' 486 1 ++ List.range' (486+1) 131) ++
        [486+(1+131)] = List.range' 486 ((1+131)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 486) (n := 1+131)).symm

private theorem traversal_619 (fuel : Nat) (hf : 619 < fuel) :
    walk nodes fuel 619 = List.range' 393 227 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 619).rule = .split 2 (141/32) 485 618 := by rfl
      simp only [walk, hr]
      rw [traversal_485 f (by omega), traversal_618 f (by omega)]
      change (List.range' 393 93 ++ List.range' (393+93) 133) ++
        [393+(93+133)] = List.range' 393 ((93+133)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 393) (n := 93+133)).symm

private theorem traversal_620 (fuel : Nat) (hf : 620 < fuel) :
    walk nodes fuel 620 = List.range' 620 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 620).rule = .bound .vertex 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_621 (fuel : Nat) (hf : 621 < fuel) :
    walk nodes fuel 621 = List.range' 621 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 621).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_622 (fuel : Nat) (hf : 622 < fuel) :
    walk nodes fuel 622 = List.range' 620 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 622).rule = .split 2 (263/64) 620 621 := by rfl
      simp only [walk, hr]
      rw [traversal_620 f (by omega), traversal_621 f (by omega)]
      change (List.range' 620 1 ++ List.range' (620+1) 1) ++
        [620+(1+1)] = List.range' 620 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 620) (n := 1+1)).symm

private theorem traversal_623 (fuel : Nat) (hf : 623 < fuel) :
    walk nodes fuel 623 = List.range' 623 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 623).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_624 (fuel : Nat) (hf : 624 < fuel) :
    walk nodes fuel 624 = List.range' 620 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 624).rule = .split 1 (15/16) 622 623 := by rfl
      simp only [walk, hr]
      rw [traversal_622 f (by omega), traversal_623 f (by omega)]
      change (List.range' 620 3 ++ List.range' (620+3) 1) ++
        [620+(3+1)] = List.range' 620 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 620) (n := 3+1)).symm

private theorem traversal_625 (fuel : Nat) (hf : 625 < fuel) :
    walk nodes fuel 625 = List.range' 625 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 625).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_626 (fuel : Nat) (hf : 626 < fuel) :
    walk nodes fuel 626 = List.range' 620 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 626).rule = .split 0 (1/20) 624 625 := by rfl
      simp only [walk, hr]
      rw [traversal_624 f (by omega), traversal_625 f (by omega)]
      change (List.range' 620 5 ++ List.range' (620+5) 1) ++
        [620+(5+1)] = List.range' 620 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 620) (n := 5+1)).symm

private theorem traversal_627 (fuel : Nat) (hf : 627 < fuel) :
    walk nodes fuel 627 = List.range' 627 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 627).rule = .bound .vertex 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_628 (fuel : Nat) (hf : 628 < fuel) :
    walk nodes fuel 628 = List.range' 628 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 628).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_629 (fuel : Nat) (hf : 629 < fuel) :
    walk nodes fuel 629 = List.range' 627 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 629).rule = .split 3 (45/16) 627 628 := by rfl
      simp only [walk, hr]
      rw [traversal_627 f (by omega), traversal_628 f (by omega)]
      change (List.range' 627 1 ++ List.range' (627+1) 1) ++
        [627+(1+1)] = List.range' 627 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 627) (n := 1+1)).symm

private theorem traversal_630 (fuel : Nat) (hf : 630 < fuel) :
    walk nodes fuel 630 = List.range' 630 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 630).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_631 (fuel : Nat) (hf : 631 < fuel) :
    walk nodes fuel 631 = List.range' 627 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 631).rule = .split 2 (263/64) 629 630 := by rfl
      simp only [walk, hr]
      rw [traversal_629 f (by omega), traversal_630 f (by omega)]
      change (List.range' 627 3 ++ List.range' (627+3) 1) ++
        [627+(3+1)] = List.range' 627 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 627) (n := 3+1)).symm

private theorem traversal_632 (fuel : Nat) (hf : 632 < fuel) :
    walk nodes fuel 632 = List.range' 632 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 632).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_633 (fuel : Nat) (hf : 633 < fuel) :
    walk nodes fuel 633 = List.range' 627 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 633).rule = .split 1 (15/16) 631 632 := by rfl
      simp only [walk, hr]
      rw [traversal_631 f (by omega), traversal_632 f (by omega)]
      change (List.range' 627 5 ++ List.range' (627+5) 1) ++
        [627+(5+1)] = List.range' 627 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 627) (n := 5+1)).symm

private theorem traversal_634 (fuel : Nat) (hf : 634 < fuel) :
    walk nodes fuel 634 = List.range' 634 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 634).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_635 (fuel : Nat) (hf : 635 < fuel) :
    walk nodes fuel 635 = List.range' 627 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 635).rule = .split 0 (1/20) 633 634 := by rfl
      simp only [walk, hr]
      rw [traversal_633 f (by omega), traversal_634 f (by omega)]
      change (List.range' 627 7 ++ List.range' (627+7) 1) ++
        [627+(7+1)] = List.range' 627 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 627) (n := 7+1)).symm

private theorem traversal_636 (fuel : Nat) (hf : 636 < fuel) :
    walk nodes fuel 636 = List.range' 620 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 636).rule = .split 3 (21/8) 626 635 := by rfl
      simp only [walk, hr]
      rw [traversal_626 f (by omega), traversal_635 f (by omega)]
      change (List.range' 620 7 ++ List.range' (620+7) 9) ++
        [620+(7+9)] = List.range' 620 ((7+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 620) (n := 7+9)).symm

private theorem traversal_637 (fuel : Nat) (hf : 637 < fuel) :
    walk nodes fuel 637 = List.range' 637 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 637).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_638 (fuel : Nat) (hf : 638 < fuel) :
    walk nodes fuel 638 = List.range' 620 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 638).rule = .split 2 (141/32) 636 637 := by rfl
      simp only [walk, hr]
      rw [traversal_636 f (by omega), traversal_637 f (by omega)]
      change (List.range' 620 17 ++ List.range' (620+17) 1) ++
        [620+(17+1)] = List.range' 620 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 620) (n := 17+1)).symm

private theorem traversal_639 (fuel : Nat) (hf : 639 < fuel) :
    walk nodes fuel 639 = List.range' 393 247 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 639).rule = .split 1 (5/8) 619 638 := by rfl
      simp only [walk, hr]
      rw [traversal_619 f (by omega), traversal_638 f (by omega)]
      change (List.range' 393 227 ++ List.range' (393+227) 19) ++
        [393+(227+19)] = List.range' 393 ((227+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 393) (n := 227+19)).symm

private theorem traversal_640 (fuel : Nat) (hf : 640 < fuel) :
    walk nodes fuel 640 = List.range' 380 261 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 640).rule = .split 3 (9/4) 392 639 := by rfl
      simp only [walk, hr]
      rw [traversal_392 f (by omega), traversal_639 f (by omega)]
      change (List.range' 380 13 ++ List.range' (380+13) 247) ++
        [380+(13+247)] = List.range' 380 ((13+247)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 380) (n := 13+247)).symm

private theorem traversal_641 (fuel : Nat) (hf : 641 < fuel) :
    walk nodes fuel 641 = List.range' 367 275 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 641).rule = .split 2 (61/16) 379 640 := by rfl
      simp only [walk, hr]
      rw [traversal_379 f (by omega), traversal_640 f (by omega)]
      change (List.range' 367 13 ++ List.range' (367+13) 261) ++
        [367+(13+261)] = List.range' 367 ((13+261)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 367) (n := 13+261)).symm

private theorem traversal_642 (fuel : Nat) (hf : 642 < fuel) :
    walk nodes fuel 642 = List.range' 642 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 642).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_643 (fuel : Nat) (hf : 643 < fuel) :
    walk nodes fuel 643 = List.range' 643 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 643).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_644 (fuel : Nat) (hf : 644 < fuel) :
    walk nodes fuel 644 = List.range' 644 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 644).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_645 (fuel : Nat) (hf : 645 < fuel) :
    walk nodes fuel 645 = List.range' 643 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 645).rule = .split 1 (25/16) 643 644 := by rfl
      simp only [walk, hr]
      rw [traversal_643 f (by omega), traversal_644 f (by omega)]
      change (List.range' 643 1 ++ List.range' (643+1) 1) ++
        [643+(1+1)] = List.range' 643 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 643) (n := 1+1)).symm

private theorem traversal_646 (fuel : Nat) (hf : 646 < fuel) :
    walk nodes fuel 646 = List.range' 646 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 646).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_647 (fuel : Nat) (hf : 647 < fuel) :
    walk nodes fuel 647 = List.range' 643 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 647).rule = .split 0 (1/20) 645 646 := by rfl
      simp only [walk, hr]
      rw [traversal_645 f (by omega), traversal_646 f (by omega)]
      change (List.range' 643 3 ++ List.range' (643+3) 1) ++
        [643+(3+1)] = List.range' 643 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 643) (n := 3+1)).symm

private theorem traversal_648 (fuel : Nat) (hf : 648 < fuel) :
    walk nodes fuel 648 = List.range' 648 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 648).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_649 (fuel : Nat) (hf : 649 < fuel) :
    walk nodes fuel 649 = List.range' 649 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 649).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_650 (fuel : Nat) (hf : 650 < fuel) :
    walk nodes fuel 650 = List.range' 648 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 650).rule = .split 0 (1/20) 648 649 := by rfl
      simp only [walk, hr]
      rw [traversal_648 f (by omega), traversal_649 f (by omega)]
      change (List.range' 648 1 ++ List.range' (648+1) 1) ++
        [648+(1+1)] = List.range' 648 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 648) (n := 1+1)).symm

private theorem traversal_651 (fuel : Nat) (hf : 651 < fuel) :
    walk nodes fuel 651 = List.range' 643 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 651).rule = .split 3 (15/8) 647 650 := by rfl
      simp only [walk, hr]
      rw [traversal_647 f (by omega), traversal_650 f (by omega)]
      change (List.range' 643 5 ++ List.range' (643+5) 3) ++
        [643+(5+3)] = List.range' 643 ((5+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 643) (n := 5+3)).symm

private theorem traversal_652 (fuel : Nat) (hf : 652 < fuel) :
    walk nodes fuel 652 = List.range' 642 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 652).rule = .split 2 (103/32) 642 651 := by rfl
      simp only [walk, hr]
      rw [traversal_642 f (by omega), traversal_651 f (by omega)]
      change (List.range' 642 1 ++ List.range' (642+1) 9) ++
        [642+(1+9)] = List.range' 642 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 642) (n := 1+9)).symm

private theorem traversal_653 (fuel : Nat) (hf : 653 < fuel) :
    walk nodes fuel 653 = List.range' 653 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 653).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_654 (fuel : Nat) (hf : 654 < fuel) :
    walk nodes fuel 654 = List.range' 654 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 654).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_655 (fuel : Nat) (hf : 655 < fuel) :
    walk nodes fuel 655 = List.range' 653 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 655).rule = .split 2 (103/32) 653 654 := by rfl
      simp only [walk, hr]
      rw [traversal_653 f (by omega), traversal_654 f (by omega)]
      change (List.range' 653 1 ++ List.range' (653+1) 1) ++
        [653+(1+1)] = List.range' 653 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 653) (n := 1+1)).symm

private theorem traversal_656 (fuel : Nat) (hf : 656 < fuel) :
    walk nodes fuel 656 = List.range' 642 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 656).rule = .split 1 (15/8) 652 655 := by rfl
      simp only [walk, hr]
      rw [traversal_652 f (by omega), traversal_655 f (by omega)]
      change (List.range' 642 11 ++ List.range' (642+11) 3) ++
        [642+(11+3)] = List.range' 642 ((11+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 642) (n := 11+3)).symm

private theorem traversal_657 (fuel : Nat) (hf : 657 < fuel) :
    walk nodes fuel 657 = List.range' 657 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 657).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_658 (fuel : Nat) (hf : 658 < fuel) :
    walk nodes fuel 658 = List.range' 642 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 658).rule = .split 3 (9/4) 656 657 := by rfl
      simp only [walk, hr]
      rw [traversal_656 f (by omega), traversal_657 f (by omega)]
      change (List.range' 642 15 ++ List.range' (642+15) 1) ++
        [642+(15+1)] = List.range' 642 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 642) (n := 15+1)).symm

private theorem traversal_659 (fuel : Nat) (hf : 659 < fuel) :
    walk nodes fuel 659 = List.range' 659 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 659).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_660 (fuel : Nat) (hf : 660 < fuel) :
    walk nodes fuel 660 = List.range' 642 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 660).rule = .split 2 (61/16) 658 659 := by rfl
      simp only [walk, hr]
      rw [traversal_658 f (by omega), traversal_659 f (by omega)]
      change (List.range' 642 17 ++ List.range' (642+17) 1) ++
        [642+(17+1)] = List.range' 642 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 642) (n := 17+1)).symm

private theorem traversal_661 (fuel : Nat) (hf : 661 < fuel) :
    walk nodes fuel 661 = List.range' 367 295 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 661).rule = .split 1 (5/4) 641 660 := by rfl
      simp only [walk, hr]
      rw [traversal_641 f (by omega), traversal_660 f (by omega)]
      change (List.range' 367 275 ++ List.range' (367+275) 19) ++
        [367+(275+19)] = List.range' 367 ((275+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 367) (n := 275+19)).symm

private theorem traversal_662 (fuel : Nat) (hf : 662 < fuel) :
    walk nodes fuel 662 = List.range' 284 379 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 662).rule = .split 3 (3/2) 366 661 := by rfl
      simp only [walk, hr]
      rw [traversal_366 f (by omega), traversal_661 f (by omega)]
      change (List.range' 284 83 ++ List.range' (284+83) 295) ++
        [284+(83+295)] = List.range' 284 ((83+295)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 284) (n := 83+295)).symm

theorem traversal_663 (fuel : Nat) (hf : 663 < fuel) :
    walk nodes fuel 663 = List.range' 1 663 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 663).rule = .split 2 (21/8) 283 662 := by rfl
      simp only [walk, hr]
      rw [traversal_283 f (by omega), traversal_662 f (by omega)]
      change (List.range' 1 283 ++ List.range' (1+283) 379) ++
        [1+(283+379)] = List.range' 1 ((283+379)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1) (n := 283+379)).symm

private theorem traversal_664 (fuel : Nat) (hf : 664 < fuel) :
    walk nodes fuel 664 = List.range' 664 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 664).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_665 (fuel : Nat) (hf : 665 < fuel) :
    walk nodes fuel 665 = List.range' 665 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 665).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_666 (fuel : Nat) (hf : 666 < fuel) :
    walk nodes fuel 666 = List.range' 664 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 666).rule = .split 3 (3/16) 664 665 := by rfl
      simp only [walk, hr]
      rw [traversal_664 f (by omega), traversal_665 f (by omega)]
      change (List.range' 664 1 ++ List.range' (664+1) 1) ++
        [664+(1+1)] = List.range' 664 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 1+1)).symm

private theorem traversal_667 (fuel : Nat) (hf : 667 < fuel) :
    walk nodes fuel 667 = List.range' 667 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 667).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_668 (fuel : Nat) (hf : 668 < fuel) :
    walk nodes fuel 668 = List.range' 664 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 668).rule = .split 2 (35/64) 666 667 := by rfl
      simp only [walk, hr]
      rw [traversal_666 f (by omega), traversal_667 f (by omega)]
      change (List.range' 664 3 ++ List.range' (664+3) 1) ++
        [664+(3+1)] = List.range' 664 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 3+1)).symm

theorem traversal_669 (fuel : Nat) (hf : 669 < fuel) :
    walk nodes fuel 669 = List.range' 669 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 669).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
