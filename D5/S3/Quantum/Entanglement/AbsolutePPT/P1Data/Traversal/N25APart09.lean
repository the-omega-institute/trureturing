/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart09
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart09
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart09.traversal_670,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart09.traversal_671
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart08
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_605 (fuel : Nat) (hf : 605 < fuel) :
    walk nodes fuel 605 = List.range' 605 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 605).rule = .bound .leftEnd 2 (3293/6144) (122275/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_606 (fuel : Nat) (hf : 606 < fuel) :
    walk nodes fuel 606 = List.range' 606 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 606).rule = .bound .leftEnd 8 (3283/6144) (245295/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_607 (fuel : Nat) (hf : 607 < fuel) :
    walk nodes fuel 607 = List.range' 607 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 607).rule = .bound .leftEnd 1 (3283/6144) (245295/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_608 (fuel : Nat) (hf : 608 < fuel) :
    walk nodes fuel 608 = List.range' 608 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 608).rule = .bound .leftEnd 2 (3283/6144) (245295/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_609 (fuel : Nat) (hf : 609 < fuel) :
    walk nodes fuel 609 = List.range' 607 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 609).rule = .split 2 (8985/4096) 607 608 := by rfl
      simp only [walk, hr]
      rw [traversal_607 f (by omega), traversal_608 f (by omega)]
      change (List.range' 607 1 ++ List.range' (607+1) 1) ++
        [607+(1+1)] = List.range' 607 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 607) (n := 1+1)).symm

private theorem traversal_610 (fuel : Nat) (hf : 610 < fuel) :
    walk nodes fuel 610 = List.range' 606 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 610).rule = .split 1 (2345/1024) 606 609 := by rfl
      simp only [walk, hr]
      rw [traversal_606 f (by omega), traversal_609 f (by omega)]
      change (List.range' 606 1 ++ List.range' (606+1) 3) ++
        [606+(1+3)] = List.range' 606 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 606) (n := 1+3)).symm

private theorem traversal_611 (fuel : Nat) (hf : 611 < fuel) :
    walk nodes fuel 611 = List.range' 611 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 611).rule = .bound .leftEnd 1 (3283/6144) (245295/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_612 (fuel : Nat) (hf : 612 < fuel) :
    walk nodes fuel 612 = List.range' 606 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 612).rule = .split 0 (1/1280) 610 611 := by rfl
      simp only [walk, hr]
      rw [traversal_610 f (by omega), traversal_611 f (by omega)]
      change (List.range' 606 5 ++ List.range' (606+5) 1) ++
        [606+(5+1)] = List.range' 606 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 606) (n := 5+1)).symm

private theorem traversal_613 (fuel : Nat) (hf : 613 < fuel) :
    walk nodes fuel 613 = List.range' 605 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 613).rule = .split 3 (447/512) 605 612 := by rfl
      simp only [walk, hr]
      rw [traversal_605 f (by omega), traversal_612 f (by omega)]
      change (List.range' 605 1 ++ List.range' (605+1) 7) ++
        [605+(1+7)] = List.range' 605 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 605) (n := 1+7)).symm

private theorem traversal_614 (fuel : Nat) (hf : 614 < fuel) :
    walk nodes fuel 614 = List.range' 604 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 614).rule = .split 2 (4483/2048) 604 613 := by rfl
      simp only [walk, hr]
      rw [traversal_604 f (by omega), traversal_613 f (by omega)]
      change (List.range' 604 1 ++ List.range' (604+1) 9) ++
        [604+(1+9)] = List.range' 604 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 604) (n := 1+9)).symm

private theorem traversal_615 (fuel : Nat) (hf : 615 < fuel) :
    walk nodes fuel 615 = List.range' 615 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 615).rule = .bound .leftEnd 2 (3293/6144) (122275/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_616 (fuel : Nat) (hf : 616 < fuel) :
    walk nodes fuel 616 = List.range' 616 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 616).rule = .bound .leftEnd 1 (3283/6144) (245295/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_617 (fuel : Nat) (hf : 617 < fuel) :
    walk nodes fuel 617 = List.range' 615 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 617).rule = .split 3 (447/512) 615 616 := by rfl
      simp only [walk, hr]
      rw [traversal_615 f (by omega), traversal_616 f (by omega)]
      change (List.range' 615 1 ++ List.range' (615+1) 1) ++
        [615+(1+1)] = List.range' 615 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 615) (n := 1+1)).symm

private theorem traversal_618 (fuel : Nat) (hf : 618 < fuel) :
    walk nodes fuel 618 = List.range' 618 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 618).rule = .bound .leftEnd 2 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_619 (fuel : Nat) (hf : 619 < fuel) :
    walk nodes fuel 619 = List.range' 615 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 619).rule = .split 2 (4483/2048) 617 618 := by rfl
      simp only [walk, hr]
      rw [traversal_617 f (by omega), traversal_618 f (by omega)]
      change (List.range' 615 3 ++ List.range' (615+3) 1) ++
        [615+(3+1)] = List.range' 615 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 615) (n := 3+1)).symm

private theorem traversal_620 (fuel : Nat) (hf : 620 < fuel) :
    walk nodes fuel 620 = List.range' 604 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 620).rule = .split 1 (1175/512) 614 619 := by rfl
      simp only [walk, hr]
      rw [traversal_614 f (by omega), traversal_619 f (by omega)]
      change (List.range' 604 11 ++ List.range' (604+11) 5) ++
        [604+(11+5)] = List.range' 604 ((11+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 604) (n := 11+5)).symm

private theorem traversal_621 (fuel : Nat) (hf : 621 < fuel) :
    walk nodes fuel 621 = List.range' 621 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 621).rule = .bound .leftEnd 1 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_622 (fuel : Nat) (hf : 622 < fuel) :
    walk nodes fuel 622 = List.range' 622 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 622).rule = .bound .leftEnd 2 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_623 (fuel : Nat) (hf : 623 < fuel) :
    walk nodes fuel 623 = List.range' 621 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 623).rule = .split 2 (4483/2048) 621 622 := by rfl
      simp only [walk, hr]
      rw [traversal_621 f (by omega), traversal_622 f (by omega)]
      change (List.range' 621 1 ++ List.range' (621+1) 1) ++
        [621+(1+1)] = List.range' 621 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 621) (n := 1+1)).symm

private theorem traversal_624 (fuel : Nat) (hf : 624 < fuel) :
    walk nodes fuel 624 = List.range' 624 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 624).rule = .bound .leftEnd 1 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_625 (fuel : Nat) (hf : 625 < fuel) :
    walk nodes fuel 625 = List.range' 621 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 625).rule = .split 1 (1175/512) 623 624 := by rfl
      simp only [walk, hr]
      rw [traversal_623 f (by omega), traversal_624 f (by omega)]
      change (List.range' 621 3 ++ List.range' (621+3) 1) ++
        [621+(3+1)] = List.range' 621 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 621) (n := 3+1)).symm

private theorem traversal_626 (fuel : Nat) (hf : 626 < fuel) :
    walk nodes fuel 626 = List.range' 604 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 626).rule = .split 0 (1/640) 620 625 := by rfl
      simp only [walk, hr]
      rw [traversal_620 f (by omega), traversal_625 f (by omega)]
      change (List.range' 604 17 ++ List.range' (604+17) 5) ++
        [604+(17+5)] = List.range' 604 ((17+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 604) (n := 17+5)).symm

private theorem traversal_627 (fuel : Nat) (hf : 627 < fuel) :
    walk nodes fuel 627 = List.range' 627 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 627).rule = .bound .leftEnd 1 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_628 (fuel : Nat) (hf : 628 < fuel) :
    walk nodes fuel 628 = List.range' 604 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 628).rule = .split 3 (225/256) 626 627 := by rfl
      simp only [walk, hr]
      rw [traversal_626 f (by omega), traversal_627 f (by omega)]
      change (List.range' 604 23 ++ List.range' (604+23) 1) ++
        [604+(23+1)] = List.range' 604 ((23+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 604) (n := 23+1)).symm

private theorem traversal_629 (fuel : Nat) (hf : 629 < fuel) :
    walk nodes fuel 629 = List.range' 629 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 629).rule = .bound .leftEnd 2 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_630 (fuel : Nat) (hf : 630 < fuel) :
    walk nodes fuel 630 = List.range' 630 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 630).rule = .bound .leftEnd 8 (3271/6144) (246195/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_631 (fuel : Nat) (hf : 631 < fuel) :
    walk nodes fuel 631 = List.range' 631 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 631).rule = .bound .leftEnd 1 (3271/6144) (246195/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_632 (fuel : Nat) (hf : 632 < fuel) :
    walk nodes fuel 632 = List.range' 630 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 632).rule = .split 1 (2345/1024) 630 631 := by rfl
      simp only [walk, hr]
      rw [traversal_630 f (by omega), traversal_631 f (by omega)]
      change (List.range' 630 1 ++ List.range' (630+1) 1) ++
        [630+(1+1)] = List.range' 630 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 630) (n := 1+1)).symm

private theorem traversal_633 (fuel : Nat) (hf : 633 < fuel) :
    walk nodes fuel 633 = List.range' 633 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 633).rule = .bound .leftEnd 1 (3271/6144) (246195/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_634 (fuel : Nat) (hf : 634 < fuel) :
    walk nodes fuel 634 = List.range' 630 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 634).rule = .split 0 (1/1280) 632 633 := by rfl
      simp only [walk, hr]
      rw [traversal_632 f (by omega), traversal_633 f (by omega)]
      change (List.range' 630 3 ++ List.range' (630+3) 1) ++
        [630+(3+1)] = List.range' 630 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 630) (n := 3+1)).symm

private theorem traversal_635 (fuel : Nat) (hf : 635 < fuel) :
    walk nodes fuel 635 = List.range' 635 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 635).rule = .bound .leftEnd 1 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_636 (fuel : Nat) (hf : 636 < fuel) :
    walk nodes fuel 636 = List.range' 630 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 636).rule = .split 3 (453/512) 634 635 := by rfl
      simp only [walk, hr]
      rw [traversal_634 f (by omega), traversal_635 f (by omega)]
      change (List.range' 630 5 ++ List.range' (630+5) 1) ++
        [630+(5+1)] = List.range' 630 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 630) (n := 5+1)).symm

private theorem traversal_637 (fuel : Nat) (hf : 637 < fuel) :
    walk nodes fuel 637 = List.range' 637 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 637).rule = .bound .leftEnd 8 (3271/6144) (246195/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_638 (fuel : Nat) (hf : 638 < fuel) :
    walk nodes fuel 638 = List.range' 638 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 638).rule = .bound .leftEnd 2 (3271/6144) (246195/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_639 (fuel : Nat) (hf : 639 < fuel) :
    walk nodes fuel 639 = List.range' 637 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 639).rule = .split 2 (9061/4096) 637 638 := by rfl
      simp only [walk, hr]
      rw [traversal_637 f (by omega), traversal_638 f (by omega)]
      change (List.range' 637 1 ++ List.range' (637+1) 1) ++
        [637+(1+1)] = List.range' 637 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 637) (n := 1+1)).symm

private theorem traversal_640 (fuel : Nat) (hf : 640 < fuel) :
    walk nodes fuel 640 = List.range' 640 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 640).rule = .bound .leftEnd 2 (3271/6144) (246195/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_641 (fuel : Nat) (hf : 641 < fuel) :
    walk nodes fuel 641 = List.range' 637 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 641).rule = .split 1 (2345/1024) 639 640 := by rfl
      simp only [walk, hr]
      rw [traversal_639 f (by omega), traversal_640 f (by omega)]
      change (List.range' 637 3 ++ List.range' (637+3) 1) ++
        [637+(3+1)] = List.range' 637 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 637) (n := 3+1)).symm

private theorem traversal_642 (fuel : Nat) (hf : 642 < fuel) :
    walk nodes fuel 642 = List.range' 642 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 642).rule = .bound .leftEnd 2 (3271/6144) (246195/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_643 (fuel : Nat) (hf : 643 < fuel) :
    walk nodes fuel 643 = List.range' 637 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 643).rule = .split 0 (1/1280) 641 642 := by rfl
      simp only [walk, hr]
      rw [traversal_641 f (by omega), traversal_642 f (by omega)]
      change (List.range' 637 5 ++ List.range' (637+5) 1) ++
        [637+(5+1)] = List.range' 637 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 637) (n := 5+1)).symm

private theorem traversal_644 (fuel : Nat) (hf : 644 < fuel) :
    walk nodes fuel 644 = List.range' 644 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 644).rule = .bound .leftEnd 8 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_645 (fuel : Nat) (hf : 645 < fuel) :
    walk nodes fuel 645 = List.range' 645 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 645).rule = .bound .leftEnd 1 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_646 (fuel : Nat) (hf : 646 < fuel) :
    walk nodes fuel 646 = List.range' 644 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 646).rule = .split 1 (2345/1024) 644 645 := by rfl
      simp only [walk, hr]
      rw [traversal_644 f (by omega), traversal_645 f (by omega)]
      change (List.range' 644 1 ++ List.range' (644+1) 1) ++
        [644+(1+1)] = List.range' 644 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 644) (n := 1+1)).symm

private theorem traversal_647 (fuel : Nat) (hf : 647 < fuel) :
    walk nodes fuel 647 = List.range' 647 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 647).rule = .bound .leftEnd 1 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_648 (fuel : Nat) (hf : 648 < fuel) :
    walk nodes fuel 648 = List.range' 644 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 648).rule = .split 0 (1/1280) 646 647 := by rfl
      simp only [walk, hr]
      rw [traversal_646 f (by omega), traversal_647 f (by omega)]
      change (List.range' 644 3 ++ List.range' (644+3) 1) ++
        [644+(3+1)] = List.range' 644 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 644) (n := 3+1)).symm

private theorem traversal_649 (fuel : Nat) (hf : 649 < fuel) :
    walk nodes fuel 649 = List.range' 637 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 649).rule = .split 3 (453/512) 643 648 := by rfl
      simp only [walk, hr]
      rw [traversal_643 f (by omega), traversal_648 f (by omega)]
      change (List.range' 637 7 ++ List.range' (637+7) 5) ++
        [637+(7+5)] = List.range' 637 ((7+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 637) (n := 7+5)).symm

private theorem traversal_650 (fuel : Nat) (hf : 650 < fuel) :
    walk nodes fuel 650 = List.range' 630 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 650).rule = .split 2 (4521/2048) 636 649 := by rfl
      simp only [walk, hr]
      rw [traversal_636 f (by omega), traversal_649 f (by omega)]
      change (List.range' 630 7 ++ List.range' (630+7) 13) ++
        [630+(7+13)] = List.range' 630 ((7+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 630) (n := 7+13)).symm

private theorem traversal_651 (fuel : Nat) (hf : 651 < fuel) :
    walk nodes fuel 651 = List.range' 651 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 651).rule = .bound .leftEnd 1 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_652 (fuel : Nat) (hf : 652 < fuel) :
    walk nodes fuel 652 = List.range' 652 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 652).rule = .bound .leftEnd 2 (3271/6144) (246195/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_653 (fuel : Nat) (hf : 653 < fuel) :
    walk nodes fuel 653 = List.range' 653 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 653).rule = .bound .leftEnd 1 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_654 (fuel : Nat) (hf : 654 < fuel) :
    walk nodes fuel 654 = List.range' 652 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 654).rule = .split 3 (453/512) 652 653 := by rfl
      simp only [walk, hr]
      rw [traversal_652 f (by omega), traversal_653 f (by omega)]
      change (List.range' 652 1 ++ List.range' (652+1) 1) ++
        [652+(1+1)] = List.range' 652 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 652) (n := 1+1)).symm

private theorem traversal_655 (fuel : Nat) (hf : 655 < fuel) :
    walk nodes fuel 655 = List.range' 651 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 655).rule = .split 2 (4521/2048) 651 654 := by rfl
      simp only [walk, hr]
      rw [traversal_651 f (by omega), traversal_654 f (by omega)]
      change (List.range' 651 1 ++ List.range' (651+1) 3) ++
        [651+(1+3)] = List.range' 651 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 651) (n := 1+3)).symm

private theorem traversal_656 (fuel : Nat) (hf : 656 < fuel) :
    walk nodes fuel 656 = List.range' 630 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 656).rule = .split 1 (1175/512) 650 655 := by rfl
      simp only [walk, hr]
      rw [traversal_650 f (by omega), traversal_655 f (by omega)]
      change (List.range' 630 21 ++ List.range' (630+21) 5) ++
        [630+(21+5)] = List.range' 630 ((21+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 630) (n := 21+5)).symm

private theorem traversal_657 (fuel : Nat) (hf : 657 < fuel) :
    walk nodes fuel 657 = List.range' 657 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 657).rule = .bound .leftEnd 1 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_658 (fuel : Nat) (hf : 658 < fuel) :
    walk nodes fuel 658 = List.range' 630 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 658).rule = .split 0 (1/640) 656 657 := by rfl
      simp only [walk, hr]
      rw [traversal_656 f (by omega), traversal_657 f (by omega)]
      change (List.range' 630 27 ++ List.range' (630+27) 1) ++
        [630+(27+1)] = List.range' 630 ((27+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 630) (n := 27+1)).symm

private theorem traversal_659 (fuel : Nat) (hf : 659 < fuel) :
    walk nodes fuel 659 = List.range' 629 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 659).rule = .split 3 (225/256) 629 658 := by rfl
      simp only [walk, hr]
      rw [traversal_629 f (by omega), traversal_658 f (by omega)]
      change (List.range' 629 1 ++ List.range' (629+1) 29) ++
        [629+(1+29)] = List.range' 629 ((1+29)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 629) (n := 1+29)).symm

private theorem traversal_660 (fuel : Nat) (hf : 660 < fuel) :
    walk nodes fuel 660 = List.range' 604 57 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 660).rule = .split 2 (2251/1024) 628 659 := by rfl
      simp only [walk, hr]
      rw [traversal_628 f (by omega), traversal_659 f (by omega)]
      change (List.range' 604 25 ++ List.range' (604+25) 31) ++
        [604+(25+31)] = List.range' 604 ((25+31)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 604) (n := 25+31)).symm

private theorem traversal_661 (fuel : Nat) (hf : 661 < fuel) :
    walk nodes fuel 661 = List.range' 603 59 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 661).rule = .split 1 (585/256) 603 660 := by rfl
      simp only [walk, hr]
      rw [traversal_603 f (by omega), traversal_660 f (by omega)]
      change (List.range' 603 1 ++ List.range' (603+1) 57) ++
        [603+(1+57)] = List.range' 603 ((1+57)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 603) (n := 1+57)).symm

private theorem traversal_662 (fuel : Nat) (hf : 662 < fuel) :
    walk nodes fuel 662 = List.range' 662 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 662).rule = .bound .leftEnd 8 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_663 (fuel : Nat) (hf : 663 < fuel) :
    walk nodes fuel 663 = List.range' 663 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 663).rule = .bound .leftEnd 1 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_664 (fuel : Nat) (hf : 664 < fuel) :
    walk nodes fuel 664 = List.range' 664 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 664).rule = .bound .leftEnd 2 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_665 (fuel : Nat) (hf : 665 < fuel) :
    walk nodes fuel 665 = List.range' 665 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 665).rule = .bound .leftEnd 1 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_666 (fuel : Nat) (hf : 666 < fuel) :
    walk nodes fuel 666 = List.range' 664 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 666).rule = .split 3 (225/256) 664 665 := by rfl
      simp only [walk, hr]
      rw [traversal_664 f (by omega), traversal_665 f (by omega)]
      change (List.range' 664 1 ++ List.range' (664+1) 1) ++
        [664+(1+1)] = List.range' 664 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 1+1)).symm

private theorem traversal_667 (fuel : Nat) (hf : 667 < fuel) :
    walk nodes fuel 667 = List.range' 663 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 667).rule = .split 2 (2251/1024) 663 666 := by rfl
      simp only [walk, hr]
      rw [traversal_663 f (by omega), traversal_666 f (by omega)]
      change (List.range' 663 1 ++ List.range' (663+1) 3) ++
        [663+(1+3)] = List.range' 663 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 663) (n := 1+3)).symm

private theorem traversal_668 (fuel : Nat) (hf : 668 < fuel) :
    walk nodes fuel 668 = List.range' 662 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 668).rule = .split 1 (585/256) 662 667 := by rfl
      simp only [walk, hr]
      rw [traversal_662 f (by omega), traversal_667 f (by omega)]
      change (List.range' 662 1 ++ List.range' (662+1) 5) ++
        [662+(1+5)] = List.range' 662 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 662) (n := 1+5)).symm

private theorem traversal_669 (fuel : Nat) (hf : 669 < fuel) :
    walk nodes fuel 669 = List.range' 603 67 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 669).rule = .split 0 (1/320) 661 668 := by rfl
      simp only [walk, hr]
      rw [traversal_661 f (by omega), traversal_668 f (by omega)]
      change (List.range' 603 59 ++ List.range' (603+59) 7) ++
        [603+(59+7)] = List.range' 603 ((59+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 603) (n := 59+7)).symm

theorem traversal_670 (fuel : Nat) (hf : 670 < fuel) :
    walk nodes fuel 670 = List.range' 602 69 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 670).rule = .split 3 (111/128) 602 669 := by rfl
      simp only [walk, hr]
      rw [traversal_602 f (by omega), traversal_669 f (by omega)]
      change (List.range' 602 1 ++ List.range' (602+1) 67) ++
        [602+(1+67)] = List.range' 602 ((1+67)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 602) (n := 1+67)).symm

theorem traversal_671 (fuel : Nat) (hf : 671 < fuel) :
    walk nodes fuel 671 = List.range' 671 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 671).rule = .bound .leftEnd 2 (6643/12288) (242441/524288) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
