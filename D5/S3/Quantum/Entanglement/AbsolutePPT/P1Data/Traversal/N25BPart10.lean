/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart10
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart10
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart10.traversal_732,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart10.traversal_733,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart10.traversal_734,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart10.traversal_735,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart10.traversal_736
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart00
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart09
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_670 (fuel : Nat) (hf : 670 < fuel) :
    walk nodes fuel 670 = List.range' 664 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 670).rule = .split 1 (45/16) 668 669 := by rfl
      simp only [walk, hr]
      rw [traversal_668 f (by omega), traversal_669 f (by omega)]
      change (List.range' 664 5 ++ List.range' (664+5) 1) ++
        [664+(5+1)] = List.range' 664 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 5+1)).symm

private theorem traversal_671 (fuel : Nat) (hf : 671 < fuel) :
    walk nodes fuel 671 = List.range' 671 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 671).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_672 (fuel : Nat) (hf : 672 < fuel) :
    walk nodes fuel 672 = List.range' 664 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 672).rule = .split 0 (1/20) 670 671 := by rfl
      simp only [walk, hr]
      rw [traversal_670 f (by omega), traversal_671 f (by omega)]
      change (List.range' 664 7 ++ List.range' (664+7) 1) ++
        [664+(7+1)] = List.range' 664 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 7+1)).symm

private theorem traversal_673 (fuel : Nat) (hf : 673 < fuel) :
    walk nodes fuel 673 = List.range' 673 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 673).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_674 (fuel : Nat) (hf : 674 < fuel) :
    walk nodes fuel 674 = List.range' 664 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 674).rule = .split 3 (3/8) 672 673 := by rfl
      simp only [walk, hr]
      rw [traversal_672 f (by omega), traversal_673 f (by omega)]
      change (List.range' 664 9 ++ List.range' (664+9) 1) ++
        [664+(9+1)] = List.range' 664 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 9+1)).symm

private theorem traversal_675 (fuel : Nat) (hf : 675 < fuel) :
    walk nodes fuel 675 = List.range' 675 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 675).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_676 (fuel : Nat) (hf : 676 < fuel) :
    walk nodes fuel 676 = List.range' 676 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 676).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_677 (fuel : Nat) (hf : 677 < fuel) :
    walk nodes fuel 677 = List.range' 677 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 677).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_678 (fuel : Nat) (hf : 678 < fuel) :
    walk nodes fuel 678 = List.range' 678 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 678).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_679 (fuel : Nat) (hf : 679 < fuel) :
    walk nodes fuel 679 = List.range' 677 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 679).rule = .split 3 (9/16) 677 678 := by rfl
      simp only [walk, hr]
      rw [traversal_677 f (by omega), traversal_678 f (by omega)]
      change (List.range' 677 1 ++ List.range' (677+1) 1) ++
        [677+(1+1)] = List.range' 677 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 677) (n := 1+1)).symm

private theorem traversal_680 (fuel : Nat) (hf : 680 < fuel) :
    walk nodes fuel 680 = List.range' 676 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 680).rule = .split 2 (73/64) 676 679 := by rfl
      simp only [walk, hr]
      rw [traversal_676 f (by omega), traversal_679 f (by omega)]
      change (List.range' 676 1 ++ List.range' (676+1) 3) ++
        [676+(1+3)] = List.range' 676 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 676) (n := 1+3)).symm

private theorem traversal_681 (fuel : Nat) (hf : 681 < fuel) :
    walk nodes fuel 681 = List.range' 681 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 681).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_682 (fuel : Nat) (hf : 682 < fuel) :
    walk nodes fuel 682 = List.range' 676 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 682).rule = .split 1 (45/16) 680 681 := by rfl
      simp only [walk, hr]
      rw [traversal_680 f (by omega), traversal_681 f (by omega)]
      change (List.range' 676 5 ++ List.range' (676+5) 1) ++
        [676+(5+1)] = List.range' 676 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 676) (n := 5+1)).symm

private theorem traversal_683 (fuel : Nat) (hf : 683 < fuel) :
    walk nodes fuel 683 = List.range' 683 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 683).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_684 (fuel : Nat) (hf : 684 < fuel) :
    walk nodes fuel 684 = List.range' 676 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 684).rule = .split 0 (1/20) 682 683 := by rfl
      simp only [walk, hr]
      rw [traversal_682 f (by omega), traversal_683 f (by omega)]
      change (List.range' 676 7 ++ List.range' (676+7) 1) ++
        [676+(7+1)] = List.range' 676 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 676) (n := 7+1)).symm

private theorem traversal_685 (fuel : Nat) (hf : 685 < fuel) :
    walk nodes fuel 685 = List.range' 675 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 685).rule = .split 3 (3/8) 675 684 := by rfl
      simp only [walk, hr]
      rw [traversal_675 f (by omega), traversal_684 f (by omega)]
      change (List.range' 675 1 ++ List.range' (675+1) 9) ++
        [675+(1+9)] = List.range' 675 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 675) (n := 1+9)).symm

private theorem traversal_686 (fuel : Nat) (hf : 686 < fuel) :
    walk nodes fuel 686 = List.range' 664 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 686).rule = .split 2 (27/32) 674 685 := by rfl
      simp only [walk, hr]
      rw [traversal_674 f (by omega), traversal_685 f (by omega)]
      change (List.range' 664 11 ++ List.range' (664+11) 11) ++
        [664+(11+11)] = List.range' 664 ((11+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 11+11)).symm

private theorem traversal_687 (fuel : Nat) (hf : 687 < fuel) :
    walk nodes fuel 687 = List.range' 687 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 687).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_688 (fuel : Nat) (hf : 688 < fuel) :
    walk nodes fuel 688 = List.range' 688 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 688).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_689 (fuel : Nat) (hf : 689 < fuel) :
    walk nodes fuel 689 = List.range' 687 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 689).rule = .split 2 (27/32) 687 688 := by rfl
      simp only [walk, hr]
      rw [traversal_687 f (by omega), traversal_688 f (by omega)]
      change (List.range' 687 1 ++ List.range' (687+1) 1) ++
        [687+(1+1)] = List.range' 687 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 687) (n := 1+1)).symm

private theorem traversal_690 (fuel : Nat) (hf : 690 < fuel) :
    walk nodes fuel 690 = List.range' 664 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 690).rule = .split 1 (25/8) 686 689 := by rfl
      simp only [walk, hr]
      rw [traversal_686 f (by omega), traversal_689 f (by omega)]
      change (List.range' 664 23 ++ List.range' (664+23) 3) ++
        [664+(23+3)] = List.range' 664 ((23+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 23+3)).symm

private theorem traversal_691 (fuel : Nat) (hf : 691 < fuel) :
    walk nodes fuel 691 = List.range' 691 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 691).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_692 (fuel : Nat) (hf : 692 < fuel) :
    walk nodes fuel 692 = List.range' 664 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 692).rule = .split 3 (3/4) 690 691 := by rfl
      simp only [walk, hr]
      rw [traversal_690 f (by omega), traversal_691 f (by omega)]
      change (List.range' 664 27 ++ List.range' (664+27) 1) ++
        [664+(27+1)] = List.range' 664 ((27+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 27+1)).symm

private theorem traversal_693 (fuel : Nat) (hf : 693 < fuel) :
    walk nodes fuel 693 = List.range' 693 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 693).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_694 (fuel : Nat) (hf : 694 < fuel) :
    walk nodes fuel 694 = List.range' 694 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 694).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_695 (fuel : Nat) (hf : 695 < fuel) :
    walk nodes fuel 695 = List.range' 695 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 695).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_696 (fuel : Nat) (hf : 696 < fuel) :
    walk nodes fuel 696 = List.range' 694 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 696).rule = .split 3 (9/16) 694 695 := by rfl
      simp only [walk, hr]
      rw [traversal_694 f (by omega), traversal_695 f (by omega)]
      change (List.range' 694 1 ++ List.range' (694+1) 1) ++
        [694+(1+1)] = List.range' 694 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 694) (n := 1+1)).symm

private theorem traversal_697 (fuel : Nat) (hf : 697 < fuel) :
    walk nodes fuel 697 = List.range' 697 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 697).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_698 (fuel : Nat) (hf : 698 < fuel) :
    walk nodes fuel 698 = List.range' 694 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 698).rule = .split 2 (111/64) 696 697 := by rfl
      simp only [walk, hr]
      rw [traversal_696 f (by omega), traversal_697 f (by omega)]
      change (List.range' 694 3 ++ List.range' (694+3) 1) ++
        [694+(3+1)] = List.range' 694 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 694) (n := 3+1)).symm

private theorem traversal_699 (fuel : Nat) (hf : 699 < fuel) :
    walk nodes fuel 699 = List.range' 699 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 699).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_700 (fuel : Nat) (hf : 700 < fuel) :
    walk nodes fuel 700 = List.range' 694 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 700).rule = .split 1 (45/16) 698 699 := by rfl
      simp only [walk, hr]
      rw [traversal_698 f (by omega), traversal_699 f (by omega)]
      change (List.range' 694 5 ++ List.range' (694+5) 1) ++
        [694+(5+1)] = List.range' 694 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 694) (n := 5+1)).symm

private theorem traversal_701 (fuel : Nat) (hf : 701 < fuel) :
    walk nodes fuel 701 = List.range' 701 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 701).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_702 (fuel : Nat) (hf : 702 < fuel) :
    walk nodes fuel 702 = List.range' 694 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 702).rule = .split 0 (1/20) 700 701 := by rfl
      simp only [walk, hr]
      rw [traversal_700 f (by omega), traversal_701 f (by omega)]
      change (List.range' 694 7 ++ List.range' (694+7) 1) ++
        [694+(7+1)] = List.range' 694 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 694) (n := 7+1)).symm

private theorem traversal_703 (fuel : Nat) (hf : 703 < fuel) :
    walk nodes fuel 703 = List.range' 693 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 703).rule = .split 3 (3/8) 693 702 := by rfl
      simp only [walk, hr]
      rw [traversal_693 f (by omega), traversal_702 f (by omega)]
      change (List.range' 693 1 ++ List.range' (693+1) 9) ++
        [693+(1+9)] = List.range' 693 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 693) (n := 1+9)).symm

private theorem traversal_704 (fuel : Nat) (hf : 704 < fuel) :
    walk nodes fuel 704 = List.range' 704 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 704).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_705 (fuel : Nat) (hf : 705 < fuel) :
    walk nodes fuel 705 = List.range' 693 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 705).rule = .split 2 (65/32) 703 704 := by rfl
      simp only [walk, hr]
      rw [traversal_703 f (by omega), traversal_704 f (by omega)]
      change (List.range' 693 11 ++ List.range' (693+11) 1) ++
        [693+(11+1)] = List.range' 693 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 693) (n := 11+1)).symm

private theorem traversal_706 (fuel : Nat) (hf : 706 < fuel) :
    walk nodes fuel 706 = List.range' 706 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 706).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_707 (fuel : Nat) (hf : 707 < fuel) :
    walk nodes fuel 707 = List.range' 693 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 707).rule = .split 1 (25/8) 705 706 := by rfl
      simp only [walk, hr]
      rw [traversal_705 f (by omega), traversal_706 f (by omega)]
      change (List.range' 693 13 ++ List.range' (693+13) 1) ++
        [693+(13+1)] = List.range' 693 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 693) (n := 13+1)).symm

private theorem traversal_708 (fuel : Nat) (hf : 708 < fuel) :
    walk nodes fuel 708 = List.range' 708 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 708).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_709 (fuel : Nat) (hf : 709 < fuel) :
    walk nodes fuel 709 = List.range' 709 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 709).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_710 (fuel : Nat) (hf : 710 < fuel) :
    walk nodes fuel 710 = List.range' 710 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 710).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_711 (fuel : Nat) (hf : 711 < fuel) :
    walk nodes fuel 711 = List.range' 709 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 711).rule = .split 2 (149/64) 709 710 := by rfl
      simp only [walk, hr]
      rw [traversal_709 f (by omega), traversal_710 f (by omega)]
      change (List.range' 709 1 ++ List.range' (709+1) 1) ++
        [709+(1+1)] = List.range' 709 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 709) (n := 1+1)).symm

private theorem traversal_712 (fuel : Nat) (hf : 712 < fuel) :
    walk nodes fuel 712 = List.range' 712 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 712).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_713 (fuel : Nat) (hf : 713 < fuel) :
    walk nodes fuel 713 = List.range' 709 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 713).rule = .split 1 (45/16) 711 712 := by rfl
      simp only [walk, hr]
      rw [traversal_711 f (by omega), traversal_712 f (by omega)]
      change (List.range' 709 3 ++ List.range' (709+3) 1) ++
        [709+(3+1)] = List.range' 709 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 709) (n := 3+1)).symm

private theorem traversal_714 (fuel : Nat) (hf : 714 < fuel) :
    walk nodes fuel 714 = List.range' 714 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 714).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_715 (fuel : Nat) (hf : 715 < fuel) :
    walk nodes fuel 715 = List.range' 709 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 715).rule = .split 0 (1/20) 713 714 := by rfl
      simp only [walk, hr]
      rw [traversal_713 f (by omega), traversal_714 f (by omega)]
      change (List.range' 709 5 ++ List.range' (709+5) 1) ++
        [709+(5+1)] = List.range' 709 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 709) (n := 5+1)).symm

private theorem traversal_716 (fuel : Nat) (hf : 716 < fuel) :
    walk nodes fuel 716 = List.range' 716 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 716).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_717 (fuel : Nat) (hf : 717 < fuel) :
    walk nodes fuel 717 = List.range' 709 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 717).rule = .split 3 (9/8) 715 716 := by rfl
      simp only [walk, hr]
      rw [traversal_715 f (by omega), traversal_716 f (by omega)]
      change (List.range' 709 7 ++ List.range' (709+7) 1) ++
        [709+(7+1)] = List.range' 709 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 709) (n := 7+1)).symm

private theorem traversal_718 (fuel : Nat) (hf : 718 < fuel) :
    walk nodes fuel 718 = List.range' 708 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 718).rule = .split 2 (65/32) 708 717 := by rfl
      simp only [walk, hr]
      rw [traversal_708 f (by omega), traversal_717 f (by omega)]
      change (List.range' 708 1 ++ List.range' (708+1) 9) ++
        [708+(1+9)] = List.range' 708 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 708) (n := 1+9)).symm

private theorem traversal_719 (fuel : Nat) (hf : 719 < fuel) :
    walk nodes fuel 719 = List.range' 719 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 719).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_720 (fuel : Nat) (hf : 720 < fuel) :
    walk nodes fuel 720 = List.range' 708 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 720).rule = .split 1 (25/8) 718 719 := by rfl
      simp only [walk, hr]
      rw [traversal_718 f (by omega), traversal_719 f (by omega)]
      change (List.range' 708 11 ++ List.range' (708+11) 1) ++
        [708+(11+1)] = List.range' 708 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 708) (n := 11+1)).symm

private theorem traversal_721 (fuel : Nat) (hf : 721 < fuel) :
    walk nodes fuel 721 = List.range' 693 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 721).rule = .split 3 (3/4) 707 720 := by rfl
      simp only [walk, hr]
      rw [traversal_707 f (by omega), traversal_720 f (by omega)]
      change (List.range' 693 15 ++ List.range' (693+15) 13) ++
        [693+(15+13)] = List.range' 693 ((15+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 693) (n := 15+13)).symm

private theorem traversal_722 (fuel : Nat) (hf : 722 < fuel) :
    walk nodes fuel 722 = List.range' 664 59 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 722).rule = .split 2 (23/16) 692 721 := by rfl
      simp only [walk, hr]
      rw [traversal_692 f (by omega), traversal_721 f (by omega)]
      change (List.range' 664 29 ++ List.range' (664+29) 29) ++
        [664+(29+29)] = List.range' 664 ((29+29)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 29+29)).symm

private theorem traversal_723 (fuel : Nat) (hf : 723 < fuel) :
    walk nodes fuel 723 = List.range' 723 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 723).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_724 (fuel : Nat) (hf : 724 < fuel) :
    walk nodes fuel 724 = List.range' 724 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 724).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_725 (fuel : Nat) (hf : 725 < fuel) :
    walk nodes fuel 725 = List.range' 723 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 725).rule = .split 2 (23/16) 723 724 := by rfl
      simp only [walk, hr]
      rw [traversal_723 f (by omega), traversal_724 f (by omega)]
      change (List.range' 723 1 ++ List.range' (723+1) 1) ++
        [723+(1+1)] = List.range' 723 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 723) (n := 1+1)).symm

private theorem traversal_726 (fuel : Nat) (hf : 726 < fuel) :
    walk nodes fuel 726 = List.range' 664 63 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 726).rule = .split 1 (15/4) 722 725 := by rfl
      simp only [walk, hr]
      rw [traversal_722 f (by omega), traversal_725 f (by omega)]
      change (List.range' 664 59 ++ List.range' (664+59) 3) ++
        [664+(59+3)] = List.range' 664 ((59+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 59+3)).symm

private theorem traversal_727 (fuel : Nat) (hf : 727 < fuel) :
    walk nodes fuel 727 = List.range' 727 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 727).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_728 (fuel : Nat) (hf : 728 < fuel) :
    walk nodes fuel 728 = List.range' 664 65 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 728).rule = .split 3 (3/2) 726 727 := by rfl
      simp only [walk, hr]
      rw [traversal_726 f (by omega), traversal_727 f (by omega)]
      change (List.range' 664 63 ++ List.range' (664+63) 1) ++
        [664+(63+1)] = List.range' 664 ((63+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 63+1)).symm

private theorem traversal_729 (fuel : Nat) (hf : 729 < fuel) :
    walk nodes fuel 729 = List.range' 729 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 729).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_730 (fuel : Nat) (hf : 730 < fuel) :
    walk nodes fuel 730 = List.range' 664 67 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 730).rule = .split 2 (21/8) 728 729 := by rfl
      simp only [walk, hr]
      rw [traversal_728 f (by omega), traversal_729 f (by omega)]
      change (List.range' 664 65 ++ List.range' (664+65) 1) ++
        [664+(65+1)] = List.range' 664 ((65+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 664) (n := 65+1)).symm

private theorem traversal_731 (fuel : Nat) (hf : 731 < fuel) :
    walk nodes fuel 731 = List.range' 1 731 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 731).rule = .split 1 (5/2) 663 730 := by rfl
      simp only [walk, hr]
      rw [traversal_663 f (by omega), traversal_730 f (by omega)]
      change (List.range' 1 663 ++ List.range' (1+663) 67) ++
        [1+(663+67)] = List.range' 1 ((663+67)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1) (n := 663+67)).symm

theorem traversal_732 (fuel : Nat) (hf : 732 < fuel) :
    walk nodes fuel 732 = List.range' 0 733 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 732).rule = .split 2 (1/4) 0 731 := by rfl
      simp only [walk, hr]
      rw [traversal_0 f (by omega), traversal_731 f (by omega)]
      change (List.range' 0 1 ++ List.range' (0+1) 731) ++
        [0+(1+731)] = List.range' 0 ((1+731)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 0) (n := 1+731)).symm

theorem traversal_733 (fuel : Nat) (hf : 733 < fuel) :
    walk nodes fuel 733 = List.range' 733 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 733).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_734 (fuel : Nat) (hf : 734 < fuel) :
    walk nodes fuel 734 = List.range' 734 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 734).rule = .bound .leftEnd 5 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_735 (fuel : Nat) (hf : 735 < fuel) :
    walk nodes fuel 735 = List.range' 735 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 735).rule = .bound .leftEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_736 (fuel : Nat) (hf : 736 < fuel) :
    walk nodes fuel 736 = List.range' 736 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 736).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
