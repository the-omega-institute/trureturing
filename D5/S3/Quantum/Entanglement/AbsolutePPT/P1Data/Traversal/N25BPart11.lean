/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart11
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart11
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart11.traversal_797,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart11.traversal_802,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart11.traversal_803
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart10
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_737 (fuel : Nat) (hf : 737 < fuel) :
    walk nodes fuel 737 = List.range' 735 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 737).rule = .split 1 (25/16) 735 736 := by rfl
      simp only [walk, hr]
      rw [traversal_735 f (by omega), traversal_736 f (by omega)]
      change (List.range' 735 1 ++ List.range' (735+1) 1) ++
        [735+(1+1)] = List.range' 735 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 735) (n := 1+1)).symm

private theorem traversal_738 (fuel : Nat) (hf : 738 < fuel) :
    walk nodes fuel 738 = List.range' 738 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 738).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_739 (fuel : Nat) (hf : 739 < fuel) :
    walk nodes fuel 739 = List.range' 735 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 739).rule = .split 0 (3/20) 737 738 := by rfl
      simp only [walk, hr]
      rw [traversal_737 f (by omega), traversal_738 f (by omega)]
      change (List.range' 735 3 ++ List.range' (735+3) 1) ++
        [735+(3+1)] = List.range' 735 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 735) (n := 3+1)).symm

private theorem traversal_740 (fuel : Nat) (hf : 740 < fuel) :
    walk nodes fuel 740 = List.range' 740 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 740).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_741 (fuel : Nat) (hf : 741 < fuel) :
    walk nodes fuel 741 = List.range' 735 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 741).rule = .split 3 (3/8) 739 740 := by rfl
      simp only [walk, hr]
      rw [traversal_739 f (by omega), traversal_740 f (by omega)]
      change (List.range' 735 5 ++ List.range' (735+5) 1) ++
        [735+(5+1)] = List.range' 735 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 735) (n := 5+1)).symm

private theorem traversal_742 (fuel : Nat) (hf : 742 < fuel) :
    walk nodes fuel 742 = List.range' 734 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 742).rule = .split 2 (5/8) 734 741 := by rfl
      simp only [walk, hr]
      rw [traversal_734 f (by omega), traversal_741 f (by omega)]
      change (List.range' 734 1 ++ List.range' (734+1) 7) ++
        [734+(1+7)] = List.range' 734 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 734) (n := 1+7)).symm

private theorem traversal_743 (fuel : Nat) (hf : 743 < fuel) :
    walk nodes fuel 743 = List.range' 743 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 743).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_744 (fuel : Nat) (hf : 744 < fuel) :
    walk nodes fuel 744 = List.range' 744 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 744).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_745 (fuel : Nat) (hf : 745 < fuel) :
    walk nodes fuel 745 = List.range' 745 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 745).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_746 (fuel : Nat) (hf : 746 < fuel) :
    walk nodes fuel 746 = List.range' 744 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 746).rule = .split 3 (3/8) 744 745 := by rfl
      simp only [walk, hr]
      rw [traversal_744 f (by omega), traversal_745 f (by omega)]
      change (List.range' 744 1 ++ List.range' (744+1) 1) ++
        [744+(1+1)] = List.range' 744 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 744) (n := 1+1)).symm

private theorem traversal_747 (fuel : Nat) (hf : 747 < fuel) :
    walk nodes fuel 747 = List.range' 743 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 747).rule = .split 2 (5/8) 743 746 := by rfl
      simp only [walk, hr]
      rw [traversal_743 f (by omega), traversal_746 f (by omega)]
      change (List.range' 743 1 ++ List.range' (743+1) 3) ++
        [743+(1+3)] = List.range' 743 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 743) (n := 1+3)).symm

private theorem traversal_748 (fuel : Nat) (hf : 748 < fuel) :
    walk nodes fuel 748 = List.range' 734 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 748).rule = .split 1 (15/8) 742 747 := by rfl
      simp only [walk, hr]
      rw [traversal_742 f (by omega), traversal_747 f (by omega)]
      change (List.range' 734 9 ++ List.range' (734+9) 5) ++
        [734+(9+5)] = List.range' 734 ((9+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 734) (n := 9+5)).symm

private theorem traversal_749 (fuel : Nat) (hf : 749 < fuel) :
    walk nodes fuel 749 = List.range' 749 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 749).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_750 (fuel : Nat) (hf : 750 < fuel) :
    walk nodes fuel 750 = List.range' 750 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 750).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_751 (fuel : Nat) (hf : 751 < fuel) :
    walk nodes fuel 751 = List.range' 749 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 751).rule = .split 2 (5/8) 749 750 := by rfl
      simp only [walk, hr]
      rw [traversal_749 f (by omega), traversal_750 f (by omega)]
      change (List.range' 749 1 ++ List.range' (749+1) 1) ++
        [749+(1+1)] = List.range' 749 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 749) (n := 1+1)).symm

private theorem traversal_752 (fuel : Nat) (hf : 752 < fuel) :
    walk nodes fuel 752 = List.range' 752 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 752).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_753 (fuel : Nat) (hf : 753 < fuel) :
    walk nodes fuel 753 = List.range' 749 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 753).rule = .split 1 (15/8) 751 752 := by rfl
      simp only [walk, hr]
      rw [traversal_751 f (by omega), traversal_752 f (by omega)]
      change (List.range' 749 3 ++ List.range' (749+3) 1) ++
        [749+(3+1)] = List.range' 749 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 749) (n := 3+1)).symm

private theorem traversal_754 (fuel : Nat) (hf : 754 < fuel) :
    walk nodes fuel 754 = List.range' 734 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 754).rule = .split 0 (1/5) 748 753 := by rfl
      simp only [walk, hr]
      rw [traversal_748 f (by omega), traversal_753 f (by omega)]
      change (List.range' 734 15 ++ List.range' (734+15) 5) ++
        [734+(15+5)] = List.range' 734 ((15+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 734) (n := 15+5)).symm

private theorem traversal_755 (fuel : Nat) (hf : 755 < fuel) :
    walk nodes fuel 755 = List.range' 755 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 755).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_756 (fuel : Nat) (hf : 756 < fuel) :
    walk nodes fuel 756 = List.range' 734 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 756).rule = .split 3 (3/4) 754 755 := by rfl
      simp only [walk, hr]
      rw [traversal_754 f (by omega), traversal_755 f (by omega)]
      change (List.range' 734 21 ++ List.range' (734+21) 1) ++
        [734+(21+1)] = List.range' 734 ((21+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 734) (n := 21+1)).symm

private theorem traversal_757 (fuel : Nat) (hf : 757 < fuel) :
    walk nodes fuel 757 = List.range' 757 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 757).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_758 (fuel : Nat) (hf : 758 < fuel) :
    walk nodes fuel 758 = List.range' 758 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 758).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_759 (fuel : Nat) (hf : 759 < fuel) :
    walk nodes fuel 759 = List.range' 757 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 759).rule = .split 3 (3/8) 757 758 := by rfl
      simp only [walk, hr]
      rw [traversal_757 f (by omega), traversal_758 f (by omega)]
      change (List.range' 757 1 ++ List.range' (757+1) 1) ++
        [757+(1+1)] = List.range' 757 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 757) (n := 1+1)).symm

private theorem traversal_760 (fuel : Nat) (hf : 760 < fuel) :
    walk nodes fuel 760 = List.range' 760 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 760).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_761 (fuel : Nat) (hf : 761 < fuel) :
    walk nodes fuel 761 = List.range' 761 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 761).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_762 (fuel : Nat) (hf : 762 < fuel) :
    walk nodes fuel 762 = List.range' 762 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 762).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_763 (fuel : Nat) (hf : 763 < fuel) :
    walk nodes fuel 763 = List.range' 761 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 763).rule = .split 1 (25/16) 761 762 := by rfl
      simp only [walk, hr]
      rw [traversal_761 f (by omega), traversal_762 f (by omega)]
      change (List.range' 761 1 ++ List.range' (761+1) 1) ++
        [761+(1+1)] = List.range' 761 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 761) (n := 1+1)).symm

private theorem traversal_764 (fuel : Nat) (hf : 764 < fuel) :
    walk nodes fuel 764 = List.range' 764 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 764).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_765 (fuel : Nat) (hf : 765 < fuel) :
    walk nodes fuel 765 = List.range' 761 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 765).rule = .split 0 (3/20) 763 764 := by rfl
      simp only [walk, hr]
      rw [traversal_763 f (by omega), traversal_764 f (by omega)]
      change (List.range' 761 3 ++ List.range' (761+3) 1) ++
        [761+(3+1)] = List.range' 761 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 761) (n := 3+1)).symm

private theorem traversal_766 (fuel : Nat) (hf : 766 < fuel) :
    walk nodes fuel 766 = List.range' 760 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 766).rule = .split 3 (3/8) 760 765 := by rfl
      simp only [walk, hr]
      rw [traversal_760 f (by omega), traversal_765 f (by omega)]
      change (List.range' 760 1 ++ List.range' (760+1) 5) ++
        [760+(1+5)] = List.range' 760 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 760) (n := 1+5)).symm

private theorem traversal_767 (fuel : Nat) (hf : 767 < fuel) :
    walk nodes fuel 767 = List.range' 757 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 767).rule = .split 2 (15/8) 759 766 := by rfl
      simp only [walk, hr]
      rw [traversal_759 f (by omega), traversal_766 f (by omega)]
      change (List.range' 757 3 ++ List.range' (757+3) 7) ++
        [757+(3+7)] = List.range' 757 ((3+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 757) (n := 3+7)).symm

private theorem traversal_768 (fuel : Nat) (hf : 768 < fuel) :
    walk nodes fuel 768 = List.range' 768 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 768).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_769 (fuel : Nat) (hf : 769 < fuel) :
    walk nodes fuel 769 = List.range' 757 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 769).rule = .split 1 (15/8) 767 768 := by rfl
      simp only [walk, hr]
      rw [traversal_767 f (by omega), traversal_768 f (by omega)]
      change (List.range' 757 11 ++ List.range' (757+11) 1) ++
        [757+(11+1)] = List.range' 757 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 757) (n := 11+1)).symm

private theorem traversal_770 (fuel : Nat) (hf : 770 < fuel) :
    walk nodes fuel 770 = List.range' 770 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 770).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_771 (fuel : Nat) (hf : 771 < fuel) :
    walk nodes fuel 771 = List.range' 757 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 771).rule = .split 0 (1/5) 769 770 := by rfl
      simp only [walk, hr]
      rw [traversal_769 f (by omega), traversal_770 f (by omega)]
      change (List.range' 757 13 ++ List.range' (757+13) 1) ++
        [757+(13+1)] = List.range' 757 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 757) (n := 13+1)).symm

private theorem traversal_772 (fuel : Nat) (hf : 772 < fuel) :
    walk nodes fuel 772 = List.range' 772 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 772).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_773 (fuel : Nat) (hf : 773 < fuel) :
    walk nodes fuel 773 = List.range' 773 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 773).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_774 (fuel : Nat) (hf : 774 < fuel) :
    walk nodes fuel 774 = List.range' 774 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 774).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_775 (fuel : Nat) (hf : 775 < fuel) :
    walk nodes fuel 775 = List.range' 773 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 775).rule = .split 2 (15/8) 773 774 := by rfl
      simp only [walk, hr]
      rw [traversal_773 f (by omega), traversal_774 f (by omega)]
      change (List.range' 773 1 ++ List.range' (773+1) 1) ++
        [773+(1+1)] = List.range' 773 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 773) (n := 1+1)).symm

private theorem traversal_776 (fuel : Nat) (hf : 776 < fuel) :
    walk nodes fuel 776 = List.range' 772 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 776).rule = .split 1 (15/8) 772 775 := by rfl
      simp only [walk, hr]
      rw [traversal_772 f (by omega), traversal_775 f (by omega)]
      change (List.range' 772 1 ++ List.range' (772+1) 3) ++
        [772+(1+3)] = List.range' 772 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 772) (n := 1+3)).symm

private theorem traversal_777 (fuel : Nat) (hf : 777 < fuel) :
    walk nodes fuel 777 = List.range' 777 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 777).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_778 (fuel : Nat) (hf : 778 < fuel) :
    walk nodes fuel 778 = List.range' 772 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 778).rule = .split 0 (1/5) 776 777 := by rfl
      simp only [walk, hr]
      rw [traversal_776 f (by omega), traversal_777 f (by omega)]
      change (List.range' 772 5 ++ List.range' (772+5) 1) ++
        [772+(5+1)] = List.range' 772 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 772) (n := 5+1)).symm

private theorem traversal_779 (fuel : Nat) (hf : 779 < fuel) :
    walk nodes fuel 779 = List.range' 757 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 779).rule = .split 3 (3/4) 771 778 := by rfl
      simp only [walk, hr]
      rw [traversal_771 f (by omega), traversal_778 f (by omega)]
      change (List.range' 757 15 ++ List.range' (757+15) 7) ++
        [757+(15+7)] = List.range' 757 ((15+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 757) (n := 15+7)).symm

private theorem traversal_780 (fuel : Nat) (hf : 780 < fuel) :
    walk nodes fuel 780 = List.range' 734 47 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 780).rule = .split 2 (5/4) 756 779 := by rfl
      simp only [walk, hr]
      rw [traversal_756 f (by omega), traversal_779 f (by omega)]
      change (List.range' 734 23 ++ List.range' (734+23) 23) ++
        [734+(23+23)] = List.range' 734 ((23+23)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 734) (n := 23+23)).symm

private theorem traversal_781 (fuel : Nat) (hf : 781 < fuel) :
    walk nodes fuel 781 = List.range' 733 49 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 781).rule = .split 1 (5/4) 733 780 := by rfl
      simp only [walk, hr]
      rw [traversal_733 f (by omega), traversal_780 f (by omega)]
      change (List.range' 733 1 ++ List.range' (733+1) 47) ++
        [733+(1+47)] = List.range' 733 ((1+47)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 733) (n := 1+47)).symm

private theorem traversal_782 (fuel : Nat) (hf : 782 < fuel) :
    walk nodes fuel 782 = List.range' 782 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 782).rule = .bound .leftEnd 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_783 (fuel : Nat) (hf : 783 < fuel) :
    walk nodes fuel 783 = List.range' 783 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 783).rule = .bound .vertex 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_784 (fuel : Nat) (hf : 784 < fuel) :
    walk nodes fuel 784 = List.range' 784 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 784).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_785 (fuel : Nat) (hf : 785 < fuel) :
    walk nodes fuel 785 = List.range' 783 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 785).rule = .split 1 (5/8) 783 784 := by rfl
      simp only [walk, hr]
      rw [traversal_783 f (by omega), traversal_784 f (by omega)]
      change (List.range' 783 1 ++ List.range' (783+1) 1) ++
        [783+(1+1)] = List.range' 783 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 783) (n := 1+1)).symm

private theorem traversal_786 (fuel : Nat) (hf : 786 < fuel) :
    walk nodes fuel 786 = List.range' 786 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 786).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_787 (fuel : Nat) (hf : 787 < fuel) :
    walk nodes fuel 787 = List.range' 783 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 787).rule = .split 0 (2/5) 785 786 := by rfl
      simp only [walk, hr]
      rw [traversal_785 f (by omega), traversal_786 f (by omega)]
      change (List.range' 783 3 ++ List.range' (783+3) 1) ++
        [783+(3+1)] = List.range' 783 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 783) (n := 3+1)).symm

private theorem traversal_788 (fuel : Nat) (hf : 788 < fuel) :
    walk nodes fuel 788 = List.range' 788 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 788).rule = .bound .vertex 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_789 (fuel : Nat) (hf : 789 < fuel) :
    walk nodes fuel 789 = List.range' 789 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 789).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_790 (fuel : Nat) (hf : 790 < fuel) :
    walk nodes fuel 790 = List.range' 788 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 790).rule = .split 0 (2/5) 788 789 := by rfl
      simp only [walk, hr]
      rw [traversal_788 f (by omega), traversal_789 f (by omega)]
      change (List.range' 788 1 ++ List.range' (788+1) 1) ++
        [788+(1+1)] = List.range' 788 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 788) (n := 1+1)).symm

private theorem traversal_791 (fuel : Nat) (hf : 791 < fuel) :
    walk nodes fuel 791 = List.range' 783 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 791).rule = .split 3 (3/4) 787 790 := by rfl
      simp only [walk, hr]
      rw [traversal_787 f (by omega), traversal_790 f (by omega)]
      change (List.range' 783 5 ++ List.range' (783+5) 3) ++
        [783+(5+3)] = List.range' 783 ((5+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 783) (n := 5+3)).symm

private theorem traversal_792 (fuel : Nat) (hf : 792 < fuel) :
    walk nodes fuel 792 = List.range' 782 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 792).rule = .split 2 (5/4) 782 791 := by rfl
      simp only [walk, hr]
      rw [traversal_782 f (by omega), traversal_791 f (by omega)]
      change (List.range' 782 1 ++ List.range' (782+1) 9) ++
        [782+(1+9)] = List.range' 782 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 782) (n := 1+9)).symm

private theorem traversal_793 (fuel : Nat) (hf : 793 < fuel) :
    walk nodes fuel 793 = List.range' 793 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 793).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_794 (fuel : Nat) (hf : 794 < fuel) :
    walk nodes fuel 794 = List.range' 794 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 794).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_795 (fuel : Nat) (hf : 795 < fuel) :
    walk nodes fuel 795 = List.range' 793 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 795).rule = .split 2 (5/4) 793 794 := by rfl
      simp only [walk, hr]
      rw [traversal_793 f (by omega), traversal_794 f (by omega)]
      change (List.range' 793 1 ++ List.range' (793+1) 1) ++
        [793+(1+1)] = List.range' 793 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 793) (n := 1+1)).symm

private theorem traversal_796 (fuel : Nat) (hf : 796 < fuel) :
    walk nodes fuel 796 = List.range' 782 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 796).rule = .split 1 (5/4) 792 795 := by rfl
      simp only [walk, hr]
      rw [traversal_792 f (by omega), traversal_795 f (by omega)]
      change (List.range' 782 11 ++ List.range' (782+11) 3) ++
        [782+(11+3)] = List.range' 782 ((11+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 782) (n := 11+3)).symm

theorem traversal_797 (fuel : Nat) (hf : 797 < fuel) :
    walk nodes fuel 797 = List.range' 733 65 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 797).rule = .split 0 (3/10) 781 796 := by rfl
      simp only [walk, hr]
      rw [traversal_781 f (by omega), traversal_796 f (by omega)]
      change (List.range' 733 49 ++ List.range' (733+49) 15) ++
        [733+(49+15)] = List.range' 733 ((49+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 733) (n := 49+15)).symm

private theorem traversal_798 (fuel : Nat) (hf : 798 < fuel) :
    walk nodes fuel 798 = List.range' 798 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 798).rule = .infeasible 3 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_799 (fuel : Nat) (hf : 799 < fuel) :
    walk nodes fuel 799 = List.range' 799 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 799).rule = .bound .leftEnd 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_800 (fuel : Nat) (hf : 800 < fuel) :
    walk nodes fuel 800 = List.range' 800 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 800).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_801 (fuel : Nat) (hf : 801 < fuel) :
    walk nodes fuel 801 = List.range' 799 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 801).rule = .split 3 (9/4) 799 800 := by rfl
      simp only [walk, hr]
      rw [traversal_799 f (by omega), traversal_800 f (by omega)]
      change (List.range' 799 1 ++ List.range' (799+1) 1) ++
        [799+(1+1)] = List.range' 799 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 799) (n := 1+1)).symm

theorem traversal_802 (fuel : Nat) (hf : 802 < fuel) :
    walk nodes fuel 802 = List.range' 798 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 802).rule = .split 2 (5/4) 798 801 := by rfl
      simp only [walk, hr]
      rw [traversal_798 f (by omega), traversal_801 f (by omega)]
      change (List.range' 798 1 ++ List.range' (798+1) 3) ++
        [798+(1+3)] = List.range' 798 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 798) (n := 1+3)).symm

theorem traversal_803 (fuel : Nat) (hf : 803 < fuel) :
    walk nodes fuel 803 = List.range' 803 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 803).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
