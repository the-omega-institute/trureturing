/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart12
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart12
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart12.traversal_869,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart12.traversal_870
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart11
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_804 (fuel : Nat) (hf : 804 < fuel) :
    walk nodes fuel 804 = List.range' 798 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 804).rule = .split 1 (5/4) 802 803 := by rfl
      simp only [walk, hr]
      rw [traversal_802 f (by omega), traversal_803 f (by omega)]
      change (List.range' 798 5 ++ List.range' (798+5) 1) ++
        [798+(5+1)] = List.range' 798 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 798) (n := 5+1)).symm

private theorem traversal_805 (fuel : Nat) (hf : 805 < fuel) :
    walk nodes fuel 805 = List.range' 805 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 805).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_806 (fuel : Nat) (hf : 806 < fuel) :
    walk nodes fuel 806 = List.range' 798 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 806).rule = .split 0 (3/10) 804 805 := by rfl
      simp only [walk, hr]
      rw [traversal_804 f (by omega), traversal_805 f (by omega)]
      change (List.range' 798 7 ++ List.range' (798+7) 1) ++
        [798+(7+1)] = List.range' 798 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 798) (n := 7+1)).symm

private theorem traversal_807 (fuel : Nat) (hf : 807 < fuel) :
    walk nodes fuel 807 = List.range' 733 75 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 807).rule = .split 3 (3/2) 797 806 := by rfl
      simp only [walk, hr]
      rw [traversal_797 f (by omega), traversal_806 f (by omega)]
      change (List.range' 733 65 ++ List.range' (733+65) 9) ++
        [733+(65+9)] = List.range' 733 ((65+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 733) (n := 65+9)).symm

private theorem traversal_808 (fuel : Nat) (hf : 808 < fuel) :
    walk nodes fuel 808 = List.range' 808 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 808).rule = .bound .vertex 4 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_809 (fuel : Nat) (hf : 809 < fuel) :
    walk nodes fuel 809 = List.range' 809 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 809).rule = .bound .vertex 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_810 (fuel : Nat) (hf : 810 < fuel) :
    walk nodes fuel 810 = List.range' 808 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 810).rule = .split 0 (1/5) 808 809 := by rfl
      simp only [walk, hr]
      rw [traversal_808 f (by omega), traversal_809 f (by omega)]
      change (List.range' 808 1 ++ List.range' (808+1) 1) ++
        [808+(1+1)] = List.range' 808 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 808) (n := 1+1)).symm

private theorem traversal_811 (fuel : Nat) (hf : 811 < fuel) :
    walk nodes fuel 811 = List.range' 811 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 811).rule = .bound .vertex 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_812 (fuel : Nat) (hf : 812 < fuel) :
    walk nodes fuel 812 = List.range' 812 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 812).rule = .bound .vertex 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_813 (fuel : Nat) (hf : 813 < fuel) :
    walk nodes fuel 813 = List.range' 813 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 813).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_814 (fuel : Nat) (hf : 814 < fuel) :
    walk nodes fuel 814 = List.range' 812 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 814).rule = .split 1 (5/8) 812 813 := by rfl
      simp only [walk, hr]
      rw [traversal_812 f (by omega), traversal_813 f (by omega)]
      change (List.range' 812 1 ++ List.range' (812+1) 1) ++
        [812+(1+1)] = List.range' 812 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 812) (n := 1+1)).symm

private theorem traversal_815 (fuel : Nat) (hf : 815 < fuel) :
    walk nodes fuel 815 = List.range' 811 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 815).rule = .split 0 (1/5) 811 814 := by rfl
      simp only [walk, hr]
      rw [traversal_811 f (by omega), traversal_814 f (by omega)]
      change (List.range' 811 1 ++ List.range' (811+1) 3) ++
        [811+(1+3)] = List.range' 811 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 811) (n := 1+3)).symm

private theorem traversal_816 (fuel : Nat) (hf : 816 < fuel) :
    walk nodes fuel 816 = List.range' 808 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 816).rule = .split 3 (3/4) 810 815 := by rfl
      simp only [walk, hr]
      rw [traversal_810 f (by omega), traversal_815 f (by omega)]
      change (List.range' 808 3 ++ List.range' (808+3) 5) ++
        [808+(3+5)] = List.range' 808 ((3+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 808) (n := 3+5)).symm

private theorem traversal_817 (fuel : Nat) (hf : 817 < fuel) :
    walk nodes fuel 817 = List.range' 817 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 817).rule = .infeasible 1 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_818 (fuel : Nat) (hf : 818 < fuel) :
    walk nodes fuel 818 = List.range' 818 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 818).rule = .bound .rightEnd 0 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_819 (fuel : Nat) (hf : 819 < fuel) :
    walk nodes fuel 819 = List.range' 819 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 819).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_820 (fuel : Nat) (hf : 820 < fuel) :
    walk nodes fuel 820 = List.range' 818 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 820).rule = .split 1 (5/8) 818 819 := by rfl
      simp only [walk, hr]
      rw [traversal_818 f (by omega), traversal_819 f (by omega)]
      change (List.range' 818 1 ++ List.range' (818+1) 1) ++
        [818+(1+1)] = List.range' 818 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 818) (n := 1+1)).symm

private theorem traversal_821 (fuel : Nat) (hf : 821 < fuel) :
    walk nodes fuel 821 = List.range' 821 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 821).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_822 (fuel : Nat) (hf : 822 < fuel) :
    walk nodes fuel 822 = List.range' 818 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 822).rule = .split 0 (1/5) 820 821 := by rfl
      simp only [walk, hr]
      rw [traversal_820 f (by omega), traversal_821 f (by omega)]
      change (List.range' 818 3 ++ List.range' (818+3) 1) ++
        [818+(3+1)] = List.range' 818 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 818) (n := 3+1)).symm

private theorem traversal_823 (fuel : Nat) (hf : 823 < fuel) :
    walk nodes fuel 823 = List.range' 817 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 823).rule = .split 3 (3/4) 817 822 := by rfl
      simp only [walk, hr]
      rw [traversal_817 f (by omega), traversal_822 f (by omega)]
      change (List.range' 817 1 ++ List.range' (817+1) 5) ++
        [817+(1+5)] = List.range' 817 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 817) (n := 1+5)).symm

private theorem traversal_824 (fuel : Nat) (hf : 824 < fuel) :
    walk nodes fuel 824 = List.range' 808 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 824).rule = .split 2 (15/4) 816 823 := by rfl
      simp only [walk, hr]
      rw [traversal_816 f (by omega), traversal_823 f (by omega)]
      change (List.range' 808 9 ++ List.range' (808+9) 7) ++
        [808+(9+7)] = List.range' 808 ((9+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 808) (n := 9+7)).symm

private theorem traversal_825 (fuel : Nat) (hf : 825 < fuel) :
    walk nodes fuel 825 = List.range' 825 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 825).rule = .bound .leftEnd 2 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_826 (fuel : Nat) (hf : 826 < fuel) :
    walk nodes fuel 826 = List.range' 826 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 826).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_827 (fuel : Nat) (hf : 827 < fuel) :
    walk nodes fuel 827 = List.range' 825 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 827).rule = .split 3 (3/4) 825 826 := by rfl
      simp only [walk, hr]
      rw [traversal_825 f (by omega), traversal_826 f (by omega)]
      change (List.range' 825 1 ++ List.range' (825+1) 1) ++
        [825+(1+1)] = List.range' 825 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 825) (n := 1+1)).symm

private theorem traversal_828 (fuel : Nat) (hf : 828 < fuel) :
    walk nodes fuel 828 = List.range' 828 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 828).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_829 (fuel : Nat) (hf : 829 < fuel) :
    walk nodes fuel 829 = List.range' 825 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 829).rule = .split 2 (15/4) 827 828 := by rfl
      simp only [walk, hr]
      rw [traversal_827 f (by omega), traversal_828 f (by omega)]
      change (List.range' 825 3 ++ List.range' (825+3) 1) ++
        [825+(3+1)] = List.range' 825 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 825) (n := 3+1)).symm

private theorem traversal_830 (fuel : Nat) (hf : 830 < fuel) :
    walk nodes fuel 830 = List.range' 808 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 830).rule = .split 1 (5/4) 824 829 := by rfl
      simp only [walk, hr]
      rw [traversal_824 f (by omega), traversal_829 f (by omega)]
      change (List.range' 808 17 ++ List.range' (808+17) 5) ++
        [808+(17+5)] = List.range' 808 ((17+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 808) (n := 17+5)).symm

private theorem traversal_831 (fuel : Nat) (hf : 831 < fuel) :
    walk nodes fuel 831 = List.range' 831 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 831).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_832 (fuel : Nat) (hf : 832 < fuel) :
    walk nodes fuel 832 = List.range' 808 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 832).rule = .split 0 (3/10) 830 831 := by rfl
      simp only [walk, hr]
      rw [traversal_830 f (by omega), traversal_831 f (by omega)]
      change (List.range' 808 23 ++ List.range' (808+23) 1) ++
        [808+(23+1)] = List.range' 808 ((23+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 808) (n := 23+1)).symm

private theorem traversal_833 (fuel : Nat) (hf : 833 < fuel) :
    walk nodes fuel 833 = List.range' 833 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 833).rule = .bound .vertex 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_834 (fuel : Nat) (hf : 834 < fuel) :
    walk nodes fuel 834 = List.range' 834 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 834).rule = .bound .vertex 6 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_835 (fuel : Nat) (hf : 835 < fuel) :
    walk nodes fuel 835 = List.range' 835 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 835).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_836 (fuel : Nat) (hf : 836 < fuel) :
    walk nodes fuel 836 = List.range' 834 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 836).rule = .split 2 (25/8) 834 835 := by rfl
      simp only [walk, hr]
      rw [traversal_834 f (by omega), traversal_835 f (by omega)]
      change (List.range' 834 1 ++ List.range' (834+1) 1) ++
        [834+(1+1)] = List.range' 834 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 834) (n := 1+1)).symm

private theorem traversal_837 (fuel : Nat) (hf : 837 < fuel) :
    walk nodes fuel 837 = List.range' 837 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 837).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_838 (fuel : Nat) (hf : 838 < fuel) :
    walk nodes fuel 838 = List.range' 834 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 838).rule = .split 1 (5/8) 836 837 := by rfl
      simp only [walk, hr]
      rw [traversal_836 f (by omega), traversal_837 f (by omega)]
      change (List.range' 834 3 ++ List.range' (834+3) 1) ++
        [834+(3+1)] = List.range' 834 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 834) (n := 3+1)).symm

private theorem traversal_839 (fuel : Nat) (hf : 839 < fuel) :
    walk nodes fuel 839 = List.range' 833 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 839).rule = .split 0 (1/5) 833 838 := by rfl
      simp only [walk, hr]
      rw [traversal_833 f (by omega), traversal_838 f (by omega)]
      change (List.range' 833 1 ++ List.range' (833+1) 5) ++
        [833+(1+5)] = List.range' 833 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 833) (n := 1+5)).symm

private theorem traversal_840 (fuel : Nat) (hf : 840 < fuel) :
    walk nodes fuel 840 = List.range' 840 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 840).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_841 (fuel : Nat) (hf : 841 < fuel) :
    walk nodes fuel 841 = List.range' 841 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 841).rule = .bound .vertex 8 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_842 (fuel : Nat) (hf : 842 < fuel) :
    walk nodes fuel 842 = List.range' 842 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 842).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_843 (fuel : Nat) (hf : 843 < fuel) :
    walk nodes fuel 843 = List.range' 841 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 843).rule = .split 0 (3/20) 841 842 := by rfl
      simp only [walk, hr]
      rw [traversal_841 f (by omega), traversal_842 f (by omega)]
      change (List.range' 841 1 ++ List.range' (841+1) 1) ++
        [841+(1+1)] = List.range' 841 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 841) (n := 1+1)).symm

private theorem traversal_844 (fuel : Nat) (hf : 844 < fuel) :
    walk nodes fuel 844 = List.range' 844 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 844).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_845 (fuel : Nat) (hf : 845 < fuel) :
    walk nodes fuel 845 = List.range' 841 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 845).rule = .split 3 (21/8) 843 844 := by rfl
      simp only [walk, hr]
      rw [traversal_843 f (by omega), traversal_844 f (by omega)]
      change (List.range' 841 3 ++ List.range' (841+3) 1) ++
        [841+(3+1)] = List.range' 841 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 841) (n := 3+1)).symm

private theorem traversal_846 (fuel : Nat) (hf : 846 < fuel) :
    walk nodes fuel 846 = List.range' 840 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 846).rule = .split 2 (25/8) 840 845 := by rfl
      simp only [walk, hr]
      rw [traversal_840 f (by omega), traversal_845 f (by omega)]
      change (List.range' 840 1 ++ List.range' (840+1) 5) ++
        [840+(1+5)] = List.range' 840 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 840) (n := 1+5)).symm

private theorem traversal_847 (fuel : Nat) (hf : 847 < fuel) :
    walk nodes fuel 847 = List.range' 847 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 847).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_848 (fuel : Nat) (hf : 848 < fuel) :
    walk nodes fuel 848 = List.range' 848 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 848).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_849 (fuel : Nat) (hf : 849 < fuel) :
    walk nodes fuel 849 = List.range' 847 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 849).rule = .split 2 (25/8) 847 848 := by rfl
      simp only [walk, hr]
      rw [traversal_847 f (by omega), traversal_848 f (by omega)]
      change (List.range' 847 1 ++ List.range' (847+1) 1) ++
        [847+(1+1)] = List.range' 847 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 847) (n := 1+1)).symm

private theorem traversal_850 (fuel : Nat) (hf : 850 < fuel) :
    walk nodes fuel 850 = List.range' 840 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 850).rule = .split 1 (5/8) 846 849 := by rfl
      simp only [walk, hr]
      rw [traversal_846 f (by omega), traversal_849 f (by omega)]
      change (List.range' 840 7 ++ List.range' (840+7) 3) ++
        [840+(7+3)] = List.range' 840 ((7+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 840) (n := 7+3)).symm

private theorem traversal_851 (fuel : Nat) (hf : 851 < fuel) :
    walk nodes fuel 851 = List.range' 851 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 851).rule = .bound .vertex 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_852 (fuel : Nat) (hf : 852 < fuel) :
    walk nodes fuel 852 = List.range' 852 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 852).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_853 (fuel : Nat) (hf : 853 < fuel) :
    walk nodes fuel 853 = List.range' 851 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 853).rule = .split 1 (5/8) 851 852 := by rfl
      simp only [walk, hr]
      rw [traversal_851 f (by omega), traversal_852 f (by omega)]
      change (List.range' 851 1 ++ List.range' (851+1) 1) ++
        [851+(1+1)] = List.range' 851 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 851) (n := 1+1)).symm

private theorem traversal_854 (fuel : Nat) (hf : 854 < fuel) :
    walk nodes fuel 854 = List.range' 840 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 854).rule = .split 0 (1/5) 850 853 := by rfl
      simp only [walk, hr]
      rw [traversal_850 f (by omega), traversal_853 f (by omega)]
      change (List.range' 840 11 ++ List.range' (840+11) 3) ++
        [840+(11+3)] = List.range' 840 ((11+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 840) (n := 11+3)).symm

private theorem traversal_855 (fuel : Nat) (hf : 855 < fuel) :
    walk nodes fuel 855 = List.range' 833 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 855).rule = .split 3 (9/4) 839 854 := by rfl
      simp only [walk, hr]
      rw [traversal_839 f (by omega), traversal_854 f (by omega)]
      change (List.range' 833 7 ++ List.range' (833+7) 15) ++
        [833+(7+15)] = List.range' 833 ((7+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 833) (n := 7+15)).symm

private theorem traversal_856 (fuel : Nat) (hf : 856 < fuel) :
    walk nodes fuel 856 = List.range' 856 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 856).rule = .bound .vertex 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_857 (fuel : Nat) (hf : 857 < fuel) :
    walk nodes fuel 857 = List.range' 857 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 857).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_858 (fuel : Nat) (hf : 858 < fuel) :
    walk nodes fuel 858 = List.range' 856 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 858).rule = .split 0 (1/5) 856 857 := by rfl
      simp only [walk, hr]
      rw [traversal_856 f (by omega), traversal_857 f (by omega)]
      change (List.range' 856 1 ++ List.range' (856+1) 1) ++
        [856+(1+1)] = List.range' 856 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 856) (n := 1+1)).symm

private theorem traversal_859 (fuel : Nat) (hf : 859 < fuel) :
    walk nodes fuel 859 = List.range' 859 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 859).rule = .bound .vertex 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_860 (fuel : Nat) (hf : 860 < fuel) :
    walk nodes fuel 860 = List.range' 856 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 860).rule = .split 3 (9/4) 858 859 := by rfl
      simp only [walk, hr]
      rw [traversal_858 f (by omega), traversal_859 f (by omega)]
      change (List.range' 856 3 ++ List.range' (856+3) 1) ++
        [856+(3+1)] = List.range' 856 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 856) (n := 3+1)).symm

private theorem traversal_861 (fuel : Nat) (hf : 861 < fuel) :
    walk nodes fuel 861 = List.range' 833 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 861).rule = .split 2 (15/4) 855 860 := by rfl
      simp only [walk, hr]
      rw [traversal_855 f (by omega), traversal_860 f (by omega)]
      change (List.range' 833 23 ++ List.range' (833+23) 5) ++
        [833+(23+5)] = List.range' 833 ((23+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 833) (n := 23+5)).symm

private theorem traversal_862 (fuel : Nat) (hf : 862 < fuel) :
    walk nodes fuel 862 = List.range' 862 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 862).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_863 (fuel : Nat) (hf : 863 < fuel) :
    walk nodes fuel 863 = List.range' 863 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 863).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_864 (fuel : Nat) (hf : 864 < fuel) :
    walk nodes fuel 864 = List.range' 862 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 864).rule = .split 2 (15/4) 862 863 := by rfl
      simp only [walk, hr]
      rw [traversal_862 f (by omega), traversal_863 f (by omega)]
      change (List.range' 862 1 ++ List.range' (862+1) 1) ++
        [862+(1+1)] = List.range' 862 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 862) (n := 1+1)).symm

private theorem traversal_865 (fuel : Nat) (hf : 865 < fuel) :
    walk nodes fuel 865 = List.range' 833 33 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 865).rule = .split 1 (5/4) 861 864 := by rfl
      simp only [walk, hr]
      rw [traversal_861 f (by omega), traversal_864 f (by omega)]
      change (List.range' 833 29 ++ List.range' (833+29) 3) ++
        [833+(29+3)] = List.range' 833 ((29+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 833) (n := 29+3)).symm

private theorem traversal_866 (fuel : Nat) (hf : 866 < fuel) :
    walk nodes fuel 866 = List.range' 866 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 866).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_867 (fuel : Nat) (hf : 867 < fuel) :
    walk nodes fuel 867 = List.range' 833 35 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 867).rule = .split 0 (3/10) 865 866 := by rfl
      simp only [walk, hr]
      rw [traversal_865 f (by omega), traversal_866 f (by omega)]
      change (List.range' 833 33 ++ List.range' (833+33) 1) ++
        [833+(33+1)] = List.range' 833 ((33+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 833) (n := 33+1)).symm

private theorem traversal_868 (fuel : Nat) (hf : 868 < fuel) :
    walk nodes fuel 868 = List.range' 808 61 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 868).rule = .split 3 (3/2) 832 867 := by rfl
      simp only [walk, hr]
      rw [traversal_832 f (by omega), traversal_867 f (by omega)]
      change (List.range' 808 25 ++ List.range' (808+25) 35) ++
        [808+(25+35)] = List.range' 808 ((25+35)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 808) (n := 25+35)).symm

theorem traversal_869 (fuel : Nat) (hf : 869 < fuel) :
    walk nodes fuel 869 = List.range' 733 137 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 869).rule = .split 2 (5/2) 807 868 := by rfl
      simp only [walk, hr]
      rw [traversal_807 f (by omega), traversal_868 f (by omega)]
      change (List.range' 733 75 ++ List.range' (733+75) 61) ++
        [733+(75+61)] = List.range' 733 ((75+61)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 733) (n := 75+61)).symm

theorem traversal_870 (fuel : Nat) (hf : 870 < fuel) :
    walk nodes fuel 870 = List.range' 870 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 870).rule = .bound .leftEnd 1 0 0 := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
