/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart12
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart12
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart12.traversal_820,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart12.traversal_827,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart12.traversal_828,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart12.traversal_829,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart12.traversal_866,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart12.traversal_871,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart12.traversal_872
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart11
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_806 (fuel : Nat) (hf : 806 < fuel) :
    walk nodes fuel 806 = List.range' 798 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 806).rule = .split 1 (595/256) 804 805 := by rfl
      simp only [walk, hr]
      rw [traversal_804 f (by omega), traversal_805 f (by omega)]
      change (List.range' 798 7 ++ List.range' (798+7) 1) ++
        [798+(7+1)] = List.range' 798 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 798) (n := 7+1)).symm

private theorem traversal_807 (fuel : Nat) (hf : 807 < fuel) :
    walk nodes fuel 807 = List.range' 807 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 807).rule = .bound .leftEnd 1 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_808 (fuel : Nat) (hf : 808 < fuel) :
    walk nodes fuel 808 = List.range' 798 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 808).rule = .split 0 (1/320) 806 807 := by rfl
      simp only [walk, hr]
      rw [traversal_806 f (by omega), traversal_807 f (by omega)]
      change (List.range' 798 9 ++ List.range' (798+9) 1) ++
        [798+(9+1)] = List.range' 798 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 798) (n := 9+1)).symm

private theorem traversal_809 (fuel : Nat) (hf : 809 < fuel) :
    walk nodes fuel 809 = List.range' 797 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 809).rule = .split 3 (111/128) 797 808 := by rfl
      simp only [walk, hr]
      rw [traversal_797 f (by omega), traversal_808 f (by omega)]
      change (List.range' 797 1 ++ List.range' (797+1) 11) ++
        [797+(1+11)] = List.range' 797 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 797) (n := 1+11)).symm

private theorem traversal_810 (fuel : Nat) (hf : 810 < fuel) :
    walk nodes fuel 810 = List.range' 810 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 810).rule = .bound .leftEnd 2 (26393/49152) (61013/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_811 (fuel : Nat) (hf : 811 < fuel) :
    walk nodes fuel 811 = List.range' 797 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 811).rule = .split 2 (1135/512) 809 810 := by rfl
      simp only [walk, hr]
      rw [traversal_809 f (by omega), traversal_810 f (by omega)]
      change (List.range' 797 13 ++ List.range' (797+13) 1) ++
        [797+(13+1)] = List.range' 797 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 797) (n := 13+1)).symm

private theorem traversal_812 (fuel : Nat) (hf : 812 < fuel) :
    walk nodes fuel 812 = List.range' 602 211 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 812).rule = .split 1 (295/128) 796 811 := by rfl
      simp only [walk, hr]
      rw [traversal_796 f (by omega), traversal_811 f (by omega)]
      change (List.range' 602 195 ++ List.range' (602+195) 15) ++
        [602+(195+15)] = List.range' 602 ((195+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 602) (n := 195+15)).symm

private theorem traversal_813 (fuel : Nat) (hf : 813 < fuel) :
    walk nodes fuel 813 = List.range' 813 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 813).rule = .bound .leftEnd 2 (6643/12288) (242441/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_814 (fuel : Nat) (hf : 814 < fuel) :
    walk nodes fuel 814 = List.range' 814 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 814).rule = .bound .leftEnd 1 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_815 (fuel : Nat) (hf : 815 < fuel) :
    walk nodes fuel 815 = List.range' 813 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 815).rule = .split 3 (111/128) 813 814 := by rfl
      simp only [walk, hr]
      rw [traversal_813 f (by omega), traversal_814 f (by omega)]
      change (List.range' 813 1 ++ List.range' (813+1) 1) ++
        [813+(1+1)] = List.range' 813 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 813) (n := 1+1)).symm

private theorem traversal_816 (fuel : Nat) (hf : 816 < fuel) :
    walk nodes fuel 816 = List.range' 816 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 816).rule = .bound .leftEnd 2 (26393/49152) (61013/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_817 (fuel : Nat) (hf : 817 < fuel) :
    walk nodes fuel 817 = List.range' 813 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 817).rule = .split 2 (1135/512) 815 816 := by rfl
      simp only [walk, hr]
      rw [traversal_815 f (by omega), traversal_816 f (by omega)]
      change (List.range' 813 3 ++ List.range' (813+3) 1) ++
        [813+(3+1)] = List.range' 813 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 813) (n := 3+1)).symm

private theorem traversal_818 (fuel : Nat) (hf : 818 < fuel) :
    walk nodes fuel 818 = List.range' 818 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 818).rule = .bound .leftEnd 2 (26393/49152) (61013/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_819 (fuel : Nat) (hf : 819 < fuel) :
    walk nodes fuel 819 = List.range' 813 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 819).rule = .split 1 (295/128) 817 818 := by rfl
      simp only [walk, hr]
      rw [traversal_817 f (by omega), traversal_818 f (by omega)]
      change (List.range' 813 5 ++ List.range' (813+5) 1) ++
        [813+(5+1)] = List.range' 813 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 813) (n := 5+1)).symm

theorem traversal_820 (fuel : Nat) (hf : 820 < fuel) :
    walk nodes fuel 820 = List.range' 602 219 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 820).rule = .split 0 (1/160) 812 819 := by rfl
      simp only [walk, hr]
      rw [traversal_812 f (by omega), traversal_819 f (by omega)]
      change (List.range' 602 211 ++ List.range' (602+211) 7) ++
        [602+(211+7)] = List.range' 602 ((211+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 602) (n := 211+7)).symm

private theorem traversal_821 (fuel : Nat) (hf : 821 < fuel) :
    walk nodes fuel 821 = List.range' 821 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 821).rule = .bound .leftEnd 8 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_822 (fuel : Nat) (hf : 822 < fuel) :
    walk nodes fuel 822 = List.range' 822 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 822).rule = .bound .leftEnd 1 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_823 (fuel : Nat) (hf : 823 < fuel) :
    walk nodes fuel 823 = List.range' 821 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 823).rule = .split 1 (585/256) 821 822 := by rfl
      simp only [walk, hr]
      rw [traversal_821 f (by omega), traversal_822 f (by omega)]
      change (List.range' 821 1 ++ List.range' (821+1) 1) ++
        [821+(1+1)] = List.range' 821 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 821) (n := 1+1)).symm

private theorem traversal_824 (fuel : Nat) (hf : 824 < fuel) :
    walk nodes fuel 824 = List.range' 824 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 824).rule = .bound .leftEnd 1 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_825 (fuel : Nat) (hf : 825 < fuel) :
    walk nodes fuel 825 = List.range' 821 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 825).rule = .split 0 (1/320) 823 824 := by rfl
      simp only [walk, hr]
      rw [traversal_823 f (by omega), traversal_824 f (by omega)]
      change (List.range' 821 3 ++ List.range' (821+3) 1) ++
        [821+(3+1)] = List.range' 821 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 821) (n := 3+1)).symm

private theorem traversal_826 (fuel : Nat) (hf : 826 < fuel) :
    walk nodes fuel 826 = List.range' 826 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 826).rule = .bound .leftEnd 1 (4257/8192) (504439/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_827 (fuel : Nat) (hf : 827 < fuel) :
    walk nodes fuel 827 = List.range' 821 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 827).rule = .split 3 (117/128) 825 826 := by rfl
      simp only [walk, hr]
      rw [traversal_825 f (by omega), traversal_826 f (by omega)]
      change (List.range' 821 5 ++ List.range' (821+5) 1) ++
        [821+(5+1)] = List.range' 821 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 821) (n := 5+1)).symm

theorem traversal_828 (fuel : Nat) (hf : 828 < fuel) :
    walk nodes fuel 828 = List.range' 828 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 828).rule = .bound .leftEnd 8 (12937/24576) (497965/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_829 (fuel : Nat) (hf : 829 < fuel) :
    walk nodes fuel 829 = List.range' 829 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 829).rule = .bound .leftEnd 8 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_830 (fuel : Nat) (hf : 830 < fuel) :
    walk nodes fuel 830 = List.range' 830 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 830).rule = .bound .leftEnd 8 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_831 (fuel : Nat) (hf : 831 < fuel) :
    walk nodes fuel 831 = List.range' 831 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 831).rule = .bound .leftEnd 8 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_832 (fuel : Nat) (hf : 832 < fuel) :
    walk nodes fuel 832 = List.range' 832 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 832).rule = .bound .leftEnd 8 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_833 (fuel : Nat) (hf : 833 < fuel) :
    walk nodes fuel 833 = List.range' 833 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 833).rule = .bound .leftEnd 2 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_834 (fuel : Nat) (hf : 834 < fuel) :
    walk nodes fuel 834 = List.range' 832 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 834).rule = .split 2 (18331/8192) 832 833 := by rfl
      simp only [walk, hr]
      rw [traversal_832 f (by omega), traversal_833 f (by omega)]
      change (List.range' 832 1 ++ List.range' (832+1) 1) ++
        [832+(1+1)] = List.range' 832 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 832) (n := 1+1)).symm

private theorem traversal_835 (fuel : Nat) (hf : 835 < fuel) :
    walk nodes fuel 835 = List.range' 831 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 835).rule = .split 1 (4675/2048) 831 834 := by rfl
      simp only [walk, hr]
      rw [traversal_831 f (by omega), traversal_834 f (by omega)]
      change (List.range' 831 1 ++ List.range' (831+1) 3) ++
        [831+(1+3)] = List.range' 831 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 831) (n := 1+3)).symm

private theorem traversal_836 (fuel : Nat) (hf : 836 < fuel) :
    walk nodes fuel 836 = List.range' 836 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 836).rule = .bound .leftEnd 2 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_837 (fuel : Nat) (hf : 837 < fuel) :
    walk nodes fuel 837 = List.range' 831 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 837).rule = .split 0 (1/2560) 835 836 := by rfl
      simp only [walk, hr]
      rw [traversal_835 f (by omega), traversal_836 f (by omega)]
      change (List.range' 831 5 ++ List.range' (831+5) 1) ++
        [831+(5+1)] = List.range' 831 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 831) (n := 5+1)).symm

private theorem traversal_838 (fuel : Nat) (hf : 838 < fuel) :
    walk nodes fuel 838 = List.range' 838 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 838).rule = .bound .leftEnd 8 (541/1024) (496183/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_839 (fuel : Nat) (hf : 839 < fuel) :
    walk nodes fuel 839 = List.range' 831 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 839).rule = .split 3 (915/1024) 837 838 := by rfl
      simp only [walk, hr]
      rw [traversal_837 f (by omega), traversal_838 f (by omega)]
      change (List.range' 831 7 ++ List.range' (831+7) 1) ++
        [831+(7+1)] = List.range' 831 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 831) (n := 7+1)).symm

private theorem traversal_840 (fuel : Nat) (hf : 840 < fuel) :
    walk nodes fuel 840 = List.range' 840 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 840).rule = .bound .leftEnd 2 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_841 (fuel : Nat) (hf : 841 < fuel) :
    walk nodes fuel 841 = List.range' 841 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 841).rule = .bound .leftEnd 8 (541/1024) (496183/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_842 (fuel : Nat) (hf : 842 < fuel) :
    walk nodes fuel 842 = List.range' 842 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 842).rule = .bound .leftEnd 3 (541/1024) (496183/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_843 (fuel : Nat) (hf : 843 < fuel) :
    walk nodes fuel 843 = List.range' 841 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 843).rule = .split 1 (4675/2048) 841 842 := by rfl
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
      have hr : (node nodes 844).rule = .bound .leftEnd 3 (541/1024) (496183/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_845 (fuel : Nat) (hf : 845 < fuel) :
    walk nodes fuel 845 = List.range' 841 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 845).rule = .split 0 (1/2560) 843 844 := by rfl
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
      have hr : (node nodes 846).rule = .split 3 (915/1024) 840 845 := by rfl
      simp only [walk, hr]
      rw [traversal_840 f (by omega), traversal_845 f (by omega)]
      change (List.range' 840 1 ++ List.range' (840+1) 5) ++
        [840+(1+5)] = List.range' 840 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 840) (n := 1+5)).symm

private theorem traversal_847 (fuel : Nat) (hf : 847 < fuel) :
    walk nodes fuel 847 = List.range' 831 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 847).rule = .split 2 (9175/4096) 839 846 := by rfl
      simp only [walk, hr]
      rw [traversal_839 f (by omega), traversal_846 f (by omega)]
      change (List.range' 831 9 ++ List.range' (831+9) 7) ++
        [831+(9+7)] = List.range' 831 ((9+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 831) (n := 9+7)).symm

private theorem traversal_848 (fuel : Nat) (hf : 848 < fuel) :
    walk nodes fuel 848 = List.range' 830 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 848).rule = .split 1 (2335/1024) 830 847 := by rfl
      simp only [walk, hr]
      rw [traversal_830 f (by omega), traversal_847 f (by omega)]
      change (List.range' 830 1 ++ List.range' (830+1) 17) ++
        [830+(1+17)] = List.range' 830 ((1+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 830) (n := 1+17)).symm

private theorem traversal_849 (fuel : Nat) (hf : 849 < fuel) :
    walk nodes fuel 849 = List.range' 849 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 849).rule = .bound .leftEnd 8 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_850 (fuel : Nat) (hf : 850 < fuel) :
    walk nodes fuel 850 = List.range' 850 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 850).rule = .bound .leftEnd 3 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_851 (fuel : Nat) (hf : 851 < fuel) :
    walk nodes fuel 851 = List.range' 849 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 851).rule = .split 1 (2335/1024) 849 850 := by rfl
      simp only [walk, hr]
      rw [traversal_849 f (by omega), traversal_850 f (by omega)]
      change (List.range' 849 1 ++ List.range' (849+1) 1) ++
        [849+(1+1)] = List.range' 849 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 849) (n := 1+1)).symm

private theorem traversal_852 (fuel : Nat) (hf : 852 < fuel) :
    walk nodes fuel 852 = List.range' 830 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 852).rule = .split 0 (1/1280) 848 851 := by rfl
      simp only [walk, hr]
      rw [traversal_848 f (by omega), traversal_851 f (by omega)]
      change (List.range' 830 19 ++ List.range' (830+19) 3) ++
        [830+(19+3)] = List.range' 830 ((19+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 830) (n := 19+3)).symm

private theorem traversal_853 (fuel : Nat) (hf : 853 < fuel) :
    walk nodes fuel 853 = List.range' 853 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 853).rule = .bound .leftEnd 8 (3239/6144) (248627/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_854 (fuel : Nat) (hf : 854 < fuel) :
    walk nodes fuel 854 = List.range' 854 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 854).rule = .bound .leftEnd 8 (3239/6144) (248627/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_855 (fuel : Nat) (hf : 855 < fuel) :
    walk nodes fuel 855 = List.range' 855 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 855).rule = .bound .leftEnd 8 (1621/3072) (496795/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_856 (fuel : Nat) (hf : 856 < fuel) :
    walk nodes fuel 856 = List.range' 856 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 856).rule = .bound .leftEnd 3 (1621/3072) (496795/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_857 (fuel : Nat) (hf : 857 < fuel) :
    walk nodes fuel 857 = List.range' 855 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 857).rule = .split 1 (4675/2048) 855 856 := by rfl
      simp only [walk, hr]
      rw [traversal_855 f (by omega), traversal_856 f (by omega)]
      change (List.range' 855 1 ++ List.range' (855+1) 1) ++
        [855+(1+1)] = List.range' 855 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 855) (n := 1+1)).symm

private theorem traversal_858 (fuel : Nat) (hf : 858 < fuel) :
    walk nodes fuel 858 = List.range' 858 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 858).rule = .bound .leftEnd 3 (1621/3072) (496795/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_859 (fuel : Nat) (hf : 859 < fuel) :
    walk nodes fuel 859 = List.range' 855 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 859).rule = .split 0 (1/2560) 857 858 := by rfl
      simp only [walk, hr]
      rw [traversal_857 f (by omega), traversal_858 f (by omega)]
      change (List.range' 855 3 ++ List.range' (855+3) 1) ++
        [855+(3+1)] = List.range' 855 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 855) (n := 3+1)).symm

private theorem traversal_860 (fuel : Nat) (hf : 860 < fuel) :
    walk nodes fuel 860 = List.range' 860 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 860).rule = .bound .leftEnd 8 (809/1536) (124429/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_861 (fuel : Nat) (hf : 861 < fuel) :
    walk nodes fuel 861 = List.range' 855 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 861).rule = .split 3 (921/1024) 859 860 := by rfl
      simp only [walk, hr]
      rw [traversal_859 f (by omega), traversal_860 f (by omega)]
      change (List.range' 855 5 ++ List.range' (855+5) 1) ++
        [855+(5+1)] = List.range' 855 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 855) (n := 5+1)).symm

private theorem traversal_862 (fuel : Nat) (hf : 862 < fuel) :
    walk nodes fuel 862 = List.range' 854 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 862).rule = .split 2 (9175/4096) 854 861 := by rfl
      simp only [walk, hr]
      rw [traversal_854 f (by omega), traversal_861 f (by omega)]
      change (List.range' 854 1 ++ List.range' (854+1) 7) ++
        [854+(1+7)] = List.range' 854 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 854) (n := 1+7)).symm

private theorem traversal_863 (fuel : Nat) (hf : 863 < fuel) :
    walk nodes fuel 863 = List.range' 853 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 863).rule = .split 1 (2335/1024) 853 862 := by rfl
      simp only [walk, hr]
      rw [traversal_853 f (by omega), traversal_862 f (by omega)]
      change (List.range' 853 1 ++ List.range' (853+1) 9) ++
        [853+(1+9)] = List.range' 853 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 853) (n := 1+9)).symm

private theorem traversal_864 (fuel : Nat) (hf : 864 < fuel) :
    walk nodes fuel 864 = List.range' 864 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 864).rule = .bound .leftEnd 8 (3239/6144) (248627/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_865 (fuel : Nat) (hf : 865 < fuel) :
    walk nodes fuel 865 = List.range' 853 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 865).rule = .split 0 (1/1280) 863 864 := by rfl
      simp only [walk, hr]
      rw [traversal_863 f (by omega), traversal_864 f (by omega)]
      change (List.range' 853 11 ++ List.range' (853+11) 1) ++
        [853+(11+1)] = List.range' 853 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 853) (n := 11+1)).symm

theorem traversal_866 (fuel : Nat) (hf : 866 < fuel) :
    walk nodes fuel 866 = List.range' 830 37 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 866).rule = .split 3 (459/512) 852 865 := by rfl
      simp only [walk, hr]
      rw [traversal_852 f (by omega), traversal_865 f (by omega)]
      change (List.range' 830 23 ++ List.range' (830+23) 13) ++
        [830+(23+13)] = List.range' 830 ((23+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 830) (n := 23+13)).symm

private theorem traversal_867 (fuel : Nat) (hf : 867 < fuel) :
    walk nodes fuel 867 = List.range' 867 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 867).rule = .bound .leftEnd 8 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_868 (fuel : Nat) (hf : 868 < fuel) :
    walk nodes fuel 868 = List.range' 868 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 868).rule = .bound .leftEnd 3 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_869 (fuel : Nat) (hf : 869 < fuel) :
    walk nodes fuel 869 = List.range' 867 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 869).rule = .split 2 (9213/4096) 867 868 := by rfl
      simp only [walk, hr]
      rw [traversal_867 f (by omega), traversal_868 f (by omega)]
      change (List.range' 867 1 ++ List.range' (867+1) 1) ++
        [867+(1+1)] = List.range' 867 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 867) (n := 1+1)).symm

private theorem traversal_870 (fuel : Nat) (hf : 870 < fuel) :
    walk nodes fuel 870 = List.range' 870 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 870).rule = .bound .leftEnd 3 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_871 (fuel : Nat) (hf : 871 < fuel) :
    walk nodes fuel 871 = List.range' 867 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 871).rule = .split 1 (2335/1024) 869 870 := by rfl
      simp only [walk, hr]
      rw [traversal_869 f (by omega), traversal_870 f (by omega)]
      change (List.range' 867 3 ++ List.range' (867+3) 1) ++
        [867+(3+1)] = List.range' 867 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 867) (n := 3+1)).symm

theorem traversal_872 (fuel : Nat) (hf : 872 < fuel) :
    walk nodes fuel 872 = List.range' 872 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 872).rule = .bound .leftEnd 2 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
