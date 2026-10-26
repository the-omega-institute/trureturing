/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart11
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart11
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart11.traversal_796,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart11.traversal_797,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart11.traversal_804,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart11.traversal_805
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart09
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart10
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_740 (fuel : Nat) (hf : 740 < fuel) :
    walk nodes fuel 740 = List.range' 740 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 740).rule = .bound .leftEnd 1 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_741 (fuel : Nat) (hf : 741 < fuel) :
    walk nodes fuel 741 = List.range' 741 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 741).rule = .bound .leftEnd 2 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_742 (fuel : Nat) (hf : 742 < fuel) :
    walk nodes fuel 742 = List.range' 740 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 742).rule = .split 2 (9099/4096) 740 741 := by rfl
      simp only [walk, hr]
      rw [traversal_740 f (by omega), traversal_741 f (by omega)]
      change (List.range' 740 1 ++ List.range' (740+1) 1) ++
        [740+(1+1)] = List.range' 740 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 740) (n := 1+1)).symm

private theorem traversal_743 (fuel : Nat) (hf : 743 < fuel) :
    walk nodes fuel 743 = List.range' 743 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 743).rule = .bound .leftEnd 1 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_744 (fuel : Nat) (hf : 744 < fuel) :
    walk nodes fuel 744 = List.range' 740 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 744).rule = .split 1 (2345/1024) 742 743 := by rfl
      simp only [walk, hr]
      rw [traversal_742 f (by omega), traversal_743 f (by omega)]
      change (List.range' 740 3 ++ List.range' (740+3) 1) ++
        [740+(3+1)] = List.range' 740 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 740) (n := 3+1)).symm

private theorem traversal_745 (fuel : Nat) (hf : 745 < fuel) :
    walk nodes fuel 745 = List.range' 703 43 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 745).rule = .split 0 (1/1280) 739 744 := by rfl
      simp only [walk, hr]
      rw [traversal_739 f (by omega), traversal_744 f (by omega)]
      change (List.range' 703 37 ++ List.range' (703+37) 5) ++
        [703+(37+5)] = List.range' 703 ((37+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 703) (n := 37+5)).symm

private theorem traversal_746 (fuel : Nat) (hf : 746 < fuel) :
    walk nodes fuel 746 = List.range' 702 45 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 746).rule = .split 3 (453/512) 702 745 := by rfl
      simp only [walk, hr]
      rw [traversal_702 f (by omega), traversal_745 f (by omega)]
      change (List.range' 702 1 ++ List.range' (702+1) 43) ++
        [702+(1+43)] = List.range' 702 ((1+43)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 702) (n := 1+43)).symm

private theorem traversal_747 (fuel : Nat) (hf : 747 < fuel) :
    walk nodes fuel 747 = List.range' 747 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 747).rule = .bound .leftEnd 2 (3271/6144) (246195/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_748 (fuel : Nat) (hf : 748 < fuel) :
    walk nodes fuel 748 = List.range' 748 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 748).rule = .bound .leftEnd 2 (1631/3072) (493749/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_749 (fuel : Nat) (hf : 749 < fuel) :
    walk nodes fuel 749 = List.range' 749 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 749).rule = .bound .leftEnd 8 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_750 (fuel : Nat) (hf : 750 < fuel) :
    walk nodes fuel 750 = List.range' 750 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 750).rule = .bound .leftEnd 2 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_751 (fuel : Nat) (hf : 751 < fuel) :
    walk nodes fuel 751 = List.range' 749 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 751).rule = .split 2 (18255/8192) 749 750 := by rfl
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
      have hr : (node nodes 752).rule = .bound .leftEnd 2 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_753 (fuel : Nat) (hf : 753 < fuel) :
    walk nodes fuel 753 = List.range' 749 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 753).rule = .split 1 (4685/2048) 751 752 := by rfl
      simp only [walk, hr]
      rw [traversal_751 f (by omega), traversal_752 f (by omega)]
      change (List.range' 749 3 ++ List.range' (749+3) 1) ++
        [749+(3+1)] = List.range' 749 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 749) (n := 3+1)).symm

private theorem traversal_754 (fuel : Nat) (hf : 754 < fuel) :
    walk nodes fuel 754 = List.range' 754 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 754).rule = .bound .leftEnd 2 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_755 (fuel : Nat) (hf : 755 < fuel) :
    walk nodes fuel 755 = List.range' 749 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 755).rule = .split 0 (1/2560) 753 754 := by rfl
      simp only [walk, hr]
      rw [traversal_753 f (by omega), traversal_754 f (by omega)]
      change (List.range' 749 5 ++ List.range' (749+5) 1) ++
        [749+(5+1)] = List.range' 749 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 749) (n := 5+1)).symm

private theorem traversal_756 (fuel : Nat) (hf : 756 < fuel) :
    walk nodes fuel 756 = List.range' 748 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 756).rule = .split 3 (909/1024) 748 755 := by rfl
      simp only [walk, hr]
      rw [traversal_748 f (by omega), traversal_755 f (by omega)]
      change (List.range' 748 1 ++ List.range' (748+1) 7) ++
        [748+(1+7)] = List.range' 748 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 748) (n := 1+7)).symm

private theorem traversal_757 (fuel : Nat) (hf : 757 < fuel) :
    walk nodes fuel 757 = List.range' 757 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 757).rule = .bound .leftEnd 2 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_758 (fuel : Nat) (hf : 758 < fuel) :
    walk nodes fuel 758 = List.range' 748 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 758).rule = .split 2 (9137/4096) 756 757 := by rfl
      simp only [walk, hr]
      rw [traversal_756 f (by omega), traversal_757 f (by omega)]
      change (List.range' 748 9 ++ List.range' (748+9) 1) ++
        [748+(9+1)] = List.range' 748 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 748) (n := 9+1)).symm

private theorem traversal_759 (fuel : Nat) (hf : 759 < fuel) :
    walk nodes fuel 759 = List.range' 759 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 759).rule = .bound .leftEnd 2 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_760 (fuel : Nat) (hf : 760 < fuel) :
    walk nodes fuel 760 = List.range' 748 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 760).rule = .split 1 (2345/1024) 758 759 := by rfl
      simp only [walk, hr]
      rw [traversal_758 f (by omega), traversal_759 f (by omega)]
      change (List.range' 748 11 ++ List.range' (748+11) 1) ++
        [748+(11+1)] = List.range' 748 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 748) (n := 11+1)).symm

private theorem traversal_761 (fuel : Nat) (hf : 761 < fuel) :
    walk nodes fuel 761 = List.range' 761 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 761).rule = .bound .leftEnd 2 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_762 (fuel : Nat) (hf : 762 < fuel) :
    walk nodes fuel 762 = List.range' 748 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 762).rule = .split 0 (1/1280) 760 761 := by rfl
      simp only [walk, hr]
      rw [traversal_760 f (by omega), traversal_761 f (by omega)]
      change (List.range' 748 13 ++ List.range' (748+13) 1) ++
        [748+(13+1)] = List.range' 748 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 748) (n := 13+1)).symm

private theorem traversal_763 (fuel : Nat) (hf : 763 < fuel) :
    walk nodes fuel 763 = List.range' 747 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 763).rule = .split 3 (453/512) 747 762 := by rfl
      simp only [walk, hr]
      rw [traversal_747 f (by omega), traversal_762 f (by omega)]
      change (List.range' 747 1 ++ List.range' (747+1) 15) ++
        [747+(1+15)] = List.range' 747 ((1+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 747) (n := 1+15)).symm

private theorem traversal_764 (fuel : Nat) (hf : 764 < fuel) :
    walk nodes fuel 764 = List.range' 702 63 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 764).rule = .split 2 (4559/2048) 746 763 := by rfl
      simp only [walk, hr]
      rw [traversal_746 f (by omega), traversal_763 f (by omega)]
      change (List.range' 702 45 ++ List.range' (702+45) 17) ++
        [702+(45+17)] = List.range' 702 ((45+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 702) (n := 45+17)).symm

private theorem traversal_765 (fuel : Nat) (hf : 765 < fuel) :
    walk nodes fuel 765 = List.range' 765 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 765).rule = .bound .leftEnd 2 (3271/6144) (246195/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_766 (fuel : Nat) (hf : 766 < fuel) :
    walk nodes fuel 766 = List.range' 766 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 766).rule = .bound .leftEnd 1 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_767 (fuel : Nat) (hf : 767 < fuel) :
    walk nodes fuel 767 = List.range' 767 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 767).rule = .bound .leftEnd 2 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_768 (fuel : Nat) (hf : 768 < fuel) :
    walk nodes fuel 768 = List.range' 766 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 768).rule = .split 2 (9099/4096) 766 767 := by rfl
      simp only [walk, hr]
      rw [traversal_766 f (by omega), traversal_767 f (by omega)]
      change (List.range' 766 1 ++ List.range' (766+1) 1) ++
        [766+(1+1)] = List.range' 766 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 766) (n := 1+1)).symm

private theorem traversal_769 (fuel : Nat) (hf : 769 < fuel) :
    walk nodes fuel 769 = List.range' 769 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 769).rule = .bound .leftEnd 1 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_770 (fuel : Nat) (hf : 770 < fuel) :
    walk nodes fuel 770 = List.range' 766 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 770).rule = .split 1 (2355/1024) 768 769 := by rfl
      simp only [walk, hr]
      rw [traversal_768 f (by omega), traversal_769 f (by omega)]
      change (List.range' 766 3 ++ List.range' (766+3) 1) ++
        [766+(3+1)] = List.range' 766 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 766) (n := 3+1)).symm

private theorem traversal_771 (fuel : Nat) (hf : 771 < fuel) :
    walk nodes fuel 771 = List.range' 771 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 771).rule = .bound .leftEnd 1 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_772 (fuel : Nat) (hf : 772 < fuel) :
    walk nodes fuel 772 = List.range' 766 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 772).rule = .split 0 (1/1280) 770 771 := by rfl
      simp only [walk, hr]
      rw [traversal_770 f (by omega), traversal_771 f (by omega)]
      change (List.range' 766 5 ++ List.range' (766+5) 1) ++
        [766+(5+1)] = List.range' 766 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 766) (n := 5+1)).symm

private theorem traversal_773 (fuel : Nat) (hf : 773 < fuel) :
    walk nodes fuel 773 = List.range' 765 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 773).rule = .split 3 (453/512) 765 772 := by rfl
      simp only [walk, hr]
      rw [traversal_765 f (by omega), traversal_772 f (by omega)]
      change (List.range' 765 1 ++ List.range' (765+1) 7) ++
        [765+(1+7)] = List.range' 765 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 765) (n := 1+7)).symm

private theorem traversal_774 (fuel : Nat) (hf : 774 < fuel) :
    walk nodes fuel 774 = List.range' 774 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 774).rule = .bound .leftEnd 2 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_775 (fuel : Nat) (hf : 775 < fuel) :
    walk nodes fuel 775 = List.range' 765 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 775).rule = .split 2 (4559/2048) 773 774 := by rfl
      simp only [walk, hr]
      rw [traversal_773 f (by omega), traversal_774 f (by omega)]
      change (List.range' 765 9 ++ List.range' (765+9) 1) ++
        [765+(9+1)] = List.range' 765 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 765) (n := 9+1)).symm

private theorem traversal_776 (fuel : Nat) (hf : 776 < fuel) :
    walk nodes fuel 776 = List.range' 702 75 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 776).rule = .split 1 (1175/512) 764 775 := by rfl
      simp only [walk, hr]
      rw [traversal_764 f (by omega), traversal_775 f (by omega)]
      change (List.range' 702 63 ++ List.range' (702+63) 11) ++
        [702+(63+11)] = List.range' 702 ((63+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 702) (n := 63+11)).symm

private theorem traversal_777 (fuel : Nat) (hf : 777 < fuel) :
    walk nodes fuel 777 = List.range' 777 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 777).rule = .bound .leftEnd 2 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_778 (fuel : Nat) (hf : 778 < fuel) :
    walk nodes fuel 778 = List.range' 702 77 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 778).rule = .split 0 (1/640) 776 777 := by rfl
      simp only [walk, hr]
      rw [traversal_776 f (by omega), traversal_777 f (by omega)]
      change (List.range' 702 75 ++ List.range' (702+75) 1) ++
        [702+(75+1)] = List.range' 702 ((75+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 702) (n := 75+1)).symm

private theorem traversal_779 (fuel : Nat) (hf : 779 < fuel) :
    walk nodes fuel 779 = List.range' 701 79 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 779).rule = .split 3 (225/256) 701 778 := by rfl
      simp only [walk, hr]
      rw [traversal_701 f (by omega), traversal_778 f (by omega)]
      change (List.range' 701 1 ++ List.range' (701+1) 77) ++
        [701+(1+77)] = List.range' 701 ((1+77)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 701) (n := 1+77)).symm

private theorem traversal_780 (fuel : Nat) (hf : 780 < fuel) :
    walk nodes fuel 780 = List.range' 780 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 780).rule = .bound .leftEnd 2 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_781 (fuel : Nat) (hf : 781 < fuel) :
    walk nodes fuel 781 = List.range' 701 81 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 781).rule = .split 2 (2289/1024) 779 780 := by rfl
      simp only [walk, hr]
      rw [traversal_779 f (by omega), traversal_780 f (by omega)]
      change (List.range' 701 79 ++ List.range' (701+79) 1) ++
        [701+(79+1)] = List.range' 701 ((79+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 701) (n := 79+1)).symm

private theorem traversal_782 (fuel : Nat) (hf : 782 < fuel) :
    walk nodes fuel 782 = List.range' 672 111 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 782).rule = .split 1 (585/256) 700 781 := by rfl
      simp only [walk, hr]
      rw [traversal_700 f (by omega), traversal_781 f (by omega)]
      change (List.range' 672 29 ++ List.range' (672+29) 81) ++
        [672+(29+81)] = List.range' 672 ((29+81)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 672) (n := 29+81)).symm

private theorem traversal_783 (fuel : Nat) (hf : 783 < fuel) :
    walk nodes fuel 783 = List.range' 783 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 783).rule = .bound .leftEnd 2 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_784 (fuel : Nat) (hf : 784 < fuel) :
    walk nodes fuel 784 = List.range' 784 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 784).rule = .bound .leftEnd 8 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_785 (fuel : Nat) (hf : 785 < fuel) :
    walk nodes fuel 785 = List.range' 785 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 785).rule = .bound .leftEnd 2 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_786 (fuel : Nat) (hf : 786 < fuel) :
    walk nodes fuel 786 = List.range' 784 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 786).rule = .split 1 (1165/512) 784 785 := by rfl
      simp only [walk, hr]
      rw [traversal_784 f (by omega), traversal_785 f (by omega)]
      change (List.range' 784 1 ++ List.range' (784+1) 1) ++
        [784+(1+1)] = List.range' 784 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 784) (n := 1+1)).symm

private theorem traversal_787 (fuel : Nat) (hf : 787 < fuel) :
    walk nodes fuel 787 = List.range' 787 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 787).rule = .bound .leftEnd 2 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_788 (fuel : Nat) (hf : 788 < fuel) :
    walk nodes fuel 788 = List.range' 784 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 788).rule = .split 0 (3/640) 786 787 := by rfl
      simp only [walk, hr]
      rw [traversal_786 f (by omega), traversal_787 f (by omega)]
      change (List.range' 784 3 ++ List.range' (784+3) 1) ++
        [784+(3+1)] = List.range' 784 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 784) (n := 3+1)).symm

private theorem traversal_789 (fuel : Nat) (hf : 789 < fuel) :
    walk nodes fuel 789 = List.range' 783 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 789).rule = .split 3 (225/256) 783 788 := by rfl
      simp only [walk, hr]
      rw [traversal_783 f (by omega), traversal_788 f (by omega)]
      change (List.range' 783 1 ++ List.range' (783+1) 5) ++
        [783+(1+5)] = List.range' 783 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 783) (n := 1+5)).symm

private theorem traversal_790 (fuel : Nat) (hf : 790 < fuel) :
    walk nodes fuel 790 = List.range' 790 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 790).rule = .bound .leftEnd 2 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_791 (fuel : Nat) (hf : 791 < fuel) :
    walk nodes fuel 791 = List.range' 783 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 791).rule = .split 2 (2289/1024) 789 790 := by rfl
      simp only [walk, hr]
      rw [traversal_789 f (by omega), traversal_790 f (by omega)]
      change (List.range' 783 7 ++ List.range' (783+7) 1) ++
        [783+(7+1)] = List.range' 783 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 783) (n := 7+1)).symm

private theorem traversal_792 (fuel : Nat) (hf : 792 < fuel) :
    walk nodes fuel 792 = List.range' 792 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 792).rule = .bound .leftEnd 2 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_793 (fuel : Nat) (hf : 793 < fuel) :
    walk nodes fuel 793 = List.range' 783 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 793).rule = .split 1 (585/256) 791 792 := by rfl
      simp only [walk, hr]
      rw [traversal_791 f (by omega), traversal_792 f (by omega)]
      change (List.range' 783 9 ++ List.range' (783+9) 1) ++
        [783+(9+1)] = List.range' 783 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 783) (n := 9+1)).symm

private theorem traversal_794 (fuel : Nat) (hf : 794 < fuel) :
    walk nodes fuel 794 = List.range' 672 123 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 794).rule = .split 0 (1/320) 782 793 := by rfl
      simp only [walk, hr]
      rw [traversal_782 f (by omega), traversal_793 f (by omega)]
      change (List.range' 672 111 ++ List.range' (672+111) 11) ++
        [672+(111+11)] = List.range' 672 ((111+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 672) (n := 111+11)).symm

private theorem traversal_795 (fuel : Nat) (hf : 795 < fuel) :
    walk nodes fuel 795 = List.range' 671 125 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 795).rule = .split 3 (111/128) 671 794 := by rfl
      simp only [walk, hr]
      rw [traversal_671 f (by omega), traversal_794 f (by omega)]
      change (List.range' 671 1 ++ List.range' (671+1) 123) ++
        [671+(1+123)] = List.range' 671 ((1+123)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 671) (n := 1+123)).symm

theorem traversal_796 (fuel : Nat) (hf : 796 < fuel) :
    walk nodes fuel 796 = List.range' 602 195 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 796).rule = .split 2 (1135/512) 670 795 := by rfl
      simp only [walk, hr]
      rw [traversal_670 f (by omega), traversal_795 f (by omega)]
      change (List.range' 602 69 ++ List.range' (602+69) 125) ++
        [602+(69+125)] = List.range' 602 ((69+125)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 602) (n := 69+125)).symm

theorem traversal_797 (fuel : Nat) (hf : 797 < fuel) :
    walk nodes fuel 797 = List.range' 797 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 797).rule = .bound .leftEnd 2 (6643/12288) (242441/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_798 (fuel : Nat) (hf : 798 < fuel) :
    walk nodes fuel 798 = List.range' 798 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 798).rule = .bound .leftEnd 2 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_799 (fuel : Nat) (hf : 799 < fuel) :
    walk nodes fuel 799 = List.range' 799 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 799).rule = .bound .leftEnd 1 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_800 (fuel : Nat) (hf : 800 < fuel) :
    walk nodes fuel 800 = List.range' 798 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 800).rule = .split 3 (225/256) 798 799 := by rfl
      simp only [walk, hr]
      rw [traversal_798 f (by omega), traversal_799 f (by omega)]
      change (List.range' 798 1 ++ List.range' (798+1) 1) ++
        [798+(1+1)] = List.range' 798 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 798) (n := 1+1)).symm

private theorem traversal_801 (fuel : Nat) (hf : 801 < fuel) :
    walk nodes fuel 801 = List.range' 801 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 801).rule = .bound .leftEnd 2 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_802 (fuel : Nat) (hf : 802 < fuel) :
    walk nodes fuel 802 = List.range' 802 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 802).rule = .bound .leftEnd 1 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_803 (fuel : Nat) (hf : 803 < fuel) :
    walk nodes fuel 803 = List.range' 801 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 803).rule = .split 3 (225/256) 801 802 := by rfl
      simp only [walk, hr]
      rw [traversal_801 f (by omega), traversal_802 f (by omega)]
      change (List.range' 801 1 ++ List.range' (801+1) 1) ++
        [801+(1+1)] = List.range' 801 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 801) (n := 1+1)).symm

theorem traversal_804 (fuel : Nat) (hf : 804 < fuel) :
    walk nodes fuel 804 = List.range' 798 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 804).rule = .split 2 (2251/1024) 800 803 := by rfl
      simp only [walk, hr]
      rw [traversal_800 f (by omega), traversal_803 f (by omega)]
      change (List.range' 798 3 ++ List.range' (798+3) 3) ++
        [798+(3+3)] = List.range' 798 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 798) (n := 3+3)).symm

theorem traversal_805 (fuel : Nat) (hf : 805 < fuel) :
    walk nodes fuel 805 = List.range' 805 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 805).rule = .bound .leftEnd 1 (4369/8192) (491505/1048576) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
