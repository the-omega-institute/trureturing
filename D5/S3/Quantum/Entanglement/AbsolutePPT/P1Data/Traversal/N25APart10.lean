/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart10
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart10
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart10.traversal_700,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart10.traversal_701,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart10.traversal_702,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart10.traversal_739
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_672 (fuel : Nat) (hf : 672 < fuel) :
    walk nodes fuel 672 = List.range' 672 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 672).rule = .bound .leftEnd 2 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_673 (fuel : Nat) (hf : 673 < fuel) :
    walk nodes fuel 673 = List.range' 673 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 673).rule = .bound .leftEnd 8 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_674 (fuel : Nat) (hf : 674 < fuel) :
    walk nodes fuel 674 = List.range' 674 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 674).rule = .bound .leftEnd 8 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_675 (fuel : Nat) (hf : 675 < fuel) :
    walk nodes fuel 675 = List.range' 675 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 675).rule = .bound .leftEnd 2 (3271/6144) (246195/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_676 (fuel : Nat) (hf : 676 < fuel) :
    walk nodes fuel 676 = List.range' 676 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 676).rule = .bound .leftEnd 8 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_677 (fuel : Nat) (hf : 677 < fuel) :
    walk nodes fuel 677 = List.range' 677 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 677).rule = .bound .leftEnd 8 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_678 (fuel : Nat) (hf : 678 < fuel) :
    walk nodes fuel 678 = List.range' 678 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 678).rule = .bound .leftEnd 2 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_679 (fuel : Nat) (hf : 679 < fuel) :
    walk nodes fuel 679 = List.range' 677 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 679).rule = .split 2 (9137/4096) 677 678 := by rfl
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
      have hr : (node nodes 680).rule = .split 1 (2335/1024) 676 679 := by rfl
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
      have hr : (node nodes 681).rule = .bound .leftEnd 8 (815/1536) (494051/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_682 (fuel : Nat) (hf : 682 < fuel) :
    walk nodes fuel 682 = List.range' 676 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 682).rule = .split 0 (1/1280) 680 681 := by rfl
      simp only [walk, hr]
      rw [traversal_680 f (by omega), traversal_681 f (by omega)]
      change (List.range' 676 5 ++ List.range' (676+5) 1) ++
        [676+(5+1)] = List.range' 676 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 676) (n := 5+1)).symm

private theorem traversal_683 (fuel : Nat) (hf : 683 < fuel) :
    walk nodes fuel 683 = List.range' 675 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 683).rule = .split 3 (453/512) 675 682 := by rfl
      simp only [walk, hr]
      rw [traversal_675 f (by omega), traversal_682 f (by omega)]
      change (List.range' 675 1 ++ List.range' (675+1) 7) ++
        [675+(1+7)] = List.range' 675 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 675) (n := 1+7)).symm

private theorem traversal_684 (fuel : Nat) (hf : 684 < fuel) :
    walk nodes fuel 684 = List.range' 674 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 684).rule = .split 2 (4559/2048) 674 683 := by rfl
      simp only [walk, hr]
      rw [traversal_674 f (by omega), traversal_683 f (by omega)]
      change (List.range' 674 1 ++ List.range' (674+1) 9) ++
        [674+(1+9)] = List.range' 674 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 674) (n := 1+9)).symm

private theorem traversal_685 (fuel : Nat) (hf : 685 < fuel) :
    walk nodes fuel 685 = List.range' 673 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 685).rule = .split 1 (1165/512) 673 684 := by rfl
      simp only [walk, hr]
      rw [traversal_673 f (by omega), traversal_684 f (by omega)]
      change (List.range' 673 1 ++ List.range' (673+1) 11) ++
        [673+(1+11)] = List.range' 673 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 673) (n := 1+11)).symm

private theorem traversal_686 (fuel : Nat) (hf : 686 < fuel) :
    walk nodes fuel 686 = List.range' 686 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 686).rule = .bound .leftEnd 8 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_687 (fuel : Nat) (hf : 687 < fuel) :
    walk nodes fuel 687 = List.range' 687 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 687).rule = .bound .leftEnd 8 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_688 (fuel : Nat) (hf : 688 < fuel) :
    walk nodes fuel 688 = List.range' 688 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 688).rule = .bound .leftEnd 2 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_689 (fuel : Nat) (hf : 689 < fuel) :
    walk nodes fuel 689 = List.range' 687 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 689).rule = .split 2 (4559/2048) 687 688 := by rfl
      simp only [walk, hr]
      rw [traversal_687 f (by omega), traversal_688 f (by omega)]
      change (List.range' 687 1 ++ List.range' (687+1) 1) ++
        [687+(1+1)] = List.range' 687 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 687) (n := 1+1)).symm

private theorem traversal_690 (fuel : Nat) (hf : 690 < fuel) :
    walk nodes fuel 690 = List.range' 686 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 690).rule = .split 1 (1165/512) 686 689 := by rfl
      simp only [walk, hr]
      rw [traversal_686 f (by omega), traversal_689 f (by omega)]
      change (List.range' 686 1 ++ List.range' (686+1) 3) ++
        [686+(1+3)] = List.range' 686 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 686) (n := 1+3)).symm

private theorem traversal_691 (fuel : Nat) (hf : 691 < fuel) :
    walk nodes fuel 691 = List.range' 673 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 691).rule = .split 0 (1/640) 685 690 := by rfl
      simp only [walk, hr]
      rw [traversal_685 f (by omega), traversal_690 f (by omega)]
      change (List.range' 673 13 ++ List.range' (673+13) 5) ++
        [673+(13+5)] = List.range' 673 ((13+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 673) (n := 13+5)).symm

private theorem traversal_692 (fuel : Nat) (hf : 692 < fuel) :
    walk nodes fuel 692 = List.range' 672 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 692).rule = .split 3 (225/256) 672 691 := by rfl
      simp only [walk, hr]
      rw [traversal_672 f (by omega), traversal_691 f (by omega)]
      change (List.range' 672 1 ++ List.range' (672+1) 19) ++
        [672+(1+19)] = List.range' 672 ((1+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 672) (n := 1+19)).symm

private theorem traversal_693 (fuel : Nat) (hf : 693 < fuel) :
    walk nodes fuel 693 = List.range' 693 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 693).rule = .bound .leftEnd 2 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_694 (fuel : Nat) (hf : 694 < fuel) :
    walk nodes fuel 694 = List.range' 694 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 694).rule = .bound .leftEnd 8 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_695 (fuel : Nat) (hf : 695 < fuel) :
    walk nodes fuel 695 = List.range' 695 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 695).rule = .bound .leftEnd 2 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_696 (fuel : Nat) (hf : 696 < fuel) :
    walk nodes fuel 696 = List.range' 694 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 696).rule = .split 1 (1165/512) 694 695 := by rfl
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
      have hr : (node nodes 697).rule = .bound .leftEnd 2 (2177/4096) (493215/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_698 (fuel : Nat) (hf : 698 < fuel) :
    walk nodes fuel 698 = List.range' 694 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 698).rule = .split 0 (1/640) 696 697 := by rfl
      simp only [walk, hr]
      rw [traversal_696 f (by omega), traversal_697 f (by omega)]
      change (List.range' 694 3 ++ List.range' (694+3) 1) ++
        [694+(3+1)] = List.range' 694 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 694) (n := 3+1)).symm

private theorem traversal_699 (fuel : Nat) (hf : 699 < fuel) :
    walk nodes fuel 699 = List.range' 693 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 699).rule = .split 3 (225/256) 693 698 := by rfl
      simp only [walk, hr]
      rw [traversal_693 f (by omega), traversal_698 f (by omega)]
      change (List.range' 693 1 ++ List.range' (693+1) 5) ++
        [693+(1+5)] = List.range' 693 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 693) (n := 1+5)).symm

theorem traversal_700 (fuel : Nat) (hf : 700 < fuel) :
    walk nodes fuel 700 = List.range' 672 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 700).rule = .split 2 (2289/1024) 692 699 := by rfl
      simp only [walk, hr]
      rw [traversal_692 f (by omega), traversal_699 f (by omega)]
      change (List.range' 672 21 ++ List.range' (672+21) 7) ++
        [672+(21+7)] = List.range' 672 ((21+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 672) (n := 21+7)).symm

theorem traversal_701 (fuel : Nat) (hf : 701 < fuel) :
    walk nodes fuel 701 = List.range' 701 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 701).rule = .bound .leftEnd 2 (137/256) (30615/65536) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_702 (fuel : Nat) (hf : 702 < fuel) :
    walk nodes fuel 702 = List.range' 702 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 702).rule = .bound .leftEnd 2 (3271/6144) (246195/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_703 (fuel : Nat) (hf : 703 < fuel) :
    walk nodes fuel 703 = List.range' 703 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 703).rule = .bound .leftEnd 8 (1631/3072) (493749/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_704 (fuel : Nat) (hf : 704 < fuel) :
    walk nodes fuel 704 = List.range' 704 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 704).rule = .bound .leftEnd 2 (1631/3072) (493749/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_705 (fuel : Nat) (hf : 705 < fuel) :
    walk nodes fuel 705 = List.range' 703 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 705).rule = .split 1 (4685/2048) 703 704 := by rfl
      simp only [walk, hr]
      rw [traversal_703 f (by omega), traversal_704 f (by omega)]
      change (List.range' 703 1 ++ List.range' (703+1) 1) ++
        [703+(1+1)] = List.range' 703 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 703) (n := 1+1)).symm

private theorem traversal_706 (fuel : Nat) (hf : 706 < fuel) :
    walk nodes fuel 706 = List.range' 706 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 706).rule = .bound .leftEnd 2 (1631/3072) (493749/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_707 (fuel : Nat) (hf : 707 < fuel) :
    walk nodes fuel 707 = List.range' 703 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 707).rule = .split 0 (1/2560) 705 706 := by rfl
      simp only [walk, hr]
      rw [traversal_705 f (by omega), traversal_706 f (by omega)]
      change (List.range' 703 3 ++ List.range' (703+3) 1) ++
        [703+(3+1)] = List.range' 703 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 703) (n := 3+1)).symm

private theorem traversal_708 (fuel : Nat) (hf : 708 < fuel) :
    walk nodes fuel 708 = List.range' 708 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 708).rule = .bound .leftEnd 8 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_709 (fuel : Nat) (hf : 709 < fuel) :
    walk nodes fuel 709 = List.range' 703 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 709).rule = .split 3 (909/1024) 707 708 := by rfl
      simp only [walk, hr]
      rw [traversal_707 f (by omega), traversal_708 f (by omega)]
      change (List.range' 703 5 ++ List.range' (703+5) 1) ++
        [703+(5+1)] = List.range' 703 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 703) (n := 5+1)).symm

private theorem traversal_710 (fuel : Nat) (hf : 710 < fuel) :
    walk nodes fuel 710 = List.range' 710 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 710).rule = .bound .leftEnd 2 (1631/3072) (493749/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_711 (fuel : Nat) (hf : 711 < fuel) :
    walk nodes fuel 711 = List.range' 711 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 711).rule = .bound .leftEnd 8 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_712 (fuel : Nat) (hf : 712 < fuel) :
    walk nodes fuel 712 = List.range' 712 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 712).rule = .bound .leftEnd 2 (815/1536) (123513/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_713 (fuel : Nat) (hf : 713 < fuel) :
    walk nodes fuel 713 = List.range' 713 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 713).rule = .bound .leftEnd 1 (407/768) (494659/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_714 (fuel : Nat) (hf : 714 < fuel) :
    walk nodes fuel 714 = List.range' 712 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 714).rule = .split 3 (1821/2048) 712 713 := by rfl
      simp only [walk, hr]
      rw [traversal_712 f (by omega), traversal_713 f (by omega)]
      change (List.range' 712 1 ++ List.range' (712+1) 1) ++
        [712+(1+1)] = List.range' 712 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 712) (n := 1+1)).symm

private theorem traversal_715 (fuel : Nat) (hf : 715 < fuel) :
    walk nodes fuel 715 = List.range' 715 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 715).rule = .bound .leftEnd 2 (815/1536) (123513/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_716 (fuel : Nat) (hf : 716 < fuel) :
    walk nodes fuel 716 = List.range' 716 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 716).rule = .bound .leftEnd 1 (407/768) (494659/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_717 (fuel : Nat) (hf : 717 < fuel) :
    walk nodes fuel 717 = List.range' 715 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 717).rule = .split 3 (1821/2048) 715 716 := by rfl
      simp only [walk, hr]
      rw [traversal_715 f (by omega), traversal_716 f (by omega)]
      change (List.range' 715 1 ++ List.range' (715+1) 1) ++
        [715+(1+1)] = List.range' 715 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 715) (n := 1+1)).symm

private theorem traversal_718 (fuel : Nat) (hf : 718 < fuel) :
    walk nodes fuel 718 = List.range' 712 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 718).rule = .split 2 (18217/8192) 714 717 := by rfl
      simp only [walk, hr]
      rw [traversal_714 f (by omega), traversal_717 f (by omega)]
      change (List.range' 712 3 ++ List.range' (712+3) 3) ++
        [712+(3+3)] = List.range' 712 ((3+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 712) (n := 3+3)).symm

private theorem traversal_719 (fuel : Nat) (hf : 719 < fuel) :
    walk nodes fuel 719 = List.range' 711 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 719).rule = .split 1 (4685/2048) 711 718 := by rfl
      simp only [walk, hr]
      rw [traversal_711 f (by omega), traversal_718 f (by omega)]
      change (List.range' 711 1 ++ List.range' (711+1) 7) ++
        [711+(1+7)] = List.range' 711 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 711) (n := 1+7)).symm

private theorem traversal_720 (fuel : Nat) (hf : 720 < fuel) :
    walk nodes fuel 720 = List.range' 720 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 720).rule = .bound .leftEnd 8 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_721 (fuel : Nat) (hf : 721 < fuel) :
    walk nodes fuel 721 = List.range' 721 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 721).rule = .bound .leftEnd 1 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_722 (fuel : Nat) (hf : 722 < fuel) :
    walk nodes fuel 722 = List.range' 720 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 722).rule = .split 1 (4685/2048) 720 721 := by rfl
      simp only [walk, hr]
      rw [traversal_720 f (by omega), traversal_721 f (by omega)]
      change (List.range' 720 1 ++ List.range' (720+1) 1) ++
        [720+(1+1)] = List.range' 720 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 720) (n := 1+1)).symm

private theorem traversal_723 (fuel : Nat) (hf : 723 < fuel) :
    walk nodes fuel 723 = List.range' 711 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 723).rule = .split 0 (1/2560) 719 722 := by rfl
      simp only [walk, hr]
      rw [traversal_719 f (by omega), traversal_722 f (by omega)]
      change (List.range' 711 9 ++ List.range' (711+9) 3) ++
        [711+(9+3)] = List.range' 711 ((9+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 711) (n := 9+3)).symm

private theorem traversal_724 (fuel : Nat) (hf : 724 < fuel) :
    walk nodes fuel 724 = List.range' 710 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 724).rule = .split 3 (909/1024) 710 723 := by rfl
      simp only [walk, hr]
      rw [traversal_710 f (by omega), traversal_723 f (by omega)]
      change (List.range' 710 1 ++ List.range' (710+1) 13) ++
        [710+(1+13)] = List.range' 710 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 710) (n := 1+13)).symm

private theorem traversal_725 (fuel : Nat) (hf : 725 < fuel) :
    walk nodes fuel 725 = List.range' 703 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 725).rule = .split 2 (9099/4096) 709 724 := by rfl
      simp only [walk, hr]
      rw [traversal_709 f (by omega), traversal_724 f (by omega)]
      change (List.range' 703 7 ++ List.range' (703+7) 15) ++
        [703+(7+15)] = List.range' 703 ((7+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 703) (n := 7+15)).symm

private theorem traversal_726 (fuel : Nat) (hf : 726 < fuel) :
    walk nodes fuel 726 = List.range' 726 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 726).rule = .bound .leftEnd 2 (1631/3072) (493749/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_727 (fuel : Nat) (hf : 727 < fuel) :
    walk nodes fuel 727 = List.range' 727 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 727).rule = .bound .leftEnd 1 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_728 (fuel : Nat) (hf : 728 < fuel) :
    walk nodes fuel 728 = List.range' 726 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 728).rule = .split 3 (909/1024) 726 727 := by rfl
      simp only [walk, hr]
      rw [traversal_726 f (by omega), traversal_727 f (by omega)]
      change (List.range' 726 1 ++ List.range' (726+1) 1) ++
        [726+(1+1)] = List.range' 726 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 726) (n := 1+1)).symm

private theorem traversal_729 (fuel : Nat) (hf : 729 < fuel) :
    walk nodes fuel 729 = List.range' 729 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 729).rule = .bound .leftEnd 2 (1631/3072) (493749/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_730 (fuel : Nat) (hf : 730 < fuel) :
    walk nodes fuel 730 = List.range' 730 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 730).rule = .bound .leftEnd 1 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_731 (fuel : Nat) (hf : 731 < fuel) :
    walk nodes fuel 731 = List.range' 731 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 731).rule = .bound .leftEnd 2 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_732 (fuel : Nat) (hf : 732 < fuel) :
    walk nodes fuel 732 = List.range' 730 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 732).rule = .split 2 (18217/8192) 730 731 := by rfl
      simp only [walk, hr]
      rw [traversal_730 f (by omega), traversal_731 f (by omega)]
      change (List.range' 730 1 ++ List.range' (730+1) 1) ++
        [730+(1+1)] = List.range' 730 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 730) (n := 1+1)).symm

private theorem traversal_733 (fuel : Nat) (hf : 733 < fuel) :
    walk nodes fuel 733 = List.range' 733 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 733).rule = .bound .leftEnd 1 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_734 (fuel : Nat) (hf : 734 < fuel) :
    walk nodes fuel 734 = List.range' 730 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 734).rule = .split 1 (4695/2048) 732 733 := by rfl
      simp only [walk, hr]
      rw [traversal_732 f (by omega), traversal_733 f (by omega)]
      change (List.range' 730 3 ++ List.range' (730+3) 1) ++
        [730+(3+1)] = List.range' 730 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 730) (n := 3+1)).symm

private theorem traversal_735 (fuel : Nat) (hf : 735 < fuel) :
    walk nodes fuel 735 = List.range' 735 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 735).rule = .bound .leftEnd 1 (543/1024) (494355/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_736 (fuel : Nat) (hf : 736 < fuel) :
    walk nodes fuel 736 = List.range' 730 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 736).rule = .split 0 (1/2560) 734 735 := by rfl
      simp only [walk, hr]
      rw [traversal_734 f (by omega), traversal_735 f (by omega)]
      change (List.range' 730 5 ++ List.range' (730+5) 1) ++
        [730+(5+1)] = List.range' 730 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 730) (n := 5+1)).symm

private theorem traversal_737 (fuel : Nat) (hf : 737 < fuel) :
    walk nodes fuel 737 = List.range' 729 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 737).rule = .split 3 (909/1024) 729 736 := by rfl
      simp only [walk, hr]
      rw [traversal_729 f (by omega), traversal_736 f (by omega)]
      change (List.range' 729 1 ++ List.range' (729+1) 7) ++
        [729+(1+7)] = List.range' 729 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 729) (n := 1+7)).symm

private theorem traversal_738 (fuel : Nat) (hf : 738 < fuel) :
    walk nodes fuel 738 = List.range' 726 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 738).rule = .split 2 (9099/4096) 728 737 := by rfl
      simp only [walk, hr]
      rw [traversal_728 f (by omega), traversal_737 f (by omega)]
      change (List.range' 726 3 ++ List.range' (726+3) 9) ++
        [726+(3+9)] = List.range' 726 ((3+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 726) (n := 3+9)).symm

theorem traversal_739 (fuel : Nat) (hf : 739 < fuel) :
    walk nodes fuel 739 = List.range' 703 37 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 739).rule = .split 1 (2345/1024) 725 738 := by rfl
      simp only [walk, hr]
      rw [traversal_725 f (by omega), traversal_738 f (by omega)]
      change (List.range' 703 23 ++ List.range' (703+23) 13) ++
        [703+(23+13)] = List.range' 703 ((23+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 703) (n := 23+13)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
