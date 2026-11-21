/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Main01
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main01.chunk_checked
   digest: Exact numerical and binary coverage certificate for the main exponent box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainSupport
import D5.S3.Arith.Divisors.ErdosNicolas.Data.RankReadouts00

/-! Opaque numerical subproofs bound temporary kernel reduction memory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.Main01

private abbrev C (lo hi : Fin 7 → ℕ) (tree : MainTree) : Prop :=
  checkExponentBoxTree mainScale boxPrimes lo hi tree = true

/-- Lower exponents at this subtree root. -/
def lo : Fin 7 → ℕ := ![0, 2, 0, 0, 0, 0, 0]

/-- Upper exponents at the same root. -/
def hi : Fin 7 → ℕ := ![1, 7, 3, 2, 1, 1, 1]

private def n641 : MainTree := .leaf (mainGapLeaf ![0, 3, 0, 0, 0, 0, 1])
private def n642 : MainTree := .leaf (mainGapLeaf ![0, 3, 0, 0, 0, 1, 1])
private def n640 : MainTree := .split 5 0 n641 n642
private def n644 : MainTree := .leaf (mainGapLeaf ![0, 3, 0, 0, 1, 0, 1])
private def n645 : MainTree := .leaf (mainGapLeaf ![0, 3, 0, 0, 1, 1, 1])
private def n643 : MainTree := .split 5 0 n644 n645
private def n639 : MainTree := .split 4 0 n640 n643
private def n648 : MainTree := .leaf (mainGapLeaf ![0, 3, 1, 0, 0, 0, 1])
private def n649 : MainTree := .leaf (mainGapLeaf ![0, 3, 1, 0, 0, 1, 1])
private def n647 : MainTree := .split 5 0 n648 n649
private def n651 : MainTree := .leaf (mainGapLeaf ![0, 3, 1, 0, 1, 0, 1])
private def n652 : MainTree := .leaf (mainGapLeaf ![0, 3, 1, 0, 1, 1, 1])
private def n650 : MainTree := .split 5 0 n651 n652
private def n646 : MainTree := .split 4 0 n647 n650
private def n638 : MainTree := .split 2 0 n639 n646
private def n657 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 0, 0, 0, 0])
private def n658 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 0, 0, 0, 1])
private def n656 : MainTree := .split 6 0 n657 n658
private def n660 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 0, 0, 1, 0])
private def n661 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 0, 0, 1, 1])
private def n659 : MainTree := .split 6 0 n660 n661
private def n655 : MainTree := .split 5 0 n656 n659
private def n664 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 0, 1, 0, 0])
private def n665 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 0, 1, 0, 1])
private def n663 : MainTree := .split 6 0 n664 n665
private def n667 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 0, 1, 1, 0])
private def n668 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 0, 1, 1, 1])
private def n666 : MainTree := .split 6 0 n667 n668
private def n662 : MainTree := .split 5 0 n663 n666
private def n654 : MainTree := .split 4 0 n655 n662
private def n673 : MainTree := .leaf (mainRankLeaf 2 ![1, 2, 1, 0, 0, 0, 0])
private def n674 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 0, 0, 0, 0])
private def n672 : MainTree := .split 1 2 n673 n674
private def n675 : MainTree := .leaf (mainRankLeaf 1 ![1, 3, 1, 0, 0, 0, 1])
private def n671 : MainTree := .split 6 0 n672 n675
private def n678 : MainTree := .leaf (mainGapLeaf ![1, 2, 1, 0, 0, 1, 0])
private def n679 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 0, 0, 1, 0])
private def n677 : MainTree := .split 1 2 n678 n679
private def n680 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 0, 0, 1, 1])
private def n676 : MainTree := .split 6 0 n677 n680
private def n670 : MainTree := .split 5 0 n671 n676
private def n684 : MainTree := .leaf (mainGapLeaf ![1, 2, 1, 0, 1, 0, 0])
private def n685 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 0, 1, 0, 0])
private def n683 : MainTree := .split 1 2 n684 n685
private def n686 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 0, 1, 0, 1])
private def n682 : MainTree := .split 6 0 n683 n686
private def n688 : MainTree := .leaf (mainRankLeaf 1 ![1, 3, 1, 0, 1, 1, 0])
private def n689 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 0, 1, 1, 1])
private def n687 : MainTree := .split 6 0 n688 n689
private def n681 : MainTree := .split 5 0 n682 n687
private def n669 : MainTree := .split 4 0 n670 n681
private def n653 : MainTree := .split 2 0 n654 n669
private def n637 : MainTree := .split 0 0 n638 n653
private def n693 : MainTree := .leaf (mainGapLeaf ![0, 7, 0, 0, 0, 1, 1])
private def n694 : MainTree := .leaf (mainGapLeaf ![0, 7, 0, 0, 1, 1, 1])
private def n692 : MainTree := .split 4 0 n693 n694
private def n697 : MainTree := .leaf (mainGapLeaf ![0, 7, 1, 0, 0, 0, 1])
private def n698 : MainTree := .leaf (mainGapLeaf ![0, 7, 1, 0, 0, 1, 1])
private def n696 : MainTree := .split 5 0 n697 n698
private def n700 : MainTree := .leaf (mainGapLeaf ![0, 7, 1, 0, 1, 0, 1])
private def n701 : MainTree := .leaf (mainGapLeaf ![0, 7, 1, 0, 1, 1, 1])
private def n699 : MainTree := .split 5 0 n700 n701
private def n695 : MainTree := .split 4 0 n696 n699
private def n691 : MainTree := .split 2 0 n692 n695
private def n706 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 0, 0, 0, 0])
private def n707 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 0, 0, 0, 1])
private def n705 : MainTree := .split 6 0 n706 n707
private def n708 : MainTree := .leaf (mainRankLeaf 1 ![1, 7, 0, 0, 0, 1, 1])
private def n704 : MainTree := .split 5 0 n705 n708
private def n711 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 0, 1, 0, 0])
private def n712 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 0, 1, 0, 1])
private def n710 : MainTree := .split 6 0 n711 n712
private def n713 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 0, 1, 1, 1])
private def n709 : MainTree := .split 5 0 n710 n713
private def n703 : MainTree := .split 4 0 n704 n709
private def n717 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 0, 0, 0, 0])
private def n718 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 0, 0, 0, 1])
private def n716 : MainTree := .split 6 0 n717 n718
private def n720 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 0, 0, 1, 0])
private def n721 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 0, 0, 1, 1])
private def n719 : MainTree := .split 6 0 n720 n721
private def n715 : MainTree := .split 5 0 n716 n719
private def n724 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 0, 1, 0, 0])
private def n725 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 0, 1, 0, 1])
private def n723 : MainTree := .split 6 0 n724 n725
private def n727 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 0, 1, 1, 0])
private def n728 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 0, 1, 1, 1])
private def n726 : MainTree := .split 6 0 n727 n728
private def n722 : MainTree := .split 5 0 n723 n726
private def n714 : MainTree := .split 4 0 n715 n722
private def n702 : MainTree := .split 2 0 n703 n714
private def n690 : MainTree := .split 0 0 n691 n702
private def n636 : MainTree := .split 1 3 n637 n690
private def n735 : MainTree := .leaf (mainGapLeaf ![0, 3, 0, 2, 0, 0, 0])
private def n736 : MainTree := .leaf (mainGapLeaf ![0, 3, 0, 2, 0, 0, 1])
private def n734 : MainTree := .split 6 0 n735 n736
private def n737 : MainTree := .leaf (mainRankLeaf 1 ![0, 3, 0, 2, 0, 1, 1])
private def n733 : MainTree := .split 5 0 n734 n737
private def n740 : MainTree := .leaf (mainGapLeaf ![0, 3, 0, 2, 1, 0, 0])
private def n741 : MainTree := .leaf (mainGapLeaf ![0, 3, 0, 2, 1, 0, 1])
private def n739 : MainTree := .split 6 0 n740 n741
private def n742 : MainTree := .leaf (mainRankLeaf 1 ![0, 3, 0, 2, 1, 1, 1])
private def n738 : MainTree := .split 5 0 n739 n742
private def n732 : MainTree := .split 4 0 n733 n738
private def n746 : MainTree := .leaf (mainGapLeaf ![0, 3, 1, 2, 0, 0, 0])
private def n747 : MainTree := .leaf (mainGapLeaf ![0, 3, 1, 2, 0, 0, 1])
private def n745 : MainTree := .split 6 0 n746 n747
private def n749 : MainTree := .leaf (mainGapLeaf ![0, 3, 1, 2, 0, 1, 0])
private def n750 : MainTree := .leaf (mainGapLeaf ![0, 3, 1, 2, 0, 1, 1])
private def n748 : MainTree := .split 6 0 n749 n750
private def n744 : MainTree := .split 5 0 n745 n748
private def n753 : MainTree := .leaf (mainGapLeaf ![0, 3, 1, 2, 1, 0, 0])
private def n754 : MainTree := .leaf (mainGapLeaf ![0, 3, 1, 2, 1, 0, 1])
private def n752 : MainTree := .split 6 0 n753 n754
private def n756 : MainTree := .leaf (mainGapLeaf ![0, 3, 1, 2, 1, 1, 0])
private def n757 : MainTree := .leaf (mainGapLeaf ![0, 3, 1, 2, 1, 1, 1])
private def n755 : MainTree := .split 6 0 n756 n757
private def n751 : MainTree := .split 5 0 n752 n755
private def n743 : MainTree := .split 4 0 n744 n751
private def n731 : MainTree := .split 2 0 n732 n743
private def n764 : MainTree := .leaf (mainGapLeaf ![1, 2, 0, 1, 0, 0, 0])
private def n765 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 1, 0, 0, 0])
private def n763 : MainTree := .split 1 2 n764 n765
private def n766 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 2, 0, 0, 0])
private def n762 : MainTree := .split 3 1 n763 n766
private def n768 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 1, 0, 0, 1])
private def n769 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 2, 0, 0, 1])
private def n767 : MainTree := .split 3 1 n768 n769
private def n761 : MainTree := .split 6 0 n762 n767
private def n772 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 1, 0, 1, 0])
private def n773 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 2, 0, 1, 0])
private def n771 : MainTree := .split 3 1 n772 n773
private def n774 : MainTree := .leaf (mainRankLeaf 1 ![1, 3, 0, 2, 0, 1, 1])
private def n770 : MainTree := .split 6 0 n771 n774
private def n760 : MainTree := .split 5 0 n761 n770
private def n778 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 1, 1, 0, 0])
private def n779 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 2, 1, 0, 0])
private def n777 : MainTree := .split 3 1 n778 n779
private def n780 : MainTree := .leaf (mainRankLeaf 1 ![1, 3, 0, 2, 1, 0, 1])
private def n776 : MainTree := .split 6 0 n777 n780
private def n783 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 1, 1, 1, 0])
private def n784 : MainTree := .leaf (mainGapLeaf ![1, 3, 0, 2, 1, 1, 0])
private def n782 : MainTree := .split 3 1 n783 n784
private def n785 : MainTree := .leaf (mainRankLeaf 1 ![1, 3, 0, 2, 1, 1, 1])
private def n781 : MainTree := .split 6 0 n782 n785
private def n775 : MainTree := .split 5 0 n776 n781
private def n759 : MainTree := .split 4 0 n760 n775
private def n791 : MainTree := .leaf (mainRankLeaf 2 ![1, 2, 1, 1, 0, 0, 0])
private def n792 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 1, 0, 0, 0])
private def n790 : MainTree := .split 1 2 n791 n792
private def n793 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 2, 0, 0, 0])
private def n789 : MainTree := .split 3 1 n790 n793
private def n795 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 1, 0, 0, 1])
private def n796 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 2, 0, 0, 1])
private def n794 : MainTree := .split 3 1 n795 n796
private def n788 : MainTree := .split 6 0 n789 n794
private def n800 : MainTree := .leaf (mainGapLeaf ![1, 2, 1, 1, 0, 1, 0])
private def n801 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 1, 0, 1, 0])
private def n799 : MainTree := .split 1 2 n800 n801
private def n802 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 2, 0, 1, 0])
private def n798 : MainTree := .split 3 1 n799 n802
private def n804 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 1, 0, 1, 1])
private def n805 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 2, 0, 1, 1])
private def n803 : MainTree := .split 3 1 n804 n805
private def n797 : MainTree := .split 6 0 n798 n803
private def n787 : MainTree := .split 5 0 n788 n797
private def n810 : MainTree := .leaf (mainGapLeaf ![1, 2, 1, 1, 1, 0, 0])
private def n811 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 1, 1, 0, 0])
private def n809 : MainTree := .split 1 2 n810 n811
private def n812 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 2, 1, 0, 0])
private def n808 : MainTree := .split 3 1 n809 n812
private def n814 : MainTree := .leaf (mainRankLeaf 1 ![1, 3, 1, 1, 1, 0, 1])
private def n815 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 2, 1, 0, 1])
private def n813 : MainTree := .split 3 1 n814 n815
private def n807 : MainTree := .split 6 0 n808 n813
private def n818 : MainTree := .leaf (mainRankLeaf 1 ![1, 3, 1, 1, 1, 1, 0])
private def n819 : MainTree := .leaf (mainGapLeaf ![1, 3, 1, 2, 1, 1, 0])
private def n817 : MainTree := .split 3 1 n818 n819
private def n820 : MainTree := .leaf (mainRankLeaf 1 ![1, 3, 1, 2, 1, 1, 1])
private def n816 : MainTree := .split 6 0 n817 n820
private def n806 : MainTree := .split 5 0 n807 n816
private def n786 : MainTree := .split 4 0 n787 n806
private def n758 : MainTree := .split 2 0 n759 n786
private def n730 : MainTree := .split 0 0 n731 n758
private def n825 : MainTree := .leaf (mainGapLeaf ![0, 7, 0, 2, 0, 0, 1])
private def n826 : MainTree := .leaf (mainGapLeaf ![0, 7, 0, 2, 0, 1, 1])
private def n824 : MainTree := .split 5 0 n825 n826
private def n828 : MainTree := .leaf (mainGapLeaf ![0, 7, 0, 2, 1, 0, 1])
private def n829 : MainTree := .leaf (mainGapLeaf ![0, 7, 0, 2, 1, 1, 1])
private def n827 : MainTree := .split 5 0 n828 n829
private def n823 : MainTree := .split 4 0 n824 n827
private def n832 : MainTree := .leaf (mainRankLeaf 1 ![0, 7, 1, 2, 0, 0, 1])
private def n833 : MainTree := .leaf (mainGapLeaf ![0, 7, 1, 2, 0, 1, 1])
private def n831 : MainTree := .split 5 0 n832 n833
private def n835 : MainTree := .leaf (mainGapLeaf ![0, 7, 1, 2, 1, 0, 1])
private def n836 : MainTree := .leaf (mainGapLeaf ![0, 7, 1, 2, 1, 1, 1])
private def n834 : MainTree := .split 5 0 n835 n836
private def n830 : MainTree := .split 4 0 n831 n834
private def n822 : MainTree := .split 2 0 n823 n830
private def n841 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 2, 0, 0, 0])
private def n842 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 2, 0, 0, 1])
private def n840 : MainTree := .split 6 0 n841 n842
private def n844 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 2, 0, 1, 0])
private def n845 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 2, 0, 1, 1])
private def n843 : MainTree := .split 6 0 n844 n845
private def n839 : MainTree := .split 5 0 n840 n843
private def n848 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 2, 1, 0, 0])
private def n849 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 2, 1, 0, 1])
private def n847 : MainTree := .split 6 0 n848 n849
private def n851 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 2, 1, 1, 0])
private def n852 : MainTree := .leaf (mainGapLeaf ![1, 7, 0, 2, 1, 1, 1])
private def n850 : MainTree := .split 6 0 n851 n852
private def n846 : MainTree := .split 5 0 n847 n850
private def n838 : MainTree := .split 4 0 n839 n846
private def n857 : MainTree := .leaf (mainGapLeaf ![1, 5, 1, 2, 0, 0, 0])
private def n858 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 2, 0, 0, 0])
private def n856 : MainTree := .split 1 5 n857 n858
private def n859 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 2, 0, 0, 1])
private def n855 : MainTree := .split 6 0 n856 n859
private def n861 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 2, 0, 1, 0])
private def n862 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 2, 0, 1, 1])
private def n860 : MainTree := .split 6 0 n861 n862
private def n854 : MainTree := .split 5 0 n855 n860
private def n865 : MainTree := .leaf (mainRankLeaf 1 ![1, 7, 1, 2, 1, 0, 0])
private def n866 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 2, 1, 0, 1])
private def n864 : MainTree := .split 6 0 n865 n866
private def n868 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 2, 1, 1, 0])
private def n869 : MainTree := .leaf (mainGapLeaf ![1, 7, 1, 2, 1, 1, 1])
private def n867 : MainTree := .split 6 0 n868 n869
private def n863 : MainTree := .split 5 0 n864 n867
private def n853 : MainTree := .split 4 0 n854 n863
private def n837 : MainTree := .split 2 0 n838 n853
private def n821 : MainTree := .split 0 0 n822 n837
private def n729 : MainTree := .split 1 3 n730 n821
private def n635 : MainTree := .split 3 0 n636 n729
private def n875 : MainTree := .leaf (mainRankLeaf 1 ![0, 3, 3, 0, 0, 0, 1])
private def n876 : MainTree := .leaf (mainGapLeaf ![0, 3, 3, 0, 0, 1, 1])
private def n874 : MainTree := .split 5 0 n875 n876
private def n878 : MainTree := .leaf (mainGapLeaf ![0, 3, 3, 0, 1, 0, 1])
private def n879 : MainTree := .leaf (mainGapLeaf ![0, 3, 3, 0, 1, 1, 1])
private def n877 : MainTree := .split 5 0 n878 n879
private def n873 : MainTree := .split 4 0 n874 n877
private def n884 : MainTree := .leaf (mainGapLeaf ![1, 2, 3, 0, 0, 0, 0])
private def n885 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 0, 0, 0, 0])
private def n883 : MainTree := .split 1 2 n884 n885
private def n886 : MainTree := .leaf (mainRankLeaf 1 ![1, 3, 3, 0, 0, 0, 1])
private def n882 : MainTree := .split 6 0 n883 n886
private def n889 : MainTree := .leaf (mainGapLeaf ![1, 2, 3, 0, 0, 1, 0])
private def n890 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 0, 0, 1, 0])
private def n888 : MainTree := .split 1 2 n889 n890
private def n891 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 0, 0, 1, 1])
private def n887 : MainTree := .split 6 0 n888 n891
private def n881 : MainTree := .split 5 0 n882 n887
private def n895 : MainTree := .leaf (mainGapLeaf ![1, 2, 3, 0, 1, 0, 0])
private def n896 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 0, 1, 0, 0])
private def n894 : MainTree := .split 1 2 n895 n896
private def n897 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 0, 1, 0, 1])
private def n893 : MainTree := .split 6 0 n894 n897
private def n899 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 0, 1, 1, 0])
private def n900 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 0, 1, 1, 1])
private def n898 : MainTree := .split 6 0 n899 n900
private def n892 : MainTree := .split 5 0 n893 n898
private def n880 : MainTree := .split 4 0 n881 n892
private def n872 : MainTree := .split 0 0 n873 n880
private def n904 : MainTree := .leaf (mainGapLeaf ![0, 7, 3, 0, 0, 0, 1])
private def n905 : MainTree := .leaf (mainGapLeaf ![0, 7, 3, 0, 0, 1, 1])
private def n903 : MainTree := .split 5 0 n904 n905
private def n907 : MainTree := .leaf (mainGapLeaf ![0, 7, 3, 0, 1, 0, 1])
private def n908 : MainTree := .leaf (mainGapLeaf ![0, 7, 3, 0, 1, 1, 1])
private def n906 : MainTree := .split 5 0 n907 n908
private def n902 : MainTree := .split 4 0 n903 n906
private def n912 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 0, 0, 0, 0])
private def n913 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 0, 0, 0, 1])
private def n911 : MainTree := .split 6 0 n912 n913
private def n915 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 0, 0, 1, 0])
private def n916 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 0, 0, 1, 1])
private def n914 : MainTree := .split 6 0 n915 n916
private def n910 : MainTree := .split 5 0 n911 n914
private def n919 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 0, 1, 0, 0])
private def n920 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 0, 1, 0, 1])
private def n918 : MainTree := .split 6 0 n919 n920
private def n922 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 0, 1, 1, 0])
private def n923 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 0, 1, 1, 1])
private def n921 : MainTree := .split 6 0 n922 n923
private def n917 : MainTree := .split 5 0 n918 n921
private def n909 : MainTree := .split 4 0 n910 n917
private def n901 : MainTree := .split 0 0 n902 n909
private def n871 : MainTree := .split 1 3 n872 n901
private def n929 : MainTree := .leaf (mainGapLeaf ![0, 3, 3, 2, 0, 0, 0])
private def n930 : MainTree := .leaf (mainGapLeaf ![0, 3, 3, 2, 0, 0, 1])
private def n928 : MainTree := .split 6 0 n929 n930
private def n932 : MainTree := .leaf (mainGapLeaf ![0, 3, 3, 2, 0, 1, 0])
private def n933 : MainTree := .leaf (mainGapLeaf ![0, 3, 3, 2, 0, 1, 1])
private def n931 : MainTree := .split 6 0 n932 n933
private def n927 : MainTree := .split 5 0 n928 n931
private def n936 : MainTree := .leaf (mainGapLeaf ![0, 3, 3, 2, 1, 0, 0])
private def n937 : MainTree := .leaf (mainGapLeaf ![0, 3, 3, 2, 1, 0, 1])
private def n935 : MainTree := .split 6 0 n936 n937
private def n939 : MainTree := .leaf (mainGapLeaf ![0, 3, 3, 2, 1, 1, 0])
private def n940 : MainTree := .leaf (mainGapLeaf ![0, 3, 3, 2, 1, 1, 1])
private def n938 : MainTree := .split 6 0 n939 n940
private def n934 : MainTree := .split 5 0 n935 n938
private def n926 : MainTree := .split 4 0 n927 n934
private def n947 : MainTree := .leaf (mainGapLeaf ![1, 2, 2, 1, 0, 0, 0])
private def n948 : MainTree := .leaf (mainGapLeaf ![1, 2, 3, 1, 0, 0, 0])
private def n946 : MainTree := .split 2 2 n947 n948
private def n949 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 1, 0, 0, 0])
private def n945 : MainTree := .split 1 2 n946 n949
private def n950 : MainTree := .leaf (mainRankLeaf 1 ![1, 3, 3, 2, 0, 0, 0])
private def n944 : MainTree := .split 3 1 n945 n950
private def n952 : MainTree := .leaf (mainRankLeaf 1 ![1, 3, 3, 1, 0, 0, 1])
private def n953 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 2, 0, 0, 1])
private def n951 : MainTree := .split 3 1 n952 n953
private def n943 : MainTree := .split 6 0 n944 n951
private def n957 : MainTree := .leaf (mainGapLeaf ![1, 2, 3, 1, 0, 1, 0])
private def n958 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 1, 0, 1, 0])
private def n956 : MainTree := .split 1 2 n957 n958
private def n959 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 2, 0, 1, 0])
private def n955 : MainTree := .split 3 1 n956 n959
private def n961 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 1, 0, 1, 1])
private def n962 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 2, 0, 1, 1])
private def n960 : MainTree := .split 3 1 n961 n962
private def n954 : MainTree := .split 6 0 n955 n960
private def n942 : MainTree := .split 5 0 n943 n954
private def n967 : MainTree := .leaf (mainGapLeaf ![1, 2, 3, 1, 1, 0, 0])
private def n968 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 1, 1, 0, 0])
private def n966 : MainTree := .split 1 2 n967 n968
private def n969 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 2, 1, 0, 0])
private def n965 : MainTree := .split 3 1 n966 n969
private def n971 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 1, 1, 0, 1])
private def n972 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 2, 1, 0, 1])
private def n970 : MainTree := .split 3 1 n971 n972
private def n964 : MainTree := .split 6 0 n965 n970
private def n975 : MainTree := .leaf (mainRankLeaf 1 ![1, 3, 3, 1, 1, 1, 0])
private def n976 : MainTree := .leaf (mainGapLeaf ![1, 3, 3, 2, 1, 1, 0])
private def n974 : MainTree := .split 3 1 n975 n976
private def n977 : MainTree :=
  .leaf (.rankIndexed 1 768 RankReadouts00.rankReadout977)
private def n973 : MainTree := .split 6 0 n974 n977
private def n963 : MainTree := .split 5 0 n964 n973
private def n941 : MainTree := .split 4 0 n942 n963
private def n925 : MainTree := .split 0 0 n926 n941
private def n981 : MainTree := .leaf (mainGapLeaf ![0, 7, 3, 2, 0, 0, 1])
private def n982 : MainTree := .leaf (mainGapLeaf ![0, 7, 3, 2, 0, 1, 1])
private def n980 : MainTree := .split 5 0 n981 n982
private def n984 : MainTree := .leaf (mainGapLeaf ![0, 7, 3, 2, 1, 0, 1])
private def n985 : MainTree := .leaf (mainGapLeaf ![0, 7, 3, 2, 1, 1, 1])
private def n983 : MainTree := .split 5 0 n984 n985
private def n979 : MainTree := .split 4 0 n980 n983
private def n991 : MainTree := .leaf (mainGapLeaf ![1, 5, 3, 1, 0, 0, 0])
private def n992 : MainTree := .leaf (mainGapLeaf ![1, 5, 3, 2, 0, 0, 0])
private def n990 : MainTree := .split 3 1 n991 n992
private def n993 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 2, 0, 0, 0])
private def n989 : MainTree := .split 1 5 n990 n993
private def n994 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 2, 0, 0, 1])
private def n988 : MainTree := .split 6 0 n989 n994
private def n996 : MainTree := .leaf (mainRankLeaf 1 ![1, 7, 3, 2, 0, 1, 0])
private def n997 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 2, 0, 1, 1])
private def n995 : MainTree := .split 6 0 n996 n997
private def n987 : MainTree := .split 5 0 n988 n995
private def n1000 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 2, 1, 0, 0])
private def n1001 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 2, 1, 0, 1])
private def n999 : MainTree := .split 6 0 n1000 n1001
private def n1003 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 2, 1, 1, 0])
private def n1004 : MainTree := .leaf (mainGapLeaf ![1, 7, 3, 2, 1, 1, 1])
private def n1002 : MainTree := .split 6 0 n1003 n1004
private def n998 : MainTree := .split 5 0 n999 n1002
private def n986 : MainTree := .split 4 0 n987 n998
private def n978 : MainTree := .split 0 0 n979 n986
private def n924 : MainTree := .split 1 3 n925 n978
private def n870 : MainTree := .split 3 0 n871 n924
private def n634 : MainTree := .split 2 1 n635 n870

private theorem c637 : C ![0, 2, 0, 0, 0, 0, 0] ![1, 3, 1, 0, 1, 1, 1] n637 := by
  decide +kernel

private theorem c690 : C ![0, 4, 0, 0, 0, 0, 0] ![1, 7, 1, 0, 1, 1, 1] n690 := by
  decide +kernel

private theorem c636 : C ![0, 2, 0, 0, 0, 0, 0] ![1, 7, 1, 0, 1, 1, 1] n636 := by
  exact checkExponentBoxTree_join c637 c690 (by decide +kernel)

private theorem c731 : C ![0, 2, 0, 1, 0, 0, 0] ![0, 3, 1, 2, 1, 1, 1] n731 := by
  decide +kernel

private theorem c759 : C ![1, 2, 0, 1, 0, 0, 0] ![1, 3, 0, 2, 1, 1, 1] n759 := by
  decide +kernel

private theorem c787 : C ![1, 2, 1, 1, 0, 0, 0] ![1, 3, 1, 2, 0, 1, 1] n787 := by
  decide +kernel

private theorem c806 : C ![1, 2, 1, 1, 1, 0, 0] ![1, 3, 1, 2, 1, 1, 1] n806 := by
  decide +kernel

private theorem c786 : C ![1, 2, 1, 1, 0, 0, 0] ![1, 3, 1, 2, 1, 1, 1] n786 := by
  exact checkExponentBoxTree_join c787 c806 (by decide +kernel)

private theorem c758 : C ![1, 2, 0, 1, 0, 0, 0] ![1, 3, 1, 2, 1, 1, 1] n758 := by
  exact checkExponentBoxTree_join c759 c786 (by decide +kernel)

private theorem c730 : C ![0, 2, 0, 1, 0, 0, 0] ![1, 3, 1, 2, 1, 1, 1] n730 := by
  exact checkExponentBoxTree_join c731 c758 (by decide +kernel)

private theorem c822 : C ![0, 4, 0, 1, 0, 0, 0] ![0, 7, 1, 2, 1, 1, 1] n822 := by
  decide +kernel

private theorem c838 : C ![1, 4, 0, 1, 0, 0, 0] ![1, 7, 0, 2, 1, 1, 1] n838 := by
  decide +kernel

private theorem c854 : C ![1, 4, 1, 1, 0, 0, 0] ![1, 7, 1, 2, 0, 1, 1] n854 := by
  decide +kernel

private theorem c864 : C ![1, 4, 1, 1, 1, 0, 0] ![1, 7, 1, 2, 1, 0, 1] n864 := by
  decide +kernel

private theorem c867 : C ![1, 4, 1, 1, 1, 1, 0] ![1, 7, 1, 2, 1, 1, 1] n867 := by
  decide +kernel

private theorem c863 : C ![1, 4, 1, 1, 1, 0, 0] ![1, 7, 1, 2, 1, 1, 1] n863 := by
  exact checkExponentBoxTree_join c864 c867 (by decide +kernel)

private theorem c853 : C ![1, 4, 1, 1, 0, 0, 0] ![1, 7, 1, 2, 1, 1, 1] n853 := by
  exact checkExponentBoxTree_join c854 c863 (by decide +kernel)

private theorem c837 : C ![1, 4, 0, 1, 0, 0, 0] ![1, 7, 1, 2, 1, 1, 1] n837 := by
  exact checkExponentBoxTree_join c838 c853 (by decide +kernel)

private theorem c821 : C ![0, 4, 0, 1, 0, 0, 0] ![1, 7, 1, 2, 1, 1, 1] n821 := by
  exact checkExponentBoxTree_join c822 c837 (by decide +kernel)

private theorem c729 : C ![0, 2, 0, 1, 0, 0, 0] ![1, 7, 1, 2, 1, 1, 1] n729 := by
  exact checkExponentBoxTree_join c730 c821 (by decide +kernel)

private theorem c635 : C ![0, 2, 0, 0, 0, 0, 0] ![1, 7, 1, 2, 1, 1, 1] n635 := by
  exact checkExponentBoxTree_join c636 c729 (by decide +kernel)

private theorem c872 : C ![0, 2, 2, 0, 0, 0, 0] ![1, 3, 3, 0, 1, 1, 1] n872 := by
  decide +kernel

private theorem c902 : C ![0, 4, 2, 0, 0, 0, 0] ![0, 7, 3, 0, 1, 1, 1] n902 := by
  decide +kernel

private theorem c909 : C ![1, 4, 2, 0, 0, 0, 0] ![1, 7, 3, 0, 1, 1, 1] n909 := by
  decide +kernel

private theorem c901 : C ![0, 4, 2, 0, 0, 0, 0] ![1, 7, 3, 0, 1, 1, 1] n901 := by
  exact checkExponentBoxTree_join c902 c909 (by decide +kernel)

private theorem c871 : C ![0, 2, 2, 0, 0, 0, 0] ![1, 7, 3, 0, 1, 1, 1] n871 := by
  exact checkExponentBoxTree_join c872 c901 (by decide +kernel)

private theorem c926 : C ![0, 2, 2, 1, 0, 0, 0] ![0, 3, 3, 2, 1, 1, 1] n926 := by
  decide +kernel

private theorem c942 : C ![1, 2, 2, 1, 0, 0, 0] ![1, 3, 3, 2, 0, 1, 1] n942 := by
  decide +kernel

private theorem c964 : C ![1, 2, 2, 1, 1, 0, 0] ![1, 3, 3, 2, 1, 0, 1] n964 := by
  decide +kernel

private theorem c974 : C ![1, 2, 2, 1, 1, 1, 0] ![1, 3, 3, 2, 1, 1, 0] n974 := by
  decide +kernel

private theorem c977 : C ![1, 2, 2, 1, 1, 1, 1] ![1, 3, 3, 2, 1, 1, 1] n977 := by
  decide +kernel

private theorem c973 : C ![1, 2, 2, 1, 1, 1, 0] ![1, 3, 3, 2, 1, 1, 1] n973 := by
  exact checkExponentBoxTree_join c974 c977 (by decide +kernel)

private theorem c963 : C ![1, 2, 2, 1, 1, 0, 0] ![1, 3, 3, 2, 1, 1, 1] n963 := by
  exact checkExponentBoxTree_join c964 c973 (by decide +kernel)

private theorem c941 : C ![1, 2, 2, 1, 0, 0, 0] ![1, 3, 3, 2, 1, 1, 1] n941 := by
  exact checkExponentBoxTree_join c942 c963 (by decide +kernel)

private theorem c925 : C ![0, 2, 2, 1, 0, 0, 0] ![1, 3, 3, 2, 1, 1, 1] n925 := by
  exact checkExponentBoxTree_join c926 c941 (by decide +kernel)

private theorem c979 : C ![0, 4, 2, 1, 0, 0, 0] ![0, 7, 3, 2, 1, 1, 1] n979 := by
  decide +kernel

private theorem c988 : C ![1, 4, 2, 1, 0, 0, 0] ![1, 7, 3, 2, 0, 0, 1] n988 := by
  decide +kernel

private theorem c995 : C ![1, 4, 2, 1, 0, 1, 0] ![1, 7, 3, 2, 0, 1, 1] n995 := by
  decide +kernel

private theorem c987 : C ![1, 4, 2, 1, 0, 0, 0] ![1, 7, 3, 2, 0, 1, 1] n987 := by
  exact checkExponentBoxTree_join c988 c995 (by decide +kernel)

private theorem c999 : C ![1, 4, 2, 1, 1, 0, 0] ![1, 7, 3, 2, 1, 0, 1] n999 := by
  decide +kernel

private theorem c1003 : C ![1, 4, 2, 1, 1, 1, 0] ![1, 7, 3, 2, 1, 1, 0] n1003 := by
  decide +kernel

private theorem c1004 : C ![1, 4, 2, 1, 1, 1, 1] ![1, 7, 3, 2, 1, 1, 1] n1004 := by
  decide +kernel

private theorem c1002 : C ![1, 4, 2, 1, 1, 1, 0] ![1, 7, 3, 2, 1, 1, 1] n1002 := by
  exact checkExponentBoxTree_join c1003 c1004 (by decide +kernel)

private theorem c998 : C ![1, 4, 2, 1, 1, 0, 0] ![1, 7, 3, 2, 1, 1, 1] n998 := by
  exact checkExponentBoxTree_join c999 c1002 (by decide +kernel)

private theorem c986 : C ![1, 4, 2, 1, 0, 0, 0] ![1, 7, 3, 2, 1, 1, 1] n986 := by
  exact checkExponentBoxTree_join c987 c998 (by decide +kernel)

private theorem c978 : C ![0, 4, 2, 1, 0, 0, 0] ![1, 7, 3, 2, 1, 1, 1] n978 := by
  exact checkExponentBoxTree_join c979 c986 (by decide +kernel)

private theorem c924 : C ![0, 2, 2, 1, 0, 0, 0] ![1, 7, 3, 2, 1, 1, 1] n924 := by
  exact checkExponentBoxTree_join c925 c978 (by decide +kernel)

private theorem c870 : C ![0, 2, 2, 0, 0, 0, 0] ![1, 7, 3, 2, 1, 1, 1] n870 := by
  exact checkExponentBoxTree_join c871 c924 (by decide +kernel)

private theorem c634 : C ![0, 2, 0, 0, 0, 0, 0] ![1, 7, 3, 2, 1, 1, 1] n634 := by
  exact checkExponentBoxTree_join c635 c870 (by decide +kernel)

/-- The complete binary certificate at this subtree root. -/
def certificate : MainTree := n634

theorem chunk_checked :
    checkExponentBoxTree mainScale boxPrimes lo hi certificate = true := c634

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.Main01
