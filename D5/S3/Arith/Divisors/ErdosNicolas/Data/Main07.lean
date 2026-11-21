/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Main07
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main07.chunk_checked
   digest: Exact numerical and binary coverage certificate for the main exponent box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainSupport
import D5.S3.Arith.Divisors.ErdosNicolas.Data.RankReadouts01

/-! Opaque numerical subproofs bound temporary kernel reduction memory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.Main07

private abbrev C (lo hi : Fin 7 → ℕ) (tree : MainTree) : Prop :=
  checkExponentBoxTree mainScale boxPrimes lo hi tree = true

/-- Lower exponents at this subtree root. -/
def lo : Fin 7 → ℕ := ![4, 2, 0, 1, 0, 0, 0]

/-- Upper exponents at the same root. -/
def hi : Fin 7 → ℕ := ![8, 3, 1, 2, 1, 1, 1]

private def n2631 : MainTree := .leaf (mainFullLeaf ![4, 2, 0, 1, 0, 0, 0])
private def n2632 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 1, 0, 0, 0])
private def n2630 : MainTree := .split 0 4 n2631 n2632
private def n2634 : MainTree := .leaf (mainGapLeaf ![4, 3, 0, 1, 0, 0, 0])
private def n2635 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 1, 0, 0, 0])
private def n2633 : MainTree := .split 0 4 n2634 n2635
private def n2629 : MainTree := .split 1 2 n2630 n2633
private def n2637 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 2, 0, 0, 0])
private def n2638 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 2, 0, 0, 0])
private def n2636 : MainTree := .split 1 2 n2637 n2638
private def n2628 : MainTree := .split 3 1 n2629 n2636
private def n2642 : MainTree := .leaf (mainGapLeaf ![6, 2, 0, 1, 0, 0, 0])
private def n2643 : MainTree := .leaf (mainGapLeaf ![8, 2, 0, 1, 0, 0, 0])
private def n2641 : MainTree := .split 0 6 n2642 n2643
private def n2644 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 1, 0, 0, 0])
private def n2640 : MainTree := .split 1 2 n2641 n2644
private def n2646 : MainTree := .leaf (mainGapLeaf ![8, 2, 0, 2, 0, 0, 0])
private def n2647 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 2, 0, 0, 0])
private def n2645 : MainTree := .split 1 2 n2646 n2647
private def n2639 : MainTree := .split 3 1 n2640 n2645
private def n2627 : MainTree := .split 0 5 n2628 n2639
private def n2651 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 1, 0, 0, 1])
private def n2652 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 1, 0, 0, 1])
private def n2650 : MainTree := .split 1 2 n2651 n2652
private def n2653 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 2, 0, 0, 1])
private def n2649 : MainTree := .split 3 1 n2650 n2653
private def n2655 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 1, 0, 0, 1])
private def n2656 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 2, 0, 0, 1])
private def n2654 : MainTree := .split 3 1 n2655 n2656
private def n2648 : MainTree := .split 0 5 n2649 n2654
private def n2626 : MainTree := .split 6 0 n2627 n2648
private def n2661 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 1, 0, 1, 0])
private def n2662 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 1, 0, 1, 0])
private def n2660 : MainTree := .split 1 2 n2661 n2662
private def n2663 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 2, 0, 1, 0])
private def n2659 : MainTree := .split 3 1 n2660 n2663
private def n2666 : MainTree := .leaf (mainGapLeaf ![8, 2, 0, 1, 0, 1, 0])
private def n2667 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 1, 0, 1, 0])
private def n2665 : MainTree := .split 1 2 n2666 n2667
private def n2668 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 2, 0, 1, 0])
private def n2664 : MainTree := .split 3 1 n2665 n2668
private def n2658 : MainTree := .split 0 5 n2659 n2664
private def n2672 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 1, 0, 1, 1])
private def n2673 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 1, 0, 1, 1])
private def n2671 : MainTree := .split 1 2 n2672 n2673
private def n2674 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 2, 0, 1, 1])
private def n2670 : MainTree := .split 3 1 n2671 n2674
private def n2676 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 1, 0, 1, 1])
private def n2677 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 2, 0, 1, 1])
private def n2675 : MainTree := .split 3 1 n2676 n2677
private def n2669 : MainTree := .split 0 5 n2670 n2675
private def n2657 : MainTree := .split 6 0 n2658 n2669
private def n2625 : MainTree := .split 5 0 n2626 n2657
private def n2684 : MainTree := .leaf (mainGapLeaf ![4, 2, 0, 1, 1, 0, 0])
private def n2685 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 1, 1, 0, 0])
private def n2683 : MainTree := .split 0 4 n2684 n2685
private def n2686 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 1, 1, 0, 0])
private def n2682 : MainTree := .split 1 2 n2683 n2686
private def n2688 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 2, 1, 0, 0])
private def n2689 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 2, 1, 0, 0])
private def n2687 : MainTree := .split 1 2 n2688 n2689
private def n2681 : MainTree := .split 3 1 n2682 n2687
private def n2692 : MainTree := .leaf (mainGapLeaf ![8, 2, 0, 1, 1, 0, 0])
private def n2693 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 1, 1, 0, 0])
private def n2691 : MainTree := .split 1 2 n2692 n2693
private def n2694 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 2, 1, 0, 0])
private def n2690 : MainTree := .split 3 1 n2691 n2694
private def n2680 : MainTree := .split 0 5 n2681 n2690
private def n2698 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 1, 1, 0, 1])
private def n2699 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 1, 1, 0, 1])
private def n2697 : MainTree := .split 1 2 n2698 n2699
private def n2700 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 2, 1, 0, 1])
private def n2696 : MainTree := .split 3 1 n2697 n2700
private def n2702 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 1, 1, 0, 1])
private def n2703 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 2, 1, 0, 1])
private def n2701 : MainTree := .split 3 1 n2702 n2703
private def n2695 : MainTree := .split 0 5 n2696 n2701
private def n2679 : MainTree := .split 6 0 n2680 n2695
private def n2708 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 1, 1, 1, 0])
private def n2709 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 1, 1, 1, 0])
private def n2707 : MainTree := .split 1 2 n2708 n2709
private def n2710 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 2, 1, 1, 0])
private def n2706 : MainTree := .split 3 1 n2707 n2710
private def n2712 : MainTree := .leaf (mainRankLeaf 1 ![8, 3, 0, 1, 1, 1, 0])
private def n2713 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 2, 1, 1, 0])
private def n2711 : MainTree := .split 3 1 n2712 n2713
private def n2705 : MainTree := .split 0 5 n2706 n2711
private def n2716 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 1, 1, 1, 1])
private def n2717 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 2, 1, 1, 1])
private def n2715 : MainTree := .split 3 1 n2716 n2717
private def n2718 : MainTree :=
  .leaf (.rankIndexed 1 864 RankReadouts01.rankReadout2718)
private def n2714 : MainTree := .split 0 5 n2715 n2718
private def n2704 : MainTree := .split 6 0 n2705 n2714
private def n2678 : MainTree := .split 5 0 n2679 n2704
private def n2624 : MainTree := .split 4 0 n2625 n2678
private def n2726 : MainTree := .leaf (mainFullLeaf ![4, 2, 1, 1, 0, 0, 0])
private def n2727 : MainTree := .leaf (mainFullLeaf ![5, 2, 1, 1, 0, 0, 0])
private def n2725 : MainTree := .split 0 4 n2726 n2727
private def n2729 : MainTree := .leaf (mainFullLeaf ![4, 3, 1, 1, 0, 0, 0])
private def n2730 : MainTree := .leaf (mainRankLeaf 2 ![5, 3, 1, 1, 0, 0, 0])
private def n2728 : MainTree := .split 0 4 n2729 n2730
private def n2724 : MainTree := .split 1 2 n2725 n2728
private def n2733 : MainTree := .leaf (mainGapLeaf ![4, 2, 1, 2, 0, 0, 0])
private def n2734 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 2, 0, 0, 0])
private def n2732 : MainTree := .split 0 4 n2733 n2734
private def n2735 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 2, 0, 0, 0])
private def n2731 : MainTree := .split 1 2 n2732 n2735
private def n2723 : MainTree := .split 3 1 n2724 n2731
private def n2739 : MainTree := .leaf (mainFullLeaf ![6, 2, 1, 1, 0, 0, 0])
private def n2741 : MainTree := .leaf (mainGapLeaf ![7, 2, 1, 1, 0, 0, 0])
private def n2742 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 1, 0, 0, 0])
private def n2740 : MainTree := .split 0 7 n2741 n2742
private def n2738 : MainTree := .split 0 6 n2739 n2740
private def n2744 : MainTree := .leaf (mainGapLeaf ![6, 3, 1, 1, 0, 0, 0])
private def n2745 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 1, 0, 0, 0])
private def n2743 : MainTree := .split 0 6 n2744 n2745
private def n2737 : MainTree := .split 1 2 n2738 n2743
private def n2747 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 2, 0, 0, 0])
private def n2748 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 2, 0, 0, 0])
private def n2746 : MainTree := .split 1 2 n2747 n2748
private def n2736 : MainTree := .split 3 1 n2737 n2746
private def n2722 : MainTree := .split 0 5 n2723 n2736
private def n2753 : MainTree := .leaf (mainRankLeaf 2 ![4, 2, 1, 1, 0, 0, 1])
private def n2754 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 1, 0, 0, 1])
private def n2752 : MainTree := .split 0 4 n2753 n2754
private def n2756 : MainTree := .leaf (mainGapLeaf ![4, 3, 1, 1, 0, 0, 1])
private def n2757 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 1, 0, 0, 1])
private def n2755 : MainTree := .split 0 4 n2756 n2757
private def n2751 : MainTree := .split 1 2 n2752 n2755
private def n2759 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 2, 0, 0, 1])
private def n2760 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 2, 0, 0, 1])
private def n2758 : MainTree := .split 1 2 n2759 n2760
private def n2750 : MainTree := .split 3 1 n2751 n2758
private def n2763 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 1, 0, 0, 1])
private def n2764 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 1, 0, 0, 1])
private def n2762 : MainTree := .split 1 2 n2763 n2764
private def n2765 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 2, 0, 0, 1])
private def n2761 : MainTree := .split 3 1 n2762 n2765
private def n2749 : MainTree := .split 0 5 n2750 n2761
private def n2721 : MainTree := .split 6 0 n2722 n2749
private def n2771 : MainTree := .leaf (mainRankLeaf 2 ![4, 2, 1, 1, 0, 1, 0])
private def n2772 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 1, 0, 1, 0])
private def n2770 : MainTree := .split 0 4 n2771 n2772
private def n2774 : MainTree := .leaf (mainGapLeaf ![4, 3, 1, 1, 0, 1, 0])
private def n2775 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 1, 0, 1, 0])
private def n2773 : MainTree := .split 0 4 n2774 n2775
private def n2769 : MainTree := .split 1 2 n2770 n2773
private def n2777 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 2, 0, 1, 0])
private def n2778 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 2, 0, 1, 0])
private def n2776 : MainTree := .split 1 2 n2777 n2778
private def n2768 : MainTree := .split 3 1 n2769 n2776
private def n2782 : MainTree := .leaf (mainGapLeaf ![6, 2, 1, 1, 0, 1, 0])
private def n2783 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 1, 0, 1, 0])
private def n2781 : MainTree := .split 0 6 n2782 n2783
private def n2784 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 1, 0, 1, 0])
private def n2780 : MainTree := .split 1 2 n2781 n2784
private def n2785 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 2, 0, 1, 0])
private def n2779 : MainTree := .split 3 1 n2780 n2785
private def n2767 : MainTree := .split 0 5 n2768 n2779
private def n2789 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 1, 0, 1, 1])
private def n2790 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 1, 0, 1, 1])
private def n2788 : MainTree := .split 1 2 n2789 n2790
private def n2791 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 2, 0, 1, 1])
private def n2787 : MainTree := .split 3 1 n2788 n2791
private def n2793 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 1, 0, 1, 1])
private def n2794 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 2, 0, 1, 1])
private def n2792 : MainTree := .split 3 1 n2793 n2794
private def n2786 : MainTree := .split 0 5 n2787 n2792
private def n2766 : MainTree := .split 6 0 n2767 n2786
private def n2720 : MainTree := .split 5 0 n2721 n2766
private def n2801 : MainTree := .leaf (mainFullLeaf ![4, 2, 1, 1, 1, 0, 0])
private def n2802 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 1, 1, 0, 0])
private def n2800 : MainTree := .split 0 4 n2801 n2802
private def n2804 : MainTree := .leaf (mainGapLeaf ![4, 3, 1, 1, 1, 0, 0])
private def n2805 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 1, 1, 0, 0])
private def n2803 : MainTree := .split 0 4 n2804 n2805
private def n2799 : MainTree := .split 1 2 n2800 n2803
private def n2808 : MainTree := .leaf (mainGapLeaf ![4, 2, 1, 2, 1, 0, 0])
private def n2809 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 2, 1, 0, 0])
private def n2807 : MainTree := .split 0 4 n2808 n2809
private def n2810 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 2, 1, 0, 0])
private def n2806 : MainTree := .split 1 2 n2807 n2810
private def n2798 : MainTree := .split 3 1 n2799 n2806
private def n2814 : MainTree := .leaf (mainGapLeaf ![6, 2, 1, 1, 1, 0, 0])
private def n2815 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 1, 1, 0, 0])
private def n2813 : MainTree := .split 0 6 n2814 n2815
private def n2816 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 1, 1, 0, 0])
private def n2812 : MainTree := .split 1 2 n2813 n2816
private def n2818 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 2, 1, 0, 0])
private def n2819 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 2, 1, 0, 0])
private def n2817 : MainTree := .split 1 2 n2818 n2819
private def n2811 : MainTree := .split 3 1 n2812 n2817
private def n2797 : MainTree := .split 0 5 n2798 n2811
private def n2824 : MainTree := .leaf (mainGapLeaf ![4, 2, 1, 1, 1, 0, 1])
private def n2825 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 1, 1, 0, 1])
private def n2823 : MainTree := .split 0 4 n2824 n2825
private def n2826 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 1, 1, 0, 1])
private def n2822 : MainTree := .split 1 2 n2823 n2826
private def n2828 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 2, 1, 0, 1])
private def n2829 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 2, 1, 0, 1])
private def n2827 : MainTree := .split 1 2 n2828 n2829
private def n2821 : MainTree := .split 3 1 n2822 n2827
private def n2832 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 1, 1, 0, 1])
private def n2833 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 1, 1, 0, 1])
private def n2831 : MainTree := .split 1 2 n2832 n2833
private def n2834 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 2, 1, 0, 1])
private def n2830 : MainTree := .split 3 1 n2831 n2834
private def n2820 : MainTree := .split 0 5 n2821 n2830
private def n2796 : MainTree := .split 6 0 n2797 n2820
private def n2840 : MainTree := .leaf (mainGapLeaf ![4, 2, 1, 1, 1, 1, 0])
private def n2841 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 1, 1, 1, 0])
private def n2839 : MainTree := .split 0 4 n2840 n2841
private def n2842 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 1, 1, 1, 0])
private def n2838 : MainTree := .split 1 2 n2839 n2842
private def n2844 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 2, 1, 1, 0])
private def n2845 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 2, 1, 1, 0])
private def n2843 : MainTree := .split 1 2 n2844 n2845
private def n2837 : MainTree := .split 3 1 n2838 n2843
private def n2848 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 1, 1, 1, 0])
private def n2849 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 1, 1, 1, 0])
private def n2847 : MainTree := .split 1 2 n2848 n2849
private def n2850 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 2, 1, 1, 0])
private def n2846 : MainTree := .split 3 1 n2847 n2850
private def n2836 : MainTree := .split 0 5 n2837 n2846
private def n2854 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 1, 1, 1, 1])
private def n2855 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 1, 1, 1, 1])
private def n2853 : MainTree := .split 1 2 n2854 n2855
private def n2856 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 2, 1, 1, 1])
private def n2852 : MainTree := .split 3 1 n2853 n2856
private def n2858 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 1, 1, 1, 1])
private def d2859 : List ℕ := [
    0x64780100c1068f0084188120309380c407066090001600120640023600106c060480020780183000c060000,
    0x4843c4320d07e00289c2440326e18c0f2018a80701811e806a400683909200e1503040c4083300f06107c258,
    0x32012a5809800a328fc3041b29e0263d8364330308406c0018d02411506d06d540250a200486261037108050,
    0x219260402723184844a1008403193003a6025a13a19ac00124f40286903249103c79000cce2d0220c08d8924,
    0x5501f0744083127887e091045220618704b8e401b1d07849c4f2250214092b815818a6295c039788248ccb38,
    0x494de00f0f9908548362597f00cce65580245019924c3c2084aa1c00f5380c30356403e9e0a28028cd12d109,
    0x6d00389e1a8990924582a203a6f0a88e2a9060c9831c8a03d9480119041a998aa4620728726300f2860c2858,
    0xa4c665c0f3140a3006866c30349003f2618a8470a145004e82a5a048c3d5f001b375205740d40d2fd18d1c9,
    0xc10145219f07b82aa881b60cad4068d42254fc4223647a0a28059a4272b61228ac230c2a1c0de3735110912c,
    0x22998054b0636b2806d8884f5505d419409c4a65a3da138a26140ce0c67f134588084c24b83621ba9f1089a2,
    0x60a5b0ec3ca9f06793ce045a4134f61127b20b2bc1b32c0d3066926324b0020cb2798269b0807342b51a01fa,
    0x461088ceb3c5a298888b03561270b5084ba09d892c10323808259ea9624104c82a849241a50cb4c87e5cc03e,
    0x800ae81d9d42d2f193ad603365219d6018d0950871e9ae80a64d15c104d267418e246af01eb2812d920813c9,
    0x53122adc0724bcce5c910d55874a4c8ecc7020539a20818634f325212ae0013101ae5230ad42118e1d130b94,
    0x3a2f0db855c454058a269066c796682512162e155025ae27103f1591d5392a840a316c915cc581fcf1449a2c,
    0x410fea9431439caa71a07d1d35690e142812172d424e3c6df07ebe8046558e14895e01c67125d7f8e441bb22,
    0x666b826624d168a9989155880398e0e320f75310d4e130e4d02d3218a9301bd0fb5288a40ac860dccd71025b,
    0x27c864d55a4c201666524b7c82c9bc81fa306fa429535d81b5ac54acf04c98f3f98a4735b6292ab204cd6141,
    0x1c68594154976015898da263b2f2288f77c429148c83861871750d60d6811fb2a5b20c44e59786d439718a84,
    0xb010e8ddb545d2356a312e7eac6d644babd0f505128e6d203c9e9a9c34b71014c92399a058b0e5470f0deca8,
    0xa24a36160676a586469a6c402fcdd058c08cc34ba3667a4856801a65024ef062da0ab685239f415c469f0d14,
    0x7a2a2d1c42a34ad10ff2d94d599056919b14c2e5217287237c465d84fd51509bac25b063050533e4f7a5c8a1,
    0x6c73f13ed68346b59a16098e0458f8e627ba2aebe51136f288b208a6a350e783aa32c4ad6204596c279b2e50,
    0xba990044cfa4f7051d4995c0c13cf74b57b6275c402eaf5aa24a16269d0a4679fd4d2e7161589086770b8bce,
    0x10c586e934d9d849e09193658b0659c60c98419e689b46909a492d5b80999a09fb73445730b075685b8ed4a1,
    0x84b245a5af89d4996022be7320fd9516d3b3929e5d644653e4cf94cd30cfb02ad38d87b66c1135640b64f579,
    0x91d08ede07667b8a131b968054c0eb2b193a5af1e085ba29deb122429504701db08d4958f5b8420b5d81595e,
    0xac3a50a4dba67735234a5521e2f157575936576240eec7420eaa22281d3a4c7abd6531704bb82c9240d4e231,
    0x28c8874940db5879e692537d82e9c0827ae7480e348d2b6bd03ace6aa4e5740326802aee2d1d578edd11729a,
    0x43d396a8c0b77017ad5325988dfa2c8ff7d48b54cc8bc48bcadc8734be831ff393a58ab6cc1d36e43b6af639,
    0x5e353a71e7c26cff591c569857c14b371aba8ac0b945d22cdf112e4415347380b9a54c5955c4438b8d83f8eb,
    0xded6b10a09cf4feeca52962a73cbe36ec6b56d0ed0835c50f0a2e20bb33ad4a4f16cdf5f4d1c2af108e1b5c,
    0xc3c81970ccdcd82d553d926272b0bd4411cf8cef0286a9a86dda135b4d8482dc557cd305bdd1a52b21e1a2ee,
    0x356b7ad2e119971e08f66a7ca2cec243ea326fe552ed6b352dd9679266c7d664be8a77b05336dcb0a4e191ad,
    0x42f40941c1c7638382bda33ed2f5f18a5a2d60b58356863875758d740afddd22cab225e6f53d66d74114293f,
    0x87623aed355a8f3d1d712f834b265de54bd2f5451a8f4790bb0daddb909b901ba223b63b34b0f2ed0f654ddc,
    0xafd44f5616685ad4e7926d58ce86c68472ead9f293d3ad88ea809a7d40d1b06adb8e87d7330af23745653581,
    0x8c827dc5651473aaa4b42bb88d14ffa6b73d996c5d383bd294b9e4411b3faeca7fad4eb60ce0b8e47cdefb8c,
    0x73ba21972c38c4777273cf46d3f6b4e9c5af709a1cdc8e245f31ab6afb28cb2dd6c8422e0b4f175665d62cb7,
    0x9278b17d5c14cf019cdd3456a5bceddd5acd9067d94ed3505703db48dc7be6d38905f5ef54c952c6d3d7e4ee,
    0x65717b25df853d5951994db7da659fe2a8db366992b393f1331f087ba689a76c13b64cb5c3461c9a41d1ac27,
    0x5ed6f43be2972fa0a01d9ca6275dbb63dac68974b14b9ad6c635a5717ce16bbd242bf1297cd569d7a1202abf,
    0xd02c9e6345bbe8dd517a9bd2b89adda0e9ab9d05ed2e55f66a248efc7755511c0f7796ba2ebee7074894ec8f,
    0x98adfdf5d1ed70d7b12af341b9f9ffd2db337c9b9d5fa1851f49ae6b5b34f393ed17711a909c75eb39ea9bba,
    0xa3b2ba21de26bb53ddb67d26f15e61e5cbe2a5e1b6235ca82ecb671a56c5cbf445c6f7910fd0a7738582fdab,
    0xb272b4bdd06bc2a1ddada7c271e9f3d86a37ad21aaef6b79ed675952fb7b9b7e5aa126bf0aae399f1f3370b7,
    0x9ece9565e56bd6f5d1f505d48b7ee547923f9aec2c3f95777a0f3b359b2fef68a7cb3aca19e1fb9881dd366d,
    0xccf4ea53e4611f76e7abaf836e3b2aa3dd5d0bee4a6f74763e9e177bbb5ba81ea283b83e3b1f7a2f60f58b57,
    0xb6d195c5eab92ebfae2b9fd154e4efe459ff5af4f4de8e6e36bfead2cf3cf462c78cd94eb6a3bb8da85a3c75,
    0x70f49b16afbd0d01e9adfaace53f4ddb58df36e272fd9dfa2597c63c9f7f11be9dc5d70e6ed3656f75f21c17,
    0xb37439dedaf7df48f5e2f7d07676fb377d2f35f3b0bfa4b12eabbbed0b17efca9fb7f8aecf53389b8fd13db3,
    0xcdf2bef1bb7cbbada1bd972ff79685e178fd47f5cb5fcff97af9d0d5cf9ce23de677731efaebac4e83f3ad2f,
    0x8cf71e9de4771fabf4753dadfa8e3bcf7cae8ff52dcba7d77e0feb3b9ae9e83ea68f761f5aacfbdf96ee747d,
    0xd7f7ff47d3fd4f73f5bc7fcbf79f5dd0fd7b7df3bbbfd7d67e93e87bf713efee2fa6f6dd7fe8bbfda7e6fe8d]
private def a2859 : List ℕ :=
  certificateIndexedDivisors (exponentFactors boxPrimes ![8, 3, 1, 2, 1, 1, 1])
    2048 32 1728 d2859
private def n2859 : MainTree := .leaf (mainGapLeafOfDivisors ![8, 3, 1, 2, 1, 1, 1] a2859)
private def n2857 : MainTree := .split 3 1 n2858 n2859
private def n2851 : MainTree := .split 0 5 n2852 n2857
private def n2835 : MainTree := .split 6 0 n2836 n2851
private def n2795 : MainTree := .split 5 0 n2796 n2835
private def n2719 : MainTree := .split 4 0 n2720 n2795
private def n2623 : MainTree := .split 2 0 n2624 n2719

private theorem c2626 : C ![4, 2, 0, 1, 0, 0, 0] ![8, 3, 0, 2, 0, 0, 1] n2626 := by
  decide +kernel

private theorem c2658 : C ![4, 2, 0, 1, 0, 1, 0] ![8, 3, 0, 2, 0, 1, 0] n2658 := by
  decide +kernel

private theorem c2669 : C ![4, 2, 0, 1, 0, 1, 1] ![8, 3, 0, 2, 0, 1, 1] n2669 := by
  decide +kernel

private theorem c2657 : C ![4, 2, 0, 1, 0, 1, 0] ![8, 3, 0, 2, 0, 1, 1] n2657 := by
  exact checkExponentBoxTree_join c2658 c2669 (by decide +kernel)

private theorem c2625 : C ![4, 2, 0, 1, 0, 0, 0] ![8, 3, 0, 2, 0, 1, 1] n2625 := by
  exact checkExponentBoxTree_join c2626 c2657 (by decide +kernel)

private theorem c2680 : C ![4, 2, 0, 1, 1, 0, 0] ![8, 3, 0, 2, 1, 0, 0] n2680 := by
  decide +kernel

private theorem c2695 : C ![4, 2, 0, 1, 1, 0, 1] ![8, 3, 0, 2, 1, 0, 1] n2695 := by
  decide +kernel

private theorem c2679 : C ![4, 2, 0, 1, 1, 0, 0] ![8, 3, 0, 2, 1, 0, 1] n2679 := by
  exact checkExponentBoxTree_join c2680 c2695 (by decide +kernel)

private theorem c2705 : C ![4, 2, 0, 1, 1, 1, 0] ![8, 3, 0, 2, 1, 1, 0] n2705 := by
  decide +kernel

private theorem c2715 : C ![4, 2, 0, 1, 1, 1, 1] ![5, 3, 0, 2, 1, 1, 1] n2715 := by
  decide +kernel

private theorem c2718 : C ![6, 2, 0, 1, 1, 1, 1] ![8, 3, 0, 2, 1, 1, 1] n2718 := by
  decide +kernel

private theorem c2714 : C ![4, 2, 0, 1, 1, 1, 1] ![8, 3, 0, 2, 1, 1, 1] n2714 := by
  exact checkExponentBoxTree_join c2715 c2718 (by decide +kernel)

private theorem c2704 : C ![4, 2, 0, 1, 1, 1, 0] ![8, 3, 0, 2, 1, 1, 1] n2704 := by
  exact checkExponentBoxTree_join c2705 c2714 (by decide +kernel)

private theorem c2678 : C ![4, 2, 0, 1, 1, 0, 0] ![8, 3, 0, 2, 1, 1, 1] n2678 := by
  exact checkExponentBoxTree_join c2679 c2704 (by decide +kernel)

private theorem c2624 : C ![4, 2, 0, 1, 0, 0, 0] ![8, 3, 0, 2, 1, 1, 1] n2624 := by
  exact checkExponentBoxTree_join c2625 c2678 (by decide +kernel)

private theorem c2723 : C ![4, 2, 1, 1, 0, 0, 0] ![5, 3, 1, 2, 0, 0, 0] n2723 := by
  decide +kernel

private theorem c2736 : C ![6, 2, 1, 1, 0, 0, 0] ![8, 3, 1, 2, 0, 0, 0] n2736 := by
  decide +kernel

private theorem c2722 : C ![4, 2, 1, 1, 0, 0, 0] ![8, 3, 1, 2, 0, 0, 0] n2722 := by
  exact checkExponentBoxTree_join c2723 c2736 (by decide +kernel)

private theorem c2750 : C ![4, 2, 1, 1, 0, 0, 1] ![5, 3, 1, 2, 0, 0, 1] n2750 := by
  decide +kernel

private theorem c2761 : C ![6, 2, 1, 1, 0, 0, 1] ![8, 3, 1, 2, 0, 0, 1] n2761 := by
  decide +kernel

private theorem c2749 : C ![4, 2, 1, 1, 0, 0, 1] ![8, 3, 1, 2, 0, 0, 1] n2749 := by
  exact checkExponentBoxTree_join c2750 c2761 (by decide +kernel)

private theorem c2721 : C ![4, 2, 1, 1, 0, 0, 0] ![8, 3, 1, 2, 0, 0, 1] n2721 := by
  exact checkExponentBoxTree_join c2722 c2749 (by decide +kernel)

private theorem c2768 : C ![4, 2, 1, 1, 0, 1, 0] ![5, 3, 1, 2, 0, 1, 0] n2768 := by
  decide +kernel

private theorem c2779 : C ![6, 2, 1, 1, 0, 1, 0] ![8, 3, 1, 2, 0, 1, 0] n2779 := by
  decide +kernel

private theorem c2767 : C ![4, 2, 1, 1, 0, 1, 0] ![8, 3, 1, 2, 0, 1, 0] n2767 := by
  exact checkExponentBoxTree_join c2768 c2779 (by decide +kernel)

private theorem c2787 : C ![4, 2, 1, 1, 0, 1, 1] ![5, 3, 1, 2, 0, 1, 1] n2787 := by
  decide +kernel

private theorem c2792 : C ![6, 2, 1, 1, 0, 1, 1] ![8, 3, 1, 2, 0, 1, 1] n2792 := by
  decide +kernel

private theorem c2786 : C ![4, 2, 1, 1, 0, 1, 1] ![8, 3, 1, 2, 0, 1, 1] n2786 := by
  exact checkExponentBoxTree_join c2787 c2792 (by decide +kernel)

private theorem c2766 : C ![4, 2, 1, 1, 0, 1, 0] ![8, 3, 1, 2, 0, 1, 1] n2766 := by
  exact checkExponentBoxTree_join c2767 c2786 (by decide +kernel)

private theorem c2720 : C ![4, 2, 1, 1, 0, 0, 0] ![8, 3, 1, 2, 0, 1, 1] n2720 := by
  exact checkExponentBoxTree_join c2721 c2766 (by decide +kernel)

private theorem c2799 : C ![4, 2, 1, 1, 1, 0, 0] ![5, 3, 1, 1, 1, 0, 0] n2799 := by
  decide +kernel

private theorem c2806 : C ![4, 2, 1, 2, 1, 0, 0] ![5, 3, 1, 2, 1, 0, 0] n2806 := by
  decide +kernel

private theorem c2798 : C ![4, 2, 1, 1, 1, 0, 0] ![5, 3, 1, 2, 1, 0, 0] n2798 := by
  exact checkExponentBoxTree_join c2799 c2806 (by decide +kernel)

private theorem c2811 : C ![6, 2, 1, 1, 1, 0, 0] ![8, 3, 1, 2, 1, 0, 0] n2811 := by
  decide +kernel

private theorem c2797 : C ![4, 2, 1, 1, 1, 0, 0] ![8, 3, 1, 2, 1, 0, 0] n2797 := by
  exact checkExponentBoxTree_join c2798 c2811 (by decide +kernel)

private theorem c2822 : C ![4, 2, 1, 1, 1, 0, 1] ![5, 3, 1, 1, 1, 0, 1] n2822 := by
  decide +kernel

private theorem c2827 : C ![4, 2, 1, 2, 1, 0, 1] ![5, 3, 1, 2, 1, 0, 1] n2827 := by
  decide +kernel

private theorem c2821 : C ![4, 2, 1, 1, 1, 0, 1] ![5, 3, 1, 2, 1, 0, 1] n2821 := by
  exact checkExponentBoxTree_join c2822 c2827 (by decide +kernel)

private theorem c2831 : C ![6, 2, 1, 1, 1, 0, 1] ![8, 3, 1, 1, 1, 0, 1] n2831 := by
  decide +kernel

private theorem c2834 : C ![6, 2, 1, 2, 1, 0, 1] ![8, 3, 1, 2, 1, 0, 1] n2834 := by
  decide +kernel

private theorem c2830 : C ![6, 2, 1, 1, 1, 0, 1] ![8, 3, 1, 2, 1, 0, 1] n2830 := by
  exact checkExponentBoxTree_join c2831 c2834 (by decide +kernel)

private theorem c2820 : C ![4, 2, 1, 1, 1, 0, 1] ![8, 3, 1, 2, 1, 0, 1] n2820 := by
  exact checkExponentBoxTree_join c2821 c2830 (by decide +kernel)

private theorem c2796 : C ![4, 2, 1, 1, 1, 0, 0] ![8, 3, 1, 2, 1, 0, 1] n2796 := by
  exact checkExponentBoxTree_join c2797 c2820 (by decide +kernel)

private theorem c2838 : C ![4, 2, 1, 1, 1, 1, 0] ![5, 3, 1, 1, 1, 1, 0] n2838 := by
  decide +kernel

private theorem c2843 : C ![4, 2, 1, 2, 1, 1, 0] ![5, 3, 1, 2, 1, 1, 0] n2843 := by
  decide +kernel

private theorem c2837 : C ![4, 2, 1, 1, 1, 1, 0] ![5, 3, 1, 2, 1, 1, 0] n2837 := by
  exact checkExponentBoxTree_join c2838 c2843 (by decide +kernel)

private theorem c2847 : C ![6, 2, 1, 1, 1, 1, 0] ![8, 3, 1, 1, 1, 1, 0] n2847 := by
  decide +kernel

private theorem c2850 : C ![6, 2, 1, 2, 1, 1, 0] ![8, 3, 1, 2, 1, 1, 0] n2850 := by
  decide +kernel

private theorem c2846 : C ![6, 2, 1, 1, 1, 1, 0] ![8, 3, 1, 2, 1, 1, 0] n2846 := by
  exact checkExponentBoxTree_join c2847 c2850 (by decide +kernel)

private theorem c2836 : C ![4, 2, 1, 1, 1, 1, 0] ![8, 3, 1, 2, 1, 1, 0] n2836 := by
  exact checkExponentBoxTree_join c2837 c2846 (by decide +kernel)

private theorem c2853 : C ![4, 2, 1, 1, 1, 1, 1] ![5, 3, 1, 1, 1, 1, 1] n2853 := by
  decide +kernel

private theorem c2856 : C ![4, 2, 1, 2, 1, 1, 1] ![5, 3, 1, 2, 1, 1, 1] n2856 := by
  decide +kernel

private theorem c2852 : C ![4, 2, 1, 1, 1, 1, 1] ![5, 3, 1, 2, 1, 1, 1] n2852 := by
  exact checkExponentBoxTree_join c2853 c2856 (by decide +kernel)

private theorem c2858 : C ![6, 2, 1, 1, 1, 1, 1] ![8, 3, 1, 1, 1, 1, 1] n2858 := by
  decide +kernel

private theorem c2859 : C ![6, 2, 1, 2, 1, 1, 1] ![8, 3, 1, 2, 1, 1, 1] n2859 := by
  decide +kernel

private theorem c2857 : C ![6, 2, 1, 1, 1, 1, 1] ![8, 3, 1, 2, 1, 1, 1] n2857 := by
  exact checkExponentBoxTree_join c2858 c2859 (by decide +kernel)

private theorem c2851 : C ![4, 2, 1, 1, 1, 1, 1] ![8, 3, 1, 2, 1, 1, 1] n2851 := by
  exact checkExponentBoxTree_join c2852 c2857 (by decide +kernel)

private theorem c2835 : C ![4, 2, 1, 1, 1, 1, 0] ![8, 3, 1, 2, 1, 1, 1] n2835 := by
  exact checkExponentBoxTree_join c2836 c2851 (by decide +kernel)

private theorem c2795 : C ![4, 2, 1, 1, 1, 0, 0] ![8, 3, 1, 2, 1, 1, 1] n2795 := by
  exact checkExponentBoxTree_join c2796 c2835 (by decide +kernel)

private theorem c2719 : C ![4, 2, 1, 1, 0, 0, 0] ![8, 3, 1, 2, 1, 1, 1] n2719 := by
  exact checkExponentBoxTree_join c2720 c2795 (by decide +kernel)

private theorem c2623 : C ![4, 2, 0, 1, 0, 0, 0] ![8, 3, 1, 2, 1, 1, 1] n2623 := by
  exact checkExponentBoxTree_join c2624 c2719 (by decide +kernel)

/-- The complete binary certificate at this subtree root. -/
def certificate : MainTree := n2623

theorem chunk_checked :
    checkExponentBoxTree mainScale boxPrimes lo hi certificate = true := c2623

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.Main07
