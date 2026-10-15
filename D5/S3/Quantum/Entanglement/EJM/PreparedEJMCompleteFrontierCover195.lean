/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover194
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_18722 : selected 9 ⟨478802, by decide⟩
    (prefixPartial 12 71810) = some ⟨12, 2, 0, 478802, 71810, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_71810_478802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71810 ⟨478802, by decide⟩ :=
  accepted_of_selected 12 71810 ⟨478802, by decide⟩ ⟨12, 2, 0, 478802, 71810, 2241, 65536⟩
    (by decide) selected_cut_18722

theorem selected_cut_18723 : selected 9 ⟨478833, by decide⟩
    (prefixPartial 12 71811) = some ⟨12, 2, 0, 478833, 71811, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_71811_478833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71811 ⟨478833, by decide⟩ :=
  accepted_of_selected 12 71811 ⟨478833, by decide⟩ ⟨12, 2, 0, 478833, 71811, 2225, 65536⟩
    (by decide) selected_cut_18723

theorem unmarked_context_11_17952_478834 : frontier 10 ⟨478834, by decide⟩
    (prefixCache 11 17952) (prefixPartial 11 17952) = false := by
  decide +kernel

theorem node_context_11_17952_478834 : EJMOriginalGlobalDAGData.nodes 10 ⟨478834, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨478780, by decide⟩,⟨478802, by decide⟩,⟨478833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17952_478834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17952 ⟨478834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17952
    ⟨478834, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨478780, by decide⟩,⟨478802, by decide⟩,⟨478833, by decide⟩]) unmarked_context_11_17952_478834 node_context_11_17952_478834
  intro a
  fin_cases a
  · exact context_12_71808_450982
  · exact context_12_71809_478780
  · exact context_12_71810_478802
  · exact context_12_71811_478833

theorem selected_cut_18724 : selected 9 ⟨478853, by decide⟩
    (prefixPartial 12 71812) = some ⟨12, 2, 0, 478853, 71812, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_71812_478853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71812 ⟨478853, by decide⟩ :=
  accepted_of_selected 12 71812 ⟨478853, by decide⟩ ⟨12, 2, 0, 478853, 71812, 1773, 65536⟩
    (by decide) selected_cut_18724

theorem selected_cut_18725 : selected 9 ⟨478889, by decide⟩
    (prefixPartial 12 71813) = some ⟨12, 2, 0, 478889, 71813, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_71813_478889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71813 ⟨478889, by decide⟩ :=
  accepted_of_selected 12 71813 ⟨478889, by decide⟩ ⟨12, 2, 0, 478889, 71813, 2005, 65536⟩
    (by decide) selected_cut_18725

theorem selected_cut_18726 : selected 9 ⟨478921, by decide⟩
    (prefixPartial 12 71814) = some ⟨12, 2, 0, 478921, 71814, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_71814_478921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71814 ⟨478921, by decide⟩ :=
  accepted_of_selected 12 71814 ⟨478921, by decide⟩ ⟨12, 2, 0, 478921, 71814, 2297, 65536⟩
    (by decide) selected_cut_18726

theorem selected_cut_18727 : selected 9 ⟨478948, by decide⟩
    (prefixPartial 12 71815) = some ⟨12, 2, 0, 478948, 71815, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_71815_478948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71815 ⟨478948, by decide⟩ :=
  accepted_of_selected 12 71815 ⟨478948, by decide⟩ ⟨12, 2, 0, 478948, 71815, 2169, 65536⟩
    (by decide) selected_cut_18727

theorem unmarked_context_11_17953_478949 : frontier 10 ⟨478949, by decide⟩
    (prefixCache 11 17953) (prefixPartial 11 17953) = false := by
  decide +kernel

theorem node_context_11_17953_478949 : EJMOriginalGlobalDAGData.nodes 10 ⟨478949, by decide⟩ =
    .split (coordinate 11) (![⟨478853, by decide⟩,⟨478889, by decide⟩,⟨478921, by decide⟩,⟨478948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17953_478949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17953 ⟨478949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17953
    ⟨478949, by decide⟩ (by decide) (![⟨478853, by decide⟩,⟨478889, by decide⟩,⟨478921, by decide⟩,⟨478948, by decide⟩]) unmarked_context_11_17953_478949 node_context_11_17953_478949
  intro a
  fin_cases a
  · exact context_12_71812_478853
  · exact context_12_71813_478889
  · exact context_12_71814_478921
  · exact context_12_71815_478948

theorem selected_cut_18728 : selected 9 ⟨478964, by decide⟩
    (prefixPartial 12 71816) = some ⟨12, 2, 0, 478964, 71816, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_71816_478964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71816 ⟨478964, by decide⟩ :=
  accepted_of_selected 12 71816 ⟨478964, by decide⟩ ⟨12, 2, 0, 478964, 71816, 1677, 65536⟩
    (by decide) selected_cut_18728

theorem selected_cut_18729 : selected 9 ⟨478993, by decide⟩
    (prefixPartial 12 71817) = some ⟨12, 2, 0, 478993, 71817, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_71817_478993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71817 ⟨478993, by decide⟩ :=
  accepted_of_selected 12 71817 ⟨478993, by decide⟩ ⟨12, 2, 0, 478993, 71817, 2117, 65536⟩
    (by decide) selected_cut_18729

theorem selected_cut_18730 : selected 9 ⟨479014, by decide⟩
    (prefixPartial 12 71818) = some ⟨12, 2, 0, 479014, 71818, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_71818_479014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71818 ⟨479014, by decide⟩ :=
  accepted_of_selected 12 71818 ⟨479014, by decide⟩ ⟨12, 2, 0, 479014, 71818, 2021, 65536⟩
    (by decide) selected_cut_18730

theorem selected_cut_18731 : selected 9 ⟨479040, by decide⟩
    (prefixPartial 12 71819) = some ⟨12, 2, 0, 479040, 71819, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_71819_479040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71819 ⟨479040, by decide⟩ :=
  accepted_of_selected 12 71819 ⟨479040, by decide⟩ ⟨12, 2, 0, 479040, 71819, 2021, 65536⟩
    (by decide) selected_cut_18731

theorem unmarked_context_11_17954_479041 : frontier 10 ⟨479041, by decide⟩
    (prefixCache 11 17954) (prefixPartial 11 17954) = false := by
  decide +kernel

theorem node_context_11_17954_479041 : EJMOriginalGlobalDAGData.nodes 10 ⟨479041, by decide⟩ =
    .split (coordinate 11) (![⟨478964, by decide⟩,⟨478993, by decide⟩,⟨479014, by decide⟩,⟨479040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17954_479041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17954 ⟨479041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17954
    ⟨479041, by decide⟩ (by decide) (![⟨478964, by decide⟩,⟨478993, by decide⟩,⟨479014, by decide⟩,⟨479040, by decide⟩]) unmarked_context_11_17954_479041 node_context_11_17954_479041
  intro a
  fin_cases a
  · exact context_12_71816_478964
  · exact context_12_71817_478993
  · exact context_12_71818_479014
  · exact context_12_71819_479040

theorem selected_cut_18732 : selected 9 ⟨479064, by decide⟩
    (prefixPartial 12 71820) = some ⟨12, 2, 0, 479064, 71820, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_71820_479064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71820 ⟨479064, by decide⟩ :=
  accepted_of_selected 12 71820 ⟨479064, by decide⟩ ⟨12, 2, 0, 479064, 71820, 1769, 65536⟩
    (by decide) selected_cut_18732

theorem selected_cut_18733 : selected 9 ⟨479098, by decide⟩
    (prefixPartial 12 71821) = some ⟨12, 2, 0, 479098, 71821, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_71821_479098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71821 ⟨479098, by decide⟩ :=
  accepted_of_selected 12 71821 ⟨479098, by decide⟩ ⟨12, 2, 0, 479098, 71821, 2285, 65536⟩
    (by decide) selected_cut_18733

theorem selected_cut_18734 : selected 9 ⟨479122, by decide⟩
    (prefixPartial 12 71822) = some ⟨12, 2, 0, 479122, 71822, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_71822_479122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71822 ⟨479122, by decide⟩ :=
  accepted_of_selected 12 71822 ⟨479122, by decide⟩ ⟨12, 2, 0, 479122, 71822, 2297, 65536⟩
    (by decide) selected_cut_18734

theorem selected_cut_18735 : selected 9 ⟨479140, by decide⟩
    (prefixPartial 12 71823) = some ⟨12, 2, 0, 479140, 71823, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_71823_479140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71823 ⟨479140, by decide⟩ :=
  accepted_of_selected 12 71823 ⟨479140, by decide⟩ ⟨12, 2, 0, 479140, 71823, 2053, 65536⟩
    (by decide) selected_cut_18735

theorem unmarked_context_11_17955_479141 : frontier 10 ⟨479141, by decide⟩
    (prefixCache 11 17955) (prefixPartial 11 17955) = false := by
  decide +kernel

theorem node_context_11_17955_479141 : EJMOriginalGlobalDAGData.nodes 10 ⟨479141, by decide⟩ =
    .split (coordinate 11) (![⟨479064, by decide⟩,⟨479098, by decide⟩,⟨479122, by decide⟩,⟨479140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17955_479141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17955 ⟨479141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17955
    ⟨479141, by decide⟩ (by decide) (![⟨479064, by decide⟩,⟨479098, by decide⟩,⟨479122, by decide⟩,⟨479140, by decide⟩]) unmarked_context_11_17955_479141 node_context_11_17955_479141
  intro a
  fin_cases a
  · exact context_12_71820_479064
  · exact context_12_71821_479098
  · exact context_12_71822_479122
  · exact context_12_71823_479140

theorem unmarked_context_10_4488_479142 : frontier 11 ⟨479142, by decide⟩
    (prefixCache 10 4488) (prefixPartial 10 4488) = false := by
  decide +kernel

theorem node_context_10_4488_479142 : EJMOriginalGlobalDAGData.nodes 11 ⟨479142, by decide⟩ =
    .split (coordinate 10) (![⟨478834, by decide⟩,⟨478949, by decide⟩,⟨479041, by decide⟩,⟨479141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4488_479142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4488 ⟨479142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4488
    ⟨479142, by decide⟩ (by decide) (![⟨478834, by decide⟩,⟨478949, by decide⟩,⟨479041, by decide⟩,⟨479141, by decide⟩]) unmarked_context_10_4488_479142 node_context_10_4488_479142
  intro a
  fin_cases a
  · exact context_11_17952_478834
  · exact context_11_17953_478949
  · exact context_11_17954_479041
  · exact context_11_17955_479141

theorem selected_cut_18736 : selected 9 ⟨479196, by decide⟩
    (prefixPartial 12 71824) = some ⟨12, 2, 0, 479196, 71824, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_71824_479196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71824 ⟨479196, by decide⟩ :=
  accepted_of_selected 12 71824 ⟨479196, by decide⟩ ⟨12, 2, 0, 479196, 71824, 2909, 65536⟩
    (by decide) selected_cut_18736

theorem selected_cut_18737 : selected 9 ⟨479218, by decide⟩
    (prefixPartial 12 71825) = some ⟨12, 2, 0, 479218, 71825, 2385, 65536⟩ := by
  decide +kernel

theorem context_12_71825_479218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71825 ⟨479218, by decide⟩ :=
  accepted_of_selected 12 71825 ⟨479218, by decide⟩ ⟨12, 2, 0, 479218, 71825, 2385, 65536⟩
    (by decide) selected_cut_18737

theorem selected_cut_18738 : selected 9 ⟨479242, by decide⟩
    (prefixPartial 12 71826) = some ⟨12, 2, 0, 479242, 71826, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_71826_479242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71826 ⟨479242, by decide⟩ :=
  accepted_of_selected 12 71826 ⟨479242, by decide⟩ ⟨12, 2, 0, 479242, 71826, 2465, 65536⟩
    (by decide) selected_cut_18738

theorem selected_cut_18739 : selected 9 ⟨479258, by decide⟩
    (prefixPartial 12 71827) = some ⟨12, 2, 0, 479258, 71827, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_71827_479258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71827 ⟨479258, by decide⟩ :=
  accepted_of_selected 12 71827 ⟨479258, by decide⟩ ⟨12, 2, 0, 479258, 71827, 2177, 65536⟩
    (by decide) selected_cut_18739

theorem unmarked_context_11_17956_479259 : frontier 10 ⟨479259, by decide⟩
    (prefixCache 11 17956) (prefixPartial 11 17956) = false := by
  decide +kernel

theorem node_context_11_17956_479259 : EJMOriginalGlobalDAGData.nodes 10 ⟨479259, by decide⟩ =
    .split (coordinate 11) (![⟨479196, by decide⟩,⟨479218, by decide⟩,⟨479242, by decide⟩,⟨479258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17956_479259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17956 ⟨479259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17956
    ⟨479259, by decide⟩ (by decide) (![⟨479196, by decide⟩,⟨479218, by decide⟩,⟨479242, by decide⟩,⟨479258, by decide⟩]) unmarked_context_11_17956_479259 node_context_11_17956_479259
  intro a
  fin_cases a
  · exact context_12_71824_479196
  · exact context_12_71825_479218
  · exact context_12_71826_479242
  · exact context_12_71827_479258

theorem selected_cut_18740 : selected 9 ⟨479283, by decide⟩
    (prefixPartial 12 71828) = some ⟨12, 2, 0, 479283, 71828, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_71828_479283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71828 ⟨479283, by decide⟩ :=
  accepted_of_selected 12 71828 ⟨479283, by decide⟩ ⟨12, 2, 0, 479283, 71828, 2125, 65536⟩
    (by decide) selected_cut_18740

theorem selected_cut_18741 : selected 9 ⟨479320, by decide⟩
    (prefixPartial 12 71829) = some ⟨12, 2, 0, 479320, 71829, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_71829_479320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71829 ⟨479320, by decide⟩ :=
  accepted_of_selected 12 71829 ⟨479320, by decide⟩ ⟨12, 2, 0, 479320, 71829, 2301, 65536⟩
    (by decide) selected_cut_18741

theorem selected_cut_18742 : selected 9 ⟨479357, by decide⟩
    (prefixPartial 12 71830) = some ⟨12, 2, 0, 479357, 71830, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_71830_479357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71830 ⟨479357, by decide⟩ :=
  accepted_of_selected 12 71830 ⟨479357, by decide⟩ ⟨12, 2, 0, 479357, 71830, 2433, 65536⟩
    (by decide) selected_cut_18742

theorem selected_cut_18743 : selected 9 ⟨479380, by decide⟩
    (prefixPartial 12 71831) = some ⟨12, 2, 0, 479380, 71831, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_71831_479380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71831 ⟨479380, by decide⟩ :=
  accepted_of_selected 12 71831 ⟨479380, by decide⟩ ⟨12, 2, 0, 479380, 71831, 2173, 65536⟩
    (by decide) selected_cut_18743

theorem unmarked_context_11_17957_479381 : frontier 10 ⟨479381, by decide⟩
    (prefixCache 11 17957) (prefixPartial 11 17957) = false := by
  decide +kernel

theorem node_context_11_17957_479381 : EJMOriginalGlobalDAGData.nodes 10 ⟨479381, by decide⟩ =
    .split (coordinate 11) (![⟨479283, by decide⟩,⟨479320, by decide⟩,⟨479357, by decide⟩,⟨479380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17957_479381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17957 ⟨479381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17957
    ⟨479381, by decide⟩ (by decide) (![⟨479283, by decide⟩,⟨479320, by decide⟩,⟨479357, by decide⟩,⟨479380, by decide⟩]) unmarked_context_11_17957_479381 node_context_11_17957_479381
  intro a
  fin_cases a
  · exact context_12_71828_479283
  · exact context_12_71829_479320
  · exact context_12_71830_479357
  · exact context_12_71831_479380

theorem selected_cut_18744 : selected 9 ⟨479397, by decide⟩
    (prefixPartial 12 71832) = some ⟨12, 2, 0, 479397, 71832, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_71832_479397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71832 ⟨479397, by decide⟩ :=
  accepted_of_selected 12 71832 ⟨479397, by decide⟩ ⟨12, 2, 0, 479397, 71832, 2077, 65536⟩
    (by decide) selected_cut_18744

theorem selected_cut_18745 : selected 9 ⟨479440, by decide⟩
    (prefixPartial 12 71833) = some ⟨12, 2, 0, 479440, 71833, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_71833_479440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71833 ⟨479440, by decide⟩ :=
  accepted_of_selected 12 71833 ⟨479440, by decide⟩ ⟨12, 2, 0, 479440, 71833, 2469, 65536⟩
    (by decide) selected_cut_18745

theorem selected_cut_18746 : selected 9 ⟨479458, by decide⟩
    (prefixPartial 12 71834) = some ⟨12, 2, 0, 479458, 71834, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_71834_479458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71834 ⟨479458, by decide⟩ :=
  accepted_of_selected 12 71834 ⟨479458, by decide⟩ ⟨12, 2, 0, 479458, 71834, 2153, 65536⟩
    (by decide) selected_cut_18746

theorem selected_cut_18747 : selected 9 ⟨479478, by decide⟩
    (prefixPartial 12 71835) = some ⟨12, 2, 0, 479478, 71835, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_71835_479478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71835 ⟨479478, by decide⟩ :=
  accepted_of_selected 12 71835 ⟨479478, by decide⟩ ⟨12, 2, 0, 479478, 71835, 2013, 65536⟩
    (by decide) selected_cut_18747

theorem unmarked_context_11_17958_479479 : frontier 10 ⟨479479, by decide⟩
    (prefixCache 11 17958) (prefixPartial 11 17958) = false := by
  decide +kernel

theorem node_context_11_17958_479479 : EJMOriginalGlobalDAGData.nodes 10 ⟨479479, by decide⟩ =
    .split (coordinate 11) (![⟨479397, by decide⟩,⟨479440, by decide⟩,⟨479458, by decide⟩,⟨479478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17958_479479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17958 ⟨479479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17958
    ⟨479479, by decide⟩ (by decide) (![⟨479397, by decide⟩,⟨479440, by decide⟩,⟨479458, by decide⟩,⟨479478, by decide⟩]) unmarked_context_11_17958_479479 node_context_11_17958_479479
  intro a
  fin_cases a
  · exact context_12_71832_479397
  · exact context_12_71833_479440
  · exact context_12_71834_479458
  · exact context_12_71835_479478

theorem selected_cut_18748 : selected 9 ⟨479501, by decide⟩
    (prefixPartial 12 71836) = some ⟨12, 2, 0, 479501, 71836, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_71836_479501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71836 ⟨479501, by decide⟩ :=
  accepted_of_selected 12 71836 ⟨479501, by decide⟩ ⟨12, 2, 0, 479501, 71836, 2045, 65536⟩
    (by decide) selected_cut_18748

theorem selected_cut_18749 : selected 9 ⟨479535, by decide⟩
    (prefixPartial 12 71837) = some ⟨12, 2, 0, 479535, 71837, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_71837_479535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71837 ⟨479535, by decide⟩ :=
  accepted_of_selected 12 71837 ⟨479535, by decide⟩ ⟨12, 2, 0, 479535, 71837, 2325, 65536⟩
    (by decide) selected_cut_18749

theorem selected_cut_18750 : selected 9 ⟨479564, by decide⟩
    (prefixPartial 12 71838) = some ⟨12, 2, 0, 479564, 71838, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_71838_479564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71838 ⟨479564, by decide⟩ :=
  accepted_of_selected 12 71838 ⟨479564, by decide⟩ ⟨12, 2, 0, 479564, 71838, 2329, 65536⟩
    (by decide) selected_cut_18750

theorem selected_cut_18751 : selected 9 ⟨479579, by decide⟩
    (prefixPartial 12 71839) = some ⟨12, 2, 0, 479579, 71839, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_71839_479579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71839 ⟨479579, by decide⟩ :=
  accepted_of_selected 12 71839 ⟨479579, by decide⟩ ⟨12, 2, 0, 479579, 71839, 1861, 65536⟩
    (by decide) selected_cut_18751

theorem unmarked_context_11_17959_479580 : frontier 10 ⟨479580, by decide⟩
    (prefixCache 11 17959) (prefixPartial 11 17959) = false := by
  decide +kernel

theorem node_context_11_17959_479580 : EJMOriginalGlobalDAGData.nodes 10 ⟨479580, by decide⟩ =
    .split (coordinate 11) (![⟨479501, by decide⟩,⟨479535, by decide⟩,⟨479564, by decide⟩,⟨479579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17959_479580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17959 ⟨479580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17959
    ⟨479580, by decide⟩ (by decide) (![⟨479501, by decide⟩,⟨479535, by decide⟩,⟨479564, by decide⟩,⟨479579, by decide⟩]) unmarked_context_11_17959_479580 node_context_11_17959_479580
  intro a
  fin_cases a
  · exact context_12_71836_479501
  · exact context_12_71837_479535
  · exact context_12_71838_479564
  · exact context_12_71839_479579

theorem unmarked_context_10_4489_479581 : frontier 11 ⟨479581, by decide⟩
    (prefixCache 10 4489) (prefixPartial 10 4489) = false := by
  decide +kernel

theorem node_context_10_4489_479581 : EJMOriginalGlobalDAGData.nodes 11 ⟨479581, by decide⟩ =
    .split (coordinate 10) (![⟨479259, by decide⟩,⟨479381, by decide⟩,⟨479479, by decide⟩,⟨479580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4489_479581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4489 ⟨479581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4489
    ⟨479581, by decide⟩ (by decide) (![⟨479259, by decide⟩,⟨479381, by decide⟩,⟨479479, by decide⟩,⟨479580, by decide⟩]) unmarked_context_10_4489_479581 node_context_10_4489_479581
  intro a
  fin_cases a
  · exact context_11_17956_479259
  · exact context_11_17957_479381
  · exact context_11_17958_479479
  · exact context_11_17959_479580

theorem selected_cut_18752 : selected 9 ⟨479582, by decide⟩
    (prefixPartial 12 71840) = some ⟨12, 1, 0, 479582, 71840, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71840_479582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71840 ⟨479582, by decide⟩ :=
  accepted_of_selected 12 71840 ⟨479582, by decide⟩ ⟨12, 1, 0, 479582, 71840, 1, 65536⟩
    (by decide) selected_cut_18752

theorem selected_cut_18753 : selected 9 ⟨479601, by decide⟩
    (prefixPartial 12 71841) = some ⟨12, 2, 0, 479601, 71841, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_71841_479601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71841 ⟨479601, by decide⟩ :=
  accepted_of_selected 12 71841 ⟨479601, by decide⟩ ⟨12, 2, 0, 479601, 71841, 1521, 65536⟩
    (by decide) selected_cut_18753

theorem selected_cut_18754 : selected 9 ⟨479615, by decide⟩
    (prefixPartial 12 71842) = some ⟨12, 2, 0, 479615, 71842, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_71842_479615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71842 ⟨479615, by decide⟩ :=
  accepted_of_selected 12 71842 ⟨479615, by decide⟩ ⟨12, 2, 0, 479615, 71842, 1529, 65536⟩
    (by decide) selected_cut_18754

theorem selected_cut_18755 : selected 9 ⟨479630, by decide⟩
    (prefixPartial 12 71843) = some ⟨12, 2, 0, 479630, 71843, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_71843_479630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71843 ⟨479630, by decide⟩ :=
  accepted_of_selected 12 71843 ⟨479630, by decide⟩ ⟨12, 2, 0, 479630, 71843, 1409, 65536⟩
    (by decide) selected_cut_18755

theorem unmarked_context_11_17960_479631 : frontier 10 ⟨479631, by decide⟩
    (prefixCache 11 17960) (prefixPartial 11 17960) = false := by
  decide +kernel

theorem node_context_11_17960_479631 : EJMOriginalGlobalDAGData.nodes 10 ⟨479631, by decide⟩ =
    .split (coordinate 11) (![⟨479582, by decide⟩,⟨479601, by decide⟩,⟨479615, by decide⟩,⟨479630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17960_479631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17960 ⟨479631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17960
    ⟨479631, by decide⟩ (by decide) (![⟨479582, by decide⟩,⟨479601, by decide⟩,⟨479615, by decide⟩,⟨479630, by decide⟩]) unmarked_context_11_17960_479631 node_context_11_17960_479631
  intro a
  fin_cases a
  · exact context_12_71840_479582
  · exact context_12_71841_479601
  · exact context_12_71842_479615
  · exact context_12_71843_479630

theorem selected_cut_18756 : selected 9 ⟨479649, by decide⟩
    (prefixPartial 12 71844) = some ⟨12, 2, 0, 479649, 71844, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_71844_479649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71844 ⟨479649, by decide⟩ :=
  accepted_of_selected 12 71844 ⟨479649, by decide⟩ ⟨12, 2, 0, 479649, 71844, 1421, 65536⟩
    (by decide) selected_cut_18756

theorem selected_cut_18757 : selected 9 ⟨479670, by decide⟩
    (prefixPartial 12 71845) = some ⟨12, 2, 0, 479670, 71845, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_71845_479670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71845 ⟨479670, by decide⟩ :=
  accepted_of_selected 12 71845 ⟨479670, by decide⟩ ⟨12, 2, 0, 479670, 71845, 1525, 65536⟩
    (by decide) selected_cut_18757

theorem selected_cut_18758 : selected 9 ⟨479687, by decide⟩
    (prefixPartial 12 71846) = some ⟨12, 2, 0, 479687, 71846, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_71846_479687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71846 ⟨479687, by decide⟩ :=
  accepted_of_selected 12 71846 ⟨479687, by decide⟩ ⟨12, 2, 0, 479687, 71846, 1533, 65536⟩
    (by decide) selected_cut_18758

theorem selected_cut_18759 : selected 9 ⟨479706, by decide⟩
    (prefixPartial 12 71847) = some ⟨12, 2, 0, 479706, 71847, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_71847_479706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71847 ⟨479706, by decide⟩ :=
  accepted_of_selected 12 71847 ⟨479706, by decide⟩ ⟨12, 2, 0, 479706, 71847, 1421, 65536⟩
    (by decide) selected_cut_18759

theorem unmarked_context_11_17961_479707 : frontier 10 ⟨479707, by decide⟩
    (prefixCache 11 17961) (prefixPartial 11 17961) = false := by
  decide +kernel

theorem node_context_11_17961_479707 : EJMOriginalGlobalDAGData.nodes 10 ⟨479707, by decide⟩ =
    .split (coordinate 11) (![⟨479649, by decide⟩,⟨479670, by decide⟩,⟨479687, by decide⟩,⟨479706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17961_479707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17961 ⟨479707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17961
    ⟨479707, by decide⟩ (by decide) (![⟨479649, by decide⟩,⟨479670, by decide⟩,⟨479687, by decide⟩,⟨479706, by decide⟩]) unmarked_context_11_17961_479707 node_context_11_17961_479707
  intro a
  fin_cases a
  · exact context_12_71844_479649
  · exact context_12_71845_479670
  · exact context_12_71846_479687
  · exact context_12_71847_479706

theorem selected_cut_18760 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 17962) = some ⟨11, 1, 0, 479708, 17962, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17962_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17962 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 17962 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 17962, 1, 262144⟩
    (by decide) selected_cut_18760

theorem selected_cut_18761 : selected 9 ⟨479725, by decide⟩
    (prefixPartial 12 71852) = some ⟨12, 2, 0, 479725, 71852, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_71852_479725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71852 ⟨479725, by decide⟩ :=
  accepted_of_selected 12 71852 ⟨479725, by decide⟩ ⟨12, 2, 0, 479725, 71852, 1401, 65536⟩
    (by decide) selected_cut_18761

theorem selected_cut_18762 : selected 9 ⟨479739, by decide⟩
    (prefixPartial 12 71853) = some ⟨12, 2, 0, 479739, 71853, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_71853_479739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71853 ⟨479739, by decide⟩ :=
  accepted_of_selected 12 71853 ⟨479739, by decide⟩ ⟨12, 2, 0, 479739, 71853, 1629, 65536⟩
    (by decide) selected_cut_18762

theorem selected_cut_18763 : selected 9 ⟨479754, by decide⟩
    (prefixPartial 12 71854) = some ⟨12, 2, 0, 479754, 71854, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_71854_479754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71854 ⟨479754, by decide⟩ :=
  accepted_of_selected 12 71854 ⟨479754, by decide⟩ ⟨12, 2, 0, 479754, 71854, 1489, 65536⟩
    (by decide) selected_cut_18763

theorem selected_cut_18764 : selected 9 ⟨479767, by decide⟩
    (prefixPartial 12 71855) = some ⟨12, 2, 0, 479767, 71855, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_71855_479767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71855 ⟨479767, by decide⟩ :=
  accepted_of_selected 12 71855 ⟨479767, by decide⟩ ⟨12, 2, 0, 479767, 71855, 1285, 65536⟩
    (by decide) selected_cut_18764

theorem unmarked_context_11_17963_479768 : frontier 10 ⟨479768, by decide⟩
    (prefixCache 11 17963) (prefixPartial 11 17963) = false := by
  decide +kernel

theorem node_context_11_17963_479768 : EJMOriginalGlobalDAGData.nodes 10 ⟨479768, by decide⟩ =
    .split (coordinate 11) (![⟨479725, by decide⟩,⟨479739, by decide⟩,⟨479754, by decide⟩,⟨479767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17963_479768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17963 ⟨479768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17963
    ⟨479768, by decide⟩ (by decide) (![⟨479725, by decide⟩,⟨479739, by decide⟩,⟨479754, by decide⟩,⟨479767, by decide⟩]) unmarked_context_11_17963_479768 node_context_11_17963_479768
  intro a
  fin_cases a
  · exact context_12_71852_479725
  · exact context_12_71853_479739
  · exact context_12_71854_479754
  · exact context_12_71855_479767

theorem unmarked_context_10_4490_479769 : frontier 11 ⟨479769, by decide⟩
    (prefixCache 10 4490) (prefixPartial 10 4490) = false := by
  decide +kernel

theorem node_context_10_4490_479769 : EJMOriginalGlobalDAGData.nodes 11 ⟨479769, by decide⟩ =
    .split (coordinate 10) (![⟨479631, by decide⟩,⟨479707, by decide⟩,⟨479708, by decide⟩,⟨479768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4490_479769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4490 ⟨479769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4490
    ⟨479769, by decide⟩ (by decide) (![⟨479631, by decide⟩,⟨479707, by decide⟩,⟨479708, by decide⟩,⟨479768, by decide⟩]) unmarked_context_10_4490_479769 node_context_10_4490_479769
  intro a
  fin_cases a
  · exact context_11_17960_479631
  · exact context_11_17961_479707
  · exact context_11_17962_479708
  · exact context_11_17963_479768

theorem selected_cut_18765 : selected 9 ⟨479810, by decide⟩
    (prefixPartial 12 71856) = some ⟨12, 2, 0, 479810, 71856, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_71856_479810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71856 ⟨479810, by decide⟩ :=
  accepted_of_selected 12 71856 ⟨479810, by decide⟩ ⟨12, 2, 0, 479810, 71856, 1869, 65536⟩
    (by decide) selected_cut_18765

theorem selected_cut_18766 : selected 9 ⟨479817, by decide⟩
    (prefixPartial 12 71857) = some ⟨12, 2, 0, 479817, 71857, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_71857_479817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71857 ⟨479817, by decide⟩ :=
  accepted_of_selected 12 71857 ⟨479817, by decide⟩ ⟨12, 2, 0, 479817, 71857, 1521, 65536⟩
    (by decide) selected_cut_18766

theorem selected_cut_18767 : selected 9 ⟨479827, by decide⟩
    (prefixPartial 12 71858) = some ⟨12, 2, 0, 479827, 71858, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_71858_479827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71858 ⟨479827, by decide⟩ :=
  accepted_of_selected 12 71858 ⟨479827, by decide⟩ ⟨12, 2, 0, 479827, 71858, 1441, 65536⟩
    (by decide) selected_cut_18767

theorem selected_cut_18768 : selected 9 ⟨479836, by decide⟩
    (prefixPartial 12 71859) = some ⟨12, 2, 0, 479836, 71859, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_71859_479836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71859 ⟨479836, by decide⟩ :=
  accepted_of_selected 12 71859 ⟨479836, by decide⟩ ⟨12, 2, 0, 479836, 71859, 1245, 65536⟩
    (by decide) selected_cut_18768

theorem unmarked_context_11_17964_479837 : frontier 10 ⟨479837, by decide⟩
    (prefixCache 11 17964) (prefixPartial 11 17964) = false := by
  decide +kernel

theorem node_context_11_17964_479837 : EJMOriginalGlobalDAGData.nodes 10 ⟨479837, by decide⟩ =
    .split (coordinate 11) (![⟨479810, by decide⟩,⟨479817, by decide⟩,⟨479827, by decide⟩,⟨479836, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17964_479837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17964 ⟨479837, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17964
    ⟨479837, by decide⟩ (by decide) (![⟨479810, by decide⟩,⟨479817, by decide⟩,⟨479827, by decide⟩,⟨479836, by decide⟩]) unmarked_context_11_17964_479837 node_context_11_17964_479837
  intro a
  fin_cases a
  · exact context_12_71856_479810
  · exact context_12_71857_479817
  · exact context_12_71858_479827
  · exact context_12_71859_479836

theorem selected_cut_18769 : selected 9 ⟨479849, by decide⟩
    (prefixPartial 12 71860) = some ⟨12, 2, 0, 479849, 71860, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_71860_479849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71860 ⟨479849, by decide⟩ :=
  accepted_of_selected 12 71860 ⟨479849, by decide⟩ ⟨12, 2, 0, 479849, 71860, 1345, 65536⟩
    (by decide) selected_cut_18769

theorem selected_cut_18770 : selected 9 ⟨479865, by decide⟩
    (prefixPartial 12 71861) = some ⟨12, 2, 0, 479865, 71861, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_71861_479865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71861 ⟨479865, by decide⟩ :=
  accepted_of_selected 12 71861 ⟨479865, by decide⟩ ⟨12, 2, 0, 479865, 71861, 1417, 65536⟩
    (by decide) selected_cut_18770

theorem selected_cut_18771 : selected 9 ⟨479882, by decide⟩
    (prefixPartial 12 71862) = some ⟨12, 2, 0, 479882, 71862, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_71862_479882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71862 ⟨479882, by decide⟩ :=
  accepted_of_selected 12 71862 ⟨479882, by decide⟩ ⟨12, 2, 0, 479882, 71862, 1365, 65536⟩
    (by decide) selected_cut_18771

theorem selected_cut_18772 : selected 9 ⟨479893, by decide⟩
    (prefixPartial 12 71863) = some ⟨12, 2, 0, 479893, 71863, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_71863_479893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71863 ⟨479893, by decide⟩ :=
  accepted_of_selected 12 71863 ⟨479893, by decide⟩ ⟨12, 2, 0, 479893, 71863, 1241, 65536⟩
    (by decide) selected_cut_18772

theorem unmarked_context_11_17965_479894 : frontier 10 ⟨479894, by decide⟩
    (prefixCache 11 17965) (prefixPartial 11 17965) = false := by
  decide +kernel

theorem node_context_11_17965_479894 : EJMOriginalGlobalDAGData.nodes 10 ⟨479894, by decide⟩ =
    .split (coordinate 11) (![⟨479849, by decide⟩,⟨479865, by decide⟩,⟨479882, by decide⟩,⟨479893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17965_479894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17965 ⟨479894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17965
    ⟨479894, by decide⟩ (by decide) (![⟨479849, by decide⟩,⟨479865, by decide⟩,⟨479882, by decide⟩,⟨479893, by decide⟩]) unmarked_context_11_17965_479894 node_context_11_17965_479894
  intro a
  fin_cases a
  · exact context_12_71860_479849
  · exact context_12_71861_479865
  · exact context_12_71862_479882
  · exact context_12_71863_479893

theorem selected_cut_18773 : selected 9 ⟨479904, by decide⟩
    (prefixPartial 12 71864) = some ⟨12, 2, 0, 479904, 71864, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_71864_479904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71864 ⟨479904, by decide⟩ :=
  accepted_of_selected 12 71864 ⟨479904, by decide⟩ ⟨12, 2, 0, 479904, 71864, 1289, 65536⟩
    (by decide) selected_cut_18773

theorem selected_cut_18774 : selected 9 ⟨479928, by decide⟩
    (prefixPartial 12 71865) = some ⟨12, 2, 0, 479928, 71865, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_71865_479928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71865 ⟨479928, by decide⟩ :=
  accepted_of_selected 12 71865 ⟨479928, by decide⟩ ⟨12, 2, 0, 479928, 71865, 1485, 65536⟩
    (by decide) selected_cut_18774

theorem selected_cut_18775 : selected 9 ⟨479937, by decide⟩
    (prefixPartial 12 71866) = some ⟨12, 2, 0, 479937, 71866, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_71866_479937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71866 ⟨479937, by decide⟩ :=
  accepted_of_selected 12 71866 ⟨479937, by decide⟩ ⟨12, 2, 0, 479937, 71866, 1237, 65536⟩
    (by decide) selected_cut_18775

theorem selected_cut_18776 : selected 9 ⟨479951, by decide⟩
    (prefixPartial 12 71867) = some ⟨12, 2, 0, 479951, 71867, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_71867_479951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71867 ⟨479951, by decide⟩ :=
  accepted_of_selected 12 71867 ⟨479951, by decide⟩ ⟨12, 2, 0, 479951, 71867, 1133, 65536⟩
    (by decide) selected_cut_18776

theorem unmarked_context_11_17966_479952 : frontier 10 ⟨479952, by decide⟩
    (prefixCache 11 17966) (prefixPartial 11 17966) = false := by
  decide +kernel

theorem node_context_11_17966_479952 : EJMOriginalGlobalDAGData.nodes 10 ⟨479952, by decide⟩ =
    .split (coordinate 11) (![⟨479904, by decide⟩,⟨479928, by decide⟩,⟨479937, by decide⟩,⟨479951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17966_479952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17966 ⟨479952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17966
    ⟨479952, by decide⟩ (by decide) (![⟨479904, by decide⟩,⟨479928, by decide⟩,⟨479937, by decide⟩,⟨479951, by decide⟩]) unmarked_context_11_17966_479952 node_context_11_17966_479952
  intro a
  fin_cases a
  · exact context_12_71864_479904
  · exact context_12_71865_479928
  · exact context_12_71866_479937
  · exact context_12_71867_479951

theorem selected_cut_18777 : selected 9 ⟨479964, by decide⟩
    (prefixPartial 12 71868) = some ⟨12, 2, 0, 479964, 71868, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_71868_479964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71868 ⟨479964, by decide⟩ :=
  accepted_of_selected 12 71868 ⟨479964, by decide⟩ ⟨12, 2, 0, 479964, 71868, 1201, 65536⟩
    (by decide) selected_cut_18777

theorem selected_cut_18778 : selected 9 ⟨479978, by decide⟩
    (prefixPartial 12 71869) = some ⟨12, 2, 0, 479978, 71869, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_71869_479978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71869 ⟨479978, by decide⟩ :=
  accepted_of_selected 12 71869 ⟨479978, by decide⟩ ⟨12, 2, 0, 479978, 71869, 1305, 65536⟩
    (by decide) selected_cut_18778

theorem selected_cut_18779 : selected 9 ⟨479989, by decide⟩
    (prefixPartial 12 71870) = some ⟨12, 2, 0, 479989, 71870, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_71870_479989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71870 ⟨479989, by decide⟩ :=
  accepted_of_selected 12 71870 ⟨479989, by decide⟩ ⟨12, 2, 0, 479989, 71870, 1201, 65536⟩
    (by decide) selected_cut_18779

theorem selected_cut_18780 : selected 9 ⟨479998, by decide⟩
    (prefixPartial 12 71871) = some ⟨12, 2, 0, 479998, 71871, 977, 65536⟩ := by
  decide +kernel

theorem context_12_71871_479998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71871 ⟨479998, by decide⟩ :=
  accepted_of_selected 12 71871 ⟨479998, by decide⟩ ⟨12, 2, 0, 479998, 71871, 977, 65536⟩
    (by decide) selected_cut_18780

theorem unmarked_context_11_17967_479999 : frontier 10 ⟨479999, by decide⟩
    (prefixCache 11 17967) (prefixPartial 11 17967) = false := by
  decide +kernel

theorem node_context_11_17967_479999 : EJMOriginalGlobalDAGData.nodes 10 ⟨479999, by decide⟩ =
    .split (coordinate 11) (![⟨479964, by decide⟩,⟨479978, by decide⟩,⟨479989, by decide⟩,⟨479998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17967_479999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17967 ⟨479999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17967
    ⟨479999, by decide⟩ (by decide) (![⟨479964, by decide⟩,⟨479978, by decide⟩,⟨479989, by decide⟩,⟨479998, by decide⟩]) unmarked_context_11_17967_479999 node_context_11_17967_479999
  intro a
  fin_cases a
  · exact context_12_71868_479964
  · exact context_12_71869_479978
  · exact context_12_71870_479989
  · exact context_12_71871_479998

theorem unmarked_context_10_4491_480000 : frontier 11 ⟨480000, by decide⟩
    (prefixCache 10 4491) (prefixPartial 10 4491) = false := by
  decide +kernel

theorem node_context_10_4491_480000 : EJMOriginalGlobalDAGData.nodes 11 ⟨480000, by decide⟩ =
    .split (coordinate 10) (![⟨479837, by decide⟩,⟨479894, by decide⟩,⟨479952, by decide⟩,⟨479999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4491_480000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4491 ⟨480000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4491
    ⟨480000, by decide⟩ (by decide) (![⟨479837, by decide⟩,⟨479894, by decide⟩,⟨479952, by decide⟩,⟨479999, by decide⟩]) unmarked_context_10_4491_480000 node_context_10_4491_480000
  intro a
  fin_cases a
  · exact context_11_17964_479837
  · exact context_11_17965_479894
  · exact context_11_17966_479952
  · exact context_11_17967_479999

theorem unmarked_context_9_1122_480001 : frontier 12 ⟨480001, by decide⟩
    (prefixCache 9 1122) (prefixPartial 9 1122) = false := by
  decide +kernel

theorem node_context_9_1122_480001 : EJMOriginalGlobalDAGData.nodes 12 ⟨480001, by decide⟩ =
    .split (coordinate 9) (![⟨479142, by decide⟩,⟨479581, by decide⟩,⟨479769, by decide⟩,⟨480000, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1122_480001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1122 ⟨480001, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1122
    ⟨480001, by decide⟩ (by decide) (![⟨479142, by decide⟩,⟨479581, by decide⟩,⟨479769, by decide⟩,⟨480000, by decide⟩]) unmarked_context_9_1122_480001 node_context_9_1122_480001
  intro a
  fin_cases a
  · exact context_10_4488_479142
  · exact context_10_4489_479581
  · exact context_10_4490_479769
  · exact context_10_4491_480000

theorem selected_cut_18781 : selected 10 ⟨480027, by decide⟩
    (prefixPartial 11 17968) = some ⟨11, 2, 0, 480027, 17968, 2421, 262144⟩ := by
  decide +kernel

theorem context_11_17968_480027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17968 ⟨480027, by decide⟩ :=
  accepted_of_selected 11 17968 ⟨480027, by decide⟩ ⟨11, 2, 0, 480027, 17968, 2421, 262144⟩
    (by decide) selected_cut_18781

theorem selected_cut_18782 : selected 10 ⟨480064, by decide⟩
    (prefixPartial 11 17969) = some ⟨11, 2, 0, 480064, 17969, 3145, 262144⟩ := by
  decide +kernel

theorem context_11_17969_480064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17969 ⟨480064, by decide⟩ :=
  accepted_of_selected 11 17969 ⟨480064, by decide⟩ ⟨11, 2, 0, 480064, 17969, 3145, 262144⟩
    (by decide) selected_cut_18782

theorem selected_cut_18783 : selected 10 ⟨480096, by decide⟩
    (prefixPartial 11 17970) = some ⟨11, 2, 0, 480096, 17970, 2793, 262144⟩ := by
  decide +kernel

theorem context_11_17970_480096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17970 ⟨480096, by decide⟩ :=
  accepted_of_selected 11 17970 ⟨480096, by decide⟩ ⟨11, 2, 0, 480096, 17970, 2793, 262144⟩
    (by decide) selected_cut_18783

theorem selected_cut_18784 : selected 10 ⟨480141, by decide⟩
    (prefixPartial 11 17971) = some ⟨11, 2, 0, 480141, 17971, 3149, 262144⟩ := by
  decide +kernel

theorem context_11_17971_480141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17971 ⟨480141, by decide⟩ :=
  accepted_of_selected 11 17971 ⟨480141, by decide⟩ ⟨11, 2, 0, 480141, 17971, 3149, 262144⟩
    (by decide) selected_cut_18784

theorem unmarked_context_10_4492_480142 : frontier 11 ⟨480142, by decide⟩
    (prefixCache 10 4492) (prefixPartial 10 4492) = false := by
  decide +kernel

theorem node_context_10_4492_480142 : EJMOriginalGlobalDAGData.nodes 11 ⟨480142, by decide⟩ =
    .split (coordinate 10) (![⟨480027, by decide⟩,⟨480064, by decide⟩,⟨480096, by decide⟩,⟨480141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4492_480142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4492 ⟨480142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4492
    ⟨480142, by decide⟩ (by decide) (![⟨480027, by decide⟩,⟨480064, by decide⟩,⟨480096, by decide⟩,⟨480141, by decide⟩]) unmarked_context_10_4492_480142 node_context_10_4492_480142
  intro a
  fin_cases a
  · exact context_11_17968_480027
  · exact context_11_17969_480064
  · exact context_11_17970_480096
  · exact context_11_17971_480141

theorem selected_cut_18785 : selected 10 ⟨480190, by decide⟩
    (prefixPartial 11 17972) = some ⟨11, 2, 0, 480190, 17972, 3001, 262144⟩ := by
  decide +kernel

theorem context_11_17972_480190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17972 ⟨480190, by decide⟩ :=
  accepted_of_selected 11 17972 ⟨480190, by decide⟩ ⟨11, 2, 0, 480190, 17972, 3001, 262144⟩
    (by decide) selected_cut_18785

theorem selected_cut_18786 : selected 10 ⟨480230, by decide⟩
    (prefixPartial 11 17973) = some ⟨11, 2, 0, 480230, 17973, 2657, 262144⟩ := by
  decide +kernel

theorem context_11_17973_480230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17973 ⟨480230, by decide⟩ :=
  accepted_of_selected 11 17973 ⟨480230, by decide⟩ ⟨11, 2, 0, 480230, 17973, 2657, 262144⟩
    (by decide) selected_cut_18786

theorem selected_cut_18787 : selected 10 ⟨480255, by decide⟩
    (prefixPartial 11 17974) = some ⟨11, 2, 0, 480255, 17974, 2325, 262144⟩ := by
  decide +kernel

theorem context_11_17974_480255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17974 ⟨480255, by decide⟩ :=
  accepted_of_selected 11 17974 ⟨480255, by decide⟩ ⟨11, 2, 0, 480255, 17974, 2325, 262144⟩
    (by decide) selected_cut_18787

theorem selected_cut_18788 : selected 10 ⟨480287, by decide⟩
    (prefixPartial 11 17975) = some ⟨11, 2, 0, 480287, 17975, 2137, 262144⟩ := by
  decide +kernel

theorem context_11_17975_480287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17975 ⟨480287, by decide⟩ :=
  accepted_of_selected 11 17975 ⟨480287, by decide⟩ ⟨11, 2, 0, 480287, 17975, 2137, 262144⟩
    (by decide) selected_cut_18788

theorem unmarked_context_10_4493_480288 : frontier 11 ⟨480288, by decide⟩
    (prefixCache 10 4493) (prefixPartial 10 4493) = false := by
  decide +kernel

theorem node_context_10_4493_480288 : EJMOriginalGlobalDAGData.nodes 11 ⟨480288, by decide⟩ =
    .split (coordinate 10) (![⟨480190, by decide⟩,⟨480230, by decide⟩,⟨480255, by decide⟩,⟨480287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4493_480288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4493 ⟨480288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4493
    ⟨480288, by decide⟩ (by decide) (![⟨480190, by decide⟩,⟨480230, by decide⟩,⟨480255, by decide⟩,⟨480287, by decide⟩]) unmarked_context_10_4493_480288 node_context_10_4493_480288
  intro a
  fin_cases a
  · exact context_11_17972_480190
  · exact context_11_17973_480230
  · exact context_11_17974_480255
  · exact context_11_17975_480287

theorem selected_cut_18789 : selected 10 ⟨480309, by decide⟩
    (prefixPartial 11 17976) = some ⟨11, 2, 0, 480309, 17976, 1589, 262144⟩ := by
  decide +kernel

theorem context_11_17976_480309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17976 ⟨480309, by decide⟩ :=
  accepted_of_selected 11 17976 ⟨480309, by decide⟩ ⟨11, 2, 0, 480309, 17976, 1589, 262144⟩
    (by decide) selected_cut_18789

theorem selected_cut_18790 : selected 10 ⟨480327, by decide⟩
    (prefixPartial 11 17977) = some ⟨11, 2, 0, 480327, 17977, 1429, 262144⟩ := by
  decide +kernel

theorem context_11_17977_480327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17977 ⟨480327, by decide⟩ :=
  accepted_of_selected 11 17977 ⟨480327, by decide⟩ ⟨11, 2, 0, 480327, 17977, 1429, 262144⟩
    (by decide) selected_cut_18790

theorem selected_cut_18791 : selected 10 ⟨480346, by decide⟩
    (prefixPartial 11 17978) = some ⟨11, 2, 0, 480346, 17978, 941, 262144⟩ := by
  decide +kernel

theorem context_11_17978_480346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17978 ⟨480346, by decide⟩ :=
  accepted_of_selected 11 17978 ⟨480346, by decide⟩ ⟨11, 2, 0, 480346, 17978, 941, 262144⟩
    (by decide) selected_cut_18791

theorem selected_cut_18792 : selected 10 ⟨480358, by decide⟩
    (prefixPartial 11 17979) = some ⟨11, 2, 0, 480358, 17979, 905, 262144⟩ := by
  decide +kernel

theorem context_11_17979_480358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17979 ⟨480358, by decide⟩ :=
  accepted_of_selected 11 17979 ⟨480358, by decide⟩ ⟨11, 2, 0, 480358, 17979, 905, 262144⟩
    (by decide) selected_cut_18792

theorem unmarked_context_10_4494_480359 : frontier 11 ⟨480359, by decide⟩
    (prefixCache 10 4494) (prefixPartial 10 4494) = false := by
  decide +kernel

theorem node_context_10_4494_480359 : EJMOriginalGlobalDAGData.nodes 11 ⟨480359, by decide⟩ =
    .split (coordinate 10) (![⟨480309, by decide⟩,⟨480327, by decide⟩,⟨480346, by decide⟩,⟨480358, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4494_480359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4494 ⟨480359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4494
    ⟨480359, by decide⟩ (by decide) (![⟨480309, by decide⟩,⟨480327, by decide⟩,⟨480346, by decide⟩,⟨480358, by decide⟩]) unmarked_context_10_4494_480359 node_context_10_4494_480359
  intro a
  fin_cases a
  · exact context_11_17976_480309
  · exact context_11_17977_480327
  · exact context_11_17978_480346
  · exact context_11_17979_480358

theorem selected_cut_18793 : selected 11 ⟨480394, by decide⟩
    (prefixPartial 10 4495) = some ⟨10, 2, 0, 480394, 4495, 1389, 1048576⟩ := by
  decide +kernel

theorem context_10_4495_480394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4495 ⟨480394, by decide⟩ :=
  accepted_of_selected 10 4495 ⟨480394, by decide⟩ ⟨10, 2, 0, 480394, 4495, 1389, 1048576⟩
    (by decide) selected_cut_18793

theorem unmarked_context_9_1123_480395 : frontier 12 ⟨480395, by decide⟩
    (prefixCache 9 1123) (prefixPartial 9 1123) = false := by
  decide +kernel

theorem node_context_9_1123_480395 : EJMOriginalGlobalDAGData.nodes 12 ⟨480395, by decide⟩ =
    .split (coordinate 9) (![⟨480142, by decide⟩,⟨480288, by decide⟩,⟨480359, by decide⟩,⟨480394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1123_480395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1123 ⟨480395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1123
    ⟨480395, by decide⟩ (by decide) (![⟨480142, by decide⟩,⟨480288, by decide⟩,⟨480359, by decide⟩,⟨480394, by decide⟩]) unmarked_context_9_1123_480395 node_context_9_1123_480395
  intro a
  fin_cases a
  · exact context_10_4492_480142
  · exact context_10_4493_480288
  · exact context_10_4494_480359
  · exact context_10_4495_480394

theorem unmarked_context_8_280_480396 : frontier 13 ⟨480396, by decide⟩
    (prefixCache 8 280) (prefixPartial 8 280) = false := by
  decide +kernel

theorem node_context_8_280_480396 : EJMOriginalGlobalDAGData.nodes 13 ⟨480396, by decide⟩ =
    .split (coordinate 8) (![⟨475723, by decide⟩,⟨478752, by decide⟩,⟨480001, by decide⟩,⟨480395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_280_480396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 280 ⟨480396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 280
    ⟨480396, by decide⟩ (by decide) (![⟨475723, by decide⟩,⟨478752, by decide⟩,⟨480001, by decide⟩,⟨480395, by decide⟩]) unmarked_context_8_280_480396 node_context_8_280_480396
  intro a
  fin_cases a
  · exact context_9_1120_475723
  · exact context_9_1121_478752
  · exact context_9_1122_480001
  · exact context_9_1123_480395

theorem selected_cut_18794 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 17984) = some ⟨11, 1, 0, 434745, 17984, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17984_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17984 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 17984 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 17984, 1, 262144⟩
    (by decide) selected_cut_18794

theorem selected_cut_18795 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 71940) = some ⟨12, 1, 0, 448748, 71940, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71940_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71940 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 71940 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 71940, 1, 65536⟩
    (by decide) selected_cut_18795

theorem selected_cut_18796 : selected 7 ⟨480446, by decide⟩
    (prefixPartial 14 1151056) = some ⟨14, 2, 0, 480446, 1151056, 2277, 4096⟩ := by
  decide +kernel

theorem context_14_1151056_480446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151056 ⟨480446, by decide⟩ :=
  accepted_of_selected 14 1151056 ⟨480446, by decide⟩ ⟨14, 2, 0, 480446, 1151056, 2277, 4096⟩
    (by decide) selected_cut_18796

theorem selected_cut_18797 : selected 7 ⟨480510, by decide⟩
    (prefixPartial 14 1151057) = some ⟨14, 2, 0, 480510, 1151057, 2621, 4096⟩ := by
  decide +kernel

theorem context_14_1151057_480510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151057 ⟨480510, by decide⟩ :=
  accepted_of_selected 14 1151057 ⟨480510, by decide⟩ ⟨14, 2, 0, 480510, 1151057, 2621, 4096⟩
    (by decide) selected_cut_18797

theorem selected_cut_18798 : selected 7 ⟨480576, by decide⟩
    (prefixPartial 14 1151058) = some ⟨14, 2, 0, 480576, 1151058, 2617, 4096⟩ := by
  decide +kernel

theorem context_14_1151058_480576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151058 ⟨480576, by decide⟩ :=
  accepted_of_selected 14 1151058 ⟨480576, by decide⟩ ⟨14, 2, 0, 480576, 1151058, 2617, 4096⟩
    (by decide) selected_cut_18798

theorem selected_cut_18799 : selected 7 ⟨480623, by decide⟩
    (prefixPartial 14 1151059) = some ⟨14, 2, 0, 480623, 1151059, 2541, 4096⟩ := by
  decide +kernel

theorem context_14_1151059_480623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151059 ⟨480623, by decide⟩ :=
  accepted_of_selected 14 1151059 ⟨480623, by decide⟩ ⟨14, 2, 0, 480623, 1151059, 2541, 4096⟩
    (by decide) selected_cut_18799

theorem unmarked_context_13_287764_480624 : frontier 8 ⟨480624, by decide⟩
    (prefixCache 13 287764) (prefixPartial 13 287764) = false := by
  decide +kernel

theorem node_context_13_287764_480624 : EJMOriginalGlobalDAGData.nodes 8 ⟨480624, by decide⟩ =
    .split (coordinate 13) (![⟨480446, by decide⟩,⟨480510, by decide⟩,⟨480576, by decide⟩,⟨480623, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287764_480624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287764 ⟨480624, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287764
    ⟨480624, by decide⟩ (by decide) (![⟨480446, by decide⟩,⟨480510, by decide⟩,⟨480576, by decide⟩,⟨480623, by decide⟩]) unmarked_context_13_287764_480624 node_context_13_287764_480624
  intro a
  fin_cases a
  · exact context_14_1151056_480446
  · exact context_14_1151057_480510
  · exact context_14_1151058_480576
  · exact context_14_1151059_480623

theorem selected_cut_18800 : selected 7 ⟨480659, by decide⟩
    (prefixPartial 14 1151060) = some ⟨14, 2, 0, 480659, 1151060, 1313, 4096⟩ := by
  decide +kernel

theorem context_14_1151060_480659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151060 ⟨480659, by decide⟩ :=
  accepted_of_selected 14 1151060 ⟨480659, by decide⟩ ⟨14, 2, 0, 480659, 1151060, 1313, 4096⟩
    (by decide) selected_cut_18800

theorem selected_cut_18801 : selected 7 ⟨480716, by decide⟩
    (prefixPartial 14 1151061) = some ⟨14, 2, 0, 480716, 1151061, 2269, 4096⟩ := by
  decide +kernel

theorem context_14_1151061_480716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151061 ⟨480716, by decide⟩ :=
  accepted_of_selected 14 1151061 ⟨480716, by decide⟩ ⟨14, 2, 0, 480716, 1151061, 2269, 4096⟩
    (by decide) selected_cut_18801

theorem selected_cut_18802 : selected 7 ⟨480763, by decide⟩
    (prefixPartial 14 1151062) = some ⟨14, 2, 0, 480763, 1151062, 2001, 4096⟩ := by
  decide +kernel

theorem context_14_1151062_480763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151062 ⟨480763, by decide⟩ :=
  accepted_of_selected 14 1151062 ⟨480763, by decide⟩ ⟨14, 2, 0, 480763, 1151062, 2001, 4096⟩
    (by decide) selected_cut_18802

theorem selected_cut_18803 : selected 7 ⟨480807, by decide⟩
    (prefixPartial 14 1151063) = some ⟨14, 2, 0, 480807, 1151063, 1989, 4096⟩ := by
  decide +kernel

theorem context_14_1151063_480807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151063 ⟨480807, by decide⟩ :=
  accepted_of_selected 14 1151063 ⟨480807, by decide⟩ ⟨14, 2, 0, 480807, 1151063, 1989, 4096⟩
    (by decide) selected_cut_18803

theorem unmarked_context_13_287765_480808 : frontier 8 ⟨480808, by decide⟩
    (prefixCache 13 287765) (prefixPartial 13 287765) = false := by
  decide +kernel

theorem node_context_13_287765_480808 : EJMOriginalGlobalDAGData.nodes 8 ⟨480808, by decide⟩ =
    .split (coordinate 13) (![⟨480659, by decide⟩,⟨480716, by decide⟩,⟨480763, by decide⟩,⟨480807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287765_480808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287765 ⟨480808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287765
    ⟨480808, by decide⟩ (by decide) (![⟨480659, by decide⟩,⟨480716, by decide⟩,⟨480763, by decide⟩,⟨480807, by decide⟩]) unmarked_context_13_287765_480808 node_context_13_287765_480808
  intro a
  fin_cases a
  · exact context_14_1151060_480659
  · exact context_14_1151061_480716
  · exact context_14_1151062_480763
  · exact context_14_1151063_480807

theorem selected_cut_18804 : selected 8 ⟨480943, by decide⟩
    (prefixPartial 13 287766) = some ⟨13, 2, 0, 480943, 287766, 4069, 16384⟩ := by
  decide +kernel

theorem context_13_287766_480943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287766 ⟨480943, by decide⟩ :=
  accepted_of_selected 13 287766 ⟨480943, by decide⟩ ⟨13, 2, 0, 480943, 287766, 4069, 16384⟩
    (by decide) selected_cut_18804

theorem selected_cut_18805 : selected 8 ⟨481021, by decide⟩
    (prefixPartial 13 287767) = some ⟨13, 2, 0, 481021, 287767, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_287767_481021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287767 ⟨481021, by decide⟩ :=
  accepted_of_selected 13 287767 ⟨481021, by decide⟩ ⟨13, 2, 0, 481021, 287767, 2225, 16384⟩
    (by decide) selected_cut_18805

theorem unmarked_context_12_71941_481022 : frontier 9 ⟨481022, by decide⟩
    (prefixCache 12 71941) (prefixPartial 12 71941) = false := by
  decide +kernel

theorem node_context_12_71941_481022 : EJMOriginalGlobalDAGData.nodes 9 ⟨481022, by decide⟩ =
    .split (coordinate 12) (![⟨480624, by decide⟩,⟨480808, by decide⟩,⟨480943, by decide⟩,⟨481021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71941_481022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71941 ⟨481022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71941
    ⟨481022, by decide⟩ (by decide) (![⟨480624, by decide⟩,⟨480808, by decide⟩,⟨480943, by decide⟩,⟨481021, by decide⟩]) unmarked_context_12_71941_481022 node_context_12_71941_481022
  intro a
  fin_cases a
  · exact context_13_287764_480624
  · exact context_13_287765_480808
  · exact context_13_287766_480943
  · exact context_13_287767_481021

theorem selected_cut_18806 : selected 7 ⟨481054, by decide⟩
    (prefixPartial 14 1151072) = some ⟨14, 2, 0, 481054, 1151072, 1101, 4096⟩ := by
  decide +kernel

theorem context_14_1151072_481054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151072 ⟨481054, by decide⟩ :=
  accepted_of_selected 14 1151072 ⟨481054, by decide⟩ ⟨14, 2, 0, 481054, 1151072, 1101, 4096⟩
    (by decide) selected_cut_18806

theorem selected_cut_18807 : selected 7 ⟨481076, by decide⟩
    (prefixPartial 14 1151073) = some ⟨14, 2, 0, 481076, 1151073, 1129, 4096⟩ := by
  decide +kernel

theorem context_14_1151073_481076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151073 ⟨481076, by decide⟩ :=
  accepted_of_selected 14 1151073 ⟨481076, by decide⟩ ⟨14, 2, 0, 481076, 1151073, 1129, 4096⟩
    (by decide) selected_cut_18807

theorem selected_cut_18808 : selected 7 ⟨481120, by decide⟩
    (prefixPartial 14 1151074) = some ⟨14, 2, 0, 481120, 1151074, 1785, 4096⟩ := by
  decide +kernel

theorem context_14_1151074_481120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151074 ⟨481120, by decide⟩ :=
  accepted_of_selected 14 1151074 ⟨481120, by decide⟩ ⟨14, 2, 0, 481120, 1151074, 1785, 4096⟩
    (by decide) selected_cut_18808

theorem selected_cut_18809 : selected 7 ⟨481154, by decide⟩
    (prefixPartial 14 1151075) = some ⟨14, 2, 0, 481154, 1151075, 1665, 4096⟩ := by
  decide +kernel

theorem context_14_1151075_481154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151075 ⟨481154, by decide⟩ :=
  accepted_of_selected 14 1151075 ⟨481154, by decide⟩ ⟨14, 2, 0, 481154, 1151075, 1665, 4096⟩
    (by decide) selected_cut_18809

theorem unmarked_context_13_287768_481155 : frontier 8 ⟨481155, by decide⟩
    (prefixCache 13 287768) (prefixPartial 13 287768) = false := by
  decide +kernel

theorem node_context_13_287768_481155 : EJMOriginalGlobalDAGData.nodes 8 ⟨481155, by decide⟩ =
    .split (coordinate 13) (![⟨481054, by decide⟩,⟨481076, by decide⟩,⟨481120, by decide⟩,⟨481154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287768_481155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287768 ⟨481155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287768
    ⟨481155, by decide⟩ (by decide) (![⟨481054, by decide⟩,⟨481076, by decide⟩,⟨481120, by decide⟩,⟨481154, by decide⟩]) unmarked_context_13_287768_481155 node_context_13_287768_481155
  intro a
  fin_cases a
  · exact context_14_1151072_481054
  · exact context_14_1151073_481076
  · exact context_14_1151074_481120
  · exact context_14_1151075_481154

theorem selected_cut_18810 : selected 7 ⟨481173, by decide⟩
    (prefixPartial 14 1151076) = some ⟨14, 2, 0, 481173, 1151076, 881, 4096⟩ := by
  decide +kernel

theorem context_14_1151076_481173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151076 ⟨481173, by decide⟩ :=
  accepted_of_selected 14 1151076 ⟨481173, by decide⟩ ⟨14, 2, 0, 481173, 1151076, 881, 4096⟩
    (by decide) selected_cut_18810

theorem selected_cut_18811 : selected 7 ⟨481194, by decide⟩
    (prefixPartial 14 1151077) = some ⟨14, 2, 0, 481194, 1151077, 1049, 4096⟩ := by
  decide +kernel

theorem context_14_1151077_481194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151077 ⟨481194, by decide⟩ :=
  accepted_of_selected 14 1151077 ⟨481194, by decide⟩ ⟨14, 2, 0, 481194, 1151077, 1049, 4096⟩
    (by decide) selected_cut_18811

theorem selected_cut_18812 : selected 7 ⟨481235, by decide⟩
    (prefixPartial 14 1151078) = some ⟨14, 2, 0, 481235, 1151078, 1353, 4096⟩ := by
  decide +kernel

theorem context_14_1151078_481235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151078 ⟨481235, by decide⟩ :=
  accepted_of_selected 14 1151078 ⟨481235, by decide⟩ ⟨14, 2, 0, 481235, 1151078, 1353, 4096⟩
    (by decide) selected_cut_18812

theorem selected_cut_18813 : selected 7 ⟨481268, by decide⟩
    (prefixPartial 14 1151079) = some ⟨14, 2, 0, 481268, 1151079, 1297, 4096⟩ := by
  decide +kernel

theorem context_14_1151079_481268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151079 ⟨481268, by decide⟩ :=
  accepted_of_selected 14 1151079 ⟨481268, by decide⟩ ⟨14, 2, 0, 481268, 1151079, 1297, 4096⟩
    (by decide) selected_cut_18813

theorem unmarked_context_13_287769_481269 : frontier 8 ⟨481269, by decide⟩
    (prefixCache 13 287769) (prefixPartial 13 287769) = false := by
  decide +kernel

theorem node_context_13_287769_481269 : EJMOriginalGlobalDAGData.nodes 8 ⟨481269, by decide⟩ =
    .split (coordinate 13) (![⟨481173, by decide⟩,⟨481194, by decide⟩,⟨481235, by decide⟩,⟨481268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287769_481269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287769 ⟨481269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287769
    ⟨481269, by decide⟩ (by decide) (![⟨481173, by decide⟩,⟨481194, by decide⟩,⟨481235, by decide⟩,⟨481268, by decide⟩]) unmarked_context_13_287769_481269 node_context_13_287769_481269
  intro a
  fin_cases a
  · exact context_14_1151076_481173
  · exact context_14_1151077_481194
  · exact context_14_1151078_481235
  · exact context_14_1151079_481268

theorem selected_cut_18814 : selected 8 ⟨481349, by decide⟩
    (prefixPartial 13 287770) = some ⟨13, 2, 0, 481349, 287770, 3077, 16384⟩ := by
  decide +kernel

theorem context_13_287770_481349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287770 ⟨481349, by decide⟩ :=
  accepted_of_selected 13 287770 ⟨481349, by decide⟩ ⟨13, 2, 0, 481349, 287770, 3077, 16384⟩
    (by decide) selected_cut_18814

theorem selected_cut_18815 : selected 8 ⟨481385, by decide⟩
    (prefixPartial 13 287771) = some ⟨13, 2, 0, 481385, 287771, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_287771_481385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287771 ⟨481385, by decide⟩ :=
  accepted_of_selected 13 287771 ⟨481385, by decide⟩ ⟨13, 2, 0, 481385, 287771, 1649, 16384⟩
    (by decide) selected_cut_18815

theorem unmarked_context_12_71942_481386 : frontier 9 ⟨481386, by decide⟩
    (prefixCache 12 71942) (prefixPartial 12 71942) = false := by
  decide +kernel

theorem node_context_12_71942_481386 : EJMOriginalGlobalDAGData.nodes 9 ⟨481386, by decide⟩ =
    .split (coordinate 12) (![⟨481155, by decide⟩,⟨481269, by decide⟩,⟨481349, by decide⟩,⟨481385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71942_481386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71942 ⟨481386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71942
    ⟨481386, by decide⟩ (by decide) (![⟨481155, by decide⟩,⟨481269, by decide⟩,⟨481349, by decide⟩,⟨481385, by decide⟩]) unmarked_context_12_71942_481386 node_context_12_71942_481386
  intro a
  fin_cases a
  · exact context_13_287768_481155
  · exact context_13_287769_481269
  · exact context_13_287770_481349
  · exact context_13_287771_481385

theorem selected_cut_18816 : selected 7 ⟨481407, by decide⟩
    (prefixPartial 14 1151088) = some ⟨14, 2, 0, 481407, 1151088, 941, 4096⟩ := by
  decide +kernel

theorem context_14_1151088_481407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151088 ⟨481407, by decide⟩ :=
  accepted_of_selected 14 1151088 ⟨481407, by decide⟩ ⟨14, 2, 0, 481407, 1151088, 941, 4096⟩
    (by decide) selected_cut_18816

theorem selected_cut_18817 : selected 7 ⟨481437, by decide⟩
    (prefixPartial 14 1151089) = some ⟨14, 2, 0, 481437, 1151089, 1213, 4096⟩ := by
  decide +kernel

theorem context_14_1151089_481437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151089 ⟨481437, by decide⟩ :=
  accepted_of_selected 14 1151089 ⟨481437, by decide⟩ ⟨14, 2, 0, 481437, 1151089, 1213, 4096⟩
    (by decide) selected_cut_18817

theorem selected_cut_18818 : selected 7 ⟨481469, by decide⟩
    (prefixPartial 14 1151090) = some ⟨14, 2, 0, 481469, 1151090, 1725, 4096⟩ := by
  decide +kernel

theorem context_14_1151090_481469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151090 ⟨481469, by decide⟩ :=
  accepted_of_selected 14 1151090 ⟨481469, by decide⟩ ⟨14, 2, 0, 481469, 1151090, 1725, 4096⟩
    (by decide) selected_cut_18818

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
