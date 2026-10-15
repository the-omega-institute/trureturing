/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover448
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_43107 : selected 10 ⟨1178271, by decide⟩
    (prefixPartial 11 84837) = some ⟨11, 2, 0, 1178271, 84837, 1905, 262144⟩ := by
  decide +kernel

theorem context_11_84837_1178271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84837 ⟨1178271, by decide⟩ :=
  accepted_of_selected 11 84837 ⟨1178271, by decide⟩ ⟨11, 2, 0, 1178271, 84837, 1905, 262144⟩
    (by decide) selected_cut_43107

theorem selected_cut_43108 : selected 10 ⟨1178313, by decide⟩
    (prefixPartial 11 84838) = some ⟨11, 2, 0, 1178313, 84838, 2965, 262144⟩ := by
  decide +kernel

theorem context_11_84838_1178313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84838 ⟨1178313, by decide⟩ :=
  accepted_of_selected 11 84838 ⟨1178313, by decide⟩ ⟨11, 2, 0, 1178313, 84838, 2965, 262144⟩
    (by decide) selected_cut_43108

theorem selected_cut_43109 : selected 10 ⟨1178378, by decide⟩
    (prefixPartial 11 84839) = some ⟨11, 2, 0, 1178378, 84839, 2865, 262144⟩ := by
  decide +kernel

theorem context_11_84839_1178378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84839 ⟨1178378, by decide⟩ :=
  accepted_of_selected 11 84839 ⟨1178378, by decide⟩ ⟨11, 2, 0, 1178378, 84839, 2865, 262144⟩
    (by decide) selected_cut_43109

theorem unmarked_context_10_21209_1178379 : frontier 11 ⟨1178379, by decide⟩
    (prefixCache 10 21209) (prefixPartial 10 21209) = false := by
  decide +kernel

theorem node_context_10_21209_1178379 : EJMOriginalGlobalDAGData.nodes 11 ⟨1178379, by decide⟩ =
    .split (coordinate 10) (![⟨1178238, by decide⟩,⟨1178271, by decide⟩,⟨1178313, by decide⟩,⟨1178378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21209_1178379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21209 ⟨1178379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21209
    ⟨1178379, by decide⟩ (by decide) (![⟨1178238, by decide⟩,⟨1178271, by decide⟩,⟨1178313, by decide⟩,⟨1178378, by decide⟩]) unmarked_context_10_21209_1178379 node_context_10_21209_1178379
  intro a
  fin_cases a
  · exact context_11_84836_1178238
  · exact context_11_84837_1178271
  · exact context_11_84838_1178313
  · exact context_11_84839_1178378

theorem selected_cut_43110 : selected 10 ⟨1178422, by decide⟩
    (prefixPartial 11 84840) = some ⟨11, 2, 0, 1178422, 84840, 2613, 262144⟩ := by
  decide +kernel

theorem context_11_84840_1178422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84840 ⟨1178422, by decide⟩ :=
  accepted_of_selected 11 84840 ⟨1178422, by decide⟩ ⟨11, 2, 0, 1178422, 84840, 2613, 262144⟩
    (by decide) selected_cut_43110

theorem selected_cut_43111 : selected 10 ⟨1178458, by decide⟩
    (prefixPartial 11 84841) = some ⟨11, 2, 0, 1178458, 84841, 1773, 262144⟩ := by
  decide +kernel

theorem context_11_84841_1178458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84841 ⟨1178458, by decide⟩ :=
  accepted_of_selected 11 84841 ⟨1178458, by decide⟩ ⟨11, 2, 0, 1178458, 84841, 1773, 262144⟩
    (by decide) selected_cut_43111

theorem selected_cut_43112 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84842) = some ⟨11, 1, 0, 1109453, 84842, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84842_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84842 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84842 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84842, 1, 262144⟩
    (by decide) selected_cut_43112

theorem selected_cut_43113 : selected 10 ⟨1178492, by decide⟩
    (prefixPartial 11 84843) = some ⟨11, 2, 0, 1178492, 84843, 2357, 262144⟩ := by
  decide +kernel

theorem context_11_84843_1178492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84843 ⟨1178492, by decide⟩ :=
  accepted_of_selected 11 84843 ⟨1178492, by decide⟩ ⟨11, 2, 0, 1178492, 84843, 2357, 262144⟩
    (by decide) selected_cut_43113

theorem unmarked_context_10_21210_1178493 : frontier 11 ⟨1178493, by decide⟩
    (prefixCache 10 21210) (prefixPartial 10 21210) = false := by
  decide +kernel

theorem node_context_10_21210_1178493 : EJMOriginalGlobalDAGData.nodes 11 ⟨1178493, by decide⟩ =
    .split (coordinate 10) (![⟨1178422, by decide⟩,⟨1178458, by decide⟩,⟨1109453, by decide⟩,⟨1178492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21210_1178493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21210 ⟨1178493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21210
    ⟨1178493, by decide⟩ (by decide) (![⟨1178422, by decide⟩,⟨1178458, by decide⟩,⟨1109453, by decide⟩,⟨1178492, by decide⟩]) unmarked_context_10_21210_1178493 node_context_10_21210_1178493
  intro a
  fin_cases a
  · exact context_11_84840_1178422
  · exact context_11_84841_1178458
  · exact context_11_84842_1109453
  · exact context_11_84843_1178492

theorem selected_cut_43114 : selected 10 ⟨1178543, by decide⟩
    (prefixPartial 11 84844) = some ⟨11, 2, 0, 1178543, 84844, 2777, 262144⟩ := by
  decide +kernel

theorem context_11_84844_1178543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84844 ⟨1178543, by decide⟩ :=
  accepted_of_selected 11 84844 ⟨1178543, by decide⟩ ⟨11, 2, 0, 1178543, 84844, 2777, 262144⟩
    (by decide) selected_cut_43114

theorem selected_cut_43115 : selected 10 ⟨1178571, by decide⟩
    (prefixPartial 11 84845) = some ⟨11, 2, 0, 1178571, 84845, 1705, 262144⟩ := by
  decide +kernel

theorem context_11_84845_1178571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84845 ⟨1178571, by decide⟩ :=
  accepted_of_selected 11 84845 ⟨1178571, by decide⟩ ⟨11, 2, 0, 1178571, 84845, 1705, 262144⟩
    (by decide) selected_cut_43115

theorem selected_cut_43116 : selected 10 ⟨1178605, by decide⟩
    (prefixPartial 11 84846) = some ⟨11, 2, 0, 1178605, 84846, 1657, 262144⟩ := by
  decide +kernel

theorem context_11_84846_1178605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84846 ⟨1178605, by decide⟩ :=
  accepted_of_selected 11 84846 ⟨1178605, by decide⟩ ⟨11, 2, 0, 1178605, 84846, 1657, 262144⟩
    (by decide) selected_cut_43116

theorem selected_cut_43117 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 84847) = some ⟨11, 1, 0, 977886, 84847, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84847_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84847 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 84847 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 84847, 1, 262144⟩
    (by decide) selected_cut_43117

theorem unmarked_context_10_21211_1178606 : frontier 11 ⟨1178606, by decide⟩
    (prefixCache 10 21211) (prefixPartial 10 21211) = false := by
  decide +kernel

theorem node_context_10_21211_1178606 : EJMOriginalGlobalDAGData.nodes 11 ⟨1178606, by decide⟩ =
    .split (coordinate 10) (![⟨1178543, by decide⟩,⟨1178571, by decide⟩,⟨1178605, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21211_1178606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21211 ⟨1178606, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21211
    ⟨1178606, by decide⟩ (by decide) (![⟨1178543, by decide⟩,⟨1178571, by decide⟩,⟨1178605, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_21211_1178606 node_context_10_21211_1178606
  intro a
  fin_cases a
  · exact context_11_84844_1178543
  · exact context_11_84845_1178571
  · exact context_11_84846_1178605
  · exact context_11_84847_977886

theorem unmarked_context_9_5302_1178607 : frontier 12 ⟨1178607, by decide⟩
    (prefixCache 9 5302) (prefixPartial 9 5302) = false := by
  decide +kernel

theorem node_context_9_5302_1178607 : EJMOriginalGlobalDAGData.nodes 12 ⟨1178607, by decide⟩ =
    .split (coordinate 9) (![⟨1178157, by decide⟩,⟨1178379, by decide⟩,⟨1178493, by decide⟩,⟨1178606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5302_1178607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5302 ⟨1178607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5302
    ⟨1178607, by decide⟩ (by decide) (![⟨1178157, by decide⟩,⟨1178379, by decide⟩,⟨1178493, by decide⟩,⟨1178606, by decide⟩]) unmarked_context_9_5302_1178607 node_context_9_5302_1178607
  intro a
  fin_cases a
  · exact context_10_21208_1178157
  · exact context_10_21209_1178379
  · exact context_10_21210_1178493
  · exact context_10_21211_1178606

theorem selected_cut_43118 : selected 10 ⟨1178643, by decide⟩
    (prefixPartial 11 84848) = some ⟨11, 2, 0, 1178643, 84848, 2009, 262144⟩ := by
  decide +kernel

theorem context_11_84848_1178643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84848 ⟨1178643, by decide⟩ :=
  accepted_of_selected 11 84848 ⟨1178643, by decide⟩ ⟨11, 2, 0, 1178643, 84848, 2009, 262144⟩
    (by decide) selected_cut_43118

theorem selected_cut_43119 : selected 10 ⟨1178668, by decide⟩
    (prefixPartial 11 84849) = some ⟨11, 2, 0, 1178668, 84849, 1609, 262144⟩ := by
  decide +kernel

theorem context_11_84849_1178668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84849 ⟨1178668, by decide⟩ :=
  accepted_of_selected 11 84849 ⟨1178668, by decide⟩ ⟨11, 2, 0, 1178668, 84849, 1609, 262144⟩
    (by decide) selected_cut_43119

theorem selected_cut_43120 : selected 10 ⟨1178699, by decide⟩
    (prefixPartial 11 84850) = some ⟨11, 2, 0, 1178699, 84850, 1925, 262144⟩ := by
  decide +kernel

theorem context_11_84850_1178699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84850 ⟨1178699, by decide⟩ :=
  accepted_of_selected 11 84850 ⟨1178699, by decide⟩ ⟨11, 2, 0, 1178699, 84850, 1925, 262144⟩
    (by decide) selected_cut_43120

theorem selected_cut_43121 : selected 10 ⟨1178715, by decide⟩
    (prefixPartial 11 84851) = some ⟨11, 2, 0, 1178715, 84851, 1093, 262144⟩ := by
  decide +kernel

theorem context_11_84851_1178715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84851 ⟨1178715, by decide⟩ :=
  accepted_of_selected 11 84851 ⟨1178715, by decide⟩ ⟨11, 2, 0, 1178715, 84851, 1093, 262144⟩
    (by decide) selected_cut_43121

theorem unmarked_context_10_21212_1178716 : frontier 11 ⟨1178716, by decide⟩
    (prefixCache 10 21212) (prefixPartial 10 21212) = false := by
  decide +kernel

theorem node_context_10_21212_1178716 : EJMOriginalGlobalDAGData.nodes 11 ⟨1178716, by decide⟩ =
    .split (coordinate 10) (![⟨1178643, by decide⟩,⟨1178668, by decide⟩,⟨1178699, by decide⟩,⟨1178715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21212_1178716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21212 ⟨1178716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21212
    ⟨1178716, by decide⟩ (by decide) (![⟨1178643, by decide⟩,⟨1178668, by decide⟩,⟨1178699, by decide⟩,⟨1178715, by decide⟩]) unmarked_context_10_21212_1178716 node_context_10_21212_1178716
  intro a
  fin_cases a
  · exact context_11_84848_1178643
  · exact context_11_84849_1178668
  · exact context_11_84850_1178699
  · exact context_11_84851_1178715

theorem selected_cut_43122 : selected 11 ⟨1178782, by decide⟩
    (prefixPartial 10 21213) = some ⟨10, 2, 0, 1178782, 21213, 3329, 1048576⟩ := by
  decide +kernel

theorem context_10_21213_1178782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21213 ⟨1178782, by decide⟩ :=
  accepted_of_selected 10 21213 ⟨1178782, by decide⟩ ⟨10, 2, 0, 1178782, 21213, 3329, 1048576⟩
    (by decide) selected_cut_43122

theorem selected_cut_43123 : selected 11 ⟨1178831, by decide⟩
    (prefixPartial 10 21214) = some ⟨10, 2, 0, 1178831, 21214, 2181, 1048576⟩ := by
  decide +kernel

theorem context_10_21214_1178831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21214 ⟨1178831, by decide⟩ :=
  accepted_of_selected 10 21214 ⟨1178831, by decide⟩ ⟨10, 2, 0, 1178831, 21214, 2181, 1048576⟩
    (by decide) selected_cut_43123

theorem selected_cut_43124 : selected 11 ⟨1178846, by decide⟩
    (prefixPartial 10 21215) = some ⟨10, 2, 0, 1178846, 21215, 305, 1048576⟩ := by
  decide +kernel

theorem context_10_21215_1178846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21215 ⟨1178846, by decide⟩ :=
  accepted_of_selected 10 21215 ⟨1178846, by decide⟩ ⟨10, 2, 0, 1178846, 21215, 305, 1048576⟩
    (by decide) selected_cut_43124

theorem unmarked_context_9_5303_1178847 : frontier 12 ⟨1178847, by decide⟩
    (prefixCache 9 5303) (prefixPartial 9 5303) = false := by
  decide +kernel

theorem node_context_9_5303_1178847 : EJMOriginalGlobalDAGData.nodes 12 ⟨1178847, by decide⟩ =
    .split (coordinate 9) (![⟨1178716, by decide⟩,⟨1178782, by decide⟩,⟨1178831, by decide⟩,⟨1178846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5303_1178847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5303 ⟨1178847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5303
    ⟨1178847, by decide⟩ (by decide) (![⟨1178716, by decide⟩,⟨1178782, by decide⟩,⟨1178831, by decide⟩,⟨1178846, by decide⟩]) unmarked_context_9_5303_1178847 node_context_9_5303_1178847
  intro a
  fin_cases a
  · exact context_10_21212_1178716
  · exact context_10_21213_1178782
  · exact context_10_21214_1178831
  · exact context_10_21215_1178846

theorem unmarked_context_8_1325_1178848 : frontier 13 ⟨1178848, by decide⟩
    (prefixCache 8 1325) (prefixPartial 8 1325) = false := by
  decide +kernel

theorem node_context_8_1325_1178848 : EJMOriginalGlobalDAGData.nodes 13 ⟨1178848, by decide⟩ =
    .split (coordinate 8) (![⟨1177057, by decide⟩,⟨1177862, by decide⟩,⟨1178607, by decide⟩,⟨1178847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1325_1178848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1325 ⟨1178848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1325
    ⟨1178848, by decide⟩ (by decide) (![⟨1177057, by decide⟩,⟨1177862, by decide⟩,⟨1178607, by decide⟩,⟨1178847, by decide⟩]) unmarked_context_8_1325_1178848 node_context_8_1325_1178848
  intro a
  fin_cases a
  · exact context_9_5300_1177057
  · exact context_9_5301_1177862
  · exact context_9_5302_1178607
  · exact context_9_5303_1178847

theorem selected_cut_43125 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84864) = some ⟨11, 1, 0, 434745, 84864, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84864_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84864 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84864 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84864, 1, 262144⟩
    (by decide) selected_cut_43125

theorem selected_cut_43126 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 339460) = some ⟨12, 1, 0, 448748, 339460, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339460_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339460 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 339460 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 339460, 1, 65536⟩
    (by decide) selected_cut_43126

theorem selected_cut_43127 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 339461) = some ⟨12, 1, 0, 34034, 339461, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339461_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339461 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 339461 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 339461, 1, 65536⟩
    (by decide) selected_cut_43127

theorem selected_cut_43128 : selected 9 ⟨1178918, by decide⟩
    (prefixPartial 12 339462) = some ⟨12, 2, 0, 1178918, 339462, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_339462_1178918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339462 ⟨1178918, by decide⟩ :=
  accepted_of_selected 12 339462 ⟨1178918, by decide⟩ ⟨12, 2, 0, 1178918, 339462, 3097, 65536⟩
    (by decide) selected_cut_43128

theorem selected_cut_43129 : selected 9 ⟨1179004, by decide⟩
    (prefixPartial 12 339463) = some ⟨12, 2, 0, 1179004, 339463, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_339463_1179004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339463 ⟨1179004, by decide⟩ :=
  accepted_of_selected 12 339463 ⟨1179004, by decide⟩ ⟨12, 2, 0, 1179004, 339463, 3761, 65536⟩
    (by decide) selected_cut_43129

theorem unmarked_context_11_84865_1179005 : frontier 10 ⟨1179005, by decide⟩
    (prefixCache 11 84865) (prefixPartial 11 84865) = false := by
  decide +kernel

theorem node_context_11_84865_1179005 : EJMOriginalGlobalDAGData.nodes 10 ⟨1179005, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1178918, by decide⟩,⟨1179004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84865_1179005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84865 ⟨1179005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84865
    ⟨1179005, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1178918, by decide⟩,⟨1179004, by decide⟩]) unmarked_context_11_84865_1179005 node_context_11_84865_1179005
  intro a
  fin_cases a
  · exact context_12_339460_448748
  · exact context_12_339461_34034
  · exact context_12_339462_1178918
  · exact context_12_339463_1179004

theorem selected_cut_43130 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 339464) = some ⟨12, 1, 0, 448748, 339464, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339464_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339464 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 339464 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 339464, 1, 65536⟩
    (by decide) selected_cut_43130

theorem selected_cut_43131 : selected 9 ⟨1179077, by decide⟩
    (prefixPartial 12 339465) = some ⟨12, 2, 0, 1179077, 339465, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_339465_1179077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339465 ⟨1179077, by decide⟩ :=
  accepted_of_selected 12 339465 ⟨1179077, by decide⟩ ⟨12, 2, 0, 1179077, 339465, 3429, 65536⟩
    (by decide) selected_cut_43131

theorem selected_cut_43132 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 339466) = some ⟨12, 1, 0, 893903, 339466, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339466_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339466 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 339466 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 339466, 1, 65536⟩
    (by decide) selected_cut_43132

theorem selected_cut_43133 : selected 9 ⟨1179149, by decide⟩
    (prefixPartial 12 339467) = some ⟨12, 2, 0, 1179149, 339467, 3685, 65536⟩ := by
  decide +kernel

theorem context_12_339467_1179149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339467 ⟨1179149, by decide⟩ :=
  accepted_of_selected 12 339467 ⟨1179149, by decide⟩ ⟨12, 2, 0, 1179149, 339467, 3685, 65536⟩
    (by decide) selected_cut_43133

theorem unmarked_context_11_84866_1179150 : frontier 10 ⟨1179150, by decide⟩
    (prefixCache 11 84866) (prefixPartial 11 84866) = false := by
  decide +kernel

theorem node_context_11_84866_1179150 : EJMOriginalGlobalDAGData.nodes 10 ⟨1179150, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1179077, by decide⟩,⟨893903, by decide⟩,⟨1179149, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84866_1179150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84866 ⟨1179150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84866
    ⟨1179150, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1179077, by decide⟩,⟨893903, by decide⟩,⟨1179149, by decide⟩]) unmarked_context_11_84866_1179150 node_context_11_84866_1179150
  intro a
  fin_cases a
  · exact context_12_339464_448748
  · exact context_12_339465_1179077
  · exact context_12_339466_893903
  · exact context_12_339467_1179149

theorem selected_cut_43134 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 339468) = some ⟨12, 1, 0, 448748, 339468, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339468_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339468 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 339468 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 339468, 1, 65536⟩
    (by decide) selected_cut_43134

theorem selected_cut_43135 : selected 9 ⟨390434, by decide⟩
    (prefixPartial 12 339469) = some ⟨12, 1, 0, 390434, 339469, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339469_390434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339469 ⟨390434, by decide⟩ :=
  accepted_of_selected 12 339469 ⟨390434, by decide⟩ ⟨12, 1, 0, 390434, 339469, 1, 65536⟩
    (by decide) selected_cut_43135

theorem selected_cut_43136 : selected 9 ⟨1179200, by decide⟩
    (prefixPartial 12 339470) = some ⟨12, 2, 0, 1179200, 339470, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_339470_1179200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339470 ⟨1179200, by decide⟩ :=
  accepted_of_selected 12 339470 ⟨1179200, by decide⟩ ⟨12, 2, 0, 1179200, 339470, 2713, 65536⟩
    (by decide) selected_cut_43136

theorem selected_cut_43137 : selected 9 ⟨1179259, by decide⟩
    (prefixPartial 12 339471) = some ⟨12, 2, 0, 1179259, 339471, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_339471_1179259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339471 ⟨1179259, by decide⟩ :=
  accepted_of_selected 12 339471 ⟨1179259, by decide⟩ ⟨12, 2, 0, 1179259, 339471, 3009, 65536⟩
    (by decide) selected_cut_43137

theorem unmarked_context_11_84867_1179260 : frontier 10 ⟨1179260, by decide⟩
    (prefixCache 11 84867) (prefixPartial 11 84867) = false := by
  decide +kernel

theorem node_context_11_84867_1179260 : EJMOriginalGlobalDAGData.nodes 10 ⟨1179260, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨1179200, by decide⟩,⟨1179259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84867_1179260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84867 ⟨1179260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84867
    ⟨1179260, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨1179200, by decide⟩,⟨1179259, by decide⟩]) unmarked_context_11_84867_1179260 node_context_11_84867_1179260
  intro a
  fin_cases a
  · exact context_12_339468_448748
  · exact context_12_339469_390434
  · exact context_12_339470_1179200
  · exact context_12_339471_1179259

theorem unmarked_context_10_21216_1179261 : frontier 11 ⟨1179261, by decide⟩
    (prefixCache 10 21216) (prefixPartial 10 21216) = false := by
  decide +kernel

theorem node_context_10_21216_1179261 : EJMOriginalGlobalDAGData.nodes 11 ⟨1179261, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1179005, by decide⟩,⟨1179150, by decide⟩,⟨1179260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21216_1179261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21216 ⟨1179261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21216
    ⟨1179261, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1179005, by decide⟩,⟨1179150, by decide⟩,⟨1179260, by decide⟩]) unmarked_context_10_21216_1179261 node_context_10_21216_1179261
  intro a
  fin_cases a
  · exact context_11_84864_434745
  · exact context_11_84865_1179005
  · exact context_11_84866_1179150
  · exact context_11_84867_1179260

theorem selected_cut_43138 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339472) = some ⟨12, 1, 0, 1108174, 339472, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339472_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339472 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339472 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339472, 1, 65536⟩
    (by decide) selected_cut_43138

theorem selected_cut_43139 : selected 9 ⟨1179315, by decide⟩
    (prefixPartial 12 339473) = some ⟨12, 2, 0, 1179315, 339473, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_339473_1179315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339473 ⟨1179315, by decide⟩ :=
  accepted_of_selected 12 339473 ⟨1179315, by decide⟩ ⟨12, 2, 0, 1179315, 339473, 3081, 65536⟩
    (by decide) selected_cut_43139

theorem selected_cut_43140 : selected 9 ⟨1179381, by decide⟩
    (prefixPartial 12 339474) = some ⟨12, 2, 0, 1179381, 339474, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_339474_1179381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339474 ⟨1179381, by decide⟩ :=
  accepted_of_selected 12 339474 ⟨1179381, by decide⟩ ⟨12, 2, 0, 1179381, 339474, 2945, 65536⟩
    (by decide) selected_cut_43140

theorem selected_cut_43141 : selected 9 ⟨1179455, by decide⟩
    (prefixPartial 12 339475) = some ⟨12, 2, 0, 1179455, 339475, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_339475_1179455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339475 ⟨1179455, by decide⟩ :=
  accepted_of_selected 12 339475 ⟨1179455, by decide⟩ ⟨12, 2, 0, 1179455, 339475, 3493, 65536⟩
    (by decide) selected_cut_43141

theorem unmarked_context_11_84868_1179456 : frontier 10 ⟨1179456, by decide⟩
    (prefixCache 11 84868) (prefixPartial 11 84868) = false := by
  decide +kernel

theorem node_context_11_84868_1179456 : EJMOriginalGlobalDAGData.nodes 10 ⟨1179456, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1179315, by decide⟩,⟨1179381, by decide⟩,⟨1179455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84868_1179456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84868 ⟨1179456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84868
    ⟨1179456, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1179315, by decide⟩,⟨1179381, by decide⟩,⟨1179455, by decide⟩]) unmarked_context_11_84868_1179456 node_context_11_84868_1179456
  intro a
  fin_cases a
  · exact context_12_339472_1108174
  · exact context_12_339473_1179315
  · exact context_12_339474_1179381
  · exact context_12_339475_1179455

theorem selected_cut_43142 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339476) = some ⟨12, 1, 0, 1108174, 339476, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339476_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339476 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339476 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339476, 1, 65536⟩
    (by decide) selected_cut_43142

theorem selected_cut_43143 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 339477) = some ⟨12, 1, 0, 1172003, 339477, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339477_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339477 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 339477 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 339477, 1, 65536⟩
    (by decide) selected_cut_43143

theorem selected_cut_43144 : selected 9 ⟨1179515, by decide⟩
    (prefixPartial 12 339478) = some ⟨12, 2, 0, 1179515, 339478, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_339478_1179515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339478 ⟨1179515, by decide⟩ :=
  accepted_of_selected 12 339478 ⟨1179515, by decide⟩ ⟨12, 2, 0, 1179515, 339478, 2957, 65536⟩
    (by decide) selected_cut_43144

theorem selected_cut_43145 : selected 9 ⟨1179575, by decide⟩
    (prefixPartial 12 339479) = some ⟨12, 2, 0, 1179575, 339479, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_339479_1179575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339479 ⟨1179575, by decide⟩ :=
  accepted_of_selected 12 339479 ⟨1179575, by decide⟩ ⟨12, 2, 0, 1179575, 339479, 3509, 65536⟩
    (by decide) selected_cut_43145

theorem unmarked_context_11_84869_1179576 : frontier 10 ⟨1179576, by decide⟩
    (prefixCache 11 84869) (prefixPartial 11 84869) = false := by
  decide +kernel

theorem node_context_11_84869_1179576 : EJMOriginalGlobalDAGData.nodes 10 ⟨1179576, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1172003, by decide⟩,⟨1179515, by decide⟩,⟨1179575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84869_1179576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84869 ⟨1179576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84869
    ⟨1179576, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1172003, by decide⟩,⟨1179515, by decide⟩,⟨1179575, by decide⟩]) unmarked_context_11_84869_1179576 node_context_11_84869_1179576
  intro a
  fin_cases a
  · exact context_12_339476_1108174
  · exact context_12_339477_1172003
  · exact context_12_339478_1179515
  · exact context_12_339479_1179575

theorem selected_cut_43146 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339480) = some ⟨12, 1, 0, 1108174, 339480, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339480_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339480 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339480 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339480, 1, 65536⟩
    (by decide) selected_cut_43146

theorem selected_cut_43147 : selected 9 ⟨1179628, by decide⟩
    (prefixPartial 12 339481) = some ⟨12, 2, 0, 1179628, 339481, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_339481_1179628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339481 ⟨1179628, by decide⟩ :=
  accepted_of_selected 12 339481 ⟨1179628, by decide⟩ ⟨12, 2, 0, 1179628, 339481, 2729, 65536⟩
    (by decide) selected_cut_43147

theorem selected_cut_43148 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 339482) = some ⟨12, 1, 0, 893903, 339482, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339482_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339482 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 339482 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 339482, 1, 65536⟩
    (by decide) selected_cut_43148

theorem selected_cut_43149 : selected 9 ⟨1179683, by decide⟩
    (prefixPartial 12 339483) = some ⟨12, 2, 0, 1179683, 339483, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_339483_1179683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339483 ⟨1179683, by decide⟩ :=
  accepted_of_selected 12 339483 ⟨1179683, by decide⟩ ⟨12, 2, 0, 1179683, 339483, 3121, 65536⟩
    (by decide) selected_cut_43149

theorem unmarked_context_11_84870_1179684 : frontier 10 ⟨1179684, by decide⟩
    (prefixCache 11 84870) (prefixPartial 11 84870) = false := by
  decide +kernel

theorem node_context_11_84870_1179684 : EJMOriginalGlobalDAGData.nodes 10 ⟨1179684, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1179628, by decide⟩,⟨893903, by decide⟩,⟨1179683, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84870_1179684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84870 ⟨1179684, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84870
    ⟨1179684, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1179628, by decide⟩,⟨893903, by decide⟩,⟨1179683, by decide⟩]) unmarked_context_11_84870_1179684 node_context_11_84870_1179684
  intro a
  fin_cases a
  · exact context_12_339480_1108174
  · exact context_12_339481_1179628
  · exact context_12_339482_893903
  · exact context_12_339483_1179683

theorem selected_cut_43150 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339484) = some ⟨12, 1, 0, 1108174, 339484, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339484_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339484 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339484 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339484, 1, 65536⟩
    (by decide) selected_cut_43150

theorem selected_cut_43151 : selected 9 ⟨1179725, by decide⟩
    (prefixPartial 12 339485) = some ⟨12, 2, 0, 1179725, 339485, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_339485_1179725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339485 ⟨1179725, by decide⟩ :=
  accepted_of_selected 12 339485 ⟨1179725, by decide⟩ ⟨12, 2, 0, 1179725, 339485, 2541, 65536⟩
    (by decide) selected_cut_43151

theorem selected_cut_43152 : selected 9 ⟨1179774, by decide⟩
    (prefixPartial 12 339486) = some ⟨12, 2, 0, 1179774, 339486, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_339486_1179774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339486 ⟨1179774, by decide⟩ :=
  accepted_of_selected 12 339486 ⟨1179774, by decide⟩ ⟨12, 2, 0, 1179774, 339486, 2493, 65536⟩
    (by decide) selected_cut_43152

theorem selected_cut_43153 : selected 9 ⟨1179814, by decide⟩
    (prefixPartial 12 339487) = some ⟨12, 2, 0, 1179814, 339487, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_339487_1179814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339487 ⟨1179814, by decide⟩ :=
  accepted_of_selected 12 339487 ⟨1179814, by decide⟩ ⟨12, 2, 0, 1179814, 339487, 2629, 65536⟩
    (by decide) selected_cut_43153

theorem unmarked_context_11_84871_1179815 : frontier 10 ⟨1179815, by decide⟩
    (prefixCache 11 84871) (prefixPartial 11 84871) = false := by
  decide +kernel

theorem node_context_11_84871_1179815 : EJMOriginalGlobalDAGData.nodes 10 ⟨1179815, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1179725, by decide⟩,⟨1179774, by decide⟩,⟨1179814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84871_1179815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84871 ⟨1179815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84871
    ⟨1179815, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1179725, by decide⟩,⟨1179774, by decide⟩,⟨1179814, by decide⟩]) unmarked_context_11_84871_1179815 node_context_11_84871_1179815
  intro a
  fin_cases a
  · exact context_12_339484_1108174
  · exact context_12_339485_1179725
  · exact context_12_339486_1179774
  · exact context_12_339487_1179814

theorem unmarked_context_10_21217_1179816 : frontier 11 ⟨1179816, by decide⟩
    (prefixCache 10 21217) (prefixPartial 10 21217) = false := by
  decide +kernel

theorem node_context_10_21217_1179816 : EJMOriginalGlobalDAGData.nodes 11 ⟨1179816, by decide⟩ =
    .split (coordinate 10) (![⟨1179456, by decide⟩,⟨1179576, by decide⟩,⟨1179684, by decide⟩,⟨1179815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21217_1179816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21217 ⟨1179816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21217
    ⟨1179816, by decide⟩ (by decide) (![⟨1179456, by decide⟩,⟨1179576, by decide⟩,⟨1179684, by decide⟩,⟨1179815, by decide⟩]) unmarked_context_10_21217_1179816 node_context_10_21217_1179816
  intro a
  fin_cases a
  · exact context_11_84868_1179456
  · exact context_11_84869_1179576
  · exact context_11_84870_1179684
  · exact context_11_84871_1179815

theorem selected_cut_43154 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339488) = some ⟨12, 1, 0, 1108174, 339488, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339488_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339488 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339488 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339488, 1, 65536⟩
    (by decide) selected_cut_43154

theorem selected_cut_43155 : selected 9 ⟨1179875, by decide⟩
    (prefixPartial 12 339489) = some ⟨12, 2, 0, 1179875, 339489, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_339489_1179875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339489 ⟨1179875, by decide⟩ :=
  accepted_of_selected 12 339489 ⟨1179875, by decide⟩ ⟨12, 2, 0, 1179875, 339489, 3081, 65536⟩
    (by decide) selected_cut_43155

theorem selected_cut_43156 : selected 9 ⟨1179920, by decide⟩
    (prefixPartial 12 339490) = some ⟨12, 2, 0, 1179920, 339490, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_339490_1179920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339490 ⟨1179920, by decide⟩ :=
  accepted_of_selected 12 339490 ⟨1179920, by decide⟩ ⟨12, 2, 0, 1179920, 339490, 2637, 65536⟩
    (by decide) selected_cut_43156

theorem selected_cut_43157 : selected 9 ⟨1179991, by decide⟩
    (prefixPartial 12 339491) = some ⟨12, 2, 0, 1179991, 339491, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_339491_1179991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339491 ⟨1179991, by decide⟩ :=
  accepted_of_selected 12 339491 ⟨1179991, by decide⟩ ⟨12, 2, 0, 1179991, 339491, 3373, 65536⟩
    (by decide) selected_cut_43157

theorem unmarked_context_11_84872_1179992 : frontier 10 ⟨1179992, by decide⟩
    (prefixCache 11 84872) (prefixPartial 11 84872) = false := by
  decide +kernel

theorem node_context_11_84872_1179992 : EJMOriginalGlobalDAGData.nodes 10 ⟨1179992, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1179875, by decide⟩,⟨1179920, by decide⟩,⟨1179991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84872_1179992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84872 ⟨1179992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84872
    ⟨1179992, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1179875, by decide⟩,⟨1179920, by decide⟩,⟨1179991, by decide⟩]) unmarked_context_11_84872_1179992 node_context_11_84872_1179992
  intro a
  fin_cases a
  · exact context_12_339488_1108174
  · exact context_12_339489_1179875
  · exact context_12_339490_1179920
  · exact context_12_339491_1179991

theorem selected_cut_43158 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339492) = some ⟨12, 1, 0, 1108174, 339492, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339492_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339492 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339492 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339492, 1, 65536⟩
    (by decide) selected_cut_43158

theorem selected_cut_43159 : selected 9 ⟨1180045, by decide⟩
    (prefixPartial 12 339493) = some ⟨12, 2, 0, 1180045, 339493, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_339493_1180045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339493 ⟨1180045, by decide⟩ :=
  accepted_of_selected 12 339493 ⟨1180045, by decide⟩ ⟨12, 2, 0, 1180045, 339493, 3029, 65536⟩
    (by decide) selected_cut_43159

theorem selected_cut_43160 : selected 9 ⟨1180096, by decide⟩
    (prefixPartial 12 339494) = some ⟨12, 2, 0, 1180096, 339494, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_339494_1180096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339494 ⟨1180096, by decide⟩ :=
  accepted_of_selected 12 339494 ⟨1180096, by decide⟩ ⟨12, 2, 0, 1180096, 339494, 2693, 65536⟩
    (by decide) selected_cut_43160

theorem selected_cut_43161 : selected 9 ⟨1180160, by decide⟩
    (prefixPartial 12 339495) = some ⟨12, 2, 0, 1180160, 339495, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_339495_1180160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339495 ⟨1180160, by decide⟩ :=
  accepted_of_selected 12 339495 ⟨1180160, by decide⟩ ⟨12, 2, 0, 1180160, 339495, 3445, 65536⟩
    (by decide) selected_cut_43161

theorem unmarked_context_11_84873_1180161 : frontier 10 ⟨1180161, by decide⟩
    (prefixCache 11 84873) (prefixPartial 11 84873) = false := by
  decide +kernel

theorem node_context_11_84873_1180161 : EJMOriginalGlobalDAGData.nodes 10 ⟨1180161, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1180045, by decide⟩,⟨1180096, by decide⟩,⟨1180160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84873_1180161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84873 ⟨1180161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84873
    ⟨1180161, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1180045, by decide⟩,⟨1180096, by decide⟩,⟨1180160, by decide⟩]) unmarked_context_11_84873_1180161 node_context_11_84873_1180161
  intro a
  fin_cases a
  · exact context_12_339492_1108174
  · exact context_12_339493_1180045
  · exact context_12_339494_1180096
  · exact context_12_339495_1180160

theorem selected_cut_43162 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339496) = some ⟨12, 1, 0, 1108174, 339496, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339496_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339496 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339496 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339496, 1, 65536⟩
    (by decide) selected_cut_43162

theorem selected_cut_43163 : selected 9 ⟨1180211, by decide⟩
    (prefixPartial 12 339497) = some ⟨12, 2, 0, 1180211, 339497, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_339497_1180211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339497 ⟨1180211, by decide⟩ :=
  accepted_of_selected 12 339497 ⟨1180211, by decide⟩ ⟨12, 2, 0, 1180211, 339497, 2713, 65536⟩
    (by decide) selected_cut_43163

theorem selected_cut_43164 : selected 9 ⟨1172910, by decide⟩
    (prefixPartial 12 339498) = some ⟨12, 1, 0, 1172910, 339498, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339498_1172910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339498 ⟨1172910, by decide⟩ :=
  accepted_of_selected 12 339498 ⟨1172910, by decide⟩ ⟨12, 1, 0, 1172910, 339498, 1, 65536⟩
    (by decide) selected_cut_43164

theorem selected_cut_43165 : selected 9 ⟨1180305, by decide⟩
    (prefixPartial 12 339499) = some ⟨12, 2, 0, 1180305, 339499, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_339499_1180305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339499 ⟨1180305, by decide⟩ :=
  accepted_of_selected 12 339499 ⟨1180305, by decide⟩ ⟨12, 2, 0, 1180305, 339499, 1657, 65536⟩
    (by decide) selected_cut_43165

theorem unmarked_context_11_84874_1180306 : frontier 10 ⟨1180306, by decide⟩
    (prefixCache 11 84874) (prefixPartial 11 84874) = false := by
  decide +kernel

theorem node_context_11_84874_1180306 : EJMOriginalGlobalDAGData.nodes 10 ⟨1180306, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1180211, by decide⟩,⟨1172910, by decide⟩,⟨1180305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84874_1180306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84874 ⟨1180306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84874
    ⟨1180306, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1180211, by decide⟩,⟨1172910, by decide⟩,⟨1180305, by decide⟩]) unmarked_context_11_84874_1180306 node_context_11_84874_1180306
  intro a
  fin_cases a
  · exact context_12_339496_1108174
  · exact context_12_339497_1180211
  · exact context_12_339498_1172910
  · exact context_12_339499_1180305

theorem selected_cut_43166 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339500) = some ⟨12, 1, 0, 1108174, 339500, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339500_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339500 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339500 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339500, 1, 65536⟩
    (by decide) selected_cut_43166

theorem selected_cut_43167 : selected 9 ⟨1180352, by decide⟩
    (prefixPartial 12 339501) = some ⟨12, 2, 0, 1180352, 339501, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_339501_1180352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339501 ⟨1180352, by decide⟩ :=
  accepted_of_selected 12 339501 ⟨1180352, by decide⟩ ⟨12, 2, 0, 1180352, 339501, 2417, 65536⟩
    (by decide) selected_cut_43167

theorem selected_cut_43168 : selected 9 ⟨1180386, by decide⟩
    (prefixPartial 12 339502) = some ⟨12, 2, 0, 1180386, 339502, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_339502_1180386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339502 ⟨1180386, by decide⟩ :=
  accepted_of_selected 12 339502 ⟨1180386, by decide⟩ ⟨12, 2, 0, 1180386, 339502, 2065, 65536⟩
    (by decide) selected_cut_43168

theorem selected_cut_43169 : selected 9 ⟨634084, by decide⟩
    (prefixPartial 12 339503) = some ⟨12, 1, 0, 634084, 339503, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339503_634084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339503 ⟨634084, by decide⟩ :=
  accepted_of_selected 12 339503 ⟨634084, by decide⟩ ⟨12, 1, 0, 634084, 339503, 1, 65536⟩
    (by decide) selected_cut_43169

theorem unmarked_context_11_84875_1180387 : frontier 10 ⟨1180387, by decide⟩
    (prefixCache 11 84875) (prefixPartial 11 84875) = false := by
  decide +kernel

theorem node_context_11_84875_1180387 : EJMOriginalGlobalDAGData.nodes 10 ⟨1180387, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1180352, by decide⟩,⟨1180386, by decide⟩,⟨634084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84875_1180387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84875 ⟨1180387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84875
    ⟨1180387, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1180352, by decide⟩,⟨1180386, by decide⟩,⟨634084, by decide⟩]) unmarked_context_11_84875_1180387 node_context_11_84875_1180387
  intro a
  fin_cases a
  · exact context_12_339500_1108174
  · exact context_12_339501_1180352
  · exact context_12_339502_1180386
  · exact context_12_339503_634084

theorem unmarked_context_10_21218_1180388 : frontier 11 ⟨1180388, by decide⟩
    (prefixCache 10 21218) (prefixPartial 10 21218) = false := by
  decide +kernel

theorem node_context_10_21218_1180388 : EJMOriginalGlobalDAGData.nodes 11 ⟨1180388, by decide⟩ =
    .split (coordinate 10) (![⟨1179992, by decide⟩,⟨1180161, by decide⟩,⟨1180306, by decide⟩,⟨1180387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21218_1180388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21218 ⟨1180388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21218
    ⟨1180388, by decide⟩ (by decide) (![⟨1179992, by decide⟩,⟨1180161, by decide⟩,⟨1180306, by decide⟩,⟨1180387, by decide⟩]) unmarked_context_10_21218_1180388 node_context_10_21218_1180388
  intro a
  fin_cases a
  · exact context_11_84872_1179992
  · exact context_11_84873_1180161
  · exact context_11_84874_1180306
  · exact context_11_84875_1180387

theorem selected_cut_43170 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339504) = some ⟨12, 1, 0, 1108174, 339504, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339504_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339504 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339504 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339504, 1, 65536⟩
    (by decide) selected_cut_43170

theorem selected_cut_43171 : selected 9 ⟨1180433, by decide⟩
    (prefixPartial 12 339505) = some ⟨12, 2, 0, 1180433, 339505, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_339505_1180433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339505 ⟨1180433, by decide⟩ :=
  accepted_of_selected 12 339505 ⟨1180433, by decide⟩ ⟨12, 2, 0, 1180433, 339505, 2561, 65536⟩
    (by decide) selected_cut_43171

theorem selected_cut_43172 : selected 9 ⟨1180470, by decide⟩
    (prefixPartial 12 339506) = some ⟨12, 2, 0, 1180470, 339506, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_339506_1180470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339506 ⟨1180470, by decide⟩ :=
  accepted_of_selected 12 339506 ⟨1180470, by decide⟩ ⟨12, 2, 0, 1180470, 339506, 2237, 65536⟩
    (by decide) selected_cut_43172

theorem selected_cut_43173 : selected 9 ⟨1180534, by decide⟩
    (prefixPartial 12 339507) = some ⟨12, 2, 0, 1180534, 339507, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_339507_1180534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339507 ⟨1180534, by decide⟩ :=
  accepted_of_selected 12 339507 ⟨1180534, by decide⟩ ⟨12, 2, 0, 1180534, 339507, 2917, 65536⟩
    (by decide) selected_cut_43173

theorem unmarked_context_11_84876_1180535 : frontier 10 ⟨1180535, by decide⟩
    (prefixCache 11 84876) (prefixPartial 11 84876) = false := by
  decide +kernel

theorem node_context_11_84876_1180535 : EJMOriginalGlobalDAGData.nodes 10 ⟨1180535, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1180433, by decide⟩,⟨1180470, by decide⟩,⟨1180534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84876_1180535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84876 ⟨1180535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84876
    ⟨1180535, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1180433, by decide⟩,⟨1180470, by decide⟩,⟨1180534, by decide⟩]) unmarked_context_11_84876_1180535 node_context_11_84876_1180535
  intro a
  fin_cases a
  · exact context_12_339504_1108174
  · exact context_12_339505_1180433
  · exact context_12_339506_1180470
  · exact context_12_339507_1180534

theorem selected_cut_43174 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339508) = some ⟨12, 1, 0, 1108174, 339508, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339508_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339508 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339508 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339508, 1, 65536⟩
    (by decide) selected_cut_43174

theorem selected_cut_43175 : selected 9 ⟨1180573, by decide⟩
    (prefixPartial 12 339509) = some ⟨12, 2, 0, 1180573, 339509, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_339509_1180573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339509 ⟨1180573, by decide⟩ :=
  accepted_of_selected 12 339509 ⟨1180573, by decide⟩ ⟨12, 2, 0, 1180573, 339509, 2337, 65536⟩
    (by decide) selected_cut_43175

theorem selected_cut_43176 : selected 9 ⟨1180615, by decide⟩
    (prefixPartial 12 339510) = some ⟨12, 2, 0, 1180615, 339510, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_339510_1180615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339510 ⟨1180615, by decide⟩ :=
  accepted_of_selected 12 339510 ⟨1180615, by decide⟩ ⟨12, 2, 0, 1180615, 339510, 2149, 65536⟩
    (by decide) selected_cut_43176

theorem selected_cut_43177 : selected 9 ⟨1180669, by decide⟩
    (prefixPartial 12 339511) = some ⟨12, 2, 0, 1180669, 339511, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_339511_1180669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339511 ⟨1180669, by decide⟩ :=
  accepted_of_selected 12 339511 ⟨1180669, by decide⟩ ⟨12, 2, 0, 1180669, 339511, 2741, 65536⟩
    (by decide) selected_cut_43177

theorem unmarked_context_11_84877_1180670 : frontier 10 ⟨1180670, by decide⟩
    (prefixCache 11 84877) (prefixPartial 11 84877) = false := by
  decide +kernel

theorem node_context_11_84877_1180670 : EJMOriginalGlobalDAGData.nodes 10 ⟨1180670, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1180573, by decide⟩,⟨1180615, by decide⟩,⟨1180669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84877_1180670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84877 ⟨1180670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84877
    ⟨1180670, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1180573, by decide⟩,⟨1180615, by decide⟩,⟨1180669, by decide⟩]) unmarked_context_11_84877_1180670 node_context_11_84877_1180670
  intro a
  fin_cases a
  · exact context_12_339508_1108174
  · exact context_12_339509_1180573
  · exact context_12_339510_1180615
  · exact context_12_339511_1180669

theorem selected_cut_43178 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339512) = some ⟨12, 1, 0, 1108174, 339512, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339512_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339512 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339512 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339512, 1, 65536⟩
    (by decide) selected_cut_43178

theorem selected_cut_43179 : selected 9 ⟨1180707, by decide⟩
    (prefixPartial 12 339513) = some ⟨12, 2, 0, 1180707, 339513, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_339513_1180707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339513 ⟨1180707, by decide⟩ :=
  accepted_of_selected 12 339513 ⟨1180707, by decide⟩ ⟨12, 2, 0, 1180707, 339513, 2161, 65536⟩
    (by decide) selected_cut_43179

theorem selected_cut_43180 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 339514) = some ⟨12, 1, 0, 893903, 339514, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339514_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339514 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 339514 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 339514, 1, 65536⟩
    (by decide) selected_cut_43180

theorem selected_cut_43181 : selected 9 ⟨1180752, by decide⟩
    (prefixPartial 12 339515) = some ⟨12, 2, 0, 1180752, 339515, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_339515_1180752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339515 ⟨1180752, by decide⟩ :=
  accepted_of_selected 12 339515 ⟨1180752, by decide⟩ ⟨12, 2, 0, 1180752, 339515, 2457, 65536⟩
    (by decide) selected_cut_43181

theorem unmarked_context_11_84878_1180753 : frontier 10 ⟨1180753, by decide⟩
    (prefixCache 11 84878) (prefixPartial 11 84878) = false := by
  decide +kernel

theorem node_context_11_84878_1180753 : EJMOriginalGlobalDAGData.nodes 10 ⟨1180753, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1180707, by decide⟩,⟨893903, by decide⟩,⟨1180752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84878_1180753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84878 ⟨1180753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84878
    ⟨1180753, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1180707, by decide⟩,⟨893903, by decide⟩,⟨1180752, by decide⟩]) unmarked_context_11_84878_1180753 node_context_11_84878_1180753
  intro a
  fin_cases a
  · exact context_12_339512_1108174
  · exact context_12_339513_1180707
  · exact context_12_339514_893903
  · exact context_12_339515_1180752

theorem selected_cut_43182 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 84879) = some ⟨11, 1, 0, 977886, 84879, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84879_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84879 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 84879 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 84879, 1, 262144⟩
    (by decide) selected_cut_43182

theorem unmarked_context_10_21219_1180754 : frontier 11 ⟨1180754, by decide⟩
    (prefixCache 10 21219) (prefixPartial 10 21219) = false := by
  decide +kernel

theorem node_context_10_21219_1180754 : EJMOriginalGlobalDAGData.nodes 11 ⟨1180754, by decide⟩ =
    .split (coordinate 10) (![⟨1180535, by decide⟩,⟨1180670, by decide⟩,⟨1180753, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21219_1180754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21219 ⟨1180754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21219
    ⟨1180754, by decide⟩ (by decide) (![⟨1180535, by decide⟩,⟨1180670, by decide⟩,⟨1180753, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_21219_1180754 node_context_10_21219_1180754
  intro a
  fin_cases a
  · exact context_11_84876_1180535
  · exact context_11_84877_1180670
  · exact context_11_84878_1180753
  · exact context_11_84879_977886

theorem unmarked_context_9_5304_1180755 : frontier 12 ⟨1180755, by decide⟩
    (prefixCache 9 5304) (prefixPartial 9 5304) = false := by
  decide +kernel

theorem node_context_9_5304_1180755 : EJMOriginalGlobalDAGData.nodes 12 ⟨1180755, by decide⟩ =
    .split (coordinate 9) (![⟨1179261, by decide⟩,⟨1179816, by decide⟩,⟨1180388, by decide⟩,⟨1180754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5304_1180755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5304 ⟨1180755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5304
    ⟨1180755, by decide⟩ (by decide) (![⟨1179261, by decide⟩,⟨1179816, by decide⟩,⟨1180388, by decide⟩,⟨1180754, by decide⟩]) unmarked_context_9_5304_1180755 node_context_9_5304_1180755
  intro a
  fin_cases a
  · exact context_10_21216_1179261
  · exact context_10_21217_1179816
  · exact context_10_21218_1180388
  · exact context_10_21219_1180754

theorem selected_cut_43183 : selected 9 ⟨1173556, by decide⟩
    (prefixPartial 12 339520) = some ⟨12, 1, 0, 1173556, 339520, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339520_1173556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339520 ⟨1173556, by decide⟩ :=
  accepted_of_selected 12 339520 ⟨1173556, by decide⟩ ⟨12, 1, 0, 1173556, 339520, 1, 65536⟩
    (by decide) selected_cut_43183

theorem selected_cut_43184 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 339521) = some ⟨12, 1, 0, 170504, 339521, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339521_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339521 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 339521 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 339521, 1, 65536⟩
    (by decide) selected_cut_43184

theorem selected_cut_43185 : selected 9 ⟨1180813, by decide⟩
    (prefixPartial 12 339522) = some ⟨12, 2, 0, 1180813, 339522, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_339522_1180813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339522 ⟨1180813, by decide⟩ :=
  accepted_of_selected 12 339522 ⟨1180813, by decide⟩ ⟨12, 2, 0, 1180813, 339522, 2449, 65536⟩
    (by decide) selected_cut_43185

theorem selected_cut_43186 : selected 9 ⟨1180865, by decide⟩
    (prefixPartial 12 339523) = some ⟨12, 2, 0, 1180865, 339523, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_339523_1180865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339523 ⟨1180865, by decide⟩ :=
  accepted_of_selected 12 339523 ⟨1180865, by decide⟩ ⟨12, 2, 0, 1180865, 339523, 2637, 65536⟩
    (by decide) selected_cut_43186

theorem unmarked_context_11_84880_1180866 : frontier 10 ⟨1180866, by decide⟩
    (prefixCache 11 84880) (prefixPartial 11 84880) = false := by
  decide +kernel

theorem node_context_11_84880_1180866 : EJMOriginalGlobalDAGData.nodes 10 ⟨1180866, by decide⟩ =
    .split (coordinate 11) (![⟨1173556, by decide⟩,⟨170504, by decide⟩,⟨1180813, by decide⟩,⟨1180865, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84880_1180866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84880 ⟨1180866, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84880
    ⟨1180866, by decide⟩ (by decide) (![⟨1173556, by decide⟩,⟨170504, by decide⟩,⟨1180813, by decide⟩,⟨1180865, by decide⟩]) unmarked_context_11_84880_1180866 node_context_11_84880_1180866
  intro a
  fin_cases a
  · exact context_12_339520_1173556
  · exact context_12_339521_170504
  · exact context_12_339522_1180813
  · exact context_12_339523_1180865

theorem selected_cut_43187 : selected 9 ⟨1180894, by decide⟩
    (prefixPartial 12 339524) = some ⟨12, 2, 0, 1180894, 339524, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_339524_1180894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339524 ⟨1180894, by decide⟩ :=
  accepted_of_selected 12 339524 ⟨1180894, by decide⟩ ⟨12, 2, 0, 1180894, 339524, 2037, 65536⟩
    (by decide) selected_cut_43187

theorem selected_cut_43188 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 339525) = some ⟨12, 1, 0, 170504, 339525, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339525_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339525 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 339525 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 339525, 1, 65536⟩
    (by decide) selected_cut_43188

theorem selected_cut_43189 : selected 9 ⟨1180934, by decide⟩
    (prefixPartial 12 339526) = some ⟨12, 2, 0, 1180934, 339526, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_339526_1180934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339526 ⟨1180934, by decide⟩ :=
  accepted_of_selected 12 339526 ⟨1180934, by decide⟩ ⟨12, 2, 0, 1180934, 339526, 2205, 65536⟩
    (by decide) selected_cut_43189

theorem selected_cut_43190 : selected 9 ⟨1180978, by decide⟩
    (prefixPartial 12 339527) = some ⟨12, 2, 0, 1180978, 339527, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_339527_1180978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339527 ⟨1180978, by decide⟩ :=
  accepted_of_selected 12 339527 ⟨1180978, by decide⟩ ⟨12, 2, 0, 1180978, 339527, 2393, 65536⟩
    (by decide) selected_cut_43190

theorem unmarked_context_11_84881_1180979 : frontier 10 ⟨1180979, by decide⟩
    (prefixCache 11 84881) (prefixPartial 11 84881) = false := by
  decide +kernel

theorem node_context_11_84881_1180979 : EJMOriginalGlobalDAGData.nodes 10 ⟨1180979, by decide⟩ =
    .split (coordinate 11) (![⟨1180894, by decide⟩,⟨170504, by decide⟩,⟨1180934, by decide⟩,⟨1180978, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84881_1180979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84881 ⟨1180979, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84881
    ⟨1180979, by decide⟩ (by decide) (![⟨1180894, by decide⟩,⟨170504, by decide⟩,⟨1180934, by decide⟩,⟨1180978, by decide⟩]) unmarked_context_11_84881_1180979 node_context_11_84881_1180979
  intro a
  fin_cases a
  · exact context_12_339524_1180894
  · exact context_12_339525_170504
  · exact context_12_339526_1180934
  · exact context_12_339527_1180978

theorem selected_cut_43191 : selected 9 ⟨1181007, by decide⟩
    (prefixPartial 12 339528) = some ⟨12, 2, 0, 1181007, 339528, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_339528_1181007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339528 ⟨1181007, by decide⟩ :=
  accepted_of_selected 12 339528 ⟨1181007, by decide⟩ ⟨12, 2, 0, 1181007, 339528, 1817, 65536⟩
    (by decide) selected_cut_43191

theorem selected_cut_43192 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 339529) = some ⟨12, 1, 0, 126371, 339529, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339529_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339529 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 339529 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 339529, 1, 65536⟩
    (by decide) selected_cut_43192

theorem selected_cut_43193 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 339530) = some ⟨12, 1, 0, 893903, 339530, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339530_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339530 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 339530 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 339530, 1, 65536⟩
    (by decide) selected_cut_43193

theorem selected_cut_43194 : selected 9 ⟨1181041, by decide⟩
    (prefixPartial 12 339531) = some ⟨12, 2, 0, 1181041, 339531, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_339531_1181041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339531 ⟨1181041, by decide⟩ :=
  accepted_of_selected 12 339531 ⟨1181041, by decide⟩ ⟨12, 2, 0, 1181041, 339531, 2305, 65536⟩
    (by decide) selected_cut_43194

theorem unmarked_context_11_84882_1181042 : frontier 10 ⟨1181042, by decide⟩
    (prefixCache 11 84882) (prefixPartial 11 84882) = false := by
  decide +kernel

theorem node_context_11_84882_1181042 : EJMOriginalGlobalDAGData.nodes 10 ⟨1181042, by decide⟩ =
    .split (coordinate 11) (![⟨1181007, by decide⟩,⟨126371, by decide⟩,⟨893903, by decide⟩,⟨1181041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84882_1181042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84882 ⟨1181042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84882
    ⟨1181042, by decide⟩ (by decide) (![⟨1181007, by decide⟩,⟨126371, by decide⟩,⟨893903, by decide⟩,⟨1181041, by decide⟩]) unmarked_context_11_84882_1181042 node_context_11_84882_1181042
  intro a
  fin_cases a
  · exact context_12_339528_1181007
  · exact context_12_339529_126371
  · exact context_12_339530_893903
  · exact context_12_339531_1181041

theorem selected_cut_43195 : selected 9 ⟨1181065, by decide⟩
    (prefixPartial 12 339532) = some ⟨12, 2, 0, 1181065, 339532, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_339532_1181065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339532 ⟨1181065, by decide⟩ :=
  accepted_of_selected 12 339532 ⟨1181065, by decide⟩ ⟨12, 2, 0, 1181065, 339532, 1601, 65536⟩
    (by decide) selected_cut_43195

theorem selected_cut_43196 : selected 9 ⟨1181074, by decide⟩
    (prefixPartial 12 339533) = some ⟨12, 2, 0, 1181074, 339533, 689, 65536⟩ := by
  decide +kernel

theorem context_12_339533_1181074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339533 ⟨1181074, by decide⟩ :=
  accepted_of_selected 12 339533 ⟨1181074, by decide⟩ ⟨12, 2, 0, 1181074, 339533, 689, 65536⟩
    (by decide) selected_cut_43196

theorem selected_cut_43197 : selected 9 ⟨1181106, by decide⟩
    (prefixPartial 12 339534) = some ⟨12, 2, 0, 1181106, 339534, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_339534_1181106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339534 ⟨1181106, by decide⟩ :=
  accepted_of_selected 12 339534 ⟨1181106, by decide⟩ ⟨12, 2, 0, 1181106, 339534, 1777, 65536⟩
    (by decide) selected_cut_43197

theorem selected_cut_43198 : selected 9 ⟨1181134, by decide⟩
    (prefixPartial 12 339535) = some ⟨12, 2, 0, 1181134, 339535, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_339535_1181134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339535 ⟨1181134, by decide⟩ :=
  accepted_of_selected 12 339535 ⟨1181134, by decide⟩ ⟨12, 2, 0, 1181134, 339535, 1833, 65536⟩
    (by decide) selected_cut_43198

theorem unmarked_context_11_84883_1181135 : frontier 10 ⟨1181135, by decide⟩
    (prefixCache 11 84883) (prefixPartial 11 84883) = false := by
  decide +kernel

theorem node_context_11_84883_1181135 : EJMOriginalGlobalDAGData.nodes 10 ⟨1181135, by decide⟩ =
    .split (coordinate 11) (![⟨1181065, by decide⟩,⟨1181074, by decide⟩,⟨1181106, by decide⟩,⟨1181134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84883_1181135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84883 ⟨1181135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84883
    ⟨1181135, by decide⟩ (by decide) (![⟨1181065, by decide⟩,⟨1181074, by decide⟩,⟨1181106, by decide⟩,⟨1181134, by decide⟩]) unmarked_context_11_84883_1181135 node_context_11_84883_1181135
  intro a
  fin_cases a
  · exact context_12_339532_1181065
  · exact context_12_339533_1181074
  · exact context_12_339534_1181106
  · exact context_12_339535_1181134

theorem unmarked_context_10_21220_1181136 : frontier 11 ⟨1181136, by decide⟩
    (prefixCache 10 21220) (prefixPartial 10 21220) = false := by
  decide +kernel

theorem node_context_10_21220_1181136 : EJMOriginalGlobalDAGData.nodes 11 ⟨1181136, by decide⟩ =
    .split (coordinate 10) (![⟨1180866, by decide⟩,⟨1180979, by decide⟩,⟨1181042, by decide⟩,⟨1181135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21220_1181136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21220 ⟨1181136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21220
    ⟨1181136, by decide⟩ (by decide) (![⟨1180866, by decide⟩,⟨1180979, by decide⟩,⟨1181042, by decide⟩,⟨1181135, by decide⟩]) unmarked_context_10_21220_1181136 node_context_10_21220_1181136
  intro a
  fin_cases a
  · exact context_11_84880_1180866
  · exact context_11_84881_1180979
  · exact context_11_84882_1181042
  · exact context_11_84883_1181135

theorem selected_cut_43199 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21221) = some ⟨10, 1, 0, 893098, 21221, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21221_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21221 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21221 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21221, 1, 1048576⟩
    (by decide) selected_cut_43199

theorem selected_cut_43200 : selected 9 ⟨1181170, by decide⟩
    (prefixPartial 12 339552) = some ⟨12, 2, 0, 1181170, 339552, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_339552_1181170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339552 ⟨1181170, by decide⟩ :=
  accepted_of_selected 12 339552 ⟨1181170, by decide⟩ ⟨12, 2, 0, 1181170, 339552, 1873, 65536⟩
    (by decide) selected_cut_43200

theorem selected_cut_43201 : selected 9 ⟨1181198, by decide⟩
    (prefixPartial 12 339553) = some ⟨12, 2, 0, 1181198, 339553, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_339553_1181198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339553 ⟨1181198, by decide⟩ :=
  accepted_of_selected 12 339553 ⟨1181198, by decide⟩ ⟨12, 2, 0, 1181198, 339553, 1881, 65536⟩
    (by decide) selected_cut_43201

theorem selected_cut_43202 : selected 9 ⟨1181233, by decide⟩
    (prefixPartial 12 339554) = some ⟨12, 2, 0, 1181233, 339554, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_339554_1181233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339554 ⟨1181233, by decide⟩ :=
  accepted_of_selected 12 339554 ⟨1181233, by decide⟩ ⟨12, 2, 0, 1181233, 339554, 1769, 65536⟩
    (by decide) selected_cut_43202

theorem selected_cut_43203 : selected 9 ⟨1181273, by decide⟩
    (prefixPartial 12 339555) = some ⟨12, 2, 0, 1181273, 339555, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_339555_1181273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339555 ⟨1181273, by decide⟩ :=
  accepted_of_selected 12 339555 ⟨1181273, by decide⟩ ⟨12, 2, 0, 1181273, 339555, 2157, 65536⟩
    (by decide) selected_cut_43203

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
