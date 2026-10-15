/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover500
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_48100 : selected 11 ⟨1347939, by decide⟩
    (prefixPartial 10 23455) = some ⟨10, 2, 0, 1347939, 23455, 193, 1048576⟩ := by
  decide +kernel

theorem context_10_23455_1347939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23455 ⟨1347939, by decide⟩ :=
  accepted_of_selected 10 23455 ⟨1347939, by decide⟩ ⟨10, 2, 0, 1347939, 23455, 193, 1048576⟩
    (by decide) selected_cut_48100

theorem unmarked_context_9_5863_1347940 : frontier 12 ⟨1347940, by decide⟩
    (prefixCache 9 5863) (prefixPartial 9 5863) = false := by
  decide +kernel

theorem node_context_9_5863_1347940 : EJMOriginalGlobalDAGData.nodes 12 ⟨1347940, by decide⟩ =
    .split (coordinate 9) (![⟨1347837, by decide⟩,⟨1347899, by decide⟩,⟨1347931, by decide⟩,⟨1347939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5863_1347940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5863 ⟨1347940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5863
    ⟨1347940, by decide⟩ (by decide) (![⟨1347837, by decide⟩,⟨1347899, by decide⟩,⟨1347931, by decide⟩,⟨1347939, by decide⟩]) unmarked_context_9_5863_1347940 node_context_9_5863_1347940
  intro a
  fin_cases a
  · exact context_10_23452_1347837
  · exact context_10_23453_1347899
  · exact context_10_23454_1347931
  · exact context_10_23455_1347939

theorem unmarked_context_8_1465_1347941 : frontier 13 ⟨1347941, by decide⟩
    (prefixCache 8 1465) (prefixPartial 8 1465) = false := by
  decide +kernel

theorem node_context_8_1465_1347941 : EJMOriginalGlobalDAGData.nodes 13 ⟨1347941, by decide⟩ =
    .split (coordinate 8) (![⟨1346767, by decide⟩,⟨1347343, by decide⟩,⟨1347717, by decide⟩,⟨1347940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1465_1347941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1465 ⟨1347941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1465
    ⟨1347941, by decide⟩ (by decide) (![⟨1346767, by decide⟩,⟨1347343, by decide⟩,⟨1347717, by decide⟩,⟨1347940, by decide⟩]) unmarked_context_8_1465_1347941 node_context_8_1465_1347941
  intro a
  fin_cases a
  · exact context_9_5860_1346767
  · exact context_9_5861_1347343
  · exact context_9_5862_1347717
  · exact context_9_5863_1347940

theorem selected_cut_48101 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93824) = some ⟨11, 1, 0, 434745, 93824, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93824_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93824 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93824 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93824, 1, 262144⟩
    (by decide) selected_cut_48101

theorem selected_cut_48102 : selected 10 ⟨1348016, by decide⟩
    (prefixPartial 11 93825) = some ⟨11, 2, 0, 1348016, 93825, 2105, 262144⟩ := by
  decide +kernel

theorem context_11_93825_1348016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93825 ⟨1348016, by decide⟩ :=
  accepted_of_selected 11 93825 ⟨1348016, by decide⟩ ⟨11, 2, 0, 1348016, 93825, 2105, 262144⟩
    (by decide) selected_cut_48102

theorem selected_cut_48103 : selected 10 ⟨1348081, by decide⟩
    (prefixPartial 11 93826) = some ⟨11, 2, 0, 1348081, 93826, 2813, 262144⟩ := by
  decide +kernel

theorem context_11_93826_1348081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93826 ⟨1348081, by decide⟩ :=
  accepted_of_selected 11 93826 ⟨1348081, by decide⟩ ⟨11, 2, 0, 1348081, 93826, 2813, 262144⟩
    (by decide) selected_cut_48103

theorem selected_cut_48104 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 375308) = some ⟨12, 1, 0, 448748, 375308, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375308_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375308 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 375308 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 375308, 1, 65536⟩
    (by decide) selected_cut_48104

theorem selected_cut_48105 : selected 9 ⟨1348193, by decide⟩
    (prefixPartial 12 375309) = some ⟨12, 2, 0, 1348193, 375309, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_375309_1348193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375309 ⟨1348193, by decide⟩ :=
  accepted_of_selected 12 375309 ⟨1348193, by decide⟩ ⟨12, 2, 0, 1348193, 375309, 4001, 65536⟩
    (by decide) selected_cut_48105

theorem selected_cut_48106 : selected 9 ⟨1348273, by decide⟩
    (prefixPartial 12 375310) = some ⟨12, 2, 0, 1348273, 375310, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_375310_1348273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375310 ⟨1348273, by decide⟩ :=
  accepted_of_selected 12 375310 ⟨1348273, by decide⟩ ⟨12, 2, 0, 1348273, 375310, 3405, 65536⟩
    (by decide) selected_cut_48106

theorem selected_cut_48107 : selected 9 ⟨1348338, by decide⟩
    (prefixPartial 12 375311) = some ⟨12, 2, 0, 1348338, 375311, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_375311_1348338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375311 ⟨1348338, by decide⟩ :=
  accepted_of_selected 12 375311 ⟨1348338, by decide⟩ ⟨12, 2, 0, 1348338, 375311, 3169, 65536⟩
    (by decide) selected_cut_48107

theorem unmarked_context_11_93827_1348339 : frontier 10 ⟨1348339, by decide⟩
    (prefixCache 11 93827) (prefixPartial 11 93827) = false := by
  decide +kernel

theorem node_context_11_93827_1348339 : EJMOriginalGlobalDAGData.nodes 10 ⟨1348339, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1348193, by decide⟩,⟨1348273, by decide⟩,⟨1348338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93827_1348339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93827 ⟨1348339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93827
    ⟨1348339, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1348193, by decide⟩,⟨1348273, by decide⟩,⟨1348338, by decide⟩]) unmarked_context_11_93827_1348339 node_context_11_93827_1348339
  intro a
  fin_cases a
  · exact context_12_375308_448748
  · exact context_12_375309_1348193
  · exact context_12_375310_1348273
  · exact context_12_375311_1348338

theorem unmarked_context_10_23456_1348340 : frontier 11 ⟨1348340, by decide⟩
    (prefixCache 10 23456) (prefixPartial 10 23456) = false := by
  decide +kernel

theorem node_context_10_23456_1348340 : EJMOriginalGlobalDAGData.nodes 11 ⟨1348340, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1348016, by decide⟩,⟨1348081, by decide⟩,⟨1348339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23456_1348340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23456 ⟨1348340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23456
    ⟨1348340, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1348016, by decide⟩,⟨1348081, by decide⟩,⟨1348339, by decide⟩]) unmarked_context_10_23456_1348340 node_context_10_23456_1348340
  intro a
  fin_cases a
  · exact context_11_93824_434745
  · exact context_11_93825_1348016
  · exact context_11_93826_1348081
  · exact context_11_93827_1348339

theorem selected_cut_48108 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 375312) = some ⟨12, 1, 0, 1255011, 375312, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375312_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375312 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 375312 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 375312, 1, 65536⟩
    (by decide) selected_cut_48108

theorem selected_cut_48109 : selected 9 ⟨1348412, by decide⟩
    (prefixPartial 12 375313) = some ⟨12, 2, 0, 1348412, 375313, 3281, 65536⟩ := by
  decide +kernel

theorem context_12_375313_1348412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375313 ⟨1348412, by decide⟩ :=
  accepted_of_selected 12 375313 ⟨1348412, by decide⟩ ⟨12, 2, 0, 1348412, 375313, 3281, 65536⟩
    (by decide) selected_cut_48109

theorem selected_cut_48110 : selected 9 ⟨1348473, by decide⟩
    (prefixPartial 12 375314) = some ⟨12, 2, 0, 1348473, 375314, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_375314_1348473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375314 ⟨1348473, by decide⟩ :=
  accepted_of_selected 12 375314 ⟨1348473, by decide⟩ ⟨12, 2, 0, 1348473, 375314, 2961, 65536⟩
    (by decide) selected_cut_48110

theorem selected_cut_48111 : selected 9 ⟨1348547, by decide⟩
    (prefixPartial 12 375315) = some ⟨12, 2, 0, 1348547, 375315, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_375315_1348547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375315 ⟨1348547, by decide⟩ :=
  accepted_of_selected 12 375315 ⟨1348547, by decide⟩ ⟨12, 2, 0, 1348547, 375315, 3321, 65536⟩
    (by decide) selected_cut_48111

theorem unmarked_context_11_93828_1348548 : frontier 10 ⟨1348548, by decide⟩
    (prefixCache 11 93828) (prefixPartial 11 93828) = false := by
  decide +kernel

theorem node_context_11_93828_1348548 : EJMOriginalGlobalDAGData.nodes 10 ⟨1348548, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1348412, by decide⟩,⟨1348473, by decide⟩,⟨1348547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93828_1348548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93828 ⟨1348548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93828
    ⟨1348548, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1348412, by decide⟩,⟨1348473, by decide⟩,⟨1348547, by decide⟩]) unmarked_context_11_93828_1348548 node_context_11_93828_1348548
  intro a
  fin_cases a
  · exact context_12_375312_1255011
  · exact context_12_375313_1348412
  · exact context_12_375314_1348473
  · exact context_12_375315_1348547

theorem selected_cut_48112 : selected 9 ⟨1348626, by decide⟩
    (prefixPartial 12 375316) = some ⟨12, 2, 0, 1348626, 375316, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_375316_1348626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375316 ⟨1348626, by decide⟩ :=
  accepted_of_selected 12 375316 ⟨1348626, by decide⟩ ⟨12, 2, 0, 1348626, 375316, 3041, 65536⟩
    (by decide) selected_cut_48112

theorem selected_cut_48113 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 375317) = some ⟨12, 1, 0, 1118965, 375317, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375317_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375317 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 375317 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 375317, 1, 65536⟩
    (by decide) selected_cut_48113

theorem selected_cut_48114 : selected 9 ⟨692793, by decide⟩
    (prefixPartial 12 375318) = some ⟨12, 1, 0, 692793, 375318, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375318_692793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375318 ⟨692793, by decide⟩ :=
  accepted_of_selected 12 375318 ⟨692793, by decide⟩ ⟨12, 1, 0, 692793, 375318, 1, 65536⟩
    (by decide) selected_cut_48114

theorem selected_cut_48115 : selected 9 ⟨1348707, by decide⟩
    (prefixPartial 12 375319) = some ⟨12, 2, 0, 1348707, 375319, 3305, 65536⟩ := by
  decide +kernel

theorem context_12_375319_1348707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375319 ⟨1348707, by decide⟩ :=
  accepted_of_selected 12 375319 ⟨1348707, by decide⟩ ⟨12, 2, 0, 1348707, 375319, 3305, 65536⟩
    (by decide) selected_cut_48115

theorem unmarked_context_11_93829_1348708 : frontier 10 ⟨1348708, by decide⟩
    (prefixCache 11 93829) (prefixPartial 11 93829) = false := by
  decide +kernel

theorem node_context_11_93829_1348708 : EJMOriginalGlobalDAGData.nodes 10 ⟨1348708, by decide⟩ =
    .split (coordinate 11) (![⟨1348626, by decide⟩,⟨1118965, by decide⟩,⟨692793, by decide⟩,⟨1348707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93829_1348708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93829 ⟨1348708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93829
    ⟨1348708, by decide⟩ (by decide) (![⟨1348626, by decide⟩,⟨1118965, by decide⟩,⟨692793, by decide⟩,⟨1348707, by decide⟩]) unmarked_context_11_93829_1348708 node_context_11_93829_1348708
  intro a
  fin_cases a
  · exact context_12_375316_1348626
  · exact context_12_375317_1118965
  · exact context_12_375318_692793
  · exact context_12_375319_1348707

theorem selected_cut_48116 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 375320) = some ⟨12, 1, 0, 994572, 375320, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375320_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375320 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 375320 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 375320, 1, 65536⟩
    (by decide) selected_cut_48116

theorem selected_cut_48117 : selected 9 ⟨1348760, by decide⟩
    (prefixPartial 12 375321) = some ⟨12, 2, 0, 1348760, 375321, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_375321_1348760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375321 ⟨1348760, by decide⟩ :=
  accepted_of_selected 12 375321 ⟨1348760, by decide⟩ ⟨12, 2, 0, 1348760, 375321, 2589, 65536⟩
    (by decide) selected_cut_48117

theorem selected_cut_48118 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 375322) = some ⟨12, 1, 0, 893903, 375322, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375322_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375322 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 375322 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 375322, 1, 65536⟩
    (by decide) selected_cut_48118

theorem selected_cut_48119 : selected 9 ⟨1348814, by decide⟩
    (prefixPartial 12 375323) = some ⟨12, 2, 0, 1348814, 375323, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_375323_1348814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375323 ⟨1348814, by decide⟩ :=
  accepted_of_selected 12 375323 ⟨1348814, by decide⟩ ⟨12, 2, 0, 1348814, 375323, 2629, 65536⟩
    (by decide) selected_cut_48119

theorem unmarked_context_11_93830_1348815 : frontier 10 ⟨1348815, by decide⟩
    (prefixCache 11 93830) (prefixPartial 11 93830) = false := by
  decide +kernel

theorem node_context_11_93830_1348815 : EJMOriginalGlobalDAGData.nodes 10 ⟨1348815, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1348760, by decide⟩,⟨893903, by decide⟩,⟨1348814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93830_1348815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93830 ⟨1348815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93830
    ⟨1348815, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1348760, by decide⟩,⟨893903, by decide⟩,⟨1348814, by decide⟩]) unmarked_context_11_93830_1348815 node_context_11_93830_1348815
  intro a
  fin_cases a
  · exact context_12_375320_994572
  · exact context_12_375321_1348760
  · exact context_12_375322_893903
  · exact context_12_375323_1348814

theorem selected_cut_48120 : selected 9 ⟨1348874, by decide⟩
    (prefixPartial 12 375324) = some ⟨12, 2, 0, 1348874, 375324, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_375324_1348874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375324 ⟨1348874, by decide⟩ :=
  accepted_of_selected 12 375324 ⟨1348874, by decide⟩ ⟨12, 2, 0, 1348874, 375324, 2861, 65536⟩
    (by decide) selected_cut_48120

theorem selected_cut_48121 : selected 9 ⟨1348942, by decide⟩
    (prefixPartial 12 375325) = some ⟨12, 2, 0, 1348942, 375325, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_375325_1348942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375325 ⟨1348942, by decide⟩ :=
  accepted_of_selected 12 375325 ⟨1348942, by decide⟩ ⟨12, 2, 0, 1348942, 375325, 3097, 65536⟩
    (by decide) selected_cut_48121

theorem selected_cut_48122 : selected 9 ⟨1348991, by decide⟩
    (prefixPartial 12 375326) = some ⟨12, 2, 0, 1348991, 375326, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_375326_1348991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375326 ⟨1348991, by decide⟩ :=
  accepted_of_selected 12 375326 ⟨1348991, by decide⟩ ⟨12, 2, 0, 1348991, 375326, 2653, 65536⟩
    (by decide) selected_cut_48122

theorem selected_cut_48123 : selected 9 ⟨1349046, by decide⟩
    (prefixPartial 12 375327) = some ⟨12, 2, 0, 1349046, 375327, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_375327_1349046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375327 ⟨1349046, by decide⟩ :=
  accepted_of_selected 12 375327 ⟨1349046, by decide⟩ ⟨12, 2, 0, 1349046, 375327, 2769, 65536⟩
    (by decide) selected_cut_48123

theorem unmarked_context_11_93831_1349047 : frontier 10 ⟨1349047, by decide⟩
    (prefixCache 11 93831) (prefixPartial 11 93831) = false := by
  decide +kernel

theorem node_context_11_93831_1349047 : EJMOriginalGlobalDAGData.nodes 10 ⟨1349047, by decide⟩ =
    .split (coordinate 11) (![⟨1348874, by decide⟩,⟨1348942, by decide⟩,⟨1348991, by decide⟩,⟨1349046, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93831_1349047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93831 ⟨1349047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93831
    ⟨1349047, by decide⟩ (by decide) (![⟨1348874, by decide⟩,⟨1348942, by decide⟩,⟨1348991, by decide⟩,⟨1349046, by decide⟩]) unmarked_context_11_93831_1349047 node_context_11_93831_1349047
  intro a
  fin_cases a
  · exact context_12_375324_1348874
  · exact context_12_375325_1348942
  · exact context_12_375326_1348991
  · exact context_12_375327_1349046

theorem unmarked_context_10_23457_1349048 : frontier 11 ⟨1349048, by decide⟩
    (prefixCache 10 23457) (prefixPartial 10 23457) = false := by
  decide +kernel

theorem node_context_10_23457_1349048 : EJMOriginalGlobalDAGData.nodes 11 ⟨1349048, by decide⟩ =
    .split (coordinate 10) (![⟨1348548, by decide⟩,⟨1348708, by decide⟩,⟨1348815, by decide⟩,⟨1349047, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23457_1349048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23457 ⟨1349048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23457
    ⟨1349048, by decide⟩ (by decide) (![⟨1348548, by decide⟩,⟨1348708, by decide⟩,⟨1348815, by decide⟩,⟨1349047, by decide⟩]) unmarked_context_10_23457_1349048 node_context_10_23457_1349048
  intro a
  fin_cases a
  · exact context_11_93828_1348548
  · exact context_11_93829_1348708
  · exact context_11_93830_1348815
  · exact context_11_93831_1349047

theorem selected_cut_48124 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 375328) = some ⟨12, 1, 0, 435790, 375328, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375328_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375328 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 375328 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 375328, 1, 65536⟩
    (by decide) selected_cut_48124

theorem selected_cut_48125 : selected 9 ⟨1349104, by decide⟩
    (prefixPartial 12 375329) = some ⟨12, 2, 0, 1349104, 375329, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_375329_1349104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375329 ⟨1349104, by decide⟩ :=
  accepted_of_selected 12 375329 ⟨1349104, by decide⟩ ⟨12, 2, 0, 1349104, 375329, 2373, 65536⟩
    (by decide) selected_cut_48125

theorem selected_cut_48126 : selected 9 ⟨1349138, by decide⟩
    (prefixPartial 12 375330) = some ⟨12, 2, 0, 1349138, 375330, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_375330_1349138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375330 ⟨1349138, by decide⟩ :=
  accepted_of_selected 12 375330 ⟨1349138, by decide⟩ ⟨12, 2, 0, 1349138, 375330, 1965, 65536⟩
    (by decide) selected_cut_48126

theorem selected_cut_48127 : selected 9 ⟨1349179, by decide⟩
    (prefixPartial 12 375331) = some ⟨12, 2, 0, 1349179, 375331, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_375331_1349179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375331 ⟨1349179, by decide⟩ :=
  accepted_of_selected 12 375331 ⟨1349179, by decide⟩ ⟨12, 2, 0, 1349179, 375331, 2113, 65536⟩
    (by decide) selected_cut_48127

theorem unmarked_context_11_93832_1349180 : frontier 10 ⟨1349180, by decide⟩
    (prefixCache 11 93832) (prefixPartial 11 93832) = false := by
  decide +kernel

theorem node_context_11_93832_1349180 : EJMOriginalGlobalDAGData.nodes 10 ⟨1349180, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1349104, by decide⟩,⟨1349138, by decide⟩,⟨1349179, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93832_1349180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93832 ⟨1349180, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93832
    ⟨1349180, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1349104, by decide⟩,⟨1349138, by decide⟩,⟨1349179, by decide⟩]) unmarked_context_11_93832_1349180 node_context_11_93832_1349180
  intro a
  fin_cases a
  · exact context_12_375328_435790
  · exact context_12_375329_1349104
  · exact context_12_375330_1349138
  · exact context_12_375331_1349179

theorem selected_cut_48128 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 375332) = some ⟨12, 1, 0, 435790, 375332, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375332_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375332 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 375332 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 375332, 1, 65536⟩
    (by decide) selected_cut_48128

theorem selected_cut_48129 : selected 9 ⟨688903, by decide⟩
    (prefixPartial 12 375333) = some ⟨12, 1, 0, 688903, 375333, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375333_688903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375333 ⟨688903, by decide⟩ :=
  accepted_of_selected 12 375333 ⟨688903, by decide⟩ ⟨12, 1, 0, 688903, 375333, 1, 65536⟩
    (by decide) selected_cut_48129

theorem selected_cut_48130 : selected 9 ⟨1349231, by decide⟩
    (prefixPartial 12 375334) = some ⟨12, 2, 0, 1349231, 375334, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_375334_1349231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375334 ⟨1349231, by decide⟩ :=
  accepted_of_selected 12 375334 ⟨1349231, by decide⟩ ⟨12, 2, 0, 1349231, 375334, 2257, 65536⟩
    (by decide) selected_cut_48130

theorem selected_cut_48131 : selected 9 ⟨1349294, by decide⟩
    (prefixPartial 12 375335) = some ⟨12, 2, 0, 1349294, 375335, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_375335_1349294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375335 ⟨1349294, by decide⟩ :=
  accepted_of_selected 12 375335 ⟨1349294, by decide⟩ ⟨12, 2, 0, 1349294, 375335, 2345, 65536⟩
    (by decide) selected_cut_48131

theorem unmarked_context_11_93833_1349295 : frontier 10 ⟨1349295, by decide⟩
    (prefixCache 11 93833) (prefixPartial 11 93833) = false := by
  decide +kernel

theorem node_context_11_93833_1349295 : EJMOriginalGlobalDAGData.nodes 10 ⟨1349295, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨688903, by decide⟩,⟨1349231, by decide⟩,⟨1349294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93833_1349295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93833 ⟨1349295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93833
    ⟨1349295, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨688903, by decide⟩,⟨1349231, by decide⟩,⟨1349294, by decide⟩]) unmarked_context_11_93833_1349295 node_context_11_93833_1349295
  intro a
  fin_cases a
  · exact context_12_375332_435790
  · exact context_12_375333_688903
  · exact context_12_375334_1349231
  · exact context_12_375335_1349294

theorem selected_cut_48132 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 93834) = some ⟨11, 1, 0, 900587, 93834, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93834_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93834 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 93834 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 93834, 1, 262144⟩
    (by decide) selected_cut_48132

theorem selected_cut_48133 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 375340) = some ⟨12, 1, 0, 450498, 375340, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375340_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375340 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 375340 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 375340, 1, 65536⟩
    (by decide) selected_cut_48133

theorem selected_cut_48134 : selected 9 ⟨1349354, by decide⟩
    (prefixPartial 12 375341) = some ⟨12, 2, 0, 1349354, 375341, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_375341_1349354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375341 ⟨1349354, by decide⟩ :=
  accepted_of_selected 12 375341 ⟨1349354, by decide⟩ ⟨12, 2, 0, 1349354, 375341, 2565, 65536⟩
    (by decide) selected_cut_48134

theorem selected_cut_48135 : selected 9 ⟨1349397, by decide⟩
    (prefixPartial 12 375342) = some ⟨12, 2, 0, 1349397, 375342, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_375342_1349397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375342 ⟨1349397, by decide⟩ :=
  accepted_of_selected 12 375342 ⟨1349397, by decide⟩ ⟨12, 2, 0, 1349397, 375342, 2005, 65536⟩
    (by decide) selected_cut_48135

theorem selected_cut_48136 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 375343) = some ⟨12, 1, 0, 758968, 375343, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375343_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375343 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 375343 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 375343, 1, 65536⟩
    (by decide) selected_cut_48136

theorem unmarked_context_11_93835_1349398 : frontier 10 ⟨1349398, by decide⟩
    (prefixCache 11 93835) (prefixPartial 11 93835) = false := by
  decide +kernel

theorem node_context_11_93835_1349398 : EJMOriginalGlobalDAGData.nodes 10 ⟨1349398, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1349354, by decide⟩,⟨1349397, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93835_1349398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93835 ⟨1349398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93835
    ⟨1349398, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1349354, by decide⟩,⟨1349397, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_93835_1349398 node_context_11_93835_1349398
  intro a
  fin_cases a
  · exact context_12_375340_450498
  · exact context_12_375341_1349354
  · exact context_12_375342_1349397
  · exact context_12_375343_758968

theorem unmarked_context_10_23458_1349399 : frontier 11 ⟨1349399, by decide⟩
    (prefixCache 10 23458) (prefixPartial 10 23458) = false := by
  decide +kernel

theorem node_context_10_23458_1349399 : EJMOriginalGlobalDAGData.nodes 11 ⟨1349399, by decide⟩ =
    .split (coordinate 10) (![⟨1349180, by decide⟩,⟨1349295, by decide⟩,⟨900587, by decide⟩,⟨1349398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23458_1349399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23458 ⟨1349399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23458
    ⟨1349399, by decide⟩ (by decide) (![⟨1349180, by decide⟩,⟨1349295, by decide⟩,⟨900587, by decide⟩,⟨1349398, by decide⟩]) unmarked_context_10_23458_1349399 node_context_10_23458_1349399
  intro a
  fin_cases a
  · exact context_11_93832_1349180
  · exact context_11_93833_1349295
  · exact context_11_93834_900587
  · exact context_11_93835_1349398

theorem selected_cut_48137 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 375344) = some ⟨12, 1, 0, 1255011, 375344, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375344_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375344 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 375344 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 375344, 1, 65536⟩
    (by decide) selected_cut_48137

theorem selected_cut_48138 : selected 9 ⟨1349446, by decide⟩
    (prefixPartial 12 375345) = some ⟨12, 2, 0, 1349446, 375345, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_375345_1349446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375345 ⟨1349446, by decide⟩ :=
  accepted_of_selected 12 375345 ⟨1349446, by decide⟩ ⟨12, 2, 0, 1349446, 375345, 2533, 65536⟩
    (by decide) selected_cut_48138

theorem selected_cut_48139 : selected 9 ⟨1349492, by decide⟩
    (prefixPartial 12 375346) = some ⟨12, 2, 0, 1349492, 375346, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_375346_1349492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375346 ⟨1349492, by decide⟩ :=
  accepted_of_selected 12 375346 ⟨1349492, by decide⟩ ⟨12, 2, 0, 1349492, 375346, 2465, 65536⟩
    (by decide) selected_cut_48139

theorem selected_cut_48140 : selected 9 ⟨1349540, by decide⟩
    (prefixPartial 12 375347) = some ⟨12, 2, 0, 1349540, 375347, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_375347_1349540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375347 ⟨1349540, by decide⟩ :=
  accepted_of_selected 12 375347 ⟨1349540, by decide⟩ ⟨12, 2, 0, 1349540, 375347, 2349, 65536⟩
    (by decide) selected_cut_48140

theorem unmarked_context_11_93836_1349541 : frontier 10 ⟨1349541, by decide⟩
    (prefixCache 11 93836) (prefixPartial 11 93836) = false := by
  decide +kernel

theorem node_context_11_93836_1349541 : EJMOriginalGlobalDAGData.nodes 10 ⟨1349541, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1349446, by decide⟩,⟨1349492, by decide⟩,⟨1349540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93836_1349541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93836 ⟨1349541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93836
    ⟨1349541, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1349446, by decide⟩,⟨1349492, by decide⟩,⟨1349540, by decide⟩]) unmarked_context_11_93836_1349541 node_context_11_93836_1349541
  intro a
  fin_cases a
  · exact context_12_375344_1255011
  · exact context_12_375345_1349446
  · exact context_12_375346_1349492
  · exact context_12_375347_1349540

theorem selected_cut_48141 : selected 9 ⟨1349595, by decide⟩
    (prefixPartial 12 375348) = some ⟨12, 2, 0, 1349595, 375348, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_375348_1349595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375348 ⟨1349595, by decide⟩ :=
  accepted_of_selected 12 375348 ⟨1349595, by decide⟩ ⟨12, 2, 0, 1349595, 375348, 2697, 65536⟩
    (by decide) selected_cut_48141

theorem selected_cut_48142 : selected 9 ⟨1349668, by decide⟩
    (prefixPartial 12 375349) = some ⟨12, 2, 0, 1349668, 375349, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_375349_1349668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375349 ⟨1349668, by decide⟩ :=
  accepted_of_selected 12 375349 ⟨1349668, by decide⟩ ⟨12, 2, 0, 1349668, 375349, 2801, 65536⟩
    (by decide) selected_cut_48142

theorem selected_cut_48143 : selected 9 ⟨1349723, by decide⟩
    (prefixPartial 12 375350) = some ⟨12, 2, 0, 1349723, 375350, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_375350_1349723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375350 ⟨1349723, by decide⟩ :=
  accepted_of_selected 12 375350 ⟨1349723, by decide⟩ ⟨12, 2, 0, 1349723, 375350, 2605, 65536⟩
    (by decide) selected_cut_48143

theorem selected_cut_48144 : selected 9 ⟨1349777, by decide⟩
    (prefixPartial 12 375351) = some ⟨12, 2, 0, 1349777, 375351, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_375351_1349777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375351 ⟨1349777, by decide⟩ :=
  accepted_of_selected 12 375351 ⟨1349777, by decide⟩ ⟨12, 2, 0, 1349777, 375351, 2381, 65536⟩
    (by decide) selected_cut_48144

theorem unmarked_context_11_93837_1349778 : frontier 10 ⟨1349778, by decide⟩
    (prefixCache 11 93837) (prefixPartial 11 93837) = false := by
  decide +kernel

theorem node_context_11_93837_1349778 : EJMOriginalGlobalDAGData.nodes 10 ⟨1349778, by decide⟩ =
    .split (coordinate 11) (![⟨1349595, by decide⟩,⟨1349668, by decide⟩,⟨1349723, by decide⟩,⟨1349777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93837_1349778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93837 ⟨1349778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93837
    ⟨1349778, by decide⟩ (by decide) (![⟨1349595, by decide⟩,⟨1349668, by decide⟩,⟨1349723, by decide⟩,⟨1349777, by decide⟩]) unmarked_context_11_93837_1349778 node_context_11_93837_1349778
  intro a
  fin_cases a
  · exact context_12_375348_1349595
  · exact context_12_375349_1349668
  · exact context_12_375350_1349723
  · exact context_12_375351_1349777

theorem selected_cut_48145 : selected 10 ⟨1349845, by decide⟩
    (prefixPartial 11 93838) = some ⟨11, 2, 0, 1349845, 93838, 3657, 262144⟩ := by
  decide +kernel

theorem context_11_93838_1349845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93838 ⟨1349845, by decide⟩ :=
  accepted_of_selected 11 93838 ⟨1349845, by decide⟩ ⟨11, 2, 0, 1349845, 93838, 3657, 262144⟩
    (by decide) selected_cut_48145

theorem selected_cut_48146 : selected 10 ⟨1349935, by decide⟩
    (prefixPartial 11 93839) = some ⟨11, 2, 0, 1349935, 93839, 4045, 262144⟩ := by
  decide +kernel

theorem context_11_93839_1349935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93839 ⟨1349935, by decide⟩ :=
  accepted_of_selected 11 93839 ⟨1349935, by decide⟩ ⟨11, 2, 0, 1349935, 93839, 4045, 262144⟩
    (by decide) selected_cut_48146

theorem unmarked_context_10_23459_1349936 : frontier 11 ⟨1349936, by decide⟩
    (prefixCache 10 23459) (prefixPartial 10 23459) = false := by
  decide +kernel

theorem node_context_10_23459_1349936 : EJMOriginalGlobalDAGData.nodes 11 ⟨1349936, by decide⟩ =
    .split (coordinate 10) (![⟨1349541, by decide⟩,⟨1349778, by decide⟩,⟨1349845, by decide⟩,⟨1349935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23459_1349936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23459 ⟨1349936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23459
    ⟨1349936, by decide⟩ (by decide) (![⟨1349541, by decide⟩,⟨1349778, by decide⟩,⟨1349845, by decide⟩,⟨1349935, by decide⟩]) unmarked_context_10_23459_1349936 node_context_10_23459_1349936
  intro a
  fin_cases a
  · exact context_11_93836_1349541
  · exact context_11_93837_1349778
  · exact context_11_93838_1349845
  · exact context_11_93839_1349935

theorem unmarked_context_9_5864_1349937 : frontier 12 ⟨1349937, by decide⟩
    (prefixCache 9 5864) (prefixPartial 9 5864) = false := by
  decide +kernel

theorem node_context_9_5864_1349937 : EJMOriginalGlobalDAGData.nodes 12 ⟨1349937, by decide⟩ =
    .split (coordinate 9) (![⟨1348340, by decide⟩,⟨1349048, by decide⟩,⟨1349399, by decide⟩,⟨1349936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5864_1349937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5864 ⟨1349937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5864
    ⟨1349937, by decide⟩ (by decide) (![⟨1348340, by decide⟩,⟨1349048, by decide⟩,⟨1349399, by decide⟩,⟨1349936, by decide⟩]) unmarked_context_9_5864_1349937 node_context_9_5864_1349937
  intro a
  fin_cases a
  · exact context_10_23456_1348340
  · exact context_10_23457_1349048
  · exact context_10_23458_1349399
  · exact context_10_23459_1349936

theorem selected_cut_48147 : selected 10 ⟨1350006, by decide⟩
    (prefixPartial 11 93840) = some ⟨11, 2, 0, 1350006, 93840, 3661, 262144⟩ := by
  decide +kernel

theorem context_11_93840_1350006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93840 ⟨1350006, by decide⟩ :=
  accepted_of_selected 11 93840 ⟨1350006, by decide⟩ ⟨11, 2, 0, 1350006, 93840, 3661, 262144⟩
    (by decide) selected_cut_48147

theorem selected_cut_48148 : selected 9 ⟨1350050, by decide⟩
    (prefixPartial 12 375364) = some ⟨12, 2, 0, 1350050, 375364, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_375364_1350050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375364 ⟨1350050, by decide⟩ :=
  accepted_of_selected 12 375364 ⟨1350050, by decide⟩ ⟨12, 2, 0, 1350050, 375364, 2037, 65536⟩
    (by decide) selected_cut_48148

theorem selected_cut_48149 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 375365) = some ⟨12, 1, 0, 1257136, 375365, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375365_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375365 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 375365 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 375365, 1, 65536⟩
    (by decide) selected_cut_48149

theorem selected_cut_48150 : selected 9 ⟨1350089, by decide⟩
    (prefixPartial 12 375366) = some ⟨12, 2, 0, 1350089, 375366, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_375366_1350089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375366 ⟨1350089, by decide⟩ :=
  accepted_of_selected 12 375366 ⟨1350089, by decide⟩ ⟨12, 2, 0, 1350089, 375366, 1825, 65536⟩
    (by decide) selected_cut_48150

theorem selected_cut_48151 : selected 9 ⟨1350122, by decide⟩
    (prefixPartial 12 375367) = some ⟨12, 2, 0, 1350122, 375367, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_375367_1350122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375367 ⟨1350122, by decide⟩ :=
  accepted_of_selected 12 375367 ⟨1350122, by decide⟩ ⟨12, 2, 0, 1350122, 375367, 1813, 65536⟩
    (by decide) selected_cut_48151

theorem unmarked_context_11_93841_1350123 : frontier 10 ⟨1350123, by decide⟩
    (prefixCache 11 93841) (prefixPartial 11 93841) = false := by
  decide +kernel

theorem node_context_11_93841_1350123 : EJMOriginalGlobalDAGData.nodes 10 ⟨1350123, by decide⟩ =
    .split (coordinate 11) (![⟨1350050, by decide⟩,⟨1257136, by decide⟩,⟨1350089, by decide⟩,⟨1350122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93841_1350123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93841 ⟨1350123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93841
    ⟨1350123, by decide⟩ (by decide) (![⟨1350050, by decide⟩,⟨1257136, by decide⟩,⟨1350089, by decide⟩,⟨1350122, by decide⟩]) unmarked_context_11_93841_1350123 node_context_11_93841_1350123
  intro a
  fin_cases a
  · exact context_12_375364_1350050
  · exact context_12_375365_1257136
  · exact context_12_375366_1350089
  · exact context_12_375367_1350122

theorem selected_cut_48152 : selected 10 ⟨1350183, by decide⟩
    (prefixPartial 11 93842) = some ⟨11, 2, 0, 1350183, 93842, 3205, 262144⟩ := by
  decide +kernel

theorem context_11_93842_1350183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93842 ⟨1350183, by decide⟩ :=
  accepted_of_selected 11 93842 ⟨1350183, by decide⟩ ⟨11, 2, 0, 1350183, 93842, 3205, 262144⟩
    (by decide) selected_cut_48152

theorem selected_cut_48153 : selected 9 ⟨1350222, by decide⟩
    (prefixPartial 12 375372) = some ⟨12, 2, 0, 1350222, 375372, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_375372_1350222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375372 ⟨1350222, by decide⟩ :=
  accepted_of_selected 12 375372 ⟨1350222, by decide⟩ ⟨12, 2, 0, 1350222, 375372, 1845, 65536⟩
    (by decide) selected_cut_48153

theorem selected_cut_48154 : selected 9 ⟨1350256, by decide⟩
    (prefixPartial 12 375373) = some ⟨12, 2, 0, 1350256, 375373, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_375373_1350256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375373 ⟨1350256, by decide⟩ :=
  accepted_of_selected 12 375373 ⟨1350256, by decide⟩ ⟨12, 2, 0, 1350256, 375373, 1721, 65536⟩
    (by decide) selected_cut_48154

theorem selected_cut_48155 : selected 9 ⟨1350289, by decide⟩
    (prefixPartial 12 375374) = some ⟨12, 2, 0, 1350289, 375374, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_375374_1350289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375374 ⟨1350289, by decide⟩ :=
  accepted_of_selected 12 375374 ⟨1350289, by decide⟩ ⟨12, 2, 0, 1350289, 375374, 1609, 65536⟩
    (by decide) selected_cut_48155

theorem selected_cut_48156 : selected 9 ⟨1350320, by decide⟩
    (prefixPartial 12 375375) = some ⟨12, 2, 0, 1350320, 375375, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_375375_1350320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375375 ⟨1350320, by decide⟩ :=
  accepted_of_selected 12 375375 ⟨1350320, by decide⟩ ⟨12, 2, 0, 1350320, 375375, 1541, 65536⟩
    (by decide) selected_cut_48156

theorem unmarked_context_11_93843_1350321 : frontier 10 ⟨1350321, by decide⟩
    (prefixCache 11 93843) (prefixPartial 11 93843) = false := by
  decide +kernel

theorem node_context_11_93843_1350321 : EJMOriginalGlobalDAGData.nodes 10 ⟨1350321, by decide⟩ =
    .split (coordinate 11) (![⟨1350222, by decide⟩,⟨1350256, by decide⟩,⟨1350289, by decide⟩,⟨1350320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93843_1350321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93843 ⟨1350321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93843
    ⟨1350321, by decide⟩ (by decide) (![⟨1350222, by decide⟩,⟨1350256, by decide⟩,⟨1350289, by decide⟩,⟨1350320, by decide⟩]) unmarked_context_11_93843_1350321 node_context_11_93843_1350321
  intro a
  fin_cases a
  · exact context_12_375372_1350222
  · exact context_12_375373_1350256
  · exact context_12_375374_1350289
  · exact context_12_375375_1350320

theorem unmarked_context_10_23460_1350322 : frontier 11 ⟨1350322, by decide⟩
    (prefixCache 10 23460) (prefixPartial 10 23460) = false := by
  decide +kernel

theorem node_context_10_23460_1350322 : EJMOriginalGlobalDAGData.nodes 11 ⟨1350322, by decide⟩ =
    .split (coordinate 10) (![⟨1350006, by decide⟩,⟨1350123, by decide⟩,⟨1350183, by decide⟩,⟨1350321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23460_1350322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23460 ⟨1350322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23460
    ⟨1350322, by decide⟩ (by decide) (![⟨1350006, by decide⟩,⟨1350123, by decide⟩,⟨1350183, by decide⟩,⟨1350321, by decide⟩]) unmarked_context_10_23460_1350322 node_context_10_23460_1350322
  intro a
  fin_cases a
  · exact context_11_93840_1350006
  · exact context_11_93841_1350123
  · exact context_11_93842_1350183
  · exact context_11_93843_1350321

theorem selected_cut_48157 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23461) = some ⟨10, 1, 0, 893098, 23461, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23461_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23461 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23461 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23461, 1, 1048576⟩
    (by decide) selected_cut_48157

theorem selected_cut_48158 : selected 10 ⟨1350363, by decide⟩
    (prefixPartial 11 93848) = some ⟨11, 2, 0, 1350363, 93848, 2449, 262144⟩ := by
  decide +kernel

theorem context_11_93848_1350363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93848 ⟨1350363, by decide⟩ :=
  accepted_of_selected 11 93848 ⟨1350363, by decide⟩ ⟨11, 2, 0, 1350363, 93848, 2449, 262144⟩
    (by decide) selected_cut_48158

theorem selected_cut_48159 : selected 10 ⟨1350425, by decide⟩
    (prefixPartial 11 93849) = some ⟨11, 2, 0, 1350425, 93849, 3501, 262144⟩ := by
  decide +kernel

theorem context_11_93849_1350425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93849 ⟨1350425, by decide⟩ :=
  accepted_of_selected 11 93849 ⟨1350425, by decide⟩ ⟨11, 2, 0, 1350425, 93849, 3501, 262144⟩
    (by decide) selected_cut_48159

theorem selected_cut_48160 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 93850) = some ⟨11, 1, 0, 900587, 93850, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93850_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93850 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 93850 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 93850, 1, 262144⟩
    (by decide) selected_cut_48160

theorem selected_cut_48161 : selected 10 ⟨1350460, by decide⟩
    (prefixPartial 11 93851) = some ⟨11, 2, 0, 1350460, 93851, 2109, 262144⟩ := by
  decide +kernel

theorem context_11_93851_1350460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93851 ⟨1350460, by decide⟩ :=
  accepted_of_selected 11 93851 ⟨1350460, by decide⟩ ⟨11, 2, 0, 1350460, 93851, 2109, 262144⟩
    (by decide) selected_cut_48161

theorem unmarked_context_10_23462_1350461 : frontier 11 ⟨1350461, by decide⟩
    (prefixCache 10 23462) (prefixPartial 10 23462) = false := by
  decide +kernel

theorem node_context_10_23462_1350461 : EJMOriginalGlobalDAGData.nodes 11 ⟨1350461, by decide⟩ =
    .split (coordinate 10) (![⟨1350363, by decide⟩,⟨1350425, by decide⟩,⟨900587, by decide⟩,⟨1350460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23462_1350461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23462 ⟨1350461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23462
    ⟨1350461, by decide⟩ (by decide) (![⟨1350363, by decide⟩,⟨1350425, by decide⟩,⟨900587, by decide⟩,⟨1350460, by decide⟩]) unmarked_context_10_23462_1350461 node_context_10_23462_1350461
  intro a
  fin_cases a
  · exact context_11_93848_1350363
  · exact context_11_93849_1350425
  · exact context_11_93850_900587
  · exact context_11_93851_1350460

theorem selected_cut_48162 : selected 9 ⟨1350477, by decide⟩
    (prefixPartial 12 375408) = some ⟨12, 2, 0, 1350477, 375408, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_375408_1350477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375408 ⟨1350477, by decide⟩ :=
  accepted_of_selected 12 375408 ⟨1350477, by decide⟩ ⟨12, 2, 0, 1350477, 375408, 1069, 65536⟩
    (by decide) selected_cut_48162

theorem selected_cut_48163 : selected 9 ⟨1350494, by decide⟩
    (prefixPartial 12 375409) = some ⟨12, 2, 0, 1350494, 375409, 1001, 65536⟩ := by
  decide +kernel

theorem context_12_375409_1350494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375409 ⟨1350494, by decide⟩ :=
  accepted_of_selected 12 375409 ⟨1350494, by decide⟩ ⟨12, 2, 0, 1350494, 375409, 1001, 65536⟩
    (by decide) selected_cut_48163

theorem selected_cut_48164 : selected 9 ⟨1350508, by decide⟩
    (prefixPartial 12 375410) = some ⟨12, 2, 0, 1350508, 375410, 1037, 65536⟩ := by
  decide +kernel

theorem context_12_375410_1350508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375410 ⟨1350508, by decide⟩ :=
  accepted_of_selected 12 375410 ⟨1350508, by decide⟩ ⟨12, 2, 0, 1350508, 375410, 1037, 65536⟩
    (by decide) selected_cut_48164

theorem selected_cut_48165 : selected 9 ⟨1350523, by decide⟩
    (prefixPartial 12 375411) = some ⟨12, 2, 0, 1350523, 375411, 1029, 65536⟩ := by
  decide +kernel

theorem context_12_375411_1350523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375411 ⟨1350523, by decide⟩ :=
  accepted_of_selected 12 375411 ⟨1350523, by decide⟩ ⟨12, 2, 0, 1350523, 375411, 1029, 65536⟩
    (by decide) selected_cut_48165

theorem unmarked_context_11_93852_1350524 : frontier 10 ⟨1350524, by decide⟩
    (prefixCache 11 93852) (prefixPartial 11 93852) = false := by
  decide +kernel

theorem node_context_11_93852_1350524 : EJMOriginalGlobalDAGData.nodes 10 ⟨1350524, by decide⟩ =
    .split (coordinate 11) (![⟨1350477, by decide⟩,⟨1350494, by decide⟩,⟨1350508, by decide⟩,⟨1350523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93852_1350524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93852 ⟨1350524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93852
    ⟨1350524, by decide⟩ (by decide) (![⟨1350477, by decide⟩,⟨1350494, by decide⟩,⟨1350508, by decide⟩,⟨1350523, by decide⟩]) unmarked_context_11_93852_1350524 node_context_11_93852_1350524
  intro a
  fin_cases a
  · exact context_12_375408_1350477
  · exact context_12_375409_1350494
  · exact context_12_375410_1350508
  · exact context_12_375411_1350523

theorem selected_cut_48166 : selected 10 ⟨1350566, by decide⟩
    (prefixPartial 11 93853) = some ⟨11, 2, 0, 1350566, 93853, 2817, 262144⟩ := by
  decide +kernel

theorem context_11_93853_1350566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93853 ⟨1350566, by decide⟩ :=
  accepted_of_selected 11 93853 ⟨1350566, by decide⟩ ⟨11, 2, 0, 1350566, 93853, 2817, 262144⟩
    (by decide) selected_cut_48166

theorem selected_cut_48167 : selected 10 ⟨1350586, by decide⟩
    (prefixPartial 11 93854) = some ⟨11, 2, 0, 1350586, 93854, 1589, 262144⟩ := by
  decide +kernel

theorem context_11_93854_1350586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93854 ⟨1350586, by decide⟩ :=
  accepted_of_selected 11 93854 ⟨1350586, by decide⟩ ⟨11, 2, 0, 1350586, 93854, 1589, 262144⟩
    (by decide) selected_cut_48167

theorem selected_cut_48168 : selected 10 ⟨1350608, by decide⟩
    (prefixPartial 11 93855) = some ⟨11, 2, 0, 1350608, 93855, 1541, 262144⟩ := by
  decide +kernel

theorem context_11_93855_1350608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93855 ⟨1350608, by decide⟩ :=
  accepted_of_selected 11 93855 ⟨1350608, by decide⟩ ⟨11, 2, 0, 1350608, 93855, 1541, 262144⟩
    (by decide) selected_cut_48168

theorem unmarked_context_10_23463_1350609 : frontier 11 ⟨1350609, by decide⟩
    (prefixCache 10 23463) (prefixPartial 10 23463) = false := by
  decide +kernel

theorem node_context_10_23463_1350609 : EJMOriginalGlobalDAGData.nodes 11 ⟨1350609, by decide⟩ =
    .split (coordinate 10) (![⟨1350524, by decide⟩,⟨1350566, by decide⟩,⟨1350586, by decide⟩,⟨1350608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23463_1350609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23463 ⟨1350609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23463
    ⟨1350609, by decide⟩ (by decide) (![⟨1350524, by decide⟩,⟨1350566, by decide⟩,⟨1350586, by decide⟩,⟨1350608, by decide⟩]) unmarked_context_10_23463_1350609 node_context_10_23463_1350609
  intro a
  fin_cases a
  · exact context_11_93852_1350524
  · exact context_11_93853_1350566
  · exact context_11_93854_1350586
  · exact context_11_93855_1350608

theorem unmarked_context_9_5865_1350610 : frontier 12 ⟨1350610, by decide⟩
    (prefixCache 9 5865) (prefixPartial 9 5865) = false := by
  decide +kernel

theorem node_context_9_5865_1350610 : EJMOriginalGlobalDAGData.nodes 12 ⟨1350610, by decide⟩ =
    .split (coordinate 9) (![⟨1350322, by decide⟩,⟨893098, by decide⟩,⟨1350461, by decide⟩,⟨1350609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5865_1350610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5865 ⟨1350610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5865
    ⟨1350610, by decide⟩ (by decide) (![⟨1350322, by decide⟩,⟨893098, by decide⟩,⟨1350461, by decide⟩,⟨1350609, by decide⟩]) unmarked_context_9_5865_1350610 node_context_9_5865_1350610
  intro a
  fin_cases a
  · exact context_10_23460_1350322
  · exact context_10_23461_893098
  · exact context_10_23462_1350461
  · exact context_10_23463_1350609

theorem selected_cut_48169 : selected 10 ⟨1344623, by decide⟩
    (prefixPartial 11 93856) = some ⟨11, 2, 0, 1344623, 93856, 5, 262144⟩ := by
  decide +kernel

theorem context_11_93856_1344623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93856 ⟨1344623, by decide⟩ :=
  accepted_of_selected 11 93856 ⟨1344623, by decide⟩ ⟨11, 2, 0, 1344623, 93856, 5, 262144⟩
    (by decide) selected_cut_48169

theorem selected_cut_48170 : selected 10 ⟨1350647, by decide⟩
    (prefixPartial 11 93857) = some ⟨11, 2, 0, 1350647, 93857, 1993, 262144⟩ := by
  decide +kernel

theorem context_11_93857_1350647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93857 ⟨1350647, by decide⟩ :=
  accepted_of_selected 11 93857 ⟨1350647, by decide⟩ ⟨11, 2, 0, 1350647, 93857, 1993, 262144⟩
    (by decide) selected_cut_48170

theorem selected_cut_48171 : selected 10 ⟨1350682, by decide⟩
    (prefixPartial 11 93858) = some ⟨11, 2, 0, 1350682, 93858, 2381, 262144⟩ := by
  decide +kernel

theorem context_11_93858_1350682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93858 ⟨1350682, by decide⟩ :=
  accepted_of_selected 11 93858 ⟨1350682, by decide⟩ ⟨11, 2, 0, 1350682, 93858, 2381, 262144⟩
    (by decide) selected_cut_48171

theorem selected_cut_48172 : selected 10 ⟨1350725, by decide⟩
    (prefixPartial 11 93859) = some ⟨11, 2, 0, 1350725, 93859, 1861, 262144⟩ := by
  decide +kernel

theorem context_11_93859_1350725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93859 ⟨1350725, by decide⟩ :=
  accepted_of_selected 11 93859 ⟨1350725, by decide⟩ ⟨11, 2, 0, 1350725, 93859, 1861, 262144⟩
    (by decide) selected_cut_48172

theorem unmarked_context_10_23464_1350726 : frontier 11 ⟨1350726, by decide⟩
    (prefixCache 10 23464) (prefixPartial 10 23464) = false := by
  decide +kernel

theorem node_context_10_23464_1350726 : EJMOriginalGlobalDAGData.nodes 11 ⟨1350726, by decide⟩ =
    .split (coordinate 10) (![⟨1344623, by decide⟩,⟨1350647, by decide⟩,⟨1350682, by decide⟩,⟨1350725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23464_1350726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23464 ⟨1350726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23464
    ⟨1350726, by decide⟩ (by decide) (![⟨1344623, by decide⟩,⟨1350647, by decide⟩,⟨1350682, by decide⟩,⟨1350725, by decide⟩]) unmarked_context_10_23464_1350726 node_context_10_23464_1350726
  intro a
  fin_cases a
  · exact context_11_93856_1344623
  · exact context_11_93857_1350647
  · exact context_11_93858_1350682
  · exact context_11_93859_1350725

theorem selected_cut_48173 : selected 10 ⟨1350760, by decide⟩
    (prefixPartial 11 93860) = some ⟨11, 2, 0, 1350760, 93860, 1669, 262144⟩ := by
  decide +kernel

theorem context_11_93860_1350760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93860 ⟨1350760, by decide⟩ :=
  accepted_of_selected 11 93860 ⟨1350760, by decide⟩ ⟨11, 2, 0, 1350760, 93860, 1669, 262144⟩
    (by decide) selected_cut_48173

theorem selected_cut_48174 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 93861) = some ⟨11, 1, 0, 1192826, 93861, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93861_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93861 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 93861 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 93861, 1, 262144⟩
    (by decide) selected_cut_48174

theorem selected_cut_48175 : selected 10 ⟨1350791, by decide⟩
    (prefixPartial 11 93862) = some ⟨11, 2, 0, 1350791, 93862, 1877, 262144⟩ := by
  decide +kernel

theorem context_11_93862_1350791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93862 ⟨1350791, by decide⟩ :=
  accepted_of_selected 11 93862 ⟨1350791, by decide⟩ ⟨11, 2, 0, 1350791, 93862, 1877, 262144⟩
    (by decide) selected_cut_48175

theorem selected_cut_48176 : selected 10 ⟨1350821, by decide⟩
    (prefixPartial 11 93863) = some ⟨11, 2, 0, 1350821, 93863, 1453, 262144⟩ := by
  decide +kernel

theorem context_11_93863_1350821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93863 ⟨1350821, by decide⟩ :=
  accepted_of_selected 11 93863 ⟨1350821, by decide⟩ ⟨11, 2, 0, 1350821, 93863, 1453, 262144⟩
    (by decide) selected_cut_48176

theorem unmarked_context_10_23465_1350822 : frontier 11 ⟨1350822, by decide⟩
    (prefixCache 10 23465) (prefixPartial 10 23465) = false := by
  decide +kernel

theorem node_context_10_23465_1350822 : EJMOriginalGlobalDAGData.nodes 11 ⟨1350822, by decide⟩ =
    .split (coordinate 10) (![⟨1350760, by decide⟩,⟨1192826, by decide⟩,⟨1350791, by decide⟩,⟨1350821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23465_1350822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23465 ⟨1350822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23465
    ⟨1350822, by decide⟩ (by decide) (![⟨1350760, by decide⟩,⟨1192826, by decide⟩,⟨1350791, by decide⟩,⟨1350821, by decide⟩]) unmarked_context_10_23465_1350822 node_context_10_23465_1350822
  intro a
  fin_cases a
  · exact context_11_93860_1350760
  · exact context_11_93861_1192826
  · exact context_11_93862_1350791
  · exact context_11_93863_1350821

theorem selected_cut_48177 : selected 11 ⟨1350841, by decide⟩
    (prefixPartial 10 23466) = some ⟨10, 2, 0, 1350841, 23466, 1069, 1048576⟩ := by
  decide +kernel

theorem context_10_23466_1350841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23466 ⟨1350841, by decide⟩ :=
  accepted_of_selected 10 23466 ⟨1350841, by decide⟩ ⟨10, 2, 0, 1350841, 23466, 1069, 1048576⟩
    (by decide) selected_cut_48177

theorem selected_cut_48178 : selected 11 ⟨1350908, by decide⟩
    (prefixPartial 10 23467) = some ⟨10, 2, 0, 1350908, 23467, 3457, 1048576⟩ := by
  decide +kernel

theorem context_10_23467_1350908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23467 ⟨1350908, by decide⟩ :=
  accepted_of_selected 10 23467 ⟨1350908, by decide⟩ ⟨10, 2, 0, 1350908, 23467, 3457, 1048576⟩
    (by decide) selected_cut_48178

theorem unmarked_context_9_5866_1350909 : frontier 12 ⟨1350909, by decide⟩
    (prefixCache 9 5866) (prefixPartial 9 5866) = false := by
  decide +kernel

theorem node_context_9_5866_1350909 : EJMOriginalGlobalDAGData.nodes 12 ⟨1350909, by decide⟩ =
    .split (coordinate 9) (![⟨1350726, by decide⟩,⟨1350822, by decide⟩,⟨1350841, by decide⟩,⟨1350908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5866_1350909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5866 ⟨1350909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5866
    ⟨1350909, by decide⟩ (by decide) (![⟨1350726, by decide⟩,⟨1350822, by decide⟩,⟨1350841, by decide⟩,⟨1350908, by decide⟩]) unmarked_context_9_5866_1350909 node_context_9_5866_1350909
  intro a
  fin_cases a
  · exact context_10_23464_1350726
  · exact context_10_23465_1350822
  · exact context_10_23466_1350841
  · exact context_10_23467_1350908

theorem selected_cut_48179 : selected 10 ⟨1350925, by decide⟩
    (prefixPartial 11 93872) = some ⟨11, 2, 0, 1350925, 93872, 1097, 262144⟩ := by
  decide +kernel

theorem context_11_93872_1350925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93872 ⟨1350925, by decide⟩ :=
  accepted_of_selected 11 93872 ⟨1350925, by decide⟩ ⟨11, 2, 0, 1350925, 93872, 1097, 262144⟩
    (by decide) selected_cut_48179

theorem selected_cut_48180 : selected 10 ⟨1350972, by decide⟩
    (prefixPartial 11 93873) = some ⟨11, 2, 0, 1350972, 93873, 2253, 262144⟩ := by
  decide +kernel

theorem context_11_93873_1350972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93873 ⟨1350972, by decide⟩ :=
  accepted_of_selected 11 93873 ⟨1350972, by decide⟩ ⟨11, 2, 0, 1350972, 93873, 2253, 262144⟩
    (by decide) selected_cut_48180

theorem selected_cut_48181 : selected 10 ⟨1350988, by decide⟩
    (prefixPartial 11 93874) = some ⟨11, 2, 0, 1350988, 93874, 893, 262144⟩ := by
  decide +kernel

theorem context_11_93874_1350988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93874 ⟨1350988, by decide⟩ :=
  accepted_of_selected 11 93874 ⟨1350988, by decide⟩ ⟨11, 2, 0, 1350988, 93874, 893, 262144⟩
    (by decide) selected_cut_48181

theorem selected_cut_48182 : selected 10 ⟨1351018, by decide⟩
    (prefixPartial 11 93875) = some ⟨11, 2, 0, 1351018, 93875, 1313, 262144⟩ := by
  decide +kernel

theorem context_11_93875_1351018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93875 ⟨1351018, by decide⟩ :=
  accepted_of_selected 11 93875 ⟨1351018, by decide⟩ ⟨11, 2, 0, 1351018, 93875, 1313, 262144⟩
    (by decide) selected_cut_48182

theorem unmarked_context_10_23468_1351019 : frontier 11 ⟨1351019, by decide⟩
    (prefixCache 10 23468) (prefixPartial 10 23468) = false := by
  decide +kernel

theorem node_context_10_23468_1351019 : EJMOriginalGlobalDAGData.nodes 11 ⟨1351019, by decide⟩ =
    .split (coordinate 10) (![⟨1350925, by decide⟩,⟨1350972, by decide⟩,⟨1350988, by decide⟩,⟨1351018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23468_1351019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23468 ⟨1351019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23468
    ⟨1351019, by decide⟩ (by decide) (![⟨1350925, by decide⟩,⟨1350972, by decide⟩,⟨1350988, by decide⟩,⟨1351018, by decide⟩]) unmarked_context_10_23468_1351019 node_context_10_23468_1351019
  intro a
  fin_cases a
  · exact context_11_93872_1350925
  · exact context_11_93873_1350972
  · exact context_11_93874_1350988
  · exact context_11_93875_1351018

theorem selected_cut_48183 : selected 11 ⟨1351074, by decide⟩
    (prefixPartial 10 23469) = some ⟨10, 2, 0, 1351074, 23469, 2801, 1048576⟩ := by
  decide +kernel

theorem context_10_23469_1351074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23469 ⟨1351074, by decide⟩ :=
  accepted_of_selected 10 23469 ⟨1351074, by decide⟩ ⟨10, 2, 0, 1351074, 23469, 2801, 1048576⟩
    (by decide) selected_cut_48183

theorem selected_cut_48184 : selected 11 ⟨1351098, by decide⟩
    (prefixPartial 10 23470) = some ⟨10, 2, 0, 1351098, 23470, 749, 1048576⟩ := by
  decide +kernel

theorem context_10_23470_1351098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23470 ⟨1351098, by decide⟩ :=
  accepted_of_selected 10 23470 ⟨1351098, by decide⟩ ⟨10, 2, 0, 1351098, 23470, 749, 1048576⟩
    (by decide) selected_cut_48184

theorem selected_cut_48185 : selected 11 ⟨1351105, by decide⟩
    (prefixPartial 10 23471) = some ⟨10, 2, 0, 1351105, 23471, 141, 1048576⟩ := by
  decide +kernel

theorem context_10_23471_1351105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23471 ⟨1351105, by decide⟩ :=
  accepted_of_selected 10 23471 ⟨1351105, by decide⟩ ⟨10, 2, 0, 1351105, 23471, 141, 1048576⟩
    (by decide) selected_cut_48185

theorem unmarked_context_9_5867_1351106 : frontier 12 ⟨1351106, by decide⟩
    (prefixCache 9 5867) (prefixPartial 9 5867) = false := by
  decide +kernel

theorem node_context_9_5867_1351106 : EJMOriginalGlobalDAGData.nodes 12 ⟨1351106, by decide⟩ =
    .split (coordinate 9) (![⟨1351019, by decide⟩,⟨1351074, by decide⟩,⟨1351098, by decide⟩,⟨1351105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5867_1351106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5867 ⟨1351106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5867
    ⟨1351106, by decide⟩ (by decide) (![⟨1351019, by decide⟩,⟨1351074, by decide⟩,⟨1351098, by decide⟩,⟨1351105, by decide⟩]) unmarked_context_9_5867_1351106 node_context_9_5867_1351106
  intro a
  fin_cases a
  · exact context_10_23468_1351019
  · exact context_10_23469_1351074
  · exact context_10_23470_1351098
  · exact context_10_23471_1351105

theorem unmarked_context_8_1466_1351107 : frontier 13 ⟨1351107, by decide⟩
    (prefixCache 8 1466) (prefixPartial 8 1466) = false := by
  decide +kernel

theorem node_context_8_1466_1351107 : EJMOriginalGlobalDAGData.nodes 13 ⟨1351107, by decide⟩ =
    .split (coordinate 8) (![⟨1349937, by decide⟩,⟨1350610, by decide⟩,⟨1350909, by decide⟩,⟨1351106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1466_1351107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1466 ⟨1351107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1466
    ⟨1351107, by decide⟩ (by decide) (![⟨1349937, by decide⟩,⟨1350610, by decide⟩,⟨1350909, by decide⟩,⟨1351106, by decide⟩]) unmarked_context_8_1466_1351107 node_context_8_1466_1351107
  intro a
  fin_cases a
  · exact context_9_5864_1349937
  · exact context_9_5865_1350610
  · exact context_9_5866_1350909
  · exact context_9_5867_1351106

theorem selected_cut_48186 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93888) = some ⟨11, 1, 0, 434745, 93888, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93888_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93888 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93888 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93888, 1, 262144⟩
    (by decide) selected_cut_48186

theorem selected_cut_48187 : selected 10 ⟨1351165, by decide⟩
    (prefixPartial 11 93889) = some ⟨11, 2, 0, 1351165, 93889, 1821, 262144⟩ := by
  decide +kernel

theorem context_11_93889_1351165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93889 ⟨1351165, by decide⟩ :=
  accepted_of_selected 11 93889 ⟨1351165, by decide⟩ ⟨11, 2, 0, 1351165, 93889, 1821, 262144⟩
    (by decide) selected_cut_48187

theorem selected_cut_48188 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 375560) = some ⟨12, 1, 0, 448748, 375560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375560_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375560 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 375560 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 375560, 1, 65536⟩
    (by decide) selected_cut_48188

theorem selected_cut_48189 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 375561) = some ⟨12, 1, 0, 34034, 375561, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375561_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375561 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 375561 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 375561, 1, 65536⟩
    (by decide) selected_cut_48189

theorem selected_cut_48190 : selected 9 ⟨1351224, by decide⟩
    (prefixPartial 12 375562) = some ⟨12, 2, 0, 1351224, 375562, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_375562_1351224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375562 ⟨1351224, by decide⟩ :=
  accepted_of_selected 12 375562 ⟨1351224, by decide⟩ ⟨12, 2, 0, 1351224, 375562, 2881, 65536⟩
    (by decide) selected_cut_48190

theorem selected_cut_48191 : selected 9 ⟨1351272, by decide⟩
    (prefixPartial 12 375563) = some ⟨12, 2, 0, 1351272, 375563, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_375563_1351272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375563 ⟨1351272, by decide⟩ :=
  accepted_of_selected 12 375563 ⟨1351272, by decide⟩ ⟨12, 2, 0, 1351272, 375563, 2617, 65536⟩
    (by decide) selected_cut_48191

theorem unmarked_context_11_93890_1351273 : frontier 10 ⟨1351273, by decide⟩
    (prefixCache 11 93890) (prefixPartial 11 93890) = false := by
  decide +kernel

theorem node_context_11_93890_1351273 : EJMOriginalGlobalDAGData.nodes 10 ⟨1351273, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1351224, by decide⟩,⟨1351272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93890_1351273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93890 ⟨1351273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93890
    ⟨1351273, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1351224, by decide⟩,⟨1351272, by decide⟩]) unmarked_context_11_93890_1351273 node_context_11_93890_1351273
  intro a
  fin_cases a
  · exact context_12_375560_448748
  · exact context_12_375561_34034
  · exact context_12_375562_1351224
  · exact context_12_375563_1351272

theorem selected_cut_48192 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 375564) = some ⟨12, 1, 0, 448748, 375564, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375564_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375564 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 375564 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 375564, 1, 65536⟩
    (by decide) selected_cut_48192

theorem selected_cut_48193 : selected 9 ⟨1351342, by decide⟩
    (prefixPartial 12 375565) = some ⟨12, 2, 0, 1351342, 375565, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_375565_1351342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375565 ⟨1351342, by decide⟩ :=
  accepted_of_selected 12 375565 ⟨1351342, by decide⟩ ⟨12, 2, 0, 1351342, 375565, 3373, 65536⟩
    (by decide) selected_cut_48193

theorem selected_cut_48194 : selected 9 ⟨1351411, by decide⟩
    (prefixPartial 12 375566) = some ⟨12, 2, 0, 1351411, 375566, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_375566_1351411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375566 ⟨1351411, by decide⟩ :=
  accepted_of_selected 12 375566 ⟨1351411, by decide⟩ ⟨12, 2, 0, 1351411, 375566, 3205, 65536⟩
    (by decide) selected_cut_48194

theorem selected_cut_48195 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 375567) = some ⟨12, 1, 0, 903806, 375567, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375567_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375567 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 375567 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 375567, 1, 65536⟩
    (by decide) selected_cut_48195

theorem unmarked_context_11_93891_1351412 : frontier 10 ⟨1351412, by decide⟩
    (prefixCache 11 93891) (prefixPartial 11 93891) = false := by
  decide +kernel

theorem node_context_11_93891_1351412 : EJMOriginalGlobalDAGData.nodes 10 ⟨1351412, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1351342, by decide⟩,⟨1351411, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93891_1351412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93891 ⟨1351412, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93891
    ⟨1351412, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1351342, by decide⟩,⟨1351411, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93891_1351412 node_context_11_93891_1351412
  intro a
  fin_cases a
  · exact context_12_375564_448748
  · exact context_12_375565_1351342
  · exact context_12_375566_1351411
  · exact context_12_375567_903806

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
