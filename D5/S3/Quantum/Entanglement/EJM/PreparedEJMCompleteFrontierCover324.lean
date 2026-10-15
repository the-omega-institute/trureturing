/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover323
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_31108 : selected 8 ⟨792112, by decide⟩
    (prefixPartial 13 422071) = some ⟨13, 2, 0, 792112, 422071, 689, 16384⟩ := by
  decide +kernel

theorem context_13_422071_792112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422071 ⟨792112, by decide⟩ :=
  accepted_of_selected 13 422071 ⟨792112, by decide⟩ ⟨13, 2, 0, 792112, 422071, 689, 16384⟩
    (by decide) selected_cut_31108

theorem unmarked_context_12_105517_792113 : frontier 9 ⟨792113, by decide⟩
    (prefixCache 12 105517) (prefixPartial 12 105517) = false := by
  decide +kernel

theorem node_context_12_105517_792113 : EJMOriginalGlobalDAGData.nodes 9 ⟨792113, by decide⟩ =
    .split (coordinate 12) (![⟨792049, by decide⟩,⟨792085, by decide⟩,⟨792106, by decide⟩,⟨792112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105517_792113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105517 ⟨792113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105517
    ⟨792113, by decide⟩ (by decide) (![⟨792049, by decide⟩,⟨792085, by decide⟩,⟨792106, by decide⟩,⟨792112, by decide⟩]) unmarked_context_12_105517_792113 node_context_12_105517_792113
  intro a
  fin_cases a
  · exact context_13_422068_792049
  · exact context_13_422069_792085
  · exact context_13_422070_792106
  · exact context_13_422071_792112

theorem selected_cut_31109 : selected 8 ⟨792128, by decide⟩
    (prefixPartial 13 422072) = some ⟨13, 2, 0, 792128, 422072, 561, 16384⟩ := by
  decide +kernel

theorem context_13_422072_792128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422072 ⟨792128, by decide⟩ :=
  accepted_of_selected 13 422072 ⟨792128, by decide⟩ ⟨13, 2, 0, 792128, 422072, 561, 16384⟩
    (by decide) selected_cut_31109

theorem selected_cut_31110 : selected 8 ⟨792161, by decide⟩
    (prefixPartial 13 422073) = some ⟨13, 2, 0, 792161, 422073, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_422073_792161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422073 ⟨792161, by decide⟩ :=
  accepted_of_selected 13 422073 ⟨792161, by decide⟩ ⟨13, 2, 0, 792161, 422073, 2285, 16384⟩
    (by decide) selected_cut_31110

theorem selected_cut_31111 : selected 8 ⟨792180, by decide⟩
    (prefixPartial 13 422074) = some ⟨13, 2, 0, 792180, 422074, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_422074_792180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422074 ⟨792180, by decide⟩ :=
  accepted_of_selected 13 422074 ⟨792180, by decide⟩ ⟨13, 2, 0, 792180, 422074, 1157, 16384⟩
    (by decide) selected_cut_31111

theorem selected_cut_31112 : selected 8 ⟨792186, by decide⟩
    (prefixPartial 13 422075) = some ⟨13, 2, 0, 792186, 422075, 673, 16384⟩ := by
  decide +kernel

theorem context_13_422075_792186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422075 ⟨792186, by decide⟩ :=
  accepted_of_selected 13 422075 ⟨792186, by decide⟩ ⟨13, 2, 0, 792186, 422075, 673, 16384⟩
    (by decide) selected_cut_31112

theorem unmarked_context_12_105518_792187 : frontier 9 ⟨792187, by decide⟩
    (prefixCache 12 105518) (prefixPartial 12 105518) = false := by
  decide +kernel

theorem node_context_12_105518_792187 : EJMOriginalGlobalDAGData.nodes 9 ⟨792187, by decide⟩ =
    .split (coordinate 12) (![⟨792128, by decide⟩,⟨792161, by decide⟩,⟨792180, by decide⟩,⟨792186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105518_792187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105518 ⟨792187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105518
    ⟨792187, by decide⟩ (by decide) (![⟨792128, by decide⟩,⟨792161, by decide⟩,⟨792180, by decide⟩,⟨792186, by decide⟩]) unmarked_context_12_105518_792187 node_context_12_105518_792187
  intro a
  fin_cases a
  · exact context_13_422072_792128
  · exact context_13_422073_792161
  · exact context_13_422074_792180
  · exact context_13_422075_792186

theorem selected_cut_31113 : selected 8 ⟨792199, by decide⟩
    (prefixPartial 13 422076) = some ⟨13, 2, 0, 792199, 422076, 549, 16384⟩ := by
  decide +kernel

theorem context_13_422076_792199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422076 ⟨792199, by decide⟩ :=
  accepted_of_selected 13 422076 ⟨792199, by decide⟩ ⟨13, 2, 0, 792199, 422076, 549, 16384⟩
    (by decide) selected_cut_31113

theorem selected_cut_31114 : selected 8 ⟨792223, by decide⟩
    (prefixPartial 13 422077) = some ⟨13, 2, 0, 792223, 422077, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_422077_792223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422077 ⟨792223, by decide⟩ :=
  accepted_of_selected 13 422077 ⟨792223, by decide⟩ ⟨13, 2, 0, 792223, 422077, 2065, 16384⟩
    (by decide) selected_cut_31114

theorem selected_cut_31115 : selected 8 ⟨792252, by decide⟩
    (prefixPartial 13 422078) = some ⟨13, 2, 0, 792252, 422078, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_422078_792252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422078 ⟨792252, by decide⟩ :=
  accepted_of_selected 13 422078 ⟨792252, by decide⟩ ⟨13, 2, 0, 792252, 422078, 1345, 16384⟩
    (by decide) selected_cut_31115

theorem selected_cut_31116 : selected 8 ⟨792256, by decide⟩
    (prefixPartial 13 422079) = some ⟨13, 2, 0, 792256, 422079, 685, 16384⟩ := by
  decide +kernel

theorem context_13_422079_792256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422079 ⟨792256, by decide⟩ :=
  accepted_of_selected 13 422079 ⟨792256, by decide⟩ ⟨13, 2, 0, 792256, 422079, 685, 16384⟩
    (by decide) selected_cut_31116

theorem unmarked_context_12_105519_792257 : frontier 9 ⟨792257, by decide⟩
    (prefixCache 12 105519) (prefixPartial 12 105519) = false := by
  decide +kernel

theorem node_context_12_105519_792257 : EJMOriginalGlobalDAGData.nodes 9 ⟨792257, by decide⟩ =
    .split (coordinate 12) (![⟨792199, by decide⟩,⟨792223, by decide⟩,⟨792252, by decide⟩,⟨792256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105519_792257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105519 ⟨792257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105519
    ⟨792257, by decide⟩ (by decide) (![⟨792199, by decide⟩,⟨792223, by decide⟩,⟨792252, by decide⟩,⟨792256, by decide⟩]) unmarked_context_12_105519_792257 node_context_12_105519_792257
  intro a
  fin_cases a
  · exact context_13_422076_792199
  · exact context_13_422077_792223
  · exact context_13_422078_792252
  · exact context_13_422079_792256

theorem unmarked_context_11_26379_792258 : frontier 10 ⟨792258, by decide⟩
    (prefixCache 11 26379) (prefixPartial 11 26379) = false := by
  decide +kernel

theorem node_context_11_26379_792258 : EJMOriginalGlobalDAGData.nodes 10 ⟨792258, by decide⟩ =
    .split (coordinate 11) (![⟨792033, by decide⟩,⟨792113, by decide⟩,⟨792187, by decide⟩,⟨792257, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26379_792258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26379 ⟨792258, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26379
    ⟨792258, by decide⟩ (by decide) (![⟨792033, by decide⟩,⟨792113, by decide⟩,⟨792187, by decide⟩,⟨792257, by decide⟩]) unmarked_context_11_26379_792258 node_context_11_26379_792258
  intro a
  fin_cases a
  · exact context_12_105516_792033
  · exact context_12_105517_792113
  · exact context_12_105518_792187
  · exact context_12_105519_792257

theorem unmarked_context_10_6594_792259 : frontier 11 ⟨792259, by decide⟩
    (prefixCache 10 6594) (prefixPartial 10 6594) = false := by
  decide +kernel

theorem node_context_10_6594_792259 : EJMOriginalGlobalDAGData.nodes 11 ⟨792259, by decide⟩ =
    .split (coordinate 10) (![⟨791188, by decide⟩,⟨791605, by decide⟩,⟨791962, by decide⟩,⟨792258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6594_792259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6594 ⟨792259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6594
    ⟨792259, by decide⟩ (by decide) (![⟨791188, by decide⟩,⟨791605, by decide⟩,⟨791962, by decide⟩,⟨792258, by decide⟩]) unmarked_context_10_6594_792259 node_context_10_6594_792259
  intro a
  fin_cases a
  · exact context_11_26376_791188
  · exact context_11_26377_791605
  · exact context_11_26378_791962
  · exact context_11_26379_792258

theorem selected_cut_31117 : selected 9 ⟨792260, by decide⟩
    (prefixPartial 12 105520) = some ⟨12, 1, 0, 792260, 105520, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105520_792260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105520 ⟨792260, by decide⟩ :=
  accepted_of_selected 12 105520 ⟨792260, by decide⟩ ⟨12, 1, 0, 792260, 105520, 1, 65536⟩
    (by decide) selected_cut_31117

theorem selected_cut_31118 : selected 8 ⟨792276, by decide⟩
    (prefixPartial 13 422084) = some ⟨13, 2, 0, 792276, 422084, 573, 16384⟩ := by
  decide +kernel

theorem context_13_422084_792276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422084 ⟨792276, by decide⟩ :=
  accepted_of_selected 13 422084 ⟨792276, by decide⟩ ⟨13, 2, 0, 792276, 422084, 573, 16384⟩
    (by decide) selected_cut_31118

theorem selected_cut_31119 : selected 8 ⟨792334, by decide⟩
    (prefixPartial 13 422085) = some ⟨13, 2, 0, 792334, 422085, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_422085_792334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422085 ⟨792334, by decide⟩ :=
  accepted_of_selected 13 422085 ⟨792334, by decide⟩ ⟨13, 2, 0, 792334, 422085, 1801, 16384⟩
    (by decide) selected_cut_31119

theorem selected_cut_31120 : selected 8 ⟨792391, by decide⟩
    (prefixPartial 13 422086) = some ⟨13, 2, 0, 792391, 422086, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_422086_792391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422086 ⟨792391, by decide⟩ :=
  accepted_of_selected 13 422086 ⟨792391, by decide⟩ ⟨13, 2, 0, 792391, 422086, 1137, 16384⟩
    (by decide) selected_cut_31120

theorem selected_cut_31121 : selected 8 ⟨792395, by decide⟩
    (prefixPartial 13 422087) = some ⟨13, 2, 0, 792395, 422087, 605, 16384⟩ := by
  decide +kernel

theorem context_13_422087_792395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422087 ⟨792395, by decide⟩ :=
  accepted_of_selected 13 422087 ⟨792395, by decide⟩ ⟨13, 2, 0, 792395, 422087, 605, 16384⟩
    (by decide) selected_cut_31121

theorem unmarked_context_12_105521_792396 : frontier 9 ⟨792396, by decide⟩
    (prefixCache 12 105521) (prefixPartial 12 105521) = false := by
  decide +kernel

theorem node_context_12_105521_792396 : EJMOriginalGlobalDAGData.nodes 9 ⟨792396, by decide⟩ =
    .split (coordinate 12) (![⟨792276, by decide⟩,⟨792334, by decide⟩,⟨792391, by decide⟩,⟨792395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105521_792396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105521 ⟨792396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105521
    ⟨792396, by decide⟩ (by decide) (![⟨792276, by decide⟩,⟨792334, by decide⟩,⟨792391, by decide⟩,⟨792395, by decide⟩]) unmarked_context_12_105521_792396 node_context_12_105521_792396
  intro a
  fin_cases a
  · exact context_13_422084_792276
  · exact context_13_422085_792334
  · exact context_13_422086_792391
  · exact context_13_422087_792395

theorem selected_cut_31122 : selected 9 ⟨792500, by decide⟩
    (prefixPartial 12 105522) = some ⟨12, 2, 0, 792500, 105522, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_105522_792500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105522 ⟨792500, by decide⟩ :=
  accepted_of_selected 12 105522 ⟨792500, by decide⟩ ⟨12, 2, 0, 792500, 105522, 4001, 65536⟩
    (by decide) selected_cut_31122

theorem selected_cut_31123 : selected 8 ⟨792509, by decide⟩
    (prefixPartial 13 422092) = some ⟨13, 2, 0, 792509, 422092, 453, 16384⟩ := by
  decide +kernel

theorem context_13_422092_792509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422092 ⟨792509, by decide⟩ :=
  accepted_of_selected 13 422092 ⟨792509, by decide⟩ ⟨13, 2, 0, 792509, 422092, 453, 16384⟩
    (by decide) selected_cut_31123

theorem selected_cut_31124 : selected 8 ⟨792558, by decide⟩
    (prefixPartial 13 422093) = some ⟨13, 2, 0, 792558, 422093, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_422093_792558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422093 ⟨792558, by decide⟩ :=
  accepted_of_selected 13 422093 ⟨792558, by decide⟩ ⟨13, 2, 0, 792558, 422093, 1889, 16384⟩
    (by decide) selected_cut_31124

theorem selected_cut_31125 : selected 8 ⟨792596, by decide⟩
    (prefixPartial 13 422094) = some ⟨13, 2, 0, 792596, 422094, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_422094_792596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422094 ⟨792596, by decide⟩ :=
  accepted_of_selected 13 422094 ⟨792596, by decide⟩ ⟨13, 2, 0, 792596, 422094, 1245, 16384⟩
    (by decide) selected_cut_31125

theorem selected_cut_31126 : selected 8 ⟨792600, by decide⟩
    (prefixPartial 13 422095) = some ⟨13, 2, 0, 792600, 422095, 665, 16384⟩ := by
  decide +kernel

theorem context_13_422095_792600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422095 ⟨792600, by decide⟩ :=
  accepted_of_selected 13 422095 ⟨792600, by decide⟩ ⟨13, 2, 0, 792600, 422095, 665, 16384⟩
    (by decide) selected_cut_31126

theorem unmarked_context_12_105523_792601 : frontier 9 ⟨792601, by decide⟩
    (prefixCache 12 105523) (prefixPartial 12 105523) = false := by
  decide +kernel

theorem node_context_12_105523_792601 : EJMOriginalGlobalDAGData.nodes 9 ⟨792601, by decide⟩ =
    .split (coordinate 12) (![⟨792509, by decide⟩,⟨792558, by decide⟩,⟨792596, by decide⟩,⟨792600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105523_792601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105523 ⟨792601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105523
    ⟨792601, by decide⟩ (by decide) (![⟨792509, by decide⟩,⟨792558, by decide⟩,⟨792596, by decide⟩,⟨792600, by decide⟩]) unmarked_context_12_105523_792601 node_context_12_105523_792601
  intro a
  fin_cases a
  · exact context_13_422092_792509
  · exact context_13_422093_792558
  · exact context_13_422094_792596
  · exact context_13_422095_792600

theorem unmarked_context_11_26380_792602 : frontier 10 ⟨792602, by decide⟩
    (prefixCache 11 26380) (prefixPartial 11 26380) = false := by
  decide +kernel

theorem node_context_11_26380_792602 : EJMOriginalGlobalDAGData.nodes 10 ⟨792602, by decide⟩ =
    .split (coordinate 11) (![⟨792260, by decide⟩,⟨792396, by decide⟩,⟨792500, by decide⟩,⟨792601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26380_792602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26380 ⟨792602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26380
    ⟨792602, by decide⟩ (by decide) (![⟨792260, by decide⟩,⟨792396, by decide⟩,⟨792500, by decide⟩,⟨792601, by decide⟩]) unmarked_context_11_26380_792602 node_context_11_26380_792602
  intro a
  fin_cases a
  · exact context_12_105520_792260
  · exact context_12_105521_792396
  · exact context_12_105522_792500
  · exact context_12_105523_792601

theorem selected_cut_31127 : selected 9 ⟨792698, by decide⟩
    (prefixPartial 12 105524) = some ⟨12, 2, 0, 792698, 105524, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_105524_792698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105524 ⟨792698, by decide⟩ :=
  accepted_of_selected 12 105524 ⟨792698, by decide⟩ ⟨12, 2, 0, 792698, 105524, 3953, 65536⟩
    (by decide) selected_cut_31127

theorem selected_cut_31128 : selected 9 ⟨792792, by decide⟩
    (prefixPartial 12 105525) = some ⟨12, 2, 0, 792792, 105525, 3685, 65536⟩ := by
  decide +kernel

theorem context_12_105525_792792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105525 ⟨792792, by decide⟩ :=
  accepted_of_selected 12 105525 ⟨792792, by decide⟩ ⟨12, 2, 0, 792792, 105525, 3685, 65536⟩
    (by decide) selected_cut_31128

theorem selected_cut_31129 : selected 9 ⟨792870, by decide⟩
    (prefixPartial 12 105526) = some ⟨12, 2, 0, 792870, 105526, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_105526_792870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105526 ⟨792870, by decide⟩ :=
  accepted_of_selected 12 105526 ⟨792870, by decide⟩ ⟨12, 2, 0, 792870, 105526, 3917, 65536⟩
    (by decide) selected_cut_31129

theorem selected_cut_31130 : selected 8 ⟨792880, by decide⟩
    (prefixPartial 13 422108) = some ⟨13, 2, 0, 792880, 422108, 313, 16384⟩ := by
  decide +kernel

theorem context_13_422108_792880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422108 ⟨792880, by decide⟩ :=
  accepted_of_selected 13 422108 ⟨792880, by decide⟩ ⟨13, 2, 0, 792880, 422108, 313, 16384⟩
    (by decide) selected_cut_31130

theorem selected_cut_31131 : selected 8 ⟨792948, by decide⟩
    (prefixPartial 13 422109) = some ⟨13, 2, 0, 792948, 422109, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_422109_792948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422109 ⟨792948, by decide⟩ :=
  accepted_of_selected 13 422109 ⟨792948, by decide⟩ ⟨13, 2, 0, 792948, 422109, 2213, 16384⟩
    (by decide) selected_cut_31131

theorem selected_cut_31132 : selected 8 ⟨792984, by decide⟩
    (prefixPartial 13 422110) = some ⟨13, 2, 0, 792984, 422110, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_422110_792984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422110 ⟨792984, by decide⟩ :=
  accepted_of_selected 13 422110 ⟨792984, by decide⟩ ⟨13, 2, 0, 792984, 422110, 1253, 16384⟩
    (by decide) selected_cut_31132

theorem selected_cut_31133 : selected 8 ⟨792988, by decide⟩
    (prefixPartial 13 422111) = some ⟨13, 2, 0, 792988, 422111, 565, 16384⟩ := by
  decide +kernel

theorem context_13_422111_792988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422111 ⟨792988, by decide⟩ :=
  accepted_of_selected 13 422111 ⟨792988, by decide⟩ ⟨13, 2, 0, 792988, 422111, 565, 16384⟩
    (by decide) selected_cut_31133

theorem unmarked_context_12_105527_792989 : frontier 9 ⟨792989, by decide⟩
    (prefixCache 12 105527) (prefixPartial 12 105527) = false := by
  decide +kernel

theorem node_context_12_105527_792989 : EJMOriginalGlobalDAGData.nodes 9 ⟨792989, by decide⟩ =
    .split (coordinate 12) (![⟨792880, by decide⟩,⟨792948, by decide⟩,⟨792984, by decide⟩,⟨792988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105527_792989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105527 ⟨792989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105527
    ⟨792989, by decide⟩ (by decide) (![⟨792880, by decide⟩,⟨792948, by decide⟩,⟨792984, by decide⟩,⟨792988, by decide⟩]) unmarked_context_12_105527_792989 node_context_12_105527_792989
  intro a
  fin_cases a
  · exact context_13_422108_792880
  · exact context_13_422109_792948
  · exact context_13_422110_792984
  · exact context_13_422111_792988

theorem unmarked_context_11_26381_792990 : frontier 10 ⟨792990, by decide⟩
    (prefixCache 11 26381) (prefixPartial 11 26381) = false := by
  decide +kernel

theorem node_context_11_26381_792990 : EJMOriginalGlobalDAGData.nodes 10 ⟨792990, by decide⟩ =
    .split (coordinate 11) (![⟨792698, by decide⟩,⟨792792, by decide⟩,⟨792870, by decide⟩,⟨792989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26381_792990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26381 ⟨792990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26381
    ⟨792990, by decide⟩ (by decide) (![⟨792698, by decide⟩,⟨792792, by decide⟩,⟨792870, by decide⟩,⟨792989, by decide⟩]) unmarked_context_11_26381_792990 node_context_11_26381_792990
  intro a
  fin_cases a
  · exact context_12_105524_792698
  · exact context_12_105525_792792
  · exact context_12_105526_792870
  · exact context_12_105527_792989

theorem selected_cut_31134 : selected 9 ⟨793068, by decide⟩
    (prefixPartial 12 105528) = some ⟨12, 2, 0, 793068, 105528, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_105528_793068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105528 ⟨793068, by decide⟩ :=
  accepted_of_selected 12 105528 ⟨793068, by decide⟩ ⟨12, 2, 0, 793068, 105528, 3677, 65536⟩
    (by decide) selected_cut_31134

theorem selected_cut_31135 : selected 9 ⟨793139, by decide⟩
    (prefixPartial 12 105529) = some ⟨12, 2, 0, 793139, 105529, 3741, 65536⟩ := by
  decide +kernel

theorem context_12_105529_793139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105529 ⟨793139, by decide⟩ :=
  accepted_of_selected 12 105529 ⟨793139, by decide⟩ ⟨12, 2, 0, 793139, 105529, 3741, 65536⟩
    (by decide) selected_cut_31135

theorem selected_cut_31136 : selected 9 ⟨793206, by decide⟩
    (prefixPartial 12 105530) = some ⟨12, 2, 0, 793206, 105530, 3325, 65536⟩ := by
  decide +kernel

theorem context_12_105530_793206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105530 ⟨793206, by decide⟩ :=
  accepted_of_selected 12 105530 ⟨793206, by decide⟩ ⟨12, 2, 0, 793206, 105530, 3325, 65536⟩
    (by decide) selected_cut_31136

theorem selected_cut_31137 : selected 9 ⟨793292, by decide⟩
    (prefixPartial 12 105531) = some ⟨12, 2, 0, 793292, 105531, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_105531_793292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105531 ⟨793292, by decide⟩ :=
  accepted_of_selected 12 105531 ⟨793292, by decide⟩ ⟨12, 2, 0, 793292, 105531, 3861, 65536⟩
    (by decide) selected_cut_31137

theorem unmarked_context_11_26382_793293 : frontier 10 ⟨793293, by decide⟩
    (prefixCache 11 26382) (prefixPartial 11 26382) = false := by
  decide +kernel

theorem node_context_11_26382_793293 : EJMOriginalGlobalDAGData.nodes 10 ⟨793293, by decide⟩ =
    .split (coordinate 11) (![⟨793068, by decide⟩,⟨793139, by decide⟩,⟨793206, by decide⟩,⟨793292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26382_793293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26382 ⟨793293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26382
    ⟨793293, by decide⟩ (by decide) (![⟨793068, by decide⟩,⟨793139, by decide⟩,⟨793206, by decide⟩,⟨793292, by decide⟩]) unmarked_context_11_26382_793293 node_context_11_26382_793293
  intro a
  fin_cases a
  · exact context_12_105528_793068
  · exact context_12_105529_793139
  · exact context_12_105530_793206
  · exact context_12_105531_793292

theorem selected_cut_31138 : selected 10 ⟨793294, by decide⟩
    (prefixPartial 11 26383) = some ⟨11, 1, 0, 793294, 26383, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26383_793294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26383 ⟨793294, by decide⟩ :=
  accepted_of_selected 11 26383 ⟨793294, by decide⟩ ⟨11, 1, 0, 793294, 26383, 1, 262144⟩
    (by decide) selected_cut_31138

theorem unmarked_context_10_6595_793295 : frontier 11 ⟨793295, by decide⟩
    (prefixCache 10 6595) (prefixPartial 10 6595) = false := by
  decide +kernel

theorem node_context_10_6595_793295 : EJMOriginalGlobalDAGData.nodes 11 ⟨793295, by decide⟩ =
    .split (coordinate 10) (![⟨792602, by decide⟩,⟨792990, by decide⟩,⟨793293, by decide⟩,⟨793294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6595_793295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6595 ⟨793295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6595
    ⟨793295, by decide⟩ (by decide) (![⟨792602, by decide⟩,⟨792990, by decide⟩,⟨793293, by decide⟩,⟨793294, by decide⟩]) unmarked_context_10_6595_793295 node_context_10_6595_793295
  intro a
  fin_cases a
  · exact context_11_26380_792602
  · exact context_11_26381_792990
  · exact context_11_26382_793293
  · exact context_11_26383_793294

theorem unmarked_context_9_1648_793296 : frontier 12 ⟨793296, by decide⟩
    (prefixCache 9 1648) (prefixPartial 9 1648) = false := by
  decide +kernel

theorem node_context_9_1648_793296 : EJMOriginalGlobalDAGData.nodes 12 ⟨793296, by decide⟩ =
    .split (coordinate 9) (![⟨789342, by decide⟩,⟨790887, by decide⟩,⟨792259, by decide⟩,⟨793295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1648_793296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1648 ⟨793296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1648
    ⟨793296, by decide⟩ (by decide) (![⟨789342, by decide⟩,⟨790887, by decide⟩,⟨792259, by decide⟩,⟨793295, by decide⟩]) unmarked_context_9_1648_793296 node_context_9_1648_793296
  intro a
  fin_cases a
  · exact context_10_6592_789342
  · exact context_10_6593_790887
  · exact context_10_6594_792259
  · exact context_10_6595_793295

theorem selected_cut_31139 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 6596) = some ⟨10, 1, 0, 793297, 6596, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6596_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6596 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 6596 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 6596, 1, 1048576⟩
    (by decide) selected_cut_31139

theorem selected_cut_31140 : selected 9 ⟨793435, by decide⟩
    (prefixPartial 12 105552) = some ⟨12, 2, 0, 793435, 105552, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_105552_793435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105552 ⟨793435, by decide⟩ :=
  accepted_of_selected 12 105552 ⟨793435, by decide⟩ ⟨12, 2, 0, 793435, 105552, 1233, 65536⟩
    (by decide) selected_cut_31140

theorem selected_cut_31141 : selected 9 ⟨793554, by decide⟩
    (prefixPartial 12 105553) = some ⟨12, 2, 0, 793554, 105553, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_105553_793554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105553 ⟨793554, by decide⟩ :=
  accepted_of_selected 12 105553 ⟨793554, by decide⟩ ⟨12, 2, 0, 793554, 105553, 3453, 65536⟩
    (by decide) selected_cut_31141

theorem selected_cut_31142 : selected 9 ⟨793624, by decide⟩
    (prefixPartial 12 105554) = some ⟨12, 2, 0, 793624, 105554, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_105554_793624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105554 ⟨793624, by decide⟩ :=
  accepted_of_selected 12 105554 ⟨793624, by decide⟩ ⟨12, 2, 0, 793624, 105554, 3485, 65536⟩
    (by decide) selected_cut_31142

theorem selected_cut_31143 : selected 9 ⟨793698, by decide⟩
    (prefixPartial 12 105555) = some ⟨12, 2, 0, 793698, 105555, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_105555_793698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105555 ⟨793698, by decide⟩ :=
  accepted_of_selected 12 105555 ⟨793698, by decide⟩ ⟨12, 2, 0, 793698, 105555, 3417, 65536⟩
    (by decide) selected_cut_31143

theorem unmarked_context_11_26388_793699 : frontier 10 ⟨793699, by decide⟩
    (prefixCache 11 26388) (prefixPartial 11 26388) = false := by
  decide +kernel

theorem node_context_11_26388_793699 : EJMOriginalGlobalDAGData.nodes 10 ⟨793699, by decide⟩ =
    .split (coordinate 11) (![⟨793435, by decide⟩,⟨793554, by decide⟩,⟨793624, by decide⟩,⟨793698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26388_793699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26388 ⟨793699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26388
    ⟨793699, by decide⟩ (by decide) (![⟨793435, by decide⟩,⟨793554, by decide⟩,⟨793624, by decide⟩,⟨793698, by decide⟩]) unmarked_context_11_26388_793699 node_context_11_26388_793699
  intro a
  fin_cases a
  · exact context_12_105552_793435
  · exact context_12_105553_793554
  · exact context_12_105554_793624
  · exact context_12_105555_793698

theorem selected_cut_31144 : selected 9 ⟨14169, by decide⟩
    (prefixPartial 12 105556) = some ⟨12, 1, 0, 14169, 105556, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105556_14169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105556 ⟨14169, by decide⟩ :=
  accepted_of_selected 12 105556 ⟨14169, by decide⟩ ⟨12, 1, 0, 14169, 105556, 1, 65536⟩
    (by decide) selected_cut_31144

theorem selected_cut_31145 : selected 9 ⟨793761, by decide⟩
    (prefixPartial 12 105557) = some ⟨12, 2, 0, 793761, 105557, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_105557_793761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105557 ⟨793761, by decide⟩ :=
  accepted_of_selected 12 105557 ⟨793761, by decide⟩ ⟨12, 2, 0, 793761, 105557, 1797, 65536⟩
    (by decide) selected_cut_31145

theorem selected_cut_31146 : selected 9 ⟨793838, by decide⟩
    (prefixPartial 12 105558) = some ⟨12, 2, 0, 793838, 105558, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_105558_793838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105558 ⟨793838, by decide⟩ :=
  accepted_of_selected 12 105558 ⟨793838, by decide⟩ ⟨12, 2, 0, 793838, 105558, 3137, 65536⟩
    (by decide) selected_cut_31146

theorem selected_cut_31147 : selected 9 ⟨793906, by decide⟩
    (prefixPartial 12 105559) = some ⟨12, 2, 0, 793906, 105559, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_105559_793906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105559 ⟨793906, by decide⟩ :=
  accepted_of_selected 12 105559 ⟨793906, by decide⟩ ⟨12, 2, 0, 793906, 105559, 3197, 65536⟩
    (by decide) selected_cut_31147

theorem unmarked_context_11_26389_793907 : frontier 10 ⟨793907, by decide⟩
    (prefixCache 11 26389) (prefixPartial 11 26389) = false := by
  decide +kernel

theorem node_context_11_26389_793907 : EJMOriginalGlobalDAGData.nodes 10 ⟨793907, by decide⟩ =
    .split (coordinate 11) (![⟨14169, by decide⟩,⟨793761, by decide⟩,⟨793838, by decide⟩,⟨793906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26389_793907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26389 ⟨793907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26389
    ⟨793907, by decide⟩ (by decide) (![⟨14169, by decide⟩,⟨793761, by decide⟩,⟨793838, by decide⟩,⟨793906, by decide⟩]) unmarked_context_11_26389_793907 node_context_11_26389_793907
  intro a
  fin_cases a
  · exact context_12_105556_14169
  · exact context_12_105557_793761
  · exact context_12_105558_793838
  · exact context_12_105559_793906

theorem selected_cut_31148 : selected 9 ⟨14169, by decide⟩
    (prefixPartial 12 105560) = some ⟨12, 1, 0, 14169, 105560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105560_14169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105560 ⟨14169, by decide⟩ :=
  accepted_of_selected 12 105560 ⟨14169, by decide⟩ ⟨12, 1, 0, 14169, 105560, 1, 65536⟩
    (by decide) selected_cut_31148

theorem selected_cut_31149 : selected 9 ⟨14169, by decide⟩
    (prefixPartial 12 105561) = some ⟨12, 1, 0, 14169, 105561, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105561_14169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105561 ⟨14169, by decide⟩ :=
  accepted_of_selected 12 105561 ⟨14169, by decide⟩ ⟨12, 1, 0, 14169, 105561, 1, 65536⟩
    (by decide) selected_cut_31149

theorem selected_cut_31150 : selected 9 ⟨793962, by decide⟩
    (prefixPartial 12 105562) = some ⟨12, 2, 0, 793962, 105562, 2997, 65536⟩ := by
  decide +kernel

theorem context_12_105562_793962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105562 ⟨793962, by decide⟩ :=
  accepted_of_selected 12 105562 ⟨793962, by decide⟩ ⟨12, 2, 0, 793962, 105562, 2997, 65536⟩
    (by decide) selected_cut_31150

theorem selected_cut_31151 : selected 9 ⟨794022, by decide⟩
    (prefixPartial 12 105563) = some ⟨12, 2, 0, 794022, 105563, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_105563_794022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105563 ⟨794022, by decide⟩ :=
  accepted_of_selected 12 105563 ⟨794022, by decide⟩ ⟨12, 2, 0, 794022, 105563, 1937, 65536⟩
    (by decide) selected_cut_31151

theorem unmarked_context_11_26390_794023 : frontier 10 ⟨794023, by decide⟩
    (prefixCache 11 26390) (prefixPartial 11 26390) = false := by
  decide +kernel

theorem node_context_11_26390_794023 : EJMOriginalGlobalDAGData.nodes 10 ⟨794023, by decide⟩ =
    .split (coordinate 11) (![⟨14169, by decide⟩,⟨14169, by decide⟩,⟨793962, by decide⟩,⟨794022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26390_794023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26390 ⟨794023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26390
    ⟨794023, by decide⟩ (by decide) (![⟨14169, by decide⟩,⟨14169, by decide⟩,⟨793962, by decide⟩,⟨794022, by decide⟩]) unmarked_context_11_26390_794023 node_context_11_26390_794023
  intro a
  fin_cases a
  · exact context_12_105560_14169
  · exact context_12_105561_14169
  · exact context_12_105562_793962
  · exact context_12_105563_794022

theorem selected_cut_31152 : selected 10 ⟨794064, by decide⟩
    (prefixPartial 11 26391) = some ⟨11, 2, 0, 794064, 26391, 1685, 262144⟩ := by
  decide +kernel

theorem context_11_26391_794064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26391 ⟨794064, by decide⟩ :=
  accepted_of_selected 11 26391 ⟨794064, by decide⟩ ⟨11, 2, 0, 794064, 26391, 1685, 262144⟩
    (by decide) selected_cut_31152

theorem unmarked_context_10_6597_794065 : frontier 11 ⟨794065, by decide⟩
    (prefixCache 10 6597) (prefixPartial 10 6597) = false := by
  decide +kernel

theorem node_context_10_6597_794065 : EJMOriginalGlobalDAGData.nodes 11 ⟨794065, by decide⟩ =
    .split (coordinate 10) (![⟨793699, by decide⟩,⟨793907, by decide⟩,⟨794023, by decide⟩,⟨794064, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6597_794065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6597 ⟨794065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6597
    ⟨794065, by decide⟩ (by decide) (![⟨793699, by decide⟩,⟨793907, by decide⟩,⟨794023, by decide⟩,⟨794064, by decide⟩]) unmarked_context_10_6597_794065 node_context_10_6597_794065
  intro a
  fin_cases a
  · exact context_11_26388_793699
  · exact context_11_26389_793907
  · exact context_11_26390_794023
  · exact context_11_26391_794064

theorem selected_cut_31153 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 422272) = some ⟨13, 1, 0, 3444, 422272, 1, 16384⟩ := by
  decide +kernel

theorem context_13_422272_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422272 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 422272 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 422272, 1, 16384⟩
    (by decide) selected_cut_31153

theorem selected_cut_31154 : selected 8 ⟨794131, by decide⟩
    (prefixPartial 13 422273) = some ⟨13, 2, 0, 794131, 422273, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_422273_794131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422273 ⟨794131, by decide⟩ :=
  accepted_of_selected 13 422273 ⟨794131, by decide⟩ ⟨13, 2, 0, 794131, 422273, 2065, 16384⟩
    (by decide) selected_cut_31154

theorem selected_cut_31155 : selected 8 ⟨794213, by decide⟩
    (prefixPartial 13 422274) = some ⟨13, 2, 0, 794213, 422274, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_422274_794213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422274 ⟨794213, by decide⟩ :=
  accepted_of_selected 13 422274 ⟨794213, by decide⟩ ⟨13, 2, 0, 794213, 422274, 1489, 16384⟩
    (by decide) selected_cut_31155

theorem selected_cut_31156 : selected 8 ⟨794238, by decide⟩
    (prefixPartial 13 422275) = some ⟨13, 2, 0, 794238, 422275, 889, 16384⟩ := by
  decide +kernel

theorem context_13_422275_794238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422275 ⟨794238, by decide⟩ :=
  accepted_of_selected 13 422275 ⟨794238, by decide⟩ ⟨13, 2, 0, 794238, 422275, 889, 16384⟩
    (by decide) selected_cut_31156

theorem unmarked_context_12_105568_794239 : frontier 9 ⟨794239, by decide⟩
    (prefixCache 12 105568) (prefixPartial 12 105568) = false := by
  decide +kernel

theorem node_context_12_105568_794239 : EJMOriginalGlobalDAGData.nodes 9 ⟨794239, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨794131, by decide⟩,⟨794213, by decide⟩,⟨794238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105568_794239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105568 ⟨794239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105568
    ⟨794239, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨794131, by decide⟩,⟨794213, by decide⟩,⟨794238, by decide⟩]) unmarked_context_12_105568_794239 node_context_12_105568_794239
  intro a
  fin_cases a
  · exact context_13_422272_3444
  · exact context_13_422273_794131
  · exact context_13_422274_794213
  · exact context_13_422275_794238

theorem selected_cut_31157 : selected 9 ⟨794308, by decide⟩
    (prefixPartial 12 105569) = some ⟨12, 2, 0, 794308, 105569, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_105569_794308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105569 ⟨794308, by decide⟩ :=
  accepted_of_selected 12 105569 ⟨794308, by decide⟩ ⟨12, 2, 0, 794308, 105569, 2821, 65536⟩
    (by decide) selected_cut_31157

theorem selected_cut_31158 : selected 9 ⟨794365, by decide⟩
    (prefixPartial 12 105570) = some ⟨12, 2, 0, 794365, 105570, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_105570_794365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105570 ⟨794365, by decide⟩ :=
  accepted_of_selected 12 105570 ⟨794365, by decide⟩ ⟨12, 2, 0, 794365, 105570, 2881, 65536⟩
    (by decide) selected_cut_31158

theorem selected_cut_31159 : selected 9 ⟨794415, by decide⟩
    (prefixPartial 12 105571) = some ⟨12, 2, 0, 794415, 105571, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_105571_794415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105571 ⟨794415, by decide⟩ :=
  accepted_of_selected 12 105571 ⟨794415, by decide⟩ ⟨12, 2, 0, 794415, 105571, 2805, 65536⟩
    (by decide) selected_cut_31159

theorem unmarked_context_11_26392_794416 : frontier 10 ⟨794416, by decide⟩
    (prefixCache 11 26392) (prefixPartial 11 26392) = false := by
  decide +kernel

theorem node_context_11_26392_794416 : EJMOriginalGlobalDAGData.nodes 10 ⟨794416, by decide⟩ =
    .split (coordinate 11) (![⟨794239, by decide⟩,⟨794308, by decide⟩,⟨794365, by decide⟩,⟨794415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26392_794416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26392 ⟨794416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26392
    ⟨794416, by decide⟩ (by decide) (![⟨794239, by decide⟩,⟨794308, by decide⟩,⟨794365, by decide⟩,⟨794415, by decide⟩]) unmarked_context_11_26392_794416 node_context_11_26392_794416
  intro a
  fin_cases a
  · exact context_12_105568_794239
  · exact context_12_105569_794308
  · exact context_12_105570_794365
  · exact context_12_105571_794415

theorem selected_cut_31160 : selected 9 ⟨794482, by decide⟩
    (prefixPartial 12 105572) = some ⟨12, 2, 0, 794482, 105572, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_105572_794482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105572 ⟨794482, by decide⟩ :=
  accepted_of_selected 12 105572 ⟨794482, by decide⟩ ⟨12, 2, 0, 794482, 105572, 2929, 65536⟩
    (by decide) selected_cut_31160

theorem selected_cut_31161 : selected 9 ⟨794530, by decide⟩
    (prefixPartial 12 105573) = some ⟨12, 2, 0, 794530, 105573, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_105573_794530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105573 ⟨794530, by decide⟩ :=
  accepted_of_selected 12 105573 ⟨794530, by decide⟩ ⟨12, 2, 0, 794530, 105573, 2493, 65536⟩
    (by decide) selected_cut_31161

theorem selected_cut_31162 : selected 9 ⟨794590, by decide⟩
    (prefixPartial 12 105574) = some ⟨12, 2, 0, 794590, 105574, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_105574_794590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105574 ⟨794590, by decide⟩ :=
  accepted_of_selected 12 105574 ⟨794590, by decide⟩ ⟨12, 2, 0, 794590, 105574, 2777, 65536⟩
    (by decide) selected_cut_31162

theorem selected_cut_31163 : selected 9 ⟨794643, by decide⟩
    (prefixPartial 12 105575) = some ⟨12, 2, 0, 794643, 105575, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_105575_794643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105575 ⟨794643, by decide⟩ :=
  accepted_of_selected 12 105575 ⟨794643, by decide⟩ ⟨12, 2, 0, 794643, 105575, 2693, 65536⟩
    (by decide) selected_cut_31163

theorem unmarked_context_11_26393_794644 : frontier 10 ⟨794644, by decide⟩
    (prefixCache 11 26393) (prefixPartial 11 26393) = false := by
  decide +kernel

theorem node_context_11_26393_794644 : EJMOriginalGlobalDAGData.nodes 10 ⟨794644, by decide⟩ =
    .split (coordinate 11) (![⟨794482, by decide⟩,⟨794530, by decide⟩,⟨794590, by decide⟩,⟨794643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26393_794644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26393 ⟨794644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26393
    ⟨794644, by decide⟩ (by decide) (![⟨794482, by decide⟩,⟨794530, by decide⟩,⟨794590, by decide⟩,⟨794643, by decide⟩]) unmarked_context_11_26393_794644 node_context_11_26393_794644
  intro a
  fin_cases a
  · exact context_12_105572_794482
  · exact context_12_105573_794530
  · exact context_12_105574_794590
  · exact context_12_105575_794643

theorem selected_cut_31164 : selected 9 ⟨794698, by decide⟩
    (prefixPartial 12 105576) = some ⟨12, 2, 0, 794698, 105576, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_105576_794698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105576 ⟨794698, by decide⟩ :=
  accepted_of_selected 12 105576 ⟨794698, by decide⟩ ⟨12, 2, 0, 794698, 105576, 2721, 65536⟩
    (by decide) selected_cut_31164

theorem selected_cut_31165 : selected 9 ⟨794754, by decide⟩
    (prefixPartial 12 105577) = some ⟨12, 2, 0, 794754, 105577, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_105577_794754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105577 ⟨794754, by decide⟩ :=
  accepted_of_selected 12 105577 ⟨794754, by decide⟩ ⟨12, 2, 0, 794754, 105577, 2509, 65536⟩
    (by decide) selected_cut_31165

theorem selected_cut_31166 : selected 9 ⟨794800, by decide⟩
    (prefixPartial 12 105578) = some ⟨12, 2, 0, 794800, 105578, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_105578_794800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105578 ⟨794800, by decide⟩ :=
  accepted_of_selected 12 105578 ⟨794800, by decide⟩ ⟨12, 2, 0, 794800, 105578, 2417, 65536⟩
    (by decide) selected_cut_31166

theorem selected_cut_31167 : selected 9 ⟨794838, by decide⟩
    (prefixPartial 12 105579) = some ⟨12, 2, 0, 794838, 105579, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_105579_794838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105579 ⟨794838, by decide⟩ :=
  accepted_of_selected 12 105579 ⟨794838, by decide⟩ ⟨12, 2, 0, 794838, 105579, 2405, 65536⟩
    (by decide) selected_cut_31167

theorem unmarked_context_11_26394_794839 : frontier 10 ⟨794839, by decide⟩
    (prefixCache 11 26394) (prefixPartial 11 26394) = false := by
  decide +kernel

theorem node_context_11_26394_794839 : EJMOriginalGlobalDAGData.nodes 10 ⟨794839, by decide⟩ =
    .split (coordinate 11) (![⟨794698, by decide⟩,⟨794754, by decide⟩,⟨794800, by decide⟩,⟨794838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26394_794839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26394 ⟨794839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26394
    ⟨794839, by decide⟩ (by decide) (![⟨794698, by decide⟩,⟨794754, by decide⟩,⟨794800, by decide⟩,⟨794838, by decide⟩]) unmarked_context_11_26394_794839 node_context_11_26394_794839
  intro a
  fin_cases a
  · exact context_12_105576_794698
  · exact context_12_105577_794754
  · exact context_12_105578_794800
  · exact context_12_105579_794838

theorem selected_cut_31168 : selected 9 ⟨794885, by decide⟩
    (prefixPartial 12 105580) = some ⟨12, 2, 0, 794885, 105580, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_105580_794885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105580 ⟨794885, by decide⟩ :=
  accepted_of_selected 12 105580 ⟨794885, by decide⟩ ⟨12, 2, 0, 794885, 105580, 2209, 65536⟩
    (by decide) selected_cut_31168

theorem selected_cut_31169 : selected 9 ⟨794918, by decide⟩
    (prefixPartial 12 105581) = some ⟨12, 2, 0, 794918, 105581, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_105581_794918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105581 ⟨794918, by decide⟩ :=
  accepted_of_selected 12 105581 ⟨794918, by decide⟩ ⟨12, 2, 0, 794918, 105581, 2025, 65536⟩
    (by decide) selected_cut_31169

theorem selected_cut_31170 : selected 9 ⟨794950, by decide⟩
    (prefixPartial 12 105582) = some ⟨12, 2, 0, 794950, 105582, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_105582_794950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105582 ⟨794950, by decide⟩ :=
  accepted_of_selected 12 105582 ⟨794950, by decide⟩ ⟨12, 2, 0, 794950, 105582, 1985, 65536⟩
    (by decide) selected_cut_31170

theorem selected_cut_31171 : selected 9 ⟨794978, by decide⟩
    (prefixPartial 12 105583) = some ⟨12, 2, 0, 794978, 105583, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_105583_794978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105583 ⟨794978, by decide⟩ :=
  accepted_of_selected 12 105583 ⟨794978, by decide⟩ ⟨12, 2, 0, 794978, 105583, 1973, 65536⟩
    (by decide) selected_cut_31171

theorem unmarked_context_11_26395_794979 : frontier 10 ⟨794979, by decide⟩
    (prefixCache 11 26395) (prefixPartial 11 26395) = false := by
  decide +kernel

theorem node_context_11_26395_794979 : EJMOriginalGlobalDAGData.nodes 10 ⟨794979, by decide⟩ =
    .split (coordinate 11) (![⟨794885, by decide⟩,⟨794918, by decide⟩,⟨794950, by decide⟩,⟨794978, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26395_794979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26395 ⟨794979, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26395
    ⟨794979, by decide⟩ (by decide) (![⟨794885, by decide⟩,⟨794918, by decide⟩,⟨794950, by decide⟩,⟨794978, by decide⟩]) unmarked_context_11_26395_794979 node_context_11_26395_794979
  intro a
  fin_cases a
  · exact context_12_105580_794885
  · exact context_12_105581_794918
  · exact context_12_105582_794950
  · exact context_12_105583_794978

theorem unmarked_context_10_6598_794980 : frontier 11 ⟨794980, by decide⟩
    (prefixCache 10 6598) (prefixPartial 10 6598) = false := by
  decide +kernel

theorem node_context_10_6598_794980 : EJMOriginalGlobalDAGData.nodes 11 ⟨794980, by decide⟩ =
    .split (coordinate 10) (![⟨794416, by decide⟩,⟨794644, by decide⟩,⟨794839, by decide⟩,⟨794979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6598_794980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6598 ⟨794980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6598
    ⟨794980, by decide⟩ (by decide) (![⟨794416, by decide⟩,⟨794644, by decide⟩,⟨794839, by decide⟩,⟨794979, by decide⟩]) unmarked_context_10_6598_794980 node_context_10_6598_794980
  intro a
  fin_cases a
  · exact context_11_26392_794416
  · exact context_11_26393_794644
  · exact context_11_26394_794839
  · exact context_11_26395_794979

theorem selected_cut_31172 : selected 9 ⟨792260, by decide⟩
    (prefixPartial 12 105584) = some ⟨12, 1, 0, 792260, 105584, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105584_792260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105584 ⟨792260, by decide⟩ :=
  accepted_of_selected 12 105584 ⟨792260, by decide⟩ ⟨12, 1, 0, 792260, 105584, 1, 65536⟩
    (by decide) selected_cut_31172

theorem selected_cut_31173 : selected 9 ⟨795047, by decide⟩
    (prefixPartial 12 105585) = some ⟨12, 2, 0, 795047, 105585, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_105585_795047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105585 ⟨795047, by decide⟩ :=
  accepted_of_selected 12 105585 ⟨795047, by decide⟩ ⟨12, 2, 0, 795047, 105585, 1705, 65536⟩
    (by decide) selected_cut_31173

theorem selected_cut_31174 : selected 9 ⟨795082, by decide⟩
    (prefixPartial 12 105586) = some ⟨12, 2, 0, 795082, 105586, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_105586_795082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105586 ⟨795082, by decide⟩ :=
  accepted_of_selected 12 105586 ⟨795082, by decide⟩ ⟨12, 2, 0, 795082, 105586, 1593, 65536⟩
    (by decide) selected_cut_31174

theorem selected_cut_31175 : selected 9 ⟨795135, by decide⟩
    (prefixPartial 12 105587) = some ⟨12, 2, 0, 795135, 105587, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_105587_795135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105587 ⟨795135, by decide⟩ :=
  accepted_of_selected 12 105587 ⟨795135, by decide⟩ ⟨12, 2, 0, 795135, 105587, 1773, 65536⟩
    (by decide) selected_cut_31175

theorem unmarked_context_11_26396_795136 : frontier 10 ⟨795136, by decide⟩
    (prefixCache 11 26396) (prefixPartial 11 26396) = false := by
  decide +kernel

theorem node_context_11_26396_795136 : EJMOriginalGlobalDAGData.nodes 10 ⟨795136, by decide⟩ =
    .split (coordinate 11) (![⟨792260, by decide⟩,⟨795047, by decide⟩,⟨795082, by decide⟩,⟨795135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26396_795136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26396 ⟨795136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26396
    ⟨795136, by decide⟩ (by decide) (![⟨792260, by decide⟩,⟨795047, by decide⟩,⟨795082, by decide⟩,⟨795135, by decide⟩]) unmarked_context_11_26396_795136 node_context_11_26396_795136
  intro a
  fin_cases a
  · exact context_12_105584_792260
  · exact context_12_105585_795047
  · exact context_12_105586_795082
  · exact context_12_105587_795135

theorem selected_cut_31176 : selected 9 ⟨795177, by decide⟩
    (prefixPartial 12 105588) = some ⟨12, 2, 0, 795177, 105588, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_105588_795177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105588 ⟨795177, by decide⟩ :=
  accepted_of_selected 12 105588 ⟨795177, by decide⟩ ⟨12, 2, 0, 795177, 105588, 1709, 65536⟩
    (by decide) selected_cut_31176

theorem selected_cut_31177 : selected 9 ⟨795212, by decide⟩
    (prefixPartial 12 105589) = some ⟨12, 2, 0, 795212, 105589, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_105589_795212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105589 ⟨795212, by decide⟩ :=
  accepted_of_selected 12 105589 ⟨795212, by decide⟩ ⟨12, 2, 0, 795212, 105589, 1413, 65536⟩
    (by decide) selected_cut_31177

theorem selected_cut_31178 : selected 9 ⟨795247, by decide⟩
    (prefixPartial 12 105590) = some ⟨12, 2, 0, 795247, 105590, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_105590_795247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105590 ⟨795247, by decide⟩ :=
  accepted_of_selected 12 105590 ⟨795247, by decide⟩ ⟨12, 2, 0, 795247, 105590, 1457, 65536⟩
    (by decide) selected_cut_31178

theorem selected_cut_31179 : selected 9 ⟨795287, by decide⟩
    (prefixPartial 12 105591) = some ⟨12, 2, 0, 795287, 105591, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_105591_795287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105591 ⟨795287, by decide⟩ :=
  accepted_of_selected 12 105591 ⟨795287, by decide⟩ ⟨12, 2, 0, 795287, 105591, 1545, 65536⟩
    (by decide) selected_cut_31179

theorem unmarked_context_11_26397_795288 : frontier 10 ⟨795288, by decide⟩
    (prefixCache 11 26397) (prefixPartial 11 26397) = false := by
  decide +kernel

theorem node_context_11_26397_795288 : EJMOriginalGlobalDAGData.nodes 10 ⟨795288, by decide⟩ =
    .split (coordinate 11) (![⟨795177, by decide⟩,⟨795212, by decide⟩,⟨795247, by decide⟩,⟨795287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26397_795288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26397 ⟨795288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26397
    ⟨795288, by decide⟩ (by decide) (![⟨795177, by decide⟩,⟨795212, by decide⟩,⟨795247, by decide⟩,⟨795287, by decide⟩]) unmarked_context_11_26397_795288 node_context_11_26397_795288
  intro a
  fin_cases a
  · exact context_12_105588_795177
  · exact context_12_105589_795212
  · exact context_12_105590_795247
  · exact context_12_105591_795287

theorem selected_cut_31180 : selected 9 ⟨795315, by decide⟩
    (prefixPartial 12 105592) = some ⟨12, 2, 0, 795315, 105592, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_105592_795315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105592 ⟨795315, by decide⟩ :=
  accepted_of_selected 12 105592 ⟨795315, by decide⟩ ⟨12, 2, 0, 795315, 105592, 1449, 65536⟩
    (by decide) selected_cut_31180

theorem selected_cut_31181 : selected 9 ⟨795340, by decide⟩
    (prefixPartial 12 105593) = some ⟨12, 2, 0, 795340, 105593, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_105593_795340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105593 ⟨795340, by decide⟩ :=
  accepted_of_selected 12 105593 ⟨795340, by decide⟩ ⟨12, 2, 0, 795340, 105593, 1265, 65536⟩
    (by decide) selected_cut_31181

theorem selected_cut_31182 : selected 9 ⟨795365, by decide⟩
    (prefixPartial 12 105594) = some ⟨12, 2, 0, 795365, 105594, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_105594_795365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105594 ⟨795365, by decide⟩ :=
  accepted_of_selected 12 105594 ⟨795365, by decide⟩ ⟨12, 2, 0, 795365, 105594, 1121, 65536⟩
    (by decide) selected_cut_31182

theorem selected_cut_31183 : selected 9 ⟨795384, by decide⟩
    (prefixPartial 12 105595) = some ⟨12, 2, 0, 795384, 105595, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_105595_795384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105595 ⟨795384, by decide⟩ :=
  accepted_of_selected 12 105595 ⟨795384, by decide⟩ ⟨12, 2, 0, 795384, 105595, 1169, 65536⟩
    (by decide) selected_cut_31183

theorem unmarked_context_11_26398_795385 : frontier 10 ⟨795385, by decide⟩
    (prefixCache 11 26398) (prefixPartial 11 26398) = false := by
  decide +kernel

theorem node_context_11_26398_795385 : EJMOriginalGlobalDAGData.nodes 10 ⟨795385, by decide⟩ =
    .split (coordinate 11) (![⟨795315, by decide⟩,⟨795340, by decide⟩,⟨795365, by decide⟩,⟨795384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26398_795385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26398 ⟨795385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26398
    ⟨795385, by decide⟩ (by decide) (![⟨795315, by decide⟩,⟨795340, by decide⟩,⟨795365, by decide⟩,⟨795384, by decide⟩]) unmarked_context_11_26398_795385 node_context_11_26398_795385
  intro a
  fin_cases a
  · exact context_12_105592_795315
  · exact context_12_105593_795340
  · exact context_12_105594_795365
  · exact context_12_105595_795384

theorem selected_cut_31184 : selected 10 ⟨795415, by decide⟩
    (prefixPartial 11 26399) = some ⟨11, 2, 0, 795415, 26399, 1169, 262144⟩ := by
  decide +kernel

theorem context_11_26399_795415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26399 ⟨795415, by decide⟩ :=
  accepted_of_selected 11 26399 ⟨795415, by decide⟩ ⟨11, 2, 0, 795415, 26399, 1169, 262144⟩
    (by decide) selected_cut_31184

theorem unmarked_context_10_6599_795416 : frontier 11 ⟨795416, by decide⟩
    (prefixCache 10 6599) (prefixPartial 10 6599) = false := by
  decide +kernel

theorem node_context_10_6599_795416 : EJMOriginalGlobalDAGData.nodes 11 ⟨795416, by decide⟩ =
    .split (coordinate 10) (![⟨795136, by decide⟩,⟨795288, by decide⟩,⟨795385, by decide⟩,⟨795415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6599_795416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6599 ⟨795416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6599
    ⟨795416, by decide⟩ (by decide) (![⟨795136, by decide⟩,⟨795288, by decide⟩,⟨795385, by decide⟩,⟨795415, by decide⟩]) unmarked_context_10_6599_795416 node_context_10_6599_795416
  intro a
  fin_cases a
  · exact context_11_26396_795136
  · exact context_11_26397_795288
  · exact context_11_26398_795385
  · exact context_11_26399_795415

theorem unmarked_context_9_1649_795417 : frontier 12 ⟨795417, by decide⟩
    (prefixCache 9 1649) (prefixPartial 9 1649) = false := by
  decide +kernel

theorem node_context_9_1649_795417 : EJMOriginalGlobalDAGData.nodes 12 ⟨795417, by decide⟩ =
    .split (coordinate 9) (![⟨793297, by decide⟩,⟨794065, by decide⟩,⟨794980, by decide⟩,⟨795416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1649_795417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1649 ⟨795417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1649
    ⟨795417, by decide⟩ (by decide) (![⟨793297, by decide⟩,⟨794065, by decide⟩,⟨794980, by decide⟩,⟨795416, by decide⟩]) unmarked_context_9_1649_795417 node_context_9_1649_795417
  intro a
  fin_cases a
  · exact context_10_6596_793297
  · exact context_10_6597_794065
  · exact context_10_6598_794980
  · exact context_10_6599_795416

theorem selected_cut_31185 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 6600) = some ⟨10, 1, 0, 793297, 6600, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6600_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6600 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 6600 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 6600, 1, 1048576⟩
    (by decide) selected_cut_31185

theorem selected_cut_31186 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 6601) = some ⟨10, 1, 0, 793297, 6601, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6601_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6601 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 6601 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 6601, 1, 1048576⟩
    (by decide) selected_cut_31186

theorem selected_cut_31187 : selected 10 ⟨795468, by decide⟩
    (prefixPartial 11 26408) = some ⟨11, 2, 0, 795468, 26408, 1757, 262144⟩ := by
  decide +kernel

theorem context_11_26408_795468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26408 ⟨795468, by decide⟩ :=
  accepted_of_selected 11 26408 ⟨795468, by decide⟩ ⟨11, 2, 0, 795468, 26408, 1757, 262144⟩
    (by decide) selected_cut_31187

theorem selected_cut_31188 : selected 10 ⟨795533, by decide⟩
    (prefixPartial 11 26409) = some ⟨11, 2, 0, 795533, 26409, 2341, 262144⟩ := by
  decide +kernel

theorem context_11_26409_795533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26409 ⟨795533, by decide⟩ :=
  accepted_of_selected 11 26409 ⟨795533, by decide⟩ ⟨11, 2, 0, 795533, 26409, 2341, 262144⟩
    (by decide) selected_cut_31188

theorem selected_cut_31189 : selected 10 ⟨795579, by decide⟩
    (prefixPartial 11 26410) = some ⟨11, 2, 0, 795579, 26410, 2169, 262144⟩ := by
  decide +kernel

theorem context_11_26410_795579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26410 ⟨795579, by decide⟩ :=
  accepted_of_selected 11 26410 ⟨795579, by decide⟩ ⟨11, 2, 0, 795579, 26410, 2169, 262144⟩
    (by decide) selected_cut_31189

theorem selected_cut_31190 : selected 10 ⟨795612, by decide⟩
    (prefixPartial 11 26411) = some ⟨11, 2, 0, 795612, 26411, 1649, 262144⟩ := by
  decide +kernel

theorem context_11_26411_795612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26411 ⟨795612, by decide⟩ :=
  accepted_of_selected 11 26411 ⟨795612, by decide⟩ ⟨11, 2, 0, 795612, 26411, 1649, 262144⟩
    (by decide) selected_cut_31190

theorem unmarked_context_10_6602_795613 : frontier 11 ⟨795613, by decide⟩
    (prefixCache 10 6602) (prefixPartial 10 6602) = false := by
  decide +kernel

theorem node_context_10_6602_795613 : EJMOriginalGlobalDAGData.nodes 11 ⟨795613, by decide⟩ =
    .split (coordinate 10) (![⟨795468, by decide⟩,⟨795533, by decide⟩,⟨795579, by decide⟩,⟨795612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6602_795613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6602 ⟨795613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6602
    ⟨795613, by decide⟩ (by decide) (![⟨795468, by decide⟩,⟨795533, by decide⟩,⟨795579, by decide⟩,⟨795612, by decide⟩]) unmarked_context_10_6602_795613 node_context_10_6602_795613
  intro a
  fin_cases a
  · exact context_11_26408_795468
  · exact context_11_26409_795533
  · exact context_11_26410_795579
  · exact context_11_26411_795612

theorem selected_cut_31191 : selected 11 ⟨795724, by decide⟩
    (prefixPartial 10 6603) = some ⟨10, 2, 0, 795724, 6603, 1937, 1048576⟩ := by
  decide +kernel

theorem context_10_6603_795724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6603 ⟨795724, by decide⟩ :=
  accepted_of_selected 10 6603 ⟨795724, by decide⟩ ⟨10, 2, 0, 795724, 6603, 1937, 1048576⟩
    (by decide) selected_cut_31191

theorem unmarked_context_9_1650_795725 : frontier 12 ⟨795725, by decide⟩
    (prefixCache 9 1650) (prefixPartial 9 1650) = false := by
  decide +kernel

theorem node_context_9_1650_795725 : EJMOriginalGlobalDAGData.nodes 12 ⟨795725, by decide⟩ =
    .split (coordinate 9) (![⟨793297, by decide⟩,⟨793297, by decide⟩,⟨795613, by decide⟩,⟨795724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1650_795725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1650 ⟨795725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1650
    ⟨795725, by decide⟩ (by decide) (![⟨793297, by decide⟩,⟨793297, by decide⟩,⟨795613, by decide⟩,⟨795724, by decide⟩]) unmarked_context_9_1650_795725 node_context_9_1650_795725
  intro a
  fin_cases a
  · exact context_10_6600_793297
  · exact context_10_6601_793297
  · exact context_10_6602_795613
  · exact context_10_6603_795724

theorem selected_cut_31192 : selected 12 ⟨795815, by decide⟩
    (prefixPartial 9 1651) = some ⟨9, 2, 0, 795815, 1651, 1229, 4194304⟩ := by
  decide +kernel

theorem context_9_1651_795815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1651 ⟨795815, by decide⟩ :=
  accepted_of_selected 9 1651 ⟨795815, by decide⟩ ⟨9, 2, 0, 795815, 1651, 1229, 4194304⟩
    (by decide) selected_cut_31192

theorem unmarked_context_8_412_795816 : frontier 13 ⟨795816, by decide⟩
    (prefixCache 8 412) (prefixPartial 8 412) = false := by
  decide +kernel

theorem node_context_8_412_795816 : EJMOriginalGlobalDAGData.nodes 13 ⟨795816, by decide⟩ =
    .split (coordinate 8) (![⟨793296, by decide⟩,⟨795417, by decide⟩,⟨795725, by decide⟩,⟨795815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_412_795816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 412 ⟨795816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 412
    ⟨795816, by decide⟩ (by decide) (![⟨793296, by decide⟩,⟨795417, by decide⟩,⟨795725, by decide⟩,⟨795815, by decide⟩]) unmarked_context_8_412_795816 node_context_8_412_795816
  intro a
  fin_cases a
  · exact context_9_1648_793296
  · exact context_9_1649_795417
  · exact context_9_1650_795725
  · exact context_9_1651_795815

theorem selected_cut_31193 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 26432) = some ⟨11, 1, 0, 434745, 26432, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26432_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26432 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 26432 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 26432, 1, 262144⟩
    (by decide) selected_cut_31193

theorem selected_cut_31194 : selected 9 ⟨14169, by decide⟩
    (prefixPartial 12 105732) = some ⟨12, 1, 0, 14169, 105732, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105732_14169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105732 ⟨14169, by decide⟩ :=
  accepted_of_selected 12 105732 ⟨14169, by decide⟩ ⟨12, 1, 0, 14169, 105732, 1, 65536⟩
    (by decide) selected_cut_31194

theorem selected_cut_31195 : selected 7 ⟨795872, by decide⟩
    (prefixPartial 14 1691728) = some ⟨14, 2, 0, 795872, 1691728, 657, 4096⟩ := by
  decide +kernel

theorem context_14_1691728_795872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691728 ⟨795872, by decide⟩ :=
  accepted_of_selected 14 1691728 ⟨795872, by decide⟩ ⟨14, 2, 0, 795872, 1691728, 657, 4096⟩
    (by decide) selected_cut_31195

theorem selected_cut_31196 : selected 7 ⟨796002, by decide⟩
    (prefixPartial 14 1691729) = some ⟨14, 2, 0, 796002, 1691729, 2721, 4096⟩ := by
  decide +kernel

theorem context_14_1691729_796002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691729 ⟨796002, by decide⟩ :=
  accepted_of_selected 14 1691729 ⟨796002, by decide⟩ ⟨14, 2, 0, 796002, 1691729, 2721, 4096⟩
    (by decide) selected_cut_31196

theorem selected_cut_31197 : selected 7 ⟨796140, by decide⟩
    (prefixPartial 14 1691730) = some ⟨14, 2, 0, 796140, 1691730, 2293, 4096⟩ := by
  decide +kernel

theorem context_14_1691730_796140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691730 ⟨796140, by decide⟩ :=
  accepted_of_selected 14 1691730 ⟨796140, by decide⟩ ⟨14, 2, 0, 796140, 1691730, 2293, 4096⟩
    (by decide) selected_cut_31197

theorem selected_cut_31198 : selected 7 ⟨796224, by decide⟩
    (prefixPartial 14 1691731) = some ⟨14, 2, 0, 796224, 1691731, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_1691731_796224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1691731 ⟨796224, by decide⟩ :=
  accepted_of_selected 14 1691731 ⟨796224, by decide⟩ ⟨14, 2, 0, 796224, 1691731, 1053, 4096⟩
    (by decide) selected_cut_31198

theorem unmarked_context_13_422932_796225 : frontier 8 ⟨796225, by decide⟩
    (prefixCache 13 422932) (prefixPartial 13 422932) = false := by
  decide +kernel

theorem node_context_13_422932_796225 : EJMOriginalGlobalDAGData.nodes 8 ⟨796225, by decide⟩ =
    .split (coordinate 13) (![⟨795872, by decide⟩,⟨796002, by decide⟩,⟨796140, by decide⟩,⟨796224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_422932_796225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422932 ⟨796225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 422932
    ⟨796225, by decide⟩ (by decide) (![⟨795872, by decide⟩,⟨796002, by decide⟩,⟨796140, by decide⟩,⟨796224, by decide⟩]) unmarked_context_13_422932_796225 node_context_13_422932_796225
  intro a
  fin_cases a
  · exact context_14_1691728_795872
  · exact context_14_1691729_796002
  · exact context_14_1691730_796140
  · exact context_14_1691731_796224

theorem selected_cut_31199 : selected 8 ⟨796423, by decide⟩
    (prefixPartial 13 422933) = some ⟨13, 2, 0, 796423, 422933, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_422933_796423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422933 ⟨796423, by decide⟩ :=
  accepted_of_selected 13 422933 ⟨796423, by decide⟩ ⟨13, 2, 0, 796423, 422933, 2061, 16384⟩
    (by decide) selected_cut_31199

theorem selected_cut_31200 : selected 8 ⟨796448, by decide⟩
    (prefixPartial 13 422934) = some ⟨13, 2, 0, 796448, 422934, 177, 16384⟩ := by
  decide +kernel

theorem context_13_422934_796448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422934 ⟨796448, by decide⟩ :=
  accepted_of_selected 13 422934 ⟨796448, by decide⟩ ⟨13, 2, 0, 796448, 422934, 177, 16384⟩
    (by decide) selected_cut_31200

theorem selected_cut_31201 : selected 8 ⟨796454, by decide⟩
    (prefixPartial 13 422935) = some ⟨13, 2, 0, 796454, 422935, 29, 16384⟩ := by
  decide +kernel

theorem context_13_422935_796454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 422935 ⟨796454, by decide⟩ :=
  accepted_of_selected 13 422935 ⟨796454, by decide⟩ ⟨13, 2, 0, 796454, 422935, 29, 16384⟩
    (by decide) selected_cut_31201

theorem unmarked_context_12_105733_796455 : frontier 9 ⟨796455, by decide⟩
    (prefixCache 12 105733) (prefixPartial 12 105733) = false := by
  decide +kernel

theorem node_context_12_105733_796455 : EJMOriginalGlobalDAGData.nodes 9 ⟨796455, by decide⟩ =
    .split (coordinate 12) (![⟨796225, by decide⟩,⟨796423, by decide⟩,⟨796448, by decide⟩,⟨796454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105733_796455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105733 ⟨796455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105733
    ⟨796455, by decide⟩ (by decide) (![⟨796225, by decide⟩,⟨796423, by decide⟩,⟨796448, by decide⟩,⟨796454, by decide⟩]) unmarked_context_12_105733_796455 node_context_12_105733_796455
  intro a
  fin_cases a
  · exact context_13_422932_796225
  · exact context_13_422933_796423
  · exact context_13_422934_796448
  · exact context_13_422935_796454

theorem selected_cut_31202 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 105734) = some ⟨12, 1, 0, 763842, 105734, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105734_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105734 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 105734 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 105734, 1, 65536⟩
    (by decide) selected_cut_31202

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
