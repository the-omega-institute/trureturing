/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover476
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_9_5765_1272954 : frontier 12 ⟨1272954, by decide⟩
    (prefixCache 9 5765) (prefixPartial 9 5765) = false := by
  decide +kernel

theorem node_context_9_5765_1272954 : EJMOriginalGlobalDAGData.nodes 12 ⟨1272954, by decide⟩ =
    .split (coordinate 9) (![⟨1272445, by decide⟩,⟨893098, by decide⟩,⟨1272723, by decide⟩,⟨1272953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5765_1272954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5765 ⟨1272954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5765
    ⟨1272954, by decide⟩ (by decide) (![⟨1272445, by decide⟩,⟨893098, by decide⟩,⟨1272723, by decide⟩,⟨1272953, by decide⟩]) unmarked_context_9_5765_1272954 node_context_9_5765_1272954
  intro a
  fin_cases a
  · exact context_10_23060_1272445
  · exact context_10_23061_893098
  · exact context_10_23062_1272723
  · exact context_10_23063_1272953

theorem selected_cut_45795 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 92256) = some ⟨11, 1, 0, 907917, 92256, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92256_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92256 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 92256 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 92256, 1, 262144⟩
    (by decide) selected_cut_45795

theorem selected_cut_45796 : selected 10 ⟨1272981, by decide⟩
    (prefixPartial 11 92257) = some ⟨11, 2, 0, 1272981, 92257, 1921, 262144⟩ := by
  decide +kernel

theorem context_11_92257_1272981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92257 ⟨1272981, by decide⟩ :=
  accepted_of_selected 11 92257 ⟨1272981, by decide⟩ ⟨11, 2, 0, 1272981, 92257, 1921, 262144⟩
    (by decide) selected_cut_45796

theorem selected_cut_45797 : selected 10 ⟨1273021, by decide⟩
    (prefixPartial 11 92258) = some ⟨11, 2, 0, 1273021, 92258, 2809, 262144⟩ := by
  decide +kernel

theorem context_11_92258_1273021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92258 ⟨1273021, by decide⟩ :=
  accepted_of_selected 11 92258 ⟨1273021, by decide⟩ ⟨11, 2, 0, 1273021, 92258, 2809, 262144⟩
    (by decide) selected_cut_45797

theorem selected_cut_45798 : selected 10 ⟨1273059, by decide⟩
    (prefixPartial 11 92259) = some ⟨11, 2, 0, 1273059, 92259, 2673, 262144⟩ := by
  decide +kernel

theorem context_11_92259_1273059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92259 ⟨1273059, by decide⟩ :=
  accepted_of_selected 11 92259 ⟨1273059, by decide⟩ ⟨11, 2, 0, 1273059, 92259, 2673, 262144⟩
    (by decide) selected_cut_45798

theorem unmarked_context_10_23064_1273060 : frontier 11 ⟨1273060, by decide⟩
    (prefixCache 10 23064) (prefixPartial 10 23064) = false := by
  decide +kernel

theorem node_context_10_23064_1273060 : EJMOriginalGlobalDAGData.nodes 11 ⟨1273060, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1272981, by decide⟩,⟨1273021, by decide⟩,⟨1273059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23064_1273060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23064 ⟨1273060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23064
    ⟨1273060, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1272981, by decide⟩,⟨1273021, by decide⟩,⟨1273059, by decide⟩]) unmarked_context_10_23064_1273060 node_context_10_23064_1273060
  intro a
  fin_cases a
  · exact context_11_92256_907917
  · exact context_11_92257_1272981
  · exact context_11_92258_1273021
  · exact context_11_92259_1273059

theorem selected_cut_45799 : selected 10 ⟨1273080, by decide⟩
    (prefixPartial 11 92260) = some ⟨11, 2, 0, 1273080, 92260, 1653, 262144⟩ := by
  decide +kernel

theorem context_11_92260_1273080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92260 ⟨1273080, by decide⟩ :=
  accepted_of_selected 11 92260 ⟨1273080, by decide⟩ ⟨11, 2, 0, 1273080, 92260, 1653, 262144⟩
    (by decide) selected_cut_45799

theorem selected_cut_45800 : selected 10 ⟨1273090, by decide⟩
    (prefixPartial 11 92261) = some ⟨11, 2, 0, 1273090, 92261, 777, 262144⟩ := by
  decide +kernel

theorem context_11_92261_1273090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92261 ⟨1273090, by decide⟩ :=
  accepted_of_selected 11 92261 ⟨1273090, by decide⟩ ⟨11, 2, 0, 1273090, 92261, 777, 262144⟩
    (by decide) selected_cut_45800

theorem selected_cut_45801 : selected 10 ⟨1273120, by decide⟩
    (prefixPartial 11 92262) = some ⟨11, 2, 0, 1273120, 92262, 2341, 262144⟩ := by
  decide +kernel

theorem context_11_92262_1273120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92262 ⟨1273120, by decide⟩ :=
  accepted_of_selected 11 92262 ⟨1273120, by decide⟩ ⟨11, 2, 0, 1273120, 92262, 2341, 262144⟩
    (by decide) selected_cut_45801

theorem selected_cut_45802 : selected 10 ⟨1273143, by decide⟩
    (prefixPartial 11 92263) = some ⟨11, 2, 0, 1273143, 92263, 2109, 262144⟩ := by
  decide +kernel

theorem context_11_92263_1273143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92263 ⟨1273143, by decide⟩ :=
  accepted_of_selected 11 92263 ⟨1273143, by decide⟩ ⟨11, 2, 0, 1273143, 92263, 2109, 262144⟩
    (by decide) selected_cut_45802

theorem unmarked_context_10_23065_1273144 : frontier 11 ⟨1273144, by decide⟩
    (prefixCache 10 23065) (prefixPartial 10 23065) = false := by
  decide +kernel

theorem node_context_10_23065_1273144 : EJMOriginalGlobalDAGData.nodes 11 ⟨1273144, by decide⟩ =
    .split (coordinate 10) (![⟨1273080, by decide⟩,⟨1273090, by decide⟩,⟨1273120, by decide⟩,⟨1273143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23065_1273144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23065 ⟨1273144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23065
    ⟨1273144, by decide⟩ (by decide) (![⟨1273080, by decide⟩,⟨1273090, by decide⟩,⟨1273120, by decide⟩,⟨1273143, by decide⟩]) unmarked_context_10_23065_1273144 node_context_10_23065_1273144
  intro a
  fin_cases a
  · exact context_11_92260_1273080
  · exact context_11_92261_1273090
  · exact context_11_92262_1273120
  · exact context_11_92263_1273143

theorem selected_cut_45803 : selected 11 ⟨1273213, by decide⟩
    (prefixPartial 10 23066) = some ⟨10, 2, 0, 1273213, 23066, 3689, 1048576⟩ := by
  decide +kernel

theorem context_10_23066_1273213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23066 ⟨1273213, by decide⟩ :=
  accepted_of_selected 10 23066 ⟨1273213, by decide⟩ ⟨10, 2, 0, 1273213, 23066, 3689, 1048576⟩
    (by decide) selected_cut_45803

theorem selected_cut_45804 : selected 10 ⟨1273234, by decide⟩
    (prefixPartial 11 92268) = some ⟨11, 2, 0, 1273234, 92268, 1629, 262144⟩ := by
  decide +kernel

theorem context_11_92268_1273234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92268 ⟨1273234, by decide⟩ :=
  accepted_of_selected 11 92268 ⟨1273234, by decide⟩ ⟨11, 2, 0, 1273234, 92268, 1629, 262144⟩
    (by decide) selected_cut_45804

theorem selected_cut_45805 : selected 10 ⟨1273249, by decide⟩
    (prefixPartial 11 92269) = some ⟨11, 2, 0, 1273249, 92269, 1077, 262144⟩ := by
  decide +kernel

theorem context_11_92269_1273249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92269 ⟨1273249, by decide⟩ :=
  accepted_of_selected 11 92269 ⟨1273249, by decide⟩ ⟨11, 2, 0, 1273249, 92269, 1077, 262144⟩
    (by decide) selected_cut_45805

theorem selected_cut_45806 : selected 10 ⟨1273268, by decide⟩
    (prefixPartial 11 92270) = some ⟨11, 2, 0, 1273268, 92270, 1489, 262144⟩ := by
  decide +kernel

theorem context_11_92270_1273268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92270 ⟨1273268, by decide⟩ :=
  accepted_of_selected 11 92270 ⟨1273268, by decide⟩ ⟨11, 2, 0, 1273268, 92270, 1489, 262144⟩
    (by decide) selected_cut_45806

theorem selected_cut_45807 : selected 10 ⟨1273280, by decide⟩
    (prefixPartial 11 92271) = some ⟨11, 2, 0, 1273280, 92271, 945, 262144⟩ := by
  decide +kernel

theorem context_11_92271_1273280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92271 ⟨1273280, by decide⟩ :=
  accepted_of_selected 11 92271 ⟨1273280, by decide⟩ ⟨11, 2, 0, 1273280, 92271, 945, 262144⟩
    (by decide) selected_cut_45807

theorem unmarked_context_10_23067_1273281 : frontier 11 ⟨1273281, by decide⟩
    (prefixCache 10 23067) (prefixPartial 10 23067) = false := by
  decide +kernel

theorem node_context_10_23067_1273281 : EJMOriginalGlobalDAGData.nodes 11 ⟨1273281, by decide⟩ =
    .split (coordinate 10) (![⟨1273234, by decide⟩,⟨1273249, by decide⟩,⟨1273268, by decide⟩,⟨1273280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23067_1273281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23067 ⟨1273281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23067
    ⟨1273281, by decide⟩ (by decide) (![⟨1273234, by decide⟩,⟨1273249, by decide⟩,⟨1273268, by decide⟩,⟨1273280, by decide⟩]) unmarked_context_10_23067_1273281 node_context_10_23067_1273281
  intro a
  fin_cases a
  · exact context_11_92268_1273234
  · exact context_11_92269_1273249
  · exact context_11_92270_1273268
  · exact context_11_92271_1273280

theorem unmarked_context_9_5766_1273282 : frontier 12 ⟨1273282, by decide⟩
    (prefixCache 9 5766) (prefixPartial 9 5766) = false := by
  decide +kernel

theorem node_context_9_5766_1273282 : EJMOriginalGlobalDAGData.nodes 12 ⟨1273282, by decide⟩ =
    .split (coordinate 9) (![⟨1273060, by decide⟩,⟨1273144, by decide⟩,⟨1273213, by decide⟩,⟨1273281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5766_1273282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5766 ⟨1273282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5766
    ⟨1273282, by decide⟩ (by decide) (![⟨1273060, by decide⟩,⟨1273144, by decide⟩,⟨1273213, by decide⟩,⟨1273281, by decide⟩]) unmarked_context_9_5766_1273282 node_context_9_5766_1273282
  intro a
  fin_cases a
  · exact context_10_23064_1273060
  · exact context_10_23065_1273144
  · exact context_10_23066_1273213
  · exact context_10_23067_1273281

theorem selected_cut_45808 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 92272) = some ⟨11, 1, 0, 907917, 92272, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92272_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92272 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 92272 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 92272, 1, 262144⟩
    (by decide) selected_cut_45808

theorem selected_cut_45809 : selected 10 ⟨1273308, by decide⟩
    (prefixPartial 11 92273) = some ⟨11, 2, 0, 1273308, 92273, 1629, 262144⟩ := by
  decide +kernel

theorem context_11_92273_1273308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92273 ⟨1273308, by decide⟩ :=
  accepted_of_selected 11 92273 ⟨1273308, by decide⟩ ⟨11, 2, 0, 1273308, 92273, 1629, 262144⟩
    (by decide) selected_cut_45809

theorem selected_cut_45810 : selected 10 ⟨1273329, by decide⟩
    (prefixPartial 11 92274) = some ⟨11, 2, 0, 1273329, 92274, 1689, 262144⟩ := by
  decide +kernel

theorem context_11_92274_1273329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92274 ⟨1273329, by decide⟩ :=
  accepted_of_selected 11 92274 ⟨1273329, by decide⟩ ⟨11, 2, 0, 1273329, 92274, 1689, 262144⟩
    (by decide) selected_cut_45810

theorem selected_cut_45811 : selected 10 ⟨1273350, by decide⟩
    (prefixPartial 11 92275) = some ⟨11, 2, 0, 1273350, 92275, 1261, 262144⟩ := by
  decide +kernel

theorem context_11_92275_1273350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92275 ⟨1273350, by decide⟩ :=
  accepted_of_selected 11 92275 ⟨1273350, by decide⟩ ⟨11, 2, 0, 1273350, 92275, 1261, 262144⟩
    (by decide) selected_cut_45811

theorem unmarked_context_10_23068_1273351 : frontier 11 ⟨1273351, by decide⟩
    (prefixCache 10 23068) (prefixPartial 10 23068) = false := by
  decide +kernel

theorem node_context_10_23068_1273351 : EJMOriginalGlobalDAGData.nodes 11 ⟨1273351, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1273308, by decide⟩,⟨1273329, by decide⟩,⟨1273350, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23068_1273351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23068 ⟨1273351, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23068
    ⟨1273351, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1273308, by decide⟩,⟨1273329, by decide⟩,⟨1273350, by decide⟩]) unmarked_context_10_23068_1273351 node_context_10_23068_1273351
  intro a
  fin_cases a
  · exact context_11_92272_907917
  · exact context_11_92273_1273308
  · exact context_11_92274_1273329
  · exact context_11_92275_1273350

theorem selected_cut_45812 : selected 11 ⟨1273406, by decide⟩
    (prefixPartial 10 23069) = some ⟨10, 2, 0, 1273406, 23069, 3545, 1048576⟩ := by
  decide +kernel

theorem context_10_23069_1273406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23069 ⟨1273406, by decide⟩ :=
  accepted_of_selected 10 23069 ⟨1273406, by decide⟩ ⟨10, 2, 0, 1273406, 23069, 3545, 1048576⟩
    (by decide) selected_cut_45812

theorem selected_cut_45813 : selected 11 ⟨1273458, by decide⟩
    (prefixPartial 10 23070) = some ⟨10, 2, 0, 1273458, 23070, 2165, 1048576⟩ := by
  decide +kernel

theorem context_10_23070_1273458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23070 ⟨1273458, by decide⟩ :=
  accepted_of_selected 10 23070 ⟨1273458, by decide⟩ ⟨10, 2, 0, 1273458, 23070, 2165, 1048576⟩
    (by decide) selected_cut_45813

theorem selected_cut_45814 : selected 11 ⟨1273468, by decide⟩
    (prefixPartial 10 23071) = some ⟨10, 2, 0, 1273468, 23071, 453, 1048576⟩ := by
  decide +kernel

theorem context_10_23071_1273468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23071 ⟨1273468, by decide⟩ :=
  accepted_of_selected 10 23071 ⟨1273468, by decide⟩ ⟨10, 2, 0, 1273468, 23071, 453, 1048576⟩
    (by decide) selected_cut_45814

theorem unmarked_context_9_5767_1273469 : frontier 12 ⟨1273469, by decide⟩
    (prefixCache 9 5767) (prefixPartial 9 5767) = false := by
  decide +kernel

theorem node_context_9_5767_1273469 : EJMOriginalGlobalDAGData.nodes 12 ⟨1273469, by decide⟩ =
    .split (coordinate 9) (![⟨1273351, by decide⟩,⟨1273406, by decide⟩,⟨1273458, by decide⟩,⟨1273468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5767_1273469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5767 ⟨1273469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5767
    ⟨1273469, by decide⟩ (by decide) (![⟨1273351, by decide⟩,⟨1273406, by decide⟩,⟨1273458, by decide⟩,⟨1273468, by decide⟩]) unmarked_context_9_5767_1273469 node_context_9_5767_1273469
  intro a
  fin_cases a
  · exact context_10_23068_1273351
  · exact context_10_23069_1273406
  · exact context_10_23070_1273458
  · exact context_10_23071_1273468

theorem unmarked_context_8_1441_1273470 : frontier 13 ⟨1273470, by decide⟩
    (prefixCache 8 1441) (prefixPartial 8 1441) = false := by
  decide +kernel

theorem node_context_8_1441_1273470 : EJMOriginalGlobalDAGData.nodes 13 ⟨1273470, by decide⟩ =
    .split (coordinate 8) (![⟨1272179, by decide⟩,⟨1272954, by decide⟩,⟨1273282, by decide⟩,⟨1273469, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1441_1273470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1441 ⟨1273470, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1441
    ⟨1273470, by decide⟩ (by decide) (![⟨1272179, by decide⟩,⟨1272954, by decide⟩,⟨1273282, by decide⟩,⟨1273469, by decide⟩]) unmarked_context_8_1441_1273470 node_context_8_1441_1273470
  intro a
  fin_cases a
  · exact context_9_5764_1272179
  · exact context_9_5765_1272954
  · exact context_9_5766_1273282
  · exact context_9_5767_1273469

theorem selected_cut_45815 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 92288) = some ⟨11, 1, 0, 434745, 92288, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92288_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92288 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 92288 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 92288, 1, 262144⟩
    (by decide) selected_cut_45815

theorem selected_cut_45816 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 92289) = some ⟨11, 1, 0, 167448, 92289, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92289_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92289 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 92289 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 92289, 1, 262144⟩
    (by decide) selected_cut_45816

theorem selected_cut_45817 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 369160) = some ⟨12, 1, 0, 448748, 369160, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369160_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369160 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 369160 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 369160, 1, 65536⟩
    (by decide) selected_cut_45817

theorem selected_cut_45818 : selected 9 ⟨1273546, by decide⟩
    (prefixPartial 12 369161) = some ⟨12, 2, 0, 1273546, 369161, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_369161_1273546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369161 ⟨1273546, by decide⟩ :=
  accepted_of_selected 12 369161 ⟨1273546, by decide⟩ ⟨12, 2, 0, 1273546, 369161, 3169, 65536⟩
    (by decide) selected_cut_45818

theorem selected_cut_45819 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 369162) = some ⟨12, 1, 0, 893903, 369162, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369162_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369162 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 369162 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 369162, 1, 65536⟩
    (by decide) selected_cut_45819

theorem selected_cut_45820 : selected 9 ⟨1273627, by decide⟩
    (prefixPartial 12 369163) = some ⟨12, 2, 0, 1273627, 369163, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_369163_1273627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369163 ⟨1273627, by decide⟩ :=
  accepted_of_selected 12 369163 ⟨1273627, by decide⟩ ⟨12, 2, 0, 1273627, 369163, 3301, 65536⟩
    (by decide) selected_cut_45820

theorem unmarked_context_11_92290_1273628 : frontier 10 ⟨1273628, by decide⟩
    (prefixCache 11 92290) (prefixPartial 11 92290) = false := by
  decide +kernel

theorem node_context_11_92290_1273628 : EJMOriginalGlobalDAGData.nodes 10 ⟨1273628, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1273546, by decide⟩,⟨893903, by decide⟩,⟨1273627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92290_1273628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92290 ⟨1273628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92290
    ⟨1273628, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1273546, by decide⟩,⟨893903, by decide⟩,⟨1273627, by decide⟩]) unmarked_context_11_92290_1273628 node_context_11_92290_1273628
  intro a
  fin_cases a
  · exact context_12_369160_448748
  · exact context_12_369161_1273546
  · exact context_12_369162_893903
  · exact context_12_369163_1273627

theorem selected_cut_45821 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 369164) = some ⟨12, 1, 0, 448748, 369164, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369164_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369164 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 369164 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 369164, 1, 65536⟩
    (by decide) selected_cut_45821

theorem selected_cut_45822 : selected 9 ⟨1273693, by decide⟩
    (prefixPartial 12 369165) = some ⟨12, 2, 0, 1273693, 369165, 3297, 65536⟩ := by
  decide +kernel

theorem context_12_369165_1273693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369165 ⟨1273693, by decide⟩ :=
  accepted_of_selected 12 369165 ⟨1273693, by decide⟩ ⟨12, 2, 0, 1273693, 369165, 3297, 65536⟩
    (by decide) selected_cut_45822

theorem selected_cut_45823 : selected 9 ⟨1273749, by decide⟩
    (prefixPartial 12 369166) = some ⟨12, 2, 0, 1273749, 369166, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_369166_1273749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369166 ⟨1273749, by decide⟩ :=
  accepted_of_selected 12 369166 ⟨1273749, by decide⟩ ⟨12, 2, 0, 1273749, 369166, 2717, 65536⟩
    (by decide) selected_cut_45823

theorem selected_cut_45824 : selected 9 ⟨1273807, by decide⟩
    (prefixPartial 12 369167) = some ⟨12, 2, 0, 1273807, 369167, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_369167_1273807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369167 ⟨1273807, by decide⟩ :=
  accepted_of_selected 12 369167 ⟨1273807, by decide⟩ ⟨12, 2, 0, 1273807, 369167, 3077, 65536⟩
    (by decide) selected_cut_45824

theorem unmarked_context_11_92291_1273808 : frontier 10 ⟨1273808, by decide⟩
    (prefixCache 11 92291) (prefixPartial 11 92291) = false := by
  decide +kernel

theorem node_context_11_92291_1273808 : EJMOriginalGlobalDAGData.nodes 10 ⟨1273808, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1273693, by decide⟩,⟨1273749, by decide⟩,⟨1273807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92291_1273808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92291 ⟨1273808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92291
    ⟨1273808, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1273693, by decide⟩,⟨1273749, by decide⟩,⟨1273807, by decide⟩]) unmarked_context_11_92291_1273808 node_context_11_92291_1273808
  intro a
  fin_cases a
  · exact context_12_369164_448748
  · exact context_12_369165_1273693
  · exact context_12_369166_1273749
  · exact context_12_369167_1273807

theorem unmarked_context_10_23072_1273809 : frontier 11 ⟨1273809, by decide⟩
    (prefixCache 10 23072) (prefixPartial 10 23072) = false := by
  decide +kernel

theorem node_context_10_23072_1273809 : EJMOriginalGlobalDAGData.nodes 11 ⟨1273809, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1273628, by decide⟩,⟨1273808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23072_1273809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23072 ⟨1273809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23072
    ⟨1273809, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1273628, by decide⟩,⟨1273808, by decide⟩]) unmarked_context_10_23072_1273809 node_context_10_23072_1273809
  intro a
  fin_cases a
  · exact context_11_92288_434745
  · exact context_11_92289_167448
  · exact context_11_92290_1273628
  · exact context_11_92291_1273808

theorem selected_cut_45825 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 369168) = some ⟨12, 1, 0, 1255011, 369168, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369168_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369168 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 369168 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 369168, 1, 65536⟩
    (by decide) selected_cut_45825

theorem selected_cut_45826 : selected 9 ⟨1273864, by decide⟩
    (prefixPartial 12 369169) = some ⟨12, 2, 0, 1273864, 369169, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_369169_1273864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369169 ⟨1273864, by decide⟩ :=
  accepted_of_selected 12 369169 ⟨1273864, by decide⟩ ⟨12, 2, 0, 1273864, 369169, 3005, 65536⟩
    (by decide) selected_cut_45826

theorem selected_cut_45827 : selected 9 ⟨1273908, by decide⟩
    (prefixPartial 12 369170) = some ⟨12, 2, 0, 1273908, 369170, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_369170_1273908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369170 ⟨1273908, by decide⟩ :=
  accepted_of_selected 12 369170 ⟨1273908, by decide⟩ ⟨12, 2, 0, 1273908, 369170, 2497, 65536⟩
    (by decide) selected_cut_45827

theorem selected_cut_45828 : selected 9 ⟨1273971, by decide⟩
    (prefixPartial 12 369171) = some ⟨12, 2, 0, 1273971, 369171, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_369171_1273971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369171 ⟨1273971, by decide⟩ :=
  accepted_of_selected 12 369171 ⟨1273971, by decide⟩ ⟨12, 2, 0, 1273971, 369171, 3365, 65536⟩
    (by decide) selected_cut_45828

theorem unmarked_context_11_92292_1273972 : frontier 10 ⟨1273972, by decide⟩
    (prefixCache 11 92292) (prefixPartial 11 92292) = false := by
  decide +kernel

theorem node_context_11_92292_1273972 : EJMOriginalGlobalDAGData.nodes 10 ⟨1273972, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1273864, by decide⟩,⟨1273908, by decide⟩,⟨1273971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92292_1273972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92292 ⟨1273972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92292
    ⟨1273972, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1273864, by decide⟩,⟨1273908, by decide⟩,⟨1273971, by decide⟩]) unmarked_context_11_92292_1273972 node_context_11_92292_1273972
  intro a
  fin_cases a
  · exact context_12_369168_1255011
  · exact context_12_369169_1273864
  · exact context_12_369170_1273908
  · exact context_12_369171_1273971

theorem selected_cut_45829 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 92293) = some ⟨11, 1, 0, 815620, 92293, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92293_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92293 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 92293 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 92293, 1, 262144⟩
    (by decide) selected_cut_45829

theorem selected_cut_45830 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 369176) = some ⟨12, 1, 0, 994572, 369176, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369176_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369176 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 369176 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 369176, 1, 65536⟩
    (by decide) selected_cut_45830

theorem selected_cut_45831 : selected 9 ⟨1274035, by decide⟩
    (prefixPartial 12 369177) = some ⟨12, 2, 0, 1274035, 369177, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_369177_1274035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369177 ⟨1274035, by decide⟩ :=
  accepted_of_selected 12 369177 ⟨1274035, by decide⟩ ⟨12, 2, 0, 1274035, 369177, 3021, 65536⟩
    (by decide) selected_cut_45831

theorem selected_cut_45832 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 369178) = some ⟨12, 1, 0, 893903, 369178, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369178_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369178 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 369178 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 369178, 1, 65536⟩
    (by decide) selected_cut_45832

theorem selected_cut_45833 : selected 9 ⟨1274113, by decide⟩
    (prefixPartial 12 369179) = some ⟨12, 2, 0, 1274113, 369179, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_369179_1274113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369179 ⟨1274113, by decide⟩ :=
  accepted_of_selected 12 369179 ⟨1274113, by decide⟩ ⟨12, 2, 0, 1274113, 369179, 3497, 65536⟩
    (by decide) selected_cut_45833

theorem unmarked_context_11_92294_1274114 : frontier 10 ⟨1274114, by decide⟩
    (prefixCache 11 92294) (prefixPartial 11 92294) = false := by
  decide +kernel

theorem node_context_11_92294_1274114 : EJMOriginalGlobalDAGData.nodes 10 ⟨1274114, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1274035, by decide⟩,⟨893903, by decide⟩,⟨1274113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92294_1274114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92294 ⟨1274114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92294
    ⟨1274114, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1274035, by decide⟩,⟨893903, by decide⟩,⟨1274113, by decide⟩]) unmarked_context_11_92294_1274114 node_context_11_92294_1274114
  intro a
  fin_cases a
  · exact context_12_369176_994572
  · exact context_12_369177_1274035
  · exact context_12_369178_893903
  · exact context_12_369179_1274113

theorem selected_cut_45834 : selected 9 ⟨1274176, by decide⟩
    (prefixPartial 12 369180) = some ⟨12, 2, 0, 1274176, 369180, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_369180_1274176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369180 ⟨1274176, by decide⟩ :=
  accepted_of_selected 12 369180 ⟨1274176, by decide⟩ ⟨12, 2, 0, 1274176, 369180, 3261, 65536⟩
    (by decide) selected_cut_45834

theorem selected_cut_45835 : selected 9 ⟨1274230, by decide⟩
    (prefixPartial 12 369181) = some ⟨12, 2, 0, 1274230, 369181, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_369181_1274230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369181 ⟨1274230, by decide⟩ :=
  accepted_of_selected 12 369181 ⟨1274230, by decide⟩ ⟨12, 2, 0, 1274230, 369181, 3217, 65536⟩
    (by decide) selected_cut_45835

theorem selected_cut_45836 : selected 9 ⟨1274276, by decide⟩
    (prefixPartial 12 369182) = some ⟨12, 2, 0, 1274276, 369182, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_369182_1274276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369182 ⟨1274276, by decide⟩ :=
  accepted_of_selected 12 369182 ⟨1274276, by decide⟩ ⟨12, 2, 0, 1274276, 369182, 2681, 65536⟩
    (by decide) selected_cut_45836

theorem selected_cut_45837 : selected 9 ⟨1274322, by decide⟩
    (prefixPartial 12 369183) = some ⟨12, 2, 0, 1274322, 369183, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_369183_1274322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369183 ⟨1274322, by decide⟩ :=
  accepted_of_selected 12 369183 ⟨1274322, by decide⟩ ⟨12, 2, 0, 1274322, 369183, 3337, 65536⟩
    (by decide) selected_cut_45837

theorem unmarked_context_11_92295_1274323 : frontier 10 ⟨1274323, by decide⟩
    (prefixCache 11 92295) (prefixPartial 11 92295) = false := by
  decide +kernel

theorem node_context_11_92295_1274323 : EJMOriginalGlobalDAGData.nodes 10 ⟨1274323, by decide⟩ =
    .split (coordinate 11) (![⟨1274176, by decide⟩,⟨1274230, by decide⟩,⟨1274276, by decide⟩,⟨1274322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92295_1274323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92295 ⟨1274323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92295
    ⟨1274323, by decide⟩ (by decide) (![⟨1274176, by decide⟩,⟨1274230, by decide⟩,⟨1274276, by decide⟩,⟨1274322, by decide⟩]) unmarked_context_11_92295_1274323 node_context_11_92295_1274323
  intro a
  fin_cases a
  · exact context_12_369180_1274176
  · exact context_12_369181_1274230
  · exact context_12_369182_1274276
  · exact context_12_369183_1274322

theorem unmarked_context_10_23073_1274324 : frontier 11 ⟨1274324, by decide⟩
    (prefixCache 10 23073) (prefixPartial 10 23073) = false := by
  decide +kernel

theorem node_context_10_23073_1274324 : EJMOriginalGlobalDAGData.nodes 11 ⟨1274324, by decide⟩ =
    .split (coordinate 10) (![⟨1273972, by decide⟩,⟨815620, by decide⟩,⟨1274114, by decide⟩,⟨1274323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23073_1274324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23073 ⟨1274324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23073
    ⟨1274324, by decide⟩ (by decide) (![⟨1273972, by decide⟩,⟨815620, by decide⟩,⟨1274114, by decide⟩,⟨1274323, by decide⟩]) unmarked_context_10_23073_1274324 node_context_10_23073_1274324
  intro a
  fin_cases a
  · exact context_11_92292_1273972
  · exact context_11_92293_815620
  · exact context_11_92294_1274114
  · exact context_11_92295_1274323

theorem selected_cut_45838 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 369184) = some ⟨12, 1, 0, 435790, 369184, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369184_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369184 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 369184 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 369184, 1, 65536⟩
    (by decide) selected_cut_45838

theorem selected_cut_45839 : selected 9 ⟨1274372, by decide⟩
    (prefixPartial 12 369185) = some ⟨12, 2, 0, 1274372, 369185, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_369185_1274372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369185 ⟨1274372, by decide⟩ :=
  accepted_of_selected 12 369185 ⟨1274372, by decide⟩ ⟨12, 2, 0, 1274372, 369185, 2609, 65536⟩
    (by decide) selected_cut_45839

theorem selected_cut_45840 : selected 9 ⟨1274407, by decide⟩
    (prefixPartial 12 369186) = some ⟨12, 2, 0, 1274407, 369186, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_369186_1274407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369186 ⟨1274407, by decide⟩ :=
  accepted_of_selected 12 369186 ⟨1274407, by decide⟩ ⟨12, 2, 0, 1274407, 369186, 2137, 65536⟩
    (by decide) selected_cut_45840

theorem selected_cut_45841 : selected 9 ⟨1274446, by decide⟩
    (prefixPartial 12 369187) = some ⟨12, 2, 0, 1274446, 369187, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_369187_1274446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369187 ⟨1274446, by decide⟩ :=
  accepted_of_selected 12 369187 ⟨1274446, by decide⟩ ⟨12, 2, 0, 1274446, 369187, 2637, 65536⟩
    (by decide) selected_cut_45841

theorem unmarked_context_11_92296_1274447 : frontier 10 ⟨1274447, by decide⟩
    (prefixCache 11 92296) (prefixPartial 11 92296) = false := by
  decide +kernel

theorem node_context_11_92296_1274447 : EJMOriginalGlobalDAGData.nodes 10 ⟨1274447, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1274372, by decide⟩,⟨1274407, by decide⟩,⟨1274446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92296_1274447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92296 ⟨1274447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92296
    ⟨1274447, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1274372, by decide⟩,⟨1274407, by decide⟩,⟨1274446, by decide⟩]) unmarked_context_11_92296_1274447 node_context_11_92296_1274447
  intro a
  fin_cases a
  · exact context_12_369184_435790
  · exact context_12_369185_1274372
  · exact context_12_369186_1274407
  · exact context_12_369187_1274446

theorem selected_cut_45842 : selected 9 ⟨1274531, by decide⟩
    (prefixPartial 12 369188) = some ⟨12, 2, 0, 1274531, 369188, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_369188_1274531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369188 ⟨1274531, by decide⟩ :=
  accepted_of_selected 12 369188 ⟨1274531, by decide⟩ ⟨12, 2, 0, 1274531, 369188, 3801, 65536⟩
    (by decide) selected_cut_45842

theorem selected_cut_45843 : selected 9 ⟨1274591, by decide⟩
    (prefixPartial 12 369189) = some ⟨12, 2, 0, 1274591, 369189, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_369189_1274591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369189 ⟨1274591, by decide⟩ :=
  accepted_of_selected 12 369189 ⟨1274591, by decide⟩ ⟨12, 2, 0, 1274591, 369189, 3369, 65536⟩
    (by decide) selected_cut_45843

theorem selected_cut_45844 : selected 9 ⟨1274648, by decide⟩
    (prefixPartial 12 369190) = some ⟨12, 2, 0, 1274648, 369190, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_369190_1274648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369190 ⟨1274648, by decide⟩ :=
  accepted_of_selected 12 369190 ⟨1274648, by decide⟩ ⟨12, 2, 0, 1274648, 369190, 2849, 65536⟩
    (by decide) selected_cut_45844

theorem selected_cut_45845 : selected 9 ⟨1274726, by decide⟩
    (prefixPartial 12 369191) = some ⟨12, 2, 0, 1274726, 369191, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_369191_1274726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369191 ⟨1274726, by decide⟩ :=
  accepted_of_selected 12 369191 ⟨1274726, by decide⟩ ⟨12, 2, 0, 1274726, 369191, 3485, 65536⟩
    (by decide) selected_cut_45845

theorem unmarked_context_11_92297_1274727 : frontier 10 ⟨1274727, by decide⟩
    (prefixCache 11 92297) (prefixPartial 11 92297) = false := by
  decide +kernel

theorem node_context_11_92297_1274727 : EJMOriginalGlobalDAGData.nodes 10 ⟨1274727, by decide⟩ =
    .split (coordinate 11) (![⟨1274531, by decide⟩,⟨1274591, by decide⟩,⟨1274648, by decide⟩,⟨1274726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92297_1274727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92297 ⟨1274727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92297
    ⟨1274727, by decide⟩ (by decide) (![⟨1274531, by decide⟩,⟨1274591, by decide⟩,⟨1274648, by decide⟩,⟨1274726, by decide⟩]) unmarked_context_11_92297_1274727 node_context_11_92297_1274727
  intro a
  fin_cases a
  · exact context_12_369188_1274531
  · exact context_12_369189_1274591
  · exact context_12_369190_1274648
  · exact context_12_369191_1274726

theorem selected_cut_45846 : selected 10 ⟨1274774, by decide⟩
    (prefixPartial 11 92298) = some ⟨11, 2, 0, 1274774, 92298, 2513, 262144⟩ := by
  decide +kernel

theorem context_11_92298_1274774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92298 ⟨1274774, by decide⟩ :=
  accepted_of_selected 11 92298 ⟨1274774, by decide⟩ ⟨11, 2, 0, 1274774, 92298, 2513, 262144⟩
    (by decide) selected_cut_45846

theorem selected_cut_45847 : selected 9 ⟨1274828, by decide⟩
    (prefixPartial 12 369196) = some ⟨12, 2, 0, 1274828, 369196, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_369196_1274828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369196 ⟨1274828, by decide⟩ :=
  accepted_of_selected 12 369196 ⟨1274828, by decide⟩ ⟨12, 2, 0, 1274828, 369196, 2945, 65536⟩
    (by decide) selected_cut_45847

theorem selected_cut_45848 : selected 9 ⟨1274889, by decide⟩
    (prefixPartial 12 369197) = some ⟨12, 2, 0, 1274889, 369197, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_369197_1274889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369197 ⟨1274889, by decide⟩ :=
  accepted_of_selected 12 369197 ⟨1274889, by decide⟩ ⟨12, 2, 0, 1274889, 369197, 2873, 65536⟩
    (by decide) selected_cut_45848

theorem selected_cut_45849 : selected 9 ⟨1274929, by decide⟩
    (prefixPartial 12 369198) = some ⟨12, 2, 0, 1274929, 369198, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_369198_1274929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369198 ⟨1274929, by decide⟩ :=
  accepted_of_selected 12 369198 ⟨1274929, by decide⟩ ⟨12, 2, 0, 1274929, 369198, 2397, 65536⟩
    (by decide) selected_cut_45849

theorem selected_cut_45850 : selected 9 ⟨1274981, by decide⟩
    (prefixPartial 12 369199) = some ⟨12, 2, 0, 1274981, 369199, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_369199_1274981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369199 ⟨1274981, by decide⟩ :=
  accepted_of_selected 12 369199 ⟨1274981, by decide⟩ ⟨12, 2, 0, 1274981, 369199, 2749, 65536⟩
    (by decide) selected_cut_45850

theorem unmarked_context_11_92299_1274982 : frontier 10 ⟨1274982, by decide⟩
    (prefixCache 11 92299) (prefixPartial 11 92299) = false := by
  decide +kernel

theorem node_context_11_92299_1274982 : EJMOriginalGlobalDAGData.nodes 10 ⟨1274982, by decide⟩ =
    .split (coordinate 11) (![⟨1274828, by decide⟩,⟨1274889, by decide⟩,⟨1274929, by decide⟩,⟨1274981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92299_1274982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92299 ⟨1274982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92299
    ⟨1274982, by decide⟩ (by decide) (![⟨1274828, by decide⟩,⟨1274889, by decide⟩,⟨1274929, by decide⟩,⟨1274981, by decide⟩]) unmarked_context_11_92299_1274982 node_context_11_92299_1274982
  intro a
  fin_cases a
  · exact context_12_369196_1274828
  · exact context_12_369197_1274889
  · exact context_12_369198_1274929
  · exact context_12_369199_1274981

theorem unmarked_context_10_23074_1274983 : frontier 11 ⟨1274983, by decide⟩
    (prefixCache 10 23074) (prefixPartial 10 23074) = false := by
  decide +kernel

theorem node_context_10_23074_1274983 : EJMOriginalGlobalDAGData.nodes 11 ⟨1274983, by decide⟩ =
    .split (coordinate 10) (![⟨1274447, by decide⟩,⟨1274727, by decide⟩,⟨1274774, by decide⟩,⟨1274982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23074_1274983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23074 ⟨1274983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23074
    ⟨1274983, by decide⟩ (by decide) (![⟨1274447, by decide⟩,⟨1274727, by decide⟩,⟨1274774, by decide⟩,⟨1274982, by decide⟩]) unmarked_context_10_23074_1274983 node_context_10_23074_1274983
  intro a
  fin_cases a
  · exact context_11_92296_1274447
  · exact context_11_92297_1274727
  · exact context_11_92298_1274774
  · exact context_11_92299_1274982

theorem selected_cut_45851 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 369200) = some ⟨12, 1, 0, 1255011, 369200, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369200_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369200 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 369200 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 369200, 1, 65536⟩
    (by decide) selected_cut_45851

theorem selected_cut_45852 : selected 9 ⟨1275026, by decide⟩
    (prefixPartial 12 369201) = some ⟨12, 2, 0, 1275026, 369201, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_369201_1275026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369201 ⟨1275026, by decide⟩ :=
  accepted_of_selected 12 369201 ⟨1275026, by decide⟩ ⟨12, 2, 0, 1275026, 369201, 2317, 65536⟩
    (by decide) selected_cut_45852

theorem selected_cut_45853 : selected 9 ⟨1275058, by decide⟩
    (prefixPartial 12 369202) = some ⟨12, 2, 0, 1275058, 369202, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_369202_1275058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369202 ⟨1275058, by decide⟩ :=
  accepted_of_selected 12 369202 ⟨1275058, by decide⟩ ⟨12, 2, 0, 1275058, 369202, 2017, 65536⟩
    (by decide) selected_cut_45853

theorem selected_cut_45854 : selected 9 ⟨1275100, by decide⟩
    (prefixPartial 12 369203) = some ⟨12, 2, 0, 1275100, 369203, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_369203_1275100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369203 ⟨1275100, by decide⟩ :=
  accepted_of_selected 12 369203 ⟨1275100, by decide⟩ ⟨12, 2, 0, 1275100, 369203, 2617, 65536⟩
    (by decide) selected_cut_45854

theorem unmarked_context_11_92300_1275101 : frontier 10 ⟨1275101, by decide⟩
    (prefixCache 11 92300) (prefixPartial 11 92300) = false := by
  decide +kernel

theorem node_context_11_92300_1275101 : EJMOriginalGlobalDAGData.nodes 10 ⟨1275101, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1275026, by decide⟩,⟨1275058, by decide⟩,⟨1275100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92300_1275101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92300 ⟨1275101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92300
    ⟨1275101, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1275026, by decide⟩,⟨1275058, by decide⟩,⟨1275100, by decide⟩]) unmarked_context_11_92300_1275101 node_context_11_92300_1275101
  intro a
  fin_cases a
  · exact context_12_369200_1255011
  · exact context_12_369201_1275026
  · exact context_12_369202_1275058
  · exact context_12_369203_1275100

theorem selected_cut_45855 : selected 9 ⟨1275176, by decide⟩
    (prefixPartial 12 369204) = some ⟨12, 2, 0, 1275176, 369204, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_369204_1275176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369204 ⟨1275176, by decide⟩ :=
  accepted_of_selected 12 369204 ⟨1275176, by decide⟩ ⟨12, 2, 0, 1275176, 369204, 2949, 65536⟩
    (by decide) selected_cut_45855

theorem selected_cut_45856 : selected 9 ⟨1275223, by decide⟩
    (prefixPartial 12 369205) = some ⟨12, 2, 0, 1275223, 369205, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_369205_1275223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369205 ⟨1275223, by decide⟩ :=
  accepted_of_selected 12 369205 ⟨1275223, by decide⟩ ⟨12, 2, 0, 1275223, 369205, 2733, 65536⟩
    (by decide) selected_cut_45856

theorem selected_cut_45857 : selected 9 ⟨1275266, by decide⟩
    (prefixPartial 12 369206) = some ⟨12, 2, 0, 1275266, 369206, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_369206_1275266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369206 ⟨1275266, by decide⟩ :=
  accepted_of_selected 12 369206 ⟨1275266, by decide⟩ ⟨12, 2, 0, 1275266, 369206, 2361, 65536⟩
    (by decide) selected_cut_45857

theorem selected_cut_45858 : selected 9 ⟨1275323, by decide⟩
    (prefixPartial 12 369207) = some ⟨12, 2, 0, 1275323, 369207, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_369207_1275323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369207 ⟨1275323, by decide⟩ :=
  accepted_of_selected 12 369207 ⟨1275323, by decide⟩ ⟨12, 2, 0, 1275323, 369207, 2897, 65536⟩
    (by decide) selected_cut_45858

theorem unmarked_context_11_92301_1275324 : frontier 10 ⟨1275324, by decide⟩
    (prefixCache 11 92301) (prefixPartial 11 92301) = false := by
  decide +kernel

theorem node_context_11_92301_1275324 : EJMOriginalGlobalDAGData.nodes 10 ⟨1275324, by decide⟩ =
    .split (coordinate 11) (![⟨1275176, by decide⟩,⟨1275223, by decide⟩,⟨1275266, by decide⟩,⟨1275323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92301_1275324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92301 ⟨1275324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92301
    ⟨1275324, by decide⟩ (by decide) (![⟨1275176, by decide⟩,⟨1275223, by decide⟩,⟨1275266, by decide⟩,⟨1275323, by decide⟩]) unmarked_context_11_92301_1275324 node_context_11_92301_1275324
  intro a
  fin_cases a
  · exact context_12_369204_1275176
  · exact context_12_369205_1275223
  · exact context_12_369206_1275266
  · exact context_12_369207_1275323

theorem selected_cut_45859 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 369208) = some ⟨12, 1, 0, 994572, 369208, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369208_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369208 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 369208 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 369208, 1, 65536⟩
    (by decide) selected_cut_45859

theorem selected_cut_45860 : selected 9 ⟨1275374, by decide⟩
    (prefixPartial 12 369209) = some ⟨12, 2, 0, 1275374, 369209, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_369209_1275374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369209 ⟨1275374, by decide⟩ :=
  accepted_of_selected 12 369209 ⟨1275374, by decide⟩ ⟨12, 2, 0, 1275374, 369209, 2393, 65536⟩
    (by decide) selected_cut_45860

theorem selected_cut_45861 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 369210) = some ⟨12, 1, 0, 893903, 369210, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369210_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369210 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 369210 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 369210, 1, 65536⟩
    (by decide) selected_cut_45861

theorem selected_cut_45862 : selected 9 ⟨1275430, by decide⟩
    (prefixPartial 12 369211) = some ⟨12, 2, 0, 1275430, 369211, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_369211_1275430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369211 ⟨1275430, by decide⟩ :=
  accepted_of_selected 12 369211 ⟨1275430, by decide⟩ ⟨12, 2, 0, 1275430, 369211, 2649, 65536⟩
    (by decide) selected_cut_45862

theorem unmarked_context_11_92302_1275431 : frontier 10 ⟨1275431, by decide⟩
    (prefixCache 11 92302) (prefixPartial 11 92302) = false := by
  decide +kernel

theorem node_context_11_92302_1275431 : EJMOriginalGlobalDAGData.nodes 10 ⟨1275431, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1275374, by decide⟩,⟨893903, by decide⟩,⟨1275430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92302_1275431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92302 ⟨1275431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92302
    ⟨1275431, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1275374, by decide⟩,⟨893903, by decide⟩,⟨1275430, by decide⟩]) unmarked_context_11_92302_1275431 node_context_11_92302_1275431
  intro a
  fin_cases a
  · exact context_12_369208_994572
  · exact context_12_369209_1275374
  · exact context_12_369210_893903
  · exact context_12_369211_1275430

theorem selected_cut_45863 : selected 9 ⟨399383, by decide⟩
    (prefixPartial 12 369212) = some ⟨12, 1, 0, 399383, 369212, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369212_399383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369212 ⟨399383, by decide⟩ :=
  accepted_of_selected 12 369212 ⟨399383, by decide⟩ ⟨12, 1, 0, 399383, 369212, 1, 65536⟩
    (by decide) selected_cut_45863

theorem selected_cut_45864 : selected 9 ⟨1275464, by decide⟩
    (prefixPartial 12 369213) = some ⟨12, 2, 0, 1275464, 369213, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_369213_1275464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369213 ⟨1275464, by decide⟩ :=
  accepted_of_selected 12 369213 ⟨1275464, by decide⟩ ⟨12, 2, 0, 1275464, 369213, 2257, 65536⟩
    (by decide) selected_cut_45864

theorem selected_cut_45865 : selected 9 ⟨1275497, by decide⟩
    (prefixPartial 12 369214) = some ⟨12, 2, 0, 1275497, 369214, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_369214_1275497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369214 ⟨1275497, by decide⟩ :=
  accepted_of_selected 12 369214 ⟨1275497, by decide⟩ ⟨12, 2, 0, 1275497, 369214, 1957, 65536⟩
    (by decide) selected_cut_45865

theorem selected_cut_45866 : selected 9 ⟨399383, by decide⟩
    (prefixPartial 12 369215) = some ⟨12, 1, 0, 399383, 369215, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369215_399383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369215 ⟨399383, by decide⟩ :=
  accepted_of_selected 12 369215 ⟨399383, by decide⟩ ⟨12, 1, 0, 399383, 369215, 1, 65536⟩
    (by decide) selected_cut_45866

theorem unmarked_context_11_92303_1275498 : frontier 10 ⟨1275498, by decide⟩
    (prefixCache 11 92303) (prefixPartial 11 92303) = false := by
  decide +kernel

theorem node_context_11_92303_1275498 : EJMOriginalGlobalDAGData.nodes 10 ⟨1275498, by decide⟩ =
    .split (coordinate 11) (![⟨399383, by decide⟩,⟨1275464, by decide⟩,⟨1275497, by decide⟩,⟨399383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92303_1275498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92303 ⟨1275498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92303
    ⟨1275498, by decide⟩ (by decide) (![⟨399383, by decide⟩,⟨1275464, by decide⟩,⟨1275497, by decide⟩,⟨399383, by decide⟩]) unmarked_context_11_92303_1275498 node_context_11_92303_1275498
  intro a
  fin_cases a
  · exact context_12_369212_399383
  · exact context_12_369213_1275464
  · exact context_12_369214_1275497
  · exact context_12_369215_399383

theorem unmarked_context_10_23075_1275499 : frontier 11 ⟨1275499, by decide⟩
    (prefixCache 10 23075) (prefixPartial 10 23075) = false := by
  decide +kernel

theorem node_context_10_23075_1275499 : EJMOriginalGlobalDAGData.nodes 11 ⟨1275499, by decide⟩ =
    .split (coordinate 10) (![⟨1275101, by decide⟩,⟨1275324, by decide⟩,⟨1275431, by decide⟩,⟨1275498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23075_1275499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23075 ⟨1275499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23075
    ⟨1275499, by decide⟩ (by decide) (![⟨1275101, by decide⟩,⟨1275324, by decide⟩,⟨1275431, by decide⟩,⟨1275498, by decide⟩]) unmarked_context_10_23075_1275499 node_context_10_23075_1275499
  intro a
  fin_cases a
  · exact context_11_92300_1275101
  · exact context_11_92301_1275324
  · exact context_11_92302_1275431
  · exact context_11_92303_1275498

theorem unmarked_context_9_5768_1275500 : frontier 12 ⟨1275500, by decide⟩
    (prefixCache 9 5768) (prefixPartial 9 5768) = false := by
  decide +kernel

theorem node_context_9_5768_1275500 : EJMOriginalGlobalDAGData.nodes 12 ⟨1275500, by decide⟩ =
    .split (coordinate 9) (![⟨1273809, by decide⟩,⟨1274324, by decide⟩,⟨1274983, by decide⟩,⟨1275499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5768_1275500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5768 ⟨1275500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5768
    ⟨1275500, by decide⟩ (by decide) (![⟨1273809, by decide⟩,⟨1274324, by decide⟩,⟨1274983, by decide⟩,⟨1275499, by decide⟩]) unmarked_context_9_5768_1275500 node_context_9_5768_1275500
  intro a
  fin_cases a
  · exact context_10_23072_1273809
  · exact context_10_23073_1274324
  · exact context_10_23074_1274983
  · exact context_10_23075_1275499

theorem selected_cut_45867 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 92304) = some ⟨11, 1, 0, 907917, 92304, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92304_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92304 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 92304 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 92304, 1, 262144⟩
    (by decide) selected_cut_45867

theorem selected_cut_45868 : selected 9 ⟨1275548, by decide⟩
    (prefixPartial 12 369220) = some ⟨12, 2, 0, 1275548, 369220, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_369220_1275548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369220 ⟨1275548, by decide⟩ :=
  accepted_of_selected 12 369220 ⟨1275548, by decide⟩ ⟨12, 2, 0, 1275548, 369220, 2237, 65536⟩
    (by decide) selected_cut_45868

theorem selected_cut_45869 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 369221) = some ⟨12, 1, 0, 1257136, 369221, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369221_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369221 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 369221 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 369221, 1, 65536⟩
    (by decide) selected_cut_45869

theorem selected_cut_45870 : selected 9 ⟨1275585, by decide⟩
    (prefixPartial 12 369222) = some ⟨12, 2, 0, 1275585, 369222, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_369222_1275585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369222 ⟨1275585, by decide⟩ :=
  accepted_of_selected 12 369222 ⟨1275585, by decide⟩ ⟨12, 2, 0, 1275585, 369222, 1905, 65536⟩
    (by decide) selected_cut_45870

theorem selected_cut_45871 : selected 9 ⟨1275631, by decide⟩
    (prefixPartial 12 369223) = some ⟨12, 2, 0, 1275631, 369223, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_369223_1275631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369223 ⟨1275631, by decide⟩ :=
  accepted_of_selected 12 369223 ⟨1275631, by decide⟩ ⟨12, 2, 0, 1275631, 369223, 2197, 65536⟩
    (by decide) selected_cut_45871

theorem unmarked_context_11_92305_1275632 : frontier 10 ⟨1275632, by decide⟩
    (prefixCache 11 92305) (prefixPartial 11 92305) = false := by
  decide +kernel

theorem node_context_11_92305_1275632 : EJMOriginalGlobalDAGData.nodes 10 ⟨1275632, by decide⟩ =
    .split (coordinate 11) (![⟨1275548, by decide⟩,⟨1257136, by decide⟩,⟨1275585, by decide⟩,⟨1275631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92305_1275632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92305 ⟨1275632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92305
    ⟨1275632, by decide⟩ (by decide) (![⟨1275548, by decide⟩,⟨1257136, by decide⟩,⟨1275585, by decide⟩,⟨1275631, by decide⟩]) unmarked_context_11_92305_1275632 node_context_11_92305_1275632
  intro a
  fin_cases a
  · exact context_12_369220_1275548
  · exact context_12_369221_1257136
  · exact context_12_369222_1275585
  · exact context_12_369223_1275631

theorem selected_cut_45872 : selected 10 ⟨1275715, by decide⟩
    (prefixPartial 11 92306) = some ⟨11, 2, 0, 1275715, 92306, 3841, 262144⟩ := by
  decide +kernel

theorem context_11_92306_1275715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92306 ⟨1275715, by decide⟩ :=
  accepted_of_selected 11 92306 ⟨1275715, by decide⟩ ⟨11, 2, 0, 1275715, 92306, 3841, 262144⟩
    (by decide) selected_cut_45872

theorem selected_cut_45873 : selected 9 ⟨1275747, by decide⟩
    (prefixPartial 12 369228) = some ⟨12, 2, 0, 1275747, 369228, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_369228_1275747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369228 ⟨1275747, by decide⟩ :=
  accepted_of_selected 12 369228 ⟨1275747, by decide⟩ ⟨12, 2, 0, 1275747, 369228, 1953, 65536⟩
    (by decide) selected_cut_45873

theorem selected_cut_45874 : selected 9 ⟨1275780, by decide⟩
    (prefixPartial 12 369229) = some ⟨12, 2, 0, 1275780, 369229, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_369229_1275780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369229 ⟨1275780, by decide⟩ :=
  accepted_of_selected 12 369229 ⟨1275780, by decide⟩ ⟨12, 2, 0, 1275780, 369229, 1805, 65536⟩
    (by decide) selected_cut_45874

theorem selected_cut_45875 : selected 9 ⟨1275812, by decide⟩
    (prefixPartial 12 369230) = some ⟨12, 2, 0, 1275812, 369230, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_369230_1275812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369230 ⟨1275812, by decide⟩ :=
  accepted_of_selected 12 369230 ⟨1275812, by decide⟩ ⟨12, 2, 0, 1275812, 369230, 1621, 65536⟩
    (by decide) selected_cut_45875

theorem selected_cut_45876 : selected 9 ⟨1275847, by decide⟩
    (prefixPartial 12 369231) = some ⟨12, 2, 0, 1275847, 369231, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_369231_1275847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369231 ⟨1275847, by decide⟩ :=
  accepted_of_selected 12 369231 ⟨1275847, by decide⟩ ⟨12, 2, 0, 1275847, 369231, 1797, 65536⟩
    (by decide) selected_cut_45876

theorem unmarked_context_11_92307_1275848 : frontier 10 ⟨1275848, by decide⟩
    (prefixCache 11 92307) (prefixPartial 11 92307) = false := by
  decide +kernel

theorem node_context_11_92307_1275848 : EJMOriginalGlobalDAGData.nodes 10 ⟨1275848, by decide⟩ =
    .split (coordinate 11) (![⟨1275747, by decide⟩,⟨1275780, by decide⟩,⟨1275812, by decide⟩,⟨1275847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92307_1275848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92307 ⟨1275848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92307
    ⟨1275848, by decide⟩ (by decide) (![⟨1275747, by decide⟩,⟨1275780, by decide⟩,⟨1275812, by decide⟩,⟨1275847, by decide⟩]) unmarked_context_11_92307_1275848 node_context_11_92307_1275848
  intro a
  fin_cases a
  · exact context_12_369228_1275747
  · exact context_12_369229_1275780
  · exact context_12_369230_1275812
  · exact context_12_369231_1275847

theorem unmarked_context_10_23076_1275849 : frontier 11 ⟨1275849, by decide⟩
    (prefixCache 10 23076) (prefixPartial 10 23076) = false := by
  decide +kernel

theorem node_context_10_23076_1275849 : EJMOriginalGlobalDAGData.nodes 11 ⟨1275849, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1275632, by decide⟩,⟨1275715, by decide⟩,⟨1275848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23076_1275849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23076 ⟨1275849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23076
    ⟨1275849, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1275632, by decide⟩,⟨1275715, by decide⟩,⟨1275848, by decide⟩]) unmarked_context_10_23076_1275849 node_context_10_23076_1275849
  intro a
  fin_cases a
  · exact context_11_92304_907917
  · exact context_11_92305_1275632
  · exact context_11_92306_1275715
  · exact context_11_92307_1275848

theorem selected_cut_45877 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23077) = some ⟨10, 1, 0, 893098, 23077, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23077_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23077 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23077 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23077, 1, 1048576⟩
    (by decide) selected_cut_45877

theorem selected_cut_45878 : selected 10 ⟨1275903, by decide⟩
    (prefixPartial 11 92312) = some ⟨11, 2, 0, 1275903, 92312, 2981, 262144⟩ := by
  decide +kernel

theorem context_11_92312_1275903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92312 ⟨1275903, by decide⟩ :=
  accepted_of_selected 11 92312 ⟨1275903, by decide⟩ ⟨11, 2, 0, 1275903, 92312, 2981, 262144⟩
    (by decide) selected_cut_45878

theorem selected_cut_45879 : selected 9 ⟨1275935, by decide⟩
    (prefixPartial 12 369252) = some ⟨12, 2, 0, 1275935, 369252, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_369252_1275935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369252 ⟨1275935, by decide⟩ :=
  accepted_of_selected 12 369252 ⟨1275935, by decide⟩ ⟨12, 2, 0, 1275935, 369252, 1897, 65536⟩
    (by decide) selected_cut_45879

theorem selected_cut_45880 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 369253) = some ⟨12, 1, 0, 1256866, 369253, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369253_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369253 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 369253 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 369253, 1, 65536⟩
    (by decide) selected_cut_45880

theorem selected_cut_45881 : selected 9 ⟨1275959, by decide⟩
    (prefixPartial 12 369254) = some ⟨12, 2, 0, 1275959, 369254, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_369254_1275959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369254 ⟨1275959, by decide⟩ :=
  accepted_of_selected 12 369254 ⟨1275959, by decide⟩ ⟨12, 2, 0, 1275959, 369254, 1413, 65536⟩
    (by decide) selected_cut_45881

theorem selected_cut_45882 : selected 9 ⟨1275996, by decide⟩
    (prefixPartial 12 369255) = some ⟨12, 2, 0, 1275996, 369255, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_369255_1275996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369255 ⟨1275996, by decide⟩ :=
  accepted_of_selected 12 369255 ⟨1275996, by decide⟩ ⟨12, 2, 0, 1275996, 369255, 1805, 65536⟩
    (by decide) selected_cut_45882

theorem unmarked_context_11_92313_1275997 : frontier 10 ⟨1275997, by decide⟩
    (prefixCache 11 92313) (prefixPartial 11 92313) = false := by
  decide +kernel

theorem node_context_11_92313_1275997 : EJMOriginalGlobalDAGData.nodes 10 ⟨1275997, by decide⟩ =
    .split (coordinate 11) (![⟨1275935, by decide⟩,⟨1256866, by decide⟩,⟨1275959, by decide⟩,⟨1275996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92313_1275997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92313 ⟨1275997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92313
    ⟨1275997, by decide⟩ (by decide) (![⟨1275935, by decide⟩,⟨1256866, by decide⟩,⟨1275959, by decide⟩,⟨1275996, by decide⟩]) unmarked_context_11_92313_1275997 node_context_11_92313_1275997
  intro a
  fin_cases a
  · exact context_12_369252_1275935
  · exact context_12_369253_1256866
  · exact context_12_369254_1275959
  · exact context_12_369255_1275996

theorem selected_cut_45883 : selected 10 ⟨1276028, by decide⟩
    (prefixPartial 11 92314) = some ⟨11, 2, 0, 1276028, 92314, 1513, 262144⟩ := by
  decide +kernel

theorem context_11_92314_1276028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92314 ⟨1276028, by decide⟩ :=
  accepted_of_selected 11 92314 ⟨1276028, by decide⟩ ⟨11, 2, 0, 1276028, 92314, 1513, 262144⟩
    (by decide) selected_cut_45883

theorem selected_cut_45884 : selected 9 ⟨1276061, by decide⟩
    (prefixPartial 12 369260) = some ⟨12, 2, 0, 1276061, 369260, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_369260_1276061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369260 ⟨1276061, by decide⟩ :=
  accepted_of_selected 12 369260 ⟨1276061, by decide⟩ ⟨12, 2, 0, 1276061, 369260, 1737, 65536⟩
    (by decide) selected_cut_45884

theorem selected_cut_45885 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 369261) = some ⟨12, 1, 0, 1256866, 369261, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369261_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369261 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 369261 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 369261, 1, 65536⟩
    (by decide) selected_cut_45885

theorem selected_cut_45886 : selected 9 ⟨1276087, by decide⟩
    (prefixPartial 12 369262) = some ⟨12, 2, 0, 1276087, 369262, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_369262_1276087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369262 ⟨1276087, by decide⟩ :=
  accepted_of_selected 12 369262 ⟨1276087, by decide⟩ ⟨12, 2, 0, 1276087, 369262, 1365, 65536⟩
    (by decide) selected_cut_45886

theorem selected_cut_45887 : selected 9 ⟨1276117, by decide⟩
    (prefixPartial 12 369263) = some ⟨12, 2, 0, 1276117, 369263, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_369263_1276117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369263 ⟨1276117, by decide⟩ :=
  accepted_of_selected 12 369263 ⟨1276117, by decide⟩ ⟨12, 2, 0, 1276117, 369263, 1613, 65536⟩
    (by decide) selected_cut_45887

theorem unmarked_context_11_92315_1276118 : frontier 10 ⟨1276118, by decide⟩
    (prefixCache 11 92315) (prefixPartial 11 92315) = false := by
  decide +kernel

theorem node_context_11_92315_1276118 : EJMOriginalGlobalDAGData.nodes 10 ⟨1276118, by decide⟩ =
    .split (coordinate 11) (![⟨1276061, by decide⟩,⟨1256866, by decide⟩,⟨1276087, by decide⟩,⟨1276117, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92315_1276118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92315 ⟨1276118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92315
    ⟨1276118, by decide⟩ (by decide) (![⟨1276061, by decide⟩,⟨1256866, by decide⟩,⟨1276087, by decide⟩,⟨1276117, by decide⟩]) unmarked_context_11_92315_1276118 node_context_11_92315_1276118
  intro a
  fin_cases a
  · exact context_12_369260_1276061
  · exact context_12_369261_1256866
  · exact context_12_369262_1276087
  · exact context_12_369263_1276117

theorem unmarked_context_10_23078_1276119 : frontier 11 ⟨1276119, by decide⟩
    (prefixCache 10 23078) (prefixPartial 10 23078) = false := by
  decide +kernel

theorem node_context_10_23078_1276119 : EJMOriginalGlobalDAGData.nodes 11 ⟨1276119, by decide⟩ =
    .split (coordinate 10) (![⟨1275903, by decide⟩,⟨1275997, by decide⟩,⟨1276028, by decide⟩,⟨1276118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23078_1276119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23078 ⟨1276119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23078
    ⟨1276119, by decide⟩ (by decide) (![⟨1275903, by decide⟩,⟨1275997, by decide⟩,⟨1276028, by decide⟩,⟨1276118, by decide⟩]) unmarked_context_10_23078_1276119 node_context_10_23078_1276119
  intro a
  fin_cases a
  · exact context_11_92312_1275903
  · exact context_11_92313_1275997
  · exact context_11_92314_1276028
  · exact context_11_92315_1276118

theorem selected_cut_45888 : selected 9 ⟨1276139, by decide⟩
    (prefixPartial 12 369264) = some ⟨12, 2, 0, 1276139, 369264, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_369264_1276139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369264 ⟨1276139, by decide⟩ :=
  accepted_of_selected 12 369264 ⟨1276139, by decide⟩ ⟨12, 2, 0, 1276139, 369264, 1333, 65536⟩
    (by decide) selected_cut_45888

theorem selected_cut_45889 : selected 9 ⟨1276160, by decide⟩
    (prefixPartial 12 369265) = some ⟨12, 2, 0, 1276160, 369265, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_369265_1276160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369265 ⟨1276160, by decide⟩ :=
  accepted_of_selected 12 369265 ⟨1276160, by decide⟩ ⟨12, 2, 0, 1276160, 369265, 1217, 65536⟩
    (by decide) selected_cut_45889

theorem selected_cut_45890 : selected 9 ⟨1276171, by decide⟩
    (prefixPartial 12 369266) = some ⟨12, 2, 0, 1276171, 369266, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_369266_1276171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369266 ⟨1276171, by decide⟩ :=
  accepted_of_selected 12 369266 ⟨1276171, by decide⟩ ⟨12, 2, 0, 1276171, 369266, 1153, 65536⟩
    (by decide) selected_cut_45890

theorem selected_cut_45891 : selected 9 ⟨1276195, by decide⟩
    (prefixPartial 12 369267) = some ⟨12, 2, 0, 1276195, 369267, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_369267_1276195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369267 ⟨1276195, by decide⟩ :=
  accepted_of_selected 12 369267 ⟨1276195, by decide⟩ ⟨12, 2, 0, 1276195, 369267, 1321, 65536⟩
    (by decide) selected_cut_45891

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
