/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover189
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_18243 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 284988) = some ⟨13, 1, 0, 3444, 284988, 1, 16384⟩ := by
  decide +kernel

theorem context_13_284988_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284988 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 284988 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 284988, 1, 16384⟩
    (by decide) selected_cut_18243

theorem selected_cut_18244 : selected 8 ⟨467162, by decide⟩
    (prefixPartial 13 284989) = some ⟨13, 2, 0, 467162, 284989, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_284989_467162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284989 ⟨467162, by decide⟩ :=
  accepted_of_selected 13 284989 ⟨467162, by decide⟩ ⟨13, 2, 0, 467162, 284989, 2181, 16384⟩
    (by decide) selected_cut_18244

theorem selected_cut_18245 : selected 8 ⟨467179, by decide⟩
    (prefixPartial 13 284990) = some ⟨13, 2, 0, 467179, 284990, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_284990_467179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284990 ⟨467179, by decide⟩ :=
  accepted_of_selected 13 284990 ⟨467179, by decide⟩ ⟨13, 2, 0, 467179, 284990, 1713, 16384⟩
    (by decide) selected_cut_18245

theorem selected_cut_18246 : selected 8 ⟨467187, by decide⟩
    (prefixPartial 13 284991) = some ⟨13, 2, 0, 467187, 284991, 773, 16384⟩ := by
  decide +kernel

theorem context_13_284991_467187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284991 ⟨467187, by decide⟩ :=
  accepted_of_selected 13 284991 ⟨467187, by decide⟩ ⟨13, 2, 0, 467187, 284991, 773, 16384⟩
    (by decide) selected_cut_18246

theorem unmarked_context_12_71247_467188 : frontier 9 ⟨467188, by decide⟩
    (prefixCache 12 71247) (prefixPartial 12 71247) = false := by
  decide +kernel

theorem node_context_12_71247_467188 : EJMOriginalGlobalDAGData.nodes 9 ⟨467188, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨467162, by decide⟩,⟨467179, by decide⟩,⟨467187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71247_467188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71247 ⟨467188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71247
    ⟨467188, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨467162, by decide⟩,⟨467179, by decide⟩,⟨467187, by decide⟩]) unmarked_context_12_71247_467188 node_context_12_71247_467188
  intro a
  fin_cases a
  · exact context_13_284988_3444
  · exact context_13_284989_467162
  · exact context_13_284990_467179
  · exact context_13_284991_467187

theorem unmarked_context_11_17811_467189 : frontier 10 ⟨467189, by decide⟩
    (prefixCache 11 17811) (prefixPartial 11 17811) = false := by
  decide +kernel

theorem node_context_11_17811_467189 : EJMOriginalGlobalDAGData.nodes 10 ⟨467189, by decide⟩ =
    .split (coordinate 11) (![⟨467029, by decide⟩,⟨467080, by decide⟩,⟨467136, by decide⟩,⟨467188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17811_467189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17811 ⟨467189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17811
    ⟨467189, by decide⟩ (by decide) (![⟨467029, by decide⟩,⟨467080, by decide⟩,⟨467136, by decide⟩,⟨467188, by decide⟩]) unmarked_context_11_17811_467189 node_context_11_17811_467189
  intro a
  fin_cases a
  · exact context_12_71244_467029
  · exact context_12_71245_467080
  · exact context_12_71246_467136
  · exact context_12_71247_467188

theorem unmarked_context_10_4452_467190 : frontier 11 ⟨467190, by decide⟩
    (prefixCache 10 4452) (prefixPartial 10 4452) = false := by
  decide +kernel

theorem node_context_10_4452_467190 : EJMOriginalGlobalDAGData.nodes 11 ⟨467190, by decide⟩ =
    .split (coordinate 10) (![⟨466531, by decide⟩,⟨466734, by decide⟩,⟨466983, by decide⟩,⟨467189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4452_467190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4452 ⟨467190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4452
    ⟨467190, by decide⟩ (by decide) (![⟨466531, by decide⟩,⟨466734, by decide⟩,⟨466983, by decide⟩,⟨467189, by decide⟩]) unmarked_context_10_4452_467190 node_context_10_4452_467190
  intro a
  fin_cases a
  · exact context_11_17808_466531
  · exact context_11_17809_466734
  · exact context_11_17810_466983
  · exact context_11_17811_467189

theorem selected_cut_18247 : selected 9 ⟨467225, by decide⟩
    (prefixPartial 12 71248) = some ⟨12, 2, 0, 467225, 71248, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_71248_467225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71248 ⟨467225, by decide⟩ :=
  accepted_of_selected 12 71248 ⟨467225, by decide⟩ ⟨12, 2, 0, 467225, 71248, 2773, 65536⟩
    (by decide) selected_cut_18247

theorem selected_cut_18248 : selected 9 ⟨467268, by decide⟩
    (prefixPartial 12 71249) = some ⟨12, 2, 0, 467268, 71249, 3393, 65536⟩ := by
  decide +kernel

theorem context_12_71249_467268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71249 ⟨467268, by decide⟩ :=
  accepted_of_selected 12 71249 ⟨467268, by decide⟩ ⟨12, 2, 0, 467268, 71249, 3393, 65536⟩
    (by decide) selected_cut_18248

theorem selected_cut_18249 : selected 9 ⟨467308, by decide⟩
    (prefixPartial 12 71250) = some ⟨12, 2, 0, 467308, 71250, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_71250_467308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71250 ⟨467308, by decide⟩ :=
  accepted_of_selected 12 71250 ⟨467308, by decide⟩ ⟨12, 2, 0, 467308, 71250, 3521, 65536⟩
    (by decide) selected_cut_18249

theorem selected_cut_18250 : selected 9 ⟨467359, by decide⟩
    (prefixPartial 12 71251) = some ⟨12, 2, 0, 467359, 71251, 4093, 65536⟩ := by
  decide +kernel

theorem context_12_71251_467359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71251 ⟨467359, by decide⟩ :=
  accepted_of_selected 12 71251 ⟨467359, by decide⟩ ⟨12, 2, 0, 467359, 71251, 4093, 65536⟩
    (by decide) selected_cut_18250

theorem unmarked_context_11_17812_467360 : frontier 10 ⟨467360, by decide⟩
    (prefixCache 11 17812) (prefixPartial 11 17812) = false := by
  decide +kernel

theorem node_context_11_17812_467360 : EJMOriginalGlobalDAGData.nodes 10 ⟨467360, by decide⟩ =
    .split (coordinate 11) (![⟨467225, by decide⟩,⟨467268, by decide⟩,⟨467308, by decide⟩,⟨467359, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17812_467360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17812 ⟨467360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17812
    ⟨467360, by decide⟩ (by decide) (![⟨467225, by decide⟩,⟨467268, by decide⟩,⟨467308, by decide⟩,⟨467359, by decide⟩]) unmarked_context_11_17812_467360 node_context_11_17812_467360
  intro a
  fin_cases a
  · exact context_12_71248_467225
  · exact context_12_71249_467268
  · exact context_12_71250_467308
  · exact context_12_71251_467359

theorem selected_cut_18251 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 17813) = some ⟨11, 1, 0, 451541, 17813, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17813_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17813 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 17813 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 17813, 1, 262144⟩
    (by decide) selected_cut_18251

theorem selected_cut_18252 : selected 9 ⟨467403, by decide⟩
    (prefixPartial 12 71256) = some ⟨12, 2, 0, 467403, 71256, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_71256_467403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71256 ⟨467403, by decide⟩ :=
  accepted_of_selected 12 71256 ⟨467403, by decide⟩ ⟨12, 2, 0, 467403, 71256, 3533, 65536⟩
    (by decide) selected_cut_18252

theorem selected_cut_18253 : selected 9 ⟨467444, by decide⟩
    (prefixPartial 12 71257) = some ⟨12, 2, 0, 467444, 71257, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_71257_467444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71257 ⟨467444, by decide⟩ :=
  accepted_of_selected 12 71257 ⟨467444, by decide⟩ ⟨12, 2, 0, 467444, 71257, 3497, 65536⟩
    (by decide) selected_cut_18253

theorem selected_cut_18254 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 285032) = some ⟨13, 1, 0, 3444, 285032, 1, 16384⟩ := by
  decide +kernel

theorem context_13_285032_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285032 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 285032 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 285032, 1, 16384⟩
    (by decide) selected_cut_18254

theorem selected_cut_18255 : selected 8 ⟨467486, by decide⟩
    (prefixPartial 13 285033) = some ⟨13, 2, 0, 467486, 285033, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_285033_467486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285033 ⟨467486, by decide⟩ :=
  accepted_of_selected 13 285033 ⟨467486, by decide⟩ ⟨13, 2, 0, 467486, 285033, 2409, 16384⟩
    (by decide) selected_cut_18255

theorem selected_cut_18256 : selected 8 ⟨467520, by decide⟩
    (prefixPartial 13 285034) = some ⟨13, 2, 0, 467520, 285034, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_285034_467520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285034 ⟨467520, by decide⟩ :=
  accepted_of_selected 13 285034 ⟨467520, by decide⟩ ⟨13, 2, 0, 467520, 285034, 2321, 16384⟩
    (by decide) selected_cut_18256

theorem selected_cut_18257 : selected 8 ⟨467550, by decide⟩
    (prefixPartial 13 285035) = some ⟨13, 2, 0, 467550, 285035, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_285035_467550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285035 ⟨467550, by decide⟩ :=
  accepted_of_selected 13 285035 ⟨467550, by decide⟩ ⟨13, 2, 0, 467550, 285035, 1325, 16384⟩
    (by decide) selected_cut_18257

theorem unmarked_context_12_71258_467551 : frontier 9 ⟨467551, by decide⟩
    (prefixCache 12 71258) (prefixPartial 12 71258) = false := by
  decide +kernel

theorem node_context_12_71258_467551 : EJMOriginalGlobalDAGData.nodes 9 ⟨467551, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨467486, by decide⟩,⟨467520, by decide⟩,⟨467550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71258_467551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71258 ⟨467551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71258
    ⟨467551, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨467486, by decide⟩,⟨467520, by decide⟩,⟨467550, by decide⟩]) unmarked_context_12_71258_467551 node_context_12_71258_467551
  intro a
  fin_cases a
  · exact context_13_285032_3444
  · exact context_13_285033_467486
  · exact context_13_285034_467520
  · exact context_13_285035_467550

theorem selected_cut_18258 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 285036) = some ⟨13, 1, 0, 3444, 285036, 1, 16384⟩ := by
  decide +kernel

theorem context_13_285036_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285036 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 285036 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 285036, 1, 16384⟩
    (by decide) selected_cut_18258

theorem selected_cut_18259 : selected 8 ⟨467570, by decide⟩
    (prefixPartial 13 285037) = some ⟨13, 2, 0, 467570, 285037, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_285037_467570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285037 ⟨467570, by decide⟩ :=
  accepted_of_selected 13 285037 ⟨467570, by decide⟩ ⟨13, 2, 0, 467570, 285037, 1781, 16384⟩
    (by decide) selected_cut_18259

theorem selected_cut_18260 : selected 8 ⟨467590, by decide⟩
    (prefixPartial 13 285038) = some ⟨13, 2, 0, 467590, 285038, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_285038_467590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285038 ⟨467590, by decide⟩ :=
  accepted_of_selected 13 285038 ⟨467590, by decide⟩ ⟨13, 2, 0, 467590, 285038, 1741, 16384⟩
    (by decide) selected_cut_18260

theorem selected_cut_18261 : selected 8 ⟨467595, by decide⟩
    (prefixPartial 13 285039) = some ⟨13, 2, 0, 467595, 285039, 741, 16384⟩ := by
  decide +kernel

theorem context_13_285039_467595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285039 ⟨467595, by decide⟩ :=
  accepted_of_selected 13 285039 ⟨467595, by decide⟩ ⟨13, 2, 0, 467595, 285039, 741, 16384⟩
    (by decide) selected_cut_18261

theorem unmarked_context_12_71259_467596 : frontier 9 ⟨467596, by decide⟩
    (prefixCache 12 71259) (prefixPartial 12 71259) = false := by
  decide +kernel

theorem node_context_12_71259_467596 : EJMOriginalGlobalDAGData.nodes 9 ⟨467596, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨467570, by decide⟩,⟨467590, by decide⟩,⟨467595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71259_467596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71259 ⟨467596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71259
    ⟨467596, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨467570, by decide⟩,⟨467590, by decide⟩,⟨467595, by decide⟩]) unmarked_context_12_71259_467596 node_context_12_71259_467596
  intro a
  fin_cases a
  · exact context_13_285036_3444
  · exact context_13_285037_467570
  · exact context_13_285038_467590
  · exact context_13_285039_467595

theorem unmarked_context_11_17814_467597 : frontier 10 ⟨467597, by decide⟩
    (prefixCache 11 17814) (prefixPartial 11 17814) = false := by
  decide +kernel

theorem node_context_11_17814_467597 : EJMOriginalGlobalDAGData.nodes 10 ⟨467597, by decide⟩ =
    .split (coordinate 11) (![⟨467403, by decide⟩,⟨467444, by decide⟩,⟨467551, by decide⟩,⟨467596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17814_467597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17814 ⟨467597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17814
    ⟨467597, by decide⟩ (by decide) (![⟨467403, by decide⟩,⟨467444, by decide⟩,⟨467551, by decide⟩,⟨467596, by decide⟩]) unmarked_context_11_17814_467597 node_context_11_17814_467597
  intro a
  fin_cases a
  · exact context_12_71256_467403
  · exact context_12_71257_467444
  · exact context_12_71258_467551
  · exact context_12_71259_467596

theorem selected_cut_18262 : selected 9 ⟨467639, by decide⟩
    (prefixPartial 12 71260) = some ⟨12, 2, 0, 467639, 71260, 3817, 65536⟩ := by
  decide +kernel

theorem context_12_71260_467639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71260 ⟨467639, by decide⟩ :=
  accepted_of_selected 12 71260 ⟨467639, by decide⟩ ⟨12, 2, 0, 467639, 71260, 3817, 65536⟩
    (by decide) selected_cut_18262

theorem selected_cut_18263 : selected 9 ⟨467688, by decide⟩
    (prefixPartial 12 71261) = some ⟨12, 2, 0, 467688, 71261, 3697, 65536⟩ := by
  decide +kernel

theorem context_12_71261_467688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71261 ⟨467688, by decide⟩ :=
  accepted_of_selected 12 71261 ⟨467688, by decide⟩ ⟨12, 2, 0, 467688, 71261, 3697, 65536⟩
    (by decide) selected_cut_18263

theorem selected_cut_18264 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 285048) = some ⟨13, 1, 0, 3444, 285048, 1, 16384⟩ := by
  decide +kernel

theorem context_13_285048_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285048 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 285048 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 285048, 1, 16384⟩
    (by decide) selected_cut_18264

theorem selected_cut_18265 : selected 8 ⟨467707, by decide⟩
    (prefixPartial 13 285049) = some ⟨13, 2, 0, 467707, 285049, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_285049_467707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285049 ⟨467707, by decide⟩ :=
  accepted_of_selected 13 285049 ⟨467707, by decide⟩ ⟨13, 2, 0, 467707, 285049, 1641, 16384⟩
    (by decide) selected_cut_18265

theorem selected_cut_18266 : selected 8 ⟨467728, by decide⟩
    (prefixPartial 13 285050) = some ⟨13, 2, 0, 467728, 285050, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_285050_467728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285050 ⟨467728, by decide⟩ :=
  accepted_of_selected 13 285050 ⟨467728, by decide⟩ ⟨13, 2, 0, 467728, 285050, 1537, 16384⟩
    (by decide) selected_cut_18266

theorem selected_cut_18267 : selected 8 ⟨467736, by decide⟩
    (prefixPartial 13 285051) = some ⟨13, 2, 0, 467736, 285051, 921, 16384⟩ := by
  decide +kernel

theorem context_13_285051_467736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285051 ⟨467736, by decide⟩ :=
  accepted_of_selected 13 285051 ⟨467736, by decide⟩ ⟨13, 2, 0, 467736, 285051, 921, 16384⟩
    (by decide) selected_cut_18267

theorem unmarked_context_12_71262_467737 : frontier 9 ⟨467737, by decide⟩
    (prefixCache 12 71262) (prefixPartial 12 71262) = false := by
  decide +kernel

theorem node_context_12_71262_467737 : EJMOriginalGlobalDAGData.nodes 9 ⟨467737, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨467707, by decide⟩,⟨467728, by decide⟩,⟨467736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71262_467737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71262 ⟨467737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71262
    ⟨467737, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨467707, by decide⟩,⟨467728, by decide⟩,⟨467736, by decide⟩]) unmarked_context_12_71262_467737 node_context_12_71262_467737
  intro a
  fin_cases a
  · exact context_13_285048_3444
  · exact context_13_285049_467707
  · exact context_13_285050_467728
  · exact context_13_285051_467736

theorem selected_cut_18268 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 285052) = some ⟨13, 1, 0, 3444, 285052, 1, 16384⟩ := by
  decide +kernel

theorem context_13_285052_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285052 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 285052 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 285052, 1, 16384⟩
    (by decide) selected_cut_18268

theorem selected_cut_18269 : selected 8 ⟨467760, by decide⟩
    (prefixPartial 13 285053) = some ⟨13, 2, 0, 467760, 285053, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_285053_467760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285053 ⟨467760, by decide⟩ :=
  accepted_of_selected 13 285053 ⟨467760, by decide⟩ ⟨13, 2, 0, 467760, 285053, 1649, 16384⟩
    (by decide) selected_cut_18269

theorem selected_cut_18270 : selected 8 ⟨467778, by decide⟩
    (prefixPartial 13 285054) = some ⟨13, 2, 0, 467778, 285054, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_285054_467778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285054 ⟨467778, by decide⟩ :=
  accepted_of_selected 13 285054 ⟨467778, by decide⟩ ⟨13, 2, 0, 467778, 285054, 1961, 16384⟩
    (by decide) selected_cut_18270

theorem selected_cut_18271 : selected 8 ⟨467785, by decide⟩
    (prefixPartial 13 285055) = some ⟨13, 2, 0, 467785, 285055, 849, 16384⟩ := by
  decide +kernel

theorem context_13_285055_467785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285055 ⟨467785, by decide⟩ :=
  accepted_of_selected 13 285055 ⟨467785, by decide⟩ ⟨13, 2, 0, 467785, 285055, 849, 16384⟩
    (by decide) selected_cut_18271

theorem unmarked_context_12_71263_467786 : frontier 9 ⟨467786, by decide⟩
    (prefixCache 12 71263) (prefixPartial 12 71263) = false := by
  decide +kernel

theorem node_context_12_71263_467786 : EJMOriginalGlobalDAGData.nodes 9 ⟨467786, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨467760, by decide⟩,⟨467778, by decide⟩,⟨467785, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71263_467786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71263 ⟨467786, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71263
    ⟨467786, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨467760, by decide⟩,⟨467778, by decide⟩,⟨467785, by decide⟩]) unmarked_context_12_71263_467786 node_context_12_71263_467786
  intro a
  fin_cases a
  · exact context_13_285052_3444
  · exact context_13_285053_467760
  · exact context_13_285054_467778
  · exact context_13_285055_467785

theorem unmarked_context_11_17815_467787 : frontier 10 ⟨467787, by decide⟩
    (prefixCache 11 17815) (prefixPartial 11 17815) = false := by
  decide +kernel

theorem node_context_11_17815_467787 : EJMOriginalGlobalDAGData.nodes 10 ⟨467787, by decide⟩ =
    .split (coordinate 11) (![⟨467639, by decide⟩,⟨467688, by decide⟩,⟨467737, by decide⟩,⟨467786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17815_467787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17815 ⟨467787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17815
    ⟨467787, by decide⟩ (by decide) (![⟨467639, by decide⟩,⟨467688, by decide⟩,⟨467737, by decide⟩,⟨467786, by decide⟩]) unmarked_context_11_17815_467787 node_context_11_17815_467787
  intro a
  fin_cases a
  · exact context_12_71260_467639
  · exact context_12_71261_467688
  · exact context_12_71262_467737
  · exact context_12_71263_467786

theorem unmarked_context_10_4453_467788 : frontier 11 ⟨467788, by decide⟩
    (prefixCache 10 4453) (prefixPartial 10 4453) = false := by
  decide +kernel

theorem node_context_10_4453_467788 : EJMOriginalGlobalDAGData.nodes 11 ⟨467788, by decide⟩ =
    .split (coordinate 10) (![⟨467360, by decide⟩,⟨451541, by decide⟩,⟨467597, by decide⟩,⟨467787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4453_467788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4453 ⟨467788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4453
    ⟨467788, by decide⟩ (by decide) (![⟨467360, by decide⟩,⟨451541, by decide⟩,⟨467597, by decide⟩,⟨467787, by decide⟩]) unmarked_context_10_4453_467788 node_context_10_4453_467788
  intro a
  fin_cases a
  · exact context_11_17812_467360
  · exact context_11_17813_451541
  · exact context_11_17814_467597
  · exact context_11_17815_467787

theorem selected_cut_18272 : selected 9 ⟨467839, by decide⟩
    (prefixPartial 12 71264) = some ⟨12, 2, 0, 467839, 71264, 3609, 65536⟩ := by
  decide +kernel

theorem context_12_71264_467839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71264 ⟨467839, by decide⟩ :=
  accepted_of_selected 12 71264 ⟨467839, by decide⟩ ⟨12, 2, 0, 467839, 71264, 3609, 65536⟩
    (by decide) selected_cut_18272

theorem selected_cut_18273 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 285060) = some ⟨13, 1, 0, 3444, 285060, 1, 16384⟩ := by
  decide +kernel

theorem context_13_285060_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285060 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 285060 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 285060, 1, 16384⟩
    (by decide) selected_cut_18273

theorem selected_cut_18274 : selected 8 ⟨467870, by decide⟩
    (prefixPartial 13 285061) = some ⟨13, 2, 0, 467870, 285061, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_285061_467870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285061 ⟨467870, by decide⟩ :=
  accepted_of_selected 13 285061 ⟨467870, by decide⟩ ⟨13, 2, 0, 467870, 285061, 1709, 16384⟩
    (by decide) selected_cut_18274

theorem selected_cut_18275 : selected 8 ⟨467892, by decide⟩
    (prefixPartial 13 285062) = some ⟨13, 2, 0, 467892, 285062, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_285062_467892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285062 ⟨467892, by decide⟩ :=
  accepted_of_selected 13 285062 ⟨467892, by decide⟩ ⟨13, 2, 0, 467892, 285062, 1637, 16384⟩
    (by decide) selected_cut_18275

theorem selected_cut_18276 : selected 8 ⟨467899, by decide⟩
    (prefixPartial 13 285063) = some ⟨13, 2, 0, 467899, 285063, 829, 16384⟩ := by
  decide +kernel

theorem context_13_285063_467899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285063 ⟨467899, by decide⟩ :=
  accepted_of_selected 13 285063 ⟨467899, by decide⟩ ⟨13, 2, 0, 467899, 285063, 829, 16384⟩
    (by decide) selected_cut_18276

theorem unmarked_context_12_71265_467900 : frontier 9 ⟨467900, by decide⟩
    (prefixCache 12 71265) (prefixPartial 12 71265) = false := by
  decide +kernel

theorem node_context_12_71265_467900 : EJMOriginalGlobalDAGData.nodes 9 ⟨467900, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨467870, by decide⟩,⟨467892, by decide⟩,⟨467899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71265_467900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71265 ⟨467900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71265
    ⟨467900, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨467870, by decide⟩,⟨467892, by decide⟩,⟨467899, by decide⟩]) unmarked_context_12_71265_467900 node_context_12_71265_467900
  intro a
  fin_cases a
  · exact context_13_285060_3444
  · exact context_13_285061_467870
  · exact context_13_285062_467892
  · exact context_13_285063_467899

theorem selected_cut_18277 : selected 9 ⟨467946, by decide⟩
    (prefixPartial 12 71266) = some ⟨12, 2, 0, 467946, 71266, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_71266_467946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71266 ⟨467946, by decide⟩ :=
  accepted_of_selected 12 71266 ⟨467946, by decide⟩ ⟨12, 2, 0, 467946, 71266, 3881, 65536⟩
    (by decide) selected_cut_18277

theorem selected_cut_18278 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 285068) = some ⟨13, 1, 0, 3444, 285068, 1, 16384⟩ := by
  decide +kernel

theorem context_13_285068_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285068 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 285068 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 285068, 1, 16384⟩
    (by decide) selected_cut_18278

theorem selected_cut_18279 : selected 8 ⟨467980, by decide⟩
    (prefixPartial 13 285069) = some ⟨13, 2, 0, 467980, 285069, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_285069_467980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285069 ⟨467980, by decide⟩ :=
  accepted_of_selected 13 285069 ⟨467980, by decide⟩ ⟨13, 2, 0, 467980, 285069, 1781, 16384⟩
    (by decide) selected_cut_18279

theorem selected_cut_18280 : selected 8 ⟨468002, by decide⟩
    (prefixPartial 13 285070) = some ⟨13, 2, 0, 468002, 285070, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_285070_468002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285070 ⟨468002, by decide⟩ :=
  accepted_of_selected 13 285070 ⟨468002, by decide⟩ ⟨13, 2, 0, 468002, 285070, 1917, 16384⟩
    (by decide) selected_cut_18280

theorem selected_cut_18281 : selected 8 ⟨468007, by decide⟩
    (prefixPartial 13 285071) = some ⟨13, 2, 0, 468007, 285071, 681, 16384⟩ := by
  decide +kernel

theorem context_13_285071_468007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285071 ⟨468007, by decide⟩ :=
  accepted_of_selected 13 285071 ⟨468007, by decide⟩ ⟨13, 2, 0, 468007, 285071, 681, 16384⟩
    (by decide) selected_cut_18281

theorem unmarked_context_12_71267_468008 : frontier 9 ⟨468008, by decide⟩
    (prefixCache 12 71267) (prefixPartial 12 71267) = false := by
  decide +kernel

theorem node_context_12_71267_468008 : EJMOriginalGlobalDAGData.nodes 9 ⟨468008, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨467980, by decide⟩,⟨468002, by decide⟩,⟨468007, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71267_468008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71267 ⟨468008, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71267
    ⟨468008, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨467980, by decide⟩,⟨468002, by decide⟩,⟨468007, by decide⟩]) unmarked_context_12_71267_468008 node_context_12_71267_468008
  intro a
  fin_cases a
  · exact context_13_285068_3444
  · exact context_13_285069_467980
  · exact context_13_285070_468002
  · exact context_13_285071_468007

theorem unmarked_context_11_17816_468009 : frontier 10 ⟨468009, by decide⟩
    (prefixCache 11 17816) (prefixPartial 11 17816) = false := by
  decide +kernel

theorem node_context_11_17816_468009 : EJMOriginalGlobalDAGData.nodes 10 ⟨468009, by decide⟩ =
    .split (coordinate 11) (![⟨467839, by decide⟩,⟨467900, by decide⟩,⟨467946, by decide⟩,⟨468008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17816_468009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17816 ⟨468009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17816
    ⟨468009, by decide⟩ (by decide) (![⟨467839, by decide⟩,⟨467900, by decide⟩,⟨467946, by decide⟩,⟨468008, by decide⟩]) unmarked_context_11_17816_468009 node_context_11_17816_468009
  intro a
  fin_cases a
  · exact context_12_71264_467839
  · exact context_12_71265_467900
  · exact context_12_71266_467946
  · exact context_12_71267_468008

theorem selected_cut_18282 : selected 9 ⟨468060, by decide⟩
    (prefixPartial 12 71268) = some ⟨12, 2, 0, 468060, 71268, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_71268_468060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71268 ⟨468060, by decide⟩ :=
  accepted_of_selected 12 71268 ⟨468060, by decide⟩ ⟨12, 2, 0, 468060, 71268, 3945, 65536⟩
    (by decide) selected_cut_18282

theorem selected_cut_18283 : selected 9 ⟨468110, by decide⟩
    (prefixPartial 12 71269) = some ⟨12, 2, 0, 468110, 71269, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_71269_468110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71269 ⟨468110, by decide⟩ :=
  accepted_of_selected 12 71269 ⟨468110, by decide⟩ ⟨12, 2, 0, 468110, 71269, 3617, 65536⟩
    (by decide) selected_cut_18283

theorem selected_cut_18284 : selected 9 ⟨468154, by decide⟩
    (prefixPartial 12 71270) = some ⟨12, 2, 0, 468154, 71270, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_71270_468154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71270 ⟨468154, by decide⟩ :=
  accepted_of_selected 12 71270 ⟨468154, by decide⟩ ⟨12, 2, 0, 468154, 71270, 3777, 65536⟩
    (by decide) selected_cut_18284

theorem selected_cut_18285 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 285084) = some ⟨13, 1, 0, 3444, 285084, 1, 16384⟩ := by
  decide +kernel

theorem context_13_285084_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285084 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 285084 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 285084, 1, 16384⟩
    (by decide) selected_cut_18285

theorem selected_cut_18286 : selected 8 ⟨468172, by decide⟩
    (prefixPartial 13 285085) = some ⟨13, 2, 0, 468172, 285085, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_285085_468172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285085 ⟨468172, by decide⟩ :=
  accepted_of_selected 13 285085 ⟨468172, by decide⟩ ⟨13, 2, 0, 468172, 285085, 1393, 16384⟩
    (by decide) selected_cut_18286

theorem selected_cut_18287 : selected 8 ⟨468207, by decide⟩
    (prefixPartial 13 285086) = some ⟨13, 2, 0, 468207, 285086, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_285086_468207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285086 ⟨468207, by decide⟩ :=
  accepted_of_selected 13 285086 ⟨468207, by decide⟩ ⟨13, 2, 0, 468207, 285086, 2153, 16384⟩
    (by decide) selected_cut_18287

theorem selected_cut_18288 : selected 8 ⟨468212, by decide⟩
    (prefixPartial 13 285087) = some ⟨13, 2, 0, 468212, 285087, 733, 16384⟩ := by
  decide +kernel

theorem context_13_285087_468212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285087 ⟨468212, by decide⟩ :=
  accepted_of_selected 13 285087 ⟨468212, by decide⟩ ⟨13, 2, 0, 468212, 285087, 733, 16384⟩
    (by decide) selected_cut_18288

theorem unmarked_context_12_71271_468213 : frontier 9 ⟨468213, by decide⟩
    (prefixCache 12 71271) (prefixPartial 12 71271) = false := by
  decide +kernel

theorem node_context_12_71271_468213 : EJMOriginalGlobalDAGData.nodes 9 ⟨468213, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨468172, by decide⟩,⟨468207, by decide⟩,⟨468212, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71271_468213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71271 ⟨468213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71271
    ⟨468213, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨468172, by decide⟩,⟨468207, by decide⟩,⟨468212, by decide⟩]) unmarked_context_12_71271_468213 node_context_12_71271_468213
  intro a
  fin_cases a
  · exact context_13_285084_3444
  · exact context_13_285085_468172
  · exact context_13_285086_468207
  · exact context_13_285087_468212

theorem unmarked_context_11_17817_468214 : frontier 10 ⟨468214, by decide⟩
    (prefixCache 11 17817) (prefixPartial 11 17817) = false := by
  decide +kernel

theorem node_context_11_17817_468214 : EJMOriginalGlobalDAGData.nodes 10 ⟨468214, by decide⟩ =
    .split (coordinate 11) (![⟨468060, by decide⟩,⟨468110, by decide⟩,⟨468154, by decide⟩,⟨468213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17817_468214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17817 ⟨468214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17817
    ⟨468214, by decide⟩ (by decide) (![⟨468060, by decide⟩,⟨468110, by decide⟩,⟨468154, by decide⟩,⟨468213, by decide⟩]) unmarked_context_11_17817_468214 node_context_11_17817_468214
  intro a
  fin_cases a
  · exact context_12_71268_468060
  · exact context_12_71269_468110
  · exact context_12_71270_468154
  · exact context_12_71271_468213

theorem selected_cut_18289 : selected 9 ⟨468252, by decide⟩
    (prefixPartial 12 71272) = some ⟨12, 2, 0, 468252, 71272, 3517, 65536⟩ := by
  decide +kernel

theorem context_12_71272_468252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71272 ⟨468252, by decide⟩ :=
  accepted_of_selected 12 71272 ⟨468252, by decide⟩ ⟨12, 2, 0, 468252, 71272, 3517, 65536⟩
    (by decide) selected_cut_18289

theorem selected_cut_18290 : selected 9 ⟨468298, by decide⟩
    (prefixPartial 12 71273) = some ⟨12, 2, 0, 468298, 71273, 3609, 65536⟩ := by
  decide +kernel

theorem context_12_71273_468298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71273 ⟨468298, by decide⟩ :=
  accepted_of_selected 12 71273 ⟨468298, by decide⟩ ⟨12, 2, 0, 468298, 71273, 3609, 65536⟩
    (by decide) selected_cut_18290

theorem selected_cut_18291 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 71274) = some ⟨12, 1, 0, 445248, 71274, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71274_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71274 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 71274 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 71274, 1, 65536⟩
    (by decide) selected_cut_18291

theorem selected_cut_18292 : selected 9 ⟨468345, by decide⟩
    (prefixPartial 12 71275) = some ⟨12, 2, 0, 468345, 71275, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_71275_468345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71275 ⟨468345, by decide⟩ :=
  accepted_of_selected 12 71275 ⟨468345, by decide⟩ ⟨12, 2, 0, 468345, 71275, 3829, 65536⟩
    (by decide) selected_cut_18292

theorem unmarked_context_11_17818_468346 : frontier 10 ⟨468346, by decide⟩
    (prefixCache 11 17818) (prefixPartial 11 17818) = false := by
  decide +kernel

theorem node_context_11_17818_468346 : EJMOriginalGlobalDAGData.nodes 10 ⟨468346, by decide⟩ =
    .split (coordinate 11) (![⟨468252, by decide⟩,⟨468298, by decide⟩,⟨445248, by decide⟩,⟨468345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17818_468346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17818 ⟨468346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17818
    ⟨468346, by decide⟩ (by decide) (![⟨468252, by decide⟩,⟨468298, by decide⟩,⟨445248, by decide⟩,⟨468345, by decide⟩]) unmarked_context_11_17818_468346 node_context_11_17818_468346
  intro a
  fin_cases a
  · exact context_12_71272_468252
  · exact context_12_71273_468298
  · exact context_12_71274_445248
  · exact context_12_71275_468345

theorem selected_cut_18293 : selected 9 ⟨468392, by decide⟩
    (prefixPartial 12 71276) = some ⟨12, 2, 0, 468392, 71276, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_71276_468392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71276 ⟨468392, by decide⟩ :=
  accepted_of_selected 12 71276 ⟨468392, by decide⟩ ⟨12, 2, 0, 468392, 71276, 3989, 65536⟩
    (by decide) selected_cut_18293

theorem selected_cut_18294 : selected 9 ⟨468449, by decide⟩
    (prefixPartial 12 71277) = some ⟨12, 2, 0, 468449, 71277, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_71277_468449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71277 ⟨468449, by decide⟩ :=
  accepted_of_selected 12 71277 ⟨468449, by decide⟩ ⟨12, 2, 0, 468449, 71277, 3941, 65536⟩
    (by decide) selected_cut_18294

theorem selected_cut_18295 : selected 9 ⟨468494, by decide⟩
    (prefixPartial 12 71278) = some ⟨12, 2, 0, 468494, 71278, 3905, 65536⟩ := by
  decide +kernel

theorem context_12_71278_468494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71278 ⟨468494, by decide⟩ :=
  accepted_of_selected 12 71278 ⟨468494, by decide⟩ ⟨12, 2, 0, 468494, 71278, 3905, 65536⟩
    (by decide) selected_cut_18295

theorem selected_cut_18296 : selected 9 ⟨468545, by decide⟩
    (prefixPartial 12 71279) = some ⟨12, 2, 0, 468545, 71279, 4005, 65536⟩ := by
  decide +kernel

theorem context_12_71279_468545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71279 ⟨468545, by decide⟩ :=
  accepted_of_selected 12 71279 ⟨468545, by decide⟩ ⟨12, 2, 0, 468545, 71279, 4005, 65536⟩
    (by decide) selected_cut_18296

theorem unmarked_context_11_17819_468546 : frontier 10 ⟨468546, by decide⟩
    (prefixCache 11 17819) (prefixPartial 11 17819) = false := by
  decide +kernel

theorem node_context_11_17819_468546 : EJMOriginalGlobalDAGData.nodes 10 ⟨468546, by decide⟩ =
    .split (coordinate 11) (![⟨468392, by decide⟩,⟨468449, by decide⟩,⟨468494, by decide⟩,⟨468545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17819_468546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17819 ⟨468546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17819
    ⟨468546, by decide⟩ (by decide) (![⟨468392, by decide⟩,⟨468449, by decide⟩,⟨468494, by decide⟩,⟨468545, by decide⟩]) unmarked_context_11_17819_468546 node_context_11_17819_468546
  intro a
  fin_cases a
  · exact context_12_71276_468392
  · exact context_12_71277_468449
  · exact context_12_71278_468494
  · exact context_12_71279_468545

theorem unmarked_context_10_4454_468547 : frontier 11 ⟨468547, by decide⟩
    (prefixCache 10 4454) (prefixPartial 10 4454) = false := by
  decide +kernel

theorem node_context_10_4454_468547 : EJMOriginalGlobalDAGData.nodes 11 ⟨468547, by decide⟩ =
    .split (coordinate 10) (![⟨468009, by decide⟩,⟨468214, by decide⟩,⟨468346, by decide⟩,⟨468546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4454_468547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4454 ⟨468547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4454
    ⟨468547, by decide⟩ (by decide) (![⟨468009, by decide⟩,⟨468214, by decide⟩,⟨468346, by decide⟩,⟨468546, by decide⟩]) unmarked_context_10_4454_468547 node_context_10_4454_468547
  intro a
  fin_cases a
  · exact context_11_17816_468009
  · exact context_11_17817_468214
  · exact context_11_17818_468346
  · exact context_11_17819_468546

theorem selected_cut_18297 : selected 9 ⟨468580, by decide⟩
    (prefixPartial 12 71280) = some ⟨12, 2, 0, 468580, 71280, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_71280_468580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71280 ⟨468580, by decide⟩ :=
  accepted_of_selected 12 71280 ⟨468580, by decide⟩ ⟨12, 2, 0, 468580, 71280, 2541, 65536⟩
    (by decide) selected_cut_18297

theorem selected_cut_18298 : selected 9 ⟨468614, by decide⟩
    (prefixPartial 12 71281) = some ⟨12, 2, 0, 468614, 71281, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_71281_468614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71281 ⟨468614, by decide⟩ :=
  accepted_of_selected 12 71281 ⟨468614, by decide⟩ ⟨12, 2, 0, 468614, 71281, 2933, 65536⟩
    (by decide) selected_cut_18298

theorem selected_cut_18299 : selected 9 ⟨468646, by decide⟩
    (prefixPartial 12 71282) = some ⟨12, 2, 0, 468646, 71282, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_71282_468646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71282 ⟨468646, by decide⟩ :=
  accepted_of_selected 12 71282 ⟨468646, by decide⟩ ⟨12, 2, 0, 468646, 71282, 2801, 65536⟩
    (by decide) selected_cut_18299

theorem selected_cut_18300 : selected 9 ⟨468689, by decide⟩
    (prefixPartial 12 71283) = some ⟨12, 2, 0, 468689, 71283, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_71283_468689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71283 ⟨468689, by decide⟩ :=
  accepted_of_selected 12 71283 ⟨468689, by decide⟩ ⟨12, 2, 0, 468689, 71283, 3181, 65536⟩
    (by decide) selected_cut_18300

theorem unmarked_context_11_17820_468690 : frontier 10 ⟨468690, by decide⟩
    (prefixCache 11 17820) (prefixPartial 11 17820) = false := by
  decide +kernel

theorem node_context_11_17820_468690 : EJMOriginalGlobalDAGData.nodes 10 ⟨468690, by decide⟩ =
    .split (coordinate 11) (![⟨468580, by decide⟩,⟨468614, by decide⟩,⟨468646, by decide⟩,⟨468689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17820_468690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17820 ⟨468690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17820
    ⟨468690, by decide⟩ (by decide) (![⟨468580, by decide⟩,⟨468614, by decide⟩,⟨468646, by decide⟩,⟨468689, by decide⟩]) unmarked_context_11_17820_468690 node_context_11_17820_468690
  intro a
  fin_cases a
  · exact context_12_71280_468580
  · exact context_12_71281_468614
  · exact context_12_71282_468646
  · exact context_12_71283_468689

theorem selected_cut_18301 : selected 9 ⟨468729, by decide⟩
    (prefixPartial 12 71284) = some ⟨12, 2, 0, 468729, 71284, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_71284_468729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71284 ⟨468729, by decide⟩ :=
  accepted_of_selected 12 71284 ⟨468729, by decide⟩ ⟨12, 2, 0, 468729, 71284, 2829, 65536⟩
    (by decide) selected_cut_18301

theorem selected_cut_18302 : selected 9 ⟨468762, by decide⟩
    (prefixPartial 12 71285) = some ⟨12, 2, 0, 468762, 71285, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_71285_468762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71285 ⟨468762, by decide⟩ :=
  accepted_of_selected 12 71285 ⟨468762, by decide⟩ ⟨12, 2, 0, 468762, 71285, 2637, 65536⟩
    (by decide) selected_cut_18302

theorem selected_cut_18303 : selected 9 ⟨468796, by decide⟩
    (prefixPartial 12 71286) = some ⟨12, 2, 0, 468796, 71286, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_71286_468796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71286 ⟨468796, by decide⟩ :=
  accepted_of_selected 12 71286 ⟨468796, by decide⟩ ⟨12, 2, 0, 468796, 71286, 2869, 65536⟩
    (by decide) selected_cut_18303

theorem selected_cut_18304 : selected 9 ⟨468849, by decide⟩
    (prefixPartial 12 71287) = some ⟨12, 2, 0, 468849, 71287, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_71287_468849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71287 ⟨468849, by decide⟩ :=
  accepted_of_selected 12 71287 ⟨468849, by decide⟩ ⟨12, 2, 0, 468849, 71287, 3253, 65536⟩
    (by decide) selected_cut_18304

theorem unmarked_context_11_17821_468850 : frontier 10 ⟨468850, by decide⟩
    (prefixCache 11 17821) (prefixPartial 11 17821) = false := by
  decide +kernel

theorem node_context_11_17821_468850 : EJMOriginalGlobalDAGData.nodes 10 ⟨468850, by decide⟩ =
    .split (coordinate 11) (![⟨468729, by decide⟩,⟨468762, by decide⟩,⟨468796, by decide⟩,⟨468849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17821_468850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17821 ⟨468850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17821
    ⟨468850, by decide⟩ (by decide) (![⟨468729, by decide⟩,⟨468762, by decide⟩,⟨468796, by decide⟩,⟨468849, by decide⟩]) unmarked_context_11_17821_468850 node_context_11_17821_468850
  intro a
  fin_cases a
  · exact context_12_71284_468729
  · exact context_12_71285_468762
  · exact context_12_71286_468796
  · exact context_12_71287_468849

theorem selected_cut_18305 : selected 9 ⟨468884, by decide⟩
    (prefixPartial 12 71288) = some ⟨12, 2, 0, 468884, 71288, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_71288_468884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71288 ⟨468884, by decide⟩ :=
  accepted_of_selected 12 71288 ⟨468884, by decide⟩ ⟨12, 2, 0, 468884, 71288, 2809, 65536⟩
    (by decide) selected_cut_18305

theorem selected_cut_18306 : selected 9 ⟨468916, by decide⟩
    (prefixPartial 12 71289) = some ⟨12, 2, 0, 468916, 71289, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_71289_468916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71289 ⟨468916, by decide⟩ :=
  accepted_of_selected 12 71289 ⟨468916, by decide⟩ ⟨12, 2, 0, 468916, 71289, 2881, 65536⟩
    (by decide) selected_cut_18306

theorem selected_cut_18307 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 285160) = some ⟨13, 1, 0, 3444, 285160, 1, 16384⟩ := by
  decide +kernel

theorem context_13_285160_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285160 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 285160 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 285160, 1, 16384⟩
    (by decide) selected_cut_18307

theorem selected_cut_18308 : selected 8 ⟨468928, by decide⟩
    (prefixPartial 13 285161) = some ⟨13, 2, 0, 468928, 285161, 469, 16384⟩ := by
  decide +kernel

theorem context_13_285161_468928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285161 ⟨468928, by decide⟩ :=
  accepted_of_selected 13 285161 ⟨468928, by decide⟩ ⟨13, 2, 0, 468928, 285161, 469, 16384⟩
    (by decide) selected_cut_18308

theorem selected_cut_18309 : selected 8 ⟨468971, by decide⟩
    (prefixPartial 13 285162) = some ⟨13, 2, 0, 468971, 285162, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_285162_468971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285162 ⟨468971, by decide⟩ :=
  accepted_of_selected 13 285162 ⟨468971, by decide⟩ ⟨13, 2, 0, 468971, 285162, 2561, 16384⟩
    (by decide) selected_cut_18309

theorem selected_cut_18310 : selected 8 ⟨469004, by decide⟩
    (prefixPartial 13 285163) = some ⟨13, 2, 0, 469004, 285163, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_285163_469004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 285163 ⟨469004, by decide⟩ :=
  accepted_of_selected 13 285163 ⟨469004, by decide⟩ ⟨13, 2, 0, 469004, 285163, 1449, 16384⟩
    (by decide) selected_cut_18310

theorem unmarked_context_12_71290_469005 : frontier 9 ⟨469005, by decide⟩
    (prefixCache 12 71290) (prefixPartial 12 71290) = false := by
  decide +kernel

theorem node_context_12_71290_469005 : EJMOriginalGlobalDAGData.nodes 9 ⟨469005, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨468928, by decide⟩,⟨468971, by decide⟩,⟨469004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71290_469005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71290 ⟨469005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71290
    ⟨469005, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨468928, by decide⟩,⟨468971, by decide⟩,⟨469004, by decide⟩]) unmarked_context_12_71290_469005 node_context_12_71290_469005
  intro a
  fin_cases a
  · exact context_13_285160_3444
  · exact context_13_285161_468928
  · exact context_13_285162_468971
  · exact context_13_285163_469004

theorem selected_cut_18311 : selected 9 ⟨469038, by decide⟩
    (prefixPartial 12 71291) = some ⟨12, 2, 0, 469038, 71291, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_71291_469038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71291 ⟨469038, by decide⟩ :=
  accepted_of_selected 12 71291 ⟨469038, by decide⟩ ⟨12, 2, 0, 469038, 71291, 2973, 65536⟩
    (by decide) selected_cut_18311

theorem unmarked_context_11_17822_469039 : frontier 10 ⟨469039, by decide⟩
    (prefixCache 11 17822) (prefixPartial 11 17822) = false := by
  decide +kernel

theorem node_context_11_17822_469039 : EJMOriginalGlobalDAGData.nodes 10 ⟨469039, by decide⟩ =
    .split (coordinate 11) (![⟨468884, by decide⟩,⟨468916, by decide⟩,⟨469005, by decide⟩,⟨469038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17822_469039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17822 ⟨469039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17822
    ⟨469039, by decide⟩ (by decide) (![⟨468884, by decide⟩,⟨468916, by decide⟩,⟨469005, by decide⟩,⟨469038, by decide⟩]) unmarked_context_11_17822_469039 node_context_11_17822_469039
  intro a
  fin_cases a
  · exact context_12_71288_468884
  · exact context_12_71289_468916
  · exact context_12_71290_469005
  · exact context_12_71291_469038

theorem selected_cut_18312 : selected 9 ⟨469068, by decide⟩
    (prefixPartial 12 71292) = some ⟨12, 2, 0, 469068, 71292, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_71292_469068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71292 ⟨469068, by decide⟩ :=
  accepted_of_selected 12 71292 ⟨469068, by decide⟩ ⟨12, 2, 0, 469068, 71292, 2661, 65536⟩
    (by decide) selected_cut_18312

theorem selected_cut_18313 : selected 9 ⟨469100, by decide⟩
    (prefixPartial 12 71293) = some ⟨12, 2, 0, 469100, 71293, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_71293_469100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71293 ⟨469100, by decide⟩ :=
  accepted_of_selected 12 71293 ⟨469100, by decide⟩ ⟨12, 2, 0, 469100, 71293, 2717, 65536⟩
    (by decide) selected_cut_18313

theorem selected_cut_18314 : selected 9 ⟨469131, by decide⟩
    (prefixPartial 12 71294) = some ⟨12, 2, 0, 469131, 71294, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_71294_469131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71294 ⟨469131, by decide⟩ :=
  accepted_of_selected 12 71294 ⟨469131, by decide⟩ ⟨12, 2, 0, 469131, 71294, 2641, 65536⟩
    (by decide) selected_cut_18314

theorem selected_cut_18315 : selected 9 ⟨469164, by decide⟩
    (prefixPartial 12 71295) = some ⟨12, 2, 0, 469164, 71295, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_71295_469164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71295 ⟨469164, by decide⟩ :=
  accepted_of_selected 12 71295 ⟨469164, by decide⟩ ⟨12, 2, 0, 469164, 71295, 2837, 65536⟩
    (by decide) selected_cut_18315

theorem unmarked_context_11_17823_469165 : frontier 10 ⟨469165, by decide⟩
    (prefixCache 11 17823) (prefixPartial 11 17823) = false := by
  decide +kernel

theorem node_context_11_17823_469165 : EJMOriginalGlobalDAGData.nodes 10 ⟨469165, by decide⟩ =
    .split (coordinate 11) (![⟨469068, by decide⟩,⟨469100, by decide⟩,⟨469131, by decide⟩,⟨469164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17823_469165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17823 ⟨469165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17823
    ⟨469165, by decide⟩ (by decide) (![⟨469068, by decide⟩,⟨469100, by decide⟩,⟨469131, by decide⟩,⟨469164, by decide⟩]) unmarked_context_11_17823_469165 node_context_11_17823_469165
  intro a
  fin_cases a
  · exact context_12_71292_469068
  · exact context_12_71293_469100
  · exact context_12_71294_469131
  · exact context_12_71295_469164

theorem unmarked_context_10_4455_469166 : frontier 11 ⟨469166, by decide⟩
    (prefixCache 10 4455) (prefixPartial 10 4455) = false := by
  decide +kernel

theorem node_context_10_4455_469166 : EJMOriginalGlobalDAGData.nodes 11 ⟨469166, by decide⟩ =
    .split (coordinate 10) (![⟨468690, by decide⟩,⟨468850, by decide⟩,⟨469039, by decide⟩,⟨469165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4455_469166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4455 ⟨469166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4455
    ⟨469166, by decide⟩ (by decide) (![⟨468690, by decide⟩,⟨468850, by decide⟩,⟨469039, by decide⟩,⟨469165, by decide⟩]) unmarked_context_10_4455_469166 node_context_10_4455_469166
  intro a
  fin_cases a
  · exact context_11_17820_468690
  · exact context_11_17821_468850
  · exact context_11_17822_469039
  · exact context_11_17823_469165

theorem unmarked_context_9_1113_469167 : frontier 12 ⟨469167, by decide⟩
    (prefixCache 9 1113) (prefixPartial 9 1113) = false := by
  decide +kernel

theorem node_context_9_1113_469167 : EJMOriginalGlobalDAGData.nodes 12 ⟨469167, by decide⟩ =
    .split (coordinate 9) (![⟨467190, by decide⟩,⟨467788, by decide⟩,⟨468547, by decide⟩,⟨469166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1113_469167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1113 ⟨469167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1113
    ⟨469167, by decide⟩ (by decide) (![⟨467190, by decide⟩,⟨467788, by decide⟩,⟨468547, by decide⟩,⟨469166, by decide⟩]) unmarked_context_9_1113_469167 node_context_9_1113_469167
  intro a
  fin_cases a
  · exact context_10_4452_467190
  · exact context_10_4453_467788
  · exact context_10_4454_468547
  · exact context_10_4455_469166

theorem selected_cut_18316 : selected 9 ⟨469186, by decide⟩
    (prefixPartial 12 71296) = some ⟨12, 2, 0, 469186, 71296, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_71296_469186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71296 ⟨469186, by decide⟩ :=
  accepted_of_selected 12 71296 ⟨469186, by decide⟩ ⟨12, 2, 0, 469186, 71296, 1601, 65536⟩
    (by decide) selected_cut_18316

theorem selected_cut_18317 : selected 9 ⟨469212, by decide⟩
    (prefixPartial 12 71297) = some ⟨12, 2, 0, 469212, 71297, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_71297_469212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71297 ⟨469212, by decide⟩ :=
  accepted_of_selected 12 71297 ⟨469212, by decide⟩ ⟨12, 2, 0, 469212, 71297, 1809, 65536⟩
    (by decide) selected_cut_18317

theorem selected_cut_18318 : selected 9 ⟨469237, by decide⟩
    (prefixPartial 12 71298) = some ⟨12, 2, 0, 469237, 71298, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_71298_469237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71298 ⟨469237, by decide⟩ :=
  accepted_of_selected 12 71298 ⟨469237, by decide⟩ ⟨12, 2, 0, 469237, 71298, 1689, 65536⟩
    (by decide) selected_cut_18318

theorem selected_cut_18319 : selected 9 ⟨469261, by decide⟩
    (prefixPartial 12 71299) = some ⟨12, 2, 0, 469261, 71299, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_71299_469261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71299 ⟨469261, by decide⟩ :=
  accepted_of_selected 12 71299 ⟨469261, by decide⟩ ⟨12, 2, 0, 469261, 71299, 1809, 65536⟩
    (by decide) selected_cut_18319

theorem unmarked_context_11_17824_469262 : frontier 10 ⟨469262, by decide⟩
    (prefixCache 11 17824) (prefixPartial 11 17824) = false := by
  decide +kernel

theorem node_context_11_17824_469262 : EJMOriginalGlobalDAGData.nodes 10 ⟨469262, by decide⟩ =
    .split (coordinate 11) (![⟨469186, by decide⟩,⟨469212, by decide⟩,⟨469237, by decide⟩,⟨469261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17824_469262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17824 ⟨469262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17824
    ⟨469262, by decide⟩ (by decide) (![⟨469186, by decide⟩,⟨469212, by decide⟩,⟨469237, by decide⟩,⟨469261, by decide⟩]) unmarked_context_11_17824_469262 node_context_11_17824_469262
  intro a
  fin_cases a
  · exact context_12_71296_469186
  · exact context_12_71297_469212
  · exact context_12_71298_469237
  · exact context_12_71299_469261

theorem selected_cut_18320 : selected 9 ⟨469287, by decide⟩
    (prefixPartial 12 71300) = some ⟨12, 2, 0, 469287, 71300, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_71300_469287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71300 ⟨469287, by decide⟩ :=
  accepted_of_selected 12 71300 ⟨469287, by decide⟩ ⟨12, 2, 0, 469287, 71300, 1877, 65536⟩
    (by decide) selected_cut_18320

theorem selected_cut_18321 : selected 9 ⟨469308, by decide⟩
    (prefixPartial 12 71301) = some ⟨12, 2, 0, 469308, 71301, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_71301_469308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71301 ⟨469308, by decide⟩ :=
  accepted_of_selected 12 71301 ⟨469308, by decide⟩ ⟨12, 2, 0, 469308, 71301, 1677, 65536⟩
    (by decide) selected_cut_18321

theorem selected_cut_18322 : selected 9 ⟨469331, by decide⟩
    (prefixPartial 12 71302) = some ⟨12, 2, 0, 469331, 71302, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_71302_469331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71302 ⟨469331, by decide⟩ :=
  accepted_of_selected 12 71302 ⟨469331, by decide⟩ ⟨12, 2, 0, 469331, 71302, 1749, 65536⟩
    (by decide) selected_cut_18322

theorem selected_cut_18323 : selected 9 ⟨469353, by decide⟩
    (prefixPartial 12 71303) = some ⟨12, 2, 0, 469353, 71303, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_71303_469353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71303 ⟨469353, by decide⟩ :=
  accepted_of_selected 12 71303 ⟨469353, by decide⟩ ⟨12, 2, 0, 469353, 71303, 1857, 65536⟩
    (by decide) selected_cut_18323

theorem unmarked_context_11_17825_469354 : frontier 10 ⟨469354, by decide⟩
    (prefixCache 11 17825) (prefixPartial 11 17825) = false := by
  decide +kernel

theorem node_context_11_17825_469354 : EJMOriginalGlobalDAGData.nodes 10 ⟨469354, by decide⟩ =
    .split (coordinate 11) (![⟨469287, by decide⟩,⟨469308, by decide⟩,⟨469331, by decide⟩,⟨469353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17825_469354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17825 ⟨469354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17825
    ⟨469354, by decide⟩ (by decide) (![⟨469287, by decide⟩,⟨469308, by decide⟩,⟨469331, by decide⟩,⟨469353, by decide⟩]) unmarked_context_11_17825_469354 node_context_11_17825_469354
  intro a
  fin_cases a
  · exact context_12_71300_469287
  · exact context_12_71301_469308
  · exact context_12_71302_469331
  · exact context_12_71303_469353

theorem selected_cut_18324 : selected 9 ⟨469373, by decide⟩
    (prefixPartial 12 71304) = some ⟨12, 2, 0, 469373, 71304, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_71304_469373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71304 ⟨469373, by decide⟩ :=
  accepted_of_selected 12 71304 ⟨469373, by decide⟩ ⟨12, 2, 0, 469373, 71304, 1641, 65536⟩
    (by decide) selected_cut_18324

theorem selected_cut_18325 : selected 9 ⟨469395, by decide⟩
    (prefixPartial 12 71305) = some ⟨12, 2, 0, 469395, 71305, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_71305_469395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71305 ⟨469395, by decide⟩ :=
  accepted_of_selected 12 71305 ⟨469395, by decide⟩ ⟨12, 2, 0, 469395, 71305, 1705, 65536⟩
    (by decide) selected_cut_18325

theorem selected_cut_18326 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 71306) = some ⟨12, 1, 0, 448662, 71306, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71306_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71306 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 71306 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 71306, 1, 65536⟩
    (by decide) selected_cut_18326

theorem selected_cut_18327 : selected 9 ⟨469411, by decide⟩
    (prefixPartial 12 71307) = some ⟨12, 2, 0, 469411, 71307, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_71307_469411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71307 ⟨469411, by decide⟩ :=
  accepted_of_selected 12 71307 ⟨469411, by decide⟩ ⟨12, 2, 0, 469411, 71307, 1709, 65536⟩
    (by decide) selected_cut_18327

theorem unmarked_context_11_17826_469412 : frontier 10 ⟨469412, by decide⟩
    (prefixCache 11 17826) (prefixPartial 11 17826) = false := by
  decide +kernel

theorem node_context_11_17826_469412 : EJMOriginalGlobalDAGData.nodes 10 ⟨469412, by decide⟩ =
    .split (coordinate 11) (![⟨469373, by decide⟩,⟨469395, by decide⟩,⟨448662, by decide⟩,⟨469411, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17826_469412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17826 ⟨469412, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17826
    ⟨469412, by decide⟩ (by decide) (![⟨469373, by decide⟩,⟨469395, by decide⟩,⟨448662, by decide⟩,⟨469411, by decide⟩]) unmarked_context_11_17826_469412 node_context_11_17826_469412
  intro a
  fin_cases a
  · exact context_12_71304_469373
  · exact context_12_71305_469395
  · exact context_12_71306_448662
  · exact context_12_71307_469411

theorem selected_cut_18328 : selected 9 ⟨469428, by decide⟩
    (prefixPartial 12 71308) = some ⟨12, 2, 0, 469428, 71308, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_71308_469428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71308 ⟨469428, by decide⟩ :=
  accepted_of_selected 12 71308 ⟨469428, by decide⟩ ⟨12, 2, 0, 469428, 71308, 1733, 65536⟩
    (by decide) selected_cut_18328

theorem selected_cut_18329 : selected 9 ⟨469445, by decide⟩
    (prefixPartial 12 71309) = some ⟨12, 2, 0, 469445, 71309, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_71309_469445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71309 ⟨469445, by decide⟩ :=
  accepted_of_selected 12 71309 ⟨469445, by decide⟩ ⟨12, 2, 0, 469445, 71309, 1737, 65536⟩
    (by decide) selected_cut_18329

theorem selected_cut_18330 : selected 9 ⟨469467, by decide⟩
    (prefixPartial 12 71310) = some ⟨12, 2, 0, 469467, 71310, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_71310_469467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71310 ⟨469467, by decide⟩ :=
  accepted_of_selected 12 71310 ⟨469467, by decide⟩ ⟨12, 2, 0, 469467, 71310, 1733, 65536⟩
    (by decide) selected_cut_18330

theorem selected_cut_18331 : selected 9 ⟨469490, by decide⟩
    (prefixPartial 12 71311) = some ⟨12, 2, 0, 469490, 71311, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_71311_469490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71311 ⟨469490, by decide⟩ :=
  accepted_of_selected 12 71311 ⟨469490, by decide⟩ ⟨12, 2, 0, 469490, 71311, 1869, 65536⟩
    (by decide) selected_cut_18331

theorem unmarked_context_11_17827_469491 : frontier 10 ⟨469491, by decide⟩
    (prefixCache 11 17827) (prefixPartial 11 17827) = false := by
  decide +kernel

theorem node_context_11_17827_469491 : EJMOriginalGlobalDAGData.nodes 10 ⟨469491, by decide⟩ =
    .split (coordinate 11) (![⟨469428, by decide⟩,⟨469445, by decide⟩,⟨469467, by decide⟩,⟨469490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17827_469491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17827 ⟨469491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17827
    ⟨469491, by decide⟩ (by decide) (![⟨469428, by decide⟩,⟨469445, by decide⟩,⟨469467, by decide⟩,⟨469490, by decide⟩]) unmarked_context_11_17827_469491 node_context_11_17827_469491
  intro a
  fin_cases a
  · exact context_12_71308_469428
  · exact context_12_71309_469445
  · exact context_12_71310_469467
  · exact context_12_71311_469490

theorem unmarked_context_10_4456_469492 : frontier 11 ⟨469492, by decide⟩
    (prefixCache 10 4456) (prefixPartial 10 4456) = false := by
  decide +kernel

theorem node_context_10_4456_469492 : EJMOriginalGlobalDAGData.nodes 11 ⟨469492, by decide⟩ =
    .split (coordinate 10) (![⟨469262, by decide⟩,⟨469354, by decide⟩,⟨469412, by decide⟩,⟨469491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4456_469492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4456 ⟨469492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4456
    ⟨469492, by decide⟩ (by decide) (![⟨469262, by decide⟩,⟨469354, by decide⟩,⟨469412, by decide⟩,⟨469491, by decide⟩]) unmarked_context_10_4456_469492 node_context_10_4456_469492
  intro a
  fin_cases a
  · exact context_11_17824_469262
  · exact context_11_17825_469354
  · exact context_11_17826_469412
  · exact context_11_17827_469491

theorem selected_cut_18332 : selected 9 ⟨469507, by decide⟩
    (prefixPartial 12 71312) = some ⟨12, 2, 0, 469507, 71312, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_71312_469507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71312 ⟨469507, by decide⟩ :=
  accepted_of_selected 12 71312 ⟨469507, by decide⟩ ⟨12, 2, 0, 469507, 71312, 1541, 65536⟩
    (by decide) selected_cut_18332

theorem selected_cut_18333 : selected 9 ⟨469526, by decide⟩
    (prefixPartial 12 71313) = some ⟨12, 2, 0, 469526, 71313, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_71313_469526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71313 ⟨469526, by decide⟩ :=
  accepted_of_selected 12 71313 ⟨469526, by decide⟩ ⟨12, 2, 0, 469526, 71313, 1685, 65536⟩
    (by decide) selected_cut_18333

theorem selected_cut_18334 : selected 9 ⟨469541, by decide⟩
    (prefixPartial 12 71314) = some ⟨12, 2, 0, 469541, 71314, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_71314_469541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71314 ⟨469541, by decide⟩ :=
  accepted_of_selected 12 71314 ⟨469541, by decide⟩ ⟨12, 2, 0, 469541, 71314, 1573, 65536⟩
    (by decide) selected_cut_18334

theorem selected_cut_18335 : selected 9 ⟨469563, by decide⟩
    (prefixPartial 12 71315) = some ⟨12, 2, 0, 469563, 71315, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_71315_469563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71315 ⟨469563, by decide⟩ :=
  accepted_of_selected 12 71315 ⟨469563, by decide⟩ ⟨12, 2, 0, 469563, 71315, 1805, 65536⟩
    (by decide) selected_cut_18335

theorem unmarked_context_11_17828_469564 : frontier 10 ⟨469564, by decide⟩
    (prefixCache 11 17828) (prefixPartial 11 17828) = false := by
  decide +kernel

theorem node_context_11_17828_469564 : EJMOriginalGlobalDAGData.nodes 10 ⟨469564, by decide⟩ =
    .split (coordinate 11) (![⟨469507, by decide⟩,⟨469526, by decide⟩,⟨469541, by decide⟩,⟨469563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17828_469564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17828 ⟨469564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17828
    ⟨469564, by decide⟩ (by decide) (![⟨469507, by decide⟩,⟨469526, by decide⟩,⟨469541, by decide⟩,⟨469563, by decide⟩]) unmarked_context_11_17828_469564 node_context_11_17828_469564
  intro a
  fin_cases a
  · exact context_12_71312_469507
  · exact context_12_71313_469526
  · exact context_12_71314_469541
  · exact context_12_71315_469563

theorem selected_cut_18336 : selected 9 ⟨469595, by decide⟩
    (prefixPartial 12 71316) = some ⟨12, 2, 0, 469595, 71316, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_71316_469595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71316 ⟨469595, by decide⟩ :=
  accepted_of_selected 12 71316 ⟨469595, by decide⟩ ⟨12, 2, 0, 469595, 71316, 2589, 65536⟩
    (by decide) selected_cut_18336

theorem selected_cut_18337 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 71317) = some ⟨12, 1, 0, 449506, 71317, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71317_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71317 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 71317 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 71317, 1, 65536⟩
    (by decide) selected_cut_18337

theorem selected_cut_18338 : selected 9 ⟨469617, by decide⟩
    (prefixPartial 12 71318) = some ⟨12, 2, 0, 469617, 71318, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_71318_469617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71318 ⟨469617, by decide⟩ :=
  accepted_of_selected 12 71318 ⟨469617, by decide⟩ ⟨12, 2, 0, 469617, 71318, 2357, 65536⟩
    (by decide) selected_cut_18338

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
