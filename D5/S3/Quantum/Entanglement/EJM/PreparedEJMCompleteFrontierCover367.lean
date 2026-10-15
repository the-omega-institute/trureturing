/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover366
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_35235 : selected 10 ⟨923706, by decide⟩
    (prefixPartial 11 71082) = some ⟨11, 2, 0, 923706, 71082, 1769, 262144⟩ := by
  decide +kernel

theorem context_11_71082_923706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71082 ⟨923706, by decide⟩ :=
  accepted_of_selected 11 71082 ⟨923706, by decide⟩ ⟨11, 2, 0, 923706, 71082, 1769, 262144⟩
    (by decide) selected_cut_35235

theorem selected_cut_35236 : selected 10 ⟨923752, by decide⟩
    (prefixPartial 11 71083) = some ⟨11, 2, 0, 923752, 71083, 3309, 262144⟩ := by
  decide +kernel

theorem context_11_71083_923752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71083 ⟨923752, by decide⟩ :=
  accepted_of_selected 11 71083 ⟨923752, by decide⟩ ⟨11, 2, 0, 923752, 71083, 3309, 262144⟩
    (by decide) selected_cut_35236

theorem unmarked_context_10_17770_923753 : frontier 11 ⟨923753, by decide⟩
    (prefixCache 10 17770) (prefixPartial 10 17770) = false := by
  decide +kernel

theorem node_context_10_17770_923753 : EJMOriginalGlobalDAGData.nodes 11 ⟨923753, by decide⟩ =
    .split (coordinate 10) (![⟨923658, by decide⟩,⟨923681, by decide⟩,⟨923706, by decide⟩,⟨923752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17770_923753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17770 ⟨923753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17770
    ⟨923753, by decide⟩ (by decide) (![⟨923658, by decide⟩,⟨923681, by decide⟩,⟨923706, by decide⟩,⟨923752, by decide⟩]) unmarked_context_10_17770_923753 node_context_10_17770_923753
  intro a
  fin_cases a
  · exact context_11_71080_923658
  · exact context_11_71081_923681
  · exact context_11_71082_923706
  · exact context_11_71083_923752

theorem selected_cut_35237 : selected 10 ⟨923785, by decide⟩
    (prefixPartial 11 71084) = some ⟨11, 2, 0, 923785, 71084, 2773, 262144⟩ := by
  decide +kernel

theorem context_11_71084_923785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71084 ⟨923785, by decide⟩ :=
  accepted_of_selected 11 71084 ⟨923785, by decide⟩ ⟨11, 2, 0, 923785, 71084, 2773, 262144⟩
    (by decide) selected_cut_35237

theorem selected_cut_35238 : selected 10 ⟨923816, by decide⟩
    (prefixPartial 11 71085) = some ⟨11, 2, 0, 923816, 71085, 2573, 262144⟩ := by
  decide +kernel

theorem context_11_71085_923816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71085 ⟨923816, by decide⟩ :=
  accepted_of_selected 11 71085 ⟨923816, by decide⟩ ⟨11, 2, 0, 923816, 71085, 2573, 262144⟩
    (by decide) selected_cut_35238

theorem selected_cut_35239 : selected 10 ⟨923840, by decide⟩
    (prefixPartial 11 71086) = some ⟨11, 2, 0, 923840, 71086, 1893, 262144⟩ := by
  decide +kernel

theorem context_11_71086_923840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71086 ⟨923840, by decide⟩ :=
  accepted_of_selected 11 71086 ⟨923840, by decide⟩ ⟨11, 2, 0, 923840, 71086, 1893, 262144⟩
    (by decide) selected_cut_35239

theorem selected_cut_35240 : selected 10 ⟨923874, by decide⟩
    (prefixPartial 11 71087) = some ⟨11, 2, 0, 923874, 71087, 2445, 262144⟩ := by
  decide +kernel

theorem context_11_71087_923874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71087 ⟨923874, by decide⟩ :=
  accepted_of_selected 11 71087 ⟨923874, by decide⟩ ⟨11, 2, 0, 923874, 71087, 2445, 262144⟩
    (by decide) selected_cut_35240

theorem unmarked_context_10_17771_923875 : frontier 11 ⟨923875, by decide⟩
    (prefixCache 10 17771) (prefixPartial 10 17771) = false := by
  decide +kernel

theorem node_context_10_17771_923875 : EJMOriginalGlobalDAGData.nodes 11 ⟨923875, by decide⟩ =
    .split (coordinate 10) (![⟨923785, by decide⟩,⟨923816, by decide⟩,⟨923840, by decide⟩,⟨923874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17771_923875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17771 ⟨923875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17771
    ⟨923875, by decide⟩ (by decide) (![⟨923785, by decide⟩,⟨923816, by decide⟩,⟨923840, by decide⟩,⟨923874, by decide⟩]) unmarked_context_10_17771_923875 node_context_10_17771_923875
  intro a
  fin_cases a
  · exact context_11_71084_923785
  · exact context_11_71085_923816
  · exact context_11_71086_923840
  · exact context_11_71087_923874

theorem unmarked_context_9_4442_923876 : frontier 12 ⟨923876, by decide⟩
    (prefixCache 9 4442) (prefixPartial 9 4442) = false := by
  decide +kernel

theorem node_context_9_4442_923876 : EJMOriginalGlobalDAGData.nodes 12 ⟨923876, by decide⟩ =
    .split (coordinate 9) (![⟨923427, by decide⟩,⟨923610, by decide⟩,⟨923753, by decide⟩,⟨923875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4442_923876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4442 ⟨923876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4442
    ⟨923876, by decide⟩ (by decide) (![⟨923427, by decide⟩,⟨923610, by decide⟩,⟨923753, by decide⟩,⟨923875, by decide⟩]) unmarked_context_9_4442_923876 node_context_9_4442_923876
  intro a
  fin_cases a
  · exact context_10_17768_923427
  · exact context_10_17769_923610
  · exact context_10_17770_923753
  · exact context_10_17771_923875

theorem selected_cut_35241 : selected 10 ⟨923939, by decide⟩
    (prefixPartial 11 71088) = some ⟨11, 2, 0, 923939, 71088, 3113, 262144⟩ := by
  decide +kernel

theorem context_11_71088_923939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71088 ⟨923939, by decide⟩ :=
  accepted_of_selected 11 71088 ⟨923939, by decide⟩ ⟨11, 2, 0, 923939, 71088, 3113, 262144⟩
    (by decide) selected_cut_35241

theorem selected_cut_35242 : selected 10 ⟨923988, by decide⟩
    (prefixPartial 11 71089) = some ⟨11, 2, 0, 923988, 71089, 2561, 262144⟩ := by
  decide +kernel

theorem context_11_71089_923988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71089 ⟨923988, by decide⟩ :=
  accepted_of_selected 11 71089 ⟨923988, by decide⟩ ⟨11, 2, 0, 923988, 71089, 2561, 262144⟩
    (by decide) selected_cut_35242

theorem selected_cut_35243 : selected 10 ⟨924022, by decide⟩
    (prefixPartial 11 71090) = some ⟨11, 2, 0, 924022, 71090, 1761, 262144⟩ := by
  decide +kernel

theorem context_11_71090_924022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71090 ⟨924022, by decide⟩ :=
  accepted_of_selected 11 71090 ⟨924022, by decide⟩ ⟨11, 2, 0, 924022, 71090, 1761, 262144⟩
    (by decide) selected_cut_35243

theorem selected_cut_35244 : selected 10 ⟨924074, by decide⟩
    (prefixPartial 11 71091) = some ⟨11, 2, 0, 924074, 71091, 2385, 262144⟩ := by
  decide +kernel

theorem context_11_71091_924074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71091 ⟨924074, by decide⟩ :=
  accepted_of_selected 11 71091 ⟨924074, by decide⟩ ⟨11, 2, 0, 924074, 71091, 2385, 262144⟩
    (by decide) selected_cut_35244

theorem unmarked_context_10_17772_924075 : frontier 11 ⟨924075, by decide⟩
    (prefixCache 10 17772) (prefixPartial 10 17772) = false := by
  decide +kernel

theorem node_context_10_17772_924075 : EJMOriginalGlobalDAGData.nodes 11 ⟨924075, by decide⟩ =
    .split (coordinate 10) (![⟨923939, by decide⟩,⟨923988, by decide⟩,⟨924022, by decide⟩,⟨924074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17772_924075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17772 ⟨924075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17772
    ⟨924075, by decide⟩ (by decide) (![⟨923939, by decide⟩,⟨923988, by decide⟩,⟨924022, by decide⟩,⟨924074, by decide⟩]) unmarked_context_10_17772_924075 node_context_10_17772_924075
  intro a
  fin_cases a
  · exact context_11_71088_923939
  · exact context_11_71089_923988
  · exact context_11_71090_924022
  · exact context_11_71091_924074

theorem selected_cut_35245 : selected 10 ⟨924101, by decide⟩
    (prefixPartial 11 71092) = some ⟨11, 2, 0, 924101, 71092, 1649, 262144⟩ := by
  decide +kernel

theorem context_11_71092_924101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71092 ⟨924101, by decide⟩ :=
  accepted_of_selected 11 71092 ⟨924101, by decide⟩ ⟨11, 2, 0, 924101, 71092, 1649, 262144⟩
    (by decide) selected_cut_35245

theorem selected_cut_35246 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 71093) = some ⟨11, 1, 0, 892405, 71093, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71093_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71093 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 71093 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 71093, 1, 262144⟩
    (by decide) selected_cut_35246

theorem selected_cut_35247 : selected 10 ⟨924115, by decide⟩
    (prefixPartial 11 71094) = some ⟨11, 2, 0, 924115, 71094, 1041, 262144⟩ := by
  decide +kernel

theorem context_11_71094_924115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71094 ⟨924115, by decide⟩ :=
  accepted_of_selected 11 71094 ⟨924115, by decide⟩ ⟨11, 2, 0, 924115, 71094, 1041, 262144⟩
    (by decide) selected_cut_35247

theorem selected_cut_35248 : selected 10 ⟨924136, by decide⟩
    (prefixPartial 11 71095) = some ⟨11, 2, 0, 924136, 71095, 1409, 262144⟩ := by
  decide +kernel

theorem context_11_71095_924136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71095 ⟨924136, by decide⟩ :=
  accepted_of_selected 11 71095 ⟨924136, by decide⟩ ⟨11, 2, 0, 924136, 71095, 1409, 262144⟩
    (by decide) selected_cut_35248

theorem unmarked_context_10_17773_924137 : frontier 11 ⟨924137, by decide⟩
    (prefixCache 10 17773) (prefixPartial 10 17773) = false := by
  decide +kernel

theorem node_context_10_17773_924137 : EJMOriginalGlobalDAGData.nodes 11 ⟨924137, by decide⟩ =
    .split (coordinate 10) (![⟨924101, by decide⟩,⟨892405, by decide⟩,⟨924115, by decide⟩,⟨924136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17773_924137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17773 ⟨924137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17773
    ⟨924137, by decide⟩ (by decide) (![⟨924101, by decide⟩,⟨892405, by decide⟩,⟨924115, by decide⟩,⟨924136, by decide⟩]) unmarked_context_10_17773_924137 node_context_10_17773_924137
  intro a
  fin_cases a
  · exact context_11_71092_924101
  · exact context_11_71093_892405
  · exact context_11_71094_924115
  · exact context_11_71095_924136

theorem selected_cut_35249 : selected 11 ⟨924192, by decide⟩
    (prefixPartial 10 17774) = some ⟨10, 2, 0, 924192, 17774, 3305, 1048576⟩ := by
  decide +kernel

theorem context_10_17774_924192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17774 ⟨924192, by decide⟩ :=
  accepted_of_selected 10 17774 ⟨924192, by decide⟩ ⟨10, 2, 0, 924192, 17774, 3305, 1048576⟩
    (by decide) selected_cut_35249

theorem selected_cut_35250 : selected 11 ⟨924238, by decide⟩
    (prefixPartial 10 17775) = some ⟨10, 2, 0, 924238, 17775, 957, 1048576⟩ := by
  decide +kernel

theorem context_10_17775_924238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17775 ⟨924238, by decide⟩ :=
  accepted_of_selected 10 17775 ⟨924238, by decide⟩ ⟨10, 2, 0, 924238, 17775, 957, 1048576⟩
    (by decide) selected_cut_35250

theorem unmarked_context_9_4443_924239 : frontier 12 ⟨924239, by decide⟩
    (prefixCache 9 4443) (prefixPartial 9 4443) = false := by
  decide +kernel

theorem node_context_9_4443_924239 : EJMOriginalGlobalDAGData.nodes 12 ⟨924239, by decide⟩ =
    .split (coordinate 9) (![⟨924075, by decide⟩,⟨924137, by decide⟩,⟨924192, by decide⟩,⟨924238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4443_924239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4443 ⟨924239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4443
    ⟨924239, by decide⟩ (by decide) (![⟨924075, by decide⟩,⟨924137, by decide⟩,⟨924192, by decide⟩,⟨924238, by decide⟩]) unmarked_context_9_4443_924239 node_context_9_4443_924239
  intro a
  fin_cases a
  · exact context_10_17772_924075
  · exact context_10_17773_924137
  · exact context_10_17774_924192
  · exact context_10_17775_924238

theorem unmarked_context_8_1110_924240 : frontier 13 ⟨924240, by decide⟩
    (prefixCache 8 1110) (prefixPartial 8 1110) = false := by
  decide +kernel

theorem node_context_8_1110_924240 : EJMOriginalGlobalDAGData.nodes 13 ⟨924240, by decide⟩ =
    .split (coordinate 8) (![⟨921875, by decide⟩,⟨923118, by decide⟩,⟨923876, by decide⟩,⟨924239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1110_924240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1110 ⟨924240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1110
    ⟨924240, by decide⟩ (by decide) (![⟨921875, by decide⟩,⟨923118, by decide⟩,⟨923876, by decide⟩,⟨924239, by decide⟩]) unmarked_context_8_1110_924240 node_context_8_1110_924240
  intro a
  fin_cases a
  · exact context_9_4440_921875
  · exact context_9_4441_923118
  · exact context_9_4442_923876
  · exact context_9_4443_924239

theorem selected_cut_35251 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 1111) = some ⟨8, 1, 0, 14298, 1111, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1111_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1111 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 1111 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 1111, 1, 16777216⟩
    (by decide) selected_cut_35251

theorem unmarked_context_7_277_924241 : frontier 14 ⟨924241, by decide⟩
    (prefixCache 7 277) (prefixPartial 7 277) = false := by
  decide +kernel

theorem node_context_7_277_924241 : EJMOriginalGlobalDAGData.nodes 14 ⟨924241, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨919185, by decide⟩,⟨924240, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_277_924241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 277 ⟨924241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 277
    ⟨924241, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨919185, by decide⟩,⟨924240, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_277_924241 node_context_7_277_924241
  intro a
  fin_cases a
  · exact context_8_1108_14300
  · exact context_8_1109_919185
  · exact context_8_1110_924240
  · exact context_8_1111_14298

theorem selected_cut_35252 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 1112) = some ⟨8, 1, 0, 14300, 1112, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1112_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1112 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 1112 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 1112, 1, 16777216⟩
    (by decide) selected_cut_35252

theorem selected_cut_35253 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 1113) = some ⟨8, 1, 0, 14300, 1113, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1113_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1113 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 1113 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 1113, 1, 16777216⟩
    (by decide) selected_cut_35253

theorem selected_cut_35254 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 285184) = some ⟨12, 1, 0, 34034, 285184, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285184_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285184 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 285184 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 285184, 1, 65536⟩
    (by decide) selected_cut_35254

theorem selected_cut_35255 : selected 9 ⟨924327, by decide⟩
    (prefixPartial 12 285185) = some ⟨12, 2, 0, 924327, 285185, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_285185_924327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285185 ⟨924327, by decide⟩ :=
  accepted_of_selected 12 285185 ⟨924327, by decide⟩ ⟨12, 2, 0, 924327, 285185, 3945, 65536⟩
    (by decide) selected_cut_35255

theorem selected_cut_35256 : selected 8 ⟨924357, by decide⟩
    (prefixPartial 13 1140744) = some ⟨13, 2, 0, 924357, 1140744, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_1140744_924357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1140744 ⟨924357, by decide⟩ :=
  accepted_of_selected 13 1140744 ⟨924357, by decide⟩ ⟨13, 2, 0, 924357, 1140744, 1565, 16384⟩
    (by decide) selected_cut_35256

theorem selected_cut_35257 : selected 8 ⟨924376, by decide⟩
    (prefixPartial 13 1140745) = some ⟨13, 2, 0, 924376, 1140745, 761, 16384⟩ := by
  decide +kernel

theorem context_13_1140745_924376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1140745 ⟨924376, by decide⟩ :=
  accepted_of_selected 13 1140745 ⟨924376, by decide⟩ ⟨13, 2, 0, 924376, 1140745, 761, 16384⟩
    (by decide) selected_cut_35257

theorem selected_cut_35258 : selected 8 ⟨924397, by decide⟩
    (prefixPartial 13 1140746) = some ⟨13, 2, 0, 924397, 1140746, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_1140746_924397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1140746 ⟨924397, by decide⟩ :=
  accepted_of_selected 13 1140746 ⟨924397, by decide⟩ ⟨13, 2, 0, 924397, 1140746, 1181, 16384⟩
    (by decide) selected_cut_35258

theorem selected_cut_35259 : selected 8 ⟨924403, by decide⟩
    (prefixPartial 13 1140747) = some ⟨13, 2, 0, 924403, 1140747, 633, 16384⟩ := by
  decide +kernel

theorem context_13_1140747_924403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1140747 ⟨924403, by decide⟩ :=
  accepted_of_selected 13 1140747 ⟨924403, by decide⟩ ⟨13, 2, 0, 924403, 1140747, 633, 16384⟩
    (by decide) selected_cut_35259

theorem unmarked_context_12_285186_924404 : frontier 9 ⟨924404, by decide⟩
    (prefixCache 12 285186) (prefixPartial 12 285186) = false := by
  decide +kernel

theorem node_context_12_285186_924404 : EJMOriginalGlobalDAGData.nodes 9 ⟨924404, by decide⟩ =
    .split (coordinate 12) (![⟨924357, by decide⟩,⟨924376, by decide⟩,⟨924397, by decide⟩,⟨924403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_285186_924404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285186 ⟨924404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 285186
    ⟨924404, by decide⟩ (by decide) (![⟨924357, by decide⟩,⟨924376, by decide⟩,⟨924397, by decide⟩,⟨924403, by decide⟩]) unmarked_context_12_285186_924404 node_context_12_285186_924404
  intro a
  fin_cases a
  · exact context_13_1140744_924357
  · exact context_13_1140745_924376
  · exact context_13_1140746_924397
  · exact context_13_1140747_924403

theorem selected_cut_35260 : selected 8 ⟨924447, by decide⟩
    (prefixPartial 13 1140748) = some ⟨13, 2, 0, 924447, 1140748, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_1140748_924447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1140748 ⟨924447, by decide⟩ :=
  accepted_of_selected 13 1140748 ⟨924447, by decide⟩ ⟨13, 2, 0, 924447, 1140748, 1717, 16384⟩
    (by decide) selected_cut_35260

theorem selected_cut_35261 : selected 8 ⟨924468, by decide⟩
    (prefixPartial 13 1140749) = some ⟨13, 2, 0, 924468, 1140749, 813, 16384⟩ := by
  decide +kernel

theorem context_13_1140749_924468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1140749 ⟨924468, by decide⟩ :=
  accepted_of_selected 13 1140749 ⟨924468, by decide⟩ ⟨13, 2, 0, 924468, 1140749, 813, 16384⟩
    (by decide) selected_cut_35261

theorem selected_cut_35262 : selected 8 ⟨924485, by decide⟩
    (prefixPartial 13 1140750) = some ⟨13, 2, 0, 924485, 1140750, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_1140750_924485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1140750 ⟨924485, by decide⟩ :=
  accepted_of_selected 13 1140750 ⟨924485, by decide⟩ ⟨13, 2, 0, 924485, 1140750, 1081, 16384⟩
    (by decide) selected_cut_35262

theorem selected_cut_35263 : selected 8 ⟨924491, by decide⟩
    (prefixPartial 13 1140751) = some ⟨13, 2, 0, 924491, 1140751, 637, 16384⟩ := by
  decide +kernel

theorem context_13_1140751_924491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1140751 ⟨924491, by decide⟩ :=
  accepted_of_selected 13 1140751 ⟨924491, by decide⟩ ⟨13, 2, 0, 924491, 1140751, 637, 16384⟩
    (by decide) selected_cut_35263

theorem unmarked_context_12_285187_924492 : frontier 9 ⟨924492, by decide⟩
    (prefixCache 12 285187) (prefixPartial 12 285187) = false := by
  decide +kernel

theorem node_context_12_285187_924492 : EJMOriginalGlobalDAGData.nodes 9 ⟨924492, by decide⟩ =
    .split (coordinate 12) (![⟨924447, by decide⟩,⟨924468, by decide⟩,⟨924485, by decide⟩,⟨924491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_285187_924492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285187 ⟨924492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 285187
    ⟨924492, by decide⟩ (by decide) (![⟨924447, by decide⟩,⟨924468, by decide⟩,⟨924485, by decide⟩,⟨924491, by decide⟩]) unmarked_context_12_285187_924492 node_context_12_285187_924492
  intro a
  fin_cases a
  · exact context_13_1140748_924447
  · exact context_13_1140749_924468
  · exact context_13_1140750_924485
  · exact context_13_1140751_924491

theorem unmarked_context_11_71296_924493 : frontier 10 ⟨924493, by decide⟩
    (prefixCache 11 71296) (prefixPartial 11 71296) = false := by
  decide +kernel

theorem node_context_11_71296_924493 : EJMOriginalGlobalDAGData.nodes 10 ⟨924493, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨924327, by decide⟩,⟨924404, by decide⟩,⟨924492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71296_924493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71296 ⟨924493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71296
    ⟨924493, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨924327, by decide⟩,⟨924404, by decide⟩,⟨924492, by decide⟩]) unmarked_context_11_71296_924493 node_context_11_71296_924493
  intro a
  fin_cases a
  · exact context_12_285184_34034
  · exact context_12_285185_924327
  · exact context_12_285186_924404
  · exact context_12_285187_924492

theorem selected_cut_35264 : selected 9 ⟨924596, by decide⟩
    (prefixPartial 12 285188) = some ⟨12, 2, 0, 924596, 285188, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_285188_924596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285188 ⟨924596, by decide⟩ :=
  accepted_of_selected 12 285188 ⟨924596, by decide⟩ ⟨12, 2, 0, 924596, 285188, 3009, 65536⟩
    (by decide) selected_cut_35264

theorem selected_cut_35265 : selected 9 ⟨924666, by decide⟩
    (prefixPartial 12 285189) = some ⟨12, 2, 0, 924666, 285189, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_285189_924666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285189 ⟨924666, by decide⟩ :=
  accepted_of_selected 12 285189 ⟨924666, by decide⟩ ⟨12, 2, 0, 924666, 285189, 3509, 65536⟩
    (by decide) selected_cut_35265

theorem selected_cut_35266 : selected 9 ⟨924737, by decide⟩
    (prefixPartial 12 285190) = some ⟨12, 2, 0, 924737, 285190, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_285190_924737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285190 ⟨924737, by decide⟩ :=
  accepted_of_selected 12 285190 ⟨924737, by decide⟩ ⟨12, 2, 0, 924737, 285190, 3509, 65536⟩
    (by decide) selected_cut_35266

theorem selected_cut_35267 : selected 9 ⟨924826, by decide⟩
    (prefixPartial 12 285191) = some ⟨12, 2, 0, 924826, 285191, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_285191_924826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285191 ⟨924826, by decide⟩ :=
  accepted_of_selected 12 285191 ⟨924826, by decide⟩ ⟨12, 2, 0, 924826, 285191, 3753, 65536⟩
    (by decide) selected_cut_35267

theorem unmarked_context_11_71297_924827 : frontier 10 ⟨924827, by decide⟩
    (prefixCache 11 71297) (prefixPartial 11 71297) = false := by
  decide +kernel

theorem node_context_11_71297_924827 : EJMOriginalGlobalDAGData.nodes 10 ⟨924827, by decide⟩ =
    .split (coordinate 11) (![⟨924596, by decide⟩,⟨924666, by decide⟩,⟨924737, by decide⟩,⟨924826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71297_924827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71297 ⟨924827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71297
    ⟨924827, by decide⟩ (by decide) (![⟨924596, by decide⟩,⟨924666, by decide⟩,⟨924737, by decide⟩,⟨924826, by decide⟩]) unmarked_context_11_71297_924827 node_context_11_71297_924827
  intro a
  fin_cases a
  · exact context_12_285188_924596
  · exact context_12_285189_924666
  · exact context_12_285190_924737
  · exact context_12_285191_924826

theorem selected_cut_35268 : selected 9 ⟨924907, by decide⟩
    (prefixPartial 12 285192) = some ⟨12, 2, 0, 924907, 285192, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_285192_924907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285192 ⟨924907, by decide⟩ :=
  accepted_of_selected 12 285192 ⟨924907, by decide⟩ ⟨12, 2, 0, 924907, 285192, 2985, 65536⟩
    (by decide) selected_cut_35268

theorem selected_cut_35269 : selected 9 ⟨924972, by decide⟩
    (prefixPartial 12 285193) = some ⟨12, 2, 0, 924972, 285193, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_285193_924972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285193 ⟨924972, by decide⟩ :=
  accepted_of_selected 12 285193 ⟨924972, by decide⟩ ⟨12, 2, 0, 924972, 285193, 3633, 65536⟩
    (by decide) selected_cut_35269

theorem selected_cut_35270 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 285194) = some ⟨12, 1, 0, 893903, 285194, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285194_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285194 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 285194 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 285194, 1, 65536⟩
    (by decide) selected_cut_35270

theorem selected_cut_35271 : selected 9 ⟨925051, by decide⟩
    (prefixPartial 12 285195) = some ⟨12, 2, 0, 925051, 285195, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_285195_925051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285195 ⟨925051, by decide⟩ :=
  accepted_of_selected 12 285195 ⟨925051, by decide⟩ ⟨12, 2, 0, 925051, 285195, 4001, 65536⟩
    (by decide) selected_cut_35271

theorem unmarked_context_11_71298_925052 : frontier 10 ⟨925052, by decide⟩
    (prefixCache 11 71298) (prefixPartial 11 71298) = false := by
  decide +kernel

theorem node_context_11_71298_925052 : EJMOriginalGlobalDAGData.nodes 10 ⟨925052, by decide⟩ =
    .split (coordinate 11) (![⟨924907, by decide⟩,⟨924972, by decide⟩,⟨893903, by decide⟩,⟨925051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71298_925052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71298 ⟨925052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71298
    ⟨925052, by decide⟩ (by decide) (![⟨924907, by decide⟩,⟨924972, by decide⟩,⟨893903, by decide⟩,⟨925051, by decide⟩]) unmarked_context_11_71298_925052 node_context_11_71298_925052
  intro a
  fin_cases a
  · exact context_12_285192_924907
  · exact context_12_285193_924972
  · exact context_12_285194_893903
  · exact context_12_285195_925051

theorem selected_cut_35272 : selected 9 ⟨925168, by decide⟩
    (prefixPartial 12 285196) = some ⟨12, 2, 0, 925168, 285196, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_285196_925168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285196 ⟨925168, by decide⟩ :=
  accepted_of_selected 12 285196 ⟨925168, by decide⟩ ⟨12, 2, 0, 925168, 285196, 3293, 65536⟩
    (by decide) selected_cut_35272

theorem selected_cut_35273 : selected 9 ⟨925247, by decide⟩
    (prefixPartial 12 285197) = some ⟨12, 2, 0, 925247, 285197, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_285197_925247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285197 ⟨925247, by decide⟩ :=
  accepted_of_selected 12 285197 ⟨925247, by decide⟩ ⟨12, 2, 0, 925247, 285197, 3893, 65536⟩
    (by decide) selected_cut_35273

theorem selected_cut_35274 : selected 8 ⟨925277, by decide⟩
    (prefixPartial 13 1140792) = some ⟨13, 2, 0, 925277, 1140792, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_1140792_925277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1140792 ⟨925277, by decide⟩ :=
  accepted_of_selected 13 1140792 ⟨925277, by decide⟩ ⟨13, 2, 0, 925277, 1140792, 1309, 16384⟩
    (by decide) selected_cut_35274

theorem selected_cut_35275 : selected 8 ⟨925293, by decide⟩
    (prefixPartial 13 1140793) = some ⟨13, 2, 0, 925293, 1140793, 817, 16384⟩ := by
  decide +kernel

theorem context_13_1140793_925293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1140793 ⟨925293, by decide⟩ :=
  accepted_of_selected 13 1140793 ⟨925293, by decide⟩ ⟨13, 2, 0, 925293, 1140793, 817, 16384⟩
    (by decide) selected_cut_35275

theorem selected_cut_35276 : selected 8 ⟨925320, by decide⟩
    (prefixPartial 13 1140794) = some ⟨13, 2, 0, 925320, 1140794, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_1140794_925320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1140794 ⟨925320, by decide⟩ :=
  accepted_of_selected 13 1140794 ⟨925320, by decide⟩ ⟨13, 2, 0, 925320, 1140794, 1381, 16384⟩
    (by decide) selected_cut_35276

theorem selected_cut_35277 : selected 8 ⟨925329, by decide⟩
    (prefixPartial 13 1140795) = some ⟨13, 2, 0, 925329, 1140795, 685, 16384⟩ := by
  decide +kernel

theorem context_13_1140795_925329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1140795 ⟨925329, by decide⟩ :=
  accepted_of_selected 13 1140795 ⟨925329, by decide⟩ ⟨13, 2, 0, 925329, 1140795, 685, 16384⟩
    (by decide) selected_cut_35277

theorem unmarked_context_12_285198_925330 : frontier 9 ⟨925330, by decide⟩
    (prefixCache 12 285198) (prefixPartial 12 285198) = false := by
  decide +kernel

theorem node_context_12_285198_925330 : EJMOriginalGlobalDAGData.nodes 9 ⟨925330, by decide⟩ =
    .split (coordinate 12) (![⟨925277, by decide⟩,⟨925293, by decide⟩,⟨925320, by decide⟩,⟨925329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_285198_925330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285198 ⟨925330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 285198
    ⟨925330, by decide⟩ (by decide) (![⟨925277, by decide⟩,⟨925293, by decide⟩,⟨925320, by decide⟩,⟨925329, by decide⟩]) unmarked_context_12_285198_925330 node_context_12_285198_925330
  intro a
  fin_cases a
  · exact context_13_1140792_925277
  · exact context_13_1140793_925293
  · exact context_13_1140794_925320
  · exact context_13_1140795_925329

theorem selected_cut_35278 : selected 9 ⟨925414, by decide⟩
    (prefixPartial 12 285199) = some ⟨12, 2, 0, 925414, 285199, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_285199_925414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285199 ⟨925414, by decide⟩ :=
  accepted_of_selected 12 285199 ⟨925414, by decide⟩ ⟨12, 2, 0, 925414, 285199, 3933, 65536⟩
    (by decide) selected_cut_35278

theorem unmarked_context_11_71299_925415 : frontier 10 ⟨925415, by decide⟩
    (prefixCache 11 71299) (prefixPartial 11 71299) = false := by
  decide +kernel

theorem node_context_11_71299_925415 : EJMOriginalGlobalDAGData.nodes 10 ⟨925415, by decide⟩ =
    .split (coordinate 11) (![⟨925168, by decide⟩,⟨925247, by decide⟩,⟨925330, by decide⟩,⟨925414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71299_925415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71299 ⟨925415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71299
    ⟨925415, by decide⟩ (by decide) (![⟨925168, by decide⟩,⟨925247, by decide⟩,⟨925330, by decide⟩,⟨925414, by decide⟩]) unmarked_context_11_71299_925415 node_context_11_71299_925415
  intro a
  fin_cases a
  · exact context_12_285196_925168
  · exact context_12_285197_925247
  · exact context_12_285198_925330
  · exact context_12_285199_925414

theorem unmarked_context_10_17824_925416 : frontier 11 ⟨925416, by decide⟩
    (prefixCache 10 17824) (prefixPartial 10 17824) = false := by
  decide +kernel

theorem node_context_10_17824_925416 : EJMOriginalGlobalDAGData.nodes 11 ⟨925416, by decide⟩ =
    .split (coordinate 10) (![⟨924493, by decide⟩,⟨924827, by decide⟩,⟨925052, by decide⟩,⟨925415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17824_925416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17824 ⟨925416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17824
    ⟨925416, by decide⟩ (by decide) (![⟨924493, by decide⟩,⟨924827, by decide⟩,⟨925052, by decide⟩,⟨925415, by decide⟩]) unmarked_context_10_17824_925416 node_context_10_17824_925416
  intro a
  fin_cases a
  · exact context_11_71296_924493
  · exact context_11_71297_924827
  · exact context_11_71298_925052
  · exact context_11_71299_925415

theorem selected_cut_35279 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 285200) = some ⟨12, 1, 0, 1738, 285200, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285200_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285200 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 285200 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 285200, 1, 65536⟩
    (by decide) selected_cut_35279

theorem selected_cut_35280 : selected 9 ⟨925484, by decide⟩
    (prefixPartial 12 285201) = some ⟨12, 2, 0, 925484, 285201, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_285201_925484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285201 ⟨925484, by decide⟩ :=
  accepted_of_selected 12 285201 ⟨925484, by decide⟩ ⟨12, 2, 0, 925484, 285201, 2345, 65536⟩
    (by decide) selected_cut_35280

theorem selected_cut_35281 : selected 9 ⟨925556, by decide⟩
    (prefixPartial 12 285202) = some ⟨12, 2, 0, 925556, 285202, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_285202_925556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285202 ⟨925556, by decide⟩ :=
  accepted_of_selected 12 285202 ⟨925556, by decide⟩ ⟨12, 2, 0, 925556, 285202, 3629, 65536⟩
    (by decide) selected_cut_35281

theorem selected_cut_35282 : selected 9 ⟨925639, by decide⟩
    (prefixPartial 12 285203) = some ⟨12, 2, 0, 925639, 285203, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_285203_925639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285203 ⟨925639, by decide⟩ :=
  accepted_of_selected 12 285203 ⟨925639, by decide⟩ ⟨12, 2, 0, 925639, 285203, 3945, 65536⟩
    (by decide) selected_cut_35282

theorem unmarked_context_11_71300_925640 : frontier 10 ⟨925640, by decide⟩
    (prefixCache 11 71300) (prefixPartial 11 71300) = false := by
  decide +kernel

theorem node_context_11_71300_925640 : EJMOriginalGlobalDAGData.nodes 10 ⟨925640, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨925484, by decide⟩,⟨925556, by decide⟩,⟨925639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71300_925640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71300 ⟨925640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71300
    ⟨925640, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨925484, by decide⟩,⟨925556, by decide⟩,⟨925639, by decide⟩]) unmarked_context_11_71300_925640 node_context_11_71300_925640
  intro a
  fin_cases a
  · exact context_12_285200_1738
  · exact context_12_285201_925484
  · exact context_12_285202_925556
  · exact context_12_285203_925639

theorem selected_cut_35283 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 285204) = some ⟨12, 1, 0, 1738, 285204, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285204_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285204 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 285204 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 285204, 1, 65536⟩
    (by decide) selected_cut_35283

theorem selected_cut_35284 : selected 9 ⟨925688, by decide⟩
    (prefixPartial 12 285205) = some ⟨12, 2, 0, 925688, 285205, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_285205_925688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285205 ⟨925688, by decide⟩ :=
  accepted_of_selected 12 285205 ⟨925688, by decide⟩ ⟨12, 2, 0, 925688, 285205, 1973, 65536⟩
    (by decide) selected_cut_35284

theorem selected_cut_35285 : selected 9 ⟨925743, by decide⟩
    (prefixPartial 12 285206) = some ⟨12, 2, 0, 925743, 285206, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_285206_925743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285206 ⟨925743, by decide⟩ :=
  accepted_of_selected 12 285206 ⟨925743, by decide⟩ ⟨12, 2, 0, 925743, 285206, 2813, 65536⟩
    (by decide) selected_cut_35285

theorem selected_cut_35286 : selected 9 ⟨925804, by decide⟩
    (prefixPartial 12 285207) = some ⟨12, 2, 0, 925804, 285207, 3113, 65536⟩ := by
  decide +kernel

theorem context_12_285207_925804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285207 ⟨925804, by decide⟩ :=
  accepted_of_selected 12 285207 ⟨925804, by decide⟩ ⟨12, 2, 0, 925804, 285207, 3113, 65536⟩
    (by decide) selected_cut_35286

theorem unmarked_context_11_71301_925805 : frontier 10 ⟨925805, by decide⟩
    (prefixCache 11 71301) (prefixPartial 11 71301) = false := by
  decide +kernel

theorem node_context_11_71301_925805 : EJMOriginalGlobalDAGData.nodes 10 ⟨925805, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨925688, by decide⟩,⟨925743, by decide⟩,⟨925804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71301_925805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71301 ⟨925805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71301
    ⟨925805, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨925688, by decide⟩,⟨925743, by decide⟩,⟨925804, by decide⟩]) unmarked_context_11_71301_925805 node_context_11_71301_925805
  intro a
  fin_cases a
  · exact context_12_285204_1738
  · exact context_12_285205_925688
  · exact context_12_285206_925743
  · exact context_12_285207_925804

theorem selected_cut_35287 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 285208) = some ⟨12, 1, 0, 1738, 285208, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285208_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285208 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 285208 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 285208, 1, 65536⟩
    (by decide) selected_cut_35287

theorem selected_cut_35288 : selected 9 ⟨925863, by decide⟩
    (prefixPartial 12 285209) = some ⟨12, 2, 0, 925863, 285209, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_285209_925863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285209 ⟨925863, by decide⟩ :=
  accepted_of_selected 12 285209 ⟨925863, by decide⟩ ⟨12, 2, 0, 925863, 285209, 2153, 65536⟩
    (by decide) selected_cut_35288

theorem selected_cut_35289 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 285210) = some ⟨12, 1, 0, 893903, 285210, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285210_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285210 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 285210 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 285210, 1, 65536⟩
    (by decide) selected_cut_35289

theorem selected_cut_35290 : selected 9 ⟨925939, by decide⟩
    (prefixPartial 12 285211) = some ⟨12, 2, 0, 925939, 285211, 3685, 65536⟩ := by
  decide +kernel

theorem context_12_285211_925939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285211 ⟨925939, by decide⟩ :=
  accepted_of_selected 12 285211 ⟨925939, by decide⟩ ⟨12, 2, 0, 925939, 285211, 3685, 65536⟩
    (by decide) selected_cut_35290

theorem unmarked_context_11_71302_925940 : frontier 10 ⟨925940, by decide⟩
    (prefixCache 11 71302) (prefixPartial 11 71302) = false := by
  decide +kernel

theorem node_context_11_71302_925940 : EJMOriginalGlobalDAGData.nodes 10 ⟨925940, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨925863, by decide⟩,⟨893903, by decide⟩,⟨925939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71302_925940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71302 ⟨925940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71302
    ⟨925940, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨925863, by decide⟩,⟨893903, by decide⟩,⟨925939, by decide⟩]) unmarked_context_11_71302_925940 node_context_11_71302_925940
  intro a
  fin_cases a
  · exact context_12_285208_1738
  · exact context_12_285209_925863
  · exact context_12_285210_893903
  · exact context_12_285211_925939

theorem selected_cut_35291 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 285212) = some ⟨12, 1, 0, 1738, 285212, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285212_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285212 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 285212 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 285212, 1, 65536⟩
    (by decide) selected_cut_35291

theorem selected_cut_35292 : selected 9 ⟨926006, by decide⟩
    (prefixPartial 12 285213) = some ⟨12, 2, 0, 926006, 285213, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_285213_926006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285213 ⟨926006, by decide⟩ :=
  accepted_of_selected 12 285213 ⟨926006, by decide⟩ ⟨12, 2, 0, 926006, 285213, 2213, 65536⟩
    (by decide) selected_cut_35292

theorem selected_cut_35293 : selected 9 ⟨926080, by decide⟩
    (prefixPartial 12 285214) = some ⟨12, 2, 0, 926080, 285214, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_285214_926080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285214 ⟨926080, by decide⟩ :=
  accepted_of_selected 12 285214 ⟨926080, by decide⟩ ⟨12, 2, 0, 926080, 285214, 3549, 65536⟩
    (by decide) selected_cut_35293

theorem selected_cut_35294 : selected 9 ⟨926155, by decide⟩
    (prefixPartial 12 285215) = some ⟨12, 2, 0, 926155, 285215, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_285215_926155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285215 ⟨926155, by decide⟩ :=
  accepted_of_selected 12 285215 ⟨926155, by decide⟩ ⟨12, 2, 0, 926155, 285215, 3409, 65536⟩
    (by decide) selected_cut_35294

theorem unmarked_context_11_71303_926156 : frontier 10 ⟨926156, by decide⟩
    (prefixCache 11 71303) (prefixPartial 11 71303) = false := by
  decide +kernel

theorem node_context_11_71303_926156 : EJMOriginalGlobalDAGData.nodes 10 ⟨926156, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨926006, by decide⟩,⟨926080, by decide⟩,⟨926155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71303_926156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71303 ⟨926156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71303
    ⟨926156, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨926006, by decide⟩,⟨926080, by decide⟩,⟨926155, by decide⟩]) unmarked_context_11_71303_926156 node_context_11_71303_926156
  intro a
  fin_cases a
  · exact context_12_285212_1738
  · exact context_12_285213_926006
  · exact context_12_285214_926080
  · exact context_12_285215_926155

theorem unmarked_context_10_17825_926157 : frontier 11 ⟨926157, by decide⟩
    (prefixCache 10 17825) (prefixPartial 10 17825) = false := by
  decide +kernel

theorem node_context_10_17825_926157 : EJMOriginalGlobalDAGData.nodes 11 ⟨926157, by decide⟩ =
    .split (coordinate 10) (![⟨925640, by decide⟩,⟨925805, by decide⟩,⟨925940, by decide⟩,⟨926156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17825_926157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17825 ⟨926157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17825
    ⟨926157, by decide⟩ (by decide) (![⟨925640, by decide⟩,⟨925805, by decide⟩,⟨925940, by decide⟩,⟨926156, by decide⟩]) unmarked_context_10_17825_926157 node_context_10_17825_926157
  intro a
  fin_cases a
  · exact context_11_71300_925640
  · exact context_11_71301_925805
  · exact context_11_71302_925940
  · exact context_11_71303_926156

theorem selected_cut_35295 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 285216) = some ⟨12, 1, 0, 1738, 285216, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285216_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285216 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 285216 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 285216, 1, 65536⟩
    (by decide) selected_cut_35295

theorem selected_cut_35296 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 285217) = some ⟨12, 1, 0, 1738, 285217, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285217_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285217 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 285217 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 285217, 1, 65536⟩
    (by decide) selected_cut_35296

theorem selected_cut_35297 : selected 9 ⟨926223, by decide⟩
    (prefixPartial 12 285218) = some ⟨12, 2, 0, 926223, 285218, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_285218_926223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285218 ⟨926223, by decide⟩ :=
  accepted_of_selected 12 285218 ⟨926223, by decide⟩ ⟨12, 2, 0, 926223, 285218, 2361, 65536⟩
    (by decide) selected_cut_35297

theorem selected_cut_35298 : selected 9 ⟨926295, by decide⟩
    (prefixPartial 12 285219) = some ⟨12, 2, 0, 926295, 285219, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_285219_926295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285219 ⟨926295, by decide⟩ :=
  accepted_of_selected 12 285219 ⟨926295, by decide⟩ ⟨12, 2, 0, 926295, 285219, 3277, 65536⟩
    (by decide) selected_cut_35298

theorem unmarked_context_11_71304_926296 : frontier 10 ⟨926296, by decide⟩
    (prefixCache 11 71304) (prefixPartial 11 71304) = false := by
  decide +kernel

theorem node_context_11_71304_926296 : EJMOriginalGlobalDAGData.nodes 10 ⟨926296, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨926223, by decide⟩,⟨926295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71304_926296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71304 ⟨926296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71304
    ⟨926296, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨926223, by decide⟩,⟨926295, by decide⟩]) unmarked_context_11_71304_926296 node_context_11_71304_926296
  intro a
  fin_cases a
  · exact context_12_285216_1738
  · exact context_12_285217_1738
  · exact context_12_285218_926223
  · exact context_12_285219_926295

theorem selected_cut_35299 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 285220) = some ⟨12, 1, 0, 1738, 285220, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285220_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285220 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 285220 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 285220, 1, 65536⟩
    (by decide) selected_cut_35299

theorem selected_cut_35300 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 285221) = some ⟨12, 1, 0, 1738, 285221, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285221_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285221 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 285221 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 285221, 1, 65536⟩
    (by decide) selected_cut_35300

theorem selected_cut_35301 : selected 9 ⟨926347, by decide⟩
    (prefixPartial 12 285222) = some ⟨12, 2, 0, 926347, 285222, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_285222_926347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285222 ⟨926347, by decide⟩ :=
  accepted_of_selected 12 285222 ⟨926347, by decide⟩ ⟨12, 2, 0, 926347, 285222, 1813, 65536⟩
    (by decide) selected_cut_35301

theorem selected_cut_35302 : selected 9 ⟨926394, by decide⟩
    (prefixPartial 12 285223) = some ⟨12, 2, 0, 926394, 285223, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_285223_926394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285223 ⟨926394, by decide⟩ :=
  accepted_of_selected 12 285223 ⟨926394, by decide⟩ ⟨12, 2, 0, 926394, 285223, 2437, 65536⟩
    (by decide) selected_cut_35302

theorem unmarked_context_11_71305_926395 : frontier 10 ⟨926395, by decide⟩
    (prefixCache 11 71305) (prefixPartial 11 71305) = false := by
  decide +kernel

theorem node_context_11_71305_926395 : EJMOriginalGlobalDAGData.nodes 10 ⟨926395, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨926347, by decide⟩,⟨926394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71305_926395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71305 ⟨926395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71305
    ⟨926395, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨926347, by decide⟩,⟨926394, by decide⟩]) unmarked_context_11_71305_926395 node_context_11_71305_926395
  intro a
  fin_cases a
  · exact context_12_285220_1738
  · exact context_12_285221_1738
  · exact context_12_285222_926347
  · exact context_12_285223_926394

theorem selected_cut_35303 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 71306) = some ⟨11, 1, 0, 900587, 71306, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71306_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71306 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 71306 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 71306, 1, 262144⟩
    (by decide) selected_cut_35303

theorem selected_cut_35304 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 285228) = some ⟨12, 1, 0, 1738, 285228, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285228_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285228 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 285228 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 285228, 1, 65536⟩
    (by decide) selected_cut_35304

theorem selected_cut_35305 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 285229) = some ⟨12, 1, 0, 1738, 285229, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285229_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285229 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 285229 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 285229, 1, 65536⟩
    (by decide) selected_cut_35305

theorem selected_cut_35306 : selected 9 ⟨926472, by decide⟩
    (prefixPartial 12 285230) = some ⟨12, 2, 0, 926472, 285230, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_285230_926472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285230 ⟨926472, by decide⟩ :=
  accepted_of_selected 12 285230 ⟨926472, by decide⟩ ⟨12, 2, 0, 926472, 285230, 2581, 65536⟩
    (by decide) selected_cut_35306

theorem selected_cut_35307 : selected 9 ⟨926546, by decide⟩
    (prefixPartial 12 285231) = some ⟨12, 2, 0, 926546, 285231, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_285231_926546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285231 ⟨926546, by decide⟩ :=
  accepted_of_selected 12 285231 ⟨926546, by decide⟩ ⟨12, 2, 0, 926546, 285231, 3165, 65536⟩
    (by decide) selected_cut_35307

theorem unmarked_context_11_71307_926547 : frontier 10 ⟨926547, by decide⟩
    (prefixCache 11 71307) (prefixPartial 11 71307) = false := by
  decide +kernel

theorem node_context_11_71307_926547 : EJMOriginalGlobalDAGData.nodes 10 ⟨926547, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨926472, by decide⟩,⟨926546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71307_926547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71307 ⟨926547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71307
    ⟨926547, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨926472, by decide⟩,⟨926546, by decide⟩]) unmarked_context_11_71307_926547 node_context_11_71307_926547
  intro a
  fin_cases a
  · exact context_12_285228_1738
  · exact context_12_285229_1738
  · exact context_12_285230_926472
  · exact context_12_285231_926546

theorem unmarked_context_10_17826_926548 : frontier 11 ⟨926548, by decide⟩
    (prefixCache 10 17826) (prefixPartial 10 17826) = false := by
  decide +kernel

theorem node_context_10_17826_926548 : EJMOriginalGlobalDAGData.nodes 11 ⟨926548, by decide⟩ =
    .split (coordinate 10) (![⟨926296, by decide⟩,⟨926395, by decide⟩,⟨900587, by decide⟩,⟨926547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17826_926548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17826 ⟨926548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17826
    ⟨926548, by decide⟩ (by decide) (![⟨926296, by decide⟩,⟨926395, by decide⟩,⟨900587, by decide⟩,⟨926547, by decide⟩]) unmarked_context_10_17826_926548 node_context_10_17826_926548
  intro a
  fin_cases a
  · exact context_11_71304_926296
  · exact context_11_71305_926395
  · exact context_11_71306_900587
  · exact context_11_71307_926547

theorem selected_cut_35308 : selected 10 ⟨926621, by decide⟩
    (prefixPartial 11 71308) = some ⟨11, 2, 0, 926621, 71308, 2393, 262144⟩ := by
  decide +kernel

theorem context_11_71308_926621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71308 ⟨926621, by decide⟩ :=
  accepted_of_selected 11 71308 ⟨926621, by decide⟩ ⟨11, 2, 0, 926621, 71308, 2393, 262144⟩
    (by decide) selected_cut_35308

theorem selected_cut_35309 : selected 10 ⟨926690, by decide⟩
    (prefixPartial 11 71309) = some ⟨11, 2, 0, 926690, 71309, 1925, 262144⟩ := by
  decide +kernel

theorem context_11_71309_926690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71309 ⟨926690, by decide⟩ :=
  accepted_of_selected 11 71309 ⟨926690, by decide⟩ ⟨11, 2, 0, 926690, 71309, 1925, 262144⟩
    (by decide) selected_cut_35309

theorem selected_cut_35310 : selected 10 ⟨926766, by decide⟩
    (prefixPartial 11 71310) = some ⟨11, 2, 0, 926766, 71310, 2569, 262144⟩ := by
  decide +kernel

theorem context_11_71310_926766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71310 ⟨926766, by decide⟩ :=
  accepted_of_selected 11 71310 ⟨926766, by decide⟩ ⟨11, 2, 0, 926766, 71310, 2569, 262144⟩
    (by decide) selected_cut_35310

theorem selected_cut_35311 : selected 10 ⟨926815, by decide⟩
    (prefixPartial 11 71311) = some ⟨11, 2, 0, 926815, 71311, 2049, 262144⟩ := by
  decide +kernel

theorem context_11_71311_926815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71311 ⟨926815, by decide⟩ :=
  accepted_of_selected 11 71311 ⟨926815, by decide⟩ ⟨11, 2, 0, 926815, 71311, 2049, 262144⟩
    (by decide) selected_cut_35311

theorem unmarked_context_10_17827_926816 : frontier 11 ⟨926816, by decide⟩
    (prefixCache 10 17827) (prefixPartial 10 17827) = false := by
  decide +kernel

theorem node_context_10_17827_926816 : EJMOriginalGlobalDAGData.nodes 11 ⟨926816, by decide⟩ =
    .split (coordinate 10) (![⟨926621, by decide⟩,⟨926690, by decide⟩,⟨926766, by decide⟩,⟨926815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17827_926816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17827 ⟨926816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17827
    ⟨926816, by decide⟩ (by decide) (![⟨926621, by decide⟩,⟨926690, by decide⟩,⟨926766, by decide⟩,⟨926815, by decide⟩]) unmarked_context_10_17827_926816 node_context_10_17827_926816
  intro a
  fin_cases a
  · exact context_11_71308_926621
  · exact context_11_71309_926690
  · exact context_11_71310_926766
  · exact context_11_71311_926815

theorem unmarked_context_9_4456_926817 : frontier 12 ⟨926817, by decide⟩
    (prefixCache 9 4456) (prefixPartial 9 4456) = false := by
  decide +kernel

theorem node_context_9_4456_926817 : EJMOriginalGlobalDAGData.nodes 12 ⟨926817, by decide⟩ =
    .split (coordinate 9) (![⟨925416, by decide⟩,⟨926157, by decide⟩,⟨926548, by decide⟩,⟨926816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4456_926817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4456 ⟨926817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4456
    ⟨926817, by decide⟩ (by decide) (![⟨925416, by decide⟩,⟨926157, by decide⟩,⟨926548, by decide⟩,⟨926816, by decide⟩]) unmarked_context_9_4456_926817 node_context_9_4456_926817
  intro a
  fin_cases a
  · exact context_10_17824_925416
  · exact context_10_17825_926157
  · exact context_10_17826_926548
  · exact context_10_17827_926816

theorem selected_cut_35312 : selected 9 ⟨926874, by decide⟩
    (prefixPartial 12 285248) = some ⟨12, 2, 0, 926874, 285248, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_285248_926874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285248 ⟨926874, by decide⟩ :=
  accepted_of_selected 12 285248 ⟨926874, by decide⟩ ⟨12, 2, 0, 926874, 285248, 2101, 65536⟩
    (by decide) selected_cut_35312

theorem selected_cut_35313 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 285249) = some ⟨12, 1, 0, 896706, 285249, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285249_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285249 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 285249 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 285249, 1, 65536⟩
    (by decide) selected_cut_35313

theorem selected_cut_35314 : selected 9 ⟨926922, by decide⟩
    (prefixPartial 12 285250) = some ⟨12, 2, 0, 926922, 285250, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_285250_926922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285250 ⟨926922, by decide⟩ :=
  accepted_of_selected 12 285250 ⟨926922, by decide⟩ ⟨12, 2, 0, 926922, 285250, 2341, 65536⟩
    (by decide) selected_cut_35314

theorem selected_cut_35315 : selected 9 ⟨926968, by decide⟩
    (prefixPartial 12 285251) = some ⟨12, 2, 0, 926968, 285251, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_285251_926968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285251 ⟨926968, by decide⟩ :=
  accepted_of_selected 12 285251 ⟨926968, by decide⟩ ⟨12, 2, 0, 926968, 285251, 2369, 65536⟩
    (by decide) selected_cut_35315

theorem unmarked_context_11_71312_926969 : frontier 10 ⟨926969, by decide⟩
    (prefixCache 11 71312) (prefixPartial 11 71312) = false := by
  decide +kernel

theorem node_context_11_71312_926969 : EJMOriginalGlobalDAGData.nodes 10 ⟨926969, by decide⟩ =
    .split (coordinate 11) (![⟨926874, by decide⟩,⟨896706, by decide⟩,⟨926922, by decide⟩,⟨926968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71312_926969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71312 ⟨926969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71312
    ⟨926969, by decide⟩ (by decide) (![⟨926874, by decide⟩,⟨896706, by decide⟩,⟨926922, by decide⟩,⟨926968, by decide⟩]) unmarked_context_11_71312_926969 node_context_11_71312_926969
  intro a
  fin_cases a
  · exact context_12_285248_926874
  · exact context_12_285249_896706
  · exact context_12_285250_926922
  · exact context_12_285251_926968

theorem selected_cut_35316 : selected 9 ⟨927019, by decide⟩
    (prefixPartial 12 285252) = some ⟨12, 2, 0, 927019, 285252, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_285252_927019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285252 ⟨927019, by decide⟩ :=
  accepted_of_selected 12 285252 ⟨927019, by decide⟩ ⟨12, 2, 0, 927019, 285252, 1793, 65536⟩
    (by decide) selected_cut_35316

theorem selected_cut_35317 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 285253) = some ⟨12, 1, 0, 896706, 285253, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285253_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285253 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 285253 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 285253, 1, 65536⟩
    (by decide) selected_cut_35317

theorem selected_cut_35318 : selected 9 ⟨927056, by decide⟩
    (prefixPartial 12 285254) = some ⟨12, 2, 0, 927056, 285254, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_285254_927056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285254 ⟨927056, by decide⟩ :=
  accepted_of_selected 12 285254 ⟨927056, by decide⟩ ⟨12, 2, 0, 927056, 285254, 1925, 65536⟩
    (by decide) selected_cut_35318

theorem selected_cut_35319 : selected 9 ⟨927093, by decide⟩
    (prefixPartial 12 285255) = some ⟨12, 2, 0, 927093, 285255, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_285255_927093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285255 ⟨927093, by decide⟩ :=
  accepted_of_selected 12 285255 ⟨927093, by decide⟩ ⟨12, 2, 0, 927093, 285255, 1925, 65536⟩
    (by decide) selected_cut_35319

theorem unmarked_context_11_71313_927094 : frontier 10 ⟨927094, by decide⟩
    (prefixCache 11 71313) (prefixPartial 11 71313) = false := by
  decide +kernel

theorem node_context_11_71313_927094 : EJMOriginalGlobalDAGData.nodes 10 ⟨927094, by decide⟩ =
    .split (coordinate 11) (![⟨927019, by decide⟩,⟨896706, by decide⟩,⟨927056, by decide⟩,⟨927093, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71313_927094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71313 ⟨927094, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71313
    ⟨927094, by decide⟩ (by decide) (![⟨927019, by decide⟩,⟨896706, by decide⟩,⟨927056, by decide⟩,⟨927093, by decide⟩]) unmarked_context_11_71313_927094 node_context_11_71313_927094
  intro a
  fin_cases a
  · exact context_12_285252_927019
  · exact context_12_285253_896706
  · exact context_12_285254_927056
  · exact context_12_285255_927093

theorem selected_cut_35320 : selected 9 ⟨927142, by decide⟩
    (prefixPartial 12 285256) = some ⟨12, 2, 0, 927142, 285256, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_285256_927142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285256 ⟨927142, by decide⟩ :=
  accepted_of_selected 12 285256 ⟨927142, by decide⟩ ⟨12, 2, 0, 927142, 285256, 1881, 65536⟩
    (by decide) selected_cut_35320

theorem selected_cut_35321 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 285257) = some ⟨12, 1, 0, 896706, 285257, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285257_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285257 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 285257 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 285257, 1, 65536⟩
    (by decide) selected_cut_35321

theorem selected_cut_35322 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 285258) = some ⟨12, 1, 0, 893903, 285258, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285258_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285258 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 285258 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 285258, 1, 65536⟩
    (by decide) selected_cut_35322

theorem selected_cut_35323 : selected 9 ⟨927194, by decide⟩
    (prefixPartial 12 285259) = some ⟨12, 2, 0, 927194, 285259, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_285259_927194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285259 ⟨927194, by decide⟩ :=
  accepted_of_selected 12 285259 ⟨927194, by decide⟩ ⟨12, 2, 0, 927194, 285259, 2285, 65536⟩
    (by decide) selected_cut_35323

theorem unmarked_context_11_71314_927195 : frontier 10 ⟨927195, by decide⟩
    (prefixCache 11 71314) (prefixPartial 11 71314) = false := by
  decide +kernel

theorem node_context_11_71314_927195 : EJMOriginalGlobalDAGData.nodes 10 ⟨927195, by decide⟩ =
    .split (coordinate 11) (![⟨927142, by decide⟩,⟨896706, by decide⟩,⟨893903, by decide⟩,⟨927194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71314_927195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71314 ⟨927195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71314
    ⟨927195, by decide⟩ (by decide) (![⟨927142, by decide⟩,⟨896706, by decide⟩,⟨893903, by decide⟩,⟨927194, by decide⟩]) unmarked_context_11_71314_927195 node_context_11_71314_927195
  intro a
  fin_cases a
  · exact context_12_285256_927142
  · exact context_12_285257_896706
  · exact context_12_285258_893903
  · exact context_12_285259_927194

theorem selected_cut_35324 : selected 9 ⟨927247, by decide⟩
    (prefixPartial 12 285260) = some ⟨12, 2, 0, 927247, 285260, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_285260_927247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285260 ⟨927247, by decide⟩ :=
  accepted_of_selected 12 285260 ⟨927247, by decide⟩ ⟨12, 2, 0, 927247, 285260, 2205, 65536⟩
    (by decide) selected_cut_35324

theorem selected_cut_35325 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 285261) = some ⟨12, 1, 0, 896706, 285261, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285261_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285261 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 285261 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 285261, 1, 65536⟩
    (by decide) selected_cut_35325

theorem selected_cut_35326 : selected 9 ⟨927297, by decide⟩
    (prefixPartial 12 285262) = some ⟨12, 2, 0, 927297, 285262, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_285262_927297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285262 ⟨927297, by decide⟩ :=
  accepted_of_selected 12 285262 ⟨927297, by decide⟩ ⟨12, 2, 0, 927297, 285262, 2557, 65536⟩
    (by decide) selected_cut_35326

theorem selected_cut_35327 : selected 9 ⟨927348, by decide⟩
    (prefixPartial 12 285263) = some ⟨12, 2, 0, 927348, 285263, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_285263_927348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285263 ⟨927348, by decide⟩ :=
  accepted_of_selected 12 285263 ⟨927348, by decide⟩ ⟨12, 2, 0, 927348, 285263, 2457, 65536⟩
    (by decide) selected_cut_35327

theorem unmarked_context_11_71315_927349 : frontier 10 ⟨927349, by decide⟩
    (prefixCache 11 71315) (prefixPartial 11 71315) = false := by
  decide +kernel

theorem node_context_11_71315_927349 : EJMOriginalGlobalDAGData.nodes 10 ⟨927349, by decide⟩ =
    .split (coordinate 11) (![⟨927247, by decide⟩,⟨896706, by decide⟩,⟨927297, by decide⟩,⟨927348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71315_927349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71315 ⟨927349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71315
    ⟨927349, by decide⟩ (by decide) (![⟨927247, by decide⟩,⟨896706, by decide⟩,⟨927297, by decide⟩,⟨927348, by decide⟩]) unmarked_context_11_71315_927349 node_context_11_71315_927349
  intro a
  fin_cases a
  · exact context_12_285260_927247
  · exact context_12_285261_896706
  · exact context_12_285262_927297
  · exact context_12_285263_927348

theorem unmarked_context_10_17828_927350 : frontier 11 ⟨927350, by decide⟩
    (prefixCache 10 17828) (prefixPartial 10 17828) = false := by
  decide +kernel

theorem node_context_10_17828_927350 : EJMOriginalGlobalDAGData.nodes 11 ⟨927350, by decide⟩ =
    .split (coordinate 10) (![⟨926969, by decide⟩,⟨927094, by decide⟩,⟨927195, by decide⟩,⟨927349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17828_927350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17828 ⟨927350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17828
    ⟨927350, by decide⟩ (by decide) (![⟨926969, by decide⟩,⟨927094, by decide⟩,⟨927195, by decide⟩,⟨927349, by decide⟩]) unmarked_context_10_17828_927350 node_context_10_17828_927350
  intro a
  fin_cases a
  · exact context_11_71312_926969
  · exact context_11_71313_927094
  · exact context_11_71314_927195
  · exact context_11_71315_927349

theorem selected_cut_35328 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17829) = some ⟨10, 1, 0, 893098, 17829, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17829_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17829 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17829 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17829, 1, 1048576⟩
    (by decide) selected_cut_35328

theorem selected_cut_35329 : selected 10 ⟨927407, by decide⟩
    (prefixPartial 11 71320) = some ⟨11, 2, 0, 927407, 71320, 2985, 262144⟩ := by
  decide +kernel

theorem context_11_71320_927407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71320 ⟨927407, by decide⟩ :=
  accepted_of_selected 11 71320 ⟨927407, by decide⟩ ⟨11, 2, 0, 927407, 71320, 2985, 262144⟩
    (by decide) selected_cut_35329

theorem selected_cut_35330 : selected 10 ⟨927453, by decide⟩
    (prefixPartial 11 71321) = some ⟨11, 2, 0, 927453, 71321, 2477, 262144⟩ := by
  decide +kernel

theorem context_11_71321_927453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71321 ⟨927453, by decide⟩ :=
  accepted_of_selected 11 71321 ⟨927453, by decide⟩ ⟨11, 2, 0, 927453, 71321, 2477, 262144⟩
    (by decide) selected_cut_35330

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
