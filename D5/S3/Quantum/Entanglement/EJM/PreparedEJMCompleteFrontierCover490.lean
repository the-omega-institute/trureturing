/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover489
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_93060_1314778 : frontier 10 ⟨1314778, by decide⟩
    (prefixCache 11 93060) (prefixPartial 11 93060) = false := by
  decide +kernel

theorem node_context_11_93060_1314778 : EJMOriginalGlobalDAGData.nodes 10 ⟨1314778, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1314660, by decide⟩,⟨1314715, by decide⟩,⟨1314777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93060_1314778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93060 ⟨1314778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93060
    ⟨1314778, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1314660, by decide⟩,⟨1314715, by decide⟩,⟨1314777, by decide⟩]) unmarked_context_11_93060_1314778 node_context_11_93060_1314778
  intro a
  fin_cases a
  · exact context_12_372240_1255011
  · exact context_12_372241_1314660
  · exact context_12_372242_1314715
  · exact context_12_372243_1314777

theorem selected_cut_47044 : selected 9 ⟨1314850, by decide⟩
    (prefixPartial 12 372244) = some ⟨12, 2, 0, 1314850, 372244, 3625, 65536⟩ := by
  decide +kernel

theorem context_12_372244_1314850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372244 ⟨1314850, by decide⟩ :=
  accepted_of_selected 12 372244 ⟨1314850, by decide⟩ ⟨12, 2, 0, 1314850, 372244, 3625, 65536⟩
    (by decide) selected_cut_47044

theorem selected_cut_47045 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 372245) = some ⟨12, 1, 0, 1172003, 372245, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372245_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372245 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 372245 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 372245, 1, 65536⟩
    (by decide) selected_cut_47045

theorem selected_cut_47046 : selected 9 ⟨1314906, by decide⟩
    (prefixPartial 12 372246) = some ⟨12, 2, 0, 1314906, 372246, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_372246_1314906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372246 ⟨1314906, by decide⟩ :=
  accepted_of_selected 12 372246 ⟨1314906, by decide⟩ ⟨12, 2, 0, 1314906, 372246, 3117, 65536⟩
    (by decide) selected_cut_47046

theorem selected_cut_47047 : selected 9 ⟨1314982, by decide⟩
    (prefixPartial 12 372247) = some ⟨12, 2, 0, 1314982, 372247, 4025, 65536⟩ := by
  decide +kernel

theorem context_12_372247_1314982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372247 ⟨1314982, by decide⟩ :=
  accepted_of_selected 12 372247 ⟨1314982, by decide⟩ ⟨12, 2, 0, 1314982, 372247, 4025, 65536⟩
    (by decide) selected_cut_47047

theorem unmarked_context_11_93061_1314983 : frontier 10 ⟨1314983, by decide⟩
    (prefixCache 11 93061) (prefixPartial 11 93061) = false := by
  decide +kernel

theorem node_context_11_93061_1314983 : EJMOriginalGlobalDAGData.nodes 10 ⟨1314983, by decide⟩ =
    .split (coordinate 11) (![⟨1314850, by decide⟩,⟨1172003, by decide⟩,⟨1314906, by decide⟩,⟨1314982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93061_1314983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93061 ⟨1314983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93061
    ⟨1314983, by decide⟩ (by decide) (![⟨1314850, by decide⟩,⟨1172003, by decide⟩,⟨1314906, by decide⟩,⟨1314982, by decide⟩]) unmarked_context_11_93061_1314983 node_context_11_93061_1314983
  intro a
  fin_cases a
  · exact context_12_372244_1314850
  · exact context_12_372245_1172003
  · exact context_12_372246_1314906
  · exact context_12_372247_1314982

theorem selected_cut_47048 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 372248) = some ⟨12, 1, 0, 994572, 372248, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372248_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372248 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 372248 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 372248, 1, 65536⟩
    (by decide) selected_cut_47048

theorem selected_cut_47049 : selected 9 ⟨1315034, by decide⟩
    (prefixPartial 12 372249) = some ⟨12, 2, 0, 1315034, 372249, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_372249_1315034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372249 ⟨1315034, by decide⟩ :=
  accepted_of_selected 12 372249 ⟨1315034, by decide⟩ ⟨12, 2, 0, 1315034, 372249, 2917, 65536⟩
    (by decide) selected_cut_47049

theorem selected_cut_47050 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 372250) = some ⟨12, 1, 0, 893903, 372250, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372250_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372250 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 372250 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 372250, 1, 65536⟩
    (by decide) selected_cut_47050

theorem selected_cut_47051 : selected 9 ⟨1315084, by decide⟩
    (prefixPartial 12 372251) = some ⟨12, 2, 0, 1315084, 372251, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_372251_1315084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372251 ⟨1315084, by decide⟩ :=
  accepted_of_selected 12 372251 ⟨1315084, by decide⟩ ⟨12, 2, 0, 1315084, 372251, 3209, 65536⟩
    (by decide) selected_cut_47051

theorem unmarked_context_11_93062_1315085 : frontier 10 ⟨1315085, by decide⟩
    (prefixCache 11 93062) (prefixPartial 11 93062) = false := by
  decide +kernel

theorem node_context_11_93062_1315085 : EJMOriginalGlobalDAGData.nodes 10 ⟨1315085, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1315034, by decide⟩,⟨893903, by decide⟩,⟨1315084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93062_1315085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93062 ⟨1315085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93062
    ⟨1315085, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1315034, by decide⟩,⟨893903, by decide⟩,⟨1315084, by decide⟩]) unmarked_context_11_93062_1315085 node_context_11_93062_1315085
  intro a
  fin_cases a
  · exact context_12_372248_994572
  · exact context_12_372249_1315034
  · exact context_12_372250_893903
  · exact context_12_372251_1315084

theorem selected_cut_47052 : selected 9 ⟨1315143, by decide⟩
    (prefixPartial 12 372252) = some ⟨12, 2, 0, 1315143, 372252, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_372252_1315143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372252 ⟨1315143, by decide⟩ :=
  accepted_of_selected 12 372252 ⟨1315143, by decide⟩ ⟨12, 2, 0, 1315143, 372252, 2981, 65536⟩
    (by decide) selected_cut_47052

theorem selected_cut_47053 : selected 9 ⟨1315194, by decide⟩
    (prefixPartial 12 372253) = some ⟨12, 2, 0, 1315194, 372253, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_372253_1315194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372253 ⟨1315194, by decide⟩ :=
  accepted_of_selected 12 372253 ⟨1315194, by decide⟩ ⟨12, 2, 0, 1315194, 372253, 3009, 65536⟩
    (by decide) selected_cut_47053

theorem selected_cut_47054 : selected 9 ⟨1315245, by decide⟩
    (prefixPartial 12 372254) = some ⟨12, 2, 0, 1315245, 372254, 2625, 65536⟩ := by
  decide +kernel

theorem context_12_372254_1315245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372254 ⟨1315245, by decide⟩ :=
  accepted_of_selected 12 372254 ⟨1315245, by decide⟩ ⟨12, 2, 0, 1315245, 372254, 2625, 65536⟩
    (by decide) selected_cut_47054

theorem selected_cut_47055 : selected 9 ⟨1315298, by decide⟩
    (prefixPartial 12 372255) = some ⟨12, 2, 0, 1315298, 372255, 3133, 65536⟩ := by
  decide +kernel

theorem context_12_372255_1315298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372255 ⟨1315298, by decide⟩ :=
  accepted_of_selected 12 372255 ⟨1315298, by decide⟩ ⟨12, 2, 0, 1315298, 372255, 3133, 65536⟩
    (by decide) selected_cut_47055

theorem unmarked_context_11_93063_1315299 : frontier 10 ⟨1315299, by decide⟩
    (prefixCache 11 93063) (prefixPartial 11 93063) = false := by
  decide +kernel

theorem node_context_11_93063_1315299 : EJMOriginalGlobalDAGData.nodes 10 ⟨1315299, by decide⟩ =
    .split (coordinate 11) (![⟨1315143, by decide⟩,⟨1315194, by decide⟩,⟨1315245, by decide⟩,⟨1315298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93063_1315299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93063 ⟨1315299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93063
    ⟨1315299, by decide⟩ (by decide) (![⟨1315143, by decide⟩,⟨1315194, by decide⟩,⟨1315245, by decide⟩,⟨1315298, by decide⟩]) unmarked_context_11_93063_1315299 node_context_11_93063_1315299
  intro a
  fin_cases a
  · exact context_12_372252_1315143
  · exact context_12_372253_1315194
  · exact context_12_372254_1315245
  · exact context_12_372255_1315298

theorem unmarked_context_10_23265_1315300 : frontier 11 ⟨1315300, by decide⟩
    (prefixCache 10 23265) (prefixPartial 10 23265) = false := by
  decide +kernel

theorem node_context_10_23265_1315300 : EJMOriginalGlobalDAGData.nodes 11 ⟨1315300, by decide⟩ =
    .split (coordinate 10) (![⟨1314778, by decide⟩,⟨1314983, by decide⟩,⟨1315085, by decide⟩,⟨1315299, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23265_1315300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23265 ⟨1315300, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23265
    ⟨1315300, by decide⟩ (by decide) (![⟨1314778, by decide⟩,⟨1314983, by decide⟩,⟨1315085, by decide⟩,⟨1315299, by decide⟩]) unmarked_context_10_23265_1315300 node_context_10_23265_1315300
  intro a
  fin_cases a
  · exact context_11_93060_1314778
  · exact context_11_93061_1314983
  · exact context_11_93062_1315085
  · exact context_11_93063_1315299

theorem selected_cut_47056 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 372256) = some ⟨12, 1, 0, 435790, 372256, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372256_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372256 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 372256 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 372256, 1, 65536⟩
    (by decide) selected_cut_47056

theorem selected_cut_47057 : selected 9 ⟨1315344, by decide⟩
    (prefixPartial 12 372257) = some ⟨12, 2, 0, 1315344, 372257, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_372257_1315344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372257 ⟨1315344, by decide⟩ :=
  accepted_of_selected 12 372257 ⟨1315344, by decide⟩ ⟨12, 2, 0, 1315344, 372257, 2877, 65536⟩
    (by decide) selected_cut_47057

theorem selected_cut_47058 : selected 9 ⟨1315385, by decide⟩
    (prefixPartial 12 372258) = some ⟨12, 2, 0, 1315385, 372258, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_372258_1315385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372258 ⟨1315385, by decide⟩ :=
  accepted_of_selected 12 372258 ⟨1315385, by decide⟩ ⟨12, 2, 0, 1315385, 372258, 2413, 65536⟩
    (by decide) selected_cut_47058

theorem selected_cut_47059 : selected 9 ⟨1315436, by decide⟩
    (prefixPartial 12 372259) = some ⟨12, 2, 0, 1315436, 372259, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_372259_1315436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372259 ⟨1315436, by decide⟩ :=
  accepted_of_selected 12 372259 ⟨1315436, by decide⟩ ⟨12, 2, 0, 1315436, 372259, 2973, 65536⟩
    (by decide) selected_cut_47059

theorem unmarked_context_11_93064_1315437 : frontier 10 ⟨1315437, by decide⟩
    (prefixCache 11 93064) (prefixPartial 11 93064) = false := by
  decide +kernel

theorem node_context_11_93064_1315437 : EJMOriginalGlobalDAGData.nodes 10 ⟨1315437, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1315344, by decide⟩,⟨1315385, by decide⟩,⟨1315436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93064_1315437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93064 ⟨1315437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93064
    ⟨1315437, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1315344, by decide⟩,⟨1315385, by decide⟩,⟨1315436, by decide⟩]) unmarked_context_11_93064_1315437 node_context_11_93064_1315437
  intro a
  fin_cases a
  · exact context_12_372256_435790
  · exact context_12_372257_1315344
  · exact context_12_372258_1315385
  · exact context_12_372259_1315436

theorem selected_cut_47060 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 372260) = some ⟨12, 1, 0, 450498, 372260, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372260_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372260 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 372260 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 372260, 1, 65536⟩
    (by decide) selected_cut_47060

theorem selected_cut_47061 : selected 9 ⟨1315483, by decide⟩
    (prefixPartial 12 372261) = some ⟨12, 2, 0, 1315483, 372261, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_372261_1315483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372261 ⟨1315483, by decide⟩ :=
  accepted_of_selected 12 372261 ⟨1315483, by decide⟩ ⟨12, 2, 0, 1315483, 372261, 3217, 65536⟩
    (by decide) selected_cut_47061

theorem selected_cut_47062 : selected 9 ⟨1315524, by decide⟩
    (prefixPartial 12 372262) = some ⟨12, 2, 0, 1315524, 372262, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_372262_1315524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372262 ⟨1315524, by decide⟩ :=
  accepted_of_selected 12 372262 ⟨1315524, by decide⟩ ⟨12, 2, 0, 1315524, 372262, 2637, 65536⟩
    (by decide) selected_cut_47062

theorem selected_cut_47063 : selected 9 ⟨1315603, by decide⟩
    (prefixPartial 12 372263) = some ⟨12, 2, 0, 1315603, 372263, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_372263_1315603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372263 ⟨1315603, by decide⟩ :=
  accepted_of_selected 12 372263 ⟨1315603, by decide⟩ ⟨12, 2, 0, 1315603, 372263, 3441, 65536⟩
    (by decide) selected_cut_47063

theorem unmarked_context_11_93065_1315604 : frontier 10 ⟨1315604, by decide⟩
    (prefixCache 11 93065) (prefixPartial 11 93065) = false := by
  decide +kernel

theorem node_context_11_93065_1315604 : EJMOriginalGlobalDAGData.nodes 10 ⟨1315604, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1315483, by decide⟩,⟨1315524, by decide⟩,⟨1315603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93065_1315604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93065 ⟨1315604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93065
    ⟨1315604, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1315483, by decide⟩,⟨1315524, by decide⟩,⟨1315603, by decide⟩]) unmarked_context_11_93065_1315604 node_context_11_93065_1315604
  intro a
  fin_cases a
  · exact context_12_372260_450498
  · exact context_12_372261_1315483
  · exact context_12_372262_1315524
  · exact context_12_372263_1315603

theorem selected_cut_47064 : selected 10 ⟨1315648, by decide⟩
    (prefixPartial 11 93066) = some ⟨11, 2, 0, 1315648, 93066, 2445, 262144⟩ := by
  decide +kernel

theorem context_11_93066_1315648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93066 ⟨1315648, by decide⟩ :=
  accepted_of_selected 11 93066 ⟨1315648, by decide⟩ ⟨11, 2, 0, 1315648, 93066, 2445, 262144⟩
    (by decide) selected_cut_47064

theorem selected_cut_47065 : selected 9 ⟨1315701, by decide⟩
    (prefixPartial 12 372268) = some ⟨12, 2, 0, 1315701, 372268, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_372268_1315701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372268 ⟨1315701, by decide⟩ :=
  accepted_of_selected 12 372268 ⟨1315701, by decide⟩ ⟨12, 2, 0, 1315701, 372268, 2509, 65536⟩
    (by decide) selected_cut_47065

theorem selected_cut_47066 : selected 9 ⟨1315742, by decide⟩
    (prefixPartial 12 372269) = some ⟨12, 2, 0, 1315742, 372269, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_372269_1315742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372269 ⟨1315742, by decide⟩ :=
  accepted_of_selected 12 372269 ⟨1315742, by decide⟩ ⟨12, 2, 0, 1315742, 372269, 2669, 65536⟩
    (by decide) selected_cut_47066

theorem selected_cut_47067 : selected 9 ⟨1315775, by decide⟩
    (prefixPartial 12 372270) = some ⟨12, 2, 0, 1315775, 372270, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_372270_1315775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372270 ⟨1315775, by decide⟩ :=
  accepted_of_selected 12 372270 ⟨1315775, by decide⟩ ⟨12, 2, 0, 1315775, 372270, 2193, 65536⟩
    (by decide) selected_cut_47067

theorem selected_cut_47068 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 372271) = some ⟨12, 1, 0, 758968, 372271, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372271_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372271 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 372271 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 372271, 1, 65536⟩
    (by decide) selected_cut_47068

theorem unmarked_context_11_93067_1315776 : frontier 10 ⟨1315776, by decide⟩
    (prefixCache 11 93067) (prefixPartial 11 93067) = false := by
  decide +kernel

theorem node_context_11_93067_1315776 : EJMOriginalGlobalDAGData.nodes 10 ⟨1315776, by decide⟩ =
    .split (coordinate 11) (![⟨1315701, by decide⟩,⟨1315742, by decide⟩,⟨1315775, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93067_1315776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93067 ⟨1315776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93067
    ⟨1315776, by decide⟩ (by decide) (![⟨1315701, by decide⟩,⟨1315742, by decide⟩,⟨1315775, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_93067_1315776 node_context_11_93067_1315776
  intro a
  fin_cases a
  · exact context_12_372268_1315701
  · exact context_12_372269_1315742
  · exact context_12_372270_1315775
  · exact context_12_372271_758968

theorem unmarked_context_10_23266_1315777 : frontier 11 ⟨1315777, by decide⟩
    (prefixCache 10 23266) (prefixPartial 10 23266) = false := by
  decide +kernel

theorem node_context_10_23266_1315777 : EJMOriginalGlobalDAGData.nodes 11 ⟨1315777, by decide⟩ =
    .split (coordinate 10) (![⟨1315437, by decide⟩,⟨1315604, by decide⟩,⟨1315648, by decide⟩,⟨1315776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23266_1315777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23266 ⟨1315777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23266
    ⟨1315777, by decide⟩ (by decide) (![⟨1315437, by decide⟩,⟨1315604, by decide⟩,⟨1315648, by decide⟩,⟨1315776, by decide⟩]) unmarked_context_10_23266_1315777 node_context_10_23266_1315777
  intro a
  fin_cases a
  · exact context_11_93064_1315437
  · exact context_11_93065_1315604
  · exact context_11_93066_1315648
  · exact context_11_93067_1315776

theorem selected_cut_47069 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 372272) = some ⟨12, 1, 0, 1255011, 372272, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372272_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372272 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 372272 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 372272, 1, 65536⟩
    (by decide) selected_cut_47069

theorem selected_cut_47070 : selected 9 ⟨1315810, by decide⟩
    (prefixPartial 12 372273) = some ⟨12, 2, 0, 1315810, 372273, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_372273_1315810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372273 ⟨1315810, by decide⟩ :=
  accepted_of_selected 12 372273 ⟨1315810, by decide⟩ ⟨12, 2, 0, 1315810, 372273, 2209, 65536⟩
    (by decide) selected_cut_47070

theorem selected_cut_47071 : selected 9 ⟨1315845, by decide⟩
    (prefixPartial 12 372274) = some ⟨12, 2, 0, 1315845, 372274, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_372274_1315845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372274 ⟨1315845, by decide⟩ :=
  accepted_of_selected 12 372274 ⟨1315845, by decide⟩ ⟨12, 2, 0, 1315845, 372274, 2045, 65536⟩
    (by decide) selected_cut_47071

theorem selected_cut_47072 : selected 9 ⟨1315883, by decide⟩
    (prefixPartial 12 372275) = some ⟨12, 2, 0, 1315883, 372275, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_372275_1315883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372275 ⟨1315883, by decide⟩ :=
  accepted_of_selected 12 372275 ⟨1315883, by decide⟩ ⟨12, 2, 0, 1315883, 372275, 2581, 65536⟩
    (by decide) selected_cut_47072

theorem unmarked_context_11_93068_1315884 : frontier 10 ⟨1315884, by decide⟩
    (prefixCache 11 93068) (prefixPartial 11 93068) = false := by
  decide +kernel

theorem node_context_11_93068_1315884 : EJMOriginalGlobalDAGData.nodes 10 ⟨1315884, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1315810, by decide⟩,⟨1315845, by decide⟩,⟨1315883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93068_1315884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93068 ⟨1315884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93068
    ⟨1315884, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1315810, by decide⟩,⟨1315845, by decide⟩,⟨1315883, by decide⟩]) unmarked_context_11_93068_1315884 node_context_11_93068_1315884
  intro a
  fin_cases a
  · exact context_12_372272_1255011
  · exact context_12_372273_1315810
  · exact context_12_372274_1315845
  · exact context_12_372275_1315883

theorem selected_cut_47073 : selected 9 ⟨1315940, by decide⟩
    (prefixPartial 12 372276) = some ⟨12, 2, 0, 1315940, 372276, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_372276_1315940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372276 ⟨1315940, by decide⟩ :=
  accepted_of_selected 12 372276 ⟨1315940, by decide⟩ ⟨12, 2, 0, 1315940, 372276, 2641, 65536⟩
    (by decide) selected_cut_47073

theorem selected_cut_47074 : selected 9 ⟨1315980, by decide⟩
    (prefixPartial 12 372277) = some ⟨12, 2, 0, 1315980, 372277, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_372277_1315980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372277 ⟨1315980, by decide⟩ :=
  accepted_of_selected 12 372277 ⟨1315980, by decide⟩ ⟨12, 2, 0, 1315980, 372277, 2293, 65536⟩
    (by decide) selected_cut_47074

theorem selected_cut_47075 : selected 9 ⟨1316019, by decide⟩
    (prefixPartial 12 372278) = some ⟨12, 2, 0, 1316019, 372278, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_372278_1316019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372278 ⟨1316019, by decide⟩ :=
  accepted_of_selected 12 372278 ⟨1316019, by decide⟩ ⟨12, 2, 0, 1316019, 372278, 2029, 65536⟩
    (by decide) selected_cut_47075

theorem selected_cut_47076 : selected 9 ⟨1316064, by decide⟩
    (prefixPartial 12 372279) = some ⟨12, 2, 0, 1316064, 372279, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_372279_1316064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372279 ⟨1316064, by decide⟩ :=
  accepted_of_selected 12 372279 ⟨1316064, by decide⟩ ⟨12, 2, 0, 1316064, 372279, 2725, 65536⟩
    (by decide) selected_cut_47076

theorem unmarked_context_11_93069_1316065 : frontier 10 ⟨1316065, by decide⟩
    (prefixCache 11 93069) (prefixPartial 11 93069) = false := by
  decide +kernel

theorem node_context_11_93069_1316065 : EJMOriginalGlobalDAGData.nodes 10 ⟨1316065, by decide⟩ =
    .split (coordinate 11) (![⟨1315940, by decide⟩,⟨1315980, by decide⟩,⟨1316019, by decide⟩,⟨1316064, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93069_1316065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93069 ⟨1316065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93069
    ⟨1316065, by decide⟩ (by decide) (![⟨1315940, by decide⟩,⟨1315980, by decide⟩,⟨1316019, by decide⟩,⟨1316064, by decide⟩]) unmarked_context_11_93069_1316065 node_context_11_93069_1316065
  intro a
  fin_cases a
  · exact context_12_372276_1315940
  · exact context_12_372277_1315980
  · exact context_12_372278_1316019
  · exact context_12_372279_1316064

theorem selected_cut_47077 : selected 10 ⟨1316153, by decide⟩
    (prefixPartial 11 93070) = some ⟨11, 2, 0, 1316153, 93070, 4025, 262144⟩ := by
  decide +kernel

theorem context_11_93070_1316153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93070 ⟨1316153, by decide⟩ :=
  accepted_of_selected 11 93070 ⟨1316153, by decide⟩ ⟨11, 2, 0, 1316153, 93070, 4025, 262144⟩
    (by decide) selected_cut_47077

theorem selected_cut_47078 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 93071) = some ⟨11, 1, 0, 977886, 93071, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93071_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93071 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 93071 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 93071, 1, 262144⟩
    (by decide) selected_cut_47078

theorem unmarked_context_10_23267_1316154 : frontier 11 ⟨1316154, by decide⟩
    (prefixCache 10 23267) (prefixPartial 10 23267) = false := by
  decide +kernel

theorem node_context_10_23267_1316154 : EJMOriginalGlobalDAGData.nodes 11 ⟨1316154, by decide⟩ =
    .split (coordinate 10) (![⟨1315884, by decide⟩,⟨1316065, by decide⟩,⟨1316153, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23267_1316154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23267 ⟨1316154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23267
    ⟨1316154, by decide⟩ (by decide) (![⟨1315884, by decide⟩,⟨1316065, by decide⟩,⟨1316153, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23267_1316154 node_context_10_23267_1316154
  intro a
  fin_cases a
  · exact context_11_93068_1315884
  · exact context_11_93069_1316065
  · exact context_11_93070_1316153
  · exact context_11_93071_977886

theorem unmarked_context_9_5816_1316155 : frontier 12 ⟨1316155, by decide⟩
    (prefixCache 9 5816) (prefixPartial 9 5816) = false := by
  decide +kernel

theorem node_context_9_5816_1316155 : EJMOriginalGlobalDAGData.nodes 12 ⟨1316155, by decide⟩ =
    .split (coordinate 9) (![⟨1314611, by decide⟩,⟨1315300, by decide⟩,⟨1315777, by decide⟩,⟨1316154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5816_1316155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5816 ⟨1316155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5816
    ⟨1316155, by decide⟩ (by decide) (![⟨1314611, by decide⟩,⟨1315300, by decide⟩,⟨1315777, by decide⟩,⟨1316154, by decide⟩]) unmarked_context_9_5816_1316155 node_context_9_5816_1316155
  intro a
  fin_cases a
  · exact context_10_23264_1314611
  · exact context_10_23265_1315300
  · exact context_10_23266_1315777
  · exact context_10_23267_1316154

theorem selected_cut_47079 : selected 9 ⟨1173556, by decide⟩
    (prefixPartial 12 372288) = some ⟨12, 1, 0, 1173556, 372288, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372288_1173556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372288 ⟨1173556, by decide⟩ :=
  accepted_of_selected 12 372288 ⟨1173556, by decide⟩ ⟨12, 1, 0, 1173556, 372288, 1, 65536⟩
    (by decide) selected_cut_47079

theorem selected_cut_47080 : selected 9 ⟨1316184, by decide⟩
    (prefixPartial 12 372289) = some ⟨12, 2, 0, 1316184, 372289, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_372289_1316184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372289 ⟨1316184, by decide⟩ :=
  accepted_of_selected 12 372289 ⟨1316184, by decide⟩ ⟨12, 2, 0, 1316184, 372289, 1941, 65536⟩
    (by decide) selected_cut_47080

theorem selected_cut_47081 : selected 9 ⟨1316215, by decide⟩
    (prefixPartial 12 372290) = some ⟨12, 2, 0, 1316215, 372290, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_372290_1316215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372290 ⟨1316215, by decide⟩ :=
  accepted_of_selected 12 372290 ⟨1316215, by decide⟩ ⟨12, 2, 0, 1316215, 372290, 1849, 65536⟩
    (by decide) selected_cut_47081

theorem selected_cut_47082 : selected 9 ⟨1316251, by decide⟩
    (prefixPartial 12 372291) = some ⟨12, 2, 0, 1316251, 372291, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_372291_1316251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372291 ⟨1316251, by decide⟩ :=
  accepted_of_selected 12 372291 ⟨1316251, by decide⟩ ⟨12, 2, 0, 1316251, 372291, 2181, 65536⟩
    (by decide) selected_cut_47082

theorem unmarked_context_11_93072_1316252 : frontier 10 ⟨1316252, by decide⟩
    (prefixCache 11 93072) (prefixPartial 11 93072) = false := by
  decide +kernel

theorem node_context_11_93072_1316252 : EJMOriginalGlobalDAGData.nodes 10 ⟨1316252, by decide⟩ =
    .split (coordinate 11) (![⟨1173556, by decide⟩,⟨1316184, by decide⟩,⟨1316215, by decide⟩,⟨1316251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93072_1316252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93072 ⟨1316252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93072
    ⟨1316252, by decide⟩ (by decide) (![⟨1173556, by decide⟩,⟨1316184, by decide⟩,⟨1316215, by decide⟩,⟨1316251, by decide⟩]) unmarked_context_11_93072_1316252 node_context_11_93072_1316252
  intro a
  fin_cases a
  · exact context_12_372288_1173556
  · exact context_12_372289_1316184
  · exact context_12_372290_1316215
  · exact context_12_372291_1316251

theorem selected_cut_47083 : selected 9 ⟨1316290, by decide⟩
    (prefixPartial 12 372292) = some ⟨12, 2, 0, 1316290, 372292, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_372292_1316290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372292 ⟨1316290, by decide⟩ :=
  accepted_of_selected 12 372292 ⟨1316290, by decide⟩ ⟨12, 2, 0, 1316290, 372292, 2193, 65536⟩
    (by decide) selected_cut_47083

theorem selected_cut_47084 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 372293) = some ⟨12, 1, 0, 1257136, 372293, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372293_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372293 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 372293 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 372293, 1, 65536⟩
    (by decide) selected_cut_47084

theorem selected_cut_47085 : selected 9 ⟨1316328, by decide⟩
    (prefixPartial 12 372294) = some ⟨12, 2, 0, 1316328, 372294, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_372294_1316328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372294 ⟨1316328, by decide⟩ :=
  accepted_of_selected 12 372294 ⟨1316328, by decide⟩ ⟨12, 2, 0, 1316328, 372294, 1861, 65536⟩
    (by decide) selected_cut_47085

theorem selected_cut_47086 : selected 9 ⟨1316366, by decide⟩
    (prefixPartial 12 372295) = some ⟨12, 2, 0, 1316366, 372295, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_372295_1316366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372295 ⟨1316366, by decide⟩ :=
  accepted_of_selected 12 372295 ⟨1316366, by decide⟩ ⟨12, 2, 0, 1316366, 372295, 1985, 65536⟩
    (by decide) selected_cut_47086

theorem unmarked_context_11_93073_1316367 : frontier 10 ⟨1316367, by decide⟩
    (prefixCache 11 93073) (prefixPartial 11 93073) = false := by
  decide +kernel

theorem node_context_11_93073_1316367 : EJMOriginalGlobalDAGData.nodes 10 ⟨1316367, by decide⟩ =
    .split (coordinate 11) (![⟨1316290, by decide⟩,⟨1257136, by decide⟩,⟨1316328, by decide⟩,⟨1316366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93073_1316367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93073 ⟨1316367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93073
    ⟨1316367, by decide⟩ (by decide) (![⟨1316290, by decide⟩,⟨1257136, by decide⟩,⟨1316328, by decide⟩,⟨1316366, by decide⟩]) unmarked_context_11_93073_1316367 node_context_11_93073_1316367
  intro a
  fin_cases a
  · exact context_12_372292_1316290
  · exact context_12_372293_1257136
  · exact context_12_372294_1316328
  · exact context_12_372295_1316366

theorem selected_cut_47087 : selected 10 ⟨1316427, by decide⟩
    (prefixPartial 11 93074) = some ⟨11, 2, 0, 1316427, 93074, 3317, 262144⟩ := by
  decide +kernel

theorem context_11_93074_1316427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93074 ⟨1316427, by decide⟩ :=
  accepted_of_selected 11 93074 ⟨1316427, by decide⟩ ⟨11, 2, 0, 1316427, 93074, 3317, 262144⟩
    (by decide) selected_cut_47087

theorem selected_cut_47088 : selected 9 ⟨1316459, by decide⟩
    (prefixPartial 12 372300) = some ⟨12, 2, 0, 1316459, 372300, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_372300_1316459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372300 ⟨1316459, by decide⟩ :=
  accepted_of_selected 12 372300 ⟨1316459, by decide⟩ ⟨12, 2, 0, 1316459, 372300, 1793, 65536⟩
    (by decide) selected_cut_47088

theorem selected_cut_47089 : selected 9 ⟨1316484, by decide⟩
    (prefixPartial 12 372301) = some ⟨12, 2, 0, 1316484, 372301, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_372301_1316484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372301 ⟨1316484, by decide⟩ :=
  accepted_of_selected 12 372301 ⟨1316484, by decide⟩ ⟨12, 2, 0, 1316484, 372301, 1549, 65536⟩
    (by decide) selected_cut_47089

theorem selected_cut_47090 : selected 9 ⟨1316509, by decide⟩
    (prefixPartial 12 372302) = some ⟨12, 2, 0, 1316509, 372302, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_372302_1316509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372302 ⟨1316509, by decide⟩ :=
  accepted_of_selected 12 372302 ⟨1316509, by decide⟩ ⟨12, 2, 0, 1316509, 372302, 1453, 65536⟩
    (by decide) selected_cut_47090

theorem selected_cut_47091 : selected 9 ⟨1316538, by decide⟩
    (prefixPartial 12 372303) = some ⟨12, 2, 0, 1316538, 372303, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_372303_1316538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372303 ⟨1316538, by decide⟩ :=
  accepted_of_selected 12 372303 ⟨1316538, by decide⟩ ⟨12, 2, 0, 1316538, 372303, 1537, 65536⟩
    (by decide) selected_cut_47091

theorem unmarked_context_11_93075_1316539 : frontier 10 ⟨1316539, by decide⟩
    (prefixCache 11 93075) (prefixPartial 11 93075) = false := by
  decide +kernel

theorem node_context_11_93075_1316539 : EJMOriginalGlobalDAGData.nodes 10 ⟨1316539, by decide⟩ =
    .split (coordinate 11) (![⟨1316459, by decide⟩,⟨1316484, by decide⟩,⟨1316509, by decide⟩,⟨1316538, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93075_1316539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93075 ⟨1316539, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93075
    ⟨1316539, by decide⟩ (by decide) (![⟨1316459, by decide⟩,⟨1316484, by decide⟩,⟨1316509, by decide⟩,⟨1316538, by decide⟩]) unmarked_context_11_93075_1316539 node_context_11_93075_1316539
  intro a
  fin_cases a
  · exact context_12_372300_1316459
  · exact context_12_372301_1316484
  · exact context_12_372302_1316509
  · exact context_12_372303_1316538

theorem unmarked_context_10_23268_1316540 : frontier 11 ⟨1316540, by decide⟩
    (prefixCache 10 23268) (prefixPartial 10 23268) = false := by
  decide +kernel

theorem node_context_10_23268_1316540 : EJMOriginalGlobalDAGData.nodes 11 ⟨1316540, by decide⟩ =
    .split (coordinate 10) (![⟨1316252, by decide⟩,⟨1316367, by decide⟩,⟨1316427, by decide⟩,⟨1316539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23268_1316540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23268 ⟨1316540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23268
    ⟨1316540, by decide⟩ (by decide) (![⟨1316252, by decide⟩,⟨1316367, by decide⟩,⟨1316427, by decide⟩,⟨1316539, by decide⟩]) unmarked_context_10_23268_1316540 node_context_10_23268_1316540
  intro a
  fin_cases a
  · exact context_11_93072_1316252
  · exact context_11_93073_1316367
  · exact context_11_93074_1316427
  · exact context_11_93075_1316539

theorem selected_cut_47092 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23269) = some ⟨10, 1, 0, 893098, 23269, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23269_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23269 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23269 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23269, 1, 1048576⟩
    (by decide) selected_cut_47092

theorem selected_cut_47093 : selected 9 ⟨1316565, by decide⟩
    (prefixPartial 12 372320) = some ⟨12, 2, 0, 1316565, 372320, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_372320_1316565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372320 ⟨1316565, by decide⟩ :=
  accepted_of_selected 12 372320 ⟨1316565, by decide⟩ ⟨12, 2, 0, 1316565, 372320, 1605, 65536⟩
    (by decide) selected_cut_47093

theorem selected_cut_47094 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 372321) = some ⟨12, 1, 0, 1256866, 372321, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372321_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372321 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 372321 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 372321, 1, 65536⟩
    (by decide) selected_cut_47094

theorem selected_cut_47095 : selected 9 ⟨1316584, by decide⟩
    (prefixPartial 12 372322) = some ⟨12, 2, 0, 1316584, 372322, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_372322_1316584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372322 ⟨1316584, by decide⟩ :=
  accepted_of_selected 12 372322 ⟨1316584, by decide⟩ ⟨12, 2, 0, 1316584, 372322, 1289, 65536⟩
    (by decide) selected_cut_47095

theorem selected_cut_47096 : selected 9 ⟨1316612, by decide⟩
    (prefixPartial 12 372323) = some ⟨12, 2, 0, 1316612, 372323, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_372323_1316612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372323 ⟨1316612, by decide⟩ :=
  accepted_of_selected 12 372323 ⟨1316612, by decide⟩ ⟨12, 2, 0, 1316612, 372323, 1549, 65536⟩
    (by decide) selected_cut_47096

theorem unmarked_context_11_93080_1316613 : frontier 10 ⟨1316613, by decide⟩
    (prefixCache 11 93080) (prefixPartial 11 93080) = false := by
  decide +kernel

theorem node_context_11_93080_1316613 : EJMOriginalGlobalDAGData.nodes 10 ⟨1316613, by decide⟩ =
    .split (coordinate 11) (![⟨1316565, by decide⟩,⟨1256866, by decide⟩,⟨1316584, by decide⟩,⟨1316612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93080_1316613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93080 ⟨1316613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93080
    ⟨1316613, by decide⟩ (by decide) (![⟨1316565, by decide⟩,⟨1256866, by decide⟩,⟨1316584, by decide⟩,⟨1316612, by decide⟩]) unmarked_context_11_93080_1316613 node_context_11_93080_1316613
  intro a
  fin_cases a
  · exact context_12_372320_1316565
  · exact context_12_372321_1256866
  · exact context_12_372322_1316584
  · exact context_12_372323_1316612

theorem selected_cut_47097 : selected 9 ⟨1316641, by decide⟩
    (prefixPartial 12 372324) = some ⟨12, 2, 0, 1316641, 372324, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_372324_1316641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372324 ⟨1316641, by decide⟩ :=
  accepted_of_selected 12 372324 ⟨1316641, by decide⟩ ⟨12, 2, 0, 1316641, 372324, 1533, 65536⟩
    (by decide) selected_cut_47097

theorem selected_cut_47098 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 372325) = some ⟨12, 1, 0, 1256866, 372325, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372325_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372325 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 372325 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 372325, 1, 65536⟩
    (by decide) selected_cut_47098

theorem selected_cut_47099 : selected 9 ⟨1316661, by decide⟩
    (prefixPartial 12 372326) = some ⟨12, 2, 0, 1316661, 372326, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_372326_1316661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372326 ⟨1316661, by decide⟩ :=
  accepted_of_selected 12 372326 ⟨1316661, by decide⟩ ⟨12, 2, 0, 1316661, 372326, 1245, 65536⟩
    (by decide) selected_cut_47099

theorem selected_cut_47100 : selected 9 ⟨1316689, by decide⟩
    (prefixPartial 12 372327) = some ⟨12, 2, 0, 1316689, 372327, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_372327_1316689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372327 ⟨1316689, by decide⟩ :=
  accepted_of_selected 12 372327 ⟨1316689, by decide⟩ ⟨12, 2, 0, 1316689, 372327, 1485, 65536⟩
    (by decide) selected_cut_47100

theorem unmarked_context_11_93081_1316690 : frontier 10 ⟨1316690, by decide⟩
    (prefixCache 11 93081) (prefixPartial 11 93081) = false := by
  decide +kernel

theorem node_context_11_93081_1316690 : EJMOriginalGlobalDAGData.nodes 10 ⟨1316690, by decide⟩ =
    .split (coordinate 11) (![⟨1316641, by decide⟩,⟨1256866, by decide⟩,⟨1316661, by decide⟩,⟨1316689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93081_1316690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93081 ⟨1316690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93081
    ⟨1316690, by decide⟩ (by decide) (![⟨1316641, by decide⟩,⟨1256866, by decide⟩,⟨1316661, by decide⟩,⟨1316689, by decide⟩]) unmarked_context_11_93081_1316690 node_context_11_93081_1316690
  intro a
  fin_cases a
  · exact context_12_372324_1316641
  · exact context_12_372325_1256866
  · exact context_12_372326_1316661
  · exact context_12_372327_1316689

theorem selected_cut_47101 : selected 10 ⟨1316710, by decide⟩
    (prefixPartial 11 93082) = some ⟨11, 2, 0, 1316710, 93082, 1153, 262144⟩ := by
  decide +kernel

theorem context_11_93082_1316710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93082 ⟨1316710, by decide⟩ :=
  accepted_of_selected 11 93082 ⟨1316710, by decide⟩ ⟨11, 2, 0, 1316710, 93082, 1153, 262144⟩
    (by decide) selected_cut_47101

theorem selected_cut_47102 : selected 10 ⟨1316746, by decide⟩
    (prefixPartial 11 93083) = some ⟨11, 2, 0, 1316746, 93083, 2389, 262144⟩ := by
  decide +kernel

theorem context_11_93083_1316746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93083 ⟨1316746, by decide⟩ :=
  accepted_of_selected 11 93083 ⟨1316746, by decide⟩ ⟨11, 2, 0, 1316746, 93083, 2389, 262144⟩
    (by decide) selected_cut_47102

theorem unmarked_context_10_23270_1316747 : frontier 11 ⟨1316747, by decide⟩
    (prefixCache 10 23270) (prefixPartial 10 23270) = false := by
  decide +kernel

theorem node_context_10_23270_1316747 : EJMOriginalGlobalDAGData.nodes 11 ⟨1316747, by decide⟩ =
    .split (coordinate 10) (![⟨1316613, by decide⟩,⟨1316690, by decide⟩,⟨1316710, by decide⟩,⟨1316746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23270_1316747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23270 ⟨1316747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23270
    ⟨1316747, by decide⟩ (by decide) (![⟨1316613, by decide⟩,⟨1316690, by decide⟩,⟨1316710, by decide⟩,⟨1316746, by decide⟩]) unmarked_context_10_23270_1316747 node_context_10_23270_1316747
  intro a
  fin_cases a
  · exact context_11_93080_1316613
  · exact context_11_93081_1316690
  · exact context_11_93082_1316710
  · exact context_11_93083_1316746

theorem selected_cut_47103 : selected 9 ⟨1316769, by decide⟩
    (prefixPartial 12 372336) = some ⟨12, 2, 0, 1316769, 372336, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_372336_1316769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372336 ⟨1316769, by decide⟩ :=
  accepted_of_selected 12 372336 ⟨1316769, by decide⟩ ⟨12, 2, 0, 1316769, 372336, 1241, 65536⟩
    (by decide) selected_cut_47103

theorem selected_cut_47104 : selected 9 ⟨1316786, by decide⟩
    (prefixPartial 12 372337) = some ⟨12, 2, 0, 1316786, 372337, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_372337_1316786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372337 ⟨1316786, by decide⟩ :=
  accepted_of_selected 12 372337 ⟨1316786, by decide⟩ ⟨12, 2, 0, 1316786, 372337, 1101, 65536⟩
    (by decide) selected_cut_47104

theorem selected_cut_47105 : selected 9 ⟨1316804, by decide⟩
    (prefixPartial 12 372338) = some ⟨12, 2, 0, 1316804, 372338, 1001, 65536⟩ := by
  decide +kernel

theorem context_12_372338_1316804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372338 ⟨1316804, by decide⟩ :=
  accepted_of_selected 12 372338 ⟨1316804, by decide⟩ ⟨12, 2, 0, 1316804, 372338, 1001, 65536⟩
    (by decide) selected_cut_47105

theorem selected_cut_47106 : selected 9 ⟨1316820, by decide⟩
    (prefixPartial 12 372339) = some ⟨12, 2, 0, 1316820, 372339, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_372339_1316820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372339 ⟨1316820, by decide⟩ :=
  accepted_of_selected 12 372339 ⟨1316820, by decide⟩ ⟨12, 2, 0, 1316820, 372339, 1189, 65536⟩
    (by decide) selected_cut_47106

theorem unmarked_context_11_93084_1316821 : frontier 10 ⟨1316821, by decide⟩
    (prefixCache 11 93084) (prefixPartial 11 93084) = false := by
  decide +kernel

theorem node_context_11_93084_1316821 : EJMOriginalGlobalDAGData.nodes 10 ⟨1316821, by decide⟩ =
    .split (coordinate 11) (![⟨1316769, by decide⟩,⟨1316786, by decide⟩,⟨1316804, by decide⟩,⟨1316820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93084_1316821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93084 ⟨1316821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93084
    ⟨1316821, by decide⟩ (by decide) (![⟨1316769, by decide⟩,⟨1316786, by decide⟩,⟨1316804, by decide⟩,⟨1316820, by decide⟩]) unmarked_context_11_93084_1316821 node_context_11_93084_1316821
  intro a
  fin_cases a
  · exact context_12_372336_1316769
  · exact context_12_372337_1316786
  · exact context_12_372338_1316804
  · exact context_12_372339_1316820

theorem selected_cut_47107 : selected 10 ⟨1316888, by decide⟩
    (prefixPartial 11 93085) = some ⟨11, 2, 0, 1316888, 93085, 3069, 262144⟩ := by
  decide +kernel

theorem context_11_93085_1316888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93085 ⟨1316888, by decide⟩ :=
  accepted_of_selected 11 93085 ⟨1316888, by decide⟩ ⟨11, 2, 0, 1316888, 93085, 3069, 262144⟩
    (by decide) selected_cut_47107

theorem selected_cut_47108 : selected 10 ⟨1316922, by decide⟩
    (prefixPartial 11 93086) = some ⟨11, 2, 0, 1316922, 93086, 1669, 262144⟩ := by
  decide +kernel

theorem context_11_93086_1316922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93086 ⟨1316922, by decide⟩ :=
  accepted_of_selected 11 93086 ⟨1316922, by decide⟩ ⟨11, 2, 0, 1316922, 93086, 1669, 262144⟩
    (by decide) selected_cut_47108

theorem selected_cut_47109 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 93087) = some ⟨11, 1, 0, 977886, 93087, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93087_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93087 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 93087 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 93087, 1, 262144⟩
    (by decide) selected_cut_47109

theorem unmarked_context_10_23271_1316923 : frontier 11 ⟨1316923, by decide⟩
    (prefixCache 10 23271) (prefixPartial 10 23271) = false := by
  decide +kernel

theorem node_context_10_23271_1316923 : EJMOriginalGlobalDAGData.nodes 11 ⟨1316923, by decide⟩ =
    .split (coordinate 10) (![⟨1316821, by decide⟩,⟨1316888, by decide⟩,⟨1316922, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23271_1316923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23271 ⟨1316923, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23271
    ⟨1316923, by decide⟩ (by decide) (![⟨1316821, by decide⟩,⟨1316888, by decide⟩,⟨1316922, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23271_1316923 node_context_10_23271_1316923
  intro a
  fin_cases a
  · exact context_11_93084_1316821
  · exact context_11_93085_1316888
  · exact context_11_93086_1316922
  · exact context_11_93087_977886

theorem unmarked_context_9_5817_1316924 : frontier 12 ⟨1316924, by decide⟩
    (prefixCache 9 5817) (prefixPartial 9 5817) = false := by
  decide +kernel

theorem node_context_9_5817_1316924 : EJMOriginalGlobalDAGData.nodes 12 ⟨1316924, by decide⟩ =
    .split (coordinate 9) (![⟨1316540, by decide⟩,⟨893098, by decide⟩,⟨1316747, by decide⟩,⟨1316923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5817_1316924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5817 ⟨1316924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5817
    ⟨1316924, by decide⟩ (by decide) (![⟨1316540, by decide⟩,⟨893098, by decide⟩,⟨1316747, by decide⟩,⟨1316923, by decide⟩]) unmarked_context_9_5817_1316924 node_context_9_5817_1316924
  intro a
  fin_cases a
  · exact context_10_23268_1316540
  · exact context_10_23269_893098
  · exact context_10_23270_1316747
  · exact context_10_23271_1316923

theorem selected_cut_47110 : selected 10 ⟨1316979, by decide⟩
    (prefixPartial 11 93088) = some ⟨11, 2, 0, 1316979, 93088, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_93088_1316979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93088 ⟨1316979, by decide⟩ :=
  accepted_of_selected 11 93088 ⟨1316979, by decide⟩ ⟨11, 2, 0, 1316979, 93088, 1537, 262144⟩
    (by decide) selected_cut_47110

theorem selected_cut_47111 : selected 10 ⟨1317043, by decide⟩
    (prefixPartial 11 93089) = some ⟨11, 2, 0, 1317043, 93089, 2665, 262144⟩ := by
  decide +kernel

theorem context_11_93089_1317043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93089 ⟨1317043, by decide⟩ :=
  accepted_of_selected 11 93089 ⟨1317043, by decide⟩ ⟨11, 2, 0, 1317043, 93089, 2665, 262144⟩
    (by decide) selected_cut_47111

theorem selected_cut_47112 : selected 10 ⟨1317093, by decide⟩
    (prefixPartial 11 93090) = some ⟨11, 2, 0, 1317093, 93090, 2909, 262144⟩ := by
  decide +kernel

theorem context_11_93090_1317093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93090 ⟨1317093, by decide⟩ :=
  accepted_of_selected 11 93090 ⟨1317093, by decide⟩ ⟨11, 2, 0, 1317093, 93090, 2909, 262144⟩
    (by decide) selected_cut_47112

theorem selected_cut_47113 : selected 10 ⟨1317136, by decide⟩
    (prefixPartial 11 93091) = some ⟨11, 2, 0, 1317136, 93091, 2165, 262144⟩ := by
  decide +kernel

theorem context_11_93091_1317136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93091 ⟨1317136, by decide⟩ :=
  accepted_of_selected 11 93091 ⟨1317136, by decide⟩ ⟨11, 2, 0, 1317136, 93091, 2165, 262144⟩
    (by decide) selected_cut_47113

theorem unmarked_context_10_23272_1317137 : frontier 11 ⟨1317137, by decide⟩
    (prefixCache 10 23272) (prefixPartial 10 23272) = false := by
  decide +kernel

theorem node_context_10_23272_1317137 : EJMOriginalGlobalDAGData.nodes 11 ⟨1317137, by decide⟩ =
    .split (coordinate 10) (![⟨1316979, by decide⟩,⟨1317043, by decide⟩,⟨1317093, by decide⟩,⟨1317136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23272_1317137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23272 ⟨1317137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23272
    ⟨1317137, by decide⟩ (by decide) (![⟨1316979, by decide⟩,⟨1317043, by decide⟩,⟨1317093, by decide⟩,⟨1317136, by decide⟩]) unmarked_context_10_23272_1317137 node_context_10_23272_1317137
  intro a
  fin_cases a
  · exact context_11_93088_1316979
  · exact context_11_93089_1317043
  · exact context_11_93090_1317093
  · exact context_11_93091_1317136

theorem selected_cut_47114 : selected 10 ⟨1317174, by decide⟩
    (prefixPartial 11 93092) = some ⟨11, 2, 0, 1317174, 93092, 1929, 262144⟩ := by
  decide +kernel

theorem context_11_93092_1317174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93092 ⟨1317174, by decide⟩ :=
  accepted_of_selected 11 93092 ⟨1317174, by decide⟩ ⟨11, 2, 0, 1317174, 93092, 1929, 262144⟩
    (by decide) selected_cut_47114

theorem selected_cut_47115 : selected 10 ⟨1317190, by decide⟩
    (prefixPartial 11 93093) = some ⟨11, 2, 0, 1317190, 93093, 969, 262144⟩ := by
  decide +kernel

theorem context_11_93093_1317190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93093 ⟨1317190, by decide⟩ :=
  accepted_of_selected 11 93093 ⟨1317190, by decide⟩ ⟨11, 2, 0, 1317190, 93093, 969, 262144⟩
    (by decide) selected_cut_47115

theorem selected_cut_47116 : selected 10 ⟨1317226, by decide⟩
    (prefixPartial 11 93094) = some ⟨11, 2, 0, 1317226, 93094, 2049, 262144⟩ := by
  decide +kernel

theorem context_11_93094_1317226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93094 ⟨1317226, by decide⟩ :=
  accepted_of_selected 11 93094 ⟨1317226, by decide⟩ ⟨11, 2, 0, 1317226, 93094, 2049, 262144⟩
    (by decide) selected_cut_47116

theorem selected_cut_47117 : selected 10 ⟨1317254, by decide⟩
    (prefixPartial 11 93095) = some ⟨11, 2, 0, 1317254, 93095, 1597, 262144⟩ := by
  decide +kernel

theorem context_11_93095_1317254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93095 ⟨1317254, by decide⟩ :=
  accepted_of_selected 11 93095 ⟨1317254, by decide⟩ ⟨11, 2, 0, 1317254, 93095, 1597, 262144⟩
    (by decide) selected_cut_47117

theorem unmarked_context_10_23273_1317255 : frontier 11 ⟨1317255, by decide⟩
    (prefixCache 10 23273) (prefixPartial 10 23273) = false := by
  decide +kernel

theorem node_context_10_23273_1317255 : EJMOriginalGlobalDAGData.nodes 11 ⟨1317255, by decide⟩ =
    .split (coordinate 10) (![⟨1317174, by decide⟩,⟨1317190, by decide⟩,⟨1317226, by decide⟩,⟨1317254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23273_1317255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23273 ⟨1317255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23273
    ⟨1317255, by decide⟩ (by decide) (![⟨1317174, by decide⟩,⟨1317190, by decide⟩,⟨1317226, by decide⟩,⟨1317254, by decide⟩]) unmarked_context_10_23273_1317255 node_context_10_23273_1317255
  intro a
  fin_cases a
  · exact context_11_93092_1317174
  · exact context_11_93093_1317190
  · exact context_11_93094_1317226
  · exact context_11_93095_1317254

theorem selected_cut_47118 : selected 11 ⟨1317296, by decide⟩
    (prefixPartial 10 23274) = some ⟨10, 2, 0, 1317296, 23274, 2145, 1048576⟩ := by
  decide +kernel

theorem context_10_23274_1317296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23274 ⟨1317296, by decide⟩ :=
  accepted_of_selected 10 23274 ⟨1317296, by decide⟩ ⟨10, 2, 0, 1317296, 23274, 2145, 1048576⟩
    (by decide) selected_cut_47118

theorem selected_cut_47119 : selected 11 ⟨1317355, by decide⟩
    (prefixPartial 10 23275) = some ⟨10, 2, 0, 1317355, 23275, 3265, 1048576⟩ := by
  decide +kernel

theorem context_10_23275_1317355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23275 ⟨1317355, by decide⟩ :=
  accepted_of_selected 10 23275 ⟨1317355, by decide⟩ ⟨10, 2, 0, 1317355, 23275, 3265, 1048576⟩
    (by decide) selected_cut_47119

theorem unmarked_context_9_5818_1317356 : frontier 12 ⟨1317356, by decide⟩
    (prefixCache 9 5818) (prefixPartial 9 5818) = false := by
  decide +kernel

theorem node_context_9_5818_1317356 : EJMOriginalGlobalDAGData.nodes 12 ⟨1317356, by decide⟩ =
    .split (coordinate 9) (![⟨1317137, by decide⟩,⟨1317255, by decide⟩,⟨1317296, by decide⟩,⟨1317355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5818_1317356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5818 ⟨1317356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5818
    ⟨1317356, by decide⟩ (by decide) (![⟨1317137, by decide⟩,⟨1317255, by decide⟩,⟨1317296, by decide⟩,⟨1317355, by decide⟩]) unmarked_context_9_5818_1317356 node_context_9_5818_1317356
  intro a
  fin_cases a
  · exact context_10_23272_1317137
  · exact context_10_23273_1317255
  · exact context_10_23274_1317296
  · exact context_10_23275_1317355

theorem selected_cut_47120 : selected 11 ⟨1317424, by decide⟩
    (prefixPartial 10 23276) = some ⟨10, 2, 0, 1317424, 23276, 3925, 1048576⟩ := by
  decide +kernel

theorem context_10_23276_1317424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23276 ⟨1317424, by decide⟩ :=
  accepted_of_selected 10 23276 ⟨1317424, by decide⟩ ⟨10, 2, 0, 1317424, 23276, 3925, 1048576⟩
    (by decide) selected_cut_47120

theorem selected_cut_47121 : selected 11 ⟨1317456, by decide⟩
    (prefixPartial 10 23277) = some ⟨10, 2, 0, 1317456, 23277, 1821, 1048576⟩ := by
  decide +kernel

theorem context_10_23277_1317456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23277 ⟨1317456, by decide⟩ :=
  accepted_of_selected 10 23277 ⟨1317456, by decide⟩ ⟨10, 2, 0, 1317456, 23277, 1821, 1048576⟩
    (by decide) selected_cut_47121

theorem selected_cut_47122 : selected 11 ⟨1317485, by decide⟩
    (prefixPartial 10 23278) = some ⟨10, 2, 0, 1317485, 23278, 965, 1048576⟩ := by
  decide +kernel

theorem context_10_23278_1317485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23278 ⟨1317485, by decide⟩ :=
  accepted_of_selected 10 23278 ⟨1317485, by decide⟩ ⟨10, 2, 0, 1317485, 23278, 965, 1048576⟩
    (by decide) selected_cut_47122

theorem selected_cut_47123 : selected 11 ⟨1317499, by decide⟩
    (prefixPartial 10 23279) = some ⟨10, 2, 0, 1317499, 23279, 165, 1048576⟩ := by
  decide +kernel

theorem context_10_23279_1317499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23279 ⟨1317499, by decide⟩ :=
  accepted_of_selected 10 23279 ⟨1317499, by decide⟩ ⟨10, 2, 0, 1317499, 23279, 165, 1048576⟩
    (by decide) selected_cut_47123

theorem unmarked_context_9_5819_1317500 : frontier 12 ⟨1317500, by decide⟩
    (prefixCache 9 5819) (prefixPartial 9 5819) = false := by
  decide +kernel

theorem node_context_9_5819_1317500 : EJMOriginalGlobalDAGData.nodes 12 ⟨1317500, by decide⟩ =
    .split (coordinate 9) (![⟨1317424, by decide⟩,⟨1317456, by decide⟩,⟨1317485, by decide⟩,⟨1317499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5819_1317500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5819 ⟨1317500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5819
    ⟨1317500, by decide⟩ (by decide) (![⟨1317424, by decide⟩,⟨1317456, by decide⟩,⟨1317485, by decide⟩,⟨1317499, by decide⟩]) unmarked_context_9_5819_1317500 node_context_9_5819_1317500
  intro a
  fin_cases a
  · exact context_10_23276_1317424
  · exact context_10_23277_1317456
  · exact context_10_23278_1317485
  · exact context_10_23279_1317499

theorem unmarked_context_8_1454_1317501 : frontier 13 ⟨1317501, by decide⟩
    (prefixCache 8 1454) (prefixPartial 8 1454) = false := by
  decide +kernel

theorem node_context_8_1454_1317501 : EJMOriginalGlobalDAGData.nodes 13 ⟨1317501, by decide⟩ =
    .split (coordinate 8) (![⟨1316155, by decide⟩,⟨1316924, by decide⟩,⟨1317356, by decide⟩,⟨1317500, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1454_1317501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1454 ⟨1317501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1454
    ⟨1317501, by decide⟩ (by decide) (![⟨1316155, by decide⟩,⟨1316924, by decide⟩,⟨1317356, by decide⟩,⟨1317500, by decide⟩]) unmarked_context_8_1454_1317501 node_context_8_1454_1317501
  intro a
  fin_cases a
  · exact context_9_5816_1316155
  · exact context_9_5817_1316924
  · exact context_9_5818_1317356
  · exact context_9_5819_1317500

theorem selected_cut_47124 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93120) = some ⟨11, 1, 0, 434745, 93120, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93120_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93120 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93120 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93120, 1, 262144⟩
    (by decide) selected_cut_47124

theorem selected_cut_47125 : selected 10 ⟨1317606, by decide⟩
    (prefixPartial 11 93121) = some ⟨11, 2, 0, 1317606, 93121, 3725, 262144⟩ := by
  decide +kernel

theorem context_11_93121_1317606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93121 ⟨1317606, by decide⟩ :=
  accepted_of_selected 11 93121 ⟨1317606, by decide⟩ ⟨11, 2, 0, 1317606, 93121, 3725, 262144⟩
    (by decide) selected_cut_47125

theorem selected_cut_47126 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 372488) = some ⟨12, 1, 0, 448748, 372488, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372488_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372488 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 372488 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 372488, 1, 65536⟩
    (by decide) selected_cut_47126

theorem selected_cut_47127 : selected 9 ⟨1317730, by decide⟩
    (prefixPartial 12 372489) = some ⟨12, 2, 0, 1317730, 372489, 4045, 65536⟩ := by
  decide +kernel

theorem context_12_372489_1317730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372489 ⟨1317730, by decide⟩ :=
  accepted_of_selected 12 372489 ⟨1317730, by decide⟩ ⟨12, 2, 0, 1317730, 372489, 4045, 65536⟩
    (by decide) selected_cut_47127

theorem selected_cut_47128 : selected 9 ⟨1317815, by decide⟩
    (prefixPartial 12 372490) = some ⟨12, 2, 0, 1317815, 372490, 3325, 65536⟩ := by
  decide +kernel

theorem context_12_372490_1317815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372490 ⟨1317815, by decide⟩ :=
  accepted_of_selected 12 372490 ⟨1317815, by decide⟩ ⟨12, 2, 0, 1317815, 372490, 3325, 65536⟩
    (by decide) selected_cut_47128

theorem selected_cut_47129 : selected 9 ⟨1317892, by decide⟩
    (prefixPartial 12 372491) = some ⟨12, 2, 0, 1317892, 372491, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_372491_1317892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372491 ⟨1317892, by decide⟩ :=
  accepted_of_selected 12 372491 ⟨1317892, by decide⟩ ⟨12, 2, 0, 1317892, 372491, 3669, 65536⟩
    (by decide) selected_cut_47129

theorem unmarked_context_11_93122_1317893 : frontier 10 ⟨1317893, by decide⟩
    (prefixCache 11 93122) (prefixPartial 11 93122) = false := by
  decide +kernel

theorem node_context_11_93122_1317893 : EJMOriginalGlobalDAGData.nodes 10 ⟨1317893, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1317730, by decide⟩,⟨1317815, by decide⟩,⟨1317892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93122_1317893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93122 ⟨1317893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93122
    ⟨1317893, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1317730, by decide⟩,⟨1317815, by decide⟩,⟨1317892, by decide⟩]) unmarked_context_11_93122_1317893 node_context_11_93122_1317893
  intro a
  fin_cases a
  · exact context_12_372488_448748
  · exact context_12_372489_1317730
  · exact context_12_372490_1317815
  · exact context_12_372491_1317892

theorem selected_cut_47130 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 372492) = some ⟨12, 1, 0, 448748, 372492, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372492_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372492 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 372492 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 372492, 1, 65536⟩
    (by decide) selected_cut_47130

theorem selected_cut_47131 : selected 9 ⟨1317955, by decide⟩
    (prefixPartial 12 372493) = some ⟨12, 2, 0, 1317955, 372493, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_372493_1317955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372493 ⟨1317955, by decide⟩ :=
  accepted_of_selected 12 372493 ⟨1317955, by decide⟩ ⟨12, 2, 0, 1317955, 372493, 3273, 65536⟩
    (by decide) selected_cut_47131

theorem selected_cut_47132 : selected 9 ⟨1318015, by decide⟩
    (prefixPartial 12 372494) = some ⟨12, 2, 0, 1318015, 372494, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_372494_1318015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372494 ⟨1318015, by decide⟩ :=
  accepted_of_selected 12 372494 ⟨1318015, by decide⟩ ⟨12, 2, 0, 1318015, 372494, 3041, 65536⟩
    (by decide) selected_cut_47132

theorem selected_cut_47133 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 372495) = some ⟨12, 1, 0, 903806, 372495, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372495_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372495 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 372495 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 372495, 1, 65536⟩
    (by decide) selected_cut_47133

theorem unmarked_context_11_93123_1318016 : frontier 10 ⟨1318016, by decide⟩
    (prefixCache 11 93123) (prefixPartial 11 93123) = false := by
  decide +kernel

theorem node_context_11_93123_1318016 : EJMOriginalGlobalDAGData.nodes 10 ⟨1318016, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1317955, by decide⟩,⟨1318015, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93123_1318016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93123 ⟨1318016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93123
    ⟨1318016, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1317955, by decide⟩,⟨1318015, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93123_1318016 node_context_11_93123_1318016
  intro a
  fin_cases a
  · exact context_12_372492_448748
  · exact context_12_372493_1317955
  · exact context_12_372494_1318015
  · exact context_12_372495_903806

theorem unmarked_context_10_23280_1318017 : frontier 11 ⟨1318017, by decide⟩
    (prefixCache 10 23280) (prefixPartial 10 23280) = false := by
  decide +kernel

theorem node_context_10_23280_1318017 : EJMOriginalGlobalDAGData.nodes 11 ⟨1318017, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1317606, by decide⟩,⟨1317893, by decide⟩,⟨1318016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23280_1318017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23280 ⟨1318017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23280
    ⟨1318017, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1317606, by decide⟩,⟨1317893, by decide⟩,⟨1318016, by decide⟩]) unmarked_context_10_23280_1318017 node_context_10_23280_1318017
  intro a
  fin_cases a
  · exact context_11_93120_434745
  · exact context_11_93121_1317606
  · exact context_11_93122_1317893
  · exact context_11_93123_1318016

theorem selected_cut_47134 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 372496) = some ⟨12, 1, 0, 1255011, 372496, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372496_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372496 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 372496 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 372496, 1, 65536⟩
    (by decide) selected_cut_47134

theorem selected_cut_47135 : selected 9 ⟨1318092, by decide⟩
    (prefixPartial 12 372497) = some ⟨12, 2, 0, 1318092, 372497, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_372497_1318092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372497 ⟨1318092, by decide⟩ :=
  accepted_of_selected 12 372497 ⟨1318092, by decide⟩ ⟨12, 2, 0, 1318092, 372497, 3553, 65536⟩
    (by decide) selected_cut_47135

theorem selected_cut_47136 : selected 9 ⟨1318158, by decide⟩
    (prefixPartial 12 372498) = some ⟨12, 2, 0, 1318158, 372498, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_372498_1318158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372498 ⟨1318158, by decide⟩ :=
  accepted_of_selected 12 372498 ⟨1318158, by decide⟩ ⟨12, 2, 0, 1318158, 372498, 3257, 65536⟩
    (by decide) selected_cut_47136

theorem selected_cut_47137 : selected 9 ⟨1318217, by decide⟩
    (prefixPartial 12 372499) = some ⟨12, 2, 0, 1318217, 372499, 3593, 65536⟩ := by
  decide +kernel

theorem context_12_372499_1318217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372499 ⟨1318217, by decide⟩ :=
  accepted_of_selected 12 372499 ⟨1318217, by decide⟩ ⟨12, 2, 0, 1318217, 372499, 3593, 65536⟩
    (by decide) selected_cut_47137

theorem unmarked_context_11_93124_1318218 : frontier 10 ⟨1318218, by decide⟩
    (prefixCache 11 93124) (prefixPartial 11 93124) = false := by
  decide +kernel

theorem node_context_11_93124_1318218 : EJMOriginalGlobalDAGData.nodes 10 ⟨1318218, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1318092, by decide⟩,⟨1318158, by decide⟩,⟨1318217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93124_1318218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93124 ⟨1318218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93124
    ⟨1318218, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1318092, by decide⟩,⟨1318158, by decide⟩,⟨1318217, by decide⟩]) unmarked_context_11_93124_1318218 node_context_11_93124_1318218
  intro a
  fin_cases a
  · exact context_12_372496_1255011
  · exact context_12_372497_1318092
  · exact context_12_372498_1318158
  · exact context_12_372499_1318217

theorem selected_cut_47138 : selected 9 ⟨1318310, by decide⟩
    (prefixPartial 12 372500) = some ⟨12, 2, 0, 1318310, 372500, 3781, 65536⟩ := by
  decide +kernel

theorem context_12_372500_1318310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372500 ⟨1318310, by decide⟩ :=
  accepted_of_selected 12 372500 ⟨1318310, by decide⟩ ⟨12, 2, 0, 1318310, 372500, 3781, 65536⟩
    (by decide) selected_cut_47138

theorem selected_cut_47139 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 372501) = some ⟨12, 1, 0, 1172003, 372501, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372501_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372501 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 372501 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 372501, 1, 65536⟩
    (by decide) selected_cut_47139

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
