/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover543
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_52226 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 288773) = some ⟨11, 1, 0, 1468419, 288773, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288773_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288773 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 288773 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 288773, 1, 262144⟩
    (by decide) selected_cut_52226

theorem selected_cut_52227 : selected 10 ⟨1518754, by decide⟩
    (prefixPartial 11 288774) = some ⟨11, 2, 0, 1518754, 288774, 2721, 262144⟩ := by
  decide +kernel

theorem context_11_288774_1518754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288774 ⟨1518754, by decide⟩ :=
  accepted_of_selected 11 288774 ⟨1518754, by decide⟩ ⟨11, 2, 0, 1518754, 288774, 2721, 262144⟩
    (by decide) selected_cut_52227

theorem selected_cut_52228 : selected 10 ⟨1518829, by decide⟩
    (prefixPartial 11 288775) = some ⟨11, 2, 0, 1518829, 288775, 2481, 262144⟩ := by
  decide +kernel

theorem context_11_288775_1518829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288775 ⟨1518829, by decide⟩ :=
  accepted_of_selected 11 288775 ⟨1518829, by decide⟩ ⟨11, 2, 0, 1518829, 288775, 2481, 262144⟩
    (by decide) selected_cut_52228

theorem unmarked_context_10_72193_1518830 : frontier 11 ⟨1518830, by decide⟩
    (prefixCache 10 72193) (prefixPartial 10 72193) = false := by
  decide +kernel

theorem node_context_10_72193_1518830 : EJMOriginalGlobalDAGData.nodes 11 ⟨1518830, by decide⟩ =
    .split (coordinate 10) (![⟨1518654, by decide⟩,⟨1468419, by decide⟩,⟨1518754, by decide⟩,⟨1518829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72193_1518830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72193 ⟨1518830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72193
    ⟨1518830, by decide⟩ (by decide) (![⟨1518654, by decide⟩,⟨1468419, by decide⟩,⟨1518754, by decide⟩,⟨1518829, by decide⟩]) unmarked_context_10_72193_1518830 node_context_10_72193_1518830
  intro a
  fin_cases a
  · exact context_11_288772_1518654
  · exact context_11_288773_1468419
  · exact context_11_288774_1518754
  · exact context_11_288775_1518829

theorem selected_cut_52229 : selected 10 ⟨1518881, by decide⟩
    (prefixPartial 11 288776) = some ⟨11, 2, 0, 1518881, 288776, 1997, 262144⟩ := by
  decide +kernel

theorem context_11_288776_1518881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288776 ⟨1518881, by decide⟩ :=
  accepted_of_selected 11 288776 ⟨1518881, by decide⟩ ⟨11, 2, 0, 1518881, 288776, 1997, 262144⟩
    (by decide) selected_cut_52229

theorem selected_cut_52230 : selected 10 ⟨1518913, by decide⟩
    (prefixPartial 11 288777) = some ⟨11, 2, 0, 1518913, 288777, 1133, 262144⟩ := by
  decide +kernel

theorem context_11_288777_1518913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288777 ⟨1518913, by decide⟩ :=
  accepted_of_selected 11 288777 ⟨1518913, by decide⟩ ⟨11, 2, 0, 1518913, 288777, 1133, 262144⟩
    (by decide) selected_cut_52230

theorem selected_cut_52231 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 288778) = some ⟨11, 1, 0, 1468743, 288778, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288778_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288778 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 288778 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 288778, 1, 262144⟩
    (by decide) selected_cut_52231

theorem selected_cut_52232 : selected 10 ⟨1518941, by decide⟩
    (prefixPartial 11 288779) = some ⟨11, 2, 0, 1518941, 288779, 1085, 262144⟩ := by
  decide +kernel

theorem context_11_288779_1518941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288779 ⟨1518941, by decide⟩ :=
  accepted_of_selected 11 288779 ⟨1518941, by decide⟩ ⟨11, 2, 0, 1518941, 288779, 1085, 262144⟩
    (by decide) selected_cut_52232

theorem unmarked_context_10_72194_1518942 : frontier 11 ⟨1518942, by decide⟩
    (prefixCache 10 72194) (prefixPartial 10 72194) = false := by
  decide +kernel

theorem node_context_10_72194_1518942 : EJMOriginalGlobalDAGData.nodes 11 ⟨1518942, by decide⟩ =
    .split (coordinate 10) (![⟨1518881, by decide⟩,⟨1518913, by decide⟩,⟨1468743, by decide⟩,⟨1518941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72194_1518942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72194 ⟨1518942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72194
    ⟨1518942, by decide⟩ (by decide) (![⟨1518881, by decide⟩,⟨1518913, by decide⟩,⟨1468743, by decide⟩,⟨1518941, by decide⟩]) unmarked_context_10_72194_1518942 node_context_10_72194_1518942
  intro a
  fin_cases a
  · exact context_11_288776_1518881
  · exact context_11_288777_1518913
  · exact context_11_288778_1468743
  · exact context_11_288779_1518941

theorem selected_cut_52233 : selected 10 ⟨1518959, by decide⟩
    (prefixPartial 11 288780) = some ⟨11, 2, 0, 1518959, 288780, 841, 262144⟩ := by
  decide +kernel

theorem context_11_288780_1518959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288780 ⟨1518959, by decide⟩ :=
  accepted_of_selected 11 288780 ⟨1518959, by decide⟩ ⟨11, 2, 0, 1518959, 288780, 841, 262144⟩
    (by decide) selected_cut_52233

theorem selected_cut_52234 : selected 10 ⟨1519011, by decide⟩
    (prefixPartial 11 288781) = some ⟨11, 2, 0, 1519011, 288781, 1849, 262144⟩ := by
  decide +kernel

theorem context_11_288781_1519011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288781 ⟨1519011, by decide⟩ :=
  accepted_of_selected 11 288781 ⟨1519011, by decide⟩ ⟨11, 2, 0, 1519011, 288781, 1849, 262144⟩
    (by decide) selected_cut_52234

theorem selected_cut_52235 : selected 10 ⟨1519059, by decide⟩
    (prefixPartial 11 288782) = some ⟨11, 2, 0, 1519059, 288782, 1461, 262144⟩ := by
  decide +kernel

theorem context_11_288782_1519059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288782 ⟨1519059, by decide⟩ :=
  accepted_of_selected 11 288782 ⟨1519059, by decide⟩ ⟨11, 2, 0, 1519059, 288782, 1461, 262144⟩
    (by decide) selected_cut_52235

theorem selected_cut_52236 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 288783) = some ⟨11, 1, 0, 1470044, 288783, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288783_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288783 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 288783 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 288783, 1, 262144⟩
    (by decide) selected_cut_52236

theorem unmarked_context_10_72195_1519060 : frontier 11 ⟨1519060, by decide⟩
    (prefixCache 10 72195) (prefixPartial 10 72195) = false := by
  decide +kernel

theorem node_context_10_72195_1519060 : EJMOriginalGlobalDAGData.nodes 11 ⟨1519060, by decide⟩ =
    .split (coordinate 10) (![⟨1518959, by decide⟩,⟨1519011, by decide⟩,⟨1519059, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72195_1519060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72195 ⟨1519060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72195
    ⟨1519060, by decide⟩ (by decide) (![⟨1518959, by decide⟩,⟨1519011, by decide⟩,⟨1519059, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_72195_1519060 node_context_10_72195_1519060
  intro a
  fin_cases a
  · exact context_11_288780_1518959
  · exact context_11_288781_1519011
  · exact context_11_288782_1519059
  · exact context_11_288783_1470044

theorem unmarked_context_9_18048_1519061 : frontier 12 ⟨1519061, by decide⟩
    (prefixCache 9 18048) (prefixPartial 9 18048) = false := by
  decide +kernel

theorem node_context_9_18048_1519061 : EJMOriginalGlobalDAGData.nodes 12 ⟨1519061, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1518830, by decide⟩,⟨1518942, by decide⟩,⟨1519060, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18048_1519061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18048 ⟨1519061, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18048
    ⟨1519061, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1518830, by decide⟩,⟨1518942, by decide⟩,⟨1519060, by decide⟩]) unmarked_context_9_18048_1519061 node_context_9_18048_1519061
  intro a
  fin_cases a
  · exact context_10_72192_1468246
  · exact context_10_72193_1518830
  · exact context_10_72194_1518942
  · exact context_10_72195_1519060

theorem selected_cut_52237 : selected 11 ⟨1519129, by decide⟩
    (prefixPartial 10 72196) = some ⟨10, 2, 0, 1519129, 72196, 2633, 1048576⟩ := by
  decide +kernel

theorem context_10_72196_1519129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72196 ⟨1519129, by decide⟩ :=
  accepted_of_selected 10 72196 ⟨1519129, by decide⟩ ⟨10, 2, 0, 1519129, 72196, 2633, 1048576⟩
    (by decide) selected_cut_52237

theorem selected_cut_52238 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72197) = some ⟨10, 1, 0, 1468874, 72197, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72197_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72197 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72197 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72197, 1, 1048576⟩
    (by decide) selected_cut_52238

theorem selected_cut_52239 : selected 11 ⟨1519217, by decide⟩
    (prefixPartial 10 72198) = some ⟨10, 2, 0, 1519217, 72198, 3101, 1048576⟩ := by
  decide +kernel

theorem context_10_72198_1519217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72198 ⟨1519217, by decide⟩ :=
  accepted_of_selected 10 72198 ⟨1519217, by decide⟩ ⟨10, 2, 0, 1519217, 72198, 3101, 1048576⟩
    (by decide) selected_cut_52239

theorem selected_cut_52240 : selected 11 ⟨1519297, by decide⟩
    (prefixPartial 10 72199) = some ⟨10, 2, 0, 1519297, 72199, 2937, 1048576⟩ := by
  decide +kernel

theorem context_10_72199_1519297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72199 ⟨1519297, by decide⟩ :=
  accepted_of_selected 10 72199 ⟨1519297, by decide⟩ ⟨10, 2, 0, 1519297, 72199, 2937, 1048576⟩
    (by decide) selected_cut_52240

theorem unmarked_context_9_18049_1519298 : frontier 12 ⟨1519298, by decide⟩
    (prefixCache 9 18049) (prefixPartial 9 18049) = false := by
  decide +kernel

theorem node_context_9_18049_1519298 : EJMOriginalGlobalDAGData.nodes 12 ⟨1519298, by decide⟩ =
    .split (coordinate 9) (![⟨1519129, by decide⟩,⟨1468874, by decide⟩,⟨1519217, by decide⟩,⟨1519297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18049_1519298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18049 ⟨1519298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18049
    ⟨1519298, by decide⟩ (by decide) (![⟨1519129, by decide⟩,⟨1468874, by decide⟩,⟨1519217, by decide⟩,⟨1519297, by decide⟩]) unmarked_context_9_18049_1519298 node_context_9_18049_1519298
  intro a
  fin_cases a
  · exact context_10_72196_1519129
  · exact context_10_72197_1468874
  · exact context_10_72198_1519217
  · exact context_10_72199_1519297

theorem selected_cut_52241 : selected 12 ⟨1519386, by decide⟩
    (prefixPartial 9 18050) = some ⟨9, 2, 0, 1519386, 18050, 3277, 4194304⟩ := by
  decide +kernel

theorem context_9_18050_1519386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18050 ⟨1519386, by decide⟩ :=
  accepted_of_selected 9 18050 ⟨1519386, by decide⟩ ⟨9, 2, 0, 1519386, 18050, 3277, 4194304⟩
    (by decide) selected_cut_52241

theorem selected_cut_52242 : selected 12 ⟨1519444, by decide⟩
    (prefixPartial 9 18051) = some ⟨9, 2, 0, 1519444, 18051, 1605, 4194304⟩ := by
  decide +kernel

theorem context_9_18051_1519444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18051 ⟨1519444, by decide⟩ :=
  accepted_of_selected 9 18051 ⟨1519444, by decide⟩ ⟨9, 2, 0, 1519444, 18051, 1605, 4194304⟩
    (by decide) selected_cut_52242

theorem unmarked_context_8_4512_1519445 : frontier 13 ⟨1519445, by decide⟩
    (prefixCache 8 4512) (prefixPartial 8 4512) = false := by
  decide +kernel

theorem node_context_8_4512_1519445 : EJMOriginalGlobalDAGData.nodes 13 ⟨1519445, by decide⟩ =
    .split (coordinate 8) (![⟨1519061, by decide⟩,⟨1519298, by decide⟩,⟨1519386, by decide⟩,⟨1519444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4512_1519445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4512 ⟨1519445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4512
    ⟨1519445, by decide⟩ (by decide) (![⟨1519061, by decide⟩,⟨1519298, by decide⟩,⟨1519386, by decide⟩,⟨1519444, by decide⟩]) unmarked_context_8_4512_1519445 node_context_8_4512_1519445
  intro a
  fin_cases a
  · exact context_9_18048_1519061
  · exact context_9_18049_1519298
  · exact context_9_18050_1519386
  · exact context_9_18051_1519444

theorem selected_cut_52243 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72208) = some ⟨10, 1, 0, 1468246, 72208, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72208_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72208 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72208 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72208, 1, 1048576⟩
    (by decide) selected_cut_52243

theorem selected_cut_52244 : selected 10 ⟨1519520, by decide⟩
    (prefixPartial 11 288836) = some ⟨11, 2, 0, 1519520, 288836, 2717, 262144⟩ := by
  decide +kernel

theorem context_11_288836_1519520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288836 ⟨1519520, by decide⟩ :=
  accepted_of_selected 11 288836 ⟨1519520, by decide⟩ ⟨11, 2, 0, 1519520, 288836, 2717, 262144⟩
    (by decide) selected_cut_52244

theorem selected_cut_52245 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 288837) = some ⟨11, 1, 0, 1468419, 288837, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288837_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288837 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 288837 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 288837, 1, 262144⟩
    (by decide) selected_cut_52245

theorem selected_cut_52246 : selected 10 ⟨1519614, by decide⟩
    (prefixPartial 11 288838) = some ⟨11, 2, 0, 1519614, 288838, 2873, 262144⟩ := by
  decide +kernel

theorem context_11_288838_1519614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288838 ⟨1519614, by decide⟩ :=
  accepted_of_selected 11 288838 ⟨1519614, by decide⟩ ⟨11, 2, 0, 1519614, 288838, 2873, 262144⟩
    (by decide) selected_cut_52246

theorem selected_cut_52247 : selected 10 ⟨1519700, by decide⟩
    (prefixPartial 11 288839) = some ⟨11, 2, 0, 1519700, 288839, 2841, 262144⟩ := by
  decide +kernel

theorem context_11_288839_1519700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288839 ⟨1519700, by decide⟩ :=
  accepted_of_selected 11 288839 ⟨1519700, by decide⟩ ⟨11, 2, 0, 1519700, 288839, 2841, 262144⟩
    (by decide) selected_cut_52247

theorem unmarked_context_10_72209_1519701 : frontier 11 ⟨1519701, by decide⟩
    (prefixCache 10 72209) (prefixPartial 10 72209) = false := by
  decide +kernel

theorem node_context_10_72209_1519701 : EJMOriginalGlobalDAGData.nodes 11 ⟨1519701, by decide⟩ =
    .split (coordinate 10) (![⟨1519520, by decide⟩,⟨1468419, by decide⟩,⟨1519614, by decide⟩,⟨1519700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72209_1519701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72209 ⟨1519701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72209
    ⟨1519701, by decide⟩ (by decide) (![⟨1519520, by decide⟩,⟨1468419, by decide⟩,⟨1519614, by decide⟩,⟨1519700, by decide⟩]) unmarked_context_10_72209_1519701 node_context_10_72209_1519701
  intro a
  fin_cases a
  · exact context_11_288836_1519520
  · exact context_11_288837_1468419
  · exact context_11_288838_1519614
  · exact context_11_288839_1519700

theorem selected_cut_52248 : selected 10 ⟨1519758, by decide⟩
    (prefixPartial 11 288840) = some ⟨11, 2, 0, 1519758, 288840, 2537, 262144⟩ := by
  decide +kernel

theorem context_11_288840_1519758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288840 ⟨1519758, by decide⟩ :=
  accepted_of_selected 11 288840 ⟨1519758, by decide⟩ ⟨11, 2, 0, 1519758, 288840, 2537, 262144⟩
    (by decide) selected_cut_52248

theorem selected_cut_52249 : selected 10 ⟨1519794, by decide⟩
    (prefixPartial 11 288841) = some ⟨11, 2, 0, 1519794, 288841, 1249, 262144⟩ := by
  decide +kernel

theorem context_11_288841_1519794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288841 ⟨1519794, by decide⟩ :=
  accepted_of_selected 11 288841 ⟨1519794, by decide⟩ ⟨11, 2, 0, 1519794, 288841, 1249, 262144⟩
    (by decide) selected_cut_52249

theorem selected_cut_52250 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 288842) = some ⟨11, 1, 0, 1468743, 288842, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288842_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288842 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 288842 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 288842, 1, 262144⟩
    (by decide) selected_cut_52250

theorem selected_cut_52251 : selected 10 ⟨1519839, by decide⟩
    (prefixPartial 11 288843) = some ⟨11, 2, 0, 1519839, 288843, 1361, 262144⟩ := by
  decide +kernel

theorem context_11_288843_1519839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288843 ⟨1519839, by decide⟩ :=
  accepted_of_selected 11 288843 ⟨1519839, by decide⟩ ⟨11, 2, 0, 1519839, 288843, 1361, 262144⟩
    (by decide) selected_cut_52251

theorem unmarked_context_10_72210_1519840 : frontier 11 ⟨1519840, by decide⟩
    (prefixCache 10 72210) (prefixPartial 10 72210) = false := by
  decide +kernel

theorem node_context_10_72210_1519840 : EJMOriginalGlobalDAGData.nodes 11 ⟨1519840, by decide⟩ =
    .split (coordinate 10) (![⟨1519758, by decide⟩,⟨1519794, by decide⟩,⟨1468743, by decide⟩,⟨1519839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72210_1519840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72210 ⟨1519840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72210
    ⟨1519840, by decide⟩ (by decide) (![⟨1519758, by decide⟩,⟨1519794, by decide⟩,⟨1468743, by decide⟩,⟨1519839, by decide⟩]) unmarked_context_10_72210_1519840 node_context_10_72210_1519840
  intro a
  fin_cases a
  · exact context_11_288840_1519758
  · exact context_11_288841_1519794
  · exact context_11_288842_1468743
  · exact context_11_288843_1519839

theorem selected_cut_52252 : selected 10 ⟨1519895, by decide⟩
    (prefixPartial 11 288844) = some ⟨11, 2, 0, 1519895, 288844, 2177, 262144⟩ := by
  decide +kernel

theorem context_11_288844_1519895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288844 ⟨1519895, by decide⟩ :=
  accepted_of_selected 11 288844 ⟨1519895, by decide⟩ ⟨11, 2, 0, 1519895, 288844, 2177, 262144⟩
    (by decide) selected_cut_52252

theorem selected_cut_52253 : selected 10 ⟨1519947, by decide⟩
    (prefixPartial 11 288845) = some ⟨11, 2, 0, 1519947, 288845, 1961, 262144⟩ := by
  decide +kernel

theorem context_11_288845_1519947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288845 ⟨1519947, by decide⟩ :=
  accepted_of_selected 11 288845 ⟨1519947, by decide⟩ ⟨11, 2, 0, 1519947, 288845, 1961, 262144⟩
    (by decide) selected_cut_52253

theorem selected_cut_52254 : selected 10 ⟨1520011, by decide⟩
    (prefixPartial 11 288846) = some ⟨11, 2, 0, 1520011, 288846, 2257, 262144⟩ := by
  decide +kernel

theorem context_11_288846_1520011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288846 ⟨1520011, by decide⟩ :=
  accepted_of_selected 11 288846 ⟨1520011, by decide⟩ ⟨11, 2, 0, 1520011, 288846, 2257, 262144⟩
    (by decide) selected_cut_52254

theorem selected_cut_52255 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 288847) = some ⟨11, 1, 0, 1470044, 288847, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288847_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288847 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 288847 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 288847, 1, 262144⟩
    (by decide) selected_cut_52255

theorem unmarked_context_10_72211_1520012 : frontier 11 ⟨1520012, by decide⟩
    (prefixCache 10 72211) (prefixPartial 10 72211) = false := by
  decide +kernel

theorem node_context_10_72211_1520012 : EJMOriginalGlobalDAGData.nodes 11 ⟨1520012, by decide⟩ =
    .split (coordinate 10) (![⟨1519895, by decide⟩,⟨1519947, by decide⟩,⟨1520011, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72211_1520012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72211 ⟨1520012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72211
    ⟨1520012, by decide⟩ (by decide) (![⟨1519895, by decide⟩,⟨1519947, by decide⟩,⟨1520011, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_72211_1520012 node_context_10_72211_1520012
  intro a
  fin_cases a
  · exact context_11_288844_1519895
  · exact context_11_288845_1519947
  · exact context_11_288846_1520011
  · exact context_11_288847_1470044

theorem unmarked_context_9_18052_1520013 : frontier 12 ⟨1520013, by decide⟩
    (prefixCache 9 18052) (prefixPartial 9 18052) = false := by
  decide +kernel

theorem node_context_9_18052_1520013 : EJMOriginalGlobalDAGData.nodes 12 ⟨1520013, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1519701, by decide⟩,⟨1519840, by decide⟩,⟨1520012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18052_1520013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18052 ⟨1520013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18052
    ⟨1520013, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1519701, by decide⟩,⟨1519840, by decide⟩,⟨1520012, by decide⟩]) unmarked_context_9_18052_1520013 node_context_9_18052_1520013
  intro a
  fin_cases a
  · exact context_10_72208_1468246
  · exact context_10_72209_1519701
  · exact context_10_72210_1519840
  · exact context_10_72211_1520012

theorem selected_cut_52256 : selected 11 ⟨1520095, by decide⟩
    (prefixPartial 10 72212) = some ⟨10, 2, 0, 1520095, 72212, 3085, 1048576⟩ := by
  decide +kernel

theorem context_10_72212_1520095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72212 ⟨1520095, by decide⟩ :=
  accepted_of_selected 10 72212 ⟨1520095, by decide⟩ ⟨10, 2, 0, 1520095, 72212, 3085, 1048576⟩
    (by decide) selected_cut_52256

theorem selected_cut_52257 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72213) = some ⟨10, 1, 0, 1468874, 72213, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72213_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72213 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72213 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72213, 1, 1048576⟩
    (by decide) selected_cut_52257

theorem selected_cut_52258 : selected 10 ⟨1520147, by decide⟩
    (prefixPartial 11 288856) = some ⟨11, 2, 0, 1520147, 288856, 1369, 262144⟩ := by
  decide +kernel

theorem context_11_288856_1520147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288856 ⟨1520147, by decide⟩ :=
  accepted_of_selected 11 288856 ⟨1520147, by decide⟩ ⟨11, 2, 0, 1520147, 288856, 1369, 262144⟩
    (by decide) selected_cut_52258

theorem selected_cut_52259 : selected 10 ⟨1520189, by decide⟩
    (prefixPartial 11 288857) = some ⟨11, 2, 0, 1520189, 288857, 1421, 262144⟩ := by
  decide +kernel

theorem context_11_288857_1520189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288857 ⟨1520189, by decide⟩ :=
  accepted_of_selected 11 288857 ⟨1520189, by decide⟩ ⟨11, 2, 0, 1520189, 288857, 1421, 262144⟩
    (by decide) selected_cut_52259

theorem selected_cut_52260 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 288858) = some ⟨11, 1, 0, 1468743, 288858, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288858_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288858 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 288858 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 288858, 1, 262144⟩
    (by decide) selected_cut_52260

theorem selected_cut_52261 : selected 10 ⟨1520227, by decide⟩
    (prefixPartial 11 288859) = some ⟨11, 2, 0, 1520227, 288859, 1437, 262144⟩ := by
  decide +kernel

theorem context_11_288859_1520227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288859 ⟨1520227, by decide⟩ :=
  accepted_of_selected 11 288859 ⟨1520227, by decide⟩ ⟨11, 2, 0, 1520227, 288859, 1437, 262144⟩
    (by decide) selected_cut_52261

theorem unmarked_context_10_72214_1520228 : frontier 11 ⟨1520228, by decide⟩
    (prefixCache 10 72214) (prefixPartial 10 72214) = false := by
  decide +kernel

theorem node_context_10_72214_1520228 : EJMOriginalGlobalDAGData.nodes 11 ⟨1520228, by decide⟩ =
    .split (coordinate 10) (![⟨1520147, by decide⟩,⟨1520189, by decide⟩,⟨1468743, by decide⟩,⟨1520227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72214_1520228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72214 ⟨1520228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72214
    ⟨1520228, by decide⟩ (by decide) (![⟨1520147, by decide⟩,⟨1520189, by decide⟩,⟨1468743, by decide⟩,⟨1520227, by decide⟩]) unmarked_context_10_72214_1520228 node_context_10_72214_1520228
  intro a
  fin_cases a
  · exact context_11_288856_1520147
  · exact context_11_288857_1520189
  · exact context_11_288858_1468743
  · exact context_11_288859_1520227

theorem selected_cut_52262 : selected 11 ⟨1520305, by decide⟩
    (prefixPartial 10 72215) = some ⟨10, 2, 0, 1520305, 72215, 2941, 1048576⟩ := by
  decide +kernel

theorem context_10_72215_1520305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72215 ⟨1520305, by decide⟩ :=
  accepted_of_selected 10 72215 ⟨1520305, by decide⟩ ⟨10, 2, 0, 1520305, 72215, 2941, 1048576⟩
    (by decide) selected_cut_52262

theorem unmarked_context_9_18053_1520306 : frontier 12 ⟨1520306, by decide⟩
    (prefixCache 9 18053) (prefixPartial 9 18053) = false := by
  decide +kernel

theorem node_context_9_18053_1520306 : EJMOriginalGlobalDAGData.nodes 12 ⟨1520306, by decide⟩ =
    .split (coordinate 9) (![⟨1520095, by decide⟩,⟨1468874, by decide⟩,⟨1520228, by decide⟩,⟨1520305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18053_1520306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18053 ⟨1520306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18053
    ⟨1520306, by decide⟩ (by decide) (![⟨1520095, by decide⟩,⟨1468874, by decide⟩,⟨1520228, by decide⟩,⟨1520305, by decide⟩]) unmarked_context_9_18053_1520306 node_context_9_18053_1520306
  intro a
  fin_cases a
  · exact context_10_72212_1520095
  · exact context_10_72213_1468874
  · exact context_10_72214_1520228
  · exact context_10_72215_1520305

theorem selected_cut_52263 : selected 12 ⟨1520394, by decide⟩
    (prefixPartial 9 18054) = some ⟨9, 2, 0, 1520394, 18054, 3765, 4194304⟩ := by
  decide +kernel

theorem context_9_18054_1520394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18054 ⟨1520394, by decide⟩ :=
  accepted_of_selected 9 18054 ⟨1520394, by decide⟩ ⟨9, 2, 0, 1520394, 18054, 3765, 4194304⟩
    (by decide) selected_cut_52263

theorem selected_cut_52264 : selected 12 ⟨1520453, by decide⟩
    (prefixPartial 9 18055) = some ⟨9, 2, 0, 1520453, 18055, 1429, 4194304⟩ := by
  decide +kernel

theorem context_9_18055_1520453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18055 ⟨1520453, by decide⟩ :=
  accepted_of_selected 9 18055 ⟨1520453, by decide⟩ ⟨9, 2, 0, 1520453, 18055, 1429, 4194304⟩
    (by decide) selected_cut_52264

theorem unmarked_context_8_4513_1520454 : frontier 13 ⟨1520454, by decide⟩
    (prefixCache 8 4513) (prefixPartial 8 4513) = false := by
  decide +kernel

theorem node_context_8_4513_1520454 : EJMOriginalGlobalDAGData.nodes 13 ⟨1520454, by decide⟩ =
    .split (coordinate 8) (![⟨1520013, by decide⟩,⟨1520306, by decide⟩,⟨1520394, by decide⟩,⟨1520453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4513_1520454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4513 ⟨1520454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4513
    ⟨1520454, by decide⟩ (by decide) (![⟨1520013, by decide⟩,⟨1520306, by decide⟩,⟨1520394, by decide⟩,⟨1520453, by decide⟩]) unmarked_context_8_4513_1520454 node_context_8_4513_1520454
  intro a
  fin_cases a
  · exact context_9_18052_1520013
  · exact context_9_18053_1520306
  · exact context_9_18054_1520394
  · exact context_9_18055_1520453

theorem selected_cut_52265 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72224) = some ⟨10, 1, 0, 1468246, 72224, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72224_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72224 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72224 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72224, 1, 1048576⟩
    (by decide) selected_cut_52265

theorem selected_cut_52266 : selected 10 ⟨1520517, by decide⟩
    (prefixPartial 11 288900) = some ⟨11, 2, 0, 1520517, 288900, 1697, 262144⟩ := by
  decide +kernel

theorem context_11_288900_1520517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288900 ⟨1520517, by decide⟩ :=
  accepted_of_selected 11 288900 ⟨1520517, by decide⟩ ⟨11, 2, 0, 1520517, 288900, 1697, 262144⟩
    (by decide) selected_cut_52266

theorem selected_cut_52267 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 288901) = some ⟨11, 1, 0, 1468419, 288901, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288901_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288901 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 288901 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 288901, 1, 262144⟩
    (by decide) selected_cut_52267

theorem selected_cut_52268 : selected 10 ⟨1520667, by decide⟩
    (prefixPartial 11 288902) = some ⟨11, 2, 0, 1520667, 288902, 2673, 262144⟩ := by
  decide +kernel

theorem context_11_288902_1520667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288902 ⟨1520667, by decide⟩ :=
  accepted_of_selected 11 288902 ⟨1520667, by decide⟩ ⟨11, 2, 0, 1520667, 288902, 2673, 262144⟩
    (by decide) selected_cut_52268

theorem selected_cut_52269 : selected 10 ⟨1520784, by decide⟩
    (prefixPartial 11 288903) = some ⟨11, 2, 0, 1520784, 288903, 3117, 262144⟩ := by
  decide +kernel

theorem context_11_288903_1520784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288903 ⟨1520784, by decide⟩ :=
  accepted_of_selected 11 288903 ⟨1520784, by decide⟩ ⟨11, 2, 0, 1520784, 288903, 3117, 262144⟩
    (by decide) selected_cut_52269

theorem unmarked_context_10_72225_1520785 : frontier 11 ⟨1520785, by decide⟩
    (prefixCache 10 72225) (prefixPartial 10 72225) = false := by
  decide +kernel

theorem node_context_10_72225_1520785 : EJMOriginalGlobalDAGData.nodes 11 ⟨1520785, by decide⟩ =
    .split (coordinate 10) (![⟨1520517, by decide⟩,⟨1468419, by decide⟩,⟨1520667, by decide⟩,⟨1520784, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72225_1520785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72225 ⟨1520785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72225
    ⟨1520785, by decide⟩ (by decide) (![⟨1520517, by decide⟩,⟨1468419, by decide⟩,⟨1520667, by decide⟩,⟨1520784, by decide⟩]) unmarked_context_10_72225_1520785 node_context_10_72225_1520785
  intro a
  fin_cases a
  · exact context_11_288900_1520517
  · exact context_11_288901_1468419
  · exact context_11_288902_1520667
  · exact context_11_288903_1520784

theorem selected_cut_52270 : selected 10 ⟨1520878, by decide⟩
    (prefixPartial 11 288904) = some ⟨11, 2, 0, 1520878, 288904, 2441, 262144⟩ := by
  decide +kernel

theorem context_11_288904_1520878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288904 ⟨1520878, by decide⟩ :=
  accepted_of_selected 11 288904 ⟨1520878, by decide⟩ ⟨11, 2, 0, 1520878, 288904, 2441, 262144⟩
    (by decide) selected_cut_52270

theorem selected_cut_52271 : selected 10 ⟨1520923, by decide⟩
    (prefixPartial 11 288905) = some ⟨11, 2, 0, 1520923, 288905, 1169, 262144⟩ := by
  decide +kernel

theorem context_11_288905_1520923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288905 ⟨1520923, by decide⟩ :=
  accepted_of_selected 11 288905 ⟨1520923, by decide⟩ ⟨11, 2, 0, 1520923, 288905, 1169, 262144⟩
    (by decide) selected_cut_52271

theorem selected_cut_52272 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 288906) = some ⟨11, 1, 0, 1468743, 288906, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288906_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288906 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 288906 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 288906, 1, 262144⟩
    (by decide) selected_cut_52272

theorem selected_cut_52273 : selected 10 ⟨1520968, by decide⟩
    (prefixPartial 11 288907) = some ⟨11, 2, 0, 1520968, 288907, 1161, 262144⟩ := by
  decide +kernel

theorem context_11_288907_1520968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288907 ⟨1520968, by decide⟩ :=
  accepted_of_selected 11 288907 ⟨1520968, by decide⟩ ⟨11, 2, 0, 1520968, 288907, 1161, 262144⟩
    (by decide) selected_cut_52273

theorem unmarked_context_10_72226_1520969 : frontier 11 ⟨1520969, by decide⟩
    (prefixCache 10 72226) (prefixPartial 10 72226) = false := by
  decide +kernel

theorem node_context_10_72226_1520969 : EJMOriginalGlobalDAGData.nodes 11 ⟨1520969, by decide⟩ =
    .split (coordinate 10) (![⟨1520878, by decide⟩,⟨1520923, by decide⟩,⟨1468743, by decide⟩,⟨1520968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72226_1520969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72226 ⟨1520969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72226
    ⟨1520969, by decide⟩ (by decide) (![⟨1520878, by decide⟩,⟨1520923, by decide⟩,⟨1468743, by decide⟩,⟨1520968, by decide⟩]) unmarked_context_10_72226_1520969 node_context_10_72226_1520969
  intro a
  fin_cases a
  · exact context_11_288904_1520878
  · exact context_11_288905_1520923
  · exact context_11_288906_1468743
  · exact context_11_288907_1520968

theorem selected_cut_52274 : selected 11 ⟨1521111, by decide⟩
    (prefixPartial 10 72227) = some ⟨10, 2, 0, 1521111, 72227, 3301, 1048576⟩ := by
  decide +kernel

theorem context_10_72227_1521111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72227 ⟨1521111, by decide⟩ :=
  accepted_of_selected 10 72227 ⟨1521111, by decide⟩ ⟨10, 2, 0, 1521111, 72227, 3301, 1048576⟩
    (by decide) selected_cut_52274

theorem unmarked_context_9_18056_1521112 : frontier 12 ⟨1521112, by decide⟩
    (prefixCache 9 18056) (prefixPartial 9 18056) = false := by
  decide +kernel

theorem node_context_9_18056_1521112 : EJMOriginalGlobalDAGData.nodes 12 ⟨1521112, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1520785, by decide⟩,⟨1520969, by decide⟩,⟨1521111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18056_1521112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18056 ⟨1521112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18056
    ⟨1521112, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1520785, by decide⟩,⟨1520969, by decide⟩,⟨1521111, by decide⟩]) unmarked_context_9_18056_1521112 node_context_9_18056_1521112
  intro a
  fin_cases a
  · exact context_10_72224_1468246
  · exact context_10_72225_1520785
  · exact context_10_72226_1520969
  · exact context_10_72227_1521111

theorem selected_cut_52275 : selected 11 ⟨1521202, by decide⟩
    (prefixPartial 10 72228) = some ⟨10, 2, 0, 1521202, 72228, 1309, 1048576⟩ := by
  decide +kernel

theorem context_10_72228_1521202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72228 ⟨1521202, by decide⟩ :=
  accepted_of_selected 10 72228 ⟨1521202, by decide⟩ ⟨10, 2, 0, 1521202, 72228, 1309, 1048576⟩
    (by decide) selected_cut_52275

theorem selected_cut_52276 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72229) = some ⟨10, 1, 0, 1468874, 72229, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72229_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72229 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72229 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72229, 1, 1048576⟩
    (by decide) selected_cut_52276

theorem selected_cut_52277 : selected 11 ⟨1521349, by decide⟩
    (prefixPartial 10 72230) = some ⟨10, 2, 0, 1521349, 72230, 2549, 1048576⟩ := by
  decide +kernel

theorem context_10_72230_1521349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72230 ⟨1521349, by decide⟩ :=
  accepted_of_selected 10 72230 ⟨1521349, by decide⟩ ⟨10, 2, 0, 1521349, 72230, 2549, 1048576⟩
    (by decide) selected_cut_52277

theorem selected_cut_52278 : selected 11 ⟨1521420, by decide⟩
    (prefixPartial 10 72231) = some ⟨10, 2, 0, 1521420, 72231, 1053, 1048576⟩ := by
  decide +kernel

theorem context_10_72231_1521420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72231 ⟨1521420, by decide⟩ :=
  accepted_of_selected 10 72231 ⟨1521420, by decide⟩ ⟨10, 2, 0, 1521420, 72231, 1053, 1048576⟩
    (by decide) selected_cut_52278

theorem unmarked_context_9_18057_1521421 : frontier 12 ⟨1521421, by decide⟩
    (prefixCache 9 18057) (prefixPartial 9 18057) = false := by
  decide +kernel

theorem node_context_9_18057_1521421 : EJMOriginalGlobalDAGData.nodes 12 ⟨1521421, by decide⟩ =
    .split (coordinate 9) (![⟨1521202, by decide⟩,⟨1468874, by decide⟩,⟨1521349, by decide⟩,⟨1521420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18057_1521421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18057 ⟨1521421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18057
    ⟨1521421, by decide⟩ (by decide) (![⟨1521202, by decide⟩,⟨1468874, by decide⟩,⟨1521349, by decide⟩,⟨1521420, by decide⟩]) unmarked_context_9_18057_1521421 node_context_9_18057_1521421
  intro a
  fin_cases a
  · exact context_10_72228_1521202
  · exact context_10_72229_1468874
  · exact context_10_72230_1521349
  · exact context_10_72231_1521420

theorem selected_cut_52279 : selected 12 ⟨1521510, by decide⟩
    (prefixPartial 9 18058) = some ⟨9, 2, 0, 1521510, 18058, 921, 4194304⟩ := by
  decide +kernel

theorem context_9_18058_1521510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18058 ⟨1521510, by decide⟩ :=
  accepted_of_selected 9 18058 ⟨1521510, by decide⟩ ⟨9, 2, 0, 1521510, 18058, 921, 4194304⟩
    (by decide) selected_cut_52279

theorem selected_cut_52280 : selected 12 ⟨1521518, by decide⟩
    (prefixPartial 9 18059) = some ⟨9, 2, 0, 1521518, 18059, 173, 4194304⟩ := by
  decide +kernel

theorem context_9_18059_1521518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18059 ⟨1521518, by decide⟩ :=
  accepted_of_selected 9 18059 ⟨1521518, by decide⟩ ⟨9, 2, 0, 1521518, 18059, 173, 4194304⟩
    (by decide) selected_cut_52280

theorem unmarked_context_8_4514_1521519 : frontier 13 ⟨1521519, by decide⟩
    (prefixCache 8 4514) (prefixPartial 8 4514) = false := by
  decide +kernel

theorem node_context_8_4514_1521519 : EJMOriginalGlobalDAGData.nodes 13 ⟨1521519, by decide⟩ =
    .split (coordinate 8) (![⟨1521112, by decide⟩,⟨1521421, by decide⟩,⟨1521510, by decide⟩,⟨1521518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4514_1521519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4514 ⟨1521519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4514
    ⟨1521519, by decide⟩ (by decide) (![⟨1521112, by decide⟩,⟨1521421, by decide⟩,⟨1521510, by decide⟩,⟨1521518, by decide⟩]) unmarked_context_8_4514_1521519 node_context_8_4514_1521519
  intro a
  fin_cases a
  · exact context_9_18056_1521112
  · exact context_9_18057_1521421
  · exact context_9_18058_1521510
  · exact context_9_18059_1521518

theorem selected_cut_52281 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72240) = some ⟨10, 1, 0, 1468246, 72240, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72240_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72240 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72240 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72240, 1, 1048576⟩
    (by decide) selected_cut_52281

theorem selected_cut_52282 : selected 10 ⟨1521610, by decide⟩
    (prefixPartial 11 288964) = some ⟨11, 2, 0, 1521610, 288964, 3125, 262144⟩ := by
  decide +kernel

theorem context_11_288964_1521610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288964 ⟨1521610, by decide⟩ :=
  accepted_of_selected 11 288964 ⟨1521610, by decide⟩ ⟨11, 2, 0, 1521610, 288964, 3125, 262144⟩
    (by decide) selected_cut_52282

theorem selected_cut_52283 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 288965) = some ⟨11, 1, 0, 1468419, 288965, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288965_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288965 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 288965 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 288965, 1, 262144⟩
    (by decide) selected_cut_52283

theorem selected_cut_52284 : selected 10 ⟨1521713, by decide⟩
    (prefixPartial 11 288966) = some ⟨11, 2, 0, 1521713, 288966, 3261, 262144⟩ := by
  decide +kernel

theorem context_11_288966_1521713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288966 ⟨1521713, by decide⟩ :=
  accepted_of_selected 11 288966 ⟨1521713, by decide⟩ ⟨11, 2, 0, 1521713, 288966, 3261, 262144⟩
    (by decide) selected_cut_52284

theorem selected_cut_52285 : selected 10 ⟨1521813, by decide⟩
    (prefixPartial 11 288967) = some ⟨11, 2, 0, 1521813, 288967, 3113, 262144⟩ := by
  decide +kernel

theorem context_11_288967_1521813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288967 ⟨1521813, by decide⟩ :=
  accepted_of_selected 11 288967 ⟨1521813, by decide⟩ ⟨11, 2, 0, 1521813, 288967, 3113, 262144⟩
    (by decide) selected_cut_52285

theorem unmarked_context_10_72241_1521814 : frontier 11 ⟨1521814, by decide⟩
    (prefixCache 10 72241) (prefixPartial 10 72241) = false := by
  decide +kernel

theorem node_context_10_72241_1521814 : EJMOriginalGlobalDAGData.nodes 11 ⟨1521814, by decide⟩ =
    .split (coordinate 10) (![⟨1521610, by decide⟩,⟨1468419, by decide⟩,⟨1521713, by decide⟩,⟨1521813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72241_1521814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72241 ⟨1521814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72241
    ⟨1521814, by decide⟩ (by decide) (![⟨1521610, by decide⟩,⟨1468419, by decide⟩,⟨1521713, by decide⟩,⟨1521813, by decide⟩]) unmarked_context_10_72241_1521814 node_context_10_72241_1521814
  intro a
  fin_cases a
  · exact context_11_288964_1521610
  · exact context_11_288965_1468419
  · exact context_11_288966_1521713
  · exact context_11_288967_1521813

theorem selected_cut_52286 : selected 10 ⟨1521893, by decide⟩
    (prefixPartial 11 288968) = some ⟨11, 2, 0, 1521893, 288968, 2821, 262144⟩ := by
  decide +kernel

theorem context_11_288968_1521893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288968 ⟨1521893, by decide⟩ :=
  accepted_of_selected 11 288968 ⟨1521893, by decide⟩ ⟨11, 2, 0, 1521893, 288968, 2821, 262144⟩
    (by decide) selected_cut_52286

theorem selected_cut_52287 : selected 10 ⟨1521925, by decide⟩
    (prefixPartial 11 288969) = some ⟨11, 2, 0, 1521925, 288969, 1305, 262144⟩ := by
  decide +kernel

theorem context_11_288969_1521925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288969 ⟨1521925, by decide⟩ :=
  accepted_of_selected 11 288969 ⟨1521925, by decide⟩ ⟨11, 2, 0, 1521925, 288969, 1305, 262144⟩
    (by decide) selected_cut_52287

theorem selected_cut_52288 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 288970) = some ⟨11, 1, 0, 1468743, 288970, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288970_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288970 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 288970 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 288970, 1, 262144⟩
    (by decide) selected_cut_52288

theorem selected_cut_52289 : selected 10 ⟨1521961, by decide⟩
    (prefixPartial 11 288971) = some ⟨11, 2, 0, 1521961, 288971, 1421, 262144⟩ := by
  decide +kernel

theorem context_11_288971_1521961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288971 ⟨1521961, by decide⟩ :=
  accepted_of_selected 11 288971 ⟨1521961, by decide⟩ ⟨11, 2, 0, 1521961, 288971, 1421, 262144⟩
    (by decide) selected_cut_52289

theorem unmarked_context_10_72242_1521962 : frontier 11 ⟨1521962, by decide⟩
    (prefixCache 10 72242) (prefixPartial 10 72242) = false := by
  decide +kernel

theorem node_context_10_72242_1521962 : EJMOriginalGlobalDAGData.nodes 11 ⟨1521962, by decide⟩ =
    .split (coordinate 10) (![⟨1521893, by decide⟩,⟨1521925, by decide⟩,⟨1468743, by decide⟩,⟨1521961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72242_1521962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72242 ⟨1521962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72242
    ⟨1521962, by decide⟩ (by decide) (![⟨1521893, by decide⟩,⟨1521925, by decide⟩,⟨1468743, by decide⟩,⟨1521961, by decide⟩]) unmarked_context_10_72242_1521962 node_context_10_72242_1521962
  intro a
  fin_cases a
  · exact context_11_288968_1521893
  · exact context_11_288969_1521925
  · exact context_11_288970_1468743
  · exact context_11_288971_1521961

theorem selected_cut_52290 : selected 10 ⟨1522030, by decide⟩
    (prefixPartial 11 288972) = some ⟨11, 2, 0, 1522030, 288972, 2465, 262144⟩ := by
  decide +kernel

theorem context_11_288972_1522030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288972 ⟨1522030, by decide⟩ :=
  accepted_of_selected 11 288972 ⟨1522030, by decide⟩ ⟨11, 2, 0, 1522030, 288972, 2465, 262144⟩
    (by decide) selected_cut_52290

theorem selected_cut_52291 : selected 10 ⟨1522085, by decide⟩
    (prefixPartial 11 288973) = some ⟨11, 2, 0, 1522085, 288973, 2149, 262144⟩ := by
  decide +kernel

theorem context_11_288973_1522085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288973 ⟨1522085, by decide⟩ :=
  accepted_of_selected 11 288973 ⟨1522085, by decide⟩ ⟨11, 2, 0, 1522085, 288973, 2149, 262144⟩
    (by decide) selected_cut_52291

theorem selected_cut_52292 : selected 10 ⟨1522117, by decide⟩
    (prefixPartial 11 288974) = some ⟨11, 2, 0, 1522117, 288974, 1121, 262144⟩ := by
  decide +kernel

theorem context_11_288974_1522117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288974 ⟨1522117, by decide⟩ :=
  accepted_of_selected 11 288974 ⟨1522117, by decide⟩ ⟨11, 2, 0, 1522117, 288974, 1121, 262144⟩
    (by decide) selected_cut_52292

theorem selected_cut_52293 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 288975) = some ⟨11, 1, 0, 1470044, 288975, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288975_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288975 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 288975 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 288975, 1, 262144⟩
    (by decide) selected_cut_52293

theorem unmarked_context_10_72243_1522118 : frontier 11 ⟨1522118, by decide⟩
    (prefixCache 10 72243) (prefixPartial 10 72243) = false := by
  decide +kernel

theorem node_context_10_72243_1522118 : EJMOriginalGlobalDAGData.nodes 11 ⟨1522118, by decide⟩ =
    .split (coordinate 10) (![⟨1522030, by decide⟩,⟨1522085, by decide⟩,⟨1522117, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72243_1522118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72243 ⟨1522118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72243
    ⟨1522118, by decide⟩ (by decide) (![⟨1522030, by decide⟩,⟨1522085, by decide⟩,⟨1522117, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_72243_1522118 node_context_10_72243_1522118
  intro a
  fin_cases a
  · exact context_11_288972_1522030
  · exact context_11_288973_1522085
  · exact context_11_288974_1522117
  · exact context_11_288975_1470044

theorem unmarked_context_9_18060_1522119 : frontier 12 ⟨1522119, by decide⟩
    (prefixCache 9 18060) (prefixPartial 9 18060) = false := by
  decide +kernel

theorem node_context_9_18060_1522119 : EJMOriginalGlobalDAGData.nodes 12 ⟨1522119, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1521814, by decide⟩,⟨1521962, by decide⟩,⟨1522118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18060_1522119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18060 ⟨1522119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18060
    ⟨1522119, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1521814, by decide⟩,⟨1521962, by decide⟩,⟨1522118, by decide⟩]) unmarked_context_9_18060_1522119 node_context_9_18060_1522119
  intro a
  fin_cases a
  · exact context_10_72240_1468246
  · exact context_10_72241_1521814
  · exact context_10_72242_1521962
  · exact context_10_72243_1522118

theorem selected_cut_52294 : selected 11 ⟨1522174, by decide⟩
    (prefixPartial 10 72244) = some ⟨10, 2, 0, 1522174, 72244, 2349, 1048576⟩ := by
  decide +kernel

theorem context_10_72244_1522174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72244 ⟨1522174, by decide⟩ :=
  accepted_of_selected 10 72244 ⟨1522174, by decide⟩ ⟨10, 2, 0, 1522174, 72244, 2349, 1048576⟩
    (by decide) selected_cut_52294

theorem selected_cut_52295 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72245) = some ⟨10, 1, 0, 1468874, 72245, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72245_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72245 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72245 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72245, 1, 1048576⟩
    (by decide) selected_cut_52295

theorem selected_cut_52296 : selected 10 ⟨1522211, by decide⟩
    (prefixPartial 11 288984) = some ⟨11, 2, 0, 1522211, 288984, 1669, 262144⟩ := by
  decide +kernel

theorem context_11_288984_1522211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288984 ⟨1522211, by decide⟩ :=
  accepted_of_selected 11 288984 ⟨1522211, by decide⟩ ⟨11, 2, 0, 1522211, 288984, 1669, 262144⟩
    (by decide) selected_cut_52296

theorem selected_cut_52297 : selected 10 ⟨1522253, by decide⟩
    (prefixPartial 11 288985) = some ⟨11, 2, 0, 1522253, 288985, 1465, 262144⟩ := by
  decide +kernel

theorem context_11_288985_1522253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288985 ⟨1522253, by decide⟩ :=
  accepted_of_selected 11 288985 ⟨1522253, by decide⟩ ⟨11, 2, 0, 1522253, 288985, 1465, 262144⟩
    (by decide) selected_cut_52297

theorem selected_cut_52298 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 288986) = some ⟨11, 1, 0, 1468743, 288986, 1, 262144⟩ := by
  decide +kernel

theorem context_11_288986_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288986 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 288986 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 288986, 1, 262144⟩
    (by decide) selected_cut_52298

theorem selected_cut_52299 : selected 10 ⟨1522281, by decide⟩
    (prefixPartial 11 288987) = some ⟨11, 2, 0, 1522281, 288987, 1329, 262144⟩ := by
  decide +kernel

theorem context_11_288987_1522281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288987 ⟨1522281, by decide⟩ :=
  accepted_of_selected 11 288987 ⟨1522281, by decide⟩ ⟨11, 2, 0, 1522281, 288987, 1329, 262144⟩
    (by decide) selected_cut_52299

theorem unmarked_context_10_72246_1522282 : frontier 11 ⟨1522282, by decide⟩
    (prefixCache 10 72246) (prefixPartial 10 72246) = false := by
  decide +kernel

theorem node_context_10_72246_1522282 : EJMOriginalGlobalDAGData.nodes 11 ⟨1522282, by decide⟩ =
    .split (coordinate 10) (![⟨1522211, by decide⟩,⟨1522253, by decide⟩,⟨1468743, by decide⟩,⟨1522281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72246_1522282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72246 ⟨1522282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72246
    ⟨1522282, by decide⟩ (by decide) (![⟨1522211, by decide⟩,⟨1522253, by decide⟩,⟨1468743, by decide⟩,⟨1522281, by decide⟩]) unmarked_context_10_72246_1522282 node_context_10_72246_1522282
  intro a
  fin_cases a
  · exact context_11_288984_1522211
  · exact context_11_288985_1522253
  · exact context_11_288986_1468743
  · exact context_11_288987_1522281

theorem selected_cut_52300 : selected 11 ⟨1522364, by decide⟩
    (prefixPartial 10 72247) = some ⟨10, 2, 0, 1522364, 72247, 2945, 1048576⟩ := by
  decide +kernel

theorem context_10_72247_1522364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72247 ⟨1522364, by decide⟩ :=
  accepted_of_selected 10 72247 ⟨1522364, by decide⟩ ⟨10, 2, 0, 1522364, 72247, 2945, 1048576⟩
    (by decide) selected_cut_52300

theorem unmarked_context_9_18061_1522365 : frontier 12 ⟨1522365, by decide⟩
    (prefixCache 9 18061) (prefixPartial 9 18061) = false := by
  decide +kernel

theorem node_context_9_18061_1522365 : EJMOriginalGlobalDAGData.nodes 12 ⟨1522365, by decide⟩ =
    .split (coordinate 9) (![⟨1522174, by decide⟩,⟨1468874, by decide⟩,⟨1522282, by decide⟩,⟨1522364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18061_1522365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18061 ⟨1522365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18061
    ⟨1522365, by decide⟩ (by decide) (![⟨1522174, by decide⟩,⟨1468874, by decide⟩,⟨1522282, by decide⟩,⟨1522364, by decide⟩]) unmarked_context_9_18061_1522365 node_context_9_18061_1522365
  intro a
  fin_cases a
  · exact context_10_72244_1522174
  · exact context_10_72245_1468874
  · exact context_10_72246_1522282
  · exact context_10_72247_1522364

theorem selected_cut_52301 : selected 11 ⟨1522393, by decide⟩
    (prefixPartial 10 72248) = some ⟨10, 2, 0, 1522393, 72248, 929, 1048576⟩ := by
  decide +kernel

theorem context_10_72248_1522393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72248 ⟨1522393, by decide⟩ :=
  accepted_of_selected 10 72248 ⟨1522393, by decide⟩ ⟨10, 2, 0, 1522393, 72248, 929, 1048576⟩
    (by decide) selected_cut_52301

theorem selected_cut_52302 : selected 11 ⟨1522452, by decide⟩
    (prefixPartial 10 72249) = some ⟨10, 2, 0, 1522452, 72249, 2189, 1048576⟩ := by
  decide +kernel

theorem context_10_72249_1522452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72249 ⟨1522452, by decide⟩ :=
  accepted_of_selected 10 72249 ⟨1522452, by decide⟩ ⟨10, 2, 0, 1522452, 72249, 2189, 1048576⟩
    (by decide) selected_cut_52302

theorem selected_cut_52303 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 72250) = some ⟨10, 1, 0, 1469103, 72250, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72250_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72250 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 72250 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 72250, 1, 1048576⟩
    (by decide) selected_cut_52303

theorem selected_cut_52304 : selected 11 ⟨1522492, by decide⟩
    (prefixPartial 10 72251) = some ⟨10, 2, 0, 1522492, 72251, 1485, 1048576⟩ := by
  decide +kernel

theorem context_10_72251_1522492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72251 ⟨1522492, by decide⟩ :=
  accepted_of_selected 10 72251 ⟨1522492, by decide⟩ ⟨10, 2, 0, 1522492, 72251, 1485, 1048576⟩
    (by decide) selected_cut_52304

theorem unmarked_context_9_18062_1522493 : frontier 12 ⟨1522493, by decide⟩
    (prefixCache 9 18062) (prefixPartial 9 18062) = false := by
  decide +kernel

theorem node_context_9_18062_1522493 : EJMOriginalGlobalDAGData.nodes 12 ⟨1522493, by decide⟩ =
    .split (coordinate 9) (![⟨1522393, by decide⟩,⟨1522452, by decide⟩,⟨1469103, by decide⟩,⟨1522492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18062_1522493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18062 ⟨1522493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18062
    ⟨1522493, by decide⟩ (by decide) (![⟨1522393, by decide⟩,⟨1522452, by decide⟩,⟨1469103, by decide⟩,⟨1522492, by decide⟩]) unmarked_context_9_18062_1522493 node_context_9_18062_1522493
  intro a
  fin_cases a
  · exact context_10_72248_1522393
  · exact context_10_72249_1522452
  · exact context_10_72250_1469103
  · exact context_10_72251_1522492

theorem selected_cut_52305 : selected 12 ⟨1522546, by decide⟩
    (prefixPartial 9 18063) = some ⟨9, 2, 0, 1522546, 18063, 1397, 4194304⟩ := by
  decide +kernel

theorem context_9_18063_1522546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18063 ⟨1522546, by decide⟩ :=
  accepted_of_selected 9 18063 ⟨1522546, by decide⟩ ⟨9, 2, 0, 1522546, 18063, 1397, 4194304⟩
    (by decide) selected_cut_52305

theorem unmarked_context_8_4515_1522547 : frontier 13 ⟨1522547, by decide⟩
    (prefixCache 8 4515) (prefixPartial 8 4515) = false := by
  decide +kernel

theorem node_context_8_4515_1522547 : EJMOriginalGlobalDAGData.nodes 13 ⟨1522547, by decide⟩ =
    .split (coordinate 8) (![⟨1522119, by decide⟩,⟨1522365, by decide⟩,⟨1522493, by decide⟩,⟨1522546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4515_1522547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4515 ⟨1522547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4515
    ⟨1522547, by decide⟩ (by decide) (![⟨1522119, by decide⟩,⟨1522365, by decide⟩,⟨1522493, by decide⟩,⟨1522546, by decide⟩]) unmarked_context_8_4515_1522547 node_context_8_4515_1522547
  intro a
  fin_cases a
  · exact context_9_18060_1522119
  · exact context_9_18061_1522365
  · exact context_9_18062_1522493
  · exact context_9_18063_1522546

theorem unmarked_context_7_1128_1522548 : frontier 14 ⟨1522548, by decide⟩
    (prefixCache 7 1128) (prefixPartial 7 1128) = false := by
  decide +kernel

theorem node_context_7_1128_1522548 : EJMOriginalGlobalDAGData.nodes 14 ⟨1522548, by decide⟩ =
    .split (coordinate 7) (![⟨1519445, by decide⟩,⟨1520454, by decide⟩,⟨1521519, by decide⟩,⟨1522547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1128_1522548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1128 ⟨1522548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1128
    ⟨1522548, by decide⟩ (by decide) (![⟨1519445, by decide⟩,⟨1520454, by decide⟩,⟨1521519, by decide⟩,⟨1522547, by decide⟩]) unmarked_context_7_1128_1522548 node_context_7_1128_1522548
  intro a
  fin_cases a
  · exact context_8_4512_1519445
  · exact context_8_4513_1520454
  · exact context_8_4514_1521519
  · exact context_8_4515_1522547

theorem selected_cut_52306 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72256) = some ⟨10, 1, 0, 1468246, 72256, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72256_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72256 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72256 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72256, 1, 1048576⟩
    (by decide) selected_cut_52306

theorem selected_cut_52307 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 289028) = some ⟨11, 1, 0, 815620, 289028, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289028_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289028 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 289028 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 289028, 1, 262144⟩
    (by decide) selected_cut_52307

theorem selected_cut_52308 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 289029) = some ⟨11, 1, 0, 1468419, 289029, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289029_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289029 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 289029 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 289029, 1, 262144⟩
    (by decide) selected_cut_52308

theorem selected_cut_52309 : selected 10 ⟨1522643, by decide⟩
    (prefixPartial 11 289030) = some ⟨11, 2, 0, 1522643, 289030, 2737, 262144⟩ := by
  decide +kernel

theorem context_11_289030_1522643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289030 ⟨1522643, by decide⟩ :=
  accepted_of_selected 11 289030 ⟨1522643, by decide⟩ ⟨11, 2, 0, 1522643, 289030, 2737, 262144⟩
    (by decide) selected_cut_52309

theorem selected_cut_52310 : selected 10 ⟨1522713, by decide⟩
    (prefixPartial 11 289031) = some ⟨11, 2, 0, 1522713, 289031, 2573, 262144⟩ := by
  decide +kernel

theorem context_11_289031_1522713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289031 ⟨1522713, by decide⟩ :=
  accepted_of_selected 11 289031 ⟨1522713, by decide⟩ ⟨11, 2, 0, 1522713, 289031, 2573, 262144⟩
    (by decide) selected_cut_52310

theorem unmarked_context_10_72257_1522714 : frontier 11 ⟨1522714, by decide⟩
    (prefixCache 10 72257) (prefixPartial 10 72257) = false := by
  decide +kernel

theorem node_context_10_72257_1522714 : EJMOriginalGlobalDAGData.nodes 11 ⟨1522714, by decide⟩ =
    .split (coordinate 10) (![⟨815620, by decide⟩,⟨1468419, by decide⟩,⟨1522643, by decide⟩,⟨1522713, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72257_1522714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72257 ⟨1522714, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72257
    ⟨1522714, by decide⟩ (by decide) (![⟨815620, by decide⟩,⟨1468419, by decide⟩,⟨1522643, by decide⟩,⟨1522713, by decide⟩]) unmarked_context_10_72257_1522714 node_context_10_72257_1522714
  intro a
  fin_cases a
  · exact context_11_289028_815620
  · exact context_11_289029_1468419
  · exact context_11_289030_1522643
  · exact context_11_289031_1522713

theorem selected_cut_52311 : selected 10 ⟨1522793, by decide⟩
    (prefixPartial 11 289032) = some ⟨11, 2, 0, 1522793, 289032, 2429, 262144⟩ := by
  decide +kernel

theorem context_11_289032_1522793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289032 ⟨1522793, by decide⟩ :=
  accepted_of_selected 11 289032 ⟨1522793, by decide⟩ ⟨11, 2, 0, 1522793, 289032, 2429, 262144⟩
    (by decide) selected_cut_52311

theorem selected_cut_52312 : selected 10 ⟨1522821, by decide⟩
    (prefixPartial 11 289033) = some ⟨11, 2, 0, 1522821, 289033, 1057, 262144⟩ := by
  decide +kernel

theorem context_11_289033_1522821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289033 ⟨1522821, by decide⟩ :=
  accepted_of_selected 11 289033 ⟨1522821, by decide⟩ ⟨11, 2, 0, 1522821, 289033, 1057, 262144⟩
    (by decide) selected_cut_52312

theorem selected_cut_52313 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 289034) = some ⟨11, 1, 0, 1468743, 289034, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289034_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289034 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 289034 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 289034, 1, 262144⟩
    (by decide) selected_cut_52313

theorem selected_cut_52314 : selected 10 ⟨1522857, by decide⟩
    (prefixPartial 11 289035) = some ⟨11, 2, 0, 1522857, 289035, 1217, 262144⟩ := by
  decide +kernel

theorem context_11_289035_1522857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289035 ⟨1522857, by decide⟩ :=
  accepted_of_selected 11 289035 ⟨1522857, by decide⟩ ⟨11, 2, 0, 1522857, 289035, 1217, 262144⟩
    (by decide) selected_cut_52314

theorem unmarked_context_10_72258_1522858 : frontier 11 ⟨1522858, by decide⟩
    (prefixCache 10 72258) (prefixPartial 10 72258) = false := by
  decide +kernel

theorem node_context_10_72258_1522858 : EJMOriginalGlobalDAGData.nodes 11 ⟨1522858, by decide⟩ =
    .split (coordinate 10) (![⟨1522793, by decide⟩,⟨1522821, by decide⟩,⟨1468743, by decide⟩,⟨1522857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72258_1522858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72258 ⟨1522858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72258
    ⟨1522858, by decide⟩ (by decide) (![⟨1522793, by decide⟩,⟨1522821, by decide⟩,⟨1468743, by decide⟩,⟨1522857, by decide⟩]) unmarked_context_10_72258_1522858 node_context_10_72258_1522858
  intro a
  fin_cases a
  · exact context_11_289032_1522793
  · exact context_11_289033_1522821
  · exact context_11_289034_1468743
  · exact context_11_289035_1522857

theorem selected_cut_52315 : selected 10 ⟨1522882, by decide⟩
    (prefixPartial 11 289036) = some ⟨11, 2, 0, 1522882, 289036, 997, 262144⟩ := by
  decide +kernel

theorem context_11_289036_1522882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289036 ⟨1522882, by decide⟩ :=
  accepted_of_selected 11 289036 ⟨1522882, by decide⟩ ⟨11, 2, 0, 1522882, 289036, 997, 262144⟩
    (by decide) selected_cut_52315

theorem selected_cut_52316 : selected 10 ⟨1522927, by decide⟩
    (prefixPartial 11 289037) = some ⟨11, 2, 0, 1522927, 289037, 1857, 262144⟩ := by
  decide +kernel

theorem context_11_289037_1522927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289037 ⟨1522927, by decide⟩ :=
  accepted_of_selected 11 289037 ⟨1522927, by decide⟩ ⟨11, 2, 0, 1522927, 289037, 1857, 262144⟩
    (by decide) selected_cut_52316

theorem selected_cut_52317 : selected 10 ⟨1522977, by decide⟩
    (prefixPartial 11 289038) = some ⟨11, 2, 0, 1522977, 289038, 2021, 262144⟩ := by
  decide +kernel

theorem context_11_289038_1522977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289038 ⟨1522977, by decide⟩ :=
  accepted_of_selected 11 289038 ⟨1522977, by decide⟩ ⟨11, 2, 0, 1522977, 289038, 2021, 262144⟩
    (by decide) selected_cut_52317

theorem selected_cut_52318 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 289039) = some ⟨11, 1, 0, 1470044, 289039, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289039_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289039 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 289039 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 289039, 1, 262144⟩
    (by decide) selected_cut_52318

theorem unmarked_context_10_72259_1522978 : frontier 11 ⟨1522978, by decide⟩
    (prefixCache 10 72259) (prefixPartial 10 72259) = false := by
  decide +kernel

theorem node_context_10_72259_1522978 : EJMOriginalGlobalDAGData.nodes 11 ⟨1522978, by decide⟩ =
    .split (coordinate 10) (![⟨1522882, by decide⟩,⟨1522927, by decide⟩,⟨1522977, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72259_1522978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72259 ⟨1522978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72259
    ⟨1522978, by decide⟩ (by decide) (![⟨1522882, by decide⟩,⟨1522927, by decide⟩,⟨1522977, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_72259_1522978 node_context_10_72259_1522978
  intro a
  fin_cases a
  · exact context_11_289036_1522882
  · exact context_11_289037_1522927
  · exact context_11_289038_1522977
  · exact context_11_289039_1470044

theorem unmarked_context_9_18064_1522979 : frontier 12 ⟨1522979, by decide⟩
    (prefixCache 9 18064) (prefixPartial 9 18064) = false := by
  decide +kernel

theorem node_context_9_18064_1522979 : EJMOriginalGlobalDAGData.nodes 12 ⟨1522979, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1522714, by decide⟩,⟨1522858, by decide⟩,⟨1522978, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18064_1522979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18064 ⟨1522979, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18064
    ⟨1522979, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1522714, by decide⟩,⟨1522858, by decide⟩,⟨1522978, by decide⟩]) unmarked_context_9_18064_1522979 node_context_9_18064_1522979
  intro a
  fin_cases a
  · exact context_10_72256_1468246
  · exact context_10_72257_1522714
  · exact context_10_72258_1522858
  · exact context_10_72259_1522978

theorem selected_cut_52319 : selected 11 ⟨1523053, by decide⟩
    (prefixPartial 10 72260) = some ⟨10, 2, 0, 1523053, 72260, 2825, 1048576⟩ := by
  decide +kernel

theorem context_10_72260_1523053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72260 ⟨1523053, by decide⟩ :=
  accepted_of_selected 10 72260 ⟨1523053, by decide⟩ ⟨10, 2, 0, 1523053, 72260, 2825, 1048576⟩
    (by decide) selected_cut_52319

theorem selected_cut_52320 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72261) = some ⟨10, 1, 0, 1468874, 72261, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72261_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72261 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72261 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72261, 1, 1048576⟩
    (by decide) selected_cut_52320

theorem selected_cut_52321 : selected 11 ⟨1523163, by decide⟩
    (prefixPartial 10 72262) = some ⟨10, 2, 0, 1523163, 72262, 3585, 1048576⟩ := by
  decide +kernel

theorem context_10_72262_1523163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72262 ⟨1523163, by decide⟩ :=
  accepted_of_selected 10 72262 ⟨1523163, by decide⟩ ⟨10, 2, 0, 1523163, 72262, 3585, 1048576⟩
    (by decide) selected_cut_52321

theorem selected_cut_52322 : selected 11 ⟨1523235, by decide⟩
    (prefixPartial 10 72263) = some ⟨10, 2, 0, 1523235, 72263, 3185, 1048576⟩ := by
  decide +kernel

theorem context_10_72263_1523235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72263 ⟨1523235, by decide⟩ :=
  accepted_of_selected 10 72263 ⟨1523235, by decide⟩ ⟨10, 2, 0, 1523235, 72263, 3185, 1048576⟩
    (by decide) selected_cut_52322

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
