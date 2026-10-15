/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover313
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_30148 : selected 9 ⟨760896, by decide⟩
    (prefixPartial 12 94042) = some ⟨12, 2, 0, 760896, 94042, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_94042_760896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94042 ⟨760896, by decide⟩ :=
  accepted_of_selected 12 94042 ⟨760896, by decide⟩ ⟨12, 2, 0, 760896, 94042, 3097, 65536⟩
    (by decide) selected_cut_30148

theorem selected_cut_30149 : selected 9 ⟨760941, by decide⟩
    (prefixPartial 12 94043) = some ⟨12, 2, 0, 760941, 94043, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_94043_760941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94043 ⟨760941, by decide⟩ :=
  accepted_of_selected 12 94043 ⟨760941, by decide⟩ ⟨12, 2, 0, 760941, 94043, 3145, 65536⟩
    (by decide) selected_cut_30149

theorem unmarked_context_11_23510_760942 : frontier 10 ⟨760942, by decide⟩
    (prefixCache 11 23510) (prefixPartial 11 23510) = false := by
  decide +kernel

theorem node_context_11_23510_760942 : EJMOriginalGlobalDAGData.nodes 10 ⟨760942, by decide⟩ =
    .split (coordinate 11) (![⟨760856, by decide⟩,⟨642341, by decide⟩,⟨760896, by decide⟩,⟨760941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23510_760942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23510 ⟨760942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23510
    ⟨760942, by decide⟩ (by decide) (![⟨760856, by decide⟩,⟨642341, by decide⟩,⟨760896, by decide⟩,⟨760941, by decide⟩]) unmarked_context_11_23510_760942 node_context_11_23510_760942
  intro a
  fin_cases a
  · exact context_12_94040_760856
  · exact context_12_94041_642341
  · exact context_12_94042_760896
  · exact context_12_94043_760941

theorem selected_cut_30150 : selected 9 ⟨760979, by decide⟩
    (prefixPartial 12 94044) = some ⟨12, 2, 0, 760979, 94044, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_94044_760979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94044 ⟨760979, by decide⟩ :=
  accepted_of_selected 12 94044 ⟨760979, by decide⟩ ⟨12, 2, 0, 760979, 94044, 2533, 65536⟩
    (by decide) selected_cut_30150

theorem selected_cut_30151 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 94045) = some ⟨12, 1, 0, 642341, 94045, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94045_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94045 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 94045 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 94045, 1, 65536⟩
    (by decide) selected_cut_30151

theorem selected_cut_30152 : selected 9 ⟨761020, by decide⟩
    (prefixPartial 12 94046) = some ⟨12, 2, 0, 761020, 94046, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_94046_761020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94046 ⟨761020, by decide⟩ :=
  accepted_of_selected 12 94046 ⟨761020, by decide⟩ ⟨12, 2, 0, 761020, 94046, 2505, 65536⟩
    (by decide) selected_cut_30152

theorem selected_cut_30153 : selected 9 ⟨757807, by decide⟩
    (prefixPartial 12 94047) = some ⟨12, 1, 0, 757807, 94047, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94047_757807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94047 ⟨757807, by decide⟩ :=
  accepted_of_selected 12 94047 ⟨757807, by decide⟩ ⟨12, 1, 0, 757807, 94047, 1, 65536⟩
    (by decide) selected_cut_30153

theorem unmarked_context_11_23511_761021 : frontier 10 ⟨761021, by decide⟩
    (prefixCache 11 23511) (prefixPartial 11 23511) = false := by
  decide +kernel

theorem node_context_11_23511_761021 : EJMOriginalGlobalDAGData.nodes 10 ⟨761021, by decide⟩ =
    .split (coordinate 11) (![⟨760979, by decide⟩,⟨642341, by decide⟩,⟨761020, by decide⟩,⟨757807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23511_761021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23511 ⟨761021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23511
    ⟨761021, by decide⟩ (by decide) (![⟨760979, by decide⟩,⟨642341, by decide⟩,⟨761020, by decide⟩,⟨757807, by decide⟩]) unmarked_context_11_23511_761021 node_context_11_23511_761021
  intro a
  fin_cases a
  · exact context_12_94044_760979
  · exact context_12_94045_642341
  · exact context_12_94046_761020
  · exact context_12_94047_757807

theorem unmarked_context_10_5877_761022 : frontier 11 ⟨761022, by decide⟩
    (prefixCache 10 5877) (prefixPartial 10 5877) = false := by
  decide +kernel

theorem node_context_10_5877_761022 : EJMOriginalGlobalDAGData.nodes 11 ⟨761022, by decide⟩ =
    .split (coordinate 10) (![⟨760673, by decide⟩,⟨760805, by decide⟩,⟨760942, by decide⟩,⟨761021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5877_761022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5877 ⟨761022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5877
    ⟨761022, by decide⟩ (by decide) (![⟨760673, by decide⟩,⟨760805, by decide⟩,⟨760942, by decide⟩,⟨761021, by decide⟩]) unmarked_context_10_5877_761022 node_context_10_5877_761022
  intro a
  fin_cases a
  · exact context_11_23508_760673
  · exact context_11_23509_760805
  · exact context_11_23510_760942
  · exact context_11_23511_761021

theorem selected_cut_30154 : selected 9 ⟨761066, by decide⟩
    (prefixPartial 12 94048) = some ⟨12, 2, 0, 761066, 94048, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_94048_761066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94048 ⟨761066, by decide⟩ :=
  accepted_of_selected 12 94048 ⟨761066, by decide⟩ ⟨12, 2, 0, 761066, 94048, 3301, 65536⟩
    (by decide) selected_cut_30154

theorem selected_cut_30155 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 376196) = some ⟨13, 1, 0, 3444, 376196, 1, 16384⟩ := by
  decide +kernel

theorem context_13_376196_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376196 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 376196 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 376196, 1, 16384⟩
    (by decide) selected_cut_30155

theorem selected_cut_30156 : selected 8 ⟨761109, by decide⟩
    (prefixPartial 13 376197) = some ⟨13, 2, 0, 761109, 376197, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_376197_761109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376197 ⟨761109, by decide⟩ :=
  accepted_of_selected 13 376197 ⟨761109, by decide⟩ ⟨13, 2, 0, 761109, 376197, 1585, 16384⟩
    (by decide) selected_cut_30156

theorem selected_cut_30157 : selected 8 ⟨761155, by decide⟩
    (prefixPartial 13 376198) = some ⟨13, 2, 0, 761155, 376198, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_376198_761155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376198 ⟨761155, by decide⟩ :=
  accepted_of_selected 13 376198 ⟨761155, by decide⟩ ⟨13, 2, 0, 761155, 376198, 2117, 16384⟩
    (by decide) selected_cut_30157

theorem selected_cut_30158 : selected 8 ⟨761163, by decide⟩
    (prefixPartial 13 376199) = some ⟨13, 2, 0, 761163, 376199, 793, 16384⟩ := by
  decide +kernel

theorem context_13_376199_761163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376199 ⟨761163, by decide⟩ :=
  accepted_of_selected 13 376199 ⟨761163, by decide⟩ ⟨13, 2, 0, 761163, 376199, 793, 16384⟩
    (by decide) selected_cut_30158

theorem unmarked_context_12_94049_761164 : frontier 9 ⟨761164, by decide⟩
    (prefixCache 12 94049) (prefixPartial 12 94049) = false := by
  decide +kernel

theorem node_context_12_94049_761164 : EJMOriginalGlobalDAGData.nodes 9 ⟨761164, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨761109, by decide⟩,⟨761155, by decide⟩,⟨761163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94049_761164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94049 ⟨761164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94049
    ⟨761164, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨761109, by decide⟩,⟨761155, by decide⟩,⟨761163, by decide⟩]) unmarked_context_12_94049_761164 node_context_12_94049_761164
  intro a
  fin_cases a
  · exact context_13_376196_3444
  · exact context_13_376197_761109
  · exact context_13_376198_761155
  · exact context_13_376199_761163

theorem selected_cut_30159 : selected 9 ⟨761219, by decide⟩
    (prefixPartial 12 94050) = some ⟨12, 2, 0, 761219, 94050, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_94050_761219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94050 ⟨761219, by decide⟩ :=
  accepted_of_selected 12 94050 ⟨761219, by decide⟩ ⟨12, 2, 0, 761219, 94050, 3217, 65536⟩
    (by decide) selected_cut_30159

theorem selected_cut_30160 : selected 9 ⟨761262, by decide⟩
    (prefixPartial 12 94051) = some ⟨12, 2, 0, 761262, 94051, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_94051_761262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94051 ⟨761262, by decide⟩ :=
  accepted_of_selected 12 94051 ⟨761262, by decide⟩ ⟨12, 2, 0, 761262, 94051, 3077, 65536⟩
    (by decide) selected_cut_30160

theorem unmarked_context_11_23512_761263 : frontier 10 ⟨761263, by decide⟩
    (prefixCache 11 23512) (prefixPartial 11 23512) = false := by
  decide +kernel

theorem node_context_11_23512_761263 : EJMOriginalGlobalDAGData.nodes 10 ⟨761263, by decide⟩ =
    .split (coordinate 11) (![⟨761066, by decide⟩,⟨761164, by decide⟩,⟨761219, by decide⟩,⟨761262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23512_761263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23512 ⟨761263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23512
    ⟨761263, by decide⟩ (by decide) (![⟨761066, by decide⟩,⟨761164, by decide⟩,⟨761219, by decide⟩,⟨761262, by decide⟩]) unmarked_context_11_23512_761263 node_context_11_23512_761263
  intro a
  fin_cases a
  · exact context_12_94048_761066
  · exact context_12_94049_761164
  · exact context_12_94050_761219
  · exact context_12_94051_761262

theorem selected_cut_30161 : selected 9 ⟨761299, by decide⟩
    (prefixPartial 12 94052) = some ⟨12, 2, 0, 761299, 94052, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_94052_761299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94052 ⟨761299, by decide⟩ :=
  accepted_of_selected 12 94052 ⟨761299, by decide⟩ ⟨12, 2, 0, 761299, 94052, 2977, 65536⟩
    (by decide) selected_cut_30161

theorem selected_cut_30162 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 94053) = some ⟨12, 1, 0, 642794, 94053, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94053_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94053 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 94053 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 94053, 1, 65536⟩
    (by decide) selected_cut_30162

theorem selected_cut_30163 : selected 9 ⟨761338, by decide⟩
    (prefixPartial 12 94054) = some ⟨12, 2, 0, 761338, 94054, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_94054_761338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94054 ⟨761338, by decide⟩ :=
  accepted_of_selected 12 94054 ⟨761338, by decide⟩ ⟨12, 2, 0, 761338, 94054, 3017, 65536⟩
    (by decide) selected_cut_30163

theorem selected_cut_30164 : selected 9 ⟨761376, by decide⟩
    (prefixPartial 12 94055) = some ⟨12, 2, 0, 761376, 94055, 2997, 65536⟩ := by
  decide +kernel

theorem context_12_94055_761376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94055 ⟨761376, by decide⟩ :=
  accepted_of_selected 12 94055 ⟨761376, by decide⟩ ⟨12, 2, 0, 761376, 94055, 2997, 65536⟩
    (by decide) selected_cut_30164

theorem unmarked_context_11_23513_761377 : frontier 10 ⟨761377, by decide⟩
    (prefixCache 11 23513) (prefixPartial 11 23513) = false := by
  decide +kernel

theorem node_context_11_23513_761377 : EJMOriginalGlobalDAGData.nodes 10 ⟨761377, by decide⟩ =
    .split (coordinate 11) (![⟨761299, by decide⟩,⟨642794, by decide⟩,⟨761338, by decide⟩,⟨761376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23513_761377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23513 ⟨761377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23513
    ⟨761377, by decide⟩ (by decide) (![⟨761299, by decide⟩,⟨642794, by decide⟩,⟨761338, by decide⟩,⟨761376, by decide⟩]) unmarked_context_11_23513_761377 node_context_11_23513_761377
  intro a
  fin_cases a
  · exact context_12_94052_761299
  · exact context_12_94053_642794
  · exact context_12_94054_761338
  · exact context_12_94055_761376

theorem selected_cut_30165 : selected 9 ⟨761416, by decide⟩
    (prefixPartial 12 94056) = some ⟨12, 2, 0, 761416, 94056, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_94056_761416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94056 ⟨761416, by decide⟩ :=
  accepted_of_selected 12 94056 ⟨761416, by decide⟩ ⟨12, 2, 0, 761416, 94056, 2757, 65536⟩
    (by decide) selected_cut_30165

theorem selected_cut_30166 : selected 9 ⟨761490, by decide⟩
    (prefixPartial 12 94057) = some ⟨12, 2, 0, 761490, 94057, 3981, 65536⟩ := by
  decide +kernel

theorem context_12_94057_761490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94057 ⟨761490, by decide⟩ :=
  accepted_of_selected 12 94057 ⟨761490, by decide⟩ ⟨12, 2, 0, 761490, 94057, 3981, 65536⟩
    (by decide) selected_cut_30166

theorem selected_cut_30167 : selected 9 ⟨761527, by decide⟩
    (prefixPartial 12 94058) = some ⟨12, 2, 0, 761527, 94058, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_94058_761527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94058 ⟨761527, by decide⟩ :=
  accepted_of_selected 12 94058 ⟨761527, by decide⟩ ⟨12, 2, 0, 761527, 94058, 2617, 65536⟩
    (by decide) selected_cut_30167

theorem selected_cut_30168 : selected 9 ⟨761565, by decide⟩
    (prefixPartial 12 94059) = some ⟨12, 2, 0, 761565, 94059, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_94059_761565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94059 ⟨761565, by decide⟩ :=
  accepted_of_selected 12 94059 ⟨761565, by decide⟩ ⟨12, 2, 0, 761565, 94059, 2681, 65536⟩
    (by decide) selected_cut_30168

theorem unmarked_context_11_23514_761566 : frontier 10 ⟨761566, by decide⟩
    (prefixCache 11 23514) (prefixPartial 11 23514) = false := by
  decide +kernel

theorem node_context_11_23514_761566 : EJMOriginalGlobalDAGData.nodes 10 ⟨761566, by decide⟩ =
    .split (coordinate 11) (![⟨761416, by decide⟩,⟨761490, by decide⟩,⟨761527, by decide⟩,⟨761565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23514_761566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23514 ⟨761566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23514
    ⟨761566, by decide⟩ (by decide) (![⟨761416, by decide⟩,⟨761490, by decide⟩,⟨761527, by decide⟩,⟨761565, by decide⟩]) unmarked_context_11_23514_761566 node_context_11_23514_761566
  intro a
  fin_cases a
  · exact context_12_94056_761416
  · exact context_12_94057_761490
  · exact context_12_94058_761527
  · exact context_12_94059_761565

theorem selected_cut_30169 : selected 9 ⟨761597, by decide⟩
    (prefixPartial 12 94060) = some ⟨12, 2, 0, 761597, 94060, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_94060_761597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94060 ⟨761597, by decide⟩ :=
  accepted_of_selected 12 94060 ⟨761597, by decide⟩ ⟨12, 2, 0, 761597, 94060, 2105, 65536⟩
    (by decide) selected_cut_30169

theorem selected_cut_30170 : selected 9 ⟨431769, by decide⟩
    (prefixPartial 12 94061) = some ⟨12, 1, 0, 431769, 94061, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94061_431769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94061 ⟨431769, by decide⟩ :=
  accepted_of_selected 12 94061 ⟨431769, by decide⟩ ⟨12, 1, 0, 431769, 94061, 1, 65536⟩
    (by decide) selected_cut_30170

theorem selected_cut_30171 : selected 9 ⟨761634, by decide⟩
    (prefixPartial 12 94062) = some ⟨12, 2, 0, 761634, 94062, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_94062_761634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94062 ⟨761634, by decide⟩ :=
  accepted_of_selected 12 94062 ⟨761634, by decide⟩ ⟨12, 2, 0, 761634, 94062, 2253, 65536⟩
    (by decide) selected_cut_30171

theorem selected_cut_30172 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 94063) = some ⟨12, 1, 0, 758968, 94063, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94063_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94063 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 94063 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 94063, 1, 65536⟩
    (by decide) selected_cut_30172

theorem unmarked_context_11_23515_761635 : frontier 10 ⟨761635, by decide⟩
    (prefixCache 11 23515) (prefixPartial 11 23515) = false := by
  decide +kernel

theorem node_context_11_23515_761635 : EJMOriginalGlobalDAGData.nodes 10 ⟨761635, by decide⟩ =
    .split (coordinate 11) (![⟨761597, by decide⟩,⟨431769, by decide⟩,⟨761634, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23515_761635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23515 ⟨761635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23515
    ⟨761635, by decide⟩ (by decide) (![⟨761597, by decide⟩,⟨431769, by decide⟩,⟨761634, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_23515_761635 node_context_11_23515_761635
  intro a
  fin_cases a
  · exact context_12_94060_761597
  · exact context_12_94061_431769
  · exact context_12_94062_761634
  · exact context_12_94063_758968

theorem unmarked_context_10_5878_761636 : frontier 11 ⟨761636, by decide⟩
    (prefixCache 10 5878) (prefixPartial 10 5878) = false := by
  decide +kernel

theorem node_context_10_5878_761636 : EJMOriginalGlobalDAGData.nodes 11 ⟨761636, by decide⟩ =
    .split (coordinate 10) (![⟨761263, by decide⟩,⟨761377, by decide⟩,⟨761566, by decide⟩,⟨761635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5878_761636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5878 ⟨761636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5878
    ⟨761636, by decide⟩ (by decide) (![⟨761263, by decide⟩,⟨761377, by decide⟩,⟨761566, by decide⟩,⟨761635, by decide⟩]) unmarked_context_10_5878_761636 node_context_10_5878_761636
  intro a
  fin_cases a
  · exact context_11_23512_761263
  · exact context_11_23513_761377
  · exact context_11_23514_761566
  · exact context_11_23515_761635

theorem selected_cut_30173 : selected 9 ⟨761682, by decide⟩
    (prefixPartial 12 94064) = some ⟨12, 2, 0, 761682, 94064, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_94064_761682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94064 ⟨761682, by decide⟩ :=
  accepted_of_selected 12 94064 ⟨761682, by decide⟩ ⟨12, 2, 0, 761682, 94064, 3129, 65536⟩
    (by decide) selected_cut_30173

theorem selected_cut_30174 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 376260) = some ⟨13, 1, 0, 3444, 376260, 1, 16384⟩ := by
  decide +kernel

theorem context_13_376260_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376260 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 376260 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 376260, 1, 16384⟩
    (by decide) selected_cut_30174

theorem selected_cut_30175 : selected 8 ⟨761704, by decide⟩
    (prefixPartial 13 376261) = some ⟨13, 2, 0, 761704, 376261, 873, 16384⟩ := by
  decide +kernel

theorem context_13_376261_761704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376261 ⟨761704, by decide⟩ :=
  accepted_of_selected 13 376261 ⟨761704, by decide⟩ ⟨13, 2, 0, 761704, 376261, 873, 16384⟩
    (by decide) selected_cut_30175

theorem selected_cut_30176 : selected 8 ⟨761735, by decide⟩
    (prefixPartial 13 376262) = some ⟨13, 2, 0, 761735, 376262, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_376262_761735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376262 ⟨761735, by decide⟩ :=
  accepted_of_selected 13 376262 ⟨761735, by decide⟩ ⟨13, 2, 0, 761735, 376262, 2321, 16384⟩
    (by decide) selected_cut_30176

theorem selected_cut_30177 : selected 8 ⟨761747, by decide⟩
    (prefixPartial 13 376263) = some ⟨13, 2, 0, 761747, 376263, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_376263_761747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376263 ⟨761747, by decide⟩ :=
  accepted_of_selected 13 376263 ⟨761747, by decide⟩ ⟨13, 2, 0, 761747, 376263, 1009, 16384⟩
    (by decide) selected_cut_30177

theorem unmarked_context_12_94065_761748 : frontier 9 ⟨761748, by decide⟩
    (prefixCache 12 94065) (prefixPartial 12 94065) = false := by
  decide +kernel

theorem node_context_12_94065_761748 : EJMOriginalGlobalDAGData.nodes 9 ⟨761748, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨761704, by decide⟩,⟨761735, by decide⟩,⟨761747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94065_761748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94065 ⟨761748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94065
    ⟨761748, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨761704, by decide⟩,⟨761735, by decide⟩,⟨761747, by decide⟩]) unmarked_context_12_94065_761748 node_context_12_94065_761748
  intro a
  fin_cases a
  · exact context_13_376260_3444
  · exact context_13_376261_761704
  · exact context_13_376262_761735
  · exact context_13_376263_761747

theorem selected_cut_30178 : selected 9 ⟨761786, by decide⟩
    (prefixPartial 12 94066) = some ⟨12, 2, 0, 761786, 94066, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_94066_761786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94066 ⟨761786, by decide⟩ :=
  accepted_of_selected 12 94066 ⟨761786, by decide⟩ ⟨12, 2, 0, 761786, 94066, 3021, 65536⟩
    (by decide) selected_cut_30178

theorem selected_cut_30179 : selected 9 ⟨761816, by decide⟩
    (prefixPartial 12 94067) = some ⟨12, 2, 0, 761816, 94067, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_94067_761816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94067 ⟨761816, by decide⟩ :=
  accepted_of_selected 12 94067 ⟨761816, by decide⟩ ⟨12, 2, 0, 761816, 94067, 2837, 65536⟩
    (by decide) selected_cut_30179

theorem unmarked_context_11_23516_761817 : frontier 10 ⟨761817, by decide⟩
    (prefixCache 11 23516) (prefixPartial 11 23516) = false := by
  decide +kernel

theorem node_context_11_23516_761817 : EJMOriginalGlobalDAGData.nodes 10 ⟨761817, by decide⟩ =
    .split (coordinate 11) (![⟨761682, by decide⟩,⟨761748, by decide⟩,⟨761786, by decide⟩,⟨761816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23516_761817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23516 ⟨761817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23516
    ⟨761817, by decide⟩ (by decide) (![⟨761682, by decide⟩,⟨761748, by decide⟩,⟨761786, by decide⟩,⟨761816, by decide⟩]) unmarked_context_11_23516_761817 node_context_11_23516_761817
  intro a
  fin_cases a
  · exact context_12_94064_761682
  · exact context_12_94065_761748
  · exact context_12_94066_761786
  · exact context_12_94067_761816

theorem selected_cut_30180 : selected 9 ⟨761856, by decide⟩
    (prefixPartial 12 94068) = some ⟨12, 2, 0, 761856, 94068, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_94068_761856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94068 ⟨761856, by decide⟩ :=
  accepted_of_selected 12 94068 ⟨761856, by decide⟩ ⟨12, 2, 0, 761856, 94068, 2861, 65536⟩
    (by decide) selected_cut_30180

theorem selected_cut_30181 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 94069) = some ⟨12, 1, 0, 642794, 94069, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94069_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94069 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 94069 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 94069, 1, 65536⟩
    (by decide) selected_cut_30181

theorem selected_cut_30182 : selected 9 ⟨761894, by decide⟩
    (prefixPartial 12 94070) = some ⟨12, 2, 0, 761894, 94070, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_94070_761894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94070 ⟨761894, by decide⟩ :=
  accepted_of_selected 12 94070 ⟨761894, by decide⟩ ⟨12, 2, 0, 761894, 94070, 2649, 65536⟩
    (by decide) selected_cut_30182

theorem selected_cut_30183 : selected 9 ⟨761929, by decide⟩
    (prefixPartial 12 94071) = some ⟨12, 2, 0, 761929, 94071, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_94071_761929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94071 ⟨761929, by decide⟩ :=
  accepted_of_selected 12 94071 ⟨761929, by decide⟩ ⟨12, 2, 0, 761929, 94071, 2769, 65536⟩
    (by decide) selected_cut_30183

theorem unmarked_context_11_23517_761930 : frontier 10 ⟨761930, by decide⟩
    (prefixCache 11 23517) (prefixPartial 11 23517) = false := by
  decide +kernel

theorem node_context_11_23517_761930 : EJMOriginalGlobalDAGData.nodes 10 ⟨761930, by decide⟩ =
    .split (coordinate 11) (![⟨761856, by decide⟩,⟨642794, by decide⟩,⟨761894, by decide⟩,⟨761929, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23517_761930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23517 ⟨761930, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23517
    ⟨761930, by decide⟩ (by decide) (![⟨761856, by decide⟩,⟨642794, by decide⟩,⟨761894, by decide⟩,⟨761929, by decide⟩]) unmarked_context_11_23517_761930 node_context_11_23517_761930
  intro a
  fin_cases a
  · exact context_12_94068_761856
  · exact context_12_94069_642794
  · exact context_12_94070_761894
  · exact context_12_94071_761929

theorem selected_cut_30184 : selected 9 ⟨761972, by decide⟩
    (prefixPartial 12 94072) = some ⟨12, 2, 0, 761972, 94072, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_94072_761972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94072 ⟨761972, by decide⟩ :=
  accepted_of_selected 12 94072 ⟨761972, by decide⟩ ⟨12, 2, 0, 761972, 94072, 2805, 65536⟩
    (by decide) selected_cut_30184

theorem selected_cut_30185 : selected 9 ⟨762043, by decide⟩
    (prefixPartial 12 94073) = some ⟨12, 2, 0, 762043, 94073, 3773, 65536⟩ := by
  decide +kernel

theorem context_12_94073_762043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94073 ⟨762043, by decide⟩ :=
  accepted_of_selected 12 94073 ⟨762043, by decide⟩ ⟨12, 2, 0, 762043, 94073, 3773, 65536⟩
    (by decide) selected_cut_30185

theorem selected_cut_30186 : selected 9 ⟨762075, by decide⟩
    (prefixPartial 12 94074) = some ⟨12, 2, 0, 762075, 94074, 2409, 65536⟩ := by
  decide +kernel

theorem context_12_94074_762075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94074 ⟨762075, by decide⟩ :=
  accepted_of_selected 12 94074 ⟨762075, by decide⟩ ⟨12, 2, 0, 762075, 94074, 2409, 65536⟩
    (by decide) selected_cut_30186

theorem selected_cut_30187 : selected 9 ⟨762106, by decide⟩
    (prefixPartial 12 94075) = some ⟨12, 2, 0, 762106, 94075, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_94075_762106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94075 ⟨762106, by decide⟩ :=
  accepted_of_selected 12 94075 ⟨762106, by decide⟩ ⟨12, 2, 0, 762106, 94075, 2477, 65536⟩
    (by decide) selected_cut_30187

theorem unmarked_context_11_23518_762107 : frontier 10 ⟨762107, by decide⟩
    (prefixCache 11 23518) (prefixPartial 11 23518) = false := by
  decide +kernel

theorem node_context_11_23518_762107 : EJMOriginalGlobalDAGData.nodes 10 ⟨762107, by decide⟩ =
    .split (coordinate 11) (![⟨761972, by decide⟩,⟨762043, by decide⟩,⟨762075, by decide⟩,⟨762106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23518_762107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23518 ⟨762107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23518
    ⟨762107, by decide⟩ (by decide) (![⟨761972, by decide⟩,⟨762043, by decide⟩,⟨762075, by decide⟩,⟨762106, by decide⟩]) unmarked_context_11_23518_762107 node_context_11_23518_762107
  intro a
  fin_cases a
  · exact context_12_94072_761972
  · exact context_12_94073_762043
  · exact context_12_94074_762075
  · exact context_12_94075_762106

theorem selected_cut_30188 : selected 10 ⟨762110, by decide⟩
    (prefixPartial 11 23519) = some ⟨11, 2, 0, 762110, 23519, 5, 262144⟩ := by
  decide +kernel

theorem context_11_23519_762110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23519 ⟨762110, by decide⟩ :=
  accepted_of_selected 11 23519 ⟨762110, by decide⟩ ⟨11, 2, 0, 762110, 23519, 5, 262144⟩
    (by decide) selected_cut_30188

theorem unmarked_context_10_5879_762111 : frontier 11 ⟨762111, by decide⟩
    (prefixCache 10 5879) (prefixPartial 10 5879) = false := by
  decide +kernel

theorem node_context_10_5879_762111 : EJMOriginalGlobalDAGData.nodes 11 ⟨762111, by decide⟩ =
    .split (coordinate 10) (![⟨761817, by decide⟩,⟨761930, by decide⟩,⟨762107, by decide⟩,⟨762110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5879_762111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5879 ⟨762111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5879
    ⟨762111, by decide⟩ (by decide) (![⟨761817, by decide⟩,⟨761930, by decide⟩,⟨762107, by decide⟩,⟨762110, by decide⟩]) unmarked_context_10_5879_762111 node_context_10_5879_762111
  intro a
  fin_cases a
  · exact context_11_23516_761817
  · exact context_11_23517_761930
  · exact context_11_23518_762107
  · exact context_11_23519_762110

theorem unmarked_context_9_1469_762112 : frontier 12 ⟨762112, by decide⟩
    (prefixCache 9 1469) (prefixPartial 9 1469) = false := by
  decide +kernel

theorem node_context_9_1469_762112 : EJMOriginalGlobalDAGData.nodes 12 ⟨762112, by decide⟩ =
    .split (coordinate 9) (![⟨760513, by decide⟩,⟨761022, by decide⟩,⟨761636, by decide⟩,⟨762111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1469_762112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1469 ⟨762112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1469
    ⟨762112, by decide⟩ (by decide) (![⟨760513, by decide⟩,⟨761022, by decide⟩,⟨761636, by decide⟩,⟨762111, by decide⟩]) unmarked_context_9_1469_762112 node_context_9_1469_762112
  intro a
  fin_cases a
  · exact context_10_5876_760513
  · exact context_10_5877_761022
  · exact context_10_5878_761636
  · exact context_10_5879_762111

theorem selected_cut_30189 : selected 9 ⟨762141, by decide⟩
    (prefixPartial 12 94080) = some ⟨12, 2, 0, 762141, 94080, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_94080_762141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94080 ⟨762141, by decide⟩ :=
  accepted_of_selected 12 94080 ⟨762141, by decide⟩ ⟨12, 2, 0, 762141, 94080, 2557, 65536⟩
    (by decide) selected_cut_30189

theorem selected_cut_30190 : selected 9 ⟨762163, by decide⟩
    (prefixPartial 12 94081) = some ⟨12, 2, 0, 762163, 94081, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_94081_762163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94081 ⟨762163, by decide⟩ :=
  accepted_of_selected 12 94081 ⟨762163, by decide⟩ ⟨12, 2, 0, 762163, 94081, 2521, 65536⟩
    (by decide) selected_cut_30190

theorem selected_cut_30191 : selected 9 ⟨762184, by decide⟩
    (prefixPartial 12 94082) = some ⟨12, 2, 0, 762184, 94082, 2385, 65536⟩ := by
  decide +kernel

theorem context_12_94082_762184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94082 ⟨762184, by decide⟩ :=
  accepted_of_selected 12 94082 ⟨762184, by decide⟩ ⟨12, 2, 0, 762184, 94082, 2385, 65536⟩
    (by decide) selected_cut_30191

theorem selected_cut_30192 : selected 9 ⟨762211, by decide⟩
    (prefixPartial 12 94083) = some ⟨12, 2, 0, 762211, 94083, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_94083_762211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94083 ⟨762211, by decide⟩ :=
  accepted_of_selected 12 94083 ⟨762211, by decide⟩ ⟨12, 2, 0, 762211, 94083, 2541, 65536⟩
    (by decide) selected_cut_30192

theorem unmarked_context_11_23520_762212 : frontier 10 ⟨762212, by decide⟩
    (prefixCache 11 23520) (prefixPartial 11 23520) = false := by
  decide +kernel

theorem node_context_11_23520_762212 : EJMOriginalGlobalDAGData.nodes 10 ⟨762212, by decide⟩ =
    .split (coordinate 11) (![⟨762141, by decide⟩,⟨762163, by decide⟩,⟨762184, by decide⟩,⟨762211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23520_762212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23520 ⟨762212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23520
    ⟨762212, by decide⟩ (by decide) (![⟨762141, by decide⟩,⟨762163, by decide⟩,⟨762184, by decide⟩,⟨762211, by decide⟩]) unmarked_context_11_23520_762212 node_context_11_23520_762212
  intro a
  fin_cases a
  · exact context_12_94080_762141
  · exact context_12_94081_762163
  · exact context_12_94082_762184
  · exact context_12_94083_762211

theorem selected_cut_30193 : selected 9 ⟨762243, by decide⟩
    (prefixPartial 12 94084) = some ⟨12, 2, 0, 762243, 94084, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_94084_762243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94084 ⟨762243, by decide⟩ :=
  accepted_of_selected 12 94084 ⟨762243, by decide⟩ ⟨12, 2, 0, 762243, 94084, 2545, 65536⟩
    (by decide) selected_cut_30193

theorem selected_cut_30194 : selected 9 ⟨762269, by decide⟩
    (prefixPartial 12 94085) = some ⟨12, 2, 0, 762269, 94085, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_94085_762269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94085 ⟨762269, by decide⟩ :=
  accepted_of_selected 12 94085 ⟨762269, by decide⟩ ⟨12, 2, 0, 762269, 94085, 2245, 65536⟩
    (by decide) selected_cut_30194

theorem selected_cut_30195 : selected 9 ⟨762289, by decide⟩
    (prefixPartial 12 94086) = some ⟨12, 2, 0, 762289, 94086, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_94086_762289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94086 ⟨762289, by decide⟩ :=
  accepted_of_selected 12 94086 ⟨762289, by decide⟩ ⟨12, 2, 0, 762289, 94086, 2249, 65536⟩
    (by decide) selected_cut_30195

theorem selected_cut_30196 : selected 9 ⟨762316, by decide⟩
    (prefixPartial 12 94087) = some ⟨12, 2, 0, 762316, 94087, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_94087_762316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94087 ⟨762316, by decide⟩ :=
  accepted_of_selected 12 94087 ⟨762316, by decide⟩ ⟨12, 2, 0, 762316, 94087, 2501, 65536⟩
    (by decide) selected_cut_30196

theorem unmarked_context_11_23521_762317 : frontier 10 ⟨762317, by decide⟩
    (prefixCache 11 23521) (prefixPartial 11 23521) = false := by
  decide +kernel

theorem node_context_11_23521_762317 : EJMOriginalGlobalDAGData.nodes 10 ⟨762317, by decide⟩ =
    .split (coordinate 11) (![⟨762243, by decide⟩,⟨762269, by decide⟩,⟨762289, by decide⟩,⟨762316, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23521_762317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23521 ⟨762317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23521
    ⟨762317, by decide⟩ (by decide) (![⟨762243, by decide⟩,⟨762269, by decide⟩,⟨762289, by decide⟩,⟨762316, by decide⟩]) unmarked_context_11_23521_762317 node_context_11_23521_762317
  intro a
  fin_cases a
  · exact context_12_94084_762243
  · exact context_12_94085_762269
  · exact context_12_94086_762289
  · exact context_12_94087_762316

theorem selected_cut_30197 : selected 9 ⟨762356, by decide⟩
    (prefixPartial 12 94088) = some ⟨12, 2, 0, 762356, 94088, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_94088_762356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94088 ⟨762356, by decide⟩ :=
  accepted_of_selected 12 94088 ⟨762356, by decide⟩ ⟨12, 2, 0, 762356, 94088, 2705, 65536⟩
    (by decide) selected_cut_30197

theorem selected_cut_30198 : selected 9 ⟨762394, by decide⟩
    (prefixPartial 12 94089) = some ⟨12, 2, 0, 762394, 94089, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_94089_762394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94089 ⟨762394, by decide⟩ :=
  accepted_of_selected 12 94089 ⟨762394, by decide⟩ ⟨12, 2, 0, 762394, 94089, 2509, 65536⟩
    (by decide) selected_cut_30198

theorem selected_cut_30199 : selected 9 ⟨762421, by decide⟩
    (prefixPartial 12 94090) = some ⟨12, 2, 0, 762421, 94090, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_94090_762421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94090 ⟨762421, by decide⟩ :=
  accepted_of_selected 12 94090 ⟨762421, by decide⟩ ⟨12, 2, 0, 762421, 94090, 2257, 65536⟩
    (by decide) selected_cut_30199

theorem selected_cut_30200 : selected 9 ⟨762457, by decide⟩
    (prefixPartial 12 94091) = some ⟨12, 2, 0, 762457, 94091, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_94091_762457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94091 ⟨762457, by decide⟩ :=
  accepted_of_selected 12 94091 ⟨762457, by decide⟩ ⟨12, 2, 0, 762457, 94091, 2493, 65536⟩
    (by decide) selected_cut_30200

theorem unmarked_context_11_23522_762458 : frontier 10 ⟨762458, by decide⟩
    (prefixCache 11 23522) (prefixPartial 11 23522) = false := by
  decide +kernel

theorem node_context_11_23522_762458 : EJMOriginalGlobalDAGData.nodes 10 ⟨762458, by decide⟩ =
    .split (coordinate 11) (![⟨762356, by decide⟩,⟨762394, by decide⟩,⟨762421, by decide⟩,⟨762457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23522_762458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23522 ⟨762458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23522
    ⟨762458, by decide⟩ (by decide) (![⟨762356, by decide⟩,⟨762394, by decide⟩,⟨762421, by decide⟩,⟨762457, by decide⟩]) unmarked_context_11_23522_762458 node_context_11_23522_762458
  intro a
  fin_cases a
  · exact context_12_94088_762356
  · exact context_12_94089_762394
  · exact context_12_94090_762421
  · exact context_12_94091_762457

theorem selected_cut_30201 : selected 9 ⟨762481, by decide⟩
    (prefixPartial 12 94092) = some ⟨12, 2, 0, 762481, 94092, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_94092_762481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94092 ⟨762481, by decide⟩ :=
  accepted_of_selected 12 94092 ⟨762481, by decide⟩ ⟨12, 2, 0, 762481, 94092, 1977, 65536⟩
    (by decide) selected_cut_30201

theorem selected_cut_30202 : selected 9 ⟨762505, by decide⟩
    (prefixPartial 12 94093) = some ⟨12, 2, 0, 762505, 94093, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_94093_762505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94093 ⟨762505, by decide⟩ :=
  accepted_of_selected 12 94093 ⟨762505, by decide⟩ ⟨12, 2, 0, 762505, 94093, 1921, 65536⟩
    (by decide) selected_cut_30202

theorem selected_cut_30203 : selected 9 ⟨762527, by decide⟩
    (prefixPartial 12 94094) = some ⟨12, 2, 0, 762527, 94094, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_94094_762527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94094 ⟨762527, by decide⟩ :=
  accepted_of_selected 12 94094 ⟨762527, by decide⟩ ⟨12, 2, 0, 762527, 94094, 1701, 65536⟩
    (by decide) selected_cut_30203

theorem selected_cut_30204 : selected 9 ⟨760511, by decide⟩
    (prefixPartial 12 94095) = some ⟨12, 1, 0, 760511, 94095, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94095_760511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94095 ⟨760511, by decide⟩ :=
  accepted_of_selected 12 94095 ⟨760511, by decide⟩ ⟨12, 1, 0, 760511, 94095, 1, 65536⟩
    (by decide) selected_cut_30204

theorem unmarked_context_11_23523_762528 : frontier 10 ⟨762528, by decide⟩
    (prefixCache 11 23523) (prefixPartial 11 23523) = false := by
  decide +kernel

theorem node_context_11_23523_762528 : EJMOriginalGlobalDAGData.nodes 10 ⟨762528, by decide⟩ =
    .split (coordinate 11) (![⟨762481, by decide⟩,⟨762505, by decide⟩,⟨762527, by decide⟩,⟨760511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23523_762528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23523 ⟨762528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23523
    ⟨762528, by decide⟩ (by decide) (![⟨762481, by decide⟩,⟨762505, by decide⟩,⟨762527, by decide⟩,⟨760511, by decide⟩]) unmarked_context_11_23523_762528 node_context_11_23523_762528
  intro a
  fin_cases a
  · exact context_12_94092_762481
  · exact context_12_94093_762505
  · exact context_12_94094_762527
  · exact context_12_94095_760511

theorem unmarked_context_10_5880_762529 : frontier 11 ⟨762529, by decide⟩
    (prefixCache 10 5880) (prefixPartial 10 5880) = false := by
  decide +kernel

theorem node_context_10_5880_762529 : EJMOriginalGlobalDAGData.nodes 11 ⟨762529, by decide⟩ =
    .split (coordinate 10) (![⟨762212, by decide⟩,⟨762317, by decide⟩,⟨762458, by decide⟩,⟨762528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5880_762529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5880 ⟨762529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5880
    ⟨762529, by decide⟩ (by decide) (![⟨762212, by decide⟩,⟨762317, by decide⟩,⟨762458, by decide⟩,⟨762528, by decide⟩]) unmarked_context_10_5880_762529 node_context_10_5880_762529
  intro a
  fin_cases a
  · exact context_11_23520_762212
  · exact context_11_23521_762317
  · exact context_11_23522_762458
  · exact context_11_23523_762528

theorem selected_cut_30205 : selected 9 ⟨762556, by decide⟩
    (prefixPartial 12 94096) = some ⟨12, 2, 0, 762556, 94096, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_94096_762556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94096 ⟨762556, by decide⟩ :=
  accepted_of_selected 12 94096 ⟨762556, by decide⟩ ⟨12, 2, 0, 762556, 94096, 2337, 65536⟩
    (by decide) selected_cut_30205

theorem selected_cut_30206 : selected 9 ⟨762585, by decide⟩
    (prefixPartial 12 94097) = some ⟨12, 2, 0, 762585, 94097, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_94097_762585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94097 ⟨762585, by decide⟩ :=
  accepted_of_selected 12 94097 ⟨762585, by decide⟩ ⟨12, 2, 0, 762585, 94097, 2229, 65536⟩
    (by decide) selected_cut_30206

theorem selected_cut_30207 : selected 9 ⟨762614, by decide⟩
    (prefixPartial 12 94098) = some ⟨12, 2, 0, 762614, 94098, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_94098_762614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94098 ⟨762614, by decide⟩ :=
  accepted_of_selected 12 94098 ⟨762614, by decide⟩ ⟨12, 2, 0, 762614, 94098, 2173, 65536⟩
    (by decide) selected_cut_30207

theorem selected_cut_30208 : selected 9 ⟨762635, by decide⟩
    (prefixPartial 12 94099) = some ⟨12, 2, 0, 762635, 94099, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_94099_762635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94099 ⟨762635, by decide⟩ :=
  accepted_of_selected 12 94099 ⟨762635, by decide⟩ ⟨12, 2, 0, 762635, 94099, 2185, 65536⟩
    (by decide) selected_cut_30208

theorem unmarked_context_11_23524_762636 : frontier 10 ⟨762636, by decide⟩
    (prefixCache 11 23524) (prefixPartial 11 23524) = false := by
  decide +kernel

theorem node_context_11_23524_762636 : EJMOriginalGlobalDAGData.nodes 10 ⟨762636, by decide⟩ =
    .split (coordinate 11) (![⟨762556, by decide⟩,⟨762585, by decide⟩,⟨762614, by decide⟩,⟨762635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23524_762636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23524 ⟨762636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23524
    ⟨762636, by decide⟩ (by decide) (![⟨762556, by decide⟩,⟨762585, by decide⟩,⟨762614, by decide⟩,⟨762635, by decide⟩]) unmarked_context_11_23524_762636 node_context_11_23524_762636
  intro a
  fin_cases a
  · exact context_12_94096_762556
  · exact context_12_94097_762585
  · exact context_12_94098_762614
  · exact context_12_94099_762635

theorem selected_cut_30209 : selected 9 ⟨762663, by decide⟩
    (prefixPartial 12 94100) = some ⟨12, 2, 0, 762663, 94100, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_94100_762663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94100 ⟨762663, by decide⟩ :=
  accepted_of_selected 12 94100 ⟨762663, by decide⟩ ⟨12, 2, 0, 762663, 94100, 2269, 65536⟩
    (by decide) selected_cut_30209

theorem selected_cut_30210 : selected 9 ⟨762683, by decide⟩
    (prefixPartial 12 94101) = some ⟨12, 2, 0, 762683, 94101, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_94101_762683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94101 ⟨762683, by decide⟩ :=
  accepted_of_selected 12 94101 ⟨762683, by decide⟩ ⟨12, 2, 0, 762683, 94101, 1961, 65536⟩
    (by decide) selected_cut_30210

theorem selected_cut_30211 : selected 9 ⟨762706, by decide⟩
    (prefixPartial 12 94102) = some ⟨12, 2, 0, 762706, 94102, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_94102_762706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94102 ⟨762706, by decide⟩ :=
  accepted_of_selected 12 94102 ⟨762706, by decide⟩ ⟨12, 2, 0, 762706, 94102, 2009, 65536⟩
    (by decide) selected_cut_30211

theorem selected_cut_30212 : selected 9 ⟨762734, by decide⟩
    (prefixPartial 12 94103) = some ⟨12, 2, 0, 762734, 94103, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_94103_762734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94103 ⟨762734, by decide⟩ :=
  accepted_of_selected 12 94103 ⟨762734, by decide⟩ ⟨12, 2, 0, 762734, 94103, 2089, 65536⟩
    (by decide) selected_cut_30212

theorem unmarked_context_11_23525_762735 : frontier 10 ⟨762735, by decide⟩
    (prefixCache 11 23525) (prefixPartial 11 23525) = false := by
  decide +kernel

theorem node_context_11_23525_762735 : EJMOriginalGlobalDAGData.nodes 10 ⟨762735, by decide⟩ =
    .split (coordinate 11) (![⟨762663, by decide⟩,⟨762683, by decide⟩,⟨762706, by decide⟩,⟨762734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23525_762735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23525 ⟨762735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23525
    ⟨762735, by decide⟩ (by decide) (![⟨762663, by decide⟩,⟨762683, by decide⟩,⟨762706, by decide⟩,⟨762734, by decide⟩]) unmarked_context_11_23525_762735 node_context_11_23525_762735
  intro a
  fin_cases a
  · exact context_12_94100_762663
  · exact context_12_94101_762683
  · exact context_12_94102_762706
  · exact context_12_94103_762734

theorem selected_cut_30213 : selected 9 ⟨762758, by decide⟩
    (prefixPartial 12 94104) = some ⟨12, 2, 0, 762758, 94104, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_94104_762758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94104 ⟨762758, by decide⟩ :=
  accepted_of_selected 12 94104 ⟨762758, by decide⟩ ⟨12, 2, 0, 762758, 94104, 2189, 65536⟩
    (by decide) selected_cut_30213

theorem selected_cut_30214 : selected 9 ⟨762782, by decide⟩
    (prefixPartial 12 94105) = some ⟨12, 2, 0, 762782, 94105, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_94105_762782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94105 ⟨762782, by decide⟩ :=
  accepted_of_selected 12 94105 ⟨762782, by decide⟩ ⟨12, 2, 0, 762782, 94105, 2041, 65536⟩
    (by decide) selected_cut_30214

theorem selected_cut_30215 : selected 9 ⟨762807, by decide⟩
    (prefixPartial 12 94106) = some ⟨12, 2, 0, 762807, 94106, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_94106_762807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94106 ⟨762807, by decide⟩ :=
  accepted_of_selected 12 94106 ⟨762807, by decide⟩ ⟨12, 2, 0, 762807, 94106, 1817, 65536⟩
    (by decide) selected_cut_30215

theorem selected_cut_30216 : selected 9 ⟨762830, by decide⟩
    (prefixPartial 12 94107) = some ⟨12, 2, 0, 762830, 94107, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_94107_762830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94107 ⟨762830, by decide⟩ :=
  accepted_of_selected 12 94107 ⟨762830, by decide⟩ ⟨12, 2, 0, 762830, 94107, 1929, 65536⟩
    (by decide) selected_cut_30216

theorem unmarked_context_11_23526_762831 : frontier 10 ⟨762831, by decide⟩
    (prefixCache 11 23526) (prefixPartial 11 23526) = false := by
  decide +kernel

theorem node_context_11_23526_762831 : EJMOriginalGlobalDAGData.nodes 10 ⟨762831, by decide⟩ =
    .split (coordinate 11) (![⟨762758, by decide⟩,⟨762782, by decide⟩,⟨762807, by decide⟩,⟨762830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23526_762831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23526 ⟨762831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23526
    ⟨762831, by decide⟩ (by decide) (![⟨762758, by decide⟩,⟨762782, by decide⟩,⟨762807, by decide⟩,⟨762830, by decide⟩]) unmarked_context_11_23526_762831 node_context_11_23526_762831
  intro a
  fin_cases a
  · exact context_12_94104_762758
  · exact context_12_94105_762782
  · exact context_12_94106_762807
  · exact context_12_94107_762830

theorem selected_cut_30217 : selected 9 ⟨762852, by decide⟩
    (prefixPartial 12 94108) = some ⟨12, 2, 0, 762852, 94108, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_94108_762852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94108 ⟨762852, by decide⟩ :=
  accepted_of_selected 12 94108 ⟨762852, by decide⟩ ⟨12, 2, 0, 762852, 94108, 1601, 65536⟩
    (by decide) selected_cut_30217

theorem selected_cut_30218 : selected 9 ⟨762872, by decide⟩
    (prefixPartial 12 94109) = some ⟨12, 2, 0, 762872, 94109, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_94109_762872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94109 ⟨762872, by decide⟩ :=
  accepted_of_selected 12 94109 ⟨762872, by decide⟩ ⟨12, 2, 0, 762872, 94109, 1517, 65536⟩
    (by decide) selected_cut_30218

theorem selected_cut_30219 : selected 9 ⟨762889, by decide⟩
    (prefixPartial 12 94110) = some ⟨12, 2, 0, 762889, 94110, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_94110_762889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94110 ⟨762889, by decide⟩ :=
  accepted_of_selected 12 94110 ⟨762889, by decide⟩ ⟨12, 2, 0, 762889, 94110, 1505, 65536⟩
    (by decide) selected_cut_30219

theorem selected_cut_30220 : selected 9 ⟨757807, by decide⟩
    (prefixPartial 12 94111) = some ⟨12, 1, 0, 757807, 94111, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94111_757807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94111 ⟨757807, by decide⟩ :=
  accepted_of_selected 12 94111 ⟨757807, by decide⟩ ⟨12, 1, 0, 757807, 94111, 1, 65536⟩
    (by decide) selected_cut_30220

theorem unmarked_context_11_23527_762890 : frontier 10 ⟨762890, by decide⟩
    (prefixCache 11 23527) (prefixPartial 11 23527) = false := by
  decide +kernel

theorem node_context_11_23527_762890 : EJMOriginalGlobalDAGData.nodes 10 ⟨762890, by decide⟩ =
    .split (coordinate 11) (![⟨762852, by decide⟩,⟨762872, by decide⟩,⟨762889, by decide⟩,⟨757807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23527_762890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23527 ⟨762890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23527
    ⟨762890, by decide⟩ (by decide) (![⟨762852, by decide⟩,⟨762872, by decide⟩,⟨762889, by decide⟩,⟨757807, by decide⟩]) unmarked_context_11_23527_762890 node_context_11_23527_762890
  intro a
  fin_cases a
  · exact context_12_94108_762852
  · exact context_12_94109_762872
  · exact context_12_94110_762889
  · exact context_12_94111_757807

theorem unmarked_context_10_5881_762891 : frontier 11 ⟨762891, by decide⟩
    (prefixCache 10 5881) (prefixPartial 10 5881) = false := by
  decide +kernel

theorem node_context_10_5881_762891 : EJMOriginalGlobalDAGData.nodes 11 ⟨762891, by decide⟩ =
    .split (coordinate 10) (![⟨762636, by decide⟩,⟨762735, by decide⟩,⟨762831, by decide⟩,⟨762890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5881_762891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5881 ⟨762891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5881
    ⟨762891, by decide⟩ (by decide) (![⟨762636, by decide⟩,⟨762735, by decide⟩,⟨762831, by decide⟩,⟨762890, by decide⟩]) unmarked_context_10_5881_762891 node_context_10_5881_762891
  intro a
  fin_cases a
  · exact context_11_23524_762636
  · exact context_11_23525_762735
  · exact context_11_23526_762831
  · exact context_11_23527_762890

theorem selected_cut_30221 : selected 9 ⟨762909, by decide⟩
    (prefixPartial 12 94112) = some ⟨12, 2, 0, 762909, 94112, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_94112_762909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94112 ⟨762909, by decide⟩ :=
  accepted_of_selected 12 94112 ⟨762909, by decide⟩ ⟨12, 2, 0, 762909, 94112, 1561, 65536⟩
    (by decide) selected_cut_30221

theorem selected_cut_30222 : selected 9 ⟨762925, by decide⟩
    (prefixPartial 12 94113) = some ⟨12, 2, 0, 762925, 94113, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_94113_762925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94113 ⟨762925, by decide⟩ :=
  accepted_of_selected 12 94113 ⟨762925, by decide⟩ ⟨12, 2, 0, 762925, 94113, 1373, 65536⟩
    (by decide) selected_cut_30222

theorem selected_cut_30223 : selected 9 ⟨762945, by decide⟩
    (prefixPartial 12 94114) = some ⟨12, 2, 0, 762945, 94114, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_94114_762945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94114 ⟨762945, by decide⟩ :=
  accepted_of_selected 12 94114 ⟨762945, by decide⟩ ⟨12, 2, 0, 762945, 94114, 1477, 65536⟩
    (by decide) selected_cut_30223

theorem selected_cut_30224 : selected 9 ⟨762967, by decide⟩
    (prefixPartial 12 94115) = some ⟨12, 2, 0, 762967, 94115, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_94115_762967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94115 ⟨762967, by decide⟩ :=
  accepted_of_selected 12 94115 ⟨762967, by decide⟩ ⟨12, 2, 0, 762967, 94115, 1437, 65536⟩
    (by decide) selected_cut_30224

theorem unmarked_context_11_23528_762968 : frontier 10 ⟨762968, by decide⟩
    (prefixCache 11 23528) (prefixPartial 11 23528) = false := by
  decide +kernel

theorem node_context_11_23528_762968 : EJMOriginalGlobalDAGData.nodes 10 ⟨762968, by decide⟩ =
    .split (coordinate 11) (![⟨762909, by decide⟩,⟨762925, by decide⟩,⟨762945, by decide⟩,⟨762967, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23528_762968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23528 ⟨762968, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23528
    ⟨762968, by decide⟩ (by decide) (![⟨762909, by decide⟩,⟨762925, by decide⟩,⟨762945, by decide⟩,⟨762967, by decide⟩]) unmarked_context_11_23528_762968 node_context_11_23528_762968
  intro a
  fin_cases a
  · exact context_12_94112_762909
  · exact context_12_94113_762925
  · exact context_12_94114_762945
  · exact context_12_94115_762967

theorem selected_cut_30225 : selected 9 ⟨762986, by decide⟩
    (prefixPartial 12 94116) = some ⟨12, 2, 0, 762986, 94116, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_94116_762986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94116 ⟨762986, by decide⟩ :=
  accepted_of_selected 12 94116 ⟨762986, by decide⟩ ⟨12, 2, 0, 762986, 94116, 1573, 65536⟩
    (by decide) selected_cut_30225

theorem selected_cut_30226 : selected 9 ⟨762998, by decide⟩
    (prefixPartial 12 94117) = some ⟨12, 2, 0, 762998, 94117, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_94117_762998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94117 ⟨762998, by decide⟩ :=
  accepted_of_selected 12 94117 ⟨762998, by decide⟩ ⟨12, 2, 0, 762998, 94117, 1233, 65536⟩
    (by decide) selected_cut_30226

theorem selected_cut_30227 : selected 9 ⟨763014, by decide⟩
    (prefixPartial 12 94118) = some ⟨12, 2, 0, 763014, 94118, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_94118_763014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94118 ⟨763014, by decide⟩ :=
  accepted_of_selected 12 94118 ⟨763014, by decide⟩ ⟨12, 2, 0, 763014, 94118, 1437, 65536⟩
    (by decide) selected_cut_30227

theorem selected_cut_30228 : selected 9 ⟨763031, by decide⟩
    (prefixPartial 12 94119) = some ⟨12, 2, 0, 763031, 94119, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_94119_763031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94119 ⟨763031, by decide⟩ :=
  accepted_of_selected 12 94119 ⟨763031, by decide⟩ ⟨12, 2, 0, 763031, 94119, 1429, 65536⟩
    (by decide) selected_cut_30228

theorem unmarked_context_11_23529_763032 : frontier 10 ⟨763032, by decide⟩
    (prefixCache 11 23529) (prefixPartial 11 23529) = false := by
  decide +kernel

theorem node_context_11_23529_763032 : EJMOriginalGlobalDAGData.nodes 10 ⟨763032, by decide⟩ =
    .split (coordinate 11) (![⟨762986, by decide⟩,⟨762998, by decide⟩,⟨763014, by decide⟩,⟨763031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23529_763032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23529 ⟨763032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23529
    ⟨763032, by decide⟩ (by decide) (![⟨762986, by decide⟩,⟨762998, by decide⟩,⟨763014, by decide⟩,⟨763031, by decide⟩]) unmarked_context_11_23529_763032 node_context_11_23529_763032
  intro a
  fin_cases a
  · exact context_12_94116_762986
  · exact context_12_94117_762998
  · exact context_12_94118_763014
  · exact context_12_94119_763031

theorem selected_cut_30229 : selected 9 ⟨763045, by decide⟩
    (prefixPartial 12 94120) = some ⟨12, 2, 0, 763045, 94120, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_94120_763045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94120 ⟨763045, by decide⟩ :=
  accepted_of_selected 12 94120 ⟨763045, by decide⟩ ⟨12, 2, 0, 763045, 94120, 1485, 65536⟩
    (by decide) selected_cut_30229

theorem selected_cut_30230 : selected 9 ⟨763059, by decide⟩
    (prefixPartial 12 94121) = some ⟨12, 2, 0, 763059, 94121, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_94121_763059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94121 ⟨763059, by decide⟩ :=
  accepted_of_selected 12 94121 ⟨763059, by decide⟩ ⟨12, 2, 0, 763059, 94121, 1237, 65536⟩
    (by decide) selected_cut_30230

theorem selected_cut_30231 : selected 9 ⟨763072, by decide⟩
    (prefixPartial 12 94122) = some ⟨12, 2, 0, 763072, 94122, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_94122_763072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94122 ⟨763072, by decide⟩ :=
  accepted_of_selected 12 94122 ⟨763072, by decide⟩ ⟨12, 2, 0, 763072, 94122, 1245, 65536⟩
    (by decide) selected_cut_30231

theorem selected_cut_30232 : selected 9 ⟨763091, by decide⟩
    (prefixPartial 12 94123) = some ⟨12, 2, 0, 763091, 94123, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_94123_763091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94123 ⟨763091, by decide⟩ :=
  accepted_of_selected 12 94123 ⟨763091, by decide⟩ ⟨12, 2, 0, 763091, 94123, 1293, 65536⟩
    (by decide) selected_cut_30232

theorem unmarked_context_11_23530_763092 : frontier 10 ⟨763092, by decide⟩
    (prefixCache 11 23530) (prefixPartial 11 23530) = false := by
  decide +kernel

theorem node_context_11_23530_763092 : EJMOriginalGlobalDAGData.nodes 10 ⟨763092, by decide⟩ =
    .split (coordinate 11) (![⟨763045, by decide⟩,⟨763059, by decide⟩,⟨763072, by decide⟩,⟨763091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23530_763092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23530 ⟨763092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23530
    ⟨763092, by decide⟩ (by decide) (![⟨763045, by decide⟩,⟨763059, by decide⟩,⟨763072, by decide⟩,⟨763091, by decide⟩]) unmarked_context_11_23530_763092 node_context_11_23530_763092
  intro a
  fin_cases a
  · exact context_12_94120_763045
  · exact context_12_94121_763059
  · exact context_12_94122_763072
  · exact context_12_94123_763091

theorem selected_cut_30233 : selected 10 ⟨763134, by decide⟩
    (prefixPartial 11 23531) = some ⟨11, 2, 0, 763134, 23531, 3085, 262144⟩ := by
  decide +kernel

theorem context_11_23531_763134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23531 ⟨763134, by decide⟩ :=
  accepted_of_selected 11 23531 ⟨763134, by decide⟩ ⟨11, 2, 0, 763134, 23531, 3085, 262144⟩
    (by decide) selected_cut_30233

theorem unmarked_context_10_5882_763135 : frontier 11 ⟨763135, by decide⟩
    (prefixCache 10 5882) (prefixPartial 10 5882) = false := by
  decide +kernel

theorem node_context_10_5882_763135 : EJMOriginalGlobalDAGData.nodes 11 ⟨763135, by decide⟩ =
    .split (coordinate 10) (![⟨762968, by decide⟩,⟨763032, by decide⟩,⟨763092, by decide⟩,⟨763134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5882_763135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5882 ⟨763135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5882
    ⟨763135, by decide⟩ (by decide) (![⟨762968, by decide⟩,⟨763032, by decide⟩,⟨763092, by decide⟩,⟨763134, by decide⟩]) unmarked_context_10_5882_763135 node_context_10_5882_763135
  intro a
  fin_cases a
  · exact context_11_23528_762968
  · exact context_11_23529_763032
  · exact context_11_23530_763092
  · exact context_11_23531_763134

theorem selected_cut_30234 : selected 9 ⟨763154, by decide⟩
    (prefixPartial 12 94128) = some ⟨12, 2, 0, 763154, 94128, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_94128_763154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94128 ⟨763154, by decide⟩ :=
  accepted_of_selected 12 94128 ⟨763154, by decide⟩ ⟨12, 2, 0, 763154, 94128, 1457, 65536⟩
    (by decide) selected_cut_30234

theorem selected_cut_30235 : selected 9 ⟨763170, by decide⟩
    (prefixPartial 12 94129) = some ⟨12, 2, 0, 763170, 94129, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_94129_763170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94129 ⟨763170, by decide⟩ :=
  accepted_of_selected 12 94129 ⟨763170, by decide⟩ ⟨12, 2, 0, 763170, 94129, 1189, 65536⟩
    (by decide) selected_cut_30235

theorem selected_cut_30236 : selected 9 ⟨763186, by decide⟩
    (prefixPartial 12 94130) = some ⟨12, 2, 0, 763186, 94130, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_94130_763186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94130 ⟨763186, by decide⟩ :=
  accepted_of_selected 12 94130 ⟨763186, by decide⟩ ⟨12, 2, 0, 763186, 94130, 1221, 65536⟩
    (by decide) selected_cut_30236

theorem selected_cut_30237 : selected 9 ⟨763199, by decide⟩
    (prefixPartial 12 94131) = some ⟨12, 2, 0, 763199, 94131, 1177, 65536⟩ := by
  decide +kernel

theorem context_12_94131_763199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94131 ⟨763199, by decide⟩ :=
  accepted_of_selected 12 94131 ⟨763199, by decide⟩ ⟨12, 2, 0, 763199, 94131, 1177, 65536⟩
    (by decide) selected_cut_30237

theorem unmarked_context_11_23532_763200 : frontier 10 ⟨763200, by decide⟩
    (prefixCache 11 23532) (prefixPartial 11 23532) = false := by
  decide +kernel

theorem node_context_11_23532_763200 : EJMOriginalGlobalDAGData.nodes 10 ⟨763200, by decide⟩ =
    .split (coordinate 11) (![⟨763154, by decide⟩,⟨763170, by decide⟩,⟨763186, by decide⟩,⟨763199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23532_763200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23532 ⟨763200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23532
    ⟨763200, by decide⟩ (by decide) (![⟨763154, by decide⟩,⟨763170, by decide⟩,⟨763186, by decide⟩,⟨763199, by decide⟩]) unmarked_context_11_23532_763200 node_context_11_23532_763200
  intro a
  fin_cases a
  · exact context_12_94128_763154
  · exact context_12_94129_763170
  · exact context_12_94130_763186
  · exact context_12_94131_763199

theorem selected_cut_30238 : selected 9 ⟨763216, by decide⟩
    (prefixPartial 12 94132) = some ⟨12, 2, 0, 763216, 94132, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_94132_763216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94132 ⟨763216, by decide⟩ :=
  accepted_of_selected 12 94132 ⟨763216, by decide⟩ ⟨12, 2, 0, 763216, 94132, 1289, 65536⟩
    (by decide) selected_cut_30238

theorem selected_cut_30239 : selected 9 ⟨763227, by decide⟩
    (prefixPartial 12 94133) = some ⟨12, 2, 0, 763227, 94133, 965, 65536⟩ := by
  decide +kernel

theorem context_12_94133_763227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94133 ⟨763227, by decide⟩ :=
  accepted_of_selected 12 94133 ⟨763227, by decide⟩ ⟨12, 2, 0, 763227, 94133, 965, 65536⟩
    (by decide) selected_cut_30239

theorem selected_cut_30240 : selected 9 ⟨763241, by decide⟩
    (prefixPartial 12 94134) = some ⟨12, 2, 0, 763241, 94134, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_94134_763241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94134 ⟨763241, by decide⟩ :=
  accepted_of_selected 12 94134 ⟨763241, by decide⟩ ⟨12, 2, 0, 763241, 94134, 1145, 65536⟩
    (by decide) selected_cut_30240

theorem selected_cut_30241 : selected 9 ⟨763253, by decide⟩
    (prefixPartial 12 94135) = some ⟨12, 2, 0, 763253, 94135, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_94135_763253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94135 ⟨763253, by decide⟩ :=
  accepted_of_selected 12 94135 ⟨763253, by decide⟩ ⟨12, 2, 0, 763253, 94135, 1109, 65536⟩
    (by decide) selected_cut_30241

theorem unmarked_context_11_23533_763254 : frontier 10 ⟨763254, by decide⟩
    (prefixCache 11 23533) (prefixPartial 11 23533) = false := by
  decide +kernel

theorem node_context_11_23533_763254 : EJMOriginalGlobalDAGData.nodes 10 ⟨763254, by decide⟩ =
    .split (coordinate 11) (![⟨763216, by decide⟩,⟨763227, by decide⟩,⟨763241, by decide⟩,⟨763253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23533_763254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23533 ⟨763254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23533
    ⟨763254, by decide⟩ (by decide) (![⟨763216, by decide⟩,⟨763227, by decide⟩,⟨763241, by decide⟩,⟨763253, by decide⟩]) unmarked_context_11_23533_763254 node_context_11_23533_763254
  intro a
  fin_cases a
  · exact context_12_94132_763216
  · exact context_12_94133_763227
  · exact context_12_94134_763241
  · exact context_12_94135_763253

theorem selected_cut_30242 : selected 9 ⟨763263, by decide⟩
    (prefixPartial 12 94136) = some ⟨12, 2, 0, 763263, 94136, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_94136_763263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94136 ⟨763263, by decide⟩ :=
  accepted_of_selected 12 94136 ⟨763263, by decide⟩ ⟨12, 2, 0, 763263, 94136, 1237, 65536⟩
    (by decide) selected_cut_30242

theorem selected_cut_30243 : selected 9 ⟨763273, by decide⟩
    (prefixPartial 12 94137) = some ⟨12, 2, 0, 763273, 94137, 1173, 65536⟩ := by
  decide +kernel

theorem context_12_94137_763273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94137 ⟨763273, by decide⟩ :=
  accepted_of_selected 12 94137 ⟨763273, by decide⟩ ⟨12, 2, 0, 763273, 94137, 1173, 65536⟩
    (by decide) selected_cut_30243

theorem selected_cut_30244 : selected 9 ⟨763285, by decide⟩
    (prefixPartial 12 94138) = some ⟨12, 2, 0, 763285, 94138, 1029, 65536⟩ := by
  decide +kernel

theorem context_12_94138_763285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94138 ⟨763285, by decide⟩ :=
  accepted_of_selected 12 94138 ⟨763285, by decide⟩ ⟨12, 2, 0, 763285, 94138, 1029, 65536⟩
    (by decide) selected_cut_30244

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
