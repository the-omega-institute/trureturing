/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover459
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_44162 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22085) = some ⟨10, 1, 0, 893098, 22085, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22085_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22085 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22085 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22085, 1, 1048576⟩
    (by decide) selected_cut_44162

theorem selected_cut_44163 : selected 10 ⟨1212745, by decide⟩
    (prefixPartial 11 88344) = some ⟨11, 2, 0, 1212745, 88344, 2977, 262144⟩ := by
  decide +kernel

theorem context_11_88344_1212745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88344 ⟨1212745, by decide⟩ :=
  accepted_of_selected 11 88344 ⟨1212745, by decide⟩ ⟨11, 2, 0, 1212745, 88344, 2977, 262144⟩
    (by decide) selected_cut_44163

theorem selected_cut_44164 : selected 10 ⟨1212804, by decide⟩
    (prefixPartial 11 88345) = some ⟨11, 2, 0, 1212804, 88345, 3513, 262144⟩ := by
  decide +kernel

theorem context_11_88345_1212804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88345 ⟨1212804, by decide⟩ :=
  accepted_of_selected 11 88345 ⟨1212804, by decide⟩ ⟨11, 2, 0, 1212804, 88345, 3513, 262144⟩
    (by decide) selected_cut_44164

theorem selected_cut_44165 : selected 10 ⟨1212858, by decide⟩
    (prefixPartial 11 88346) = some ⟨11, 2, 0, 1212858, 88346, 3069, 262144⟩ := by
  decide +kernel

theorem context_11_88346_1212858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88346 ⟨1212858, by decide⟩ :=
  accepted_of_selected 11 88346 ⟨1212858, by decide⟩ ⟨11, 2, 0, 1212858, 88346, 3069, 262144⟩
    (by decide) selected_cut_44165

theorem selected_cut_44166 : selected 9 ⟨1212879, by decide⟩
    (prefixPartial 12 353388) = some ⟨12, 2, 0, 1212879, 353388, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_353388_1212879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353388 ⟨1212879, by decide⟩ :=
  accepted_of_selected 12 353388 ⟨1212879, by decide⟩ ⟨12, 2, 0, 1212879, 353388, 1409, 65536⟩
    (by decide) selected_cut_44166

theorem selected_cut_44167 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353389) = some ⟨12, 1, 0, 896706, 353389, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353389_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353389 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353389 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353389, 1, 65536⟩
    (by decide) selected_cut_44167

theorem selected_cut_44168 : selected 9 ⟨1212904, by decide⟩
    (prefixPartial 12 353390) = some ⟨12, 2, 0, 1212904, 353390, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_353390_1212904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353390 ⟨1212904, by decide⟩ :=
  accepted_of_selected 12 353390 ⟨1212904, by decide⟩ ⟨12, 2, 0, 1212904, 353390, 1561, 65536⟩
    (by decide) selected_cut_44168

theorem selected_cut_44169 : selected 9 ⟨1212931, by decide⟩
    (prefixPartial 12 353391) = some ⟨12, 2, 0, 1212931, 353391, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_353391_1212931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353391 ⟨1212931, by decide⟩ :=
  accepted_of_selected 12 353391 ⟨1212931, by decide⟩ ⟨12, 2, 0, 1212931, 353391, 1497, 65536⟩
    (by decide) selected_cut_44169

theorem unmarked_context_11_88347_1212932 : frontier 10 ⟨1212932, by decide⟩
    (prefixCache 11 88347) (prefixPartial 11 88347) = false := by
  decide +kernel

theorem node_context_11_88347_1212932 : EJMOriginalGlobalDAGData.nodes 10 ⟨1212932, by decide⟩ =
    .split (coordinate 11) (![⟨1212879, by decide⟩,⟨896706, by decide⟩,⟨1212904, by decide⟩,⟨1212931, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88347_1212932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88347 ⟨1212932, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88347
    ⟨1212932, by decide⟩ (by decide) (![⟨1212879, by decide⟩,⟨896706, by decide⟩,⟨1212904, by decide⟩,⟨1212931, by decide⟩]) unmarked_context_11_88347_1212932 node_context_11_88347_1212932
  intro a
  fin_cases a
  · exact context_12_353388_1212879
  · exact context_12_353389_896706
  · exact context_12_353390_1212904
  · exact context_12_353391_1212931

theorem unmarked_context_10_22086_1212933 : frontier 11 ⟨1212933, by decide⟩
    (prefixCache 10 22086) (prefixPartial 10 22086) = false := by
  decide +kernel

theorem node_context_10_22086_1212933 : EJMOriginalGlobalDAGData.nodes 11 ⟨1212933, by decide⟩ =
    .split (coordinate 10) (![⟨1212745, by decide⟩,⟨1212804, by decide⟩,⟨1212858, by decide⟩,⟨1212932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22086_1212933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22086 ⟨1212933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22086
    ⟨1212933, by decide⟩ (by decide) (![⟨1212745, by decide⟩,⟨1212804, by decide⟩,⟨1212858, by decide⟩,⟨1212932, by decide⟩]) unmarked_context_10_22086_1212933 node_context_10_22086_1212933
  intro a
  fin_cases a
  · exact context_11_88344_1212745
  · exact context_11_88345_1212804
  · exact context_11_88346_1212858
  · exact context_11_88347_1212932

theorem selected_cut_44170 : selected 10 ⟨1212983, by decide⟩
    (prefixPartial 11 88348) = some ⟨11, 2, 0, 1212983, 88348, 2893, 262144⟩ := by
  decide +kernel

theorem context_11_88348_1212983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88348 ⟨1212983, by decide⟩ :=
  accepted_of_selected 11 88348 ⟨1212983, by decide⟩ ⟨11, 2, 0, 1212983, 88348, 2893, 262144⟩
    (by decide) selected_cut_44170

theorem selected_cut_44171 : selected 10 ⟨1213036, by decide⟩
    (prefixPartial 11 88349) = some ⟨11, 2, 0, 1213036, 88349, 3269, 262144⟩ := by
  decide +kernel

theorem context_11_88349_1213036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88349 ⟨1213036, by decide⟩ :=
  accepted_of_selected 11 88349 ⟨1213036, by decide⟩ ⟨11, 2, 0, 1213036, 88349, 3269, 262144⟩
    (by decide) selected_cut_44171

theorem selected_cut_44172 : selected 9 ⟨1213063, by decide⟩
    (prefixPartial 12 353400) = some ⟨12, 2, 0, 1213063, 353400, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_353400_1213063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353400 ⟨1213063, by decide⟩ :=
  accepted_of_selected 12 353400 ⟨1213063, by decide⟩ ⟨12, 2, 0, 1213063, 353400, 1373, 65536⟩
    (by decide) selected_cut_44172

theorem selected_cut_44173 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353401) = some ⟨12, 1, 0, 896706, 353401, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353401_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353401 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353401 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353401, 1, 65536⟩
    (by decide) selected_cut_44173

theorem selected_cut_44174 : selected 9 ⟨1213089, by decide⟩
    (prefixPartial 12 353402) = some ⟨12, 2, 0, 1213089, 353402, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_353402_1213089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353402 ⟨1213089, by decide⟩ :=
  accepted_of_selected 12 353402 ⟨1213089, by decide⟩ ⟨12, 2, 0, 1213089, 353402, 1389, 65536⟩
    (by decide) selected_cut_44174

theorem selected_cut_44175 : selected 9 ⟨1213116, by decide⟩
    (prefixPartial 12 353403) = some ⟨12, 2, 0, 1213116, 353403, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_353403_1213116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353403 ⟨1213116, by decide⟩ :=
  accepted_of_selected 12 353403 ⟨1213116, by decide⟩ ⟨12, 2, 0, 1213116, 353403, 1409, 65536⟩
    (by decide) selected_cut_44175

theorem unmarked_context_11_88350_1213117 : frontier 10 ⟨1213117, by decide⟩
    (prefixCache 11 88350) (prefixPartial 11 88350) = false := by
  decide +kernel

theorem node_context_11_88350_1213117 : EJMOriginalGlobalDAGData.nodes 10 ⟨1213117, by decide⟩ =
    .split (coordinate 11) (![⟨1213063, by decide⟩,⟨896706, by decide⟩,⟨1213089, by decide⟩,⟨1213116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88350_1213117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88350 ⟨1213117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88350
    ⟨1213117, by decide⟩ (by decide) (![⟨1213063, by decide⟩,⟨896706, by decide⟩,⟨1213089, by decide⟩,⟨1213116, by decide⟩]) unmarked_context_11_88350_1213117 node_context_11_88350_1213117
  intro a
  fin_cases a
  · exact context_12_353400_1213063
  · exact context_12_353401_896706
  · exact context_12_353402_1213089
  · exact context_12_353403_1213116

theorem selected_cut_44176 : selected 10 ⟨1213160, by decide⟩
    (prefixPartial 11 88351) = some ⟨11, 2, 0, 1213160, 88351, 2501, 262144⟩ := by
  decide +kernel

theorem context_11_88351_1213160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88351 ⟨1213160, by decide⟩ :=
  accepted_of_selected 11 88351 ⟨1213160, by decide⟩ ⟨11, 2, 0, 1213160, 88351, 2501, 262144⟩
    (by decide) selected_cut_44176

theorem unmarked_context_10_22087_1213161 : frontier 11 ⟨1213161, by decide⟩
    (prefixCache 10 22087) (prefixPartial 10 22087) = false := by
  decide +kernel

theorem node_context_10_22087_1213161 : EJMOriginalGlobalDAGData.nodes 11 ⟨1213161, by decide⟩ =
    .split (coordinate 10) (![⟨1212983, by decide⟩,⟨1213036, by decide⟩,⟨1213117, by decide⟩,⟨1213160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22087_1213161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22087 ⟨1213161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22087
    ⟨1213161, by decide⟩ (by decide) (![⟨1212983, by decide⟩,⟨1213036, by decide⟩,⟨1213117, by decide⟩,⟨1213160, by decide⟩]) unmarked_context_10_22087_1213161 node_context_10_22087_1213161
  intro a
  fin_cases a
  · exact context_11_88348_1212983
  · exact context_11_88349_1213036
  · exact context_11_88350_1213117
  · exact context_11_88351_1213160

theorem unmarked_context_9_5521_1213162 : frontier 12 ⟨1213162, by decide⟩
    (prefixCache 9 5521) (prefixPartial 9 5521) = false := by
  decide +kernel

theorem node_context_9_5521_1213162 : EJMOriginalGlobalDAGData.nodes 12 ⟨1213162, by decide⟩ =
    .split (coordinate 9) (![⟨1212699, by decide⟩,⟨893098, by decide⟩,⟨1212933, by decide⟩,⟨1213161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5521_1213162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5521 ⟨1213162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5521
    ⟨1213162, by decide⟩ (by decide) (![⟨1212699, by decide⟩,⟨893098, by decide⟩,⟨1212933, by decide⟩,⟨1213161, by decide⟩]) unmarked_context_9_5521_1213162 node_context_9_5521_1213162
  intro a
  fin_cases a
  · exact context_10_22084_1212699
  · exact context_10_22085_893098
  · exact context_10_22086_1212933
  · exact context_10_22087_1213161

theorem selected_cut_44177 : selected 10 ⟨1213198, by decide⟩
    (prefixPartial 11 88352) = some ⟨11, 2, 0, 1213198, 88352, 2353, 262144⟩ := by
  decide +kernel

theorem context_11_88352_1213198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88352 ⟨1213198, by decide⟩ :=
  accepted_of_selected 11 88352 ⟨1213198, by decide⟩ ⟨11, 2, 0, 1213198, 88352, 2353, 262144⟩
    (by decide) selected_cut_44177

theorem selected_cut_44178 : selected 10 ⟨1213239, by decide⟩
    (prefixPartial 11 88353) = some ⟨11, 2, 0, 1213239, 88353, 3373, 262144⟩ := by
  decide +kernel

theorem context_11_88353_1213239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88353 ⟨1213239, by decide⟩ :=
  accepted_of_selected 11 88353 ⟨1213239, by decide⟩ ⟨11, 2, 0, 1213239, 88353, 3373, 262144⟩
    (by decide) selected_cut_44178

theorem selected_cut_44179 : selected 10 ⟨1213299, by decide⟩
    (prefixPartial 11 88354) = some ⟨11, 2, 0, 1213299, 88354, 3733, 262144⟩ := by
  decide +kernel

theorem context_11_88354_1213299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88354 ⟨1213299, by decide⟩ :=
  accepted_of_selected 11 88354 ⟨1213299, by decide⟩ ⟨11, 2, 0, 1213299, 88354, 3733, 262144⟩
    (by decide) selected_cut_44179

theorem selected_cut_44180 : selected 9 ⟨1213312, by decide⟩
    (prefixPartial 12 353420) = some ⟨12, 2, 0, 1213312, 353420, 961, 65536⟩ := by
  decide +kernel

theorem context_12_353420_1213312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353420 ⟨1213312, by decide⟩ :=
  accepted_of_selected 12 353420 ⟨1213312, by decide⟩ ⟨12, 2, 0, 1213312, 353420, 961, 65536⟩
    (by decide) selected_cut_44180

theorem selected_cut_44181 : selected 9 ⟨1213324, by decide⟩
    (prefixPartial 12 353421) = some ⟨12, 2, 0, 1213324, 353421, 917, 65536⟩ := by
  decide +kernel

theorem context_12_353421_1213324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353421 ⟨1213324, by decide⟩ :=
  accepted_of_selected 12 353421 ⟨1213324, by decide⟩ ⟨12, 2, 0, 1213324, 353421, 917, 65536⟩
    (by decide) selected_cut_44181

theorem selected_cut_44182 : selected 9 ⟨1213338, by decide⟩
    (prefixPartial 12 353422) = some ⟨12, 2, 0, 1213338, 353422, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_353422_1213338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353422 ⟨1213338, by decide⟩ :=
  accepted_of_selected 12 353422 ⟨1213338, by decide⟩ ⟨12, 2, 0, 1213338, 353422, 1097, 65536⟩
    (by decide) selected_cut_44182

theorem selected_cut_44183 : selected 9 ⟨1213353, by decide⟩
    (prefixPartial 12 353423) = some ⟨12, 2, 0, 1213353, 353423, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_353423_1213353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353423 ⟨1213353, by decide⟩ :=
  accepted_of_selected 12 353423 ⟨1213353, by decide⟩ ⟨12, 2, 0, 1213353, 353423, 1125, 65536⟩
    (by decide) selected_cut_44183

theorem unmarked_context_11_88355_1213354 : frontier 10 ⟨1213354, by decide⟩
    (prefixCache 11 88355) (prefixPartial 11 88355) = false := by
  decide +kernel

theorem node_context_11_88355_1213354 : EJMOriginalGlobalDAGData.nodes 10 ⟨1213354, by decide⟩ =
    .split (coordinate 11) (![⟨1213312, by decide⟩,⟨1213324, by decide⟩,⟨1213338, by decide⟩,⟨1213353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88355_1213354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88355 ⟨1213354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88355
    ⟨1213354, by decide⟩ (by decide) (![⟨1213312, by decide⟩,⟨1213324, by decide⟩,⟨1213338, by decide⟩,⟨1213353, by decide⟩]) unmarked_context_11_88355_1213354 node_context_11_88355_1213354
  intro a
  fin_cases a
  · exact context_12_353420_1213312
  · exact context_12_353421_1213324
  · exact context_12_353422_1213338
  · exact context_12_353423_1213353

theorem unmarked_context_10_22088_1213355 : frontier 11 ⟨1213355, by decide⟩
    (prefixCache 10 22088) (prefixPartial 10 22088) = false := by
  decide +kernel

theorem node_context_10_22088_1213355 : EJMOriginalGlobalDAGData.nodes 11 ⟨1213355, by decide⟩ =
    .split (coordinate 10) (![⟨1213198, by decide⟩,⟨1213239, by decide⟩,⟨1213299, by decide⟩,⟨1213354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22088_1213355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22088 ⟨1213355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22088
    ⟨1213355, by decide⟩ (by decide) (![⟨1213198, by decide⟩,⟨1213239, by decide⟩,⟨1213299, by decide⟩,⟨1213354, by decide⟩]) unmarked_context_10_22088_1213355 node_context_10_22088_1213355
  intro a
  fin_cases a
  · exact context_11_88352_1213198
  · exact context_11_88353_1213239
  · exact context_11_88354_1213299
  · exact context_11_88355_1213354

theorem selected_cut_44184 : selected 10 ⟨1213392, by decide⟩
    (prefixPartial 11 88356) = some ⟨11, 2, 0, 1213392, 88356, 2725, 262144⟩ := by
  decide +kernel

theorem context_11_88356_1213392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88356 ⟨1213392, by decide⟩ :=
  accepted_of_selected 11 88356 ⟨1213392, by decide⟩ ⟨11, 2, 0, 1213392, 88356, 2725, 262144⟩
    (by decide) selected_cut_44184

theorem selected_cut_44185 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 88357) = some ⟨11, 1, 0, 892405, 88357, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88357_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88357 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 88357 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 88357, 1, 262144⟩
    (by decide) selected_cut_44185

theorem selected_cut_44186 : selected 10 ⟨1213438, by decide⟩
    (prefixPartial 11 88358) = some ⟨11, 2, 0, 1213438, 88358, 2989, 262144⟩ := by
  decide +kernel

theorem context_11_88358_1213438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88358 ⟨1213438, by decide⟩ :=
  accepted_of_selected 11 88358 ⟨1213438, by decide⟩ ⟨11, 2, 0, 1213438, 88358, 2989, 262144⟩
    (by decide) selected_cut_44186

theorem selected_cut_44187 : selected 10 ⟨1213477, by decide⟩
    (prefixPartial 11 88359) = some ⟨11, 2, 0, 1213477, 88359, 3261, 262144⟩ := by
  decide +kernel

theorem context_11_88359_1213477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88359 ⟨1213477, by decide⟩ :=
  accepted_of_selected 11 88359 ⟨1213477, by decide⟩ ⟨11, 2, 0, 1213477, 88359, 3261, 262144⟩
    (by decide) selected_cut_44187

theorem unmarked_context_10_22089_1213478 : frontier 11 ⟨1213478, by decide⟩
    (prefixCache 10 22089) (prefixPartial 10 22089) = false := by
  decide +kernel

theorem node_context_10_22089_1213478 : EJMOriginalGlobalDAGData.nodes 11 ⟨1213478, by decide⟩ =
    .split (coordinate 10) (![⟨1213392, by decide⟩,⟨892405, by decide⟩,⟨1213438, by decide⟩,⟨1213477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22089_1213478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22089 ⟨1213478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22089
    ⟨1213478, by decide⟩ (by decide) (![⟨1213392, by decide⟩,⟨892405, by decide⟩,⟨1213438, by decide⟩,⟨1213477, by decide⟩]) unmarked_context_10_22089_1213478 node_context_10_22089_1213478
  intro a
  fin_cases a
  · exact context_11_88356_1213392
  · exact context_11_88357_892405
  · exact context_11_88358_1213438
  · exact context_11_88359_1213477

theorem selected_cut_44188 : selected 10 ⟨1213501, by decide⟩
    (prefixPartial 11 88360) = some ⟨11, 2, 0, 1213501, 88360, 1517, 262144⟩ := by
  decide +kernel

theorem context_11_88360_1213501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88360 ⟨1213501, by decide⟩ :=
  accepted_of_selected 11 88360 ⟨1213501, by decide⟩ ⟨11, 2, 0, 1213501, 88360, 1517, 262144⟩
    (by decide) selected_cut_44188

theorem selected_cut_44189 : selected 10 ⟨1213522, by decide⟩
    (prefixPartial 11 88361) = some ⟨11, 2, 0, 1213522, 88361, 1477, 262144⟩ := by
  decide +kernel

theorem context_11_88361_1213522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88361 ⟨1213522, by decide⟩ :=
  accepted_of_selected 11 88361 ⟨1213522, by decide⟩ ⟨11, 2, 0, 1213522, 88361, 1477, 262144⟩
    (by decide) selected_cut_44189

theorem selected_cut_44190 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 88362) = some ⟨11, 1, 0, 1109453, 88362, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88362_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88362 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 88362 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 88362, 1, 262144⟩
    (by decide) selected_cut_44190

theorem selected_cut_44191 : selected 10 ⟨1213550, by decide⟩
    (prefixPartial 11 88363) = some ⟨11, 2, 0, 1213550, 88363, 2249, 262144⟩ := by
  decide +kernel

theorem context_11_88363_1213550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88363 ⟨1213550, by decide⟩ :=
  accepted_of_selected 11 88363 ⟨1213550, by decide⟩ ⟨11, 2, 0, 1213550, 88363, 2249, 262144⟩
    (by decide) selected_cut_44191

theorem unmarked_context_10_22090_1213551 : frontier 11 ⟨1213551, by decide⟩
    (prefixCache 10 22090) (prefixPartial 10 22090) = false := by
  decide +kernel

theorem node_context_10_22090_1213551 : EJMOriginalGlobalDAGData.nodes 11 ⟨1213551, by decide⟩ =
    .split (coordinate 10) (![⟨1213501, by decide⟩,⟨1213522, by decide⟩,⟨1109453, by decide⟩,⟨1213550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22090_1213551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22090 ⟨1213551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22090
    ⟨1213551, by decide⟩ (by decide) (![⟨1213501, by decide⟩,⟨1213522, by decide⟩,⟨1109453, by decide⟩,⟨1213550, by decide⟩]) unmarked_context_10_22090_1213551 node_context_10_22090_1213551
  intro a
  fin_cases a
  · exact context_11_88360_1213501
  · exact context_11_88361_1213522
  · exact context_11_88362_1109453
  · exact context_11_88363_1213550

theorem selected_cut_44192 : selected 10 ⟨1213584, by decide⟩
    (prefixPartial 11 88364) = some ⟨11, 2, 0, 1213584, 88364, 2049, 262144⟩ := by
  decide +kernel

theorem context_11_88364_1213584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88364 ⟨1213584, by decide⟩ :=
  accepted_of_selected 11 88364 ⟨1213584, by decide⟩ ⟨11, 2, 0, 1213584, 88364, 2049, 262144⟩
    (by decide) selected_cut_44192

theorem selected_cut_44193 : selected 10 ⟨1213615, by decide⟩
    (prefixPartial 11 88365) = some ⟨11, 2, 0, 1213615, 88365, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_88365_1213615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88365 ⟨1213615, by decide⟩ :=
  accepted_of_selected 11 88365 ⟨1213615, by decide⟩ ⟨11, 2, 0, 1213615, 88365, 2173, 262144⟩
    (by decide) selected_cut_44193

theorem selected_cut_44194 : selected 10 ⟨1213645, by decide⟩
    (prefixPartial 11 88366) = some ⟨11, 2, 0, 1213645, 88366, 1849, 262144⟩ := by
  decide +kernel

theorem context_11_88366_1213645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88366 ⟨1213645, by decide⟩ :=
  accepted_of_selected 11 88366 ⟨1213645, by decide⟩ ⟨11, 2, 0, 1213645, 88366, 1849, 262144⟩
    (by decide) selected_cut_44194

theorem selected_cut_44195 : selected 10 ⟨1213662, by decide⟩
    (prefixPartial 11 88367) = some ⟨11, 2, 0, 1213662, 88367, 1425, 262144⟩ := by
  decide +kernel

theorem context_11_88367_1213662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88367 ⟨1213662, by decide⟩ :=
  accepted_of_selected 11 88367 ⟨1213662, by decide⟩ ⟨11, 2, 0, 1213662, 88367, 1425, 262144⟩
    (by decide) selected_cut_44195

theorem unmarked_context_10_22091_1213663 : frontier 11 ⟨1213663, by decide⟩
    (prefixCache 10 22091) (prefixPartial 10 22091) = false := by
  decide +kernel

theorem node_context_10_22091_1213663 : EJMOriginalGlobalDAGData.nodes 11 ⟨1213663, by decide⟩ =
    .split (coordinate 10) (![⟨1213584, by decide⟩,⟨1213615, by decide⟩,⟨1213645, by decide⟩,⟨1213662, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22091_1213663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22091 ⟨1213663, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22091
    ⟨1213663, by decide⟩ (by decide) (![⟨1213584, by decide⟩,⟨1213615, by decide⟩,⟨1213645, by decide⟩,⟨1213662, by decide⟩]) unmarked_context_10_22091_1213663 node_context_10_22091_1213663
  intro a
  fin_cases a
  · exact context_11_88364_1213584
  · exact context_11_88365_1213615
  · exact context_11_88366_1213645
  · exact context_11_88367_1213662

theorem unmarked_context_9_5522_1213664 : frontier 12 ⟨1213664, by decide⟩
    (prefixCache 9 5522) (prefixPartial 9 5522) = false := by
  decide +kernel

theorem node_context_9_5522_1213664 : EJMOriginalGlobalDAGData.nodes 12 ⟨1213664, by decide⟩ =
    .split (coordinate 9) (![⟨1213355, by decide⟩,⟨1213478, by decide⟩,⟨1213551, by decide⟩,⟨1213663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5522_1213664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5522 ⟨1213664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5522
    ⟨1213664, by decide⟩ (by decide) (![⟨1213355, by decide⟩,⟨1213478, by decide⟩,⟨1213551, by decide⟩,⟨1213663, by decide⟩]) unmarked_context_9_5522_1213664 node_context_9_5522_1213664
  intro a
  fin_cases a
  · exact context_10_22088_1213355
  · exact context_10_22089_1213478
  · exact context_10_22090_1213551
  · exact context_10_22091_1213663

theorem selected_cut_44196 : selected 10 ⟨1213674, by decide⟩
    (prefixPartial 11 88368) = some ⟨11, 2, 0, 1213674, 88368, 937, 262144⟩ := by
  decide +kernel

theorem context_11_88368_1213674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88368 ⟨1213674, by decide⟩ :=
  accepted_of_selected 11 88368 ⟨1213674, by decide⟩ ⟨11, 2, 0, 1213674, 88368, 937, 262144⟩
    (by decide) selected_cut_44196

theorem selected_cut_44197 : selected 10 ⟨1213687, by decide⟩
    (prefixPartial 11 88369) = some ⟨11, 2, 0, 1213687, 88369, 1221, 262144⟩ := by
  decide +kernel

theorem context_11_88369_1213687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88369 ⟨1213687, by decide⟩ :=
  accepted_of_selected 11 88369 ⟨1213687, by decide⟩ ⟨11, 2, 0, 1213687, 88369, 1221, 262144⟩
    (by decide) selected_cut_44197

theorem selected_cut_44198 : selected 10 ⟨1213708, by decide⟩
    (prefixPartial 11 88370) = some ⟨11, 2, 0, 1213708, 88370, 1593, 262144⟩ := by
  decide +kernel

theorem context_11_88370_1213708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88370 ⟨1213708, by decide⟩ :=
  accepted_of_selected 11 88370 ⟨1213708, by decide⟩ ⟨11, 2, 0, 1213708, 88370, 1593, 262144⟩
    (by decide) selected_cut_44198

theorem selected_cut_44199 : selected 10 ⟨1213730, by decide⟩
    (prefixPartial 11 88371) = some ⟨11, 2, 0, 1213730, 88371, 1201, 262144⟩ := by
  decide +kernel

theorem context_11_88371_1213730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88371 ⟨1213730, by decide⟩ :=
  accepted_of_selected 11 88371 ⟨1213730, by decide⟩ ⟨11, 2, 0, 1213730, 88371, 1201, 262144⟩
    (by decide) selected_cut_44199

theorem unmarked_context_10_22092_1213731 : frontier 11 ⟨1213731, by decide⟩
    (prefixCache 10 22092) (prefixPartial 10 22092) = false := by
  decide +kernel

theorem node_context_10_22092_1213731 : EJMOriginalGlobalDAGData.nodes 11 ⟨1213731, by decide⟩ =
    .split (coordinate 10) (![⟨1213674, by decide⟩,⟨1213687, by decide⟩,⟨1213708, by decide⟩,⟨1213730, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22092_1213731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22092 ⟨1213731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22092
    ⟨1213731, by decide⟩ (by decide) (![⟨1213674, by decide⟩,⟨1213687, by decide⟩,⟨1213708, by decide⟩,⟨1213730, by decide⟩]) unmarked_context_10_22092_1213731 node_context_10_22092_1213731
  intro a
  fin_cases a
  · exact context_11_88368_1213674
  · exact context_11_88369_1213687
  · exact context_11_88370_1213708
  · exact context_11_88371_1213730

theorem selected_cut_44200 : selected 11 ⟨1213771, by decide⟩
    (prefixPartial 10 22093) = some ⟨10, 2, 0, 1213771, 22093, 2701, 1048576⟩ := by
  decide +kernel

theorem context_10_22093_1213771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22093 ⟨1213771, by decide⟩ :=
  accepted_of_selected 10 22093 ⟨1213771, by decide⟩ ⟨10, 2, 0, 1213771, 22093, 2701, 1048576⟩
    (by decide) selected_cut_44200

theorem selected_cut_44201 : selected 11 ⟨1213818, by decide⟩
    (prefixPartial 10 22094) = some ⟨10, 2, 0, 1213818, 22094, 1953, 1048576⟩ := by
  decide +kernel

theorem context_10_22094_1213818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22094 ⟨1213818, by decide⟩ :=
  accepted_of_selected 10 22094 ⟨1213818, by decide⟩ ⟨10, 2, 0, 1213818, 22094, 1953, 1048576⟩
    (by decide) selected_cut_44201

theorem selected_cut_44202 : selected 11 ⟨1213831, by decide⟩
    (prefixPartial 10 22095) = some ⟨10, 2, 0, 1213831, 22095, 365, 1048576⟩ := by
  decide +kernel

theorem context_10_22095_1213831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22095 ⟨1213831, by decide⟩ :=
  accepted_of_selected 10 22095 ⟨1213831, by decide⟩ ⟨10, 2, 0, 1213831, 22095, 365, 1048576⟩
    (by decide) selected_cut_44202

theorem unmarked_context_9_5523_1213832 : frontier 12 ⟨1213832, by decide⟩
    (prefixCache 9 5523) (prefixPartial 9 5523) = false := by
  decide +kernel

theorem node_context_9_5523_1213832 : EJMOriginalGlobalDAGData.nodes 12 ⟨1213832, by decide⟩ =
    .split (coordinate 9) (![⟨1213731, by decide⟩,⟨1213771, by decide⟩,⟨1213818, by decide⟩,⟨1213831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5523_1213832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5523 ⟨1213832, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5523
    ⟨1213832, by decide⟩ (by decide) (![⟨1213731, by decide⟩,⟨1213771, by decide⟩,⟨1213818, by decide⟩,⟨1213831, by decide⟩]) unmarked_context_9_5523_1213832 node_context_9_5523_1213832
  intro a
  fin_cases a
  · exact context_10_22092_1213731
  · exact context_10_22093_1213771
  · exact context_10_22094_1213818
  · exact context_10_22095_1213831

theorem unmarked_context_8_1380_1213833 : frontier 13 ⟨1213833, by decide⟩
    (prefixCache 8 1380) (prefixPartial 8 1380) = false := by
  decide +kernel

theorem node_context_8_1380_1213833 : EJMOriginalGlobalDAGData.nodes 13 ⟨1213833, by decide⟩ =
    .split (coordinate 8) (![⟨1212424, by decide⟩,⟨1213162, by decide⟩,⟨1213664, by decide⟩,⟨1213832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1380_1213833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1380 ⟨1213833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1380
    ⟨1213833, by decide⟩ (by decide) (![⟨1212424, by decide⟩,⟨1213162, by decide⟩,⟨1213664, by decide⟩,⟨1213832, by decide⟩]) unmarked_context_8_1380_1213833 node_context_8_1380_1213833
  intro a
  fin_cases a
  · exact context_9_5520_1212424
  · exact context_9_5521_1213162
  · exact context_9_5522_1213664
  · exact context_9_5523_1213832

theorem selected_cut_44203 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88384) = some ⟨11, 1, 0, 434745, 88384, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88384_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88384 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88384 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88384, 1, 262144⟩
    (by decide) selected_cut_44203

theorem selected_cut_44204 : selected 10 ⟨1213913, by decide⟩
    (prefixPartial 11 88385) = some ⟨11, 2, 0, 1213913, 88385, 3113, 262144⟩ := by
  decide +kernel

theorem context_11_88385_1213913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88385 ⟨1213913, by decide⟩ :=
  accepted_of_selected 11 88385 ⟨1213913, by decide⟩ ⟨11, 2, 0, 1213913, 88385, 3113, 262144⟩
    (by decide) selected_cut_44204

theorem selected_cut_44205 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 353544) = some ⟨12, 1, 0, 448748, 353544, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353544_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353544 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 353544 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 353544, 1, 65536⟩
    (by decide) selected_cut_44205

theorem selected_cut_44206 : selected 9 ⟨1213962, by decide⟩
    (prefixPartial 12 353545) = some ⟨12, 2, 0, 1213962, 353545, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_353545_1213962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353545 ⟨1213962, by decide⟩ :=
  accepted_of_selected 12 353545 ⟨1213962, by decide⟩ ⟨12, 2, 0, 1213962, 353545, 2797, 65536⟩
    (by decide) selected_cut_44206

theorem selected_cut_44207 : selected 9 ⟨1214028, by decide⟩
    (prefixPartial 12 353546) = some ⟨12, 2, 0, 1214028, 353546, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_353546_1214028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353546 ⟨1214028, by decide⟩ :=
  accepted_of_selected 12 353546 ⟨1214028, by decide⟩ ⟨12, 2, 0, 1214028, 353546, 3089, 65536⟩
    (by decide) selected_cut_44207

theorem selected_cut_44208 : selected 9 ⟨1214091, by decide⟩
    (prefixPartial 12 353547) = some ⟨12, 2, 0, 1214091, 353547, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_353547_1214091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353547 ⟨1214091, by decide⟩ :=
  accepted_of_selected 12 353547 ⟨1214091, by decide⟩ ⟨12, 2, 0, 1214091, 353547, 3337, 65536⟩
    (by decide) selected_cut_44208

theorem unmarked_context_11_88386_1214092 : frontier 10 ⟨1214092, by decide⟩
    (prefixCache 11 88386) (prefixPartial 11 88386) = false := by
  decide +kernel

theorem node_context_11_88386_1214092 : EJMOriginalGlobalDAGData.nodes 10 ⟨1214092, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1213962, by decide⟩,⟨1214028, by decide⟩,⟨1214091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88386_1214092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88386 ⟨1214092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88386
    ⟨1214092, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1213962, by decide⟩,⟨1214028, by decide⟩,⟨1214091, by decide⟩]) unmarked_context_11_88386_1214092 node_context_11_88386_1214092
  intro a
  fin_cases a
  · exact context_12_353544_448748
  · exact context_12_353545_1213962
  · exact context_12_353546_1214028
  · exact context_12_353547_1214091

theorem selected_cut_44209 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 353548) = some ⟨12, 1, 0, 448748, 353548, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353548_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353548 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 353548 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 353548, 1, 65536⟩
    (by decide) selected_cut_44209

theorem selected_cut_44210 : selected 9 ⟨1214111, by decide⟩
    (prefixPartial 12 353549) = some ⟨12, 2, 0, 1214111, 353549, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_353549_1214111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353549 ⟨1214111, by decide⟩ :=
  accepted_of_selected 12 353549 ⟨1214111, by decide⟩ ⟨12, 2, 0, 1214111, 353549, 1317, 65536⟩
    (by decide) selected_cut_44210

theorem selected_cut_44211 : selected 9 ⟨1214162, by decide⟩
    (prefixPartial 12 353550) = some ⟨12, 2, 0, 1214162, 353550, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_353550_1214162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353550 ⟨1214162, by decide⟩ :=
  accepted_of_selected 12 353550 ⟨1214162, by decide⟩ ⟨12, 2, 0, 1214162, 353550, 2857, 65536⟩
    (by decide) selected_cut_44211

theorem selected_cut_44212 : selected 9 ⟨1214220, by decide⟩
    (prefixPartial 12 353551) = some ⟨12, 2, 0, 1214220, 353551, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_353551_1214220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353551 ⟨1214220, by decide⟩ :=
  accepted_of_selected 12 353551 ⟨1214220, by decide⟩ ⟨12, 2, 0, 1214220, 353551, 3161, 65536⟩
    (by decide) selected_cut_44212

theorem unmarked_context_11_88387_1214221 : frontier 10 ⟨1214221, by decide⟩
    (prefixCache 11 88387) (prefixPartial 11 88387) = false := by
  decide +kernel

theorem node_context_11_88387_1214221 : EJMOriginalGlobalDAGData.nodes 10 ⟨1214221, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1214111, by decide⟩,⟨1214162, by decide⟩,⟨1214220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88387_1214221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88387 ⟨1214221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88387
    ⟨1214221, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1214111, by decide⟩,⟨1214162, by decide⟩,⟨1214220, by decide⟩]) unmarked_context_11_88387_1214221 node_context_11_88387_1214221
  intro a
  fin_cases a
  · exact context_12_353548_448748
  · exact context_12_353549_1214111
  · exact context_12_353550_1214162
  · exact context_12_353551_1214220

theorem unmarked_context_10_22096_1214222 : frontier 11 ⟨1214222, by decide⟩
    (prefixCache 10 22096) (prefixPartial 10 22096) = false := by
  decide +kernel

theorem node_context_10_22096_1214222 : EJMOriginalGlobalDAGData.nodes 11 ⟨1214222, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1213913, by decide⟩,⟨1214092, by decide⟩,⟨1214221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22096_1214222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22096 ⟨1214222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22096
    ⟨1214222, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1213913, by decide⟩,⟨1214092, by decide⟩,⟨1214221, by decide⟩]) unmarked_context_10_22096_1214222 node_context_10_22096_1214222
  intro a
  fin_cases a
  · exact context_11_88384_434745
  · exact context_11_88385_1213913
  · exact context_11_88386_1214092
  · exact context_11_88387_1214221

theorem selected_cut_44213 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 353552) = some ⟨12, 1, 0, 435160, 353552, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353552_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353552 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 353552 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 353552, 1, 65536⟩
    (by decide) selected_cut_44213

theorem selected_cut_44214 : selected 9 ⟨1214268, by decide⟩
    (prefixPartial 12 353553) = some ⟨12, 2, 0, 1214268, 353553, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_353553_1214268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353553 ⟨1214268, by decide⟩ :=
  accepted_of_selected 12 353553 ⟨1214268, by decide⟩ ⟨12, 2, 0, 1214268, 353553, 2045, 65536⟩
    (by decide) selected_cut_44214

theorem selected_cut_44215 : selected 9 ⟨1214315, by decide⟩
    (prefixPartial 12 353554) = some ⟨12, 2, 0, 1214315, 353554, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_353554_1214315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353554 ⟨1214315, by decide⟩ :=
  accepted_of_selected 12 353554 ⟨1214315, by decide⟩ ⟨12, 2, 0, 1214315, 353554, 2545, 65536⟩
    (by decide) selected_cut_44215

theorem selected_cut_44216 : selected 9 ⟨1214357, by decide⟩
    (prefixPartial 12 353555) = some ⟨12, 2, 0, 1214357, 353555, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_353555_1214357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353555 ⟨1214357, by decide⟩ :=
  accepted_of_selected 12 353555 ⟨1214357, by decide⟩ ⟨12, 2, 0, 1214357, 353555, 2701, 65536⟩
    (by decide) selected_cut_44216

theorem unmarked_context_11_88388_1214358 : frontier 10 ⟨1214358, by decide⟩
    (prefixCache 11 88388) (prefixPartial 11 88388) = false := by
  decide +kernel

theorem node_context_11_88388_1214358 : EJMOriginalGlobalDAGData.nodes 10 ⟨1214358, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1214268, by decide⟩,⟨1214315, by decide⟩,⟨1214357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88388_1214358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88388 ⟨1214358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88388
    ⟨1214358, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1214268, by decide⟩,⟨1214315, by decide⟩,⟨1214357, by decide⟩]) unmarked_context_11_88388_1214358 node_context_11_88388_1214358
  intro a
  fin_cases a
  · exact context_12_353552_435160
  · exact context_12_353553_1214268
  · exact context_12_353554_1214315
  · exact context_12_353555_1214357

theorem selected_cut_44217 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 88389) = some ⟨11, 1, 0, 892405, 88389, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88389_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88389 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 88389 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 88389, 1, 262144⟩
    (by decide) selected_cut_44217

theorem selected_cut_44218 : selected 9 ⟨1214408, by decide⟩
    (prefixPartial 12 353560) = some ⟨12, 2, 0, 1214408, 353560, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_353560_1214408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353560 ⟨1214408, by decide⟩ :=
  accepted_of_selected 12 353560 ⟨1214408, by decide⟩ ⟨12, 2, 0, 1214408, 353560, 1473, 65536⟩
    (by decide) selected_cut_44218

theorem selected_cut_44219 : selected 9 ⟨1214443, by decide⟩
    (prefixPartial 12 353561) = some ⟨12, 2, 0, 1214443, 353561, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_353561_1214443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353561 ⟨1214443, by decide⟩ :=
  accepted_of_selected 12 353561 ⟨1214443, by decide⟩ ⟨12, 2, 0, 1214443, 353561, 2093, 65536⟩
    (by decide) selected_cut_44219

theorem selected_cut_44220 : selected 9 ⟨1214509, by decide⟩
    (prefixPartial 12 353562) = some ⟨12, 2, 0, 1214509, 353562, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_353562_1214509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353562 ⟨1214509, by decide⟩ :=
  accepted_of_selected 12 353562 ⟨1214509, by decide⟩ ⟨12, 2, 0, 1214509, 353562, 1609, 65536⟩
    (by decide) selected_cut_44220

theorem selected_cut_44221 : selected 9 ⟨1214552, by decide⟩
    (prefixPartial 12 353563) = some ⟨12, 2, 0, 1214552, 353563, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_353563_1214552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353563 ⟨1214552, by decide⟩ :=
  accepted_of_selected 12 353563 ⟨1214552, by decide⟩ ⟨12, 2, 0, 1214552, 353563, 2697, 65536⟩
    (by decide) selected_cut_44221

theorem unmarked_context_11_88390_1214553 : frontier 10 ⟨1214553, by decide⟩
    (prefixCache 11 88390) (prefixPartial 11 88390) = false := by
  decide +kernel

theorem node_context_11_88390_1214553 : EJMOriginalGlobalDAGData.nodes 10 ⟨1214553, by decide⟩ =
    .split (coordinate 11) (![⟨1214408, by decide⟩,⟨1214443, by decide⟩,⟨1214509, by decide⟩,⟨1214552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88390_1214553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88390 ⟨1214553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88390
    ⟨1214553, by decide⟩ (by decide) (![⟨1214408, by decide⟩,⟨1214443, by decide⟩,⟨1214509, by decide⟩,⟨1214552, by decide⟩]) unmarked_context_11_88390_1214553 node_context_11_88390_1214553
  intro a
  fin_cases a
  · exact context_12_353560_1214408
  · exact context_12_353561_1214443
  · exact context_12_353562_1214509
  · exact context_12_353563_1214552

theorem selected_cut_44222 : selected 9 ⟨1214591, by decide⟩
    (prefixPartial 12 353564) = some ⟨12, 2, 0, 1214591, 353564, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_353564_1214591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353564 ⟨1214591, by decide⟩ :=
  accepted_of_selected 12 353564 ⟨1214591, by decide⟩ ⟨12, 2, 0, 1214591, 353564, 1181, 65536⟩
    (by decide) selected_cut_44222

theorem selected_cut_44223 : selected 9 ⟨1214619, by decide⟩
    (prefixPartial 12 353565) = some ⟨12, 2, 0, 1214619, 353565, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_353565_1214619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353565 ⟨1214619, by decide⟩ :=
  accepted_of_selected 12 353565 ⟨1214619, by decide⟩ ⟨12, 2, 0, 1214619, 353565, 1901, 65536⟩
    (by decide) selected_cut_44223

theorem selected_cut_44224 : selected 9 ⟨1214653, by decide⟩
    (prefixPartial 12 353566) = some ⟨12, 2, 0, 1214653, 353566, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_353566_1214653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353566 ⟨1214653, by decide⟩ :=
  accepted_of_selected 12 353566 ⟨1214653, by decide⟩ ⟨12, 2, 0, 1214653, 353566, 2361, 65536⟩
    (by decide) selected_cut_44224

theorem selected_cut_44225 : selected 9 ⟨1214710, by decide⟩
    (prefixPartial 12 353567) = some ⟨12, 2, 0, 1214710, 353567, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_353567_1214710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353567 ⟨1214710, by decide⟩ :=
  accepted_of_selected 12 353567 ⟨1214710, by decide⟩ ⟨12, 2, 0, 1214710, 353567, 2365, 65536⟩
    (by decide) selected_cut_44225

theorem unmarked_context_11_88391_1214711 : frontier 10 ⟨1214711, by decide⟩
    (prefixCache 11 88391) (prefixPartial 11 88391) = false := by
  decide +kernel

theorem node_context_11_88391_1214711 : EJMOriginalGlobalDAGData.nodes 10 ⟨1214711, by decide⟩ =
    .split (coordinate 11) (![⟨1214591, by decide⟩,⟨1214619, by decide⟩,⟨1214653, by decide⟩,⟨1214710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88391_1214711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88391 ⟨1214711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88391
    ⟨1214711, by decide⟩ (by decide) (![⟨1214591, by decide⟩,⟨1214619, by decide⟩,⟨1214653, by decide⟩,⟨1214710, by decide⟩]) unmarked_context_11_88391_1214711 node_context_11_88391_1214711
  intro a
  fin_cases a
  · exact context_12_353564_1214591
  · exact context_12_353565_1214619
  · exact context_12_353566_1214653
  · exact context_12_353567_1214710

theorem unmarked_context_10_22097_1214712 : frontier 11 ⟨1214712, by decide⟩
    (prefixCache 10 22097) (prefixPartial 10 22097) = false := by
  decide +kernel

theorem node_context_10_22097_1214712 : EJMOriginalGlobalDAGData.nodes 11 ⟨1214712, by decide⟩ =
    .split (coordinate 10) (![⟨1214358, by decide⟩,⟨892405, by decide⟩,⟨1214553, by decide⟩,⟨1214711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22097_1214712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22097 ⟨1214712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22097
    ⟨1214712, by decide⟩ (by decide) (![⟨1214358, by decide⟩,⟨892405, by decide⟩,⟨1214553, by decide⟩,⟨1214711, by decide⟩]) unmarked_context_10_22097_1214712 node_context_10_22097_1214712
  intro a
  fin_cases a
  · exact context_11_88388_1214358
  · exact context_11_88389_892405
  · exact context_11_88390_1214553
  · exact context_11_88391_1214711

theorem selected_cut_44226 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 353568) = some ⟨12, 1, 0, 1187656, 353568, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353568_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353568 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 353568 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 353568, 1, 65536⟩
    (by decide) selected_cut_44226

theorem selected_cut_44227 : selected 9 ⟨1214761, by decide⟩
    (prefixPartial 12 353569) = some ⟨12, 2, 0, 1214761, 353569, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_353569_1214761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353569 ⟨1214761, by decide⟩ :=
  accepted_of_selected 12 353569 ⟨1214761, by decide⟩ ⟨12, 2, 0, 1214761, 353569, 2569, 65536⟩
    (by decide) selected_cut_44227

theorem selected_cut_44228 : selected 9 ⟨1214811, by decide⟩
    (prefixPartial 12 353570) = some ⟨12, 2, 0, 1214811, 353570, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_353570_1214811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353570 ⟨1214811, by decide⟩ :=
  accepted_of_selected 12 353570 ⟨1214811, by decide⟩ ⟨12, 2, 0, 1214811, 353570, 2601, 65536⟩
    (by decide) selected_cut_44228

theorem selected_cut_44229 : selected 9 ⟨1214868, by decide⟩
    (prefixPartial 12 353571) = some ⟨12, 2, 0, 1214868, 353571, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_353571_1214868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353571 ⟨1214868, by decide⟩ :=
  accepted_of_selected 12 353571 ⟨1214868, by decide⟩ ⟨12, 2, 0, 1214868, 353571, 3013, 65536⟩
    (by decide) selected_cut_44229

theorem unmarked_context_11_88392_1214869 : frontier 10 ⟨1214869, by decide⟩
    (prefixCache 11 88392) (prefixPartial 11 88392) = false := by
  decide +kernel

theorem node_context_11_88392_1214869 : EJMOriginalGlobalDAGData.nodes 10 ⟨1214869, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1214761, by decide⟩,⟨1214811, by decide⟩,⟨1214868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88392_1214869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88392 ⟨1214869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88392
    ⟨1214869, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1214761, by decide⟩,⟨1214811, by decide⟩,⟨1214868, by decide⟩]) unmarked_context_11_88392_1214869 node_context_11_88392_1214869
  intro a
  fin_cases a
  · exact context_12_353568_1187656
  · exact context_12_353569_1214761
  · exact context_12_353570_1214811
  · exact context_12_353571_1214868

theorem selected_cut_44230 : selected 9 ⟨1214922, by decide⟩
    (prefixPartial 12 353572) = some ⟨12, 2, 0, 1214922, 353572, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_353572_1214922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353572 ⟨1214922, by decide⟩ :=
  accepted_of_selected 12 353572 ⟨1214922, by decide⟩ ⟨12, 2, 0, 1214922, 353572, 1845, 65536⟩
    (by decide) selected_cut_44230

theorem selected_cut_44231 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 353573) = some ⟨12, 1, 0, 891951, 353573, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353573_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353573 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 353573 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 353573, 1, 65536⟩
    (by decide) selected_cut_44231

theorem selected_cut_44232 : selected 9 ⟨1214953, by decide⟩
    (prefixPartial 12 353574) = some ⟨12, 2, 0, 1214953, 353574, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_353574_1214953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353574 ⟨1214953, by decide⟩ :=
  accepted_of_selected 12 353574 ⟨1214953, by decide⟩ ⟨12, 2, 0, 1214953, 353574, 1917, 65536⟩
    (by decide) selected_cut_44232

theorem selected_cut_44233 : selected 9 ⟨1214986, by decide⟩
    (prefixPartial 12 353575) = some ⟨12, 2, 0, 1214986, 353575, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_353575_1214986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353575 ⟨1214986, by decide⟩ :=
  accepted_of_selected 12 353575 ⟨1214986, by decide⟩ ⟨12, 2, 0, 1214986, 353575, 2225, 65536⟩
    (by decide) selected_cut_44233

theorem unmarked_context_11_88393_1214987 : frontier 10 ⟨1214987, by decide⟩
    (prefixCache 11 88393) (prefixPartial 11 88393) = false := by
  decide +kernel

theorem node_context_11_88393_1214987 : EJMOriginalGlobalDAGData.nodes 10 ⟨1214987, by decide⟩ =
    .split (coordinate 11) (![⟨1214922, by decide⟩,⟨891951, by decide⟩,⟨1214953, by decide⟩,⟨1214986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88393_1214987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88393 ⟨1214987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88393
    ⟨1214987, by decide⟩ (by decide) (![⟨1214922, by decide⟩,⟨891951, by decide⟩,⟨1214953, by decide⟩,⟨1214986, by decide⟩]) unmarked_context_11_88393_1214987 node_context_11_88393_1214987
  intro a
  fin_cases a
  · exact context_12_353572_1214922
  · exact context_12_353573_891951
  · exact context_12_353574_1214953
  · exact context_12_353575_1214986

theorem selected_cut_44234 : selected 9 ⟨1215047, by decide⟩
    (prefixPartial 12 353576) = some ⟨12, 2, 0, 1215047, 353576, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_353576_1215047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353576 ⟨1215047, by decide⟩ :=
  accepted_of_selected 12 353576 ⟨1215047, by decide⟩ ⟨12, 2, 0, 1215047, 353576, 2485, 65536⟩
    (by decide) selected_cut_44234

theorem selected_cut_44235 : selected 9 ⟨1215106, by decide⟩
    (prefixPartial 12 353577) = some ⟨12, 2, 0, 1215106, 353577, 1249, 65536⟩ := by
  decide +kernel

theorem context_12_353577_1215106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353577 ⟨1215106, by decide⟩ :=
  accepted_of_selected 12 353577 ⟨1215106, by decide⟩ ⟨12, 2, 0, 1215106, 353577, 1249, 65536⟩
    (by decide) selected_cut_44235

theorem selected_cut_44236 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 353578) = some ⟨12, 1, 0, 1113261, 353578, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353578_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353578 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 353578 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 353578, 1, 65536⟩
    (by decide) selected_cut_44236

theorem selected_cut_44237 : selected 9 ⟨1215162, by decide⟩
    (prefixPartial 12 353579) = some ⟨12, 2, 0, 1215162, 353579, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_353579_1215162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353579 ⟨1215162, by decide⟩ :=
  accepted_of_selected 12 353579 ⟨1215162, by decide⟩ ⟨12, 2, 0, 1215162, 353579, 2797, 65536⟩
    (by decide) selected_cut_44237

theorem unmarked_context_11_88394_1215163 : frontier 10 ⟨1215163, by decide⟩
    (prefixCache 11 88394) (prefixPartial 11 88394) = false := by
  decide +kernel

theorem node_context_11_88394_1215163 : EJMOriginalGlobalDAGData.nodes 10 ⟨1215163, by decide⟩ =
    .split (coordinate 11) (![⟨1215047, by decide⟩,⟨1215106, by decide⟩,⟨1113261, by decide⟩,⟨1215162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88394_1215163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88394 ⟨1215163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88394
    ⟨1215163, by decide⟩ (by decide) (![⟨1215047, by decide⟩,⟨1215106, by decide⟩,⟨1113261, by decide⟩,⟨1215162, by decide⟩]) unmarked_context_11_88394_1215163 node_context_11_88394_1215163
  intro a
  fin_cases a
  · exact context_12_353576_1215047
  · exact context_12_353577_1215106
  · exact context_12_353578_1113261
  · exact context_12_353579_1215162

theorem selected_cut_44238 : selected 9 ⟨1215213, by decide⟩
    (prefixPartial 12 353580) = some ⟨12, 2, 0, 1215213, 353580, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_353580_1215213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353580 ⟨1215213, by decide⟩ :=
  accepted_of_selected 12 353580 ⟨1215213, by decide⟩ ⟨12, 2, 0, 1215213, 353580, 2481, 65536⟩
    (by decide) selected_cut_44238

theorem selected_cut_44239 : selected 9 ⟨1215242, by decide⟩
    (prefixPartial 12 353581) = some ⟨12, 2, 0, 1215242, 353581, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_353581_1215242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353581 ⟨1215242, by decide⟩ :=
  accepted_of_selected 12 353581 ⟨1215242, by decide⟩ ⟨12, 2, 0, 1215242, 353581, 2077, 65536⟩
    (by decide) selected_cut_44239

theorem selected_cut_44240 : selected 9 ⟨1215280, by decide⟩
    (prefixPartial 12 353582) = some ⟨12, 2, 0, 1215280, 353582, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_353582_1215280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353582 ⟨1215280, by decide⟩ :=
  accepted_of_selected 12 353582 ⟨1215280, by decide⟩ ⟨12, 2, 0, 1215280, 353582, 2333, 65536⟩
    (by decide) selected_cut_44240

theorem selected_cut_44241 : selected 9 ⟨1215334, by decide⟩
    (prefixPartial 12 353583) = some ⟨12, 2, 0, 1215334, 353583, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_353583_1215334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353583 ⟨1215334, by decide⟩ :=
  accepted_of_selected 12 353583 ⟨1215334, by decide⟩ ⟨12, 2, 0, 1215334, 353583, 2753, 65536⟩
    (by decide) selected_cut_44241

theorem unmarked_context_11_88395_1215335 : frontier 10 ⟨1215335, by decide⟩
    (prefixCache 11 88395) (prefixPartial 11 88395) = false := by
  decide +kernel

theorem node_context_11_88395_1215335 : EJMOriginalGlobalDAGData.nodes 10 ⟨1215335, by decide⟩ =
    .split (coordinate 11) (![⟨1215213, by decide⟩,⟨1215242, by decide⟩,⟨1215280, by decide⟩,⟨1215334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88395_1215335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88395 ⟨1215335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88395
    ⟨1215335, by decide⟩ (by decide) (![⟨1215213, by decide⟩,⟨1215242, by decide⟩,⟨1215280, by decide⟩,⟨1215334, by decide⟩]) unmarked_context_11_88395_1215335 node_context_11_88395_1215335
  intro a
  fin_cases a
  · exact context_12_353580_1215213
  · exact context_12_353581_1215242
  · exact context_12_353582_1215280
  · exact context_12_353583_1215334

theorem unmarked_context_10_22098_1215336 : frontier 11 ⟨1215336, by decide⟩
    (prefixCache 10 22098) (prefixPartial 10 22098) = false := by
  decide +kernel

theorem node_context_10_22098_1215336 : EJMOriginalGlobalDAGData.nodes 11 ⟨1215336, by decide⟩ =
    .split (coordinate 10) (![⟨1214869, by decide⟩,⟨1214987, by decide⟩,⟨1215163, by decide⟩,⟨1215335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22098_1215336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22098 ⟨1215336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22098
    ⟨1215336, by decide⟩ (by decide) (![⟨1214869, by decide⟩,⟨1214987, by decide⟩,⟨1215163, by decide⟩,⟨1215335, by decide⟩]) unmarked_context_10_22098_1215336 node_context_10_22098_1215336
  intro a
  fin_cases a
  · exact context_11_88392_1214869
  · exact context_11_88393_1214987
  · exact context_11_88394_1215163
  · exact context_11_88395_1215335

theorem selected_cut_44242 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 353584) = some ⟨12, 1, 0, 1187656, 353584, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353584_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353584 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 353584 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 353584, 1, 65536⟩
    (by decide) selected_cut_44242

theorem selected_cut_44243 : selected 9 ⟨1215384, by decide⟩
    (prefixPartial 12 353585) = some ⟨12, 2, 0, 1215384, 353585, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_353585_1215384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353585 ⟨1215384, by decide⟩ :=
  accepted_of_selected 12 353585 ⟨1215384, by decide⟩ ⟨12, 2, 0, 1215384, 353585, 2209, 65536⟩
    (by decide) selected_cut_44243

theorem selected_cut_44244 : selected 9 ⟨1215434, by decide⟩
    (prefixPartial 12 353586) = some ⟨12, 2, 0, 1215434, 353586, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_353586_1215434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353586 ⟨1215434, by decide⟩ :=
  accepted_of_selected 12 353586 ⟨1215434, by decide⟩ ⟨12, 2, 0, 1215434, 353586, 2517, 65536⟩
    (by decide) selected_cut_44244

theorem selected_cut_44245 : selected 9 ⟨1215499, by decide⟩
    (prefixPartial 12 353587) = some ⟨12, 2, 0, 1215499, 353587, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_353587_1215499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353587 ⟨1215499, by decide⟩ :=
  accepted_of_selected 12 353587 ⟨1215499, by decide⟩ ⟨12, 2, 0, 1215499, 353587, 2457, 65536⟩
    (by decide) selected_cut_44245

theorem unmarked_context_11_88396_1215500 : frontier 10 ⟨1215500, by decide⟩
    (prefixCache 11 88396) (prefixPartial 11 88396) = false := by
  decide +kernel

theorem node_context_11_88396_1215500 : EJMOriginalGlobalDAGData.nodes 10 ⟨1215500, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1215384, by decide⟩,⟨1215434, by decide⟩,⟨1215499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88396_1215500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88396 ⟨1215500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88396
    ⟨1215500, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1215384, by decide⟩,⟨1215434, by decide⟩,⟨1215499, by decide⟩]) unmarked_context_11_88396_1215500 node_context_11_88396_1215500
  intro a
  fin_cases a
  · exact context_12_353584_1187656
  · exact context_12_353585_1215384
  · exact context_12_353586_1215434
  · exact context_12_353587_1215499

theorem selected_cut_44246 : selected 9 ⟨1215562, by decide⟩
    (prefixPartial 12 353588) = some ⟨12, 2, 0, 1215562, 353588, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_353588_1215562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353588 ⟨1215562, by decide⟩ :=
  accepted_of_selected 12 353588 ⟨1215562, by decide⟩ ⟨12, 2, 0, 1215562, 353588, 1605, 65536⟩
    (by decide) selected_cut_44246

theorem selected_cut_44247 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 353589) = some ⟨12, 1, 0, 891951, 353589, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353589_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353589 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 353589 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 353589, 1, 65536⟩
    (by decide) selected_cut_44247

theorem selected_cut_44248 : selected 9 ⟨1215599, by decide⟩
    (prefixPartial 12 353590) = some ⟨12, 2, 0, 1215599, 353590, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_353590_1215599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353590 ⟨1215599, by decide⟩ :=
  accepted_of_selected 12 353590 ⟨1215599, by decide⟩ ⟨12, 2, 0, 1215599, 353590, 1933, 65536⟩
    (by decide) selected_cut_44248

theorem selected_cut_44249 : selected 9 ⟨1215629, by decide⟩
    (prefixPartial 12 353591) = some ⟨12, 2, 0, 1215629, 353591, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_353591_1215629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353591 ⟨1215629, by decide⟩ :=
  accepted_of_selected 12 353591 ⟨1215629, by decide⟩ ⟨12, 2, 0, 1215629, 353591, 1821, 65536⟩
    (by decide) selected_cut_44249

theorem unmarked_context_11_88397_1215630 : frontier 10 ⟨1215630, by decide⟩
    (prefixCache 11 88397) (prefixPartial 11 88397) = false := by
  decide +kernel

theorem node_context_11_88397_1215630 : EJMOriginalGlobalDAGData.nodes 10 ⟨1215630, by decide⟩ =
    .split (coordinate 11) (![⟨1215562, by decide⟩,⟨891951, by decide⟩,⟨1215599, by decide⟩,⟨1215629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88397_1215630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88397 ⟨1215630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88397
    ⟨1215630, by decide⟩ (by decide) (![⟨1215562, by decide⟩,⟨891951, by decide⟩,⟨1215599, by decide⟩,⟨1215629, by decide⟩]) unmarked_context_11_88397_1215630 node_context_11_88397_1215630
  intro a
  fin_cases a
  · exact context_12_353588_1215562
  · exact context_12_353589_891951
  · exact context_12_353590_1215599
  · exact context_12_353591_1215629

theorem selected_cut_44250 : selected 9 ⟨1215683, by decide⟩
    (prefixPartial 12 353592) = some ⟨12, 2, 0, 1215683, 353592, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_353592_1215683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353592 ⟨1215683, by decide⟩ :=
  accepted_of_selected 12 353592 ⟨1215683, by decide⟩ ⟨12, 2, 0, 1215683, 353592, 2417, 65536⟩
    (by decide) selected_cut_44250

theorem selected_cut_44251 : selected 9 ⟨1215714, by decide⟩
    (prefixPartial 12 353593) = some ⟨12, 2, 0, 1215714, 353593, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_353593_1215714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353593 ⟨1215714, by decide⟩ :=
  accepted_of_selected 12 353593 ⟨1215714, by decide⟩ ⟨12, 2, 0, 1215714, 353593, 2009, 65536⟩
    (by decide) selected_cut_44251

theorem selected_cut_44252 : selected 9 ⟨1215764, by decide⟩
    (prefixPartial 12 353594) = some ⟨12, 2, 0, 1215764, 353594, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_353594_1215764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353594 ⟨1215764, by decide⟩ :=
  accepted_of_selected 12 353594 ⟨1215764, by decide⟩ ⟨12, 2, 0, 1215764, 353594, 2281, 65536⟩
    (by decide) selected_cut_44252

theorem selected_cut_44253 : selected 9 ⟨1215806, by decide⟩
    (prefixPartial 12 353595) = some ⟨12, 2, 0, 1215806, 353595, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_353595_1215806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353595 ⟨1215806, by decide⟩ :=
  accepted_of_selected 12 353595 ⟨1215806, by decide⟩ ⟨12, 2, 0, 1215806, 353595, 2225, 65536⟩
    (by decide) selected_cut_44253

theorem unmarked_context_11_88398_1215807 : frontier 10 ⟨1215807, by decide⟩
    (prefixCache 11 88398) (prefixPartial 11 88398) = false := by
  decide +kernel

theorem node_context_11_88398_1215807 : EJMOriginalGlobalDAGData.nodes 10 ⟨1215807, by decide⟩ =
    .split (coordinate 11) (![⟨1215683, by decide⟩,⟨1215714, by decide⟩,⟨1215764, by decide⟩,⟨1215806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88398_1215807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88398 ⟨1215807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88398
    ⟨1215807, by decide⟩ (by decide) (![⟨1215683, by decide⟩,⟨1215714, by decide⟩,⟨1215764, by decide⟩,⟨1215806, by decide⟩]) unmarked_context_11_88398_1215807 node_context_11_88398_1215807
  intro a
  fin_cases a
  · exact context_12_353592_1215683
  · exact context_12_353593_1215714
  · exact context_12_353594_1215764
  · exact context_12_353595_1215806

theorem selected_cut_44254 : selected 9 ⟨1215851, by decide⟩
    (prefixPartial 12 353596) = some ⟨12, 2, 0, 1215851, 353596, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_353596_1215851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353596 ⟨1215851, by decide⟩ :=
  accepted_of_selected 12 353596 ⟨1215851, by decide⟩ ⟨12, 2, 0, 1215851, 353596, 1981, 65536⟩
    (by decide) selected_cut_44254

theorem selected_cut_44255 : selected 9 ⟨1215880, by decide⟩
    (prefixPartial 12 353597) = some ⟨12, 2, 0, 1215880, 353597, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_353597_1215880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353597 ⟨1215880, by decide⟩ :=
  accepted_of_selected 12 353597 ⟨1215880, by decide⟩ ⟨12, 2, 0, 1215880, 353597, 1201, 65536⟩
    (by decide) selected_cut_44255

theorem selected_cut_44256 : selected 9 ⟨1215917, by decide⟩
    (prefixPartial 12 353598) = some ⟨12, 2, 0, 1215917, 353598, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_353598_1215917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353598 ⟨1215917, by decide⟩ :=
  accepted_of_selected 12 353598 ⟨1215917, by decide⟩ ⟨12, 2, 0, 1215917, 353598, 1865, 65536⟩
    (by decide) selected_cut_44256

theorem selected_cut_44257 : selected 9 ⟨1116246, by decide⟩
    (prefixPartial 12 353599) = some ⟨12, 1, 0, 1116246, 353599, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353599_1116246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353599 ⟨1116246, by decide⟩ :=
  accepted_of_selected 12 353599 ⟨1116246, by decide⟩ ⟨12, 1, 0, 1116246, 353599, 1, 65536⟩
    (by decide) selected_cut_44257

theorem unmarked_context_11_88399_1215918 : frontier 10 ⟨1215918, by decide⟩
    (prefixCache 11 88399) (prefixPartial 11 88399) = false := by
  decide +kernel

theorem node_context_11_88399_1215918 : EJMOriginalGlobalDAGData.nodes 10 ⟨1215918, by decide⟩ =
    .split (coordinate 11) (![⟨1215851, by decide⟩,⟨1215880, by decide⟩,⟨1215917, by decide⟩,⟨1116246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88399_1215918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88399 ⟨1215918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88399
    ⟨1215918, by decide⟩ (by decide) (![⟨1215851, by decide⟩,⟨1215880, by decide⟩,⟨1215917, by decide⟩,⟨1116246, by decide⟩]) unmarked_context_11_88399_1215918 node_context_11_88399_1215918
  intro a
  fin_cases a
  · exact context_12_353596_1215851
  · exact context_12_353597_1215880
  · exact context_12_353598_1215917
  · exact context_12_353599_1116246

theorem unmarked_context_10_22099_1215919 : frontier 11 ⟨1215919, by decide⟩
    (prefixCache 10 22099) (prefixPartial 10 22099) = false := by
  decide +kernel

theorem node_context_10_22099_1215919 : EJMOriginalGlobalDAGData.nodes 11 ⟨1215919, by decide⟩ =
    .split (coordinate 10) (![⟨1215500, by decide⟩,⟨1215630, by decide⟩,⟨1215807, by decide⟩,⟨1215918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22099_1215919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22099 ⟨1215919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22099
    ⟨1215919, by decide⟩ (by decide) (![⟨1215500, by decide⟩,⟨1215630, by decide⟩,⟨1215807, by decide⟩,⟨1215918, by decide⟩]) unmarked_context_10_22099_1215919 node_context_10_22099_1215919
  intro a
  fin_cases a
  · exact context_11_88396_1215500
  · exact context_11_88397_1215630
  · exact context_11_88398_1215807
  · exact context_11_88399_1215918

theorem unmarked_context_9_5524_1215920 : frontier 12 ⟨1215920, by decide⟩
    (prefixCache 9 5524) (prefixPartial 9 5524) = false := by
  decide +kernel

theorem node_context_9_5524_1215920 : EJMOriginalGlobalDAGData.nodes 12 ⟨1215920, by decide⟩ =
    .split (coordinate 9) (![⟨1214222, by decide⟩,⟨1214712, by decide⟩,⟨1215336, by decide⟩,⟨1215919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5524_1215920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5524 ⟨1215920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5524
    ⟨1215920, by decide⟩ (by decide) (![⟨1214222, by decide⟩,⟨1214712, by decide⟩,⟨1215336, by decide⟩,⟨1215919, by decide⟩]) unmarked_context_9_5524_1215920 node_context_9_5524_1215920
  intro a
  fin_cases a
  · exact context_10_22096_1214222
  · exact context_10_22097_1214712
  · exact context_10_22098_1215336
  · exact context_10_22099_1215919

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
