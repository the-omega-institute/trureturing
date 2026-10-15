/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover094
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_09124 : selected 7 ⟨252787, by decide⟩
    (prefixPartial 14 372979) = some ⟨14, 2, 0, 252787, 372979, 1525, 4096⟩ := by
  decide +kernel

theorem context_14_372979_252787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372979 ⟨252787, by decide⟩ :=
  accepted_of_selected 14 372979 ⟨252787, by decide⟩ ⟨14, 2, 0, 252787, 372979, 1525, 4096⟩
    (by decide) selected_cut_09124

theorem unmarked_context_13_93244_252788 : frontier 8 ⟨252788, by decide⟩
    (prefixCache 13 93244) (prefixPartial 13 93244) = false := by
  decide +kernel

theorem node_context_13_93244_252788 : EJMOriginalGlobalDAGData.nodes 8 ⟨252788, by decide⟩ =
    .split (coordinate 13) (![⟨252694, by decide⟩,⟨252725, by decide⟩,⟨252758, by decide⟩,⟨252787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93244_252788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93244 ⟨252788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93244
    ⟨252788, by decide⟩ (by decide) (![⟨252694, by decide⟩,⟨252725, by decide⟩,⟨252758, by decide⟩,⟨252787, by decide⟩]) unmarked_context_13_93244_252788 node_context_13_93244_252788
  intro a
  fin_cases a
  · exact context_14_372976_252694
  · exact context_14_372977_252725
  · exact context_14_372978_252758
  · exact context_14_372979_252787

theorem selected_cut_09125 : selected 7 ⟨252829, by decide⟩
    (prefixPartial 14 372980) = some ⟨14, 2, 0, 252829, 372980, 1937, 4096⟩ := by
  decide +kernel

theorem context_14_372980_252829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372980 ⟨252829, by decide⟩ :=
  accepted_of_selected 14 372980 ⟨252829, by decide⟩ ⟨14, 2, 0, 252829, 372980, 1937, 4096⟩
    (by decide) selected_cut_09125

theorem selected_cut_09126 : selected 7 ⟨252873, by decide⟩
    (prefixPartial 14 372981) = some ⟨14, 2, 0, 252873, 372981, 2189, 4096⟩ := by
  decide +kernel

theorem context_14_372981_252873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372981 ⟨252873, by decide⟩ :=
  accepted_of_selected 14 372981 ⟨252873, by decide⟩ ⟨14, 2, 0, 252873, 372981, 2189, 4096⟩
    (by decide) selected_cut_09126

theorem selected_cut_09127 : selected 7 ⟨252926, by decide⟩
    (prefixPartial 14 372982) = some ⟨14, 2, 0, 252926, 372982, 1797, 4096⟩ := by
  decide +kernel

theorem context_14_372982_252926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372982 ⟨252926, by decide⟩ :=
  accepted_of_selected 14 372982 ⟨252926, by decide⟩ ⟨14, 2, 0, 252926, 372982, 1797, 4096⟩
    (by decide) selected_cut_09127

theorem selected_cut_09128 : selected 7 ⟨252959, by decide⟩
    (prefixPartial 14 372983) = some ⟨14, 2, 0, 252959, 372983, 1501, 4096⟩ := by
  decide +kernel

theorem context_14_372983_252959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372983 ⟨252959, by decide⟩ :=
  accepted_of_selected 14 372983 ⟨252959, by decide⟩ ⟨14, 2, 0, 252959, 372983, 1501, 4096⟩
    (by decide) selected_cut_09128

theorem unmarked_context_13_93245_252960 : frontier 8 ⟨252960, by decide⟩
    (prefixCache 13 93245) (prefixPartial 13 93245) = false := by
  decide +kernel

theorem node_context_13_93245_252960 : EJMOriginalGlobalDAGData.nodes 8 ⟨252960, by decide⟩ =
    .split (coordinate 13) (![⟨252829, by decide⟩,⟨252873, by decide⟩,⟨252926, by decide⟩,⟨252959, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93245_252960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93245 ⟨252960, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93245
    ⟨252960, by decide⟩ (by decide) (![⟨252829, by decide⟩,⟨252873, by decide⟩,⟨252926, by decide⟩,⟨252959, by decide⟩]) unmarked_context_13_93245_252960 node_context_13_93245_252960
  intro a
  fin_cases a
  · exact context_14_372980_252829
  · exact context_14_372981_252873
  · exact context_14_372982_252926
  · exact context_14_372983_252959

theorem selected_cut_09129 : selected 8 ⟨253087, by decide⟩
    (prefixPartial 13 93246) = some ⟨13, 2, 0, 253087, 93246, 3577, 16384⟩ := by
  decide +kernel

theorem context_13_93246_253087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93246 ⟨253087, by decide⟩ :=
  accepted_of_selected 13 93246 ⟨253087, by decide⟩ ⟨13, 2, 0, 253087, 93246, 3577, 16384⟩
    (by decide) selected_cut_09129

theorem selected_cut_09130 : selected 8 ⟨253165, by decide⟩
    (prefixPartial 13 93247) = some ⟨13, 2, 0, 253165, 93247, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_93247_253165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93247 ⟨253165, by decide⟩ :=
  accepted_of_selected 13 93247 ⟨253165, by decide⟩ ⟨13, 2, 0, 253165, 93247, 1501, 16384⟩
    (by decide) selected_cut_09130

theorem unmarked_context_12_23311_253166 : frontier 9 ⟨253166, by decide⟩
    (prefixCache 12 23311) (prefixPartial 12 23311) = false := by
  decide +kernel

theorem node_context_12_23311_253166 : EJMOriginalGlobalDAGData.nodes 9 ⟨253166, by decide⟩ =
    .split (coordinate 12) (![⟨252788, by decide⟩,⟨252960, by decide⟩,⟨253087, by decide⟩,⟨253165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23311_253166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23311 ⟨253166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23311
    ⟨253166, by decide⟩ (by decide) (![⟨252788, by decide⟩,⟨252960, by decide⟩,⟨253087, by decide⟩,⟨253165, by decide⟩]) unmarked_context_12_23311_253166 node_context_12_23311_253166
  intro a
  fin_cases a
  · exact context_13_93244_252788
  · exact context_13_93245_252960
  · exact context_13_93246_253087
  · exact context_13_93247_253165

theorem unmarked_context_11_5827_253167 : frontier 10 ⟨253167, by decide⟩
    (prefixCache 11 5827) (prefixPartial 11 5827) = false := by
  decide +kernel

theorem node_context_11_5827_253167 : EJMOriginalGlobalDAGData.nodes 10 ⟨253167, by decide⟩ =
    .split (coordinate 11) (![⟨252319, by decide⟩,⟨252488, by decide⟩,⟨252688, by decide⟩,⟨253166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5827_253167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5827 ⟨253167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5827
    ⟨253167, by decide⟩ (by decide) (![⟨252319, by decide⟩,⟨252488, by decide⟩,⟨252688, by decide⟩,⟨253166, by decide⟩]) unmarked_context_11_5827_253167 node_context_11_5827_253167
  intro a
  fin_cases a
  · exact context_12_23308_252319
  · exact context_12_23309_252488
  · exact context_12_23310_252688
  · exact context_12_23311_253166

theorem unmarked_context_10_1456_253168 : frontier 11 ⟨253168, by decide⟩
    (prefixCache 10 1456) (prefixPartial 10 1456) = false := by
  decide +kernel

theorem node_context_10_1456_253168 : EJMOriginalGlobalDAGData.nodes 11 ⟨253168, by decide⟩ =
    .split (coordinate 10) (![⟨250484, by decide⟩,⟨251387, by decide⟩,⟨252167, by decide⟩,⟨253167, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1456_253168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1456 ⟨253168, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1456
    ⟨253168, by decide⟩ (by decide) (![⟨250484, by decide⟩,⟨251387, by decide⟩,⟨252167, by decide⟩,⟨253167, by decide⟩]) unmarked_context_10_1456_253168 node_context_10_1456_253168
  intro a
  fin_cases a
  · exact context_11_5824_250484
  · exact context_11_5825_251387
  · exact context_11_5826_252167
  · exact context_11_5827_253167

theorem selected_cut_09131 : selected 8 ⟨253186, by decide⟩
    (prefixPartial 13 93248) = some ⟨13, 2, 0, 253186, 93248, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_93248_253186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93248 ⟨253186, by decide⟩ :=
  accepted_of_selected 13 93248 ⟨253186, by decide⟩ ⟨13, 2, 0, 253186, 93248, 1877, 16384⟩
    (by decide) selected_cut_09131

theorem selected_cut_09132 : selected 8 ⟨253210, by decide⟩
    (prefixPartial 13 93249) = some ⟨13, 2, 0, 253210, 93249, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_93249_253210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93249 ⟨253210, by decide⟩ :=
  accepted_of_selected 13 93249 ⟨253210, by decide⟩ ⟨13, 2, 0, 253210, 93249, 2517, 16384⟩
    (by decide) selected_cut_09132

theorem selected_cut_09133 : selected 8 ⟨253229, by decide⟩
    (prefixPartial 13 93250) = some ⟨13, 2, 0, 253229, 93250, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_93250_253229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93250 ⟨253229, by decide⟩ :=
  accepted_of_selected 13 93250 ⟨253229, by decide⟩ ⟨13, 2, 0, 253229, 93250, 1489, 16384⟩
    (by decide) selected_cut_09133

theorem selected_cut_09134 : selected 8 ⟨253247, by decide⟩
    (prefixPartial 13 93251) = some ⟨13, 2, 0, 253247, 93251, 897, 16384⟩ := by
  decide +kernel

theorem context_13_93251_253247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93251 ⟨253247, by decide⟩ :=
  accepted_of_selected 13 93251 ⟨253247, by decide⟩ ⟨13, 2, 0, 253247, 93251, 897, 16384⟩
    (by decide) selected_cut_09134

theorem unmarked_context_12_23312_253248 : frontier 9 ⟨253248, by decide⟩
    (prefixCache 12 23312) (prefixPartial 12 23312) = false := by
  decide +kernel

theorem node_context_12_23312_253248 : EJMOriginalGlobalDAGData.nodes 9 ⟨253248, by decide⟩ =
    .split (coordinate 12) (![⟨253186, by decide⟩,⟨253210, by decide⟩,⟨253229, by decide⟩,⟨253247, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23312_253248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23312 ⟨253248, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23312
    ⟨253248, by decide⟩ (by decide) (![⟨253186, by decide⟩,⟨253210, by decide⟩,⟨253229, by decide⟩,⟨253247, by decide⟩]) unmarked_context_12_23312_253248 node_context_12_23312_253248
  intro a
  fin_cases a
  · exact context_13_93248_253186
  · exact context_13_93249_253210
  · exact context_13_93250_253229
  · exact context_13_93251_253247

theorem selected_cut_09135 : selected 8 ⟨253277, by decide⟩
    (prefixPartial 13 93252) = some ⟨13, 2, 0, 253277, 93252, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_93252_253277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93252 ⟨253277, by decide⟩ :=
  accepted_of_selected 13 93252 ⟨253277, by decide⟩ ⟨13, 2, 0, 253277, 93252, 2133, 16384⟩
    (by decide) selected_cut_09135

theorem selected_cut_09136 : selected 8 ⟨253309, by decide⟩
    (prefixPartial 13 93253) = some ⟨13, 2, 0, 253309, 93253, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_93253_253309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93253 ⟨253309, by decide⟩ :=
  accepted_of_selected 13 93253 ⟨253309, by decide⟩ ⟨13, 2, 0, 253309, 93253, 2333, 16384⟩
    (by decide) selected_cut_09136

theorem selected_cut_09137 : selected 8 ⟨253339, by decide⟩
    (prefixPartial 13 93254) = some ⟨13, 2, 0, 253339, 93254, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_93254_253339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93254 ⟨253339, by decide⟩ :=
  accepted_of_selected 13 93254 ⟨253339, by decide⟩ ⟨13, 2, 0, 253339, 93254, 1681, 16384⟩
    (by decide) selected_cut_09137

theorem selected_cut_09138 : selected 8 ⟨253349, by decide⟩
    (prefixPartial 13 93255) = some ⟨13, 2, 0, 253349, 93255, 745, 16384⟩ := by
  decide +kernel

theorem context_13_93255_253349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93255 ⟨253349, by decide⟩ :=
  accepted_of_selected 13 93255 ⟨253349, by decide⟩ ⟨13, 2, 0, 253349, 93255, 745, 16384⟩
    (by decide) selected_cut_09138

theorem unmarked_context_12_23313_253350 : frontier 9 ⟨253350, by decide⟩
    (prefixCache 12 23313) (prefixPartial 12 23313) = false := by
  decide +kernel

theorem node_context_12_23313_253350 : EJMOriginalGlobalDAGData.nodes 9 ⟨253350, by decide⟩ =
    .split (coordinate 12) (![⟨253277, by decide⟩,⟨253309, by decide⟩,⟨253339, by decide⟩,⟨253349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23313_253350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23313 ⟨253350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23313
    ⟨253350, by decide⟩ (by decide) (![⟨253277, by decide⟩,⟨253309, by decide⟩,⟨253339, by decide⟩,⟨253349, by decide⟩]) unmarked_context_12_23313_253350 node_context_12_23313_253350
  intro a
  fin_cases a
  · exact context_13_93252_253277
  · exact context_13_93253_253309
  · exact context_13_93254_253339
  · exact context_13_93255_253349

theorem selected_cut_09139 : selected 8 ⟨253382, by decide⟩
    (prefixPartial 13 93256) = some ⟨13, 2, 0, 253382, 93256, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_93256_253382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93256 ⟨253382, by decide⟩ :=
  accepted_of_selected 13 93256 ⟨253382, by decide⟩ ⟨13, 2, 0, 253382, 93256, 2561, 16384⟩
    (by decide) selected_cut_09139

theorem selected_cut_09140 : selected 8 ⟨253438, by decide⟩
    (prefixPartial 13 93257) = some ⟨13, 2, 0, 253438, 93257, 3145, 16384⟩ := by
  decide +kernel

theorem context_13_93257_253438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93257 ⟨253438, by decide⟩ :=
  accepted_of_selected 13 93257 ⟨253438, by decide⟩ ⟨13, 2, 0, 253438, 93257, 3145, 16384⟩
    (by decide) selected_cut_09140

theorem selected_cut_09141 : selected 8 ⟨253473, by decide⟩
    (prefixPartial 13 93258) = some ⟨13, 2, 0, 253473, 93258, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_93258_253473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93258 ⟨253473, by decide⟩ :=
  accepted_of_selected 13 93258 ⟨253473, by decide⟩ ⟨13, 2, 0, 253473, 93258, 2149, 16384⟩
    (by decide) selected_cut_09141

theorem selected_cut_09142 : selected 8 ⟨253483, by decide⟩
    (prefixPartial 13 93259) = some ⟨13, 2, 0, 253483, 93259, 849, 16384⟩ := by
  decide +kernel

theorem context_13_93259_253483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93259 ⟨253483, by decide⟩ :=
  accepted_of_selected 13 93259 ⟨253483, by decide⟩ ⟨13, 2, 0, 253483, 93259, 849, 16384⟩
    (by decide) selected_cut_09142

theorem unmarked_context_12_23314_253484 : frontier 9 ⟨253484, by decide⟩
    (prefixCache 12 23314) (prefixPartial 12 23314) = false := by
  decide +kernel

theorem node_context_12_23314_253484 : EJMOriginalGlobalDAGData.nodes 9 ⟨253484, by decide⟩ =
    .split (coordinate 12) (![⟨253382, by decide⟩,⟨253438, by decide⟩,⟨253473, by decide⟩,⟨253483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23314_253484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23314 ⟨253484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23314
    ⟨253484, by decide⟩ (by decide) (![⟨253382, by decide⟩,⟨253438, by decide⟩,⟨253473, by decide⟩,⟨253483, by decide⟩]) unmarked_context_12_23314_253484 node_context_12_23314_253484
  intro a
  fin_cases a
  · exact context_13_93256_253382
  · exact context_13_93257_253438
  · exact context_13_93258_253473
  · exact context_13_93259_253483

theorem selected_cut_09143 : selected 8 ⟨253506, by decide⟩
    (prefixPartial 13 93260) = some ⟨13, 2, 0, 253506, 93260, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_93260_253506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93260 ⟨253506, by decide⟩ :=
  accepted_of_selected 13 93260 ⟨253506, by decide⟩ ⟨13, 2, 0, 253506, 93260, 2293, 16384⟩
    (by decide) selected_cut_09143

theorem selected_cut_09144 : selected 8 ⟨253543, by decide⟩
    (prefixPartial 13 93261) = some ⟨13, 2, 0, 253543, 93261, 2969, 16384⟩ := by
  decide +kernel

theorem context_13_93261_253543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93261 ⟨253543, by decide⟩ :=
  accepted_of_selected 13 93261 ⟨253543, by decide⟩ ⟨13, 2, 0, 253543, 93261, 2969, 16384⟩
    (by decide) selected_cut_09144

theorem selected_cut_09145 : selected 8 ⟨253562, by decide⟩
    (prefixPartial 13 93262) = some ⟨13, 2, 0, 253562, 93262, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_93262_253562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93262 ⟨253562, by decide⟩ :=
  accepted_of_selected 13 93262 ⟨253562, by decide⟩ ⟨13, 2, 0, 253562, 93262, 1905, 16384⟩
    (by decide) selected_cut_09145

theorem selected_cut_09146 : selected 8 ⟨253568, by decide⟩
    (prefixPartial 13 93263) = some ⟨13, 2, 0, 253568, 93263, 773, 16384⟩ := by
  decide +kernel

theorem context_13_93263_253568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93263 ⟨253568, by decide⟩ :=
  accepted_of_selected 13 93263 ⟨253568, by decide⟩ ⟨13, 2, 0, 253568, 93263, 773, 16384⟩
    (by decide) selected_cut_09146

theorem unmarked_context_12_23315_253569 : frontier 9 ⟨253569, by decide⟩
    (prefixCache 12 23315) (prefixPartial 12 23315) = false := by
  decide +kernel

theorem node_context_12_23315_253569 : EJMOriginalGlobalDAGData.nodes 9 ⟨253569, by decide⟩ =
    .split (coordinate 12) (![⟨253506, by decide⟩,⟨253543, by decide⟩,⟨253562, by decide⟩,⟨253568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23315_253569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23315 ⟨253569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23315
    ⟨253569, by decide⟩ (by decide) (![⟨253506, by decide⟩,⟨253543, by decide⟩,⟨253562, by decide⟩,⟨253568, by decide⟩]) unmarked_context_12_23315_253569 node_context_12_23315_253569
  intro a
  fin_cases a
  · exact context_13_93260_253506
  · exact context_13_93261_253543
  · exact context_13_93262_253562
  · exact context_13_93263_253568

theorem unmarked_context_11_5828_253570 : frontier 10 ⟨253570, by decide⟩
    (prefixCache 11 5828) (prefixPartial 11 5828) = false := by
  decide +kernel

theorem node_context_11_5828_253570 : EJMOriginalGlobalDAGData.nodes 10 ⟨253570, by decide⟩ =
    .split (coordinate 11) (![⟨253248, by decide⟩,⟨253350, by decide⟩,⟨253484, by decide⟩,⟨253569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5828_253570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5828 ⟨253570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5828
    ⟨253570, by decide⟩ (by decide) (![⟨253248, by decide⟩,⟨253350, by decide⟩,⟨253484, by decide⟩,⟨253569, by decide⟩]) unmarked_context_11_5828_253570 node_context_11_5828_253570
  intro a
  fin_cases a
  · exact context_12_23312_253248
  · exact context_12_23313_253350
  · exact context_12_23314_253484
  · exact context_12_23315_253569

theorem selected_cut_09147 : selected 8 ⟨253595, by decide⟩
    (prefixPartial 13 93264) = some ⟨13, 2, 0, 253595, 93264, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_93264_253595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93264 ⟨253595, by decide⟩ :=
  accepted_of_selected 13 93264 ⟨253595, by decide⟩ ⟨13, 2, 0, 253595, 93264, 1817, 16384⟩
    (by decide) selected_cut_09147

theorem selected_cut_09148 : selected 8 ⟨253639, by decide⟩
    (prefixPartial 13 93265) = some ⟨13, 2, 0, 253639, 93265, 2869, 16384⟩ := by
  decide +kernel

theorem context_13_93265_253639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93265 ⟨253639, by decide⟩ :=
  accepted_of_selected 13 93265 ⟨253639, by decide⟩ ⟨13, 2, 0, 253639, 93265, 2869, 16384⟩
    (by decide) selected_cut_09148

theorem selected_cut_09149 : selected 8 ⟨253657, by decide⟩
    (prefixPartial 13 93266) = some ⟨13, 2, 0, 253657, 93266, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_93266_253657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93266 ⟨253657, by decide⟩ :=
  accepted_of_selected 13 93266 ⟨253657, by decide⟩ ⟨13, 2, 0, 253657, 93266, 1381, 16384⟩
    (by decide) selected_cut_09149

theorem selected_cut_09150 : selected 8 ⟨253668, by decide⟩
    (prefixPartial 13 93267) = some ⟨13, 2, 0, 253668, 93267, 929, 16384⟩ := by
  decide +kernel

theorem context_13_93267_253668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93267 ⟨253668, by decide⟩ :=
  accepted_of_selected 13 93267 ⟨253668, by decide⟩ ⟨13, 2, 0, 253668, 93267, 929, 16384⟩
    (by decide) selected_cut_09150

theorem unmarked_context_12_23316_253669 : frontier 9 ⟨253669, by decide⟩
    (prefixCache 12 23316) (prefixPartial 12 23316) = false := by
  decide +kernel

theorem node_context_12_23316_253669 : EJMOriginalGlobalDAGData.nodes 9 ⟨253669, by decide⟩ =
    .split (coordinate 12) (![⟨253595, by decide⟩,⟨253639, by decide⟩,⟨253657, by decide⟩,⟨253668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23316_253669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23316 ⟨253669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23316
    ⟨253669, by decide⟩ (by decide) (![⟨253595, by decide⟩,⟨253639, by decide⟩,⟨253657, by decide⟩,⟨253668, by decide⟩]) unmarked_context_12_23316_253669 node_context_12_23316_253669
  intro a
  fin_cases a
  · exact context_13_93264_253595
  · exact context_13_93265_253639
  · exact context_13_93266_253657
  · exact context_13_93267_253668

theorem selected_cut_09151 : selected 8 ⟨253693, by decide⟩
    (prefixPartial 13 93268) = some ⟨13, 2, 0, 253693, 93268, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_93268_253693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93268 ⟨253693, by decide⟩ :=
  accepted_of_selected 13 93268 ⟨253693, by decide⟩ ⟨13, 2, 0, 253693, 93268, 1813, 16384⟩
    (by decide) selected_cut_09151

theorem selected_cut_09152 : selected 8 ⟨253727, by decide⟩
    (prefixPartial 13 93269) = some ⟨13, 2, 0, 253727, 93269, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_93269_253727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93269 ⟨253727, by decide⟩ :=
  accepted_of_selected 13 93269 ⟨253727, by decide⟩ ⟨13, 2, 0, 253727, 93269, 2193, 16384⟩
    (by decide) selected_cut_09152

theorem selected_cut_09153 : selected 8 ⟨253748, by decide⟩
    (prefixPartial 13 93270) = some ⟨13, 2, 0, 253748, 93270, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_93270_253748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93270 ⟨253748, by decide⟩ :=
  accepted_of_selected 13 93270 ⟨253748, by decide⟩ ⟨13, 2, 0, 253748, 93270, 1397, 16384⟩
    (by decide) selected_cut_09153

theorem selected_cut_09154 : selected 8 ⟨253753, by decide⟩
    (prefixPartial 13 93271) = some ⟨13, 2, 0, 253753, 93271, 897, 16384⟩ := by
  decide +kernel

theorem context_13_93271_253753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93271 ⟨253753, by decide⟩ :=
  accepted_of_selected 13 93271 ⟨253753, by decide⟩ ⟨13, 2, 0, 253753, 93271, 897, 16384⟩
    (by decide) selected_cut_09154

theorem unmarked_context_12_23317_253754 : frontier 9 ⟨253754, by decide⟩
    (prefixCache 12 23317) (prefixPartial 12 23317) = false := by
  decide +kernel

theorem node_context_12_23317_253754 : EJMOriginalGlobalDAGData.nodes 9 ⟨253754, by decide⟩ =
    .split (coordinate 12) (![⟨253693, by decide⟩,⟨253727, by decide⟩,⟨253748, by decide⟩,⟨253753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23317_253754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23317 ⟨253754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23317
    ⟨253754, by decide⟩ (by decide) (![⟨253693, by decide⟩,⟨253727, by decide⟩,⟨253748, by decide⟩,⟨253753, by decide⟩]) unmarked_context_12_23317_253754 node_context_12_23317_253754
  intro a
  fin_cases a
  · exact context_13_93268_253693
  · exact context_13_93269_253727
  · exact context_13_93270_253748
  · exact context_13_93271_253753

theorem selected_cut_09155 : selected 8 ⟨253786, by decide⟩
    (prefixPartial 13 93272) = some ⟨13, 2, 0, 253786, 93272, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_93272_253786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93272 ⟨253786, by decide⟩ :=
  accepted_of_selected 13 93272 ⟨253786, by decide⟩ ⟨13, 2, 0, 253786, 93272, 2309, 16384⟩
    (by decide) selected_cut_09155

theorem selected_cut_09156 : selected 8 ⟨253831, by decide⟩
    (prefixPartial 13 93273) = some ⟨13, 2, 0, 253831, 93273, 2985, 16384⟩ := by
  decide +kernel

theorem context_13_93273_253831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93273 ⟨253831, by decide⟩ :=
  accepted_of_selected 13 93273 ⟨253831, by decide⟩ ⟨13, 2, 0, 253831, 93273, 2985, 16384⟩
    (by decide) selected_cut_09156

theorem selected_cut_09157 : selected 8 ⟨253857, by decide⟩
    (prefixPartial 13 93274) = some ⟨13, 2, 0, 253857, 93274, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_93274_253857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93274 ⟨253857, by decide⟩ :=
  accepted_of_selected 13 93274 ⟨253857, by decide⟩ ⟨13, 2, 0, 253857, 93274, 1813, 16384⟩
    (by decide) selected_cut_09157

theorem selected_cut_09158 : selected 8 ⟨253864, by decide⟩
    (prefixPartial 13 93275) = some ⟨13, 2, 0, 253864, 93275, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_93275_253864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93275 ⟨253864, by decide⟩ :=
  accepted_of_selected 13 93275 ⟨253864, by decide⟩ ⟨13, 2, 0, 253864, 93275, 1021, 16384⟩
    (by decide) selected_cut_09158

theorem unmarked_context_12_23318_253865 : frontier 9 ⟨253865, by decide⟩
    (prefixCache 12 23318) (prefixPartial 12 23318) = false := by
  decide +kernel

theorem node_context_12_23318_253865 : EJMOriginalGlobalDAGData.nodes 9 ⟨253865, by decide⟩ =
    .split (coordinate 12) (![⟨253786, by decide⟩,⟨253831, by decide⟩,⟨253857, by decide⟩,⟨253864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23318_253865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23318 ⟨253865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23318
    ⟨253865, by decide⟩ (by decide) (![⟨253786, by decide⟩,⟨253831, by decide⟩,⟨253857, by decide⟩,⟨253864, by decide⟩]) unmarked_context_12_23318_253865 node_context_12_23318_253865
  intro a
  fin_cases a
  · exact context_13_93272_253786
  · exact context_13_93273_253831
  · exact context_13_93274_253857
  · exact context_13_93275_253864

theorem selected_cut_09159 : selected 8 ⟨253888, by decide⟩
    (prefixPartial 13 93276) = some ⟨13, 2, 0, 253888, 93276, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_93276_253888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93276 ⟨253888, by decide⟩ :=
  accepted_of_selected 13 93276 ⟨253888, by decide⟩ ⟨13, 2, 0, 253888, 93276, 2001, 16384⟩
    (by decide) selected_cut_09159

theorem selected_cut_09160 : selected 8 ⟨253921, by decide⟩
    (prefixPartial 13 93277) = some ⟨13, 2, 0, 253921, 93277, 2737, 16384⟩ := by
  decide +kernel

theorem context_13_93277_253921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93277 ⟨253921, by decide⟩ :=
  accepted_of_selected 13 93277 ⟨253921, by decide⟩ ⟨13, 2, 0, 253921, 93277, 2737, 16384⟩
    (by decide) selected_cut_09160

theorem selected_cut_09161 : selected 8 ⟨253940, by decide⟩
    (prefixPartial 13 93278) = some ⟨13, 2, 0, 253940, 93278, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_93278_253940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93278 ⟨253940, by decide⟩ :=
  accepted_of_selected 13 93278 ⟨253940, by decide⟩ ⟨13, 2, 0, 253940, 93278, 1525, 16384⟩
    (by decide) selected_cut_09161

theorem selected_cut_09162 : selected 8 ⟨253945, by decide⟩
    (prefixPartial 13 93279) = some ⟨13, 2, 0, 253945, 93279, 861, 16384⟩ := by
  decide +kernel

theorem context_13_93279_253945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93279 ⟨253945, by decide⟩ :=
  accepted_of_selected 13 93279 ⟨253945, by decide⟩ ⟨13, 2, 0, 253945, 93279, 861, 16384⟩
    (by decide) selected_cut_09162

theorem unmarked_context_12_23319_253946 : frontier 9 ⟨253946, by decide⟩
    (prefixCache 12 23319) (prefixPartial 12 23319) = false := by
  decide +kernel

theorem node_context_12_23319_253946 : EJMOriginalGlobalDAGData.nodes 9 ⟨253946, by decide⟩ =
    .split (coordinate 12) (![⟨253888, by decide⟩,⟨253921, by decide⟩,⟨253940, by decide⟩,⟨253945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23319_253946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23319 ⟨253946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23319
    ⟨253946, by decide⟩ (by decide) (![⟨253888, by decide⟩,⟨253921, by decide⟩,⟨253940, by decide⟩,⟨253945, by decide⟩]) unmarked_context_12_23319_253946 node_context_12_23319_253946
  intro a
  fin_cases a
  · exact context_13_93276_253888
  · exact context_13_93277_253921
  · exact context_13_93278_253940
  · exact context_13_93279_253945

theorem unmarked_context_11_5829_253947 : frontier 10 ⟨253947, by decide⟩
    (prefixCache 11 5829) (prefixPartial 11 5829) = false := by
  decide +kernel

theorem node_context_11_5829_253947 : EJMOriginalGlobalDAGData.nodes 10 ⟨253947, by decide⟩ =
    .split (coordinate 11) (![⟨253669, by decide⟩,⟨253754, by decide⟩,⟨253865, by decide⟩,⟨253946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5829_253947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5829 ⟨253947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5829
    ⟨253947, by decide⟩ (by decide) (![⟨253669, by decide⟩,⟨253754, by decide⟩,⟨253865, by decide⟩,⟨253946, by decide⟩]) unmarked_context_11_5829_253947 node_context_11_5829_253947
  intro a
  fin_cases a
  · exact context_12_23316_253669
  · exact context_12_23317_253754
  · exact context_12_23318_253865
  · exact context_12_23319_253946

theorem selected_cut_09163 : selected 8 ⟨253965, by decide⟩
    (prefixPartial 13 93280) = some ⟨13, 2, 0, 253965, 93280, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_93280_253965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93280 ⟨253965, by decide⟩ :=
  accepted_of_selected 13 93280 ⟨253965, by decide⟩ ⟨13, 2, 0, 253965, 93280, 1425, 16384⟩
    (by decide) selected_cut_09163

theorem selected_cut_09164 : selected 8 ⟨253996, by decide⟩
    (prefixPartial 13 93281) = some ⟨13, 2, 0, 253996, 93281, 2805, 16384⟩ := by
  decide +kernel

theorem context_13_93281_253996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93281 ⟨253996, by decide⟩ :=
  accepted_of_selected 13 93281 ⟨253996, by decide⟩ ⟨13, 2, 0, 253996, 93281, 2805, 16384⟩
    (by decide) selected_cut_09164

theorem selected_cut_09165 : selected 8 ⟨254023, by decide⟩
    (prefixPartial 13 93282) = some ⟨13, 2, 0, 254023, 93282, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_93282_254023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93282 ⟨254023, by decide⟩ :=
  accepted_of_selected 13 93282 ⟨254023, by decide⟩ ⟨13, 2, 0, 254023, 93282, 1869, 16384⟩
    (by decide) selected_cut_09165

theorem selected_cut_09166 : selected 8 ⟨254035, by decide⟩
    (prefixPartial 13 93283) = some ⟨13, 2, 0, 254035, 93283, 885, 16384⟩ := by
  decide +kernel

theorem context_13_93283_254035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93283 ⟨254035, by decide⟩ :=
  accepted_of_selected 13 93283 ⟨254035, by decide⟩ ⟨13, 2, 0, 254035, 93283, 885, 16384⟩
    (by decide) selected_cut_09166

theorem unmarked_context_12_23320_254036 : frontier 9 ⟨254036, by decide⟩
    (prefixCache 12 23320) (prefixPartial 12 23320) = false := by
  decide +kernel

theorem node_context_12_23320_254036 : EJMOriginalGlobalDAGData.nodes 9 ⟨254036, by decide⟩ =
    .split (coordinate 12) (![⟨253965, by decide⟩,⟨253996, by decide⟩,⟨254023, by decide⟩,⟨254035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23320_254036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23320 ⟨254036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23320
    ⟨254036, by decide⟩ (by decide) (![⟨253965, by decide⟩,⟨253996, by decide⟩,⟨254023, by decide⟩,⟨254035, by decide⟩]) unmarked_context_12_23320_254036 node_context_12_23320_254036
  intro a
  fin_cases a
  · exact context_13_93280_253965
  · exact context_13_93281_253996
  · exact context_13_93282_254023
  · exact context_13_93283_254035

theorem selected_cut_09167 : selected 8 ⟨254062, by decide⟩
    (prefixPartial 13 93284) = some ⟨13, 2, 0, 254062, 93284, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_93284_254062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93284 ⟨254062, by decide⟩ :=
  accepted_of_selected 13 93284 ⟨254062, by decide⟩ ⟨13, 2, 0, 254062, 93284, 1601, 16384⟩
    (by decide) selected_cut_09167

theorem selected_cut_09168 : selected 8 ⟨254095, by decide⟩
    (prefixPartial 13 93285) = some ⟨13, 2, 0, 254095, 93285, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_93285_254095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93285 ⟨254095, by decide⟩ :=
  accepted_of_selected 13 93285 ⟨254095, by decide⟩ ⟨13, 2, 0, 254095, 93285, 2293, 16384⟩
    (by decide) selected_cut_09168

theorem selected_cut_09169 : selected 8 ⟨254124, by decide⟩
    (prefixPartial 13 93286) = some ⟨13, 2, 0, 254124, 93286, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_93286_254124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93286 ⟨254124, by decide⟩ :=
  accepted_of_selected 13 93286 ⟨254124, by decide⟩ ⟨13, 2, 0, 254124, 93286, 1957, 16384⟩
    (by decide) selected_cut_09169

theorem selected_cut_09170 : selected 8 ⟨254137, by decide⟩
    (prefixPartial 13 93287) = some ⟨13, 2, 0, 254137, 93287, 885, 16384⟩ := by
  decide +kernel

theorem context_13_93287_254137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93287 ⟨254137, by decide⟩ :=
  accepted_of_selected 13 93287 ⟨254137, by decide⟩ ⟨13, 2, 0, 254137, 93287, 885, 16384⟩
    (by decide) selected_cut_09170

theorem unmarked_context_12_23321_254138 : frontier 9 ⟨254138, by decide⟩
    (prefixCache 12 23321) (prefixPartial 12 23321) = false := by
  decide +kernel

theorem node_context_12_23321_254138 : EJMOriginalGlobalDAGData.nodes 9 ⟨254138, by decide⟩ =
    .split (coordinate 12) (![⟨254062, by decide⟩,⟨254095, by decide⟩,⟨254124, by decide⟩,⟨254137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23321_254138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23321 ⟨254138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23321
    ⟨254138, by decide⟩ (by decide) (![⟨254062, by decide⟩,⟨254095, by decide⟩,⟨254124, by decide⟩,⟨254137, by decide⟩]) unmarked_context_12_23321_254138 node_context_12_23321_254138
  intro a
  fin_cases a
  · exact context_13_93284_254062
  · exact context_13_93285_254095
  · exact context_13_93286_254124
  · exact context_13_93287_254137

theorem selected_cut_09171 : selected 8 ⟨254162, by decide⟩
    (prefixPartial 13 93288) = some ⟨13, 2, 0, 254162, 93288, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_93288_254162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93288 ⟨254162, by decide⟩ :=
  accepted_of_selected 13 93288 ⟨254162, by decide⟩ ⟨13, 2, 0, 254162, 93288, 1913, 16384⟩
    (by decide) selected_cut_09171

theorem selected_cut_09172 : selected 8 ⟨254205, by decide⟩
    (prefixPartial 13 93289) = some ⟨13, 2, 0, 254205, 93289, 3133, 16384⟩ := by
  decide +kernel

theorem context_13_93289_254205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93289 ⟨254205, by decide⟩ :=
  accepted_of_selected 13 93289 ⟨254205, by decide⟩ ⟨13, 2, 0, 254205, 93289, 3133, 16384⟩
    (by decide) selected_cut_09172

theorem selected_cut_09173 : selected 8 ⟨254237, by decide⟩
    (prefixPartial 13 93290) = some ⟨13, 2, 0, 254237, 93290, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_93290_254237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93290 ⟨254237, by decide⟩ :=
  accepted_of_selected 13 93290 ⟨254237, by decide⟩ ⟨13, 2, 0, 254237, 93290, 2369, 16384⟩
    (by decide) selected_cut_09173

theorem selected_cut_09174 : selected 8 ⟨254245, by decide⟩
    (prefixPartial 13 93291) = some ⟨13, 2, 0, 254245, 93291, 877, 16384⟩ := by
  decide +kernel

theorem context_13_93291_254245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93291 ⟨254245, by decide⟩ :=
  accepted_of_selected 13 93291 ⟨254245, by decide⟩ ⟨13, 2, 0, 254245, 93291, 877, 16384⟩
    (by decide) selected_cut_09174

theorem unmarked_context_12_23322_254246 : frontier 9 ⟨254246, by decide⟩
    (prefixCache 12 23322) (prefixPartial 12 23322) = false := by
  decide +kernel

theorem node_context_12_23322_254246 : EJMOriginalGlobalDAGData.nodes 9 ⟨254246, by decide⟩ =
    .split (coordinate 12) (![⟨254162, by decide⟩,⟨254205, by decide⟩,⟨254237, by decide⟩,⟨254245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23322_254246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23322 ⟨254246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23322
    ⟨254246, by decide⟩ (by decide) (![⟨254162, by decide⟩,⟨254205, by decide⟩,⟨254237, by decide⟩,⟨254245, by decide⟩]) unmarked_context_12_23322_254246 node_context_12_23322_254246
  intro a
  fin_cases a
  · exact context_13_93288_254162
  · exact context_13_93289_254205
  · exact context_13_93290_254237
  · exact context_13_93291_254245

theorem selected_cut_09175 : selected 8 ⟨254268, by decide⟩
    (prefixPartial 13 93292) = some ⟨13, 2, 0, 254268, 93292, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_93292_254268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93292 ⟨254268, by decide⟩ :=
  accepted_of_selected 13 93292 ⟨254268, by decide⟩ ⟨13, 2, 0, 254268, 93292, 1729, 16384⟩
    (by decide) selected_cut_09175

theorem selected_cut_09176 : selected 8 ⟨254309, by decide⟩
    (prefixPartial 13 93293) = some ⟨13, 2, 0, 254309, 93293, 3149, 16384⟩ := by
  decide +kernel

theorem context_13_93293_254309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93293 ⟨254309, by decide⟩ :=
  accepted_of_selected 13 93293 ⟨254309, by decide⟩ ⟨13, 2, 0, 254309, 93293, 3149, 16384⟩
    (by decide) selected_cut_09176

theorem selected_cut_09177 : selected 8 ⟨254330, by decide⟩
    (prefixPartial 13 93294) = some ⟨13, 2, 0, 254330, 93294, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_93294_254330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93294 ⟨254330, by decide⟩ :=
  accepted_of_selected 13 93294 ⟨254330, by decide⟩ ⟨13, 2, 0, 254330, 93294, 1985, 16384⟩
    (by decide) selected_cut_09177

theorem selected_cut_09178 : selected 8 ⟨254334, by decide⟩
    (prefixPartial 13 93295) = some ⟨13, 2, 0, 254334, 93295, 861, 16384⟩ := by
  decide +kernel

theorem context_13_93295_254334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93295 ⟨254334, by decide⟩ :=
  accepted_of_selected 13 93295 ⟨254334, by decide⟩ ⟨13, 2, 0, 254334, 93295, 861, 16384⟩
    (by decide) selected_cut_09178

theorem unmarked_context_12_23323_254335 : frontier 9 ⟨254335, by decide⟩
    (prefixCache 12 23323) (prefixPartial 12 23323) = false := by
  decide +kernel

theorem node_context_12_23323_254335 : EJMOriginalGlobalDAGData.nodes 9 ⟨254335, by decide⟩ =
    .split (coordinate 12) (![⟨254268, by decide⟩,⟨254309, by decide⟩,⟨254330, by decide⟩,⟨254334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23323_254335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23323 ⟨254335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23323
    ⟨254335, by decide⟩ (by decide) (![⟨254268, by decide⟩,⟨254309, by decide⟩,⟨254330, by decide⟩,⟨254334, by decide⟩]) unmarked_context_12_23323_254335 node_context_12_23323_254335
  intro a
  fin_cases a
  · exact context_13_93292_254268
  · exact context_13_93293_254309
  · exact context_13_93294_254330
  · exact context_13_93295_254334

theorem unmarked_context_11_5830_254336 : frontier 10 ⟨254336, by decide⟩
    (prefixCache 11 5830) (prefixPartial 11 5830) = false := by
  decide +kernel

theorem node_context_11_5830_254336 : EJMOriginalGlobalDAGData.nodes 10 ⟨254336, by decide⟩ =
    .split (coordinate 11) (![⟨254036, by decide⟩,⟨254138, by decide⟩,⟨254246, by decide⟩,⟨254335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5830_254336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5830 ⟨254336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5830
    ⟨254336, by decide⟩ (by decide) (![⟨254036, by decide⟩,⟨254138, by decide⟩,⟨254246, by decide⟩,⟨254335, by decide⟩]) unmarked_context_11_5830_254336 node_context_11_5830_254336
  intro a
  fin_cases a
  · exact context_12_23320_254036
  · exact context_12_23321_254138
  · exact context_12_23322_254246
  · exact context_12_23323_254335

theorem selected_cut_09179 : selected 8 ⟨254354, by decide⟩
    (prefixPartial 13 93296) = some ⟨13, 2, 0, 254354, 93296, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_93296_254354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93296 ⟨254354, by decide⟩ :=
  accepted_of_selected 13 93296 ⟨254354, by decide⟩ ⟨13, 2, 0, 254354, 93296, 1465, 16384⟩
    (by decide) selected_cut_09179

theorem selected_cut_09180 : selected 8 ⟨254384, by decide⟩
    (prefixPartial 13 93297) = some ⟨13, 2, 0, 254384, 93297, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_93297_254384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93297 ⟨254384, by decide⟩ :=
  accepted_of_selected 13 93297 ⟨254384, by decide⟩ ⟨13, 2, 0, 254384, 93297, 2497, 16384⟩
    (by decide) selected_cut_09180

theorem selected_cut_09181 : selected 8 ⟨254402, by decide⟩
    (prefixPartial 13 93298) = some ⟨13, 2, 0, 254402, 93298, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_93298_254402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93298 ⟨254402, by decide⟩ :=
  accepted_of_selected 13 93298 ⟨254402, by decide⟩ ⟨13, 2, 0, 254402, 93298, 1385, 16384⟩
    (by decide) selected_cut_09181

theorem selected_cut_09182 : selected 8 ⟨254408, by decide⟩
    (prefixPartial 13 93299) = some ⟨13, 2, 0, 254408, 93299, 797, 16384⟩ := by
  decide +kernel

theorem context_13_93299_254408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93299 ⟨254408, by decide⟩ :=
  accepted_of_selected 13 93299 ⟨254408, by decide⟩ ⟨13, 2, 0, 254408, 93299, 797, 16384⟩
    (by decide) selected_cut_09182

theorem unmarked_context_12_23324_254409 : frontier 9 ⟨254409, by decide⟩
    (prefixCache 12 23324) (prefixPartial 12 23324) = false := by
  decide +kernel

theorem node_context_12_23324_254409 : EJMOriginalGlobalDAGData.nodes 9 ⟨254409, by decide⟩ =
    .split (coordinate 12) (![⟨254354, by decide⟩,⟨254384, by decide⟩,⟨254402, by decide⟩,⟨254408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23324_254409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23324 ⟨254409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23324
    ⟨254409, by decide⟩ (by decide) (![⟨254354, by decide⟩,⟨254384, by decide⟩,⟨254402, by decide⟩,⟨254408, by decide⟩]) unmarked_context_12_23324_254409 node_context_12_23324_254409
  intro a
  fin_cases a
  · exact context_13_93296_254354
  · exact context_13_93297_254384
  · exact context_13_93298_254402
  · exact context_13_93299_254408

theorem selected_cut_09183 : selected 8 ⟨254429, by decide⟩
    (prefixPartial 13 93300) = some ⟨13, 2, 0, 254429, 93300, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_93300_254429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93300 ⟨254429, by decide⟩ :=
  accepted_of_selected 13 93300 ⟨254429, by decide⟩ ⟨13, 2, 0, 254429, 93300, 1593, 16384⟩
    (by decide) selected_cut_09183

theorem selected_cut_09184 : selected 8 ⟨254461, by decide⟩
    (prefixPartial 13 93301) = some ⟨13, 2, 0, 254461, 93301, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_93301_254461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93301 ⟨254461, by decide⟩ :=
  accepted_of_selected 13 93301 ⟨254461, by decide⟩ ⟨13, 2, 0, 254461, 93301, 2089, 16384⟩
    (by decide) selected_cut_09184

theorem selected_cut_09185 : selected 8 ⟨254486, by decide⟩
    (prefixPartial 13 93302) = some ⟨13, 2, 0, 254486, 93302, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_93302_254486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93302 ⟨254486, by decide⟩ :=
  accepted_of_selected 13 93302 ⟨254486, by decide⟩ ⟨13, 2, 0, 254486, 93302, 1633, 16384⟩
    (by decide) selected_cut_09185

theorem selected_cut_09186 : selected 8 ⟨254495, by decide⟩
    (prefixPartial 13 93303) = some ⟨13, 2, 0, 254495, 93303, 741, 16384⟩ := by
  decide +kernel

theorem context_13_93303_254495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93303 ⟨254495, by decide⟩ :=
  accepted_of_selected 13 93303 ⟨254495, by decide⟩ ⟨13, 2, 0, 254495, 93303, 741, 16384⟩
    (by decide) selected_cut_09186

theorem unmarked_context_12_23325_254496 : frontier 9 ⟨254496, by decide⟩
    (prefixCache 12 23325) (prefixPartial 12 23325) = false := by
  decide +kernel

theorem node_context_12_23325_254496 : EJMOriginalGlobalDAGData.nodes 9 ⟨254496, by decide⟩ =
    .split (coordinate 12) (![⟨254429, by decide⟩,⟨254461, by decide⟩,⟨254486, by decide⟩,⟨254495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23325_254496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23325 ⟨254496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23325
    ⟨254496, by decide⟩ (by decide) (![⟨254429, by decide⟩,⟨254461, by decide⟩,⟨254486, by decide⟩,⟨254495, by decide⟩]) unmarked_context_12_23325_254496 node_context_12_23325_254496
  intro a
  fin_cases a
  · exact context_13_93300_254429
  · exact context_13_93301_254461
  · exact context_13_93302_254486
  · exact context_13_93303_254495

theorem selected_cut_09187 : selected 8 ⟨254520, by decide⟩
    (prefixPartial 13 93304) = some ⟨13, 2, 0, 254520, 93304, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_93304_254520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93304 ⟨254520, by decide⟩ :=
  accepted_of_selected 13 93304 ⟨254520, by decide⟩ ⟨13, 2, 0, 254520, 93304, 1829, 16384⟩
    (by decide) selected_cut_09187

theorem selected_cut_09188 : selected 8 ⟨254571, by decide⟩
    (prefixPartial 13 93305) = some ⟨13, 2, 0, 254571, 93305, 2973, 16384⟩ := by
  decide +kernel

theorem context_13_93305_254571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93305 ⟨254571, by decide⟩ :=
  accepted_of_selected 13 93305 ⟨254571, by decide⟩ ⟨13, 2, 0, 254571, 93305, 2973, 16384⟩
    (by decide) selected_cut_09188

theorem selected_cut_09189 : selected 8 ⟨254594, by decide⟩
    (prefixPartial 13 93306) = some ⟨13, 2, 0, 254594, 93306, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_93306_254594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93306 ⟨254594, by decide⟩ :=
  accepted_of_selected 13 93306 ⟨254594, by decide⟩ ⟨13, 2, 0, 254594, 93306, 1881, 16384⟩
    (by decide) selected_cut_09189

theorem selected_cut_09190 : selected 8 ⟨254601, by decide⟩
    (prefixPartial 13 93307) = some ⟨13, 2, 0, 254601, 93307, 797, 16384⟩ := by
  decide +kernel

theorem context_13_93307_254601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93307 ⟨254601, by decide⟩ :=
  accepted_of_selected 13 93307 ⟨254601, by decide⟩ ⟨13, 2, 0, 254601, 93307, 797, 16384⟩
    (by decide) selected_cut_09190

theorem unmarked_context_12_23326_254602 : frontier 9 ⟨254602, by decide⟩
    (prefixCache 12 23326) (prefixPartial 12 23326) = false := by
  decide +kernel

theorem node_context_12_23326_254602 : EJMOriginalGlobalDAGData.nodes 9 ⟨254602, by decide⟩ =
    .split (coordinate 12) (![⟨254520, by decide⟩,⟨254571, by decide⟩,⟨254594, by decide⟩,⟨254601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23326_254602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23326 ⟨254602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23326
    ⟨254602, by decide⟩ (by decide) (![⟨254520, by decide⟩,⟨254571, by decide⟩,⟨254594, by decide⟩,⟨254601, by decide⟩]) unmarked_context_12_23326_254602 node_context_12_23326_254602
  intro a
  fin_cases a
  · exact context_13_93304_254520
  · exact context_13_93305_254571
  · exact context_13_93306_254594
  · exact context_13_93307_254601

theorem selected_cut_09191 : selected 8 ⟨254646, by decide⟩
    (prefixPartial 13 93308) = some ⟨13, 2, 0, 254646, 93308, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_93308_254646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93308 ⟨254646, by decide⟩ :=
  accepted_of_selected 13 93308 ⟨254646, by decide⟩ ⟨13, 2, 0, 254646, 93308, 2757, 16384⟩
    (by decide) selected_cut_09191

theorem selected_cut_09192 : selected 7 ⟨254674, by decide⟩
    (prefixPartial 14 373236) = some ⟨14, 2, 0, 254674, 373236, 1253, 4096⟩ := by
  decide +kernel

theorem context_14_373236_254674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 373236 ⟨254674, by decide⟩ :=
  accepted_of_selected 14 373236 ⟨254674, by decide⟩ ⟨14, 2, 0, 254674, 373236, 1253, 4096⟩
    (by decide) selected_cut_09192

theorem selected_cut_09193 : selected 7 ⟨254701, by decide⟩
    (prefixPartial 14 373237) = some ⟨14, 2, 0, 254701, 373237, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_373237_254701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 373237 ⟨254701, by decide⟩ :=
  accepted_of_selected 14 373237 ⟨254701, by decide⟩ ⟨14, 2, 0, 254701, 373237, 1161, 4096⟩
    (by decide) selected_cut_09193

theorem selected_cut_09194 : selected 7 ⟨254728, by decide⟩
    (prefixPartial 14 373238) = some ⟨14, 2, 0, 254728, 373238, 1221, 4096⟩ := by
  decide +kernel

theorem context_14_373238_254728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 373238 ⟨254728, by decide⟩ :=
  accepted_of_selected 14 373238 ⟨254728, by decide⟩ ⟨14, 2, 0, 254728, 373238, 1221, 4096⟩
    (by decide) selected_cut_09194

theorem selected_cut_09195 : selected 7 ⟨254750, by decide⟩
    (prefixPartial 14 373239) = some ⟨14, 2, 0, 254750, 373239, 949, 4096⟩ := by
  decide +kernel

theorem context_14_373239_254750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 373239 ⟨254750, by decide⟩ :=
  accepted_of_selected 14 373239 ⟨254750, by decide⟩ ⟨14, 2, 0, 254750, 373239, 949, 4096⟩
    (by decide) selected_cut_09195

theorem unmarked_context_13_93309_254751 : frontier 8 ⟨254751, by decide⟩
    (prefixCache 13 93309) (prefixPartial 13 93309) = false := by
  decide +kernel

theorem node_context_13_93309_254751 : EJMOriginalGlobalDAGData.nodes 8 ⟨254751, by decide⟩ =
    .split (coordinate 13) (![⟨254674, by decide⟩,⟨254701, by decide⟩,⟨254728, by decide⟩,⟨254750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93309_254751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93309 ⟨254751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93309
    ⟨254751, by decide⟩ (by decide) (![⟨254674, by decide⟩,⟨254701, by decide⟩,⟨254728, by decide⟩,⟨254750, by decide⟩]) unmarked_context_13_93309_254751 node_context_13_93309_254751
  intro a
  fin_cases a
  · exact context_14_373236_254674
  · exact context_14_373237_254701
  · exact context_14_373238_254728
  · exact context_14_373239_254750

theorem selected_cut_09196 : selected 8 ⟨254796, by decide⟩
    (prefixPartial 13 93310) = some ⟨13, 2, 0, 254796, 93310, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_93310_254796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93310 ⟨254796, by decide⟩ :=
  accepted_of_selected 13 93310 ⟨254796, by decide⟩ ⟨13, 2, 0, 254796, 93310, 2505, 16384⟩
    (by decide) selected_cut_09196

theorem selected_cut_09197 : selected 8 ⟨254822, by decide⟩
    (prefixPartial 13 93311) = some ⟨13, 2, 0, 254822, 93311, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_93311_254822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93311 ⟨254822, by decide⟩ :=
  accepted_of_selected 13 93311 ⟨254822, by decide⟩ ⟨13, 2, 0, 254822, 93311, 1093, 16384⟩
    (by decide) selected_cut_09197

theorem unmarked_context_12_23327_254823 : frontier 9 ⟨254823, by decide⟩
    (prefixCache 12 23327) (prefixPartial 12 23327) = false := by
  decide +kernel

theorem node_context_12_23327_254823 : EJMOriginalGlobalDAGData.nodes 9 ⟨254823, by decide⟩ =
    .split (coordinate 12) (![⟨254646, by decide⟩,⟨254751, by decide⟩,⟨254796, by decide⟩,⟨254822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23327_254823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23327 ⟨254823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23327
    ⟨254823, by decide⟩ (by decide) (![⟨254646, by decide⟩,⟨254751, by decide⟩,⟨254796, by decide⟩,⟨254822, by decide⟩]) unmarked_context_12_23327_254823 node_context_12_23327_254823
  intro a
  fin_cases a
  · exact context_13_93308_254646
  · exact context_13_93309_254751
  · exact context_13_93310_254796
  · exact context_13_93311_254822

theorem unmarked_context_11_5831_254824 : frontier 10 ⟨254824, by decide⟩
    (prefixCache 11 5831) (prefixPartial 11 5831) = false := by
  decide +kernel

theorem node_context_11_5831_254824 : EJMOriginalGlobalDAGData.nodes 10 ⟨254824, by decide⟩ =
    .split (coordinate 11) (![⟨254409, by decide⟩,⟨254496, by decide⟩,⟨254602, by decide⟩,⟨254823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5831_254824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5831 ⟨254824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5831
    ⟨254824, by decide⟩ (by decide) (![⟨254409, by decide⟩,⟨254496, by decide⟩,⟨254602, by decide⟩,⟨254823, by decide⟩]) unmarked_context_11_5831_254824 node_context_11_5831_254824
  intro a
  fin_cases a
  · exact context_12_23324_254409
  · exact context_12_23325_254496
  · exact context_12_23326_254602
  · exact context_12_23327_254823

theorem unmarked_context_10_1457_254825 : frontier 11 ⟨254825, by decide⟩
    (prefixCache 10 1457) (prefixPartial 10 1457) = false := by
  decide +kernel

theorem node_context_10_1457_254825 : EJMOriginalGlobalDAGData.nodes 11 ⟨254825, by decide⟩ =
    .split (coordinate 10) (![⟨253570, by decide⟩,⟨253947, by decide⟩,⟨254336, by decide⟩,⟨254824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1457_254825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1457 ⟨254825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1457
    ⟨254825, by decide⟩ (by decide) (![⟨253570, by decide⟩,⟨253947, by decide⟩,⟨254336, by decide⟩,⟨254824, by decide⟩]) unmarked_context_10_1457_254825 node_context_10_1457_254825
  intro a
  fin_cases a
  · exact context_11_5828_253570
  · exact context_11_5829_253947
  · exact context_11_5830_254336
  · exact context_11_5831_254824

theorem selected_cut_09198 : selected 8 ⟨254843, by decide⟩
    (prefixPartial 13 93312) = some ⟨13, 2, 0, 254843, 93312, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_93312_254843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93312 ⟨254843, by decide⟩ :=
  accepted_of_selected 13 93312 ⟨254843, by decide⟩ ⟨13, 2, 0, 254843, 93312, 1477, 16384⟩
    (by decide) selected_cut_09198

theorem selected_cut_09199 : selected 8 ⟨254868, by decide⟩
    (prefixPartial 13 93313) = some ⟨13, 2, 0, 254868, 93313, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_93313_254868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93313 ⟨254868, by decide⟩ :=
  accepted_of_selected 13 93313 ⟨254868, by decide⟩ ⟨13, 2, 0, 254868, 93313, 2445, 16384⟩
    (by decide) selected_cut_09199

theorem selected_cut_09200 : selected 8 ⟨254884, by decide⟩
    (prefixPartial 13 93314) = some ⟨13, 2, 0, 254884, 93314, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_93314_254884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93314 ⟨254884, by decide⟩ :=
  accepted_of_selected 13 93314 ⟨254884, by decide⟩ ⟨13, 2, 0, 254884, 93314, 1241, 16384⟩
    (by decide) selected_cut_09200

theorem selected_cut_09201 : selected 8 ⟨254889, by decide⟩
    (prefixPartial 13 93315) = some ⟨13, 2, 0, 254889, 93315, 909, 16384⟩ := by
  decide +kernel

theorem context_13_93315_254889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93315 ⟨254889, by decide⟩ :=
  accepted_of_selected 13 93315 ⟨254889, by decide⟩ ⟨13, 2, 0, 254889, 93315, 909, 16384⟩
    (by decide) selected_cut_09201

theorem unmarked_context_12_23328_254890 : frontier 9 ⟨254890, by decide⟩
    (prefixCache 12 23328) (prefixPartial 12 23328) = false := by
  decide +kernel

theorem node_context_12_23328_254890 : EJMOriginalGlobalDAGData.nodes 9 ⟨254890, by decide⟩ =
    .split (coordinate 12) (![⟨254843, by decide⟩,⟨254868, by decide⟩,⟨254884, by decide⟩,⟨254889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23328_254890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23328 ⟨254890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23328
    ⟨254890, by decide⟩ (by decide) (![⟨254843, by decide⟩,⟨254868, by decide⟩,⟨254884, by decide⟩,⟨254889, by decide⟩]) unmarked_context_12_23328_254890 node_context_12_23328_254890
  intro a
  fin_cases a
  · exact context_13_93312_254843
  · exact context_13_93313_254868
  · exact context_13_93314_254884
  · exact context_13_93315_254889

theorem selected_cut_09202 : selected 8 ⟨254905, by decide⟩
    (prefixPartial 13 93316) = some ⟨13, 2, 0, 254905, 93316, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_93316_254905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93316 ⟨254905, by decide⟩ :=
  accepted_of_selected 13 93316 ⟨254905, by decide⟩ ⟨13, 2, 0, 254905, 93316, 1473, 16384⟩
    (by decide) selected_cut_09202

theorem selected_cut_09203 : selected 8 ⟨254936, by decide⟩
    (prefixPartial 13 93317) = some ⟨13, 2, 0, 254936, 93317, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_93317_254936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93317 ⟨254936, by decide⟩ :=
  accepted_of_selected 13 93317 ⟨254936, by decide⟩ ⟨13, 2, 0, 254936, 93317, 2353, 16384⟩
    (by decide) selected_cut_09203

theorem selected_cut_09204 : selected 8 ⟨254954, by decide⟩
    (prefixPartial 13 93318) = some ⟨13, 2, 0, 254954, 93318, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_93318_254954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93318 ⟨254954, by decide⟩ :=
  accepted_of_selected 13 93318 ⟨254954, by decide⟩ ⟨13, 2, 0, 254954, 93318, 1401, 16384⟩
    (by decide) selected_cut_09204

theorem selected_cut_09205 : selected 8 ⟨254966, by decide⟩
    (prefixPartial 13 93319) = some ⟨13, 2, 0, 254966, 93319, 725, 16384⟩ := by
  decide +kernel

theorem context_13_93319_254966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93319 ⟨254966, by decide⟩ :=
  accepted_of_selected 13 93319 ⟨254966, by decide⟩ ⟨13, 2, 0, 254966, 93319, 725, 16384⟩
    (by decide) selected_cut_09205

theorem unmarked_context_12_23329_254967 : frontier 9 ⟨254967, by decide⟩
    (prefixCache 12 23329) (prefixPartial 12 23329) = false := by
  decide +kernel

theorem node_context_12_23329_254967 : EJMOriginalGlobalDAGData.nodes 9 ⟨254967, by decide⟩ =
    .split (coordinate 12) (![⟨254905, by decide⟩,⟨254936, by decide⟩,⟨254954, by decide⟩,⟨254966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23329_254967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23329 ⟨254967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23329
    ⟨254967, by decide⟩ (by decide) (![⟨254905, by decide⟩,⟨254936, by decide⟩,⟨254954, by decide⟩,⟨254966, by decide⟩]) unmarked_context_12_23329_254967 node_context_12_23329_254967
  intro a
  fin_cases a
  · exact context_13_93316_254905
  · exact context_13_93317_254936
  · exact context_13_93318_254954
  · exact context_13_93319_254966

theorem selected_cut_09206 : selected 8 ⟨254993, by decide⟩
    (prefixPartial 13 93320) = some ⟨13, 2, 0, 254993, 93320, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_93320_254993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93320 ⟨254993, by decide⟩ :=
  accepted_of_selected 13 93320 ⟨254993, by decide⟩ ⟨13, 2, 0, 254993, 93320, 1749, 16384⟩
    (by decide) selected_cut_09206

theorem selected_cut_09207 : selected 8 ⟨255037, by decide⟩
    (prefixPartial 13 93321) = some ⟨13, 2, 0, 255037, 93321, 2881, 16384⟩ := by
  decide +kernel

theorem context_13_93321_255037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93321 ⟨255037, by decide⟩ :=
  accepted_of_selected 13 93321 ⟨255037, by decide⟩ ⟨13, 2, 0, 255037, 93321, 2881, 16384⟩
    (by decide) selected_cut_09207

theorem selected_cut_09208 : selected 8 ⟨255056, by decide⟩
    (prefixPartial 13 93322) = some ⟨13, 2, 0, 255056, 93322, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_93322_255056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93322 ⟨255056, by decide⟩ :=
  accepted_of_selected 13 93322 ⟨255056, by decide⟩ ⟨13, 2, 0, 255056, 93322, 1621, 16384⟩
    (by decide) selected_cut_09208

theorem selected_cut_09209 : selected 8 ⟨255062, by decide⟩
    (prefixPartial 13 93323) = some ⟨13, 2, 0, 255062, 93323, 805, 16384⟩ := by
  decide +kernel

theorem context_13_93323_255062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93323 ⟨255062, by decide⟩ :=
  accepted_of_selected 13 93323 ⟨255062, by decide⟩ ⟨13, 2, 0, 255062, 93323, 805, 16384⟩
    (by decide) selected_cut_09209

theorem unmarked_context_12_23330_255063 : frontier 9 ⟨255063, by decide⟩
    (prefixCache 12 23330) (prefixPartial 12 23330) = false := by
  decide +kernel

theorem node_context_12_23330_255063 : EJMOriginalGlobalDAGData.nodes 9 ⟨255063, by decide⟩ =
    .split (coordinate 12) (![⟨254993, by decide⟩,⟨255037, by decide⟩,⟨255056, by decide⟩,⟨255062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23330_255063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23330 ⟨255063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23330
    ⟨255063, by decide⟩ (by decide) (![⟨254993, by decide⟩,⟨255037, by decide⟩,⟨255056, by decide⟩,⟨255062, by decide⟩]) unmarked_context_12_23330_255063 node_context_12_23330_255063
  intro a
  fin_cases a
  · exact context_13_93320_254993
  · exact context_13_93321_255037
  · exact context_13_93322_255056
  · exact context_13_93323_255062

theorem selected_cut_09210 : selected 8 ⟨255080, by decide⟩
    (prefixPartial 13 93324) = some ⟨13, 2, 0, 255080, 93324, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_93324_255080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93324 ⟨255080, by decide⟩ :=
  accepted_of_selected 13 93324 ⟨255080, by decide⟩ ⟨13, 2, 0, 255080, 93324, 1457, 16384⟩
    (by decide) selected_cut_09210

theorem selected_cut_09211 : selected 8 ⟨255119, by decide⟩
    (prefixPartial 13 93325) = some ⟨13, 2, 0, 255119, 93325, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_93325_255119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93325 ⟨255119, by decide⟩ :=
  accepted_of_selected 13 93325 ⟨255119, by decide⟩ ⟨13, 2, 0, 255119, 93325, 2673, 16384⟩
    (by decide) selected_cut_09211

theorem selected_cut_09212 : selected 8 ⟨255137, by decide⟩
    (prefixPartial 13 93326) = some ⟨13, 2, 0, 255137, 93326, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_93326_255137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93326 ⟨255137, by decide⟩ :=
  accepted_of_selected 13 93326 ⟨255137, by decide⟩ ⟨13, 2, 0, 255137, 93326, 1457, 16384⟩
    (by decide) selected_cut_09212

theorem selected_cut_09213 : selected 8 ⟨255143, by decide⟩
    (prefixPartial 13 93327) = some ⟨13, 2, 0, 255143, 93327, 741, 16384⟩ := by
  decide +kernel

theorem context_13_93327_255143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93327 ⟨255143, by decide⟩ :=
  accepted_of_selected 13 93327 ⟨255143, by decide⟩ ⟨13, 2, 0, 255143, 93327, 741, 16384⟩
    (by decide) selected_cut_09213

theorem unmarked_context_12_23331_255144 : frontier 9 ⟨255144, by decide⟩
    (prefixCache 12 23331) (prefixPartial 12 23331) = false := by
  decide +kernel

theorem node_context_12_23331_255144 : EJMOriginalGlobalDAGData.nodes 9 ⟨255144, by decide⟩ =
    .split (coordinate 12) (![⟨255080, by decide⟩,⟨255119, by decide⟩,⟨255137, by decide⟩,⟨255143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23331_255144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23331 ⟨255144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23331
    ⟨255144, by decide⟩ (by decide) (![⟨255080, by decide⟩,⟨255119, by decide⟩,⟨255137, by decide⟩,⟨255143, by decide⟩]) unmarked_context_12_23331_255144 node_context_12_23331_255144
  intro a
  fin_cases a
  · exact context_13_93324_255080
  · exact context_13_93325_255119
  · exact context_13_93326_255137
  · exact context_13_93327_255143

theorem unmarked_context_11_5832_255145 : frontier 10 ⟨255145, by decide⟩
    (prefixCache 11 5832) (prefixPartial 11 5832) = false := by
  decide +kernel

theorem node_context_11_5832_255145 : EJMOriginalGlobalDAGData.nodes 10 ⟨255145, by decide⟩ =
    .split (coordinate 11) (![⟨254890, by decide⟩,⟨254967, by decide⟩,⟨255063, by decide⟩,⟨255144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5832_255145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5832 ⟨255145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5832
    ⟨255145, by decide⟩ (by decide) (![⟨254890, by decide⟩,⟨254967, by decide⟩,⟨255063, by decide⟩,⟨255144, by decide⟩]) unmarked_context_11_5832_255145 node_context_11_5832_255145
  intro a
  fin_cases a
  · exact context_12_23328_254890
  · exact context_12_23329_254967
  · exact context_12_23330_255063
  · exact context_12_23331_255144

theorem selected_cut_09214 : selected 8 ⟨255161, by decide⟩
    (prefixPartial 13 93328) = some ⟨13, 2, 0, 255161, 93328, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_93328_255161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93328 ⟨255161, by decide⟩ :=
  accepted_of_selected 13 93328 ⟨255161, by decide⟩ ⟨13, 2, 0, 255161, 93328, 1145, 16384⟩
    (by decide) selected_cut_09214

theorem selected_cut_09215 : selected 8 ⟨255213, by decide⟩
    (prefixPartial 13 93329) = some ⟨13, 2, 0, 255213, 93329, 2901, 16384⟩ := by
  decide +kernel

theorem context_13_93329_255213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93329 ⟨255213, by decide⟩ :=
  accepted_of_selected 13 93329 ⟨255213, by decide⟩ ⟨13, 2, 0, 255213, 93329, 2901, 16384⟩
    (by decide) selected_cut_09215

theorem selected_cut_09216 : selected 8 ⟨255232, by decide⟩
    (prefixPartial 13 93330) = some ⟨13, 2, 0, 255232, 93330, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_93330_255232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93330 ⟨255232, by decide⟩ :=
  accepted_of_selected 13 93330 ⟨255232, by decide⟩ ⟨13, 2, 0, 255232, 93330, 1257, 16384⟩
    (by decide) selected_cut_09216

theorem selected_cut_09217 : selected 8 ⟨255238, by decide⟩
    (prefixPartial 13 93331) = some ⟨13, 2, 0, 255238, 93331, 917, 16384⟩ := by
  decide +kernel

theorem context_13_93331_255238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93331 ⟨255238, by decide⟩ :=
  accepted_of_selected 13 93331 ⟨255238, by decide⟩ ⟨13, 2, 0, 255238, 93331, 917, 16384⟩
    (by decide) selected_cut_09217

theorem unmarked_context_12_23332_255239 : frontier 9 ⟨255239, by decide⟩
    (prefixCache 12 23332) (prefixPartial 12 23332) = false := by
  decide +kernel

theorem node_context_12_23332_255239 : EJMOriginalGlobalDAGData.nodes 9 ⟨255239, by decide⟩ =
    .split (coordinate 12) (![⟨255161, by decide⟩,⟨255213, by decide⟩,⟨255232, by decide⟩,⟨255238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23332_255239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23332 ⟨255239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23332
    ⟨255239, by decide⟩ (by decide) (![⟨255161, by decide⟩,⟨255213, by decide⟩,⟨255232, by decide⟩,⟨255238, by decide⟩]) unmarked_context_12_23332_255239 node_context_12_23332_255239
  intro a
  fin_cases a
  · exact context_13_93328_255161
  · exact context_13_93329_255213
  · exact context_13_93330_255232
  · exact context_13_93331_255238

theorem selected_cut_09218 : selected 8 ⟨255254, by decide⟩
    (prefixPartial 13 93332) = some ⟨13, 2, 0, 255254, 93332, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_93332_255254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93332 ⟨255254, by decide⟩ :=
  accepted_of_selected 13 93332 ⟨255254, by decide⟩ ⟨13, 2, 0, 255254, 93332, 1025, 16384⟩
    (by decide) selected_cut_09218

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
