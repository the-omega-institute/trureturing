/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover084
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_1427_231106 : frontier 11 ⟨231106, by decide⟩
    (prefixCache 10 1427) (prefixPartial 10 1427) = false := by
  decide +kernel

theorem node_context_10_1427_231106 : EJMOriginalGlobalDAGData.nodes 11 ⟨231106, by decide⟩ =
    .split (coordinate 10) (![⟨230356, by decide⟩,⟨230609, by decide⟩,⟨230879, by decide⟩,⟨231105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1427_231106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1427 ⟨231106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1427
    ⟨231106, by decide⟩ (by decide) (![⟨230356, by decide⟩,⟨230609, by decide⟩,⟨230879, by decide⟩,⟨231105, by decide⟩]) unmarked_context_10_1427_231106 node_context_10_1427_231106
  intro a
  fin_cases a
  · exact context_11_5708_230356
  · exact context_11_5709_230609
  · exact context_11_5710_230879
  · exact context_11_5711_231105

theorem unmarked_context_9_356_231107 : frontier 12 ⟨231107, by decide⟩
    (prefixCache 9 356) (prefixPartial 9 356) = false := by
  decide +kernel

theorem node_context_9_356_231107 : EJMOriginalGlobalDAGData.nodes 12 ⟨231107, by decide⟩ =
    .split (coordinate 9) (![⟨227429, by decide⟩,⟨228785, by decide⟩,⟨230062, by decide⟩,⟨231106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_356_231107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 356 ⟨231107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 356
    ⟨231107, by decide⟩ (by decide) (![⟨227429, by decide⟩,⟨228785, by decide⟩,⟨230062, by decide⟩,⟨231106, by decide⟩]) unmarked_context_9_356_231107 node_context_9_356_231107
  intro a
  fin_cases a
  · exact context_10_1424_227429
  · exact context_10_1425_228785
  · exact context_10_1426_230062
  · exact context_10_1427_231106

theorem selected_cut_08163 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91392) = some ⟨13, 1, 0, 3444, 91392, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91392_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91392 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91392 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91392, 1, 16384⟩
    (by decide) selected_cut_08163

theorem selected_cut_08164 : selected 8 ⟨231130, by decide⟩
    (prefixPartial 13 91393) = some ⟨13, 2, 0, 231130, 91393, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_91393_231130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91393 ⟨231130, by decide⟩ :=
  accepted_of_selected 13 91393 ⟨231130, by decide⟩ ⟨13, 2, 0, 231130, 91393, 2417, 16384⟩
    (by decide) selected_cut_08164

theorem selected_cut_08165 : selected 8 ⟨231148, by decide⟩
    (prefixPartial 13 91394) = some ⟨13, 2, 0, 231148, 91394, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_91394_231148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91394 ⟨231148, by decide⟩ :=
  accepted_of_selected 13 91394 ⟨231148, by decide⟩ ⟨13, 2, 0, 231148, 91394, 1633, 16384⟩
    (by decide) selected_cut_08165

theorem selected_cut_08166 : selected 8 ⟨231155, by decide⟩
    (prefixPartial 13 91395) = some ⟨13, 2, 0, 231155, 91395, 949, 16384⟩ := by
  decide +kernel

theorem context_13_91395_231155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91395 ⟨231155, by decide⟩ :=
  accepted_of_selected 13 91395 ⟨231155, by decide⟩ ⟨13, 2, 0, 231155, 91395, 949, 16384⟩
    (by decide) selected_cut_08166

theorem unmarked_context_12_22848_231156 : frontier 9 ⟨231156, by decide⟩
    (prefixCache 12 22848) (prefixPartial 12 22848) = false := by
  decide +kernel

theorem node_context_12_22848_231156 : EJMOriginalGlobalDAGData.nodes 9 ⟨231156, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231130, by decide⟩,⟨231148, by decide⟩,⟨231155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22848_231156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22848 ⟨231156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22848
    ⟨231156, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231130, by decide⟩,⟨231148, by decide⟩,⟨231155, by decide⟩]) unmarked_context_12_22848_231156 node_context_12_22848_231156
  intro a
  fin_cases a
  · exact context_13_91392_3444
  · exact context_13_91393_231130
  · exact context_13_91394_231148
  · exact context_13_91395_231155

theorem selected_cut_08167 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91396) = some ⟨13, 1, 0, 3444, 91396, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91396_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91396 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91396 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91396, 1, 16384⟩
    (by decide) selected_cut_08167

theorem selected_cut_08168 : selected 8 ⟨231205, by decide⟩
    (prefixPartial 13 91397) = some ⟨13, 2, 0, 231205, 91397, 3269, 16384⟩ := by
  decide +kernel

theorem context_13_91397_231205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91397 ⟨231205, by decide⟩ :=
  accepted_of_selected 13 91397 ⟨231205, by decide⟩ ⟨13, 2, 0, 231205, 91397, 3269, 16384⟩
    (by decide) selected_cut_08168

theorem selected_cut_08169 : selected 8 ⟨231224, by decide⟩
    (prefixPartial 13 91398) = some ⟨13, 2, 0, 231224, 91398, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_91398_231224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91398 ⟨231224, by decide⟩ :=
  accepted_of_selected 13 91398 ⟨231224, by decide⟩ ⟨13, 2, 0, 231224, 91398, 2089, 16384⟩
    (by decide) selected_cut_08169

theorem selected_cut_08170 : selected 8 ⟨231235, by decide⟩
    (prefixPartial 13 91399) = some ⟨13, 2, 0, 231235, 91399, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_91399_231235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91399 ⟨231235, by decide⟩ :=
  accepted_of_selected 13 91399 ⟨231235, by decide⟩ ⟨13, 2, 0, 231235, 91399, 1169, 16384⟩
    (by decide) selected_cut_08170

theorem unmarked_context_12_22849_231236 : frontier 9 ⟨231236, by decide⟩
    (prefixCache 12 22849) (prefixPartial 12 22849) = false := by
  decide +kernel

theorem node_context_12_22849_231236 : EJMOriginalGlobalDAGData.nodes 9 ⟨231236, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231205, by decide⟩,⟨231224, by decide⟩,⟨231235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22849_231236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22849 ⟨231236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22849
    ⟨231236, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231205, by decide⟩,⟨231224, by decide⟩,⟨231235, by decide⟩]) unmarked_context_12_22849_231236 node_context_12_22849_231236
  intro a
  fin_cases a
  · exact context_13_91396_3444
  · exact context_13_91397_231205
  · exact context_13_91398_231224
  · exact context_13_91399_231235

theorem selected_cut_08171 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91400) = some ⟨13, 1, 0, 3444, 91400, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91400_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91400 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91400 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91400, 1, 16384⟩
    (by decide) selected_cut_08171

theorem selected_cut_08172 : selected 8 ⟨231272, by decide⟩
    (prefixPartial 13 91401) = some ⟨13, 2, 0, 231272, 91401, 2945, 16384⟩ := by
  decide +kernel

theorem context_13_91401_231272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91401 ⟨231272, by decide⟩ :=
  accepted_of_selected 13 91401 ⟨231272, by decide⟩ ⟨13, 2, 0, 231272, 91401, 2945, 16384⟩
    (by decide) selected_cut_08172

theorem selected_cut_08173 : selected 8 ⟨231293, by decide⟩
    (prefixPartial 13 91402) = some ⟨13, 2, 0, 231293, 91402, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_91402_231293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91402 ⟨231293, by decide⟩ :=
  accepted_of_selected 13 91402 ⟨231293, by decide⟩ ⟨13, 2, 0, 231293, 91402, 2009, 16384⟩
    (by decide) selected_cut_08173

theorem selected_cut_08174 : selected 8 ⟨231302, by decide⟩
    (prefixPartial 13 91403) = some ⟨13, 2, 0, 231302, 91403, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_91403_231302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91403 ⟨231302, by decide⟩ :=
  accepted_of_selected 13 91403 ⟨231302, by decide⟩ ⟨13, 2, 0, 231302, 91403, 1073, 16384⟩
    (by decide) selected_cut_08174

theorem unmarked_context_12_22850_231303 : frontier 9 ⟨231303, by decide⟩
    (prefixCache 12 22850) (prefixPartial 12 22850) = false := by
  decide +kernel

theorem node_context_12_22850_231303 : EJMOriginalGlobalDAGData.nodes 9 ⟨231303, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231272, by decide⟩,⟨231293, by decide⟩,⟨231302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22850_231303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22850 ⟨231303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22850
    ⟨231303, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231272, by decide⟩,⟨231293, by decide⟩,⟨231302, by decide⟩]) unmarked_context_12_22850_231303 node_context_12_22850_231303
  intro a
  fin_cases a
  · exact context_13_91400_3444
  · exact context_13_91401_231272
  · exact context_13_91402_231293
  · exact context_13_91403_231302

theorem selected_cut_08175 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91404) = some ⟨13, 1, 0, 3444, 91404, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91404_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91404 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91404 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91404, 1, 16384⟩
    (by decide) selected_cut_08175

theorem selected_cut_08176 : selected 8 ⟨231337, by decide⟩
    (prefixPartial 13 91405) = some ⟨13, 2, 0, 231337, 91405, 2909, 16384⟩ := by
  decide +kernel

theorem context_13_91405_231337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91405 ⟨231337, by decide⟩ :=
  accepted_of_selected 13 91405 ⟨231337, by decide⟩ ⟨13, 2, 0, 231337, 91405, 2909, 16384⟩
    (by decide) selected_cut_08176

theorem selected_cut_08177 : selected 8 ⟨231361, by decide⟩
    (prefixPartial 13 91406) = some ⟨13, 2, 0, 231361, 91406, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_91406_231361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91406 ⟨231361, by decide⟩ :=
  accepted_of_selected 13 91406 ⟨231361, by decide⟩ ⟨13, 2, 0, 231361, 91406, 2181, 16384⟩
    (by decide) selected_cut_08177

theorem selected_cut_08178 : selected 8 ⟨231370, by decide⟩
    (prefixPartial 13 91407) = some ⟨13, 2, 0, 231370, 91407, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_91407_231370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91407 ⟨231370, by decide⟩ :=
  accepted_of_selected 13 91407 ⟨231370, by decide⟩ ⟨13, 2, 0, 231370, 91407, 1057, 16384⟩
    (by decide) selected_cut_08178

theorem unmarked_context_12_22851_231371 : frontier 9 ⟨231371, by decide⟩
    (prefixCache 12 22851) (prefixPartial 12 22851) = false := by
  decide +kernel

theorem node_context_12_22851_231371 : EJMOriginalGlobalDAGData.nodes 9 ⟨231371, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231337, by decide⟩,⟨231361, by decide⟩,⟨231370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22851_231371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22851 ⟨231371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22851
    ⟨231371, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231337, by decide⟩,⟨231361, by decide⟩,⟨231370, by decide⟩]) unmarked_context_12_22851_231371 node_context_12_22851_231371
  intro a
  fin_cases a
  · exact context_13_91404_3444
  · exact context_13_91405_231337
  · exact context_13_91406_231361
  · exact context_13_91407_231370

theorem unmarked_context_11_5712_231372 : frontier 10 ⟨231372, by decide⟩
    (prefixCache 11 5712) (prefixPartial 11 5712) = false := by
  decide +kernel

theorem node_context_11_5712_231372 : EJMOriginalGlobalDAGData.nodes 10 ⟨231372, by decide⟩ =
    .split (coordinate 11) (![⟨231156, by decide⟩,⟨231236, by decide⟩,⟨231303, by decide⟩,⟨231371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5712_231372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5712 ⟨231372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5712
    ⟨231372, by decide⟩ (by decide) (![⟨231156, by decide⟩,⟨231236, by decide⟩,⟨231303, by decide⟩,⟨231371, by decide⟩]) unmarked_context_11_5712_231372 node_context_11_5712_231372
  intro a
  fin_cases a
  · exact context_12_22848_231156
  · exact context_12_22849_231236
  · exact context_12_22850_231303
  · exact context_12_22851_231371

theorem selected_cut_08179 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91408) = some ⟨13, 1, 0, 3444, 91408, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91408_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91408 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91408 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91408, 1, 16384⟩
    (by decide) selected_cut_08179

theorem selected_cut_08180 : selected 8 ⟨231396, by decide⟩
    (prefixPartial 13 91409) = some ⟨13, 2, 0, 231396, 91409, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_91409_231396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91409 ⟨231396, by decide⟩ :=
  accepted_of_selected 13 91409 ⟨231396, by decide⟩ ⟨13, 2, 0, 231396, 91409, 1993, 16384⟩
    (by decide) selected_cut_08180

theorem selected_cut_08181 : selected 8 ⟨231414, by decide⟩
    (prefixPartial 13 91410) = some ⟨13, 2, 0, 231414, 91410, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_91410_231414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91410 ⟨231414, by decide⟩ :=
  accepted_of_selected 13 91410 ⟨231414, by decide⟩ ⟨13, 2, 0, 231414, 91410, 1289, 16384⟩
    (by decide) selected_cut_08181

theorem selected_cut_08182 : selected 8 ⟨231419, by decide⟩
    (prefixPartial 13 91411) = some ⟨13, 2, 0, 231419, 91411, 909, 16384⟩ := by
  decide +kernel

theorem context_13_91411_231419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91411 ⟨231419, by decide⟩ :=
  accepted_of_selected 13 91411 ⟨231419, by decide⟩ ⟨13, 2, 0, 231419, 91411, 909, 16384⟩
    (by decide) selected_cut_08182

theorem unmarked_context_12_22852_231420 : frontier 9 ⟨231420, by decide⟩
    (prefixCache 12 22852) (prefixPartial 12 22852) = false := by
  decide +kernel

theorem node_context_12_22852_231420 : EJMOriginalGlobalDAGData.nodes 9 ⟨231420, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231396, by decide⟩,⟨231414, by decide⟩,⟨231419, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22852_231420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22852 ⟨231420, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22852
    ⟨231420, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231396, by decide⟩,⟨231414, by decide⟩,⟨231419, by decide⟩]) unmarked_context_12_22852_231420 node_context_12_22852_231420
  intro a
  fin_cases a
  · exact context_13_91408_3444
  · exact context_13_91409_231396
  · exact context_13_91410_231414
  · exact context_13_91411_231419

theorem selected_cut_08183 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 22853) = some ⟨12, 1, 0, 126884, 22853, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22853_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22853 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 22853 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 22853, 1, 65536⟩
    (by decide) selected_cut_08183

theorem selected_cut_08184 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91416) = some ⟨13, 1, 0, 3444, 91416, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91416_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91416 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91416 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91416, 1, 16384⟩
    (by decide) selected_cut_08184

theorem selected_cut_08185 : selected 8 ⟨231446, by decide⟩
    (prefixPartial 13 91417) = some ⟨13, 2, 0, 231446, 91417, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_91417_231446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91417 ⟨231446, by decide⟩ :=
  accepted_of_selected 13 91417 ⟨231446, by decide⟩ ⟨13, 2, 0, 231446, 91417, 2361, 16384⟩
    (by decide) selected_cut_08185

theorem selected_cut_08186 : selected 8 ⟨231467, by decide⟩
    (prefixPartial 13 91418) = some ⟨13, 2, 0, 231467, 91418, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_91418_231467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91418 ⟨231467, by decide⟩ :=
  accepted_of_selected 13 91418 ⟨231467, by decide⟩ ⟨13, 2, 0, 231467, 91418, 1605, 16384⟩
    (by decide) selected_cut_08186

theorem selected_cut_08187 : selected 8 ⟨231476, by decide⟩
    (prefixPartial 13 91419) = some ⟨13, 2, 0, 231476, 91419, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_91419_231476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91419 ⟨231476, by decide⟩ :=
  accepted_of_selected 13 91419 ⟨231476, by decide⟩ ⟨13, 2, 0, 231476, 91419, 1037, 16384⟩
    (by decide) selected_cut_08187

theorem unmarked_context_12_22854_231477 : frontier 9 ⟨231477, by decide⟩
    (prefixCache 12 22854) (prefixPartial 12 22854) = false := by
  decide +kernel

theorem node_context_12_22854_231477 : EJMOriginalGlobalDAGData.nodes 9 ⟨231477, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231446, by decide⟩,⟨231467, by decide⟩,⟨231476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22854_231477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22854 ⟨231477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22854
    ⟨231477, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231446, by decide⟩,⟨231467, by decide⟩,⟨231476, by decide⟩]) unmarked_context_12_22854_231477 node_context_12_22854_231477
  intro a
  fin_cases a
  · exact context_13_91416_3444
  · exact context_13_91417_231446
  · exact context_13_91418_231467
  · exact context_13_91419_231476

theorem selected_cut_08188 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91420) = some ⟨13, 1, 0, 3444, 91420, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91420_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91420 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91420 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91420, 1, 16384⟩
    (by decide) selected_cut_08188

theorem selected_cut_08189 : selected 8 ⟨231500, by decide⟩
    (prefixPartial 13 91421) = some ⟨13, 2, 0, 231500, 91421, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_91421_231500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91421 ⟨231500, by decide⟩ :=
  accepted_of_selected 13 91421 ⟨231500, by decide⟩ ⟨13, 2, 0, 231500, 91421, 2309, 16384⟩
    (by decide) selected_cut_08189

theorem selected_cut_08190 : selected 8 ⟨231521, by decide⟩
    (prefixPartial 13 91422) = some ⟨13, 2, 0, 231521, 91422, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_91422_231521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91422 ⟨231521, by decide⟩ :=
  accepted_of_selected 13 91422 ⟨231521, by decide⟩ ⟨13, 2, 0, 231521, 91422, 1701, 16384⟩
    (by decide) selected_cut_08190

theorem selected_cut_08191 : selected 8 ⟨231531, by decide⟩
    (prefixPartial 13 91423) = some ⟨13, 2, 0, 231531, 91423, 985, 16384⟩ := by
  decide +kernel

theorem context_13_91423_231531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91423 ⟨231531, by decide⟩ :=
  accepted_of_selected 13 91423 ⟨231531, by decide⟩ ⟨13, 2, 0, 231531, 91423, 985, 16384⟩
    (by decide) selected_cut_08191

theorem unmarked_context_12_22855_231532 : frontier 9 ⟨231532, by decide⟩
    (prefixCache 12 22855) (prefixPartial 12 22855) = false := by
  decide +kernel

theorem node_context_12_22855_231532 : EJMOriginalGlobalDAGData.nodes 9 ⟨231532, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231500, by decide⟩,⟨231521, by decide⟩,⟨231531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22855_231532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22855 ⟨231532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22855
    ⟨231532, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231500, by decide⟩,⟨231521, by decide⟩,⟨231531, by decide⟩]) unmarked_context_12_22855_231532 node_context_12_22855_231532
  intro a
  fin_cases a
  · exact context_13_91420_3444
  · exact context_13_91421_231500
  · exact context_13_91422_231521
  · exact context_13_91423_231531

theorem unmarked_context_11_5713_231533 : frontier 10 ⟨231533, by decide⟩
    (prefixCache 11 5713) (prefixPartial 11 5713) = false := by
  decide +kernel

theorem node_context_11_5713_231533 : EJMOriginalGlobalDAGData.nodes 10 ⟨231533, by decide⟩ =
    .split (coordinate 11) (![⟨231420, by decide⟩,⟨126884, by decide⟩,⟨231477, by decide⟩,⟨231532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5713_231533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5713 ⟨231533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5713
    ⟨231533, by decide⟩ (by decide) (![⟨231420, by decide⟩,⟨126884, by decide⟩,⟨231477, by decide⟩,⟨231532, by decide⟩]) unmarked_context_11_5713_231533 node_context_11_5713_231533
  intro a
  fin_cases a
  · exact context_12_22852_231420
  · exact context_12_22853_126884
  · exact context_12_22854_231477
  · exact context_12_22855_231532

theorem selected_cut_08192 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91424) = some ⟨13, 1, 0, 3444, 91424, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91424_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91424 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91424 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91424, 1, 16384⟩
    (by decide) selected_cut_08192

theorem selected_cut_08193 : selected 8 ⟨231556, by decide⟩
    (prefixPartial 13 91425) = some ⟨13, 2, 0, 231556, 91425, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_91425_231556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91425 ⟨231556, by decide⟩ :=
  accepted_of_selected 13 91425 ⟨231556, by decide⟩ ⟨13, 2, 0, 231556, 91425, 2009, 16384⟩
    (by decide) selected_cut_08193

theorem selected_cut_08194 : selected 8 ⟨231577, by decide⟩
    (prefixPartial 13 91426) = some ⟨13, 2, 0, 231577, 91426, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_91426_231577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91426 ⟨231577, by decide⟩ :=
  accepted_of_selected 13 91426 ⟨231577, by decide⟩ ⟨13, 2, 0, 231577, 91426, 1793, 16384⟩
    (by decide) selected_cut_08194

theorem selected_cut_08195 : selected 8 ⟨231583, by decide⟩
    (prefixPartial 13 91427) = some ⟨13, 2, 0, 231583, 91427, 941, 16384⟩ := by
  decide +kernel

theorem context_13_91427_231583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91427 ⟨231583, by decide⟩ :=
  accepted_of_selected 13 91427 ⟨231583, by decide⟩ ⟨13, 2, 0, 231583, 91427, 941, 16384⟩
    (by decide) selected_cut_08195

theorem unmarked_context_12_22856_231584 : frontier 9 ⟨231584, by decide⟩
    (prefixCache 12 22856) (prefixPartial 12 22856) = false := by
  decide +kernel

theorem node_context_12_22856_231584 : EJMOriginalGlobalDAGData.nodes 9 ⟨231584, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231556, by decide⟩,⟨231577, by decide⟩,⟨231583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22856_231584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22856 ⟨231584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22856
    ⟨231584, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231556, by decide⟩,⟨231577, by decide⟩,⟨231583, by decide⟩]) unmarked_context_12_22856_231584 node_context_12_22856_231584
  intro a
  fin_cases a
  · exact context_13_91424_3444
  · exact context_13_91425_231556
  · exact context_13_91426_231577
  · exact context_13_91427_231583

theorem selected_cut_08196 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91428) = some ⟨13, 1, 0, 3444, 91428, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91428_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91428 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91428 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91428, 1, 16384⟩
    (by decide) selected_cut_08196

theorem selected_cut_08197 : selected 8 ⟨231614, by decide⟩
    (prefixPartial 13 91429) = some ⟨13, 2, 0, 231614, 91429, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_91429_231614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91429 ⟨231614, by decide⟩ :=
  accepted_of_selected 13 91429 ⟨231614, by decide⟩ ⟨13, 2, 0, 231614, 91429, 2677, 16384⟩
    (by decide) selected_cut_08197

theorem selected_cut_08198 : selected 8 ⟨231629, by decide⟩
    (prefixPartial 13 91430) = some ⟨13, 2, 0, 231629, 91430, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_91430_231629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91430 ⟨231629, by decide⟩ :=
  accepted_of_selected 13 91430 ⟨231629, by decide⟩ ⟨13, 2, 0, 231629, 91430, 2253, 16384⟩
    (by decide) selected_cut_08198

theorem selected_cut_08199 : selected 8 ⟨231640, by decide⟩
    (prefixPartial 13 91431) = some ⟨13, 2, 0, 231640, 91431, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_91431_231640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91431 ⟨231640, by decide⟩ :=
  accepted_of_selected 13 91431 ⟨231640, by decide⟩ ⟨13, 2, 0, 231640, 91431, 1189, 16384⟩
    (by decide) selected_cut_08199

theorem unmarked_context_12_22857_231641 : frontier 9 ⟨231641, by decide⟩
    (prefixCache 12 22857) (prefixPartial 12 22857) = false := by
  decide +kernel

theorem node_context_12_22857_231641 : EJMOriginalGlobalDAGData.nodes 9 ⟨231641, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231614, by decide⟩,⟨231629, by decide⟩,⟨231640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22857_231641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22857 ⟨231641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22857
    ⟨231641, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231614, by decide⟩,⟨231629, by decide⟩,⟨231640, by decide⟩]) unmarked_context_12_22857_231641 node_context_12_22857_231641
  intro a
  fin_cases a
  · exact context_13_91428_3444
  · exact context_13_91429_231614
  · exact context_13_91430_231629
  · exact context_13_91431_231640

theorem selected_cut_08200 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91432) = some ⟨13, 1, 0, 3444, 91432, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91432_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91432 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91432 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91432, 1, 16384⟩
    (by decide) selected_cut_08200

theorem selected_cut_08201 : selected 8 ⟨231662, by decide⟩
    (prefixPartial 13 91433) = some ⟨13, 2, 0, 231662, 91433, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_91433_231662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91433 ⟨231662, by decide⟩ :=
  accepted_of_selected 13 91433 ⟨231662, by decide⟩ ⟨13, 2, 0, 231662, 91433, 2225, 16384⟩
    (by decide) selected_cut_08201

theorem selected_cut_08202 : selected 8 ⟨231685, by decide⟩
    (prefixPartial 13 91434) = some ⟨13, 2, 0, 231685, 91434, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_91434_231685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91434 ⟨231685, by decide⟩ :=
  accepted_of_selected 13 91434 ⟨231685, by decide⟩ ⟨13, 2, 0, 231685, 91434, 2169, 16384⟩
    (by decide) selected_cut_08202

theorem selected_cut_08203 : selected 8 ⟨231696, by decide⟩
    (prefixPartial 13 91435) = some ⟨13, 2, 0, 231696, 91435, 965, 16384⟩ := by
  decide +kernel

theorem context_13_91435_231696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91435 ⟨231696, by decide⟩ :=
  accepted_of_selected 13 91435 ⟨231696, by decide⟩ ⟨13, 2, 0, 231696, 91435, 965, 16384⟩
    (by decide) selected_cut_08203

theorem unmarked_context_12_22858_231697 : frontier 9 ⟨231697, by decide⟩
    (prefixCache 12 22858) (prefixPartial 12 22858) = false := by
  decide +kernel

theorem node_context_12_22858_231697 : EJMOriginalGlobalDAGData.nodes 9 ⟨231697, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231662, by decide⟩,⟨231685, by decide⟩,⟨231696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22858_231697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22858 ⟨231697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22858
    ⟨231697, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231662, by decide⟩,⟨231685, by decide⟩,⟨231696, by decide⟩]) unmarked_context_12_22858_231697 node_context_12_22858_231697
  intro a
  fin_cases a
  · exact context_13_91432_3444
  · exact context_13_91433_231662
  · exact context_13_91434_231685
  · exact context_13_91435_231696

theorem selected_cut_08204 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91436) = some ⟨13, 1, 0, 3444, 91436, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91436_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91436 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91436 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91436, 1, 16384⟩
    (by decide) selected_cut_08204

theorem selected_cut_08205 : selected 8 ⟨231720, by decide⟩
    (prefixPartial 13 91437) = some ⟨13, 2, 0, 231720, 91437, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_91437_231720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91437 ⟨231720, by decide⟩ :=
  accepted_of_selected 13 91437 ⟨231720, by decide⟩ ⟨13, 2, 0, 231720, 91437, 2273, 16384⟩
    (by decide) selected_cut_08205

theorem selected_cut_08206 : selected 8 ⟨231743, by decide⟩
    (prefixPartial 13 91438) = some ⟨13, 2, 0, 231743, 91438, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_91438_231743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91438 ⟨231743, by decide⟩ :=
  accepted_of_selected 13 91438 ⟨231743, by decide⟩ ⟨13, 2, 0, 231743, 91438, 2281, 16384⟩
    (by decide) selected_cut_08206

theorem selected_cut_08207 : selected 8 ⟨231756, by decide⟩
    (prefixPartial 13 91439) = some ⟨13, 2, 0, 231756, 91439, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_91439_231756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91439 ⟨231756, by decide⟩ :=
  accepted_of_selected 13 91439 ⟨231756, by decide⟩ ⟨13, 2, 0, 231756, 91439, 1013, 16384⟩
    (by decide) selected_cut_08207

theorem unmarked_context_12_22859_231757 : frontier 9 ⟨231757, by decide⟩
    (prefixCache 12 22859) (prefixPartial 12 22859) = false := by
  decide +kernel

theorem node_context_12_22859_231757 : EJMOriginalGlobalDAGData.nodes 9 ⟨231757, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231720, by decide⟩,⟨231743, by decide⟩,⟨231756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22859_231757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22859 ⟨231757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22859
    ⟨231757, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231720, by decide⟩,⟨231743, by decide⟩,⟨231756, by decide⟩]) unmarked_context_12_22859_231757 node_context_12_22859_231757
  intro a
  fin_cases a
  · exact context_13_91436_3444
  · exact context_13_91437_231720
  · exact context_13_91438_231743
  · exact context_13_91439_231756

theorem unmarked_context_11_5714_231758 : frontier 10 ⟨231758, by decide⟩
    (prefixCache 11 5714) (prefixPartial 11 5714) = false := by
  decide +kernel

theorem node_context_11_5714_231758 : EJMOriginalGlobalDAGData.nodes 10 ⟨231758, by decide⟩ =
    .split (coordinate 11) (![⟨231584, by decide⟩,⟨231641, by decide⟩,⟨231697, by decide⟩,⟨231757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5714_231758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5714 ⟨231758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5714
    ⟨231758, by decide⟩ (by decide) (![⟨231584, by decide⟩,⟨231641, by decide⟩,⟨231697, by decide⟩,⟨231757, by decide⟩]) unmarked_context_11_5714_231758 node_context_11_5714_231758
  intro a
  fin_cases a
  · exact context_12_22856_231584
  · exact context_12_22857_231641
  · exact context_12_22858_231697
  · exact context_12_22859_231757

theorem selected_cut_08208 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91440) = some ⟨13, 1, 0, 3444, 91440, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91440_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91440 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91440 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91440, 1, 16384⟩
    (by decide) selected_cut_08208

theorem selected_cut_08209 : selected 8 ⟨231781, by decide⟩
    (prefixPartial 13 91441) = some ⟨13, 2, 0, 231781, 91441, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_91441_231781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91441 ⟨231781, by decide⟩ :=
  accepted_of_selected 13 91441 ⟨231781, by decide⟩ ⟨13, 2, 0, 231781, 91441, 2033, 16384⟩
    (by decide) selected_cut_08209

theorem selected_cut_08210 : selected 8 ⟨231800, by decide⟩
    (prefixPartial 13 91442) = some ⟨13, 2, 0, 231800, 91442, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_91442_231800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91442 ⟨231800, by decide⟩ :=
  accepted_of_selected 13 91442 ⟨231800, by decide⟩ ⟨13, 2, 0, 231800, 91442, 1681, 16384⟩
    (by decide) selected_cut_08210

theorem selected_cut_08211 : selected 8 ⟨231808, by decide⟩
    (prefixPartial 13 91443) = some ⟨13, 2, 0, 231808, 91443, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_91443_231808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91443 ⟨231808, by decide⟩ :=
  accepted_of_selected 13 91443 ⟨231808, by decide⟩ ⟨13, 2, 0, 231808, 91443, 1169, 16384⟩
    (by decide) selected_cut_08211

theorem unmarked_context_12_22860_231809 : frontier 9 ⟨231809, by decide⟩
    (prefixCache 12 22860) (prefixPartial 12 22860) = false := by
  decide +kernel

theorem node_context_12_22860_231809 : EJMOriginalGlobalDAGData.nodes 9 ⟨231809, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231781, by decide⟩,⟨231800, by decide⟩,⟨231808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22860_231809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22860 ⟨231809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22860
    ⟨231809, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231781, by decide⟩,⟨231800, by decide⟩,⟨231808, by decide⟩]) unmarked_context_12_22860_231809 node_context_12_22860_231809
  intro a
  fin_cases a
  · exact context_13_91440_3444
  · exact context_13_91441_231781
  · exact context_13_91442_231800
  · exact context_13_91443_231808

theorem selected_cut_08212 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91444) = some ⟨13, 1, 0, 3444, 91444, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91444_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91444 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91444 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91444, 1, 16384⟩
    (by decide) selected_cut_08212

theorem selected_cut_08213 : selected 8 ⟨231846, by decide⟩
    (prefixPartial 13 91445) = some ⟨13, 2, 0, 231846, 91445, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_91445_231846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91445 ⟨231846, by decide⟩ :=
  accepted_of_selected 13 91445 ⟨231846, by decide⟩ ⟨13, 2, 0, 231846, 91445, 2693, 16384⟩
    (by decide) selected_cut_08213

theorem selected_cut_08214 : selected 8 ⟨231863, by decide⟩
    (prefixPartial 13 91446) = some ⟨13, 2, 0, 231863, 91446, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_91446_231863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91446 ⟨231863, by decide⟩ :=
  accepted_of_selected 13 91446 ⟨231863, by decide⟩ ⟨13, 2, 0, 231863, 91446, 2205, 16384⟩
    (by decide) selected_cut_08214

theorem selected_cut_08215 : selected 8 ⟨231875, by decide⟩
    (prefixPartial 13 91447) = some ⟨13, 2, 0, 231875, 91447, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_91447_231875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91447 ⟨231875, by decide⟩ :=
  accepted_of_selected 13 91447 ⟨231875, by decide⟩ ⟨13, 2, 0, 231875, 91447, 1357, 16384⟩
    (by decide) selected_cut_08215

theorem unmarked_context_12_22861_231876 : frontier 9 ⟨231876, by decide⟩
    (prefixCache 12 22861) (prefixPartial 12 22861) = false := by
  decide +kernel

theorem node_context_12_22861_231876 : EJMOriginalGlobalDAGData.nodes 9 ⟨231876, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231846, by decide⟩,⟨231863, by decide⟩,⟨231875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22861_231876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22861 ⟨231876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22861
    ⟨231876, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231846, by decide⟩,⟨231863, by decide⟩,⟨231875, by decide⟩]) unmarked_context_12_22861_231876 node_context_12_22861_231876
  intro a
  fin_cases a
  · exact context_13_91444_3444
  · exact context_13_91445_231846
  · exact context_13_91446_231863
  · exact context_13_91447_231875

theorem selected_cut_08216 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91448) = some ⟨13, 1, 0, 3444, 91448, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91448_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91448 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91448 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91448, 1, 16384⟩
    (by decide) selected_cut_08216

theorem selected_cut_08217 : selected 8 ⟨231902, by decide⟩
    (prefixPartial 13 91449) = some ⟨13, 2, 0, 231902, 91449, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_91449_231902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91449 ⟨231902, by decide⟩ :=
  accepted_of_selected 13 91449 ⟨231902, by decide⟩ ⟨13, 2, 0, 231902, 91449, 2277, 16384⟩
    (by decide) selected_cut_08217

theorem selected_cut_08218 : selected 8 ⟨231921, by decide⟩
    (prefixPartial 13 91450) = some ⟨13, 2, 0, 231921, 91450, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_91450_231921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91450 ⟨231921, by decide⟩ :=
  accepted_of_selected 13 91450 ⟨231921, by decide⟩ ⟨13, 2, 0, 231921, 91450, 2113, 16384⟩
    (by decide) selected_cut_08218

theorem selected_cut_08219 : selected 8 ⟨231929, by decide⟩
    (prefixPartial 13 91451) = some ⟨13, 2, 0, 231929, 91451, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_91451_231929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91451 ⟨231929, by decide⟩ :=
  accepted_of_selected 13 91451 ⟨231929, by decide⟩ ⟨13, 2, 0, 231929, 91451, 1177, 16384⟩
    (by decide) selected_cut_08219

theorem unmarked_context_12_22862_231930 : frontier 9 ⟨231930, by decide⟩
    (prefixCache 12 22862) (prefixPartial 12 22862) = false := by
  decide +kernel

theorem node_context_12_22862_231930 : EJMOriginalGlobalDAGData.nodes 9 ⟨231930, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231902, by decide⟩,⟨231921, by decide⟩,⟨231929, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22862_231930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22862 ⟨231930, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22862
    ⟨231930, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231902, by decide⟩,⟨231921, by decide⟩,⟨231929, by decide⟩]) unmarked_context_12_22862_231930 node_context_12_22862_231930
  intro a
  fin_cases a
  · exact context_13_91448_3444
  · exact context_13_91449_231902
  · exact context_13_91450_231921
  · exact context_13_91451_231929

theorem selected_cut_08220 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91452) = some ⟨13, 1, 0, 3444, 91452, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91452_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91452 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91452 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91452, 1, 16384⟩
    (by decide) selected_cut_08220

theorem selected_cut_08221 : selected 8 ⟨231952, by decide⟩
    (prefixPartial 13 91453) = some ⟨13, 2, 0, 231952, 91453, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_91453_231952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91453 ⟨231952, by decide⟩ :=
  accepted_of_selected 13 91453 ⟨231952, by decide⟩ ⟨13, 2, 0, 231952, 91453, 2233, 16384⟩
    (by decide) selected_cut_08221

theorem selected_cut_08222 : selected 8 ⟨231972, by decide⟩
    (prefixPartial 13 91454) = some ⟨13, 2, 0, 231972, 91454, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_91454_231972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91454 ⟨231972, by decide⟩ :=
  accepted_of_selected 13 91454 ⟨231972, by decide⟩ ⟨13, 2, 0, 231972, 91454, 2165, 16384⟩
    (by decide) selected_cut_08222

theorem selected_cut_08223 : selected 8 ⟨231982, by decide⟩
    (prefixPartial 13 91455) = some ⟨13, 2, 0, 231982, 91455, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_91455_231982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91455 ⟨231982, by decide⟩ :=
  accepted_of_selected 13 91455 ⟨231982, by decide⟩ ⟨13, 2, 0, 231982, 91455, 1165, 16384⟩
    (by decide) selected_cut_08223

theorem unmarked_context_12_22863_231983 : frontier 9 ⟨231983, by decide⟩
    (prefixCache 12 22863) (prefixPartial 12 22863) = false := by
  decide +kernel

theorem node_context_12_22863_231983 : EJMOriginalGlobalDAGData.nodes 9 ⟨231983, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨231952, by decide⟩,⟨231972, by decide⟩,⟨231982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22863_231983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22863 ⟨231983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22863
    ⟨231983, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨231952, by decide⟩,⟨231972, by decide⟩,⟨231982, by decide⟩]) unmarked_context_12_22863_231983 node_context_12_22863_231983
  intro a
  fin_cases a
  · exact context_13_91452_3444
  · exact context_13_91453_231952
  · exact context_13_91454_231972
  · exact context_13_91455_231982

theorem unmarked_context_11_5715_231984 : frontier 10 ⟨231984, by decide⟩
    (prefixCache 11 5715) (prefixPartial 11 5715) = false := by
  decide +kernel

theorem node_context_11_5715_231984 : EJMOriginalGlobalDAGData.nodes 10 ⟨231984, by decide⟩ =
    .split (coordinate 11) (![⟨231809, by decide⟩,⟨231876, by decide⟩,⟨231930, by decide⟩,⟨231983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5715_231984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5715 ⟨231984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5715
    ⟨231984, by decide⟩ (by decide) (![⟨231809, by decide⟩,⟨231876, by decide⟩,⟨231930, by decide⟩,⟨231983, by decide⟩]) unmarked_context_11_5715_231984 node_context_11_5715_231984
  intro a
  fin_cases a
  · exact context_12_22860_231809
  · exact context_12_22861_231876
  · exact context_12_22862_231930
  · exact context_12_22863_231983

theorem unmarked_context_10_1428_231985 : frontier 11 ⟨231985, by decide⟩
    (prefixCache 10 1428) (prefixPartial 10 1428) = false := by
  decide +kernel

theorem node_context_10_1428_231985 : EJMOriginalGlobalDAGData.nodes 11 ⟨231985, by decide⟩ =
    .split (coordinate 10) (![⟨231372, by decide⟩,⟨231533, by decide⟩,⟨231758, by decide⟩,⟨231984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1428_231985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1428 ⟨231985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1428
    ⟨231985, by decide⟩ (by decide) (![⟨231372, by decide⟩,⟨231533, by decide⟩,⟨231758, by decide⟩,⟨231984, by decide⟩]) unmarked_context_10_1428_231985 node_context_10_1428_231985
  intro a
  fin_cases a
  · exact context_11_5712_231372
  · exact context_11_5713_231533
  · exact context_11_5714_231758
  · exact context_11_5715_231984

theorem selected_cut_08224 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91456) = some ⟨13, 1, 0, 3444, 91456, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91456_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91456 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91456 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91456, 1, 16384⟩
    (by decide) selected_cut_08224

theorem selected_cut_08225 : selected 8 ⟨232007, by decide⟩
    (prefixPartial 13 91457) = some ⟨13, 2, 0, 232007, 91457, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_91457_232007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91457 ⟨232007, by decide⟩ :=
  accepted_of_selected 13 91457 ⟨232007, by decide⟩ ⟨13, 2, 0, 232007, 91457, 1797, 16384⟩
    (by decide) selected_cut_08225

theorem selected_cut_08226 : selected 8 ⟨232026, by decide⟩
    (prefixPartial 13 91458) = some ⟨13, 2, 0, 232026, 91458, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_91458_232026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91458 ⟨232026, by decide⟩ :=
  accepted_of_selected 13 91458 ⟨232026, by decide⟩ ⟨13, 2, 0, 232026, 91458, 1549, 16384⟩
    (by decide) selected_cut_08226

theorem selected_cut_08227 : selected 8 ⟨232033, by decide⟩
    (prefixPartial 13 91459) = some ⟨13, 2, 0, 232033, 91459, 913, 16384⟩ := by
  decide +kernel

theorem context_13_91459_232033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91459 ⟨232033, by decide⟩ :=
  accepted_of_selected 13 91459 ⟨232033, by decide⟩ ⟨13, 2, 0, 232033, 91459, 913, 16384⟩
    (by decide) selected_cut_08227

theorem unmarked_context_12_22864_232034 : frontier 9 ⟨232034, by decide⟩
    (prefixCache 12 22864) (prefixPartial 12 22864) = false := by
  decide +kernel

theorem node_context_12_22864_232034 : EJMOriginalGlobalDAGData.nodes 9 ⟨232034, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232007, by decide⟩,⟨232026, by decide⟩,⟨232033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22864_232034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22864 ⟨232034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22864
    ⟨232034, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232007, by decide⟩,⟨232026, by decide⟩,⟨232033, by decide⟩]) unmarked_context_12_22864_232034 node_context_12_22864_232034
  intro a
  fin_cases a
  · exact context_13_91456_3444
  · exact context_13_91457_232007
  · exact context_13_91458_232026
  · exact context_13_91459_232033

theorem selected_cut_08228 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 22865) = some ⟨12, 1, 0, 126371, 22865, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22865_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22865 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 22865 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 22865, 1, 65536⟩
    (by decide) selected_cut_08228

theorem selected_cut_08229 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91464) = some ⟨13, 1, 0, 3444, 91464, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91464_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91464 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91464 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91464, 1, 16384⟩
    (by decide) selected_cut_08229

theorem selected_cut_08230 : selected 8 ⟨232070, by decide⟩
    (prefixPartial 13 91465) = some ⟨13, 2, 0, 232070, 91465, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_91465_232070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91465 ⟨232070, by decide⟩ :=
  accepted_of_selected 13 91465 ⟨232070, by decide⟩ ⟨13, 2, 0, 232070, 91465, 2421, 16384⟩
    (by decide) selected_cut_08230

theorem selected_cut_08231 : selected 8 ⟨232088, by decide⟩
    (prefixPartial 13 91466) = some ⟨13, 2, 0, 232088, 91466, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_91466_232088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91466 ⟨232088, by decide⟩ :=
  accepted_of_selected 13 91466 ⟨232088, by decide⟩ ⟨13, 2, 0, 232088, 91466, 2169, 16384⟩
    (by decide) selected_cut_08231

theorem selected_cut_08232 : selected 8 ⟨232097, by decide⟩
    (prefixPartial 13 91467) = some ⟨13, 2, 0, 232097, 91467, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_91467_232097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91467 ⟨232097, by decide⟩ :=
  accepted_of_selected 13 91467 ⟨232097, by decide⟩ ⟨13, 2, 0, 232097, 91467, 1121, 16384⟩
    (by decide) selected_cut_08232

theorem unmarked_context_12_22866_232098 : frontier 9 ⟨232098, by decide⟩
    (prefixCache 12 22866) (prefixPartial 12 22866) = false := by
  decide +kernel

theorem node_context_12_22866_232098 : EJMOriginalGlobalDAGData.nodes 9 ⟨232098, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232070, by decide⟩,⟨232088, by decide⟩,⟨232097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22866_232098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22866 ⟨232098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22866
    ⟨232098, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232070, by decide⟩,⟨232088, by decide⟩,⟨232097, by decide⟩]) unmarked_context_12_22866_232098 node_context_12_22866_232098
  intro a
  fin_cases a
  · exact context_13_91464_3444
  · exact context_13_91465_232070
  · exact context_13_91466_232088
  · exact context_13_91467_232097

theorem selected_cut_08233 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91468) = some ⟨13, 1, 0, 3444, 91468, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91468_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91468 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91468 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91468, 1, 16384⟩
    (by decide) selected_cut_08233

theorem selected_cut_08234 : selected 8 ⟨232128, by decide⟩
    (prefixPartial 13 91469) = some ⟨13, 2, 0, 232128, 91469, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_91469_232128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91469 ⟨232128, by decide⟩ :=
  accepted_of_selected 13 91469 ⟨232128, by decide⟩ ⟨13, 2, 0, 232128, 91469, 2341, 16384⟩
    (by decide) selected_cut_08234

theorem selected_cut_08235 : selected 8 ⟨232146, by decide⟩
    (prefixPartial 13 91470) = some ⟨13, 2, 0, 232146, 91470, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_91470_232146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91470 ⟨232146, by decide⟩ :=
  accepted_of_selected 13 91470 ⟨232146, by decide⟩ ⟨13, 2, 0, 232146, 91470, 2169, 16384⟩
    (by decide) selected_cut_08235

theorem selected_cut_08236 : selected 8 ⟨232155, by decide⟩
    (prefixPartial 13 91471) = some ⟨13, 2, 0, 232155, 91471, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_91471_232155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91471 ⟨232155, by decide⟩ :=
  accepted_of_selected 13 91471 ⟨232155, by decide⟩ ⟨13, 2, 0, 232155, 91471, 1057, 16384⟩
    (by decide) selected_cut_08236

theorem unmarked_context_12_22867_232156 : frontier 9 ⟨232156, by decide⟩
    (prefixCache 12 22867) (prefixPartial 12 22867) = false := by
  decide +kernel

theorem node_context_12_22867_232156 : EJMOriginalGlobalDAGData.nodes 9 ⟨232156, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232128, by decide⟩,⟨232146, by decide⟩,⟨232155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22867_232156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22867 ⟨232156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22867
    ⟨232156, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232128, by decide⟩,⟨232146, by decide⟩,⟨232155, by decide⟩]) unmarked_context_12_22867_232156 node_context_12_22867_232156
  intro a
  fin_cases a
  · exact context_13_91468_3444
  · exact context_13_91469_232128
  · exact context_13_91470_232146
  · exact context_13_91471_232155

theorem unmarked_context_11_5716_232157 : frontier 10 ⟨232157, by decide⟩
    (prefixCache 11 5716) (prefixPartial 11 5716) = false := by
  decide +kernel

theorem node_context_11_5716_232157 : EJMOriginalGlobalDAGData.nodes 10 ⟨232157, by decide⟩ =
    .split (coordinate 11) (![⟨232034, by decide⟩,⟨126371, by decide⟩,⟨232098, by decide⟩,⟨232156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5716_232157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5716 ⟨232157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5716
    ⟨232157, by decide⟩ (by decide) (![⟨232034, by decide⟩,⟨126371, by decide⟩,⟨232098, by decide⟩,⟨232156, by decide⟩]) unmarked_context_11_5716_232157 node_context_11_5716_232157
  intro a
  fin_cases a
  · exact context_12_22864_232034
  · exact context_12_22865_126371
  · exact context_12_22866_232098
  · exact context_12_22867_232156

theorem selected_cut_08237 : selected 9 ⟨232200, by decide⟩
    (prefixPartial 12 22868) = some ⟨12, 2, 0, 232200, 22868, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_22868_232200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22868 ⟨232200, by decide⟩ :=
  accepted_of_selected 12 22868 ⟨232200, by decide⟩ ⟨12, 2, 0, 232200, 22868, 3441, 65536⟩
    (by decide) selected_cut_08237

theorem selected_cut_08238 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 22869) = some ⟨12, 1, 0, 170504, 22869, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22869_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22869 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 22869 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 22869, 1, 65536⟩
    (by decide) selected_cut_08238

theorem selected_cut_08239 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91480) = some ⟨13, 1, 0, 3444, 91480, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91480_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91480 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91480 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91480, 1, 16384⟩
    (by decide) selected_cut_08239

theorem selected_cut_08240 : selected 8 ⟨232216, by decide⟩
    (prefixPartial 13 91481) = some ⟨13, 2, 0, 232216, 91481, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_91481_232216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91481 ⟨232216, by decide⟩ :=
  accepted_of_selected 13 91481 ⟨232216, by decide⟩ ⟨13, 2, 0, 232216, 91481, 1665, 16384⟩
    (by decide) selected_cut_08240

theorem selected_cut_08241 : selected 8 ⟨232235, by decide⟩
    (prefixPartial 13 91482) = some ⟨13, 2, 0, 232235, 91482, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_91482_232235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91482 ⟨232235, by decide⟩ :=
  accepted_of_selected 13 91482 ⟨232235, by decide⟩ ⟨13, 2, 0, 232235, 91482, 1585, 16384⟩
    (by decide) selected_cut_08241

theorem selected_cut_08242 : selected 8 ⟨232243, by decide⟩
    (prefixPartial 13 91483) = some ⟨13, 2, 0, 232243, 91483, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_91483_232243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91483 ⟨232243, by decide⟩ :=
  accepted_of_selected 13 91483 ⟨232243, by decide⟩ ⟨13, 2, 0, 232243, 91483, 1069, 16384⟩
    (by decide) selected_cut_08242

theorem unmarked_context_12_22870_232244 : frontier 9 ⟨232244, by decide⟩
    (prefixCache 12 22870) (prefixPartial 12 22870) = false := by
  decide +kernel

theorem node_context_12_22870_232244 : EJMOriginalGlobalDAGData.nodes 9 ⟨232244, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232216, by decide⟩,⟨232235, by decide⟩,⟨232243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22870_232244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22870 ⟨232244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22870
    ⟨232244, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232216, by decide⟩,⟨232235, by decide⟩,⟨232243, by decide⟩]) unmarked_context_12_22870_232244 node_context_12_22870_232244
  intro a
  fin_cases a
  · exact context_13_91480_3444
  · exact context_13_91481_232216
  · exact context_13_91482_232235
  · exact context_13_91483_232243

theorem selected_cut_08243 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91484) = some ⟨13, 1, 0, 3444, 91484, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91484_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91484 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91484 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91484, 1, 16384⟩
    (by decide) selected_cut_08243

theorem selected_cut_08244 : selected 8 ⟨232263, by decide⟩
    (prefixPartial 13 91485) = some ⟨13, 2, 0, 232263, 91485, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_91485_232263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91485 ⟨232263, by decide⟩ :=
  accepted_of_selected 13 91485 ⟨232263, by decide⟩ ⟨13, 2, 0, 232263, 91485, 1753, 16384⟩
    (by decide) selected_cut_08244

theorem selected_cut_08245 : selected 8 ⟨232285, by decide⟩
    (prefixPartial 13 91486) = some ⟨13, 2, 0, 232285, 91486, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_91486_232285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91486 ⟨232285, by decide⟩ :=
  accepted_of_selected 13 91486 ⟨232285, by decide⟩ ⟨13, 2, 0, 232285, 91486, 1653, 16384⟩
    (by decide) selected_cut_08245

theorem selected_cut_08246 : selected 8 ⟨232296, by decide⟩
    (prefixPartial 13 91487) = some ⟨13, 2, 0, 232296, 91487, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_91487_232296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91487 ⟨232296, by decide⟩ :=
  accepted_of_selected 13 91487 ⟨232296, by decide⟩ ⟨13, 2, 0, 232296, 91487, 1009, 16384⟩
    (by decide) selected_cut_08246

theorem unmarked_context_12_22871_232297 : frontier 9 ⟨232297, by decide⟩
    (prefixCache 12 22871) (prefixPartial 12 22871) = false := by
  decide +kernel

theorem node_context_12_22871_232297 : EJMOriginalGlobalDAGData.nodes 9 ⟨232297, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232263, by decide⟩,⟨232285, by decide⟩,⟨232296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22871_232297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22871 ⟨232297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22871
    ⟨232297, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232263, by decide⟩,⟨232285, by decide⟩,⟨232296, by decide⟩]) unmarked_context_12_22871_232297 node_context_12_22871_232297
  intro a
  fin_cases a
  · exact context_13_91484_3444
  · exact context_13_91485_232263
  · exact context_13_91486_232285
  · exact context_13_91487_232296

theorem unmarked_context_11_5717_232298 : frontier 10 ⟨232298, by decide⟩
    (prefixCache 11 5717) (prefixPartial 11 5717) = false := by
  decide +kernel

theorem node_context_11_5717_232298 : EJMOriginalGlobalDAGData.nodes 10 ⟨232298, by decide⟩ =
    .split (coordinate 11) (![⟨232200, by decide⟩,⟨170504, by decide⟩,⟨232244, by decide⟩,⟨232297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5717_232298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5717 ⟨232298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5717
    ⟨232298, by decide⟩ (by decide) (![⟨232200, by decide⟩,⟨170504, by decide⟩,⟨232244, by decide⟩,⟨232297, by decide⟩]) unmarked_context_11_5717_232298 node_context_11_5717_232298
  intro a
  fin_cases a
  · exact context_12_22868_232200
  · exact context_12_22869_170504
  · exact context_12_22870_232244
  · exact context_12_22871_232297

theorem selected_cut_08247 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91488) = some ⟨13, 1, 0, 3444, 91488, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91488_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91488 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91488 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91488, 1, 16384⟩
    (by decide) selected_cut_08247

theorem selected_cut_08248 : selected 8 ⟨232316, by decide⟩
    (prefixPartial 13 91489) = some ⟨13, 2, 0, 232316, 91489, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_91489_232316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91489 ⟨232316, by decide⟩ :=
  accepted_of_selected 13 91489 ⟨232316, by decide⟩ ⟨13, 2, 0, 232316, 91489, 1445, 16384⟩
    (by decide) selected_cut_08248

theorem selected_cut_08249 : selected 8 ⟨232338, by decide⟩
    (prefixPartial 13 91490) = some ⟨13, 2, 0, 232338, 91490, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_91490_232338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91490 ⟨232338, by decide⟩ :=
  accepted_of_selected 13 91490 ⟨232338, by decide⟩ ⟨13, 2, 0, 232338, 91490, 1865, 16384⟩
    (by decide) selected_cut_08249

theorem selected_cut_08250 : selected 8 ⟨232346, by decide⟩
    (prefixPartial 13 91491) = some ⟨13, 2, 0, 232346, 91491, 893, 16384⟩ := by
  decide +kernel

theorem context_13_91491_232346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91491 ⟨232346, by decide⟩ :=
  accepted_of_selected 13 91491 ⟨232346, by decide⟩ ⟨13, 2, 0, 232346, 91491, 893, 16384⟩
    (by decide) selected_cut_08250

theorem unmarked_context_12_22872_232347 : frontier 9 ⟨232347, by decide⟩
    (prefixCache 12 22872) (prefixPartial 12 22872) = false := by
  decide +kernel

theorem node_context_12_22872_232347 : EJMOriginalGlobalDAGData.nodes 9 ⟨232347, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232316, by decide⟩,⟨232338, by decide⟩,⟨232346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22872_232347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22872 ⟨232347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22872
    ⟨232347, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232316, by decide⟩,⟨232338, by decide⟩,⟨232346, by decide⟩]) unmarked_context_12_22872_232347 node_context_12_22872_232347
  intro a
  fin_cases a
  · exact context_13_91488_3444
  · exact context_13_91489_232316
  · exact context_13_91490_232338
  · exact context_13_91491_232346

theorem selected_cut_08251 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91492) = some ⟨13, 1, 0, 3444, 91492, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91492_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91492 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91492 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91492, 1, 16384⟩
    (by decide) selected_cut_08251

theorem selected_cut_08252 : selected 8 ⟨232366, by decide⟩
    (prefixPartial 13 91493) = some ⟨13, 2, 0, 232366, 91493, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_91493_232366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91493 ⟨232366, by decide⟩ :=
  accepted_of_selected 13 91493 ⟨232366, by decide⟩ ⟨13, 2, 0, 232366, 91493, 1805, 16384⟩
    (by decide) selected_cut_08252

theorem selected_cut_08253 : selected 8 ⟨232398, by decide⟩
    (prefixPartial 13 91494) = some ⟨13, 2, 0, 232398, 91494, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_91494_232398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91494 ⟨232398, by decide⟩ :=
  accepted_of_selected 13 91494 ⟨232398, by decide⟩ ⟨13, 2, 0, 232398, 91494, 2365, 16384⟩
    (by decide) selected_cut_08253

theorem selected_cut_08254 : selected 8 ⟨232409, by decide⟩
    (prefixPartial 13 91495) = some ⟨13, 2, 0, 232409, 91495, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_91495_232409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91495 ⟨232409, by decide⟩ :=
  accepted_of_selected 13 91495 ⟨232409, by decide⟩ ⟨13, 2, 0, 232409, 91495, 1077, 16384⟩
    (by decide) selected_cut_08254

theorem unmarked_context_12_22873_232410 : frontier 9 ⟨232410, by decide⟩
    (prefixCache 12 22873) (prefixPartial 12 22873) = false := by
  decide +kernel

theorem node_context_12_22873_232410 : EJMOriginalGlobalDAGData.nodes 9 ⟨232410, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232366, by decide⟩,⟨232398, by decide⟩,⟨232409, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22873_232410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22873 ⟨232410, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22873
    ⟨232410, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232366, by decide⟩,⟨232398, by decide⟩,⟨232409, by decide⟩]) unmarked_context_12_22873_232410 node_context_12_22873_232410
  intro a
  fin_cases a
  · exact context_13_91492_3444
  · exact context_13_91493_232366
  · exact context_13_91494_232398
  · exact context_13_91495_232409

theorem selected_cut_08255 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91496) = some ⟨13, 1, 0, 3444, 91496, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91496_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91496 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91496 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91496, 1, 16384⟩
    (by decide) selected_cut_08255

theorem selected_cut_08256 : selected 8 ⟨232425, by decide⟩
    (prefixPartial 13 91497) = some ⟨13, 2, 0, 232425, 91497, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_91497_232425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91497 ⟨232425, by decide⟩ :=
  accepted_of_selected 13 91497 ⟨232425, by decide⟩ ⟨13, 2, 0, 232425, 91497, 1773, 16384⟩
    (by decide) selected_cut_08256

theorem selected_cut_08257 : selected 8 ⟨232455, by decide⟩
    (prefixPartial 13 91498) = some ⟨13, 2, 0, 232455, 91498, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_91498_232455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91498 ⟨232455, by decide⟩ :=
  accepted_of_selected 13 91498 ⟨232455, by decide⟩ ⟨13, 2, 0, 232455, 91498, 2485, 16384⟩
    (by decide) selected_cut_08257

theorem selected_cut_08258 : selected 8 ⟨232464, by decide⟩
    (prefixPartial 13 91499) = some ⟨13, 2, 0, 232464, 91499, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_91499_232464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91499 ⟨232464, by decide⟩ :=
  accepted_of_selected 13 91499 ⟨232464, by decide⟩ ⟨13, 2, 0, 232464, 91499, 1001, 16384⟩
    (by decide) selected_cut_08258

theorem unmarked_context_12_22874_232465 : frontier 9 ⟨232465, by decide⟩
    (prefixCache 12 22874) (prefixPartial 12 22874) = false := by
  decide +kernel

theorem node_context_12_22874_232465 : EJMOriginalGlobalDAGData.nodes 9 ⟨232465, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232425, by decide⟩,⟨232455, by decide⟩,⟨232464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22874_232465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22874 ⟨232465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22874
    ⟨232465, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232425, by decide⟩,⟨232455, by decide⟩,⟨232464, by decide⟩]) unmarked_context_12_22874_232465 node_context_12_22874_232465
  intro a
  fin_cases a
  · exact context_13_91496_3444
  · exact context_13_91497_232425
  · exact context_13_91498_232455
  · exact context_13_91499_232464

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
