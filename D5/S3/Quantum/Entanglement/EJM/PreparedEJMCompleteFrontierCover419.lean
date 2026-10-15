/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover418
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_40228 : selected 9 ⟨1092950, by decide⟩
    (prefixPartial 12 308845) = some ⟨12, 2, 0, 1092950, 308845, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_308845_1092950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308845 ⟨1092950, by decide⟩ :=
  accepted_of_selected 12 308845 ⟨1092950, by decide⟩ ⟨12, 2, 0, 1092950, 308845, 1545, 65536⟩
    (by decide) selected_cut_40228

theorem selected_cut_40229 : selected 9 ⟨1092980, by decide⟩
    (prefixPartial 12 308846) = some ⟨12, 2, 0, 1092980, 308846, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_308846_1092980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308846 ⟨1092980, by decide⟩ :=
  accepted_of_selected 12 308846 ⟨1092980, by decide⟩ ⟨12, 2, 0, 1092980, 308846, 1533, 65536⟩
    (by decide) selected_cut_40229

theorem selected_cut_40230 : selected 9 ⟨1093011, by decide⟩
    (prefixPartial 12 308847) = some ⟨12, 2, 0, 1093011, 308847, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_308847_1093011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308847 ⟨1093011, by decide⟩ :=
  accepted_of_selected 12 308847 ⟨1093011, by decide⟩ ⟨12, 2, 0, 1093011, 308847, 1517, 65536⟩
    (by decide) selected_cut_40230

theorem unmarked_context_11_77211_1093012 : frontier 10 ⟨1093012, by decide⟩
    (prefixCache 11 77211) (prefixPartial 11 77211) = false := by
  decide +kernel

theorem node_context_11_77211_1093012 : EJMOriginalGlobalDAGData.nodes 10 ⟨1093012, by decide⟩ =
    .split (coordinate 11) (![⟨1092920, by decide⟩,⟨1092950, by decide⟩,⟨1092980, by decide⟩,⟨1093011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77211_1093012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77211 ⟨1093012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77211
    ⟨1093012, by decide⟩ (by decide) (![⟨1092920, by decide⟩,⟨1092950, by decide⟩,⟨1092980, by decide⟩,⟨1093011, by decide⟩]) unmarked_context_11_77211_1093012 node_context_11_77211_1093012
  intro a
  fin_cases a
  · exact context_12_308844_1092920
  · exact context_12_308845_1092950
  · exact context_12_308846_1092980
  · exact context_12_308847_1093011

theorem unmarked_context_10_19302_1093013 : frontier 11 ⟨1093013, by decide⟩
    (prefixCache 10 19302) (prefixPartial 10 19302) = false := by
  decide +kernel

theorem node_context_10_19302_1093013 : EJMOriginalGlobalDAGData.nodes 11 ⟨1093013, by decide⟩ =
    .split (coordinate 10) (![⟨1092668, by decide⟩,⟨1092765, by decide⟩,⟨1092891, by decide⟩,⟨1093012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19302_1093013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19302 ⟨1093013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19302
    ⟨1093013, by decide⟩ (by decide) (![⟨1092668, by decide⟩,⟨1092765, by decide⟩,⟨1092891, by decide⟩,⟨1093012, by decide⟩]) unmarked_context_10_19302_1093013 node_context_10_19302_1093013
  intro a
  fin_cases a
  · exact context_11_77208_1092668
  · exact context_11_77209_1092765
  · exact context_11_77210_1092891
  · exact context_11_77211_1093012

theorem selected_cut_40231 : selected 9 ⟨1093052, by decide⟩
    (prefixPartial 12 308848) = some ⟨12, 2, 0, 1093052, 308848, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_308848_1093052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308848 ⟨1093052, by decide⟩ :=
  accepted_of_selected 12 308848 ⟨1093052, by decide⟩ ⟨12, 2, 0, 1093052, 308848, 1501, 65536⟩
    (by decide) selected_cut_40231

theorem selected_cut_40232 : selected 9 ⟨1093084, by decide⟩
    (prefixPartial 12 308849) = some ⟨12, 2, 0, 1093084, 308849, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_308849_1093084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308849 ⟨1093084, by decide⟩ :=
  accepted_of_selected 12 308849 ⟨1093084, by decide⟩ ⟨12, 2, 0, 1093084, 308849, 1333, 65536⟩
    (by decide) selected_cut_40232

theorem selected_cut_40233 : selected 9 ⟨1093126, by decide⟩
    (prefixPartial 12 308850) = some ⟨12, 2, 0, 1093126, 308850, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_308850_1093126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308850 ⟨1093126, by decide⟩ :=
  accepted_of_selected 12 308850 ⟨1093126, by decide⟩ ⟨12, 2, 0, 1093126, 308850, 1377, 65536⟩
    (by decide) selected_cut_40233

theorem selected_cut_40234 : selected 9 ⟨1093158, by decide⟩
    (prefixPartial 12 308851) = some ⟨12, 2, 0, 1093158, 308851, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_308851_1093158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308851 ⟨1093158, by decide⟩ :=
  accepted_of_selected 12 308851 ⟨1093158, by decide⟩ ⟨12, 2, 0, 1093158, 308851, 1233, 65536⟩
    (by decide) selected_cut_40234

theorem unmarked_context_11_77212_1093159 : frontier 10 ⟨1093159, by decide⟩
    (prefixCache 11 77212) (prefixPartial 11 77212) = false := by
  decide +kernel

theorem node_context_11_77212_1093159 : EJMOriginalGlobalDAGData.nodes 10 ⟨1093159, by decide⟩ =
    .split (coordinate 11) (![⟨1093052, by decide⟩,⟨1093084, by decide⟩,⟨1093126, by decide⟩,⟨1093158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77212_1093159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77212 ⟨1093159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77212
    ⟨1093159, by decide⟩ (by decide) (![⟨1093052, by decide⟩,⟨1093084, by decide⟩,⟨1093126, by decide⟩,⟨1093158, by decide⟩]) unmarked_context_11_77212_1093159 node_context_11_77212_1093159
  intro a
  fin_cases a
  · exact context_12_308848_1093052
  · exact context_12_308849_1093084
  · exact context_12_308850_1093126
  · exact context_12_308851_1093158

theorem selected_cut_40235 : selected 10 ⟨1093220, by decide⟩
    (prefixPartial 11 77213) = some ⟨11, 2, 0, 1093220, 77213, 3113, 262144⟩ := by
  decide +kernel

theorem context_11_77213_1093220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77213 ⟨1093220, by decide⟩ :=
  accepted_of_selected 11 77213 ⟨1093220, by decide⟩ ⟨11, 2, 0, 1093220, 77213, 3113, 262144⟩
    (by decide) selected_cut_40235

theorem selected_cut_40236 : selected 10 ⟨1093282, by decide⟩
    (prefixPartial 11 77214) = some ⟨11, 2, 0, 1093282, 77214, 2745, 262144⟩ := by
  decide +kernel

theorem context_11_77214_1093282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77214 ⟨1093282, by decide⟩ :=
  accepted_of_selected 11 77214 ⟨1093282, by decide⟩ ⟨11, 2, 0, 1093282, 77214, 2745, 262144⟩
    (by decide) selected_cut_40236

theorem selected_cut_40237 : selected 10 ⟨1093333, by decide⟩
    (prefixPartial 11 77215) = some ⟨11, 2, 0, 1093333, 77215, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_77215_1093333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77215 ⟨1093333, by decide⟩ :=
  accepted_of_selected 11 77215 ⟨1093333, by decide⟩ ⟨11, 2, 0, 1093333, 77215, 2413, 262144⟩
    (by decide) selected_cut_40237

theorem unmarked_context_10_19303_1093334 : frontier 11 ⟨1093334, by decide⟩
    (prefixCache 10 19303) (prefixPartial 10 19303) = false := by
  decide +kernel

theorem node_context_10_19303_1093334 : EJMOriginalGlobalDAGData.nodes 11 ⟨1093334, by decide⟩ =
    .split (coordinate 10) (![⟨1093159, by decide⟩,⟨1093220, by decide⟩,⟨1093282, by decide⟩,⟨1093333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19303_1093334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19303 ⟨1093334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19303
    ⟨1093334, by decide⟩ (by decide) (![⟨1093159, by decide⟩,⟨1093220, by decide⟩,⟨1093282, by decide⟩,⟨1093333, by decide⟩]) unmarked_context_10_19303_1093334 node_context_10_19303_1093334
  intro a
  fin_cases a
  · exact context_11_77212_1093159
  · exact context_11_77213_1093220
  · exact context_11_77214_1093282
  · exact context_11_77215_1093333

theorem unmarked_context_9_4825_1093335 : frontier 12 ⟨1093335, by decide⟩
    (prefixCache 9 4825) (prefixPartial 9 4825) = false := by
  decide +kernel

theorem node_context_9_4825_1093335 : EJMOriginalGlobalDAGData.nodes 12 ⟨1093335, by decide⟩ =
    .split (coordinate 9) (![⟨1092496, by decide⟩,⟨893098, by decide⟩,⟨1093013, by decide⟩,⟨1093334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4825_1093335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4825 ⟨1093335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4825
    ⟨1093335, by decide⟩ (by decide) (![⟨1092496, by decide⟩,⟨893098, by decide⟩,⟨1093013, by decide⟩,⟨1093334, by decide⟩]) unmarked_context_9_4825_1093335 node_context_9_4825_1093335
  intro a
  fin_cases a
  · exact context_10_19300_1092496
  · exact context_10_19301_893098
  · exact context_10_19302_1093013
  · exact context_10_19303_1093334

theorem selected_cut_40238 : selected 12 ⟨33466, by decide⟩
    (prefixPartial 9 4826) = some ⟨9, 1, 0, 33466, 4826, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_4826_33466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4826 ⟨33466, by decide⟩ :=
  accepted_of_selected 9 4826 ⟨33466, by decide⟩ ⟨9, 1, 0, 33466, 4826, 1, 4194304⟩
    (by decide) selected_cut_40238

theorem selected_cut_40239 : selected 10 ⟨1093391, by decide⟩
    (prefixPartial 11 77232) = some ⟨11, 2, 0, 1093391, 77232, 2321, 262144⟩ := by
  decide +kernel

theorem context_11_77232_1093391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77232 ⟨1093391, by decide⟩ :=
  accepted_of_selected 11 77232 ⟨1093391, by decide⟩ ⟨11, 2, 0, 1093391, 77232, 2321, 262144⟩
    (by decide) selected_cut_40239

theorem selected_cut_40240 : selected 10 ⟨1093444, by decide⟩
    (prefixPartial 11 77233) = some ⟨11, 2, 0, 1093444, 77233, 2377, 262144⟩ := by
  decide +kernel

theorem context_11_77233_1093444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77233 ⟨1093444, by decide⟩ :=
  accepted_of_selected 11 77233 ⟨1093444, by decide⟩ ⟨11, 2, 0, 1093444, 77233, 2377, 262144⟩
    (by decide) selected_cut_40240

theorem selected_cut_40241 : selected 10 ⟨1093467, by decide⟩
    (prefixPartial 11 77234) = some ⟨11, 2, 0, 1093467, 77234, 809, 262144⟩ := by
  decide +kernel

theorem context_11_77234_1093467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77234 ⟨1093467, by decide⟩ :=
  accepted_of_selected 11 77234 ⟨1093467, by decide⟩ ⟨11, 2, 0, 1093467, 77234, 809, 262144⟩
    (by decide) selected_cut_40241

theorem selected_cut_40242 : selected 10 ⟨1093526, by decide⟩
    (prefixPartial 11 77235) = some ⟨11, 2, 0, 1093526, 77235, 1217, 262144⟩ := by
  decide +kernel

theorem context_11_77235_1093526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77235 ⟨1093526, by decide⟩ :=
  accepted_of_selected 11 77235 ⟨1093526, by decide⟩ ⟨11, 2, 0, 1093526, 77235, 1217, 262144⟩
    (by decide) selected_cut_40242

theorem unmarked_context_10_19308_1093527 : frontier 11 ⟨1093527, by decide⟩
    (prefixCache 10 19308) (prefixPartial 10 19308) = false := by
  decide +kernel

theorem node_context_10_19308_1093527 : EJMOriginalGlobalDAGData.nodes 11 ⟨1093527, by decide⟩ =
    .split (coordinate 10) (![⟨1093391, by decide⟩,⟨1093444, by decide⟩,⟨1093467, by decide⟩,⟨1093526, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19308_1093527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19308 ⟨1093527, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19308
    ⟨1093527, by decide⟩ (by decide) (![⟨1093391, by decide⟩,⟨1093444, by decide⟩,⟨1093467, by decide⟩,⟨1093526, by decide⟩]) unmarked_context_10_19308_1093527 node_context_10_19308_1093527
  intro a
  fin_cases a
  · exact context_11_77232_1093391
  · exact context_11_77233_1093444
  · exact context_11_77234_1093467
  · exact context_11_77235_1093526

theorem selected_cut_40243 : selected 11 ⟨1093589, by decide⟩
    (prefixPartial 10 19309) = some ⟨10, 2, 0, 1093589, 19309, 1453, 1048576⟩ := by
  decide +kernel

theorem context_10_19309_1093589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19309 ⟨1093589, by decide⟩ :=
  accepted_of_selected 10 19309 ⟨1093589, by decide⟩ ⟨10, 2, 0, 1093589, 19309, 1453, 1048576⟩
    (by decide) selected_cut_40243

theorem selected_cut_40244 : selected 11 ⟨1093627, by decide⟩
    (prefixPartial 10 19310) = some ⟨10, 2, 0, 1093627, 19310, 585, 1048576⟩ := by
  decide +kernel

theorem context_10_19310_1093627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19310 ⟨1093627, by decide⟩ :=
  accepted_of_selected 10 19310 ⟨1093627, by decide⟩ ⟨10, 2, 0, 1093627, 19310, 585, 1048576⟩
    (by decide) selected_cut_40244

theorem selected_cut_40245 : selected 11 ⟨1093628, by decide⟩
    (prefixPartial 10 19311) = some ⟨10, 2, 0, 1093628, 19311, 21, 1048576⟩ := by
  decide +kernel

theorem context_10_19311_1093628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19311 ⟨1093628, by decide⟩ :=
  accepted_of_selected 10 19311 ⟨1093628, by decide⟩ ⟨10, 2, 0, 1093628, 19311, 21, 1048576⟩
    (by decide) selected_cut_40245

theorem unmarked_context_9_4827_1093629 : frontier 12 ⟨1093629, by decide⟩
    (prefixCache 9 4827) (prefixPartial 9 4827) = false := by
  decide +kernel

theorem node_context_9_4827_1093629 : EJMOriginalGlobalDAGData.nodes 12 ⟨1093629, by decide⟩ =
    .split (coordinate 9) (![⟨1093527, by decide⟩,⟨1093589, by decide⟩,⟨1093627, by decide⟩,⟨1093628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4827_1093629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4827 ⟨1093629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4827
    ⟨1093629, by decide⟩ (by decide) (![⟨1093527, by decide⟩,⟨1093589, by decide⟩,⟨1093627, by decide⟩,⟨1093628, by decide⟩]) unmarked_context_9_4827_1093629 node_context_9_4827_1093629
  intro a
  fin_cases a
  · exact context_10_19308_1093527
  · exact context_10_19309_1093589
  · exact context_10_19310_1093627
  · exact context_10_19311_1093628

theorem unmarked_context_8_1206_1093630 : frontier 13 ⟨1093630, by decide⟩
    (prefixCache 8 1206) (prefixPartial 8 1206) = false := by
  decide +kernel

theorem node_context_8_1206_1093630 : EJMOriginalGlobalDAGData.nodes 13 ⟨1093630, by decide⟩ =
    .split (coordinate 8) (![⟨1091759, by decide⟩,⟨1093335, by decide⟩,⟨33466, by decide⟩,⟨1093629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1206_1093630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1206 ⟨1093630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1206
    ⟨1093630, by decide⟩ (by decide) (![⟨1091759, by decide⟩,⟨1093335, by decide⟩,⟨33466, by decide⟩,⟨1093629, by decide⟩]) unmarked_context_8_1206_1093630 node_context_8_1206_1093630
  intro a
  fin_cases a
  · exact context_9_4824_1091759
  · exact context_9_4825_1093335
  · exact context_9_4826_33466
  · exact context_9_4827_1093629

theorem selected_cut_40246 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 77248) = some ⟨11, 1, 0, 167448, 77248, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77248_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77248 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 77248 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 77248, 1, 262144⟩
    (by decide) selected_cut_40246

theorem selected_cut_40247 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 308996) = some ⟨12, 1, 0, 34034, 308996, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308996_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308996 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 308996 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 308996, 1, 65536⟩
    (by decide) selected_cut_40247

theorem selected_cut_40248 : selected 8 ⟨1093656, by decide⟩
    (prefixPartial 13 1235988) = some ⟨13, 2, 0, 1093656, 1235988, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_1235988_1093656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235988 ⟨1093656, by decide⟩ :=
  accepted_of_selected 13 1235988 ⟨1093656, by decide⟩ ⟨13, 2, 0, 1093656, 1235988, 1525, 16384⟩
    (by decide) selected_cut_40248

theorem selected_cut_40249 : selected 8 ⟨1093678, by decide⟩
    (prefixPartial 13 1235989) = some ⟨13, 2, 0, 1093678, 1235989, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_1235989_1093678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235989 ⟨1093678, by decide⟩ :=
  accepted_of_selected 13 1235989 ⟨1093678, by decide⟩ ⟨13, 2, 0, 1093678, 1235989, 1321, 16384⟩
    (by decide) selected_cut_40249

theorem selected_cut_40250 : selected 8 ⟨1093691, by decide⟩
    (prefixPartial 13 1235990) = some ⟨13, 2, 0, 1093691, 1235990, 781, 16384⟩ := by
  decide +kernel

theorem context_13_1235990_1093691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235990 ⟨1093691, by decide⟩ :=
  accepted_of_selected 13 1235990 ⟨1093691, by decide⟩ ⟨13, 2, 0, 1093691, 1235990, 781, 16384⟩
    (by decide) selected_cut_40250

theorem selected_cut_40251 : selected 8 ⟨1093699, by decide⟩
    (prefixPartial 13 1235991) = some ⟨13, 2, 0, 1093699, 1235991, 497, 16384⟩ := by
  decide +kernel

theorem context_13_1235991_1093699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235991 ⟨1093699, by decide⟩ :=
  accepted_of_selected 13 1235991 ⟨1093699, by decide⟩ ⟨13, 2, 0, 1093699, 1235991, 497, 16384⟩
    (by decide) selected_cut_40251

theorem unmarked_context_12_308997_1093700 : frontier 9 ⟨1093700, by decide⟩
    (prefixCache 12 308997) (prefixPartial 12 308997) = false := by
  decide +kernel

theorem node_context_12_308997_1093700 : EJMOriginalGlobalDAGData.nodes 9 ⟨1093700, by decide⟩ =
    .split (coordinate 12) (![⟨1093656, by decide⟩,⟨1093678, by decide⟩,⟨1093691, by decide⟩,⟨1093699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308997_1093700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308997 ⟨1093700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308997
    ⟨1093700, by decide⟩ (by decide) (![⟨1093656, by decide⟩,⟨1093678, by decide⟩,⟨1093691, by decide⟩,⟨1093699, by decide⟩]) unmarked_context_12_308997_1093700 node_context_12_308997_1093700
  intro a
  fin_cases a
  · exact context_13_1235988_1093656
  · exact context_13_1235989_1093678
  · exact context_13_1235990_1093691
  · exact context_13_1235991_1093699

theorem selected_cut_40252 : selected 8 ⟨1093724, by decide⟩
    (prefixPartial 13 1235992) = some ⟨13, 2, 0, 1093724, 1235992, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_1235992_1093724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235992 ⟨1093724, by decide⟩ :=
  accepted_of_selected 13 1235992 ⟨1093724, by decide⟩ ⟨13, 2, 0, 1093724, 1235992, 1617, 16384⟩
    (by decide) selected_cut_40252

theorem selected_cut_40253 : selected 8 ⟨1093740, by decide⟩
    (prefixPartial 13 1235993) = some ⟨13, 2, 0, 1093740, 1235993, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_1235993_1093740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235993 ⟨1093740, by decide⟩ :=
  accepted_of_selected 13 1235993 ⟨1093740, by decide⟩ ⟨13, 2, 0, 1093740, 1235993, 1193, 16384⟩
    (by decide) selected_cut_40253

theorem selected_cut_40254 : selected 8 ⟨1093753, by decide⟩
    (prefixPartial 13 1235994) = some ⟨13, 2, 0, 1093753, 1235994, 817, 16384⟩ := by
  decide +kernel

theorem context_13_1235994_1093753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235994 ⟨1093753, by decide⟩ :=
  accepted_of_selected 13 1235994 ⟨1093753, by decide⟩ ⟨13, 2, 0, 1093753, 1235994, 817, 16384⟩
    (by decide) selected_cut_40254

theorem selected_cut_40255 : selected 8 ⟨1093760, by decide⟩
    (prefixPartial 13 1235995) = some ⟨13, 2, 0, 1093760, 1235995, 565, 16384⟩ := by
  decide +kernel

theorem context_13_1235995_1093760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235995 ⟨1093760, by decide⟩ :=
  accepted_of_selected 13 1235995 ⟨1093760, by decide⟩ ⟨13, 2, 0, 1093760, 1235995, 565, 16384⟩
    (by decide) selected_cut_40255

theorem unmarked_context_12_308998_1093761 : frontier 9 ⟨1093761, by decide⟩
    (prefixCache 12 308998) (prefixPartial 12 308998) = false := by
  decide +kernel

theorem node_context_12_308998_1093761 : EJMOriginalGlobalDAGData.nodes 9 ⟨1093761, by decide⟩ =
    .split (coordinate 12) (![⟨1093724, by decide⟩,⟨1093740, by decide⟩,⟨1093753, by decide⟩,⟨1093760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308998_1093761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308998 ⟨1093761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308998
    ⟨1093761, by decide⟩ (by decide) (![⟨1093724, by decide⟩,⟨1093740, by decide⟩,⟨1093753, by decide⟩,⟨1093760, by decide⟩]) unmarked_context_12_308998_1093761 node_context_12_308998_1093761
  intro a
  fin_cases a
  · exact context_13_1235992_1093724
  · exact context_13_1235993_1093740
  · exact context_13_1235994_1093753
  · exact context_13_1235995_1093760

theorem selected_cut_40256 : selected 9 ⟨1093820, by decide⟩
    (prefixPartial 12 308999) = some ⟨12, 2, 0, 1093820, 308999, 3877, 65536⟩ := by
  decide +kernel

theorem context_12_308999_1093820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308999 ⟨1093820, by decide⟩ :=
  accepted_of_selected 12 308999 ⟨1093820, by decide⟩ ⟨12, 2, 0, 1093820, 308999, 3877, 65536⟩
    (by decide) selected_cut_40256

theorem unmarked_context_11_77249_1093821 : frontier 10 ⟨1093821, by decide⟩
    (prefixCache 11 77249) (prefixPartial 11 77249) = false := by
  decide +kernel

theorem node_context_11_77249_1093821 : EJMOriginalGlobalDAGData.nodes 10 ⟨1093821, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1093700, by decide⟩,⟨1093761, by decide⟩,⟨1093820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77249_1093821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77249 ⟨1093821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77249
    ⟨1093821, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1093700, by decide⟩,⟨1093761, by decide⟩,⟨1093820, by decide⟩]) unmarked_context_11_77249_1093821 node_context_11_77249_1093821
  intro a
  fin_cases a
  · exact context_12_308996_34034
  · exact context_12_308997_1093700
  · exact context_12_308998_1093761
  · exact context_12_308999_1093820

theorem selected_cut_40257 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 309000) = some ⟨12, 1, 0, 34034, 309000, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309000_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309000 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 309000 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 309000, 1, 65536⟩
    (by decide) selected_cut_40257

theorem selected_cut_40258 : selected 8 ⟨1093844, by decide⟩
    (prefixPartial 13 1236004) = some ⟨13, 2, 0, 1093844, 1236004, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_1236004_1093844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236004 ⟨1093844, by decide⟩ :=
  accepted_of_selected 13 1236004 ⟨1093844, by decide⟩ ⟨13, 2, 0, 1093844, 1236004, 1373, 16384⟩
    (by decide) selected_cut_40258

theorem selected_cut_40259 : selected 8 ⟨1093861, by decide⟩
    (prefixPartial 13 1236005) = some ⟨13, 2, 0, 1093861, 1236005, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_1236005_1093861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236005 ⟨1093861, by decide⟩ :=
  accepted_of_selected 13 1236005 ⟨1093861, by decide⟩ ⟨13, 2, 0, 1093861, 1236005, 1341, 16384⟩
    (by decide) selected_cut_40259

theorem selected_cut_40260 : selected 8 ⟨1093875, by decide⟩
    (prefixPartial 13 1236006) = some ⟨13, 2, 0, 1093875, 1236006, 857, 16384⟩ := by
  decide +kernel

theorem context_13_1236006_1093875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236006 ⟨1093875, by decide⟩ :=
  accepted_of_selected 13 1236006 ⟨1093875, by decide⟩ ⟨13, 2, 0, 1093875, 1236006, 857, 16384⟩
    (by decide) selected_cut_40260

theorem selected_cut_40261 : selected 8 ⟨1093882, by decide⟩
    (prefixPartial 13 1236007) = some ⟨13, 2, 0, 1093882, 1236007, 557, 16384⟩ := by
  decide +kernel

theorem context_13_1236007_1093882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236007 ⟨1093882, by decide⟩ :=
  accepted_of_selected 13 1236007 ⟨1093882, by decide⟩ ⟨13, 2, 0, 1093882, 1236007, 557, 16384⟩
    (by decide) selected_cut_40261

theorem unmarked_context_12_309001_1093883 : frontier 9 ⟨1093883, by decide⟩
    (prefixCache 12 309001) (prefixPartial 12 309001) = false := by
  decide +kernel

theorem node_context_12_309001_1093883 : EJMOriginalGlobalDAGData.nodes 9 ⟨1093883, by decide⟩ =
    .split (coordinate 12) (![⟨1093844, by decide⟩,⟨1093861, by decide⟩,⟨1093875, by decide⟩,⟨1093882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_309001_1093883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309001 ⟨1093883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 309001
    ⟨1093883, by decide⟩ (by decide) (![⟨1093844, by decide⟩,⟨1093861, by decide⟩,⟨1093875, by decide⟩,⟨1093882, by decide⟩]) unmarked_context_12_309001_1093883 node_context_12_309001_1093883
  intro a
  fin_cases a
  · exact context_13_1236004_1093844
  · exact context_13_1236005_1093861
  · exact context_13_1236006_1093875
  · exact context_13_1236007_1093882

theorem selected_cut_40262 : selected 8 ⟨1093907, by decide⟩
    (prefixPartial 13 1236008) = some ⟨13, 2, 0, 1093907, 1236008, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_1236008_1093907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236008 ⟨1093907, by decide⟩ :=
  accepted_of_selected 13 1236008 ⟨1093907, by decide⟩ ⟨13, 2, 0, 1093907, 1236008, 1437, 16384⟩
    (by decide) selected_cut_40262

theorem selected_cut_40263 : selected 8 ⟨1093927, by decide⟩
    (prefixPartial 13 1236009) = some ⟨13, 2, 0, 1093927, 1236009, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_1236009_1093927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236009 ⟨1093927, by decide⟩ :=
  accepted_of_selected 13 1236009 ⟨1093927, by decide⟩ ⟨13, 2, 0, 1093927, 1236009, 1377, 16384⟩
    (by decide) selected_cut_40263

theorem selected_cut_40264 : selected 8 ⟨1093948, by decide⟩
    (prefixPartial 13 1236010) = some ⟨13, 2, 0, 1093948, 1236010, 981, 16384⟩ := by
  decide +kernel

theorem context_13_1236010_1093948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236010 ⟨1093948, by decide⟩ :=
  accepted_of_selected 13 1236010 ⟨1093948, by decide⟩ ⟨13, 2, 0, 1093948, 1236010, 981, 16384⟩
    (by decide) selected_cut_40264

theorem selected_cut_40265 : selected 8 ⟨1093954, by decide⟩
    (prefixPartial 13 1236011) = some ⟨13, 2, 0, 1093954, 1236011, 577, 16384⟩ := by
  decide +kernel

theorem context_13_1236011_1093954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236011 ⟨1093954, by decide⟩ :=
  accepted_of_selected 13 1236011 ⟨1093954, by decide⟩ ⟨13, 2, 0, 1093954, 1236011, 577, 16384⟩
    (by decide) selected_cut_40265

theorem unmarked_context_12_309002_1093955 : frontier 9 ⟨1093955, by decide⟩
    (prefixCache 12 309002) (prefixPartial 12 309002) = false := by
  decide +kernel

theorem node_context_12_309002_1093955 : EJMOriginalGlobalDAGData.nodes 9 ⟨1093955, by decide⟩ =
    .split (coordinate 12) (![⟨1093907, by decide⟩,⟨1093927, by decide⟩,⟨1093948, by decide⟩,⟨1093954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_309002_1093955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309002 ⟨1093955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 309002
    ⟨1093955, by decide⟩ (by decide) (![⟨1093907, by decide⟩,⟨1093927, by decide⟩,⟨1093948, by decide⟩,⟨1093954, by decide⟩]) unmarked_context_12_309002_1093955 node_context_12_309002_1093955
  intro a
  fin_cases a
  · exact context_13_1236008_1093907
  · exact context_13_1236009_1093927
  · exact context_13_1236010_1093948
  · exact context_13_1236011_1093954

theorem selected_cut_40266 : selected 8 ⟨1093975, by decide⟩
    (prefixPartial 13 1236012) = some ⟨13, 2, 0, 1093975, 1236012, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_1236012_1093975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236012 ⟨1093975, by decide⟩ :=
  accepted_of_selected 13 1236012 ⟨1093975, by decide⟩ ⟨13, 2, 0, 1093975, 1236012, 1329, 16384⟩
    (by decide) selected_cut_40266

theorem selected_cut_40267 : selected 8 ⟨1094001, by decide⟩
    (prefixPartial 13 1236013) = some ⟨13, 2, 0, 1094001, 1236013, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_1236013_1094001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236013 ⟨1094001, by decide⟩ :=
  accepted_of_selected 13 1236013 ⟨1094001, by decide⟩ ⟨13, 2, 0, 1094001, 1236013, 1485, 16384⟩
    (by decide) selected_cut_40267

theorem selected_cut_40268 : selected 8 ⟨1094019, by decide⟩
    (prefixPartial 13 1236014) = some ⟨13, 2, 0, 1094019, 1236014, 941, 16384⟩ := by
  decide +kernel

theorem context_13_1236014_1094019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236014 ⟨1094019, by decide⟩ :=
  accepted_of_selected 13 1236014 ⟨1094019, by decide⟩ ⟨13, 2, 0, 1094019, 1236014, 941, 16384⟩
    (by decide) selected_cut_40268

theorem selected_cut_40269 : selected 8 ⟨1094025, by decide⟩
    (prefixPartial 13 1236015) = some ⟨13, 2, 0, 1094025, 1236015, 537, 16384⟩ := by
  decide +kernel

theorem context_13_1236015_1094025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236015 ⟨1094025, by decide⟩ :=
  accepted_of_selected 13 1236015 ⟨1094025, by decide⟩ ⟨13, 2, 0, 1094025, 1236015, 537, 16384⟩
    (by decide) selected_cut_40269

theorem unmarked_context_12_309003_1094026 : frontier 9 ⟨1094026, by decide⟩
    (prefixCache 12 309003) (prefixPartial 12 309003) = false := by
  decide +kernel

theorem node_context_12_309003_1094026 : EJMOriginalGlobalDAGData.nodes 9 ⟨1094026, by decide⟩ =
    .split (coordinate 12) (![⟨1093975, by decide⟩,⟨1094001, by decide⟩,⟨1094019, by decide⟩,⟨1094025, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_309003_1094026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309003 ⟨1094026, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 309003
    ⟨1094026, by decide⟩ (by decide) (![⟨1093975, by decide⟩,⟨1094001, by decide⟩,⟨1094019, by decide⟩,⟨1094025, by decide⟩]) unmarked_context_12_309003_1094026 node_context_12_309003_1094026
  intro a
  fin_cases a
  · exact context_13_1236012_1093975
  · exact context_13_1236013_1094001
  · exact context_13_1236014_1094019
  · exact context_13_1236015_1094025

theorem unmarked_context_11_77250_1094027 : frontier 10 ⟨1094027, by decide⟩
    (prefixCache 11 77250) (prefixPartial 11 77250) = false := by
  decide +kernel

theorem node_context_11_77250_1094027 : EJMOriginalGlobalDAGData.nodes 10 ⟨1094027, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1093883, by decide⟩,⟨1093955, by decide⟩,⟨1094026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77250_1094027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77250 ⟨1094027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77250
    ⟨1094027, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1093883, by decide⟩,⟨1093955, by decide⟩,⟨1094026, by decide⟩]) unmarked_context_11_77250_1094027 node_context_11_77250_1094027
  intro a
  fin_cases a
  · exact context_12_309000_34034
  · exact context_12_309001_1093883
  · exact context_12_309002_1093955
  · exact context_12_309003_1094026

theorem selected_cut_40270 : selected 8 ⟨1094054, by decide⟩
    (prefixPartial 13 1236016) = some ⟨13, 2, 0, 1094054, 1236016, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_1236016_1094054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236016 ⟨1094054, by decide⟩ :=
  accepted_of_selected 13 1236016 ⟨1094054, by decide⟩ ⟨13, 2, 0, 1094054, 1236016, 1181, 16384⟩
    (by decide) selected_cut_40270

theorem selected_cut_40271 : selected 8 ⟨1094094, by decide⟩
    (prefixPartial 13 1236017) = some ⟨13, 2, 0, 1094094, 1236017, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_1236017_1094094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236017 ⟨1094094, by decide⟩ :=
  accepted_of_selected 13 1236017 ⟨1094094, by decide⟩ ⟨13, 2, 0, 1094094, 1236017, 1785, 16384⟩
    (by decide) selected_cut_40271

theorem selected_cut_40272 : selected 8 ⟨1094121, by decide⟩
    (prefixPartial 13 1236018) = some ⟨13, 2, 0, 1094121, 1236018, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_1236018_1094121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236018 ⟨1094121, by decide⟩ :=
  accepted_of_selected 13 1236018 ⟨1094121, by decide⟩ ⟨13, 2, 0, 1094121, 1236018, 1021, 16384⟩
    (by decide) selected_cut_40272

theorem selected_cut_40273 : selected 8 ⟨1094135, by decide⟩
    (prefixPartial 13 1236019) = some ⟨13, 2, 0, 1094135, 1236019, 737, 16384⟩ := by
  decide +kernel

theorem context_13_1236019_1094135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236019 ⟨1094135, by decide⟩ :=
  accepted_of_selected 13 1236019 ⟨1094135, by decide⟩ ⟨13, 2, 0, 1094135, 1236019, 737, 16384⟩
    (by decide) selected_cut_40273

theorem unmarked_context_12_309004_1094136 : frontier 9 ⟨1094136, by decide⟩
    (prefixCache 12 309004) (prefixPartial 12 309004) = false := by
  decide +kernel

theorem node_context_12_309004_1094136 : EJMOriginalGlobalDAGData.nodes 9 ⟨1094136, by decide⟩ =
    .split (coordinate 12) (![⟨1094054, by decide⟩,⟨1094094, by decide⟩,⟨1094121, by decide⟩,⟨1094135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_309004_1094136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309004 ⟨1094136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 309004
    ⟨1094136, by decide⟩ (by decide) (![⟨1094054, by decide⟩,⟨1094094, by decide⟩,⟨1094121, by decide⟩,⟨1094135, by decide⟩]) unmarked_context_12_309004_1094136 node_context_12_309004_1094136
  intro a
  fin_cases a
  · exact context_13_1236016_1094054
  · exact context_13_1236017_1094094
  · exact context_13_1236018_1094121
  · exact context_13_1236019_1094135

theorem selected_cut_40274 : selected 9 ⟨1094202, by decide⟩
    (prefixPartial 12 309005) = some ⟨12, 2, 0, 1094202, 309005, 4013, 65536⟩ := by
  decide +kernel

theorem context_12_309005_1094202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309005 ⟨1094202, by decide⟩ :=
  accepted_of_selected 12 309005 ⟨1094202, by decide⟩ ⟨12, 2, 0, 1094202, 309005, 4013, 65536⟩
    (by decide) selected_cut_40274

theorem selected_cut_40275 : selected 8 ⟨1094224, by decide⟩
    (prefixPartial 13 1236024) = some ⟨13, 2, 0, 1094224, 1236024, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_1236024_1094224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236024 ⟨1094224, by decide⟩ :=
  accepted_of_selected 13 1236024 ⟨1094224, by decide⟩ ⟨13, 2, 0, 1094224, 1236024, 1285, 16384⟩
    (by decide) selected_cut_40275

theorem selected_cut_40276 : selected 8 ⟨1094251, by decide⟩
    (prefixPartial 13 1236025) = some ⟨13, 2, 0, 1094251, 1236025, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_1236025_1094251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236025 ⟨1094251, by decide⟩ :=
  accepted_of_selected 13 1236025 ⟨1094251, by decide⟩ ⟨13, 2, 0, 1094251, 1236025, 1621, 16384⟩
    (by decide) selected_cut_40276

theorem selected_cut_40277 : selected 8 ⟨1094267, by decide⟩
    (prefixPartial 13 1236026) = some ⟨13, 2, 0, 1094267, 1236026, 841, 16384⟩ := by
  decide +kernel

theorem context_13_1236026_1094267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236026 ⟨1094267, by decide⟩ :=
  accepted_of_selected 13 1236026 ⟨1094267, by decide⟩ ⟨13, 2, 0, 1094267, 1236026, 841, 16384⟩
    (by decide) selected_cut_40277

theorem selected_cut_40278 : selected 8 ⟨1094274, by decide⟩
    (prefixPartial 13 1236027) = some ⟨13, 2, 0, 1094274, 1236027, 605, 16384⟩ := by
  decide +kernel

theorem context_13_1236027_1094274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1236027 ⟨1094274, by decide⟩ :=
  accepted_of_selected 13 1236027 ⟨1094274, by decide⟩ ⟨13, 2, 0, 1094274, 1236027, 605, 16384⟩
    (by decide) selected_cut_40278

theorem unmarked_context_12_309006_1094275 : frontier 9 ⟨1094275, by decide⟩
    (prefixCache 12 309006) (prefixPartial 12 309006) = false := by
  decide +kernel

theorem node_context_12_309006_1094275 : EJMOriginalGlobalDAGData.nodes 9 ⟨1094275, by decide⟩ =
    .split (coordinate 12) (![⟨1094224, by decide⟩,⟨1094251, by decide⟩,⟨1094267, by decide⟩,⟨1094274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_309006_1094275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309006 ⟨1094275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 309006
    ⟨1094275, by decide⟩ (by decide) (![⟨1094224, by decide⟩,⟨1094251, by decide⟩,⟨1094267, by decide⟩,⟨1094274, by decide⟩]) unmarked_context_12_309006_1094275 node_context_12_309006_1094275
  intro a
  fin_cases a
  · exact context_13_1236024_1094224
  · exact context_13_1236025_1094251
  · exact context_13_1236026_1094267
  · exact context_13_1236027_1094274

theorem selected_cut_40279 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 309007) = some ⟨12, 1, 0, 903806, 309007, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309007_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309007 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 309007 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 309007, 1, 65536⟩
    (by decide) selected_cut_40279

theorem unmarked_context_11_77251_1094276 : frontier 10 ⟨1094276, by decide⟩
    (prefixCache 11 77251) (prefixPartial 11 77251) = false := by
  decide +kernel

theorem node_context_11_77251_1094276 : EJMOriginalGlobalDAGData.nodes 10 ⟨1094276, by decide⟩ =
    .split (coordinate 11) (![⟨1094136, by decide⟩,⟨1094202, by decide⟩,⟨1094275, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77251_1094276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77251 ⟨1094276, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77251
    ⟨1094276, by decide⟩ (by decide) (![⟨1094136, by decide⟩,⟨1094202, by decide⟩,⟨1094275, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77251_1094276 node_context_11_77251_1094276
  intro a
  fin_cases a
  · exact context_12_309004_1094136
  · exact context_12_309005_1094202
  · exact context_12_309006_1094275
  · exact context_12_309007_903806

theorem unmarked_context_10_19312_1094277 : frontier 11 ⟨1094277, by decide⟩
    (prefixCache 10 19312) (prefixPartial 10 19312) = false := by
  decide +kernel

theorem node_context_10_19312_1094277 : EJMOriginalGlobalDAGData.nodes 11 ⟨1094277, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨1093821, by decide⟩,⟨1094027, by decide⟩,⟨1094276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19312_1094277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19312 ⟨1094277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19312
    ⟨1094277, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨1093821, by decide⟩,⟨1094027, by decide⟩,⟨1094276, by decide⟩]) unmarked_context_10_19312_1094277 node_context_10_19312_1094277
  intro a
  fin_cases a
  · exact context_11_77248_167448
  · exact context_11_77249_1093821
  · exact context_11_77250_1094027
  · exact context_11_77251_1094276

theorem selected_cut_40280 : selected 9 ⟨1094332, by decide⟩
    (prefixPartial 12 309008) = some ⟨12, 2, 0, 1094332, 309008, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_309008_1094332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309008 ⟨1094332, by decide⟩ :=
  accepted_of_selected 12 309008 ⟨1094332, by decide⟩ ⟨12, 2, 0, 1094332, 309008, 3285, 65536⟩
    (by decide) selected_cut_40280

theorem selected_cut_40281 : selected 9 ⟨1094382, by decide⟩
    (prefixPartial 12 309009) = some ⟨12, 2, 0, 1094382, 309009, 3113, 65536⟩ := by
  decide +kernel

theorem context_12_309009_1094382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309009 ⟨1094382, by decide⟩ :=
  accepted_of_selected 12 309009 ⟨1094382, by decide⟩ ⟨12, 2, 0, 1094382, 309009, 3113, 65536⟩
    (by decide) selected_cut_40281

theorem selected_cut_40282 : selected 9 ⟨1094435, by decide⟩
    (prefixPartial 12 309010) = some ⟨12, 2, 0, 1094435, 309010, 3361, 65536⟩ := by
  decide +kernel

theorem context_12_309010_1094435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309010 ⟨1094435, by decide⟩ :=
  accepted_of_selected 12 309010 ⟨1094435, by decide⟩ ⟨12, 2, 0, 1094435, 309010, 3361, 65536⟩
    (by decide) selected_cut_40282

theorem selected_cut_40283 : selected 9 ⟨1094482, by decide⟩
    (prefixPartial 12 309011) = some ⟨12, 2, 0, 1094482, 309011, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_309011_1094482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309011 ⟨1094482, by decide⟩ :=
  accepted_of_selected 12 309011 ⟨1094482, by decide⟩ ⟨12, 2, 0, 1094482, 309011, 3121, 65536⟩
    (by decide) selected_cut_40283

theorem unmarked_context_11_77252_1094483 : frontier 10 ⟨1094483, by decide⟩
    (prefixCache 11 77252) (prefixPartial 11 77252) = false := by
  decide +kernel

theorem node_context_11_77252_1094483 : EJMOriginalGlobalDAGData.nodes 10 ⟨1094483, by decide⟩ =
    .split (coordinate 11) (![⟨1094332, by decide⟩,⟨1094382, by decide⟩,⟨1094435, by decide⟩,⟨1094482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77252_1094483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77252 ⟨1094483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77252
    ⟨1094483, by decide⟩ (by decide) (![⟨1094332, by decide⟩,⟨1094382, by decide⟩,⟨1094435, by decide⟩,⟨1094482, by decide⟩]) unmarked_context_11_77252_1094483 node_context_11_77252_1094483
  intro a
  fin_cases a
  · exact context_12_309008_1094332
  · exact context_12_309009_1094382
  · exact context_12_309010_1094435
  · exact context_12_309011_1094482

theorem selected_cut_40284 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 77253) = some ⟨11, 1, 0, 892405, 77253, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77253_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77253 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 77253 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 77253, 1, 262144⟩
    (by decide) selected_cut_40284

theorem selected_cut_40285 : selected 9 ⟨1094547, by decide⟩
    (prefixPartial 12 309016) = some ⟨12, 2, 0, 1094547, 309016, 3837, 65536⟩ := by
  decide +kernel

theorem context_12_309016_1094547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309016 ⟨1094547, by decide⟩ :=
  accepted_of_selected 12 309016 ⟨1094547, by decide⟩ ⟨12, 2, 0, 1094547, 309016, 3837, 65536⟩
    (by decide) selected_cut_40285

theorem selected_cut_40286 : selected 9 ⟨1094595, by decide⟩
    (prefixPartial 12 309017) = some ⟨12, 2, 0, 1094595, 309017, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_309017_1094595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309017 ⟨1094595, by decide⟩ :=
  accepted_of_selected 12 309017 ⟨1094595, by decide⟩ ⟨12, 2, 0, 1094595, 309017, 3277, 65536⟩
    (by decide) selected_cut_40286

theorem selected_cut_40287 : selected 9 ⟨1094648, by decide⟩
    (prefixPartial 12 309018) = some ⟨12, 2, 0, 1094648, 309018, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_309018_1094648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309018 ⟨1094648, by decide⟩ :=
  accepted_of_selected 12 309018 ⟨1094648, by decide⟩ ⟨12, 2, 0, 1094648, 309018, 3421, 65536⟩
    (by decide) selected_cut_40287

theorem selected_cut_40288 : selected 9 ⟨1094700, by decide⟩
    (prefixPartial 12 309019) = some ⟨12, 2, 0, 1094700, 309019, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_309019_1094700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309019 ⟨1094700, by decide⟩ :=
  accepted_of_selected 12 309019 ⟨1094700, by decide⟩ ⟨12, 2, 0, 1094700, 309019, 3509, 65536⟩
    (by decide) selected_cut_40288

theorem unmarked_context_11_77254_1094701 : frontier 10 ⟨1094701, by decide⟩
    (prefixCache 11 77254) (prefixPartial 11 77254) = false := by
  decide +kernel

theorem node_context_11_77254_1094701 : EJMOriginalGlobalDAGData.nodes 10 ⟨1094701, by decide⟩ =
    .split (coordinate 11) (![⟨1094547, by decide⟩,⟨1094595, by decide⟩,⟨1094648, by decide⟩,⟨1094700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77254_1094701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77254 ⟨1094701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77254
    ⟨1094701, by decide⟩ (by decide) (![⟨1094547, by decide⟩,⟨1094595, by decide⟩,⟨1094648, by decide⟩,⟨1094700, by decide⟩]) unmarked_context_11_77254_1094701 node_context_11_77254_1094701
  intro a
  fin_cases a
  · exact context_12_309016_1094547
  · exact context_12_309017_1094595
  · exact context_12_309018_1094648
  · exact context_12_309019_1094700

theorem selected_cut_40289 : selected 9 ⟨1094762, by decide⟩
    (prefixPartial 12 309020) = some ⟨12, 2, 0, 1094762, 309020, 3773, 65536⟩ := by
  decide +kernel

theorem context_12_309020_1094762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309020 ⟨1094762, by decide⟩ :=
  accepted_of_selected 12 309020 ⟨1094762, by decide⟩ ⟨12, 2, 0, 1094762, 309020, 3773, 65536⟩
    (by decide) selected_cut_40289

theorem selected_cut_40290 : selected 9 ⟨1094804, by decide⟩
    (prefixPartial 12 309021) = some ⟨12, 2, 0, 1094804, 309021, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_309021_1094804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309021 ⟨1094804, by decide⟩ :=
  accepted_of_selected 12 309021 ⟨1094804, by decide⟩ ⟨12, 2, 0, 1094804, 309021, 3249, 65536⟩
    (by decide) selected_cut_40290

theorem selected_cut_40291 : selected 9 ⟨1094860, by decide⟩
    (prefixPartial 12 309022) = some ⟨12, 2, 0, 1094860, 309022, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_309022_1094860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309022 ⟨1094860, by decide⟩ :=
  accepted_of_selected 12 309022 ⟨1094860, by decide⟩ ⟨12, 2, 0, 1094860, 309022, 3513, 65536⟩
    (by decide) selected_cut_40291

theorem selected_cut_40292 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 309023) = some ⟨12, 1, 0, 903806, 309023, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309023_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309023 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 309023 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 309023, 1, 65536⟩
    (by decide) selected_cut_40292

theorem unmarked_context_11_77255_1094861 : frontier 10 ⟨1094861, by decide⟩
    (prefixCache 11 77255) (prefixPartial 11 77255) = false := by
  decide +kernel

theorem node_context_11_77255_1094861 : EJMOriginalGlobalDAGData.nodes 10 ⟨1094861, by decide⟩ =
    .split (coordinate 11) (![⟨1094762, by decide⟩,⟨1094804, by decide⟩,⟨1094860, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77255_1094861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77255 ⟨1094861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77255
    ⟨1094861, by decide⟩ (by decide) (![⟨1094762, by decide⟩,⟨1094804, by decide⟩,⟨1094860, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77255_1094861 node_context_11_77255_1094861
  intro a
  fin_cases a
  · exact context_12_309020_1094762
  · exact context_12_309021_1094804
  · exact context_12_309022_1094860
  · exact context_12_309023_903806

theorem unmarked_context_10_19313_1094862 : frontier 11 ⟨1094862, by decide⟩
    (prefixCache 10 19313) (prefixPartial 10 19313) = false := by
  decide +kernel

theorem node_context_10_19313_1094862 : EJMOriginalGlobalDAGData.nodes 11 ⟨1094862, by decide⟩ =
    .split (coordinate 10) (![⟨1094483, by decide⟩,⟨892405, by decide⟩,⟨1094701, by decide⟩,⟨1094861, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19313_1094862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19313 ⟨1094862, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19313
    ⟨1094862, by decide⟩ (by decide) (![⟨1094483, by decide⟩,⟨892405, by decide⟩,⟨1094701, by decide⟩,⟨1094861, by decide⟩]) unmarked_context_10_19313_1094862 node_context_10_19313_1094862
  intro a
  fin_cases a
  · exact context_11_77252_1094483
  · exact context_11_77253_892405
  · exact context_11_77254_1094701
  · exact context_11_77255_1094861

theorem selected_cut_40293 : selected 9 ⟨1082322, by decide⟩
    (prefixPartial 12 309024) = some ⟨12, 1, 0, 1082322, 309024, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309024_1082322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309024 ⟨1082322, by decide⟩ :=
  accepted_of_selected 12 309024 ⟨1082322, by decide⟩ ⟨12, 1, 0, 1082322, 309024, 1, 65536⟩
    (by decide) selected_cut_40293

theorem selected_cut_40294 : selected 9 ⟨1094912, by decide⟩
    (prefixPartial 12 309025) = some ⟨12, 2, 0, 1094912, 309025, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_309025_1094912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309025 ⟨1094912, by decide⟩ :=
  accepted_of_selected 12 309025 ⟨1094912, by decide⟩ ⟨12, 2, 0, 1094912, 309025, 3257, 65536⟩
    (by decide) selected_cut_40294

theorem selected_cut_40295 : selected 9 ⟨1094961, by decide⟩
    (prefixPartial 12 309026) = some ⟨12, 2, 0, 1094961, 309026, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_309026_1094961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309026 ⟨1094961, by decide⟩ :=
  accepted_of_selected 12 309026 ⟨1094961, by decide⟩ ⟨12, 2, 0, 1094961, 309026, 3401, 65536⟩
    (by decide) selected_cut_40295

theorem selected_cut_40296 : selected 9 ⟨1095004, by decide⟩
    (prefixPartial 12 309027) = some ⟨12, 2, 0, 1095004, 309027, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_309027_1095004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309027 ⟨1095004, by decide⟩ :=
  accepted_of_selected 12 309027 ⟨1095004, by decide⟩ ⟨12, 2, 0, 1095004, 309027, 3173, 65536⟩
    (by decide) selected_cut_40296

theorem unmarked_context_11_77256_1095005 : frontier 10 ⟨1095005, by decide⟩
    (prefixCache 11 77256) (prefixPartial 11 77256) = false := by
  decide +kernel

theorem node_context_11_77256_1095005 : EJMOriginalGlobalDAGData.nodes 10 ⟨1095005, by decide⟩ =
    .split (coordinate 11) (![⟨1082322, by decide⟩,⟨1094912, by decide⟩,⟨1094961, by decide⟩,⟨1095004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77256_1095005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77256 ⟨1095005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77256
    ⟨1095005, by decide⟩ (by decide) (![⟨1082322, by decide⟩,⟨1094912, by decide⟩,⟨1094961, by decide⟩,⟨1095004, by decide⟩]) unmarked_context_11_77256_1095005 node_context_11_77256_1095005
  intro a
  fin_cases a
  · exact context_12_309024_1082322
  · exact context_12_309025_1094912
  · exact context_12_309026_1094961
  · exact context_12_309027_1095004

theorem selected_cut_40297 : selected 9 ⟨1095053, by decide⟩
    (prefixPartial 12 309028) = some ⟨12, 2, 0, 1095053, 309028, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_309028_1095053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309028 ⟨1095053, by decide⟩ :=
  accepted_of_selected 12 309028 ⟨1095053, by decide⟩ ⟨12, 2, 0, 1095053, 309028, 3321, 65536⟩
    (by decide) selected_cut_40297

theorem selected_cut_40298 : selected 9 ⟨1095097, by decide⟩
    (prefixPartial 12 309029) = some ⟨12, 2, 0, 1095097, 309029, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_309029_1095097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309029 ⟨1095097, by decide⟩ :=
  accepted_of_selected 12 309029 ⟨1095097, by decide⟩ ⟨12, 2, 0, 1095097, 309029, 3369, 65536⟩
    (by decide) selected_cut_40298

theorem selected_cut_40299 : selected 9 ⟨1095139, by decide⟩
    (prefixPartial 12 309030) = some ⟨12, 2, 0, 1095139, 309030, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_309030_1095139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309030 ⟨1095139, by decide⟩ :=
  accepted_of_selected 12 309030 ⟨1095139, by decide⟩ ⟨12, 2, 0, 1095139, 309030, 3217, 65536⟩
    (by decide) selected_cut_40299

theorem selected_cut_40300 : selected 9 ⟨1095176, by decide⟩
    (prefixPartial 12 309031) = some ⟨12, 2, 0, 1095176, 309031, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_309031_1095176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309031 ⟨1095176, by decide⟩ :=
  accepted_of_selected 12 309031 ⟨1095176, by decide⟩ ⟨12, 2, 0, 1095176, 309031, 3117, 65536⟩
    (by decide) selected_cut_40300

theorem unmarked_context_11_77257_1095177 : frontier 10 ⟨1095177, by decide⟩
    (prefixCache 11 77257) (prefixPartial 11 77257) = false := by
  decide +kernel

theorem node_context_11_77257_1095177 : EJMOriginalGlobalDAGData.nodes 10 ⟨1095177, by decide⟩ =
    .split (coordinate 11) (![⟨1095053, by decide⟩,⟨1095097, by decide⟩,⟨1095139, by decide⟩,⟨1095176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77257_1095177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77257 ⟨1095177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77257
    ⟨1095177, by decide⟩ (by decide) (![⟨1095053, by decide⟩,⟨1095097, by decide⟩,⟨1095139, by decide⟩,⟨1095176, by decide⟩]) unmarked_context_11_77257_1095177 node_context_11_77257_1095177
  intro a
  fin_cases a
  · exact context_12_309028_1095053
  · exact context_12_309029_1095097
  · exact context_12_309030_1095139
  · exact context_12_309031_1095176

theorem selected_cut_40301 : selected 9 ⟨1095236, by decide⟩
    (prefixPartial 12 309032) = some ⟨12, 2, 0, 1095236, 309032, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_309032_1095236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309032 ⟨1095236, by decide⟩ :=
  accepted_of_selected 12 309032 ⟨1095236, by decide⟩ ⟨12, 2, 0, 1095236, 309032, 3633, 65536⟩
    (by decide) selected_cut_40301

theorem selected_cut_40302 : selected 9 ⟨1095286, by decide⟩
    (prefixPartial 12 309033) = some ⟨12, 2, 0, 1095286, 309033, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_309033_1095286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309033 ⟨1095286, by decide⟩ :=
  accepted_of_selected 12 309033 ⟨1095286, by decide⟩ ⟨12, 2, 0, 1095286, 309033, 3497, 65536⟩
    (by decide) selected_cut_40302

theorem selected_cut_40303 : selected 9 ⟨1025950, by decide⟩
    (prefixPartial 12 309034) = some ⟨12, 1, 0, 1025950, 309034, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309034_1025950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309034 ⟨1025950, by decide⟩ :=
  accepted_of_selected 12 309034 ⟨1025950, by decide⟩ ⟨12, 1, 0, 1025950, 309034, 1, 65536⟩
    (by decide) selected_cut_40303

theorem selected_cut_40304 : selected 9 ⟨1095338, by decide⟩
    (prefixPartial 12 309035) = some ⟨12, 2, 0, 1095338, 309035, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_309035_1095338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309035 ⟨1095338, by decide⟩ :=
  accepted_of_selected 12 309035 ⟨1095338, by decide⟩ ⟨12, 2, 0, 1095338, 309035, 3569, 65536⟩
    (by decide) selected_cut_40304

theorem unmarked_context_11_77258_1095339 : frontier 10 ⟨1095339, by decide⟩
    (prefixCache 11 77258) (prefixPartial 11 77258) = false := by
  decide +kernel

theorem node_context_11_77258_1095339 : EJMOriginalGlobalDAGData.nodes 10 ⟨1095339, by decide⟩ =
    .split (coordinate 11) (![⟨1095236, by decide⟩,⟨1095286, by decide⟩,⟨1025950, by decide⟩,⟨1095338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77258_1095339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77258 ⟨1095339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77258
    ⟨1095339, by decide⟩ (by decide) (![⟨1095236, by decide⟩,⟨1095286, by decide⟩,⟨1025950, by decide⟩,⟨1095338, by decide⟩]) unmarked_context_11_77258_1095339 node_context_11_77258_1095339
  intro a
  fin_cases a
  · exact context_12_309032_1095236
  · exact context_12_309033_1095286
  · exact context_12_309034_1025950
  · exact context_12_309035_1095338

theorem selected_cut_40305 : selected 9 ⟨1095404, by decide⟩
    (prefixPartial 12 309036) = some ⟨12, 2, 0, 1095404, 309036, 3433, 65536⟩ := by
  decide +kernel

theorem context_12_309036_1095404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309036 ⟨1095404, by decide⟩ :=
  accepted_of_selected 12 309036 ⟨1095404, by decide⟩ ⟨12, 2, 0, 1095404, 309036, 3433, 65536⟩
    (by decide) selected_cut_40305

theorem selected_cut_40306 : selected 9 ⟨1095449, by decide⟩
    (prefixPartial 12 309037) = some ⟨12, 2, 0, 1095449, 309037, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_309037_1095449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309037 ⟨1095449, by decide⟩ :=
  accepted_of_selected 12 309037 ⟨1095449, by decide⟩ ⟨12, 2, 0, 1095449, 309037, 3145, 65536⟩
    (by decide) selected_cut_40306

theorem selected_cut_40307 : selected 9 ⟨1095494, by decide⟩
    (prefixPartial 12 309038) = some ⟨12, 2, 0, 1095494, 309038, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_309038_1095494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309038 ⟨1095494, by decide⟩ :=
  accepted_of_selected 12 309038 ⟨1095494, by decide⟩ ⟨12, 2, 0, 1095494, 309038, 3241, 65536⟩
    (by decide) selected_cut_40307

theorem selected_cut_40308 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 309039) = some ⟨12, 1, 0, 903806, 309039, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309039_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309039 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 309039 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 309039, 1, 65536⟩
    (by decide) selected_cut_40308

theorem unmarked_context_11_77259_1095495 : frontier 10 ⟨1095495, by decide⟩
    (prefixCache 11 77259) (prefixPartial 11 77259) = false := by
  decide +kernel

theorem node_context_11_77259_1095495 : EJMOriginalGlobalDAGData.nodes 10 ⟨1095495, by decide⟩ =
    .split (coordinate 11) (![⟨1095404, by decide⟩,⟨1095449, by decide⟩,⟨1095494, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77259_1095495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77259 ⟨1095495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77259
    ⟨1095495, by decide⟩ (by decide) (![⟨1095404, by decide⟩,⟨1095449, by decide⟩,⟨1095494, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77259_1095495 node_context_11_77259_1095495
  intro a
  fin_cases a
  · exact context_12_309036_1095404
  · exact context_12_309037_1095449
  · exact context_12_309038_1095494
  · exact context_12_309039_903806

theorem unmarked_context_10_19314_1095496 : frontier 11 ⟨1095496, by decide⟩
    (prefixCache 10 19314) (prefixPartial 10 19314) = false := by
  decide +kernel

theorem node_context_10_19314_1095496 : EJMOriginalGlobalDAGData.nodes 11 ⟨1095496, by decide⟩ =
    .split (coordinate 10) (![⟨1095005, by decide⟩,⟨1095177, by decide⟩,⟨1095339, by decide⟩,⟨1095495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19314_1095496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19314 ⟨1095496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19314
    ⟨1095496, by decide⟩ (by decide) (![⟨1095005, by decide⟩,⟨1095177, by decide⟩,⟨1095339, by decide⟩,⟨1095495, by decide⟩]) unmarked_context_10_19314_1095496 node_context_10_19314_1095496
  intro a
  fin_cases a
  · exact context_11_77256_1095005
  · exact context_11_77257_1095177
  · exact context_11_77258_1095339
  · exact context_11_77259_1095495

theorem selected_cut_40309 : selected 9 ⟨1082322, by decide⟩
    (prefixPartial 12 309040) = some ⟨12, 1, 0, 1082322, 309040, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309040_1082322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309040 ⟨1082322, by decide⟩ :=
  accepted_of_selected 12 309040 ⟨1082322, by decide⟩ ⟨12, 1, 0, 1082322, 309040, 1, 65536⟩
    (by decide) selected_cut_40309

theorem selected_cut_40310 : selected 9 ⟨1095535, by decide⟩
    (prefixPartial 12 309041) = some ⟨12, 2, 0, 1095535, 309041, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_309041_1095535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309041 ⟨1095535, by decide⟩ :=
  accepted_of_selected 12 309041 ⟨1095535, by decide⟩ ⟨12, 2, 0, 1095535, 309041, 2949, 65536⟩
    (by decide) selected_cut_40310

theorem selected_cut_40311 : selected 9 ⟨1095586, by decide⟩
    (prefixPartial 12 309042) = some ⟨12, 2, 0, 1095586, 309042, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_309042_1095586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309042 ⟨1095586, by decide⟩ :=
  accepted_of_selected 12 309042 ⟨1095586, by decide⟩ ⟨12, 2, 0, 1095586, 309042, 3125, 65536⟩
    (by decide) selected_cut_40311

theorem selected_cut_40312 : selected 9 ⟨1095630, by decide⟩
    (prefixPartial 12 309043) = some ⟨12, 2, 0, 1095630, 309043, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_309043_1095630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309043 ⟨1095630, by decide⟩ :=
  accepted_of_selected 12 309043 ⟨1095630, by decide⟩ ⟨12, 2, 0, 1095630, 309043, 2553, 65536⟩
    (by decide) selected_cut_40312

theorem unmarked_context_11_77260_1095631 : frontier 10 ⟨1095631, by decide⟩
    (prefixCache 11 77260) (prefixPartial 11 77260) = false := by
  decide +kernel

theorem node_context_11_77260_1095631 : EJMOriginalGlobalDAGData.nodes 10 ⟨1095631, by decide⟩ =
    .split (coordinate 11) (![⟨1082322, by decide⟩,⟨1095535, by decide⟩,⟨1095586, by decide⟩,⟨1095630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77260_1095631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77260 ⟨1095631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77260
    ⟨1095631, by decide⟩ (by decide) (![⟨1082322, by decide⟩,⟨1095535, by decide⟩,⟨1095586, by decide⟩,⟨1095630, by decide⟩]) unmarked_context_11_77260_1095631 node_context_11_77260_1095631
  intro a
  fin_cases a
  · exact context_12_309040_1082322
  · exact context_12_309041_1095535
  · exact context_12_309042_1095586
  · exact context_12_309043_1095630

theorem selected_cut_40313 : selected 9 ⟨1095672, by decide⟩
    (prefixPartial 12 309044) = some ⟨12, 2, 0, 1095672, 309044, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_309044_1095672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309044 ⟨1095672, by decide⟩ :=
  accepted_of_selected 12 309044 ⟨1095672, by decide⟩ ⟨12, 2, 0, 1095672, 309044, 3037, 65536⟩
    (by decide) selected_cut_40313

theorem selected_cut_40314 : selected 9 ⟨1095715, by decide⟩
    (prefixPartial 12 309045) = some ⟨12, 2, 0, 1095715, 309045, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_309045_1095715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309045 ⟨1095715, by decide⟩ :=
  accepted_of_selected 12 309045 ⟨1095715, by decide⟩ ⟨12, 2, 0, 1095715, 309045, 3097, 65536⟩
    (by decide) selected_cut_40314

theorem selected_cut_40315 : selected 9 ⟨1095764, by decide⟩
    (prefixPartial 12 309046) = some ⟨12, 2, 0, 1095764, 309046, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_309046_1095764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309046 ⟨1095764, by decide⟩ :=
  accepted_of_selected 12 309046 ⟨1095764, by decide⟩ ⟨12, 2, 0, 1095764, 309046, 3061, 65536⟩
    (by decide) selected_cut_40315

theorem selected_cut_40316 : selected 9 ⟨1095803, by decide⟩
    (prefixPartial 12 309047) = some ⟨12, 2, 0, 1095803, 309047, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_309047_1095803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309047 ⟨1095803, by decide⟩ :=
  accepted_of_selected 12 309047 ⟨1095803, by decide⟩ ⟨12, 2, 0, 1095803, 309047, 2661, 65536⟩
    (by decide) selected_cut_40316

theorem unmarked_context_11_77261_1095804 : frontier 10 ⟨1095804, by decide⟩
    (prefixCache 11 77261) (prefixPartial 11 77261) = false := by
  decide +kernel

theorem node_context_11_77261_1095804 : EJMOriginalGlobalDAGData.nodes 10 ⟨1095804, by decide⟩ =
    .split (coordinate 11) (![⟨1095672, by decide⟩,⟨1095715, by decide⟩,⟨1095764, by decide⟩,⟨1095803, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77261_1095804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77261 ⟨1095804, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77261
    ⟨1095804, by decide⟩ (by decide) (![⟨1095672, by decide⟩,⟨1095715, by decide⟩,⟨1095764, by decide⟩,⟨1095803, by decide⟩]) unmarked_context_11_77261_1095804 node_context_11_77261_1095804
  intro a
  fin_cases a
  · exact context_12_309044_1095672
  · exact context_12_309045_1095715
  · exact context_12_309046_1095764
  · exact context_12_309047_1095803

theorem selected_cut_40317 : selected 9 ⟨1095851, by decide⟩
    (prefixPartial 12 309048) = some ⟨12, 2, 0, 1095851, 309048, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_309048_1095851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309048 ⟨1095851, by decide⟩ :=
  accepted_of_selected 12 309048 ⟨1095851, by decide⟩ ⟨12, 2, 0, 1095851, 309048, 2981, 65536⟩
    (by decide) selected_cut_40317

theorem selected_cut_40318 : selected 9 ⟨1095890, by decide⟩
    (prefixPartial 12 309049) = some ⟨12, 2, 0, 1095890, 309049, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_309049_1095890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309049 ⟨1095890, by decide⟩ :=
  accepted_of_selected 12 309049 ⟨1095890, by decide⟩ ⟨12, 2, 0, 1095890, 309049, 2889, 65536⟩
    (by decide) selected_cut_40318

theorem selected_cut_40319 : selected 9 ⟨1095931, by decide⟩
    (prefixPartial 12 309050) = some ⟨12, 2, 0, 1095931, 309050, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_309050_1095931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309050 ⟨1095931, by decide⟩ :=
  accepted_of_selected 12 309050 ⟨1095931, by decide⟩ ⟨12, 2, 0, 1095931, 309050, 2905, 65536⟩
    (by decide) selected_cut_40319

theorem selected_cut_40320 : selected 9 ⟨1095970, by decide⟩
    (prefixPartial 12 309051) = some ⟨12, 2, 0, 1095970, 309051, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_309051_1095970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309051 ⟨1095970, by decide⟩ :=
  accepted_of_selected 12 309051 ⟨1095970, by decide⟩ ⟨12, 2, 0, 1095970, 309051, 2733, 65536⟩
    (by decide) selected_cut_40320

theorem unmarked_context_11_77262_1095971 : frontier 10 ⟨1095971, by decide⟩
    (prefixCache 11 77262) (prefixPartial 11 77262) = false := by
  decide +kernel

theorem node_context_11_77262_1095971 : EJMOriginalGlobalDAGData.nodes 10 ⟨1095971, by decide⟩ =
    .split (coordinate 11) (![⟨1095851, by decide⟩,⟨1095890, by decide⟩,⟨1095931, by decide⟩,⟨1095970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77262_1095971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77262 ⟨1095971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77262
    ⟨1095971, by decide⟩ (by decide) (![⟨1095851, by decide⟩,⟨1095890, by decide⟩,⟨1095931, by decide⟩,⟨1095970, by decide⟩]) unmarked_context_11_77262_1095971 node_context_11_77262_1095971
  intro a
  fin_cases a
  · exact context_12_309048_1095851
  · exact context_12_309049_1095890
  · exact context_12_309050_1095931
  · exact context_12_309051_1095970

theorem selected_cut_40321 : selected 9 ⟨1096025, by decide⟩
    (prefixPartial 12 309052) = some ⟨12, 2, 0, 1096025, 309052, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_309052_1096025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309052 ⟨1096025, by decide⟩ :=
  accepted_of_selected 12 309052 ⟨1096025, by decide⟩ ⟨12, 2, 0, 1096025, 309052, 2877, 65536⟩
    (by decide) selected_cut_40321

theorem selected_cut_40322 : selected 9 ⟨1096070, by decide⟩
    (prefixPartial 12 309053) = some ⟨12, 2, 0, 1096070, 309053, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_309053_1096070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309053 ⟨1096070, by decide⟩ :=
  accepted_of_selected 12 309053 ⟨1096070, by decide⟩ ⟨12, 2, 0, 1096070, 309053, 2713, 65536⟩
    (by decide) selected_cut_40322

theorem selected_cut_40323 : selected 9 ⟨1096115, by decide⟩
    (prefixPartial 12 309054) = some ⟨12, 2, 0, 1096115, 309054, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_309054_1096115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309054 ⟨1096115, by decide⟩ :=
  accepted_of_selected 12 309054 ⟨1096115, by decide⟩ ⟨12, 2, 0, 1096115, 309054, 2773, 65536⟩
    (by decide) selected_cut_40323

theorem selected_cut_40324 : selected 9 ⟨762108, by decide⟩
    (prefixPartial 12 309055) = some ⟨12, 1, 0, 762108, 309055, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309055_762108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309055 ⟨762108, by decide⟩ :=
  accepted_of_selected 12 309055 ⟨762108, by decide⟩ ⟨12, 1, 0, 762108, 309055, 1, 65536⟩
    (by decide) selected_cut_40324

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
