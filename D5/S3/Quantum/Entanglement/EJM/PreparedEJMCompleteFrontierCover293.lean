/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover292
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_28132 : selected 10 ⟨710219, by decide⟩
    (prefixPartial 11 23023) = some ⟨11, 2, 0, 710219, 23023, 2633, 262144⟩ := by
  decide +kernel

theorem context_11_23023_710219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23023 ⟨710219, by decide⟩ :=
  accepted_of_selected 11 23023 ⟨710219, by decide⟩ ⟨11, 2, 0, 710219, 23023, 2633, 262144⟩
    (by decide) selected_cut_28132

theorem unmarked_context_10_5755_710220 : frontier 11 ⟨710220, by decide⟩
    (prefixCache 10 5755) (prefixPartial 10 5755) = false := by
  decide +kernel

theorem node_context_10_5755_710220 : EJMOriginalGlobalDAGData.nodes 11 ⟨710220, by decide⟩ =
    .split (coordinate 10) (![⟨710081, by decide⟩,⟨710127, by decide⟩,⟨710185, by decide⟩,⟨710219, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5755_710220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5755 ⟨710220, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5755
    ⟨710220, by decide⟩ (by decide) (![⟨710081, by decide⟩,⟨710127, by decide⟩,⟨710185, by decide⟩,⟨710219, by decide⟩]) unmarked_context_10_5755_710220 node_context_10_5755_710220
  intro a
  fin_cases a
  · exact context_11_23020_710081
  · exact context_11_23021_710127
  · exact context_11_23022_710185
  · exact context_11_23023_710219

theorem unmarked_context_9_1438_710221 : frontier 12 ⟨710221, by decide⟩
    (prefixCache 9 1438) (prefixPartial 9 1438) = false := by
  decide +kernel

theorem node_context_9_1438_710221 : EJMOriginalGlobalDAGData.nodes 12 ⟨710221, by decide⟩ =
    .split (coordinate 9) (![⟨709394, by decide⟩,⟨709778, by decide⟩,⟨710024, by decide⟩,⟨710220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1438_710221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1438 ⟨710221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1438
    ⟨710221, by decide⟩ (by decide) (![⟨709394, by decide⟩,⟨709778, by decide⟩,⟨710024, by decide⟩,⟨710220, by decide⟩]) unmarked_context_9_1438_710221 node_context_9_1438_710221
  intro a
  fin_cases a
  · exact context_10_5752_709394
  · exact context_10_5753_709778
  · exact context_10_5754_710024
  · exact context_10_5755_710220

theorem selected_cut_28133 : selected 10 ⟨710247, by decide⟩
    (prefixPartial 11 23024) = some ⟨11, 2, 0, 710247, 23024, 2013, 262144⟩ := by
  decide +kernel

theorem context_11_23024_710247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23024 ⟨710247, by decide⟩ :=
  accepted_of_selected 11 23024 ⟨710247, by decide⟩ ⟨11, 2, 0, 710247, 23024, 2013, 262144⟩
    (by decide) selected_cut_28133

theorem selected_cut_28134 : selected 10 ⟨710271, by decide⟩
    (prefixPartial 11 23025) = some ⟨11, 2, 0, 710271, 23025, 2185, 262144⟩ := by
  decide +kernel

theorem context_11_23025_710271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23025 ⟨710271, by decide⟩ :=
  accepted_of_selected 11 23025 ⟨710271, by decide⟩ ⟨11, 2, 0, 710271, 23025, 2185, 262144⟩
    (by decide) selected_cut_28134

theorem selected_cut_28135 : selected 10 ⟨710287, by decide⟩
    (prefixPartial 11 23026) = some ⟨11, 2, 0, 710287, 23026, 2045, 262144⟩ := by
  decide +kernel

theorem context_11_23026_710287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23026 ⟨710287, by decide⟩ :=
  accepted_of_selected 11 23026 ⟨710287, by decide⟩ ⟨11, 2, 0, 710287, 23026, 2045, 262144⟩
    (by decide) selected_cut_28135

theorem selected_cut_28136 : selected 10 ⟨710306, by decide⟩
    (prefixPartial 11 23027) = some ⟨11, 2, 0, 710306, 23027, 1513, 262144⟩ := by
  decide +kernel

theorem context_11_23027_710306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23027 ⟨710306, by decide⟩ :=
  accepted_of_selected 11 23027 ⟨710306, by decide⟩ ⟨11, 2, 0, 710306, 23027, 1513, 262144⟩
    (by decide) selected_cut_28136

theorem unmarked_context_10_5756_710307 : frontier 11 ⟨710307, by decide⟩
    (prefixCache 10 5756) (prefixPartial 10 5756) = false := by
  decide +kernel

theorem node_context_10_5756_710307 : EJMOriginalGlobalDAGData.nodes 11 ⟨710307, by decide⟩ =
    .split (coordinate 10) (![⟨710247, by decide⟩,⟨710271, by decide⟩,⟨710287, by decide⟩,⟨710306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5756_710307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5756 ⟨710307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5756
    ⟨710307, by decide⟩ (by decide) (![⟨710247, by decide⟩,⟨710271, by decide⟩,⟨710287, by decide⟩,⟨710306, by decide⟩]) unmarked_context_10_5756_710307 node_context_10_5756_710307
  intro a
  fin_cases a
  · exact context_11_23024_710247
  · exact context_11_23025_710271
  · exact context_11_23026_710287
  · exact context_11_23027_710306

theorem selected_cut_28137 : selected 10 ⟨710330, by decide⟩
    (prefixPartial 11 23028) = some ⟨11, 2, 0, 710330, 23028, 1945, 262144⟩ := by
  decide +kernel

theorem context_11_23028_710330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23028 ⟨710330, by decide⟩ :=
  accepted_of_selected 11 23028 ⟨710330, by decide⟩ ⟨11, 2, 0, 710330, 23028, 1945, 262144⟩
    (by decide) selected_cut_28137

theorem selected_cut_28138 : selected 10 ⟨710356, by decide⟩
    (prefixPartial 11 23029) = some ⟨11, 2, 0, 710356, 23029, 1445, 262144⟩ := by
  decide +kernel

theorem context_11_23029_710356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23029 ⟨710356, by decide⟩ :=
  accepted_of_selected 11 23029 ⟨710356, by decide⟩ ⟨11, 2, 0, 710356, 23029, 1445, 262144⟩
    (by decide) selected_cut_28138

theorem selected_cut_28139 : selected 10 ⟨710377, by decide⟩
    (prefixPartial 11 23030) = some ⟨11, 2, 0, 710377, 23030, 1881, 262144⟩ := by
  decide +kernel

theorem context_11_23030_710377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23030 ⟨710377, by decide⟩ :=
  accepted_of_selected 11 23030 ⟨710377, by decide⟩ ⟨11, 2, 0, 710377, 23030, 1881, 262144⟩
    (by decide) selected_cut_28139

theorem selected_cut_28140 : selected 10 ⟨710398, by decide⟩
    (prefixPartial 11 23031) = some ⟨11, 2, 0, 710398, 23031, 1277, 262144⟩ := by
  decide +kernel

theorem context_11_23031_710398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23031 ⟨710398, by decide⟩ :=
  accepted_of_selected 11 23031 ⟨710398, by decide⟩ ⟨11, 2, 0, 710398, 23031, 1277, 262144⟩
    (by decide) selected_cut_28140

theorem unmarked_context_10_5757_710399 : frontier 11 ⟨710399, by decide⟩
    (prefixCache 10 5757) (prefixPartial 10 5757) = false := by
  decide +kernel

theorem node_context_10_5757_710399 : EJMOriginalGlobalDAGData.nodes 11 ⟨710399, by decide⟩ =
    .split (coordinate 10) (![⟨710330, by decide⟩,⟨710356, by decide⟩,⟨710377, by decide⟩,⟨710398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5757_710399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5757 ⟨710399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5757
    ⟨710399, by decide⟩ (by decide) (![⟨710330, by decide⟩,⟨710356, by decide⟩,⟨710377, by decide⟩,⟨710398, by decide⟩]) unmarked_context_10_5757_710399 node_context_10_5757_710399
  intro a
  fin_cases a
  · exact context_11_23028_710330
  · exact context_11_23029_710356
  · exact context_11_23030_710377
  · exact context_11_23031_710398

theorem selected_cut_28141 : selected 11 ⟨710459, by decide⟩
    (prefixPartial 10 5758) = some ⟨10, 2, 0, 710459, 5758, 3993, 1048576⟩ := by
  decide +kernel

theorem context_10_5758_710459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5758 ⟨710459, by decide⟩ :=
  accepted_of_selected 10 5758 ⟨710459, by decide⟩ ⟨10, 2, 0, 710459, 5758, 3993, 1048576⟩
    (by decide) selected_cut_28141

theorem selected_cut_28142 : selected 11 ⟨710490, by decide⟩
    (prefixPartial 10 5759) = some ⟨10, 2, 0, 710490, 5759, 1409, 1048576⟩ := by
  decide +kernel

theorem context_10_5759_710490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5759 ⟨710490, by decide⟩ :=
  accepted_of_selected 10 5759 ⟨710490, by decide⟩ ⟨10, 2, 0, 710490, 5759, 1409, 1048576⟩
    (by decide) selected_cut_28142

theorem unmarked_context_9_1439_710491 : frontier 12 ⟨710491, by decide⟩
    (prefixCache 9 1439) (prefixPartial 9 1439) = false := by
  decide +kernel

theorem node_context_9_1439_710491 : EJMOriginalGlobalDAGData.nodes 12 ⟨710491, by decide⟩ =
    .split (coordinate 9) (![⟨710307, by decide⟩,⟨710399, by decide⟩,⟨710459, by decide⟩,⟨710490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1439_710491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1439 ⟨710491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1439
    ⟨710491, by decide⟩ (by decide) (![⟨710307, by decide⟩,⟨710399, by decide⟩,⟨710459, by decide⟩,⟨710490, by decide⟩]) unmarked_context_9_1439_710491 node_context_9_1439_710491
  intro a
  fin_cases a
  · exact context_10_5756_710307
  · exact context_10_5757_710399
  · exact context_10_5758_710459
  · exact context_10_5759_710490

theorem unmarked_context_8_359_710492 : frontier 13 ⟨710492, by decide⟩
    (prefixCache 8 359) (prefixPartial 8 359) = false := by
  decide +kernel

theorem node_context_8_359_710492 : EJMOriginalGlobalDAGData.nodes 13 ⟨710492, by decide⟩ =
    .split (coordinate 8) (![⟨706395, by decide⟩,⟨708970, by decide⟩,⟨710221, by decide⟩,⟨710491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_359_710492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 359 ⟨710492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 359
    ⟨710492, by decide⟩ (by decide) (![⟨706395, by decide⟩,⟨708970, by decide⟩,⟨710221, by decide⟩,⟨710491, by decide⟩]) unmarked_context_8_359_710492 node_context_8_359_710492
  intro a
  fin_cases a
  · exact context_9_1436_706395
  · exact context_9_1437_708970
  · exact context_9_1438_710221
  · exact context_9_1439_710491

theorem unmarked_context_7_89_710493 : frontier 14 ⟨710493, by decide⟩
    (prefixCache 7 89) (prefixPartial 7 89) = false := by
  decide +kernel

theorem node_context_7_89_710493 : EJMOriginalGlobalDAGData.nodes 14 ⟨710493, by decide⟩ =
    .split (coordinate 7) (![⟨686316, by decide⟩,⟨693672, by decide⟩,⟨701739, by decide⟩,⟨710492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_89_710493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 89 ⟨710493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 89
    ⟨710493, by decide⟩ (by decide) (![⟨686316, by decide⟩,⟨693672, by decide⟩,⟨701739, by decide⟩,⟨710492, by decide⟩]) unmarked_context_7_89_710493 node_context_7_89_710493
  intro a
  fin_cases a
  · exact context_8_356_686316
  · exact context_8_357_693672
  · exact context_8_358_701739
  · exact context_8_359_710492

theorem selected_cut_28143 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 23040) = some ⟨11, 1, 0, 434745, 23040, 1, 262144⟩ := by
  decide +kernel

theorem context_11_23040_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23040 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 23040 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 23040, 1, 262144⟩
    (by decide) selected_cut_28143

theorem selected_cut_28144 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 92164) = some ⟨12, 1, 0, 4595, 92164, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92164_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92164 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 92164 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 92164, 1, 65536⟩
    (by decide) selected_cut_28144

theorem selected_cut_28145 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 92165) = some ⟨12, 1, 0, 34034, 92165, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92165_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92165 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 92165 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 92165, 1, 65536⟩
    (by decide) selected_cut_28145

theorem selected_cut_28146 : selected 8 ⟨710580, by decide⟩
    (prefixPartial 13 368664) = some ⟨13, 2, 0, 710580, 368664, 2925, 16384⟩ := by
  decide +kernel

theorem context_13_368664_710580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368664 ⟨710580, by decide⟩ :=
  accepted_of_selected 13 368664 ⟨710580, by decide⟩ ⟨13, 2, 0, 710580, 368664, 2925, 16384⟩
    (by decide) selected_cut_28146

theorem selected_cut_28147 : selected 8 ⟨710634, by decide⟩
    (prefixPartial 13 368665) = some ⟨13, 2, 0, 710634, 368665, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_368665_710634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368665 ⟨710634, by decide⟩ :=
  accepted_of_selected 13 368665 ⟨710634, by decide⟩ ⟨13, 2, 0, 710634, 368665, 1597, 16384⟩
    (by decide) selected_cut_28147

theorem selected_cut_28148 : selected 8 ⟨710646, by decide⟩
    (prefixPartial 13 368666) = some ⟨13, 2, 0, 710646, 368666, 725, 16384⟩ := by
  decide +kernel

theorem context_13_368666_710646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368666 ⟨710646, by decide⟩ :=
  accepted_of_selected 13 368666 ⟨710646, by decide⟩ ⟨13, 2, 0, 710646, 368666, 725, 16384⟩
    (by decide) selected_cut_28148

theorem selected_cut_28149 : selected 8 ⟨710648, by decide⟩
    (prefixPartial 13 368667) = some ⟨13, 2, 0, 710648, 368667, 145, 16384⟩ := by
  decide +kernel

theorem context_13_368667_710648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368667 ⟨710648, by decide⟩ :=
  accepted_of_selected 13 368667 ⟨710648, by decide⟩ ⟨13, 2, 0, 710648, 368667, 145, 16384⟩
    (by decide) selected_cut_28149

theorem unmarked_context_12_92166_710649 : frontier 9 ⟨710649, by decide⟩
    (prefixCache 12 92166) (prefixPartial 12 92166) = false := by
  decide +kernel

theorem node_context_12_92166_710649 : EJMOriginalGlobalDAGData.nodes 9 ⟨710649, by decide⟩ =
    .split (coordinate 12) (![⟨710580, by decide⟩,⟨710634, by decide⟩,⟨710646, by decide⟩,⟨710648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92166_710649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92166 ⟨710649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92166
    ⟨710649, by decide⟩ (by decide) (![⟨710580, by decide⟩,⟨710634, by decide⟩,⟨710646, by decide⟩,⟨710648, by decide⟩]) unmarked_context_12_92166_710649 node_context_12_92166_710649
  intro a
  fin_cases a
  · exact context_13_368664_710580
  · exact context_13_368665_710634
  · exact context_13_368666_710646
  · exact context_13_368667_710648

theorem selected_cut_28150 : selected 8 ⟨710725, by decide⟩
    (prefixPartial 13 368668) = some ⟨13, 2, 0, 710725, 368668, 3269, 16384⟩ := by
  decide +kernel

theorem context_13_368668_710725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368668 ⟨710725, by decide⟩ :=
  accepted_of_selected 13 368668 ⟨710725, by decide⟩ ⟨13, 2, 0, 710725, 368668, 3269, 16384⟩
    (by decide) selected_cut_28150

theorem selected_cut_28151 : selected 8 ⟨710796, by decide⟩
    (prefixPartial 13 368669) = some ⟨13, 2, 0, 710796, 368669, 3097, 16384⟩ := by
  decide +kernel

theorem context_13_368669_710796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368669 ⟨710796, by decide⟩ :=
  accepted_of_selected 13 368669 ⟨710796, by decide⟩ ⟨13, 2, 0, 710796, 368669, 3097, 16384⟩
    (by decide) selected_cut_28151

theorem selected_cut_28152 : selected 8 ⟨710828, by decide⟩
    (prefixPartial 13 368670) = some ⟨13, 2, 0, 710828, 368670, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_368670_710828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368670 ⟨710828, by decide⟩ :=
  accepted_of_selected 13 368670 ⟨710828, by decide⟩ ⟨13, 2, 0, 710828, 368670, 2365, 16384⟩
    (by decide) selected_cut_28152

theorem selected_cut_28153 : selected 8 ⟨710845, by decide⟩
    (prefixPartial 13 368671) = some ⟨13, 2, 0, 710845, 368671, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_368671_710845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368671 ⟨710845, by decide⟩ :=
  accepted_of_selected 13 368671 ⟨710845, by decide⟩ ⟨13, 2, 0, 710845, 368671, 1197, 16384⟩
    (by decide) selected_cut_28153

theorem unmarked_context_12_92167_710846 : frontier 9 ⟨710846, by decide⟩
    (prefixCache 12 92167) (prefixPartial 12 92167) = false := by
  decide +kernel

theorem node_context_12_92167_710846 : EJMOriginalGlobalDAGData.nodes 9 ⟨710846, by decide⟩ =
    .split (coordinate 12) (![⟨710725, by decide⟩,⟨710796, by decide⟩,⟨710828, by decide⟩,⟨710845, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92167_710846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92167 ⟨710846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92167
    ⟨710846, by decide⟩ (by decide) (![⟨710725, by decide⟩,⟨710796, by decide⟩,⟨710828, by decide⟩,⟨710845, by decide⟩]) unmarked_context_12_92167_710846 node_context_12_92167_710846
  intro a
  fin_cases a
  · exact context_13_368668_710725
  · exact context_13_368669_710796
  · exact context_13_368670_710828
  · exact context_13_368671_710845

theorem unmarked_context_11_23041_710847 : frontier 10 ⟨710847, by decide⟩
    (prefixCache 11 23041) (prefixPartial 11 23041) = false := by
  decide +kernel

theorem node_context_11_23041_710847 : EJMOriginalGlobalDAGData.nodes 10 ⟨710847, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨34034, by decide⟩,⟨710649, by decide⟩,⟨710846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23041_710847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23041 ⟨710847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23041
    ⟨710847, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨34034, by decide⟩,⟨710649, by decide⟩,⟨710846, by decide⟩]) unmarked_context_11_23041_710847 node_context_11_23041_710847
  intro a
  fin_cases a
  · exact context_12_92164_4595
  · exact context_12_92165_34034
  · exact context_12_92166_710649
  · exact context_12_92167_710846

theorem selected_cut_28154 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 92168) = some ⟨12, 1, 0, 4595, 92168, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92168_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92168 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 92168 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 92168, 1, 65536⟩
    (by decide) selected_cut_28154

theorem selected_cut_28155 : selected 8 ⟨710935, by decide⟩
    (prefixPartial 13 368676) = some ⟨13, 2, 0, 710935, 368676, 3185, 16384⟩ := by
  decide +kernel

theorem context_13_368676_710935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368676 ⟨710935, by decide⟩ :=
  accepted_of_selected 13 368676 ⟨710935, by decide⟩ ⟨13, 2, 0, 710935, 368676, 3185, 16384⟩
    (by decide) selected_cut_28155

theorem selected_cut_28156 : selected 8 ⟨710973, by decide⟩
    (prefixPartial 13 368677) = some ⟨13, 2, 0, 710973, 368677, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_368677_710973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368677 ⟨710973, by decide⟩ :=
  accepted_of_selected 13 368677 ⟨710973, by decide⟩ ⟨13, 2, 0, 710973, 368677, 1493, 16384⟩
    (by decide) selected_cut_28156

theorem selected_cut_28157 : selected 8 ⟨710987, by decide⟩
    (prefixPartial 13 368678) = some ⟨13, 2, 0, 710987, 368678, 649, 16384⟩ := by
  decide +kernel

theorem context_13_368678_710987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368678 ⟨710987, by decide⟩ :=
  accepted_of_selected 13 368678 ⟨710987, by decide⟩ ⟨13, 2, 0, 710987, 368678, 649, 16384⟩
    (by decide) selected_cut_28157

theorem selected_cut_28158 : selected 8 ⟨710989, by decide⟩
    (prefixPartial 13 368679) = some ⟨13, 2, 0, 710989, 368679, 141, 16384⟩ := by
  decide +kernel

theorem context_13_368679_710989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368679 ⟨710989, by decide⟩ :=
  accepted_of_selected 13 368679 ⟨710989, by decide⟩ ⟨13, 2, 0, 710989, 368679, 141, 16384⟩
    (by decide) selected_cut_28158

theorem unmarked_context_12_92169_710990 : frontier 9 ⟨710990, by decide⟩
    (prefixCache 12 92169) (prefixPartial 12 92169) = false := by
  decide +kernel

theorem node_context_12_92169_710990 : EJMOriginalGlobalDAGData.nodes 9 ⟨710990, by decide⟩ =
    .split (coordinate 12) (![⟨710935, by decide⟩,⟨710973, by decide⟩,⟨710987, by decide⟩,⟨710989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92169_710990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92169 ⟨710990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92169
    ⟨710990, by decide⟩ (by decide) (![⟨710935, by decide⟩,⟨710973, by decide⟩,⟨710987, by decide⟩,⟨710989, by decide⟩]) unmarked_context_12_92169_710990 node_context_12_92169_710990
  intro a
  fin_cases a
  · exact context_13_368676_710935
  · exact context_13_368677_710973
  · exact context_13_368678_710987
  · exact context_13_368679_710989

theorem selected_cut_28159 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 92170) = some ⟨12, 1, 0, 4595, 92170, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92170_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92170 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 92170 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 92170, 1, 65536⟩
    (by decide) selected_cut_28159

theorem selected_cut_28160 : selected 8 ⟨711053, by decide⟩
    (prefixPartial 13 368684) = some ⟨13, 2, 0, 711053, 368684, 3097, 16384⟩ := by
  decide +kernel

theorem context_13_368684_711053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368684 ⟨711053, by decide⟩ :=
  accepted_of_selected 13 368684 ⟨711053, by decide⟩ ⟨13, 2, 0, 711053, 368684, 3097, 16384⟩
    (by decide) selected_cut_28160

theorem selected_cut_28161 : selected 8 ⟨711125, by decide⟩
    (prefixPartial 13 368685) = some ⟨13, 2, 0, 711125, 368685, 3181, 16384⟩ := by
  decide +kernel

theorem context_13_368685_711125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368685 ⟨711125, by decide⟩ :=
  accepted_of_selected 13 368685 ⟨711125, by decide⟩ ⟨13, 2, 0, 711125, 368685, 3181, 16384⟩
    (by decide) selected_cut_28161

theorem selected_cut_28162 : selected 8 ⟨711147, by decide⟩
    (prefixPartial 13 368686) = some ⟨13, 2, 0, 711147, 368686, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_368686_711147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368686 ⟨711147, by decide⟩ :=
  accepted_of_selected 13 368686 ⟨711147, by decide⟩ ⟨13, 2, 0, 711147, 368686, 2069, 16384⟩
    (by decide) selected_cut_28162

theorem selected_cut_28163 : selected 8 ⟨711158, by decide⟩
    (prefixPartial 13 368687) = some ⟨13, 2, 0, 711158, 368687, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_368687_711158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368687 ⟨711158, by decide⟩ :=
  accepted_of_selected 13 368687 ⟨711158, by decide⟩ ⟨13, 2, 0, 711158, 368687, 1185, 16384⟩
    (by decide) selected_cut_28163

theorem unmarked_context_12_92171_711159 : frontier 9 ⟨711159, by decide⟩
    (prefixCache 12 92171) (prefixPartial 12 92171) = false := by
  decide +kernel

theorem node_context_12_92171_711159 : EJMOriginalGlobalDAGData.nodes 9 ⟨711159, by decide⟩ =
    .split (coordinate 12) (![⟨711053, by decide⟩,⟨711125, by decide⟩,⟨711147, by decide⟩,⟨711158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92171_711159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92171 ⟨711159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92171
    ⟨711159, by decide⟩ (by decide) (![⟨711053, by decide⟩,⟨711125, by decide⟩,⟨711147, by decide⟩,⟨711158, by decide⟩]) unmarked_context_12_92171_711159 node_context_12_92171_711159
  intro a
  fin_cases a
  · exact context_13_368684_711053
  · exact context_13_368685_711125
  · exact context_13_368686_711147
  · exact context_13_368687_711158

theorem unmarked_context_11_23042_711160 : frontier 10 ⟨711160, by decide⟩
    (prefixCache 11 23042) (prefixPartial 11 23042) = false := by
  decide +kernel

theorem node_context_11_23042_711160 : EJMOriginalGlobalDAGData.nodes 10 ⟨711160, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨710990, by decide⟩,⟨4595, by decide⟩,⟨711159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23042_711160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23042 ⟨711160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23042
    ⟨711160, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨710990, by decide⟩,⟨4595, by decide⟩,⟨711159, by decide⟩]) unmarked_context_11_23042_711160 node_context_11_23042_711160
  intro a
  fin_cases a
  · exact context_12_92168_4595
  · exact context_12_92169_710990
  · exact context_12_92170_4595
  · exact context_12_92171_711159

theorem selected_cut_28164 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 92172) = some ⟨12, 1, 0, 4595, 92172, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92172_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92172 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 92172 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 92172, 1, 65536⟩
    (by decide) selected_cut_28164

theorem selected_cut_28165 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 92173) = some ⟨12, 1, 0, 4595, 92173, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92173_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92173 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 92173 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 92173, 1, 65536⟩
    (by decide) selected_cut_28165

theorem selected_cut_28166 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 92174) = some ⟨12, 1, 0, 4595, 92174, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92174_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92174 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 92174 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 92174, 1, 65536⟩
    (by decide) selected_cut_28166

theorem selected_cut_28167 : selected 8 ⟨711244, by decide⟩
    (prefixPartial 13 368700) = some ⟨13, 2, 0, 711244, 368700, 2717, 16384⟩ := by
  decide +kernel

theorem context_13_368700_711244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368700 ⟨711244, by decide⟩ :=
  accepted_of_selected 13 368700 ⟨711244, by decide⟩ ⟨13, 2, 0, 711244, 368700, 2717, 16384⟩
    (by decide) selected_cut_28167

theorem selected_cut_28168 : selected 8 ⟨711306, by decide⟩
    (prefixPartial 13 368701) = some ⟨13, 2, 0, 711306, 368701, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_368701_711306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368701 ⟨711306, by decide⟩ :=
  accepted_of_selected 13 368701 ⟨711306, by decide⟩ ⟨13, 2, 0, 711306, 368701, 1917, 16384⟩
    (by decide) selected_cut_28168

theorem selected_cut_28169 : selected 8 ⟨711319, by decide⟩
    (prefixPartial 13 368702) = some ⟨13, 2, 0, 711319, 368702, 721, 16384⟩ := by
  decide +kernel

theorem context_13_368702_711319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368702 ⟨711319, by decide⟩ :=
  accepted_of_selected 13 368702 ⟨711319, by decide⟩ ⟨13, 2, 0, 711319, 368702, 721, 16384⟩
    (by decide) selected_cut_28169

theorem selected_cut_28170 : selected 8 ⟨711321, by decide⟩
    (prefixPartial 13 368703) = some ⟨13, 2, 0, 711321, 368703, 149, 16384⟩ := by
  decide +kernel

theorem context_13_368703_711321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368703 ⟨711321, by decide⟩ :=
  accepted_of_selected 13 368703 ⟨711321, by decide⟩ ⟨13, 2, 0, 711321, 368703, 149, 16384⟩
    (by decide) selected_cut_28170

theorem unmarked_context_12_92175_711322 : frontier 9 ⟨711322, by decide⟩
    (prefixCache 12 92175) (prefixPartial 12 92175) = false := by
  decide +kernel

theorem node_context_12_92175_711322 : EJMOriginalGlobalDAGData.nodes 9 ⟨711322, by decide⟩ =
    .split (coordinate 12) (![⟨711244, by decide⟩,⟨711306, by decide⟩,⟨711319, by decide⟩,⟨711321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92175_711322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92175 ⟨711322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92175
    ⟨711322, by decide⟩ (by decide) (![⟨711244, by decide⟩,⟨711306, by decide⟩,⟨711319, by decide⟩,⟨711321, by decide⟩]) unmarked_context_12_92175_711322 node_context_12_92175_711322
  intro a
  fin_cases a
  · exact context_13_368700_711244
  · exact context_13_368701_711306
  · exact context_13_368702_711319
  · exact context_13_368703_711321

theorem unmarked_context_11_23043_711323 : frontier 10 ⟨711323, by decide⟩
    (prefixCache 11 23043) (prefixPartial 11 23043) = false := by
  decide +kernel

theorem node_context_11_23043_711323 : EJMOriginalGlobalDAGData.nodes 10 ⟨711323, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨4595, by decide⟩,⟨4595, by decide⟩,⟨711322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23043_711323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23043 ⟨711323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23043
    ⟨711323, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨4595, by decide⟩,⟨4595, by decide⟩,⟨711322, by decide⟩]) unmarked_context_11_23043_711323 node_context_11_23043_711323
  intro a
  fin_cases a
  · exact context_12_92172_4595
  · exact context_12_92173_4595
  · exact context_12_92174_4595
  · exact context_12_92175_711322

theorem unmarked_context_10_5760_711324 : frontier 11 ⟨711324, by decide⟩
    (prefixCache 10 5760) (prefixPartial 10 5760) = false := by
  decide +kernel

theorem node_context_10_5760_711324 : EJMOriginalGlobalDAGData.nodes 11 ⟨711324, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨710847, by decide⟩,⟨711160, by decide⟩,⟨711323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5760_711324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5760 ⟨711324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5760
    ⟨711324, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨710847, by decide⟩,⟨711160, by decide⟩,⟨711323, by decide⟩]) unmarked_context_10_5760_711324 node_context_10_5760_711324
  intro a
  fin_cases a
  · exact context_11_23040_434745
  · exact context_11_23041_710847
  · exact context_11_23042_711160
  · exact context_11_23043_711323

theorem selected_cut_28171 : selected 9 ⟨641337, by decide⟩
    (prefixPartial 12 92176) = some ⟨12, 1, 0, 641337, 92176, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92176_641337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92176 ⟨641337, by decide⟩ :=
  accepted_of_selected 12 92176 ⟨641337, by decide⟩ ⟨12, 1, 0, 641337, 92176, 1, 65536⟩
    (by decide) selected_cut_28171

theorem selected_cut_28172 : selected 8 ⟨711349, by decide⟩
    (prefixPartial 13 368708) = some ⟨13, 2, 0, 711349, 368708, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_368708_711349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368708 ⟨711349, by decide⟩ :=
  accepted_of_selected 13 368708 ⟨711349, by decide⟩ ⟨13, 2, 0, 711349, 368708, 1561, 16384⟩
    (by decide) selected_cut_28172

theorem selected_cut_28173 : selected 8 ⟨711371, by decide⟩
    (prefixPartial 13 368709) = some ⟨13, 2, 0, 711371, 368709, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_368709_711371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368709 ⟨711371, by decide⟩ :=
  accepted_of_selected 13 368709 ⟨711371, by decide⟩ ⟨13, 2, 0, 711371, 368709, 1321, 16384⟩
    (by decide) selected_cut_28173

theorem selected_cut_28174 : selected 8 ⟨711389, by decide⟩
    (prefixPartial 13 368710) = some ⟨13, 2, 0, 711389, 368710, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_368710_711389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368710 ⟨711389, by decide⟩ :=
  accepted_of_selected 13 368710 ⟨711389, by decide⟩ ⟨13, 2, 0, 711389, 368710, 1241, 16384⟩
    (by decide) selected_cut_28174

theorem selected_cut_28175 : selected 8 ⟨711396, by decide⟩
    (prefixPartial 13 368711) = some ⟨13, 2, 0, 711396, 368711, 825, 16384⟩ := by
  decide +kernel

theorem context_13_368711_711396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368711 ⟨711396, by decide⟩ :=
  accepted_of_selected 13 368711 ⟨711396, by decide⟩ ⟨13, 2, 0, 711396, 368711, 825, 16384⟩
    (by decide) selected_cut_28175

theorem unmarked_context_12_92177_711397 : frontier 9 ⟨711397, by decide⟩
    (prefixCache 12 92177) (prefixPartial 12 92177) = false := by
  decide +kernel

theorem node_context_12_92177_711397 : EJMOriginalGlobalDAGData.nodes 9 ⟨711397, by decide⟩ =
    .split (coordinate 12) (![⟨711349, by decide⟩,⟨711371, by decide⟩,⟨711389, by decide⟩,⟨711396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92177_711397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92177 ⟨711397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92177
    ⟨711397, by decide⟩ (by decide) (![⟨711349, by decide⟩,⟨711371, by decide⟩,⟨711389, by decide⟩,⟨711396, by decide⟩]) unmarked_context_12_92177_711397 node_context_12_92177_711397
  intro a
  fin_cases a
  · exact context_13_368708_711349
  · exact context_13_368709_711371
  · exact context_13_368710_711389
  · exact context_13_368711_711396

theorem selected_cut_28176 : selected 8 ⟨711420, by decide⟩
    (prefixPartial 13 368712) = some ⟨13, 2, 0, 711420, 368712, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_368712_711420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368712 ⟨711420, by decide⟩ :=
  accepted_of_selected 13 368712 ⟨711420, by decide⟩ ⟨13, 2, 0, 711420, 368712, 1565, 16384⟩
    (by decide) selected_cut_28176

theorem selected_cut_28177 : selected 8 ⟨711443, by decide⟩
    (prefixPartial 13 368713) = some ⟨13, 2, 0, 711443, 368713, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_368713_711443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368713 ⟨711443, by decide⟩ :=
  accepted_of_selected 13 368713 ⟨711443, by decide⟩ ⟨13, 2, 0, 711443, 368713, 1345, 16384⟩
    (by decide) selected_cut_28177

theorem selected_cut_28178 : selected 8 ⟨711456, by decide⟩
    (prefixPartial 13 368714) = some ⟨13, 2, 0, 711456, 368714, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_368714_711456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368714 ⟨711456, by decide⟩ :=
  accepted_of_selected 13 368714 ⟨711456, by decide⟩ ⟨13, 2, 0, 711456, 368714, 1149, 16384⟩
    (by decide) selected_cut_28178

theorem selected_cut_28179 : selected 8 ⟨711463, by decide⟩
    (prefixPartial 13 368715) = some ⟨13, 2, 0, 711463, 368715, 853, 16384⟩ := by
  decide +kernel

theorem context_13_368715_711463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368715 ⟨711463, by decide⟩ :=
  accepted_of_selected 13 368715 ⟨711463, by decide⟩ ⟨13, 2, 0, 711463, 368715, 853, 16384⟩
    (by decide) selected_cut_28179

theorem unmarked_context_12_92178_711464 : frontier 9 ⟨711464, by decide⟩
    (prefixCache 12 92178) (prefixPartial 12 92178) = false := by
  decide +kernel

theorem node_context_12_92178_711464 : EJMOriginalGlobalDAGData.nodes 9 ⟨711464, by decide⟩ =
    .split (coordinate 12) (![⟨711420, by decide⟩,⟨711443, by decide⟩,⟨711456, by decide⟩,⟨711463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92178_711464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92178 ⟨711464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92178
    ⟨711464, by decide⟩ (by decide) (![⟨711420, by decide⟩,⟨711443, by decide⟩,⟨711456, by decide⟩,⟨711463, by decide⟩]) unmarked_context_12_92178_711464 node_context_12_92178_711464
  intro a
  fin_cases a
  · exact context_13_368712_711420
  · exact context_13_368713_711443
  · exact context_13_368714_711456
  · exact context_13_368715_711463

theorem selected_cut_28180 : selected 8 ⟨711490, by decide⟩
    (prefixPartial 13 368716) = some ⟨13, 2, 0, 711490, 368716, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_368716_711490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368716 ⟨711490, by decide⟩ :=
  accepted_of_selected 13 368716 ⟨711490, by decide⟩ ⟨13, 2, 0, 711490, 368716, 1605, 16384⟩
    (by decide) selected_cut_28180

theorem selected_cut_28181 : selected 8 ⟨711513, by decide⟩
    (prefixPartial 13 368717) = some ⟨13, 2, 0, 711513, 368717, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_368717_711513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368717 ⟨711513, by decide⟩ :=
  accepted_of_selected 13 368717 ⟨711513, by decide⟩ ⟨13, 2, 0, 711513, 368717, 1553, 16384⟩
    (by decide) selected_cut_28181

theorem selected_cut_28182 : selected 8 ⟨711531, by decide⟩
    (prefixPartial 13 368718) = some ⟨13, 2, 0, 711531, 368718, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_368718_711531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368718 ⟨711531, by decide⟩ :=
  accepted_of_selected 13 368718 ⟨711531, by decide⟩ ⟨13, 2, 0, 711531, 368718, 1201, 16384⟩
    (by decide) selected_cut_28182

theorem selected_cut_28183 : selected 8 ⟨711535, by decide⟩
    (prefixPartial 13 368719) = some ⟨13, 2, 0, 711535, 368719, 697, 16384⟩ := by
  decide +kernel

theorem context_13_368719_711535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368719 ⟨711535, by decide⟩ :=
  accepted_of_selected 13 368719 ⟨711535, by decide⟩ ⟨13, 2, 0, 711535, 368719, 697, 16384⟩
    (by decide) selected_cut_28183

theorem unmarked_context_12_92179_711536 : frontier 9 ⟨711536, by decide⟩
    (prefixCache 12 92179) (prefixPartial 12 92179) = false := by
  decide +kernel

theorem node_context_12_92179_711536 : EJMOriginalGlobalDAGData.nodes 9 ⟨711536, by decide⟩ =
    .split (coordinate 12) (![⟨711490, by decide⟩,⟨711513, by decide⟩,⟨711531, by decide⟩,⟨711535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92179_711536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92179 ⟨711536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92179
    ⟨711536, by decide⟩ (by decide) (![⟨711490, by decide⟩,⟨711513, by decide⟩,⟨711531, by decide⟩,⟨711535, by decide⟩]) unmarked_context_12_92179_711536 node_context_12_92179_711536
  intro a
  fin_cases a
  · exact context_13_368716_711490
  · exact context_13_368717_711513
  · exact context_13_368718_711531
  · exact context_13_368719_711535

theorem unmarked_context_11_23044_711537 : frontier 10 ⟨711537, by decide⟩
    (prefixCache 11 23044) (prefixPartial 11 23044) = false := by
  decide +kernel

theorem node_context_11_23044_711537 : EJMOriginalGlobalDAGData.nodes 10 ⟨711537, by decide⟩ =
    .split (coordinate 11) (![⟨641337, by decide⟩,⟨711397, by decide⟩,⟨711464, by decide⟩,⟨711536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23044_711537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23044 ⟨711537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23044
    ⟨711537, by decide⟩ (by decide) (![⟨641337, by decide⟩,⟨711397, by decide⟩,⟨711464, by decide⟩,⟨711536, by decide⟩]) unmarked_context_11_23044_711537 node_context_11_23044_711537
  intro a
  fin_cases a
  · exact context_12_92176_641337
  · exact context_12_92177_711397
  · exact context_12_92178_711464
  · exact context_12_92179_711536

theorem selected_cut_28184 : selected 8 ⟨711556, by decide⟩
    (prefixPartial 13 368720) = some ⟨13, 2, 0, 711556, 368720, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_368720_711556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368720 ⟨711556, by decide⟩ :=
  accepted_of_selected 13 368720 ⟨711556, by decide⟩ ⟨13, 2, 0, 711556, 368720, 1165, 16384⟩
    (by decide) selected_cut_28184

theorem selected_cut_28185 : selected 8 ⟨711585, by decide⟩
    (prefixPartial 13 368721) = some ⟨13, 2, 0, 711585, 368721, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_368721_711585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368721 ⟨711585, by decide⟩ :=
  accepted_of_selected 13 368721 ⟨711585, by decide⟩ ⟨13, 2, 0, 711585, 368721, 1889, 16384⟩
    (by decide) selected_cut_28185

theorem selected_cut_28186 : selected 8 ⟨711604, by decide⟩
    (prefixPartial 13 368722) = some ⟨13, 2, 0, 711604, 368722, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_368722_711604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368722 ⟨711604, by decide⟩ :=
  accepted_of_selected 13 368722 ⟨711604, by decide⟩ ⟨13, 2, 0, 711604, 368722, 1381, 16384⟩
    (by decide) selected_cut_28186

theorem selected_cut_28187 : selected 8 ⟨711610, by decide⟩
    (prefixPartial 13 368723) = some ⟨13, 2, 0, 711610, 368723, 789, 16384⟩ := by
  decide +kernel

theorem context_13_368723_711610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368723 ⟨711610, by decide⟩ :=
  accepted_of_selected 13 368723 ⟨711610, by decide⟩ ⟨13, 2, 0, 711610, 368723, 789, 16384⟩
    (by decide) selected_cut_28187

theorem unmarked_context_12_92180_711611 : frontier 9 ⟨711611, by decide⟩
    (prefixCache 12 92180) (prefixPartial 12 92180) = false := by
  decide +kernel

theorem node_context_12_92180_711611 : EJMOriginalGlobalDAGData.nodes 9 ⟨711611, by decide⟩ =
    .split (coordinate 12) (![⟨711556, by decide⟩,⟨711585, by decide⟩,⟨711604, by decide⟩,⟨711610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92180_711611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92180 ⟨711611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92180
    ⟨711611, by decide⟩ (by decide) (![⟨711556, by decide⟩,⟨711585, by decide⟩,⟨711604, by decide⟩,⟨711610, by decide⟩]) unmarked_context_12_92180_711611 node_context_12_92180_711611
  intro a
  fin_cases a
  · exact context_13_368720_711556
  · exact context_13_368721_711585
  · exact context_13_368722_711604
  · exact context_13_368723_711610

theorem selected_cut_28188 : selected 8 ⟨711646, by decide⟩
    (prefixPartial 13 368724) = some ⟨13, 2, 0, 711646, 368724, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_368724_711646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368724 ⟨711646, by decide⟩ :=
  accepted_of_selected 13 368724 ⟨711646, by decide⟩ ⟨13, 2, 0, 711646, 368724, 1553, 16384⟩
    (by decide) selected_cut_28188

theorem selected_cut_28189 : selected 8 ⟨711670, by decide⟩
    (prefixPartial 13 368725) = some ⟨13, 2, 0, 711670, 368725, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_368725_711670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368725 ⟨711670, by decide⟩ :=
  accepted_of_selected 13 368725 ⟨711670, by decide⟩ ⟨13, 2, 0, 711670, 368725, 1429, 16384⟩
    (by decide) selected_cut_28189

theorem selected_cut_28190 : selected 8 ⟨711687, by decide⟩
    (prefixPartial 13 368726) = some ⟨13, 2, 0, 711687, 368726, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_368726_711687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368726 ⟨711687, by decide⟩ :=
  accepted_of_selected 13 368726 ⟨711687, by decide⟩ ⟨13, 2, 0, 711687, 368726, 1401, 16384⟩
    (by decide) selected_cut_28190

theorem selected_cut_28191 : selected 8 ⟨711693, by decide⟩
    (prefixPartial 13 368727) = some ⟨13, 2, 0, 711693, 368727, 813, 16384⟩ := by
  decide +kernel

theorem context_13_368727_711693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368727 ⟨711693, by decide⟩ :=
  accepted_of_selected 13 368727 ⟨711693, by decide⟩ ⟨13, 2, 0, 711693, 368727, 813, 16384⟩
    (by decide) selected_cut_28191

theorem unmarked_context_12_92181_711694 : frontier 9 ⟨711694, by decide⟩
    (prefixCache 12 92181) (prefixPartial 12 92181) = false := by
  decide +kernel

theorem node_context_12_92181_711694 : EJMOriginalGlobalDAGData.nodes 9 ⟨711694, by decide⟩ =
    .split (coordinate 12) (![⟨711646, by decide⟩,⟨711670, by decide⟩,⟨711687, by decide⟩,⟨711693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92181_711694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92181 ⟨711694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92181
    ⟨711694, by decide⟩ (by decide) (![⟨711646, by decide⟩,⟨711670, by decide⟩,⟨711687, by decide⟩,⟨711693, by decide⟩]) unmarked_context_12_92181_711694 node_context_12_92181_711694
  intro a
  fin_cases a
  · exact context_13_368724_711646
  · exact context_13_368725_711670
  · exact context_13_368726_711687
  · exact context_13_368727_711693

theorem selected_cut_28192 : selected 8 ⟨711714, by decide⟩
    (prefixPartial 13 368728) = some ⟨13, 2, 0, 711714, 368728, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_368728_711714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368728 ⟨711714, by decide⟩ :=
  accepted_of_selected 13 368728 ⟨711714, by decide⟩ ⟨13, 2, 0, 711714, 368728, 1613, 16384⟩
    (by decide) selected_cut_28192

theorem selected_cut_28193 : selected 8 ⟨711739, by decide⟩
    (prefixPartial 13 368729) = some ⟨13, 2, 0, 711739, 368729, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_368729_711739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368729 ⟨711739, by decide⟩ :=
  accepted_of_selected 13 368729 ⟨711739, by decide⟩ ⟨13, 2, 0, 711739, 368729, 1733, 16384⟩
    (by decide) selected_cut_28193

theorem selected_cut_28194 : selected 8 ⟨711757, by decide⟩
    (prefixPartial 13 368730) = some ⟨13, 2, 0, 711757, 368730, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_368730_711757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368730 ⟨711757, by decide⟩ :=
  accepted_of_selected 13 368730 ⟨711757, by decide⟩ ⟨13, 2, 0, 711757, 368730, 1301, 16384⟩
    (by decide) selected_cut_28194

theorem selected_cut_28195 : selected 8 ⟨711762, by decide⟩
    (prefixPartial 13 368731) = some ⟨13, 2, 0, 711762, 368731, 901, 16384⟩ := by
  decide +kernel

theorem context_13_368731_711762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368731 ⟨711762, by decide⟩ :=
  accepted_of_selected 13 368731 ⟨711762, by decide⟩ ⟨13, 2, 0, 711762, 368731, 901, 16384⟩
    (by decide) selected_cut_28195

theorem unmarked_context_12_92182_711763 : frontier 9 ⟨711763, by decide⟩
    (prefixCache 12 92182) (prefixPartial 12 92182) = false := by
  decide +kernel

theorem node_context_12_92182_711763 : EJMOriginalGlobalDAGData.nodes 9 ⟨711763, by decide⟩ =
    .split (coordinate 12) (![⟨711714, by decide⟩,⟨711739, by decide⟩,⟨711757, by decide⟩,⟨711762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92182_711763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92182 ⟨711763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92182
    ⟨711763, by decide⟩ (by decide) (![⟨711714, by decide⟩,⟨711739, by decide⟩,⟨711757, by decide⟩,⟨711762, by decide⟩]) unmarked_context_12_92182_711763 node_context_12_92182_711763
  intro a
  fin_cases a
  · exact context_13_368728_711714
  · exact context_13_368729_711739
  · exact context_13_368730_711757
  · exact context_13_368731_711762

theorem selected_cut_28196 : selected 8 ⟨711795, by decide⟩
    (prefixPartial 13 368732) = some ⟨13, 2, 0, 711795, 368732, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_368732_711795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368732 ⟨711795, by decide⟩ :=
  accepted_of_selected 13 368732 ⟨711795, by decide⟩ ⟨13, 2, 0, 711795, 368732, 1725, 16384⟩
    (by decide) selected_cut_28196

theorem selected_cut_28197 : selected 8 ⟨711826, by decide⟩
    (prefixPartial 13 368733) = some ⟨13, 2, 0, 711826, 368733, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_368733_711826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368733 ⟨711826, by decide⟩ :=
  accepted_of_selected 13 368733 ⟨711826, by decide⟩ ⟨13, 2, 0, 711826, 368733, 2013, 16384⟩
    (by decide) selected_cut_28197

theorem selected_cut_28198 : selected 8 ⟨711843, by decide⟩
    (prefixPartial 13 368734) = some ⟨13, 2, 0, 711843, 368734, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_368734_711843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368734 ⟨711843, by decide⟩ :=
  accepted_of_selected 13 368734 ⟨711843, by decide⟩ ⟨13, 2, 0, 711843, 368734, 1477, 16384⟩
    (by decide) selected_cut_28198

theorem selected_cut_28199 : selected 8 ⟨711851, by decide⟩
    (prefixPartial 13 368735) = some ⟨13, 2, 0, 711851, 368735, 817, 16384⟩ := by
  decide +kernel

theorem context_13_368735_711851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368735 ⟨711851, by decide⟩ :=
  accepted_of_selected 13 368735 ⟨711851, by decide⟩ ⟨13, 2, 0, 711851, 368735, 817, 16384⟩
    (by decide) selected_cut_28199

theorem unmarked_context_12_92183_711852 : frontier 9 ⟨711852, by decide⟩
    (prefixCache 12 92183) (prefixPartial 12 92183) = false := by
  decide +kernel

theorem node_context_12_92183_711852 : EJMOriginalGlobalDAGData.nodes 9 ⟨711852, by decide⟩ =
    .split (coordinate 12) (![⟨711795, by decide⟩,⟨711826, by decide⟩,⟨711843, by decide⟩,⟨711851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92183_711852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92183 ⟨711852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92183
    ⟨711852, by decide⟩ (by decide) (![⟨711795, by decide⟩,⟨711826, by decide⟩,⟨711843, by decide⟩,⟨711851, by decide⟩]) unmarked_context_12_92183_711852 node_context_12_92183_711852
  intro a
  fin_cases a
  · exact context_13_368732_711795
  · exact context_13_368733_711826
  · exact context_13_368734_711843
  · exact context_13_368735_711851

theorem unmarked_context_11_23045_711853 : frontier 10 ⟨711853, by decide⟩
    (prefixCache 11 23045) (prefixPartial 11 23045) = false := by
  decide +kernel

theorem node_context_11_23045_711853 : EJMOriginalGlobalDAGData.nodes 10 ⟨711853, by decide⟩ =
    .split (coordinate 11) (![⟨711611, by decide⟩,⟨711694, by decide⟩,⟨711763, by decide⟩,⟨711852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23045_711853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23045 ⟨711853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23045
    ⟨711853, by decide⟩ (by decide) (![⟨711611, by decide⟩,⟨711694, by decide⟩,⟨711763, by decide⟩,⟨711852, by decide⟩]) unmarked_context_11_23045_711853 node_context_11_23045_711853
  intro a
  fin_cases a
  · exact context_12_92180_711611
  · exact context_12_92181_711694
  · exact context_12_92182_711763
  · exact context_12_92183_711852

theorem selected_cut_28200 : selected 8 ⟨711867, by decide⟩
    (prefixPartial 13 368736) = some ⟨13, 2, 0, 711867, 368736, 905, 16384⟩ := by
  decide +kernel

theorem context_13_368736_711867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368736 ⟨711867, by decide⟩ :=
  accepted_of_selected 13 368736 ⟨711867, by decide⟩ ⟨13, 2, 0, 711867, 368736, 905, 16384⟩
    (by decide) selected_cut_28200

theorem selected_cut_28201 : selected 8 ⟨711893, by decide⟩
    (prefixPartial 13 368737) = some ⟨13, 2, 0, 711893, 368737, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_368737_711893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368737 ⟨711893, by decide⟩ :=
  accepted_of_selected 13 368737 ⟨711893, by decide⟩ ⟨13, 2, 0, 711893, 368737, 1681, 16384⟩
    (by decide) selected_cut_28201

theorem selected_cut_28202 : selected 8 ⟨711907, by decide⟩
    (prefixPartial 13 368738) = some ⟨13, 2, 0, 711907, 368738, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_368738_711907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368738 ⟨711907, by decide⟩ :=
  accepted_of_selected 13 368738 ⟨711907, by decide⟩ ⟨13, 2, 0, 711907, 368738, 1045, 16384⟩
    (by decide) selected_cut_28202

theorem selected_cut_28203 : selected 8 ⟨711913, by decide⟩
    (prefixPartial 13 368739) = some ⟨13, 2, 0, 711913, 368739, 749, 16384⟩ := by
  decide +kernel

theorem context_13_368739_711913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368739 ⟨711913, by decide⟩ :=
  accepted_of_selected 13 368739 ⟨711913, by decide⟩ ⟨13, 2, 0, 711913, 368739, 749, 16384⟩
    (by decide) selected_cut_28203

theorem unmarked_context_12_92184_711914 : frontier 9 ⟨711914, by decide⟩
    (prefixCache 12 92184) (prefixPartial 12 92184) = false := by
  decide +kernel

theorem node_context_12_92184_711914 : EJMOriginalGlobalDAGData.nodes 9 ⟨711914, by decide⟩ =
    .split (coordinate 12) (![⟨711867, by decide⟩,⟨711893, by decide⟩,⟨711907, by decide⟩,⟨711913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92184_711914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92184 ⟨711914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92184
    ⟨711914, by decide⟩ (by decide) (![⟨711867, by decide⟩,⟨711893, by decide⟩,⟨711907, by decide⟩,⟨711913, by decide⟩]) unmarked_context_12_92184_711914 node_context_12_92184_711914
  intro a
  fin_cases a
  · exact context_13_368736_711867
  · exact context_13_368737_711893
  · exact context_13_368738_711907
  · exact context_13_368739_711913

theorem selected_cut_28204 : selected 8 ⟨711944, by decide⟩
    (prefixPartial 13 368740) = some ⟨13, 2, 0, 711944, 368740, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_368740_711944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368740 ⟨711944, by decide⟩ :=
  accepted_of_selected 13 368740 ⟨711944, by decide⟩ ⟨13, 2, 0, 711944, 368740, 1381, 16384⟩
    (by decide) selected_cut_28204

theorem selected_cut_28205 : selected 8 ⟨711967, by decide⟩
    (prefixPartial 13 368741) = some ⟨13, 2, 0, 711967, 368741, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_368741_711967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368741 ⟨711967, by decide⟩ :=
  accepted_of_selected 13 368741 ⟨711967, by decide⟩ ⟨13, 2, 0, 711967, 368741, 1489, 16384⟩
    (by decide) selected_cut_28205

theorem selected_cut_28206 : selected 8 ⟨711986, by decide⟩
    (prefixPartial 13 368742) = some ⟨13, 2, 0, 711986, 368742, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_368742_711986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368742 ⟨711986, by decide⟩ :=
  accepted_of_selected 13 368742 ⟨711986, by decide⟩ ⟨13, 2, 0, 711986, 368742, 1181, 16384⟩
    (by decide) selected_cut_28206

theorem selected_cut_28207 : selected 8 ⟨711992, by decide⟩
    (prefixPartial 13 368743) = some ⟨13, 2, 0, 711992, 368743, 917, 16384⟩ := by
  decide +kernel

theorem context_13_368743_711992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368743 ⟨711992, by decide⟩ :=
  accepted_of_selected 13 368743 ⟨711992, by decide⟩ ⟨13, 2, 0, 711992, 368743, 917, 16384⟩
    (by decide) selected_cut_28207

theorem unmarked_context_12_92185_711993 : frontier 9 ⟨711993, by decide⟩
    (prefixCache 12 92185) (prefixPartial 12 92185) = false := by
  decide +kernel

theorem node_context_12_92185_711993 : EJMOriginalGlobalDAGData.nodes 9 ⟨711993, by decide⟩ =
    .split (coordinate 12) (![⟨711944, by decide⟩,⟨711967, by decide⟩,⟨711986, by decide⟩,⟨711992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92185_711993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92185 ⟨711993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92185
    ⟨711993, by decide⟩ (by decide) (![⟨711944, by decide⟩,⟨711967, by decide⟩,⟨711986, by decide⟩,⟨711992, by decide⟩]) unmarked_context_12_92185_711993 node_context_12_92185_711993
  intro a
  fin_cases a
  · exact context_13_368740_711944
  · exact context_13_368741_711967
  · exact context_13_368742_711986
  · exact context_13_368743_711992

theorem selected_cut_28208 : selected 8 ⟨712015, by decide⟩
    (prefixPartial 13 368744) = some ⟨13, 2, 0, 712015, 368744, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_368744_712015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368744 ⟨712015, by decide⟩ :=
  accepted_of_selected 13 368744 ⟨712015, by decide⟩ ⟨13, 2, 0, 712015, 368744, 1153, 16384⟩
    (by decide) selected_cut_28208

theorem selected_cut_28209 : selected 8 ⟨712035, by decide⟩
    (prefixPartial 13 368745) = some ⟨13, 2, 0, 712035, 368745, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_368745_712035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368745 ⟨712035, by decide⟩ :=
  accepted_of_selected 13 368745 ⟨712035, by decide⟩ ⟨13, 2, 0, 712035, 368745, 1309, 16384⟩
    (by decide) selected_cut_28209

theorem selected_cut_28210 : selected 8 ⟨712048, by decide⟩
    (prefixPartial 13 368746) = some ⟨13, 2, 0, 712048, 368746, 969, 16384⟩ := by
  decide +kernel

theorem context_13_368746_712048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368746 ⟨712048, by decide⟩ :=
  accepted_of_selected 13 368746 ⟨712048, by decide⟩ ⟨13, 2, 0, 712048, 368746, 969, 16384⟩
    (by decide) selected_cut_28210

theorem selected_cut_28211 : selected 8 ⟨712056, by decide⟩
    (prefixPartial 13 368747) = some ⟨13, 2, 0, 712056, 368747, 833, 16384⟩ := by
  decide +kernel

theorem context_13_368747_712056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368747 ⟨712056, by decide⟩ :=
  accepted_of_selected 13 368747 ⟨712056, by decide⟩ ⟨13, 2, 0, 712056, 368747, 833, 16384⟩
    (by decide) selected_cut_28211

theorem unmarked_context_12_92186_712057 : frontier 9 ⟨712057, by decide⟩
    (prefixCache 12 92186) (prefixPartial 12 92186) = false := by
  decide +kernel

theorem node_context_12_92186_712057 : EJMOriginalGlobalDAGData.nodes 9 ⟨712057, by decide⟩ =
    .split (coordinate 12) (![⟨712015, by decide⟩,⟨712035, by decide⟩,⟨712048, by decide⟩,⟨712056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92186_712057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92186 ⟨712057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92186
    ⟨712057, by decide⟩ (by decide) (![⟨712015, by decide⟩,⟨712035, by decide⟩,⟨712048, by decide⟩,⟨712056, by decide⟩]) unmarked_context_12_92186_712057 node_context_12_92186_712057
  intro a
  fin_cases a
  · exact context_13_368744_712015
  · exact context_13_368745_712035
  · exact context_13_368746_712048
  · exact context_13_368747_712056

theorem selected_cut_28212 : selected 8 ⟨712082, by decide⟩
    (prefixPartial 13 368748) = some ⟨13, 2, 0, 712082, 368748, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_368748_712082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368748 ⟨712082, by decide⟩ :=
  accepted_of_selected 13 368748 ⟨712082, by decide⟩ ⟨13, 2, 0, 712082, 368748, 1257, 16384⟩
    (by decide) selected_cut_28212

theorem selected_cut_28213 : selected 8 ⟨712113, by decide⟩
    (prefixPartial 13 368749) = some ⟨13, 2, 0, 712113, 368749, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_368749_712113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368749 ⟨712113, by decide⟩ :=
  accepted_of_selected 13 368749 ⟨712113, by decide⟩ ⟨13, 2, 0, 712113, 368749, 1837, 16384⟩
    (by decide) selected_cut_28213

theorem selected_cut_28214 : selected 8 ⟨712131, by decide⟩
    (prefixPartial 13 368750) = some ⟨13, 2, 0, 712131, 368750, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_368750_712131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368750 ⟨712131, by decide⟩ :=
  accepted_of_selected 13 368750 ⟨712131, by decide⟩ ⟨13, 2, 0, 712131, 368750, 1069, 16384⟩
    (by decide) selected_cut_28214

theorem selected_cut_28215 : selected 8 ⟨712136, by decide⟩
    (prefixPartial 13 368751) = some ⟨13, 2, 0, 712136, 368751, 781, 16384⟩ := by
  decide +kernel

theorem context_13_368751_712136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368751 ⟨712136, by decide⟩ :=
  accepted_of_selected 13 368751 ⟨712136, by decide⟩ ⟨13, 2, 0, 712136, 368751, 781, 16384⟩
    (by decide) selected_cut_28215

theorem unmarked_context_12_92187_712137 : frontier 9 ⟨712137, by decide⟩
    (prefixCache 12 92187) (prefixPartial 12 92187) = false := by
  decide +kernel

theorem node_context_12_92187_712137 : EJMOriginalGlobalDAGData.nodes 9 ⟨712137, by decide⟩ =
    .split (coordinate 12) (![⟨712082, by decide⟩,⟨712113, by decide⟩,⟨712131, by decide⟩,⟨712136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92187_712137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92187 ⟨712137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92187
    ⟨712137, by decide⟩ (by decide) (![⟨712082, by decide⟩,⟨712113, by decide⟩,⟨712131, by decide⟩,⟨712136, by decide⟩]) unmarked_context_12_92187_712137 node_context_12_92187_712137
  intro a
  fin_cases a
  · exact context_13_368748_712082
  · exact context_13_368749_712113
  · exact context_13_368750_712131
  · exact context_13_368751_712136

theorem unmarked_context_11_23046_712138 : frontier 10 ⟨712138, by decide⟩
    (prefixCache 11 23046) (prefixPartial 11 23046) = false := by
  decide +kernel

theorem node_context_11_23046_712138 : EJMOriginalGlobalDAGData.nodes 10 ⟨712138, by decide⟩ =
    .split (coordinate 11) (![⟨711914, by decide⟩,⟨711993, by decide⟩,⟨712057, by decide⟩,⟨712137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23046_712138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23046 ⟨712138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23046
    ⟨712138, by decide⟩ (by decide) (![⟨711914, by decide⟩,⟨711993, by decide⟩,⟨712057, by decide⟩,⟨712137, by decide⟩]) unmarked_context_11_23046_712138 node_context_11_23046_712138
  intro a
  fin_cases a
  · exact context_12_92184_711914
  · exact context_12_92185_711993
  · exact context_12_92186_712057
  · exact context_12_92187_712137

theorem selected_cut_28216 : selected 8 ⟨712149, by decide⟩
    (prefixPartial 13 368752) = some ⟨13, 2, 0, 712149, 368752, 941, 16384⟩ := by
  decide +kernel

theorem context_13_368752_712149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368752 ⟨712149, by decide⟩ :=
  accepted_of_selected 13 368752 ⟨712149, by decide⟩ ⟨13, 2, 0, 712149, 368752, 941, 16384⟩
    (by decide) selected_cut_28216

theorem selected_cut_28217 : selected 8 ⟨712175, by decide⟩
    (prefixPartial 13 368753) = some ⟨13, 2, 0, 712175, 368753, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_368753_712175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368753 ⟨712175, by decide⟩ :=
  accepted_of_selected 13 368753 ⟨712175, by decide⟩ ⟨13, 2, 0, 712175, 368753, 1765, 16384⟩
    (by decide) selected_cut_28217

theorem selected_cut_28218 : selected 8 ⟨712193, by decide⟩
    (prefixPartial 13 368754) = some ⟨13, 2, 0, 712193, 368754, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_368754_712193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368754 ⟨712193, by decide⟩ :=
  accepted_of_selected 13 368754 ⟨712193, by decide⟩ ⟨13, 2, 0, 712193, 368754, 1133, 16384⟩
    (by decide) selected_cut_28218

theorem selected_cut_28219 : selected 8 ⟨712197, by decide⟩
    (prefixPartial 13 368755) = some ⟨13, 2, 0, 712197, 368755, 733, 16384⟩ := by
  decide +kernel

theorem context_13_368755_712197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368755 ⟨712197, by decide⟩ :=
  accepted_of_selected 13 368755 ⟨712197, by decide⟩ ⟨13, 2, 0, 712197, 368755, 733, 16384⟩
    (by decide) selected_cut_28219

theorem unmarked_context_12_92188_712198 : frontier 9 ⟨712198, by decide⟩
    (prefixCache 12 92188) (prefixPartial 12 92188) = false := by
  decide +kernel

theorem node_context_12_92188_712198 : EJMOriginalGlobalDAGData.nodes 9 ⟨712198, by decide⟩ =
    .split (coordinate 12) (![⟨712149, by decide⟩,⟨712175, by decide⟩,⟨712193, by decide⟩,⟨712197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92188_712198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92188 ⟨712198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92188
    ⟨712198, by decide⟩ (by decide) (![⟨712149, by decide⟩,⟨712175, by decide⟩,⟨712193, by decide⟩,⟨712197, by decide⟩]) unmarked_context_12_92188_712198 node_context_12_92188_712198
  intro a
  fin_cases a
  · exact context_13_368752_712149
  · exact context_13_368753_712175
  · exact context_13_368754_712193
  · exact context_13_368755_712197

theorem selected_cut_28220 : selected 8 ⟨712226, by decide⟩
    (prefixPartial 13 368756) = some ⟨13, 2, 0, 712226, 368756, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_368756_712226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368756 ⟨712226, by decide⟩ :=
  accepted_of_selected 13 368756 ⟨712226, by decide⟩ ⟨13, 2, 0, 712226, 368756, 1329, 16384⟩
    (by decide) selected_cut_28220

theorem selected_cut_28221 : selected 8 ⟨712253, by decide⟩
    (prefixPartial 13 368757) = some ⟨13, 2, 0, 712253, 368757, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_368757_712253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368757 ⟨712253, by decide⟩ :=
  accepted_of_selected 13 368757 ⟨712253, by decide⟩ ⟨13, 2, 0, 712253, 368757, 1681, 16384⟩
    (by decide) selected_cut_28221

theorem selected_cut_28222 : selected 8 ⟨712271, by decide⟩
    (prefixPartial 13 368758) = some ⟨13, 2, 0, 712271, 368758, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_368758_712271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368758 ⟨712271, by decide⟩ :=
  accepted_of_selected 13 368758 ⟨712271, by decide⟩ ⟨13, 2, 0, 712271, 368758, 1265, 16384⟩
    (by decide) selected_cut_28222

theorem selected_cut_28223 : selected 8 ⟨712276, by decide⟩
    (prefixPartial 13 368759) = some ⟨13, 2, 0, 712276, 368759, 805, 16384⟩ := by
  decide +kernel

theorem context_13_368759_712276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368759 ⟨712276, by decide⟩ :=
  accepted_of_selected 13 368759 ⟨712276, by decide⟩ ⟨13, 2, 0, 712276, 368759, 805, 16384⟩
    (by decide) selected_cut_28223

theorem unmarked_context_12_92189_712277 : frontier 9 ⟨712277, by decide⟩
    (prefixCache 12 92189) (prefixPartial 12 92189) = false := by
  decide +kernel

theorem node_context_12_92189_712277 : EJMOriginalGlobalDAGData.nodes 9 ⟨712277, by decide⟩ =
    .split (coordinate 12) (![⟨712226, by decide⟩,⟨712253, by decide⟩,⟨712271, by decide⟩,⟨712276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92189_712277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92189 ⟨712277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92189
    ⟨712277, by decide⟩ (by decide) (![⟨712226, by decide⟩,⟨712253, by decide⟩,⟨712271, by decide⟩,⟨712276, by decide⟩]) unmarked_context_12_92189_712277 node_context_12_92189_712277
  intro a
  fin_cases a
  · exact context_13_368756_712226
  · exact context_13_368757_712253
  · exact context_13_368758_712271
  · exact context_13_368759_712276

theorem selected_cut_28224 : selected 8 ⟨712295, by decide⟩
    (prefixPartial 13 368760) = some ⟨13, 2, 0, 712295, 368760, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_368760_712295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368760 ⟨712295, by decide⟩ :=
  accepted_of_selected 13 368760 ⟨712295, by decide⟩ ⟨13, 2, 0, 712295, 368760, 1157, 16384⟩
    (by decide) selected_cut_28224

theorem selected_cut_28225 : selected 8 ⟨712319, by decide⟩
    (prefixPartial 13 368761) = some ⟨13, 2, 0, 712319, 368761, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_368761_712319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368761 ⟨712319, by decide⟩ :=
  accepted_of_selected 13 368761 ⟨712319, by decide⟩ ⟨13, 2, 0, 712319, 368761, 1701, 16384⟩
    (by decide) selected_cut_28225

theorem selected_cut_28226 : selected 8 ⟨712336, by decide⟩
    (prefixPartial 13 368762) = some ⟨13, 2, 0, 712336, 368762, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_368762_712336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368762 ⟨712336, by decide⟩ :=
  accepted_of_selected 13 368762 ⟨712336, by decide⟩ ⟨13, 2, 0, 712336, 368762, 1149, 16384⟩
    (by decide) selected_cut_28226

theorem selected_cut_28227 : selected 8 ⟨712341, by decide⟩
    (prefixPartial 13 368763) = some ⟨13, 2, 0, 712341, 368763, 861, 16384⟩ := by
  decide +kernel

theorem context_13_368763_712341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368763 ⟨712341, by decide⟩ :=
  accepted_of_selected 13 368763 ⟨712341, by decide⟩ ⟨13, 2, 0, 712341, 368763, 861, 16384⟩
    (by decide) selected_cut_28227

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
