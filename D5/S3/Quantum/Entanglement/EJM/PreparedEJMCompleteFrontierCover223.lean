/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover222
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_21411 : selected 8 ⟨548118, by decide⟩
    (prefixPartial 13 300156) = some ⟨13, 2, 0, 548118, 300156, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_300156_548118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300156 ⟨548118, by decide⟩ :=
  accepted_of_selected 13 300156 ⟨548118, by decide⟩ ⟨13, 2, 0, 548118, 300156, 1733, 16384⟩
    (by decide) selected_cut_21411

theorem selected_cut_21412 : selected 8 ⟨548145, by decide⟩
    (prefixPartial 13 300157) = some ⟨13, 2, 0, 548145, 300157, 2801, 16384⟩ := by
  decide +kernel

theorem context_13_300157_548145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300157 ⟨548145, by decide⟩ :=
  accepted_of_selected 13 300157 ⟨548145, by decide⟩ ⟨13, 2, 0, 548145, 300157, 2801, 16384⟩
    (by decide) selected_cut_21412

theorem selected_cut_21413 : selected 8 ⟨548168, by decide⟩
    (prefixPartial 13 300158) = some ⟨13, 2, 0, 548168, 300158, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_300158_548168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300158 ⟨548168, by decide⟩ :=
  accepted_of_selected 13 300158 ⟨548168, by decide⟩ ⟨13, 2, 0, 548168, 300158, 2021, 16384⟩
    (by decide) selected_cut_21413

theorem selected_cut_21414 : selected 8 ⟨548174, by decide⟩
    (prefixPartial 13 300159) = some ⟨13, 2, 0, 548174, 300159, 925, 16384⟩ := by
  decide +kernel

theorem context_13_300159_548174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300159 ⟨548174, by decide⟩ :=
  accepted_of_selected 13 300159 ⟨548174, by decide⟩ ⟨13, 2, 0, 548174, 300159, 925, 16384⟩
    (by decide) selected_cut_21414

theorem unmarked_context_12_75039_548175 : frontier 9 ⟨548175, by decide⟩
    (prefixCache 12 75039) (prefixPartial 12 75039) = false := by
  decide +kernel

theorem node_context_12_75039_548175 : EJMOriginalGlobalDAGData.nodes 9 ⟨548175, by decide⟩ =
    .split (coordinate 12) (![⟨548118, by decide⟩,⟨548145, by decide⟩,⟨548168, by decide⟩,⟨548174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75039_548175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75039 ⟨548175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75039
    ⟨548175, by decide⟩ (by decide) (![⟨548118, by decide⟩,⟨548145, by decide⟩,⟨548168, by decide⟩,⟨548174, by decide⟩]) unmarked_context_12_75039_548175 node_context_12_75039_548175
  intro a
  fin_cases a
  · exact context_13_300156_548118
  · exact context_13_300157_548145
  · exact context_13_300158_548168
  · exact context_13_300159_548174

theorem unmarked_context_11_18759_548176 : frontier 10 ⟨548176, by decide⟩
    (prefixCache 11 18759) (prefixPartial 11 18759) = false := by
  decide +kernel

theorem node_context_11_18759_548176 : EJMOriginalGlobalDAGData.nodes 10 ⟨548176, by decide⟩ =
    .split (coordinate 11) (![⟨547928, by decide⟩,⟨547998, by decide⟩,⟨548080, by decide⟩,⟨548175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18759_548176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18759 ⟨548176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18759
    ⟨548176, by decide⟩ (by decide) (![⟨547928, by decide⟩,⟨547998, by decide⟩,⟨548080, by decide⟩,⟨548175, by decide⟩]) unmarked_context_11_18759_548176 node_context_11_18759_548176
  intro a
  fin_cases a
  · exact context_12_75036_547928
  · exact context_12_75037_547998
  · exact context_12_75038_548080
  · exact context_12_75039_548175

theorem unmarked_context_10_4689_548177 : frontier 11 ⟨548177, by decide⟩
    (prefixCache 10 4689) (prefixPartial 10 4689) = false := by
  decide +kernel

theorem node_context_10_4689_548177 : EJMOriginalGlobalDAGData.nodes 11 ⟨548177, by decide⟩ =
    .split (coordinate 10) (![⟨546976, by decide⟩,⟨547323, by decide⟩,⟨547780, by decide⟩,⟨548176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4689_548177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4689 ⟨548177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4689
    ⟨548177, by decide⟩ (by decide) (![⟨546976, by decide⟩,⟨547323, by decide⟩,⟨547780, by decide⟩,⟨548176, by decide⟩]) unmarked_context_10_4689_548177 node_context_10_4689_548177
  intro a
  fin_cases a
  · exact context_11_18756_546976
  · exact context_11_18757_547323
  · exact context_11_18758_547780
  · exact context_11_18759_548176

theorem selected_cut_21415 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 75040) = some ⟨12, 1, 0, 435790, 75040, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75040_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75040 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 75040 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 75040, 1, 65536⟩
    (by decide) selected_cut_21415

theorem selected_cut_21416 : selected 8 ⟨548199, by decide⟩
    (prefixPartial 13 300164) = some ⟨13, 2, 0, 548199, 300164, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_300164_548199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300164 ⟨548199, by decide⟩ :=
  accepted_of_selected 13 300164 ⟨548199, by decide⟩ ⟨13, 2, 0, 548199, 300164, 1345, 16384⟩
    (by decide) selected_cut_21416

theorem selected_cut_21417 : selected 8 ⟨548220, by decide⟩
    (prefixPartial 13 300165) = some ⟨13, 2, 0, 548220, 300165, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_300165_548220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300165 ⟨548220, by decide⟩ :=
  accepted_of_selected 13 300165 ⟨548220, by decide⟩ ⟨13, 2, 0, 548220, 300165, 1677, 16384⟩
    (by decide) selected_cut_21417

theorem selected_cut_21418 : selected 8 ⟨548238, by decide⟩
    (prefixPartial 13 300166) = some ⟨13, 2, 0, 548238, 300166, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_300166_548238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300166 ⟨548238, by decide⟩ :=
  accepted_of_selected 13 300166 ⟨548238, by decide⟩ ⟨13, 2, 0, 548238, 300166, 1317, 16384⟩
    (by decide) selected_cut_21418

theorem selected_cut_21419 : selected 8 ⟨548246, by decide⟩
    (prefixPartial 13 300167) = some ⟨13, 2, 0, 548246, 300167, 745, 16384⟩ := by
  decide +kernel

theorem context_13_300167_548246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300167 ⟨548246, by decide⟩ :=
  accepted_of_selected 13 300167 ⟨548246, by decide⟩ ⟨13, 2, 0, 548246, 300167, 745, 16384⟩
    (by decide) selected_cut_21419

theorem unmarked_context_12_75041_548247 : frontier 9 ⟨548247, by decide⟩
    (prefixCache 12 75041) (prefixPartial 12 75041) = false := by
  decide +kernel

theorem node_context_12_75041_548247 : EJMOriginalGlobalDAGData.nodes 9 ⟨548247, by decide⟩ =
    .split (coordinate 12) (![⟨548199, by decide⟩,⟨548220, by decide⟩,⟨548238, by decide⟩,⟨548246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75041_548247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75041 ⟨548247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75041
    ⟨548247, by decide⟩ (by decide) (![⟨548199, by decide⟩,⟨548220, by decide⟩,⟨548238, by decide⟩,⟨548246, by decide⟩]) unmarked_context_12_75041_548247 node_context_12_75041_548247
  intro a
  fin_cases a
  · exact context_13_300164_548199
  · exact context_13_300165_548220
  · exact context_13_300166_548238
  · exact context_13_300167_548246

theorem selected_cut_21420 : selected 8 ⟨548281, by decide⟩
    (prefixPartial 13 300168) = some ⟨13, 2, 0, 548281, 300168, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_300168_548281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300168 ⟨548281, by decide⟩ :=
  accepted_of_selected 13 300168 ⟨548281, by decide⟩ ⟨13, 2, 0, 548281, 300168, 1497, 16384⟩
    (by decide) selected_cut_21420

theorem selected_cut_21421 : selected 8 ⟨548305, by decide⟩
    (prefixPartial 13 300169) = some ⟨13, 2, 0, 548305, 300169, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_300169_548305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300169 ⟨548305, by decide⟩ :=
  accepted_of_selected 13 300169 ⟨548305, by decide⟩ ⟨13, 2, 0, 548305, 300169, 1877, 16384⟩
    (by decide) selected_cut_21421

theorem selected_cut_21422 : selected 8 ⟨548327, by decide⟩
    (prefixPartial 13 300170) = some ⟨13, 2, 0, 548327, 300170, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_300170_548327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300170 ⟨548327, by decide⟩ :=
  accepted_of_selected 13 300170 ⟨548327, by decide⟩ ⟨13, 2, 0, 548327, 300170, 1477, 16384⟩
    (by decide) selected_cut_21422

theorem selected_cut_21423 : selected 8 ⟨548338, by decide⟩
    (prefixPartial 13 300171) = some ⟨13, 2, 0, 548338, 300171, 861, 16384⟩ := by
  decide +kernel

theorem context_13_300171_548338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300171 ⟨548338, by decide⟩ :=
  accepted_of_selected 13 300171 ⟨548338, by decide⟩ ⟨13, 2, 0, 548338, 300171, 861, 16384⟩
    (by decide) selected_cut_21423

theorem unmarked_context_12_75042_548339 : frontier 9 ⟨548339, by decide⟩
    (prefixCache 12 75042) (prefixPartial 12 75042) = false := by
  decide +kernel

theorem node_context_12_75042_548339 : EJMOriginalGlobalDAGData.nodes 9 ⟨548339, by decide⟩ =
    .split (coordinate 12) (![⟨548281, by decide⟩,⟨548305, by decide⟩,⟨548327, by decide⟩,⟨548338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75042_548339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75042 ⟨548339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75042
    ⟨548339, by decide⟩ (by decide) (![⟨548281, by decide⟩,⟨548305, by decide⟩,⟨548327, by decide⟩,⟨548338, by decide⟩]) unmarked_context_12_75042_548339 node_context_12_75042_548339
  intro a
  fin_cases a
  · exact context_13_300168_548281
  · exact context_13_300169_548305
  · exact context_13_300170_548327
  · exact context_13_300171_548338

theorem selected_cut_21424 : selected 8 ⟨548367, by decide⟩
    (prefixPartial 13 300172) = some ⟨13, 2, 0, 548367, 300172, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_300172_548367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300172 ⟨548367, by decide⟩ :=
  accepted_of_selected 13 300172 ⟨548367, by decide⟩ ⟨13, 2, 0, 548367, 300172, 1733, 16384⟩
    (by decide) selected_cut_21424

theorem selected_cut_21425 : selected 8 ⟨548391, by decide⟩
    (prefixPartial 13 300173) = some ⟨13, 2, 0, 548391, 300173, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_300173_548391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300173 ⟨548391, by decide⟩ :=
  accepted_of_selected 13 300173 ⟨548391, by decide⟩ ⟨13, 2, 0, 548391, 300173, 2169, 16384⟩
    (by decide) selected_cut_21425

theorem selected_cut_21426 : selected 8 ⟨548423, by decide⟩
    (prefixPartial 13 300174) = some ⟨13, 2, 0, 548423, 300174, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_300174_548423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300174 ⟨548423, by decide⟩ :=
  accepted_of_selected 13 300174 ⟨548423, by decide⟩ ⟨13, 2, 0, 548423, 300174, 1809, 16384⟩
    (by decide) selected_cut_21426

theorem selected_cut_21427 : selected 8 ⟨548432, by decide⟩
    (prefixPartial 13 300175) = some ⟨13, 2, 0, 548432, 300175, 941, 16384⟩ := by
  decide +kernel

theorem context_13_300175_548432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300175 ⟨548432, by decide⟩ :=
  accepted_of_selected 13 300175 ⟨548432, by decide⟩ ⟨13, 2, 0, 548432, 300175, 941, 16384⟩
    (by decide) selected_cut_21427

theorem unmarked_context_12_75043_548433 : frontier 9 ⟨548433, by decide⟩
    (prefixCache 12 75043) (prefixPartial 12 75043) = false := by
  decide +kernel

theorem node_context_12_75043_548433 : EJMOriginalGlobalDAGData.nodes 9 ⟨548433, by decide⟩ =
    .split (coordinate 12) (![⟨548367, by decide⟩,⟨548391, by decide⟩,⟨548423, by decide⟩,⟨548432, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75043_548433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75043 ⟨548433, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75043
    ⟨548433, by decide⟩ (by decide) (![⟨548367, by decide⟩,⟨548391, by decide⟩,⟨548423, by decide⟩,⟨548432, by decide⟩]) unmarked_context_12_75043_548433 node_context_12_75043_548433
  intro a
  fin_cases a
  · exact context_13_300172_548367
  · exact context_13_300173_548391
  · exact context_13_300174_548423
  · exact context_13_300175_548432

theorem unmarked_context_11_18760_548434 : frontier 10 ⟨548434, by decide⟩
    (prefixCache 11 18760) (prefixPartial 11 18760) = false := by
  decide +kernel

theorem node_context_11_18760_548434 : EJMOriginalGlobalDAGData.nodes 10 ⟨548434, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨548247, by decide⟩,⟨548339, by decide⟩,⟨548433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18760_548434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18760 ⟨548434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18760
    ⟨548434, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨548247, by decide⟩,⟨548339, by decide⟩,⟨548433, by decide⟩]) unmarked_context_11_18760_548434 node_context_11_18760_548434
  intro a
  fin_cases a
  · exact context_12_75040_435790
  · exact context_12_75041_548247
  · exact context_12_75042_548339
  · exact context_12_75043_548433

theorem selected_cut_21428 : selected 8 ⟨548467, by decide⟩
    (prefixPartial 13 300176) = some ⟨13, 2, 0, 548467, 300176, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_300176_548467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300176 ⟨548467, by decide⟩ :=
  accepted_of_selected 13 300176 ⟨548467, by decide⟩ ⟨13, 2, 0, 548467, 300176, 1769, 16384⟩
    (by decide) selected_cut_21428

theorem selected_cut_21429 : selected 8 ⟨548500, by decide⟩
    (prefixPartial 13 300177) = some ⟨13, 2, 0, 548500, 300177, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_300177_548500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300177 ⟨548500, by decide⟩ :=
  accepted_of_selected 13 300177 ⟨548500, by decide⟩ ⟨13, 2, 0, 548500, 300177, 2337, 16384⟩
    (by decide) selected_cut_21429

theorem selected_cut_21430 : selected 8 ⟨548541, by decide⟩
    (prefixPartial 13 300178) = some ⟨13, 2, 0, 548541, 300178, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_300178_548541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300178 ⟨548541, by decide⟩ :=
  accepted_of_selected 13 300178 ⟨548541, by decide⟩ ⟨13, 2, 0, 548541, 300178, 2057, 16384⟩
    (by decide) selected_cut_21430

theorem selected_cut_21431 : selected 8 ⟨548564, by decide⟩
    (prefixPartial 13 300179) = some ⟨13, 2, 0, 548564, 300179, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_300179_548564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300179 ⟨548564, by decide⟩ :=
  accepted_of_selected 13 300179 ⟨548564, by decide⟩ ⟨13, 2, 0, 548564, 300179, 1169, 16384⟩
    (by decide) selected_cut_21431

theorem unmarked_context_12_75044_548565 : frontier 9 ⟨548565, by decide⟩
    (prefixCache 12 75044) (prefixPartial 12 75044) = false := by
  decide +kernel

theorem node_context_12_75044_548565 : EJMOriginalGlobalDAGData.nodes 9 ⟨548565, by decide⟩ =
    .split (coordinate 12) (![⟨548467, by decide⟩,⟨548500, by decide⟩,⟨548541, by decide⟩,⟨548564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75044_548565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75044 ⟨548565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75044
    ⟨548565, by decide⟩ (by decide) (![⟨548467, by decide⟩,⟨548500, by decide⟩,⟨548541, by decide⟩,⟨548564, by decide⟩]) unmarked_context_12_75044_548565 node_context_12_75044_548565
  intro a
  fin_cases a
  · exact context_13_300176_548467
  · exact context_13_300177_548500
  · exact context_13_300178_548541
  · exact context_13_300179_548564

theorem selected_cut_21432 : selected 8 ⟨548609, by decide⟩
    (prefixPartial 13 300180) = some ⟨13, 2, 0, 548609, 300180, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_300180_548609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300180 ⟨548609, by decide⟩ :=
  accepted_of_selected 13 300180 ⟨548609, by decide⟩ ⟨13, 2, 0, 548609, 300180, 1889, 16384⟩
    (by decide) selected_cut_21432

theorem selected_cut_21433 : selected 8 ⟨548645, by decide⟩
    (prefixPartial 13 300181) = some ⟨13, 2, 0, 548645, 300181, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_300181_548645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300181 ⟨548645, by decide⟩ :=
  accepted_of_selected 13 300181 ⟨548645, by decide⟩ ⟨13, 2, 0, 548645, 300181, 2649, 16384⟩
    (by decide) selected_cut_21433

theorem selected_cut_21434 : selected 8 ⟨548681, by decide⟩
    (prefixPartial 13 300182) = some ⟨13, 2, 0, 548681, 300182, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_300182_548681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300182 ⟨548681, by decide⟩ :=
  accepted_of_selected 13 300182 ⟨548681, by decide⟩ ⟨13, 2, 0, 548681, 300182, 2133, 16384⟩
    (by decide) selected_cut_21434

theorem selected_cut_21435 : selected 8 ⟨548692, by decide⟩
    (prefixPartial 13 300183) = some ⟨13, 2, 0, 548692, 300183, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_300183_548692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300183 ⟨548692, by decide⟩ :=
  accepted_of_selected 13 300183 ⟨548692, by decide⟩ ⟨13, 2, 0, 548692, 300183, 1097, 16384⟩
    (by decide) selected_cut_21435

theorem unmarked_context_12_75045_548693 : frontier 9 ⟨548693, by decide⟩
    (prefixCache 12 75045) (prefixPartial 12 75045) = false := by
  decide +kernel

theorem node_context_12_75045_548693 : EJMOriginalGlobalDAGData.nodes 9 ⟨548693, by decide⟩ =
    .split (coordinate 12) (![⟨548609, by decide⟩,⟨548645, by decide⟩,⟨548681, by decide⟩,⟨548692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75045_548693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75045 ⟨548693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75045
    ⟨548693, by decide⟩ (by decide) (![⟨548609, by decide⟩,⟨548645, by decide⟩,⟨548681, by decide⟩,⟨548692, by decide⟩]) unmarked_context_12_75045_548693 node_context_12_75045_548693
  intro a
  fin_cases a
  · exact context_13_300180_548609
  · exact context_13_300181_548645
  · exact context_13_300182_548681
  · exact context_13_300183_548692

theorem selected_cut_21436 : selected 8 ⟨548719, by decide⟩
    (prefixPartial 13 300184) = some ⟨13, 2, 0, 548719, 300184, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_300184_548719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300184 ⟨548719, by decide⟩ :=
  accepted_of_selected 13 300184 ⟨548719, by decide⟩ ⟨13, 2, 0, 548719, 300184, 1225, 16384⟩
    (by decide) selected_cut_21436

theorem selected_cut_21437 : selected 8 ⟨548740, by decide⟩
    (prefixPartial 13 300185) = some ⟨13, 2, 0, 548740, 300185, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_300185_548740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300185 ⟨548740, by decide⟩ :=
  accepted_of_selected 13 300185 ⟨548740, by decide⟩ ⟨13, 2, 0, 548740, 300185, 1565, 16384⟩
    (by decide) selected_cut_21437

theorem selected_cut_21438 : selected 8 ⟨548761, by decide⟩
    (prefixPartial 13 300186) = some ⟨13, 2, 0, 548761, 300186, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_300186_548761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300186 ⟨548761, by decide⟩ :=
  accepted_of_selected 13 300186 ⟨548761, by decide⟩ ⟨13, 2, 0, 548761, 300186, 1241, 16384⟩
    (by decide) selected_cut_21438

theorem selected_cut_21439 : selected 8 ⟨548770, by decide⟩
    (prefixPartial 13 300187) = some ⟨13, 2, 0, 548770, 300187, 889, 16384⟩ := by
  decide +kernel

theorem context_13_300187_548770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300187 ⟨548770, by decide⟩ :=
  accepted_of_selected 13 300187 ⟨548770, by decide⟩ ⟨13, 2, 0, 548770, 300187, 889, 16384⟩
    (by decide) selected_cut_21439

theorem unmarked_context_12_75046_548771 : frontier 9 ⟨548771, by decide⟩
    (prefixCache 12 75046) (prefixPartial 12 75046) = false := by
  decide +kernel

theorem node_context_12_75046_548771 : EJMOriginalGlobalDAGData.nodes 9 ⟨548771, by decide⟩ =
    .split (coordinate 12) (![⟨548719, by decide⟩,⟨548740, by decide⟩,⟨548761, by decide⟩,⟨548770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75046_548771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75046 ⟨548771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75046
    ⟨548771, by decide⟩ (by decide) (![⟨548719, by decide⟩,⟨548740, by decide⟩,⟨548761, by decide⟩,⟨548770, by decide⟩]) unmarked_context_12_75046_548771 node_context_12_75046_548771
  intro a
  fin_cases a
  · exact context_13_300184_548719
  · exact context_13_300185_548740
  · exact context_13_300186_548761
  · exact context_13_300187_548770

theorem selected_cut_21440 : selected 8 ⟨548805, by decide⟩
    (prefixPartial 13 300188) = some ⟨13, 2, 0, 548805, 300188, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_300188_548805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300188 ⟨548805, by decide⟩ :=
  accepted_of_selected 13 300188 ⟨548805, by decide⟩ ⟨13, 2, 0, 548805, 300188, 1457, 16384⟩
    (by decide) selected_cut_21440

theorem selected_cut_21441 : selected 8 ⟨548826, by decide⟩
    (prefixPartial 13 300189) = some ⟨13, 2, 0, 548826, 300189, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_300189_548826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300189 ⟨548826, by decide⟩ :=
  accepted_of_selected 13 300189 ⟨548826, by decide⟩ ⟨13, 2, 0, 548826, 300189, 1853, 16384⟩
    (by decide) selected_cut_21441

theorem selected_cut_21442 : selected 8 ⟨548858, by decide⟩
    (prefixPartial 13 300190) = some ⟨13, 2, 0, 548858, 300190, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_300190_548858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300190 ⟨548858, by decide⟩ :=
  accepted_of_selected 13 300190 ⟨548858, by decide⟩ ⟨13, 2, 0, 548858, 300190, 1785, 16384⟩
    (by decide) selected_cut_21442

theorem selected_cut_21443 : selected 8 ⟨548868, by decide⟩
    (prefixPartial 13 300191) = some ⟨13, 2, 0, 548868, 300191, 921, 16384⟩ := by
  decide +kernel

theorem context_13_300191_548868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300191 ⟨548868, by decide⟩ :=
  accepted_of_selected 13 300191 ⟨548868, by decide⟩ ⟨13, 2, 0, 548868, 300191, 921, 16384⟩
    (by decide) selected_cut_21443

theorem unmarked_context_12_75047_548869 : frontier 9 ⟨548869, by decide⟩
    (prefixCache 12 75047) (prefixPartial 12 75047) = false := by
  decide +kernel

theorem node_context_12_75047_548869 : EJMOriginalGlobalDAGData.nodes 9 ⟨548869, by decide⟩ =
    .split (coordinate 12) (![⟨548805, by decide⟩,⟨548826, by decide⟩,⟨548858, by decide⟩,⟨548868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75047_548869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75047 ⟨548869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75047
    ⟨548869, by decide⟩ (by decide) (![⟨548805, by decide⟩,⟨548826, by decide⟩,⟨548858, by decide⟩,⟨548868, by decide⟩]) unmarked_context_12_75047_548869 node_context_12_75047_548869
  intro a
  fin_cases a
  · exact context_13_300188_548805
  · exact context_13_300189_548826
  · exact context_13_300190_548858
  · exact context_13_300191_548868

theorem unmarked_context_11_18761_548870 : frontier 10 ⟨548870, by decide⟩
    (prefixCache 11 18761) (prefixPartial 11 18761) = false := by
  decide +kernel

theorem node_context_11_18761_548870 : EJMOriginalGlobalDAGData.nodes 10 ⟨548870, by decide⟩ =
    .split (coordinate 11) (![⟨548565, by decide⟩,⟨548693, by decide⟩,⟨548771, by decide⟩,⟨548869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18761_548870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18761 ⟨548870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18761
    ⟨548870, by decide⟩ (by decide) (![⟨548565, by decide⟩,⟨548693, by decide⟩,⟨548771, by decide⟩,⟨548869, by decide⟩]) unmarked_context_11_18761_548870 node_context_11_18761_548870
  intro a
  fin_cases a
  · exact context_12_75044_548565
  · exact context_12_75045_548693
  · exact context_12_75046_548771
  · exact context_12_75047_548869

theorem selected_cut_21444 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 75048) = some ⟨12, 1, 0, 435790, 75048, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75048_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75048 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 75048 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 75048, 1, 65536⟩
    (by decide) selected_cut_21444

theorem selected_cut_21445 : selected 8 ⟨548891, by decide⟩
    (prefixPartial 13 300196) = some ⟨13, 2, 0, 548891, 300196, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_300196_548891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300196 ⟨548891, by decide⟩ :=
  accepted_of_selected 13 300196 ⟨548891, by decide⟩ ⟨13, 2, 0, 548891, 300196, 1045, 16384⟩
    (by decide) selected_cut_21445

theorem selected_cut_21446 : selected 8 ⟨548915, by decide⟩
    (prefixPartial 13 300197) = some ⟨13, 2, 0, 548915, 300197, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_300197_548915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300197 ⟨548915, by decide⟩ :=
  accepted_of_selected 13 300197 ⟨548915, by decide⟩ ⟨13, 2, 0, 548915, 300197, 1689, 16384⟩
    (by decide) selected_cut_21446

theorem selected_cut_21447 : selected 8 ⟨548937, by decide⟩
    (prefixPartial 13 300198) = some ⟨13, 2, 0, 548937, 300198, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_300198_548937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300198 ⟨548937, by decide⟩ :=
  accepted_of_selected 13 300198 ⟨548937, by decide⟩ ⟨13, 2, 0, 548937, 300198, 1601, 16384⟩
    (by decide) selected_cut_21447

theorem selected_cut_21448 : selected 8 ⟨548944, by decide⟩
    (prefixPartial 13 300199) = some ⟨13, 2, 0, 548944, 300199, 881, 16384⟩ := by
  decide +kernel

theorem context_13_300199_548944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300199 ⟨548944, by decide⟩ :=
  accepted_of_selected 13 300199 ⟨548944, by decide⟩ ⟨13, 2, 0, 548944, 300199, 881, 16384⟩
    (by decide) selected_cut_21448

theorem unmarked_context_12_75049_548945 : frontier 9 ⟨548945, by decide⟩
    (prefixCache 12 75049) (prefixPartial 12 75049) = false := by
  decide +kernel

theorem node_context_12_75049_548945 : EJMOriginalGlobalDAGData.nodes 9 ⟨548945, by decide⟩ =
    .split (coordinate 12) (![⟨548891, by decide⟩,⟨548915, by decide⟩,⟨548937, by decide⟩,⟨548944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75049_548945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75049 ⟨548945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75049
    ⟨548945, by decide⟩ (by decide) (![⟨548891, by decide⟩,⟨548915, by decide⟩,⟨548937, by decide⟩,⟨548944, by decide⟩]) unmarked_context_12_75049_548945 node_context_12_75049_548945
  intro a
  fin_cases a
  · exact context_13_300196_548891
  · exact context_13_300197_548915
  · exact context_13_300198_548937
  · exact context_13_300199_548944

theorem selected_cut_21449 : selected 8 ⟨548967, by decide⟩
    (prefixPartial 13 300200) = some ⟨13, 2, 0, 548967, 300200, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_300200_548967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300200 ⟨548967, by decide⟩ :=
  accepted_of_selected 13 300200 ⟨548967, by decide⟩ ⟨13, 2, 0, 548967, 300200, 1041, 16384⟩
    (by decide) selected_cut_21449

theorem selected_cut_21450 : selected 8 ⟨548990, by decide⟩
    (prefixPartial 13 300201) = some ⟨13, 2, 0, 548990, 300201, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_300201_548990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300201 ⟨548990, by decide⟩ :=
  accepted_of_selected 13 300201 ⟨548990, by decide⟩ ⟨13, 2, 0, 548990, 300201, 1797, 16384⟩
    (by decide) selected_cut_21450

theorem selected_cut_21451 : selected 8 ⟨549009, by decide⟩
    (prefixPartial 13 300202) = some ⟨13, 2, 0, 549009, 300202, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_300202_549009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300202 ⟨549009, by decide⟩ :=
  accepted_of_selected 13 300202 ⟨549009, by decide⟩ ⟨13, 2, 0, 549009, 300202, 1489, 16384⟩
    (by decide) selected_cut_21451

theorem selected_cut_21452 : selected 8 ⟨549017, by decide⟩
    (prefixPartial 13 300203) = some ⟨13, 2, 0, 549017, 300203, 929, 16384⟩ := by
  decide +kernel

theorem context_13_300203_549017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300203 ⟨549017, by decide⟩ :=
  accepted_of_selected 13 300203 ⟨549017, by decide⟩ ⟨13, 2, 0, 549017, 300203, 929, 16384⟩
    (by decide) selected_cut_21452

theorem unmarked_context_12_75050_549018 : frontier 9 ⟨549018, by decide⟩
    (prefixCache 12 75050) (prefixPartial 12 75050) = false := by
  decide +kernel

theorem node_context_12_75050_549018 : EJMOriginalGlobalDAGData.nodes 9 ⟨549018, by decide⟩ =
    .split (coordinate 12) (![⟨548967, by decide⟩,⟨548990, by decide⟩,⟨549009, by decide⟩,⟨549017, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75050_549018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75050 ⟨549018, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75050
    ⟨549018, by decide⟩ (by decide) (![⟨548967, by decide⟩,⟨548990, by decide⟩,⟨549009, by decide⟩,⟨549017, by decide⟩]) unmarked_context_12_75050_549018 node_context_12_75050_549018
  intro a
  fin_cases a
  · exact context_13_300200_548967
  · exact context_13_300201_548990
  · exact context_13_300202_549009
  · exact context_13_300203_549017

theorem selected_cut_21453 : selected 8 ⟨549043, by decide⟩
    (prefixPartial 13 300204) = some ⟨13, 2, 0, 549043, 300204, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_300204_549043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300204 ⟨549043, by decide⟩ :=
  accepted_of_selected 13 300204 ⟨549043, by decide⟩ ⟨13, 2, 0, 549043, 300204, 1221, 16384⟩
    (by decide) selected_cut_21453

theorem selected_cut_21454 : selected 8 ⟨549069, by decide⟩
    (prefixPartial 13 300205) = some ⟨13, 2, 0, 549069, 300205, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_300205_549069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300205 ⟨549069, by decide⟩ :=
  accepted_of_selected 13 300205 ⟨549069, by decide⟩ ⟨13, 2, 0, 549069, 300205, 2209, 16384⟩
    (by decide) selected_cut_21454

theorem selected_cut_21455 : selected 8 ⟨549098, by decide⟩
    (prefixPartial 13 300206) = some ⟨13, 2, 0, 549098, 300206, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_300206_549098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300206 ⟨549098, by decide⟩ :=
  accepted_of_selected 13 300206 ⟨549098, by decide⟩ ⟨13, 2, 0, 549098, 300206, 1973, 16384⟩
    (by decide) selected_cut_21455

theorem selected_cut_21456 : selected 8 ⟨549105, by decide⟩
    (prefixPartial 13 300207) = some ⟨13, 2, 0, 549105, 300207, 981, 16384⟩ := by
  decide +kernel

theorem context_13_300207_549105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300207 ⟨549105, by decide⟩ :=
  accepted_of_selected 13 300207 ⟨549105, by decide⟩ ⟨13, 2, 0, 549105, 300207, 981, 16384⟩
    (by decide) selected_cut_21456

theorem unmarked_context_12_75051_549106 : frontier 9 ⟨549106, by decide⟩
    (prefixCache 12 75051) (prefixPartial 12 75051) = false := by
  decide +kernel

theorem node_context_12_75051_549106 : EJMOriginalGlobalDAGData.nodes 9 ⟨549106, by decide⟩ =
    .split (coordinate 12) (![⟨549043, by decide⟩,⟨549069, by decide⟩,⟨549098, by decide⟩,⟨549105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75051_549106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75051 ⟨549106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75051
    ⟨549106, by decide⟩ (by decide) (![⟨549043, by decide⟩,⟨549069, by decide⟩,⟨549098, by decide⟩,⟨549105, by decide⟩]) unmarked_context_12_75051_549106 node_context_12_75051_549106
  intro a
  fin_cases a
  · exact context_13_300204_549043
  · exact context_13_300205_549069
  · exact context_13_300206_549098
  · exact context_13_300207_549105

theorem unmarked_context_11_18762_549107 : frontier 10 ⟨549107, by decide⟩
    (prefixCache 11 18762) (prefixPartial 11 18762) = false := by
  decide +kernel

theorem node_context_11_18762_549107 : EJMOriginalGlobalDAGData.nodes 10 ⟨549107, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨548945, by decide⟩,⟨549018, by decide⟩,⟨549106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18762_549107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18762 ⟨549107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18762
    ⟨549107, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨548945, by decide⟩,⟨549018, by decide⟩,⟨549106, by decide⟩]) unmarked_context_11_18762_549107 node_context_11_18762_549107
  intro a
  fin_cases a
  · exact context_12_75048_435790
  · exact context_12_75049_548945
  · exact context_12_75050_549018
  · exact context_12_75051_549106

theorem selected_cut_21457 : selected 8 ⟨549132, by decide⟩
    (prefixPartial 13 300208) = some ⟨13, 2, 0, 549132, 300208, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_300208_549132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300208 ⟨549132, by decide⟩ :=
  accepted_of_selected 13 300208 ⟨549132, by decide⟩ ⟨13, 2, 0, 549132, 300208, 1193, 16384⟩
    (by decide) selected_cut_21457

theorem selected_cut_21458 : selected 8 ⟨549187, by decide⟩
    (prefixPartial 13 300209) = some ⟨13, 2, 0, 549187, 300209, 3245, 16384⟩ := by
  decide +kernel

theorem context_13_300209_549187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300209 ⟨549187, by decide⟩ :=
  accepted_of_selected 13 300209 ⟨549187, by decide⟩ ⟨13, 2, 0, 549187, 300209, 3245, 16384⟩
    (by decide) selected_cut_21458

theorem selected_cut_21459 : selected 8 ⟨549243, by decide⟩
    (prefixPartial 13 300210) = some ⟨13, 2, 0, 549243, 300210, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_300210_549243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300210 ⟨549243, by decide⟩ :=
  accepted_of_selected 13 300210 ⟨549243, by decide⟩ ⟨13, 2, 0, 549243, 300210, 2525, 16384⟩
    (by decide) selected_cut_21459

theorem selected_cut_21460 : selected 8 ⟨549257, by decide⟩
    (prefixPartial 13 300211) = some ⟨13, 2, 0, 549257, 300211, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_300211_549257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300211 ⟨549257, by decide⟩ :=
  accepted_of_selected 13 300211 ⟨549257, by decide⟩ ⟨13, 2, 0, 549257, 300211, 1189, 16384⟩
    (by decide) selected_cut_21460

theorem unmarked_context_12_75052_549258 : frontier 9 ⟨549258, by decide⟩
    (prefixCache 12 75052) (prefixPartial 12 75052) = false := by
  decide +kernel

theorem node_context_12_75052_549258 : EJMOriginalGlobalDAGData.nodes 9 ⟨549258, by decide⟩ =
    .split (coordinate 12) (![⟨549132, by decide⟩,⟨549187, by decide⟩,⟨549243, by decide⟩,⟨549257, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75052_549258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75052 ⟨549258, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75052
    ⟨549258, by decide⟩ (by decide) (![⟨549132, by decide⟩,⟨549187, by decide⟩,⟨549243, by decide⟩,⟨549257, by decide⟩]) unmarked_context_12_75052_549258 node_context_12_75052_549258
  intro a
  fin_cases a
  · exact context_13_300208_549132
  · exact context_13_300209_549187
  · exact context_13_300210_549243
  · exact context_13_300211_549257

theorem selected_cut_21461 : selected 8 ⟨549271, by decide⟩
    (prefixPartial 13 300212) = some ⟨13, 2, 0, 549271, 300212, 717, 16384⟩ := by
  decide +kernel

theorem context_13_300212_549271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300212 ⟨549271, by decide⟩ :=
  accepted_of_selected 13 300212 ⟨549271, by decide⟩ ⟨13, 2, 0, 549271, 300212, 717, 16384⟩
    (by decide) selected_cut_21461

theorem selected_cut_21462 : selected 8 ⟨549294, by decide⟩
    (prefixPartial 13 300213) = some ⟨13, 2, 0, 549294, 300213, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_300213_549294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300213 ⟨549294, by decide⟩ :=
  accepted_of_selected 13 300213 ⟨549294, by decide⟩ ⟨13, 2, 0, 549294, 300213, 1921, 16384⟩
    (by decide) selected_cut_21462

theorem selected_cut_21463 : selected 8 ⟨549315, by decide⟩
    (prefixPartial 13 300214) = some ⟨13, 2, 0, 549315, 300214, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_300214_549315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300214 ⟨549315, by decide⟩ :=
  accepted_of_selected 13 300214 ⟨549315, by decide⟩ ⟨13, 2, 0, 549315, 300214, 1553, 16384⟩
    (by decide) selected_cut_21463

theorem selected_cut_21464 : selected 8 ⟨549323, by decide⟩
    (prefixPartial 13 300215) = some ⟨13, 2, 0, 549323, 300215, 737, 16384⟩ := by
  decide +kernel

theorem context_13_300215_549323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300215 ⟨549323, by decide⟩ :=
  accepted_of_selected 13 300215 ⟨549323, by decide⟩ ⟨13, 2, 0, 549323, 300215, 737, 16384⟩
    (by decide) selected_cut_21464

theorem unmarked_context_12_75053_549324 : frontier 9 ⟨549324, by decide⟩
    (prefixCache 12 75053) (prefixPartial 12 75053) = false := by
  decide +kernel

theorem node_context_12_75053_549324 : EJMOriginalGlobalDAGData.nodes 9 ⟨549324, by decide⟩ =
    .split (coordinate 12) (![⟨549271, by decide⟩,⟨549294, by decide⟩,⟨549315, by decide⟩,⟨549323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75053_549324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75053 ⟨549324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75053
    ⟨549324, by decide⟩ (by decide) (![⟨549271, by decide⟩,⟨549294, by decide⟩,⟨549315, by decide⟩,⟨549323, by decide⟩]) unmarked_context_12_75053_549324 node_context_12_75053_549324
  intro a
  fin_cases a
  · exact context_13_300212_549271
  · exact context_13_300213_549294
  · exact context_13_300214_549315
  · exact context_13_300215_549323

theorem selected_cut_21465 : selected 8 ⟨549340, by decide⟩
    (prefixPartial 13 300216) = some ⟨13, 2, 0, 549340, 300216, 849, 16384⟩ := by
  decide +kernel

theorem context_13_300216_549340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300216 ⟨549340, by decide⟩ :=
  accepted_of_selected 13 300216 ⟨549340, by decide⟩ ⟨13, 2, 0, 549340, 300216, 849, 16384⟩
    (by decide) selected_cut_21465

theorem selected_cut_21466 : selected 8 ⟨549364, by decide⟩
    (prefixPartial 13 300217) = some ⟨13, 2, 0, 549364, 300217, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_300217_549364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300217 ⟨549364, by decide⟩ :=
  accepted_of_selected 13 300217 ⟨549364, by decide⟩ ⟨13, 2, 0, 549364, 300217, 2205, 16384⟩
    (by decide) selected_cut_21466

theorem selected_cut_21467 : selected 8 ⟨549386, by decide⟩
    (prefixPartial 13 300218) = some ⟨13, 2, 0, 549386, 300218, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_300218_549386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300218 ⟨549386, by decide⟩ :=
  accepted_of_selected 13 300218 ⟨549386, by decide⟩ ⟨13, 2, 0, 549386, 300218, 1565, 16384⟩
    (by decide) selected_cut_21467

theorem selected_cut_21468 : selected 8 ⟨549394, by decide⟩
    (prefixPartial 13 300219) = some ⟨13, 2, 0, 549394, 300219, 901, 16384⟩ := by
  decide +kernel

theorem context_13_300219_549394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300219 ⟨549394, by decide⟩ :=
  accepted_of_selected 13 300219 ⟨549394, by decide⟩ ⟨13, 2, 0, 549394, 300219, 901, 16384⟩
    (by decide) selected_cut_21468

theorem unmarked_context_12_75054_549395 : frontier 9 ⟨549395, by decide⟩
    (prefixCache 12 75054) (prefixPartial 12 75054) = false := by
  decide +kernel

theorem node_context_12_75054_549395 : EJMOriginalGlobalDAGData.nodes 9 ⟨549395, by decide⟩ =
    .split (coordinate 12) (![⟨549340, by decide⟩,⟨549364, by decide⟩,⟨549386, by decide⟩,⟨549394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75054_549395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75054 ⟨549395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75054
    ⟨549395, by decide⟩ (by decide) (![⟨549340, by decide⟩,⟨549364, by decide⟩,⟨549386, by decide⟩,⟨549394, by decide⟩]) unmarked_context_12_75054_549395 node_context_12_75054_549395
  intro a
  fin_cases a
  · exact context_13_300216_549340
  · exact context_13_300217_549364
  · exact context_13_300218_549386
  · exact context_13_300219_549394

theorem selected_cut_21469 : selected 8 ⟨549413, by decide⟩
    (prefixPartial 13 300220) = some ⟨13, 2, 0, 549413, 300220, 961, 16384⟩ := by
  decide +kernel

theorem context_13_300220_549413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300220 ⟨549413, by decide⟩ :=
  accepted_of_selected 13 300220 ⟨549413, by decide⟩ ⟨13, 2, 0, 549413, 300220, 961, 16384⟩
    (by decide) selected_cut_21469

theorem selected_cut_21470 : selected 8 ⟨549438, by decide⟩
    (prefixPartial 13 300221) = some ⟨13, 2, 0, 549438, 300221, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_300221_549438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300221 ⟨549438, by decide⟩ :=
  accepted_of_selected 13 300221 ⟨549438, by decide⟩ ⟨13, 2, 0, 549438, 300221, 2521, 16384⟩
    (by decide) selected_cut_21470

theorem selected_cut_21471 : selected 8 ⟨549468, by decide⟩
    (prefixPartial 13 300222) = some ⟨13, 2, 0, 549468, 300222, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_300222_549468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300222 ⟨549468, by decide⟩ :=
  accepted_of_selected 13 300222 ⟨549468, by decide⟩ ⟨13, 2, 0, 549468, 300222, 2057, 16384⟩
    (by decide) selected_cut_21471

theorem selected_cut_21472 : selected 8 ⟨549478, by decide⟩
    (prefixPartial 13 300223) = some ⟨13, 2, 0, 549478, 300223, 937, 16384⟩ := by
  decide +kernel

theorem context_13_300223_549478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300223 ⟨549478, by decide⟩ :=
  accepted_of_selected 13 300223 ⟨549478, by decide⟩ ⟨13, 2, 0, 549478, 300223, 937, 16384⟩
    (by decide) selected_cut_21472

theorem unmarked_context_12_75055_549479 : frontier 9 ⟨549479, by decide⟩
    (prefixCache 12 75055) (prefixPartial 12 75055) = false := by
  decide +kernel

theorem node_context_12_75055_549479 : EJMOriginalGlobalDAGData.nodes 9 ⟨549479, by decide⟩ =
    .split (coordinate 12) (![⟨549413, by decide⟩,⟨549438, by decide⟩,⟨549468, by decide⟩,⟨549478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75055_549479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75055 ⟨549479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75055
    ⟨549479, by decide⟩ (by decide) (![⟨549413, by decide⟩,⟨549438, by decide⟩,⟨549468, by decide⟩,⟨549478, by decide⟩]) unmarked_context_12_75055_549479 node_context_12_75055_549479
  intro a
  fin_cases a
  · exact context_13_300220_549413
  · exact context_13_300221_549438
  · exact context_13_300222_549468
  · exact context_13_300223_549478

theorem unmarked_context_11_18763_549480 : frontier 10 ⟨549480, by decide⟩
    (prefixCache 11 18763) (prefixPartial 11 18763) = false := by
  decide +kernel

theorem node_context_11_18763_549480 : EJMOriginalGlobalDAGData.nodes 10 ⟨549480, by decide⟩ =
    .split (coordinate 11) (![⟨549258, by decide⟩,⟨549324, by decide⟩,⟨549395, by decide⟩,⟨549479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18763_549480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18763 ⟨549480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18763
    ⟨549480, by decide⟩ (by decide) (![⟨549258, by decide⟩,⟨549324, by decide⟩,⟨549395, by decide⟩,⟨549479, by decide⟩]) unmarked_context_11_18763_549480 node_context_11_18763_549480
  intro a
  fin_cases a
  · exact context_12_75052_549258
  · exact context_12_75053_549324
  · exact context_12_75054_549395
  · exact context_12_75055_549479

theorem unmarked_context_10_4690_549481 : frontier 11 ⟨549481, by decide⟩
    (prefixCache 10 4690) (prefixPartial 10 4690) = false := by
  decide +kernel

theorem node_context_10_4690_549481 : EJMOriginalGlobalDAGData.nodes 11 ⟨549481, by decide⟩ =
    .split (coordinate 10) (![⟨548434, by decide⟩,⟨548870, by decide⟩,⟨549107, by decide⟩,⟨549480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4690_549481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4690 ⟨549481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4690
    ⟨549481, by decide⟩ (by decide) (![⟨548434, by decide⟩,⟨548870, by decide⟩,⟨549107, by decide⟩,⟨549480, by decide⟩]) unmarked_context_10_4690_549481 node_context_10_4690_549481
  intro a
  fin_cases a
  · exact context_11_18760_548434
  · exact context_11_18761_548870
  · exact context_11_18762_549107
  · exact context_11_18763_549480

theorem selected_cut_21473 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 75056) = some ⟨12, 1, 0, 445562, 75056, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75056_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75056 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 75056 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 75056, 1, 65536⟩
    (by decide) selected_cut_21473

theorem selected_cut_21474 : selected 8 ⟨549492, by decide⟩
    (prefixPartial 13 300228) = some ⟨13, 2, 0, 549492, 300228, 661, 16384⟩ := by
  decide +kernel

theorem context_13_300228_549492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300228 ⟨549492, by decide⟩ :=
  accepted_of_selected 13 300228 ⟨549492, by decide⟩ ⟨13, 2, 0, 549492, 300228, 661, 16384⟩
    (by decide) selected_cut_21474

theorem selected_cut_21475 : selected 8 ⟨549517, by decide⟩
    (prefixPartial 13 300229) = some ⟨13, 2, 0, 549517, 300229, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_300229_549517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300229 ⟨549517, by decide⟩ :=
  accepted_of_selected 13 300229 ⟨549517, by decide⟩ ⟨13, 2, 0, 549517, 300229, 2025, 16384⟩
    (by decide) selected_cut_21475

theorem selected_cut_21476 : selected 8 ⟨549536, by decide⟩
    (prefixPartial 13 300230) = some ⟨13, 2, 0, 549536, 300230, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_300230_549536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300230 ⟨549536, by decide⟩ :=
  accepted_of_selected 13 300230 ⟨549536, by decide⟩ ⟨13, 2, 0, 549536, 300230, 1445, 16384⟩
    (by decide) selected_cut_21476

theorem selected_cut_21477 : selected 8 ⟨549542, by decide⟩
    (prefixPartial 13 300231) = some ⟨13, 2, 0, 549542, 300231, 785, 16384⟩ := by
  decide +kernel

theorem context_13_300231_549542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300231 ⟨549542, by decide⟩ :=
  accepted_of_selected 13 300231 ⟨549542, by decide⟩ ⟨13, 2, 0, 549542, 300231, 785, 16384⟩
    (by decide) selected_cut_21477

theorem unmarked_context_12_75057_549543 : frontier 9 ⟨549543, by decide⟩
    (prefixCache 12 75057) (prefixPartial 12 75057) = false := by
  decide +kernel

theorem node_context_12_75057_549543 : EJMOriginalGlobalDAGData.nodes 9 ⟨549543, by decide⟩ =
    .split (coordinate 12) (![⟨549492, by decide⟩,⟨549517, by decide⟩,⟨549536, by decide⟩,⟨549542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75057_549543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75057 ⟨549543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75057
    ⟨549543, by decide⟩ (by decide) (![⟨549492, by decide⟩,⟨549517, by decide⟩,⟨549536, by decide⟩,⟨549542, by decide⟩]) unmarked_context_12_75057_549543 node_context_12_75057_549543
  intro a
  fin_cases a
  · exact context_13_300228_549492
  · exact context_13_300229_549517
  · exact context_13_300230_549536
  · exact context_13_300231_549542

theorem selected_cut_21478 : selected 8 ⟨549558, by decide⟩
    (prefixPartial 13 300232) = some ⟨13, 2, 0, 549558, 300232, 857, 16384⟩ := by
  decide +kernel

theorem context_13_300232_549558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300232 ⟨549558, by decide⟩ :=
  accepted_of_selected 13 300232 ⟨549558, by decide⟩ ⟨13, 2, 0, 549558, 300232, 857, 16384⟩
    (by decide) selected_cut_21478

theorem selected_cut_21479 : selected 8 ⟨549586, by decide⟩
    (prefixPartial 13 300233) = some ⟨13, 2, 0, 549586, 300233, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_300233_549586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300233 ⟨549586, by decide⟩ :=
  accepted_of_selected 13 300233 ⟨549586, by decide⟩ ⟨13, 2, 0, 549586, 300233, 2293, 16384⟩
    (by decide) selected_cut_21479

theorem selected_cut_21480 : selected 8 ⟨549611, by decide⟩
    (prefixPartial 13 300234) = some ⟨13, 2, 0, 549611, 300234, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_300234_549611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300234 ⟨549611, by decide⟩ :=
  accepted_of_selected 13 300234 ⟨549611, by decide⟩ ⟨13, 2, 0, 549611, 300234, 1713, 16384⟩
    (by decide) selected_cut_21480

theorem selected_cut_21481 : selected 8 ⟨549625, by decide⟩
    (prefixPartial 13 300235) = some ⟨13, 2, 0, 549625, 300235, 929, 16384⟩ := by
  decide +kernel

theorem context_13_300235_549625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300235 ⟨549625, by decide⟩ :=
  accepted_of_selected 13 300235 ⟨549625, by decide⟩ ⟨13, 2, 0, 549625, 300235, 929, 16384⟩
    (by decide) selected_cut_21481

theorem unmarked_context_12_75058_549626 : frontier 9 ⟨549626, by decide⟩
    (prefixCache 12 75058) (prefixPartial 12 75058) = false := by
  decide +kernel

theorem node_context_12_75058_549626 : EJMOriginalGlobalDAGData.nodes 9 ⟨549626, by decide⟩ =
    .split (coordinate 12) (![⟨549558, by decide⟩,⟨549586, by decide⟩,⟨549611, by decide⟩,⟨549625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75058_549626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75058 ⟨549626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75058
    ⟨549626, by decide⟩ (by decide) (![⟨549558, by decide⟩,⟨549586, by decide⟩,⟨549611, by decide⟩,⟨549625, by decide⟩]) unmarked_context_12_75058_549626 node_context_12_75058_549626
  intro a
  fin_cases a
  · exact context_13_300232_549558
  · exact context_13_300233_549586
  · exact context_13_300234_549611
  · exact context_13_300235_549625

theorem selected_cut_21482 : selected 8 ⟨549642, by decide⟩
    (prefixPartial 13 300236) = some ⟨13, 2, 0, 549642, 300236, 849, 16384⟩ := by
  decide +kernel

theorem context_13_300236_549642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300236 ⟨549642, by decide⟩ :=
  accepted_of_selected 13 300236 ⟨549642, by decide⟩ ⟨13, 2, 0, 549642, 300236, 849, 16384⟩
    (by decide) selected_cut_21482

theorem selected_cut_21483 : selected 8 ⟨549676, by decide⟩
    (prefixPartial 13 300237) = some ⟨13, 2, 0, 549676, 300237, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_300237_549676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300237 ⟨549676, by decide⟩ :=
  accepted_of_selected 13 300237 ⟨549676, by decide⟩ ⟨13, 2, 0, 549676, 300237, 2589, 16384⟩
    (by decide) selected_cut_21483

theorem selected_cut_21484 : selected 8 ⟨549699, by decide⟩
    (prefixPartial 13 300238) = some ⟨13, 2, 0, 549699, 300238, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_300238_549699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300238 ⟨549699, by decide⟩ :=
  accepted_of_selected 13 300238 ⟨549699, by decide⟩ ⟨13, 2, 0, 549699, 300238, 1789, 16384⟩
    (by decide) selected_cut_21484

theorem selected_cut_21485 : selected 8 ⟨549708, by decide⟩
    (prefixPartial 13 300239) = some ⟨13, 2, 0, 549708, 300239, 913, 16384⟩ := by
  decide +kernel

theorem context_13_300239_549708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300239 ⟨549708, by decide⟩ :=
  accepted_of_selected 13 300239 ⟨549708, by decide⟩ ⟨13, 2, 0, 549708, 300239, 913, 16384⟩
    (by decide) selected_cut_21485

theorem unmarked_context_12_75059_549709 : frontier 9 ⟨549709, by decide⟩
    (prefixCache 12 75059) (prefixPartial 12 75059) = false := by
  decide +kernel

theorem node_context_12_75059_549709 : EJMOriginalGlobalDAGData.nodes 9 ⟨549709, by decide⟩ =
    .split (coordinate 12) (![⟨549642, by decide⟩,⟨549676, by decide⟩,⟨549699, by decide⟩,⟨549708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75059_549709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75059 ⟨549709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75059
    ⟨549709, by decide⟩ (by decide) (![⟨549642, by decide⟩,⟨549676, by decide⟩,⟨549699, by decide⟩,⟨549708, by decide⟩]) unmarked_context_12_75059_549709 node_context_12_75059_549709
  intro a
  fin_cases a
  · exact context_13_300236_549642
  · exact context_13_300237_549676
  · exact context_13_300238_549699
  · exact context_13_300239_549708

theorem unmarked_context_11_18764_549710 : frontier 10 ⟨549710, by decide⟩
    (prefixCache 11 18764) (prefixPartial 11 18764) = false := by
  decide +kernel

theorem node_context_11_18764_549710 : EJMOriginalGlobalDAGData.nodes 10 ⟨549710, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨549543, by decide⟩,⟨549626, by decide⟩,⟨549709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18764_549710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18764 ⟨549710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18764
    ⟨549710, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨549543, by decide⟩,⟨549626, by decide⟩,⟨549709, by decide⟩]) unmarked_context_11_18764_549710 node_context_11_18764_549710
  intro a
  fin_cases a
  · exact context_12_75056_445562
  · exact context_12_75057_549543
  · exact context_12_75058_549626
  · exact context_12_75059_549709

theorem selected_cut_21486 : selected 8 ⟨549729, by decide⟩
    (prefixPartial 13 300240) = some ⟨13, 2, 0, 549729, 300240, 833, 16384⟩ := by
  decide +kernel

theorem context_13_300240_549729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300240 ⟨549729, by decide⟩ :=
  accepted_of_selected 13 300240 ⟨549729, by decide⟩ ⟨13, 2, 0, 549729, 300240, 833, 16384⟩
    (by decide) selected_cut_21486

theorem selected_cut_21487 : selected 8 ⟨549783, by decide⟩
    (prefixPartial 13 300241) = some ⟨13, 2, 0, 549783, 300241, 2857, 16384⟩ := by
  decide +kernel

theorem context_13_300241_549783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300241 ⟨549783, by decide⟩ :=
  accepted_of_selected 13 300241 ⟨549783, by decide⟩ ⟨13, 2, 0, 549783, 300241, 2857, 16384⟩
    (by decide) selected_cut_21487

theorem selected_cut_21488 : selected 8 ⟨549839, by decide⟩
    (prefixPartial 13 300242) = some ⟨13, 2, 0, 549839, 300242, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_300242_549839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300242 ⟨549839, by decide⟩ :=
  accepted_of_selected 13 300242 ⟨549839, by decide⟩ ⟨13, 2, 0, 549839, 300242, 2261, 16384⟩
    (by decide) selected_cut_21488

theorem selected_cut_21489 : selected 8 ⟨549862, by decide⟩
    (prefixPartial 13 300243) = some ⟨13, 2, 0, 549862, 300243, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_300243_549862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300243 ⟨549862, by decide⟩ :=
  accepted_of_selected 13 300243 ⟨549862, by decide⟩ ⟨13, 2, 0, 549862, 300243, 1117, 16384⟩
    (by decide) selected_cut_21489

theorem unmarked_context_12_75060_549863 : frontier 9 ⟨549863, by decide⟩
    (prefixCache 12 75060) (prefixPartial 12 75060) = false := by
  decide +kernel

theorem node_context_12_75060_549863 : EJMOriginalGlobalDAGData.nodes 9 ⟨549863, by decide⟩ =
    .split (coordinate 12) (![⟨549729, by decide⟩,⟨549783, by decide⟩,⟨549839, by decide⟩,⟨549862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75060_549863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75060 ⟨549863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75060
    ⟨549863, by decide⟩ (by decide) (![⟨549729, by decide⟩,⟨549783, by decide⟩,⟨549839, by decide⟩,⟨549862, by decide⟩]) unmarked_context_12_75060_549863 node_context_12_75060_549863
  intro a
  fin_cases a
  · exact context_13_300240_549729
  · exact context_13_300241_549783
  · exact context_13_300242_549839
  · exact context_13_300243_549862

theorem selected_cut_21490 : selected 8 ⟨549881, by decide⟩
    (prefixPartial 13 300244) = some ⟨13, 2, 0, 549881, 300244, 829, 16384⟩ := by
  decide +kernel

theorem context_13_300244_549881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300244 ⟨549881, by decide⟩ :=
  accepted_of_selected 13 300244 ⟨549881, by decide⟩ ⟨13, 2, 0, 549881, 300244, 829, 16384⟩
    (by decide) selected_cut_21490

theorem selected_cut_21491 : selected 8 ⟨549928, by decide⟩
    (prefixPartial 13 300245) = some ⟨13, 2, 0, 549928, 300245, 3117, 16384⟩ := by
  decide +kernel

theorem context_13_300245_549928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300245 ⟨549928, by decide⟩ :=
  accepted_of_selected 13 300245 ⟨549928, by decide⟩ ⟨13, 2, 0, 549928, 300245, 3117, 16384⟩
    (by decide) selected_cut_21491

theorem selected_cut_21492 : selected 8 ⟨549965, by decide⟩
    (prefixPartial 13 300246) = some ⟨13, 2, 0, 549965, 300246, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_300246_549965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300246 ⟨549965, by decide⟩ :=
  accepted_of_selected 13 300246 ⟨549965, by decide⟩ ⟨13, 2, 0, 549965, 300246, 2245, 16384⟩
    (by decide) selected_cut_21492

theorem selected_cut_21493 : selected 8 ⟨549992, by decide⟩
    (prefixPartial 13 300247) = some ⟨13, 2, 0, 549992, 300247, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_300247_549992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300247 ⟨549992, by decide⟩ :=
  accepted_of_selected 13 300247 ⟨549992, by decide⟩ ⟨13, 2, 0, 549992, 300247, 1157, 16384⟩
    (by decide) selected_cut_21493

theorem unmarked_context_12_75061_549993 : frontier 9 ⟨549993, by decide⟩
    (prefixCache 12 75061) (prefixPartial 12 75061) = false := by
  decide +kernel

theorem node_context_12_75061_549993 : EJMOriginalGlobalDAGData.nodes 9 ⟨549993, by decide⟩ =
    .split (coordinate 12) (![⟨549881, by decide⟩,⟨549928, by decide⟩,⟨549965, by decide⟩,⟨549992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75061_549993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75061 ⟨549993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75061
    ⟨549993, by decide⟩ (by decide) (![⟨549881, by decide⟩,⟨549928, by decide⟩,⟨549965, by decide⟩,⟨549992, by decide⟩]) unmarked_context_12_75061_549993 node_context_12_75061_549993
  intro a
  fin_cases a
  · exact context_13_300244_549881
  · exact context_13_300245_549928
  · exact context_13_300246_549965
  · exact context_13_300247_549992

theorem selected_cut_21494 : selected 8 ⟨550002, by decide⟩
    (prefixPartial 13 300248) = some ⟨13, 2, 0, 550002, 300248, 493, 16384⟩ := by
  decide +kernel

theorem context_13_300248_550002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300248 ⟨550002, by decide⟩ :=
  accepted_of_selected 13 300248 ⟨550002, by decide⟩ ⟨13, 2, 0, 550002, 300248, 493, 16384⟩
    (by decide) selected_cut_21494

theorem selected_cut_21495 : selected 8 ⟨550026, by decide⟩
    (prefixPartial 13 300249) = some ⟨13, 2, 0, 550026, 300249, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_300249_550026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300249 ⟨550026, by decide⟩ :=
  accepted_of_selected 13 300249 ⟨550026, by decide⟩ ⟨13, 2, 0, 550026, 300249, 1917, 16384⟩
    (by decide) selected_cut_21495

theorem selected_cut_21496 : selected 8 ⟨550046, by decide⟩
    (prefixPartial 13 300250) = some ⟨13, 2, 0, 550046, 300250, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_300250_550046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300250 ⟨550046, by decide⟩ :=
  accepted_of_selected 13 300250 ⟨550046, by decide⟩ ⟨13, 2, 0, 550046, 300250, 1501, 16384⟩
    (by decide) selected_cut_21496

theorem selected_cut_21497 : selected 8 ⟨550059, by decide⟩
    (prefixPartial 13 300251) = some ⟨13, 2, 0, 550059, 300251, 957, 16384⟩ := by
  decide +kernel

theorem context_13_300251_550059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300251 ⟨550059, by decide⟩ :=
  accepted_of_selected 13 300251 ⟨550059, by decide⟩ ⟨13, 2, 0, 550059, 300251, 957, 16384⟩
    (by decide) selected_cut_21497

theorem unmarked_context_12_75062_550060 : frontier 9 ⟨550060, by decide⟩
    (prefixCache 12 75062) (prefixPartial 12 75062) = false := by
  decide +kernel

theorem node_context_12_75062_550060 : EJMOriginalGlobalDAGData.nodes 9 ⟨550060, by decide⟩ =
    .split (coordinate 12) (![⟨550002, by decide⟩,⟨550026, by decide⟩,⟨550046, by decide⟩,⟨550059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75062_550060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75062 ⟨550060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75062
    ⟨550060, by decide⟩ (by decide) (![⟨550002, by decide⟩,⟨550026, by decide⟩,⟨550046, by decide⟩,⟨550059, by decide⟩]) unmarked_context_12_75062_550060 node_context_12_75062_550060
  intro a
  fin_cases a
  · exact context_13_300248_550002
  · exact context_13_300249_550026
  · exact context_13_300250_550046
  · exact context_13_300251_550059

theorem selected_cut_21498 : selected 8 ⟨550072, by decide⟩
    (prefixPartial 13 300252) = some ⟨13, 2, 0, 550072, 300252, 517, 16384⟩ := by
  decide +kernel

theorem context_13_300252_550072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300252 ⟨550072, by decide⟩ :=
  accepted_of_selected 13 300252 ⟨550072, by decide⟩ ⟨13, 2, 0, 550072, 300252, 517, 16384⟩
    (by decide) selected_cut_21498

theorem selected_cut_21499 : selected 8 ⟨550105, by decide⟩
    (prefixPartial 13 300253) = some ⟨13, 2, 0, 550105, 300253, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_300253_550105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300253 ⟨550105, by decide⟩ :=
  accepted_of_selected 13 300253 ⟨550105, by decide⟩ ⟨13, 2, 0, 550105, 300253, 2337, 16384⟩
    (by decide) selected_cut_21499

theorem selected_cut_21500 : selected 8 ⟨550135, by decide⟩
    (prefixPartial 13 300254) = some ⟨13, 2, 0, 550135, 300254, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_300254_550135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300254 ⟨550135, by decide⟩ :=
  accepted_of_selected 13 300254 ⟨550135, by decide⟩ ⟨13, 2, 0, 550135, 300254, 1801, 16384⟩
    (by decide) selected_cut_21500

theorem selected_cut_21501 : selected 8 ⟨550145, by decide⟩
    (prefixPartial 13 300255) = some ⟨13, 2, 0, 550145, 300255, 849, 16384⟩ := by
  decide +kernel

theorem context_13_300255_550145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300255 ⟨550145, by decide⟩ :=
  accepted_of_selected 13 300255 ⟨550145, by decide⟩ ⟨13, 2, 0, 550145, 300255, 849, 16384⟩
    (by decide) selected_cut_21501

theorem unmarked_context_12_75063_550146 : frontier 9 ⟨550146, by decide⟩
    (prefixCache 12 75063) (prefixPartial 12 75063) = false := by
  decide +kernel

theorem node_context_12_75063_550146 : EJMOriginalGlobalDAGData.nodes 9 ⟨550146, by decide⟩ =
    .split (coordinate 12) (![⟨550072, by decide⟩,⟨550105, by decide⟩,⟨550135, by decide⟩,⟨550145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75063_550146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75063 ⟨550146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75063
    ⟨550146, by decide⟩ (by decide) (![⟨550072, by decide⟩,⟨550105, by decide⟩,⟨550135, by decide⟩,⟨550145, by decide⟩]) unmarked_context_12_75063_550146 node_context_12_75063_550146
  intro a
  fin_cases a
  · exact context_13_300252_550072
  · exact context_13_300253_550105
  · exact context_13_300254_550135
  · exact context_13_300255_550145

theorem unmarked_context_11_18765_550147 : frontier 10 ⟨550147, by decide⟩
    (prefixCache 11 18765) (prefixPartial 11 18765) = false := by
  decide +kernel

theorem node_context_11_18765_550147 : EJMOriginalGlobalDAGData.nodes 10 ⟨550147, by decide⟩ =
    .split (coordinate 11) (![⟨549863, by decide⟩,⟨549993, by decide⟩,⟨550060, by decide⟩,⟨550146, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18765_550147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18765 ⟨550147, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18765
    ⟨550147, by decide⟩ (by decide) (![⟨549863, by decide⟩,⟨549993, by decide⟩,⟨550060, by decide⟩,⟨550146, by decide⟩]) unmarked_context_11_18765_550147 node_context_11_18765_550147
  intro a
  fin_cases a
  · exact context_12_75060_549863
  · exact context_12_75061_549993
  · exact context_12_75062_550060
  · exact context_12_75063_550146

theorem selected_cut_21502 : selected 8 ⟨550158, by decide⟩
    (prefixPartial 13 300256) = some ⟨13, 2, 0, 550158, 300256, 521, 16384⟩ := by
  decide +kernel

theorem context_13_300256_550158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300256 ⟨550158, by decide⟩ :=
  accepted_of_selected 13 300256 ⟨550158, by decide⟩ ⟨13, 2, 0, 550158, 300256, 521, 16384⟩
    (by decide) selected_cut_21502

theorem selected_cut_21503 : selected 8 ⟨550229, by decide⟩
    (prefixPartial 13 300257) = some ⟨13, 2, 0, 550229, 300257, 3373, 16384⟩ := by
  decide +kernel

theorem context_13_300257_550229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300257 ⟨550229, by decide⟩ :=
  accepted_of_selected 13 300257 ⟨550229, by decide⟩ ⟨13, 2, 0, 550229, 300257, 3373, 16384⟩
    (by decide) selected_cut_21503

theorem selected_cut_21504 : selected 8 ⟨550294, by decide⟩
    (prefixPartial 13 300258) = some ⟨13, 2, 0, 550294, 300258, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_300258_550294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300258 ⟨550294, by decide⟩ :=
  accepted_of_selected 13 300258 ⟨550294, by decide⟩ ⟨13, 2, 0, 550294, 300258, 2669, 16384⟩
    (by decide) selected_cut_21504

theorem selected_cut_21505 : selected 8 ⟨550331, by decide⟩
    (prefixPartial 13 300259) = some ⟨13, 2, 0, 550331, 300259, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_300259_550331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300259 ⟨550331, by decide⟩ :=
  accepted_of_selected 13 300259 ⟨550331, by decide⟩ ⟨13, 2, 0, 550331, 300259, 1361, 16384⟩
    (by decide) selected_cut_21505

theorem unmarked_context_12_75064_550332 : frontier 9 ⟨550332, by decide⟩
    (prefixCache 12 75064) (prefixPartial 12 75064) = false := by
  decide +kernel

theorem node_context_12_75064_550332 : EJMOriginalGlobalDAGData.nodes 9 ⟨550332, by decide⟩ =
    .split (coordinate 12) (![⟨550158, by decide⟩,⟨550229, by decide⟩,⟨550294, by decide⟩,⟨550331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75064_550332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75064 ⟨550332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75064
    ⟨550332, by decide⟩ (by decide) (![⟨550158, by decide⟩,⟨550229, by decide⟩,⟨550294, by decide⟩,⟨550331, by decide⟩]) unmarked_context_12_75064_550332 node_context_12_75064_550332
  intro a
  fin_cases a
  · exact context_13_300256_550158
  · exact context_13_300257_550229
  · exact context_13_300258_550294
  · exact context_13_300259_550331

theorem selected_cut_21506 : selected 8 ⟨550341, by decide⟩
    (prefixPartial 13 300260) = some ⟨13, 2, 0, 550341, 300260, 329, 16384⟩ := by
  decide +kernel

theorem context_13_300260_550341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300260 ⟨550341, by decide⟩ :=
  accepted_of_selected 13 300260 ⟨550341, by decide⟩ ⟨13, 2, 0, 550341, 300260, 329, 16384⟩
    (by decide) selected_cut_21506

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
