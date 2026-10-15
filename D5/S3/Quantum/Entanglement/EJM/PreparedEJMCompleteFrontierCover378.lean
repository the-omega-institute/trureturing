/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover377
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_36291 : selected 10 ⟨959787, by decide⟩
    (prefixPartial 11 72114) = some ⟨11, 2, 0, 959787, 72114, 1797, 262144⟩ := by
  decide +kernel

theorem context_11_72114_959787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72114 ⟨959787, by decide⟩ :=
  accepted_of_selected 11 72114 ⟨959787, by decide⟩ ⟨11, 2, 0, 959787, 72114, 1797, 262144⟩
    (by decide) selected_cut_36291

theorem selected_cut_36292 : selected 10 ⟨959825, by decide⟩
    (prefixPartial 11 72115) = some ⟨11, 2, 0, 959825, 72115, 2205, 262144⟩ := by
  decide +kernel

theorem context_11_72115_959825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72115 ⟨959825, by decide⟩ :=
  accepted_of_selected 11 72115 ⟨959825, by decide⟩ ⟨11, 2, 0, 959825, 72115, 2205, 262144⟩
    (by decide) selected_cut_36292

theorem unmarked_context_10_18028_959826 : frontier 11 ⟨959826, by decide⟩
    (prefixCache 10 18028) (prefixPartial 10 18028) = false := by
  decide +kernel

theorem node_context_10_18028_959826 : EJMOriginalGlobalDAGData.nodes 11 ⟨959826, by decide⟩ =
    .split (coordinate 10) (![⟨959721, by decide⟩,⟨959759, by decide⟩,⟨959787, by decide⟩,⟨959825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18028_959826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18028 ⟨959826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18028
    ⟨959826, by decide⟩ (by decide) (![⟨959721, by decide⟩,⟨959759, by decide⟩,⟨959787, by decide⟩,⟨959825, by decide⟩]) unmarked_context_10_18028_959826 node_context_10_18028_959826
  intro a
  fin_cases a
  · exact context_11_72112_959721
  · exact context_11_72113_959759
  · exact context_11_72114_959787
  · exact context_11_72115_959825

theorem selected_cut_36293 : selected 11 ⟨959885, by decide⟩
    (prefixPartial 10 18029) = some ⟨10, 2, 0, 959885, 18029, 4013, 1048576⟩ := by
  decide +kernel

theorem context_10_18029_959885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18029 ⟨959885, by decide⟩ :=
  accepted_of_selected 10 18029 ⟨959885, by decide⟩ ⟨10, 2, 0, 959885, 18029, 4013, 1048576⟩
    (by decide) selected_cut_36293

theorem selected_cut_36294 : selected 11 ⟨959946, by decide⟩
    (prefixPartial 10 18030) = some ⟨10, 2, 0, 959946, 18030, 3369, 1048576⟩ := by
  decide +kernel

theorem context_10_18030_959946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18030 ⟨959946, by decide⟩ :=
  accepted_of_selected 10 18030 ⟨959946, by decide⟩ ⟨10, 2, 0, 959946, 18030, 3369, 1048576⟩
    (by decide) selected_cut_36294

theorem selected_cut_36295 : selected 11 ⟨959983, by decide⟩
    (prefixPartial 10 18031) = some ⟨10, 2, 0, 959983, 18031, 749, 1048576⟩ := by
  decide +kernel

theorem context_10_18031_959983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18031 ⟨959983, by decide⟩ :=
  accepted_of_selected 10 18031 ⟨959983, by decide⟩ ⟨10, 2, 0, 959983, 18031, 749, 1048576⟩
    (by decide) selected_cut_36295

theorem unmarked_context_9_4507_959984 : frontier 12 ⟨959984, by decide⟩
    (prefixCache 9 4507) (prefixPartial 9 4507) = false := by
  decide +kernel

theorem node_context_9_4507_959984 : EJMOriginalGlobalDAGData.nodes 12 ⟨959984, by decide⟩ =
    .split (coordinate 9) (![⟨959826, by decide⟩,⟨959885, by decide⟩,⟨959946, by decide⟩,⟨959983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4507_959984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4507 ⟨959984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4507
    ⟨959984, by decide⟩ (by decide) (![⟨959826, by decide⟩,⟨959885, by decide⟩,⟨959946, by decide⟩,⟨959983, by decide⟩]) unmarked_context_9_4507_959984 node_context_9_4507_959984
  intro a
  fin_cases a
  · exact context_10_18028_959826
  · exact context_10_18029_959885
  · exact context_10_18030_959946
  · exact context_10_18031_959983

theorem unmarked_context_8_1126_959985 : frontier 13 ⟨959985, by decide⟩
    (prefixCache 8 1126) (prefixPartial 8 1126) = false := by
  decide +kernel

theorem node_context_8_1126_959985 : EJMOriginalGlobalDAGData.nodes 13 ⟨959985, by decide⟩ =
    .split (coordinate 8) (![⟨957362, by decide⟩,⟨958713, by decide⟩,⟨959657, by decide⟩,⟨959984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1126_959985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1126 ⟨959985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1126
    ⟨959985, by decide⟩ (by decide) (![⟨957362, by decide⟩,⟨958713, by decide⟩,⟨959657, by decide⟩,⟨959984, by decide⟩]) unmarked_context_8_1126_959985 node_context_8_1126_959985
  intro a
  fin_cases a
  · exact context_9_4504_957362
  · exact context_9_4505_958713
  · exact context_9_4506_959657
  · exact context_9_4507_959984

theorem selected_cut_36296 : selected 10 ⟨960051, by decide⟩
    (prefixPartial 11 72128) = some ⟨11, 2, 0, 960051, 72128, 2137, 262144⟩ := by
  decide +kernel

theorem context_11_72128_960051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72128 ⟨960051, by decide⟩ :=
  accepted_of_selected 11 72128 ⟨960051, by decide⟩ ⟨11, 2, 0, 960051, 72128, 2137, 262144⟩
    (by decide) selected_cut_36296

theorem selected_cut_36297 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 288516) = some ⟨12, 1, 0, 34034, 288516, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288516_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288516 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 288516 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 288516, 1, 65536⟩
    (by decide) selected_cut_36297

theorem selected_cut_36298 : selected 9 ⟨960111, by decide⟩
    (prefixPartial 12 288517) = some ⟨12, 2, 0, 960111, 288517, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_288517_960111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288517 ⟨960111, by decide⟩ :=
  accepted_of_selected 12 288517 ⟨960111, by decide⟩ ⟨12, 2, 0, 960111, 288517, 3129, 65536⟩
    (by decide) selected_cut_36298

theorem selected_cut_36299 : selected 9 ⟨960171, by decide⟩
    (prefixPartial 12 288518) = some ⟨12, 2, 0, 960171, 288518, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_288518_960171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288518 ⟨960171, by decide⟩ :=
  accepted_of_selected 12 288518 ⟨960171, by decide⟩ ⟨12, 2, 0, 960171, 288518, 3513, 65536⟩
    (by decide) selected_cut_36299

theorem selected_cut_36300 : selected 9 ⟨960230, by decide⟩
    (prefixPartial 12 288519) = some ⟨12, 2, 0, 960230, 288519, 3697, 65536⟩ := by
  decide +kernel

theorem context_12_288519_960230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288519 ⟨960230, by decide⟩ :=
  accepted_of_selected 12 288519 ⟨960230, by decide⟩ ⟨12, 2, 0, 960230, 288519, 3697, 65536⟩
    (by decide) selected_cut_36300

theorem unmarked_context_11_72129_960231 : frontier 10 ⟨960231, by decide⟩
    (prefixCache 11 72129) (prefixPartial 11 72129) = false := by
  decide +kernel

theorem node_context_11_72129_960231 : EJMOriginalGlobalDAGData.nodes 10 ⟨960231, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨960111, by decide⟩,⟨960171, by decide⟩,⟨960230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72129_960231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72129 ⟨960231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72129
    ⟨960231, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨960111, by decide⟩,⟨960171, by decide⟩,⟨960230, by decide⟩]) unmarked_context_11_72129_960231 node_context_11_72129_960231
  intro a
  fin_cases a
  · exact context_12_288516_34034
  · exact context_12_288517_960111
  · exact context_12_288518_960171
  · exact context_12_288519_960230

theorem selected_cut_36301 : selected 8 ⟨960270, by decide⟩
    (prefixPartial 13 1154080) = some ⟨13, 2, 0, 960270, 1154080, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_1154080_960270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1154080 ⟨960270, by decide⟩ :=
  accepted_of_selected 13 1154080 ⟨960270, by decide⟩ ⟨13, 2, 0, 960270, 1154080, 1297, 16384⟩
    (by decide) selected_cut_36301

theorem selected_cut_36302 : selected 8 ⟨960305, by decide⟩
    (prefixPartial 13 1154081) = some ⟨13, 2, 0, 960305, 1154081, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_1154081_960305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1154081 ⟨960305, by decide⟩ :=
  accepted_of_selected 13 1154081 ⟨960305, by decide⟩ ⟨13, 2, 0, 960305, 1154081, 1169, 16384⟩
    (by decide) selected_cut_36302

theorem selected_cut_36303 : selected 8 ⟨960349, by decide⟩
    (prefixPartial 13 1154082) = some ⟨13, 2, 0, 960349, 1154082, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_1154082_960349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1154082 ⟨960349, by decide⟩ :=
  accepted_of_selected 13 1154082 ⟨960349, by decide⟩ ⟨13, 2, 0, 960349, 1154082, 1249, 16384⟩
    (by decide) selected_cut_36303

theorem selected_cut_36304 : selected 8 ⟨960367, by decide⟩
    (prefixPartial 13 1154083) = some ⟨13, 2, 0, 960367, 1154083, 709, 16384⟩ := by
  decide +kernel

theorem context_13_1154083_960367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1154083 ⟨960367, by decide⟩ :=
  accepted_of_selected 13 1154083 ⟨960367, by decide⟩ ⟨13, 2, 0, 960367, 1154083, 709, 16384⟩
    (by decide) selected_cut_36304

theorem unmarked_context_12_288520_960368 : frontier 9 ⟨960368, by decide⟩
    (prefixCache 12 288520) (prefixPartial 12 288520) = false := by
  decide +kernel

theorem node_context_12_288520_960368 : EJMOriginalGlobalDAGData.nodes 9 ⟨960368, by decide⟩ =
    .split (coordinate 12) (![⟨960270, by decide⟩,⟨960305, by decide⟩,⟨960349, by decide⟩,⟨960367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_288520_960368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288520 ⟨960368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 288520
    ⟨960368, by decide⟩ (by decide) (![⟨960270, by decide⟩,⟨960305, by decide⟩,⟨960349, by decide⟩,⟨960367, by decide⟩]) unmarked_context_12_288520_960368 node_context_12_288520_960368
  intro a
  fin_cases a
  · exact context_13_1154080_960270
  · exact context_13_1154081_960305
  · exact context_13_1154082_960349
  · exact context_13_1154083_960367

theorem selected_cut_36305 : selected 9 ⟨960443, by decide⟩
    (prefixPartial 12 288521) = some ⟨12, 2, 0, 960443, 288521, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_288521_960443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288521 ⟨960443, by decide⟩ :=
  accepted_of_selected 12 288521 ⟨960443, by decide⟩ ⟨12, 2, 0, 960443, 288521, 3553, 65536⟩
    (by decide) selected_cut_36305

theorem selected_cut_36306 : selected 9 ⟨960516, by decide⟩
    (prefixPartial 12 288522) = some ⟨12, 2, 0, 960516, 288522, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_288522_960516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288522 ⟨960516, by decide⟩ :=
  accepted_of_selected 12 288522 ⟨960516, by decide⟩ ⟨12, 2, 0, 960516, 288522, 3761, 65536⟩
    (by decide) selected_cut_36306

theorem selected_cut_36307 : selected 8 ⟨960553, by decide⟩
    (prefixPartial 13 1154092) = some ⟨13, 2, 0, 960553, 1154092, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_1154092_960553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1154092 ⟨960553, by decide⟩ :=
  accepted_of_selected 13 1154092 ⟨960553, by decide⟩ ⟨13, 2, 0, 960553, 1154092, 1545, 16384⟩
    (by decide) selected_cut_36307

theorem selected_cut_36308 : selected 8 ⟨960579, by decide⟩
    (prefixPartial 13 1154093) = some ⟨13, 2, 0, 960579, 1154093, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_1154093_960579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1154093 ⟨960579, by decide⟩ :=
  accepted_of_selected 13 1154093 ⟨960579, by decide⟩ ⟨13, 2, 0, 960579, 1154093, 1181, 16384⟩
    (by decide) selected_cut_36308

theorem selected_cut_36309 : selected 8 ⟨960596, by decide⟩
    (prefixPartial 13 1154094) = some ⟨13, 2, 0, 960596, 1154094, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_1154094_960596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1154094 ⟨960596, by decide⟩ :=
  accepted_of_selected 13 1154094 ⟨960596, by decide⟩ ⟨13, 2, 0, 960596, 1154094, 1013, 16384⟩
    (by decide) selected_cut_36309

theorem selected_cut_36310 : selected 8 ⟨960602, by decide⟩
    (prefixPartial 13 1154095) = some ⟨13, 2, 0, 960602, 1154095, 573, 16384⟩ := by
  decide +kernel

theorem context_13_1154095_960602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1154095 ⟨960602, by decide⟩ :=
  accepted_of_selected 13 1154095 ⟨960602, by decide⟩ ⟨13, 2, 0, 960602, 1154095, 573, 16384⟩
    (by decide) selected_cut_36310

theorem unmarked_context_12_288523_960603 : frontier 9 ⟨960603, by decide⟩
    (prefixCache 12 288523) (prefixPartial 12 288523) = false := by
  decide +kernel

theorem node_context_12_288523_960603 : EJMOriginalGlobalDAGData.nodes 9 ⟨960603, by decide⟩ =
    .split (coordinate 12) (![⟨960553, by decide⟩,⟨960579, by decide⟩,⟨960596, by decide⟩,⟨960602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_288523_960603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288523 ⟨960603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 288523
    ⟨960603, by decide⟩ (by decide) (![⟨960553, by decide⟩,⟨960579, by decide⟩,⟨960596, by decide⟩,⟨960602, by decide⟩]) unmarked_context_12_288523_960603 node_context_12_288523_960603
  intro a
  fin_cases a
  · exact context_13_1154092_960553
  · exact context_13_1154093_960579
  · exact context_13_1154094_960596
  · exact context_13_1154095_960602

theorem unmarked_context_11_72130_960604 : frontier 10 ⟨960604, by decide⟩
    (prefixCache 11 72130) (prefixPartial 11 72130) = false := by
  decide +kernel

theorem node_context_11_72130_960604 : EJMOriginalGlobalDAGData.nodes 10 ⟨960604, by decide⟩ =
    .split (coordinate 11) (![⟨960368, by decide⟩,⟨960443, by decide⟩,⟨960516, by decide⟩,⟨960603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72130_960604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72130 ⟨960604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72130
    ⟨960604, by decide⟩ (by decide) (![⟨960368, by decide⟩,⟨960443, by decide⟩,⟨960516, by decide⟩,⟨960603, by decide⟩]) unmarked_context_11_72130_960604 node_context_11_72130_960604
  intro a
  fin_cases a
  · exact context_12_288520_960368
  · exact context_12_288521_960443
  · exact context_12_288522_960516
  · exact context_12_288523_960603

theorem selected_cut_36311 : selected 9 ⟨292651, by decide⟩
    (prefixPartial 12 288524) = some ⟨12, 1, 0, 292651, 288524, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288524_292651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288524 ⟨292651, by decide⟩ :=
  accepted_of_selected 12 288524 ⟨292651, by decide⟩ ⟨12, 1, 0, 292651, 288524, 1, 65536⟩
    (by decide) selected_cut_36311

theorem selected_cut_36312 : selected 9 ⟨960656, by decide⟩
    (prefixPartial 12 288525) = some ⟨12, 2, 0, 960656, 288525, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_288525_960656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288525 ⟨960656, by decide⟩ :=
  accepted_of_selected 12 288525 ⟨960656, by decide⟩ ⟨12, 2, 0, 960656, 288525, 3037, 65536⟩
    (by decide) selected_cut_36312

theorem selected_cut_36313 : selected 9 ⟨960732, by decide⟩
    (prefixPartial 12 288526) = some ⟨12, 2, 0, 960732, 288526, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_288526_960732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288526 ⟨960732, by decide⟩ :=
  accepted_of_selected 12 288526 ⟨960732, by decide⟩ ⟨12, 2, 0, 960732, 288526, 3729, 65536⟩
    (by decide) selected_cut_36313

theorem selected_cut_36314 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 288527) = some ⟨12, 1, 0, 903806, 288527, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288527_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288527 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 288527 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 288527, 1, 65536⟩
    (by decide) selected_cut_36314

theorem unmarked_context_11_72131_960733 : frontier 10 ⟨960733, by decide⟩
    (prefixCache 11 72131) (prefixPartial 11 72131) = false := by
  decide +kernel

theorem node_context_11_72131_960733 : EJMOriginalGlobalDAGData.nodes 10 ⟨960733, by decide⟩ =
    .split (coordinate 11) (![⟨292651, by decide⟩,⟨960656, by decide⟩,⟨960732, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72131_960733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72131 ⟨960733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72131
    ⟨960733, by decide⟩ (by decide) (![⟨292651, by decide⟩,⟨960656, by decide⟩,⟨960732, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_72131_960733 node_context_11_72131_960733
  intro a
  fin_cases a
  · exact context_12_288524_292651
  · exact context_12_288525_960656
  · exact context_12_288526_960732
  · exact context_12_288527_903806

theorem unmarked_context_10_18032_960734 : frontier 11 ⟨960734, by decide⟩
    (prefixCache 10 18032) (prefixPartial 10 18032) = false := by
  decide +kernel

theorem node_context_10_18032_960734 : EJMOriginalGlobalDAGData.nodes 11 ⟨960734, by decide⟩ =
    .split (coordinate 10) (![⟨960051, by decide⟩,⟨960231, by decide⟩,⟨960604, by decide⟩,⟨960733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18032_960734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18032 ⟨960734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18032
    ⟨960734, by decide⟩ (by decide) (![⟨960051, by decide⟩,⟨960231, by decide⟩,⟨960604, by decide⟩,⟨960733, by decide⟩]) unmarked_context_10_18032_960734 node_context_10_18032_960734
  intro a
  fin_cases a
  · exact context_11_72128_960051
  · exact context_11_72129_960231
  · exact context_11_72130_960604
  · exact context_11_72131_960733

theorem selected_cut_36315 : selected 9 ⟨960777, by decide⟩
    (prefixPartial 12 288528) = some ⟨12, 2, 0, 960777, 288528, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_288528_960777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288528 ⟨960777, by decide⟩ :=
  accepted_of_selected 12 288528 ⟨960777, by decide⟩ ⟨12, 2, 0, 960777, 288528, 2837, 65536⟩
    (by decide) selected_cut_36315

theorem selected_cut_36316 : selected 9 ⟨960826, by decide⟩
    (prefixPartial 12 288529) = some ⟨12, 2, 0, 960826, 288529, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_288529_960826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288529 ⟨960826, by decide⟩ :=
  accepted_of_selected 12 288529 ⟨960826, by decide⟩ ⟨12, 2, 0, 960826, 288529, 2753, 65536⟩
    (by decide) selected_cut_36316

theorem selected_cut_36317 : selected 9 ⟨960888, by decide⟩
    (prefixPartial 12 288530) = some ⟨12, 2, 0, 960888, 288530, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_288530_960888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288530 ⟨960888, by decide⟩ :=
  accepted_of_selected 12 288530 ⟨960888, by decide⟩ ⟨12, 2, 0, 960888, 288530, 3449, 65536⟩
    (by decide) selected_cut_36317

theorem selected_cut_36318 : selected 9 ⟨960943, by decide⟩
    (prefixPartial 12 288531) = some ⟨12, 2, 0, 960943, 288531, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_288531_960943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288531 ⟨960943, by decide⟩ :=
  accepted_of_selected 12 288531 ⟨960943, by decide⟩ ⟨12, 2, 0, 960943, 288531, 3373, 65536⟩
    (by decide) selected_cut_36318

theorem unmarked_context_11_72132_960944 : frontier 10 ⟨960944, by decide⟩
    (prefixCache 11 72132) (prefixPartial 11 72132) = false := by
  decide +kernel

theorem node_context_11_72132_960944 : EJMOriginalGlobalDAGData.nodes 10 ⟨960944, by decide⟩ =
    .split (coordinate 11) (![⟨960777, by decide⟩,⟨960826, by decide⟩,⟨960888, by decide⟩,⟨960943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72132_960944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72132 ⟨960944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72132
    ⟨960944, by decide⟩ (by decide) (![⟨960777, by decide⟩,⟨960826, by decide⟩,⟨960888, by decide⟩,⟨960943, by decide⟩]) unmarked_context_11_72132_960944 node_context_11_72132_960944
  intro a
  fin_cases a
  · exact context_12_288528_960777
  · exact context_12_288529_960826
  · exact context_12_288530_960888
  · exact context_12_288531_960943

theorem selected_cut_36319 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 72133) = some ⟨11, 1, 0, 892405, 72133, 1, 262144⟩ := by
  decide +kernel

theorem context_11_72133_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72133 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 72133 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 72133, 1, 262144⟩
    (by decide) selected_cut_36319

theorem selected_cut_36320 : selected 9 ⟨961003, by decide⟩
    (prefixPartial 12 288536) = some ⟨12, 2, 0, 961003, 288536, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_288536_961003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288536 ⟨961003, by decide⟩ :=
  accepted_of_selected 12 288536 ⟨961003, by decide⟩ ⟨12, 2, 0, 961003, 288536, 3417, 65536⟩
    (by decide) selected_cut_36320

theorem selected_cut_36321 : selected 9 ⟨961050, by decide⟩
    (prefixPartial 12 288537) = some ⟨12, 2, 0, 961050, 288537, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_288537_961050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288537 ⟨961050, by decide⟩ :=
  accepted_of_selected 12 288537 ⟨961050, by decide⟩ ⟨12, 2, 0, 961050, 288537, 2965, 65536⟩
    (by decide) selected_cut_36321

theorem selected_cut_36322 : selected 9 ⟨961117, by decide⟩
    (prefixPartial 12 288538) = some ⟨12, 2, 0, 961117, 288538, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_288538_961117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288538 ⟨961117, by decide⟩ :=
  accepted_of_selected 12 288538 ⟨961117, by decide⟩ ⟨12, 2, 0, 961117, 288538, 3245, 65536⟩
    (by decide) selected_cut_36322

theorem selected_cut_36323 : selected 9 ⟨961179, by decide⟩
    (prefixPartial 12 288539) = some ⟨12, 2, 0, 961179, 288539, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_288539_961179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288539 ⟨961179, by decide⟩ :=
  accepted_of_selected 12 288539 ⟨961179, by decide⟩ ⟨12, 2, 0, 961179, 288539, 3553, 65536⟩
    (by decide) selected_cut_36323

theorem unmarked_context_11_72134_961180 : frontier 10 ⟨961180, by decide⟩
    (prefixCache 11 72134) (prefixPartial 11 72134) = false := by
  decide +kernel

theorem node_context_11_72134_961180 : EJMOriginalGlobalDAGData.nodes 10 ⟨961180, by decide⟩ =
    .split (coordinate 11) (![⟨961003, by decide⟩,⟨961050, by decide⟩,⟨961117, by decide⟩,⟨961179, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72134_961180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72134 ⟨961180, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72134
    ⟨961180, by decide⟩ (by decide) (![⟨961003, by decide⟩,⟨961050, by decide⟩,⟨961117, by decide⟩,⟨961179, by decide⟩]) unmarked_context_11_72134_961180 node_context_11_72134_961180
  intro a
  fin_cases a
  · exact context_12_288536_961003
  · exact context_12_288537_961050
  · exact context_12_288538_961117
  · exact context_12_288539_961179

theorem selected_cut_36324 : selected 9 ⟨961227, by decide⟩
    (prefixPartial 12 288540) = some ⟨12, 2, 0, 961227, 288540, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_288540_961227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288540 ⟨961227, by decide⟩ :=
  accepted_of_selected 12 288540 ⟨961227, by decide⟩ ⟨12, 2, 0, 961227, 288540, 3077, 65536⟩
    (by decide) selected_cut_36324

theorem selected_cut_36325 : selected 9 ⟨961272, by decide⟩
    (prefixPartial 12 288541) = some ⟨12, 2, 0, 961272, 288541, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_288541_961272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288541 ⟨961272, by decide⟩ :=
  accepted_of_selected 12 288541 ⟨961272, by decide⟩ ⟨12, 2, 0, 961272, 288541, 2725, 65536⟩
    (by decide) selected_cut_36325

theorem selected_cut_36326 : selected 9 ⟨961328, by decide⟩
    (prefixPartial 12 288542) = some ⟨12, 2, 0, 961328, 288542, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_288542_961328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288542 ⟨961328, by decide⟩ :=
  accepted_of_selected 12 288542 ⟨961328, by decide⟩ ⟨12, 2, 0, 961328, 288542, 3289, 65536⟩
    (by decide) selected_cut_36326

theorem selected_cut_36327 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 288543) = some ⟨12, 1, 0, 903806, 288543, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288543_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288543 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 288543 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 288543, 1, 65536⟩
    (by decide) selected_cut_36327

theorem unmarked_context_11_72135_961329 : frontier 10 ⟨961329, by decide⟩
    (prefixCache 11 72135) (prefixPartial 11 72135) = false := by
  decide +kernel

theorem node_context_11_72135_961329 : EJMOriginalGlobalDAGData.nodes 10 ⟨961329, by decide⟩ =
    .split (coordinate 11) (![⟨961227, by decide⟩,⟨961272, by decide⟩,⟨961328, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72135_961329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72135 ⟨961329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72135
    ⟨961329, by decide⟩ (by decide) (![⟨961227, by decide⟩,⟨961272, by decide⟩,⟨961328, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_72135_961329 node_context_11_72135_961329
  intro a
  fin_cases a
  · exact context_12_288540_961227
  · exact context_12_288541_961272
  · exact context_12_288542_961328
  · exact context_12_288543_903806

theorem unmarked_context_10_18033_961330 : frontier 11 ⟨961330, by decide⟩
    (prefixCache 10 18033) (prefixPartial 10 18033) = false := by
  decide +kernel

theorem node_context_10_18033_961330 : EJMOriginalGlobalDAGData.nodes 11 ⟨961330, by decide⟩ =
    .split (coordinate 10) (![⟨960944, by decide⟩,⟨892405, by decide⟩,⟨961180, by decide⟩,⟨961329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18033_961330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18033 ⟨961330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18033
    ⟨961330, by decide⟩ (by decide) (![⟨960944, by decide⟩,⟨892405, by decide⟩,⟨961180, by decide⟩,⟨961329, by decide⟩]) unmarked_context_10_18033_961330 node_context_10_18033_961330
  intro a
  fin_cases a
  · exact context_11_72132_960944
  · exact context_11_72133_892405
  · exact context_11_72134_961180
  · exact context_11_72135_961329

theorem selected_cut_36328 : selected 9 ⟨961373, by decide⟩
    (prefixPartial 12 288544) = some ⟨12, 2, 0, 961373, 288544, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_288544_961373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288544 ⟨961373, by decide⟩ :=
  accepted_of_selected 12 288544 ⟨961373, by decide⟩ ⟨12, 2, 0, 961373, 288544, 2765, 65536⟩
    (by decide) selected_cut_36328

theorem selected_cut_36329 : selected 9 ⟨961414, by decide⟩
    (prefixPartial 12 288545) = some ⟨12, 2, 0, 961414, 288545, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_288545_961414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288545 ⟨961414, by decide⟩ :=
  accepted_of_selected 12 288545 ⟨961414, by decide⟩ ⟨12, 2, 0, 961414, 288545, 2737, 65536⟩
    (by decide) selected_cut_36329

theorem selected_cut_36330 : selected 9 ⟨961490, by decide⟩
    (prefixPartial 12 288546) = some ⟨12, 2, 0, 961490, 288546, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_288546_961490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288546 ⟨961490, by decide⟩ :=
  accepted_of_selected 12 288546 ⟨961490, by decide⟩ ⟨12, 2, 0, 961490, 288546, 3613, 65536⟩
    (by decide) selected_cut_36330

theorem selected_cut_36331 : selected 9 ⟨961550, by decide⟩
    (prefixPartial 12 288547) = some ⟨12, 2, 0, 961550, 288547, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_288547_961550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288547 ⟨961550, by decide⟩ :=
  accepted_of_selected 12 288547 ⟨961550, by decide⟩ ⟨12, 2, 0, 961550, 288547, 3421, 65536⟩
    (by decide) selected_cut_36331

theorem unmarked_context_11_72136_961551 : frontier 10 ⟨961551, by decide⟩
    (prefixCache 11 72136) (prefixPartial 11 72136) = false := by
  decide +kernel

theorem node_context_11_72136_961551 : EJMOriginalGlobalDAGData.nodes 10 ⟨961551, by decide⟩ =
    .split (coordinate 11) (![⟨961373, by decide⟩,⟨961414, by decide⟩,⟨961490, by decide⟩,⟨961550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72136_961551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72136 ⟨961551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72136
    ⟨961551, by decide⟩ (by decide) (![⟨961373, by decide⟩,⟨961414, by decide⟩,⟨961490, by decide⟩,⟨961550, by decide⟩]) unmarked_context_11_72136_961551 node_context_11_72136_961551
  intro a
  fin_cases a
  · exact context_12_288544_961373
  · exact context_12_288545_961414
  · exact context_12_288546_961490
  · exact context_12_288547_961550

theorem selected_cut_36332 : selected 9 ⟨961600, by decide⟩
    (prefixPartial 12 288548) = some ⟨12, 2, 0, 961600, 288548, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_288548_961600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288548 ⟨961600, by decide⟩ :=
  accepted_of_selected 12 288548 ⟨961600, by decide⟩ ⟨12, 2, 0, 961600, 288548, 2813, 65536⟩
    (by decide) selected_cut_36332

theorem selected_cut_36333 : selected 9 ⟨961639, by decide⟩
    (prefixPartial 12 288549) = some ⟨12, 2, 0, 961639, 288549, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_288549_961639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288549 ⟨961639, by decide⟩ :=
  accepted_of_selected 12 288549 ⟨961639, by decide⟩ ⟨12, 2, 0, 961639, 288549, 2485, 65536⟩
    (by decide) selected_cut_36333

theorem selected_cut_36334 : selected 9 ⟨961685, by decide⟩
    (prefixPartial 12 288550) = some ⟨12, 2, 0, 961685, 288550, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_288550_961685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288550 ⟨961685, by decide⟩ :=
  accepted_of_selected 12 288550 ⟨961685, by decide⟩ ⟨12, 2, 0, 961685, 288550, 2937, 65536⟩
    (by decide) selected_cut_36334

theorem selected_cut_36335 : selected 9 ⟨961731, by decide⟩
    (prefixPartial 12 288551) = some ⟨12, 2, 0, 961731, 288551, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_288551_961731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288551 ⟨961731, by decide⟩ :=
  accepted_of_selected 12 288551 ⟨961731, by decide⟩ ⟨12, 2, 0, 961731, 288551, 2961, 65536⟩
    (by decide) selected_cut_36335

theorem unmarked_context_11_72137_961732 : frontier 10 ⟨961732, by decide⟩
    (prefixCache 11 72137) (prefixPartial 11 72137) = false := by
  decide +kernel

theorem node_context_11_72137_961732 : EJMOriginalGlobalDAGData.nodes 10 ⟨961732, by decide⟩ =
    .split (coordinate 11) (![⟨961600, by decide⟩,⟨961639, by decide⟩,⟨961685, by decide⟩,⟨961731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72137_961732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72137 ⟨961732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72137
    ⟨961732, by decide⟩ (by decide) (![⟨961600, by decide⟩,⟨961639, by decide⟩,⟨961685, by decide⟩,⟨961731, by decide⟩]) unmarked_context_11_72137_961732 node_context_11_72137_961732
  intro a
  fin_cases a
  · exact context_12_288548_961600
  · exact context_12_288549_961639
  · exact context_12_288550_961685
  · exact context_12_288551_961731

theorem selected_cut_36336 : selected 9 ⟨961787, by decide⟩
    (prefixPartial 12 288552) = some ⟨12, 2, 0, 961787, 288552, 3113, 65536⟩ := by
  decide +kernel

theorem context_12_288552_961787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288552 ⟨961787, by decide⟩ :=
  accepted_of_selected 12 288552 ⟨961787, by decide⟩ ⟨12, 2, 0, 961787, 288552, 3113, 65536⟩
    (by decide) selected_cut_36336

theorem selected_cut_36337 : selected 9 ⟨961823, by decide⟩
    (prefixPartial 12 288553) = some ⟨12, 2, 0, 961823, 288553, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_288553_961823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288553 ⟨961823, by decide⟩ :=
  accepted_of_selected 12 288553 ⟨961823, by decide⟩ ⟨12, 2, 0, 961823, 288553, 2717, 65536⟩
    (by decide) selected_cut_36337

theorem selected_cut_36338 : selected 9 ⟨961874, by decide⟩
    (prefixPartial 12 288554) = some ⟨12, 2, 0, 961874, 288554, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_288554_961874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288554 ⟨961874, by decide⟩ :=
  accepted_of_selected 12 288554 ⟨961874, by decide⟩ ⟨12, 2, 0, 961874, 288554, 3121, 65536⟩
    (by decide) selected_cut_36338

theorem selected_cut_36339 : selected 9 ⟨961928, by decide⟩
    (prefixPartial 12 288555) = some ⟨12, 2, 0, 961928, 288555, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_288555_961928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288555 ⟨961928, by decide⟩ :=
  accepted_of_selected 12 288555 ⟨961928, by decide⟩ ⟨12, 2, 0, 961928, 288555, 3321, 65536⟩
    (by decide) selected_cut_36339

theorem unmarked_context_11_72138_961929 : frontier 10 ⟨961929, by decide⟩
    (prefixCache 11 72138) (prefixPartial 11 72138) = false := by
  decide +kernel

theorem node_context_11_72138_961929 : EJMOriginalGlobalDAGData.nodes 10 ⟨961929, by decide⟩ =
    .split (coordinate 11) (![⟨961787, by decide⟩,⟨961823, by decide⟩,⟨961874, by decide⟩,⟨961928, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72138_961929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72138 ⟨961929, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72138
    ⟨961929, by decide⟩ (by decide) (![⟨961787, by decide⟩,⟨961823, by decide⟩,⟨961874, by decide⟩,⟨961928, by decide⟩]) unmarked_context_11_72138_961929 node_context_11_72138_961929
  intro a
  fin_cases a
  · exact context_12_288552_961787
  · exact context_12_288553_961823
  · exact context_12_288554_961874
  · exact context_12_288555_961928

theorem selected_cut_36340 : selected 9 ⟨961982, by decide⟩
    (prefixPartial 12 288556) = some ⟨12, 2, 0, 961982, 288556, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_288556_961982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288556 ⟨961982, by decide⟩ :=
  accepted_of_selected 12 288556 ⟨961982, by decide⟩ ⟨12, 2, 0, 961982, 288556, 2937, 65536⟩
    (by decide) selected_cut_36340

theorem selected_cut_36341 : selected 9 ⟨962019, by decide⟩
    (prefixPartial 12 288557) = some ⟨12, 2, 0, 962019, 288557, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_288557_962019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288557 ⟨962019, by decide⟩ :=
  accepted_of_selected 12 288557 ⟨962019, by decide⟩ ⟨12, 2, 0, 962019, 288557, 2493, 65536⟩
    (by decide) selected_cut_36341

theorem selected_cut_36342 : selected 9 ⟨962086, by decide⟩
    (prefixPartial 12 288558) = some ⟨12, 2, 0, 962086, 288558, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_288558_962086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288558 ⟨962086, by decide⟩ :=
  accepted_of_selected 12 288558 ⟨962086, by decide⟩ ⟨12, 2, 0, 962086, 288558, 3369, 65536⟩
    (by decide) selected_cut_36342

theorem selected_cut_36343 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 288559) = some ⟨12, 1, 0, 903806, 288559, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288559_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288559 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 288559 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 288559, 1, 65536⟩
    (by decide) selected_cut_36343

theorem unmarked_context_11_72139_962087 : frontier 10 ⟨962087, by decide⟩
    (prefixCache 11 72139) (prefixPartial 11 72139) = false := by
  decide +kernel

theorem node_context_11_72139_962087 : EJMOriginalGlobalDAGData.nodes 10 ⟨962087, by decide⟩ =
    .split (coordinate 11) (![⟨961982, by decide⟩,⟨962019, by decide⟩,⟨962086, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72139_962087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72139 ⟨962087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72139
    ⟨962087, by decide⟩ (by decide) (![⟨961982, by decide⟩,⟨962019, by decide⟩,⟨962086, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_72139_962087 node_context_11_72139_962087
  intro a
  fin_cases a
  · exact context_12_288556_961982
  · exact context_12_288557_962019
  · exact context_12_288558_962086
  · exact context_12_288559_903806

theorem unmarked_context_10_18034_962088 : frontier 11 ⟨962088, by decide⟩
    (prefixCache 10 18034) (prefixPartial 10 18034) = false := by
  decide +kernel

theorem node_context_10_18034_962088 : EJMOriginalGlobalDAGData.nodes 11 ⟨962088, by decide⟩ =
    .split (coordinate 10) (![⟨961551, by decide⟩,⟨961732, by decide⟩,⟨961929, by decide⟩,⟨962087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18034_962088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18034 ⟨962088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18034
    ⟨962088, by decide⟩ (by decide) (![⟨961551, by decide⟩,⟨961732, by decide⟩,⟨961929, by decide⟩,⟨962087, by decide⟩]) unmarked_context_10_18034_962088 node_context_10_18034_962088
  intro a
  fin_cases a
  · exact context_11_72136_961551
  · exact context_11_72137_961732
  · exact context_11_72138_961929
  · exact context_11_72139_962087

theorem selected_cut_36344 : selected 9 ⟨962139, by decide⟩
    (prefixPartial 12 288560) = some ⟨12, 2, 0, 962139, 288560, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_288560_962139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288560 ⟨962139, by decide⟩ :=
  accepted_of_selected 12 288560 ⟨962139, by decide⟩ ⟨12, 2, 0, 962139, 288560, 2821, 65536⟩
    (by decide) selected_cut_36344

theorem selected_cut_36345 : selected 9 ⟨962186, by decide⟩
    (prefixPartial 12 288561) = some ⟨12, 2, 0, 962186, 288561, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_288561_962186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288561 ⟨962186, by decide⟩ :=
  accepted_of_selected 12 288561 ⟨962186, by decide⟩ ⟨12, 2, 0, 962186, 288561, 2797, 65536⟩
    (by decide) selected_cut_36345

theorem selected_cut_36346 : selected 9 ⟨962260, by decide⟩
    (prefixPartial 12 288562) = some ⟨12, 2, 0, 962260, 288562, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_288562_962260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288562 ⟨962260, by decide⟩ :=
  accepted_of_selected 12 288562 ⟨962260, by decide⟩ ⟨12, 2, 0, 962260, 288562, 3481, 65536⟩
    (by decide) selected_cut_36346

theorem selected_cut_36347 : selected 9 ⟨962327, by decide⟩
    (prefixPartial 12 288563) = some ⟨12, 2, 0, 962327, 288563, 3489, 65536⟩ := by
  decide +kernel

theorem context_12_288563_962327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288563 ⟨962327, by decide⟩ :=
  accepted_of_selected 12 288563 ⟨962327, by decide⟩ ⟨12, 2, 0, 962327, 288563, 3489, 65536⟩
    (by decide) selected_cut_36347

theorem unmarked_context_11_72140_962328 : frontier 10 ⟨962328, by decide⟩
    (prefixCache 11 72140) (prefixPartial 11 72140) = false := by
  decide +kernel

theorem node_context_11_72140_962328 : EJMOriginalGlobalDAGData.nodes 10 ⟨962328, by decide⟩ =
    .split (coordinate 11) (![⟨962139, by decide⟩,⟨962186, by decide⟩,⟨962260, by decide⟩,⟨962327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72140_962328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72140 ⟨962328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72140
    ⟨962328, by decide⟩ (by decide) (![⟨962139, by decide⟩,⟨962186, by decide⟩,⟨962260, by decide⟩,⟨962327, by decide⟩]) unmarked_context_11_72140_962328 node_context_11_72140_962328
  intro a
  fin_cases a
  · exact context_12_288560_962139
  · exact context_12_288561_962186
  · exact context_12_288562_962260
  · exact context_12_288563_962327

theorem selected_cut_36348 : selected 9 ⟨962374, by decide⟩
    (prefixPartial 12 288564) = some ⟨12, 2, 0, 962374, 288564, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_288564_962374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288564 ⟨962374, by decide⟩ :=
  accepted_of_selected 12 288564 ⟨962374, by decide⟩ ⟨12, 2, 0, 962374, 288564, 2741, 65536⟩
    (by decide) selected_cut_36348

theorem selected_cut_36349 : selected 9 ⟨962418, by decide⟩
    (prefixPartial 12 288565) = some ⟨12, 2, 0, 962418, 288565, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_288565_962418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288565 ⟨962418, by decide⟩ :=
  accepted_of_selected 12 288565 ⟨962418, by decide⟩ ⟨12, 2, 0, 962418, 288565, 2417, 65536⟩
    (by decide) selected_cut_36349

theorem selected_cut_36350 : selected 9 ⟨962467, by decide⟩
    (prefixPartial 12 288566) = some ⟨12, 2, 0, 962467, 288566, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_288566_962467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288566 ⟨962467, by decide⟩ :=
  accepted_of_selected 12 288566 ⟨962467, by decide⟩ ⟨12, 2, 0, 962467, 288566, 2889, 65536⟩
    (by decide) selected_cut_36350

theorem selected_cut_36351 : selected 9 ⟨962512, by decide⟩
    (prefixPartial 12 288567) = some ⟨12, 2, 0, 962512, 288567, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_288567_962512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288567 ⟨962512, by decide⟩ :=
  accepted_of_selected 12 288567 ⟨962512, by decide⟩ ⟨12, 2, 0, 962512, 288567, 2953, 65536⟩
    (by decide) selected_cut_36351

theorem unmarked_context_11_72141_962513 : frontier 10 ⟨962513, by decide⟩
    (prefixCache 11 72141) (prefixPartial 11 72141) = false := by
  decide +kernel

theorem node_context_11_72141_962513 : EJMOriginalGlobalDAGData.nodes 10 ⟨962513, by decide⟩ =
    .split (coordinate 11) (![⟨962374, by decide⟩,⟨962418, by decide⟩,⟨962467, by decide⟩,⟨962512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72141_962513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72141 ⟨962513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72141
    ⟨962513, by decide⟩ (by decide) (![⟨962374, by decide⟩,⟨962418, by decide⟩,⟨962467, by decide⟩,⟨962512, by decide⟩]) unmarked_context_11_72141_962513 node_context_11_72141_962513
  intro a
  fin_cases a
  · exact context_12_288564_962374
  · exact context_12_288565_962418
  · exact context_12_288566_962467
  · exact context_12_288567_962512

theorem selected_cut_36352 : selected 9 ⟨962577, by decide⟩
    (prefixPartial 12 288568) = some ⟨12, 2, 0, 962577, 288568, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_288568_962577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288568 ⟨962577, by decide⟩ :=
  accepted_of_selected 12 288568 ⟨962577, by decide⟩ ⟨12, 2, 0, 962577, 288568, 3245, 65536⟩
    (by decide) selected_cut_36352

theorem selected_cut_36353 : selected 9 ⟨962628, by decide⟩
    (prefixPartial 12 288569) = some ⟨12, 2, 0, 962628, 288569, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_288569_962628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288569 ⟨962628, by decide⟩ :=
  accepted_of_selected 12 288569 ⟨962628, by decide⟩ ⟨12, 2, 0, 962628, 288569, 2813, 65536⟩
    (by decide) selected_cut_36353

theorem selected_cut_36354 : selected 9 ⟨962684, by decide⟩
    (prefixPartial 12 288570) = some ⟨12, 2, 0, 962684, 288570, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_288570_962684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288570 ⟨962684, by decide⟩ :=
  accepted_of_selected 12 288570 ⟨962684, by decide⟩ ⟨12, 2, 0, 962684, 288570, 2949, 65536⟩
    (by decide) selected_cut_36354

theorem selected_cut_36355 : selected 9 ⟨962746, by decide⟩
    (prefixPartial 12 288571) = some ⟨12, 2, 0, 962746, 288571, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_288571_962746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288571 ⟨962746, by decide⟩ :=
  accepted_of_selected 12 288571 ⟨962746, by decide⟩ ⟨12, 2, 0, 962746, 288571, 3293, 65536⟩
    (by decide) selected_cut_36355

theorem unmarked_context_11_72142_962747 : frontier 10 ⟨962747, by decide⟩
    (prefixCache 11 72142) (prefixPartial 11 72142) = false := by
  decide +kernel

theorem node_context_11_72142_962747 : EJMOriginalGlobalDAGData.nodes 10 ⟨962747, by decide⟩ =
    .split (coordinate 11) (![⟨962577, by decide⟩,⟨962628, by decide⟩,⟨962684, by decide⟩,⟨962746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72142_962747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72142 ⟨962747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72142
    ⟨962747, by decide⟩ (by decide) (![⟨962577, by decide⟩,⟨962628, by decide⟩,⟨962684, by decide⟩,⟨962746, by decide⟩]) unmarked_context_11_72142_962747 node_context_11_72142_962747
  intro a
  fin_cases a
  · exact context_12_288568_962577
  · exact context_12_288569_962628
  · exact context_12_288570_962684
  · exact context_12_288571_962746

theorem selected_cut_36356 : selected 9 ⟨962799, by decide⟩
    (prefixPartial 12 288572) = some ⟨12, 2, 0, 962799, 288572, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_288572_962799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288572 ⟨962799, by decide⟩ :=
  accepted_of_selected 12 288572 ⟨962799, by decide⟩ ⟨12, 2, 0, 962799, 288572, 2653, 65536⟩
    (by decide) selected_cut_36356

theorem selected_cut_36357 : selected 9 ⟨962840, by decide⟩
    (prefixPartial 12 288573) = some ⟨12, 2, 0, 962840, 288573, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_288573_962840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288573 ⟨962840, by decide⟩ :=
  accepted_of_selected 12 288573 ⟨962840, by decide⟩ ⟨12, 2, 0, 962840, 288573, 2281, 65536⟩
    (by decide) selected_cut_36357

theorem selected_cut_36358 : selected 9 ⟨962896, by decide⟩
    (prefixPartial 12 288574) = some ⟨12, 2, 0, 962896, 288574, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_288574_962896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288574 ⟨962896, by decide⟩ :=
  accepted_of_selected 12 288574 ⟨962896, by decide⟩ ⟨12, 2, 0, 962896, 288574, 3005, 65536⟩
    (by decide) selected_cut_36358

theorem selected_cut_36359 : selected 9 ⟨762108, by decide⟩
    (prefixPartial 12 288575) = some ⟨12, 1, 0, 762108, 288575, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288575_762108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288575 ⟨762108, by decide⟩ :=
  accepted_of_selected 12 288575 ⟨762108, by decide⟩ ⟨12, 1, 0, 762108, 288575, 1, 65536⟩
    (by decide) selected_cut_36359

theorem unmarked_context_11_72143_962897 : frontier 10 ⟨962897, by decide⟩
    (prefixCache 11 72143) (prefixPartial 11 72143) = false := by
  decide +kernel

theorem node_context_11_72143_962897 : EJMOriginalGlobalDAGData.nodes 10 ⟨962897, by decide⟩ =
    .split (coordinate 11) (![⟨962799, by decide⟩,⟨962840, by decide⟩,⟨962896, by decide⟩,⟨762108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72143_962897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72143 ⟨962897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72143
    ⟨962897, by decide⟩ (by decide) (![⟨962799, by decide⟩,⟨962840, by decide⟩,⟨962896, by decide⟩,⟨762108, by decide⟩]) unmarked_context_11_72143_962897 node_context_11_72143_962897
  intro a
  fin_cases a
  · exact context_12_288572_962799
  · exact context_12_288573_962840
  · exact context_12_288574_962896
  · exact context_12_288575_762108

theorem unmarked_context_10_18035_962898 : frontier 11 ⟨962898, by decide⟩
    (prefixCache 10 18035) (prefixPartial 10 18035) = false := by
  decide +kernel

theorem node_context_10_18035_962898 : EJMOriginalGlobalDAGData.nodes 11 ⟨962898, by decide⟩ =
    .split (coordinate 10) (![⟨962328, by decide⟩,⟨962513, by decide⟩,⟨962747, by decide⟩,⟨962897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18035_962898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18035 ⟨962898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18035
    ⟨962898, by decide⟩ (by decide) (![⟨962328, by decide⟩,⟨962513, by decide⟩,⟨962747, by decide⟩,⟨962897, by decide⟩]) unmarked_context_10_18035_962898 node_context_10_18035_962898
  intro a
  fin_cases a
  · exact context_11_72140_962328
  · exact context_11_72141_962513
  · exact context_11_72142_962747
  · exact context_11_72143_962897

theorem unmarked_context_9_4508_962899 : frontier 12 ⟨962899, by decide⟩
    (prefixCache 9 4508) (prefixPartial 9 4508) = false := by
  decide +kernel

theorem node_context_9_4508_962899 : EJMOriginalGlobalDAGData.nodes 12 ⟨962899, by decide⟩ =
    .split (coordinate 9) (![⟨960734, by decide⟩,⟨961330, by decide⟩,⟨962088, by decide⟩,⟨962898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4508_962899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4508 ⟨962899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4508
    ⟨962899, by decide⟩ (by decide) (![⟨960734, by decide⟩,⟨961330, by decide⟩,⟨962088, by decide⟩,⟨962898, by decide⟩]) unmarked_context_9_4508_962899 node_context_9_4508_962899
  intro a
  fin_cases a
  · exact context_10_18032_960734
  · exact context_10_18033_961330
  · exact context_10_18034_962088
  · exact context_10_18035_962898

theorem selected_cut_36360 : selected 9 ⟨962971, by decide⟩
    (prefixPartial 12 288576) = some ⟨12, 2, 0, 962971, 288576, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_288576_962971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288576 ⟨962971, by decide⟩ :=
  accepted_of_selected 12 288576 ⟨962971, by decide⟩ ⟨12, 2, 0, 962971, 288576, 3317, 65536⟩
    (by decide) selected_cut_36360

theorem selected_cut_36361 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288577) = some ⟨12, 1, 0, 896706, 288577, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288577_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288577 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288577 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288577, 1, 65536⟩
    (by decide) selected_cut_36361

theorem selected_cut_36362 : selected 9 ⟨963022, by decide⟩
    (prefixPartial 12 288578) = some ⟨12, 2, 0, 963022, 288578, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_288578_963022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288578 ⟨963022, by decide⟩ :=
  accepted_of_selected 12 288578 ⟨963022, by decide⟩ ⟨12, 2, 0, 963022, 288578, 3137, 65536⟩
    (by decide) selected_cut_36362

theorem selected_cut_36363 : selected 9 ⟨963072, by decide⟩
    (prefixPartial 12 288579) = some ⟨12, 2, 0, 963072, 288579, 3073, 65536⟩ := by
  decide +kernel

theorem context_12_288579_963072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288579 ⟨963072, by decide⟩ :=
  accepted_of_selected 12 288579 ⟨963072, by decide⟩ ⟨12, 2, 0, 963072, 288579, 3073, 65536⟩
    (by decide) selected_cut_36363

theorem unmarked_context_11_72144_963073 : frontier 10 ⟨963073, by decide⟩
    (prefixCache 11 72144) (prefixPartial 11 72144) = false := by
  decide +kernel

theorem node_context_11_72144_963073 : EJMOriginalGlobalDAGData.nodes 10 ⟨963073, by decide⟩ =
    .split (coordinate 11) (![⟨962971, by decide⟩,⟨896706, by decide⟩,⟨963022, by decide⟩,⟨963072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72144_963073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72144 ⟨963073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72144
    ⟨963073, by decide⟩ (by decide) (![⟨962971, by decide⟩,⟨896706, by decide⟩,⟨963022, by decide⟩,⟨963072, by decide⟩]) unmarked_context_11_72144_963073 node_context_11_72144_963073
  intro a
  fin_cases a
  · exact context_12_288576_962971
  · exact context_12_288577_896706
  · exact context_12_288578_963022
  · exact context_12_288579_963072

theorem selected_cut_36364 : selected 9 ⟨963124, by decide⟩
    (prefixPartial 12 288580) = some ⟨12, 2, 0, 963124, 288580, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_288580_963124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288580 ⟨963124, by decide⟩ :=
  accepted_of_selected 12 288580 ⟨963124, by decide⟩ ⟨12, 2, 0, 963124, 288580, 2601, 65536⟩
    (by decide) selected_cut_36364

theorem selected_cut_36365 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288581) = some ⟨12, 1, 0, 896706, 288581, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288581_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288581 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288581 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288581, 1, 65536⟩
    (by decide) selected_cut_36365

theorem selected_cut_36366 : selected 9 ⟨963168, by decide⟩
    (prefixPartial 12 288582) = some ⟨12, 2, 0, 963168, 288582, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_288582_963168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288582 ⟨963168, by decide⟩ :=
  accepted_of_selected 12 288582 ⟨963168, by decide⟩ ⟨12, 2, 0, 963168, 288582, 2381, 65536⟩
    (by decide) selected_cut_36366

theorem selected_cut_36367 : selected 9 ⟨963210, by decide⟩
    (prefixPartial 12 288583) = some ⟨12, 2, 0, 963210, 288583, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_288583_963210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288583 ⟨963210, by decide⟩ :=
  accepted_of_selected 12 288583 ⟨963210, by decide⟩ ⟨12, 2, 0, 963210, 288583, 2285, 65536⟩
    (by decide) selected_cut_36367

theorem unmarked_context_11_72145_963211 : frontier 10 ⟨963211, by decide⟩
    (prefixCache 11 72145) (prefixPartial 11 72145) = false := by
  decide +kernel

theorem node_context_11_72145_963211 : EJMOriginalGlobalDAGData.nodes 10 ⟨963211, by decide⟩ =
    .split (coordinate 11) (![⟨963124, by decide⟩,⟨896706, by decide⟩,⟨963168, by decide⟩,⟨963210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72145_963211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72145 ⟨963211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72145
    ⟨963211, by decide⟩ (by decide) (![⟨963124, by decide⟩,⟨896706, by decide⟩,⟨963168, by decide⟩,⟨963210, by decide⟩]) unmarked_context_11_72145_963211 node_context_11_72145_963211
  intro a
  fin_cases a
  · exact context_12_288580_963124
  · exact context_12_288581_896706
  · exact context_12_288582_963168
  · exact context_12_288583_963210

theorem selected_cut_36368 : selected 9 ⟨963284, by decide⟩
    (prefixPartial 12 288584) = some ⟨12, 2, 0, 963284, 288584, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_288584_963284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288584 ⟨963284, by decide⟩ :=
  accepted_of_selected 12 288584 ⟨963284, by decide⟩ ⟨12, 2, 0, 963284, 288584, 3181, 65536⟩
    (by decide) selected_cut_36368

theorem selected_cut_36369 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288585) = some ⟨12, 1, 0, 896706, 288585, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288585_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288585 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288585 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288585, 1, 65536⟩
    (by decide) selected_cut_36369

theorem selected_cut_36370 : selected 9 ⟨963330, by decide⟩
    (prefixPartial 12 288586) = some ⟨12, 2, 0, 963330, 288586, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_288586_963330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288586 ⟨963330, by decide⟩ :=
  accepted_of_selected 12 288586 ⟨963330, by decide⟩ ⟨12, 2, 0, 963330, 288586, 2645, 65536⟩
    (by decide) selected_cut_36370

theorem selected_cut_36371 : selected 9 ⟨963380, by decide⟩
    (prefixPartial 12 288587) = some ⟨12, 2, 0, 963380, 288587, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_288587_963380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288587 ⟨963380, by decide⟩ :=
  accepted_of_selected 12 288587 ⟨963380, by decide⟩ ⟨12, 2, 0, 963380, 288587, 2753, 65536⟩
    (by decide) selected_cut_36371

theorem unmarked_context_11_72146_963381 : frontier 10 ⟨963381, by decide⟩
    (prefixCache 11 72146) (prefixPartial 11 72146) = false := by
  decide +kernel

theorem node_context_11_72146_963381 : EJMOriginalGlobalDAGData.nodes 10 ⟨963381, by decide⟩ =
    .split (coordinate 11) (![⟨963284, by decide⟩,⟨896706, by decide⟩,⟨963330, by decide⟩,⟨963380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72146_963381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72146 ⟨963381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72146
    ⟨963381, by decide⟩ (by decide) (![⟨963284, by decide⟩,⟨896706, by decide⟩,⟨963330, by decide⟩,⟨963380, by decide⟩]) unmarked_context_11_72146_963381 node_context_11_72146_963381
  intro a
  fin_cases a
  · exact context_12_288584_963284
  · exact context_12_288585_896706
  · exact context_12_288586_963330
  · exact context_12_288587_963380

theorem selected_cut_36372 : selected 9 ⟨963428, by decide⟩
    (prefixPartial 12 288588) = some ⟨12, 2, 0, 963428, 288588, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_288588_963428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288588 ⟨963428, by decide⟩ :=
  accepted_of_selected 12 288588 ⟨963428, by decide⟩ ⟨12, 2, 0, 963428, 288588, 2677, 65536⟩
    (by decide) selected_cut_36372

theorem selected_cut_36373 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288589) = some ⟨12, 1, 0, 896706, 288589, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288589_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288589 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288589 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288589, 1, 65536⟩
    (by decide) selected_cut_36373

theorem selected_cut_36374 : selected 9 ⟨963476, by decide⟩
    (prefixPartial 12 288590) = some ⟨12, 2, 0, 963476, 288590, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_288590_963476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288590 ⟨963476, by decide⟩ :=
  accepted_of_selected 12 288590 ⟨963476, by decide⟩ ⟨12, 2, 0, 963476, 288590, 2405, 65536⟩
    (by decide) selected_cut_36374

theorem selected_cut_36375 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 288591) = some ⟨12, 1, 0, 903806, 288591, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288591_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288591 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 288591 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 288591, 1, 65536⟩
    (by decide) selected_cut_36375

theorem unmarked_context_11_72147_963477 : frontier 10 ⟨963477, by decide⟩
    (prefixCache 11 72147) (prefixPartial 11 72147) = false := by
  decide +kernel

theorem node_context_11_72147_963477 : EJMOriginalGlobalDAGData.nodes 10 ⟨963477, by decide⟩ =
    .split (coordinate 11) (![⟨963428, by decide⟩,⟨896706, by decide⟩,⟨963476, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72147_963477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72147 ⟨963477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72147
    ⟨963477, by decide⟩ (by decide) (![⟨963428, by decide⟩,⟨896706, by decide⟩,⟨963476, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_72147_963477 node_context_11_72147_963477
  intro a
  fin_cases a
  · exact context_12_288588_963428
  · exact context_12_288589_896706
  · exact context_12_288590_963476
  · exact context_12_288591_903806

theorem unmarked_context_10_18036_963478 : frontier 11 ⟨963478, by decide⟩
    (prefixCache 10 18036) (prefixPartial 10 18036) = false := by
  decide +kernel

theorem node_context_10_18036_963478 : EJMOriginalGlobalDAGData.nodes 11 ⟨963478, by decide⟩ =
    .split (coordinate 10) (![⟨963073, by decide⟩,⟨963211, by decide⟩,⟨963381, by decide⟩,⟨963477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18036_963478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18036 ⟨963478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18036
    ⟨963478, by decide⟩ (by decide) (![⟨963073, by decide⟩,⟨963211, by decide⟩,⟨963381, by decide⟩,⟨963477, by decide⟩]) unmarked_context_10_18036_963478 node_context_10_18036_963478
  intro a
  fin_cases a
  · exact context_11_72144_963073
  · exact context_11_72145_963211
  · exact context_11_72146_963381
  · exact context_11_72147_963477

theorem selected_cut_36376 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18037) = some ⟨10, 1, 0, 893098, 18037, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18037_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18037 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18037 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18037, 1, 1048576⟩
    (by decide) selected_cut_36376

theorem selected_cut_36377 : selected 9 ⟨963513, by decide⟩
    (prefixPartial 12 288608) = some ⟨12, 2, 0, 963513, 288608, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_288608_963513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288608 ⟨963513, by decide⟩ :=
  accepted_of_selected 12 288608 ⟨963513, by decide⟩ ⟨12, 2, 0, 963513, 288608, 2213, 65536⟩
    (by decide) selected_cut_36377

theorem selected_cut_36378 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288609) = some ⟨12, 1, 0, 896706, 288609, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288609_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288609 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288609 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288609, 1, 65536⟩
    (by decide) selected_cut_36378

theorem selected_cut_36379 : selected 9 ⟨963565, by decide⟩
    (prefixPartial 12 288610) = some ⟨12, 2, 0, 963565, 288610, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_288610_963565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288610 ⟨963565, by decide⟩ :=
  accepted_of_selected 12 288610 ⟨963565, by decide⟩ ⟨12, 2, 0, 963565, 288610, 2653, 65536⟩
    (by decide) selected_cut_36379

theorem selected_cut_36380 : selected 9 ⟨963608, by decide⟩
    (prefixPartial 12 288611) = some ⟨12, 2, 0, 963608, 288611, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_288611_963608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288611 ⟨963608, by decide⟩ :=
  accepted_of_selected 12 288611 ⟨963608, by decide⟩ ⟨12, 2, 0, 963608, 288611, 2269, 65536⟩
    (by decide) selected_cut_36380

theorem unmarked_context_11_72152_963609 : frontier 10 ⟨963609, by decide⟩
    (prefixCache 11 72152) (prefixPartial 11 72152) = false := by
  decide +kernel

theorem node_context_11_72152_963609 : EJMOriginalGlobalDAGData.nodes 10 ⟨963609, by decide⟩ =
    .split (coordinate 11) (![⟨963513, by decide⟩,⟨896706, by decide⟩,⟨963565, by decide⟩,⟨963608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72152_963609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72152 ⟨963609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72152
    ⟨963609, by decide⟩ (by decide) (![⟨963513, by decide⟩,⟨896706, by decide⟩,⟨963565, by decide⟩,⟨963608, by decide⟩]) unmarked_context_11_72152_963609 node_context_11_72152_963609
  intro a
  fin_cases a
  · exact context_12_288608_963513
  · exact context_12_288609_896706
  · exact context_12_288610_963565
  · exact context_12_288611_963608

theorem selected_cut_36381 : selected 9 ⟨963634, by decide⟩
    (prefixPartial 12 288612) = some ⟨12, 2, 0, 963634, 288612, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_288612_963634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288612 ⟨963634, by decide⟩ :=
  accepted_of_selected 12 288612 ⟨963634, by decide⟩ ⟨12, 2, 0, 963634, 288612, 1597, 65536⟩
    (by decide) selected_cut_36381

theorem selected_cut_36382 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288613) = some ⟨12, 1, 0, 896706, 288613, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288613_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288613 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288613 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288613, 1, 65536⟩
    (by decide) selected_cut_36382

theorem selected_cut_36383 : selected 9 ⟨963654, by decide⟩
    (prefixPartial 12 288614) = some ⟨12, 2, 0, 963654, 288614, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_288614_963654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288614 ⟨963654, by decide⟩ :=
  accepted_of_selected 12 288614 ⟨963654, by decide⟩ ⟨12, 2, 0, 963654, 288614, 1705, 65536⟩
    (by decide) selected_cut_36383

theorem selected_cut_36384 : selected 9 ⟨963680, by decide⟩
    (prefixPartial 12 288615) = some ⟨12, 2, 0, 963680, 288615, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_288615_963680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288615 ⟨963680, by decide⟩ :=
  accepted_of_selected 12 288615 ⟨963680, by decide⟩ ⟨12, 2, 0, 963680, 288615, 1629, 65536⟩
    (by decide) selected_cut_36384

theorem unmarked_context_11_72153_963681 : frontier 10 ⟨963681, by decide⟩
    (prefixCache 11 72153) (prefixPartial 11 72153) = false := by
  decide +kernel

theorem node_context_11_72153_963681 : EJMOriginalGlobalDAGData.nodes 10 ⟨963681, by decide⟩ =
    .split (coordinate 11) (![⟨963634, by decide⟩,⟨896706, by decide⟩,⟨963654, by decide⟩,⟨963680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72153_963681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72153 ⟨963681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72153
    ⟨963681, by decide⟩ (by decide) (![⟨963634, by decide⟩,⟨896706, by decide⟩,⟨963654, by decide⟩,⟨963680, by decide⟩]) unmarked_context_11_72153_963681 node_context_11_72153_963681
  intro a
  fin_cases a
  · exact context_12_288612_963634
  · exact context_12_288613_896706
  · exact context_12_288614_963654
  · exact context_12_288615_963680

theorem selected_cut_36385 : selected 9 ⟨963715, by decide⟩
    (prefixPartial 12 288616) = some ⟨12, 2, 0, 963715, 288616, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_288616_963715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288616 ⟨963715, by decide⟩ :=
  accepted_of_selected 12 288616 ⟨963715, by decide⟩ ⟨12, 2, 0, 963715, 288616, 2137, 65536⟩
    (by decide) selected_cut_36385

theorem selected_cut_36386 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288617) = some ⟨12, 1, 0, 896706, 288617, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288617_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288617 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288617 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288617, 1, 65536⟩
    (by decide) selected_cut_36386

theorem selected_cut_36387 : selected 9 ⟨963745, by decide⟩
    (prefixPartial 12 288618) = some ⟨12, 2, 0, 963745, 288618, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_288618_963745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288618 ⟨963745, by decide⟩ :=
  accepted_of_selected 12 288618 ⟨963745, by decide⟩ ⟨12, 2, 0, 963745, 288618, 1949, 65536⟩
    (by decide) selected_cut_36387

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
