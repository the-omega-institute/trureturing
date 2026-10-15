/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover118
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_11427 : selected 8 ⟨306029, by decide⟩
    (prefixPartial 13 102588) = some ⟨13, 2, 0, 306029, 102588, 517, 16384⟩ := by
  decide +kernel

theorem context_13_102588_306029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102588 ⟨306029, by decide⟩ :=
  accepted_of_selected 13 102588 ⟨306029, by decide⟩ ⟨13, 2, 0, 306029, 102588, 517, 16384⟩
    (by decide) selected_cut_11427

theorem selected_cut_11428 : selected 8 ⟨306059, by decide⟩
    (prefixPartial 13 102589) = some ⟨13, 2, 0, 306059, 102589, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_102589_306059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102589 ⟨306059, by decide⟩ :=
  accepted_of_selected 13 102589 ⟨306059, by decide⟩ ⟨13, 2, 0, 306059, 102589, 2245, 16384⟩
    (by decide) selected_cut_11428

theorem selected_cut_11429 : selected 8 ⟨306078, by decide⟩
    (prefixPartial 13 102590) = some ⟨13, 2, 0, 306078, 102590, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_102590_306078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102590 ⟨306078, by decide⟩ :=
  accepted_of_selected 13 102590 ⟨306078, by decide⟩ ⟨13, 2, 0, 306078, 102590, 1165, 16384⟩
    (by decide) selected_cut_11429

theorem selected_cut_11430 : selected 8 ⟨306085, by decide⟩
    (prefixPartial 13 102591) = some ⟨13, 2, 0, 306085, 102591, 705, 16384⟩ := by
  decide +kernel

theorem context_13_102591_306085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102591 ⟨306085, by decide⟩ :=
  accepted_of_selected 13 102591 ⟨306085, by decide⟩ ⟨13, 2, 0, 306085, 102591, 705, 16384⟩
    (by decide) selected_cut_11430

theorem unmarked_context_12_25647_306086 : frontier 9 ⟨306086, by decide⟩
    (prefixCache 12 25647) (prefixPartial 12 25647) = false := by
  decide +kernel

theorem node_context_12_25647_306086 : EJMOriginalGlobalDAGData.nodes 9 ⟨306086, by decide⟩ =
    .split (coordinate 12) (![⟨306029, by decide⟩,⟨306059, by decide⟩,⟨306078, by decide⟩,⟨306085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25647_306086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25647 ⟨306086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25647
    ⟨306086, by decide⟩ (by decide) (![⟨306029, by decide⟩,⟨306059, by decide⟩,⟨306078, by decide⟩,⟨306085, by decide⟩]) unmarked_context_12_25647_306086 node_context_12_25647_306086
  intro a
  fin_cases a
  · exact context_13_102588_306029
  · exact context_13_102589_306059
  · exact context_13_102590_306078
  · exact context_13_102591_306085

theorem unmarked_context_11_6411_306087 : frontier 10 ⟨306087, by decide⟩
    (prefixCache 11 6411) (prefixPartial 11 6411) = false := by
  decide +kernel

theorem node_context_11_6411_306087 : EJMOriginalGlobalDAGData.nodes 10 ⟨306087, by decide⟩ =
    .split (coordinate 11) (![⟨305896, by decide⟩,⟨305961, by decide⟩,⟨306020, by decide⟩,⟨306086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6411_306087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6411 ⟨306087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6411
    ⟨306087, by decide⟩ (by decide) (![⟨305896, by decide⟩,⟨305961, by decide⟩,⟨306020, by decide⟩,⟨306086, by decide⟩]) unmarked_context_11_6411_306087 node_context_11_6411_306087
  intro a
  fin_cases a
  · exact context_12_25644_305896
  · exact context_12_25645_305961
  · exact context_12_25646_306020
  · exact context_12_25647_306086

theorem unmarked_context_10_1602_306088 : frontier 11 ⟨306088, by decide⟩
    (prefixCache 10 1602) (prefixPartial 10 1602) = false := by
  decide +kernel

theorem node_context_10_1602_306088 : EJMOriginalGlobalDAGData.nodes 11 ⟨306088, by decide⟩ =
    .split (coordinate 10) (![⟨305332, by decide⟩,⟨305574, by decide⟩,⟨305843, by decide⟩,⟨306087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1602_306088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1602 ⟨306088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1602
    ⟨306088, by decide⟩ (by decide) (![⟨305332, by decide⟩,⟨305574, by decide⟩,⟨305843, by decide⟩,⟨306087, by decide⟩]) unmarked_context_10_1602_306088 node_context_10_1602_306088
  intro a
  fin_cases a
  · exact context_11_6408_305332
  · exact context_11_6409_305574
  · exact context_11_6410_305843
  · exact context_11_6411_306087

theorem selected_cut_11431 : selected 8 ⟨306127, by decide⟩
    (prefixPartial 13 102592) = some ⟨13, 2, 0, 306127, 102592, 837, 16384⟩ := by
  decide +kernel

theorem context_13_102592_306127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102592 ⟨306127, by decide⟩ :=
  accepted_of_selected 13 102592 ⟨306127, by decide⟩ ⟨13, 2, 0, 306127, 102592, 837, 16384⟩
    (by decide) selected_cut_11431

theorem selected_cut_11432 : selected 8 ⟨306222, by decide⟩
    (prefixPartial 13 102593) = some ⟨13, 2, 0, 306222, 102593, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_102593_306222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102593 ⟨306222, by decide⟩ :=
  accepted_of_selected 13 102593 ⟨306222, by decide⟩ ⟨13, 2, 0, 306222, 102593, 2361, 16384⟩
    (by decide) selected_cut_11432

theorem selected_cut_11433 : selected 8 ⟨306261, by decide⟩
    (prefixPartial 13 102594) = some ⟨13, 2, 0, 306261, 102594, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_102594_306261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102594 ⟨306261, by decide⟩ :=
  accepted_of_selected 13 102594 ⟨306261, by decide⟩ ⟨13, 2, 0, 306261, 102594, 1013, 16384⟩
    (by decide) selected_cut_11433

theorem selected_cut_11434 : selected 8 ⟨306277, by decide⟩
    (prefixPartial 13 102595) = some ⟨13, 2, 0, 306277, 102595, 281, 16384⟩ := by
  decide +kernel

theorem context_13_102595_306277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102595 ⟨306277, by decide⟩ :=
  accepted_of_selected 13 102595 ⟨306277, by decide⟩ ⟨13, 2, 0, 306277, 102595, 281, 16384⟩
    (by decide) selected_cut_11434

theorem unmarked_context_12_25648_306278 : frontier 9 ⟨306278, by decide⟩
    (prefixCache 12 25648) (prefixPartial 12 25648) = false := by
  decide +kernel

theorem node_context_12_25648_306278 : EJMOriginalGlobalDAGData.nodes 9 ⟨306278, by decide⟩ =
    .split (coordinate 12) (![⟨306127, by decide⟩,⟨306222, by decide⟩,⟨306261, by decide⟩,⟨306277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25648_306278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25648 ⟨306278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25648
    ⟨306278, by decide⟩ (by decide) (![⟨306127, by decide⟩,⟨306222, by decide⟩,⟨306261, by decide⟩,⟨306277, by decide⟩]) unmarked_context_12_25648_306278 node_context_12_25648_306278
  intro a
  fin_cases a
  · exact context_13_102592_306127
  · exact context_13_102593_306222
  · exact context_13_102594_306261
  · exact context_13_102595_306277

theorem selected_cut_11435 : selected 8 ⟨306287, by decide⟩
    (prefixPartial 13 102596) = some ⟨13, 2, 0, 306287, 102596, 645, 16384⟩ := by
  decide +kernel

theorem context_13_102596_306287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102596 ⟨306287, by decide⟩ :=
  accepted_of_selected 13 102596 ⟨306287, by decide⟩ ⟨13, 2, 0, 306287, 102596, 645, 16384⟩
    (by decide) selected_cut_11435

theorem selected_cut_11436 : selected 8 ⟨306314, by decide⟩
    (prefixPartial 13 102597) = some ⟨13, 2, 0, 306314, 102597, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_102597_306314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102597 ⟨306314, by decide⟩ :=
  accepted_of_selected 13 102597 ⟨306314, by decide⟩ ⟨13, 2, 0, 306314, 102597, 1773, 16384⟩
    (by decide) selected_cut_11436

theorem selected_cut_11437 : selected 8 ⟨306336, by decide⟩
    (prefixPartial 13 102598) = some ⟨13, 2, 0, 306336, 102598, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_102598_306336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102598 ⟨306336, by decide⟩ :=
  accepted_of_selected 13 102598 ⟨306336, by decide⟩ ⟨13, 2, 0, 306336, 102598, 1301, 16384⟩
    (by decide) selected_cut_11437

theorem selected_cut_11438 : selected 8 ⟨306343, by decide⟩
    (prefixPartial 13 102599) = some ⟨13, 2, 0, 306343, 102599, 621, 16384⟩ := by
  decide +kernel

theorem context_13_102599_306343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102599 ⟨306343, by decide⟩ :=
  accepted_of_selected 13 102599 ⟨306343, by decide⟩ ⟨13, 2, 0, 306343, 102599, 621, 16384⟩
    (by decide) selected_cut_11438

theorem unmarked_context_12_25649_306344 : frontier 9 ⟨306344, by decide⟩
    (prefixCache 12 25649) (prefixPartial 12 25649) = false := by
  decide +kernel

theorem node_context_12_25649_306344 : EJMOriginalGlobalDAGData.nodes 9 ⟨306344, by decide⟩ =
    .split (coordinate 12) (![⟨306287, by decide⟩,⟨306314, by decide⟩,⟨306336, by decide⟩,⟨306343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25649_306344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25649 ⟨306344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25649
    ⟨306344, by decide⟩ (by decide) (![⟨306287, by decide⟩,⟨306314, by decide⟩,⟨306336, by decide⟩,⟨306343, by decide⟩]) unmarked_context_12_25649_306344 node_context_12_25649_306344
  intro a
  fin_cases a
  · exact context_13_102596_306287
  · exact context_13_102597_306314
  · exact context_13_102598_306336
  · exact context_13_102599_306343

theorem selected_cut_11439 : selected 8 ⟨306353, by decide⟩
    (prefixPartial 13 102600) = some ⟨13, 2, 0, 306353, 102600, 593, 16384⟩ := by
  decide +kernel

theorem context_13_102600_306353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102600 ⟨306353, by decide⟩ :=
  accepted_of_selected 13 102600 ⟨306353, by decide⟩ ⟨13, 2, 0, 306353, 102600, 593, 16384⟩
    (by decide) selected_cut_11439

theorem selected_cut_11440 : selected 8 ⟨306386, by decide⟩
    (prefixPartial 13 102601) = some ⟨13, 2, 0, 306386, 102601, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_102601_306386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102601 ⟨306386, by decide⟩ :=
  accepted_of_selected 13 102601 ⟨306386, by decide⟩ ⟨13, 2, 0, 306386, 102601, 1941, 16384⟩
    (by decide) selected_cut_11440

theorem selected_cut_11441 : selected 8 ⟨306405, by decide⟩
    (prefixPartial 13 102602) = some ⟨13, 2, 0, 306405, 102602, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_102602_306405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102602 ⟨306405, by decide⟩ :=
  accepted_of_selected 13 102602 ⟨306405, by decide⟩ ⟨13, 2, 0, 306405, 102602, 1105, 16384⟩
    (by decide) selected_cut_11441

theorem selected_cut_11442 : selected 8 ⟨306414, by decide⟩
    (prefixPartial 13 102603) = some ⟨13, 2, 0, 306414, 102603, 741, 16384⟩ := by
  decide +kernel

theorem context_13_102603_306414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102603 ⟨306414, by decide⟩ :=
  accepted_of_selected 13 102603 ⟨306414, by decide⟩ ⟨13, 2, 0, 306414, 102603, 741, 16384⟩
    (by decide) selected_cut_11442

theorem unmarked_context_12_25650_306415 : frontier 9 ⟨306415, by decide⟩
    (prefixCache 12 25650) (prefixPartial 12 25650) = false := by
  decide +kernel

theorem node_context_12_25650_306415 : EJMOriginalGlobalDAGData.nodes 9 ⟨306415, by decide⟩ =
    .split (coordinate 12) (![⟨306353, by decide⟩,⟨306386, by decide⟩,⟨306405, by decide⟩,⟨306414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25650_306415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25650 ⟨306415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25650
    ⟨306415, by decide⟩ (by decide) (![⟨306353, by decide⟩,⟨306386, by decide⟩,⟨306405, by decide⟩,⟨306414, by decide⟩]) unmarked_context_12_25650_306415 node_context_12_25650_306415
  intro a
  fin_cases a
  · exact context_13_102600_306353
  · exact context_13_102601_306386
  · exact context_13_102602_306405
  · exact context_13_102603_306414

theorem selected_cut_11443 : selected 8 ⟨306427, by decide⟩
    (prefixPartial 13 102604) = some ⟨13, 2, 0, 306427, 102604, 609, 16384⟩ := by
  decide +kernel

theorem context_13_102604_306427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102604 ⟨306427, by decide⟩ :=
  accepted_of_selected 13 102604 ⟨306427, by decide⟩ ⟨13, 2, 0, 306427, 102604, 609, 16384⟩
    (by decide) selected_cut_11443

theorem selected_cut_11444 : selected 8 ⟨306475, by decide⟩
    (prefixPartial 13 102605) = some ⟨13, 2, 0, 306475, 102605, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_102605_306475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102605 ⟨306475, by decide⟩ :=
  accepted_of_selected 13 102605 ⟨306475, by decide⟩ ⟨13, 2, 0, 306475, 102605, 2397, 16384⟩
    (by decide) selected_cut_11444

theorem selected_cut_11445 : selected 8 ⟨306504, by decide⟩
    (prefixPartial 13 102606) = some ⟨13, 2, 0, 306504, 102606, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_102606_306504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102606 ⟨306504, by decide⟩ :=
  accepted_of_selected 13 102606 ⟨306504, by decide⟩ ⟨13, 2, 0, 306504, 102606, 1425, 16384⟩
    (by decide) selected_cut_11445

theorem selected_cut_11446 : selected 8 ⟨306510, by decide⟩
    (prefixPartial 13 102607) = some ⟨13, 2, 0, 306510, 102607, 681, 16384⟩ := by
  decide +kernel

theorem context_13_102607_306510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102607 ⟨306510, by decide⟩ :=
  accepted_of_selected 13 102607 ⟨306510, by decide⟩ ⟨13, 2, 0, 306510, 102607, 681, 16384⟩
    (by decide) selected_cut_11446

theorem unmarked_context_12_25651_306511 : frontier 9 ⟨306511, by decide⟩
    (prefixCache 12 25651) (prefixPartial 12 25651) = false := by
  decide +kernel

theorem node_context_12_25651_306511 : EJMOriginalGlobalDAGData.nodes 9 ⟨306511, by decide⟩ =
    .split (coordinate 12) (![⟨306427, by decide⟩,⟨306475, by decide⟩,⟨306504, by decide⟩,⟨306510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25651_306511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25651 ⟨306511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25651
    ⟨306511, by decide⟩ (by decide) (![⟨306427, by decide⟩,⟨306475, by decide⟩,⟨306504, by decide⟩,⟨306510, by decide⟩]) unmarked_context_12_25651_306511 node_context_12_25651_306511
  intro a
  fin_cases a
  · exact context_13_102604_306427
  · exact context_13_102605_306475
  · exact context_13_102606_306504
  · exact context_13_102607_306510

theorem unmarked_context_11_6412_306512 : frontier 10 ⟨306512, by decide⟩
    (prefixCache 11 6412) (prefixPartial 11 6412) = false := by
  decide +kernel

theorem node_context_11_6412_306512 : EJMOriginalGlobalDAGData.nodes 10 ⟨306512, by decide⟩ =
    .split (coordinate 11) (![⟨306278, by decide⟩,⟨306344, by decide⟩,⟨306415, by decide⟩,⟨306511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6412_306512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6412 ⟨306512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6412
    ⟨306512, by decide⟩ (by decide) (![⟨306278, by decide⟩,⟨306344, by decide⟩,⟨306415, by decide⟩,⟨306511, by decide⟩]) unmarked_context_11_6412_306512 node_context_11_6412_306512
  intro a
  fin_cases a
  · exact context_12_25648_306278
  · exact context_12_25649_306344
  · exact context_12_25650_306415
  · exact context_12_25651_306511

theorem selected_cut_11447 : selected 8 ⟨306516, by decide⟩
    (prefixPartial 13 102608) = some ⟨13, 2, 0, 306516, 102608, 333, 16384⟩ := by
  decide +kernel

theorem context_13_102608_306516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102608 ⟨306516, by decide⟩ :=
  accepted_of_selected 13 102608 ⟨306516, by decide⟩ ⟨13, 2, 0, 306516, 102608, 333, 16384⟩
    (by decide) selected_cut_11447

theorem selected_cut_11448 : selected 8 ⟨306551, by decide⟩
    (prefixPartial 13 102609) = some ⟨13, 2, 0, 306551, 102609, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_102609_306551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102609 ⟨306551, by decide⟩ :=
  accepted_of_selected 13 102609 ⟨306551, by decide⟩ ⟨13, 2, 0, 306551, 102609, 2045, 16384⟩
    (by decide) selected_cut_11448

theorem selected_cut_11449 : selected 8 ⟨306567, by decide⟩
    (prefixPartial 13 102610) = some ⟨13, 2, 0, 306567, 102610, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_102610_306567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102610 ⟨306567, by decide⟩ :=
  accepted_of_selected 13 102610 ⟨306567, by decide⟩ ⟨13, 2, 0, 306567, 102610, 1149, 16384⟩
    (by decide) selected_cut_11449

theorem selected_cut_11450 : selected 8 ⟨306575, by decide⟩
    (prefixPartial 13 102611) = some ⟨13, 2, 0, 306575, 102611, 693, 16384⟩ := by
  decide +kernel

theorem context_13_102611_306575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102611 ⟨306575, by decide⟩ :=
  accepted_of_selected 13 102611 ⟨306575, by decide⟩ ⟨13, 2, 0, 306575, 102611, 693, 16384⟩
    (by decide) selected_cut_11450

theorem unmarked_context_12_25652_306576 : frontier 9 ⟨306576, by decide⟩
    (prefixCache 12 25652) (prefixPartial 12 25652) = false := by
  decide +kernel

theorem node_context_12_25652_306576 : EJMOriginalGlobalDAGData.nodes 9 ⟨306576, by decide⟩ =
    .split (coordinate 12) (![⟨306516, by decide⟩,⟨306551, by decide⟩,⟨306567, by decide⟩,⟨306575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25652_306576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25652 ⟨306576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25652
    ⟨306576, by decide⟩ (by decide) (![⟨306516, by decide⟩,⟨306551, by decide⟩,⟨306567, by decide⟩,⟨306575, by decide⟩]) unmarked_context_12_25652_306576 node_context_12_25652_306576
  intro a
  fin_cases a
  · exact context_13_102608_306516
  · exact context_13_102609_306551
  · exact context_13_102610_306567
  · exact context_13_102611_306575

theorem selected_cut_11451 : selected 8 ⟨306583, by decide⟩
    (prefixPartial 13 102612) = some ⟨13, 2, 0, 306583, 102612, 429, 16384⟩ := by
  decide +kernel

theorem context_13_102612_306583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102612 ⟨306583, by decide⟩ :=
  accepted_of_selected 13 102612 ⟨306583, by decide⟩ ⟨13, 2, 0, 306583, 102612, 429, 16384⟩
    (by decide) selected_cut_11451

theorem selected_cut_11452 : selected 8 ⟨306617, by decide⟩
    (prefixPartial 13 102613) = some ⟨13, 2, 0, 306617, 102613, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_102613_306617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102613 ⟨306617, by decide⟩ :=
  accepted_of_selected 13 102613 ⟨306617, by decide⟩ ⟨13, 2, 0, 306617, 102613, 2001, 16384⟩
    (by decide) selected_cut_11452

theorem selected_cut_11453 : selected 8 ⟨306635, by decide⟩
    (prefixPartial 13 102614) = some ⟨13, 2, 0, 306635, 102614, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_102614_306635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102614 ⟨306635, by decide⟩ :=
  accepted_of_selected 13 102614 ⟨306635, by decide⟩ ⟨13, 2, 0, 306635, 102614, 1329, 16384⟩
    (by decide) selected_cut_11453

theorem selected_cut_11454 : selected 8 ⟨306640, by decide⟩
    (prefixPartial 13 102615) = some ⟨13, 2, 0, 306640, 102615, 605, 16384⟩ := by
  decide +kernel

theorem context_13_102615_306640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102615 ⟨306640, by decide⟩ :=
  accepted_of_selected 13 102615 ⟨306640, by decide⟩ ⟨13, 2, 0, 306640, 102615, 605, 16384⟩
    (by decide) selected_cut_11454

theorem unmarked_context_12_25653_306641 : frontier 9 ⟨306641, by decide⟩
    (prefixCache 12 25653) (prefixPartial 12 25653) = false := by
  decide +kernel

theorem node_context_12_25653_306641 : EJMOriginalGlobalDAGData.nodes 9 ⟨306641, by decide⟩ =
    .split (coordinate 12) (![⟨306583, by decide⟩,⟨306617, by decide⟩,⟨306635, by decide⟩,⟨306640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25653_306641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25653 ⟨306641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25653
    ⟨306641, by decide⟩ (by decide) (![⟨306583, by decide⟩,⟨306617, by decide⟩,⟨306635, by decide⟩,⟨306640, by decide⟩]) unmarked_context_12_25653_306641 node_context_12_25653_306641
  intro a
  fin_cases a
  · exact context_13_102612_306583
  · exact context_13_102613_306617
  · exact context_13_102614_306635
  · exact context_13_102615_306640

theorem selected_cut_11455 : selected 8 ⟨306648, by decide⟩
    (prefixPartial 13 102616) = some ⟨13, 2, 0, 306648, 102616, 421, 16384⟩ := by
  decide +kernel

theorem context_13_102616_306648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102616 ⟨306648, by decide⟩ :=
  accepted_of_selected 13 102616 ⟨306648, by decide⟩ ⟨13, 2, 0, 306648, 102616, 421, 16384⟩
    (by decide) selected_cut_11455

theorem selected_cut_11456 : selected 8 ⟨306679, by decide⟩
    (prefixPartial 13 102617) = some ⟨13, 2, 0, 306679, 102617, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_102617_306679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102617 ⟨306679, by decide⟩ :=
  accepted_of_selected 13 102617 ⟨306679, by decide⟩ ⟨13, 2, 0, 306679, 102617, 2377, 16384⟩
    (by decide) selected_cut_11456

theorem selected_cut_11457 : selected 8 ⟨306698, by decide⟩
    (prefixPartial 13 102618) = some ⟨13, 2, 0, 306698, 102618, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_102618_306698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102618 ⟨306698, by decide⟩ :=
  accepted_of_selected 13 102618 ⟨306698, by decide⟩ ⟨13, 2, 0, 306698, 102618, 1173, 16384⟩
    (by decide) selected_cut_11457

theorem selected_cut_11458 : selected 8 ⟨306705, by decide⟩
    (prefixPartial 13 102619) = some ⟨13, 2, 0, 306705, 102619, 737, 16384⟩ := by
  decide +kernel

theorem context_13_102619_306705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102619 ⟨306705, by decide⟩ :=
  accepted_of_selected 13 102619 ⟨306705, by decide⟩ ⟨13, 2, 0, 306705, 102619, 737, 16384⟩
    (by decide) selected_cut_11458

theorem unmarked_context_12_25654_306706 : frontier 9 ⟨306706, by decide⟩
    (prefixCache 12 25654) (prefixPartial 12 25654) = false := by
  decide +kernel

theorem node_context_12_25654_306706 : EJMOriginalGlobalDAGData.nodes 9 ⟨306706, by decide⟩ =
    .split (coordinate 12) (![⟨306648, by decide⟩,⟨306679, by decide⟩,⟨306698, by decide⟩,⟨306705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25654_306706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25654 ⟨306706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25654
    ⟨306706, by decide⟩ (by decide) (![⟨306648, by decide⟩,⟨306679, by decide⟩,⟨306698, by decide⟩,⟨306705, by decide⟩]) unmarked_context_12_25654_306706 node_context_12_25654_306706
  intro a
  fin_cases a
  · exact context_13_102616_306648
  · exact context_13_102617_306679
  · exact context_13_102618_306698
  · exact context_13_102619_306705

theorem selected_cut_11459 : selected 8 ⟨306715, by decide⟩
    (prefixPartial 13 102620) = some ⟨13, 2, 0, 306715, 102620, 429, 16384⟩ := by
  decide +kernel

theorem context_13_102620_306715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102620 ⟨306715, by decide⟩ :=
  accepted_of_selected 13 102620 ⟨306715, by decide⟩ ⟨13, 2, 0, 306715, 102620, 429, 16384⟩
    (by decide) selected_cut_11459

theorem selected_cut_11460 : selected 8 ⟨306758, by decide⟩
    (prefixPartial 13 102621) = some ⟨13, 2, 0, 306758, 102621, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_102621_306758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102621 ⟨306758, by decide⟩ :=
  accepted_of_selected 13 102621 ⟨306758, by decide⟩ ⟨13, 2, 0, 306758, 102621, 2773, 16384⟩
    (by decide) selected_cut_11460

theorem selected_cut_11461 : selected 8 ⟨306782, by decide⟩
    (prefixPartial 13 102622) = some ⟨13, 2, 0, 306782, 102622, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_102622_306782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102622 ⟨306782, by decide⟩ :=
  accepted_of_selected 13 102622 ⟨306782, by decide⟩ ⟨13, 2, 0, 306782, 102622, 1493, 16384⟩
    (by decide) selected_cut_11461

theorem selected_cut_11462 : selected 8 ⟨306789, by decide⟩
    (prefixPartial 13 102623) = some ⟨13, 2, 0, 306789, 102623, 761, 16384⟩ := by
  decide +kernel

theorem context_13_102623_306789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102623 ⟨306789, by decide⟩ :=
  accepted_of_selected 13 102623 ⟨306789, by decide⟩ ⟨13, 2, 0, 306789, 102623, 761, 16384⟩
    (by decide) selected_cut_11462

theorem unmarked_context_12_25655_306790 : frontier 9 ⟨306790, by decide⟩
    (prefixCache 12 25655) (prefixPartial 12 25655) = false := by
  decide +kernel

theorem node_context_12_25655_306790 : EJMOriginalGlobalDAGData.nodes 9 ⟨306790, by decide⟩ =
    .split (coordinate 12) (![⟨306715, by decide⟩,⟨306758, by decide⟩,⟨306782, by decide⟩,⟨306789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25655_306790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25655 ⟨306790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25655
    ⟨306790, by decide⟩ (by decide) (![⟨306715, by decide⟩,⟨306758, by decide⟩,⟨306782, by decide⟩,⟨306789, by decide⟩]) unmarked_context_12_25655_306790 node_context_12_25655_306790
  intro a
  fin_cases a
  · exact context_13_102620_306715
  · exact context_13_102621_306758
  · exact context_13_102622_306782
  · exact context_13_102623_306789

theorem unmarked_context_11_6413_306791 : frontier 10 ⟨306791, by decide⟩
    (prefixCache 11 6413) (prefixPartial 11 6413) = false := by
  decide +kernel

theorem node_context_11_6413_306791 : EJMOriginalGlobalDAGData.nodes 10 ⟨306791, by decide⟩ =
    .split (coordinate 11) (![⟨306576, by decide⟩,⟨306641, by decide⟩,⟨306706, by decide⟩,⟨306790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6413_306791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6413 ⟨306791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6413
    ⟨306791, by decide⟩ (by decide) (![⟨306576, by decide⟩,⟨306641, by decide⟩,⟨306706, by decide⟩,⟨306790, by decide⟩]) unmarked_context_11_6413_306791 node_context_11_6413_306791
  intro a
  fin_cases a
  · exact context_12_25652_306576
  · exact context_12_25653_306641
  · exact context_12_25654_306706
  · exact context_12_25655_306790

theorem selected_cut_11463 : selected 8 ⟨306797, by decide⟩
    (prefixPartial 13 102624) = some ⟨13, 2, 0, 306797, 102624, 269, 16384⟩ := by
  decide +kernel

theorem context_13_102624_306797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102624 ⟨306797, by decide⟩ :=
  accepted_of_selected 13 102624 ⟨306797, by decide⟩ ⟨13, 2, 0, 306797, 102624, 269, 16384⟩
    (by decide) selected_cut_11463

theorem selected_cut_11464 : selected 8 ⟨306840, by decide⟩
    (prefixPartial 13 102625) = some ⟨13, 2, 0, 306840, 102625, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_102625_306840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102625 ⟨306840, by decide⟩ :=
  accepted_of_selected 13 102625 ⟨306840, by decide⟩ ⟨13, 2, 0, 306840, 102625, 2329, 16384⟩
    (by decide) selected_cut_11464

theorem selected_cut_11465 : selected 8 ⟨306862, by decide⟩
    (prefixPartial 13 102626) = some ⟨13, 2, 0, 306862, 102626, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_102626_306862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102626 ⟨306862, by decide⟩ :=
  accepted_of_selected 13 102626 ⟨306862, by decide⟩ ⟨13, 2, 0, 306862, 102626, 1357, 16384⟩
    (by decide) selected_cut_11465

theorem selected_cut_11466 : selected 8 ⟨306873, by decide⟩
    (prefixPartial 13 102627) = some ⟨13, 2, 0, 306873, 102627, 841, 16384⟩ := by
  decide +kernel

theorem context_13_102627_306873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102627 ⟨306873, by decide⟩ :=
  accepted_of_selected 13 102627 ⟨306873, by decide⟩ ⟨13, 2, 0, 306873, 102627, 841, 16384⟩
    (by decide) selected_cut_11466

theorem unmarked_context_12_25656_306874 : frontier 9 ⟨306874, by decide⟩
    (prefixCache 12 25656) (prefixPartial 12 25656) = false := by
  decide +kernel

theorem node_context_12_25656_306874 : EJMOriginalGlobalDAGData.nodes 9 ⟨306874, by decide⟩ =
    .split (coordinate 12) (![⟨306797, by decide⟩,⟨306840, by decide⟩,⟨306862, by decide⟩,⟨306873, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25656_306874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25656 ⟨306874, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25656
    ⟨306874, by decide⟩ (by decide) (![⟨306797, by decide⟩,⟨306840, by decide⟩,⟨306862, by decide⟩,⟨306873, by decide⟩]) unmarked_context_12_25656_306874 node_context_12_25656_306874
  intro a
  fin_cases a
  · exact context_13_102624_306797
  · exact context_13_102625_306840
  · exact context_13_102626_306862
  · exact context_13_102627_306873

theorem selected_cut_11467 : selected 8 ⟨306882, by decide⟩
    (prefixPartial 13 102628) = some ⟨13, 2, 0, 306882, 102628, 389, 16384⟩ := by
  decide +kernel

theorem context_13_102628_306882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102628 ⟨306882, by decide⟩ :=
  accepted_of_selected 13 102628 ⟨306882, by decide⟩ ⟨13, 2, 0, 306882, 102628, 389, 16384⟩
    (by decide) selected_cut_11467

theorem selected_cut_11468 : selected 8 ⟨306922, by decide⟩
    (prefixPartial 13 102629) = some ⟨13, 2, 0, 306922, 102629, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_102629_306922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102629 ⟨306922, by decide⟩ :=
  accepted_of_selected 13 102629 ⟨306922, by decide⟩ ⟨13, 2, 0, 306922, 102629, 2481, 16384⟩
    (by decide) selected_cut_11468

theorem selected_cut_11469 : selected 8 ⟨306941, by decide⟩
    (prefixPartial 13 102630) = some ⟨13, 2, 0, 306941, 102630, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_102630_306941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102630 ⟨306941, by decide⟩ :=
  accepted_of_selected 13 102630 ⟨306941, by decide⟩ ⟨13, 2, 0, 306941, 102630, 1469, 16384⟩
    (by decide) selected_cut_11469

theorem selected_cut_11470 : selected 8 ⟨306949, by decide⟩
    (prefixPartial 13 102631) = some ⟨13, 2, 0, 306949, 102631, 693, 16384⟩ := by
  decide +kernel

theorem context_13_102631_306949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102631 ⟨306949, by decide⟩ :=
  accepted_of_selected 13 102631 ⟨306949, by decide⟩ ⟨13, 2, 0, 306949, 102631, 693, 16384⟩
    (by decide) selected_cut_11470

theorem unmarked_context_12_25657_306950 : frontier 9 ⟨306950, by decide⟩
    (prefixCache 12 25657) (prefixPartial 12 25657) = false := by
  decide +kernel

theorem node_context_12_25657_306950 : EJMOriginalGlobalDAGData.nodes 9 ⟨306950, by decide⟩ =
    .split (coordinate 12) (![⟨306882, by decide⟩,⟨306922, by decide⟩,⟨306941, by decide⟩,⟨306949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25657_306950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25657 ⟨306950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25657
    ⟨306950, by decide⟩ (by decide) (![⟨306882, by decide⟩,⟨306922, by decide⟩,⟨306941, by decide⟩,⟨306949, by decide⟩]) unmarked_context_12_25657_306950 node_context_12_25657_306950
  intro a
  fin_cases a
  · exact context_13_102628_306882
  · exact context_13_102629_306922
  · exact context_13_102630_306941
  · exact context_13_102631_306949

theorem selected_cut_11471 : selected 8 ⟨306955, by decide⟩
    (prefixPartial 13 102632) = some ⟨13, 2, 0, 306955, 102632, 241, 16384⟩ := by
  decide +kernel

theorem context_13_102632_306955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102632 ⟨306955, by decide⟩ :=
  accepted_of_selected 13 102632 ⟨306955, by decide⟩ ⟨13, 2, 0, 306955, 102632, 241, 16384⟩
    (by decide) selected_cut_11471

theorem selected_cut_11472 : selected 8 ⟨306988, by decide⟩
    (prefixPartial 13 102633) = some ⟨13, 2, 0, 306988, 102633, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_102633_306988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102633 ⟨306988, by decide⟩ :=
  accepted_of_selected 13 102633 ⟨306988, by decide⟩ ⟨13, 2, 0, 306988, 102633, 2385, 16384⟩
    (by decide) selected_cut_11472

theorem selected_cut_11473 : selected 8 ⟨307001, by decide⟩
    (prefixPartial 13 102634) = some ⟨13, 2, 0, 307001, 102634, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_102634_307001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102634 ⟨307001, by decide⟩ :=
  accepted_of_selected 13 102634 ⟨307001, by decide⟩ ⟨13, 2, 0, 307001, 102634, 1121, 16384⟩
    (by decide) selected_cut_11473

theorem selected_cut_11474 : selected 8 ⟨307009, by decide⟩
    (prefixPartial 13 102635) = some ⟨13, 2, 0, 307009, 102635, 845, 16384⟩ := by
  decide +kernel

theorem context_13_102635_307009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102635 ⟨307009, by decide⟩ :=
  accepted_of_selected 13 102635 ⟨307009, by decide⟩ ⟨13, 2, 0, 307009, 102635, 845, 16384⟩
    (by decide) selected_cut_11474

theorem unmarked_context_12_25658_307010 : frontier 9 ⟨307010, by decide⟩
    (prefixCache 12 25658) (prefixPartial 12 25658) = false := by
  decide +kernel

theorem node_context_12_25658_307010 : EJMOriginalGlobalDAGData.nodes 9 ⟨307010, by decide⟩ =
    .split (coordinate 12) (![⟨306955, by decide⟩,⟨306988, by decide⟩,⟨307001, by decide⟩,⟨307009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25658_307010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25658 ⟨307010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25658
    ⟨307010, by decide⟩ (by decide) (![⟨306955, by decide⟩,⟨306988, by decide⟩,⟨307001, by decide⟩,⟨307009, by decide⟩]) unmarked_context_12_25658_307010 node_context_12_25658_307010
  intro a
  fin_cases a
  · exact context_13_102632_306955
  · exact context_13_102633_306988
  · exact context_13_102634_307001
  · exact context_13_102635_307009

theorem selected_cut_11475 : selected 8 ⟨307016, by decide⟩
    (prefixPartial 13 102636) = some ⟨13, 2, 0, 307016, 102636, 257, 16384⟩ := by
  decide +kernel

theorem context_13_102636_307016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102636 ⟨307016, by decide⟩ :=
  accepted_of_selected 13 102636 ⟨307016, by decide⟩ ⟨13, 2, 0, 307016, 102636, 257, 16384⟩
    (by decide) selected_cut_11475

theorem selected_cut_11476 : selected 8 ⟨307082, by decide⟩
    (prefixPartial 13 102637) = some ⟨13, 2, 0, 307082, 102637, 2981, 16384⟩ := by
  decide +kernel

theorem context_13_102637_307082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102637 ⟨307082, by decide⟩ :=
  accepted_of_selected 13 102637 ⟨307082, by decide⟩ ⟨13, 2, 0, 307082, 102637, 2981, 16384⟩
    (by decide) selected_cut_11476

theorem selected_cut_11477 : selected 8 ⟨307105, by decide⟩
    (prefixPartial 13 102638) = some ⟨13, 2, 0, 307105, 102638, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_102638_307105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102638 ⟨307105, by decide⟩ :=
  accepted_of_selected 13 102638 ⟨307105, by decide⟩ ⟨13, 2, 0, 307105, 102638, 1489, 16384⟩
    (by decide) selected_cut_11477

theorem selected_cut_11478 : selected 8 ⟨307112, by decide⟩
    (prefixPartial 13 102639) = some ⟨13, 2, 0, 307112, 102639, 849, 16384⟩ := by
  decide +kernel

theorem context_13_102639_307112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102639 ⟨307112, by decide⟩ :=
  accepted_of_selected 13 102639 ⟨307112, by decide⟩ ⟨13, 2, 0, 307112, 102639, 849, 16384⟩
    (by decide) selected_cut_11478

theorem unmarked_context_12_25659_307113 : frontier 9 ⟨307113, by decide⟩
    (prefixCache 12 25659) (prefixPartial 12 25659) = false := by
  decide +kernel

theorem node_context_12_25659_307113 : EJMOriginalGlobalDAGData.nodes 9 ⟨307113, by decide⟩ =
    .split (coordinate 12) (![⟨307016, by decide⟩,⟨307082, by decide⟩,⟨307105, by decide⟩,⟨307112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25659_307113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25659 ⟨307113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25659
    ⟨307113, by decide⟩ (by decide) (![⟨307016, by decide⟩,⟨307082, by decide⟩,⟨307105, by decide⟩,⟨307112, by decide⟩]) unmarked_context_12_25659_307113 node_context_12_25659_307113
  intro a
  fin_cases a
  · exact context_13_102636_307016
  · exact context_13_102637_307082
  · exact context_13_102638_307105
  · exact context_13_102639_307112

theorem unmarked_context_11_6414_307114 : frontier 10 ⟨307114, by decide⟩
    (prefixCache 11 6414) (prefixPartial 11 6414) = false := by
  decide +kernel

theorem node_context_11_6414_307114 : EJMOriginalGlobalDAGData.nodes 10 ⟨307114, by decide⟩ =
    .split (coordinate 11) (![⟨306874, by decide⟩,⟨306950, by decide⟩,⟨307010, by decide⟩,⟨307113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6414_307114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6414 ⟨307114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6414
    ⟨307114, by decide⟩ (by decide) (![⟨306874, by decide⟩,⟨306950, by decide⟩,⟨307010, by decide⟩,⟨307113, by decide⟩]) unmarked_context_11_6414_307114 node_context_11_6414_307114
  intro a
  fin_cases a
  · exact context_12_25656_306874
  · exact context_12_25657_306950
  · exact context_12_25658_307010
  · exact context_12_25659_307113

theorem selected_cut_11479 : selected 9 ⟨307178, by decide⟩
    (prefixPartial 12 25660) = some ⟨12, 2, 0, 307178, 25660, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_25660_307178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25660 ⟨307178, by decide⟩ :=
  accepted_of_selected 12 25660 ⟨307178, by decide⟩ ⟨12, 2, 0, 307178, 25660, 3749, 65536⟩
    (by decide) selected_cut_11479

theorem selected_cut_11480 : selected 8 ⟨307182, by decide⟩
    (prefixPartial 13 102644) = some ⟨13, 2, 0, 307182, 102644, 141, 16384⟩ := by
  decide +kernel

theorem context_13_102644_307182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102644 ⟨307182, by decide⟩ :=
  accepted_of_selected 13 102644 ⟨307182, by decide⟩ ⟨13, 2, 0, 307182, 102644, 141, 16384⟩
    (by decide) selected_cut_11480

theorem selected_cut_11481 : selected 8 ⟨307214, by decide⟩
    (prefixPartial 13 102645) = some ⟨13, 2, 0, 307214, 102645, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_102645_307214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102645 ⟨307214, by decide⟩ :=
  accepted_of_selected 13 102645 ⟨307214, by decide⟩ ⟨13, 2, 0, 307214, 102645, 2101, 16384⟩
    (by decide) selected_cut_11481

theorem selected_cut_11482 : selected 8 ⟨307233, by decide⟩
    (prefixPartial 13 102646) = some ⟨13, 2, 0, 307233, 102646, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_102646_307233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102646 ⟨307233, by decide⟩ :=
  accepted_of_selected 13 102646 ⟨307233, by decide⟩ ⟨13, 2, 0, 307233, 102646, 1373, 16384⟩
    (by decide) selected_cut_11482

theorem selected_cut_11483 : selected 8 ⟨307240, by decide⟩
    (prefixPartial 13 102647) = some ⟨13, 2, 0, 307240, 102647, 601, 16384⟩ := by
  decide +kernel

theorem context_13_102647_307240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102647 ⟨307240, by decide⟩ :=
  accepted_of_selected 13 102647 ⟨307240, by decide⟩ ⟨13, 2, 0, 307240, 102647, 601, 16384⟩
    (by decide) selected_cut_11483

theorem unmarked_context_12_25661_307241 : frontier 9 ⟨307241, by decide⟩
    (prefixCache 12 25661) (prefixPartial 12 25661) = false := by
  decide +kernel

theorem node_context_12_25661_307241 : EJMOriginalGlobalDAGData.nodes 9 ⟨307241, by decide⟩ =
    .split (coordinate 12) (![⟨307182, by decide⟩,⟨307214, by decide⟩,⟨307233, by decide⟩,⟨307240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25661_307241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25661 ⟨307241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25661
    ⟨307241, by decide⟩ (by decide) (![⟨307182, by decide⟩,⟨307214, by decide⟩,⟨307233, by decide⟩,⟨307240, by decide⟩]) unmarked_context_12_25661_307241 node_context_12_25661_307241
  intro a
  fin_cases a
  · exact context_13_102644_307182
  · exact context_13_102645_307214
  · exact context_13_102646_307233
  · exact context_13_102647_307240

theorem selected_cut_11484 : selected 8 ⟨307245, by decide⟩
    (prefixPartial 13 102648) = some ⟨13, 2, 0, 307245, 102648, 81, 16384⟩ := by
  decide +kernel

theorem context_13_102648_307245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102648 ⟨307245, by decide⟩ :=
  accepted_of_selected 13 102648 ⟨307245, by decide⟩ ⟨13, 2, 0, 307245, 102648, 81, 16384⟩
    (by decide) selected_cut_11484

theorem selected_cut_11485 : selected 8 ⟨307275, by decide⟩
    (prefixPartial 13 102649) = some ⟨13, 2, 0, 307275, 102649, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_102649_307275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102649 ⟨307275, by decide⟩ :=
  accepted_of_selected 13 102649 ⟨307275, by decide⟩ ⟨13, 2, 0, 307275, 102649, 2241, 16384⟩
    (by decide) selected_cut_11485

theorem selected_cut_11486 : selected 8 ⟨307292, by decide⟩
    (prefixPartial 13 102650) = some ⟨13, 2, 0, 307292, 102650, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_102650_307292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102650 ⟨307292, by decide⟩ :=
  accepted_of_selected 13 102650 ⟨307292, by decide⟩ ⟨13, 2, 0, 307292, 102650, 1193, 16384⟩
    (by decide) selected_cut_11486

theorem selected_cut_11487 : selected 8 ⟨307298, by decide⟩
    (prefixPartial 13 102651) = some ⟨13, 2, 0, 307298, 102651, 725, 16384⟩ := by
  decide +kernel

theorem context_13_102651_307298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102651 ⟨307298, by decide⟩ :=
  accepted_of_selected 13 102651 ⟨307298, by decide⟩ ⟨13, 2, 0, 307298, 102651, 725, 16384⟩
    (by decide) selected_cut_11487

theorem unmarked_context_12_25662_307299 : frontier 9 ⟨307299, by decide⟩
    (prefixCache 12 25662) (prefixPartial 12 25662) = false := by
  decide +kernel

theorem node_context_12_25662_307299 : EJMOriginalGlobalDAGData.nodes 9 ⟨307299, by decide⟩ =
    .split (coordinate 12) (![⟨307245, by decide⟩,⟨307275, by decide⟩,⟨307292, by decide⟩,⟨307298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25662_307299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25662 ⟨307299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25662
    ⟨307299, by decide⟩ (by decide) (![⟨307245, by decide⟩,⟨307275, by decide⟩,⟨307292, by decide⟩,⟨307298, by decide⟩]) unmarked_context_12_25662_307299 node_context_12_25662_307299
  intro a
  fin_cases a
  · exact context_13_102648_307245
  · exact context_13_102649_307275
  · exact context_13_102650_307292
  · exact context_13_102651_307298

theorem selected_cut_11488 : selected 8 ⟨307302, by decide⟩
    (prefixPartial 13 102652) = some ⟨13, 2, 0, 307302, 102652, 49, 16384⟩ := by
  decide +kernel

theorem context_13_102652_307302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102652 ⟨307302, by decide⟩ :=
  accepted_of_selected 13 102652 ⟨307302, by decide⟩ ⟨13, 2, 0, 307302, 102652, 49, 16384⟩
    (by decide) selected_cut_11488

theorem selected_cut_11489 : selected 8 ⟨307345, by decide⟩
    (prefixPartial 13 102653) = some ⟨13, 2, 0, 307345, 102653, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_102653_307345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102653 ⟨307345, by decide⟩ :=
  accepted_of_selected 13 102653 ⟨307345, by decide⟩ ⟨13, 2, 0, 307345, 102653, 2569, 16384⟩
    (by decide) selected_cut_11489

theorem selected_cut_11490 : selected 8 ⟨307369, by decide⟩
    (prefixPartial 13 102654) = some ⟨13, 2, 0, 307369, 102654, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_102654_307369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102654 ⟨307369, by decide⟩ :=
  accepted_of_selected 13 102654 ⟨307369, by decide⟩ ⟨13, 2, 0, 307369, 102654, 1493, 16384⟩
    (by decide) selected_cut_11490

theorem selected_cut_11491 : selected 8 ⟨307376, by decide⟩
    (prefixPartial 13 102655) = some ⟨13, 2, 0, 307376, 102655, 697, 16384⟩ := by
  decide +kernel

theorem context_13_102655_307376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102655 ⟨307376, by decide⟩ :=
  accepted_of_selected 13 102655 ⟨307376, by decide⟩ ⟨13, 2, 0, 307376, 102655, 697, 16384⟩
    (by decide) selected_cut_11491

theorem unmarked_context_12_25663_307377 : frontier 9 ⟨307377, by decide⟩
    (prefixCache 12 25663) (prefixPartial 12 25663) = false := by
  decide +kernel

theorem node_context_12_25663_307377 : EJMOriginalGlobalDAGData.nodes 9 ⟨307377, by decide⟩ =
    .split (coordinate 12) (![⟨307302, by decide⟩,⟨307345, by decide⟩,⟨307369, by decide⟩,⟨307376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25663_307377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25663 ⟨307377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25663
    ⟨307377, by decide⟩ (by decide) (![⟨307302, by decide⟩,⟨307345, by decide⟩,⟨307369, by decide⟩,⟨307376, by decide⟩]) unmarked_context_12_25663_307377 node_context_12_25663_307377
  intro a
  fin_cases a
  · exact context_13_102652_307302
  · exact context_13_102653_307345
  · exact context_13_102654_307369
  · exact context_13_102655_307376

theorem unmarked_context_11_6415_307378 : frontier 10 ⟨307378, by decide⟩
    (prefixCache 11 6415) (prefixPartial 11 6415) = false := by
  decide +kernel

theorem node_context_11_6415_307378 : EJMOriginalGlobalDAGData.nodes 10 ⟨307378, by decide⟩ =
    .split (coordinate 11) (![⟨307178, by decide⟩,⟨307241, by decide⟩,⟨307299, by decide⟩,⟨307377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6415_307378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6415 ⟨307378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6415
    ⟨307378, by decide⟩ (by decide) (![⟨307178, by decide⟩,⟨307241, by decide⟩,⟨307299, by decide⟩,⟨307377, by decide⟩]) unmarked_context_11_6415_307378 node_context_11_6415_307378
  intro a
  fin_cases a
  · exact context_12_25660_307178
  · exact context_12_25661_307241
  · exact context_12_25662_307299
  · exact context_12_25663_307377

theorem unmarked_context_10_1603_307379 : frontier 11 ⟨307379, by decide⟩
    (prefixCache 10 1603) (prefixPartial 10 1603) = false := by
  decide +kernel

theorem node_context_10_1603_307379 : EJMOriginalGlobalDAGData.nodes 11 ⟨307379, by decide⟩ =
    .split (coordinate 10) (![⟨306512, by decide⟩,⟨306791, by decide⟩,⟨307114, by decide⟩,⟨307378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1603_307379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1603 ⟨307379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1603
    ⟨307379, by decide⟩ (by decide) (![⟨306512, by decide⟩,⟨306791, by decide⟩,⟨307114, by decide⟩,⟨307378, by decide⟩]) unmarked_context_10_1603_307379 node_context_10_1603_307379
  intro a
  fin_cases a
  · exact context_11_6412_306512
  · exact context_11_6413_306791
  · exact context_11_6414_307114
  · exact context_11_6415_307378

theorem unmarked_context_9_400_307380 : frontier 12 ⟨307380, by decide⟩
    (prefixCache 9 400) (prefixPartial 9 400) = false := by
  decide +kernel

theorem node_context_9_400_307380 : EJMOriginalGlobalDAGData.nodes 12 ⟨307380, by decide⟩ =
    .split (coordinate 9) (![⟨303791, by decide⟩,⟨305013, by decide⟩,⟨306088, by decide⟩,⟨307379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_400_307380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 400 ⟨307380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 400
    ⟨307380, by decide⟩ (by decide) (![⟨303791, by decide⟩,⟨305013, by decide⟩,⟨306088, by decide⟩,⟨307379, by decide⟩]) unmarked_context_9_400_307380 node_context_9_400_307380
  intro a
  fin_cases a
  · exact context_10_1600_303791
  · exact context_10_1601_305013
  · exact context_10_1602_306088
  · exact context_10_1603_307379

theorem selected_cut_11492 : selected 9 ⟨307381, by decide⟩
    (prefixPartial 12 25664) = some ⟨12, 1, 0, 307381, 25664, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25664_307381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25664 ⟨307381, by decide⟩ :=
  accepted_of_selected 12 25664 ⟨307381, by decide⟩ ⟨12, 1, 0, 307381, 25664, 1, 65536⟩
    (by decide) selected_cut_11492

theorem selected_cut_11493 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102660) = some ⟨13, 1, 0, 3444, 102660, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102660_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102660 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102660 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102660, 1, 16384⟩
    (by decide) selected_cut_11493

theorem selected_cut_11494 : selected 8 ⟨307422, by decide⟩
    (prefixPartial 13 102661) = some ⟨13, 2, 0, 307422, 102661, 2937, 16384⟩ := by
  decide +kernel

theorem context_13_102661_307422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102661 ⟨307422, by decide⟩ :=
  accepted_of_selected 13 102661 ⟨307422, by decide⟩ ⟨13, 2, 0, 307422, 102661, 2937, 16384⟩
    (by decide) selected_cut_11494

theorem selected_cut_11495 : selected 8 ⟨307467, by decide⟩
    (prefixPartial 13 102662) = some ⟨13, 2, 0, 307467, 102662, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_102662_307467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102662 ⟨307467, by decide⟩ :=
  accepted_of_selected 13 102662 ⟨307467, by decide⟩ ⟨13, 2, 0, 307467, 102662, 2325, 16384⟩
    (by decide) selected_cut_11495

theorem selected_cut_11496 : selected 8 ⟨307491, by decide⟩
    (prefixPartial 13 102663) = some ⟨13, 2, 0, 307491, 102663, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_102663_307491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102663 ⟨307491, by decide⟩ :=
  accepted_of_selected 13 102663 ⟨307491, by decide⟩ ⟨13, 2, 0, 307491, 102663, 1113, 16384⟩
    (by decide) selected_cut_11496

theorem unmarked_context_12_25665_307492 : frontier 9 ⟨307492, by decide⟩
    (prefixCache 12 25665) (prefixPartial 12 25665) = false := by
  decide +kernel

theorem node_context_12_25665_307492 : EJMOriginalGlobalDAGData.nodes 9 ⟨307492, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨307422, by decide⟩,⟨307467, by decide⟩,⟨307491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25665_307492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25665 ⟨307492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25665
    ⟨307492, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨307422, by decide⟩,⟨307467, by decide⟩,⟨307491, by decide⟩]) unmarked_context_12_25665_307492 node_context_12_25665_307492
  intro a
  fin_cases a
  · exact context_13_102660_3444
  · exact context_13_102661_307422
  · exact context_13_102662_307467
  · exact context_13_102663_307491

theorem selected_cut_11497 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102664) = some ⟨13, 1, 0, 3444, 102664, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102664_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102664 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102664 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102664, 1, 16384⟩
    (by decide) selected_cut_11497

theorem selected_cut_11498 : selected 8 ⟨307525, by decide⟩
    (prefixPartial 13 102665) = some ⟨13, 2, 0, 307525, 102665, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_102665_307525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102665 ⟨307525, by decide⟩ :=
  accepted_of_selected 13 102665 ⟨307525, by decide⟩ ⟨13, 2, 0, 307525, 102665, 2417, 16384⟩
    (by decide) selected_cut_11498

theorem selected_cut_11499 : selected 8 ⟨307548, by decide⟩
    (prefixPartial 13 102666) = some ⟨13, 2, 0, 307548, 102666, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_102666_307548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102666 ⟨307548, by decide⟩ :=
  accepted_of_selected 13 102666 ⟨307548, by decide⟩ ⟨13, 2, 0, 307548, 102666, 1465, 16384⟩
    (by decide) selected_cut_11499

theorem selected_cut_11500 : selected 8 ⟨307557, by decide⟩
    (prefixPartial 13 102667) = some ⟨13, 2, 0, 307557, 102667, 845, 16384⟩ := by
  decide +kernel

theorem context_13_102667_307557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102667 ⟨307557, by decide⟩ :=
  accepted_of_selected 13 102667 ⟨307557, by decide⟩ ⟨13, 2, 0, 307557, 102667, 845, 16384⟩
    (by decide) selected_cut_11500

theorem unmarked_context_12_25666_307558 : frontier 9 ⟨307558, by decide⟩
    (prefixCache 12 25666) (prefixPartial 12 25666) = false := by
  decide +kernel

theorem node_context_12_25666_307558 : EJMOriginalGlobalDAGData.nodes 9 ⟨307558, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨307525, by decide⟩,⟨307548, by decide⟩,⟨307557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25666_307558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25666 ⟨307558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25666
    ⟨307558, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨307525, by decide⟩,⟨307548, by decide⟩,⟨307557, by decide⟩]) unmarked_context_12_25666_307558 node_context_12_25666_307558
  intro a
  fin_cases a
  · exact context_13_102664_3444
  · exact context_13_102665_307525
  · exact context_13_102666_307548
  · exact context_13_102667_307557

theorem selected_cut_11501 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102668) = some ⟨13, 1, 0, 3444, 102668, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102668_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102668 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102668 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102668, 1, 16384⟩
    (by decide) selected_cut_11501

theorem selected_cut_11502 : selected 8 ⟨307585, by decide⟩
    (prefixPartial 13 102669) = some ⟨13, 2, 0, 307585, 102669, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_102669_307585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102669 ⟨307585, by decide⟩ :=
  accepted_of_selected 13 102669 ⟨307585, by decide⟩ ⟨13, 2, 0, 307585, 102669, 2485, 16384⟩
    (by decide) selected_cut_11502

theorem selected_cut_11503 : selected 8 ⟨307606, by decide⟩
    (prefixPartial 13 102670) = some ⟨13, 2, 0, 307606, 102670, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_102670_307606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102670 ⟨307606, by decide⟩ :=
  accepted_of_selected 13 102670 ⟨307606, by decide⟩ ⟨13, 2, 0, 307606, 102670, 1609, 16384⟩
    (by decide) selected_cut_11503

theorem selected_cut_11504 : selected 8 ⟨307615, by decide⟩
    (prefixPartial 13 102671) = some ⟨13, 2, 0, 307615, 102671, 773, 16384⟩ := by
  decide +kernel

theorem context_13_102671_307615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102671 ⟨307615, by decide⟩ :=
  accepted_of_selected 13 102671 ⟨307615, by decide⟩ ⟨13, 2, 0, 307615, 102671, 773, 16384⟩
    (by decide) selected_cut_11504

theorem unmarked_context_12_25667_307616 : frontier 9 ⟨307616, by decide⟩
    (prefixCache 12 25667) (prefixPartial 12 25667) = false := by
  decide +kernel

theorem node_context_12_25667_307616 : EJMOriginalGlobalDAGData.nodes 9 ⟨307616, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨307585, by decide⟩,⟨307606, by decide⟩,⟨307615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25667_307616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25667 ⟨307616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25667
    ⟨307616, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨307585, by decide⟩,⟨307606, by decide⟩,⟨307615, by decide⟩]) unmarked_context_12_25667_307616 node_context_12_25667_307616
  intro a
  fin_cases a
  · exact context_13_102668_3444
  · exact context_13_102669_307585
  · exact context_13_102670_307606
  · exact context_13_102671_307615

theorem unmarked_context_11_6416_307617 : frontier 10 ⟨307617, by decide⟩
    (prefixCache 11 6416) (prefixPartial 11 6416) = false := by
  decide +kernel

theorem node_context_11_6416_307617 : EJMOriginalGlobalDAGData.nodes 10 ⟨307617, by decide⟩ =
    .split (coordinate 11) (![⟨307381, by decide⟩,⟨307492, by decide⟩,⟨307558, by decide⟩,⟨307616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6416_307617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6416 ⟨307617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6416
    ⟨307617, by decide⟩ (by decide) (![⟨307381, by decide⟩,⟨307492, by decide⟩,⟨307558, by decide⟩,⟨307616, by decide⟩]) unmarked_context_11_6416_307617 node_context_11_6416_307617
  intro a
  fin_cases a
  · exact context_12_25664_307381
  · exact context_12_25665_307492
  · exact context_12_25666_307558
  · exact context_12_25667_307616

theorem selected_cut_11505 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102672) = some ⟨13, 1, 0, 3444, 102672, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102672_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102672 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102672 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102672, 1, 16384⟩
    (by decide) selected_cut_11505

theorem selected_cut_11506 : selected 8 ⟨307654, by decide⟩
    (prefixPartial 13 102673) = some ⟨13, 2, 0, 307654, 102673, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_102673_307654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102673 ⟨307654, by decide⟩ :=
  accepted_of_selected 13 102673 ⟨307654, by decide⟩ ⟨13, 2, 0, 307654, 102673, 2289, 16384⟩
    (by decide) selected_cut_11506

theorem selected_cut_11507 : selected 8 ⟨307678, by decide⟩
    (prefixPartial 13 102674) = some ⟨13, 2, 0, 307678, 102674, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_102674_307678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102674 ⟨307678, by decide⟩ :=
  accepted_of_selected 13 102674 ⟨307678, by decide⟩ ⟨13, 2, 0, 307678, 102674, 1533, 16384⟩
    (by decide) selected_cut_11507

theorem selected_cut_11508 : selected 8 ⟨307688, by decide⟩
    (prefixPartial 13 102675) = some ⟨13, 2, 0, 307688, 102675, 757, 16384⟩ := by
  decide +kernel

theorem context_13_102675_307688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102675 ⟨307688, by decide⟩ :=
  accepted_of_selected 13 102675 ⟨307688, by decide⟩ ⟨13, 2, 0, 307688, 102675, 757, 16384⟩
    (by decide) selected_cut_11508

theorem unmarked_context_12_25668_307689 : frontier 9 ⟨307689, by decide⟩
    (prefixCache 12 25668) (prefixPartial 12 25668) = false := by
  decide +kernel

theorem node_context_12_25668_307689 : EJMOriginalGlobalDAGData.nodes 9 ⟨307689, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨307654, by decide⟩,⟨307678, by decide⟩,⟨307688, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25668_307689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25668 ⟨307689, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25668
    ⟨307689, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨307654, by decide⟩,⟨307678, by decide⟩,⟨307688, by decide⟩]) unmarked_context_12_25668_307689 node_context_12_25668_307689
  intro a
  fin_cases a
  · exact context_13_102672_3444
  · exact context_13_102673_307654
  · exact context_13_102674_307678
  · exact context_13_102675_307688

theorem selected_cut_11509 : selected 9 ⟨268917, by decide⟩
    (prefixPartial 12 25669) = some ⟨12, 1, 0, 268917, 25669, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25669_268917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25669 ⟨268917, by decide⟩ :=
  accepted_of_selected 12 25669 ⟨268917, by decide⟩ ⟨12, 1, 0, 268917, 25669, 1, 65536⟩
    (by decide) selected_cut_11509

theorem selected_cut_11510 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102680) = some ⟨13, 1, 0, 3444, 102680, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102680_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102680 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102680 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102680, 1, 16384⟩
    (by decide) selected_cut_11510

theorem selected_cut_11511 : selected 8 ⟨307719, by decide⟩
    (prefixPartial 13 102681) = some ⟨13, 2, 0, 307719, 102681, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_102681_307719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102681 ⟨307719, by decide⟩ :=
  accepted_of_selected 13 102681 ⟨307719, by decide⟩ ⟨13, 2, 0, 307719, 102681, 2357, 16384⟩
    (by decide) selected_cut_11511

theorem selected_cut_11512 : selected 8 ⟨307744, by decide⟩
    (prefixPartial 13 102682) = some ⟨13, 2, 0, 307744, 102682, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_102682_307744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102682 ⟨307744, by decide⟩ :=
  accepted_of_selected 13 102682 ⟨307744, by decide⟩ ⟨13, 2, 0, 307744, 102682, 1649, 16384⟩
    (by decide) selected_cut_11512

theorem selected_cut_11513 : selected 8 ⟨307760, by decide⟩
    (prefixPartial 13 102683) = some ⟨13, 2, 0, 307760, 102683, 873, 16384⟩ := by
  decide +kernel

theorem context_13_102683_307760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102683 ⟨307760, by decide⟩ :=
  accepted_of_selected 13 102683 ⟨307760, by decide⟩ ⟨13, 2, 0, 307760, 102683, 873, 16384⟩
    (by decide) selected_cut_11513

theorem unmarked_context_12_25670_307761 : frontier 9 ⟨307761, by decide⟩
    (prefixCache 12 25670) (prefixPartial 12 25670) = false := by
  decide +kernel

theorem node_context_12_25670_307761 : EJMOriginalGlobalDAGData.nodes 9 ⟨307761, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨307719, by decide⟩,⟨307744, by decide⟩,⟨307760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25670_307761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25670 ⟨307761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25670
    ⟨307761, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨307719, by decide⟩,⟨307744, by decide⟩,⟨307760, by decide⟩]) unmarked_context_12_25670_307761 node_context_12_25670_307761
  intro a
  fin_cases a
  · exact context_13_102680_3444
  · exact context_13_102681_307719
  · exact context_13_102682_307744
  · exact context_13_102683_307760

theorem selected_cut_11514 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102684) = some ⟨13, 1, 0, 3444, 102684, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102684_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102684 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102684 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102684, 1, 16384⟩
    (by decide) selected_cut_11514

theorem selected_cut_11515 : selected 8 ⟨307794, by decide⟩
    (prefixPartial 13 102685) = some ⟨13, 2, 0, 307794, 102685, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_102685_307794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102685 ⟨307794, by decide⟩ :=
  accepted_of_selected 13 102685 ⟨307794, by decide⟩ ⟨13, 2, 0, 307794, 102685, 2357, 16384⟩
    (by decide) selected_cut_11515

theorem selected_cut_11516 : selected 8 ⟨307824, by decide⟩
    (prefixPartial 13 102686) = some ⟨13, 2, 0, 307824, 102686, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_102686_307824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102686 ⟨307824, by decide⟩ :=
  accepted_of_selected 13 102686 ⟨307824, by decide⟩ ⟨13, 2, 0, 307824, 102686, 1729, 16384⟩
    (by decide) selected_cut_11516

theorem selected_cut_11517 : selected 8 ⟨307836, by decide⟩
    (prefixPartial 13 102687) = some ⟨13, 2, 0, 307836, 102687, 881, 16384⟩ := by
  decide +kernel

theorem context_13_102687_307836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102687 ⟨307836, by decide⟩ :=
  accepted_of_selected 13 102687 ⟨307836, by decide⟩ ⟨13, 2, 0, 307836, 102687, 881, 16384⟩
    (by decide) selected_cut_11517

theorem unmarked_context_12_25671_307837 : frontier 9 ⟨307837, by decide⟩
    (prefixCache 12 25671) (prefixPartial 12 25671) = false := by
  decide +kernel

theorem node_context_12_25671_307837 : EJMOriginalGlobalDAGData.nodes 9 ⟨307837, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨307794, by decide⟩,⟨307824, by decide⟩,⟨307836, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25671_307837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25671 ⟨307837, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25671
    ⟨307837, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨307794, by decide⟩,⟨307824, by decide⟩,⟨307836, by decide⟩]) unmarked_context_12_25671_307837 node_context_12_25671_307837
  intro a
  fin_cases a
  · exact context_13_102684_3444
  · exact context_13_102685_307794
  · exact context_13_102686_307824
  · exact context_13_102687_307836

theorem unmarked_context_11_6417_307838 : frontier 10 ⟨307838, by decide⟩
    (prefixCache 11 6417) (prefixPartial 11 6417) = false := by
  decide +kernel

theorem node_context_11_6417_307838 : EJMOriginalGlobalDAGData.nodes 10 ⟨307838, by decide⟩ =
    .split (coordinate 11) (![⟨307689, by decide⟩,⟨268917, by decide⟩,⟨307761, by decide⟩,⟨307837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6417_307838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6417 ⟨307838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6417
    ⟨307838, by decide⟩ (by decide) (![⟨307689, by decide⟩,⟨268917, by decide⟩,⟨307761, by decide⟩,⟨307837, by decide⟩]) unmarked_context_11_6417_307838 node_context_11_6417_307838
  intro a
  fin_cases a
  · exact context_12_25668_307689
  · exact context_12_25669_268917
  · exact context_12_25670_307761
  · exact context_12_25671_307837

theorem selected_cut_11518 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102688) = some ⟨13, 1, 0, 3444, 102688, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102688_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102688 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102688 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102688, 1, 16384⟩
    (by decide) selected_cut_11518

theorem selected_cut_11519 : selected 8 ⟨307876, by decide⟩
    (prefixPartial 13 102689) = some ⟨13, 2, 0, 307876, 102689, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_102689_307876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102689 ⟨307876, by decide⟩ :=
  accepted_of_selected 13 102689 ⟨307876, by decide⟩ ⟨13, 2, 0, 307876, 102689, 2333, 16384⟩
    (by decide) selected_cut_11519

theorem selected_cut_11520 : selected 8 ⟨307900, by decide⟩
    (prefixPartial 13 102690) = some ⟨13, 2, 0, 307900, 102690, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_102690_307900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102690 ⟨307900, by decide⟩ :=
  accepted_of_selected 13 102690 ⟨307900, by decide⟩ ⟨13, 2, 0, 307900, 102690, 1773, 16384⟩
    (by decide) selected_cut_11520

theorem selected_cut_11521 : selected 8 ⟨307915, by decide⟩
    (prefixPartial 13 102691) = some ⟨13, 2, 0, 307915, 102691, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_102691_307915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102691 ⟨307915, by decide⟩ :=
  accepted_of_selected 13 102691 ⟨307915, by decide⟩ ⟨13, 2, 0, 307915, 102691, 1001, 16384⟩
    (by decide) selected_cut_11521

theorem unmarked_context_12_25672_307916 : frontier 9 ⟨307916, by decide⟩
    (prefixCache 12 25672) (prefixPartial 12 25672) = false := by
  decide +kernel

theorem node_context_12_25672_307916 : EJMOriginalGlobalDAGData.nodes 9 ⟨307916, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨307876, by decide⟩,⟨307900, by decide⟩,⟨307915, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25672_307916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25672 ⟨307916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25672
    ⟨307916, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨307876, by decide⟩,⟨307900, by decide⟩,⟨307915, by decide⟩]) unmarked_context_12_25672_307916 node_context_12_25672_307916
  intro a
  fin_cases a
  · exact context_13_102688_3444
  · exact context_13_102689_307876
  · exact context_13_102690_307900
  · exact context_13_102691_307915

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
