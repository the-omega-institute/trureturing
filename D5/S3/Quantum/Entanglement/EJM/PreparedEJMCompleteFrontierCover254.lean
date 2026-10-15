/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover253
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_19278_616491 : frontier 10 ⟨616491, by decide⟩
    (prefixCache 11 19278) (prefixPartial 11 19278) = false := by
  decide +kernel

theorem node_context_11_19278_616491 : EJMOriginalGlobalDAGData.nodes 10 ⟨616491, by decide⟩ =
    .split (coordinate 11) (![⟨616250, by decide⟩,⟨616320, by decide⟩,⟨616394, by decide⟩,⟨616490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19278_616491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19278 ⟨616491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19278
    ⟨616491, by decide⟩ (by decide) (![⟨616250, by decide⟩,⟨616320, by decide⟩,⟨616394, by decide⟩,⟨616490, by decide⟩]) unmarked_context_11_19278_616491 node_context_11_19278_616491
  intro a
  fin_cases a
  · exact context_12_77112_616250
  · exact context_12_77113_616320
  · exact context_12_77114_616394
  · exact context_12_77115_616490

theorem selected_cut_24388 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 77116) = some ⟨12, 1, 0, 445562, 77116, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77116_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77116 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 77116 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 77116, 1, 65536⟩
    (by decide) selected_cut_24388

theorem selected_cut_24389 : selected 8 ⟨616494, by decide⟩
    (prefixPartial 13 308468) = some ⟨13, 2, 0, 616494, 308468, 153, 16384⟩ := by
  decide +kernel

theorem context_13_308468_616494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308468 ⟨616494, by decide⟩ :=
  accepted_of_selected 13 308468 ⟨616494, by decide⟩ ⟨13, 2, 0, 616494, 308468, 153, 16384⟩
    (by decide) selected_cut_24389

theorem selected_cut_24390 : selected 8 ⟨616526, by decide⟩
    (prefixPartial 13 308469) = some ⟨13, 2, 0, 616526, 308469, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_308469_616526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308469 ⟨616526, by decide⟩ :=
  accepted_of_selected 13 308469 ⟨616526, by decide⟩ ⟨13, 2, 0, 616526, 308469, 2773, 16384⟩
    (by decide) selected_cut_24390

theorem selected_cut_24391 : selected 8 ⟨616554, by decide⟩
    (prefixPartial 13 308470) = some ⟨13, 2, 0, 616554, 308470, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_308470_616554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308470 ⟨616554, by decide⟩ :=
  accepted_of_selected 13 308470 ⟨616554, by decide⟩ ⟨13, 2, 0, 616554, 308470, 2257, 16384⟩
    (by decide) selected_cut_24391

theorem selected_cut_24392 : selected 8 ⟨616562, by decide⟩
    (prefixPartial 13 308471) = some ⟨13, 2, 0, 616562, 308471, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_308471_616562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308471 ⟨616562, by decide⟩ :=
  accepted_of_selected 13 308471 ⟨616562, by decide⟩ ⟨13, 2, 0, 616562, 308471, 1085, 16384⟩
    (by decide) selected_cut_24392

theorem unmarked_context_12_77117_616563 : frontier 9 ⟨616563, by decide⟩
    (prefixCache 12 77117) (prefixPartial 12 77117) = false := by
  decide +kernel

theorem node_context_12_77117_616563 : EJMOriginalGlobalDAGData.nodes 9 ⟨616563, by decide⟩ =
    .split (coordinate 12) (![⟨616494, by decide⟩,⟨616526, by decide⟩,⟨616554, by decide⟩,⟨616562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77117_616563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77117 ⟨616563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77117
    ⟨616563, by decide⟩ (by decide) (![⟨616494, by decide⟩,⟨616526, by decide⟩,⟨616554, by decide⟩,⟨616562, by decide⟩]) unmarked_context_12_77117_616563 node_context_12_77117_616563
  intro a
  fin_cases a
  · exact context_13_308468_616494
  · exact context_13_308469_616526
  · exact context_13_308470_616554
  · exact context_13_308471_616562

theorem selected_cut_24393 : selected 8 ⟨616567, by decide⟩
    (prefixPartial 13 308472) = some ⟨13, 2, 0, 616567, 308472, 65, 16384⟩ := by
  decide +kernel

theorem context_13_308472_616567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308472 ⟨616567, by decide⟩ :=
  accepted_of_selected 13 308472 ⟨616567, by decide⟩ ⟨13, 2, 0, 616567, 308472, 65, 16384⟩
    (by decide) selected_cut_24393

theorem selected_cut_24394 : selected 8 ⟨616602, by decide⟩
    (prefixPartial 13 308473) = some ⟨13, 2, 0, 616602, 308473, 2913, 16384⟩ := by
  decide +kernel

theorem context_13_308473_616602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308473 ⟨616602, by decide⟩ :=
  accepted_of_selected 13 308473 ⟨616602, by decide⟩ ⟨13, 2, 0, 616602, 308473, 2913, 16384⟩
    (by decide) selected_cut_24394

theorem selected_cut_24395 : selected 8 ⟨616625, by decide⟩
    (prefixPartial 13 308474) = some ⟨13, 2, 0, 616625, 308474, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_308474_616625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308474 ⟨616625, by decide⟩ :=
  accepted_of_selected 13 308474 ⟨616625, by decide⟩ ⟨13, 2, 0, 616625, 308474, 2037, 16384⟩
    (by decide) selected_cut_24395

theorem selected_cut_24396 : selected 8 ⟨616635, by decide⟩
    (prefixPartial 13 308475) = some ⟨13, 2, 0, 616635, 308475, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_308475_616635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308475 ⟨616635, by decide⟩ :=
  accepted_of_selected 13 308475 ⟨616635, by decide⟩ ⟨13, 2, 0, 616635, 308475, 1121, 16384⟩
    (by decide) selected_cut_24396

theorem unmarked_context_12_77118_616636 : frontier 9 ⟨616636, by decide⟩
    (prefixCache 12 77118) (prefixPartial 12 77118) = false := by
  decide +kernel

theorem node_context_12_77118_616636 : EJMOriginalGlobalDAGData.nodes 9 ⟨616636, by decide⟩ =
    .split (coordinate 12) (![⟨616567, by decide⟩,⟨616602, by decide⟩,⟨616625, by decide⟩,⟨616635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77118_616636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77118 ⟨616636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77118
    ⟨616636, by decide⟩ (by decide) (![⟨616567, by decide⟩,⟨616602, by decide⟩,⟨616625, by decide⟩,⟨616635, by decide⟩]) unmarked_context_12_77118_616636 node_context_12_77118_616636
  intro a
  fin_cases a
  · exact context_13_308472_616567
  · exact context_13_308473_616602
  · exact context_13_308474_616625
  · exact context_13_308475_616635

theorem selected_cut_24397 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 77119) = some ⟨12, 1, 0, 607719, 77119, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77119_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77119 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 77119 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 77119, 1, 65536⟩
    (by decide) selected_cut_24397

theorem unmarked_context_11_19279_616637 : frontier 10 ⟨616637, by decide⟩
    (prefixCache 11 19279) (prefixPartial 11 19279) = false := by
  decide +kernel

theorem node_context_11_19279_616637 : EJMOriginalGlobalDAGData.nodes 10 ⟨616637, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨616563, by decide⟩,⟨616636, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19279_616637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19279 ⟨616637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19279
    ⟨616637, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨616563, by decide⟩,⟨616636, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_19279_616637 node_context_11_19279_616637
  intro a
  fin_cases a
  · exact context_12_77116_445562
  · exact context_12_77117_616563
  · exact context_12_77118_616636
  · exact context_12_77119_607719

theorem unmarked_context_10_4819_616638 : frontier 11 ⟨616638, by decide⟩
    (prefixCache 10 4819) (prefixPartial 10 4819) = false := by
  decide +kernel

theorem node_context_10_4819_616638 : EJMOriginalGlobalDAGData.nodes 11 ⟨616638, by decide⟩ =
    .split (coordinate 10) (![⟨615887, by decide⟩,⟨616138, by decide⟩,⟨616491, by decide⟩,⟨616637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4819_616638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4819 ⟨616638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4819
    ⟨616638, by decide⟩ (by decide) (![⟨615887, by decide⟩,⟨616138, by decide⟩,⟨616491, by decide⟩,⟨616637, by decide⟩]) unmarked_context_10_4819_616638 node_context_10_4819_616638
  intro a
  fin_cases a
  · exact context_11_19276_615887
  · exact context_11_19277_616138
  · exact context_11_19278_616491
  · exact context_11_19279_616637

theorem unmarked_context_9_1204_616639 : frontier 12 ⟨616639, by decide⟩
    (prefixCache 9 1204) (prefixPartial 9 1204) = false := by
  decide +kernel

theorem node_context_9_1204_616639 : EJMOriginalGlobalDAGData.nodes 12 ⟨616639, by decide⟩ =
    .split (coordinate 9) (![⟨613325, by decide⟩,⟨614438, by decide⟩,⟨615656, by decide⟩,⟨616638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1204_616639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1204 ⟨616639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1204
    ⟨616639, by decide⟩ (by decide) (![⟨613325, by decide⟩,⟨614438, by decide⟩,⟨615656, by decide⟩,⟨616638, by decide⟩]) unmarked_context_9_1204_616639 node_context_9_1204_616639
  intro a
  fin_cases a
  · exact context_10_4816_613325
  · exact context_10_4817_614438
  · exact context_10_4818_615656
  · exact context_10_4819_616638

theorem selected_cut_24398 : selected 9 ⟨616697, by decide⟩
    (prefixPartial 12 77120) = some ⟨12, 2, 0, 616697, 77120, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_77120_616697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77120 ⟨616697, by decide⟩ :=
  accepted_of_selected 12 77120 ⟨616697, by decide⟩ ⟨12, 2, 0, 616697, 77120, 3797, 65536⟩
    (by decide) selected_cut_24398

theorem selected_cut_24399 : selected 9 ⟨616753, by decide⟩
    (prefixPartial 12 77121) = some ⟨12, 2, 0, 616753, 77121, 3697, 65536⟩ := by
  decide +kernel

theorem context_12_77121_616753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77121 ⟨616753, by decide⟩ :=
  accepted_of_selected 12 77121 ⟨616753, by decide⟩ ⟨12, 2, 0, 616753, 77121, 3697, 65536⟩
    (by decide) selected_cut_24399

theorem selected_cut_24400 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308488) = some ⟨13, 1, 0, 3444, 308488, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308488_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308488 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308488 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308488, 1, 16384⟩
    (by decide) selected_cut_24400

theorem selected_cut_24401 : selected 8 ⟨616781, by decide⟩
    (prefixPartial 13 308489) = some ⟨13, 2, 0, 616781, 308489, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_308489_616781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308489 ⟨616781, by decide⟩ :=
  accepted_of_selected 13 308489 ⟨616781, by decide⟩ ⟨13, 2, 0, 616781, 308489, 1961, 16384⟩
    (by decide) selected_cut_24401

theorem selected_cut_24402 : selected 8 ⟨616805, by decide⟩
    (prefixPartial 13 308490) = some ⟨13, 2, 0, 616805, 308490, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_308490_616805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308490 ⟨616805, by decide⟩ :=
  accepted_of_selected 13 308490 ⟨616805, by decide⟩ ⟨13, 2, 0, 616805, 308490, 1873, 16384⟩
    (by decide) selected_cut_24402

theorem selected_cut_24403 : selected 8 ⟨616822, by decide⟩
    (prefixPartial 13 308491) = some ⟨13, 2, 0, 616822, 308491, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_308491_616822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308491 ⟨616822, by decide⟩ :=
  accepted_of_selected 13 308491 ⟨616822, by decide⟩ ⟨13, 2, 0, 616822, 308491, 1069, 16384⟩
    (by decide) selected_cut_24403

theorem unmarked_context_12_77122_616823 : frontier 9 ⟨616823, by decide⟩
    (prefixCache 12 77122) (prefixPartial 12 77122) = false := by
  decide +kernel

theorem node_context_12_77122_616823 : EJMOriginalGlobalDAGData.nodes 9 ⟨616823, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨616781, by decide⟩,⟨616805, by decide⟩,⟨616822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77122_616823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77122 ⟨616823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77122
    ⟨616823, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨616781, by decide⟩,⟨616805, by decide⟩,⟨616822, by decide⟩]) unmarked_context_12_77122_616823 node_context_12_77122_616823
  intro a
  fin_cases a
  · exact context_13_308488_3444
  · exact context_13_308489_616781
  · exact context_13_308490_616805
  · exact context_13_308491_616822

theorem selected_cut_24404 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308492) = some ⟨13, 1, 0, 3444, 308492, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308492_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308492 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308492 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308492, 1, 16384⟩
    (by decide) selected_cut_24404

theorem selected_cut_24405 : selected 8 ⟨616847, by decide⟩
    (prefixPartial 13 308493) = some ⟨13, 2, 0, 616847, 308493, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_308493_616847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308493 ⟨616847, by decide⟩ :=
  accepted_of_selected 13 308493 ⟨616847, by decide⟩ ⟨13, 2, 0, 616847, 308493, 2017, 16384⟩
    (by decide) selected_cut_24405

theorem selected_cut_24406 : selected 8 ⟨616876, by decide⟩
    (prefixPartial 13 308494) = some ⟨13, 2, 0, 616876, 308494, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_308494_616876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308494 ⟨616876, by decide⟩ :=
  accepted_of_selected 13 308494 ⟨616876, by decide⟩ ⟨13, 2, 0, 616876, 308494, 1833, 16384⟩
    (by decide) selected_cut_24406

theorem selected_cut_24407 : selected 8 ⟨616888, by decide⟩
    (prefixPartial 13 308495) = some ⟨13, 2, 0, 616888, 308495, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_308495_616888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308495 ⟨616888, by decide⟩ :=
  accepted_of_selected 13 308495 ⟨616888, by decide⟩ ⟨13, 2, 0, 616888, 308495, 1013, 16384⟩
    (by decide) selected_cut_24407

theorem unmarked_context_12_77123_616889 : frontier 9 ⟨616889, by decide⟩
    (prefixCache 12 77123) (prefixPartial 12 77123) = false := by
  decide +kernel

theorem node_context_12_77123_616889 : EJMOriginalGlobalDAGData.nodes 9 ⟨616889, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨616847, by decide⟩,⟨616876, by decide⟩,⟨616888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77123_616889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77123 ⟨616889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77123
    ⟨616889, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨616847, by decide⟩,⟨616876, by decide⟩,⟨616888, by decide⟩]) unmarked_context_12_77123_616889 node_context_12_77123_616889
  intro a
  fin_cases a
  · exact context_13_308492_3444
  · exact context_13_308493_616847
  · exact context_13_308494_616876
  · exact context_13_308495_616888

theorem unmarked_context_11_19280_616890 : frontier 10 ⟨616890, by decide⟩
    (prefixCache 11 19280) (prefixPartial 11 19280) = false := by
  decide +kernel

theorem node_context_11_19280_616890 : EJMOriginalGlobalDAGData.nodes 10 ⟨616890, by decide⟩ =
    .split (coordinate 11) (![⟨616697, by decide⟩,⟨616753, by decide⟩,⟨616823, by decide⟩,⟨616889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19280_616890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19280 ⟨616890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19280
    ⟨616890, by decide⟩ (by decide) (![⟨616697, by decide⟩,⟨616753, by decide⟩,⟨616823, by decide⟩,⟨616889, by decide⟩]) unmarked_context_11_19280_616890 node_context_11_19280_616890
  intro a
  fin_cases a
  · exact context_12_77120_616697
  · exact context_12_77121_616753
  · exact context_12_77122_616823
  · exact context_12_77123_616889

theorem selected_cut_24408 : selected 9 ⟨616940, by decide⟩
    (prefixPartial 12 77124) = some ⟨12, 2, 0, 616940, 77124, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_77124_616940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77124 ⟨616940, by decide⟩ :=
  accepted_of_selected 12 77124 ⟨616940, by decide⟩ ⟨12, 2, 0, 616940, 77124, 3293, 65536⟩
    (by decide) selected_cut_24408

theorem selected_cut_24409 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 77125) = some ⟨12, 1, 0, 441672, 77125, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77125_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77125 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 77125 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 77125, 1, 65536⟩
    (by decide) selected_cut_24409

theorem selected_cut_24410 : selected 9 ⟨616998, by decide⟩
    (prefixPartial 12 77126) = some ⟨12, 2, 0, 616998, 77126, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_77126_616998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77126 ⟨616998, by decide⟩ :=
  accepted_of_selected 12 77126 ⟨616998, by decide⟩ ⟨12, 2, 0, 616998, 77126, 4077, 65536⟩
    (by decide) selected_cut_24410

theorem selected_cut_24411 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308508) = some ⟨13, 1, 0, 3444, 308508, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308508_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308508 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308508 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308508, 1, 16384⟩
    (by decide) selected_cut_24411

theorem selected_cut_24412 : selected 8 ⟨617019, by decide⟩
    (prefixPartial 13 308509) = some ⟨13, 2, 0, 617019, 308509, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_308509_617019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308509 ⟨617019, by decide⟩ :=
  accepted_of_selected 13 308509 ⟨617019, by decide⟩ ⟨13, 2, 0, 617019, 308509, 1681, 16384⟩
    (by decide) selected_cut_24412

theorem selected_cut_24413 : selected 8 ⟨617043, by decide⟩
    (prefixPartial 13 308510) = some ⟨13, 2, 0, 617043, 308510, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_308510_617043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308510 ⟨617043, by decide⟩ :=
  accepted_of_selected 13 308510 ⟨617043, by decide⟩ ⟨13, 2, 0, 617043, 308510, 1725, 16384⟩
    (by decide) selected_cut_24413

theorem selected_cut_24414 : selected 8 ⟨617053, by decide⟩
    (prefixPartial 13 308511) = some ⟨13, 2, 0, 617053, 308511, 869, 16384⟩ := by
  decide +kernel

theorem context_13_308511_617053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308511 ⟨617053, by decide⟩ :=
  accepted_of_selected 13 308511 ⟨617053, by decide⟩ ⟨13, 2, 0, 617053, 308511, 869, 16384⟩
    (by decide) selected_cut_24414

theorem unmarked_context_12_77127_617054 : frontier 9 ⟨617054, by decide⟩
    (prefixCache 12 77127) (prefixPartial 12 77127) = false := by
  decide +kernel

theorem node_context_12_77127_617054 : EJMOriginalGlobalDAGData.nodes 9 ⟨617054, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨617019, by decide⟩,⟨617043, by decide⟩,⟨617053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77127_617054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77127 ⟨617054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77127
    ⟨617054, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨617019, by decide⟩,⟨617043, by decide⟩,⟨617053, by decide⟩]) unmarked_context_12_77127_617054 node_context_12_77127_617054
  intro a
  fin_cases a
  · exact context_13_308508_3444
  · exact context_13_308509_617019
  · exact context_13_308510_617043
  · exact context_13_308511_617053

theorem unmarked_context_11_19281_617055 : frontier 10 ⟨617055, by decide⟩
    (prefixCache 11 19281) (prefixPartial 11 19281) = false := by
  decide +kernel

theorem node_context_11_19281_617055 : EJMOriginalGlobalDAGData.nodes 10 ⟨617055, by decide⟩ =
    .split (coordinate 11) (![⟨616940, by decide⟩,⟨441672, by decide⟩,⟨616998, by decide⟩,⟨617054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19281_617055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19281 ⟨617055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19281
    ⟨617055, by decide⟩ (by decide) (![⟨616940, by decide⟩,⟨441672, by decide⟩,⟨616998, by decide⟩,⟨617054, by decide⟩]) unmarked_context_11_19281_617055 node_context_11_19281_617055
  intro a
  fin_cases a
  · exact context_12_77124_616940
  · exact context_12_77125_441672
  · exact context_12_77126_616998
  · exact context_12_77127_617054

theorem selected_cut_24415 : selected 9 ⟨617107, by decide⟩
    (prefixPartial 12 77128) = some ⟨12, 2, 0, 617107, 77128, 3961, 65536⟩ := by
  decide +kernel

theorem context_12_77128_617107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77128 ⟨617107, by decide⟩ :=
  accepted_of_selected 12 77128 ⟨617107, by decide⟩ ⟨12, 2, 0, 617107, 77128, 3961, 65536⟩
    (by decide) selected_cut_24415

theorem selected_cut_24416 : selected 9 ⟨617168, by decide⟩
    (prefixPartial 12 77129) = some ⟨12, 2, 0, 617168, 77129, 3853, 65536⟩ := by
  decide +kernel

theorem context_12_77129_617168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77129 ⟨617168, by decide⟩ :=
  accepted_of_selected 12 77129 ⟨617168, by decide⟩ ⟨12, 2, 0, 617168, 77129, 3853, 65536⟩
    (by decide) selected_cut_24416

theorem selected_cut_24417 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308520) = some ⟨13, 1, 0, 3444, 308520, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308520_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308520 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308520 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308520, 1, 16384⟩
    (by decide) selected_cut_24417

theorem selected_cut_24418 : selected 8 ⟨617187, by decide⟩
    (prefixPartial 13 308521) = some ⟨13, 2, 0, 617187, 308521, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_308521_617187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308521 ⟨617187, by decide⟩ :=
  accepted_of_selected 13 308521 ⟨617187, by decide⟩ ⟨13, 2, 0, 617187, 308521, 1733, 16384⟩
    (by decide) selected_cut_24418

theorem selected_cut_24419 : selected 8 ⟨617211, by decide⟩
    (prefixPartial 13 308522) = some ⟨13, 2, 0, 617211, 308522, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_308522_617211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308522 ⟨617211, by decide⟩ :=
  accepted_of_selected 13 308522 ⟨617211, by decide⟩ ⟨13, 2, 0, 617211, 308522, 1817, 16384⟩
    (by decide) selected_cut_24419

theorem selected_cut_24420 : selected 8 ⟨617224, by decide⟩
    (prefixPartial 13 308523) = some ⟨13, 2, 0, 617224, 308523, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_308523_617224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308523 ⟨617224, by decide⟩ :=
  accepted_of_selected 13 308523 ⟨617224, by decide⟩ ⟨13, 2, 0, 617224, 308523, 1037, 16384⟩
    (by decide) selected_cut_24420

theorem unmarked_context_12_77130_617225 : frontier 9 ⟨617225, by decide⟩
    (prefixCache 12 77130) (prefixPartial 12 77130) = false := by
  decide +kernel

theorem node_context_12_77130_617225 : EJMOriginalGlobalDAGData.nodes 9 ⟨617225, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨617187, by decide⟩,⟨617211, by decide⟩,⟨617224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77130_617225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77130 ⟨617225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77130
    ⟨617225, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨617187, by decide⟩,⟨617211, by decide⟩,⟨617224, by decide⟩]) unmarked_context_12_77130_617225 node_context_12_77130_617225
  intro a
  fin_cases a
  · exact context_13_308520_3444
  · exact context_13_308521_617187
  · exact context_13_308522_617211
  · exact context_13_308523_617224

theorem selected_cut_24421 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308524) = some ⟨13, 1, 0, 3444, 308524, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308524_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308524 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308524 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308524, 1, 16384⟩
    (by decide) selected_cut_24421

theorem selected_cut_24422 : selected 8 ⟨617248, by decide⟩
    (prefixPartial 13 308525) = some ⟨13, 2, 0, 617248, 308525, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_308525_617248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308525 ⟨617248, by decide⟩ :=
  accepted_of_selected 13 308525 ⟨617248, by decide⟩ ⟨13, 2, 0, 617248, 308525, 1845, 16384⟩
    (by decide) selected_cut_24422

theorem selected_cut_24423 : selected 8 ⟨617278, by decide⟩
    (prefixPartial 13 308526) = some ⟨13, 2, 0, 617278, 308526, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_308526_617278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308526 ⟨617278, by decide⟩ :=
  accepted_of_selected 13 308526 ⟨617278, by decide⟩ ⟨13, 2, 0, 617278, 308526, 1841, 16384⟩
    (by decide) selected_cut_24423

theorem selected_cut_24424 : selected 8 ⟨617291, by decide⟩
    (prefixPartial 13 308527) = some ⟨13, 2, 0, 617291, 308527, 997, 16384⟩ := by
  decide +kernel

theorem context_13_308527_617291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308527 ⟨617291, by decide⟩ :=
  accepted_of_selected 13 308527 ⟨617291, by decide⟩ ⟨13, 2, 0, 617291, 308527, 997, 16384⟩
    (by decide) selected_cut_24424

theorem unmarked_context_12_77131_617292 : frontier 9 ⟨617292, by decide⟩
    (prefixCache 12 77131) (prefixPartial 12 77131) = false := by
  decide +kernel

theorem node_context_12_77131_617292 : EJMOriginalGlobalDAGData.nodes 9 ⟨617292, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨617248, by decide⟩,⟨617278, by decide⟩,⟨617291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77131_617292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77131 ⟨617292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77131
    ⟨617292, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨617248, by decide⟩,⟨617278, by decide⟩,⟨617291, by decide⟩]) unmarked_context_12_77131_617292 node_context_12_77131_617292
  intro a
  fin_cases a
  · exact context_13_308524_3444
  · exact context_13_308525_617248
  · exact context_13_308526_617278
  · exact context_13_308527_617291

theorem unmarked_context_11_19282_617293 : frontier 10 ⟨617293, by decide⟩
    (prefixCache 11 19282) (prefixPartial 11 19282) = false := by
  decide +kernel

theorem node_context_11_19282_617293 : EJMOriginalGlobalDAGData.nodes 10 ⟨617293, by decide⟩ =
    .split (coordinate 11) (![⟨617107, by decide⟩,⟨617168, by decide⟩,⟨617225, by decide⟩,⟨617292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19282_617293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19282 ⟨617293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19282
    ⟨617293, by decide⟩ (by decide) (![⟨617107, by decide⟩,⟨617168, by decide⟩,⟨617225, by decide⟩,⟨617292, by decide⟩]) unmarked_context_11_19282_617293 node_context_11_19282_617293
  intro a
  fin_cases a
  · exact context_12_77128_617107
  · exact context_12_77129_617168
  · exact context_12_77130_617225
  · exact context_12_77131_617292

theorem selected_cut_24425 : selected 9 ⟨617344, by decide⟩
    (prefixPartial 12 77132) = some ⟨12, 2, 0, 617344, 77132, 3589, 65536⟩ := by
  decide +kernel

theorem context_12_77132_617344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77132 ⟨617344, by decide⟩ :=
  accepted_of_selected 12 77132 ⟨617344, by decide⟩ ⟨12, 2, 0, 617344, 77132, 3589, 65536⟩
    (by decide) selected_cut_24425

theorem selected_cut_24426 : selected 9 ⟨617389, by decide⟩
    (prefixPartial 12 77133) = some ⟨12, 2, 0, 617389, 77133, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_77133_617389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77133 ⟨617389, by decide⟩ :=
  accepted_of_selected 12 77133 ⟨617389, by decide⟩ ⟨12, 2, 0, 617389, 77133, 3261, 65536⟩
    (by decide) selected_cut_24426

theorem selected_cut_24427 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308536) = some ⟨13, 1, 0, 3444, 308536, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308536_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308536 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308536 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308536, 1, 16384⟩
    (by decide) selected_cut_24427

theorem selected_cut_24428 : selected 8 ⟨617409, by decide⟩
    (prefixPartial 13 308537) = some ⟨13, 2, 0, 617409, 308537, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_308537_617409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308537 ⟨617409, by decide⟩ :=
  accepted_of_selected 13 308537 ⟨617409, by decide⟩ ⟨13, 2, 0, 617409, 308537, 1509, 16384⟩
    (by decide) selected_cut_24428

theorem selected_cut_24429 : selected 8 ⟨617430, by decide⟩
    (prefixPartial 13 308538) = some ⟨13, 2, 0, 617430, 308538, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_308538_617430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308538 ⟨617430, by decide⟩ :=
  accepted_of_selected 13 308538 ⟨617430, by decide⟩ ⟨13, 2, 0, 617430, 308538, 1717, 16384⟩
    (by decide) selected_cut_24429

theorem selected_cut_24430 : selected 8 ⟨617440, by decide⟩
    (prefixPartial 13 308539) = some ⟨13, 2, 0, 617440, 308539, 989, 16384⟩ := by
  decide +kernel

theorem context_13_308539_617440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308539 ⟨617440, by decide⟩ :=
  accepted_of_selected 13 308539 ⟨617440, by decide⟩ ⟨13, 2, 0, 617440, 308539, 989, 16384⟩
    (by decide) selected_cut_24430

theorem unmarked_context_12_77134_617441 : frontier 9 ⟨617441, by decide⟩
    (prefixCache 12 77134) (prefixPartial 12 77134) = false := by
  decide +kernel

theorem node_context_12_77134_617441 : EJMOriginalGlobalDAGData.nodes 9 ⟨617441, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨617409, by decide⟩,⟨617430, by decide⟩,⟨617440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77134_617441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77134 ⟨617441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77134
    ⟨617441, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨617409, by decide⟩,⟨617430, by decide⟩,⟨617440, by decide⟩]) unmarked_context_12_77134_617441 node_context_12_77134_617441
  intro a
  fin_cases a
  · exact context_13_308536_3444
  · exact context_13_308537_617409
  · exact context_13_308538_617430
  · exact context_13_308539_617440

theorem selected_cut_24431 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308540) = some ⟨13, 1, 0, 3444, 308540, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308540_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308540 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308540 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308540, 1, 16384⟩
    (by decide) selected_cut_24431

theorem selected_cut_24432 : selected 8 ⟨617460, by decide⟩
    (prefixPartial 13 308541) = some ⟨13, 2, 0, 617460, 308541, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_308541_617460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308541 ⟨617460, by decide⟩ :=
  accepted_of_selected 13 308541 ⟨617460, by decide⟩ ⟨13, 2, 0, 617460, 308541, 1645, 16384⟩
    (by decide) selected_cut_24432

theorem selected_cut_24433 : selected 8 ⟨617478, by decide⟩
    (prefixPartial 13 308542) = some ⟨13, 2, 0, 617478, 308542, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_308542_617478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308542 ⟨617478, by decide⟩ :=
  accepted_of_selected 13 308542 ⟨617478, by decide⟩ ⟨13, 2, 0, 617478, 308542, 1717, 16384⟩
    (by decide) selected_cut_24433

theorem selected_cut_24434 : selected 8 ⟨617488, by decide⟩
    (prefixPartial 13 308543) = some ⟨13, 2, 0, 617488, 308543, 937, 16384⟩ := by
  decide +kernel

theorem context_13_308543_617488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308543 ⟨617488, by decide⟩ :=
  accepted_of_selected 13 308543 ⟨617488, by decide⟩ ⟨13, 2, 0, 617488, 308543, 937, 16384⟩
    (by decide) selected_cut_24434

theorem unmarked_context_12_77135_617489 : frontier 9 ⟨617489, by decide⟩
    (prefixCache 12 77135) (prefixPartial 12 77135) = false := by
  decide +kernel

theorem node_context_12_77135_617489 : EJMOriginalGlobalDAGData.nodes 9 ⟨617489, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨617460, by decide⟩,⟨617478, by decide⟩,⟨617488, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77135_617489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77135 ⟨617489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77135
    ⟨617489, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨617460, by decide⟩,⟨617478, by decide⟩,⟨617488, by decide⟩]) unmarked_context_12_77135_617489 node_context_12_77135_617489
  intro a
  fin_cases a
  · exact context_13_308540_3444
  · exact context_13_308541_617460
  · exact context_13_308542_617478
  · exact context_13_308543_617488

theorem unmarked_context_11_19283_617490 : frontier 10 ⟨617490, by decide⟩
    (prefixCache 11 19283) (prefixPartial 11 19283) = false := by
  decide +kernel

theorem node_context_11_19283_617490 : EJMOriginalGlobalDAGData.nodes 10 ⟨617490, by decide⟩ =
    .split (coordinate 11) (![⟨617344, by decide⟩,⟨617389, by decide⟩,⟨617441, by decide⟩,⟨617489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19283_617490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19283 ⟨617490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19283
    ⟨617490, by decide⟩ (by decide) (![⟨617344, by decide⟩,⟨617389, by decide⟩,⟨617441, by decide⟩,⟨617489, by decide⟩]) unmarked_context_11_19283_617490 node_context_11_19283_617490
  intro a
  fin_cases a
  · exact context_12_77132_617344
  · exact context_12_77133_617389
  · exact context_12_77134_617441
  · exact context_12_77135_617489

theorem unmarked_context_10_4820_617491 : frontier 11 ⟨617491, by decide⟩
    (prefixCache 10 4820) (prefixPartial 10 4820) = false := by
  decide +kernel

theorem node_context_10_4820_617491 : EJMOriginalGlobalDAGData.nodes 11 ⟨617491, by decide⟩ =
    .split (coordinate 10) (![⟨616890, by decide⟩,⟨617055, by decide⟩,⟨617293, by decide⟩,⟨617490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4820_617491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4820 ⟨617491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4820
    ⟨617491, by decide⟩ (by decide) (![⟨616890, by decide⟩,⟨617055, by decide⟩,⟨617293, by decide⟩,⟨617490, by decide⟩]) unmarked_context_10_4820_617491 node_context_10_4820_617491
  intro a
  fin_cases a
  · exact context_11_19280_616890
  · exact context_11_19281_617055
  · exact context_11_19282_617293
  · exact context_11_19283_617490

theorem selected_cut_24435 : selected 9 ⟨617543, by decide⟩
    (prefixPartial 12 77136) = some ⟨12, 2, 0, 617543, 77136, 3885, 65536⟩ := by
  decide +kernel

theorem context_12_77136_617543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77136 ⟨617543, by decide⟩ :=
  accepted_of_selected 12 77136 ⟨617543, by decide⟩ ⟨12, 2, 0, 617543, 77136, 3885, 65536⟩
    (by decide) selected_cut_24435

theorem selected_cut_24436 : selected 9 ⟨617587, by decide⟩
    (prefixPartial 12 77137) = some ⟨12, 2, 0, 617587, 77137, 3985, 65536⟩ := by
  decide +kernel

theorem context_12_77137_617587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77137 ⟨617587, by decide⟩ :=
  accepted_of_selected 12 77137 ⟨617587, by decide⟩ ⟨12, 2, 0, 617587, 77137, 3985, 65536⟩
    (by decide) selected_cut_24436

theorem selected_cut_24437 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308552) = some ⟨13, 1, 0, 3444, 308552, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308552_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308552 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308552 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308552, 1, 16384⟩
    (by decide) selected_cut_24437

theorem selected_cut_24438 : selected 8 ⟨617615, by decide⟩
    (prefixPartial 13 308553) = some ⟨13, 2, 0, 617615, 308553, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_308553_617615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308553 ⟨617615, by decide⟩ :=
  accepted_of_selected 13 308553 ⟨617615, by decide⟩ ⟨13, 2, 0, 617615, 308553, 1805, 16384⟩
    (by decide) selected_cut_24438

theorem selected_cut_24439 : selected 8 ⟨617640, by decide⟩
    (prefixPartial 13 308554) = some ⟨13, 2, 0, 617640, 308554, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_308554_617640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308554 ⟨617640, by decide⟩ :=
  accepted_of_selected 13 308554 ⟨617640, by decide⟩ ⟨13, 2, 0, 617640, 308554, 2053, 16384⟩
    (by decide) selected_cut_24439

theorem selected_cut_24440 : selected 8 ⟨617649, by decide⟩
    (prefixPartial 13 308555) = some ⟨13, 2, 0, 617649, 308555, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_308555_617649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308555 ⟨617649, by decide⟩ :=
  accepted_of_selected 13 308555 ⟨617649, by decide⟩ ⟨13, 2, 0, 617649, 308555, 1045, 16384⟩
    (by decide) selected_cut_24440

theorem unmarked_context_12_77138_617650 : frontier 9 ⟨617650, by decide⟩
    (prefixCache 12 77138) (prefixPartial 12 77138) = false := by
  decide +kernel

theorem node_context_12_77138_617650 : EJMOriginalGlobalDAGData.nodes 9 ⟨617650, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨617615, by decide⟩,⟨617640, by decide⟩,⟨617649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77138_617650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77138 ⟨617650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77138
    ⟨617650, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨617615, by decide⟩,⟨617640, by decide⟩,⟨617649, by decide⟩]) unmarked_context_12_77138_617650 node_context_12_77138_617650
  intro a
  fin_cases a
  · exact context_13_308552_3444
  · exact context_13_308553_617615
  · exact context_13_308554_617640
  · exact context_13_308555_617649

theorem selected_cut_24441 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308556) = some ⟨13, 1, 0, 3444, 308556, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308556_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308556 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308556 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308556, 1, 16384⟩
    (by decide) selected_cut_24441

theorem selected_cut_24442 : selected 8 ⟨617676, by decide⟩
    (prefixPartial 13 308557) = some ⟨13, 2, 0, 617676, 308557, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_308557_617676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308557 ⟨617676, by decide⟩ :=
  accepted_of_selected 13 308557 ⟨617676, by decide⟩ ⟨13, 2, 0, 617676, 308557, 1881, 16384⟩
    (by decide) selected_cut_24442

theorem selected_cut_24443 : selected 8 ⟨617715, by decide⟩
    (prefixPartial 13 308558) = some ⟨13, 2, 0, 617715, 308558, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_308558_617715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308558 ⟨617715, by decide⟩ :=
  accepted_of_selected 13 308558 ⟨617715, by decide⟩ ⟨13, 2, 0, 617715, 308558, 2113, 16384⟩
    (by decide) selected_cut_24443

theorem selected_cut_24444 : selected 8 ⟨617729, by decide⟩
    (prefixPartial 13 308559) = some ⟨13, 2, 0, 617729, 308559, 981, 16384⟩ := by
  decide +kernel

theorem context_13_308559_617729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308559 ⟨617729, by decide⟩ :=
  accepted_of_selected 13 308559 ⟨617729, by decide⟩ ⟨13, 2, 0, 617729, 308559, 981, 16384⟩
    (by decide) selected_cut_24444

theorem unmarked_context_12_77139_617730 : frontier 9 ⟨617730, by decide⟩
    (prefixCache 12 77139) (prefixPartial 12 77139) = false := by
  decide +kernel

theorem node_context_12_77139_617730 : EJMOriginalGlobalDAGData.nodes 9 ⟨617730, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨617676, by decide⟩,⟨617715, by decide⟩,⟨617729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77139_617730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77139 ⟨617730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77139
    ⟨617730, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨617676, by decide⟩,⟨617715, by decide⟩,⟨617729, by decide⟩]) unmarked_context_12_77139_617730 node_context_12_77139_617730
  intro a
  fin_cases a
  · exact context_13_308556_3444
  · exact context_13_308557_617676
  · exact context_13_308558_617715
  · exact context_13_308559_617729

theorem unmarked_context_11_19284_617731 : frontier 10 ⟨617731, by decide⟩
    (prefixCache 11 19284) (prefixPartial 11 19284) = false := by
  decide +kernel

theorem node_context_11_19284_617731 : EJMOriginalGlobalDAGData.nodes 10 ⟨617731, by decide⟩ =
    .split (coordinate 11) (![⟨617543, by decide⟩,⟨617587, by decide⟩,⟨617650, by decide⟩,⟨617730, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19284_617731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19284 ⟨617731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19284
    ⟨617731, by decide⟩ (by decide) (![⟨617543, by decide⟩,⟨617587, by decide⟩,⟨617650, by decide⟩,⟨617730, by decide⟩]) unmarked_context_11_19284_617731 node_context_11_19284_617731
  intro a
  fin_cases a
  · exact context_12_77136_617543
  · exact context_12_77137_617587
  · exact context_12_77138_617650
  · exact context_12_77139_617730

theorem selected_cut_24445 : selected 9 ⟨617778, by decide⟩
    (prefixPartial 12 77140) = some ⟨12, 2, 0, 617778, 77140, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_77140_617778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77140 ⟨617778, by decide⟩ :=
  accepted_of_selected 12 77140 ⟨617778, by decide⟩ ⟨12, 2, 0, 617778, 77140, 3501, 65536⟩
    (by decide) selected_cut_24445

theorem selected_cut_24446 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 77141) = some ⟨12, 1, 0, 439069, 77141, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77141_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77141 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 77141 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 77141, 1, 65536⟩
    (by decide) selected_cut_24446

theorem selected_cut_24447 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308568) = some ⟨13, 1, 0, 3444, 308568, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308568_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308568 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308568 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308568, 1, 16384⟩
    (by decide) selected_cut_24447

theorem selected_cut_24448 : selected 8 ⟨617797, by decide⟩
    (prefixPartial 13 308569) = some ⟨13, 2, 0, 617797, 308569, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_308569_617797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308569 ⟨617797, by decide⟩ :=
  accepted_of_selected 13 308569 ⟨617797, by decide⟩ ⟨13, 2, 0, 617797, 308569, 1537, 16384⟩
    (by decide) selected_cut_24448

theorem selected_cut_24449 : selected 8 ⟨617822, by decide⟩
    (prefixPartial 13 308570) = some ⟨13, 2, 0, 617822, 308570, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_308570_617822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308570 ⟨617822, by decide⟩ :=
  accepted_of_selected 13 308570 ⟨617822, by decide⟩ ⟨13, 2, 0, 617822, 308570, 1901, 16384⟩
    (by decide) selected_cut_24449

theorem selected_cut_24450 : selected 8 ⟨617829, by decide⟩
    (prefixPartial 13 308571) = some ⟨13, 2, 0, 617829, 308571, 985, 16384⟩ := by
  decide +kernel

theorem context_13_308571_617829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308571 ⟨617829, by decide⟩ :=
  accepted_of_selected 13 308571 ⟨617829, by decide⟩ ⟨13, 2, 0, 617829, 308571, 985, 16384⟩
    (by decide) selected_cut_24450

theorem unmarked_context_12_77142_617830 : frontier 9 ⟨617830, by decide⟩
    (prefixCache 12 77142) (prefixPartial 12 77142) = false := by
  decide +kernel

theorem node_context_12_77142_617830 : EJMOriginalGlobalDAGData.nodes 9 ⟨617830, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨617797, by decide⟩,⟨617822, by decide⟩,⟨617829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77142_617830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77142 ⟨617830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77142
    ⟨617830, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨617797, by decide⟩,⟨617822, by decide⟩,⟨617829, by decide⟩]) unmarked_context_12_77142_617830 node_context_12_77142_617830
  intro a
  fin_cases a
  · exact context_13_308568_3444
  · exact context_13_308569_617797
  · exact context_13_308570_617822
  · exact context_13_308571_617829

theorem selected_cut_24451 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308572) = some ⟨13, 1, 0, 3444, 308572, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308572_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308572 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308572 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308572, 1, 16384⟩
    (by decide) selected_cut_24451

theorem selected_cut_24452 : selected 8 ⟨617847, by decide⟩
    (prefixPartial 13 308573) = some ⟨13, 2, 0, 617847, 308573, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_308573_617847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308573 ⟨617847, by decide⟩ :=
  accepted_of_selected 13 308573 ⟨617847, by decide⟩ ⟨13, 2, 0, 617847, 308573, 1629, 16384⟩
    (by decide) selected_cut_24452

theorem selected_cut_24453 : selected 8 ⟨617878, by decide⟩
    (prefixPartial 13 308574) = some ⟨13, 2, 0, 617878, 308574, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_308574_617878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308574 ⟨617878, by decide⟩ :=
  accepted_of_selected 13 308574 ⟨617878, by decide⟩ ⟨13, 2, 0, 617878, 308574, 2109, 16384⟩
    (by decide) selected_cut_24453

theorem selected_cut_24454 : selected 8 ⟨617884, by decide⟩
    (prefixPartial 13 308575) = some ⟨13, 2, 0, 617884, 308575, 865, 16384⟩ := by
  decide +kernel

theorem context_13_308575_617884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308575 ⟨617884, by decide⟩ :=
  accepted_of_selected 13 308575 ⟨617884, by decide⟩ ⟨13, 2, 0, 617884, 308575, 865, 16384⟩
    (by decide) selected_cut_24454

theorem unmarked_context_12_77143_617885 : frontier 9 ⟨617885, by decide⟩
    (prefixCache 12 77143) (prefixPartial 12 77143) = false := by
  decide +kernel

theorem node_context_12_77143_617885 : EJMOriginalGlobalDAGData.nodes 9 ⟨617885, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨617847, by decide⟩,⟨617878, by decide⟩,⟨617884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77143_617885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77143 ⟨617885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77143
    ⟨617885, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨617847, by decide⟩,⟨617878, by decide⟩,⟨617884, by decide⟩]) unmarked_context_12_77143_617885 node_context_12_77143_617885
  intro a
  fin_cases a
  · exact context_13_308572_3444
  · exact context_13_308573_617847
  · exact context_13_308574_617878
  · exact context_13_308575_617884

theorem unmarked_context_11_19285_617886 : frontier 10 ⟨617886, by decide⟩
    (prefixCache 11 19285) (prefixPartial 11 19285) = false := by
  decide +kernel

theorem node_context_11_19285_617886 : EJMOriginalGlobalDAGData.nodes 10 ⟨617886, by decide⟩ =
    .split (coordinate 11) (![⟨617778, by decide⟩,⟨439069, by decide⟩,⟨617830, by decide⟩,⟨617885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19285_617886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19285 ⟨617886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19285
    ⟨617886, by decide⟩ (by decide) (![⟨617778, by decide⟩,⟨439069, by decide⟩,⟨617830, by decide⟩,⟨617885, by decide⟩]) unmarked_context_11_19285_617886 node_context_11_19285_617886
  intro a
  fin_cases a
  · exact context_12_77140_617778
  · exact context_12_77141_439069
  · exact context_12_77142_617830
  · exact context_12_77143_617885

theorem selected_cut_24455 : selected 9 ⟨617935, by decide⟩
    (prefixPartial 12 77144) = some ⟨12, 2, 0, 617935, 77144, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_77144_617935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77144 ⟨617935, by decide⟩ :=
  accepted_of_selected 12 77144 ⟨617935, by decide⟩ ⟨12, 2, 0, 617935, 77144, 3893, 65536⟩
    (by decide) selected_cut_24455

theorem selected_cut_24456 : selected 9 ⟨617983, by decide⟩
    (prefixPartial 12 77145) = some ⟨12, 2, 0, 617983, 77145, 3921, 65536⟩ := by
  decide +kernel

theorem context_12_77145_617983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77145 ⟨617983, by decide⟩ :=
  accepted_of_selected 12 77145 ⟨617983, by decide⟩ ⟨12, 2, 0, 617983, 77145, 3921, 65536⟩
    (by decide) selected_cut_24456

theorem selected_cut_24457 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308584) = some ⟨13, 1, 0, 3444, 308584, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308584_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308584 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308584 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308584, 1, 16384⟩
    (by decide) selected_cut_24457

theorem selected_cut_24458 : selected 8 ⟨618000, by decide⟩
    (prefixPartial 13 308585) = some ⟨13, 2, 0, 618000, 308585, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_308585_618000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308585 ⟨618000, by decide⟩ :=
  accepted_of_selected 13 308585 ⟨618000, by decide⟩ ⟨13, 2, 0, 618000, 308585, 1405, 16384⟩
    (by decide) selected_cut_24458

theorem selected_cut_24459 : selected 8 ⟨618020, by decide⟩
    (prefixPartial 13 308586) = some ⟨13, 2, 0, 618020, 308586, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_308586_618020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308586 ⟨618020, by decide⟩ :=
  accepted_of_selected 13 308586 ⟨618020, by decide⟩ ⟨13, 2, 0, 618020, 308586, 1973, 16384⟩
    (by decide) selected_cut_24459

theorem selected_cut_24460 : selected 8 ⟨618030, by decide⟩
    (prefixPartial 13 308587) = some ⟨13, 2, 0, 618030, 308587, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_308587_618030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308587 ⟨618030, by decide⟩ :=
  accepted_of_selected 13 308587 ⟨618030, by decide⟩ ⟨13, 2, 0, 618030, 308587, 1121, 16384⟩
    (by decide) selected_cut_24460

theorem unmarked_context_12_77146_618031 : frontier 9 ⟨618031, by decide⟩
    (prefixCache 12 77146) (prefixPartial 12 77146) = false := by
  decide +kernel

theorem node_context_12_77146_618031 : EJMOriginalGlobalDAGData.nodes 9 ⟨618031, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨618000, by decide⟩,⟨618020, by decide⟩,⟨618030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77146_618031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77146 ⟨618031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77146
    ⟨618031, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨618000, by decide⟩,⟨618020, by decide⟩,⟨618030, by decide⟩]) unmarked_context_12_77146_618031 node_context_12_77146_618031
  intro a
  fin_cases a
  · exact context_13_308584_3444
  · exact context_13_308585_618000
  · exact context_13_308586_618020
  · exact context_13_308587_618030

theorem selected_cut_24461 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308588) = some ⟨13, 1, 0, 3444, 308588, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308588_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308588 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308588 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308588, 1, 16384⟩
    (by decide) selected_cut_24461

theorem selected_cut_24462 : selected 8 ⟨618050, by decide⟩
    (prefixPartial 13 308589) = some ⟨13, 2, 0, 618050, 308589, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_308589_618050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308589 ⟨618050, by decide⟩ :=
  accepted_of_selected 13 308589 ⟨618050, by decide⟩ ⟨13, 2, 0, 618050, 308589, 1557, 16384⟩
    (by decide) selected_cut_24462

theorem selected_cut_24463 : selected 8 ⟨618081, by decide⟩
    (prefixPartial 13 308590) = some ⟨13, 2, 0, 618081, 308590, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_308590_618081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308590 ⟨618081, by decide⟩ :=
  accepted_of_selected 13 308590 ⟨618081, by decide⟩ ⟨13, 2, 0, 618081, 308590, 2189, 16384⟩
    (by decide) selected_cut_24463

theorem selected_cut_24464 : selected 8 ⟨618095, by decide⟩
    (prefixPartial 13 308591) = some ⟨13, 2, 0, 618095, 308591, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_308591_618095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308591 ⟨618095, by decide⟩ :=
  accepted_of_selected 13 308591 ⟨618095, by decide⟩ ⟨13, 2, 0, 618095, 308591, 1005, 16384⟩
    (by decide) selected_cut_24464

theorem unmarked_context_12_77147_618096 : frontier 9 ⟨618096, by decide⟩
    (prefixCache 12 77147) (prefixPartial 12 77147) = false := by
  decide +kernel

theorem node_context_12_77147_618096 : EJMOriginalGlobalDAGData.nodes 9 ⟨618096, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨618050, by decide⟩,⟨618081, by decide⟩,⟨618095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77147_618096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77147 ⟨618096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77147
    ⟨618096, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨618050, by decide⟩,⟨618081, by decide⟩,⟨618095, by decide⟩]) unmarked_context_12_77147_618096 node_context_12_77147_618096
  intro a
  fin_cases a
  · exact context_13_308588_3444
  · exact context_13_308589_618050
  · exact context_13_308590_618081
  · exact context_13_308591_618095

theorem unmarked_context_11_19286_618097 : frontier 10 ⟨618097, by decide⟩
    (prefixCache 11 19286) (prefixPartial 11 19286) = false := by
  decide +kernel

theorem node_context_11_19286_618097 : EJMOriginalGlobalDAGData.nodes 10 ⟨618097, by decide⟩ =
    .split (coordinate 11) (![⟨617935, by decide⟩,⟨617983, by decide⟩,⟨618031, by decide⟩,⟨618096, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19286_618097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19286 ⟨618097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19286
    ⟨618097, by decide⟩ (by decide) (![⟨617935, by decide⟩,⟨617983, by decide⟩,⟨618031, by decide⟩,⟨618096, by decide⟩]) unmarked_context_11_19286_618097 node_context_11_19286_618097
  intro a
  fin_cases a
  · exact context_12_77144_617935
  · exact context_12_77145_617983
  · exact context_12_77146_618031
  · exact context_12_77147_618096

theorem selected_cut_24465 : selected 9 ⟨618148, by decide⟩
    (prefixPartial 12 77148) = some ⟨12, 2, 0, 618148, 77148, 3837, 65536⟩ := by
  decide +kernel

theorem context_12_77148_618148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77148 ⟨618148, by decide⟩ :=
  accepted_of_selected 12 77148 ⟨618148, by decide⟩ ⟨12, 2, 0, 618148, 77148, 3837, 65536⟩
    (by decide) selected_cut_24465

theorem selected_cut_24466 : selected 9 ⟨618187, by decide⟩
    (prefixPartial 12 77149) = some ⟨12, 2, 0, 618187, 77149, 3581, 65536⟩ := by
  decide +kernel

theorem context_12_77149_618187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77149 ⟨618187, by decide⟩ :=
  accepted_of_selected 12 77149 ⟨618187, by decide⟩ ⟨12, 2, 0, 618187, 77149, 3581, 65536⟩
    (by decide) selected_cut_24466

theorem selected_cut_24467 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308600) = some ⟨13, 1, 0, 3444, 308600, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308600_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308600 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308600 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308600, 1, 16384⟩
    (by decide) selected_cut_24467

theorem selected_cut_24468 : selected 8 ⟨618202, by decide⟩
    (prefixPartial 13 308601) = some ⟨13, 2, 0, 618202, 308601, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_308601_618202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308601 ⟨618202, by decide⟩ :=
  accepted_of_selected 13 308601 ⟨618202, by decide⟩ ⟨13, 2, 0, 618202, 308601, 1445, 16384⟩
    (by decide) selected_cut_24468

theorem selected_cut_24469 : selected 8 ⟨618224, by decide⟩
    (prefixPartial 13 308602) = some ⟨13, 2, 0, 618224, 308602, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_308602_618224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308602 ⟨618224, by decide⟩ :=
  accepted_of_selected 13 308602 ⟨618224, by decide⟩ ⟨13, 2, 0, 618224, 308602, 2017, 16384⟩
    (by decide) selected_cut_24469

theorem selected_cut_24470 : selected 8 ⟨618232, by decide⟩
    (prefixPartial 13 308603) = some ⟨13, 2, 0, 618232, 308603, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_308603_618232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308603 ⟨618232, by decide⟩ :=
  accepted_of_selected 13 308603 ⟨618232, by decide⟩ ⟨13, 2, 0, 618232, 308603, 1081, 16384⟩
    (by decide) selected_cut_24470

theorem unmarked_context_12_77150_618233 : frontier 9 ⟨618233, by decide⟩
    (prefixCache 12 77150) (prefixPartial 12 77150) = false := by
  decide +kernel

theorem node_context_12_77150_618233 : EJMOriginalGlobalDAGData.nodes 9 ⟨618233, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨618202, by decide⟩,⟨618224, by decide⟩,⟨618232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77150_618233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77150 ⟨618233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77150
    ⟨618233, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨618202, by decide⟩,⟨618224, by decide⟩,⟨618232, by decide⟩]) unmarked_context_12_77150_618233 node_context_12_77150_618233
  intro a
  fin_cases a
  · exact context_13_308600_3444
  · exact context_13_308601_618202
  · exact context_13_308602_618224
  · exact context_13_308603_618232

theorem selected_cut_24471 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308604) = some ⟨13, 1, 0, 3444, 308604, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308604_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308604 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308604 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308604, 1, 16384⟩
    (by decide) selected_cut_24471

theorem selected_cut_24472 : selected 8 ⟨618253, by decide⟩
    (prefixPartial 13 308605) = some ⟨13, 2, 0, 618253, 308605, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_308605_618253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308605 ⟨618253, by decide⟩ :=
  accepted_of_selected 13 308605 ⟨618253, by decide⟩ ⟨13, 2, 0, 618253, 308605, 1477, 16384⟩
    (by decide) selected_cut_24472

theorem selected_cut_24473 : selected 8 ⟨618282, by decide⟩
    (prefixPartial 13 308606) = some ⟨13, 2, 0, 618282, 308606, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_308606_618282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308606 ⟨618282, by decide⟩ :=
  accepted_of_selected 13 308606 ⟨618282, by decide⟩ ⟨13, 2, 0, 618282, 308606, 2053, 16384⟩
    (by decide) selected_cut_24473

theorem selected_cut_24474 : selected 8 ⟨618288, by decide⟩
    (prefixPartial 13 308607) = some ⟨13, 2, 0, 618288, 308607, 977, 16384⟩ := by
  decide +kernel

theorem context_13_308607_618288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308607 ⟨618288, by decide⟩ :=
  accepted_of_selected 13 308607 ⟨618288, by decide⟩ ⟨13, 2, 0, 618288, 308607, 977, 16384⟩
    (by decide) selected_cut_24474

theorem unmarked_context_12_77151_618289 : frontier 9 ⟨618289, by decide⟩
    (prefixCache 12 77151) (prefixPartial 12 77151) = false := by
  decide +kernel

theorem node_context_12_77151_618289 : EJMOriginalGlobalDAGData.nodes 9 ⟨618289, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨618253, by decide⟩,⟨618282, by decide⟩,⟨618288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77151_618289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77151 ⟨618289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77151
    ⟨618289, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨618253, by decide⟩,⟨618282, by decide⟩,⟨618288, by decide⟩]) unmarked_context_12_77151_618289 node_context_12_77151_618289
  intro a
  fin_cases a
  · exact context_13_308604_3444
  · exact context_13_308605_618253
  · exact context_13_308606_618282
  · exact context_13_308607_618288

theorem unmarked_context_11_19287_618290 : frontier 10 ⟨618290, by decide⟩
    (prefixCache 11 19287) (prefixPartial 11 19287) = false := by
  decide +kernel

theorem node_context_11_19287_618290 : EJMOriginalGlobalDAGData.nodes 10 ⟨618290, by decide⟩ =
    .split (coordinate 11) (![⟨618148, by decide⟩,⟨618187, by decide⟩,⟨618233, by decide⟩,⟨618289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19287_618290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19287 ⟨618290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19287
    ⟨618290, by decide⟩ (by decide) (![⟨618148, by decide⟩,⟨618187, by decide⟩,⟨618233, by decide⟩,⟨618289, by decide⟩]) unmarked_context_11_19287_618290 node_context_11_19287_618290
  intro a
  fin_cases a
  · exact context_12_77148_618148
  · exact context_12_77149_618187
  · exact context_12_77150_618233
  · exact context_12_77151_618289

theorem unmarked_context_10_4821_618291 : frontier 11 ⟨618291, by decide⟩
    (prefixCache 10 4821) (prefixPartial 10 4821) = false := by
  decide +kernel

theorem node_context_10_4821_618291 : EJMOriginalGlobalDAGData.nodes 11 ⟨618291, by decide⟩ =
    .split (coordinate 10) (![⟨617731, by decide⟩,⟨617886, by decide⟩,⟨618097, by decide⟩,⟨618290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4821_618291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4821 ⟨618291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4821
    ⟨618291, by decide⟩ (by decide) (![⟨617731, by decide⟩,⟨617886, by decide⟩,⟨618097, by decide⟩,⟨618290, by decide⟩]) unmarked_context_10_4821_618291 node_context_10_4821_618291
  intro a
  fin_cases a
  · exact context_11_19284_617731
  · exact context_11_19285_617886
  · exact context_11_19286_618097
  · exact context_11_19287_618290

theorem selected_cut_24475 : selected 9 ⟨618335, by decide⟩
    (prefixPartial 12 77152) = some ⟨12, 2, 0, 618335, 77152, 3561, 65536⟩ := by
  decide +kernel

theorem context_12_77152_618335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77152 ⟨618335, by decide⟩ :=
  accepted_of_selected 12 77152 ⟨618335, by decide⟩ ⟨12, 2, 0, 618335, 77152, 3561, 65536⟩
    (by decide) selected_cut_24475

theorem selected_cut_24476 : selected 9 ⟨618383, by decide⟩
    (prefixPartial 12 77153) = some ⟨12, 2, 0, 618383, 77153, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_77153_618383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77153 ⟨618383, by decide⟩ :=
  accepted_of_selected 12 77153 ⟨618383, by decide⟩ ⟨12, 2, 0, 618383, 77153, 3529, 65536⟩
    (by decide) selected_cut_24476

theorem selected_cut_24477 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308616) = some ⟨13, 1, 0, 3444, 308616, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308616_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308616 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308616 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308616, 1, 16384⟩
    (by decide) selected_cut_24477

theorem selected_cut_24478 : selected 8 ⟨618398, by decide⟩
    (prefixPartial 13 308617) = some ⟨13, 2, 0, 618398, 308617, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_308617_618398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308617 ⟨618398, by decide⟩ :=
  accepted_of_selected 13 308617 ⟨618398, by decide⟩ ⟨13, 2, 0, 618398, 308617, 1117, 16384⟩
    (by decide) selected_cut_24478

theorem selected_cut_24479 : selected 8 ⟨618419, by decide⟩
    (prefixPartial 13 308618) = some ⟨13, 2, 0, 618419, 308618, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_308618_618419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308618 ⟨618419, by decide⟩ :=
  accepted_of_selected 13 308618 ⟨618419, by decide⟩ ⟨13, 2, 0, 618419, 308618, 2017, 16384⟩
    (by decide) selected_cut_24479

theorem selected_cut_24480 : selected 8 ⟨618428, by decide⟩
    (prefixPartial 13 308619) = some ⟨13, 2, 0, 618428, 308619, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_308619_618428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308619 ⟨618428, by decide⟩ :=
  accepted_of_selected 13 308619 ⟨618428, by decide⟩ ⟨13, 2, 0, 618428, 308619, 1093, 16384⟩
    (by decide) selected_cut_24480

theorem unmarked_context_12_77154_618429 : frontier 9 ⟨618429, by decide⟩
    (prefixCache 12 77154) (prefixPartial 12 77154) = false := by
  decide +kernel

theorem node_context_12_77154_618429 : EJMOriginalGlobalDAGData.nodes 9 ⟨618429, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨618398, by decide⟩,⟨618419, by decide⟩,⟨618428, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77154_618429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77154 ⟨618429, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77154
    ⟨618429, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨618398, by decide⟩,⟨618419, by decide⟩,⟨618428, by decide⟩]) unmarked_context_12_77154_618429 node_context_12_77154_618429
  intro a
  fin_cases a
  · exact context_13_308616_3444
  · exact context_13_308617_618398
  · exact context_13_308618_618419
  · exact context_13_308619_618428

theorem selected_cut_24481 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308620) = some ⟨13, 1, 0, 3444, 308620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308620, 1, 16384⟩
    (by decide) selected_cut_24481

theorem selected_cut_24482 : selected 8 ⟨618442, by decide⟩
    (prefixPartial 13 308621) = some ⟨13, 2, 0, 618442, 308621, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_308621_618442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308621 ⟨618442, by decide⟩ :=
  accepted_of_selected 13 308621 ⟨618442, by decide⟩ ⟨13, 2, 0, 618442, 308621, 1145, 16384⟩
    (by decide) selected_cut_24482

theorem selected_cut_24483 : selected 8 ⟨618471, by decide⟩
    (prefixPartial 13 308622) = some ⟨13, 2, 0, 618471, 308622, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_308622_618471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308622 ⟨618471, by decide⟩ :=
  accepted_of_selected 13 308622 ⟨618471, by decide⟩ ⟨13, 2, 0, 618471, 308622, 2145, 16384⟩
    (by decide) selected_cut_24483

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
