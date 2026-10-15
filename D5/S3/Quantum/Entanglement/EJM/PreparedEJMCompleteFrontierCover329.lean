/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover328
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_31588 : selected 8 ⟨810431, by decide⟩
    (prefixPartial 13 424219) = some ⟨13, 2, 0, 810431, 424219, 813, 16384⟩ := by
  decide +kernel

theorem context_13_424219_810431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424219 ⟨810431, by decide⟩ :=
  accepted_of_selected 13 424219 ⟨810431, by decide⟩ ⟨13, 2, 0, 810431, 424219, 813, 16384⟩
    (by decide) selected_cut_31588

theorem unmarked_context_12_106054_810432 : frontier 9 ⟨810432, by decide⟩
    (prefixCache 12 106054) (prefixPartial 12 106054) = false := by
  decide +kernel

theorem node_context_12_106054_810432 : EJMOriginalGlobalDAGData.nodes 9 ⟨810432, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810400, by decide⟩,⟨810423, by decide⟩,⟨810431, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106054_810432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106054 ⟨810432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106054
    ⟨810432, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810400, by decide⟩,⟨810423, by decide⟩,⟨810431, by decide⟩]) unmarked_context_12_106054_810432 node_context_12_106054_810432
  intro a
  fin_cases a
  · exact context_13_424216_3444
  · exact context_13_424217_810400
  · exact context_13_424218_810423
  · exact context_13_424219_810431

theorem selected_cut_31589 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424220) = some ⟨13, 1, 0, 3444, 424220, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424220_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424220 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424220 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424220, 1, 16384⟩
    (by decide) selected_cut_31589

theorem selected_cut_31590 : selected 8 ⟨810475, by decide⟩
    (prefixPartial 13 424221) = some ⟨13, 2, 0, 810475, 424221, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_424221_810475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424221 ⟨810475, by decide⟩ :=
  accepted_of_selected 13 424221 ⟨810475, by decide⟩ ⟨13, 2, 0, 810475, 424221, 2809, 16384⟩
    (by decide) selected_cut_31590

theorem selected_cut_31591 : selected 8 ⟨810504, by decide⟩
    (prefixPartial 13 424222) = some ⟨13, 2, 0, 810504, 424222, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_424222_810504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424222 ⟨810504, by decide⟩ :=
  accepted_of_selected 13 424222 ⟨810504, by decide⟩ ⟨13, 2, 0, 810504, 424222, 1689, 16384⟩
    (by decide) selected_cut_31591

theorem selected_cut_31592 : selected 8 ⟨810515, by decide⟩
    (prefixPartial 13 424223) = some ⟨13, 2, 0, 810515, 424223, 941, 16384⟩ := by
  decide +kernel

theorem context_13_424223_810515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424223 ⟨810515, by decide⟩ :=
  accepted_of_selected 13 424223 ⟨810515, by decide⟩ ⟨13, 2, 0, 810515, 424223, 941, 16384⟩
    (by decide) selected_cut_31592

theorem unmarked_context_12_106055_810516 : frontier 9 ⟨810516, by decide⟩
    (prefixCache 12 106055) (prefixPartial 12 106055) = false := by
  decide +kernel

theorem node_context_12_106055_810516 : EJMOriginalGlobalDAGData.nodes 9 ⟨810516, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810475, by decide⟩,⟨810504, by decide⟩,⟨810515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106055_810516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106055 ⟨810516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106055
    ⟨810516, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810475, by decide⟩,⟨810504, by decide⟩,⟨810515, by decide⟩]) unmarked_context_12_106055_810516 node_context_12_106055_810516
  intro a
  fin_cases a
  · exact context_13_424220_3444
  · exact context_13_424221_810475
  · exact context_13_424222_810504
  · exact context_13_424223_810515

theorem unmarked_context_11_26513_810517 : frontier 10 ⟨810517, by decide⟩
    (prefixCache 11 26513) (prefixPartial 11 26513) = false := by
  decide +kernel

theorem node_context_11_26513_810517 : EJMOriginalGlobalDAGData.nodes 10 ⟨810517, by decide⟩ =
    .split (coordinate 11) (![⟨810292, by decide⟩,⟨810364, by decide⟩,⟨810432, by decide⟩,⟨810516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26513_810517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26513 ⟨810517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26513
    ⟨810517, by decide⟩ (by decide) (![⟨810292, by decide⟩,⟨810364, by decide⟩,⟨810432, by decide⟩,⟨810516, by decide⟩]) unmarked_context_11_26513_810517 node_context_11_26513_810517
  intro a
  fin_cases a
  · exact context_12_106052_810292
  · exact context_12_106053_810364
  · exact context_12_106054_810432
  · exact context_12_106055_810516

theorem selected_cut_31593 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424224) = some ⟨13, 1, 0, 3444, 424224, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424224_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424224 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424224 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424224, 1, 16384⟩
    (by decide) selected_cut_31593

theorem selected_cut_31594 : selected 8 ⟨810562, by decide⟩
    (prefixPartial 13 424225) = some ⟨13, 2, 0, 810562, 424225, 2609, 16384⟩ := by
  decide +kernel

theorem context_13_424225_810562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424225 ⟨810562, by decide⟩ :=
  accepted_of_selected 13 424225 ⟨810562, by decide⟩ ⟨13, 2, 0, 810562, 424225, 2609, 16384⟩
    (by decide) selected_cut_31594

theorem selected_cut_31595 : selected 8 ⟨810607, by decide⟩
    (prefixPartial 13 424226) = some ⟨13, 2, 0, 810607, 424226, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_424226_810607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424226 ⟨810607, by decide⟩ :=
  accepted_of_selected 13 424226 ⟨810607, by decide⟩ ⟨13, 2, 0, 810607, 424226, 1829, 16384⟩
    (by decide) selected_cut_31595

theorem selected_cut_31596 : selected 8 ⟨810618, by decide⟩
    (prefixPartial 13 424227) = some ⟨13, 2, 0, 810618, 424227, 725, 16384⟩ := by
  decide +kernel

theorem context_13_424227_810618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424227 ⟨810618, by decide⟩ :=
  accepted_of_selected 13 424227 ⟨810618, by decide⟩ ⟨13, 2, 0, 810618, 424227, 725, 16384⟩
    (by decide) selected_cut_31596

theorem unmarked_context_12_106056_810619 : frontier 9 ⟨810619, by decide⟩
    (prefixCache 12 106056) (prefixPartial 12 106056) = false := by
  decide +kernel

theorem node_context_12_106056_810619 : EJMOriginalGlobalDAGData.nodes 9 ⟨810619, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810562, by decide⟩,⟨810607, by decide⟩,⟨810618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106056_810619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106056 ⟨810619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106056
    ⟨810619, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810562, by decide⟩,⟨810607, by decide⟩,⟨810618, by decide⟩]) unmarked_context_12_106056_810619 node_context_12_106056_810619
  intro a
  fin_cases a
  · exact context_13_424224_3444
  · exact context_13_424225_810562
  · exact context_13_424226_810607
  · exact context_13_424227_810618

theorem selected_cut_31597 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424228) = some ⟨13, 1, 0, 3444, 424228, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424228_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424228 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424228 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424228, 1, 16384⟩
    (by decide) selected_cut_31597

theorem selected_cut_31598 : selected 8 ⟨810646, by decide⟩
    (prefixPartial 13 424229) = some ⟨13, 2, 0, 810646, 424229, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_424229_810646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424229 ⟨810646, by decide⟩ :=
  accepted_of_selected 13 424229 ⟨810646, by decide⟩ ⟨13, 2, 0, 810646, 424229, 2337, 16384⟩
    (by decide) selected_cut_31598

theorem selected_cut_31599 : selected 8 ⟨810667, by decide⟩
    (prefixPartial 13 424230) = some ⟨13, 2, 0, 810667, 424230, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_424230_810667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424230 ⟨810667, by decide⟩ :=
  accepted_of_selected 13 424230 ⟨810667, by decide⟩ ⟨13, 2, 0, 810667, 424230, 1453, 16384⟩
    (by decide) selected_cut_31599

theorem selected_cut_31600 : selected 8 ⟨810676, by decide⟩
    (prefixPartial 13 424231) = some ⟨13, 2, 0, 810676, 424231, 677, 16384⟩ := by
  decide +kernel

theorem context_13_424231_810676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424231 ⟨810676, by decide⟩ :=
  accepted_of_selected 13 424231 ⟨810676, by decide⟩ ⟨13, 2, 0, 810676, 424231, 677, 16384⟩
    (by decide) selected_cut_31600

theorem unmarked_context_12_106057_810677 : frontier 9 ⟨810677, by decide⟩
    (prefixCache 12 106057) (prefixPartial 12 106057) = false := by
  decide +kernel

theorem node_context_12_106057_810677 : EJMOriginalGlobalDAGData.nodes 9 ⟨810677, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810646, by decide⟩,⟨810667, by decide⟩,⟨810676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106057_810677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106057 ⟨810677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106057
    ⟨810677, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810646, by decide⟩,⟨810667, by decide⟩,⟨810676, by decide⟩]) unmarked_context_12_106057_810677 node_context_12_106057_810677
  intro a
  fin_cases a
  · exact context_13_424228_3444
  · exact context_13_424229_810646
  · exact context_13_424230_810667
  · exact context_13_424231_810676

theorem selected_cut_31601 : selected 9 ⟨810678, by decide⟩
    (prefixPartial 12 106058) = some ⟨12, 1, 0, 810678, 106058, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106058_810678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106058 ⟨810678, by decide⟩ :=
  accepted_of_selected 12 106058 ⟨810678, by decide⟩ ⟨12, 1, 0, 810678, 106058, 1, 65536⟩
    (by decide) selected_cut_31601

theorem selected_cut_31602 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424236) = some ⟨13, 1, 0, 3444, 424236, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424236_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424236 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424236 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424236, 1, 16384⟩
    (by decide) selected_cut_31602

theorem selected_cut_31603 : selected 8 ⟨810711, by decide⟩
    (prefixPartial 13 424237) = some ⟨13, 2, 0, 810711, 424237, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_424237_810711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424237 ⟨810711, by decide⟩ :=
  accepted_of_selected 13 424237 ⟨810711, by decide⟩ ⟨13, 2, 0, 810711, 424237, 2673, 16384⟩
    (by decide) selected_cut_31603

theorem selected_cut_31604 : selected 8 ⟨810735, by decide⟩
    (prefixPartial 13 424238) = some ⟨13, 2, 0, 810735, 424238, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_424238_810735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424238 ⟨810735, by decide⟩ :=
  accepted_of_selected 13 424238 ⟨810735, by decide⟩ ⟨13, 2, 0, 810735, 424238, 1621, 16384⟩
    (by decide) selected_cut_31604

theorem selected_cut_31605 : selected 8 ⟨810746, by decide⟩
    (prefixPartial 13 424239) = some ⟨13, 2, 0, 810746, 424239, 789, 16384⟩ := by
  decide +kernel

theorem context_13_424239_810746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424239 ⟨810746, by decide⟩ :=
  accepted_of_selected 13 424239 ⟨810746, by decide⟩ ⟨13, 2, 0, 810746, 424239, 789, 16384⟩
    (by decide) selected_cut_31605

theorem unmarked_context_12_106059_810747 : frontier 9 ⟨810747, by decide⟩
    (prefixCache 12 106059) (prefixPartial 12 106059) = false := by
  decide +kernel

theorem node_context_12_106059_810747 : EJMOriginalGlobalDAGData.nodes 9 ⟨810747, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810711, by decide⟩,⟨810735, by decide⟩,⟨810746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106059_810747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106059 ⟨810747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106059
    ⟨810747, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810711, by decide⟩,⟨810735, by decide⟩,⟨810746, by decide⟩]) unmarked_context_12_106059_810747 node_context_12_106059_810747
  intro a
  fin_cases a
  · exact context_13_424236_3444
  · exact context_13_424237_810711
  · exact context_13_424238_810735
  · exact context_13_424239_810746

theorem unmarked_context_11_26514_810748 : frontier 10 ⟨810748, by decide⟩
    (prefixCache 11 26514) (prefixPartial 11 26514) = false := by
  decide +kernel

theorem node_context_11_26514_810748 : EJMOriginalGlobalDAGData.nodes 10 ⟨810748, by decide⟩ =
    .split (coordinate 11) (![⟨810619, by decide⟩,⟨810677, by decide⟩,⟨810678, by decide⟩,⟨810747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26514_810748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26514 ⟨810748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26514
    ⟨810748, by decide⟩ (by decide) (![⟨810619, by decide⟩,⟨810677, by decide⟩,⟨810678, by decide⟩,⟨810747, by decide⟩]) unmarked_context_11_26514_810748 node_context_11_26514_810748
  intro a
  fin_cases a
  · exact context_12_106056_810619
  · exact context_12_106057_810677
  · exact context_12_106058_810678
  · exact context_12_106059_810747

theorem selected_cut_31606 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424240) = some ⟨13, 1, 0, 3444, 424240, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424240_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424240 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424240 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424240, 1, 16384⟩
    (by decide) selected_cut_31606

theorem selected_cut_31607 : selected 8 ⟨810792, by decide⟩
    (prefixPartial 13 424241) = some ⟨13, 2, 0, 810792, 424241, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_424241_810792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424241 ⟨810792, by decide⟩ :=
  accepted_of_selected 13 424241 ⟨810792, by decide⟩ ⟨13, 2, 0, 810792, 424241, 2569, 16384⟩
    (by decide) selected_cut_31607

theorem selected_cut_31608 : selected 8 ⟨810816, by decide⟩
    (prefixPartial 13 424242) = some ⟨13, 2, 0, 810816, 424242, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_424242_810816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424242 ⟨810816, by decide⟩ :=
  accepted_of_selected 13 424242 ⟨810816, by decide⟩ ⟨13, 2, 0, 810816, 424242, 1713, 16384⟩
    (by decide) selected_cut_31608

theorem selected_cut_31609 : selected 8 ⟨810820, by decide⟩
    (prefixPartial 13 424243) = some ⟨13, 2, 0, 810820, 424243, 873, 16384⟩ := by
  decide +kernel

theorem context_13_424243_810820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424243 ⟨810820, by decide⟩ :=
  accepted_of_selected 13 424243 ⟨810820, by decide⟩ ⟨13, 2, 0, 810820, 424243, 873, 16384⟩
    (by decide) selected_cut_31609

theorem unmarked_context_12_106060_810821 : frontier 9 ⟨810821, by decide⟩
    (prefixCache 12 106060) (prefixPartial 12 106060) = false := by
  decide +kernel

theorem node_context_12_106060_810821 : EJMOriginalGlobalDAGData.nodes 9 ⟨810821, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810792, by decide⟩,⟨810816, by decide⟩,⟨810820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106060_810821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106060 ⟨810821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106060
    ⟨810821, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810792, by decide⟩,⟨810816, by decide⟩,⟨810820, by decide⟩]) unmarked_context_12_106060_810821 node_context_12_106060_810821
  intro a
  fin_cases a
  · exact context_13_424240_3444
  · exact context_13_424241_810792
  · exact context_13_424242_810816
  · exact context_13_424243_810820

theorem selected_cut_31610 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424244) = some ⟨13, 1, 0, 3444, 424244, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424244_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424244 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424244 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424244, 1, 16384⟩
    (by decide) selected_cut_31610

theorem selected_cut_31611 : selected 8 ⟨810856, by decide⟩
    (prefixPartial 13 424245) = some ⟨13, 2, 0, 810856, 424245, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_424245_810856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424245 ⟨810856, by decide⟩ :=
  accepted_of_selected 13 424245 ⟨810856, by decide⟩ ⟨13, 2, 0, 810856, 424245, 2209, 16384⟩
    (by decide) selected_cut_31611

theorem selected_cut_31612 : selected 8 ⟨810879, by decide⟩
    (prefixPartial 13 424246) = some ⟨13, 2, 0, 810879, 424246, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_424246_810879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424246 ⟨810879, by decide⟩ :=
  accepted_of_selected 13 424246 ⟨810879, by decide⟩ ⟨13, 2, 0, 810879, 424246, 1341, 16384⟩
    (by decide) selected_cut_31612

theorem selected_cut_31613 : selected 8 ⟨810886, by decide⟩
    (prefixPartial 13 424247) = some ⟨13, 2, 0, 810886, 424247, 741, 16384⟩ := by
  decide +kernel

theorem context_13_424247_810886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424247 ⟨810886, by decide⟩ :=
  accepted_of_selected 13 424247 ⟨810886, by decide⟩ ⟨13, 2, 0, 810886, 424247, 741, 16384⟩
    (by decide) selected_cut_31613

theorem unmarked_context_12_106061_810887 : frontier 9 ⟨810887, by decide⟩
    (prefixCache 12 106061) (prefixPartial 12 106061) = false := by
  decide +kernel

theorem node_context_12_106061_810887 : EJMOriginalGlobalDAGData.nodes 9 ⟨810887, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810856, by decide⟩,⟨810879, by decide⟩,⟨810886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106061_810887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106061 ⟨810887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106061
    ⟨810887, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810856, by decide⟩,⟨810879, by decide⟩,⟨810886, by decide⟩]) unmarked_context_12_106061_810887 node_context_12_106061_810887
  intro a
  fin_cases a
  · exact context_13_424244_3444
  · exact context_13_424245_810856
  · exact context_13_424246_810879
  · exact context_13_424247_810886

theorem selected_cut_31614 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424248) = some ⟨13, 1, 0, 3444, 424248, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424248_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424248 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424248 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424248, 1, 16384⟩
    (by decide) selected_cut_31614

theorem selected_cut_31615 : selected 8 ⟨810917, by decide⟩
    (prefixPartial 13 424249) = some ⟨13, 2, 0, 810917, 424249, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_424249_810917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424249 ⟨810917, by decide⟩ :=
  accepted_of_selected 13 424249 ⟨810917, by decide⟩ ⟨13, 2, 0, 810917, 424249, 2249, 16384⟩
    (by decide) selected_cut_31615

theorem selected_cut_31616 : selected 8 ⟨810943, by decide⟩
    (prefixPartial 13 424250) = some ⟨13, 2, 0, 810943, 424250, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_424250_810943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424250 ⟨810943, by decide⟩ :=
  accepted_of_selected 13 424250 ⟨810943, by decide⟩ ⟨13, 2, 0, 810943, 424250, 1485, 16384⟩
    (by decide) selected_cut_31616

theorem selected_cut_31617 : selected 8 ⟨810950, by decide⟩
    (prefixPartial 13 424251) = some ⟨13, 2, 0, 810950, 424251, 721, 16384⟩ := by
  decide +kernel

theorem context_13_424251_810950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424251 ⟨810950, by decide⟩ :=
  accepted_of_selected 13 424251 ⟨810950, by decide⟩ ⟨13, 2, 0, 810950, 424251, 721, 16384⟩
    (by decide) selected_cut_31617

theorem unmarked_context_12_106062_810951 : frontier 9 ⟨810951, by decide⟩
    (prefixCache 12 106062) (prefixPartial 12 106062) = false := by
  decide +kernel

theorem node_context_12_106062_810951 : EJMOriginalGlobalDAGData.nodes 9 ⟨810951, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810917, by decide⟩,⟨810943, by decide⟩,⟨810950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106062_810951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106062 ⟨810951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106062
    ⟨810951, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810917, by decide⟩,⟨810943, by decide⟩,⟨810950, by decide⟩]) unmarked_context_12_106062_810951 node_context_12_106062_810951
  intro a
  fin_cases a
  · exact context_13_424248_3444
  · exact context_13_424249_810917
  · exact context_13_424250_810943
  · exact context_13_424251_810950

theorem selected_cut_31618 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424252) = some ⟨13, 1, 0, 3444, 424252, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424252_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424252 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424252 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424252, 1, 16384⟩
    (by decide) selected_cut_31618

theorem selected_cut_31619 : selected 8 ⟨810982, by decide⟩
    (prefixPartial 13 424253) = some ⟨13, 2, 0, 810982, 424253, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_424253_810982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424253 ⟨810982, by decide⟩ :=
  accepted_of_selected 13 424253 ⟨810982, by decide⟩ ⟨13, 2, 0, 810982, 424253, 2285, 16384⟩
    (by decide) selected_cut_31619

theorem selected_cut_31620 : selected 8 ⟨811003, by decide⟩
    (prefixPartial 13 424254) = some ⟨13, 2, 0, 811003, 424254, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_424254_811003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424254 ⟨811003, by decide⟩ :=
  accepted_of_selected 13 424254 ⟨811003, by decide⟩ ⟨13, 2, 0, 811003, 424254, 1649, 16384⟩
    (by decide) selected_cut_31620

theorem selected_cut_31621 : selected 8 ⟨811012, by decide⟩
    (prefixPartial 13 424255) = some ⟨13, 2, 0, 811012, 424255, 933, 16384⟩ := by
  decide +kernel

theorem context_13_424255_811012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424255 ⟨811012, by decide⟩ :=
  accepted_of_selected 13 424255 ⟨811012, by decide⟩ ⟨13, 2, 0, 811012, 424255, 933, 16384⟩
    (by decide) selected_cut_31621

theorem unmarked_context_12_106063_811013 : frontier 9 ⟨811013, by decide⟩
    (prefixCache 12 106063) (prefixPartial 12 106063) = false := by
  decide +kernel

theorem node_context_12_106063_811013 : EJMOriginalGlobalDAGData.nodes 9 ⟨811013, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810982, by decide⟩,⟨811003, by decide⟩,⟨811012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106063_811013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106063 ⟨811013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106063
    ⟨811013, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810982, by decide⟩,⟨811003, by decide⟩,⟨811012, by decide⟩]) unmarked_context_12_106063_811013 node_context_12_106063_811013
  intro a
  fin_cases a
  · exact context_13_424252_3444
  · exact context_13_424253_810982
  · exact context_13_424254_811003
  · exact context_13_424255_811012

theorem unmarked_context_11_26515_811014 : frontier 10 ⟨811014, by decide⟩
    (prefixCache 11 26515) (prefixPartial 11 26515) = false := by
  decide +kernel

theorem node_context_11_26515_811014 : EJMOriginalGlobalDAGData.nodes 10 ⟨811014, by decide⟩ =
    .split (coordinate 11) (![⟨810821, by decide⟩,⟨810887, by decide⟩,⟨810951, by decide⟩,⟨811013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26515_811014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26515 ⟨811014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26515
    ⟨811014, by decide⟩ (by decide) (![⟨810821, by decide⟩,⟨810887, by decide⟩,⟨810951, by decide⟩,⟨811013, by decide⟩]) unmarked_context_11_26515_811014 node_context_11_26515_811014
  intro a
  fin_cases a
  · exact context_12_106060_810821
  · exact context_12_106061_810887
  · exact context_12_106062_810951
  · exact context_12_106063_811013

theorem unmarked_context_10_6628_811015 : frontier 11 ⟨811015, by decide⟩
    (prefixCache 10 6628) (prefixPartial 10 6628) = false := by
  decide +kernel

theorem node_context_10_6628_811015 : EJMOriginalGlobalDAGData.nodes 11 ⟨811015, by decide⟩ =
    .split (coordinate 10) (![⟨810184, by decide⟩,⟨810517, by decide⟩,⟨810748, by decide⟩,⟨811014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6628_811015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6628 ⟨811015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6628
    ⟨811015, by decide⟩ (by decide) (![⟨810184, by decide⟩,⟨810517, by decide⟩,⟨810748, by decide⟩,⟨811014, by decide⟩]) unmarked_context_10_6628_811015 node_context_10_6628_811015
  intro a
  fin_cases a
  · exact context_11_26512_810184
  · exact context_11_26513_810517
  · exact context_11_26514_810748
  · exact context_11_26515_811014

theorem selected_cut_31622 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424256) = some ⟨13, 1, 0, 3444, 424256, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424256_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424256 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424256 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424256, 1, 16384⟩
    (by decide) selected_cut_31622

theorem selected_cut_31623 : selected 8 ⟨811044, by decide⟩
    (prefixPartial 13 424257) = some ⟨13, 2, 0, 811044, 424257, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_424257_811044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424257 ⟨811044, by decide⟩ :=
  accepted_of_selected 13 424257 ⟨811044, by decide⟩ ⟨13, 2, 0, 811044, 424257, 1885, 16384⟩
    (by decide) selected_cut_31623

theorem selected_cut_31624 : selected 8 ⟨811064, by decide⟩
    (prefixPartial 13 424258) = some ⟨13, 2, 0, 811064, 424258, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_424258_811064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424258 ⟨811064, by decide⟩ :=
  accepted_of_selected 13 424258 ⟨811064, by decide⟩ ⟨13, 2, 0, 811064, 424258, 1557, 16384⟩
    (by decide) selected_cut_31624

theorem selected_cut_31625 : selected 8 ⟨811073, by decide⟩
    (prefixPartial 13 424259) = some ⟨13, 2, 0, 811073, 424259, 917, 16384⟩ := by
  decide +kernel

theorem context_13_424259_811073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424259 ⟨811073, by decide⟩ :=
  accepted_of_selected 13 424259 ⟨811073, by decide⟩ ⟨13, 2, 0, 811073, 424259, 917, 16384⟩
    (by decide) selected_cut_31625

theorem unmarked_context_12_106064_811074 : frontier 9 ⟨811074, by decide⟩
    (prefixCache 12 106064) (prefixPartial 12 106064) = false := by
  decide +kernel

theorem node_context_12_106064_811074 : EJMOriginalGlobalDAGData.nodes 9 ⟨811074, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨811044, by decide⟩,⟨811064, by decide⟩,⟨811073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106064_811074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106064 ⟨811074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106064
    ⟨811074, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨811044, by decide⟩,⟨811064, by decide⟩,⟨811073, by decide⟩]) unmarked_context_12_106064_811074 node_context_12_106064_811074
  intro a
  fin_cases a
  · exact context_13_424256_3444
  · exact context_13_424257_811044
  · exact context_13_424258_811064
  · exact context_13_424259_811073

theorem selected_cut_31626 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424260) = some ⟨13, 1, 0, 3444, 424260, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424260_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424260 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424260 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424260, 1, 16384⟩
    (by decide) selected_cut_31626

theorem selected_cut_31627 : selected 8 ⟨811109, by decide⟩
    (prefixPartial 13 424261) = some ⟨13, 2, 0, 811109, 424261, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_424261_811109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424261 ⟨811109, by decide⟩ :=
  accepted_of_selected 13 424261 ⟨811109, by decide⟩ ⟨13, 2, 0, 811109, 424261, 2153, 16384⟩
    (by decide) selected_cut_31627

theorem selected_cut_31628 : selected 8 ⟨811127, by decide⟩
    (prefixPartial 13 424262) = some ⟨13, 2, 0, 811127, 424262, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_424262_811127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424262 ⟨811127, by decide⟩ :=
  accepted_of_selected 13 424262 ⟨811127, by decide⟩ ⟨13, 2, 0, 811127, 424262, 1513, 16384⟩
    (by decide) selected_cut_31628

theorem selected_cut_31629 : selected 8 ⟨811137, by decide⟩
    (prefixPartial 13 424263) = some ⟨13, 2, 0, 811137, 424263, 901, 16384⟩ := by
  decide +kernel

theorem context_13_424263_811137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424263 ⟨811137, by decide⟩ :=
  accepted_of_selected 13 424263 ⟨811137, by decide⟩ ⟨13, 2, 0, 811137, 424263, 901, 16384⟩
    (by decide) selected_cut_31629

theorem unmarked_context_12_106065_811138 : frontier 9 ⟨811138, by decide⟩
    (prefixCache 12 106065) (prefixPartial 12 106065) = false := by
  decide +kernel

theorem node_context_12_106065_811138 : EJMOriginalGlobalDAGData.nodes 9 ⟨811138, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨811109, by decide⟩,⟨811127, by decide⟩,⟨811137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106065_811138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106065 ⟨811138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106065
    ⟨811138, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨811109, by decide⟩,⟨811127, by decide⟩,⟨811137, by decide⟩]) unmarked_context_12_106065_811138 node_context_12_106065_811138
  intro a
  fin_cases a
  · exact context_13_424260_3444
  · exact context_13_424261_811109
  · exact context_13_424262_811127
  · exact context_13_424263_811137

theorem selected_cut_31630 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424264) = some ⟨13, 1, 0, 3444, 424264, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424264_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424264 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424264 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424264, 1, 16384⟩
    (by decide) selected_cut_31630

theorem selected_cut_31631 : selected 8 ⟨811158, by decide⟩
    (prefixPartial 13 424265) = some ⟨13, 2, 0, 811158, 424265, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_424265_811158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424265 ⟨811158, by decide⟩ :=
  accepted_of_selected 13 424265 ⟨811158, by decide⟩ ⟨13, 2, 0, 811158, 424265, 1985, 16384⟩
    (by decide) selected_cut_31631

theorem selected_cut_31632 : selected 8 ⟨811178, by decide⟩
    (prefixPartial 13 424266) = some ⟨13, 2, 0, 811178, 424266, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_424266_811178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424266 ⟨811178, by decide⟩ :=
  accepted_of_selected 13 424266 ⟨811178, by decide⟩ ⟨13, 2, 0, 811178, 424266, 1237, 16384⟩
    (by decide) selected_cut_31632

theorem selected_cut_31633 : selected 8 ⟨811188, by decide⟩
    (prefixPartial 13 424267) = some ⟨13, 2, 0, 811188, 424267, 949, 16384⟩ := by
  decide +kernel

theorem context_13_424267_811188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424267 ⟨811188, by decide⟩ :=
  accepted_of_selected 13 424267 ⟨811188, by decide⟩ ⟨13, 2, 0, 811188, 424267, 949, 16384⟩
    (by decide) selected_cut_31633

theorem unmarked_context_12_106066_811189 : frontier 9 ⟨811189, by decide⟩
    (prefixCache 12 106066) (prefixPartial 12 106066) = false := by
  decide +kernel

theorem node_context_12_106066_811189 : EJMOriginalGlobalDAGData.nodes 9 ⟨811189, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨811158, by decide⟩,⟨811178, by decide⟩,⟨811188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106066_811189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106066 ⟨811189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106066
    ⟨811189, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨811158, by decide⟩,⟨811178, by decide⟩,⟨811188, by decide⟩]) unmarked_context_12_106066_811189 node_context_12_106066_811189
  intro a
  fin_cases a
  · exact context_13_424264_3444
  · exact context_13_424265_811158
  · exact context_13_424266_811178
  · exact context_13_424267_811188

theorem selected_cut_31634 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424268) = some ⟨13, 1, 0, 3444, 424268, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424268_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424268 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424268 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424268, 1, 16384⟩
    (by decide) selected_cut_31634

theorem selected_cut_31635 : selected 8 ⟨811231, by decide⟩
    (prefixPartial 13 424269) = some ⟨13, 2, 0, 811231, 424269, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_424269_811231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424269 ⟨811231, by decide⟩ :=
  accepted_of_selected 13 424269 ⟨811231, by decide⟩ ⟨13, 2, 0, 811231, 424269, 2373, 16384⟩
    (by decide) selected_cut_31635

theorem selected_cut_31636 : selected 8 ⟨811263, by decide⟩
    (prefixPartial 13 424270) = some ⟨13, 2, 0, 811263, 424270, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_424270_811263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424270 ⟨811263, by decide⟩ :=
  accepted_of_selected 13 424270 ⟨811263, by decide⟩ ⟨13, 2, 0, 811263, 424270, 1721, 16384⟩
    (by decide) selected_cut_31636

theorem selected_cut_31637 : selected 8 ⟨811277, by decide⟩
    (prefixPartial 13 424271) = some ⟨13, 2, 0, 811277, 424271, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_424271_811277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424271 ⟨811277, by decide⟩ :=
  accepted_of_selected 13 424271 ⟨811277, by decide⟩ ⟨13, 2, 0, 811277, 424271, 1025, 16384⟩
    (by decide) selected_cut_31637

theorem unmarked_context_12_106067_811278 : frontier 9 ⟨811278, by decide⟩
    (prefixCache 12 106067) (prefixPartial 12 106067) = false := by
  decide +kernel

theorem node_context_12_106067_811278 : EJMOriginalGlobalDAGData.nodes 9 ⟨811278, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨811231, by decide⟩,⟨811263, by decide⟩,⟨811277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106067_811278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106067 ⟨811278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106067
    ⟨811278, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨811231, by decide⟩,⟨811263, by decide⟩,⟨811277, by decide⟩]) unmarked_context_12_106067_811278 node_context_12_106067_811278
  intro a
  fin_cases a
  · exact context_13_424268_3444
  · exact context_13_424269_811231
  · exact context_13_424270_811263
  · exact context_13_424271_811277

theorem unmarked_context_11_26516_811279 : frontier 10 ⟨811279, by decide⟩
    (prefixCache 11 26516) (prefixPartial 11 26516) = false := by
  decide +kernel

theorem node_context_11_26516_811279 : EJMOriginalGlobalDAGData.nodes 10 ⟨811279, by decide⟩ =
    .split (coordinate 11) (![⟨811074, by decide⟩,⟨811138, by decide⟩,⟨811189, by decide⟩,⟨811278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26516_811279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26516 ⟨811279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26516
    ⟨811279, by decide⟩ (by decide) (![⟨811074, by decide⟩,⟨811138, by decide⟩,⟨811189, by decide⟩,⟨811278, by decide⟩]) unmarked_context_11_26516_811279 node_context_11_26516_811279
  intro a
  fin_cases a
  · exact context_12_106064_811074
  · exact context_12_106065_811138
  · exact context_12_106066_811189
  · exact context_12_106067_811278

theorem selected_cut_31638 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424272) = some ⟨13, 1, 0, 3444, 424272, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424272_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424272 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424272 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424272, 1, 16384⟩
    (by decide) selected_cut_31638

theorem selected_cut_31639 : selected 8 ⟨811309, by decide⟩
    (prefixPartial 13 424273) = some ⟨13, 2, 0, 811309, 424273, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_424273_811309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424273 ⟨811309, by decide⟩ :=
  accepted_of_selected 13 424273 ⟨811309, by decide⟩ ⟨13, 2, 0, 811309, 424273, 1797, 16384⟩
    (by decide) selected_cut_31639

theorem selected_cut_31640 : selected 8 ⟨811335, by decide⟩
    (prefixPartial 13 424274) = some ⟨13, 2, 0, 811335, 424274, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_424274_811335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424274 ⟨811335, by decide⟩ :=
  accepted_of_selected 13 424274 ⟨811335, by decide⟩ ⟨13, 2, 0, 811335, 424274, 1701, 16384⟩
    (by decide) selected_cut_31640

theorem selected_cut_31641 : selected 8 ⟨811341, by decide⟩
    (prefixPartial 13 424275) = some ⟨13, 2, 0, 811341, 424275, 929, 16384⟩ := by
  decide +kernel

theorem context_13_424275_811341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424275 ⟨811341, by decide⟩ :=
  accepted_of_selected 13 424275 ⟨811341, by decide⟩ ⟨13, 2, 0, 811341, 424275, 929, 16384⟩
    (by decide) selected_cut_31641

theorem unmarked_context_12_106068_811342 : frontier 9 ⟨811342, by decide⟩
    (prefixCache 12 106068) (prefixPartial 12 106068) = false := by
  decide +kernel

theorem node_context_12_106068_811342 : EJMOriginalGlobalDAGData.nodes 9 ⟨811342, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨811309, by decide⟩,⟨811335, by decide⟩,⟨811341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106068_811342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106068 ⟨811342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106068
    ⟨811342, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨811309, by decide⟩,⟨811335, by decide⟩,⟨811341, by decide⟩]) unmarked_context_12_106068_811342 node_context_12_106068_811342
  intro a
  fin_cases a
  · exact context_13_424272_3444
  · exact context_13_424273_811309
  · exact context_13_424274_811335
  · exact context_13_424275_811341

theorem selected_cut_31642 : selected 9 ⟨811395, by decide⟩
    (prefixPartial 12 106069) = some ⟨12, 2, 0, 811395, 106069, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_106069_811395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106069 ⟨811395, by decide⟩ :=
  accepted_of_selected 12 106069 ⟨811395, by decide⟩ ⟨12, 2, 0, 811395, 106069, 3705, 65536⟩
    (by decide) selected_cut_31642

theorem selected_cut_31643 : selected 9 ⟨811444, by decide⟩
    (prefixPartial 12 106070) = some ⟨12, 2, 0, 811444, 106070, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_106070_811444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106070 ⟨811444, by decide⟩ :=
  accepted_of_selected 12 106070 ⟨811444, by decide⟩ ⟨12, 2, 0, 811444, 106070, 3729, 65536⟩
    (by decide) selected_cut_31643

theorem selected_cut_31644 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424284) = some ⟨13, 1, 0, 3444, 424284, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424284_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424284 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424284 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424284, 1, 16384⟩
    (by decide) selected_cut_31644

theorem selected_cut_31645 : selected 8 ⟨811470, by decide⟩
    (prefixPartial 13 424285) = some ⟨13, 2, 0, 811470, 424285, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_424285_811470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424285 ⟨811470, by decide⟩ :=
  accepted_of_selected 13 424285 ⟨811470, by decide⟩ ⟨13, 2, 0, 811470, 424285, 1789, 16384⟩
    (by decide) selected_cut_31645

theorem selected_cut_31646 : selected 8 ⟨811505, by decide⟩
    (prefixPartial 13 424286) = some ⟨13, 2, 0, 811505, 424286, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_424286_811505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424286 ⟨811505, by decide⟩ :=
  accepted_of_selected 13 424286 ⟨811505, by decide⟩ ⟨13, 2, 0, 811505, 424286, 1853, 16384⟩
    (by decide) selected_cut_31646

theorem selected_cut_31647 : selected 8 ⟨811512, by decide⟩
    (prefixPartial 13 424287) = some ⟨13, 2, 0, 811512, 424287, 985, 16384⟩ := by
  decide +kernel

theorem context_13_424287_811512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424287 ⟨811512, by decide⟩ :=
  accepted_of_selected 13 424287 ⟨811512, by decide⟩ ⟨13, 2, 0, 811512, 424287, 985, 16384⟩
    (by decide) selected_cut_31647

theorem unmarked_context_12_106071_811513 : frontier 9 ⟨811513, by decide⟩
    (prefixCache 12 106071) (prefixPartial 12 106071) = false := by
  decide +kernel

theorem node_context_12_106071_811513 : EJMOriginalGlobalDAGData.nodes 9 ⟨811513, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨811470, by decide⟩,⟨811505, by decide⟩,⟨811512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106071_811513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106071 ⟨811513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106071
    ⟨811513, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨811470, by decide⟩,⟨811505, by decide⟩,⟨811512, by decide⟩]) unmarked_context_12_106071_811513 node_context_12_106071_811513
  intro a
  fin_cases a
  · exact context_13_424284_3444
  · exact context_13_424285_811470
  · exact context_13_424286_811505
  · exact context_13_424287_811512

theorem unmarked_context_11_26517_811514 : frontier 10 ⟨811514, by decide⟩
    (prefixCache 11 26517) (prefixPartial 11 26517) = false := by
  decide +kernel

theorem node_context_11_26517_811514 : EJMOriginalGlobalDAGData.nodes 10 ⟨811514, by decide⟩ =
    .split (coordinate 11) (![⟨811342, by decide⟩,⟨811395, by decide⟩,⟨811444, by decide⟩,⟨811513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26517_811514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26517 ⟨811514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26517
    ⟨811514, by decide⟩ (by decide) (![⟨811342, by decide⟩,⟨811395, by decide⟩,⟨811444, by decide⟩,⟨811513, by decide⟩]) unmarked_context_11_26517_811514 node_context_11_26517_811514
  intro a
  fin_cases a
  · exact context_12_106068_811342
  · exact context_12_106069_811395
  · exact context_12_106070_811444
  · exact context_12_106071_811513

theorem selected_cut_31648 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424288) = some ⟨13, 1, 0, 3444, 424288, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424288_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424288 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424288 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424288, 1, 16384⟩
    (by decide) selected_cut_31648

theorem selected_cut_31649 : selected 8 ⟨811540, by decide⟩
    (prefixPartial 13 424289) = some ⟨13, 2, 0, 811540, 424289, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_424289_811540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424289 ⟨811540, by decide⟩ :=
  accepted_of_selected 13 424289 ⟨811540, by decide⟩ ⟨13, 2, 0, 811540, 424289, 1597, 16384⟩
    (by decide) selected_cut_31649

theorem selected_cut_31650 : selected 8 ⟨811573, by decide⟩
    (prefixPartial 13 424290) = some ⟨13, 2, 0, 811573, 424290, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_424290_811573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424290 ⟨811573, by decide⟩ :=
  accepted_of_selected 13 424290 ⟨811573, by decide⟩ ⟨13, 2, 0, 811573, 424290, 1749, 16384⟩
    (by decide) selected_cut_31650

theorem selected_cut_31651 : selected 8 ⟨811581, by decide⟩
    (prefixPartial 13 424291) = some ⟨13, 2, 0, 811581, 424291, 809, 16384⟩ := by
  decide +kernel

theorem context_13_424291_811581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424291 ⟨811581, by decide⟩ :=
  accepted_of_selected 13 424291 ⟨811581, by decide⟩ ⟨13, 2, 0, 811581, 424291, 809, 16384⟩
    (by decide) selected_cut_31651

theorem unmarked_context_12_106072_811582 : frontier 9 ⟨811582, by decide⟩
    (prefixCache 12 106072) (prefixPartial 12 106072) = false := by
  decide +kernel

theorem node_context_12_106072_811582 : EJMOriginalGlobalDAGData.nodes 9 ⟨811582, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨811540, by decide⟩,⟨811573, by decide⟩,⟨811581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106072_811582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106072 ⟨811582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106072
    ⟨811582, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨811540, by decide⟩,⟨811573, by decide⟩,⟨811581, by decide⟩]) unmarked_context_12_106072_811582 node_context_12_106072_811582
  intro a
  fin_cases a
  · exact context_13_424288_3444
  · exact context_13_424289_811540
  · exact context_13_424290_811573
  · exact context_13_424291_811581

theorem selected_cut_31652 : selected 9 ⟨811629, by decide⟩
    (prefixPartial 12 106073) = some ⟨12, 2, 0, 811629, 106073, 3681, 65536⟩ := by
  decide +kernel

theorem context_12_106073_811629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106073 ⟨811629, by decide⟩ :=
  accepted_of_selected 12 106073 ⟨811629, by decide⟩ ⟨12, 2, 0, 811629, 106073, 3681, 65536⟩
    (by decide) selected_cut_31652

theorem selected_cut_31653 : selected 9 ⟨811630, by decide⟩
    (prefixPartial 12 106074) = some ⟨12, 1, 0, 811630, 106074, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106074_811630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106074 ⟨811630, by decide⟩ :=
  accepted_of_selected 12 106074 ⟨811630, by decide⟩ ⟨12, 1, 0, 811630, 106074, 1, 65536⟩
    (by decide) selected_cut_31653

theorem selected_cut_31654 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424300) = some ⟨13, 1, 0, 3444, 424300, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424300_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424300 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424300 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424300, 1, 16384⟩
    (by decide) selected_cut_31654

theorem selected_cut_31655 : selected 8 ⟨811663, by decide⟩
    (prefixPartial 13 424301) = some ⟨13, 2, 0, 811663, 424301, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_424301_811663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424301 ⟨811663, by decide⟩ :=
  accepted_of_selected 13 424301 ⟨811663, by decide⟩ ⟨13, 2, 0, 811663, 424301, 1861, 16384⟩
    (by decide) selected_cut_31655

theorem selected_cut_31656 : selected 8 ⟨811692, by decide⟩
    (prefixPartial 13 424302) = some ⟨13, 2, 0, 811692, 424302, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_424302_811692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424302 ⟨811692, by decide⟩ :=
  accepted_of_selected 13 424302 ⟨811692, by decide⟩ ⟨13, 2, 0, 811692, 424302, 1741, 16384⟩
    (by decide) selected_cut_31656

theorem selected_cut_31657 : selected 8 ⟨811698, by decide⟩
    (prefixPartial 13 424303) = some ⟨13, 2, 0, 811698, 424303, 861, 16384⟩ := by
  decide +kernel

theorem context_13_424303_811698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424303 ⟨811698, by decide⟩ :=
  accepted_of_selected 13 424303 ⟨811698, by decide⟩ ⟨13, 2, 0, 811698, 424303, 861, 16384⟩
    (by decide) selected_cut_31657

theorem unmarked_context_12_106075_811699 : frontier 9 ⟨811699, by decide⟩
    (prefixCache 12 106075) (prefixPartial 12 106075) = false := by
  decide +kernel

theorem node_context_12_106075_811699 : EJMOriginalGlobalDAGData.nodes 9 ⟨811699, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨811663, by decide⟩,⟨811692, by decide⟩,⟨811698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106075_811699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106075 ⟨811699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106075
    ⟨811699, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨811663, by decide⟩,⟨811692, by decide⟩,⟨811698, by decide⟩]) unmarked_context_12_106075_811699 node_context_12_106075_811699
  intro a
  fin_cases a
  · exact context_13_424300_3444
  · exact context_13_424301_811663
  · exact context_13_424302_811692
  · exact context_13_424303_811698

theorem unmarked_context_11_26518_811700 : frontier 10 ⟨811700, by decide⟩
    (prefixCache 11 26518) (prefixPartial 11 26518) = false := by
  decide +kernel

theorem node_context_11_26518_811700 : EJMOriginalGlobalDAGData.nodes 10 ⟨811700, by decide⟩ =
    .split (coordinate 11) (![⟨811582, by decide⟩,⟨811629, by decide⟩,⟨811630, by decide⟩,⟨811699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26518_811700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26518 ⟨811700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26518
    ⟨811700, by decide⟩ (by decide) (![⟨811582, by decide⟩,⟨811629, by decide⟩,⟨811630, by decide⟩,⟨811699, by decide⟩]) unmarked_context_11_26518_811700 node_context_11_26518_811700
  intro a
  fin_cases a
  · exact context_12_106072_811582
  · exact context_12_106073_811629
  · exact context_12_106074_811630
  · exact context_12_106075_811699

theorem selected_cut_31658 : selected 9 ⟨811752, by decide⟩
    (prefixPartial 12 106076) = some ⟨12, 2, 0, 811752, 106076, 4081, 65536⟩ := by
  decide +kernel

theorem context_12_106076_811752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106076 ⟨811752, by decide⟩ :=
  accepted_of_selected 12 106076 ⟨811752, by decide⟩ ⟨12, 2, 0, 811752, 106076, 4081, 65536⟩
    (by decide) selected_cut_31658

theorem selected_cut_31659 : selected 9 ⟨811808, by decide⟩
    (prefixPartial 12 106077) = some ⟨12, 2, 0, 811808, 106077, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_106077_811808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106077 ⟨811808, by decide⟩ :=
  accepted_of_selected 12 106077 ⟨811808, by decide⟩ ⟨12, 2, 0, 811808, 106077, 3569, 65536⟩
    (by decide) selected_cut_31659

theorem selected_cut_31660 : selected 9 ⟨811856, by decide⟩
    (prefixPartial 12 106078) = some ⟨12, 2, 0, 811856, 106078, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_106078_811856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106078 ⟨811856, by decide⟩ :=
  accepted_of_selected 12 106078 ⟨811856, by decide⟩ ⟨12, 2, 0, 811856, 106078, 3577, 65536⟩
    (by decide) selected_cut_31660

theorem selected_cut_31661 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424316) = some ⟨13, 1, 0, 3444, 424316, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424316_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424316 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424316 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424316, 1, 16384⟩
    (by decide) selected_cut_31661

theorem selected_cut_31662 : selected 8 ⟨811873, by decide⟩
    (prefixPartial 13 424317) = some ⟨13, 2, 0, 811873, 424317, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_424317_811873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424317 ⟨811873, by decide⟩ :=
  accepted_of_selected 13 424317 ⟨811873, by decide⟩ ⟨13, 2, 0, 811873, 424317, 1385, 16384⟩
    (by decide) selected_cut_31662

theorem selected_cut_31663 : selected 8 ⟨811900, by decide⟩
    (prefixPartial 13 424318) = some ⟨13, 2, 0, 811900, 424318, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_424318_811900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424318 ⟨811900, by decide⟩ :=
  accepted_of_selected 13 424318 ⟨811900, by decide⟩ ⟨13, 2, 0, 811900, 424318, 1777, 16384⟩
    (by decide) selected_cut_31663

theorem selected_cut_31664 : selected 8 ⟨811907, by decide⟩
    (prefixPartial 13 424319) = some ⟨13, 2, 0, 811907, 424319, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_424319_811907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424319 ⟨811907, by decide⟩ :=
  accepted_of_selected 13 424319 ⟨811907, by decide⟩ ⟨13, 2, 0, 811907, 424319, 1001, 16384⟩
    (by decide) selected_cut_31664

theorem unmarked_context_12_106079_811908 : frontier 9 ⟨811908, by decide⟩
    (prefixCache 12 106079) (prefixPartial 12 106079) = false := by
  decide +kernel

theorem node_context_12_106079_811908 : EJMOriginalGlobalDAGData.nodes 9 ⟨811908, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨811873, by decide⟩,⟨811900, by decide⟩,⟨811907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106079_811908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106079 ⟨811908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106079
    ⟨811908, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨811873, by decide⟩,⟨811900, by decide⟩,⟨811907, by decide⟩]) unmarked_context_12_106079_811908 node_context_12_106079_811908
  intro a
  fin_cases a
  · exact context_13_424316_3444
  · exact context_13_424317_811873
  · exact context_13_424318_811900
  · exact context_13_424319_811907

theorem unmarked_context_11_26519_811909 : frontier 10 ⟨811909, by decide⟩
    (prefixCache 11 26519) (prefixPartial 11 26519) = false := by
  decide +kernel

theorem node_context_11_26519_811909 : EJMOriginalGlobalDAGData.nodes 10 ⟨811909, by decide⟩ =
    .split (coordinate 11) (![⟨811752, by decide⟩,⟨811808, by decide⟩,⟨811856, by decide⟩,⟨811908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26519_811909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26519 ⟨811909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26519
    ⟨811909, by decide⟩ (by decide) (![⟨811752, by decide⟩,⟨811808, by decide⟩,⟨811856, by decide⟩,⟨811908, by decide⟩]) unmarked_context_11_26519_811909 node_context_11_26519_811909
  intro a
  fin_cases a
  · exact context_12_106076_811752
  · exact context_12_106077_811808
  · exact context_12_106078_811856
  · exact context_12_106079_811908

theorem unmarked_context_10_6629_811910 : frontier 11 ⟨811910, by decide⟩
    (prefixCache 10 6629) (prefixPartial 10 6629) = false := by
  decide +kernel

theorem node_context_10_6629_811910 : EJMOriginalGlobalDAGData.nodes 11 ⟨811910, by decide⟩ =
    .split (coordinate 10) (![⟨811279, by decide⟩,⟨811514, by decide⟩,⟨811700, by decide⟩,⟨811909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6629_811910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6629 ⟨811910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6629
    ⟨811910, by decide⟩ (by decide) (![⟨811279, by decide⟩,⟨811514, by decide⟩,⟨811700, by decide⟩,⟨811909, by decide⟩]) unmarked_context_10_6629_811910 node_context_10_6629_811910
  intro a
  fin_cases a
  · exact context_11_26516_811279
  · exact context_11_26517_811514
  · exact context_11_26518_811700
  · exact context_11_26519_811909

theorem selected_cut_31665 : selected 9 ⟨811974, by decide⟩
    (prefixPartial 12 106080) = some ⟨12, 2, 0, 811974, 106080, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_106080_811974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106080 ⟨811974, by decide⟩ :=
  accepted_of_selected 12 106080 ⟨811974, by decide⟩ ⟨12, 2, 0, 811974, 106080, 3505, 65536⟩
    (by decide) selected_cut_31665

theorem selected_cut_31666 : selected 9 ⟨812034, by decide⟩
    (prefixPartial 12 106081) = some ⟨12, 2, 0, 812034, 106081, 3661, 65536⟩ := by
  decide +kernel

theorem context_12_106081_812034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106081 ⟨812034, by decide⟩ :=
  accepted_of_selected 12 106081 ⟨812034, by decide⟩ ⟨12, 2, 0, 812034, 106081, 3661, 65536⟩
    (by decide) selected_cut_31666

theorem selected_cut_31667 : selected 9 ⟨812086, by decide⟩
    (prefixPartial 12 106082) = some ⟨12, 2, 0, 812086, 106082, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_106082_812086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106082 ⟨812086, by decide⟩ :=
  accepted_of_selected 12 106082 ⟨812086, by decide⟩ ⟨12, 2, 0, 812086, 106082, 3233, 65536⟩
    (by decide) selected_cut_31667

theorem selected_cut_31668 : selected 9 ⟨812157, by decide⟩
    (prefixPartial 12 106083) = some ⟨12, 2, 0, 812157, 106083, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_106083_812157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106083 ⟨812157, by decide⟩ :=
  accepted_of_selected 12 106083 ⟨812157, by decide⟩ ⟨12, 2, 0, 812157, 106083, 4077, 65536⟩
    (by decide) selected_cut_31668

theorem unmarked_context_11_26520_812158 : frontier 10 ⟨812158, by decide⟩
    (prefixCache 11 26520) (prefixPartial 11 26520) = false := by
  decide +kernel

theorem node_context_11_26520_812158 : EJMOriginalGlobalDAGData.nodes 10 ⟨812158, by decide⟩ =
    .split (coordinate 11) (![⟨811974, by decide⟩,⟨812034, by decide⟩,⟨812086, by decide⟩,⟨812157, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26520_812158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26520 ⟨812158, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26520
    ⟨812158, by decide⟩ (by decide) (![⟨811974, by decide⟩,⟨812034, by decide⟩,⟨812086, by decide⟩,⟨812157, by decide⟩]) unmarked_context_11_26520_812158 node_context_11_26520_812158
  intro a
  fin_cases a
  · exact context_12_106080_811974
  · exact context_12_106081_812034
  · exact context_12_106082_812086
  · exact context_12_106083_812157

theorem selected_cut_31669 : selected 9 ⟨812207, by decide⟩
    (prefixPartial 12 106084) = some ⟨12, 2, 0, 812207, 106084, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_106084_812207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106084 ⟨812207, by decide⟩ :=
  accepted_of_selected 12 106084 ⟨812207, by decide⟩ ⟨12, 2, 0, 812207, 106084, 3829, 65536⟩
    (by decide) selected_cut_31669

theorem selected_cut_31670 : selected 9 ⟨812261, by decide⟩
    (prefixPartial 12 106085) = some ⟨12, 2, 0, 812261, 106085, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_106085_812261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106085 ⟨812261, by decide⟩ :=
  accepted_of_selected 12 106085 ⟨812261, by decide⟩ ⟨12, 2, 0, 812261, 106085, 3257, 65536⟩
    (by decide) selected_cut_31670

theorem selected_cut_31671 : selected 9 ⟨812303, by decide⟩
    (prefixPartial 12 106086) = some ⟨12, 2, 0, 812303, 106086, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_106086_812303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106086 ⟨812303, by decide⟩ :=
  accepted_of_selected 12 106086 ⟨812303, by decide⟩ ⟨12, 2, 0, 812303, 106086, 3201, 65536⟩
    (by decide) selected_cut_31671

theorem selected_cut_31672 : selected 9 ⟨812357, by decide⟩
    (prefixPartial 12 106087) = some ⟨12, 2, 0, 812357, 106087, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_106087_812357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106087 ⟨812357, by decide⟩ :=
  accepted_of_selected 12 106087 ⟨812357, by decide⟩ ⟨12, 2, 0, 812357, 106087, 3861, 65536⟩
    (by decide) selected_cut_31672

theorem unmarked_context_11_26521_812358 : frontier 10 ⟨812358, by decide⟩
    (prefixCache 11 26521) (prefixPartial 11 26521) = false := by
  decide +kernel

theorem node_context_11_26521_812358 : EJMOriginalGlobalDAGData.nodes 10 ⟨812358, by decide⟩ =
    .split (coordinate 11) (![⟨812207, by decide⟩,⟨812261, by decide⟩,⟨812303, by decide⟩,⟨812357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26521_812358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26521 ⟨812358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26521
    ⟨812358, by decide⟩ (by decide) (![⟨812207, by decide⟩,⟨812261, by decide⟩,⟨812303, by decide⟩,⟨812357, by decide⟩]) unmarked_context_11_26521_812358 node_context_11_26521_812358
  intro a
  fin_cases a
  · exact context_12_106084_812207
  · exact context_12_106085_812261
  · exact context_12_106086_812303
  · exact context_12_106087_812357

theorem selected_cut_31673 : selected 9 ⟨812413, by decide⟩
    (prefixPartial 12 106088) = some ⟨12, 2, 0, 812413, 106088, 3477, 65536⟩ := by
  decide +kernel

theorem context_12_106088_812413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106088 ⟨812413, by decide⟩ :=
  accepted_of_selected 12 106088 ⟨812413, by decide⟩ ⟨12, 2, 0, 812413, 106088, 3477, 65536⟩
    (by decide) selected_cut_31673

theorem selected_cut_31674 : selected 9 ⟨812455, by decide⟩
    (prefixPartial 12 106089) = some ⟨12, 2, 0, 812455, 106089, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_106089_812455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106089 ⟨812455, by decide⟩ :=
  accepted_of_selected 12 106089 ⟨812455, by decide⟩ ⟨12, 2, 0, 812455, 106089, 3165, 65536⟩
    (by decide) selected_cut_31674

theorem selected_cut_31675 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 106090) = some ⟨12, 1, 0, 445248, 106090, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106090_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106090 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 106090 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 106090, 1, 65536⟩
    (by decide) selected_cut_31675

theorem selected_cut_31676 : selected 9 ⟨812504, by decide⟩
    (prefixPartial 12 106091) = some ⟨12, 2, 0, 812504, 106091, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_106091_812504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106091 ⟨812504, by decide⟩ :=
  accepted_of_selected 12 106091 ⟨812504, by decide⟩ ⟨12, 2, 0, 812504, 106091, 3573, 65536⟩
    (by decide) selected_cut_31676

theorem unmarked_context_11_26522_812505 : frontier 10 ⟨812505, by decide⟩
    (prefixCache 11 26522) (prefixPartial 11 26522) = false := by
  decide +kernel

theorem node_context_11_26522_812505 : EJMOriginalGlobalDAGData.nodes 10 ⟨812505, by decide⟩ =
    .split (coordinate 11) (![⟨812413, by decide⟩,⟨812455, by decide⟩,⟨445248, by decide⟩,⟨812504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26522_812505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26522 ⟨812505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26522
    ⟨812505, by decide⟩ (by decide) (![⟨812413, by decide⟩,⟨812455, by decide⟩,⟨445248, by decide⟩,⟨812504, by decide⟩]) unmarked_context_11_26522_812505 node_context_11_26522_812505
  intro a
  fin_cases a
  · exact context_12_106088_812413
  · exact context_12_106089_812455
  · exact context_12_106090_445248
  · exact context_12_106091_812504

theorem selected_cut_31677 : selected 9 ⟨812545, by decide⟩
    (prefixPartial 12 106092) = some ⟨12, 2, 0, 812545, 106092, 3377, 65536⟩ := by
  decide +kernel

theorem context_12_106092_812545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106092 ⟨812545, by decide⟩ :=
  accepted_of_selected 12 106092 ⟨812545, by decide⟩ ⟨12, 2, 0, 812545, 106092, 3377, 65536⟩
    (by decide) selected_cut_31677

theorem selected_cut_31678 : selected 9 ⟨812586, by decide⟩
    (prefixPartial 12 106093) = some ⟨12, 2, 0, 812586, 106093, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_106093_812586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106093 ⟨812586, by decide⟩ :=
  accepted_of_selected 12 106093 ⟨812586, by decide⟩ ⟨12, 2, 0, 812586, 106093, 2909, 65536⟩
    (by decide) selected_cut_31678

theorem selected_cut_31679 : selected 9 ⟨812622, by decide⟩
    (prefixPartial 12 106094) = some ⟨12, 2, 0, 812622, 106094, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_106094_812622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106094 ⟨812622, by decide⟩ :=
  accepted_of_selected 12 106094 ⟨812622, by decide⟩ ⟨12, 2, 0, 812622, 106094, 2861, 65536⟩
    (by decide) selected_cut_31679

theorem selected_cut_31680 : selected 9 ⟨812671, by decide⟩
    (prefixPartial 12 106095) = some ⟨12, 2, 0, 812671, 106095, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_106095_812671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106095 ⟨812671, by decide⟩ :=
  accepted_of_selected 12 106095 ⟨812671, by decide⟩ ⟨12, 2, 0, 812671, 106095, 3357, 65536⟩
    (by decide) selected_cut_31680

theorem unmarked_context_11_26523_812672 : frontier 10 ⟨812672, by decide⟩
    (prefixCache 11 26523) (prefixPartial 11 26523) = false := by
  decide +kernel

theorem node_context_11_26523_812672 : EJMOriginalGlobalDAGData.nodes 10 ⟨812672, by decide⟩ =
    .split (coordinate 11) (![⟨812545, by decide⟩,⟨812586, by decide⟩,⟨812622, by decide⟩,⟨812671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26523_812672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26523 ⟨812672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26523
    ⟨812672, by decide⟩ (by decide) (![⟨812545, by decide⟩,⟨812586, by decide⟩,⟨812622, by decide⟩,⟨812671, by decide⟩]) unmarked_context_11_26523_812672 node_context_11_26523_812672
  intro a
  fin_cases a
  · exact context_12_106092_812545
  · exact context_12_106093_812586
  · exact context_12_106094_812622
  · exact context_12_106095_812671

theorem unmarked_context_10_6630_812673 : frontier 11 ⟨812673, by decide⟩
    (prefixCache 10 6630) (prefixPartial 10 6630) = false := by
  decide +kernel

theorem node_context_10_6630_812673 : EJMOriginalGlobalDAGData.nodes 11 ⟨812673, by decide⟩ =
    .split (coordinate 10) (![⟨812158, by decide⟩,⟨812358, by decide⟩,⟨812505, by decide⟩,⟨812672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6630_812673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6630 ⟨812673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6630
    ⟨812673, by decide⟩ (by decide) (![⟨812158, by decide⟩,⟨812358, by decide⟩,⟨812505, by decide⟩,⟨812672, by decide⟩]) unmarked_context_10_6630_812673 node_context_10_6630_812673
  intro a
  fin_cases a
  · exact context_11_26520_812158
  · exact context_11_26521_812358
  · exact context_11_26522_812505
  · exact context_11_26523_812672

theorem selected_cut_31681 : selected 9 ⟨812728, by decide⟩
    (prefixPartial 12 106096) = some ⟨12, 2, 0, 812728, 106096, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_106096_812728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106096 ⟨812728, by decide⟩ :=
  accepted_of_selected 12 106096 ⟨812728, by decide⟩ ⟨12, 2, 0, 812728, 106096, 3089, 65536⟩
    (by decide) selected_cut_31681

theorem selected_cut_31682 : selected 9 ⟨812768, by decide⟩
    (prefixPartial 12 106097) = some ⟨12, 2, 0, 812768, 106097, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_106097_812768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106097 ⟨812768, by decide⟩ :=
  accepted_of_selected 12 106097 ⟨812768, by decide⟩ ⟨12, 2, 0, 812768, 106097, 2813, 65536⟩
    (by decide) selected_cut_31682

theorem selected_cut_31683 : selected 9 ⟨812807, by decide⟩
    (prefixPartial 12 106098) = some ⟨12, 2, 0, 812807, 106098, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_106098_812807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106098 ⟨812807, by decide⟩ :=
  accepted_of_selected 12 106098 ⟨812807, by decide⟩ ⟨12, 2, 0, 812807, 106098, 2561, 65536⟩
    (by decide) selected_cut_31683

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
