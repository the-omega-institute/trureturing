/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover005
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_00578 : selected 7 ⟨25965, by decide⟩
    (prefixPartial 14 24773) = some ⟨14, 2, 0, 25965, 24773, 1453, 4096⟩ := by
  decide +kernel

theorem context_14_24773_25965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24773 ⟨25965, by decide⟩ :=
  accepted_of_selected 14 24773 ⟨25965, by decide⟩ ⟨14, 2, 0, 25965, 24773, 1453, 4096⟩
    (by decide) selected_cut_00578

theorem selected_cut_00579 : selected 7 ⟨26008, by decide⟩
    (prefixPartial 14 24774) = some ⟨14, 2, 0, 26008, 24774, 1093, 4096⟩ := by
  decide +kernel

theorem context_14_24774_26008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24774 ⟨26008, by decide⟩ :=
  accepted_of_selected 14 24774 ⟨26008, by decide⟩ ⟨14, 2, 0, 26008, 24774, 1093, 4096⟩
    (by decide) selected_cut_00579

theorem selected_cut_00580 : selected 7 ⟨26055, by decide⟩
    (prefixPartial 14 24775) = some ⟨14, 2, 0, 26055, 24775, 1273, 4096⟩ := by
  decide +kernel

theorem context_14_24775_26055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24775 ⟨26055, by decide⟩ :=
  accepted_of_selected 14 24775 ⟨26055, by decide⟩ ⟨14, 2, 0, 26055, 24775, 1273, 4096⟩
    (by decide) selected_cut_00580

theorem unmarked_context_13_6193_26056 : frontier 8 ⟨26056, by decide⟩
    (prefixCache 13 6193) (prefixPartial 13 6193) = false := by
  decide +kernel

theorem node_context_13_6193_26056 : EJMOriginalGlobalDAGData.nodes 8 ⟨26056, by decide⟩ =
    .split (coordinate 13) (![⟨25924, by decide⟩,⟨25965, by decide⟩,⟨26008, by decide⟩,⟨26055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6193_26056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6193 ⟨26056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6193
    ⟨26056, by decide⟩ (by decide) (![⟨25924, by decide⟩,⟨25965, by decide⟩,⟨26008, by decide⟩,⟨26055, by decide⟩]) unmarked_context_13_6193_26056 node_context_13_6193_26056
  intro a
  fin_cases a
  · exact context_14_24772_25924
  · exact context_14_24773_25965
  · exact context_14_24774_26008
  · exact context_14_24775_26055

theorem selected_cut_00581 : selected 8 ⟨1982, by decide⟩
    (prefixPartial 13 6194) = some ⟨13, 1, 0, 1982, 6194, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6194_1982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6194 ⟨1982, by decide⟩ :=
  accepted_of_selected 13 6194 ⟨1982, by decide⟩ ⟨13, 1, 0, 1982, 6194, 1, 16384⟩
    (by decide) selected_cut_00581

theorem selected_cut_00582 : selected 8 ⟨26106, by decide⟩
    (prefixPartial 13 6195) = some ⟨13, 2, 0, 26106, 6195, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_6195_26106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6195 ⟨26106, by decide⟩ :=
  accepted_of_selected 13 6195 ⟨26106, by decide⟩ ⟨13, 2, 0, 26106, 6195, 1069, 16384⟩
    (by decide) selected_cut_00582

theorem unmarked_context_12_1548_26107 : frontier 9 ⟨26107, by decide⟩
    (prefixCache 12 1548) (prefixPartial 12 1548) = false := by
  decide +kernel

theorem node_context_12_1548_26107 : EJMOriginalGlobalDAGData.nodes 9 ⟨26107, by decide⟩ =
    .split (coordinate 12) (![⟨25878, by decide⟩,⟨26056, by decide⟩,⟨1982, by decide⟩,⟨26106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1548_26107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1548 ⟨26107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1548
    ⟨26107, by decide⟩ (by decide) (![⟨25878, by decide⟩,⟨26056, by decide⟩,⟨1982, by decide⟩,⟨26106, by decide⟩]) unmarked_context_12_1548_26107 node_context_12_1548_26107
  intro a
  fin_cases a
  · exact context_13_6192_25878
  · exact context_13_6193_26056
  · exact context_13_6194_1982
  · exact context_13_6195_26106

theorem selected_cut_00583 : selected 8 ⟨26185, by decide⟩
    (prefixPartial 13 6196) = some ⟨13, 2, 0, 26185, 6196, 3757, 16384⟩ := by
  decide +kernel

theorem context_13_6196_26185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6196 ⟨26185, by decide⟩ :=
  accepted_of_selected 13 6196 ⟨26185, by decide⟩ ⟨13, 2, 0, 26185, 6196, 3757, 16384⟩
    (by decide) selected_cut_00583

theorem selected_cut_00584 : selected 7 ⟨26203, by decide⟩
    (prefixPartial 14 24788) = some ⟨14, 2, 0, 26203, 24788, 1245, 4096⟩ := by
  decide +kernel

theorem context_14_24788_26203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24788 ⟨26203, by decide⟩ :=
  accepted_of_selected 14 24788 ⟨26203, by decide⟩ ⟨14, 2, 0, 26203, 24788, 1245, 4096⟩
    (by decide) selected_cut_00584

theorem selected_cut_00585 : selected 7 ⟨26225, by decide⟩
    (prefixPartial 14 24789) = some ⟨14, 2, 0, 26225, 24789, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_24789_26225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24789 ⟨26225, by decide⟩ :=
  accepted_of_selected 14 24789 ⟨26225, by decide⟩ ⟨14, 2, 0, 26225, 24789, 1105, 4096⟩
    (by decide) selected_cut_00585

theorem selected_cut_00586 : selected 7 ⟨26242, by decide⟩
    (prefixPartial 14 24790) = some ⟨14, 2, 0, 26242, 24790, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_24790_26242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24790 ⟨26242, by decide⟩ :=
  accepted_of_selected 14 24790 ⟨26242, by decide⟩ ⟨14, 2, 0, 26242, 24790, 1153, 4096⟩
    (by decide) selected_cut_00586

theorem selected_cut_00587 : selected 7 ⟨26263, by decide⟩
    (prefixPartial 14 24791) = some ⟨14, 2, 0, 26263, 24791, 1093, 4096⟩ := by
  decide +kernel

theorem context_14_24791_26263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24791 ⟨26263, by decide⟩ :=
  accepted_of_selected 14 24791 ⟨26263, by decide⟩ ⟨14, 2, 0, 26263, 24791, 1093, 4096⟩
    (by decide) selected_cut_00587

theorem unmarked_context_13_6197_26264 : frontier 8 ⟨26264, by decide⟩
    (prefixCache 13 6197) (prefixPartial 13 6197) = false := by
  decide +kernel

theorem node_context_13_6197_26264 : EJMOriginalGlobalDAGData.nodes 8 ⟨26264, by decide⟩ =
    .split (coordinate 13) (![⟨26203, by decide⟩,⟨26225, by decide⟩,⟨26242, by decide⟩,⟨26263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6197_26264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6197 ⟨26264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6197
    ⟨26264, by decide⟩ (by decide) (![⟨26203, by decide⟩,⟨26225, by decide⟩,⟨26242, by decide⟩,⟨26263, by decide⟩]) unmarked_context_13_6197_26264 node_context_13_6197_26264
  intro a
  fin_cases a
  · exact context_14_24788_26203
  · exact context_14_24789_26225
  · exact context_14_24790_26242
  · exact context_14_24791_26263

theorem selected_cut_00588 : selected 8 ⟨26304, by decide⟩
    (prefixPartial 13 6198) = some ⟨13, 2, 0, 26304, 6198, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_6198_26304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6198 ⟨26304, by decide⟩ :=
  accepted_of_selected 13 6198 ⟨26304, by decide⟩ ⟨13, 2, 0, 26304, 6198, 2657, 16384⟩
    (by decide) selected_cut_00588

theorem selected_cut_00589 : selected 8 ⟨26324, by decide⟩
    (prefixPartial 13 6199) = some ⟨13, 2, 0, 26324, 6199, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_6199_26324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6199 ⟨26324, by decide⟩ :=
  accepted_of_selected 13 6199 ⟨26324, by decide⟩ ⟨13, 2, 0, 26324, 6199, 1357, 16384⟩
    (by decide) selected_cut_00589

theorem unmarked_context_12_1549_26325 : frontier 9 ⟨26325, by decide⟩
    (prefixCache 12 1549) (prefixPartial 12 1549) = false := by
  decide +kernel

theorem node_context_12_1549_26325 : EJMOriginalGlobalDAGData.nodes 9 ⟨26325, by decide⟩ =
    .split (coordinate 12) (![⟨26185, by decide⟩,⟨26264, by decide⟩,⟨26304, by decide⟩,⟨26324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1549_26325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1549 ⟨26325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1549
    ⟨26325, by decide⟩ (by decide) (![⟨26185, by decide⟩,⟨26264, by decide⟩,⟨26304, by decide⟩,⟨26324, by decide⟩]) unmarked_context_12_1549_26325 node_context_12_1549_26325
  intro a
  fin_cases a
  · exact context_13_6196_26185
  · exact context_13_6197_26264
  · exact context_13_6198_26304
  · exact context_13_6199_26324

theorem selected_cut_00590 : selected 8 ⟨26386, by decide⟩
    (prefixPartial 13 6200) = some ⟨13, 2, 0, 26386, 6200, 3025, 16384⟩ := by
  decide +kernel

theorem context_13_6200_26386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6200 ⟨26386, by decide⟩ :=
  accepted_of_selected 13 6200 ⟨26386, by decide⟩ ⟨13, 2, 0, 26386, 6200, 3025, 16384⟩
    (by decide) selected_cut_00590

theorem selected_cut_00591 : selected 8 ⟨26444, by decide⟩
    (prefixPartial 13 6201) = some ⟨13, 2, 0, 26444, 6201, 4037, 16384⟩ := by
  decide +kernel

theorem context_13_6201_26444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6201 ⟨26444, by decide⟩ :=
  accepted_of_selected 13 6201 ⟨26444, by decide⟩ ⟨13, 2, 0, 26444, 6201, 4037, 16384⟩
    (by decide) selected_cut_00591

theorem selected_cut_00592 : selected 8 ⟨26473, by decide⟩
    (prefixPartial 13 6202) = some ⟨13, 2, 0, 26473, 6202, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_6202_26473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6202 ⟨26473, by decide⟩ :=
  accepted_of_selected 13 6202 ⟨26473, by decide⟩ ⟨13, 2, 0, 26473, 6202, 2289, 16384⟩
    (by decide) selected_cut_00592

theorem selected_cut_00593 : selected 8 ⟨26498, by decide⟩
    (prefixPartial 13 6203) = some ⟨13, 2, 0, 26498, 6203, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_6203_26498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6203 ⟨26498, by decide⟩ :=
  accepted_of_selected 13 6203 ⟨26498, by decide⟩ ⟨13, 2, 0, 26498, 6203, 1349, 16384⟩
    (by decide) selected_cut_00593

theorem unmarked_context_12_1550_26499 : frontier 9 ⟨26499, by decide⟩
    (prefixCache 12 1550) (prefixPartial 12 1550) = false := by
  decide +kernel

theorem node_context_12_1550_26499 : EJMOriginalGlobalDAGData.nodes 9 ⟨26499, by decide⟩ =
    .split (coordinate 12) (![⟨26386, by decide⟩,⟨26444, by decide⟩,⟨26473, by decide⟩,⟨26498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1550_26499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1550 ⟨26499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1550
    ⟨26499, by decide⟩ (by decide) (![⟨26386, by decide⟩,⟨26444, by decide⟩,⟨26473, by decide⟩,⟨26498, by decide⟩]) unmarked_context_12_1550_26499 node_context_12_1550_26499
  intro a
  fin_cases a
  · exact context_13_6200_26386
  · exact context_13_6201_26444
  · exact context_13_6202_26473
  · exact context_13_6203_26498

theorem selected_cut_00594 : selected 8 ⟨26553, by decide⟩
    (prefixPartial 13 6204) = some ⟨13, 2, 0, 26553, 6204, 3029, 16384⟩ := by
  decide +kernel

theorem context_13_6204_26553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6204 ⟨26553, by decide⟩ :=
  accepted_of_selected 13 6204 ⟨26553, by decide⟩ ⟨13, 2, 0, 26553, 6204, 3029, 16384⟩
    (by decide) selected_cut_00594

theorem selected_cut_00595 : selected 7 ⟨26571, by decide⟩
    (prefixPartial 14 24820) = some ⟨14, 2, 0, 26571, 24820, 1177, 4096⟩ := by
  decide +kernel

theorem context_14_24820_26571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24820 ⟨26571, by decide⟩ :=
  accepted_of_selected 14 24820 ⟨26571, by decide⟩ ⟨14, 2, 0, 26571, 24820, 1177, 4096⟩
    (by decide) selected_cut_00595

theorem selected_cut_00596 : selected 7 ⟨26590, by decide⟩
    (prefixPartial 14 24821) = some ⟨14, 2, 0, 26590, 24821, 1025, 4096⟩ := by
  decide +kernel

theorem context_14_24821_26590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24821 ⟨26590, by decide⟩ :=
  accepted_of_selected 14 24821 ⟨26590, by decide⟩ ⟨14, 2, 0, 26590, 24821, 1025, 4096⟩
    (by decide) selected_cut_00596

theorem selected_cut_00597 : selected 7 ⟨26607, by decide⟩
    (prefixPartial 14 24822) = some ⟨14, 2, 0, 26607, 24822, 1089, 4096⟩ := by
  decide +kernel

theorem context_14_24822_26607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24822 ⟨26607, by decide⟩ :=
  accepted_of_selected 14 24822 ⟨26607, by decide⟩ ⟨14, 2, 0, 26607, 24822, 1089, 4096⟩
    (by decide) selected_cut_00597

theorem selected_cut_00598 : selected 7 ⟨26620, by decide⟩
    (prefixPartial 14 24823) = some ⟨14, 2, 0, 26620, 24823, 893, 4096⟩ := by
  decide +kernel

theorem context_14_24823_26620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24823 ⟨26620, by decide⟩ :=
  accepted_of_selected 14 24823 ⟨26620, by decide⟩ ⟨14, 2, 0, 26620, 24823, 893, 4096⟩
    (by decide) selected_cut_00598

theorem unmarked_context_13_6205_26621 : frontier 8 ⟨26621, by decide⟩
    (prefixCache 13 6205) (prefixPartial 13 6205) = false := by
  decide +kernel

theorem node_context_13_6205_26621 : EJMOriginalGlobalDAGData.nodes 8 ⟨26621, by decide⟩ =
    .split (coordinate 13) (![⟨26571, by decide⟩,⟨26590, by decide⟩,⟨26607, by decide⟩,⟨26620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6205_26621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6205 ⟨26621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6205
    ⟨26621, by decide⟩ (by decide) (![⟨26571, by decide⟩,⟨26590, by decide⟩,⟨26607, by decide⟩,⟨26620, by decide⟩]) unmarked_context_13_6205_26621 node_context_13_6205_26621
  intro a
  fin_cases a
  · exact context_14_24820_26571
  · exact context_14_24821_26590
  · exact context_14_24822_26607
  · exact context_14_24823_26620

theorem selected_cut_00599 : selected 8 ⟨26656, by decide⟩
    (prefixPartial 13 6206) = some ⟨13, 2, 0, 26656, 6206, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_6206_26656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6206 ⟨26656, by decide⟩ :=
  accepted_of_selected 13 6206 ⟨26656, by decide⟩ ⟨13, 2, 0, 26656, 6206, 2589, 16384⟩
    (by decide) selected_cut_00599

theorem selected_cut_00600 : selected 8 ⟨26673, by decide⟩
    (prefixPartial 13 6207) = some ⟨13, 2, 0, 26673, 6207, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_6207_26673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6207 ⟨26673, by decide⟩ :=
  accepted_of_selected 13 6207 ⟨26673, by decide⟩ ⟨13, 2, 0, 26673, 6207, 1157, 16384⟩
    (by decide) selected_cut_00600

theorem unmarked_context_12_1551_26674 : frontier 9 ⟨26674, by decide⟩
    (prefixCache 12 1551) (prefixPartial 12 1551) = false := by
  decide +kernel

theorem node_context_12_1551_26674 : EJMOriginalGlobalDAGData.nodes 9 ⟨26674, by decide⟩ =
    .split (coordinate 12) (![⟨26553, by decide⟩,⟨26621, by decide⟩,⟨26656, by decide⟩,⟨26673, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1551_26674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1551 ⟨26674, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1551
    ⟨26674, by decide⟩ (by decide) (![⟨26553, by decide⟩,⟨26621, by decide⟩,⟨26656, by decide⟩,⟨26673, by decide⟩]) unmarked_context_12_1551_26674 node_context_12_1551_26674
  intro a
  fin_cases a
  · exact context_13_6204_26553
  · exact context_13_6205_26621
  · exact context_13_6206_26656
  · exact context_13_6207_26673

theorem unmarked_context_11_387_26675 : frontier 10 ⟨26675, by decide⟩
    (prefixCache 11 387) (prefixPartial 11 387) = false := by
  decide +kernel

theorem node_context_11_387_26675 : EJMOriginalGlobalDAGData.nodes 10 ⟨26675, by decide⟩ =
    .split (coordinate 11) (![⟨26107, by decide⟩,⟨26325, by decide⟩,⟨26499, by decide⟩,⟨26674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_387_26675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 387 ⟨26675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 387
    ⟨26675, by decide⟩ (by decide) (![⟨26107, by decide⟩,⟨26325, by decide⟩,⟨26499, by decide⟩,⟨26674, by decide⟩]) unmarked_context_11_387_26675 node_context_11_387_26675
  intro a
  fin_cases a
  · exact context_12_1548_26107
  · exact context_12_1549_26325
  · exact context_12_1550_26499
  · exact context_12_1551_26674

theorem unmarked_context_10_96_26676 : frontier 11 ⟨26676, by decide⟩
    (prefixCache 10 96) (prefixPartial 10 96) = false := by
  decide +kernel

theorem node_context_10_96_26676 : EJMOriginalGlobalDAGData.nodes 11 ⟨26676, by decide⟩ =
    .split (coordinate 10) (![⟨23953, by decide⟩,⟨24977, by decide⟩,⟨25818, by decide⟩,⟨26675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_96_26676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 96 ⟨26676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 96
    ⟨26676, by decide⟩ (by decide) (![⟨23953, by decide⟩,⟨24977, by decide⟩,⟨25818, by decide⟩,⟨26675, by decide⟩]) unmarked_context_10_96_26676 node_context_10_96_26676
  intro a
  fin_cases a
  · exact context_11_384_23953
  · exact context_11_385_24977
  · exact context_11_386_25818
  · exact context_11_387_26675

theorem selected_cut_00601 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1552) = some ⟨12, 1, 0, 26677, 1552, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1552_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1552 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1552 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1552, 1, 65536⟩
    (by decide) selected_cut_00601

theorem selected_cut_00602 : selected 8 ⟨26729, by decide⟩
    (prefixPartial 13 6212) = some ⟨13, 2, 0, 26729, 6212, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_6212_26729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6212 ⟨26729, by decide⟩ :=
  accepted_of_selected 13 6212 ⟨26729, by decide⟩ ⟨13, 2, 0, 26729, 6212, 1741, 16384⟩
    (by decide) selected_cut_00602

theorem selected_cut_00603 : selected 8 ⟨26761, by decide⟩
    (prefixPartial 13 6213) = some ⟨13, 2, 0, 26761, 6213, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_6213_26761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6213 ⟨26761, by decide⟩ :=
  accepted_of_selected 13 6213 ⟨26761, by decide⟩ ⟨13, 2, 0, 26761, 6213, 1557, 16384⟩
    (by decide) selected_cut_00603

theorem selected_cut_00604 : selected 8 ⟨26786, by decide⟩
    (prefixPartial 13 6214) = some ⟨13, 2, 0, 26786, 6214, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_6214_26786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6214 ⟨26786, by decide⟩ :=
  accepted_of_selected 13 6214 ⟨26786, by decide⟩ ⟨13, 2, 0, 26786, 6214, 1373, 16384⟩
    (by decide) selected_cut_00604

theorem selected_cut_00605 : selected 8 ⟨26804, by decide⟩
    (prefixPartial 13 6215) = some ⟨13, 2, 0, 26804, 6215, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_6215_26804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6215 ⟨26804, by decide⟩ :=
  accepted_of_selected 13 6215 ⟨26804, by decide⟩ ⟨13, 2, 0, 26804, 6215, 1053, 16384⟩
    (by decide) selected_cut_00605

theorem unmarked_context_12_1553_26805 : frontier 9 ⟨26805, by decide⟩
    (prefixCache 12 1553) (prefixPartial 12 1553) = false := by
  decide +kernel

theorem node_context_12_1553_26805 : EJMOriginalGlobalDAGData.nodes 9 ⟨26805, by decide⟩ =
    .split (coordinate 12) (![⟨26729, by decide⟩,⟨26761, by decide⟩,⟨26786, by decide⟩,⟨26804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1553_26805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1553 ⟨26805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1553
    ⟨26805, by decide⟩ (by decide) (![⟨26729, by decide⟩,⟨26761, by decide⟩,⟨26786, by decide⟩,⟨26804, by decide⟩]) unmarked_context_12_1553_26805 node_context_12_1553_26805
  intro a
  fin_cases a
  · exact context_13_6212_26729
  · exact context_13_6213_26761
  · exact context_13_6214_26786
  · exact context_13_6215_26804

theorem selected_cut_00606 : selected 9 ⟨26878, by decide⟩
    (prefixPartial 12 1554) = some ⟨12, 2, 0, 26878, 1554, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_1554_26878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1554 ⟨26878, by decide⟩ :=
  accepted_of_selected 12 1554 ⟨26878, by decide⟩ ⟨12, 2, 0, 26878, 1554, 2797, 65536⟩
    (by decide) selected_cut_00606

theorem selected_cut_00607 : selected 8 ⟨26918, by decide⟩
    (prefixPartial 13 6220) = some ⟨13, 2, 0, 26918, 6220, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_6220_26918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6220 ⟨26918, by decide⟩ :=
  accepted_of_selected 13 6220 ⟨26918, by decide⟩ ⟨13, 2, 0, 26918, 6220, 1685, 16384⟩
    (by decide) selected_cut_00607

theorem selected_cut_00608 : selected 8 ⟨26949, by decide⟩
    (prefixPartial 13 6221) = some ⟨13, 2, 0, 26949, 6221, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_6221_26949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6221 ⟨26949, by decide⟩ :=
  accepted_of_selected 13 6221 ⟨26949, by decide⟩ ⟨13, 2, 0, 26949, 6221, 1601, 16384⟩
    (by decide) selected_cut_00608

theorem selected_cut_00609 : selected 8 ⟨26977, by decide⟩
    (prefixPartial 13 6222) = some ⟨13, 2, 0, 26977, 6222, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_6222_26977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6222 ⟨26977, by decide⟩ :=
  accepted_of_selected 13 6222 ⟨26977, by decide⟩ ⟨13, 2, 0, 26977, 6222, 1353, 16384⟩
    (by decide) selected_cut_00609

theorem selected_cut_00610 : selected 8 ⟨26990, by decide⟩
    (prefixPartial 13 6223) = some ⟨13, 2, 0, 26990, 6223, 909, 16384⟩ := by
  decide +kernel

theorem context_13_6223_26990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6223 ⟨26990, by decide⟩ :=
  accepted_of_selected 13 6223 ⟨26990, by decide⟩ ⟨13, 2, 0, 26990, 6223, 909, 16384⟩
    (by decide) selected_cut_00610

theorem unmarked_context_12_1555_26991 : frontier 9 ⟨26991, by decide⟩
    (prefixCache 12 1555) (prefixPartial 12 1555) = false := by
  decide +kernel

theorem node_context_12_1555_26991 : EJMOriginalGlobalDAGData.nodes 9 ⟨26991, by decide⟩ =
    .split (coordinate 12) (![⟨26918, by decide⟩,⟨26949, by decide⟩,⟨26977, by decide⟩,⟨26990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1555_26991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1555 ⟨26991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1555
    ⟨26991, by decide⟩ (by decide) (![⟨26918, by decide⟩,⟨26949, by decide⟩,⟨26977, by decide⟩,⟨26990, by decide⟩]) unmarked_context_12_1555_26991 node_context_12_1555_26991
  intro a
  fin_cases a
  · exact context_13_6220_26918
  · exact context_13_6221_26949
  · exact context_13_6222_26977
  · exact context_13_6223_26990

theorem unmarked_context_11_388_26992 : frontier 10 ⟨26992, by decide⟩
    (prefixCache 11 388) (prefixPartial 11 388) = false := by
  decide +kernel

theorem node_context_11_388_26992 : EJMOriginalGlobalDAGData.nodes 10 ⟨26992, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨26805, by decide⟩,⟨26878, by decide⟩,⟨26991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_388_26992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 388 ⟨26992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 388
    ⟨26992, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨26805, by decide⟩,⟨26878, by decide⟩,⟨26991, by decide⟩]) unmarked_context_11_388_26992 node_context_11_388_26992
  intro a
  fin_cases a
  · exact context_12_1552_26677
  · exact context_12_1553_26805
  · exact context_12_1554_26878
  · exact context_12_1555_26991

theorem selected_cut_00611 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1556) = some ⟨12, 1, 0, 26677, 1556, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1556_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1556 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1556 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1556, 1, 65536⟩
    (by decide) selected_cut_00611

theorem selected_cut_00612 : selected 8 ⟨27060, by decide⟩
    (prefixPartial 13 6228) = some ⟨13, 2, 0, 27060, 6228, 2581, 16384⟩ := by
  decide +kernel

theorem context_13_6228_27060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6228 ⟨27060, by decide⟩ :=
  accepted_of_selected 13 6228 ⟨27060, by decide⟩ ⟨13, 2, 0, 27060, 6228, 2581, 16384⟩
    (by decide) selected_cut_00612

theorem selected_cut_00613 : selected 8 ⟨27112, by decide⟩
    (prefixPartial 13 6229) = some ⟨13, 2, 0, 27112, 6229, 3629, 16384⟩ := by
  decide +kernel

theorem context_13_6229_27112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6229 ⟨27112, by decide⟩ :=
  accepted_of_selected 13 6229 ⟨27112, by decide⟩ ⟨13, 2, 0, 27112, 6229, 3629, 16384⟩
    (by decide) selected_cut_00613

theorem selected_cut_00614 : selected 8 ⟨27152, by decide⟩
    (prefixPartial 13 6230) = some ⟨13, 2, 0, 27152, 6230, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_6230_27152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6230 ⟨27152, by decide⟩ :=
  accepted_of_selected 13 6230 ⟨27152, by decide⟩ ⟨13, 2, 0, 27152, 6230, 2541, 16384⟩
    (by decide) selected_cut_00614

theorem selected_cut_00615 : selected 8 ⟨27187, by decide⟩
    (prefixPartial 13 6231) = some ⟨13, 2, 0, 27187, 6231, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_6231_27187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6231 ⟨27187, by decide⟩ :=
  accepted_of_selected 13 6231 ⟨27187, by decide⟩ ⟨13, 2, 0, 27187, 6231, 1477, 16384⟩
    (by decide) selected_cut_00615

theorem unmarked_context_12_1557_27188 : frontier 9 ⟨27188, by decide⟩
    (prefixCache 12 1557) (prefixPartial 12 1557) = false := by
  decide +kernel

theorem node_context_12_1557_27188 : EJMOriginalGlobalDAGData.nodes 9 ⟨27188, by decide⟩ =
    .split (coordinate 12) (![⟨27060, by decide⟩,⟨27112, by decide⟩,⟨27152, by decide⟩,⟨27187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1557_27188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1557 ⟨27188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1557
    ⟨27188, by decide⟩ (by decide) (![⟨27060, by decide⟩,⟨27112, by decide⟩,⟨27152, by decide⟩,⟨27187, by decide⟩]) unmarked_context_12_1557_27188 node_context_12_1557_27188
  intro a
  fin_cases a
  · exact context_13_6228_27060
  · exact context_13_6229_27112
  · exact context_13_6230_27152
  · exact context_13_6231_27187

theorem selected_cut_00616 : selected 8 ⟨27235, by decide⟩
    (prefixPartial 13 6232) = some ⟨13, 2, 0, 27235, 6232, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_6232_27235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6232 ⟨27235, by decide⟩ :=
  accepted_of_selected 13 6232 ⟨27235, by decide⟩ ⟨13, 2, 0, 27235, 6232, 2125, 16384⟩
    (by decide) selected_cut_00616

theorem selected_cut_00617 : selected 8 ⟨27288, by decide⟩
    (prefixPartial 13 6233) = some ⟨13, 2, 0, 27288, 6233, 3637, 16384⟩ := by
  decide +kernel

theorem context_13_6233_27288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6233 ⟨27288, by decide⟩ :=
  accepted_of_selected 13 6233 ⟨27288, by decide⟩ ⟨13, 2, 0, 27288, 6233, 3637, 16384⟩
    (by decide) selected_cut_00617

theorem selected_cut_00618 : selected 8 ⟨27321, by decide⟩
    (prefixPartial 13 6234) = some ⟨13, 2, 0, 27321, 6234, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_6234_27321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6234 ⟨27321, by decide⟩ :=
  accepted_of_selected 13 6234 ⟨27321, by decide⟩ ⟨13, 2, 0, 27321, 6234, 2429, 16384⟩
    (by decide) selected_cut_00618

theorem selected_cut_00619 : selected 8 ⟨27356, by decide⟩
    (prefixPartial 13 6235) = some ⟨13, 2, 0, 27356, 6235, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_6235_27356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6235 ⟨27356, by decide⟩ :=
  accepted_of_selected 13 6235 ⟨27356, by decide⟩ ⟨13, 2, 0, 27356, 6235, 1529, 16384⟩
    (by decide) selected_cut_00619

theorem unmarked_context_12_1558_27357 : frontier 9 ⟨27357, by decide⟩
    (prefixCache 12 1558) (prefixPartial 12 1558) = false := by
  decide +kernel

theorem node_context_12_1558_27357 : EJMOriginalGlobalDAGData.nodes 9 ⟨27357, by decide⟩ =
    .split (coordinate 12) (![⟨27235, by decide⟩,⟨27288, by decide⟩,⟨27321, by decide⟩,⟨27356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1558_27357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1558 ⟨27357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1558
    ⟨27357, by decide⟩ (by decide) (![⟨27235, by decide⟩,⟨27288, by decide⟩,⟨27321, by decide⟩,⟨27356, by decide⟩]) unmarked_context_12_1558_27357 node_context_12_1558_27357
  intro a
  fin_cases a
  · exact context_13_6232_27235
  · exact context_13_6233_27288
  · exact context_13_6234_27321
  · exact context_13_6235_27356

theorem selected_cut_00620 : selected 8 ⟨27425, by decide⟩
    (prefixPartial 13 6236) = some ⟨13, 2, 0, 27425, 6236, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_6236_27425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6236 ⟨27425, by decide⟩ :=
  accepted_of_selected 13 6236 ⟨27425, by decide⟩ ⟨13, 2, 0, 27425, 6236, 2457, 16384⟩
    (by decide) selected_cut_00620

theorem selected_cut_00621 : selected 7 ⟨27436, by decide⟩
    (prefixPartial 14 24948) = some ⟨14, 2, 0, 27436, 24948, 1037, 4096⟩ := by
  decide +kernel

theorem context_14_24948_27436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24948 ⟨27436, by decide⟩ :=
  accepted_of_selected 14 24948 ⟨27436, by decide⟩ ⟨14, 2, 0, 27436, 24948, 1037, 4096⟩
    (by decide) selected_cut_00621

theorem selected_cut_00622 : selected 7 ⟨27451, by decide⟩
    (prefixPartial 14 24949) = some ⟨14, 2, 0, 27451, 24949, 1137, 4096⟩ := by
  decide +kernel

theorem context_14_24949_27451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24949 ⟨27451, by decide⟩ :=
  accepted_of_selected 14 24949 ⟨27451, by decide⟩ ⟨14, 2, 0, 27451, 24949, 1137, 4096⟩
    (by decide) selected_cut_00622

theorem selected_cut_00623 : selected 7 ⟨27465, by decide⟩
    (prefixPartial 14 24950) = some ⟨14, 2, 0, 27465, 24950, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_24950_27465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24950 ⟨27465, by decide⟩ :=
  accepted_of_selected 14 24950 ⟨27465, by decide⟩ ⟨14, 2, 0, 27465, 24950, 1053, 4096⟩
    (by decide) selected_cut_00623

theorem selected_cut_00624 : selected 7 ⟨27477, by decide⟩
    (prefixPartial 14 24951) = some ⟨14, 2, 0, 27477, 24951, 977, 4096⟩ := by
  decide +kernel

theorem context_14_24951_27477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 24951 ⟨27477, by decide⟩ :=
  accepted_of_selected 14 24951 ⟨27477, by decide⟩ ⟨14, 2, 0, 27477, 24951, 977, 4096⟩
    (by decide) selected_cut_00624

theorem unmarked_context_13_6237_27478 : frontier 8 ⟨27478, by decide⟩
    (prefixCache 13 6237) (prefixPartial 13 6237) = false := by
  decide +kernel

theorem node_context_13_6237_27478 : EJMOriginalGlobalDAGData.nodes 8 ⟨27478, by decide⟩ =
    .split (coordinate 13) (![⟨27436, by decide⟩,⟨27451, by decide⟩,⟨27465, by decide⟩,⟨27477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_6237_27478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6237 ⟨27478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 6237
    ⟨27478, by decide⟩ (by decide) (![⟨27436, by decide⟩,⟨27451, by decide⟩,⟨27465, by decide⟩,⟨27477, by decide⟩]) unmarked_context_13_6237_27478 node_context_13_6237_27478
  intro a
  fin_cases a
  · exact context_14_24948_27436
  · exact context_14_24949_27451
  · exact context_14_24950_27465
  · exact context_14_24951_27477

theorem selected_cut_00625 : selected 8 ⟨27534, by decide⟩
    (prefixPartial 13 6238) = some ⟨13, 2, 0, 27534, 6238, 2957, 16384⟩ := by
  decide +kernel

theorem context_13_6238_27534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6238 ⟨27534, by decide⟩ :=
  accepted_of_selected 13 6238 ⟨27534, by decide⟩ ⟨13, 2, 0, 27534, 6238, 2957, 16384⟩
    (by decide) selected_cut_00625

theorem selected_cut_00626 : selected 8 ⟨27561, by decide⟩
    (prefixPartial 13 6239) = some ⟨13, 2, 0, 27561, 6239, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_6239_27561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6239 ⟨27561, by decide⟩ :=
  accepted_of_selected 13 6239 ⟨27561, by decide⟩ ⟨13, 2, 0, 27561, 6239, 1449, 16384⟩
    (by decide) selected_cut_00626

theorem unmarked_context_12_1559_27562 : frontier 9 ⟨27562, by decide⟩
    (prefixCache 12 1559) (prefixPartial 12 1559) = false := by
  decide +kernel

theorem node_context_12_1559_27562 : EJMOriginalGlobalDAGData.nodes 9 ⟨27562, by decide⟩ =
    .split (coordinate 12) (![⟨27425, by decide⟩,⟨27478, by decide⟩,⟨27534, by decide⟩,⟨27561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1559_27562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1559 ⟨27562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1559
    ⟨27562, by decide⟩ (by decide) (![⟨27425, by decide⟩,⟨27478, by decide⟩,⟨27534, by decide⟩,⟨27561, by decide⟩]) unmarked_context_12_1559_27562 node_context_12_1559_27562
  intro a
  fin_cases a
  · exact context_13_6236_27425
  · exact context_13_6237_27478
  · exact context_13_6238_27534
  · exact context_13_6239_27561

theorem unmarked_context_11_389_27563 : frontier 10 ⟨27563, by decide⟩
    (prefixCache 11 389) (prefixPartial 11 389) = false := by
  decide +kernel

theorem node_context_11_389_27563 : EJMOriginalGlobalDAGData.nodes 10 ⟨27563, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨27188, by decide⟩,⟨27357, by decide⟩,⟨27562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_389_27563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 389 ⟨27563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 389
    ⟨27563, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨27188, by decide⟩,⟨27357, by decide⟩,⟨27562, by decide⟩]) unmarked_context_11_389_27563 node_context_11_389_27563
  intro a
  fin_cases a
  · exact context_12_1556_26677
  · exact context_12_1557_27188
  · exact context_12_1558_27357
  · exact context_12_1559_27562

theorem selected_cut_00627 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1560) = some ⟨12, 1, 0, 26677, 1560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1560_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1560 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1560 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1560, 1, 65536⟩
    (by decide) selected_cut_00627

theorem selected_cut_00628 : selected 8 ⟨27600, by decide⟩
    (prefixPartial 13 6244) = some ⟨13, 2, 0, 27600, 6244, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_6244_27600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6244 ⟨27600, by decide⟩ :=
  accepted_of_selected 13 6244 ⟨27600, by decide⟩ ⟨13, 2, 0, 27600, 6244, 1417, 16384⟩
    (by decide) selected_cut_00628

theorem selected_cut_00629 : selected 8 ⟨27644, by decide⟩
    (prefixPartial 13 6245) = some ⟨13, 2, 0, 27644, 6245, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_6245_27644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6245 ⟨27644, by decide⟩ :=
  accepted_of_selected 13 6245 ⟨27644, by decide⟩ ⟨13, 2, 0, 27644, 6245, 2381, 16384⟩
    (by decide) selected_cut_00629

theorem selected_cut_00630 : selected 8 ⟨27672, by decide⟩
    (prefixPartial 13 6246) = some ⟨13, 2, 0, 27672, 6246, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_6246_27672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6246 ⟨27672, by decide⟩ :=
  accepted_of_selected 13 6246 ⟨27672, by decide⟩ ⟨13, 2, 0, 27672, 6246, 2205, 16384⟩
    (by decide) selected_cut_00630

theorem selected_cut_00631 : selected 8 ⟨27691, by decide⟩
    (prefixPartial 13 6247) = some ⟨13, 2, 0, 27691, 6247, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_6247_27691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6247 ⟨27691, by decide⟩ :=
  accepted_of_selected 13 6247 ⟨27691, by decide⟩ ⟨13, 2, 0, 27691, 6247, 1253, 16384⟩
    (by decide) selected_cut_00631

theorem unmarked_context_12_1561_27692 : frontier 9 ⟨27692, by decide⟩
    (prefixCache 12 1561) (prefixPartial 12 1561) = false := by
  decide +kernel

theorem node_context_12_1561_27692 : EJMOriginalGlobalDAGData.nodes 9 ⟨27692, by decide⟩ =
    .split (coordinate 12) (![⟨27600, by decide⟩,⟨27644, by decide⟩,⟨27672, by decide⟩,⟨27691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1561_27692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1561 ⟨27692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1561
    ⟨27692, by decide⟩ (by decide) (![⟨27600, by decide⟩,⟨27644, by decide⟩,⟨27672, by decide⟩,⟨27691, by decide⟩]) unmarked_context_12_1561_27692 node_context_12_1561_27692
  intro a
  fin_cases a
  · exact context_13_6244_27600
  · exact context_13_6245_27644
  · exact context_13_6246_27672
  · exact context_13_6247_27691

theorem selected_cut_00632 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 1562) = some ⟨12, 1, 0, 3161, 1562, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1562_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1562 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 1562 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 1562, 1, 65536⟩
    (by decide) selected_cut_00632

theorem selected_cut_00633 : selected 8 ⟨27724, by decide⟩
    (prefixPartial 13 6252) = some ⟨13, 2, 0, 27724, 6252, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_6252_27724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6252 ⟨27724, by decide⟩ :=
  accepted_of_selected 13 6252 ⟨27724, by decide⟩ ⟨13, 2, 0, 27724, 6252, 1345, 16384⟩
    (by decide) selected_cut_00633

theorem selected_cut_00634 : selected 8 ⟨27772, by decide⟩
    (prefixPartial 13 6253) = some ⟨13, 2, 0, 27772, 6253, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_6253_27772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6253 ⟨27772, by decide⟩ :=
  accepted_of_selected 13 6253 ⟨27772, by decide⟩ ⟨13, 2, 0, 27772, 6253, 2657, 16384⟩
    (by decide) selected_cut_00634

theorem selected_cut_00635 : selected 8 ⟨27806, by decide⟩
    (prefixPartial 13 6254) = some ⟨13, 2, 0, 27806, 6254, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_6254_27806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6254 ⟨27806, by decide⟩ :=
  accepted_of_selected 13 6254 ⟨27806, by decide⟩ ⟨13, 2, 0, 27806, 6254, 2109, 16384⟩
    (by decide) selected_cut_00635

theorem selected_cut_00636 : selected 8 ⟨27823, by decide⟩
    (prefixPartial 13 6255) = some ⟨13, 2, 0, 27823, 6255, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_6255_27823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6255 ⟨27823, by decide⟩ :=
  accepted_of_selected 13 6255 ⟨27823, by decide⟩ ⟨13, 2, 0, 27823, 6255, 1089, 16384⟩
    (by decide) selected_cut_00636

theorem unmarked_context_12_1563_27824 : frontier 9 ⟨27824, by decide⟩
    (prefixCache 12 1563) (prefixPartial 12 1563) = false := by
  decide +kernel

theorem node_context_12_1563_27824 : EJMOriginalGlobalDAGData.nodes 9 ⟨27824, by decide⟩ =
    .split (coordinate 12) (![⟨27724, by decide⟩,⟨27772, by decide⟩,⟨27806, by decide⟩,⟨27823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1563_27824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1563 ⟨27824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1563
    ⟨27824, by decide⟩ (by decide) (![⟨27724, by decide⟩,⟨27772, by decide⟩,⟨27806, by decide⟩,⟨27823, by decide⟩]) unmarked_context_12_1563_27824 node_context_12_1563_27824
  intro a
  fin_cases a
  · exact context_13_6252_27724
  · exact context_13_6253_27772
  · exact context_13_6254_27806
  · exact context_13_6255_27823

theorem unmarked_context_11_390_27825 : frontier 10 ⟨27825, by decide⟩
    (prefixCache 11 390) (prefixPartial 11 390) = false := by
  decide +kernel

theorem node_context_11_390_27825 : EJMOriginalGlobalDAGData.nodes 10 ⟨27825, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨27692, by decide⟩,⟨3161, by decide⟩,⟨27824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_390_27825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 390 ⟨27825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 390
    ⟨27825, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨27692, by decide⟩,⟨3161, by decide⟩,⟨27824, by decide⟩]) unmarked_context_11_390_27825 node_context_11_390_27825
  intro a
  fin_cases a
  · exact context_12_1560_26677
  · exact context_12_1561_27692
  · exact context_12_1562_3161
  · exact context_12_1563_27824

theorem selected_cut_00637 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1564) = some ⟨12, 1, 0, 26677, 1564, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1564_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1564 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1564 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1564, 1, 65536⟩
    (by decide) selected_cut_00637

theorem selected_cut_00638 : selected 8 ⟨27854, by decide⟩
    (prefixPartial 13 6260) = some ⟨13, 2, 0, 27854, 6260, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_6260_27854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6260 ⟨27854, by decide⟩ :=
  accepted_of_selected 13 6260 ⟨27854, by decide⟩ ⟨13, 2, 0, 27854, 6260, 1257, 16384⟩
    (by decide) selected_cut_00638

theorem selected_cut_00639 : selected 8 ⟨27912, by decide⟩
    (prefixPartial 13 6261) = some ⟨13, 2, 0, 27912, 6261, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_6261_27912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6261 ⟨27912, by decide⟩ :=
  accepted_of_selected 13 6261 ⟨27912, by decide⟩ ⟨13, 2, 0, 27912, 6261, 2933, 16384⟩
    (by decide) selected_cut_00639

theorem selected_cut_00640 : selected 8 ⟨27946, by decide⟩
    (prefixPartial 13 6262) = some ⟨13, 2, 0, 27946, 6262, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_6262_27946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6262 ⟨27946, by decide⟩ :=
  accepted_of_selected 13 6262 ⟨27946, by decide⟩ ⟨13, 2, 0, 27946, 6262, 2361, 16384⟩
    (by decide) selected_cut_00640

theorem selected_cut_00641 : selected 8 ⟨27960, by decide⟩
    (prefixPartial 13 6263) = some ⟨13, 2, 0, 27960, 6263, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_6263_27960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6263 ⟨27960, by decide⟩ :=
  accepted_of_selected 13 6263 ⟨27960, by decide⟩ ⟨13, 2, 0, 27960, 6263, 1201, 16384⟩
    (by decide) selected_cut_00641

theorem unmarked_context_12_1565_27961 : frontier 9 ⟨27961, by decide⟩
    (prefixCache 12 1565) (prefixPartial 12 1565) = false := by
  decide +kernel

theorem node_context_12_1565_27961 : EJMOriginalGlobalDAGData.nodes 9 ⟨27961, by decide⟩ =
    .split (coordinate 12) (![⟨27854, by decide⟩,⟨27912, by decide⟩,⟨27946, by decide⟩,⟨27960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1565_27961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1565 ⟨27961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1565
    ⟨27961, by decide⟩ (by decide) (![⟨27854, by decide⟩,⟨27912, by decide⟩,⟨27946, by decide⟩,⟨27960, by decide⟩]) unmarked_context_12_1565_27961 node_context_12_1565_27961
  intro a
  fin_cases a
  · exact context_13_6260_27854
  · exact context_13_6261_27912
  · exact context_13_6262_27946
  · exact context_13_6263_27960

theorem selected_cut_00642 : selected 8 ⟨27980, by decide⟩
    (prefixPartial 13 6264) = some ⟨13, 2, 0, 27980, 6264, 589, 16384⟩ := by
  decide +kernel

theorem context_13_6264_27980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6264 ⟨27980, by decide⟩ :=
  accepted_of_selected 13 6264 ⟨27980, by decide⟩ ⟨13, 2, 0, 27980, 6264, 589, 16384⟩
    (by decide) selected_cut_00642

theorem selected_cut_00643 : selected 8 ⟨28034, by decide⟩
    (prefixPartial 13 6265) = some ⟨13, 2, 0, 28034, 6265, 2789, 16384⟩ := by
  decide +kernel

theorem context_13_6265_28034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6265 ⟨28034, by decide⟩ :=
  accepted_of_selected 13 6265 ⟨28034, by decide⟩ ⟨13, 2, 0, 28034, 6265, 2789, 16384⟩
    (by decide) selected_cut_00643

theorem selected_cut_00644 : selected 8 ⟨1982, by decide⟩
    (prefixPartial 13 6266) = some ⟨13, 1, 0, 1982, 6266, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6266_1982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6266 ⟨1982, by decide⟩ :=
  accepted_of_selected 13 6266 ⟨1982, by decide⟩ ⟨13, 1, 0, 1982, 6266, 1, 16384⟩
    (by decide) selected_cut_00644

theorem selected_cut_00645 : selected 8 ⟨28055, by decide⟩
    (prefixPartial 13 6267) = some ⟨13, 2, 0, 28055, 6267, 749, 16384⟩ := by
  decide +kernel

theorem context_13_6267_28055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6267 ⟨28055, by decide⟩ :=
  accepted_of_selected 13 6267 ⟨28055, by decide⟩ ⟨13, 2, 0, 28055, 6267, 749, 16384⟩
    (by decide) selected_cut_00645

theorem unmarked_context_12_1566_28056 : frontier 9 ⟨28056, by decide⟩
    (prefixCache 12 1566) (prefixPartial 12 1566) = false := by
  decide +kernel

theorem node_context_12_1566_28056 : EJMOriginalGlobalDAGData.nodes 9 ⟨28056, by decide⟩ =
    .split (coordinate 12) (![⟨27980, by decide⟩,⟨28034, by decide⟩,⟨1982, by decide⟩,⟨28055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1566_28056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1566 ⟨28056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1566
    ⟨28056, by decide⟩ (by decide) (![⟨27980, by decide⟩,⟨28034, by decide⟩,⟨1982, by decide⟩,⟨28055, by decide⟩]) unmarked_context_12_1566_28056 node_context_12_1566_28056
  intro a
  fin_cases a
  · exact context_13_6264_27980
  · exact context_13_6265_28034
  · exact context_13_6266_1982
  · exact context_13_6267_28055

theorem selected_cut_00646 : selected 8 ⟨28084, by decide⟩
    (prefixPartial 13 6268) = some ⟨13, 2, 0, 28084, 6268, 977, 16384⟩ := by
  decide +kernel

theorem context_13_6268_28084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6268 ⟨28084, by decide⟩ :=
  accepted_of_selected 13 6268 ⟨28084, by decide⟩ ⟨13, 2, 0, 28084, 6268, 977, 16384⟩
    (by decide) selected_cut_00646

theorem selected_cut_00647 : selected 8 ⟨28130, by decide⟩
    (prefixPartial 13 6269) = some ⟨13, 2, 0, 28130, 6269, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_6269_28130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6269 ⟨28130, by decide⟩ :=
  accepted_of_selected 13 6269 ⟨28130, by decide⟩ ⟨13, 2, 0, 28130, 6269, 2561, 16384⟩
    (by decide) selected_cut_00647

theorem selected_cut_00648 : selected 8 ⟨28158, by decide⟩
    (prefixPartial 13 6270) = some ⟨13, 2, 0, 28158, 6270, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_6270_28158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6270 ⟨28158, by decide⟩ :=
  accepted_of_selected 13 6270 ⟨28158, by decide⟩ ⟨13, 2, 0, 28158, 6270, 2093, 16384⟩
    (by decide) selected_cut_00648

theorem selected_cut_00649 : selected 8 ⟨28169, by decide⟩
    (prefixPartial 13 6271) = some ⟨13, 2, 0, 28169, 6271, 969, 16384⟩ := by
  decide +kernel

theorem context_13_6271_28169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6271 ⟨28169, by decide⟩ :=
  accepted_of_selected 13 6271 ⟨28169, by decide⟩ ⟨13, 2, 0, 28169, 6271, 969, 16384⟩
    (by decide) selected_cut_00649

theorem unmarked_context_12_1567_28170 : frontier 9 ⟨28170, by decide⟩
    (prefixCache 12 1567) (prefixPartial 12 1567) = false := by
  decide +kernel

theorem node_context_12_1567_28170 : EJMOriginalGlobalDAGData.nodes 9 ⟨28170, by decide⟩ =
    .split (coordinate 12) (![⟨28084, by decide⟩,⟨28130, by decide⟩,⟨28158, by decide⟩,⟨28169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1567_28170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1567 ⟨28170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1567
    ⟨28170, by decide⟩ (by decide) (![⟨28084, by decide⟩,⟨28130, by decide⟩,⟨28158, by decide⟩,⟨28169, by decide⟩]) unmarked_context_12_1567_28170 node_context_12_1567_28170
  intro a
  fin_cases a
  · exact context_13_6268_28084
  · exact context_13_6269_28130
  · exact context_13_6270_28158
  · exact context_13_6271_28169

theorem unmarked_context_11_391_28171 : frontier 10 ⟨28171, by decide⟩
    (prefixCache 11 391) (prefixPartial 11 391) = false := by
  decide +kernel

theorem node_context_11_391_28171 : EJMOriginalGlobalDAGData.nodes 10 ⟨28171, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨27961, by decide⟩,⟨28056, by decide⟩,⟨28170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_391_28171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 391 ⟨28171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 391
    ⟨28171, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨27961, by decide⟩,⟨28056, by decide⟩,⟨28170, by decide⟩]) unmarked_context_11_391_28171 node_context_11_391_28171
  intro a
  fin_cases a
  · exact context_12_1564_26677
  · exact context_12_1565_27961
  · exact context_12_1566_28056
  · exact context_12_1567_28170

theorem unmarked_context_10_97_28172 : frontier 11 ⟨28172, by decide⟩
    (prefixCache 10 97) (prefixPartial 10 97) = false := by
  decide +kernel

theorem node_context_10_97_28172 : EJMOriginalGlobalDAGData.nodes 11 ⟨28172, by decide⟩ =
    .split (coordinate 10) (![⟨26992, by decide⟩,⟨27563, by decide⟩,⟨27825, by decide⟩,⟨28171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_97_28172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 97 ⟨28172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 97
    ⟨28172, by decide⟩ (by decide) (![⟨26992, by decide⟩,⟨27563, by decide⟩,⟨27825, by decide⟩,⟨28171, by decide⟩]) unmarked_context_10_97_28172 node_context_10_97_28172
  intro a
  fin_cases a
  · exact context_11_388_26992
  · exact context_11_389_27563
  · exact context_11_390_27825
  · exact context_11_391_28171

theorem selected_cut_00650 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1568) = some ⟨12, 1, 0, 26677, 1568, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1568_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1568 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1568 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1568, 1, 65536⟩
    (by decide) selected_cut_00650

theorem selected_cut_00651 : selected 9 ⟨28241, by decide⟩
    (prefixPartial 12 1569) = some ⟨12, 2, 0, 28241, 1569, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_1569_28241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1569 ⟨28241, by decide⟩ :=
  accepted_of_selected 12 1569 ⟨28241, by decide⟩ ⟨12, 2, 0, 28241, 1569, 2961, 65536⟩
    (by decide) selected_cut_00651

theorem selected_cut_00652 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1570) = some ⟨12, 1, 0, 26677, 1570, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1570_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1570 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1570 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1570, 1, 65536⟩
    (by decide) selected_cut_00652

theorem selected_cut_00653 : selected 8 ⟨28261, by decide⟩
    (prefixPartial 13 6284) = some ⟨13, 2, 0, 28261, 6284, 765, 16384⟩ := by
  decide +kernel

theorem context_13_6284_28261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6284 ⟨28261, by decide⟩ :=
  accepted_of_selected 13 6284 ⟨28261, by decide⟩ ⟨13, 2, 0, 28261, 6284, 765, 16384⟩
    (by decide) selected_cut_00653

theorem selected_cut_00654 : selected 8 ⟨28296, by decide⟩
    (prefixPartial 13 6285) = some ⟨13, 2, 0, 28296, 6285, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_6285_28296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6285 ⟨28296, by decide⟩ :=
  accepted_of_selected 13 6285 ⟨28296, by decide⟩ ⟨13, 2, 0, 28296, 6285, 1977, 16384⟩
    (by decide) selected_cut_00654

theorem selected_cut_00655 : selected 8 ⟨28322, by decide⟩
    (prefixPartial 13 6286) = some ⟨13, 2, 0, 28322, 6286, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_6286_28322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6286 ⟨28322, by decide⟩ :=
  accepted_of_selected 13 6286 ⟨28322, by decide⟩ ⟨13, 2, 0, 28322, 6286, 1441, 16384⟩
    (by decide) selected_cut_00655

theorem selected_cut_00656 : selected 8 ⟨28338, by decide⟩
    (prefixPartial 13 6287) = some ⟨13, 2, 0, 28338, 6287, 901, 16384⟩ := by
  decide +kernel

theorem context_13_6287_28338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6287 ⟨28338, by decide⟩ :=
  accepted_of_selected 13 6287 ⟨28338, by decide⟩ ⟨13, 2, 0, 28338, 6287, 901, 16384⟩
    (by decide) selected_cut_00656

theorem unmarked_context_12_1571_28339 : frontier 9 ⟨28339, by decide⟩
    (prefixCache 12 1571) (prefixPartial 12 1571) = false := by
  decide +kernel

theorem node_context_12_1571_28339 : EJMOriginalGlobalDAGData.nodes 9 ⟨28339, by decide⟩ =
    .split (coordinate 12) (![⟨28261, by decide⟩,⟨28296, by decide⟩,⟨28322, by decide⟩,⟨28338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1571_28339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1571 ⟨28339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1571
    ⟨28339, by decide⟩ (by decide) (![⟨28261, by decide⟩,⟨28296, by decide⟩,⟨28322, by decide⟩,⟨28338, by decide⟩]) unmarked_context_12_1571_28339 node_context_12_1571_28339
  intro a
  fin_cases a
  · exact context_13_6284_28261
  · exact context_13_6285_28296
  · exact context_13_6286_28322
  · exact context_13_6287_28338

theorem unmarked_context_11_392_28340 : frontier 10 ⟨28340, by decide⟩
    (prefixCache 11 392) (prefixPartial 11 392) = false := by
  decide +kernel

theorem node_context_11_392_28340 : EJMOriginalGlobalDAGData.nodes 10 ⟨28340, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨28241, by decide⟩,⟨26677, by decide⟩,⟨28339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_392_28340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 392 ⟨28340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 392
    ⟨28340, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨28241, by decide⟩,⟨26677, by decide⟩,⟨28339, by decide⟩]) unmarked_context_11_392_28340 node_context_11_392_28340
  intro a
  fin_cases a
  · exact context_12_1568_26677
  · exact context_12_1569_28241
  · exact context_12_1570_26677
  · exact context_12_1571_28339

theorem selected_cut_00657 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1572) = some ⟨12, 1, 0, 26677, 1572, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1572_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1572 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1572 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1572, 1, 65536⟩
    (by decide) selected_cut_00657

theorem selected_cut_00658 : selected 8 ⟨28363, by decide⟩
    (prefixPartial 13 6292) = some ⟨13, 2, 0, 28363, 6292, 625, 16384⟩ := by
  decide +kernel

theorem context_13_6292_28363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6292 ⟨28363, by decide⟩ :=
  accepted_of_selected 13 6292 ⟨28363, by decide⟩ ⟨13, 2, 0, 28363, 6292, 625, 16384⟩
    (by decide) selected_cut_00658

theorem selected_cut_00659 : selected 8 ⟨28399, by decide⟩
    (prefixPartial 13 6293) = some ⟨13, 2, 0, 28399, 6293, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_6293_28399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6293 ⟨28399, by decide⟩ :=
  accepted_of_selected 13 6293 ⟨28399, by decide⟩ ⟨13, 2, 0, 28399, 6293, 2337, 16384⟩
    (by decide) selected_cut_00659

theorem selected_cut_00660 : selected 8 ⟨28421, by decide⟩
    (prefixPartial 13 6294) = some ⟨13, 2, 0, 28421, 6294, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_6294_28421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6294 ⟨28421, by decide⟩ :=
  accepted_of_selected 13 6294 ⟨28421, by decide⟩ ⟨13, 2, 0, 28421, 6294, 1609, 16384⟩
    (by decide) selected_cut_00660

theorem selected_cut_00661 : selected 8 ⟨28437, by decide⟩
    (prefixPartial 13 6295) = some ⟨13, 2, 0, 28437, 6295, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_6295_28437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6295 ⟨28437, by decide⟩ :=
  accepted_of_selected 13 6295 ⟨28437, by decide⟩ ⟨13, 2, 0, 28437, 6295, 1021, 16384⟩
    (by decide) selected_cut_00661

theorem unmarked_context_12_1573_28438 : frontier 9 ⟨28438, by decide⟩
    (prefixCache 12 1573) (prefixPartial 12 1573) = false := by
  decide +kernel

theorem node_context_12_1573_28438 : EJMOriginalGlobalDAGData.nodes 9 ⟨28438, by decide⟩ =
    .split (coordinate 12) (![⟨28363, by decide⟩,⟨28399, by decide⟩,⟨28421, by decide⟩,⟨28437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1573_28438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1573 ⟨28438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1573
    ⟨28438, by decide⟩ (by decide) (![⟨28363, by decide⟩,⟨28399, by decide⟩,⟨28421, by decide⟩,⟨28437, by decide⟩]) unmarked_context_12_1573_28438 node_context_12_1573_28438
  intro a
  fin_cases a
  · exact context_13_6292_28363
  · exact context_13_6293_28399
  · exact context_13_6294_28421
  · exact context_13_6295_28437

theorem selected_cut_00662 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1574) = some ⟨12, 1, 0, 26677, 1574, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1574_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1574 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1574 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1574, 1, 65536⟩
    (by decide) selected_cut_00662

theorem selected_cut_00663 : selected 8 ⟨28460, by decide⟩
    (prefixPartial 13 6300) = some ⟨13, 2, 0, 28460, 6300, 685, 16384⟩ := by
  decide +kernel

theorem context_13_6300_28460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6300 ⟨28460, by decide⟩ :=
  accepted_of_selected 13 6300 ⟨28460, by decide⟩ ⟨13, 2, 0, 28460, 6300, 685, 16384⟩
    (by decide) selected_cut_00663

theorem selected_cut_00664 : selected 8 ⟨28508, by decide⟩
    (prefixPartial 13 6301) = some ⟨13, 2, 0, 28508, 6301, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_6301_28508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6301 ⟨28508, by decide⟩ :=
  accepted_of_selected 13 6301 ⟨28508, by decide⟩ ⟨13, 2, 0, 28508, 6301, 2761, 16384⟩
    (by decide) selected_cut_00664

theorem selected_cut_00665 : selected 8 ⟨28539, by decide⟩
    (prefixPartial 13 6302) = some ⟨13, 2, 0, 28539, 6302, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_6302_28539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6302 ⟨28539, by decide⟩ :=
  accepted_of_selected 13 6302 ⟨28539, by decide⟩ ⟨13, 2, 0, 28539, 6302, 2025, 16384⟩
    (by decide) selected_cut_00665

theorem selected_cut_00666 : selected 8 ⟨28553, by decide⟩
    (prefixPartial 13 6303) = some ⟨13, 2, 0, 28553, 6303, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_6303_28553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6303 ⟨28553, by decide⟩ :=
  accepted_of_selected 13 6303 ⟨28553, by decide⟩ ⟨13, 2, 0, 28553, 6303, 1009, 16384⟩
    (by decide) selected_cut_00666

theorem unmarked_context_12_1575_28554 : frontier 9 ⟨28554, by decide⟩
    (prefixCache 12 1575) (prefixPartial 12 1575) = false := by
  decide +kernel

theorem node_context_12_1575_28554 : EJMOriginalGlobalDAGData.nodes 9 ⟨28554, by decide⟩ =
    .split (coordinate 12) (![⟨28460, by decide⟩,⟨28508, by decide⟩,⟨28539, by decide⟩,⟨28553, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1575_28554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1575 ⟨28554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1575
    ⟨28554, by decide⟩ (by decide) (![⟨28460, by decide⟩,⟨28508, by decide⟩,⟨28539, by decide⟩,⟨28553, by decide⟩]) unmarked_context_12_1575_28554 node_context_12_1575_28554
  intro a
  fin_cases a
  · exact context_13_6300_28460
  · exact context_13_6301_28508
  · exact context_13_6302_28539
  · exact context_13_6303_28553

theorem unmarked_context_11_393_28555 : frontier 10 ⟨28555, by decide⟩
    (prefixCache 11 393) (prefixPartial 11 393) = false := by
  decide +kernel

theorem node_context_11_393_28555 : EJMOriginalGlobalDAGData.nodes 10 ⟨28555, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨28438, by decide⟩,⟨26677, by decide⟩,⟨28554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_393_28555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 393 ⟨28555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 393
    ⟨28555, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨28438, by decide⟩,⟨26677, by decide⟩,⟨28554, by decide⟩]) unmarked_context_11_393_28555 node_context_11_393_28555
  intro a
  fin_cases a
  · exact context_12_1572_26677
  · exact context_12_1573_28438
  · exact context_12_1574_26677
  · exact context_12_1575_28554

theorem selected_cut_00667 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1576) = some ⟨12, 1, 0, 26677, 1576, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1576_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1576 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1576 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1576, 1, 65536⟩
    (by decide) selected_cut_00667

theorem selected_cut_00668 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 1577) = some ⟨12, 1, 0, 3161, 1577, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1577_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1577 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 1577 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 1577, 1, 65536⟩
    (by decide) selected_cut_00668

theorem selected_cut_00669 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 1578) = some ⟨12, 1, 0, 26677, 1578, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1578_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1578 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 1578 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 1578, 1, 65536⟩
    (by decide) selected_cut_00669

theorem selected_cut_00670 : selected 8 ⟨28572, by decide⟩
    (prefixPartial 13 6316) = some ⟨13, 2, 0, 28572, 6316, 473, 16384⟩ := by
  decide +kernel

theorem context_13_6316_28572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6316 ⟨28572, by decide⟩ :=
  accepted_of_selected 13 6316 ⟨28572, by decide⟩ ⟨13, 2, 0, 28572, 6316, 473, 16384⟩
    (by decide) selected_cut_00670

theorem selected_cut_00671 : selected 8 ⟨28614, by decide⟩
    (prefixPartial 13 6317) = some ⟨13, 2, 0, 28614, 6317, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_6317_28614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6317 ⟨28614, by decide⟩ :=
  accepted_of_selected 13 6317 ⟨28614, by decide⟩ ⟨13, 2, 0, 28614, 6317, 2493, 16384⟩
    (by decide) selected_cut_00671

theorem selected_cut_00672 : selected 8 ⟨28641, by decide⟩
    (prefixPartial 13 6318) = some ⟨13, 2, 0, 28641, 6318, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_6318_28641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6318 ⟨28641, by decide⟩ :=
  accepted_of_selected 13 6318 ⟨28641, by decide⟩ ⟨13, 2, 0, 28641, 6318, 1753, 16384⟩
    (by decide) selected_cut_00672

theorem selected_cut_00673 : selected 8 ⟨28653, by decide⟩
    (prefixPartial 13 6319) = some ⟨13, 2, 0, 28653, 6319, 889, 16384⟩ := by
  decide +kernel

theorem context_13_6319_28653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6319 ⟨28653, by decide⟩ :=
  accepted_of_selected 13 6319 ⟨28653, by decide⟩ ⟨13, 2, 0, 28653, 6319, 889, 16384⟩
    (by decide) selected_cut_00673

theorem unmarked_context_12_1579_28654 : frontier 9 ⟨28654, by decide⟩
    (prefixCache 12 1579) (prefixPartial 12 1579) = false := by
  decide +kernel

theorem node_context_12_1579_28654 : EJMOriginalGlobalDAGData.nodes 9 ⟨28654, by decide⟩ =
    .split (coordinate 12) (![⟨28572, by decide⟩,⟨28614, by decide⟩,⟨28641, by decide⟩,⟨28653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1579_28654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1579 ⟨28654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1579
    ⟨28654, by decide⟩ (by decide) (![⟨28572, by decide⟩,⟨28614, by decide⟩,⟨28641, by decide⟩,⟨28653, by decide⟩]) unmarked_context_12_1579_28654 node_context_12_1579_28654
  intro a
  fin_cases a
  · exact context_13_6316_28572
  · exact context_13_6317_28614
  · exact context_13_6318_28641
  · exact context_13_6319_28653

theorem unmarked_context_11_394_28655 : frontier 10 ⟨28655, by decide⟩
    (prefixCache 11 394) (prefixPartial 11 394) = false := by
  decide +kernel

theorem node_context_11_394_28655 : EJMOriginalGlobalDAGData.nodes 10 ⟨28655, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨3161, by decide⟩,⟨26677, by decide⟩,⟨28654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_394_28655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 394 ⟨28655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 394
    ⟨28655, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨3161, by decide⟩,⟨26677, by decide⟩,⟨28654, by decide⟩]) unmarked_context_11_394_28655 node_context_11_394_28655
  intro a
  fin_cases a
  · exact context_12_1576_26677
  · exact context_12_1577_3161
  · exact context_12_1578_26677
  · exact context_12_1579_28654

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
