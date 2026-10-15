/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover276
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_26596 : selected 8 ⟨672432, by decide⟩
    (prefixPartial 13 355576) = some ⟨13, 2, 0, 672432, 355576, 53, 16384⟩ := by
  decide +kernel

theorem context_13_355576_672432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355576 ⟨672432, by decide⟩ :=
  accepted_of_selected 13 355576 ⟨672432, by decide⟩ ⟨13, 2, 0, 672432, 355576, 53, 16384⟩
    (by decide) selected_cut_26596

theorem selected_cut_26597 : selected 8 ⟨672460, by decide⟩
    (prefixPartial 13 355577) = some ⟨13, 2, 0, 672460, 355577, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_355577_672460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355577 ⟨672460, by decide⟩ :=
  accepted_of_selected 13 355577 ⟨672460, by decide⟩ ⟨13, 2, 0, 672460, 355577, 2285, 16384⟩
    (by decide) selected_cut_26597

theorem selected_cut_26598 : selected 8 ⟨672478, by decide⟩
    (prefixPartial 13 355578) = some ⟨13, 2, 0, 672478, 355578, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_355578_672478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355578 ⟨672478, by decide⟩ :=
  accepted_of_selected 13 355578 ⟨672478, by decide⟩ ⟨13, 2, 0, 672478, 355578, 1601, 16384⟩
    (by decide) selected_cut_26598

theorem selected_cut_26599 : selected 8 ⟨672483, by decide⟩
    (prefixPartial 13 355579) = some ⟨13, 2, 0, 672483, 355579, 805, 16384⟩ := by
  decide +kernel

theorem context_13_355579_672483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355579 ⟨672483, by decide⟩ :=
  accepted_of_selected 13 355579 ⟨672483, by decide⟩ ⟨13, 2, 0, 672483, 355579, 805, 16384⟩
    (by decide) selected_cut_26599

theorem unmarked_context_12_88894_672484 : frontier 9 ⟨672484, by decide⟩
    (prefixCache 12 88894) (prefixPartial 12 88894) = false := by
  decide +kernel

theorem node_context_12_88894_672484 : EJMOriginalGlobalDAGData.nodes 9 ⟨672484, by decide⟩ =
    .split (coordinate 12) (![⟨672432, by decide⟩,⟨672460, by decide⟩,⟨672478, by decide⟩,⟨672483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88894_672484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88894 ⟨672484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88894
    ⟨672484, by decide⟩ (by decide) (![⟨672432, by decide⟩,⟨672460, by decide⟩,⟨672478, by decide⟩,⟨672483, by decide⟩]) unmarked_context_12_88894_672484 node_context_12_88894_672484
  intro a
  fin_cases a
  · exact context_13_355576_672432
  · exact context_13_355577_672460
  · exact context_13_355578_672478
  · exact context_13_355579_672483

theorem selected_cut_26600 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 88895) = some ⟨12, 1, 0, 512556, 88895, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88895_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88895 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 88895 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 88895, 1, 65536⟩
    (by decide) selected_cut_26600

theorem unmarked_context_11_22223_672485 : frontier 10 ⟨672485, by decide⟩
    (prefixCache 11 22223) (prefixPartial 11 22223) = false := by
  decide +kernel

theorem node_context_11_22223_672485 : EJMOriginalGlobalDAGData.nodes 10 ⟨672485, by decide⟩ =
    .split (coordinate 11) (![⟨672378, by decide⟩,⟨672428, by decide⟩,⟨672484, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22223_672485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22223 ⟨672485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22223
    ⟨672485, by decide⟩ (by decide) (![⟨672378, by decide⟩,⟨672428, by decide⟩,⟨672484, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_22223_672485 node_context_11_22223_672485
  intro a
  fin_cases a
  · exact context_12_88892_672378
  · exact context_12_88893_672428
  · exact context_12_88894_672484
  · exact context_12_88895_512556

theorem unmarked_context_10_5555_672486 : frontier 11 ⟨672486, by decide⟩
    (prefixCache 10 5555) (prefixPartial 10 5555) = false := by
  decide +kernel

theorem node_context_10_5555_672486 : EJMOriginalGlobalDAGData.nodes 11 ⟨672486, by decide⟩ =
    .split (coordinate 10) (![⟨671819, by decide⟩,⟨672065, by decide⟩,⟨672328, by decide⟩,⟨672485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5555_672486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5555 ⟨672486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5555
    ⟨672486, by decide⟩ (by decide) (![⟨671819, by decide⟩,⟨672065, by decide⟩,⟨672328, by decide⟩,⟨672485, by decide⟩]) unmarked_context_10_5555_672486 node_context_10_5555_672486
  intro a
  fin_cases a
  · exact context_11_22220_671819
  · exact context_11_22221_672065
  · exact context_11_22222_672328
  · exact context_11_22223_672485

theorem unmarked_context_9_1388_672487 : frontier 12 ⟨672487, by decide⟩
    (prefixCache 9 1388) (prefixPartial 9 1388) = false := by
  decide +kernel

theorem node_context_9_1388_672487 : EJMOriginalGlobalDAGData.nodes 12 ⟨672487, by decide⟩ =
    .split (coordinate 9) (![⟨668553, by decide⟩,⟨670178, by decide⟩,⟨671571, by decide⟩,⟨672486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1388_672487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1388 ⟨672487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1388
    ⟨672487, by decide⟩ (by decide) (![⟨668553, by decide⟩,⟨670178, by decide⟩,⟨671571, by decide⟩,⟨672486, by decide⟩]) unmarked_context_9_1388_672487 node_context_9_1388_672487
  intro a
  fin_cases a
  · exact context_10_5552_668553
  · exact context_10_5553_670178
  · exact context_10_5554_671571
  · exact context_10_5555_672486

theorem selected_cut_26601 : selected 9 ⟨672540, by decide⟩
    (prefixPartial 12 88896) = some ⟨12, 2, 0, 672540, 88896, 3929, 65536⟩ := by
  decide +kernel

theorem context_12_88896_672540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88896 ⟨672540, by decide⟩ :=
  accepted_of_selected 12 88896 ⟨672540, by decide⟩ ⟨12, 2, 0, 672540, 88896, 3929, 65536⟩
    (by decide) selected_cut_26601

theorem selected_cut_26602 : selected 9 ⟨672573, by decide⟩
    (prefixPartial 12 88897) = some ⟨12, 2, 0, 672573, 88897, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_88897_672573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88897 ⟨672573, by decide⟩ :=
  accepted_of_selected 12 88897 ⟨672573, by decide⟩ ⟨12, 2, 0, 672573, 88897, 1485, 65536⟩
    (by decide) selected_cut_26602

theorem selected_cut_26603 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355592) = some ⟨13, 1, 0, 3444, 355592, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355592_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355592 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355592 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355592, 1, 16384⟩
    (by decide) selected_cut_26603

theorem selected_cut_26604 : selected 8 ⟨672613, by decide⟩
    (prefixPartial 13 355593) = some ⟨13, 2, 0, 672613, 355593, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_355593_672613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355593 ⟨672613, by decide⟩ :=
  accepted_of_selected 13 355593 ⟨672613, by decide⟩ ⟨13, 2, 0, 672613, 355593, 2409, 16384⟩
    (by decide) selected_cut_26604

theorem selected_cut_26605 : selected 8 ⟨672636, by decide⟩
    (prefixPartial 13 355594) = some ⟨13, 2, 0, 672636, 355594, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_355594_672636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355594 ⟨672636, by decide⟩ :=
  accepted_of_selected 13 355594 ⟨672636, by decide⟩ ⟨13, 2, 0, 672636, 355594, 1445, 16384⟩
    (by decide) selected_cut_26605

theorem selected_cut_26606 : selected 8 ⟨672643, by decide⟩
    (prefixPartial 13 355595) = some ⟨13, 2, 0, 672643, 355595, 633, 16384⟩ := by
  decide +kernel

theorem context_13_355595_672643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355595 ⟨672643, by decide⟩ :=
  accepted_of_selected 13 355595 ⟨672643, by decide⟩ ⟨13, 2, 0, 672643, 355595, 633, 16384⟩
    (by decide) selected_cut_26606

theorem unmarked_context_12_88898_672644 : frontier 9 ⟨672644, by decide⟩
    (prefixCache 12 88898) (prefixPartial 12 88898) = false := by
  decide +kernel

theorem node_context_12_88898_672644 : EJMOriginalGlobalDAGData.nodes 9 ⟨672644, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨672613, by decide⟩,⟨672636, by decide⟩,⟨672643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88898_672644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88898 ⟨672644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88898
    ⟨672644, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨672613, by decide⟩,⟨672636, by decide⟩,⟨672643, by decide⟩]) unmarked_context_12_88898_672644 node_context_12_88898_672644
  intro a
  fin_cases a
  · exact context_13_355592_3444
  · exact context_13_355593_672613
  · exact context_13_355594_672636
  · exact context_13_355595_672643

theorem selected_cut_26607 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355596) = some ⟨13, 1, 0, 3444, 355596, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355596_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355596 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355596 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355596, 1, 16384⟩
    (by decide) selected_cut_26607

theorem selected_cut_26608 : selected 8 ⟨672670, by decide⟩
    (prefixPartial 13 355597) = some ⟨13, 2, 0, 672670, 355597, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_355597_672670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355597 ⟨672670, by decide⟩ :=
  accepted_of_selected 13 355597 ⟨672670, by decide⟩ ⟨13, 2, 0, 672670, 355597, 2285, 16384⟩
    (by decide) selected_cut_26608

theorem selected_cut_26609 : selected 8 ⟨672687, by decide⟩
    (prefixPartial 13 355598) = some ⟨13, 2, 0, 672687, 355598, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_355598_672687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355598 ⟨672687, by decide⟩ :=
  accepted_of_selected 13 355598 ⟨672687, by decide⟩ ⟨13, 2, 0, 672687, 355598, 1265, 16384⟩
    (by decide) selected_cut_26609

theorem selected_cut_26610 : selected 8 ⟨672694, by decide⟩
    (prefixPartial 13 355599) = some ⟨13, 2, 0, 672694, 355599, 617, 16384⟩ := by
  decide +kernel

theorem context_13_355599_672694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355599 ⟨672694, by decide⟩ :=
  accepted_of_selected 13 355599 ⟨672694, by decide⟩ ⟨13, 2, 0, 672694, 355599, 617, 16384⟩
    (by decide) selected_cut_26610

theorem unmarked_context_12_88899_672695 : frontier 9 ⟨672695, by decide⟩
    (prefixCache 12 88899) (prefixPartial 12 88899) = false := by
  decide +kernel

theorem node_context_12_88899_672695 : EJMOriginalGlobalDAGData.nodes 9 ⟨672695, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨672670, by decide⟩,⟨672687, by decide⟩,⟨672694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88899_672695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88899 ⟨672695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88899
    ⟨672695, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨672670, by decide⟩,⟨672687, by decide⟩,⟨672694, by decide⟩]) unmarked_context_12_88899_672695 node_context_12_88899_672695
  intro a
  fin_cases a
  · exact context_13_355596_3444
  · exact context_13_355597_672670
  · exact context_13_355598_672687
  · exact context_13_355599_672694

theorem unmarked_context_11_22224_672696 : frontier 10 ⟨672696, by decide⟩
    (prefixCache 11 22224) (prefixPartial 11 22224) = false := by
  decide +kernel

theorem node_context_11_22224_672696 : EJMOriginalGlobalDAGData.nodes 10 ⟨672696, by decide⟩ =
    .split (coordinate 11) (![⟨672540, by decide⟩,⟨672573, by decide⟩,⟨672644, by decide⟩,⟨672695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22224_672696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22224 ⟨672696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22224
    ⟨672696, by decide⟩ (by decide) (![⟨672540, by decide⟩,⟨672573, by decide⟩,⟨672644, by decide⟩,⟨672695, by decide⟩]) unmarked_context_11_22224_672696 node_context_11_22224_672696
  intro a
  fin_cases a
  · exact context_12_88896_672540
  · exact context_12_88897_672573
  · exact context_12_88898_672644
  · exact context_12_88899_672695

theorem selected_cut_26611 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355600) = some ⟨13, 1, 0, 3444, 355600, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355600_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355600 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355600 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355600, 1, 16384⟩
    (by decide) selected_cut_26611

theorem selected_cut_26612 : selected 8 ⟨672732, by decide⟩
    (prefixPartial 13 355601) = some ⟨13, 2, 0, 672732, 355601, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_355601_672732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355601 ⟨672732, by decide⟩ :=
  accepted_of_selected 13 355601 ⟨672732, by decide⟩ ⟨13, 2, 0, 672732, 355601, 2109, 16384⟩
    (by decide) selected_cut_26612

theorem selected_cut_26613 : selected 8 ⟨672751, by decide⟩
    (prefixPartial 13 355602) = some ⟨13, 2, 0, 672751, 355602, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_355602_672751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355602 ⟨672751, by decide⟩ :=
  accepted_of_selected 13 355602 ⟨672751, by decide⟩ ⟨13, 2, 0, 672751, 355602, 1193, 16384⟩
    (by decide) selected_cut_26613

theorem selected_cut_26614 : selected 8 ⟨672756, by decide⟩
    (prefixPartial 13 355603) = some ⟨13, 2, 0, 672756, 355603, 817, 16384⟩ := by
  decide +kernel

theorem context_13_355603_672756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355603 ⟨672756, by decide⟩ :=
  accepted_of_selected 13 355603 ⟨672756, by decide⟩ ⟨13, 2, 0, 672756, 355603, 817, 16384⟩
    (by decide) selected_cut_26614

theorem unmarked_context_12_88900_672757 : frontier 9 ⟨672757, by decide⟩
    (prefixCache 12 88900) (prefixPartial 12 88900) = false := by
  decide +kernel

theorem node_context_12_88900_672757 : EJMOriginalGlobalDAGData.nodes 9 ⟨672757, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨672732, by decide⟩,⟨672751, by decide⟩,⟨672756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88900_672757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88900 ⟨672757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88900
    ⟨672757, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨672732, by decide⟩,⟨672751, by decide⟩,⟨672756, by decide⟩]) unmarked_context_12_88900_672757 node_context_12_88900_672757
  intro a
  fin_cases a
  · exact context_13_355600_3444
  · exact context_13_355601_672732
  · exact context_13_355602_672751
  · exact context_13_355603_672756

theorem selected_cut_26615 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 88901) = some ⟨12, 1, 0, 170504, 88901, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88901_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88901 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 88901 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 88901, 1, 65536⟩
    (by decide) selected_cut_26615

theorem selected_cut_26616 : selected 9 ⟨672808, by decide⟩
    (prefixPartial 12 88902) = some ⟨12, 2, 0, 672808, 88902, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_88902_672808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88902 ⟨672808, by decide⟩ :=
  accepted_of_selected 12 88902 ⟨672808, by decide⟩ ⟨12, 2, 0, 672808, 88902, 3953, 65536⟩
    (by decide) selected_cut_26616

theorem selected_cut_26617 : selected 9 ⟨672855, by decide⟩
    (prefixPartial 12 88903) = some ⟨12, 2, 0, 672855, 88903, 3605, 65536⟩ := by
  decide +kernel

theorem context_12_88903_672855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88903 ⟨672855, by decide⟩ :=
  accepted_of_selected 12 88903 ⟨672855, by decide⟩ ⟨12, 2, 0, 672855, 88903, 3605, 65536⟩
    (by decide) selected_cut_26617

theorem unmarked_context_11_22225_672856 : frontier 10 ⟨672856, by decide⟩
    (prefixCache 11 22225) (prefixPartial 11 22225) = false := by
  decide +kernel

theorem node_context_11_22225_672856 : EJMOriginalGlobalDAGData.nodes 10 ⟨672856, by decide⟩ =
    .split (coordinate 11) (![⟨672757, by decide⟩,⟨170504, by decide⟩,⟨672808, by decide⟩,⟨672855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22225_672856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22225 ⟨672856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22225
    ⟨672856, by decide⟩ (by decide) (![⟨672757, by decide⟩,⟨170504, by decide⟩,⟨672808, by decide⟩,⟨672855, by decide⟩]) unmarked_context_11_22225_672856 node_context_11_22225_672856
  intro a
  fin_cases a
  · exact context_12_88900_672757
  · exact context_12_88901_170504
  · exact context_12_88902_672808
  · exact context_12_88903_672855

theorem selected_cut_26618 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355616) = some ⟨13, 1, 0, 3444, 355616, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355616_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355616 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355616 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355616, 1, 16384⟩
    (by decide) selected_cut_26618

theorem selected_cut_26619 : selected 8 ⟨672894, by decide⟩
    (prefixPartial 13 355617) = some ⟨13, 2, 0, 672894, 355617, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_355617_672894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355617 ⟨672894, by decide⟩ :=
  accepted_of_selected 13 355617 ⟨672894, by decide⟩ ⟨13, 2, 0, 672894, 355617, 1953, 16384⟩
    (by decide) selected_cut_26619

theorem selected_cut_26620 : selected 8 ⟨672911, by decide⟩
    (prefixPartial 13 355618) = some ⟨13, 2, 0, 672911, 355618, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_355618_672911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355618 ⟨672911, by decide⟩ :=
  accepted_of_selected 13 355618 ⟨672911, by decide⟩ ⟨13, 2, 0, 672911, 355618, 1505, 16384⟩
    (by decide) selected_cut_26620

theorem selected_cut_26621 : selected 8 ⟨672916, by decide⟩
    (prefixPartial 13 355619) = some ⟨13, 2, 0, 672916, 355619, 801, 16384⟩ := by
  decide +kernel

theorem context_13_355619_672916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355619 ⟨672916, by decide⟩ :=
  accepted_of_selected 13 355619 ⟨672916, by decide⟩ ⟨13, 2, 0, 672916, 355619, 801, 16384⟩
    (by decide) selected_cut_26621

theorem unmarked_context_12_88904_672917 : frontier 9 ⟨672917, by decide⟩
    (prefixCache 12 88904) (prefixPartial 12 88904) = false := by
  decide +kernel

theorem node_context_12_88904_672917 : EJMOriginalGlobalDAGData.nodes 9 ⟨672917, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨672894, by decide⟩,⟨672911, by decide⟩,⟨672916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88904_672917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88904 ⟨672917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88904
    ⟨672917, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨672894, by decide⟩,⟨672911, by decide⟩,⟨672916, by decide⟩]) unmarked_context_12_88904_672917 node_context_12_88904_672917
  intro a
  fin_cases a
  · exact context_13_355616_3444
  · exact context_13_355617_672894
  · exact context_13_355618_672911
  · exact context_13_355619_672916

theorem selected_cut_26622 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355620) = some ⟨13, 1, 0, 3444, 355620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355620, 1, 16384⟩
    (by decide) selected_cut_26622

theorem selected_cut_26623 : selected 8 ⟨672984, by decide⟩
    (prefixPartial 13 355621) = some ⟨13, 2, 0, 672984, 355621, 2685, 16384⟩ := by
  decide +kernel

theorem context_13_355621_672984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355621 ⟨672984, by decide⟩ :=
  accepted_of_selected 13 355621 ⟨672984, by decide⟩ ⟨13, 2, 0, 672984, 355621, 2685, 16384⟩
    (by decide) selected_cut_26623

theorem selected_cut_26624 : selected 8 ⟨673001, by decide⟩
    (prefixPartial 13 355622) = some ⟨13, 2, 0, 673001, 355622, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_355622_673001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355622 ⟨673001, by decide⟩ :=
  accepted_of_selected 13 355622 ⟨673001, by decide⟩ ⟨13, 2, 0, 673001, 355622, 1953, 16384⟩
    (by decide) selected_cut_26624

theorem selected_cut_26625 : selected 8 ⟨673009, by decide⟩
    (prefixPartial 13 355623) = some ⟨13, 2, 0, 673009, 355623, 941, 16384⟩ := by
  decide +kernel

theorem context_13_355623_673009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355623 ⟨673009, by decide⟩ :=
  accepted_of_selected 13 355623 ⟨673009, by decide⟩ ⟨13, 2, 0, 673009, 355623, 941, 16384⟩
    (by decide) selected_cut_26625

theorem unmarked_context_12_88905_673010 : frontier 9 ⟨673010, by decide⟩
    (prefixCache 12 88905) (prefixPartial 12 88905) = false := by
  decide +kernel

theorem node_context_12_88905_673010 : EJMOriginalGlobalDAGData.nodes 9 ⟨673010, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨672984, by decide⟩,⟨673001, by decide⟩,⟨673009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88905_673010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88905 ⟨673010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88905
    ⟨673010, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨672984, by decide⟩,⟨673001, by decide⟩,⟨673009, by decide⟩]) unmarked_context_12_88905_673010 node_context_12_88905_673010
  intro a
  fin_cases a
  · exact context_13_355620_3444
  · exact context_13_355621_672984
  · exact context_13_355622_673001
  · exact context_13_355623_673009

theorem selected_cut_26626 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355624) = some ⟨13, 1, 0, 3444, 355624, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355624_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355624 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355624 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355624, 1, 16384⟩
    (by decide) selected_cut_26626

theorem selected_cut_26627 : selected 8 ⟨673031, by decide⟩
    (prefixPartial 13 355625) = some ⟨13, 2, 0, 673031, 355625, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_355625_673031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355625 ⟨673031, by decide⟩ :=
  accepted_of_selected 13 355625 ⟨673031, by decide⟩ ⟨13, 2, 0, 673031, 355625, 1853, 16384⟩
    (by decide) selected_cut_26627

theorem selected_cut_26628 : selected 8 ⟨673053, by decide⟩
    (prefixPartial 13 355626) = some ⟨13, 2, 0, 673053, 355626, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_355626_673053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355626 ⟨673053, by decide⟩ :=
  accepted_of_selected 13 355626 ⟨673053, by decide⟩ ⟨13, 2, 0, 673053, 355626, 1861, 16384⟩
    (by decide) selected_cut_26628

theorem selected_cut_26629 : selected 8 ⟨673058, by decide⟩
    (prefixPartial 13 355627) = some ⟨13, 2, 0, 673058, 355627, 701, 16384⟩ := by
  decide +kernel

theorem context_13_355627_673058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355627 ⟨673058, by decide⟩ :=
  accepted_of_selected 13 355627 ⟨673058, by decide⟩ ⟨13, 2, 0, 673058, 355627, 701, 16384⟩
    (by decide) selected_cut_26629

theorem unmarked_context_12_88906_673059 : frontier 9 ⟨673059, by decide⟩
    (prefixCache 12 88906) (prefixPartial 12 88906) = false := by
  decide +kernel

theorem node_context_12_88906_673059 : EJMOriginalGlobalDAGData.nodes 9 ⟨673059, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨673031, by decide⟩,⟨673053, by decide⟩,⟨673058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88906_673059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88906 ⟨673059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88906
    ⟨673059, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨673031, by decide⟩,⟨673053, by decide⟩,⟨673058, by decide⟩]) unmarked_context_12_88906_673059 node_context_12_88906_673059
  intro a
  fin_cases a
  · exact context_13_355624_3444
  · exact context_13_355625_673031
  · exact context_13_355626_673053
  · exact context_13_355627_673058

theorem selected_cut_26630 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355628) = some ⟨13, 1, 0, 3444, 355628, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355628_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355628 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355628 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355628, 1, 16384⟩
    (by decide) selected_cut_26630

theorem selected_cut_26631 : selected 8 ⟨673082, by decide⟩
    (prefixPartial 13 355629) = some ⟨13, 2, 0, 673082, 355629, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_355629_673082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355629 ⟨673082, by decide⟩ :=
  accepted_of_selected 13 355629 ⟨673082, by decide⟩ ⟨13, 2, 0, 673082, 355629, 1837, 16384⟩
    (by decide) selected_cut_26631

theorem selected_cut_26632 : selected 8 ⟨673104, by decide⟩
    (prefixPartial 13 355630) = some ⟨13, 2, 0, 673104, 355630, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_355630_673104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355630 ⟨673104, by decide⟩ :=
  accepted_of_selected 13 355630 ⟨673104, by decide⟩ ⟨13, 2, 0, 673104, 355630, 1609, 16384⟩
    (by decide) selected_cut_26632

theorem selected_cut_26633 : selected 8 ⟨673110, by decide⟩
    (prefixPartial 13 355631) = some ⟨13, 2, 0, 673110, 355631, 749, 16384⟩ := by
  decide +kernel

theorem context_13_355631_673110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355631 ⟨673110, by decide⟩ :=
  accepted_of_selected 13 355631 ⟨673110, by decide⟩ ⟨13, 2, 0, 673110, 355631, 749, 16384⟩
    (by decide) selected_cut_26633

theorem unmarked_context_12_88907_673111 : frontier 9 ⟨673111, by decide⟩
    (prefixCache 12 88907) (prefixPartial 12 88907) = false := by
  decide +kernel

theorem node_context_12_88907_673111 : EJMOriginalGlobalDAGData.nodes 9 ⟨673111, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨673082, by decide⟩,⟨673104, by decide⟩,⟨673110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88907_673111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88907 ⟨673111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88907
    ⟨673111, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨673082, by decide⟩,⟨673104, by decide⟩,⟨673110, by decide⟩]) unmarked_context_12_88907_673111 node_context_12_88907_673111
  intro a
  fin_cases a
  · exact context_13_355628_3444
  · exact context_13_355629_673082
  · exact context_13_355630_673104
  · exact context_13_355631_673110

theorem unmarked_context_11_22226_673112 : frontier 10 ⟨673112, by decide⟩
    (prefixCache 11 22226) (prefixPartial 11 22226) = false := by
  decide +kernel

theorem node_context_11_22226_673112 : EJMOriginalGlobalDAGData.nodes 10 ⟨673112, by decide⟩ =
    .split (coordinate 11) (![⟨672917, by decide⟩,⟨673010, by decide⟩,⟨673059, by decide⟩,⟨673111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22226_673112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22226 ⟨673112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22226
    ⟨673112, by decide⟩ (by decide) (![⟨672917, by decide⟩,⟨673010, by decide⟩,⟨673059, by decide⟩,⟨673111, by decide⟩]) unmarked_context_11_22226_673112 node_context_11_22226_673112
  intro a
  fin_cases a
  · exact context_12_88904_672917
  · exact context_12_88905_673010
  · exact context_12_88906_673059
  · exact context_12_88907_673111

theorem selected_cut_26634 : selected 9 ⟨673157, by decide⟩
    (prefixPartial 12 88908) = some ⟨12, 2, 0, 673157, 88908, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_88908_673157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88908 ⟨673157, by decide⟩ :=
  accepted_of_selected 12 88908 ⟨673157, by decide⟩ ⟨12, 2, 0, 673157, 88908, 3677, 65536⟩
    (by decide) selected_cut_26634

theorem selected_cut_26635 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355636) = some ⟨13, 1, 0, 3444, 355636, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355636_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355636 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355636 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355636, 1, 16384⟩
    (by decide) selected_cut_26635

theorem selected_cut_26636 : selected 8 ⟨673210, by decide⟩
    (prefixPartial 13 355637) = some ⟨13, 2, 0, 673210, 355637, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_355637_673210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355637 ⟨673210, by decide⟩ :=
  accepted_of_selected 13 355637 ⟨673210, by decide⟩ ⟨13, 2, 0, 673210, 355637, 2357, 16384⟩
    (by decide) selected_cut_26636

theorem selected_cut_26637 : selected 8 ⟨673227, by decide⟩
    (prefixPartial 13 355638) = some ⟨13, 2, 0, 673227, 355638, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_355638_673227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355638 ⟨673227, by decide⟩ :=
  accepted_of_selected 13 355638 ⟨673227, by decide⟩ ⟨13, 2, 0, 673227, 355638, 1601, 16384⟩
    (by decide) selected_cut_26637

theorem selected_cut_26638 : selected 8 ⟨673232, by decide⟩
    (prefixPartial 13 355639) = some ⟨13, 2, 0, 673232, 355639, 961, 16384⟩ := by
  decide +kernel

theorem context_13_355639_673232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355639 ⟨673232, by decide⟩ :=
  accepted_of_selected 13 355639 ⟨673232, by decide⟩ ⟨13, 2, 0, 673232, 355639, 961, 16384⟩
    (by decide) selected_cut_26638

theorem unmarked_context_12_88909_673233 : frontier 9 ⟨673233, by decide⟩
    (prefixCache 12 88909) (prefixPartial 12 88909) = false := by
  decide +kernel

theorem node_context_12_88909_673233 : EJMOriginalGlobalDAGData.nodes 9 ⟨673233, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨673210, by decide⟩,⟨673227, by decide⟩,⟨673232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88909_673233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88909 ⟨673233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88909
    ⟨673233, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨673210, by decide⟩,⟨673227, by decide⟩,⟨673232, by decide⟩]) unmarked_context_12_88909_673233 node_context_12_88909_673233
  intro a
  fin_cases a
  · exact context_13_355636_3444
  · exact context_13_355637_673210
  · exact context_13_355638_673227
  · exact context_13_355639_673232

theorem selected_cut_26639 : selected 9 ⟨673287, by decide⟩
    (prefixPartial 12 88910) = some ⟨12, 2, 0, 673287, 88910, 3873, 65536⟩ := by
  decide +kernel

theorem context_12_88910_673287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88910 ⟨673287, by decide⟩ :=
  accepted_of_selected 12 88910 ⟨673287, by decide⟩ ⟨12, 2, 0, 673287, 88910, 3873, 65536⟩
    (by decide) selected_cut_26639

theorem selected_cut_26640 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355644) = some ⟨13, 1, 0, 3444, 355644, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355644_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355644 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355644 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355644, 1, 16384⟩
    (by decide) selected_cut_26640

theorem selected_cut_26641 : selected 8 ⟨673343, by decide⟩
    (prefixPartial 13 355645) = some ⟨13, 2, 0, 673343, 355645, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_355645_673343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355645 ⟨673343, by decide⟩ :=
  accepted_of_selected 13 355645 ⟨673343, by decide⟩ ⟨13, 2, 0, 673343, 355645, 2589, 16384⟩
    (by decide) selected_cut_26641

theorem selected_cut_26642 : selected 8 ⟨673369, by decide⟩
    (prefixPartial 13 355646) = some ⟨13, 2, 0, 673369, 355646, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_355646_673369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355646 ⟨673369, by decide⟩ :=
  accepted_of_selected 13 355646 ⟨673369, by decide⟩ ⟨13, 2, 0, 673369, 355646, 2277, 16384⟩
    (by decide) selected_cut_26642

theorem selected_cut_26643 : selected 8 ⟨673378, by decide⟩
    (prefixPartial 13 355647) = some ⟨13, 2, 0, 673378, 355647, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_355647_673378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355647 ⟨673378, by decide⟩ :=
  accepted_of_selected 13 355647 ⟨673378, by decide⟩ ⟨13, 2, 0, 673378, 355647, 1093, 16384⟩
    (by decide) selected_cut_26643

theorem unmarked_context_12_88911_673379 : frontier 9 ⟨673379, by decide⟩
    (prefixCache 12 88911) (prefixPartial 12 88911) = false := by
  decide +kernel

theorem node_context_12_88911_673379 : EJMOriginalGlobalDAGData.nodes 9 ⟨673379, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨673343, by decide⟩,⟨673369, by decide⟩,⟨673378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88911_673379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88911 ⟨673379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88911
    ⟨673379, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨673343, by decide⟩,⟨673369, by decide⟩,⟨673378, by decide⟩]) unmarked_context_12_88911_673379 node_context_12_88911_673379
  intro a
  fin_cases a
  · exact context_13_355644_3444
  · exact context_13_355645_673343
  · exact context_13_355646_673369
  · exact context_13_355647_673378

theorem unmarked_context_11_22227_673380 : frontier 10 ⟨673380, by decide⟩
    (prefixCache 11 22227) (prefixPartial 11 22227) = false := by
  decide +kernel

theorem node_context_11_22227_673380 : EJMOriginalGlobalDAGData.nodes 10 ⟨673380, by decide⟩ =
    .split (coordinate 11) (![⟨673157, by decide⟩,⟨673233, by decide⟩,⟨673287, by decide⟩,⟨673379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22227_673380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22227 ⟨673380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22227
    ⟨673380, by decide⟩ (by decide) (![⟨673157, by decide⟩,⟨673233, by decide⟩,⟨673287, by decide⟩,⟨673379, by decide⟩]) unmarked_context_11_22227_673380 node_context_11_22227_673380
  intro a
  fin_cases a
  · exact context_12_88908_673157
  · exact context_12_88909_673233
  · exact context_12_88910_673287
  · exact context_12_88911_673379

theorem unmarked_context_10_5556_673381 : frontier 11 ⟨673381, by decide⟩
    (prefixCache 10 5556) (prefixPartial 10 5556) = false := by
  decide +kernel

theorem node_context_10_5556_673381 : EJMOriginalGlobalDAGData.nodes 11 ⟨673381, by decide⟩ =
    .split (coordinate 10) (![⟨672696, by decide⟩,⟨672856, by decide⟩,⟨673112, by decide⟩,⟨673380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5556_673381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5556 ⟨673381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5556
    ⟨673381, by decide⟩ (by decide) (![⟨672696, by decide⟩,⟨672856, by decide⟩,⟨673112, by decide⟩,⟨673380, by decide⟩]) unmarked_context_10_5556_673381 node_context_10_5556_673381
  intro a
  fin_cases a
  · exact context_11_22224_672696
  · exact context_11_22225_672856
  · exact context_11_22226_673112
  · exact context_11_22227_673380

theorem selected_cut_26644 : selected 9 ⟨673425, by decide⟩
    (prefixPartial 12 88912) = some ⟨12, 2, 0, 673425, 88912, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_88912_673425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88912 ⟨673425, by decide⟩ :=
  accepted_of_selected 12 88912 ⟨673425, by decide⟩ ⟨12, 2, 0, 673425, 88912, 3409, 65536⟩
    (by decide) selected_cut_26644

theorem selected_cut_26645 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 88913) = some ⟨12, 1, 0, 642341, 88913, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88913_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88913 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 88913 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 88913, 1, 65536⟩
    (by decide) selected_cut_26645

theorem selected_cut_26646 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355656) = some ⟨13, 1, 0, 3444, 355656, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355656_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355656 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355656 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355656, 1, 16384⟩
    (by decide) selected_cut_26646

theorem selected_cut_26647 : selected 8 ⟨673454, by decide⟩
    (prefixPartial 13 355657) = some ⟨13, 2, 0, 673454, 355657, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_355657_673454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355657 ⟨673454, by decide⟩ :=
  accepted_of_selected 13 355657 ⟨673454, by decide⟩ ⟨13, 2, 0, 673454, 355657, 1853, 16384⟩
    (by decide) selected_cut_26647

theorem selected_cut_26648 : selected 8 ⟨673482, by decide⟩
    (prefixPartial 13 355658) = some ⟨13, 2, 0, 673482, 355658, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_355658_673482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355658 ⟨673482, by decide⟩ :=
  accepted_of_selected 13 355658 ⟨673482, by decide⟩ ⟨13, 2, 0, 673482, 355658, 1573, 16384⟩
    (by decide) selected_cut_26648

theorem selected_cut_26649 : selected 8 ⟨673489, by decide⟩
    (prefixPartial 13 355659) = some ⟨13, 2, 0, 673489, 355659, 673, 16384⟩ := by
  decide +kernel

theorem context_13_355659_673489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355659 ⟨673489, by decide⟩ :=
  accepted_of_selected 13 355659 ⟨673489, by decide⟩ ⟨13, 2, 0, 673489, 355659, 673, 16384⟩
    (by decide) selected_cut_26649

theorem unmarked_context_12_88914_673490 : frontier 9 ⟨673490, by decide⟩
    (prefixCache 12 88914) (prefixPartial 12 88914) = false := by
  decide +kernel

theorem node_context_12_88914_673490 : EJMOriginalGlobalDAGData.nodes 9 ⟨673490, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨673454, by decide⟩,⟨673482, by decide⟩,⟨673489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88914_673490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88914 ⟨673490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88914
    ⟨673490, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨673454, by decide⟩,⟨673482, by decide⟩,⟨673489, by decide⟩]) unmarked_context_12_88914_673490 node_context_12_88914_673490
  intro a
  fin_cases a
  · exact context_13_355656_3444
  · exact context_13_355657_673454
  · exact context_13_355658_673482
  · exact context_13_355659_673489

theorem selected_cut_26650 : selected 9 ⟨673534, by decide⟩
    (prefixPartial 12 88915) = some ⟨12, 2, 0, 673534, 88915, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_88915_673534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88915 ⟨673534, by decide⟩ :=
  accepted_of_selected 12 88915 ⟨673534, by decide⟩ ⟨12, 2, 0, 673534, 88915, 3573, 65536⟩
    (by decide) selected_cut_26650

theorem unmarked_context_11_22228_673535 : frontier 10 ⟨673535, by decide⟩
    (prefixCache 11 22228) (prefixPartial 11 22228) = false := by
  decide +kernel

theorem node_context_11_22228_673535 : EJMOriginalGlobalDAGData.nodes 10 ⟨673535, by decide⟩ =
    .split (coordinate 11) (![⟨673425, by decide⟩,⟨642341, by decide⟩,⟨673490, by decide⟩,⟨673534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22228_673535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22228 ⟨673535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22228
    ⟨673535, by decide⟩ (by decide) (![⟨673425, by decide⟩,⟨642341, by decide⟩,⟨673490, by decide⟩,⟨673534, by decide⟩]) unmarked_context_11_22228_673535 node_context_11_22228_673535
  intro a
  fin_cases a
  · exact context_12_88912_673425
  · exact context_12_88913_642341
  · exact context_12_88914_673490
  · exact context_12_88915_673534

theorem selected_cut_26651 : selected 9 ⟨673580, by decide⟩
    (prefixPartial 12 88916) = some ⟨12, 2, 0, 673580, 88916, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_88916_673580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88916 ⟨673580, by decide⟩ :=
  accepted_of_selected 12 88916 ⟨673580, by decide⟩ ⟨12, 2, 0, 673580, 88916, 3617, 65536⟩
    (by decide) selected_cut_26651

theorem selected_cut_26652 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 88917) = some ⟨12, 1, 0, 642341, 88917, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88917_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88917 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 88917 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 88917, 1, 65536⟩
    (by decide) selected_cut_26652

theorem selected_cut_26653 : selected 9 ⟨673627, by decide⟩
    (prefixPartial 12 88918) = some ⟨12, 2, 0, 673627, 88918, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_88918_673627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88918 ⟨673627, by decide⟩ :=
  accepted_of_selected 12 88918 ⟨673627, by decide⟩ ⟨12, 2, 0, 673627, 88918, 3693, 65536⟩
    (by decide) selected_cut_26653

theorem selected_cut_26654 : selected 9 ⟨673669, by decide⟩
    (prefixPartial 12 88919) = some ⟨12, 2, 0, 673669, 88919, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_88919_673669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88919 ⟨673669, by decide⟩ :=
  accepted_of_selected 12 88919 ⟨673669, by decide⟩ ⟨12, 2, 0, 673669, 88919, 3141, 65536⟩
    (by decide) selected_cut_26654

theorem unmarked_context_11_22229_673670 : frontier 10 ⟨673670, by decide⟩
    (prefixCache 11 22229) (prefixPartial 11 22229) = false := by
  decide +kernel

theorem node_context_11_22229_673670 : EJMOriginalGlobalDAGData.nodes 10 ⟨673670, by decide⟩ =
    .split (coordinate 11) (![⟨673580, by decide⟩,⟨642341, by decide⟩,⟨673627, by decide⟩,⟨673669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22229_673670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22229 ⟨673670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22229
    ⟨673670, by decide⟩ (by decide) (![⟨673580, by decide⟩,⟨642341, by decide⟩,⟨673627, by decide⟩,⟨673669, by decide⟩]) unmarked_context_11_22229_673670 node_context_11_22229_673670
  intro a
  fin_cases a
  · exact context_12_88916_673580
  · exact context_12_88917_642341
  · exact context_12_88918_673627
  · exact context_12_88919_673669

theorem selected_cut_26655 : selected 9 ⟨673723, by decide⟩
    (prefixPartial 12 88920) = some ⟨12, 2, 0, 673723, 88920, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_88920_673723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88920 ⟨673723, by decide⟩ :=
  accepted_of_selected 12 88920 ⟨673723, by decide⟩ ⟨12, 2, 0, 673723, 88920, 3945, 65536⟩
    (by decide) selected_cut_26655

theorem selected_cut_26656 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 88921) = some ⟨12, 1, 0, 642341, 88921, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88921_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88921 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 88921 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 88921, 1, 65536⟩
    (by decide) selected_cut_26656

theorem selected_cut_26657 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355688) = some ⟨13, 1, 0, 3444, 355688, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355688_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355688 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355688 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355688, 1, 16384⟩
    (by decide) selected_cut_26657

theorem selected_cut_26658 : selected 8 ⟨673744, by decide⟩
    (prefixPartial 13 355689) = some ⟨13, 2, 0, 673744, 355689, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_355689_673744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355689 ⟨673744, by decide⟩ :=
  accepted_of_selected 13 355689 ⟨673744, by decide⟩ ⟨13, 2, 0, 673744, 355689, 1365, 16384⟩
    (by decide) selected_cut_26658

theorem selected_cut_26659 : selected 8 ⟨673784, by decide⟩
    (prefixPartial 13 355690) = some ⟨13, 2, 0, 673784, 355690, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_355690_673784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355690 ⟨673784, by decide⟩ :=
  accepted_of_selected 13 355690 ⟨673784, by decide⟩ ⟨13, 2, 0, 673784, 355690, 2045, 16384⟩
    (by decide) selected_cut_26659

theorem selected_cut_26660 : selected 8 ⟨673792, by decide⟩
    (prefixPartial 13 355691) = some ⟨13, 2, 0, 673792, 355691, 813, 16384⟩ := by
  decide +kernel

theorem context_13_355691_673792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355691 ⟨673792, by decide⟩ :=
  accepted_of_selected 13 355691 ⟨673792, by decide⟩ ⟨13, 2, 0, 673792, 355691, 813, 16384⟩
    (by decide) selected_cut_26660

theorem unmarked_context_12_88922_673793 : frontier 9 ⟨673793, by decide⟩
    (prefixCache 12 88922) (prefixPartial 12 88922) = false := by
  decide +kernel

theorem node_context_12_88922_673793 : EJMOriginalGlobalDAGData.nodes 9 ⟨673793, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨673744, by decide⟩,⟨673784, by decide⟩,⟨673792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88922_673793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88922 ⟨673793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88922
    ⟨673793, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨673744, by decide⟩,⟨673784, by decide⟩,⟨673792, by decide⟩]) unmarked_context_12_88922_673793 node_context_12_88922_673793
  intro a
  fin_cases a
  · exact context_13_355688_3444
  · exact context_13_355689_673744
  · exact context_13_355690_673784
  · exact context_13_355691_673792

theorem selected_cut_26661 : selected 9 ⟨673841, by decide⟩
    (prefixPartial 12 88923) = some ⟨12, 2, 0, 673841, 88923, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_88923_673841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88923 ⟨673841, by decide⟩ :=
  accepted_of_selected 12 88923 ⟨673841, by decide⟩ ⟨12, 2, 0, 673841, 88923, 3797, 65536⟩
    (by decide) selected_cut_26661

theorem unmarked_context_11_22230_673842 : frontier 10 ⟨673842, by decide⟩
    (prefixCache 11 22230) (prefixPartial 11 22230) = false := by
  decide +kernel

theorem node_context_11_22230_673842 : EJMOriginalGlobalDAGData.nodes 10 ⟨673842, by decide⟩ =
    .split (coordinate 11) (![⟨673723, by decide⟩,⟨642341, by decide⟩,⟨673793, by decide⟩,⟨673841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22230_673842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22230 ⟨673842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22230
    ⟨673842, by decide⟩ (by decide) (![⟨673723, by decide⟩,⟨642341, by decide⟩,⟨673793, by decide⟩,⟨673841, by decide⟩]) unmarked_context_11_22230_673842 node_context_11_22230_673842
  intro a
  fin_cases a
  · exact context_12_88920_673723
  · exact context_12_88921_642341
  · exact context_12_88922_673793
  · exact context_12_88923_673841

theorem selected_cut_26662 : selected 9 ⟨673884, by decide⟩
    (prefixPartial 12 88924) = some ⟨12, 2, 0, 673884, 88924, 3281, 65536⟩ := by
  decide +kernel

theorem context_12_88924_673884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88924 ⟨673884, by decide⟩ :=
  accepted_of_selected 12 88924 ⟨673884, by decide⟩ ⟨12, 2, 0, 673884, 88924, 3281, 65536⟩
    (by decide) selected_cut_26662

theorem selected_cut_26663 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 88925) = some ⟨12, 1, 0, 642341, 88925, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88925_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88925 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 88925 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 88925, 1, 65536⟩
    (by decide) selected_cut_26663

theorem selected_cut_26664 : selected 9 ⟨673931, by decide⟩
    (prefixPartial 12 88926) = some ⟨12, 2, 0, 673931, 88926, 3589, 65536⟩ := by
  decide +kernel

theorem context_12_88926_673931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88926 ⟨673931, by decide⟩ :=
  accepted_of_selected 12 88926 ⟨673931, by decide⟩ ⟨12, 2, 0, 673931, 88926, 3589, 65536⟩
    (by decide) selected_cut_26664

theorem selected_cut_26665 : selected 9 ⟨674070, by decide⟩
    (prefixPartial 12 88927) = some ⟨12, 2, 0, 674070, 88927, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_88927_674070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88927 ⟨674070, by decide⟩ :=
  accepted_of_selected 12 88927 ⟨674070, by decide⟩ ⟨12, 2, 0, 674070, 88927, 2561, 65536⟩
    (by decide) selected_cut_26665

theorem unmarked_context_11_22231_674071 : frontier 10 ⟨674071, by decide⟩
    (prefixCache 11 22231) (prefixPartial 11 22231) = false := by
  decide +kernel

theorem node_context_11_22231_674071 : EJMOriginalGlobalDAGData.nodes 10 ⟨674071, by decide⟩ =
    .split (coordinate 11) (![⟨673884, by decide⟩,⟨642341, by decide⟩,⟨673931, by decide⟩,⟨674070, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22231_674071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22231 ⟨674071, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22231
    ⟨674071, by decide⟩ (by decide) (![⟨673884, by decide⟩,⟨642341, by decide⟩,⟨673931, by decide⟩,⟨674070, by decide⟩]) unmarked_context_11_22231_674071 node_context_11_22231_674071
  intro a
  fin_cases a
  · exact context_12_88924_673884
  · exact context_12_88925_642341
  · exact context_12_88926_673931
  · exact context_12_88927_674070

theorem unmarked_context_10_5557_674072 : frontier 11 ⟨674072, by decide⟩
    (prefixCache 10 5557) (prefixPartial 10 5557) = false := by
  decide +kernel

theorem node_context_10_5557_674072 : EJMOriginalGlobalDAGData.nodes 11 ⟨674072, by decide⟩ =
    .split (coordinate 10) (![⟨673535, by decide⟩,⟨673670, by decide⟩,⟨673842, by decide⟩,⟨674071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5557_674072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5557 ⟨674072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5557
    ⟨674072, by decide⟩ (by decide) (![⟨673535, by decide⟩,⟨673670, by decide⟩,⟨673842, by decide⟩,⟨674071, by decide⟩]) unmarked_context_10_5557_674072 node_context_10_5557_674072
  intro a
  fin_cases a
  · exact context_11_22228_673535
  · exact context_11_22229_673670
  · exact context_11_22230_673842
  · exact context_11_22231_674071

theorem selected_cut_26666 : selected 9 ⟨674108, by decide⟩
    (prefixPartial 12 88928) = some ⟨12, 2, 0, 674108, 88928, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_88928_674108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88928 ⟨674108, by decide⟩ :=
  accepted_of_selected 12 88928 ⟨674108, by decide⟩ ⟨12, 2, 0, 674108, 88928, 2933, 65536⟩
    (by decide) selected_cut_26666

theorem selected_cut_26667 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355716) = some ⟨13, 1, 0, 3444, 355716, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355716_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355716 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355716 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355716, 1, 16384⟩
    (by decide) selected_cut_26667

theorem selected_cut_26668 : selected 8 ⟨674141, by decide⟩
    (prefixPartial 13 355717) = some ⟨13, 2, 0, 674141, 355717, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_355717_674141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355717 ⟨674141, by decide⟩ :=
  accepted_of_selected 13 355717 ⟨674141, by decide⟩ ⟨13, 2, 0, 674141, 355717, 1597, 16384⟩
    (by decide) selected_cut_26668

theorem selected_cut_26669 : selected 8 ⟨674165, by decide⟩
    (prefixPartial 13 355718) = some ⟨13, 2, 0, 674165, 355718, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_355718_674165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355718 ⟨674165, by decide⟩ :=
  accepted_of_selected 13 355718 ⟨674165, by decide⟩ ⟨13, 2, 0, 674165, 355718, 1681, 16384⟩
    (by decide) selected_cut_26669

theorem selected_cut_26670 : selected 8 ⟨674171, by decide⟩
    (prefixPartial 13 355719) = some ⟨13, 2, 0, 674171, 355719, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_355719_674171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355719 ⟨674171, by decide⟩ :=
  accepted_of_selected 13 355719 ⟨674171, by decide⟩ ⟨13, 2, 0, 674171, 355719, 1005, 16384⟩
    (by decide) selected_cut_26670

theorem unmarked_context_12_88929_674172 : frontier 9 ⟨674172, by decide⟩
    (prefixCache 12 88929) (prefixPartial 12 88929) = false := by
  decide +kernel

theorem node_context_12_88929_674172 : EJMOriginalGlobalDAGData.nodes 9 ⟨674172, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨674141, by decide⟩,⟨674165, by decide⟩,⟨674171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88929_674172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88929 ⟨674172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88929
    ⟨674172, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨674141, by decide⟩,⟨674165, by decide⟩,⟨674171, by decide⟩]) unmarked_context_12_88929_674172 node_context_12_88929_674172
  intro a
  fin_cases a
  · exact context_13_355716_3444
  · exact context_13_355717_674141
  · exact context_13_355718_674165
  · exact context_13_355719_674171

theorem selected_cut_26671 : selected 9 ⟨674216, by decide⟩
    (prefixPartial 12 88930) = some ⟨12, 2, 0, 674216, 88930, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_88930_674216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88930 ⟨674216, by decide⟩ :=
  accepted_of_selected 12 88930 ⟨674216, by decide⟩ ⟨12, 2, 0, 674216, 88930, 3397, 65536⟩
    (by decide) selected_cut_26671

theorem selected_cut_26672 : selected 9 ⟨674250, by decide⟩
    (prefixPartial 12 88931) = some ⟨12, 2, 0, 674250, 88931, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_88931_674250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88931 ⟨674250, by decide⟩ :=
  accepted_of_selected 12 88931 ⟨674250, by decide⟩ ⟨12, 2, 0, 674250, 88931, 2885, 65536⟩
    (by decide) selected_cut_26672

theorem unmarked_context_11_22232_674251 : frontier 10 ⟨674251, by decide⟩
    (prefixCache 11 22232) (prefixPartial 11 22232) = false := by
  decide +kernel

theorem node_context_11_22232_674251 : EJMOriginalGlobalDAGData.nodes 10 ⟨674251, by decide⟩ =
    .split (coordinate 11) (![⟨674108, by decide⟩,⟨674172, by decide⟩,⟨674216, by decide⟩,⟨674250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22232_674251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22232 ⟨674251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22232
    ⟨674251, by decide⟩ (by decide) (![⟨674108, by decide⟩,⟨674172, by decide⟩,⟨674216, by decide⟩,⟨674250, by decide⟩]) unmarked_context_11_22232_674251 node_context_11_22232_674251
  intro a
  fin_cases a
  · exact context_12_88928_674108
  · exact context_12_88929_674172
  · exact context_12_88930_674216
  · exact context_12_88931_674250

theorem selected_cut_26673 : selected 9 ⟨674291, by decide⟩
    (prefixPartial 12 88932) = some ⟨12, 2, 0, 674291, 88932, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_88932_674291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88932 ⟨674291, by decide⟩ :=
  accepted_of_selected 12 88932 ⟨674291, by decide⟩ ⟨12, 2, 0, 674291, 88932, 2933, 65536⟩
    (by decide) selected_cut_26673

theorem selected_cut_26674 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 88933) = some ⟨12, 1, 0, 642794, 88933, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88933_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88933 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 88933 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 88933, 1, 65536⟩
    (by decide) selected_cut_26674

theorem selected_cut_26675 : selected 9 ⟨674328, by decide⟩
    (prefixPartial 12 88934) = some ⟨12, 2, 0, 674328, 88934, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_88934_674328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88934 ⟨674328, by decide⟩ :=
  accepted_of_selected 12 88934 ⟨674328, by decide⟩ ⟨12, 2, 0, 674328, 88934, 3017, 65536⟩
    (by decide) selected_cut_26675

theorem selected_cut_26676 : selected 9 ⟨674361, by decide⟩
    (prefixPartial 12 88935) = some ⟨12, 2, 0, 674361, 88935, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_88935_674361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88935 ⟨674361, by decide⟩ :=
  accepted_of_selected 12 88935 ⟨674361, by decide⟩ ⟨12, 2, 0, 674361, 88935, 2517, 65536⟩
    (by decide) selected_cut_26676

theorem unmarked_context_11_22233_674362 : frontier 10 ⟨674362, by decide⟩
    (prefixCache 11 22233) (prefixPartial 11 22233) = false := by
  decide +kernel

theorem node_context_11_22233_674362 : EJMOriginalGlobalDAGData.nodes 10 ⟨674362, by decide⟩ =
    .split (coordinate 11) (![⟨674291, by decide⟩,⟨642794, by decide⟩,⟨674328, by decide⟩,⟨674361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22233_674362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22233 ⟨674362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22233
    ⟨674362, by decide⟩ (by decide) (![⟨674291, by decide⟩,⟨642794, by decide⟩,⟨674328, by decide⟩,⟨674361, by decide⟩]) unmarked_context_11_22233_674362 node_context_11_22233_674362
  intro a
  fin_cases a
  · exact context_12_88932_674291
  · exact context_12_88933_642794
  · exact context_12_88934_674328
  · exact context_12_88935_674361

theorem selected_cut_26677 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355744) = some ⟨13, 1, 0, 3444, 355744, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355744_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355744 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355744 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355744, 1, 16384⟩
    (by decide) selected_cut_26677

theorem selected_cut_26678 : selected 8 ⟨674384, by decide⟩
    (prefixPartial 13 355745) = some ⟨13, 2, 0, 674384, 355745, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_355745_674384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355745 ⟨674384, by decide⟩ :=
  accepted_of_selected 13 355745 ⟨674384, by decide⟩ ⟨13, 2, 0, 674384, 355745, 1113, 16384⟩
    (by decide) selected_cut_26678

theorem selected_cut_26679 : selected 8 ⟨674404, by decide⟩
    (prefixPartial 13 355746) = some ⟨13, 2, 0, 674404, 355746, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_355746_674404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355746 ⟨674404, by decide⟩ :=
  accepted_of_selected 13 355746 ⟨674404, by decide⟩ ⟨13, 2, 0, 674404, 355746, 1905, 16384⟩
    (by decide) selected_cut_26679

theorem selected_cut_26680 : selected 8 ⟨674438, by decide⟩
    (prefixPartial 13 355747) = some ⟨13, 2, 0, 674438, 355747, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_355747_674438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355747 ⟨674438, by decide⟩ :=
  accepted_of_selected 13 355747 ⟨674438, by decide⟩ ⟨13, 2, 0, 674438, 355747, 1241, 16384⟩
    (by decide) selected_cut_26680

theorem unmarked_context_12_88936_674439 : frontier 9 ⟨674439, by decide⟩
    (prefixCache 12 88936) (prefixPartial 12 88936) = false := by
  decide +kernel

theorem node_context_12_88936_674439 : EJMOriginalGlobalDAGData.nodes 9 ⟨674439, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨674384, by decide⟩,⟨674404, by decide⟩,⟨674438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88936_674439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88936 ⟨674439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88936
    ⟨674439, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨674384, by decide⟩,⟨674404, by decide⟩,⟨674438, by decide⟩]) unmarked_context_12_88936_674439 node_context_12_88936_674439
  intro a
  fin_cases a
  · exact context_13_355744_3444
  · exact context_13_355745_674384
  · exact context_13_355746_674404
  · exact context_13_355747_674438

theorem selected_cut_26681 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355748) = some ⟨13, 1, 0, 3444, 355748, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355748_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355748 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355748 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355748, 1, 16384⟩
    (by decide) selected_cut_26681

theorem selected_cut_26682 : selected 8 ⟨674480, by decide⟩
    (prefixPartial 13 355749) = some ⟨13, 2, 0, 674480, 355749, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_355749_674480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355749 ⟨674480, by decide⟩ :=
  accepted_of_selected 13 355749 ⟨674480, by decide⟩ ⟨13, 2, 0, 674480, 355749, 1461, 16384⟩
    (by decide) selected_cut_26682

theorem selected_cut_26683 : selected 8 ⟨674523, by decide⟩
    (prefixPartial 13 355750) = some ⟨13, 2, 0, 674523, 355750, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_355750_674523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355750 ⟨674523, by decide⟩ :=
  accepted_of_selected 13 355750 ⟨674523, by decide⟩ ⟨13, 2, 0, 674523, 355750, 2505, 16384⟩
    (by decide) selected_cut_26683

theorem selected_cut_26684 : selected 8 ⟨674582, by decide⟩
    (prefixPartial 13 355751) = some ⟨13, 2, 0, 674582, 355751, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_355751_674582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355751 ⟨674582, by decide⟩ :=
  accepted_of_selected 13 355751 ⟨674582, by decide⟩ ⟨13, 2, 0, 674582, 355751, 1485, 16384⟩
    (by decide) selected_cut_26684

theorem unmarked_context_12_88937_674583 : frontier 9 ⟨674583, by decide⟩
    (prefixCache 12 88937) (prefixPartial 12 88937) = false := by
  decide +kernel

theorem node_context_12_88937_674583 : EJMOriginalGlobalDAGData.nodes 9 ⟨674583, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨674480, by decide⟩,⟨674523, by decide⟩,⟨674582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88937_674583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88937 ⟨674583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88937
    ⟨674583, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨674480, by decide⟩,⟨674523, by decide⟩,⟨674582, by decide⟩]) unmarked_context_12_88937_674583 node_context_12_88937_674583
  intro a
  fin_cases a
  · exact context_13_355748_3444
  · exact context_13_355749_674480
  · exact context_13_355750_674523
  · exact context_13_355751_674582

theorem selected_cut_26685 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 88938) = some ⟨12, 1, 0, 474208, 88938, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88938_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88938 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 88938 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 88938, 1, 65536⟩
    (by decide) selected_cut_26685

theorem selected_cut_26686 : selected 9 ⟨674634, by decide⟩
    (prefixPartial 12 88939) = some ⟨12, 2, 0, 674634, 88939, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_88939_674634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88939 ⟨674634, by decide⟩ :=
  accepted_of_selected 12 88939 ⟨674634, by decide⟩ ⟨12, 2, 0, 674634, 88939, 3989, 65536⟩
    (by decide) selected_cut_26686

theorem unmarked_context_11_22234_674635 : frontier 10 ⟨674635, by decide⟩
    (prefixCache 11 22234) (prefixPartial 11 22234) = false := by
  decide +kernel

theorem node_context_11_22234_674635 : EJMOriginalGlobalDAGData.nodes 10 ⟨674635, by decide⟩ =
    .split (coordinate 11) (![⟨674439, by decide⟩,⟨674583, by decide⟩,⟨474208, by decide⟩,⟨674634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22234_674635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22234 ⟨674635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22234
    ⟨674635, by decide⟩ (by decide) (![⟨674439, by decide⟩,⟨674583, by decide⟩,⟨474208, by decide⟩,⟨674634, by decide⟩]) unmarked_context_11_22234_674635 node_context_11_22234_674635
  intro a
  fin_cases a
  · exact context_12_88936_674439
  · exact context_12_88937_674583
  · exact context_12_88938_474208
  · exact context_12_88939_674634

theorem selected_cut_26687 : selected 9 ⟨674668, by decide⟩
    (prefixPartial 12 88940) = some ⟨12, 2, 0, 674668, 88940, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_88940_674668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88940 ⟨674668, by decide⟩ :=
  accepted_of_selected 12 88940 ⟨674668, by decide⟩ ⟨12, 2, 0, 674668, 88940, 2745, 65536⟩
    (by decide) selected_cut_26687

theorem selected_cut_26688 : selected 9 ⟨674713, by decide⟩
    (prefixPartial 12 88941) = some ⟨12, 2, 0, 674713, 88941, 3697, 65536⟩ := by
  decide +kernel

theorem context_12_88941_674713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88941 ⟨674713, by decide⟩ :=
  accepted_of_selected 12 88941 ⟨674713, by decide⟩ ⟨12, 2, 0, 674713, 88941, 3697, 65536⟩
    (by decide) selected_cut_26688

theorem selected_cut_26689 : selected 9 ⟨674749, by decide⟩
    (prefixPartial 12 88942) = some ⟨12, 2, 0, 674749, 88942, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_88942_674749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88942 ⟨674749, by decide⟩ :=
  accepted_of_selected 12 88942 ⟨674749, by decide⟩ ⟨12, 2, 0, 674749, 88942, 2945, 65536⟩
    (by decide) selected_cut_26689

theorem selected_cut_26690 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 355772) = some ⟨13, 1, 0, 3444, 355772, 1, 16384⟩ := by
  decide +kernel

theorem context_13_355772_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355772 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 355772 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 355772, 1, 16384⟩
    (by decide) selected_cut_26690

theorem selected_cut_26691 : selected 8 ⟨674763, by decide⟩
    (prefixPartial 13 355773) = some ⟨13, 2, 0, 674763, 355773, 821, 16384⟩ := by
  decide +kernel

theorem context_13_355773_674763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355773 ⟨674763, by decide⟩ :=
  accepted_of_selected 13 355773 ⟨674763, by decide⟩ ⟨13, 2, 0, 674763, 355773, 821, 16384⟩
    (by decide) selected_cut_26691

theorem selected_cut_26692 : selected 8 ⟨674785, by decide⟩
    (prefixPartial 13 355774) = some ⟨13, 2, 0, 674785, 355774, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_355774_674785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355774 ⟨674785, by decide⟩ :=
  accepted_of_selected 13 355774 ⟨674785, by decide⟩ ⟨13, 2, 0, 674785, 355774, 2305, 16384⟩
    (by decide) selected_cut_26692

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
