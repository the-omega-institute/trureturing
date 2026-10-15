/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover215
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_4634_531059 : frontier 11 ⟨531059, by decide⟩
    (prefixCache 10 4634) (prefixPartial 10 4634) = false := by
  decide +kernel

theorem node_context_10_4634_531059 : EJMOriginalGlobalDAGData.nodes 11 ⟨531059, by decide⟩ =
    .split (coordinate 10) (![⟨530840, by decide⟩,⟨530926, by decide⟩,⟨530997, by decide⟩,⟨531058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4634_531059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4634 ⟨531059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4634
    ⟨531059, by decide⟩ (by decide) (![⟨530840, by decide⟩,⟨530926, by decide⟩,⟨530997, by decide⟩,⟨531058, by decide⟩]) unmarked_context_10_4634_531059 node_context_10_4634_531059
  intro a
  fin_cases a
  · exact context_11_18536_530840
  · exact context_11_18537_530926
  · exact context_11_18538_530997
  · exact context_11_18539_531058

theorem selected_cut_20739 : selected 9 ⟨531072, by decide⟩
    (prefixPartial 12 74160) = some ⟨12, 2, 0, 531072, 74160, 1009, 65536⟩ := by
  decide +kernel

theorem context_12_74160_531072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74160 ⟨531072, by decide⟩ :=
  accepted_of_selected 12 74160 ⟨531072, by decide⟩ ⟨12, 2, 0, 531072, 74160, 1009, 65536⟩
    (by decide) selected_cut_20739

theorem selected_cut_20740 : selected 9 ⟨531084, by decide⟩
    (prefixPartial 12 74161) = some ⟨12, 2, 0, 531084, 74161, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_74161_531084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74161 ⟨531084, by decide⟩ :=
  accepted_of_selected 12 74161 ⟨531084, by decide⟩ ⟨12, 2, 0, 531084, 74161, 1069, 65536⟩
    (by decide) selected_cut_20740

theorem selected_cut_20741 : selected 9 ⟨531100, by decide⟩
    (prefixPartial 12 74162) = some ⟨12, 2, 0, 531100, 74162, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_74162_531100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74162 ⟨531100, by decide⟩ :=
  accepted_of_selected 12 74162 ⟨531100, by decide⟩ ⟨12, 2, 0, 531100, 74162, 1149, 65536⟩
    (by decide) selected_cut_20741

theorem selected_cut_20742 : selected 9 ⟨531110, by decide⟩
    (prefixPartial 12 74163) = some ⟨12, 2, 0, 531110, 74163, 997, 65536⟩ := by
  decide +kernel

theorem context_12_74163_531110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74163 ⟨531110, by decide⟩ :=
  accepted_of_selected 12 74163 ⟨531110, by decide⟩ ⟨12, 2, 0, 531110, 74163, 997, 65536⟩
    (by decide) selected_cut_20742

theorem unmarked_context_11_18540_531111 : frontier 10 ⟨531111, by decide⟩
    (prefixCache 11 18540) (prefixPartial 11 18540) = false := by
  decide +kernel

theorem node_context_11_18540_531111 : EJMOriginalGlobalDAGData.nodes 10 ⟨531111, by decide⟩ =
    .split (coordinate 11) (![⟨531072, by decide⟩,⟨531084, by decide⟩,⟨531100, by decide⟩,⟨531110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18540_531111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18540 ⟨531111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18540
    ⟨531111, by decide⟩ (by decide) (![⟨531072, by decide⟩,⟨531084, by decide⟩,⟨531100, by decide⟩,⟨531110, by decide⟩]) unmarked_context_11_18540_531111 node_context_11_18540_531111
  intro a
  fin_cases a
  · exact context_12_74160_531072
  · exact context_12_74161_531084
  · exact context_12_74162_531100
  · exact context_12_74163_531110

theorem selected_cut_20743 : selected 9 ⟨531123, by decide⟩
    (prefixPartial 12 74164) = some ⟨12, 2, 0, 531123, 74164, 1073, 65536⟩ := by
  decide +kernel

theorem context_12_74164_531123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74164 ⟨531123, by decide⟩ :=
  accepted_of_selected 12 74164 ⟨531123, by decide⟩ ⟨12, 2, 0, 531123, 74164, 1073, 65536⟩
    (by decide) selected_cut_20743

theorem selected_cut_20744 : selected 9 ⟨531147, by decide⟩
    (prefixPartial 12 74165) = some ⟨12, 2, 0, 531147, 74165, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_74165_531147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74165 ⟨531147, by decide⟩ :=
  accepted_of_selected 12 74165 ⟨531147, by decide⟩ ⟨12, 2, 0, 531147, 74165, 1765, 65536⟩
    (by decide) selected_cut_20744

theorem selected_cut_20745 : selected 9 ⟨531159, by decide⟩
    (prefixPartial 12 74166) = some ⟨12, 2, 0, 531159, 74166, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_74166_531159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74166 ⟨531159, by decide⟩ :=
  accepted_of_selected 12 74166 ⟨531159, by decide⟩ ⟨12, 2, 0, 531159, 74166, 1201, 65536⟩
    (by decide) selected_cut_20745

theorem selected_cut_20746 : selected 9 ⟨531170, by decide⟩
    (prefixPartial 12 74167) = some ⟨12, 2, 0, 531170, 74167, 1009, 65536⟩ := by
  decide +kernel

theorem context_12_74167_531170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74167 ⟨531170, by decide⟩ :=
  accepted_of_selected 12 74167 ⟨531170, by decide⟩ ⟨12, 2, 0, 531170, 74167, 1009, 65536⟩
    (by decide) selected_cut_20746

theorem unmarked_context_11_18541_531171 : frontier 10 ⟨531171, by decide⟩
    (prefixCache 11 18541) (prefixPartial 11 18541) = false := by
  decide +kernel

theorem node_context_11_18541_531171 : EJMOriginalGlobalDAGData.nodes 10 ⟨531171, by decide⟩ =
    .split (coordinate 11) (![⟨531123, by decide⟩,⟨531147, by decide⟩,⟨531159, by decide⟩,⟨531170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18541_531171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18541 ⟨531171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18541
    ⟨531171, by decide⟩ (by decide) (![⟨531123, by decide⟩,⟨531147, by decide⟩,⟨531159, by decide⟩,⟨531170, by decide⟩]) unmarked_context_11_18541_531171 node_context_11_18541_531171
  intro a
  fin_cases a
  · exact context_12_74164_531123
  · exact context_12_74165_531147
  · exact context_12_74166_531159
  · exact context_12_74167_531170

theorem selected_cut_20747 : selected 10 ⟨531214, by decide⟩
    (prefixPartial 11 18542) = some ⟨11, 2, 0, 531214, 18542, 3961, 262144⟩ := by
  decide +kernel

theorem context_11_18542_531214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18542 ⟨531214, by decide⟩ :=
  accepted_of_selected 11 18542 ⟨531214, by decide⟩ ⟨11, 2, 0, 531214, 18542, 3961, 262144⟩
    (by decide) selected_cut_20747

theorem selected_cut_20748 : selected 10 ⟨531254, by decide⟩
    (prefixPartial 11 18543) = some ⟨11, 2, 0, 531254, 18543, 3941, 262144⟩ := by
  decide +kernel

theorem context_11_18543_531254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18543 ⟨531254, by decide⟩ :=
  accepted_of_selected 11 18543 ⟨531254, by decide⟩ ⟨11, 2, 0, 531254, 18543, 3941, 262144⟩
    (by decide) selected_cut_20748

theorem unmarked_context_10_4635_531255 : frontier 11 ⟨531255, by decide⟩
    (prefixCache 10 4635) (prefixPartial 10 4635) = false := by
  decide +kernel

theorem node_context_10_4635_531255 : EJMOriginalGlobalDAGData.nodes 11 ⟨531255, by decide⟩ =
    .split (coordinate 10) (![⟨531111, by decide⟩,⟨531171, by decide⟩,⟨531214, by decide⟩,⟨531254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4635_531255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4635 ⟨531255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4635
    ⟨531255, by decide⟩ (by decide) (![⟨531111, by decide⟩,⟨531171, by decide⟩,⟨531214, by decide⟩,⟨531254, by decide⟩]) unmarked_context_10_4635_531255 node_context_10_4635_531255
  intro a
  fin_cases a
  · exact context_11_18540_531111
  · exact context_11_18541_531171
  · exact context_11_18542_531214
  · exact context_11_18543_531254

theorem unmarked_context_9_1158_531256 : frontier 12 ⟨531256, by decide⟩
    (prefixCache 9 1158) (prefixPartial 9 1158) = false := by
  decide +kernel

theorem node_context_9_1158_531256 : EJMOriginalGlobalDAGData.nodes 12 ⟨531256, by decide⟩ =
    .split (coordinate 9) (![⟨530449, by decide⟩,⟨530774, by decide⟩,⟨531059, by decide⟩,⟨531255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1158_531256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1158 ⟨531256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1158
    ⟨531256, by decide⟩ (by decide) (![⟨530449, by decide⟩,⟨530774, by decide⟩,⟨531059, by decide⟩,⟨531255, by decide⟩]) unmarked_context_9_1158_531256 node_context_9_1158_531256
  intro a
  fin_cases a
  · exact context_10_4632_530449
  · exact context_10_4633_530774
  · exact context_10_4634_531059
  · exact context_10_4635_531255

theorem selected_cut_20749 : selected 10 ⟨531277, by decide⟩
    (prefixPartial 11 18544) = some ⟨11, 2, 0, 531277, 18544, 1981, 262144⟩ := by
  decide +kernel

theorem context_11_18544_531277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18544 ⟨531277, by decide⟩ :=
  accepted_of_selected 11 18544 ⟨531277, by decide⟩ ⟨11, 2, 0, 531277, 18544, 1981, 262144⟩
    (by decide) selected_cut_20749

theorem selected_cut_20750 : selected 10 ⟨531308, by decide⟩
    (prefixPartial 11 18545) = some ⟨11, 2, 0, 531308, 18545, 3037, 262144⟩ := by
  decide +kernel

theorem context_11_18545_531308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18545 ⟨531308, by decide⟩ :=
  accepted_of_selected 11 18545 ⟨531308, by decide⟩ ⟨11, 2, 0, 531308, 18545, 3037, 262144⟩
    (by decide) selected_cut_20750

theorem selected_cut_20751 : selected 10 ⟨531337, by decide⟩
    (prefixPartial 11 18546) = some ⟨11, 2, 0, 531337, 18546, 2601, 262144⟩ := by
  decide +kernel

theorem context_11_18546_531337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18546 ⟨531337, by decide⟩ :=
  accepted_of_selected 11 18546 ⟨531337, by decide⟩ ⟨11, 2, 0, 531337, 18546, 2601, 262144⟩
    (by decide) selected_cut_20751

theorem selected_cut_20752 : selected 10 ⟨531363, by decide⟩
    (prefixPartial 11 18547) = some ⟨11, 2, 0, 531363, 18547, 2721, 262144⟩ := by
  decide +kernel

theorem context_11_18547_531363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18547 ⟨531363, by decide⟩ :=
  accepted_of_selected 11 18547 ⟨531363, by decide⟩ ⟨11, 2, 0, 531363, 18547, 2721, 262144⟩
    (by decide) selected_cut_20752

theorem unmarked_context_10_4636_531364 : frontier 11 ⟨531364, by decide⟩
    (prefixCache 10 4636) (prefixPartial 10 4636) = false := by
  decide +kernel

theorem node_context_10_4636_531364 : EJMOriginalGlobalDAGData.nodes 11 ⟨531364, by decide⟩ =
    .split (coordinate 10) (![⟨531277, by decide⟩,⟨531308, by decide⟩,⟨531337, by decide⟩,⟨531363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4636_531364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4636 ⟨531364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4636
    ⟨531364, by decide⟩ (by decide) (![⟨531277, by decide⟩,⟨531308, by decide⟩,⟨531337, by decide⟩,⟨531363, by decide⟩]) unmarked_context_10_4636_531364 node_context_10_4636_531364
  intro a
  fin_cases a
  · exact context_11_18544_531277
  · exact context_11_18545_531308
  · exact context_11_18546_531337
  · exact context_11_18547_531363

theorem selected_cut_20753 : selected 10 ⟨531385, by decide⟩
    (prefixPartial 11 18548) = some ⟨11, 2, 0, 531385, 18548, 2209, 262144⟩ := by
  decide +kernel

theorem context_11_18548_531385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18548 ⟨531385, by decide⟩ :=
  accepted_of_selected 11 18548 ⟨531385, by decide⟩ ⟨11, 2, 0, 531385, 18548, 2209, 262144⟩
    (by decide) selected_cut_20753

theorem selected_cut_20754 : selected 10 ⟨531400, by decide⟩
    (prefixPartial 11 18549) = some ⟨11, 2, 0, 531400, 18549, 1697, 262144⟩ := by
  decide +kernel

theorem context_11_18549_531400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18549 ⟨531400, by decide⟩ :=
  accepted_of_selected 11 18549 ⟨531400, by decide⟩ ⟨11, 2, 0, 531400, 18549, 1697, 262144⟩
    (by decide) selected_cut_20754

theorem selected_cut_20755 : selected 10 ⟨531419, by decide⟩
    (prefixPartial 11 18550) = some ⟨11, 2, 0, 531419, 18550, 1813, 262144⟩ := by
  decide +kernel

theorem context_11_18550_531419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18550 ⟨531419, by decide⟩ :=
  accepted_of_selected 11 18550 ⟨531419, by decide⟩ ⟨11, 2, 0, 531419, 18550, 1813, 262144⟩
    (by decide) selected_cut_20755

theorem selected_cut_20756 : selected 10 ⟨531443, by decide⟩
    (prefixPartial 11 18551) = some ⟨11, 2, 0, 531443, 18551, 1965, 262144⟩ := by
  decide +kernel

theorem context_11_18551_531443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18551 ⟨531443, by decide⟩ :=
  accepted_of_selected 11 18551 ⟨531443, by decide⟩ ⟨11, 2, 0, 531443, 18551, 1965, 262144⟩
    (by decide) selected_cut_20756

theorem unmarked_context_10_4637_531444 : frontier 11 ⟨531444, by decide⟩
    (prefixCache 10 4637) (prefixPartial 10 4637) = false := by
  decide +kernel

theorem node_context_10_4637_531444 : EJMOriginalGlobalDAGData.nodes 11 ⟨531444, by decide⟩ =
    .split (coordinate 10) (![⟨531385, by decide⟩,⟨531400, by decide⟩,⟨531419, by decide⟩,⟨531443, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4637_531444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4637 ⟨531444, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4637
    ⟨531444, by decide⟩ (by decide) (![⟨531385, by decide⟩,⟨531400, by decide⟩,⟨531419, by decide⟩,⟨531443, by decide⟩]) unmarked_context_10_4637_531444 node_context_10_4637_531444
  intro a
  fin_cases a
  · exact context_11_18548_531385
  · exact context_11_18549_531400
  · exact context_11_18550_531419
  · exact context_11_18551_531443

theorem selected_cut_20757 : selected 10 ⟨531458, by decide⟩
    (prefixPartial 11 18552) = some ⟨11, 2, 0, 531458, 18552, 1309, 262144⟩ := by
  decide +kernel

theorem context_11_18552_531458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18552 ⟨531458, by decide⟩ :=
  accepted_of_selected 11 18552 ⟨531458, by decide⟩ ⟨11, 2, 0, 531458, 18552, 1309, 262144⟩
    (by decide) selected_cut_20757

theorem selected_cut_20758 : selected 10 ⟨531477, by decide⟩
    (prefixPartial 11 18553) = some ⟨11, 2, 0, 531477, 18553, 1525, 262144⟩ := by
  decide +kernel

theorem context_11_18553_531477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18553 ⟨531477, by decide⟩ :=
  accepted_of_selected 11 18553 ⟨531477, by decide⟩ ⟨11, 2, 0, 531477, 18553, 1525, 262144⟩
    (by decide) selected_cut_20758

theorem selected_cut_20759 : selected 10 ⟨531494, by decide⟩
    (prefixPartial 11 18554) = some ⟨11, 2, 0, 531494, 18554, 1065, 262144⟩ := by
  decide +kernel

theorem context_11_18554_531494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18554 ⟨531494, by decide⟩ :=
  accepted_of_selected 11 18554 ⟨531494, by decide⟩ ⟨11, 2, 0, 531494, 18554, 1065, 262144⟩
    (by decide) selected_cut_20759

theorem selected_cut_20760 : selected 10 ⟨531507, by decide⟩
    (prefixPartial 11 18555) = some ⟨11, 2, 0, 531507, 18555, 957, 262144⟩ := by
  decide +kernel

theorem context_11_18555_531507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18555 ⟨531507, by decide⟩ :=
  accepted_of_selected 11 18555 ⟨531507, by decide⟩ ⟨11, 2, 0, 531507, 18555, 957, 262144⟩
    (by decide) selected_cut_20760

theorem unmarked_context_10_4638_531508 : frontier 11 ⟨531508, by decide⟩
    (prefixCache 10 4638) (prefixPartial 10 4638) = false := by
  decide +kernel

theorem node_context_10_4638_531508 : EJMOriginalGlobalDAGData.nodes 11 ⟨531508, by decide⟩ =
    .split (coordinate 10) (![⟨531458, by decide⟩,⟨531477, by decide⟩,⟨531494, by decide⟩,⟨531507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4638_531508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4638 ⟨531508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4638
    ⟨531508, by decide⟩ (by decide) (![⟨531458, by decide⟩,⟨531477, by decide⟩,⟨531494, by decide⟩,⟨531507, by decide⟩]) unmarked_context_10_4638_531508 node_context_10_4638_531508
  intro a
  fin_cases a
  · exact context_11_18552_531458
  · exact context_11_18553_531477
  · exact context_11_18554_531494
  · exact context_11_18555_531507

theorem selected_cut_20761 : selected 11 ⟨531551, by decide⟩
    (prefixPartial 10 4639) = some ⟨10, 2, 0, 531551, 4639, 1693, 1048576⟩ := by
  decide +kernel

theorem context_10_4639_531551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4639 ⟨531551, by decide⟩ :=
  accepted_of_selected 10 4639 ⟨531551, by decide⟩ ⟨10, 2, 0, 531551, 4639, 1693, 1048576⟩
    (by decide) selected_cut_20761

theorem unmarked_context_9_1159_531552 : frontier 12 ⟨531552, by decide⟩
    (prefixCache 9 1159) (prefixPartial 9 1159) = false := by
  decide +kernel

theorem node_context_9_1159_531552 : EJMOriginalGlobalDAGData.nodes 12 ⟨531552, by decide⟩ =
    .split (coordinate 9) (![⟨531364, by decide⟩,⟨531444, by decide⟩,⟨531508, by decide⟩,⟨531551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1159_531552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1159 ⟨531552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1159
    ⟨531552, by decide⟩ (by decide) (![⟨531364, by decide⟩,⟨531444, by decide⟩,⟨531508, by decide⟩,⟨531551, by decide⟩]) unmarked_context_9_1159_531552 node_context_9_1159_531552
  intro a
  fin_cases a
  · exact context_10_4636_531364
  · exact context_10_4637_531444
  · exact context_10_4638_531508
  · exact context_10_4639_531551

theorem unmarked_context_8_289_531553 : frontier 13 ⟨531553, by decide⟩
    (prefixCache 8 289) (prefixPartial 8 289) = false := by
  decide +kernel

theorem node_context_8_289_531553 : EJMOriginalGlobalDAGData.nodes 13 ⟨531553, by decide⟩ =
    .split (coordinate 8) (![⟨527582, by decide⟩,⟨530060, by decide⟩,⟨531256, by decide⟩,⟨531552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_289_531553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 289 ⟨531553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 289
    ⟨531553, by decide⟩ (by decide) (![⟨527582, by decide⟩,⟨530060, by decide⟩,⟨531256, by decide⟩,⟨531552, by decide⟩]) unmarked_context_8_289_531553 node_context_8_289_531553
  intro a
  fin_cases a
  · exact context_9_1156_527582
  · exact context_9_1157_530060
  · exact context_9_1158_531256
  · exact context_9_1159_531552

theorem selected_cut_20762 : selected 13 ⟨158379, by decide⟩
    (prefixPartial 8 290) = some ⟨8, 1, 0, 158379, 290, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_290_158379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 290 ⟨158379, by decide⟩ :=
  accepted_of_selected 8 290 ⟨158379, by decide⟩ ⟨8, 1, 0, 158379, 290, 1, 16777216⟩
    (by decide) selected_cut_20762

theorem selected_cut_20763 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 18624) = some ⟨11, 1, 0, 434745, 18624, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18624_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18624 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 18624 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 18624, 1, 262144⟩
    (by decide) selected_cut_20763

theorem selected_cut_20764 : selected 10 ⟨531653, by decide⟩
    (prefixPartial 11 18625) = some ⟨11, 2, 0, 531653, 18625, 2485, 262144⟩ := by
  decide +kernel

theorem context_11_18625_531653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18625 ⟨531653, by decide⟩ :=
  accepted_of_selected 11 18625 ⟨531653, by decide⟩ ⟨11, 2, 0, 531653, 18625, 2485, 262144⟩
    (by decide) selected_cut_20764

theorem selected_cut_20765 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 74504) = some ⟨12, 1, 0, 4595, 74504, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74504_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74504 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 74504 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 74504, 1, 65536⟩
    (by decide) selected_cut_20765

theorem selected_cut_20766 : selected 8 ⟨531731, by decide⟩
    (prefixPartial 13 298020) = some ⟨13, 2, 0, 531731, 298020, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_298020_531731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298020 ⟨531731, by decide⟩ :=
  accepted_of_selected 13 298020 ⟨531731, by decide⟩ ⟨13, 2, 0, 531731, 298020, 2613, 16384⟩
    (by decide) selected_cut_20766

theorem selected_cut_20767 : selected 8 ⟨531780, by decide⟩
    (prefixPartial 13 298021) = some ⟨13, 2, 0, 531780, 298021, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_298021_531780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298021 ⟨531780, by decide⟩ :=
  accepted_of_selected 13 298021 ⟨531780, by decide⟩ ⟨13, 2, 0, 531780, 298021, 1449, 16384⟩
    (by decide) selected_cut_20767

theorem selected_cut_20768 : selected 8 ⟨531814, by decide⟩
    (prefixPartial 13 298022) = some ⟨13, 2, 0, 531814, 298022, 697, 16384⟩ := by
  decide +kernel

theorem context_13_298022_531814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298022 ⟨531814, by decide⟩ :=
  accepted_of_selected 13 298022 ⟨531814, by decide⟩ ⟨13, 2, 0, 531814, 298022, 697, 16384⟩
    (by decide) selected_cut_20768

theorem selected_cut_20769 : selected 8 ⟨531816, by decide⟩
    (prefixPartial 13 298023) = some ⟨13, 2, 0, 531816, 298023, 97, 16384⟩ := by
  decide +kernel

theorem context_13_298023_531816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298023 ⟨531816, by decide⟩ :=
  accepted_of_selected 13 298023 ⟨531816, by decide⟩ ⟨13, 2, 0, 531816, 298023, 97, 16384⟩
    (by decide) selected_cut_20769

theorem unmarked_context_12_74505_531817 : frontier 9 ⟨531817, by decide⟩
    (prefixCache 12 74505) (prefixPartial 12 74505) = false := by
  decide +kernel

theorem node_context_12_74505_531817 : EJMOriginalGlobalDAGData.nodes 9 ⟨531817, by decide⟩ =
    .split (coordinate 12) (![⟨531731, by decide⟩,⟨531780, by decide⟩,⟨531814, by decide⟩,⟨531816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74505_531817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74505 ⟨531817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74505
    ⟨531817, by decide⟩ (by decide) (![⟨531731, by decide⟩,⟨531780, by decide⟩,⟨531814, by decide⟩,⟨531816, by decide⟩]) unmarked_context_12_74505_531817 node_context_12_74505_531817
  intro a
  fin_cases a
  · exact context_13_298020_531731
  · exact context_13_298021_531780
  · exact context_13_298022_531814
  · exact context_13_298023_531816

theorem selected_cut_20770 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 74506) = some ⟨12, 1, 0, 4595, 74506, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74506_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74506 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 74506 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 74506, 1, 65536⟩
    (by decide) selected_cut_20770

theorem selected_cut_20771 : selected 9 ⟨508415, by decide⟩
    (prefixPartial 12 74507) = some ⟨12, 1, 0, 508415, 74507, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74507_508415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74507 ⟨508415, by decide⟩ :=
  accepted_of_selected 12 74507 ⟨508415, by decide⟩ ⟨12, 1, 0, 508415, 74507, 1, 65536⟩
    (by decide) selected_cut_20771

theorem unmarked_context_11_18626_531818 : frontier 10 ⟨531818, by decide⟩
    (prefixCache 11 18626) (prefixPartial 11 18626) = false := by
  decide +kernel

theorem node_context_11_18626_531818 : EJMOriginalGlobalDAGData.nodes 10 ⟨531818, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨531817, by decide⟩,⟨4595, by decide⟩,⟨508415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18626_531818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18626 ⟨531818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18626
    ⟨531818, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨531817, by decide⟩,⟨4595, by decide⟩,⟨508415, by decide⟩]) unmarked_context_11_18626_531818 node_context_11_18626_531818
  intro a
  fin_cases a
  · exact context_12_74504_4595
  · exact context_12_74505_531817
  · exact context_12_74506_4595
  · exact context_12_74507_508415

theorem selected_cut_20772 : selected 10 ⟨518279, by decide⟩
    (prefixPartial 11 18627) = some ⟨11, 2, 0, 518279, 18627, 5, 262144⟩ := by
  decide +kernel

theorem context_11_18627_518279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18627 ⟨518279, by decide⟩ :=
  accepted_of_selected 11 18627 ⟨518279, by decide⟩ ⟨11, 2, 0, 518279, 18627, 5, 262144⟩
    (by decide) selected_cut_20772

theorem unmarked_context_10_4656_531819 : frontier 11 ⟨531819, by decide⟩
    (prefixCache 10 4656) (prefixPartial 10 4656) = false := by
  decide +kernel

theorem node_context_10_4656_531819 : EJMOriginalGlobalDAGData.nodes 11 ⟨531819, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨531653, by decide⟩,⟨531818, by decide⟩,⟨518279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4656_531819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4656 ⟨531819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4656
    ⟨531819, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨531653, by decide⟩,⟨531818, by decide⟩,⟨518279, by decide⟩]) unmarked_context_10_4656_531819 node_context_10_4656_531819
  intro a
  fin_cases a
  · exact context_11_18624_434745
  · exact context_11_18625_531653
  · exact context_11_18626_531818
  · exact context_11_18627_518279

theorem selected_cut_20773 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 74512) = some ⟨12, 1, 0, 435160, 74512, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74512_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74512 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 74512 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 74512, 1, 65536⟩
    (by decide) selected_cut_20773

theorem selected_cut_20774 : selected 8 ⟨531855, by decide⟩
    (prefixPartial 13 298052) = some ⟨13, 2, 0, 531855, 298052, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_298052_531855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298052 ⟨531855, by decide⟩ :=
  accepted_of_selected 13 298052 ⟨531855, by decide⟩ ⟨13, 2, 0, 531855, 298052, 1921, 16384⟩
    (by decide) selected_cut_20774

theorem selected_cut_20775 : selected 8 ⟨531877, by decide⟩
    (prefixPartial 13 298053) = some ⟨13, 2, 0, 531877, 298053, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_298053_531877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298053 ⟨531877, by decide⟩ :=
  accepted_of_selected 13 298053 ⟨531877, by decide⟩ ⟨13, 2, 0, 531877, 298053, 1557, 16384⟩
    (by decide) selected_cut_20775

theorem selected_cut_20776 : selected 8 ⟨531900, by decide⟩
    (prefixPartial 13 298054) = some ⟨13, 2, 0, 531900, 298054, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_298054_531900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298054 ⟨531900, by decide⟩ :=
  accepted_of_selected 13 298054 ⟨531900, by decide⟩ ⟨13, 2, 0, 531900, 298054, 1821, 16384⟩
    (by decide) selected_cut_20776

theorem selected_cut_20777 : selected 8 ⟨531907, by decide⟩
    (prefixPartial 13 298055) = some ⟨13, 2, 0, 531907, 298055, 629, 16384⟩ := by
  decide +kernel

theorem context_13_298055_531907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298055 ⟨531907, by decide⟩ :=
  accepted_of_selected 13 298055 ⟨531907, by decide⟩ ⟨13, 2, 0, 531907, 298055, 629, 16384⟩
    (by decide) selected_cut_20777

theorem unmarked_context_12_74513_531908 : frontier 9 ⟨531908, by decide⟩
    (prefixCache 12 74513) (prefixPartial 12 74513) = false := by
  decide +kernel

theorem node_context_12_74513_531908 : EJMOriginalGlobalDAGData.nodes 9 ⟨531908, by decide⟩ =
    .split (coordinate 12) (![⟨531855, by decide⟩,⟨531877, by decide⟩,⟨531900, by decide⟩,⟨531907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74513_531908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74513 ⟨531908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74513
    ⟨531908, by decide⟩ (by decide) (![⟨531855, by decide⟩,⟨531877, by decide⟩,⟨531900, by decide⟩,⟨531907, by decide⟩]) unmarked_context_12_74513_531908 node_context_12_74513_531908
  intro a
  fin_cases a
  · exact context_13_298052_531855
  · exact context_13_298053_531877
  · exact context_13_298054_531900
  · exact context_13_298055_531907

theorem selected_cut_20778 : selected 8 ⟨531931, by decide⟩
    (prefixPartial 13 298056) = some ⟨13, 2, 0, 531931, 298056, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_298056_531931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298056 ⟨531931, by decide⟩ :=
  accepted_of_selected 13 298056 ⟨531931, by decide⟩ ⟨13, 2, 0, 531931, 298056, 1453, 16384⟩
    (by decide) selected_cut_20778

theorem selected_cut_20779 : selected 8 ⟨531954, by decide⟩
    (prefixPartial 13 298057) = some ⟨13, 2, 0, 531954, 298057, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_298057_531954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298057 ⟨531954, by decide⟩ :=
  accepted_of_selected 13 298057 ⟨531954, by decide⟩ ⟨13, 2, 0, 531954, 298057, 2001, 16384⟩
    (by decide) selected_cut_20779

theorem selected_cut_20780 : selected 8 ⟨531974, by decide⟩
    (prefixPartial 13 298058) = some ⟨13, 2, 0, 531974, 298058, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_298058_531974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298058 ⟨531974, by decide⟩ :=
  accepted_of_selected 13 298058 ⟨531974, by decide⟩ ⟨13, 2, 0, 531974, 298058, 1269, 16384⟩
    (by decide) selected_cut_20780

theorem selected_cut_20781 : selected 8 ⟨531979, by decide⟩
    (prefixPartial 13 298059) = some ⟨13, 2, 0, 531979, 298059, 609, 16384⟩ := by
  decide +kernel

theorem context_13_298059_531979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298059 ⟨531979, by decide⟩ :=
  accepted_of_selected 13 298059 ⟨531979, by decide⟩ ⟨13, 2, 0, 531979, 298059, 609, 16384⟩
    (by decide) selected_cut_20781

theorem unmarked_context_12_74514_531980 : frontier 9 ⟨531980, by decide⟩
    (prefixCache 12 74514) (prefixPartial 12 74514) = false := by
  decide +kernel

theorem node_context_12_74514_531980 : EJMOriginalGlobalDAGData.nodes 9 ⟨531980, by decide⟩ =
    .split (coordinate 12) (![⟨531931, by decide⟩,⟨531954, by decide⟩,⟨531974, by decide⟩,⟨531979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74514_531980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74514 ⟨531980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74514
    ⟨531980, by decide⟩ (by decide) (![⟨531931, by decide⟩,⟨531954, by decide⟩,⟨531974, by decide⟩,⟨531979, by decide⟩]) unmarked_context_12_74514_531980 node_context_12_74514_531980
  intro a
  fin_cases a
  · exact context_13_298056_531931
  · exact context_13_298057_531954
  · exact context_13_298058_531974
  · exact context_13_298059_531979

theorem selected_cut_20782 : selected 8 ⟨532006, by decide⟩
    (prefixPartial 13 298060) = some ⟨13, 2, 0, 532006, 298060, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_298060_532006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298060 ⟨532006, by decide⟩ :=
  accepted_of_selected 13 298060 ⟨532006, by decide⟩ ⟨13, 2, 0, 532006, 298060, 1217, 16384⟩
    (by decide) selected_cut_20782

theorem selected_cut_20783 : selected 8 ⟨532027, by decide⟩
    (prefixPartial 13 298061) = some ⟨13, 2, 0, 532027, 298061, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_298061_532027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298061 ⟨532027, by decide⟩ :=
  accepted_of_selected 13 298061 ⟨532027, by decide⟩ ⟨13, 2, 0, 532027, 298061, 1829, 16384⟩
    (by decide) selected_cut_20783

theorem selected_cut_20784 : selected 8 ⟨532048, by decide⟩
    (prefixPartial 13 298062) = some ⟨13, 2, 0, 532048, 298062, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_298062_532048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298062 ⟨532048, by decide⟩ :=
  accepted_of_selected 13 298062 ⟨532048, by decide⟩ ⟨13, 2, 0, 532048, 298062, 1397, 16384⟩
    (by decide) selected_cut_20784

theorem selected_cut_20785 : selected 8 ⟨532054, by decide⟩
    (prefixPartial 13 298063) = some ⟨13, 2, 0, 532054, 298063, 489, 16384⟩ := by
  decide +kernel

theorem context_13_298063_532054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298063 ⟨532054, by decide⟩ :=
  accepted_of_selected 13 298063 ⟨532054, by decide⟩ ⟨13, 2, 0, 532054, 298063, 489, 16384⟩
    (by decide) selected_cut_20785

theorem unmarked_context_12_74515_532055 : frontier 9 ⟨532055, by decide⟩
    (prefixCache 12 74515) (prefixPartial 12 74515) = false := by
  decide +kernel

theorem node_context_12_74515_532055 : EJMOriginalGlobalDAGData.nodes 9 ⟨532055, by decide⟩ =
    .split (coordinate 12) (![⟨532006, by decide⟩,⟨532027, by decide⟩,⟨532048, by decide⟩,⟨532054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74515_532055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74515 ⟨532055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74515
    ⟨532055, by decide⟩ (by decide) (![⟨532006, by decide⟩,⟨532027, by decide⟩,⟨532048, by decide⟩,⟨532054, by decide⟩]) unmarked_context_12_74515_532055 node_context_12_74515_532055
  intro a
  fin_cases a
  · exact context_13_298060_532006
  · exact context_13_298061_532027
  · exact context_13_298062_532048
  · exact context_13_298063_532054

theorem unmarked_context_11_18628_532056 : frontier 10 ⟨532056, by decide⟩
    (prefixCache 11 18628) (prefixPartial 11 18628) = false := by
  decide +kernel

theorem node_context_11_18628_532056 : EJMOriginalGlobalDAGData.nodes 10 ⟨532056, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨531908, by decide⟩,⟨531980, by decide⟩,⟨532055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18628_532056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18628 ⟨532056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18628
    ⟨532056, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨531908, by decide⟩,⟨531980, by decide⟩,⟨532055, by decide⟩]) unmarked_context_11_18628_532056 node_context_11_18628_532056
  intro a
  fin_cases a
  · exact context_12_74512_435160
  · exact context_12_74513_531908
  · exact context_12_74514_531980
  · exact context_12_74515_532055

theorem selected_cut_20786 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 74516) = some ⟨12, 1, 0, 435160, 74516, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74516_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74516 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 74516 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 74516, 1, 65536⟩
    (by decide) selected_cut_20786

theorem selected_cut_20787 : selected 8 ⟨532103, by decide⟩
    (prefixPartial 13 298068) = some ⟨13, 2, 0, 532103, 298068, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_298068_532103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298068 ⟨532103, by decide⟩ :=
  accepted_of_selected 13 298068 ⟨532103, by decide⟩ ⟨13, 2, 0, 532103, 298068, 2149, 16384⟩
    (by decide) selected_cut_20787

theorem selected_cut_20788 : selected 8 ⟨532125, by decide⟩
    (prefixPartial 13 298069) = some ⟨13, 2, 0, 532125, 298069, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_298069_532125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298069 ⟨532125, by decide⟩ :=
  accepted_of_selected 13 298069 ⟨532125, by decide⟩ ⟨13, 2, 0, 532125, 298069, 1721, 16384⟩
    (by decide) selected_cut_20788

theorem selected_cut_20789 : selected 8 ⟨532153, by decide⟩
    (prefixPartial 13 298070) = some ⟨13, 2, 0, 532153, 298070, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_298070_532153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298070 ⟨532153, by decide⟩ :=
  accepted_of_selected 13 298070 ⟨532153, by decide⟩ ⟨13, 2, 0, 532153, 298070, 2129, 16384⟩
    (by decide) selected_cut_20789

theorem selected_cut_20790 : selected 8 ⟨532161, by decide⟩
    (prefixPartial 13 298071) = some ⟨13, 2, 0, 532161, 298071, 777, 16384⟩ := by
  decide +kernel

theorem context_13_298071_532161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298071 ⟨532161, by decide⟩ :=
  accepted_of_selected 13 298071 ⟨532161, by decide⟩ ⟨13, 2, 0, 532161, 298071, 777, 16384⟩
    (by decide) selected_cut_20790

theorem unmarked_context_12_74517_532162 : frontier 9 ⟨532162, by decide⟩
    (prefixCache 12 74517) (prefixPartial 12 74517) = false := by
  decide +kernel

theorem node_context_12_74517_532162 : EJMOriginalGlobalDAGData.nodes 9 ⟨532162, by decide⟩ =
    .split (coordinate 12) (![⟨532103, by decide⟩,⟨532125, by decide⟩,⟨532153, by decide⟩,⟨532161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74517_532162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74517 ⟨532162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74517
    ⟨532162, by decide⟩ (by decide) (![⟨532103, by decide⟩,⟨532125, by decide⟩,⟨532153, by decide⟩,⟨532161, by decide⟩]) unmarked_context_12_74517_532162 node_context_12_74517_532162
  intro a
  fin_cases a
  · exact context_13_298068_532103
  · exact context_13_298069_532125
  · exact context_13_298070_532153
  · exact context_13_298071_532161

theorem selected_cut_20791 : selected 8 ⟨532205, by decide⟩
    (prefixPartial 13 298072) = some ⟨13, 2, 0, 532205, 298072, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_298072_532205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298072 ⟨532205, by decide⟩ :=
  accepted_of_selected 13 298072 ⟨532205, by decide⟩ ⟨13, 2, 0, 532205, 298072, 1841, 16384⟩
    (by decide) selected_cut_20791

theorem selected_cut_20792 : selected 8 ⟨532227, by decide⟩
    (prefixPartial 13 298073) = some ⟨13, 2, 0, 532227, 298073, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_298073_532227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298073 ⟨532227, by decide⟩ :=
  accepted_of_selected 13 298073 ⟨532227, by decide⟩ ⟨13, 2, 0, 532227, 298073, 2369, 16384⟩
    (by decide) selected_cut_20792

theorem selected_cut_20793 : selected 8 ⟨532248, by decide⟩
    (prefixPartial 13 298074) = some ⟨13, 2, 0, 532248, 298074, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_298074_532248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298074 ⟨532248, by decide⟩ :=
  accepted_of_selected 13 298074 ⟨532248, by decide⟩ ⟨13, 2, 0, 532248, 298074, 1713, 16384⟩
    (by decide) selected_cut_20793

theorem selected_cut_20794 : selected 8 ⟨532258, by decide⟩
    (prefixPartial 13 298075) = some ⟨13, 2, 0, 532258, 298075, 841, 16384⟩ := by
  decide +kernel

theorem context_13_298075_532258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298075 ⟨532258, by decide⟩ :=
  accepted_of_selected 13 298075 ⟨532258, by decide⟩ ⟨13, 2, 0, 532258, 298075, 841, 16384⟩
    (by decide) selected_cut_20794

theorem unmarked_context_12_74518_532259 : frontier 9 ⟨532259, by decide⟩
    (prefixCache 12 74518) (prefixPartial 12 74518) = false := by
  decide +kernel

theorem node_context_12_74518_532259 : EJMOriginalGlobalDAGData.nodes 9 ⟨532259, by decide⟩ =
    .split (coordinate 12) (![⟨532205, by decide⟩,⟨532227, by decide⟩,⟨532248, by decide⟩,⟨532258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74518_532259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74518 ⟨532259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74518
    ⟨532259, by decide⟩ (by decide) (![⟨532205, by decide⟩,⟨532227, by decide⟩,⟨532248, by decide⟩,⟨532258, by decide⟩]) unmarked_context_12_74518_532259 node_context_12_74518_532259
  intro a
  fin_cases a
  · exact context_13_298072_532205
  · exact context_13_298073_532227
  · exact context_13_298074_532248
  · exact context_13_298075_532258

theorem selected_cut_20795 : selected 8 ⟨532300, by decide⟩
    (prefixPartial 13 298076) = some ⟨13, 2, 0, 532300, 298076, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_298076_532300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298076 ⟨532300, by decide⟩ :=
  accepted_of_selected 13 298076 ⟨532300, by decide⟩ ⟨13, 2, 0, 532300, 298076, 1697, 16384⟩
    (by decide) selected_cut_20795

theorem selected_cut_20796 : selected 8 ⟨532326, by decide⟩
    (prefixPartial 13 298077) = some ⟨13, 2, 0, 532326, 298077, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_298077_532326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298077 ⟨532326, by decide⟩ :=
  accepted_of_selected 13 298077 ⟨532326, by decide⟩ ⟨13, 2, 0, 532326, 298077, 2117, 16384⟩
    (by decide) selected_cut_20796

theorem selected_cut_20797 : selected 8 ⟨532355, by decide⟩
    (prefixPartial 13 298078) = some ⟨13, 2, 0, 532355, 298078, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_298078_532355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298078 ⟨532355, by decide⟩ :=
  accepted_of_selected 13 298078 ⟨532355, by decide⟩ ⟨13, 2, 0, 532355, 298078, 1845, 16384⟩
    (by decide) selected_cut_20797

theorem selected_cut_20798 : selected 8 ⟨532361, by decide⟩
    (prefixPartial 13 298079) = some ⟨13, 2, 0, 532361, 298079, 593, 16384⟩ := by
  decide +kernel

theorem context_13_298079_532361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298079 ⟨532361, by decide⟩ :=
  accepted_of_selected 13 298079 ⟨532361, by decide⟩ ⟨13, 2, 0, 532361, 298079, 593, 16384⟩
    (by decide) selected_cut_20798

theorem unmarked_context_12_74519_532362 : frontier 9 ⟨532362, by decide⟩
    (prefixCache 12 74519) (prefixPartial 12 74519) = false := by
  decide +kernel

theorem node_context_12_74519_532362 : EJMOriginalGlobalDAGData.nodes 9 ⟨532362, by decide⟩ =
    .split (coordinate 12) (![⟨532300, by decide⟩,⟨532326, by decide⟩,⟨532355, by decide⟩,⟨532361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74519_532362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74519 ⟨532362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74519
    ⟨532362, by decide⟩ (by decide) (![⟨532300, by decide⟩,⟨532326, by decide⟩,⟨532355, by decide⟩,⟨532361, by decide⟩]) unmarked_context_12_74519_532362 node_context_12_74519_532362
  intro a
  fin_cases a
  · exact context_13_298076_532300
  · exact context_13_298077_532326
  · exact context_13_298078_532355
  · exact context_13_298079_532361

theorem unmarked_context_11_18629_532363 : frontier 10 ⟨532363, by decide⟩
    (prefixCache 11 18629) (prefixPartial 11 18629) = false := by
  decide +kernel

theorem node_context_11_18629_532363 : EJMOriginalGlobalDAGData.nodes 10 ⟨532363, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨532162, by decide⟩,⟨532259, by decide⟩,⟨532362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18629_532363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18629 ⟨532363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18629
    ⟨532363, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨532162, by decide⟩,⟨532259, by decide⟩,⟨532362, by decide⟩]) unmarked_context_11_18629_532363 node_context_11_18629_532363
  intro a
  fin_cases a
  · exact context_12_74516_435160
  · exact context_12_74517_532162
  · exact context_12_74518_532259
  · exact context_12_74519_532362

theorem selected_cut_20799 : selected 8 ⟨532396, by decide⟩
    (prefixPartial 13 298080) = some ⟨13, 2, 0, 532396, 298080, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_298080_532396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298080 ⟨532396, by decide⟩ :=
  accepted_of_selected 13 298080 ⟨532396, by decide⟩ ⟨13, 2, 0, 532396, 298080, 1961, 16384⟩
    (by decide) selected_cut_20799

theorem selected_cut_20800 : selected 8 ⟨532451, by decide⟩
    (prefixPartial 13 298081) = some ⟨13, 2, 0, 532451, 298081, 3245, 16384⟩ := by
  decide +kernel

theorem context_13_298081_532451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298081 ⟨532451, by decide⟩ :=
  accepted_of_selected 13 298081 ⟨532451, by decide⟩ ⟨13, 2, 0, 532451, 298081, 3245, 16384⟩
    (by decide) selected_cut_20800

theorem selected_cut_20801 : selected 8 ⟨532481, by decide⟩
    (prefixPartial 13 298082) = some ⟨13, 2, 0, 532481, 298082, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_298082_532481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298082 ⟨532481, by decide⟩ :=
  accepted_of_selected 13 298082 ⟨532481, by decide⟩ ⟨13, 2, 0, 532481, 298082, 1913, 16384⟩
    (by decide) selected_cut_20801

theorem selected_cut_20802 : selected 8 ⟨532490, by decide⟩
    (prefixPartial 13 298083) = some ⟨13, 2, 0, 532490, 298083, 849, 16384⟩ := by
  decide +kernel

theorem context_13_298083_532490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298083 ⟨532490, by decide⟩ :=
  accepted_of_selected 13 298083 ⟨532490, by decide⟩ ⟨13, 2, 0, 532490, 298083, 849, 16384⟩
    (by decide) selected_cut_20802

theorem unmarked_context_12_74520_532491 : frontier 9 ⟨532491, by decide⟩
    (prefixCache 12 74520) (prefixPartial 12 74520) = false := by
  decide +kernel

theorem node_context_12_74520_532491 : EJMOriginalGlobalDAGData.nodes 9 ⟨532491, by decide⟩ =
    .split (coordinate 12) (![⟨532396, by decide⟩,⟨532451, by decide⟩,⟨532481, by decide⟩,⟨532490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74520_532491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74520 ⟨532491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74520
    ⟨532491, by decide⟩ (by decide) (![⟨532396, by decide⟩,⟨532451, by decide⟩,⟨532481, by decide⟩,⟨532490, by decide⟩]) unmarked_context_12_74520_532491 node_context_12_74520_532491
  intro a
  fin_cases a
  · exact context_13_298080_532396
  · exact context_13_298081_532451
  · exact context_13_298082_532481
  · exact context_13_298083_532490

theorem selected_cut_20803 : selected 8 ⟨532527, by decide⟩
    (prefixPartial 13 298084) = some ⟨13, 2, 0, 532527, 298084, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_298084_532527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298084 ⟨532527, by decide⟩ :=
  accepted_of_selected 13 298084 ⟨532527, by decide⟩ ⟨13, 2, 0, 532527, 298084, 1905, 16384⟩
    (by decide) selected_cut_20803

theorem selected_cut_20804 : selected 8 ⟨532550, by decide⟩
    (prefixPartial 13 298085) = some ⟨13, 2, 0, 532550, 298085, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_298085_532550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298085 ⟨532550, by decide⟩ :=
  accepted_of_selected 13 298085 ⟨532550, by decide⟩ ⟨13, 2, 0, 532550, 298085, 1657, 16384⟩
    (by decide) selected_cut_20804

theorem selected_cut_20805 : selected 8 ⟨532576, by decide⟩
    (prefixPartial 13 298086) = some ⟨13, 2, 0, 532576, 298086, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_298086_532576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298086 ⟨532576, by decide⟩ :=
  accepted_of_selected 13 298086 ⟨532576, by decide⟩ ⟨13, 2, 0, 532576, 298086, 1785, 16384⟩
    (by decide) selected_cut_20805

theorem selected_cut_20806 : selected 8 ⟨532585, by decide⟩
    (prefixPartial 13 298087) = some ⟨13, 2, 0, 532585, 298087, 789, 16384⟩ := by
  decide +kernel

theorem context_13_298087_532585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298087 ⟨532585, by decide⟩ :=
  accepted_of_selected 13 298087 ⟨532585, by decide⟩ ⟨13, 2, 0, 532585, 298087, 789, 16384⟩
    (by decide) selected_cut_20806

theorem unmarked_context_12_74521_532586 : frontier 9 ⟨532586, by decide⟩
    (prefixCache 12 74521) (prefixPartial 12 74521) = false := by
  decide +kernel

theorem node_context_12_74521_532586 : EJMOriginalGlobalDAGData.nodes 9 ⟨532586, by decide⟩ =
    .split (coordinate 12) (![⟨532527, by decide⟩,⟨532550, by decide⟩,⟨532576, by decide⟩,⟨532585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74521_532586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74521 ⟨532586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74521
    ⟨532586, by decide⟩ (by decide) (![⟨532527, by decide⟩,⟨532550, by decide⟩,⟨532576, by decide⟩,⟨532585, by decide⟩]) unmarked_context_12_74521_532586 node_context_12_74521_532586
  intro a
  fin_cases a
  · exact context_13_298084_532527
  · exact context_13_298085_532550
  · exact context_13_298086_532576
  · exact context_13_298087_532585

theorem selected_cut_20807 : selected 8 ⟨532611, by decide⟩
    (prefixPartial 13 298088) = some ⟨13, 2, 0, 532611, 298088, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_298088_532611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298088 ⟨532611, by decide⟩ :=
  accepted_of_selected 13 298088 ⟨532611, by decide⟩ ⟨13, 2, 0, 532611, 298088, 1361, 16384⟩
    (by decide) selected_cut_20807

theorem selected_cut_20808 : selected 8 ⟨532638, by decide⟩
    (prefixPartial 13 298089) = some ⟨13, 2, 0, 532638, 298089, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_298089_532638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298089 ⟨532638, by decide⟩ :=
  accepted_of_selected 13 298089 ⟨532638, by decide⟩ ⟨13, 2, 0, 532638, 298089, 2189, 16384⟩
    (by decide) selected_cut_20808

theorem selected_cut_20809 : selected 8 ⟨532656, by decide⟩
    (prefixPartial 13 298090) = some ⟨13, 2, 0, 532656, 298090, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_298090_532656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298090 ⟨532656, by decide⟩ :=
  accepted_of_selected 13 298090 ⟨532656, by decide⟩ ⟨13, 2, 0, 532656, 298090, 1269, 16384⟩
    (by decide) selected_cut_20809

theorem selected_cut_20810 : selected 8 ⟨532663, by decide⟩
    (prefixPartial 13 298091) = some ⟨13, 2, 0, 532663, 298091, 681, 16384⟩ := by
  decide +kernel

theorem context_13_298091_532663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298091 ⟨532663, by decide⟩ :=
  accepted_of_selected 13 298091 ⟨532663, by decide⟩ ⟨13, 2, 0, 532663, 298091, 681, 16384⟩
    (by decide) selected_cut_20810

theorem unmarked_context_12_74522_532664 : frontier 9 ⟨532664, by decide⟩
    (prefixCache 12 74522) (prefixPartial 12 74522) = false := by
  decide +kernel

theorem node_context_12_74522_532664 : EJMOriginalGlobalDAGData.nodes 9 ⟨532664, by decide⟩ =
    .split (coordinate 12) (![⟨532611, by decide⟩,⟨532638, by decide⟩,⟨532656, by decide⟩,⟨532663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74522_532664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74522 ⟨532664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74522
    ⟨532664, by decide⟩ (by decide) (![⟨532611, by decide⟩,⟨532638, by decide⟩,⟨532656, by decide⟩,⟨532663, by decide⟩]) unmarked_context_12_74522_532664 node_context_12_74522_532664
  intro a
  fin_cases a
  · exact context_13_298088_532611
  · exact context_13_298089_532638
  · exact context_13_298090_532656
  · exact context_13_298091_532663

theorem selected_cut_20811 : selected 8 ⟨532689, by decide⟩
    (prefixPartial 13 298092) = some ⟨13, 2, 0, 532689, 298092, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_298092_532689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298092 ⟨532689, by decide⟩ :=
  accepted_of_selected 13 298092 ⟨532689, by decide⟩ ⟨13, 2, 0, 532689, 298092, 1301, 16384⟩
    (by decide) selected_cut_20811

theorem selected_cut_20812 : selected 8 ⟨532712, by decide⟩
    (prefixPartial 13 298093) = some ⟨13, 2, 0, 532712, 298093, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_298093_532712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298093 ⟨532712, by decide⟩ :=
  accepted_of_selected 13 298093 ⟨532712, by decide⟩ ⟨13, 2, 0, 532712, 298093, 2141, 16384⟩
    (by decide) selected_cut_20812

theorem selected_cut_20813 : selected 8 ⟨532734, by decide⟩
    (prefixPartial 13 298094) = some ⟨13, 2, 0, 532734, 298094, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_298094_532734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298094 ⟨532734, by decide⟩ :=
  accepted_of_selected 13 298094 ⟨532734, by decide⟩ ⟨13, 2, 0, 532734, 298094, 1325, 16384⟩
    (by decide) selected_cut_20813

theorem selected_cut_20814 : selected 8 ⟨532740, by decide⟩
    (prefixPartial 13 298095) = some ⟨13, 2, 0, 532740, 298095, 561, 16384⟩ := by
  decide +kernel

theorem context_13_298095_532740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298095 ⟨532740, by decide⟩ :=
  accepted_of_selected 13 298095 ⟨532740, by decide⟩ ⟨13, 2, 0, 532740, 298095, 561, 16384⟩
    (by decide) selected_cut_20814

theorem unmarked_context_12_74523_532741 : frontier 9 ⟨532741, by decide⟩
    (prefixCache 12 74523) (prefixPartial 12 74523) = false := by
  decide +kernel

theorem node_context_12_74523_532741 : EJMOriginalGlobalDAGData.nodes 9 ⟨532741, by decide⟩ =
    .split (coordinate 12) (![⟨532689, by decide⟩,⟨532712, by decide⟩,⟨532734, by decide⟩,⟨532740, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74523_532741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74523 ⟨532741, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74523
    ⟨532741, by decide⟩ (by decide) (![⟨532689, by decide⟩,⟨532712, by decide⟩,⟨532734, by decide⟩,⟨532740, by decide⟩]) unmarked_context_12_74523_532741 node_context_12_74523_532741
  intro a
  fin_cases a
  · exact context_13_298092_532689
  · exact context_13_298093_532712
  · exact context_13_298094_532734
  · exact context_13_298095_532740

theorem unmarked_context_11_18630_532742 : frontier 10 ⟨532742, by decide⟩
    (prefixCache 11 18630) (prefixPartial 11 18630) = false := by
  decide +kernel

theorem node_context_11_18630_532742 : EJMOriginalGlobalDAGData.nodes 10 ⟨532742, by decide⟩ =
    .split (coordinate 11) (![⟨532491, by decide⟩,⟨532586, by decide⟩,⟨532664, by decide⟩,⟨532741, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18630_532742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18630 ⟨532742, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18630
    ⟨532742, by decide⟩ (by decide) (![⟨532491, by decide⟩,⟨532586, by decide⟩,⟨532664, by decide⟩,⟨532741, by decide⟩]) unmarked_context_11_18630_532742 node_context_11_18630_532742
  intro a
  fin_cases a
  · exact context_12_74520_532491
  · exact context_12_74521_532586
  · exact context_12_74522_532664
  · exact context_12_74523_532741

theorem selected_cut_20815 : selected 8 ⟨532766, by decide⟩
    (prefixPartial 13 298096) = some ⟨13, 2, 0, 532766, 298096, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_298096_532766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298096 ⟨532766, by decide⟩ :=
  accepted_of_selected 13 298096 ⟨532766, by decide⟩ ⟨13, 2, 0, 532766, 298096, 1541, 16384⟩
    (by decide) selected_cut_20815

theorem selected_cut_20816 : selected 8 ⟨532812, by decide⟩
    (prefixPartial 13 298097) = some ⟨13, 2, 0, 532812, 298097, 3217, 16384⟩ := by
  decide +kernel

theorem context_13_298097_532812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298097 ⟨532812, by decide⟩ :=
  accepted_of_selected 13 298097 ⟨532812, by decide⟩ ⟨13, 2, 0, 532812, 298097, 3217, 16384⟩
    (by decide) selected_cut_20816

theorem selected_cut_20817 : selected 8 ⟨532832, by decide⟩
    (prefixPartial 13 298098) = some ⟨13, 2, 0, 532832, 298098, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_298098_532832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298098 ⟨532832, by decide⟩ :=
  accepted_of_selected 13 298098 ⟨532832, by decide⟩ ⟨13, 2, 0, 532832, 298098, 1601, 16384⟩
    (by decide) selected_cut_20817

theorem selected_cut_20818 : selected 8 ⟨532843, by decide⟩
    (prefixPartial 13 298099) = some ⟨13, 2, 0, 532843, 298099, 877, 16384⟩ := by
  decide +kernel

theorem context_13_298099_532843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298099 ⟨532843, by decide⟩ :=
  accepted_of_selected 13 298099 ⟨532843, by decide⟩ ⟨13, 2, 0, 532843, 298099, 877, 16384⟩
    (by decide) selected_cut_20818

theorem unmarked_context_12_74524_532844 : frontier 9 ⟨532844, by decide⟩
    (prefixCache 12 74524) (prefixPartial 12 74524) = false := by
  decide +kernel

theorem node_context_12_74524_532844 : EJMOriginalGlobalDAGData.nodes 9 ⟨532844, by decide⟩ =
    .split (coordinate 12) (![⟨532766, by decide⟩,⟨532812, by decide⟩,⟨532832, by decide⟩,⟨532843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74524_532844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74524 ⟨532844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74524
    ⟨532844, by decide⟩ (by decide) (![⟨532766, by decide⟩,⟨532812, by decide⟩,⟨532832, by decide⟩,⟨532843, by decide⟩]) unmarked_context_12_74524_532844 node_context_12_74524_532844
  intro a
  fin_cases a
  · exact context_13_298096_532766
  · exact context_13_298097_532812
  · exact context_13_298098_532832
  · exact context_13_298099_532843

theorem selected_cut_20819 : selected 8 ⟨532875, by decide⟩
    (prefixPartial 13 298100) = some ⟨13, 2, 0, 532875, 298100, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_298100_532875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298100 ⟨532875, by decide⟩ :=
  accepted_of_selected 13 298100 ⟨532875, by decide⟩ ⟨13, 2, 0, 532875, 298100, 1489, 16384⟩
    (by decide) selected_cut_20819

theorem selected_cut_20820 : selected 8 ⟨532902, by decide⟩
    (prefixPartial 13 298101) = some ⟨13, 2, 0, 532902, 298101, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_298101_532902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298101 ⟨532902, by decide⟩ :=
  accepted_of_selected 13 298101 ⟨532902, by decide⟩ ⟨13, 2, 0, 532902, 298101, 1853, 16384⟩
    (by decide) selected_cut_20820

theorem selected_cut_20821 : selected 8 ⟨532916, by decide⟩
    (prefixPartial 13 298102) = some ⟨13, 2, 0, 532916, 298102, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_298102_532916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298102 ⟨532916, by decide⟩ :=
  accepted_of_selected 13 298102 ⟨532916, by decide⟩ ⟨13, 2, 0, 532916, 298102, 1713, 16384⟩
    (by decide) selected_cut_20821

theorem selected_cut_20822 : selected 8 ⟨532923, by decide⟩
    (prefixPartial 13 298103) = some ⟨13, 2, 0, 532923, 298103, 761, 16384⟩ := by
  decide +kernel

theorem context_13_298103_532923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298103 ⟨532923, by decide⟩ :=
  accepted_of_selected 13 298103 ⟨532923, by decide⟩ ⟨13, 2, 0, 532923, 298103, 761, 16384⟩
    (by decide) selected_cut_20822

theorem unmarked_context_12_74525_532924 : frontier 9 ⟨532924, by decide⟩
    (prefixCache 12 74525) (prefixPartial 12 74525) = false := by
  decide +kernel

theorem node_context_12_74525_532924 : EJMOriginalGlobalDAGData.nodes 9 ⟨532924, by decide⟩ =
    .split (coordinate 12) (![⟨532875, by decide⟩,⟨532902, by decide⟩,⟨532916, by decide⟩,⟨532923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74525_532924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74525 ⟨532924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74525
    ⟨532924, by decide⟩ (by decide) (![⟨532875, by decide⟩,⟨532902, by decide⟩,⟨532916, by decide⟩,⟨532923, by decide⟩]) unmarked_context_12_74525_532924 node_context_12_74525_532924
  intro a
  fin_cases a
  · exact context_13_298100_532875
  · exact context_13_298101_532902
  · exact context_13_298102_532916
  · exact context_13_298103_532923

theorem selected_cut_20823 : selected 8 ⟨532945, by decide⟩
    (prefixPartial 13 298104) = some ⟨13, 2, 0, 532945, 298104, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_298104_532945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298104 ⟨532945, by decide⟩ :=
  accepted_of_selected 13 298104 ⟨532945, by decide⟩ ⟨13, 2, 0, 532945, 298104, 1121, 16384⟩
    (by decide) selected_cut_20823

theorem selected_cut_20824 : selected 8 ⟨532974, by decide⟩
    (prefixPartial 13 298105) = some ⟨13, 2, 0, 532974, 298105, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_298105_532974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298105 ⟨532974, by decide⟩ :=
  accepted_of_selected 13 298105 ⟨532974, by decide⟩ ⟨13, 2, 0, 532974, 298105, 2477, 16384⟩
    (by decide) selected_cut_20824

theorem selected_cut_20825 : selected 8 ⟨532990, by decide⟩
    (prefixPartial 13 298106) = some ⟨13, 2, 0, 532990, 298106, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_298106_532990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298106 ⟨532990, by decide⟩ :=
  accepted_of_selected 13 298106 ⟨532990, by decide⟩ ⟨13, 2, 0, 532990, 298106, 1157, 16384⟩
    (by decide) selected_cut_20825

theorem selected_cut_20826 : selected 8 ⟨532996, by decide⟩
    (prefixPartial 13 298107) = some ⟨13, 2, 0, 532996, 298107, 725, 16384⟩ := by
  decide +kernel

theorem context_13_298107_532996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298107 ⟨532996, by decide⟩ :=
  accepted_of_selected 13 298107 ⟨532996, by decide⟩ ⟨13, 2, 0, 532996, 298107, 725, 16384⟩
    (by decide) selected_cut_20826

theorem unmarked_context_12_74526_532997 : frontier 9 ⟨532997, by decide⟩
    (prefixCache 12 74526) (prefixPartial 12 74526) = false := by
  decide +kernel

theorem node_context_12_74526_532997 : EJMOriginalGlobalDAGData.nodes 9 ⟨532997, by decide⟩ =
    .split (coordinate 12) (![⟨532945, by decide⟩,⟨532974, by decide⟩,⟨532990, by decide⟩,⟨532996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74526_532997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74526 ⟨532997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74526
    ⟨532997, by decide⟩ (by decide) (![⟨532945, by decide⟩,⟨532974, by decide⟩,⟨532990, by decide⟩,⟨532996, by decide⟩]) unmarked_context_12_74526_532997 node_context_12_74526_532997
  intro a
  fin_cases a
  · exact context_13_298104_532945
  · exact context_13_298105_532974
  · exact context_13_298106_532990
  · exact context_13_298107_532996

theorem selected_cut_20827 : selected 8 ⟨533028, by decide⟩
    (prefixPartial 13 298108) = some ⟨13, 2, 0, 533028, 298108, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_298108_533028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298108 ⟨533028, by decide⟩ :=
  accepted_of_selected 13 298108 ⟨533028, by decide⟩ ⟨13, 2, 0, 533028, 298108, 1957, 16384⟩
    (by decide) selected_cut_20827

theorem selected_cut_20828 : selected 8 ⟨533072, by decide⟩
    (prefixPartial 13 298109) = some ⟨13, 2, 0, 533072, 298109, 3545, 16384⟩ := by
  decide +kernel

theorem context_13_298109_533072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298109 ⟨533072, by decide⟩ :=
  accepted_of_selected 13 298109 ⟨533072, by decide⟩ ⟨13, 2, 0, 533072, 298109, 3545, 16384⟩
    (by decide) selected_cut_20828

theorem selected_cut_20829 : selected 8 ⟨533090, by decide⟩
    (prefixPartial 13 298110) = some ⟨13, 2, 0, 533090, 298110, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_298110_533090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298110 ⟨533090, by decide⟩ :=
  accepted_of_selected 13 298110 ⟨533090, by decide⟩ ⟨13, 2, 0, 533090, 298110, 1829, 16384⟩
    (by decide) selected_cut_20829

theorem selected_cut_20830 : selected 8 ⟨533102, by decide⟩
    (prefixPartial 13 298111) = some ⟨13, 2, 0, 533102, 298111, 905, 16384⟩ := by
  decide +kernel

theorem context_13_298111_533102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298111 ⟨533102, by decide⟩ :=
  accepted_of_selected 13 298111 ⟨533102, by decide⟩ ⟨13, 2, 0, 533102, 298111, 905, 16384⟩
    (by decide) selected_cut_20830

theorem unmarked_context_12_74527_533103 : frontier 9 ⟨533103, by decide⟩
    (prefixCache 12 74527) (prefixPartial 12 74527) = false := by
  decide +kernel

theorem node_context_12_74527_533103 : EJMOriginalGlobalDAGData.nodes 9 ⟨533103, by decide⟩ =
    .split (coordinate 12) (![⟨533028, by decide⟩,⟨533072, by decide⟩,⟨533090, by decide⟩,⟨533102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74527_533103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74527 ⟨533103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74527
    ⟨533103, by decide⟩ (by decide) (![⟨533028, by decide⟩,⟨533072, by decide⟩,⟨533090, by decide⟩,⟨533102, by decide⟩]) unmarked_context_12_74527_533103 node_context_12_74527_533103
  intro a
  fin_cases a
  · exact context_13_298108_533028
  · exact context_13_298109_533072
  · exact context_13_298110_533090
  · exact context_13_298111_533102

theorem unmarked_context_11_18631_533104 : frontier 10 ⟨533104, by decide⟩
    (prefixCache 11 18631) (prefixPartial 11 18631) = false := by
  decide +kernel

theorem node_context_11_18631_533104 : EJMOriginalGlobalDAGData.nodes 10 ⟨533104, by decide⟩ =
    .split (coordinate 11) (![⟨532844, by decide⟩,⟨532924, by decide⟩,⟨532997, by decide⟩,⟨533103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18631_533104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18631 ⟨533104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18631
    ⟨533104, by decide⟩ (by decide) (![⟨532844, by decide⟩,⟨532924, by decide⟩,⟨532997, by decide⟩,⟨533103, by decide⟩]) unmarked_context_11_18631_533104 node_context_11_18631_533104
  intro a
  fin_cases a
  · exact context_12_74524_532844
  · exact context_12_74525_532924
  · exact context_12_74526_532997
  · exact context_12_74527_533103

theorem unmarked_context_10_4657_533105 : frontier 11 ⟨533105, by decide⟩
    (prefixCache 10 4657) (prefixPartial 10 4657) = false := by
  decide +kernel

theorem node_context_10_4657_533105 : EJMOriginalGlobalDAGData.nodes 11 ⟨533105, by decide⟩ =
    .split (coordinate 10) (![⟨532056, by decide⟩,⟨532363, by decide⟩,⟨532742, by decide⟩,⟨533104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4657_533105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4657 ⟨533105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4657
    ⟨533105, by decide⟩ (by decide) (![⟨532056, by decide⟩,⟨532363, by decide⟩,⟨532742, by decide⟩,⟨533104, by decide⟩]) unmarked_context_10_4657_533105 node_context_10_4657_533105
  intro a
  fin_cases a
  · exact context_11_18628_532056
  · exact context_11_18629_532363
  · exact context_11_18630_532742
  · exact context_11_18631_533104

theorem selected_cut_20831 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 74528) = some ⟨12, 1, 0, 435790, 74528, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74528_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74528 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 74528 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 74528, 1, 65536⟩
    (by decide) selected_cut_20831

theorem selected_cut_20832 : selected 8 ⟨533140, by decide⟩
    (prefixPartial 13 298116) = some ⟨13, 2, 0, 533140, 298116, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_298116_533140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298116 ⟨533140, by decide⟩ :=
  accepted_of_selected 13 298116 ⟨533140, by decide⟩ ⟨13, 2, 0, 533140, 298116, 1157, 16384⟩
    (by decide) selected_cut_20832

theorem selected_cut_20833 : selected 8 ⟨533173, by decide⟩
    (prefixPartial 13 298117) = some ⟨13, 2, 0, 533173, 298117, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_298117_533173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298117 ⟨533173, by decide⟩ :=
  accepted_of_selected 13 298117 ⟨533173, by decide⟩ ⟨13, 2, 0, 533173, 298117, 1497, 16384⟩
    (by decide) selected_cut_20833

theorem selected_cut_20834 : selected 8 ⟨533189, by decide⟩
    (prefixPartial 13 298118) = some ⟨13, 2, 0, 533189, 298118, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_298118_533189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 298118 ⟨533189, by decide⟩ :=
  accepted_of_selected 13 298118 ⟨533189, by decide⟩ ⟨13, 2, 0, 533189, 298118, 1169, 16384⟩
    (by decide) selected_cut_20834

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
