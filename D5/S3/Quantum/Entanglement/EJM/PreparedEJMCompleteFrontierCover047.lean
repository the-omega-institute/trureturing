/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover046
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_04515 : selected 9 ⟨145420, by decide⟩
    (prefixPartial 12 18495) = some ⟨12, 2, 0, 145420, 18495, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_18495_145420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18495 ⟨145420, by decide⟩ :=
  accepted_of_selected 12 18495 ⟨145420, by decide⟩ ⟨12, 2, 0, 145420, 18495, 2989, 65536⟩
    (by decide) selected_cut_04515

theorem unmarked_context_11_4623_145421 : frontier 10 ⟨145421, by decide⟩
    (prefixCache 11 4623) (prefixPartial 11 4623) = false := by
  decide +kernel

theorem node_context_11_4623_145421 : EJMOriginalGlobalDAGData.nodes 10 ⟨145421, by decide⟩ =
    .split (coordinate 11) (![⟨145206, by decide⟩,⟨145274, by decide⟩,⟨145361, by decide⟩,⟨145420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4623_145421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4623 ⟨145421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4623
    ⟨145421, by decide⟩ (by decide) (![⟨145206, by decide⟩,⟨145274, by decide⟩,⟨145361, by decide⟩,⟨145420, by decide⟩]) unmarked_context_11_4623_145421 node_context_11_4623_145421
  intro a
  fin_cases a
  · exact context_12_18492_145206
  · exact context_12_18493_145274
  · exact context_12_18494_145361
  · exact context_12_18495_145420

theorem unmarked_context_10_1155_145422 : frontier 11 ⟨145422, by decide⟩
    (prefixCache 10 1155) (prefixPartial 10 1155) = false := by
  decide +kernel

theorem node_context_10_1155_145422 : EJMOriginalGlobalDAGData.nodes 11 ⟨145422, by decide⟩ =
    .split (coordinate 10) (![⟨144456, by decide⟩,⟨144808, by decide⟩,⟨145127, by decide⟩,⟨145421, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1155_145422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1155 ⟨145422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1155
    ⟨145422, by decide⟩ (by decide) (![⟨144456, by decide⟩,⟨144808, by decide⟩,⟨145127, by decide⟩,⟨145421, by decide⟩]) unmarked_context_10_1155_145422 node_context_10_1155_145422
  intro a
  fin_cases a
  · exact context_11_4620_144456
  · exact context_11_4621_144808
  · exact context_11_4622_145127
  · exact context_11_4623_145421

theorem unmarked_context_9_288_145423 : frontier 12 ⟨145423, by decide⟩
    (prefixCache 9 288) (prefixPartial 9 288) = false := by
  decide +kernel

theorem node_context_9_288_145423 : EJMOriginalGlobalDAGData.nodes 12 ⟨145423, by decide⟩ =
    .split (coordinate 9) (![⟨139845, by decide⟩,⟨142180, by decide⟩,⟨144328, by decide⟩,⟨145422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_288_145423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 288 ⟨145423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 288
    ⟨145423, by decide⟩ (by decide) (![⟨139845, by decide⟩,⟨142180, by decide⟩,⟨144328, by decide⟩,⟨145422, by decide⟩]) unmarked_context_9_288_145423 node_context_9_288_145423
  intro a
  fin_cases a
  · exact context_10_1152_139845
  · exact context_10_1153_142180
  · exact context_10_1154_144328
  · exact context_10_1155_145422

theorem selected_cut_04516 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 1156) = some ⟨10, 1, 0, 145424, 1156, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1156_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1156 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 1156 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 1156, 1, 1048576⟩
    (by decide) selected_cut_04516

theorem selected_cut_04517 : selected 10 ⟨145425, by decide⟩
    (prefixPartial 11 4628) = some ⟨11, 1, 0, 145425, 4628, 1, 262144⟩ := by
  decide +kernel

theorem context_11_4628_145425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4628 ⟨145425, by decide⟩ :=
  accepted_of_selected 11 4628 ⟨145425, by decide⟩ ⟨11, 1, 0, 145425, 4628, 1, 262144⟩
    (by decide) selected_cut_04517

theorem selected_cut_04518 : selected 9 ⟨122215, by decide⟩
    (prefixPartial 12 18516) = some ⟨12, 1, 0, 122215, 18516, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18516_122215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18516 ⟨122215, by decide⟩ :=
  accepted_of_selected 12 18516 ⟨122215, by decide⟩ ⟨12, 1, 0, 122215, 18516, 1, 65536⟩
    (by decide) selected_cut_04518

theorem selected_cut_04519 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 18517) = some ⟨12, 1, 0, 126371, 18517, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18517_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18517 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 18517 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 18517, 1, 65536⟩
    (by decide) selected_cut_04519

theorem selected_cut_04520 : selected 9 ⟨145551, by decide⟩
    (prefixPartial 12 18518) = some ⟨12, 2, 0, 145551, 18518, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_18518_145551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18518 ⟨145551, by decide⟩ :=
  accepted_of_selected 12 18518 ⟨145551, by decide⟩ ⟨12, 2, 0, 145551, 18518, 2813, 65536⟩
    (by decide) selected_cut_04520

theorem selected_cut_04521 : selected 9 ⟨145636, by decide⟩
    (prefixPartial 12 18519) = some ⟨12, 2, 0, 145636, 18519, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_18519_145636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18519 ⟨145636, by decide⟩ :=
  accepted_of_selected 12 18519 ⟨145636, by decide⟩ ⟨12, 2, 0, 145636, 18519, 2745, 65536⟩
    (by decide) selected_cut_04521

theorem unmarked_context_11_4629_145637 : frontier 10 ⟨145637, by decide⟩
    (prefixCache 11 4629) (prefixPartial 11 4629) = false := by
  decide +kernel

theorem node_context_11_4629_145637 : EJMOriginalGlobalDAGData.nodes 10 ⟨145637, by decide⟩ =
    .split (coordinate 11) (![⟨122215, by decide⟩,⟨126371, by decide⟩,⟨145551, by decide⟩,⟨145636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4629_145637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4629 ⟨145637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4629
    ⟨145637, by decide⟩ (by decide) (![⟨122215, by decide⟩,⟨126371, by decide⟩,⟨145551, by decide⟩,⟨145636, by decide⟩]) unmarked_context_11_4629_145637 node_context_11_4629_145637
  intro a
  fin_cases a
  · exact context_12_18516_122215
  · exact context_12_18517_126371
  · exact context_12_18518_145551
  · exact context_12_18519_145636

theorem selected_cut_04522 : selected 9 ⟨122215, by decide⟩
    (prefixPartial 12 18520) = some ⟨12, 1, 0, 122215, 18520, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18520_122215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18520 ⟨122215, by decide⟩ :=
  accepted_of_selected 12 18520 ⟨122215, by decide⟩ ⟨12, 1, 0, 122215, 18520, 1, 65536⟩
    (by decide) selected_cut_04522

theorem selected_cut_04523 : selected 9 ⟨145771, by decide⟩
    (prefixPartial 12 18521) = some ⟨12, 2, 0, 145771, 18521, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_18521_145771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18521 ⟨145771, by decide⟩ :=
  accepted_of_selected 12 18521 ⟨145771, by decide⟩ ⟨12, 2, 0, 145771, 18521, 3033, 65536⟩
    (by decide) selected_cut_04523

theorem selected_cut_04524 : selected 9 ⟨145850, by decide⟩
    (prefixPartial 12 18522) = some ⟨12, 2, 0, 145850, 18522, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_18522_145850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18522 ⟨145850, by decide⟩ :=
  accepted_of_selected 12 18522 ⟨145850, by decide⟩ ⟨12, 2, 0, 145850, 18522, 1577, 65536⟩
    (by decide) selected_cut_04524

theorem selected_cut_04525 : selected 9 ⟨145914, by decide⟩
    (prefixPartial 12 18523) = some ⟨12, 2, 0, 145914, 18523, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_18523_145914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18523 ⟨145914, by decide⟩ :=
  accepted_of_selected 12 18523 ⟨145914, by decide⟩ ⟨12, 2, 0, 145914, 18523, 2317, 65536⟩
    (by decide) selected_cut_04525

theorem unmarked_context_11_4630_145915 : frontier 10 ⟨145915, by decide⟩
    (prefixCache 11 4630) (prefixPartial 11 4630) = false := by
  decide +kernel

theorem node_context_11_4630_145915 : EJMOriginalGlobalDAGData.nodes 10 ⟨145915, by decide⟩ =
    .split (coordinate 11) (![⟨122215, by decide⟩,⟨145771, by decide⟩,⟨145850, by decide⟩,⟨145914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4630_145915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4630 ⟨145915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4630
    ⟨145915, by decide⟩ (by decide) (![⟨122215, by decide⟩,⟨145771, by decide⟩,⟨145850, by decide⟩,⟨145914, by decide⟩]) unmarked_context_11_4630_145915 node_context_11_4630_145915
  intro a
  fin_cases a
  · exact context_12_18520_122215
  · exact context_12_18521_145771
  · exact context_12_18522_145850
  · exact context_12_18523_145914

theorem selected_cut_04526 : selected 9 ⟨122215, by decide⟩
    (prefixPartial 12 18524) = some ⟨12, 1, 0, 122215, 18524, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18524_122215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18524 ⟨122215, by decide⟩ :=
  accepted_of_selected 12 18524 ⟨122215, by decide⟩ ⟨12, 1, 0, 122215, 18524, 1, 65536⟩
    (by decide) selected_cut_04526

theorem selected_cut_04527 : selected 9 ⟨146022, by decide⟩
    (prefixPartial 12 18525) = some ⟨12, 2, 0, 146022, 18525, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_18525_146022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18525 ⟨146022, by decide⟩ :=
  accepted_of_selected 12 18525 ⟨146022, by decide⟩ ⟨12, 2, 0, 146022, 18525, 2477, 65536⟩
    (by decide) selected_cut_04527

theorem selected_cut_04528 : selected 9 ⟨146073, by decide⟩
    (prefixPartial 12 18526) = some ⟨12, 2, 0, 146073, 18526, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_18526_146073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18526 ⟨146073, by decide⟩ :=
  accepted_of_selected 12 18526 ⟨146073, by decide⟩ ⟨12, 2, 0, 146073, 18526, 1957, 65536⟩
    (by decide) selected_cut_04528

theorem selected_cut_04529 : selected 9 ⟨146118, by decide⟩
    (prefixPartial 12 18527) = some ⟨12, 2, 0, 146118, 18527, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_18527_146118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18527 ⟨146118, by decide⟩ :=
  accepted_of_selected 12 18527 ⟨146118, by decide⟩ ⟨12, 2, 0, 146118, 18527, 1725, 65536⟩
    (by decide) selected_cut_04529

theorem unmarked_context_11_4631_146119 : frontier 10 ⟨146119, by decide⟩
    (prefixCache 11 4631) (prefixPartial 11 4631) = false := by
  decide +kernel

theorem node_context_11_4631_146119 : EJMOriginalGlobalDAGData.nodes 10 ⟨146119, by decide⟩ =
    .split (coordinate 11) (![⟨122215, by decide⟩,⟨146022, by decide⟩,⟨146073, by decide⟩,⟨146118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4631_146119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4631 ⟨146119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4631
    ⟨146119, by decide⟩ (by decide) (![⟨122215, by decide⟩,⟨146022, by decide⟩,⟨146073, by decide⟩,⟨146118, by decide⟩]) unmarked_context_11_4631_146119 node_context_11_4631_146119
  intro a
  fin_cases a
  · exact context_12_18524_122215
  · exact context_12_18525_146022
  · exact context_12_18526_146073
  · exact context_12_18527_146118

theorem unmarked_context_10_1157_146120 : frontier 11 ⟨146120, by decide⟩
    (prefixCache 10 1157) (prefixPartial 10 1157) = false := by
  decide +kernel

theorem node_context_10_1157_146120 : EJMOriginalGlobalDAGData.nodes 11 ⟨146120, by decide⟩ =
    .split (coordinate 10) (![⟨145425, by decide⟩,⟨145637, by decide⟩,⟨145915, by decide⟩,⟨146119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1157_146120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1157 ⟨146120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1157
    ⟨146120, by decide⟩ (by decide) (![⟨145425, by decide⟩,⟨145637, by decide⟩,⟨145915, by decide⟩,⟨146119, by decide⟩]) unmarked_context_10_1157_146120 node_context_10_1157_146120
  intro a
  fin_cases a
  · exact context_11_4628_145425
  · exact context_11_4629_145637
  · exact context_11_4630_145915
  · exact context_11_4631_146119

theorem selected_cut_04530 : selected 10 ⟨145425, by decide⟩
    (prefixPartial 11 4632) = some ⟨11, 1, 0, 145425, 4632, 1, 262144⟩ := by
  decide +kernel

theorem context_11_4632_145425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4632 ⟨145425, by decide⟩ :=
  accepted_of_selected 11 4632 ⟨145425, by decide⟩ ⟨11, 1, 0, 145425, 4632, 1, 262144⟩
    (by decide) selected_cut_04530

theorem selected_cut_04531 : selected 10 ⟨146283, by decide⟩
    (prefixPartial 11 4633) = some ⟨11, 2, 0, 146283, 4633, 2637, 262144⟩ := by
  decide +kernel

theorem context_11_4633_146283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4633 ⟨146283, by decide⟩ :=
  accepted_of_selected 11 4633 ⟨146283, by decide⟩ ⟨11, 2, 0, 146283, 4633, 2637, 262144⟩
    (by decide) selected_cut_04531

theorem selected_cut_04532 : selected 10 ⟨146440, by decide⟩
    (prefixPartial 11 4634) = some ⟨11, 2, 0, 146440, 4634, 2669, 262144⟩ := by
  decide +kernel

theorem context_11_4634_146440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4634 ⟨146440, by decide⟩ :=
  accepted_of_selected 11 4634 ⟨146440, by decide⟩ ⟨11, 2, 0, 146440, 4634, 2669, 262144⟩
    (by decide) selected_cut_04532

theorem selected_cut_04533 : selected 10 ⟨146477, by decide⟩
    (prefixPartial 11 4635) = some ⟨11, 2, 0, 146477, 4635, 697, 262144⟩ := by
  decide +kernel

theorem context_11_4635_146477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4635 ⟨146477, by decide⟩ :=
  accepted_of_selected 11 4635 ⟨146477, by decide⟩ ⟨11, 2, 0, 146477, 4635, 697, 262144⟩
    (by decide) selected_cut_04533

theorem unmarked_context_10_1158_146478 : frontier 11 ⟨146478, by decide⟩
    (prefixCache 10 1158) (prefixPartial 10 1158) = false := by
  decide +kernel

theorem node_context_10_1158_146478 : EJMOriginalGlobalDAGData.nodes 11 ⟨146478, by decide⟩ =
    .split (coordinate 10) (![⟨145425, by decide⟩,⟨146283, by decide⟩,⟨146440, by decide⟩,⟨146477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1158_146478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1158 ⟨146478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1158
    ⟨146478, by decide⟩ (by decide) (![⟨145425, by decide⟩,⟨146283, by decide⟩,⟨146440, by decide⟩,⟨146477, by decide⟩]) unmarked_context_10_1158_146478 node_context_10_1158_146478
  intro a
  fin_cases a
  · exact context_11_4632_145425
  · exact context_11_4633_146283
  · exact context_11_4634_146440
  · exact context_11_4635_146477

theorem selected_cut_04534 : selected 10 ⟨145425, by decide⟩
    (prefixPartial 11 4636) = some ⟨11, 1, 0, 145425, 4636, 1, 262144⟩ := by
  decide +kernel

theorem context_11_4636_145425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4636 ⟨145425, by decide⟩ :=
  accepted_of_selected 11 4636 ⟨145425, by decide⟩ ⟨11, 1, 0, 145425, 4636, 1, 262144⟩
    (by decide) selected_cut_04534

theorem selected_cut_04535 : selected 10 ⟨146562, by decide⟩
    (prefixPartial 11 4637) = some ⟨11, 2, 0, 146562, 4637, 1965, 262144⟩ := by
  decide +kernel

theorem context_11_4637_146562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4637 ⟨146562, by decide⟩ :=
  accepted_of_selected 11 4637 ⟨146562, by decide⟩ ⟨11, 2, 0, 146562, 4637, 1965, 262144⟩
    (by decide) selected_cut_04535

theorem selected_cut_04536 : selected 10 ⟨146607, by decide⟩
    (prefixPartial 11 4638) = some ⟨11, 2, 0, 146607, 4638, 601, 262144⟩ := by
  decide +kernel

theorem context_11_4638_146607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4638 ⟨146607, by decide⟩ :=
  accepted_of_selected 11 4638 ⟨146607, by decide⟩ ⟨11, 2, 0, 146607, 4638, 601, 262144⟩
    (by decide) selected_cut_04536

theorem selected_cut_04537 : selected 10 ⟨146678, by decide⟩
    (prefixPartial 11 4639) = some ⟨11, 2, 0, 146678, 4639, 1745, 262144⟩ := by
  decide +kernel

theorem context_11_4639_146678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4639 ⟨146678, by decide⟩ :=
  accepted_of_selected 11 4639 ⟨146678, by decide⟩ ⟨11, 2, 0, 146678, 4639, 1745, 262144⟩
    (by decide) selected_cut_04537

theorem unmarked_context_10_1159_146679 : frontier 11 ⟨146679, by decide⟩
    (prefixCache 10 1159) (prefixPartial 10 1159) = false := by
  decide +kernel

theorem node_context_10_1159_146679 : EJMOriginalGlobalDAGData.nodes 11 ⟨146679, by decide⟩ =
    .split (coordinate 10) (![⟨145425, by decide⟩,⟨146562, by decide⟩,⟨146607, by decide⟩,⟨146678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1159_146679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1159 ⟨146679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1159
    ⟨146679, by decide⟩ (by decide) (![⟨145425, by decide⟩,⟨146562, by decide⟩,⟨146607, by decide⟩,⟨146678, by decide⟩]) unmarked_context_10_1159_146679 node_context_10_1159_146679
  intro a
  fin_cases a
  · exact context_11_4636_145425
  · exact context_11_4637_146562
  · exact context_11_4638_146607
  · exact context_11_4639_146678

theorem unmarked_context_9_289_146680 : frontier 12 ⟨146680, by decide⟩
    (prefixCache 9 289) (prefixPartial 9 289) = false := by
  decide +kernel

theorem node_context_9_289_146680 : EJMOriginalGlobalDAGData.nodes 12 ⟨146680, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨146120, by decide⟩,⟨146478, by decide⟩,⟨146679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_289_146680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 289 ⟨146680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 289
    ⟨146680, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨146120, by decide⟩,⟨146478, by decide⟩,⟨146679, by decide⟩]) unmarked_context_9_289_146680 node_context_9_289_146680
  intro a
  fin_cases a
  · exact context_10_1156_145424
  · exact context_10_1157_146120
  · exact context_10_1158_146478
  · exact context_10_1159_146679

theorem selected_cut_04538 : selected 12 ⟨146799, by decide⟩
    (prefixPartial 9 290) = some ⟨9, 2, 0, 146799, 290, 1113, 4194304⟩ := by
  decide +kernel

theorem context_9_290_146799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 290 ⟨146799, by decide⟩ :=
  accepted_of_selected 9 290 ⟨146799, by decide⟩ ⟨9, 2, 0, 146799, 290, 1113, 4194304⟩
    (by decide) selected_cut_04538

theorem selected_cut_04539 : selected 12 ⟨146805, by decide⟩
    (prefixPartial 9 291) = some ⟨9, 2, 0, 146805, 291, 37, 4194304⟩ := by
  decide +kernel

theorem context_9_291_146805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 291 ⟨146805, by decide⟩ :=
  accepted_of_selected 9 291 ⟨146805, by decide⟩ ⟨9, 2, 0, 146805, 291, 37, 4194304⟩
    (by decide) selected_cut_04539

theorem unmarked_context_8_72_146806 : frontier 13 ⟨146806, by decide⟩
    (prefixCache 8 72) (prefixPartial 8 72) = false := by
  decide +kernel

theorem node_context_8_72_146806 : EJMOriginalGlobalDAGData.nodes 13 ⟨146806, by decide⟩ =
    .split (coordinate 8) (![⟨145423, by decide⟩,⟨146680, by decide⟩,⟨146799, by decide⟩,⟨146805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_72_146806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 72 ⟨146806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 72
    ⟨146806, by decide⟩ (by decide) (![⟨145423, by decide⟩,⟨146680, by decide⟩,⟨146799, by decide⟩,⟨146805, by decide⟩]) unmarked_context_8_72_146806 node_context_8_72_146806
  intro a
  fin_cases a
  · exact context_9_288_145423
  · exact context_9_289_146680
  · exact context_9_290_146799
  · exact context_9_291_146805

theorem selected_cut_04540 : selected 8 ⟨146884, by decide⟩
    (prefixPartial 13 74752) = some ⟨13, 2, 0, 146884, 74752, 3997, 16384⟩ := by
  decide +kernel

theorem context_13_74752_146884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74752 ⟨146884, by decide⟩ :=
  accepted_of_selected 13 74752 ⟨146884, by decide⟩ ⟨13, 2, 0, 146884, 74752, 3997, 16384⟩
    (by decide) selected_cut_04540

theorem selected_cut_04541 : selected 8 ⟨146965, by decide⟩
    (prefixPartial 13 74753) = some ⟨13, 2, 0, 146965, 74753, 3933, 16384⟩ := by
  decide +kernel

theorem context_13_74753_146965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74753 ⟨146965, by decide⟩ :=
  accepted_of_selected 13 74753 ⟨146965, by decide⟩ ⟨13, 2, 0, 146965, 74753, 3933, 16384⟩
    (by decide) selected_cut_04541

theorem selected_cut_04542 : selected 8 ⟨146989, by decide⟩
    (prefixPartial 13 74754) = some ⟨13, 2, 0, 146989, 74754, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_74754_146989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74754 ⟨146989, by decide⟩ :=
  accepted_of_selected 13 74754 ⟨146989, by decide⟩ ⟨13, 2, 0, 146989, 74754, 2249, 16384⟩
    (by decide) selected_cut_04542

theorem selected_cut_04543 : selected 8 ⟨147001, by decide⟩
    (prefixPartial 13 74755) = some ⟨13, 2, 0, 147001, 74755, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_74755_147001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74755 ⟨147001, by decide⟩ :=
  accepted_of_selected 13 74755 ⟨147001, by decide⟩ ⟨13, 2, 0, 147001, 74755, 1165, 16384⟩
    (by decide) selected_cut_04543

theorem unmarked_context_12_18688_147002 : frontier 9 ⟨147002, by decide⟩
    (prefixCache 12 18688) (prefixPartial 12 18688) = false := by
  decide +kernel

theorem node_context_12_18688_147002 : EJMOriginalGlobalDAGData.nodes 9 ⟨147002, by decide⟩ =
    .split (coordinate 12) (![⟨146884, by decide⟩,⟨146965, by decide⟩,⟨146989, by decide⟩,⟨147001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18688_147002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18688 ⟨147002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18688
    ⟨147002, by decide⟩ (by decide) (![⟨146884, by decide⟩,⟨146965, by decide⟩,⟨146989, by decide⟩,⟨147001, by decide⟩]) unmarked_context_12_18688_147002 node_context_12_18688_147002
  intro a
  fin_cases a
  · exact context_13_74752_146884
  · exact context_13_74753_146965
  · exact context_13_74754_146989
  · exact context_13_74755_147001

theorem selected_cut_04544 : selected 8 ⟨147064, by decide⟩
    (prefixPartial 13 74756) = some ⟨13, 2, 0, 147064, 74756, 3921, 16384⟩ := by
  decide +kernel

theorem context_13_74756_147064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74756 ⟨147064, by decide⟩ :=
  accepted_of_selected 13 74756 ⟨147064, by decide⟩ ⟨13, 2, 0, 147064, 74756, 3921, 16384⟩
    (by decide) selected_cut_04544

theorem selected_cut_04545 : selected 8 ⟨147097, by decide⟩
    (prefixPartial 13 74757) = some ⟨13, 2, 0, 147097, 74757, 2873, 16384⟩ := by
  decide +kernel

theorem context_13_74757_147097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74757 ⟨147097, by decide⟩ :=
  accepted_of_selected 13 74757 ⟨147097, by decide⟩ ⟨13, 2, 0, 147097, 74757, 2873, 16384⟩
    (by decide) selected_cut_04545

theorem selected_cut_04546 : selected 8 ⟨147118, by decide⟩
    (prefixPartial 13 74758) = some ⟨13, 2, 0, 147118, 74758, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_74758_147118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74758 ⟨147118, by decide⟩ :=
  accepted_of_selected 13 74758 ⟨147118, by decide⟩ ⟨13, 2, 0, 147118, 74758, 2189, 16384⟩
    (by decide) selected_cut_04546

theorem selected_cut_04547 : selected 8 ⟨147125, by decide⟩
    (prefixPartial 13 74759) = some ⟨13, 2, 0, 147125, 74759, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_74759_147125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74759 ⟨147125, by decide⟩ :=
  accepted_of_selected 13 74759 ⟨147125, by decide⟩ ⟨13, 2, 0, 147125, 74759, 1089, 16384⟩
    (by decide) selected_cut_04547

theorem unmarked_context_12_18689_147126 : frontier 9 ⟨147126, by decide⟩
    (prefixCache 12 18689) (prefixPartial 12 18689) = false := by
  decide +kernel

theorem node_context_12_18689_147126 : EJMOriginalGlobalDAGData.nodes 9 ⟨147126, by decide⟩ =
    .split (coordinate 12) (![⟨147064, by decide⟩,⟨147097, by decide⟩,⟨147118, by decide⟩,⟨147125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18689_147126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18689 ⟨147126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18689
    ⟨147126, by decide⟩ (by decide) (![⟨147064, by decide⟩,⟨147097, by decide⟩,⟨147118, by decide⟩,⟨147125, by decide⟩]) unmarked_context_12_18689_147126 node_context_12_18689_147126
  intro a
  fin_cases a
  · exact context_13_74756_147064
  · exact context_13_74757_147097
  · exact context_13_74758_147118
  · exact context_13_74759_147125

theorem selected_cut_04548 : selected 7 ⟨147150, by decide⟩
    (prefixPartial 14 299040) = some ⟨14, 2, 0, 147150, 299040, 1281, 4096⟩ := by
  decide +kernel

theorem context_14_299040_147150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299040 ⟨147150, by decide⟩ :=
  accepted_of_selected 14 299040 ⟨147150, by decide⟩ ⟨14, 2, 0, 147150, 299040, 1281, 4096⟩
    (by decide) selected_cut_04548

theorem selected_cut_04549 : selected 7 ⟨147169, by decide⟩
    (prefixPartial 14 299041) = some ⟨14, 2, 0, 147169, 299041, 1009, 4096⟩ := by
  decide +kernel

theorem context_14_299041_147169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299041 ⟨147169, by decide⟩ :=
  accepted_of_selected 14 299041 ⟨147169, by decide⟩ ⟨14, 2, 0, 147169, 299041, 1009, 4096⟩
    (by decide) selected_cut_04549

theorem selected_cut_04550 : selected 7 ⟨147191, by decide⟩
    (prefixPartial 14 299042) = some ⟨14, 2, 0, 147191, 299042, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_299042_147191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299042 ⟨147191, by decide⟩ :=
  accepted_of_selected 14 299042 ⟨147191, by decide⟩ ⟨14, 2, 0, 147191, 299042, 1193, 4096⟩
    (by decide) selected_cut_04550

theorem selected_cut_04551 : selected 7 ⟨147207, by decide⟩
    (prefixPartial 14 299043) = some ⟨14, 2, 0, 147207, 299043, 1085, 4096⟩ := by
  decide +kernel

theorem context_14_299043_147207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299043 ⟨147207, by decide⟩ :=
  accepted_of_selected 14 299043 ⟨147207, by decide⟩ ⟨14, 2, 0, 147207, 299043, 1085, 4096⟩
    (by decide) selected_cut_04551

theorem unmarked_context_13_74760_147208 : frontier 8 ⟨147208, by decide⟩
    (prefixCache 13 74760) (prefixPartial 13 74760) = false := by
  decide +kernel

theorem node_context_13_74760_147208 : EJMOriginalGlobalDAGData.nodes 8 ⟨147208, by decide⟩ =
    .split (coordinate 13) (![⟨147150, by decide⟩,⟨147169, by decide⟩,⟨147191, by decide⟩,⟨147207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_74760_147208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74760 ⟨147208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 74760
    ⟨147208, by decide⟩ (by decide) (![⟨147150, by decide⟩,⟨147169, by decide⟩,⟨147191, by decide⟩,⟨147207, by decide⟩]) unmarked_context_13_74760_147208 node_context_13_74760_147208
  intro a
  fin_cases a
  · exact context_14_299040_147150
  · exact context_14_299041_147169
  · exact context_14_299042_147191
  · exact context_14_299043_147207

theorem selected_cut_04552 : selected 8 ⟨147260, by decide⟩
    (prefixPartial 13 74761) = some ⟨13, 2, 0, 147260, 74761, 3513, 16384⟩ := by
  decide +kernel

theorem context_13_74761_147260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74761 ⟨147260, by decide⟩ :=
  accepted_of_selected 13 74761 ⟨147260, by decide⟩ ⟨13, 2, 0, 147260, 74761, 3513, 16384⟩
    (by decide) selected_cut_04552

theorem selected_cut_04553 : selected 8 ⟨147289, by decide⟩
    (prefixPartial 13 74762) = some ⟨13, 2, 0, 147289, 74762, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_74762_147289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74762 ⟨147289, by decide⟩ :=
  accepted_of_selected 13 74762 ⟨147289, by decide⟩ ⟨13, 2, 0, 147289, 74762, 2409, 16384⟩
    (by decide) selected_cut_04553

theorem selected_cut_04554 : selected 8 ⟨147301, by decide⟩
    (prefixPartial 13 74763) = some ⟨13, 2, 0, 147301, 74763, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_74763_147301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74763 ⟨147301, by decide⟩ :=
  accepted_of_selected 13 74763 ⟨147301, by decide⟩ ⟨13, 2, 0, 147301, 74763, 1289, 16384⟩
    (by decide) selected_cut_04554

theorem unmarked_context_12_18690_147302 : frontier 9 ⟨147302, by decide⟩
    (prefixCache 12 18690) (prefixPartial 12 18690) = false := by
  decide +kernel

theorem node_context_12_18690_147302 : EJMOriginalGlobalDAGData.nodes 9 ⟨147302, by decide⟩ =
    .split (coordinate 12) (![⟨147208, by decide⟩,⟨147260, by decide⟩,⟨147289, by decide⟩,⟨147301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18690_147302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18690 ⟨147302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18690
    ⟨147302, by decide⟩ (by decide) (![⟨147208, by decide⟩,⟨147260, by decide⟩,⟨147289, by decide⟩,⟨147301, by decide⟩]) unmarked_context_12_18690_147302 node_context_12_18690_147302
  intro a
  fin_cases a
  · exact context_13_74760_147208
  · exact context_13_74761_147260
  · exact context_13_74762_147289
  · exact context_13_74763_147301

theorem selected_cut_04555 : selected 7 ⟨147326, by decide⟩
    (prefixPartial 14 299056) = some ⟨14, 2, 0, 147326, 299056, 1245, 4096⟩ := by
  decide +kernel

theorem context_14_299056_147326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299056 ⟨147326, by decide⟩ :=
  accepted_of_selected 14 299056 ⟨147326, by decide⟩ ⟨14, 2, 0, 147326, 299056, 1245, 4096⟩
    (by decide) selected_cut_04555

theorem selected_cut_04556 : selected 7 ⟨147343, by decide⟩
    (prefixPartial 14 299057) = some ⟨14, 2, 0, 147343, 299057, 1077, 4096⟩ := by
  decide +kernel

theorem context_14_299057_147343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299057 ⟨147343, by decide⟩ :=
  accepted_of_selected 14 299057 ⟨147343, by decide⟩ ⟨14, 2, 0, 147343, 299057, 1077, 4096⟩
    (by decide) selected_cut_04556

theorem selected_cut_04557 : selected 7 ⟨147364, by decide⟩
    (prefixPartial 14 299058) = some ⟨14, 2, 0, 147364, 299058, 1297, 4096⟩ := by
  decide +kernel

theorem context_14_299058_147364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299058 ⟨147364, by decide⟩ :=
  accepted_of_selected 14 299058 ⟨147364, by decide⟩ ⟨14, 2, 0, 147364, 299058, 1297, 4096⟩
    (by decide) selected_cut_04557

theorem selected_cut_04558 : selected 7 ⟨147382, by decide⟩
    (prefixPartial 14 299059) = some ⟨14, 2, 0, 147382, 299059, 1069, 4096⟩ := by
  decide +kernel

theorem context_14_299059_147382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299059 ⟨147382, by decide⟩ :=
  accepted_of_selected 14 299059 ⟨147382, by decide⟩ ⟨14, 2, 0, 147382, 299059, 1069, 4096⟩
    (by decide) selected_cut_04558

theorem unmarked_context_13_74764_147383 : frontier 8 ⟨147383, by decide⟩
    (prefixCache 13 74764) (prefixPartial 13 74764) = false := by
  decide +kernel

theorem node_context_13_74764_147383 : EJMOriginalGlobalDAGData.nodes 8 ⟨147383, by decide⟩ =
    .split (coordinate 13) (![⟨147326, by decide⟩,⟨147343, by decide⟩,⟨147364, by decide⟩,⟨147382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_74764_147383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74764 ⟨147383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 74764
    ⟨147383, by decide⟩ (by decide) (![⟨147326, by decide⟩,⟨147343, by decide⟩,⟨147364, by decide⟩,⟨147382, by decide⟩]) unmarked_context_13_74764_147383 node_context_13_74764_147383
  intro a
  fin_cases a
  · exact context_14_299056_147326
  · exact context_14_299057_147343
  · exact context_14_299058_147364
  · exact context_14_299059_147382

theorem selected_cut_04559 : selected 8 ⟨147439, by decide⟩
    (prefixPartial 13 74765) = some ⟨13, 2, 0, 147439, 74765, 3605, 16384⟩ := by
  decide +kernel

theorem context_13_74765_147439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74765 ⟨147439, by decide⟩ :=
  accepted_of_selected 13 74765 ⟨147439, by decide⟩ ⟨13, 2, 0, 147439, 74765, 3605, 16384⟩
    (by decide) selected_cut_04559

theorem selected_cut_04560 : selected 8 ⟨147474, by decide⟩
    (prefixPartial 13 74766) = some ⟨13, 2, 0, 147474, 74766, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_74766_147474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74766 ⟨147474, by decide⟩ :=
  accepted_of_selected 13 74766 ⟨147474, by decide⟩ ⟨13, 2, 0, 147474, 74766, 2549, 16384⟩
    (by decide) selected_cut_04560

theorem selected_cut_04561 : selected 8 ⟨147485, by decide⟩
    (prefixPartial 13 74767) = some ⟨13, 2, 0, 147485, 74767, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_74767_147485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74767 ⟨147485, by decide⟩ :=
  accepted_of_selected 13 74767 ⟨147485, by decide⟩ ⟨13, 2, 0, 147485, 74767, 1117, 16384⟩
    (by decide) selected_cut_04561

theorem unmarked_context_12_18691_147486 : frontier 9 ⟨147486, by decide⟩
    (prefixCache 12 18691) (prefixPartial 12 18691) = false := by
  decide +kernel

theorem node_context_12_18691_147486 : EJMOriginalGlobalDAGData.nodes 9 ⟨147486, by decide⟩ =
    .split (coordinate 12) (![⟨147383, by decide⟩,⟨147439, by decide⟩,⟨147474, by decide⟩,⟨147485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18691_147486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18691 ⟨147486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18691
    ⟨147486, by decide⟩ (by decide) (![⟨147383, by decide⟩,⟨147439, by decide⟩,⟨147474, by decide⟩,⟨147485, by decide⟩]) unmarked_context_12_18691_147486 node_context_12_18691_147486
  intro a
  fin_cases a
  · exact context_13_74764_147383
  · exact context_13_74765_147439
  · exact context_13_74766_147474
  · exact context_13_74767_147485

theorem unmarked_context_11_4672_147487 : frontier 10 ⟨147487, by decide⟩
    (prefixCache 11 4672) (prefixPartial 11 4672) = false := by
  decide +kernel

theorem node_context_11_4672_147487 : EJMOriginalGlobalDAGData.nodes 10 ⟨147487, by decide⟩ =
    .split (coordinate 11) (![⟨147002, by decide⟩,⟨147126, by decide⟩,⟨147302, by decide⟩,⟨147486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4672_147487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4672 ⟨147487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4672
    ⟨147487, by decide⟩ (by decide) (![⟨147002, by decide⟩,⟨147126, by decide⟩,⟨147302, by decide⟩,⟨147486, by decide⟩]) unmarked_context_11_4672_147487 node_context_11_4672_147487
  intro a
  fin_cases a
  · exact context_12_18688_147002
  · exact context_12_18689_147126
  · exact context_12_18690_147302
  · exact context_12_18691_147486

theorem selected_cut_04562 : selected 8 ⟨147538, by decide⟩
    (prefixPartial 13 74768) = some ⟨13, 2, 0, 147538, 74768, 3477, 16384⟩ := by
  decide +kernel

theorem context_13_74768_147538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74768 ⟨147538, by decide⟩ :=
  accepted_of_selected 13 74768 ⟨147538, by decide⟩ ⟨13, 2, 0, 147538, 74768, 3477, 16384⟩
    (by decide) selected_cut_04562

theorem selected_cut_04563 : selected 8 ⟨147590, by decide⟩
    (prefixPartial 13 74769) = some ⟨13, 2, 0, 147590, 74769, 3429, 16384⟩ := by
  decide +kernel

theorem context_13_74769_147590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74769 ⟨147590, by decide⟩ :=
  accepted_of_selected 13 74769 ⟨147590, by decide⟩ ⟨13, 2, 0, 147590, 74769, 3429, 16384⟩
    (by decide) selected_cut_04563

theorem selected_cut_04564 : selected 8 ⟨147611, by decide⟩
    (prefixPartial 13 74770) = some ⟨13, 2, 0, 147611, 74770, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_74770_147611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74770 ⟨147611, by decide⟩ :=
  accepted_of_selected 13 74770 ⟨147611, by decide⟩ ⟨13, 2, 0, 147611, 74770, 2117, 16384⟩
    (by decide) selected_cut_04564

theorem selected_cut_04565 : selected 8 ⟨147622, by decide⟩
    (prefixPartial 13 74771) = some ⟨13, 2, 0, 147622, 74771, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_74771_147622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74771 ⟨147622, by decide⟩ :=
  accepted_of_selected 13 74771 ⟨147622, by decide⟩ ⟨13, 2, 0, 147622, 74771, 1177, 16384⟩
    (by decide) selected_cut_04565

theorem unmarked_context_12_18692_147623 : frontier 9 ⟨147623, by decide⟩
    (prefixCache 12 18692) (prefixPartial 12 18692) = false := by
  decide +kernel

theorem node_context_12_18692_147623 : EJMOriginalGlobalDAGData.nodes 9 ⟨147623, by decide⟩ =
    .split (coordinate 12) (![⟨147538, by decide⟩,⟨147590, by decide⟩,⟨147611, by decide⟩,⟨147622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18692_147623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18692 ⟨147623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18692
    ⟨147623, by decide⟩ (by decide) (![⟨147538, by decide⟩,⟨147590, by decide⟩,⟨147611, by decide⟩,⟨147622, by decide⟩]) unmarked_context_12_18692_147623 node_context_12_18692_147623
  intro a
  fin_cases a
  · exact context_13_74768_147538
  · exact context_13_74769_147590
  · exact context_13_74770_147611
  · exact context_13_74771_147622

theorem selected_cut_04566 : selected 7 ⟨147660, by decide⟩
    (prefixPartial 14 299088) = some ⟨14, 2, 0, 147660, 299088, 1997, 4096⟩ := by
  decide +kernel

theorem context_14_299088_147660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299088 ⟨147660, by decide⟩ :=
  accepted_of_selected 14 299088 ⟨147660, by decide⟩ ⟨14, 2, 0, 147660, 299088, 1997, 4096⟩
    (by decide) selected_cut_04566

theorem selected_cut_04567 : selected 7 ⟨147676, by decide⟩
    (prefixPartial 14 299089) = some ⟨14, 2, 0, 147676, 299089, 1289, 4096⟩ := by
  decide +kernel

theorem context_14_299089_147676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299089 ⟨147676, by decide⟩ :=
  accepted_of_selected 14 299089 ⟨147676, by decide⟩ ⟨14, 2, 0, 147676, 299089, 1289, 4096⟩
    (by decide) selected_cut_04567

theorem selected_cut_04568 : selected 7 ⟨147701, by decide⟩
    (prefixPartial 14 299090) = some ⟨14, 2, 0, 147701, 299090, 1417, 4096⟩ := by
  decide +kernel

theorem context_14_299090_147701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299090 ⟨147701, by decide⟩ :=
  accepted_of_selected 14 299090 ⟨147701, by decide⟩ ⟨14, 2, 0, 147701, 299090, 1417, 4096⟩
    (by decide) selected_cut_04568

theorem selected_cut_04569 : selected 7 ⟨147723, by decide⟩
    (prefixPartial 14 299091) = some ⟨14, 2, 0, 147723, 299091, 1361, 4096⟩ := by
  decide +kernel

theorem context_14_299091_147723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299091 ⟨147723, by decide⟩ :=
  accepted_of_selected 14 299091 ⟨147723, by decide⟩ ⟨14, 2, 0, 147723, 299091, 1361, 4096⟩
    (by decide) selected_cut_04569

theorem unmarked_context_13_74772_147724 : frontier 8 ⟨147724, by decide⟩
    (prefixCache 13 74772) (prefixPartial 13 74772) = false := by
  decide +kernel

theorem node_context_13_74772_147724 : EJMOriginalGlobalDAGData.nodes 8 ⟨147724, by decide⟩ =
    .split (coordinate 13) (![⟨147660, by decide⟩,⟨147676, by decide⟩,⟨147701, by decide⟩,⟨147723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_74772_147724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74772 ⟨147724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 74772
    ⟨147724, by decide⟩ (by decide) (![⟨147660, by decide⟩,⟨147676, by decide⟩,⟨147701, by decide⟩,⟨147723, by decide⟩]) unmarked_context_13_74772_147724 node_context_13_74772_147724
  intro a
  fin_cases a
  · exact context_14_299088_147660
  · exact context_14_299089_147676
  · exact context_14_299090_147701
  · exact context_14_299091_147723

theorem selected_cut_04570 : selected 7 ⟨147739, by decide⟩
    (prefixPartial 14 299092) = some ⟨14, 2, 0, 147739, 299092, 981, 4096⟩ := by
  decide +kernel

theorem context_14_299092_147739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299092 ⟨147739, by decide⟩ :=
  accepted_of_selected 14 299092 ⟨147739, by decide⟩ ⟨14, 2, 0, 147739, 299092, 981, 4096⟩
    (by decide) selected_cut_04570

theorem selected_cut_04571 : selected 7 ⟨147764, by decide⟩
    (prefixPartial 14 299093) = some ⟨14, 2, 0, 147764, 299093, 1297, 4096⟩ := by
  decide +kernel

theorem context_14_299093_147764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299093 ⟨147764, by decide⟩ :=
  accepted_of_selected 14 299093 ⟨147764, by decide⟩ ⟨14, 2, 0, 147764, 299093, 1297, 4096⟩
    (by decide) selected_cut_04571

theorem selected_cut_04572 : selected 7 ⟨147794, by decide⟩
    (prefixPartial 14 299094) = some ⟨14, 2, 0, 147794, 299094, 1425, 4096⟩ := by
  decide +kernel

theorem context_14_299094_147794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299094 ⟨147794, by decide⟩ :=
  accepted_of_selected 14 299094 ⟨147794, by decide⟩ ⟨14, 2, 0, 147794, 299094, 1425, 4096⟩
    (by decide) selected_cut_04572

theorem selected_cut_04573 : selected 7 ⟨147817, by decide⟩
    (prefixPartial 14 299095) = some ⟨14, 2, 0, 147817, 299095, 1237, 4096⟩ := by
  decide +kernel

theorem context_14_299095_147817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299095 ⟨147817, by decide⟩ :=
  accepted_of_selected 14 299095 ⟨147817, by decide⟩ ⟨14, 2, 0, 147817, 299095, 1237, 4096⟩
    (by decide) selected_cut_04573

theorem unmarked_context_13_74773_147818 : frontier 8 ⟨147818, by decide⟩
    (prefixCache 13 74773) (prefixPartial 13 74773) = false := by
  decide +kernel

theorem node_context_13_74773_147818 : EJMOriginalGlobalDAGData.nodes 8 ⟨147818, by decide⟩ =
    .split (coordinate 13) (![⟨147739, by decide⟩,⟨147764, by decide⟩,⟨147794, by decide⟩,⟨147817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_74773_147818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74773 ⟨147818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 74773
    ⟨147818, by decide⟩ (by decide) (![⟨147739, by decide⟩,⟨147764, by decide⟩,⟨147794, by decide⟩,⟨147817, by decide⟩]) unmarked_context_13_74773_147818 node_context_13_74773_147818
  intro a
  fin_cases a
  · exact context_14_299092_147739
  · exact context_14_299093_147764
  · exact context_14_299094_147794
  · exact context_14_299095_147817

theorem selected_cut_04574 : selected 8 ⟨147860, by decide⟩
    (prefixPartial 13 74774) = some ⟨13, 2, 0, 147860, 74774, 2805, 16384⟩ := by
  decide +kernel

theorem context_13_74774_147860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74774 ⟨147860, by decide⟩ :=
  accepted_of_selected 13 74774 ⟨147860, by decide⟩ ⟨13, 2, 0, 147860, 74774, 2805, 16384⟩
    (by decide) selected_cut_04574

theorem selected_cut_04575 : selected 8 ⟨147890, by decide⟩
    (prefixPartial 13 74775) = some ⟨13, 2, 0, 147890, 74775, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_74775_147890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74775 ⟨147890, by decide⟩ :=
  accepted_of_selected 13 74775 ⟨147890, by decide⟩ ⟨13, 2, 0, 147890, 74775, 1481, 16384⟩
    (by decide) selected_cut_04575

theorem unmarked_context_12_18693_147891 : frontier 9 ⟨147891, by decide⟩
    (prefixCache 12 18693) (prefixPartial 12 18693) = false := by
  decide +kernel

theorem node_context_12_18693_147891 : EJMOriginalGlobalDAGData.nodes 9 ⟨147891, by decide⟩ =
    .split (coordinate 12) (![⟨147724, by decide⟩,⟨147818, by decide⟩,⟨147860, by decide⟩,⟨147890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18693_147891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18693 ⟨147891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18693
    ⟨147891, by decide⟩ (by decide) (![⟨147724, by decide⟩,⟨147818, by decide⟩,⟨147860, by decide⟩,⟨147890, by decide⟩]) unmarked_context_12_18693_147891 node_context_12_18693_147891
  intro a
  fin_cases a
  · exact context_13_74772_147724
  · exact context_13_74773_147818
  · exact context_13_74774_147860
  · exact context_13_74775_147890

theorem selected_cut_04576 : selected 7 ⟨147911, by decide⟩
    (prefixPartial 14 299104) = some ⟨14, 2, 0, 147911, 299104, 1029, 4096⟩ := by
  decide +kernel

theorem context_14_299104_147911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299104 ⟨147911, by decide⟩ :=
  accepted_of_selected 14 299104 ⟨147911, by decide⟩ ⟨14, 2, 0, 147911, 299104, 1029, 4096⟩
    (by decide) selected_cut_04576

theorem selected_cut_04577 : selected 7 ⟨147928, by decide⟩
    (prefixPartial 14 299105) = some ⟨14, 2, 0, 147928, 299105, 1037, 4096⟩ := by
  decide +kernel

theorem context_14_299105_147928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299105 ⟨147928, by decide⟩ :=
  accepted_of_selected 14 299105 ⟨147928, by decide⟩ ⟨14, 2, 0, 147928, 299105, 1037, 4096⟩
    (by decide) selected_cut_04577

theorem selected_cut_04578 : selected 7 ⟨147943, by decide⟩
    (prefixPartial 14 299106) = some ⟨14, 2, 0, 147943, 299106, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_299106_147943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299106 ⟨147943, by decide⟩ :=
  accepted_of_selected 14 299106 ⟨147943, by decide⟩ ⟨14, 2, 0, 147943, 299106, 1193, 4096⟩
    (by decide) selected_cut_04578

theorem selected_cut_04579 : selected 7 ⟨147959, by decide⟩
    (prefixPartial 14 299107) = some ⟨14, 2, 0, 147959, 299107, 1109, 4096⟩ := by
  decide +kernel

theorem context_14_299107_147959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299107 ⟨147959, by decide⟩ :=
  accepted_of_selected 14 299107 ⟨147959, by decide⟩ ⟨14, 2, 0, 147959, 299107, 1109, 4096⟩
    (by decide) selected_cut_04579

theorem unmarked_context_13_74776_147960 : frontier 8 ⟨147960, by decide⟩
    (prefixCache 13 74776) (prefixPartial 13 74776) = false := by
  decide +kernel

theorem node_context_13_74776_147960 : EJMOriginalGlobalDAGData.nodes 8 ⟨147960, by decide⟩ =
    .split (coordinate 13) (![⟨147911, by decide⟩,⟨147928, by decide⟩,⟨147943, by decide⟩,⟨147959, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_74776_147960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74776 ⟨147960, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 74776
    ⟨147960, by decide⟩ (by decide) (![⟨147911, by decide⟩,⟨147928, by decide⟩,⟨147943, by decide⟩,⟨147959, by decide⟩]) unmarked_context_13_74776_147960 node_context_13_74776_147960
  intro a
  fin_cases a
  · exact context_14_299104_147911
  · exact context_14_299105_147928
  · exact context_14_299106_147943
  · exact context_14_299107_147959

theorem selected_cut_04580 : selected 8 ⟨148027, by decide⟩
    (prefixPartial 13 74777) = some ⟨13, 2, 0, 148027, 74777, 3833, 16384⟩ := by
  decide +kernel

theorem context_13_74777_148027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74777 ⟨148027, by decide⟩ :=
  accepted_of_selected 13 74777 ⟨148027, by decide⟩ ⟨13, 2, 0, 148027, 74777, 3833, 16384⟩
    (by decide) selected_cut_04580

theorem selected_cut_04581 : selected 8 ⟨148050, by decide⟩
    (prefixPartial 13 74778) = some ⟨13, 2, 0, 148050, 74778, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_74778_148050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74778 ⟨148050, by decide⟩ :=
  accepted_of_selected 13 74778 ⟨148050, by decide⟩ ⟨13, 2, 0, 148050, 74778, 2357, 16384⟩
    (by decide) selected_cut_04581

theorem selected_cut_04582 : selected 8 ⟨148063, by decide⟩
    (prefixPartial 13 74779) = some ⟨13, 2, 0, 148063, 74779, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_74779_148063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74779 ⟨148063, by decide⟩ :=
  accepted_of_selected 13 74779 ⟨148063, by decide⟩ ⟨13, 2, 0, 148063, 74779, 1265, 16384⟩
    (by decide) selected_cut_04582

theorem unmarked_context_12_18694_148064 : frontier 9 ⟨148064, by decide⟩
    (prefixCache 12 18694) (prefixPartial 12 18694) = false := by
  decide +kernel

theorem node_context_12_18694_148064 : EJMOriginalGlobalDAGData.nodes 9 ⟨148064, by decide⟩ =
    .split (coordinate 12) (![⟨147960, by decide⟩,⟨148027, by decide⟩,⟨148050, by decide⟩,⟨148063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18694_148064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18694 ⟨148064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18694
    ⟨148064, by decide⟩ (by decide) (![⟨147960, by decide⟩,⟨148027, by decide⟩,⟨148050, by decide⟩,⟨148063, by decide⟩]) unmarked_context_12_18694_148064 node_context_12_18694_148064
  intro a
  fin_cases a
  · exact context_13_74776_147960
  · exact context_13_74777_148027
  · exact context_13_74778_148050
  · exact context_13_74779_148063

theorem selected_cut_04583 : selected 7 ⟨148079, by decide⟩
    (prefixPartial 14 299120) = some ⟨14, 2, 0, 148079, 299120, 881, 4096⟩ := by
  decide +kernel

theorem context_14_299120_148079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299120 ⟨148079, by decide⟩ :=
  accepted_of_selected 14 299120 ⟨148079, by decide⟩ ⟨14, 2, 0, 148079, 299120, 881, 4096⟩
    (by decide) selected_cut_04583

theorem selected_cut_04584 : selected 7 ⟨148094, by decide⟩
    (prefixPartial 14 299121) = some ⟨14, 2, 0, 148094, 299121, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_299121_148094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299121 ⟨148094, by decide⟩ :=
  accepted_of_selected 14 299121 ⟨148094, by decide⟩ ⟨14, 2, 0, 148094, 299121, 1097, 4096⟩
    (by decide) selected_cut_04584

theorem selected_cut_04585 : selected 7 ⟨148114, by decide⟩
    (prefixPartial 14 299122) = some ⟨14, 2, 0, 148114, 299122, 1301, 4096⟩ := by
  decide +kernel

theorem context_14_299122_148114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299122 ⟨148114, by decide⟩ :=
  accepted_of_selected 14 299122 ⟨148114, by decide⟩ ⟨14, 2, 0, 148114, 299122, 1301, 4096⟩
    (by decide) selected_cut_04585

theorem selected_cut_04586 : selected 7 ⟨148128, by decide⟩
    (prefixPartial 14 299123) = some ⟨14, 2, 0, 148128, 299123, 1025, 4096⟩ := by
  decide +kernel

theorem context_14_299123_148128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299123 ⟨148128, by decide⟩ :=
  accepted_of_selected 14 299123 ⟨148128, by decide⟩ ⟨14, 2, 0, 148128, 299123, 1025, 4096⟩
    (by decide) selected_cut_04586

theorem unmarked_context_13_74780_148129 : frontier 8 ⟨148129, by decide⟩
    (prefixCache 13 74780) (prefixPartial 13 74780) = false := by
  decide +kernel

theorem node_context_13_74780_148129 : EJMOriginalGlobalDAGData.nodes 8 ⟨148129, by decide⟩ =
    .split (coordinate 13) (![⟨148079, by decide⟩,⟨148094, by decide⟩,⟨148114, by decide⟩,⟨148128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_74780_148129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74780 ⟨148129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 74780
    ⟨148129, by decide⟩ (by decide) (![⟨148079, by decide⟩,⟨148094, by decide⟩,⟨148114, by decide⟩,⟨148128, by decide⟩]) unmarked_context_13_74780_148129 node_context_13_74780_148129
  intro a
  fin_cases a
  · exact context_14_299120_148079
  · exact context_14_299121_148094
  · exact context_14_299122_148114
  · exact context_14_299123_148128

theorem selected_cut_04587 : selected 8 ⟨148201, by decide⟩
    (prefixPartial 13 74781) = some ⟨13, 2, 0, 148201, 74781, 4005, 16384⟩ := by
  decide +kernel

theorem context_13_74781_148201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74781 ⟨148201, by decide⟩ :=
  accepted_of_selected 13 74781 ⟨148201, by decide⟩ ⟨13, 2, 0, 148201, 74781, 4005, 16384⟩
    (by decide) selected_cut_04587

theorem selected_cut_04588 : selected 8 ⟨148222, by decide⟩
    (prefixPartial 13 74782) = some ⟨13, 2, 0, 148222, 74782, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_74782_148222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74782 ⟨148222, by decide⟩ :=
  accepted_of_selected 13 74782 ⟨148222, by decide⟩ ⟨13, 2, 0, 148222, 74782, 2357, 16384⟩
    (by decide) selected_cut_04588

theorem selected_cut_04589 : selected 8 ⟨148230, by decide⟩
    (prefixPartial 13 74783) = some ⟨13, 2, 0, 148230, 74783, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_74783_148230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74783 ⟨148230, by decide⟩ :=
  accepted_of_selected 13 74783 ⟨148230, by decide⟩ ⟨13, 2, 0, 148230, 74783, 1157, 16384⟩
    (by decide) selected_cut_04589

theorem unmarked_context_12_18695_148231 : frontier 9 ⟨148231, by decide⟩
    (prefixCache 12 18695) (prefixPartial 12 18695) = false := by
  decide +kernel

theorem node_context_12_18695_148231 : EJMOriginalGlobalDAGData.nodes 9 ⟨148231, by decide⟩ =
    .split (coordinate 12) (![⟨148129, by decide⟩,⟨148201, by decide⟩,⟨148222, by decide⟩,⟨148230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18695_148231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18695 ⟨148231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18695
    ⟨148231, by decide⟩ (by decide) (![⟨148129, by decide⟩,⟨148201, by decide⟩,⟨148222, by decide⟩,⟨148230, by decide⟩]) unmarked_context_12_18695_148231 node_context_12_18695_148231
  intro a
  fin_cases a
  · exact context_13_74780_148129
  · exact context_13_74781_148201
  · exact context_13_74782_148222
  · exact context_13_74783_148230

theorem unmarked_context_11_4673_148232 : frontier 10 ⟨148232, by decide⟩
    (prefixCache 11 4673) (prefixPartial 11 4673) = false := by
  decide +kernel

theorem node_context_11_4673_148232 : EJMOriginalGlobalDAGData.nodes 10 ⟨148232, by decide⟩ =
    .split (coordinate 11) (![⟨147623, by decide⟩,⟨147891, by decide⟩,⟨148064, by decide⟩,⟨148231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4673_148232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4673 ⟨148232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4673
    ⟨148232, by decide⟩ (by decide) (![⟨147623, by decide⟩,⟨147891, by decide⟩,⟨148064, by decide⟩,⟨148231, by decide⟩]) unmarked_context_11_4673_148232 node_context_11_4673_148232
  intro a
  fin_cases a
  · exact context_12_18692_147623
  · exact context_12_18693_147891
  · exact context_12_18694_148064
  · exact context_12_18695_148231

theorem selected_cut_04590 : selected 8 ⟨148286, by decide⟩
    (prefixPartial 13 74784) = some ⟨13, 2, 0, 148286, 74784, 3101, 16384⟩ := by
  decide +kernel

theorem context_13_74784_148286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74784 ⟨148286, by decide⟩ :=
  accepted_of_selected 13 74784 ⟨148286, by decide⟩ ⟨13, 2, 0, 148286, 74784, 3101, 16384⟩
    (by decide) selected_cut_04590

theorem selected_cut_04591 : selected 8 ⟨148360, by decide⟩
    (prefixPartial 13 74785) = some ⟨13, 2, 0, 148360, 74785, 3989, 16384⟩ := by
  decide +kernel

theorem context_13_74785_148360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74785 ⟨148360, by decide⟩ :=
  accepted_of_selected 13 74785 ⟨148360, by decide⟩ ⟨13, 2, 0, 148360, 74785, 3989, 16384⟩
    (by decide) selected_cut_04591

theorem selected_cut_04592 : selected 8 ⟨148383, by decide⟩
    (prefixPartial 13 74786) = some ⟨13, 2, 0, 148383, 74786, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_74786_148383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74786 ⟨148383, by decide⟩ :=
  accepted_of_selected 13 74786 ⟨148383, by decide⟩ ⟨13, 2, 0, 148383, 74786, 2257, 16384⟩
    (by decide) selected_cut_04592

theorem selected_cut_04593 : selected 8 ⟨148390, by decide⟩
    (prefixPartial 13 74787) = some ⟨13, 2, 0, 148390, 74787, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_74787_148390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74787 ⟨148390, by decide⟩ :=
  accepted_of_selected 13 74787 ⟨148390, by decide⟩ ⟨13, 2, 0, 148390, 74787, 1145, 16384⟩
    (by decide) selected_cut_04593

theorem unmarked_context_12_18696_148391 : frontier 9 ⟨148391, by decide⟩
    (prefixCache 12 18696) (prefixPartial 12 18696) = false := by
  decide +kernel

theorem node_context_12_18696_148391 : EJMOriginalGlobalDAGData.nodes 9 ⟨148391, by decide⟩ =
    .split (coordinate 12) (![⟨148286, by decide⟩,⟨148360, by decide⟩,⟨148383, by decide⟩,⟨148390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18696_148391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18696 ⟨148391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18696
    ⟨148391, by decide⟩ (by decide) (![⟨148286, by decide⟩,⟨148360, by decide⟩,⟨148383, by decide⟩,⟨148390, by decide⟩]) unmarked_context_12_18696_148391 node_context_12_18696_148391
  intro a
  fin_cases a
  · exact context_13_74784_148286
  · exact context_13_74785_148360
  · exact context_13_74786_148383
  · exact context_13_74787_148390

theorem selected_cut_04594 : selected 8 ⟨148449, by decide⟩
    (prefixPartial 13 74788) = some ⟨13, 2, 0, 148449, 74788, 3533, 16384⟩ := by
  decide +kernel

theorem context_13_74788_148449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74788 ⟨148449, by decide⟩ :=
  accepted_of_selected 13 74788 ⟨148449, by decide⟩ ⟨13, 2, 0, 148449, 74788, 3533, 16384⟩
    (by decide) selected_cut_04594

theorem selected_cut_04595 : selected 8 ⟨148484, by decide⟩
    (prefixPartial 13 74789) = some ⟨13, 2, 0, 148484, 74789, 3313, 16384⟩ := by
  decide +kernel

theorem context_13_74789_148484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74789 ⟨148484, by decide⟩ :=
  accepted_of_selected 13 74789 ⟨148484, by decide⟩ ⟨13, 2, 0, 148484, 74789, 3313, 16384⟩
    (by decide) selected_cut_04595

theorem selected_cut_04596 : selected 8 ⟨148506, by decide⟩
    (prefixPartial 13 74790) = some ⟨13, 2, 0, 148506, 74790, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_74790_148506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74790 ⟨148506, by decide⟩ :=
  accepted_of_selected 13 74790 ⟨148506, by decide⟩ ⟨13, 2, 0, 148506, 74790, 2353, 16384⟩
    (by decide) selected_cut_04596

theorem selected_cut_04597 : selected 8 ⟨148512, by decide⟩
    (prefixPartial 13 74791) = some ⟨13, 2, 0, 148512, 74791, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_74791_148512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74791 ⟨148512, by decide⟩ :=
  accepted_of_selected 13 74791 ⟨148512, by decide⟩ ⟨13, 2, 0, 148512, 74791, 1165, 16384⟩
    (by decide) selected_cut_04597

theorem unmarked_context_12_18697_148513 : frontier 9 ⟨148513, by decide⟩
    (prefixCache 12 18697) (prefixPartial 12 18697) = false := by
  decide +kernel

theorem node_context_12_18697_148513 : EJMOriginalGlobalDAGData.nodes 9 ⟨148513, by decide⟩ =
    .split (coordinate 12) (![⟨148449, by decide⟩,⟨148484, by decide⟩,⟨148506, by decide⟩,⟨148512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18697_148513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18697 ⟨148513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18697
    ⟨148513, by decide⟩ (by decide) (![⟨148449, by decide⟩,⟨148484, by decide⟩,⟨148506, by decide⟩,⟨148512, by decide⟩]) unmarked_context_12_18697_148513 node_context_12_18697_148513
  intro a
  fin_cases a
  · exact context_13_74788_148449
  · exact context_13_74789_148484
  · exact context_13_74790_148506
  · exact context_13_74791_148512

theorem selected_cut_04598 : selected 8 ⟨148581, by decide⟩
    (prefixPartial 13 74792) = some ⟨13, 2, 0, 148581, 74792, 3785, 16384⟩ := by
  decide +kernel

theorem context_13_74792_148581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74792 ⟨148581, by decide⟩ :=
  accepted_of_selected 13 74792 ⟨148581, by decide⟩ ⟨13, 2, 0, 148581, 74792, 3785, 16384⟩
    (by decide) selected_cut_04598

theorem selected_cut_04599 : selected 8 ⟨148632, by decide⟩
    (prefixPartial 13 74793) = some ⟨13, 2, 0, 148632, 74793, 3613, 16384⟩ := by
  decide +kernel

theorem context_13_74793_148632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74793 ⟨148632, by decide⟩ :=
  accepted_of_selected 13 74793 ⟨148632, by decide⟩ ⟨13, 2, 0, 148632, 74793, 3613, 16384⟩
    (by decide) selected_cut_04599

theorem selected_cut_04600 : selected 8 ⟨148655, by decide⟩
    (prefixPartial 13 74794) = some ⟨13, 2, 0, 148655, 74794, 2465, 16384⟩ := by
  decide +kernel

theorem context_13_74794_148655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74794 ⟨148655, by decide⟩ :=
  accepted_of_selected 13 74794 ⟨148655, by decide⟩ ⟨13, 2, 0, 148655, 74794, 2465, 16384⟩
    (by decide) selected_cut_04600

theorem selected_cut_04601 : selected 8 ⟨148663, by decide⟩
    (prefixPartial 13 74795) = some ⟨13, 2, 0, 148663, 74795, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_74795_148663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74795 ⟨148663, by decide⟩ :=
  accepted_of_selected 13 74795 ⟨148663, by decide⟩ ⟨13, 2, 0, 148663, 74795, 1173, 16384⟩
    (by decide) selected_cut_04601

theorem unmarked_context_12_18698_148664 : frontier 9 ⟨148664, by decide⟩
    (prefixCache 12 18698) (prefixPartial 12 18698) = false := by
  decide +kernel

theorem node_context_12_18698_148664 : EJMOriginalGlobalDAGData.nodes 9 ⟨148664, by decide⟩ =
    .split (coordinate 12) (![⟨148581, by decide⟩,⟨148632, by decide⟩,⟨148655, by decide⟩,⟨148663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18698_148664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18698 ⟨148664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18698
    ⟨148664, by decide⟩ (by decide) (![⟨148581, by decide⟩,⟨148632, by decide⟩,⟨148655, by decide⟩,⟨148663, by decide⟩]) unmarked_context_12_18698_148664 node_context_12_18698_148664
  intro a
  fin_cases a
  · exact context_13_74792_148581
  · exact context_13_74793_148632
  · exact context_13_74794_148655
  · exact context_13_74795_148663

theorem selected_cut_04602 : selected 8 ⟨148729, by decide⟩
    (prefixPartial 13 74796) = some ⟨13, 2, 0, 148729, 74796, 3977, 16384⟩ := by
  decide +kernel

theorem context_13_74796_148729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74796 ⟨148729, by decide⟩ :=
  accepted_of_selected 13 74796 ⟨148729, by decide⟩ ⟨13, 2, 0, 148729, 74796, 3977, 16384⟩
    (by decide) selected_cut_04602

theorem selected_cut_04603 : selected 7 ⟨148756, by decide⟩
    (prefixPartial 14 299188) = some ⟨14, 2, 0, 148756, 299188, 1125, 4096⟩ := by
  decide +kernel

theorem context_14_299188_148756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299188 ⟨148756, by decide⟩ :=
  accepted_of_selected 14 299188 ⟨148756, by decide⟩ ⟨14, 2, 0, 148756, 299188, 1125, 4096⟩
    (by decide) selected_cut_04603

theorem selected_cut_04604 : selected 7 ⟨148772, by decide⟩
    (prefixPartial 14 299189) = some ⟨14, 2, 0, 148772, 299189, 985, 4096⟩ := by
  decide +kernel

theorem context_14_299189_148772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299189 ⟨148772, by decide⟩ :=
  accepted_of_selected 14 299189 ⟨148772, by decide⟩ ⟨14, 2, 0, 148772, 299189, 985, 4096⟩
    (by decide) selected_cut_04604

theorem selected_cut_04605 : selected 7 ⟨148792, by decide⟩
    (prefixPartial 14 299190) = some ⟨14, 2, 0, 148792, 299190, 1201, 4096⟩ := by
  decide +kernel

theorem context_14_299190_148792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299190 ⟨148792, by decide⟩ :=
  accepted_of_selected 14 299190 ⟨148792, by decide⟩ ⟨14, 2, 0, 148792, 299190, 1201, 4096⟩
    (by decide) selected_cut_04605

theorem selected_cut_04606 : selected 7 ⟨148811, by decide⟩
    (prefixPartial 14 299191) = some ⟨14, 2, 0, 148811, 299191, 1037, 4096⟩ := by
  decide +kernel

theorem context_14_299191_148811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 299191 ⟨148811, by decide⟩ :=
  accepted_of_selected 14 299191 ⟨148811, by decide⟩ ⟨14, 2, 0, 148811, 299191, 1037, 4096⟩
    (by decide) selected_cut_04606

theorem unmarked_context_13_74797_148812 : frontier 8 ⟨148812, by decide⟩
    (prefixCache 13 74797) (prefixPartial 13 74797) = false := by
  decide +kernel

theorem node_context_13_74797_148812 : EJMOriginalGlobalDAGData.nodes 8 ⟨148812, by decide⟩ =
    .split (coordinate 13) (![⟨148756, by decide⟩,⟨148772, by decide⟩,⟨148792, by decide⟩,⟨148811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_74797_148812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74797 ⟨148812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 74797
    ⟨148812, by decide⟩ (by decide) (![⟨148756, by decide⟩,⟨148772, by decide⟩,⟨148792, by decide⟩,⟨148811, by decide⟩]) unmarked_context_13_74797_148812 node_context_13_74797_148812
  intro a
  fin_cases a
  · exact context_14_299188_148756
  · exact context_14_299189_148772
  · exact context_14_299190_148792
  · exact context_14_299191_148811

theorem selected_cut_04607 : selected 8 ⟨148840, by decide⟩
    (prefixPartial 13 74798) = some ⟨13, 2, 0, 148840, 74798, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_74798_148840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74798 ⟨148840, by decide⟩ :=
  accepted_of_selected 13 74798 ⟨148840, by decide⟩ ⟨13, 2, 0, 148840, 74798, 2541, 16384⟩
    (by decide) selected_cut_04607

theorem selected_cut_04608 : selected 8 ⟨148847, by decide⟩
    (prefixPartial 13 74799) = some ⟨13, 2, 0, 148847, 74799, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_74799_148847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74799 ⟨148847, by decide⟩ :=
  accepted_of_selected 13 74799 ⟨148847, by decide⟩ ⟨13, 2, 0, 148847, 74799, 1237, 16384⟩
    (by decide) selected_cut_04608

theorem unmarked_context_12_18699_148848 : frontier 9 ⟨148848, by decide⟩
    (prefixCache 12 18699) (prefixPartial 12 18699) = false := by
  decide +kernel

theorem node_context_12_18699_148848 : EJMOriginalGlobalDAGData.nodes 9 ⟨148848, by decide⟩ =
    .split (coordinate 12) (![⟨148729, by decide⟩,⟨148812, by decide⟩,⟨148840, by decide⟩,⟨148847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18699_148848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18699 ⟨148848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18699
    ⟨148848, by decide⟩ (by decide) (![⟨148729, by decide⟩,⟨148812, by decide⟩,⟨148840, by decide⟩,⟨148847, by decide⟩]) unmarked_context_12_18699_148848 node_context_12_18699_148848
  intro a
  fin_cases a
  · exact context_13_74796_148729
  · exact context_13_74797_148812
  · exact context_13_74798_148840
  · exact context_13_74799_148847

theorem unmarked_context_11_4674_148849 : frontier 10 ⟨148849, by decide⟩
    (prefixCache 11 4674) (prefixPartial 11 4674) = false := by
  decide +kernel

theorem node_context_11_4674_148849 : EJMOriginalGlobalDAGData.nodes 10 ⟨148849, by decide⟩ =
    .split (coordinate 11) (![⟨148391, by decide⟩,⟨148513, by decide⟩,⟨148664, by decide⟩,⟨148848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4674_148849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4674 ⟨148849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4674
    ⟨148849, by decide⟩ (by decide) (![⟨148391, by decide⟩,⟨148513, by decide⟩,⟨148664, by decide⟩,⟨148848, by decide⟩]) unmarked_context_11_4674_148849 node_context_11_4674_148849
  intro a
  fin_cases a
  · exact context_12_18696_148391
  · exact context_12_18697_148513
  · exact context_12_18698_148664
  · exact context_12_18699_148848

theorem selected_cut_04609 : selected 8 ⟨148899, by decide⟩
    (prefixPartial 13 74800) = some ⟨13, 2, 0, 148899, 74800, 2861, 16384⟩ := by
  decide +kernel

theorem context_13_74800_148899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74800 ⟨148899, by decide⟩ :=
  accepted_of_selected 13 74800 ⟨148899, by decide⟩ ⟨13, 2, 0, 148899, 74800, 2861, 16384⟩
    (by decide) selected_cut_04609

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
