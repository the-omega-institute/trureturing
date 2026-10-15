/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover014
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_01442 : selected 8 ⟨52675, by decide⟩
    (prefixPartial 13 18533) = some ⟨13, 2, 0, 52675, 18533, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_18533_52675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18533 ⟨52675, by decide⟩ :=
  accepted_of_selected 13 18533 ⟨52675, by decide⟩ ⟨13, 2, 0, 52675, 18533, 2385, 16384⟩
    (by decide) selected_cut_01442

theorem selected_cut_01443 : selected 8 ⟨52701, by decide⟩
    (prefixPartial 13 18534) = some ⟨13, 2, 0, 52701, 18534, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_18534_52701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18534 ⟨52701, by decide⟩ :=
  accepted_of_selected 13 18534 ⟨52701, by decide⟩ ⟨13, 2, 0, 52701, 18534, 1997, 16384⟩
    (by decide) selected_cut_01443

theorem selected_cut_01444 : selected 8 ⟨52712, by decide⟩
    (prefixPartial 13 18535) = some ⟨13, 2, 0, 52712, 18535, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_18535_52712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18535 ⟨52712, by decide⟩ :=
  accepted_of_selected 13 18535 ⟨52712, by decide⟩ ⟨13, 2, 0, 52712, 18535, 1113, 16384⟩
    (by decide) selected_cut_01444

theorem unmarked_context_12_4633_52713 : frontier 9 ⟨52713, by decide⟩
    (prefixCache 12 4633) (prefixPartial 12 4633) = false := by
  decide +kernel

theorem node_context_12_4633_52713 : EJMOriginalGlobalDAGData.nodes 9 ⟨52713, by decide⟩ =
    .split (coordinate 12) (![⟨52635, by decide⟩,⟨52675, by decide⟩,⟨52701, by decide⟩,⟨52712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4633_52713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4633 ⟨52713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4633
    ⟨52713, by decide⟩ (by decide) (![⟨52635, by decide⟩,⟨52675, by decide⟩,⟨52701, by decide⟩,⟨52712, by decide⟩]) unmarked_context_12_4633_52713 node_context_12_4633_52713
  intro a
  fin_cases a
  · exact context_13_18532_52635
  · exact context_13_18533_52675
  · exact context_13_18534_52701
  · exact context_13_18535_52712

theorem selected_cut_01445 : selected 8 ⟨52752, by decide⟩
    (prefixPartial 13 18536) = some ⟨13, 2, 0, 52752, 18536, 3049, 16384⟩ := by
  decide +kernel

theorem context_13_18536_52752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18536 ⟨52752, by decide⟩ :=
  accepted_of_selected 13 18536 ⟨52752, by decide⟩ ⟨13, 2, 0, 52752, 18536, 3049, 16384⟩
    (by decide) selected_cut_01445

theorem selected_cut_01446 : selected 8 ⟨52812, by decide⟩
    (prefixPartial 13 18537) = some ⟨13, 2, 0, 52812, 18537, 4037, 16384⟩ := by
  decide +kernel

theorem context_13_18537_52812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18537 ⟨52812, by decide⟩ :=
  accepted_of_selected 13 18537 ⟨52812, by decide⟩ ⟨13, 2, 0, 52812, 18537, 4037, 16384⟩
    (by decide) selected_cut_01446

theorem selected_cut_01447 : selected 8 ⟨52862, by decide⟩
    (prefixPartial 13 18538) = some ⟨13, 2, 0, 52862, 18538, 2925, 16384⟩ := by
  decide +kernel

theorem context_13_18538_52862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18538 ⟨52862, by decide⟩ :=
  accepted_of_selected 13 18538 ⟨52862, by decide⟩ ⟨13, 2, 0, 52862, 18538, 2925, 16384⟩
    (by decide) selected_cut_01447

theorem selected_cut_01448 : selected 8 ⟨52899, by decide⟩
    (prefixPartial 13 18539) = some ⟨13, 2, 0, 52899, 18539, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_18539_52899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18539 ⟨52899, by decide⟩ :=
  accepted_of_selected 13 18539 ⟨52899, by decide⟩ ⟨13, 2, 0, 52899, 18539, 1573, 16384⟩
    (by decide) selected_cut_01448

theorem unmarked_context_12_4634_52900 : frontier 9 ⟨52900, by decide⟩
    (prefixCache 12 4634) (prefixPartial 12 4634) = false := by
  decide +kernel

theorem node_context_12_4634_52900 : EJMOriginalGlobalDAGData.nodes 9 ⟨52900, by decide⟩ =
    .split (coordinate 12) (![⟨52752, by decide⟩,⟨52812, by decide⟩,⟨52862, by decide⟩,⟨52899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4634_52900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4634 ⟨52900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4634
    ⟨52900, by decide⟩ (by decide) (![⟨52752, by decide⟩,⟨52812, by decide⟩,⟨52862, by decide⟩,⟨52899, by decide⟩]) unmarked_context_12_4634_52900 node_context_12_4634_52900
  intro a
  fin_cases a
  · exact context_13_18536_52752
  · exact context_13_18537_52812
  · exact context_13_18538_52862
  · exact context_13_18539_52899

theorem selected_cut_01449 : selected 8 ⟨52937, by decide⟩
    (prefixPartial 13 18540) = some ⟨13, 2, 0, 52937, 18540, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_18540_52937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18540 ⟨52937, by decide⟩ :=
  accepted_of_selected 13 18540 ⟨52937, by decide⟩ ⟨13, 2, 0, 52937, 18540, 1929, 16384⟩
    (by decide) selected_cut_01449

theorem selected_cut_01450 : selected 8 ⟨52977, by decide⟩
    (prefixPartial 13 18541) = some ⟨13, 2, 0, 52977, 18541, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_18541_52977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18541 ⟨52977, by decide⟩ :=
  accepted_of_selected 13 18541 ⟨52977, by decide⟩ ⟨13, 2, 0, 52977, 18541, 2669, 16384⟩
    (by decide) selected_cut_01450

theorem selected_cut_01451 : selected 8 ⟨52999, by decide⟩
    (prefixPartial 13 18542) = some ⟨13, 2, 0, 52999, 18542, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_18542_52999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18542 ⟨52999, by decide⟩ :=
  accepted_of_selected 13 18542 ⟨52999, by decide⟩ ⟨13, 2, 0, 52999, 18542, 1985, 16384⟩
    (by decide) selected_cut_01451

theorem selected_cut_01452 : selected 8 ⟨53008, by decide⟩
    (prefixPartial 13 18543) = some ⟨13, 2, 0, 53008, 18543, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_18543_53008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18543 ⟨53008, by decide⟩ :=
  accepted_of_selected 13 18543 ⟨53008, by decide⟩ ⟨13, 2, 0, 53008, 18543, 1029, 16384⟩
    (by decide) selected_cut_01452

theorem unmarked_context_12_4635_53009 : frontier 9 ⟨53009, by decide⟩
    (prefixCache 12 4635) (prefixPartial 12 4635) = false := by
  decide +kernel

theorem node_context_12_4635_53009 : EJMOriginalGlobalDAGData.nodes 9 ⟨53009, by decide⟩ =
    .split (coordinate 12) (![⟨52937, by decide⟩,⟨52977, by decide⟩,⟨52999, by decide⟩,⟨53008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4635_53009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4635 ⟨53009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4635
    ⟨53009, by decide⟩ (by decide) (![⟨52937, by decide⟩,⟨52977, by decide⟩,⟨52999, by decide⟩,⟨53008, by decide⟩]) unmarked_context_12_4635_53009 node_context_12_4635_53009
  intro a
  fin_cases a
  · exact context_13_18540_52937
  · exact context_13_18541_52977
  · exact context_13_18542_52999
  · exact context_13_18543_53008

theorem unmarked_context_11_1158_53010 : frontier 10 ⟨53010, by decide⟩
    (prefixCache 11 1158) (prefixPartial 11 1158) = false := by
  decide +kernel

theorem node_context_11_1158_53010 : EJMOriginalGlobalDAGData.nodes 10 ⟨53010, by decide⟩ =
    .split (coordinate 11) (![⟨52592, by decide⟩,⟨52713, by decide⟩,⟨52900, by decide⟩,⟨53009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1158_53010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1158 ⟨53010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1158
    ⟨53010, by decide⟩ (by decide) (![⟨52592, by decide⟩,⟨52713, by decide⟩,⟨52900, by decide⟩,⟨53009, by decide⟩]) unmarked_context_11_1158_53010 node_context_11_1158_53010
  intro a
  fin_cases a
  · exact context_12_4632_52592
  · exact context_12_4633_52713
  · exact context_12_4634_52900
  · exact context_12_4635_53009

theorem selected_cut_01453 : selected 8 ⟨53048, by decide⟩
    (prefixPartial 13 18544) = some ⟨13, 2, 0, 53048, 18544, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_18544_53048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18544 ⟨53048, by decide⟩ :=
  accepted_of_selected 13 18544 ⟨53048, by decide⟩ ⟨13, 2, 0, 53048, 18544, 1705, 16384⟩
    (by decide) selected_cut_01453

theorem selected_cut_01454 : selected 8 ⟨53097, by decide⟩
    (prefixPartial 13 18545) = some ⟨13, 2, 0, 53097, 18545, 3365, 16384⟩ := by
  decide +kernel

theorem context_13_18545_53097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18545 ⟨53097, by decide⟩ :=
  accepted_of_selected 13 18545 ⟨53097, by decide⟩ ⟨13, 2, 0, 53097, 18545, 3365, 16384⟩
    (by decide) selected_cut_01454

theorem selected_cut_01455 : selected 8 ⟨53133, by decide⟩
    (prefixPartial 13 18546) = some ⟨13, 2, 0, 53133, 18546, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_18546_53133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18546 ⟨53133, by decide⟩ :=
  accepted_of_selected 13 18546 ⟨53133, by decide⟩ ⟨13, 2, 0, 53133, 18546, 2413, 16384⟩
    (by decide) selected_cut_01455

theorem selected_cut_01456 : selected 8 ⟨53153, by decide⟩
    (prefixPartial 13 18547) = some ⟨13, 2, 0, 53153, 18547, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_18547_53153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18547 ⟨53153, by decide⟩ :=
  accepted_of_selected 13 18547 ⟨53153, by decide⟩ ⟨13, 2, 0, 53153, 18547, 1269, 16384⟩
    (by decide) selected_cut_01456

theorem unmarked_context_12_4636_53154 : frontier 9 ⟨53154, by decide⟩
    (prefixCache 12 4636) (prefixPartial 12 4636) = false := by
  decide +kernel

theorem node_context_12_4636_53154 : EJMOriginalGlobalDAGData.nodes 9 ⟨53154, by decide⟩ =
    .split (coordinate 12) (![⟨53048, by decide⟩,⟨53097, by decide⟩,⟨53133, by decide⟩,⟨53153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4636_53154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4636 ⟨53154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4636
    ⟨53154, by decide⟩ (by decide) (![⟨53048, by decide⟩,⟨53097, by decide⟩,⟨53133, by decide⟩,⟨53153, by decide⟩]) unmarked_context_12_4636_53154 node_context_12_4636_53154
  intro a
  fin_cases a
  · exact context_13_18544_53048
  · exact context_13_18545_53097
  · exact context_13_18546_53133
  · exact context_13_18547_53153

theorem selected_cut_01457 : selected 8 ⟨53189, by decide⟩
    (prefixPartial 13 18548) = some ⟨13, 2, 0, 53189, 18548, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_18548_53189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18548 ⟨53189, by decide⟩ :=
  accepted_of_selected 13 18548 ⟨53189, by decide⟩ ⟨13, 2, 0, 53189, 18548, 1793, 16384⟩
    (by decide) selected_cut_01457

theorem selected_cut_01458 : selected 8 ⟨53229, by decide⟩
    (prefixPartial 13 18549) = some ⟨13, 2, 0, 53229, 18549, 2681, 16384⟩ := by
  decide +kernel

theorem context_13_18549_53229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18549 ⟨53229, by decide⟩ :=
  accepted_of_selected 13 18549 ⟨53229, by decide⟩ ⟨13, 2, 0, 53229, 18549, 2681, 16384⟩
    (by decide) selected_cut_01458

theorem selected_cut_01459 : selected 8 ⟨53260, by decide⟩
    (prefixPartial 13 18550) = some ⟨13, 2, 0, 53260, 18550, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_18550_53260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18550 ⟨53260, by decide⟩ :=
  accepted_of_selected 13 18550 ⟨53260, by decide⟩ ⟨13, 2, 0, 53260, 18550, 2245, 16384⟩
    (by decide) selected_cut_01459

theorem selected_cut_01460 : selected 8 ⟨53271, by decide⟩
    (prefixPartial 13 18551) = some ⟨13, 2, 0, 53271, 18551, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_18551_53271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18551 ⟨53271, by decide⟩ :=
  accepted_of_selected 13 18551 ⟨53271, by decide⟩ ⟨13, 2, 0, 53271, 18551, 1049, 16384⟩
    (by decide) selected_cut_01460

theorem unmarked_context_12_4637_53272 : frontier 9 ⟨53272, by decide⟩
    (prefixCache 12 4637) (prefixPartial 12 4637) = false := by
  decide +kernel

theorem node_context_12_4637_53272 : EJMOriginalGlobalDAGData.nodes 9 ⟨53272, by decide⟩ =
    .split (coordinate 12) (![⟨53189, by decide⟩,⟨53229, by decide⟩,⟨53260, by decide⟩,⟨53271, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4637_53272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4637 ⟨53272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4637
    ⟨53272, by decide⟩ (by decide) (![⟨53189, by decide⟩,⟨53229, by decide⟩,⟨53260, by decide⟩,⟨53271, by decide⟩]) unmarked_context_12_4637_53272 node_context_12_4637_53272
  intro a
  fin_cases a
  · exact context_13_18548_53189
  · exact context_13_18549_53229
  · exact context_13_18550_53260
  · exact context_13_18551_53271

theorem selected_cut_01461 : selected 8 ⟨53310, by decide⟩
    (prefixPartial 13 18552) = some ⟨13, 2, 0, 53310, 18552, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_18552_53310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18552 ⟨53310, by decide⟩ :=
  accepted_of_selected 13 18552 ⟨53310, by decide⟩ ⟨13, 2, 0, 53310, 18552, 1593, 16384⟩
    (by decide) selected_cut_01461

theorem selected_cut_01462 : selected 8 ⟨53347, by decide⟩
    (prefixPartial 13 18553) = some ⟨13, 2, 0, 53347, 18553, 2797, 16384⟩ := by
  decide +kernel

theorem context_13_18553_53347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18553 ⟨53347, by decide⟩ :=
  accepted_of_selected 13 18553 ⟨53347, by decide⟩ ⟨13, 2, 0, 53347, 18553, 2797, 16384⟩
    (by decide) selected_cut_01462

theorem selected_cut_01463 : selected 8 ⟨53372, by decide⟩
    (prefixPartial 13 18554) = some ⟨13, 2, 0, 53372, 18554, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_18554_53372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18554 ⟨53372, by decide⟩ :=
  accepted_of_selected 13 18554 ⟨53372, by decide⟩ ⟨13, 2, 0, 53372, 18554, 2005, 16384⟩
    (by decide) selected_cut_01463

theorem selected_cut_01464 : selected 8 ⟨53385, by decide⟩
    (prefixPartial 13 18555) = some ⟨13, 2, 0, 53385, 18555, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_18555_53385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18555 ⟨53385, by decide⟩ :=
  accepted_of_selected 13 18555 ⟨53385, by decide⟩ ⟨13, 2, 0, 53385, 18555, 1073, 16384⟩
    (by decide) selected_cut_01464

theorem unmarked_context_12_4638_53386 : frontier 9 ⟨53386, by decide⟩
    (prefixCache 12 4638) (prefixPartial 12 4638) = false := by
  decide +kernel

theorem node_context_12_4638_53386 : EJMOriginalGlobalDAGData.nodes 9 ⟨53386, by decide⟩ =
    .split (coordinate 12) (![⟨53310, by decide⟩,⟨53347, by decide⟩,⟨53372, by decide⟩,⟨53385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4638_53386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4638 ⟨53386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4638
    ⟨53386, by decide⟩ (by decide) (![⟨53310, by decide⟩,⟨53347, by decide⟩,⟨53372, by decide⟩,⟨53385, by decide⟩]) unmarked_context_12_4638_53386 node_context_12_4638_53386
  intro a
  fin_cases a
  · exact context_13_18552_53310
  · exact context_13_18553_53347
  · exact context_13_18554_53372
  · exact context_13_18555_53385

theorem selected_cut_01465 : selected 8 ⟨53424, by decide⟩
    (prefixPartial 13 18556) = some ⟨13, 2, 0, 53424, 18556, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_18556_53424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18556 ⟨53424, by decide⟩ :=
  accepted_of_selected 13 18556 ⟨53424, by decide⟩ ⟨13, 2, 0, 53424, 18556, 1745, 16384⟩
    (by decide) selected_cut_01465

theorem selected_cut_01466 : selected 8 ⟨53463, by decide⟩
    (prefixPartial 13 18557) = some ⟨13, 2, 0, 53463, 18557, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_18557_53463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18557 ⟨53463, by decide⟩ :=
  accepted_of_selected 13 18557 ⟨53463, by decide⟩ ⟨13, 2, 0, 53463, 18557, 2669, 16384⟩
    (by decide) selected_cut_01466

theorem selected_cut_01467 : selected 8 ⟨53486, by decide⟩
    (prefixPartial 13 18558) = some ⟨13, 2, 0, 53486, 18558, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_18558_53486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18558 ⟨53486, by decide⟩ :=
  accepted_of_selected 13 18558 ⟨53486, by decide⟩ ⟨13, 2, 0, 53486, 18558, 2133, 16384⟩
    (by decide) selected_cut_01467

theorem selected_cut_01468 : selected 8 ⟨53496, by decide⟩
    (prefixPartial 13 18559) = some ⟨13, 2, 0, 53496, 18559, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_18559_53496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18559 ⟨53496, by decide⟩ :=
  accepted_of_selected 13 18559 ⟨53496, by decide⟩ ⟨13, 2, 0, 53496, 18559, 1057, 16384⟩
    (by decide) selected_cut_01468

theorem unmarked_context_12_4639_53497 : frontier 9 ⟨53497, by decide⟩
    (prefixCache 12 4639) (prefixPartial 12 4639) = false := by
  decide +kernel

theorem node_context_12_4639_53497 : EJMOriginalGlobalDAGData.nodes 9 ⟨53497, by decide⟩ =
    .split (coordinate 12) (![⟨53424, by decide⟩,⟨53463, by decide⟩,⟨53486, by decide⟩,⟨53496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4639_53497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4639 ⟨53497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4639
    ⟨53497, by decide⟩ (by decide) (![⟨53424, by decide⟩,⟨53463, by decide⟩,⟨53486, by decide⟩,⟨53496, by decide⟩]) unmarked_context_12_4639_53497 node_context_12_4639_53497
  intro a
  fin_cases a
  · exact context_13_18556_53424
  · exact context_13_18557_53463
  · exact context_13_18558_53486
  · exact context_13_18559_53496

theorem unmarked_context_11_1159_53498 : frontier 10 ⟨53498, by decide⟩
    (prefixCache 11 1159) (prefixPartial 11 1159) = false := by
  decide +kernel

theorem node_context_11_1159_53498 : EJMOriginalGlobalDAGData.nodes 10 ⟨53498, by decide⟩ =
    .split (coordinate 11) (![⟨53154, by decide⟩,⟨53272, by decide⟩,⟨53386, by decide⟩,⟨53497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1159_53498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1159 ⟨53498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1159
    ⟨53498, by decide⟩ (by decide) (![⟨53154, by decide⟩,⟨53272, by decide⟩,⟨53386, by decide⟩,⟨53497, by decide⟩]) unmarked_context_11_1159_53498 node_context_11_1159_53498
  intro a
  fin_cases a
  · exact context_12_4636_53154
  · exact context_12_4637_53272
  · exact context_12_4638_53386
  · exact context_12_4639_53497

theorem unmarked_context_10_289_53499 : frontier 11 ⟨53499, by decide⟩
    (prefixCache 10 289) (prefixPartial 10 289) = false := by
  decide +kernel

theorem node_context_10_289_53499 : EJMOriginalGlobalDAGData.nodes 11 ⟨53499, by decide⟩ =
    .split (coordinate 10) (![⟨51964, by decide⟩,⟨52457, by decide⟩,⟨53010, by decide⟩,⟨53498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_289_53499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 289 ⟨53499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 289
    ⟨53499, by decide⟩ (by decide) (![⟨51964, by decide⟩,⟨52457, by decide⟩,⟨53010, by decide⟩,⟨53498, by decide⟩]) unmarked_context_10_289_53499 node_context_10_289_53499
  intro a
  fin_cases a
  · exact context_11_1156_51964
  · exact context_11_1157_52457
  · exact context_11_1158_53010
  · exact context_11_1159_53498

theorem selected_cut_01469 : selected 8 ⟨53519, by decide⟩
    (prefixPartial 13 18560) = some ⟨13, 2, 0, 53519, 18560, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_18560_53519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18560 ⟨53519, by decide⟩ :=
  accepted_of_selected 13 18560 ⟨53519, by decide⟩ ⟨13, 2, 0, 53519, 18560, 1109, 16384⟩
    (by decide) selected_cut_01469

theorem selected_cut_01470 : selected 8 ⟨53558, by decide⟩
    (prefixPartial 13 18561) = some ⟨13, 2, 0, 53558, 18561, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_18561_53558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18561 ⟨53558, by decide⟩ :=
  accepted_of_selected 13 18561 ⟨53558, by decide⟩ ⟨13, 2, 0, 53558, 18561, 2481, 16384⟩
    (by decide) selected_cut_01470

theorem selected_cut_01471 : selected 8 ⟨53580, by decide⟩
    (prefixPartial 13 18562) = some ⟨13, 2, 0, 53580, 18562, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_18562_53580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18562 ⟨53580, by decide⟩ :=
  accepted_of_selected 13 18562 ⟨53580, by decide⟩ ⟨13, 2, 0, 53580, 18562, 1709, 16384⟩
    (by decide) selected_cut_01471

theorem selected_cut_01472 : selected 8 ⟨53591, by decide⟩
    (prefixPartial 13 18563) = some ⟨13, 2, 0, 53591, 18563, 801, 16384⟩ := by
  decide +kernel

theorem context_13_18563_53591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18563 ⟨53591, by decide⟩ :=
  accepted_of_selected 13 18563 ⟨53591, by decide⟩ ⟨13, 2, 0, 53591, 18563, 801, 16384⟩
    (by decide) selected_cut_01472

theorem unmarked_context_12_4640_53592 : frontier 9 ⟨53592, by decide⟩
    (prefixCache 12 4640) (prefixPartial 12 4640) = false := by
  decide +kernel

theorem node_context_12_4640_53592 : EJMOriginalGlobalDAGData.nodes 9 ⟨53592, by decide⟩ =
    .split (coordinate 12) (![⟨53519, by decide⟩,⟨53558, by decide⟩,⟨53580, by decide⟩,⟨53591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4640_53592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4640 ⟨53592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4640
    ⟨53592, by decide⟩ (by decide) (![⟨53519, by decide⟩,⟨53558, by decide⟩,⟨53580, by decide⟩,⟨53591, by decide⟩]) unmarked_context_12_4640_53592 node_context_12_4640_53592
  intro a
  fin_cases a
  · exact context_13_18560_53519
  · exact context_13_18561_53558
  · exact context_13_18562_53580
  · exact context_13_18563_53591

theorem selected_cut_01473 : selected 8 ⟨53609, by decide⟩
    (prefixPartial 13 18564) = some ⟨13, 2, 0, 53609, 18564, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_18564_53609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18564 ⟨53609, by decide⟩ :=
  accepted_of_selected 13 18564 ⟨53609, by decide⟩ ⟨13, 2, 0, 53609, 18564, 1033, 16384⟩
    (by decide) selected_cut_01473

theorem selected_cut_01474 : selected 8 ⟨53639, by decide⟩
    (prefixPartial 13 18565) = some ⟨13, 2, 0, 53639, 18565, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_18565_53639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18565 ⟨53639, by decide⟩ :=
  accepted_of_selected 13 18565 ⟨53639, by decide⟩ ⟨13, 2, 0, 53639, 18565, 1881, 16384⟩
    (by decide) selected_cut_01474

theorem selected_cut_01475 : selected 8 ⟨53661, by decide⟩
    (prefixPartial 13 18566) = some ⟨13, 2, 0, 53661, 18566, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_18566_53661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18566 ⟨53661, by decide⟩ :=
  accepted_of_selected 13 18566 ⟨53661, by decide⟩ ⟨13, 2, 0, 53661, 18566, 1473, 16384⟩
    (by decide) selected_cut_01475

theorem selected_cut_01476 : selected 8 ⟨53670, by decide⟩
    (prefixPartial 13 18567) = some ⟨13, 2, 0, 53670, 18567, 821, 16384⟩ := by
  decide +kernel

theorem context_13_18567_53670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18567 ⟨53670, by decide⟩ :=
  accepted_of_selected 13 18567 ⟨53670, by decide⟩ ⟨13, 2, 0, 53670, 18567, 821, 16384⟩
    (by decide) selected_cut_01476

theorem unmarked_context_12_4641_53671 : frontier 9 ⟨53671, by decide⟩
    (prefixCache 12 4641) (prefixPartial 12 4641) = false := by
  decide +kernel

theorem node_context_12_4641_53671 : EJMOriginalGlobalDAGData.nodes 9 ⟨53671, by decide⟩ =
    .split (coordinate 12) (![⟨53609, by decide⟩,⟨53639, by decide⟩,⟨53661, by decide⟩,⟨53670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4641_53671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4641 ⟨53671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4641
    ⟨53671, by decide⟩ (by decide) (![⟨53609, by decide⟩,⟨53639, by decide⟩,⟨53661, by decide⟩,⟨53670, by decide⟩]) unmarked_context_12_4641_53671 node_context_12_4641_53671
  intro a
  fin_cases a
  · exact context_13_18564_53609
  · exact context_13_18565_53639
  · exact context_13_18566_53661
  · exact context_13_18567_53670

theorem selected_cut_01477 : selected 8 ⟨53689, by decide⟩
    (prefixPartial 13 18568) = some ⟨13, 2, 0, 53689, 18568, 977, 16384⟩ := by
  decide +kernel

theorem context_13_18568_53689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18568 ⟨53689, by decide⟩ :=
  accepted_of_selected 13 18568 ⟨53689, by decide⟩ ⟨13, 2, 0, 53689, 18568, 977, 16384⟩
    (by decide) selected_cut_01477

theorem selected_cut_01478 : selected 8 ⟨53728, by decide⟩
    (prefixPartial 13 18569) = some ⟨13, 2, 0, 53728, 18569, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_18569_53728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18569 ⟨53728, by decide⟩ :=
  accepted_of_selected 13 18569 ⟨53728, by decide⟩ ⟨13, 2, 0, 53728, 18569, 2005, 16384⟩
    (by decide) selected_cut_01478

theorem selected_cut_01479 : selected 8 ⟨53747, by decide⟩
    (prefixPartial 13 18570) = some ⟨13, 2, 0, 53747, 18570, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_18570_53747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18570 ⟨53747, by decide⟩ :=
  accepted_of_selected 13 18570 ⟨53747, by decide⟩ ⟨13, 2, 0, 53747, 18570, 1265, 16384⟩
    (by decide) selected_cut_01479

theorem selected_cut_01480 : selected 8 ⟨53756, by decide⟩
    (prefixPartial 13 18571) = some ⟨13, 2, 0, 53756, 18571, 769, 16384⟩ := by
  decide +kernel

theorem context_13_18571_53756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18571 ⟨53756, by decide⟩ :=
  accepted_of_selected 13 18571 ⟨53756, by decide⟩ ⟨13, 2, 0, 53756, 18571, 769, 16384⟩
    (by decide) selected_cut_01480

theorem unmarked_context_12_4642_53757 : frontier 9 ⟨53757, by decide⟩
    (prefixCache 12 4642) (prefixPartial 12 4642) = false := by
  decide +kernel

theorem node_context_12_4642_53757 : EJMOriginalGlobalDAGData.nodes 9 ⟨53757, by decide⟩ =
    .split (coordinate 12) (![⟨53689, by decide⟩,⟨53728, by decide⟩,⟨53747, by decide⟩,⟨53756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4642_53757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4642 ⟨53757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4642
    ⟨53757, by decide⟩ (by decide) (![⟨53689, by decide⟩,⟨53728, by decide⟩,⟨53747, by decide⟩,⟨53756, by decide⟩]) unmarked_context_12_4642_53757 node_context_12_4642_53757
  intro a
  fin_cases a
  · exact context_13_18568_53689
  · exact context_13_18569_53728
  · exact context_13_18570_53747
  · exact context_13_18571_53756

theorem selected_cut_01481 : selected 8 ⟨53788, by decide⟩
    (prefixPartial 13 18572) = some ⟨13, 2, 0, 53788, 18572, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_18572_53788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18572 ⟨53788, by decide⟩ :=
  accepted_of_selected 13 18572 ⟨53788, by decide⟩ ⟨13, 2, 0, 53788, 18572, 1117, 16384⟩
    (by decide) selected_cut_01481

theorem selected_cut_01482 : selected 8 ⟨53830, by decide⟩
    (prefixPartial 13 18573) = some ⟨13, 2, 0, 53830, 18573, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_18573_53830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18573 ⟨53830, by decide⟩ :=
  accepted_of_selected 13 18573 ⟨53830, by decide⟩ ⟨13, 2, 0, 53830, 18573, 2353, 16384⟩
    (by decide) selected_cut_01482

theorem selected_cut_01483 : selected 8 ⟨53849, by decide⟩
    (prefixPartial 13 18574) = some ⟨13, 2, 0, 53849, 18574, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_18574_53849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18574 ⟨53849, by decide⟩ :=
  accepted_of_selected 13 18574 ⟨53849, by decide⟩ ⟨13, 2, 0, 53849, 18574, 1429, 16384⟩
    (by decide) selected_cut_01483

theorem selected_cut_01484 : selected 8 ⟨53859, by decide⟩
    (prefixPartial 13 18575) = some ⟨13, 2, 0, 53859, 18575, 733, 16384⟩ := by
  decide +kernel

theorem context_13_18575_53859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18575 ⟨53859, by decide⟩ :=
  accepted_of_selected 13 18575 ⟨53859, by decide⟩ ⟨13, 2, 0, 53859, 18575, 733, 16384⟩
    (by decide) selected_cut_01484

theorem unmarked_context_12_4643_53860 : frontier 9 ⟨53860, by decide⟩
    (prefixCache 12 4643) (prefixPartial 12 4643) = false := by
  decide +kernel

theorem node_context_12_4643_53860 : EJMOriginalGlobalDAGData.nodes 9 ⟨53860, by decide⟩ =
    .split (coordinate 12) (![⟨53788, by decide⟩,⟨53830, by decide⟩,⟨53849, by decide⟩,⟨53859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4643_53860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4643 ⟨53860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4643
    ⟨53860, by decide⟩ (by decide) (![⟨53788, by decide⟩,⟨53830, by decide⟩,⟨53849, by decide⟩,⟨53859, by decide⟩]) unmarked_context_12_4643_53860 node_context_12_4643_53860
  intro a
  fin_cases a
  · exact context_13_18572_53788
  · exact context_13_18573_53830
  · exact context_13_18574_53849
  · exact context_13_18575_53859

theorem unmarked_context_11_1160_53861 : frontier 10 ⟨53861, by decide⟩
    (prefixCache 11 1160) (prefixPartial 11 1160) = false := by
  decide +kernel

theorem node_context_11_1160_53861 : EJMOriginalGlobalDAGData.nodes 10 ⟨53861, by decide⟩ =
    .split (coordinate 11) (![⟨53592, by decide⟩,⟨53671, by decide⟩,⟨53757, by decide⟩,⟨53860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1160_53861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1160 ⟨53861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1160
    ⟨53861, by decide⟩ (by decide) (![⟨53592, by decide⟩,⟨53671, by decide⟩,⟨53757, by decide⟩,⟨53860, by decide⟩]) unmarked_context_11_1160_53861 node_context_11_1160_53861
  intro a
  fin_cases a
  · exact context_12_4640_53592
  · exact context_12_4641_53671
  · exact context_12_4642_53757
  · exact context_12_4643_53860

theorem selected_cut_01485 : selected 8 ⟨53889, by decide⟩
    (prefixPartial 13 18576) = some ⟨13, 2, 0, 53889, 18576, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_18576_53889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18576 ⟨53889, by decide⟩ :=
  accepted_of_selected 13 18576 ⟨53889, by decide⟩ ⟨13, 2, 0, 53889, 18576, 1509, 16384⟩
    (by decide) selected_cut_01485

theorem selected_cut_01486 : selected 8 ⟨53957, by decide⟩
    (prefixPartial 13 18577) = some ⟨13, 2, 0, 53957, 18577, 3737, 16384⟩ := by
  decide +kernel

theorem context_13_18577_53957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18577 ⟨53957, by decide⟩ :=
  accepted_of_selected 13 18577 ⟨53957, by decide⟩ ⟨13, 2, 0, 53957, 18577, 3737, 16384⟩
    (by decide) selected_cut_01486

theorem selected_cut_01487 : selected 8 ⟨54011, by decide⟩
    (prefixPartial 13 18578) = some ⟨13, 2, 0, 54011, 18578, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_18578_54011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18578 ⟨54011, by decide⟩ :=
  accepted_of_selected 13 18578 ⟨54011, by decide⟩ ⟨13, 2, 0, 54011, 18578, 2337, 16384⟩
    (by decide) selected_cut_01487

theorem selected_cut_01488 : selected 8 ⟨54033, by decide⟩
    (prefixPartial 13 18579) = some ⟨13, 2, 0, 54033, 18579, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_18579_54033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18579 ⟨54033, by decide⟩ :=
  accepted_of_selected 13 18579 ⟨54033, by decide⟩ ⟨13, 2, 0, 54033, 18579, 1097, 16384⟩
    (by decide) selected_cut_01488

theorem unmarked_context_12_4644_54034 : frontier 9 ⟨54034, by decide⟩
    (prefixCache 12 4644) (prefixPartial 12 4644) = false := by
  decide +kernel

theorem node_context_12_4644_54034 : EJMOriginalGlobalDAGData.nodes 9 ⟨54034, by decide⟩ =
    .split (coordinate 12) (![⟨53889, by decide⟩,⟨53957, by decide⟩,⟨54011, by decide⟩,⟨54033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4644_54034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4644 ⟨54034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4644
    ⟨54034, by decide⟩ (by decide) (![⟨53889, by decide⟩,⟨53957, by decide⟩,⟨54011, by decide⟩,⟨54033, by decide⟩]) unmarked_context_12_4644_54034 node_context_12_4644_54034
  intro a
  fin_cases a
  · exact context_13_18576_53889
  · exact context_13_18577_53957
  · exact context_13_18578_54011
  · exact context_13_18579_54033

theorem selected_cut_01489 : selected 8 ⟨54061, by decide⟩
    (prefixPartial 13 18580) = some ⟨13, 2, 0, 54061, 18580, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_18580_54061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18580 ⟨54061, by decide⟩ :=
  accepted_of_selected 13 18580 ⟨54061, by decide⟩ ⟨13, 2, 0, 54061, 18580, 1417, 16384⟩
    (by decide) selected_cut_01489

theorem selected_cut_01490 : selected 8 ⟨54095, by decide⟩
    (prefixPartial 13 18581) = some ⟨13, 2, 0, 54095, 18581, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_18581_54095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18581 ⟨54095, by decide⟩ :=
  accepted_of_selected 13 18581 ⟨54095, by decide⟩ ⟨13, 2, 0, 54095, 18581, 2577, 16384⟩
    (by decide) selected_cut_01490

theorem selected_cut_01491 : selected 8 ⟨54119, by decide⟩
    (prefixPartial 13 18582) = some ⟨13, 2, 0, 54119, 18582, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_18582_54119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18582 ⟨54119, by decide⟩ :=
  accepted_of_selected 13 18582 ⟨54119, by decide⟩ ⟨13, 2, 0, 54119, 18582, 2057, 16384⟩
    (by decide) selected_cut_01491

theorem selected_cut_01492 : selected 8 ⟨54133, by decide⟩
    (prefixPartial 13 18583) = some ⟨13, 2, 0, 54133, 18583, 997, 16384⟩ := by
  decide +kernel

theorem context_13_18583_54133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18583 ⟨54133, by decide⟩ :=
  accepted_of_selected 13 18583 ⟨54133, by decide⟩ ⟨13, 2, 0, 54133, 18583, 997, 16384⟩
    (by decide) selected_cut_01492

theorem unmarked_context_12_4645_54134 : frontier 9 ⟨54134, by decide⟩
    (prefixCache 12 4645) (prefixPartial 12 4645) = false := by
  decide +kernel

theorem node_context_12_4645_54134 : EJMOriginalGlobalDAGData.nodes 9 ⟨54134, by decide⟩ =
    .split (coordinate 12) (![⟨54061, by decide⟩,⟨54095, by decide⟩,⟨54119, by decide⟩,⟨54133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4645_54134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4645 ⟨54134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4645
    ⟨54134, by decide⟩ (by decide) (![⟨54061, by decide⟩,⟨54095, by decide⟩,⟨54119, by decide⟩,⟨54133, by decide⟩]) unmarked_context_12_4645_54134 node_context_12_4645_54134
  intro a
  fin_cases a
  · exact context_13_18580_54061
  · exact context_13_18581_54095
  · exact context_13_18582_54119
  · exact context_13_18583_54133

theorem selected_cut_01493 : selected 8 ⟨54159, by decide⟩
    (prefixPartial 13 18584) = some ⟨13, 2, 0, 54159, 18584, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_18584_54159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18584 ⟨54159, by decide⟩ :=
  accepted_of_selected 13 18584 ⟨54159, by decide⟩ ⟨13, 2, 0, 54159, 18584, 1385, 16384⟩
    (by decide) selected_cut_01493

theorem selected_cut_01494 : selected 8 ⟨54203, by decide⟩
    (prefixPartial 13 18585) = some ⟨13, 2, 0, 54203, 18585, 2689, 16384⟩ := by
  decide +kernel

theorem context_13_18585_54203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18585 ⟨54203, by decide⟩ :=
  accepted_of_selected 13 18585 ⟨54203, by decide⟩ ⟨13, 2, 0, 54203, 18585, 2689, 16384⟩
    (by decide) selected_cut_01494

theorem selected_cut_01495 : selected 8 ⟨54226, by decide⟩
    (prefixPartial 13 18586) = some ⟨13, 2, 0, 54226, 18586, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_18586_54226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18586 ⟨54226, by decide⟩ :=
  accepted_of_selected 13 18586 ⟨54226, by decide⟩ ⟨13, 2, 0, 54226, 18586, 1729, 16384⟩
    (by decide) selected_cut_01495

theorem selected_cut_01496 : selected 8 ⟨54237, by decide⟩
    (prefixPartial 13 18587) = some ⟨13, 2, 0, 54237, 18587, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_18587_54237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18587 ⟨54237, by decide⟩ :=
  accepted_of_selected 13 18587 ⟨54237, by decide⟩ ⟨13, 2, 0, 54237, 18587, 1017, 16384⟩
    (by decide) selected_cut_01496

theorem unmarked_context_12_4646_54238 : frontier 9 ⟨54238, by decide⟩
    (prefixCache 12 4646) (prefixPartial 12 4646) = false := by
  decide +kernel

theorem node_context_12_4646_54238 : EJMOriginalGlobalDAGData.nodes 9 ⟨54238, by decide⟩ =
    .split (coordinate 12) (![⟨54159, by decide⟩,⟨54203, by decide⟩,⟨54226, by decide⟩,⟨54237, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4646_54238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4646 ⟨54238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4646
    ⟨54238, by decide⟩ (by decide) (![⟨54159, by decide⟩,⟨54203, by decide⟩,⟨54226, by decide⟩,⟨54237, by decide⟩]) unmarked_context_12_4646_54238 node_context_12_4646_54238
  intro a
  fin_cases a
  · exact context_13_18584_54159
  · exact context_13_18585_54203
  · exact context_13_18586_54226
  · exact context_13_18587_54237

theorem selected_cut_01497 : selected 8 ⟨54264, by decide⟩
    (prefixPartial 13 18588) = some ⟨13, 2, 0, 54264, 18588, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_18588_54264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18588 ⟨54264, by decide⟩ :=
  accepted_of_selected 13 18588 ⟨54264, by decide⟩ ⟨13, 2, 0, 54264, 18588, 1441, 16384⟩
    (by decide) selected_cut_01497

theorem selected_cut_01498 : selected 8 ⟨54304, by decide⟩
    (prefixPartial 13 18589) = some ⟨13, 2, 0, 54304, 18589, 2921, 16384⟩ := by
  decide +kernel

theorem context_13_18589_54304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18589 ⟨54304, by decide⟩ :=
  accepted_of_selected 13 18589 ⟨54304, by decide⟩ ⟨13, 2, 0, 54304, 18589, 2921, 16384⟩
    (by decide) selected_cut_01498

theorem selected_cut_01499 : selected 8 ⟨54332, by decide⟩
    (prefixPartial 13 18590) = some ⟨13, 2, 0, 54332, 18590, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_18590_54332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18590 ⟨54332, by decide⟩ :=
  accepted_of_selected 13 18590 ⟨54332, by decide⟩ ⟨13, 2, 0, 54332, 18590, 2149, 16384⟩
    (by decide) selected_cut_01499

theorem selected_cut_01500 : selected 8 ⟨54346, by decide⟩
    (prefixPartial 13 18591) = some ⟨13, 2, 0, 54346, 18591, 897, 16384⟩ := by
  decide +kernel

theorem context_13_18591_54346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18591 ⟨54346, by decide⟩ :=
  accepted_of_selected 13 18591 ⟨54346, by decide⟩ ⟨13, 2, 0, 54346, 18591, 897, 16384⟩
    (by decide) selected_cut_01500

theorem unmarked_context_12_4647_54347 : frontier 9 ⟨54347, by decide⟩
    (prefixCache 12 4647) (prefixPartial 12 4647) = false := by
  decide +kernel

theorem node_context_12_4647_54347 : EJMOriginalGlobalDAGData.nodes 9 ⟨54347, by decide⟩ =
    .split (coordinate 12) (![⟨54264, by decide⟩,⟨54304, by decide⟩,⟨54332, by decide⟩,⟨54346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4647_54347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4647 ⟨54347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4647
    ⟨54347, by decide⟩ (by decide) (![⟨54264, by decide⟩,⟨54304, by decide⟩,⟨54332, by decide⟩,⟨54346, by decide⟩]) unmarked_context_12_4647_54347 node_context_12_4647_54347
  intro a
  fin_cases a
  · exact context_13_18588_54264
  · exact context_13_18589_54304
  · exact context_13_18590_54332
  · exact context_13_18591_54346

theorem unmarked_context_11_1161_54348 : frontier 10 ⟨54348, by decide⟩
    (prefixCache 11 1161) (prefixPartial 11 1161) = false := by
  decide +kernel

theorem node_context_11_1161_54348 : EJMOriginalGlobalDAGData.nodes 10 ⟨54348, by decide⟩ =
    .split (coordinate 11) (![⟨54034, by decide⟩,⟨54134, by decide⟩,⟨54238, by decide⟩,⟨54347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1161_54348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1161 ⟨54348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1161
    ⟨54348, by decide⟩ (by decide) (![⟨54034, by decide⟩,⟨54134, by decide⟩,⟨54238, by decide⟩,⟨54347, by decide⟩]) unmarked_context_11_1161_54348 node_context_11_1161_54348
  intro a
  fin_cases a
  · exact context_12_4644_54034
  · exact context_12_4645_54134
  · exact context_12_4646_54238
  · exact context_12_4647_54347

theorem selected_cut_01501 : selected 8 ⟨54370, by decide⟩
    (prefixPartial 13 18592) = some ⟨13, 2, 0, 54370, 18592, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_18592_54370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18592 ⟨54370, by decide⟩ :=
  accepted_of_selected 13 18592 ⟨54370, by decide⟩ ⟨13, 2, 0, 54370, 18592, 1101, 16384⟩
    (by decide) selected_cut_01501

theorem selected_cut_01502 : selected 8 ⟨54418, by decide⟩
    (prefixPartial 13 18593) = some ⟨13, 2, 0, 54418, 18593, 3245, 16384⟩ := by
  decide +kernel

theorem context_13_18593_54418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18593 ⟨54418, by decide⟩ :=
  accepted_of_selected 13 18593 ⟨54418, by decide⟩ ⟨13, 2, 0, 54418, 18593, 3245, 16384⟩
    (by decide) selected_cut_01502

theorem selected_cut_01503 : selected 8 ⟨54444, by decide⟩
    (prefixPartial 13 18594) = some ⟨13, 2, 0, 54444, 18594, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_18594_54444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18594 ⟨54444, by decide⟩ :=
  accepted_of_selected 13 18594 ⟨54444, by decide⟩ ⟨13, 2, 0, 54444, 18594, 1977, 16384⟩
    (by decide) selected_cut_01503

theorem selected_cut_01504 : selected 8 ⟨54458, by decide⟩
    (prefixPartial 13 18595) = some ⟨13, 2, 0, 54458, 18595, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_18595_54458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18595 ⟨54458, by decide⟩ :=
  accepted_of_selected 13 18595 ⟨54458, by decide⟩ ⟨13, 2, 0, 54458, 18595, 1021, 16384⟩
    (by decide) selected_cut_01504

theorem unmarked_context_12_4648_54459 : frontier 9 ⟨54459, by decide⟩
    (prefixCache 12 4648) (prefixPartial 12 4648) = false := by
  decide +kernel

theorem node_context_12_4648_54459 : EJMOriginalGlobalDAGData.nodes 9 ⟨54459, by decide⟩ =
    .split (coordinate 12) (![⟨54370, by decide⟩,⟨54418, by decide⟩,⟨54444, by decide⟩,⟨54458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4648_54459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4648 ⟨54459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4648
    ⟨54459, by decide⟩ (by decide) (![⟨54370, by decide⟩,⟨54418, by decide⟩,⟨54444, by decide⟩,⟨54458, by decide⟩]) unmarked_context_12_4648_54459 node_context_12_4648_54459
  intro a
  fin_cases a
  · exact context_13_18592_54370
  · exact context_13_18593_54418
  · exact context_13_18594_54444
  · exact context_13_18595_54458

theorem selected_cut_01505 : selected 8 ⟨54482, by decide⟩
    (prefixPartial 13 18596) = some ⟨13, 2, 0, 54482, 18596, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_18596_54482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18596 ⟨54482, by decide⟩ :=
  accepted_of_selected 13 18596 ⟨54482, by decide⟩ ⟨13, 2, 0, 54482, 18596, 1201, 16384⟩
    (by decide) selected_cut_01505

theorem selected_cut_01506 : selected 8 ⟨54516, by decide⟩
    (prefixPartial 13 18597) = some ⟨13, 2, 0, 54516, 18597, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_18597_54516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18597 ⟨54516, by decide⟩ :=
  accepted_of_selected 13 18597 ⟨54516, by decide⟩ ⟨13, 2, 0, 54516, 18597, 2469, 16384⟩
    (by decide) selected_cut_01506

theorem selected_cut_01507 : selected 8 ⟨54538, by decide⟩
    (prefixPartial 13 18598) = some ⟨13, 2, 0, 54538, 18598, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_18598_54538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18598 ⟨54538, by decide⟩ :=
  accepted_of_selected 13 18598 ⟨54538, by decide⟩ ⟨13, 2, 0, 54538, 18598, 1825, 16384⟩
    (by decide) selected_cut_01507

theorem selected_cut_01508 : selected 8 ⟨54545, by decide⟩
    (prefixPartial 13 18599) = some ⟨13, 2, 0, 54545, 18599, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_18599_54545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18599 ⟨54545, by decide⟩ :=
  accepted_of_selected 13 18599 ⟨54545, by decide⟩ ⟨13, 2, 0, 54545, 18599, 1053, 16384⟩
    (by decide) selected_cut_01508

theorem unmarked_context_12_4649_54546 : frontier 9 ⟨54546, by decide⟩
    (prefixCache 12 4649) (prefixPartial 12 4649) = false := by
  decide +kernel

theorem node_context_12_4649_54546 : EJMOriginalGlobalDAGData.nodes 9 ⟨54546, by decide⟩ =
    .split (coordinate 12) (![⟨54482, by decide⟩,⟨54516, by decide⟩,⟨54538, by decide⟩,⟨54545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4649_54546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4649 ⟨54546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4649
    ⟨54546, by decide⟩ (by decide) (![⟨54482, by decide⟩,⟨54516, by decide⟩,⟨54538, by decide⟩,⟨54545, by decide⟩]) unmarked_context_12_4649_54546 node_context_12_4649_54546
  intro a
  fin_cases a
  · exact context_13_18596_54482
  · exact context_13_18597_54516
  · exact context_13_18598_54538
  · exact context_13_18599_54545

theorem selected_cut_01509 : selected 8 ⟨54568, by decide⟩
    (prefixPartial 13 18600) = some ⟨13, 2, 0, 54568, 18600, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_18600_54568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18600 ⟨54568, by decide⟩ :=
  accepted_of_selected 13 18600 ⟨54568, by decide⟩ ⟨13, 2, 0, 54568, 18600, 1769, 16384⟩
    (by decide) selected_cut_01509

theorem selected_cut_01510 : selected 8 ⟨54624, by decide⟩
    (prefixPartial 13 18601) = some ⟨13, 2, 0, 54624, 18601, 4049, 16384⟩ := by
  decide +kernel

theorem context_13_18601_54624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18601 ⟨54624, by decide⟩ :=
  accepted_of_selected 13 18601 ⟨54624, by decide⟩ ⟨13, 2, 0, 54624, 18601, 4049, 16384⟩
    (by decide) selected_cut_01510

theorem selected_cut_01511 : selected 8 ⟨54658, by decide⟩
    (prefixPartial 13 18602) = some ⟨13, 2, 0, 54658, 18602, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_18602_54658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18602 ⟨54658, by decide⟩ :=
  accepted_of_selected 13 18602 ⟨54658, by decide⟩ ⟨13, 2, 0, 54658, 18602, 2577, 16384⟩
    (by decide) selected_cut_01511

theorem selected_cut_01512 : selected 8 ⟨54677, by decide⟩
    (prefixPartial 13 18603) = some ⟨13, 2, 0, 54677, 18603, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_18603_54677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18603 ⟨54677, by decide⟩ :=
  accepted_of_selected 13 18603 ⟨54677, by decide⟩ ⟨13, 2, 0, 54677, 18603, 1345, 16384⟩
    (by decide) selected_cut_01512

theorem unmarked_context_12_4650_54678 : frontier 9 ⟨54678, by decide⟩
    (prefixCache 12 4650) (prefixPartial 12 4650) = false := by
  decide +kernel

theorem node_context_12_4650_54678 : EJMOriginalGlobalDAGData.nodes 9 ⟨54678, by decide⟩ =
    .split (coordinate 12) (![⟨54568, by decide⟩,⟨54624, by decide⟩,⟨54658, by decide⟩,⟨54677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4650_54678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4650 ⟨54678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4650
    ⟨54678, by decide⟩ (by decide) (![⟨54568, by decide⟩,⟨54624, by decide⟩,⟨54658, by decide⟩,⟨54677, by decide⟩]) unmarked_context_12_4650_54678 node_context_12_4650_54678
  intro a
  fin_cases a
  · exact context_13_18600_54568
  · exact context_13_18601_54624
  · exact context_13_18602_54658
  · exact context_13_18603_54677

theorem selected_cut_01513 : selected 8 ⟨54700, by decide⟩
    (prefixPartial 13 18604) = some ⟨13, 2, 0, 54700, 18604, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_18604_54700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18604 ⟨54700, by decide⟩ :=
  accepted_of_selected 13 18604 ⟨54700, by decide⟩ ⟨13, 2, 0, 54700, 18604, 1017, 16384⟩
    (by decide) selected_cut_01513

theorem selected_cut_01514 : selected 8 ⟨54747, by decide⟩
    (prefixPartial 13 18605) = some ⟨13, 2, 0, 54747, 18605, 2969, 16384⟩ := by
  decide +kernel

theorem context_13_18605_54747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18605 ⟨54747, by decide⟩ :=
  accepted_of_selected 13 18605 ⟨54747, by decide⟩ ⟨13, 2, 0, 54747, 18605, 2969, 16384⟩
    (by decide) selected_cut_01514

theorem selected_cut_01515 : selected 8 ⟨54767, by decide⟩
    (prefixPartial 13 18606) = some ⟨13, 2, 0, 54767, 18606, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_18606_54767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18606 ⟨54767, by decide⟩ :=
  accepted_of_selected 13 18606 ⟨54767, by decide⟩ ⟨13, 2, 0, 54767, 18606, 1797, 16384⟩
    (by decide) selected_cut_01515

theorem selected_cut_01516 : selected 8 ⟨54777, by decide⟩
    (prefixPartial 13 18607) = some ⟨13, 2, 0, 54777, 18607, 913, 16384⟩ := by
  decide +kernel

theorem context_13_18607_54777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18607 ⟨54777, by decide⟩ :=
  accepted_of_selected 13 18607 ⟨54777, by decide⟩ ⟨13, 2, 0, 54777, 18607, 913, 16384⟩
    (by decide) selected_cut_01516

theorem unmarked_context_12_4651_54778 : frontier 9 ⟨54778, by decide⟩
    (prefixCache 12 4651) (prefixPartial 12 4651) = false := by
  decide +kernel

theorem node_context_12_4651_54778 : EJMOriginalGlobalDAGData.nodes 9 ⟨54778, by decide⟩ =
    .split (coordinate 12) (![⟨54700, by decide⟩,⟨54747, by decide⟩,⟨54767, by decide⟩,⟨54777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4651_54778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4651 ⟨54778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4651
    ⟨54778, by decide⟩ (by decide) (![⟨54700, by decide⟩,⟨54747, by decide⟩,⟨54767, by decide⟩,⟨54777, by decide⟩]) unmarked_context_12_4651_54778 node_context_12_4651_54778
  intro a
  fin_cases a
  · exact context_13_18604_54700
  · exact context_13_18605_54747
  · exact context_13_18606_54767
  · exact context_13_18607_54777

theorem unmarked_context_11_1162_54779 : frontier 10 ⟨54779, by decide⟩
    (prefixCache 11 1162) (prefixPartial 11 1162) = false := by
  decide +kernel

theorem node_context_11_1162_54779 : EJMOriginalGlobalDAGData.nodes 10 ⟨54779, by decide⟩ =
    .split (coordinate 11) (![⟨54459, by decide⟩,⟨54546, by decide⟩,⟨54678, by decide⟩,⟨54778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1162_54779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1162 ⟨54779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1162
    ⟨54779, by decide⟩ (by decide) (![⟨54459, by decide⟩,⟨54546, by decide⟩,⟨54678, by decide⟩,⟨54778, by decide⟩]) unmarked_context_11_1162_54779 node_context_11_1162_54779
  intro a
  fin_cases a
  · exact context_12_4648_54459
  · exact context_12_4649_54546
  · exact context_12_4650_54678
  · exact context_12_4651_54778

theorem selected_cut_01517 : selected 8 ⟨54796, by decide⟩
    (prefixPartial 13 18608) = some ⟨13, 2, 0, 54796, 18608, 929, 16384⟩ := by
  decide +kernel

theorem context_13_18608_54796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18608 ⟨54796, by decide⟩ :=
  accepted_of_selected 13 18608 ⟨54796, by decide⟩ ⟨13, 2, 0, 54796, 18608, 929, 16384⟩
    (by decide) selected_cut_01517

theorem selected_cut_01518 : selected 8 ⟨54853, by decide⟩
    (prefixPartial 13 18609) = some ⟨13, 2, 0, 54853, 18609, 3813, 16384⟩ := by
  decide +kernel

theorem context_13_18609_54853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18609 ⟨54853, by decide⟩ :=
  accepted_of_selected 13 18609 ⟨54853, by decide⟩ ⟨13, 2, 0, 54853, 18609, 3813, 16384⟩
    (by decide) selected_cut_01518

theorem selected_cut_01519 : selected 8 ⟨54901, by decide⟩
    (prefixPartial 13 18610) = some ⟨13, 2, 0, 54901, 18610, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_18610_54901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18610 ⟨54901, by decide⟩ :=
  accepted_of_selected 13 18610 ⟨54901, by decide⟩ ⟨13, 2, 0, 54901, 18610, 2469, 16384⟩
    (by decide) selected_cut_01519

theorem selected_cut_01520 : selected 8 ⟨54919, by decide⟩
    (prefixPartial 13 18611) = some ⟨13, 2, 0, 54919, 18611, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_18611_54919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18611 ⟨54919, by decide⟩ :=
  accepted_of_selected 13 18611 ⟨54919, by decide⟩ ⟨13, 2, 0, 54919, 18611, 1097, 16384⟩
    (by decide) selected_cut_01520

theorem unmarked_context_12_4652_54920 : frontier 9 ⟨54920, by decide⟩
    (prefixCache 12 4652) (prefixPartial 12 4652) = false := by
  decide +kernel

theorem node_context_12_4652_54920 : EJMOriginalGlobalDAGData.nodes 9 ⟨54920, by decide⟩ =
    .split (coordinate 12) (![⟨54796, by decide⟩,⟨54853, by decide⟩,⟨54901, by decide⟩,⟨54919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4652_54920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4652 ⟨54920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4652
    ⟨54920, by decide⟩ (by decide) (![⟨54796, by decide⟩,⟨54853, by decide⟩,⟨54901, by decide⟩,⟨54919, by decide⟩]) unmarked_context_12_4652_54920 node_context_12_4652_54920
  intro a
  fin_cases a
  · exact context_13_18608_54796
  · exact context_13_18609_54853
  · exact context_13_18610_54901
  · exact context_13_18611_54919

theorem selected_cut_01521 : selected 8 ⟨54936, by decide⟩
    (prefixPartial 13 18612) = some ⟨13, 2, 0, 54936, 18612, 969, 16384⟩ := by
  decide +kernel

theorem context_13_18612_54936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18612 ⟨54936, by decide⟩ :=
  accepted_of_selected 13 18612 ⟨54936, by decide⟩ ⟨13, 2, 0, 54936, 18612, 969, 16384⟩
    (by decide) selected_cut_01521

theorem selected_cut_01522 : selected 8 ⟨54973, by decide⟩
    (prefixPartial 13 18613) = some ⟨13, 2, 0, 54973, 18613, 2853, 16384⟩ := by
  decide +kernel

theorem context_13_18613_54973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18613 ⟨54973, by decide⟩ :=
  accepted_of_selected 13 18613 ⟨54973, by decide⟩ ⟨13, 2, 0, 54973, 18613, 2853, 16384⟩
    (by decide) selected_cut_01522

theorem selected_cut_01523 : selected 8 ⟨54997, by decide⟩
    (prefixPartial 13 18614) = some ⟨13, 2, 0, 54997, 18614, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_18614_54997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18614 ⟨54997, by decide⟩ :=
  accepted_of_selected 13 18614 ⟨54997, by decide⟩ ⟨13, 2, 0, 54997, 18614, 2233, 16384⟩
    (by decide) selected_cut_01523

theorem selected_cut_01524 : selected 8 ⟨55007, by decide⟩
    (prefixPartial 13 18615) = some ⟨13, 2, 0, 55007, 18615, 977, 16384⟩ := by
  decide +kernel

theorem context_13_18615_55007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18615 ⟨55007, by decide⟩ :=
  accepted_of_selected 13 18615 ⟨55007, by decide⟩ ⟨13, 2, 0, 55007, 18615, 977, 16384⟩
    (by decide) selected_cut_01524

theorem unmarked_context_12_4653_55008 : frontier 9 ⟨55008, by decide⟩
    (prefixCache 12 4653) (prefixPartial 12 4653) = false := by
  decide +kernel

theorem node_context_12_4653_55008 : EJMOriginalGlobalDAGData.nodes 9 ⟨55008, by decide⟩ =
    .split (coordinate 12) (![⟨54936, by decide⟩,⟨54973, by decide⟩,⟨54997, by decide⟩,⟨55007, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4653_55008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4653 ⟨55008, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4653
    ⟨55008, by decide⟩ (by decide) (![⟨54936, by decide⟩,⟨54973, by decide⟩,⟨54997, by decide⟩,⟨55007, by decide⟩]) unmarked_context_12_4653_55008 node_context_12_4653_55008
  intro a
  fin_cases a
  · exact context_13_18612_54936
  · exact context_13_18613_54973
  · exact context_13_18614_54997
  · exact context_13_18615_55007

theorem selected_cut_01525 : selected 8 ⟨55027, by decide⟩
    (prefixPartial 13 18616) = some ⟨13, 2, 0, 55027, 18616, 817, 16384⟩ := by
  decide +kernel

theorem context_13_18616_55027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18616 ⟨55027, by decide⟩ :=
  accepted_of_selected 13 18616 ⟨55027, by decide⟩ ⟨13, 2, 0, 55027, 18616, 817, 16384⟩
    (by decide) selected_cut_01525

theorem selected_cut_01526 : selected 8 ⟨55063, by decide⟩
    (prefixPartial 13 18617) = some ⟨13, 2, 0, 55063, 18617, 3149, 16384⟩ := by
  decide +kernel

theorem context_13_18617_55063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18617 ⟨55063, by decide⟩ :=
  accepted_of_selected 13 18617 ⟨55063, by decide⟩ ⟨13, 2, 0, 55063, 18617, 3149, 16384⟩
    (by decide) selected_cut_01526

theorem selected_cut_01527 : selected 8 ⟨55089, by decide⟩
    (prefixPartial 13 18618) = some ⟨13, 2, 0, 55089, 18618, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_18618_55089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18618 ⟨55089, by decide⟩ :=
  accepted_of_selected 13 18618 ⟨55089, by decide⟩ ⟨13, 2, 0, 55089, 18618, 1877, 16384⟩
    (by decide) selected_cut_01527

theorem selected_cut_01528 : selected 8 ⟨55098, by decide⟩
    (prefixPartial 13 18619) = some ⟨13, 2, 0, 55098, 18619, 873, 16384⟩ := by
  decide +kernel

theorem context_13_18619_55098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18619 ⟨55098, by decide⟩ :=
  accepted_of_selected 13 18619 ⟨55098, by decide⟩ ⟨13, 2, 0, 55098, 18619, 873, 16384⟩
    (by decide) selected_cut_01528

theorem unmarked_context_12_4654_55099 : frontier 9 ⟨55099, by decide⟩
    (prefixCache 12 4654) (prefixPartial 12 4654) = false := by
  decide +kernel

theorem node_context_12_4654_55099 : EJMOriginalGlobalDAGData.nodes 9 ⟨55099, by decide⟩ =
    .split (coordinate 12) (![⟨55027, by decide⟩,⟨55063, by decide⟩,⟨55089, by decide⟩,⟨55098, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4654_55099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4654 ⟨55099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4654
    ⟨55099, by decide⟩ (by decide) (![⟨55027, by decide⟩,⟨55063, by decide⟩,⟨55089, by decide⟩,⟨55098, by decide⟩]) unmarked_context_12_4654_55099 node_context_12_4654_55099
  intro a
  fin_cases a
  · exact context_13_18616_55027
  · exact context_13_18617_55063
  · exact context_13_18618_55089
  · exact context_13_18619_55098

theorem selected_cut_01529 : selected 8 ⟨55117, by decide⟩
    (prefixPartial 13 18620) = some ⟨13, 2, 0, 55117, 18620, 805, 16384⟩ := by
  decide +kernel

theorem context_13_18620_55117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18620 ⟨55117, by decide⟩ :=
  accepted_of_selected 13 18620 ⟨55117, by decide⟩ ⟨13, 2, 0, 55117, 18620, 805, 16384⟩
    (by decide) selected_cut_01529

theorem selected_cut_01530 : selected 8 ⟨55158, by decide⟩
    (prefixPartial 13 18621) = some ⟨13, 2, 0, 55158, 18621, 3137, 16384⟩ := by
  decide +kernel

theorem context_13_18621_55158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18621 ⟨55158, by decide⟩ :=
  accepted_of_selected 13 18621 ⟨55158, by decide⟩ ⟨13, 2, 0, 55158, 18621, 3137, 16384⟩
    (by decide) selected_cut_01530

theorem selected_cut_01531 : selected 8 ⟨55180, by decide⟩
    (prefixPartial 13 18622) = some ⟨13, 2, 0, 55180, 18622, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_18622_55180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18622 ⟨55180, by decide⟩ :=
  accepted_of_selected 13 18622 ⟨55180, by decide⟩ ⟨13, 2, 0, 55180, 18622, 2045, 16384⟩
    (by decide) selected_cut_01531

theorem selected_cut_01532 : selected 8 ⟨55193, by decide⟩
    (prefixPartial 13 18623) = some ⟨13, 2, 0, 55193, 18623, 881, 16384⟩ := by
  decide +kernel

theorem context_13_18623_55193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18623 ⟨55193, by decide⟩ :=
  accepted_of_selected 13 18623 ⟨55193, by decide⟩ ⟨13, 2, 0, 55193, 18623, 881, 16384⟩
    (by decide) selected_cut_01532

theorem unmarked_context_12_4655_55194 : frontier 9 ⟨55194, by decide⟩
    (prefixCache 12 4655) (prefixPartial 12 4655) = false := by
  decide +kernel

theorem node_context_12_4655_55194 : EJMOriginalGlobalDAGData.nodes 9 ⟨55194, by decide⟩ =
    .split (coordinate 12) (![⟨55117, by decide⟩,⟨55158, by decide⟩,⟨55180, by decide⟩,⟨55193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4655_55194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4655 ⟨55194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4655
    ⟨55194, by decide⟩ (by decide) (![⟨55117, by decide⟩,⟨55158, by decide⟩,⟨55180, by decide⟩,⟨55193, by decide⟩]) unmarked_context_12_4655_55194 node_context_12_4655_55194
  intro a
  fin_cases a
  · exact context_13_18620_55117
  · exact context_13_18621_55158
  · exact context_13_18622_55180
  · exact context_13_18623_55193

theorem unmarked_context_11_1163_55195 : frontier 10 ⟨55195, by decide⟩
    (prefixCache 11 1163) (prefixPartial 11 1163) = false := by
  decide +kernel

theorem node_context_11_1163_55195 : EJMOriginalGlobalDAGData.nodes 10 ⟨55195, by decide⟩ =
    .split (coordinate 11) (![⟨54920, by decide⟩,⟨55008, by decide⟩,⟨55099, by decide⟩,⟨55194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1163_55195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1163 ⟨55195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1163
    ⟨55195, by decide⟩ (by decide) (![⟨54920, by decide⟩,⟨55008, by decide⟩,⟨55099, by decide⟩,⟨55194, by decide⟩]) unmarked_context_11_1163_55195 node_context_11_1163_55195
  intro a
  fin_cases a
  · exact context_12_4652_54920
  · exact context_12_4653_55008
  · exact context_12_4654_55099
  · exact context_12_4655_55194

theorem unmarked_context_10_290_55196 : frontier 11 ⟨55196, by decide⟩
    (prefixCache 10 290) (prefixPartial 10 290) = false := by
  decide +kernel

theorem node_context_10_290_55196 : EJMOriginalGlobalDAGData.nodes 11 ⟨55196, by decide⟩ =
    .split (coordinate 10) (![⟨53861, by decide⟩,⟨54348, by decide⟩,⟨54779, by decide⟩,⟨55195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_290_55196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 290 ⟨55196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 290
    ⟨55196, by decide⟩ (by decide) (![⟨53861, by decide⟩,⟨54348, by decide⟩,⟨54779, by decide⟩,⟨55195, by decide⟩]) unmarked_context_10_290_55196 node_context_10_290_55196
  intro a
  fin_cases a
  · exact context_11_1160_53861
  · exact context_11_1161_54348
  · exact context_11_1162_54779
  · exact context_11_1163_55195

theorem selected_cut_01533 : selected 8 ⟨55209, by decide⟩
    (prefixPartial 13 18624) = some ⟨13, 2, 0, 55209, 18624, 749, 16384⟩ := by
  decide +kernel

theorem context_13_18624_55209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18624 ⟨55209, by decide⟩ :=
  accepted_of_selected 13 18624 ⟨55209, by decide⟩ ⟨13, 2, 0, 55209, 18624, 749, 16384⟩
    (by decide) selected_cut_01533

theorem selected_cut_01534 : selected 8 ⟨55244, by decide⟩
    (prefixPartial 13 18625) = some ⟨13, 2, 0, 55244, 18625, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_18625_55244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18625 ⟨55244, by decide⟩ :=
  accepted_of_selected 13 18625 ⟨55244, by decide⟩ ⟨13, 2, 0, 55244, 18625, 2577, 16384⟩
    (by decide) selected_cut_01534

theorem selected_cut_01535 : selected 8 ⟨55265, by decide⟩
    (prefixPartial 13 18626) = some ⟨13, 2, 0, 55265, 18626, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_18626_55265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18626 ⟨55265, by decide⟩ :=
  accepted_of_selected 13 18626 ⟨55265, by decide⟩ ⟨13, 2, 0, 55265, 18626, 1709, 16384⟩
    (by decide) selected_cut_01535

theorem selected_cut_01536 : selected 8 ⟨55274, by decide⟩
    (prefixPartial 13 18627) = some ⟨13, 2, 0, 55274, 18627, 777, 16384⟩ := by
  decide +kernel

theorem context_13_18627_55274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18627 ⟨55274, by decide⟩ :=
  accepted_of_selected 13 18627 ⟨55274, by decide⟩ ⟨13, 2, 0, 55274, 18627, 777, 16384⟩
    (by decide) selected_cut_01536

theorem unmarked_context_12_4656_55275 : frontier 9 ⟨55275, by decide⟩
    (prefixCache 12 4656) (prefixPartial 12 4656) = false := by
  decide +kernel

theorem node_context_12_4656_55275 : EJMOriginalGlobalDAGData.nodes 9 ⟨55275, by decide⟩ =
    .split (coordinate 12) (![⟨55209, by decide⟩,⟨55244, by decide⟩,⟨55265, by decide⟩,⟨55274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4656_55275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4656 ⟨55275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4656
    ⟨55275, by decide⟩ (by decide) (![⟨55209, by decide⟩,⟨55244, by decide⟩,⟨55265, by decide⟩,⟨55274, by decide⟩]) unmarked_context_12_4656_55275 node_context_12_4656_55275
  intro a
  fin_cases a
  · exact context_13_18624_55209
  · exact context_13_18625_55244
  · exact context_13_18626_55265
  · exact context_13_18627_55274

theorem selected_cut_01537 : selected 8 ⟨55290, by decide⟩
    (prefixPartial 13 18628) = some ⟨13, 2, 0, 55290, 18628, 617, 16384⟩ := by
  decide +kernel

theorem context_13_18628_55290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18628 ⟨55290, by decide⟩ :=
  accepted_of_selected 13 18628 ⟨55290, by decide⟩ ⟨13, 2, 0, 55290, 18628, 617, 16384⟩
    (by decide) selected_cut_01537

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
