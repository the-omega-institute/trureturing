/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover337
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_32451 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 27093) = some ⟨11, 1, 0, 451541, 27093, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27093_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27093 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 27093 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 27093, 1, 262144⟩
    (by decide) selected_cut_32451

theorem selected_cut_32452 : selected 9 ⟨834592, by decide⟩
    (prefixPartial 12 108376) = some ⟨12, 2, 0, 834592, 108376, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_108376_834592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108376 ⟨834592, by decide⟩ :=
  accepted_of_selected 12 108376 ⟨834592, by decide⟩ ⟨12, 2, 0, 834592, 108376, 2849, 65536⟩
    (by decide) selected_cut_32452

theorem selected_cut_32453 : selected 9 ⟨834636, by decide⟩
    (prefixPartial 12 108377) = some ⟨12, 2, 0, 834636, 108377, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_108377_834636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108377 ⟨834636, by decide⟩ :=
  accepted_of_selected 12 108377 ⟨834636, by decide⟩ ⟨12, 2, 0, 834636, 108377, 2601, 65536⟩
    (by decide) selected_cut_32453

theorem selected_cut_32454 : selected 9 ⟨834676, by decide⟩
    (prefixPartial 12 108378) = some ⟨12, 2, 0, 834676, 108378, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_108378_834676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108378 ⟨834676, by decide⟩ :=
  accepted_of_selected 12 108378 ⟨834676, by decide⟩ ⟨12, 2, 0, 834676, 108378, 2785, 65536⟩
    (by decide) selected_cut_32454

theorem selected_cut_32455 : selected 9 ⟨834730, by decide⟩
    (prefixPartial 12 108379) = some ⟨12, 2, 0, 834730, 108379, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_108379_834730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108379 ⟨834730, by decide⟩ :=
  accepted_of_selected 12 108379 ⟨834730, by decide⟩ ⟨12, 2, 0, 834730, 108379, 2585, 65536⟩
    (by decide) selected_cut_32455

theorem unmarked_context_11_27094_834731 : frontier 10 ⟨834731, by decide⟩
    (prefixCache 11 27094) (prefixPartial 11 27094) = false := by
  decide +kernel

theorem node_context_11_27094_834731 : EJMOriginalGlobalDAGData.nodes 10 ⟨834731, by decide⟩ =
    .split (coordinate 11) (![⟨834592, by decide⟩,⟨834636, by decide⟩,⟨834676, by decide⟩,⟨834730, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27094_834731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27094 ⟨834731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27094
    ⟨834731, by decide⟩ (by decide) (![⟨834592, by decide⟩,⟨834636, by decide⟩,⟨834676, by decide⟩,⟨834730, by decide⟩]) unmarked_context_11_27094_834731 node_context_11_27094_834731
  intro a
  fin_cases a
  · exact context_12_108376_834592
  · exact context_12_108377_834636
  · exact context_12_108378_834676
  · exact context_12_108379_834730

theorem selected_cut_32456 : selected 9 ⟨834779, by decide⟩
    (prefixPartial 12 108380) = some ⟨12, 2, 0, 834779, 108380, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_108380_834779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108380 ⟨834779, by decide⟩ :=
  accepted_of_selected 12 108380 ⟨834779, by decide⟩ ⟨12, 2, 0, 834779, 108380, 2461, 65536⟩
    (by decide) selected_cut_32456

theorem selected_cut_32457 : selected 9 ⟨834829, by decide⟩
    (prefixPartial 12 108381) = some ⟨12, 2, 0, 834829, 108381, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_108381_834829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108381 ⟨834829, by decide⟩ :=
  accepted_of_selected 12 108381 ⟨834829, by decide⟩ ⟨12, 2, 0, 834829, 108381, 2377, 65536⟩
    (by decide) selected_cut_32457

theorem selected_cut_32458 : selected 9 ⟨834867, by decide⟩
    (prefixPartial 12 108382) = some ⟨12, 2, 0, 834867, 108382, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_108382_834867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108382 ⟨834867, by decide⟩ :=
  accepted_of_selected 12 108382 ⟨834867, by decide⟩ ⟨12, 2, 0, 834867, 108382, 2509, 65536⟩
    (by decide) selected_cut_32458

theorem selected_cut_32459 : selected 9 ⟨757807, by decide⟩
    (prefixPartial 12 108383) = some ⟨12, 1, 0, 757807, 108383, 1, 65536⟩ := by
  decide +kernel

theorem context_12_108383_757807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108383 ⟨757807, by decide⟩ :=
  accepted_of_selected 12 108383 ⟨757807, by decide⟩ ⟨12, 1, 0, 757807, 108383, 1, 65536⟩
    (by decide) selected_cut_32459

theorem unmarked_context_11_27095_834868 : frontier 10 ⟨834868, by decide⟩
    (prefixCache 11 27095) (prefixPartial 11 27095) = false := by
  decide +kernel

theorem node_context_11_27095_834868 : EJMOriginalGlobalDAGData.nodes 10 ⟨834868, by decide⟩ =
    .split (coordinate 11) (![⟨834779, by decide⟩,⟨834829, by decide⟩,⟨834867, by decide⟩,⟨757807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27095_834868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27095 ⟨834868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27095
    ⟨834868, by decide⟩ (by decide) (![⟨834779, by decide⟩,⟨834829, by decide⟩,⟨834867, by decide⟩,⟨757807, by decide⟩]) unmarked_context_11_27095_834868 node_context_11_27095_834868
  intro a
  fin_cases a
  · exact context_12_108380_834779
  · exact context_12_108381_834829
  · exact context_12_108382_834867
  · exact context_12_108383_757807

theorem unmarked_context_10_6773_834869 : frontier 11 ⟨834869, by decide⟩
    (prefixCache 10 6773) (prefixPartial 10 6773) = false := by
  decide +kernel

theorem node_context_10_6773_834869 : EJMOriginalGlobalDAGData.nodes 11 ⟨834869, by decide⟩ =
    .split (coordinate 10) (![⟨834531, by decide⟩,⟨451541, by decide⟩,⟨834731, by decide⟩,⟨834868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6773_834869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6773 ⟨834869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6773
    ⟨834869, by decide⟩ (by decide) (![⟨834531, by decide⟩,⟨451541, by decide⟩,⟨834731, by decide⟩,⟨834868, by decide⟩]) unmarked_context_10_6773_834869 node_context_10_6773_834869
  intro a
  fin_cases a
  · exact context_11_27092_834531
  · exact context_11_27093_451541
  · exact context_11_27094_834731
  · exact context_11_27095_834868

theorem selected_cut_32460 : selected 9 ⟨834907, by decide⟩
    (prefixPartial 12 108384) = some ⟨12, 2, 0, 834907, 108384, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_108384_834907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108384 ⟨834907, by decide⟩ :=
  accepted_of_selected 12 108384 ⟨834907, by decide⟩ ⟨12, 2, 0, 834907, 108384, 1529, 65536⟩
    (by decide) selected_cut_32460

theorem selected_cut_32461 : selected 9 ⟨834964, by decide⟩
    (prefixPartial 12 108385) = some ⟨12, 2, 0, 834964, 108385, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_108385_834964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108385 ⟨834964, by decide⟩ :=
  accepted_of_selected 12 108385 ⟨834964, by decide⟩ ⟨12, 2, 0, 834964, 108385, 2265, 65536⟩
    (by decide) selected_cut_32461

theorem selected_cut_32462 : selected 9 ⟨835029, by decide⟩
    (prefixPartial 12 108386) = some ⟨12, 2, 0, 835029, 108386, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_108386_835029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108386 ⟨835029, by decide⟩ :=
  accepted_of_selected 12 108386 ⟨835029, by decide⟩ ⟨12, 2, 0, 835029, 108386, 2401, 65536⟩
    (by decide) selected_cut_32462

theorem selected_cut_32463 : selected 9 ⟨835078, by decide⟩
    (prefixPartial 12 108387) = some ⟨12, 2, 0, 835078, 108387, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_108387_835078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108387 ⟨835078, by decide⟩ :=
  accepted_of_selected 12 108387 ⟨835078, by decide⟩ ⟨12, 2, 0, 835078, 108387, 2053, 65536⟩
    (by decide) selected_cut_32463

theorem unmarked_context_11_27096_835079 : frontier 10 ⟨835079, by decide⟩
    (prefixCache 11 27096) (prefixPartial 11 27096) = false := by
  decide +kernel

theorem node_context_11_27096_835079 : EJMOriginalGlobalDAGData.nodes 10 ⟨835079, by decide⟩ =
    .split (coordinate 11) (![⟨834907, by decide⟩,⟨834964, by decide⟩,⟨835029, by decide⟩,⟨835078, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27096_835079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27096 ⟨835079, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27096
    ⟨835079, by decide⟩ (by decide) (![⟨834907, by decide⟩,⟨834964, by decide⟩,⟨835029, by decide⟩,⟨835078, by decide⟩]) unmarked_context_11_27096_835079 node_context_11_27096_835079
  intro a
  fin_cases a
  · exact context_12_108384_834907
  · exact context_12_108385_834964
  · exact context_12_108386_835029
  · exact context_12_108387_835078

theorem selected_cut_32464 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 108388) = some ⟨12, 1, 0, 4595, 108388, 1, 65536⟩ := by
  decide +kernel

theorem context_12_108388_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108388 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 108388 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 108388, 1, 65536⟩
    (by decide) selected_cut_32464

theorem selected_cut_32465 : selected 9 ⟨835110, by decide⟩
    (prefixPartial 12 108389) = some ⟨12, 2, 0, 835110, 108389, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_108389_835110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108389 ⟨835110, by decide⟩ :=
  accepted_of_selected 12 108389 ⟨835110, by decide⟩ ⟨12, 2, 0, 835110, 108389, 2029, 65536⟩
    (by decide) selected_cut_32465

theorem selected_cut_32466 : selected 9 ⟨835149, by decide⟩
    (prefixPartial 12 108390) = some ⟨12, 2, 0, 835149, 108390, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_108390_835149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108390 ⟨835149, by decide⟩ :=
  accepted_of_selected 12 108390 ⟨835149, by decide⟩ ⟨12, 2, 0, 835149, 108390, 1405, 65536⟩
    (by decide) selected_cut_32466

theorem selected_cut_32467 : selected 9 ⟨835182, by decide⟩
    (prefixPartial 12 108391) = some ⟨12, 2, 0, 835182, 108391, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_108391_835182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108391 ⟨835182, by decide⟩ :=
  accepted_of_selected 12 108391 ⟨835182, by decide⟩ ⟨12, 2, 0, 835182, 108391, 1969, 65536⟩
    (by decide) selected_cut_32467

theorem unmarked_context_11_27097_835183 : frontier 10 ⟨835183, by decide⟩
    (prefixCache 11 27097) (prefixPartial 11 27097) = false := by
  decide +kernel

theorem node_context_11_27097_835183 : EJMOriginalGlobalDAGData.nodes 10 ⟨835183, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨835110, by decide⟩,⟨835149, by decide⟩,⟨835182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27097_835183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27097 ⟨835183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27097
    ⟨835183, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨835110, by decide⟩,⟨835149, by decide⟩,⟨835182, by decide⟩]) unmarked_context_11_27097_835183 node_context_11_27097_835183
  intro a
  fin_cases a
  · exact context_12_108388_4595
  · exact context_12_108389_835110
  · exact context_12_108390_835149
  · exact context_12_108391_835182

theorem selected_cut_32468 : selected 10 ⟨835242, by decide⟩
    (prefixPartial 11 27098) = some ⟨11, 2, 0, 835242, 27098, 3093, 262144⟩ := by
  decide +kernel

theorem context_11_27098_835242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27098 ⟨835242, by decide⟩ :=
  accepted_of_selected 11 27098 ⟨835242, by decide⟩ ⟨11, 2, 0, 835242, 27098, 3093, 262144⟩
    (by decide) selected_cut_32468

theorem selected_cut_32469 : selected 10 ⟨835293, by decide⟩
    (prefixPartial 11 27099) = some ⟨11, 2, 0, 835293, 27099, 489, 262144⟩ := by
  decide +kernel

theorem context_11_27099_835293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27099 ⟨835293, by decide⟩ :=
  accepted_of_selected 11 27099 ⟨835293, by decide⟩ ⟨11, 2, 0, 835293, 27099, 489, 262144⟩
    (by decide) selected_cut_32469

theorem unmarked_context_10_6774_835294 : frontier 11 ⟨835294, by decide⟩
    (prefixCache 10 6774) (prefixPartial 10 6774) = false := by
  decide +kernel

theorem node_context_10_6774_835294 : EJMOriginalGlobalDAGData.nodes 11 ⟨835294, by decide⟩ =
    .split (coordinate 10) (![⟨835079, by decide⟩,⟨835183, by decide⟩,⟨835242, by decide⟩,⟨835293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6774_835294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6774 ⟨835294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6774
    ⟨835294, by decide⟩ (by decide) (![⟨835079, by decide⟩,⟨835183, by decide⟩,⟨835242, by decide⟩,⟨835293, by decide⟩]) unmarked_context_10_6774_835294 node_context_10_6774_835294
  intro a
  fin_cases a
  · exact context_11_27096_835079
  · exact context_11_27097_835183
  · exact context_11_27098_835242
  · exact context_11_27099_835293

theorem selected_cut_32470 : selected 9 ⟨835340, by decide⟩
    (prefixPartial 12 108400) = some ⟨12, 2, 0, 835340, 108400, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_108400_835340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108400 ⟨835340, by decide⟩ :=
  accepted_of_selected 12 108400 ⟨835340, by decide⟩ ⟨12, 2, 0, 835340, 108400, 1893, 65536⟩
    (by decide) selected_cut_32470

theorem selected_cut_32471 : selected 9 ⟨835375, by decide⟩
    (prefixPartial 12 108401) = some ⟨12, 2, 0, 835375, 108401, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_108401_835375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108401 ⟨835375, by decide⟩ :=
  accepted_of_selected 12 108401 ⟨835375, by decide⟩ ⟨12, 2, 0, 835375, 108401, 1761, 65536⟩
    (by decide) selected_cut_32471

theorem selected_cut_32472 : selected 9 ⟨835408, by decide⟩
    (prefixPartial 12 108402) = some ⟨12, 2, 0, 835408, 108402, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_108402_835408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108402 ⟨835408, by decide⟩ :=
  accepted_of_selected 12 108402 ⟨835408, by decide⟩ ⟨12, 2, 0, 835408, 108402, 1805, 65536⟩
    (by decide) selected_cut_32472

theorem selected_cut_32473 : selected 9 ⟨835441, by decide⟩
    (prefixPartial 12 108403) = some ⟨12, 2, 0, 835441, 108403, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_108403_835441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108403 ⟨835441, by decide⟩ :=
  accepted_of_selected 12 108403 ⟨835441, by decide⟩ ⟨12, 2, 0, 835441, 108403, 1685, 65536⟩
    (by decide) selected_cut_32473

theorem unmarked_context_11_27100_835442 : frontier 10 ⟨835442, by decide⟩
    (prefixCache 11 27100) (prefixPartial 11 27100) = false := by
  decide +kernel

theorem node_context_11_27100_835442 : EJMOriginalGlobalDAGData.nodes 10 ⟨835442, by decide⟩ =
    .split (coordinate 11) (![⟨835340, by decide⟩,⟨835375, by decide⟩,⟨835408, by decide⟩,⟨835441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27100_835442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27100 ⟨835442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27100
    ⟨835442, by decide⟩ (by decide) (![⟨835340, by decide⟩,⟨835375, by decide⟩,⟨835408, by decide⟩,⟨835441, by decide⟩]) unmarked_context_11_27100_835442 node_context_11_27100_835442
  intro a
  fin_cases a
  · exact context_12_108400_835340
  · exact context_12_108401_835375
  · exact context_12_108402_835408
  · exact context_12_108403_835441

theorem selected_cut_32474 : selected 9 ⟨835483, by decide⟩
    (prefixPartial 12 108404) = some ⟨12, 2, 0, 835483, 108404, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_108404_835483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108404 ⟨835483, by decide⟩ :=
  accepted_of_selected 12 108404 ⟨835483, by decide⟩ ⟨12, 2, 0, 835483, 108404, 1577, 65536⟩
    (by decide) selected_cut_32474

theorem selected_cut_32475 : selected 9 ⟨835506, by decide⟩
    (prefixPartial 12 108405) = some ⟨12, 2, 0, 835506, 108405, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_108405_835506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108405 ⟨835506, by decide⟩ :=
  accepted_of_selected 12 108405 ⟨835506, by decide⟩ ⟨12, 2, 0, 835506, 108405, 1393, 65536⟩
    (by decide) selected_cut_32475

theorem selected_cut_32476 : selected 9 ⟨835534, by decide⟩
    (prefixPartial 12 108406) = some ⟨12, 2, 0, 835534, 108406, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_108406_835534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108406 ⟨835534, by decide⟩ :=
  accepted_of_selected 12 108406 ⟨835534, by decide⟩ ⟨12, 2, 0, 835534, 108406, 1485, 65536⟩
    (by decide) selected_cut_32476

theorem selected_cut_32477 : selected 9 ⟨835561, by decide⟩
    (prefixPartial 12 108407) = some ⟨12, 2, 0, 835561, 108407, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_108407_835561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108407 ⟨835561, by decide⟩ :=
  accepted_of_selected 12 108407 ⟨835561, by decide⟩ ⟨12, 2, 0, 835561, 108407, 1429, 65536⟩
    (by decide) selected_cut_32477

theorem unmarked_context_11_27101_835562 : frontier 10 ⟨835562, by decide⟩
    (prefixCache 11 27101) (prefixPartial 11 27101) = false := by
  decide +kernel

theorem node_context_11_27101_835562 : EJMOriginalGlobalDAGData.nodes 10 ⟨835562, by decide⟩ =
    .split (coordinate 11) (![⟨835483, by decide⟩,⟨835506, by decide⟩,⟨835534, by decide⟩,⟨835561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27101_835562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27101 ⟨835562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27101
    ⟨835562, by decide⟩ (by decide) (![⟨835483, by decide⟩,⟨835506, by decide⟩,⟨835534, by decide⟩,⟨835561, by decide⟩]) unmarked_context_11_27101_835562 node_context_11_27101_835562
  intro a
  fin_cases a
  · exact context_12_108404_835483
  · exact context_12_108405_835506
  · exact context_12_108406_835534
  · exact context_12_108407_835561

theorem selected_cut_32478 : selected 9 ⟨835618, by decide⟩
    (prefixPartial 12 108408) = some ⟨12, 2, 0, 835618, 108408, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_108408_835618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108408 ⟨835618, by decide⟩ :=
  accepted_of_selected 12 108408 ⟨835618, by decide⟩ ⟨12, 2, 0, 835618, 108408, 1469, 65536⟩
    (by decide) selected_cut_32478

theorem selected_cut_32479 : selected 9 ⟨835648, by decide⟩
    (prefixPartial 12 108409) = some ⟨12, 2, 0, 835648, 108409, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_108409_835648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108409 ⟨835648, by decide⟩ :=
  accepted_of_selected 12 108409 ⟨835648, by decide⟩ ⟨12, 2, 0, 835648, 108409, 1393, 65536⟩
    (by decide) selected_cut_32479

theorem selected_cut_32480 : selected 9 ⟨835673, by decide⟩
    (prefixPartial 12 108410) = some ⟨12, 2, 0, 835673, 108410, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_108410_835673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108410 ⟨835673, by decide⟩ :=
  accepted_of_selected 12 108410 ⟨835673, by decide⟩ ⟨12, 2, 0, 835673, 108410, 1333, 65536⟩
    (by decide) selected_cut_32480

theorem selected_cut_32481 : selected 9 ⟨835704, by decide⟩
    (prefixPartial 12 108411) = some ⟨12, 2, 0, 835704, 108411, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_108411_835704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108411 ⟨835704, by decide⟩ :=
  accepted_of_selected 12 108411 ⟨835704, by decide⟩ ⟨12, 2, 0, 835704, 108411, 1325, 65536⟩
    (by decide) selected_cut_32481

theorem unmarked_context_11_27102_835705 : frontier 10 ⟨835705, by decide⟩
    (prefixCache 11 27102) (prefixPartial 11 27102) = false := by
  decide +kernel

theorem node_context_11_27102_835705 : EJMOriginalGlobalDAGData.nodes 10 ⟨835705, by decide⟩ =
    .split (coordinate 11) (![⟨835618, by decide⟩,⟨835648, by decide⟩,⟨835673, by decide⟩,⟨835704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27102_835705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27102 ⟨835705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27102
    ⟨835705, by decide⟩ (by decide) (![⟨835618, by decide⟩,⟨835648, by decide⟩,⟨835673, by decide⟩,⟨835704, by decide⟩]) unmarked_context_11_27102_835705 node_context_11_27102_835705
  intro a
  fin_cases a
  · exact context_12_108408_835618
  · exact context_12_108409_835648
  · exact context_12_108410_835673
  · exact context_12_108411_835704

theorem selected_cut_32482 : selected 10 ⟨835770, by decide⟩
    (prefixPartial 11 27103) = some ⟨11, 2, 0, 835770, 27103, 3181, 262144⟩ := by
  decide +kernel

theorem context_11_27103_835770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27103 ⟨835770, by decide⟩ :=
  accepted_of_selected 11 27103 ⟨835770, by decide⟩ ⟨11, 2, 0, 835770, 27103, 3181, 262144⟩
    (by decide) selected_cut_32482

theorem unmarked_context_10_6775_835771 : frontier 11 ⟨835771, by decide⟩
    (prefixCache 10 6775) (prefixPartial 10 6775) = false := by
  decide +kernel

theorem node_context_10_6775_835771 : EJMOriginalGlobalDAGData.nodes 11 ⟨835771, by decide⟩ =
    .split (coordinate 10) (![⟨835442, by decide⟩,⟨835562, by decide⟩,⟨835705, by decide⟩,⟨835770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6775_835771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6775 ⟨835771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6775
    ⟨835771, by decide⟩ (by decide) (![⟨835442, by decide⟩,⟨835562, by decide⟩,⟨835705, by decide⟩,⟨835770, by decide⟩]) unmarked_context_10_6775_835771 node_context_10_6775_835771
  intro a
  fin_cases a
  · exact context_11_27100_835442
  · exact context_11_27101_835562
  · exact context_11_27102_835705
  · exact context_11_27103_835770

theorem unmarked_context_9_1693_835772 : frontier 12 ⟨835772, by decide⟩
    (prefixCache 9 1693) (prefixPartial 9 1693) = false := by
  decide +kernel

theorem node_context_9_1693_835772 : EJMOriginalGlobalDAGData.nodes 12 ⟨835772, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨834869, by decide⟩,⟨835294, by decide⟩,⟨835771, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1693_835772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1693 ⟨835772, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1693
    ⟨835772, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨834869, by decide⟩,⟨835294, by decide⟩,⟨835771, by decide⟩]) unmarked_context_9_1693_835772 node_context_9_1693_835772
  intro a
  fin_cases a
  · exact context_10_6772_145424
  · exact context_10_6773_834869
  · exact context_10_6774_835294
  · exact context_10_6775_835771

theorem selected_cut_32483 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 6776) = some ⟨10, 1, 0, 145424, 6776, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6776_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6776 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 6776 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 6776, 1, 1048576⟩
    (by decide) selected_cut_32483

theorem selected_cut_32484 : selected 10 ⟨835864, by decide⟩
    (prefixPartial 11 27108) = some ⟨11, 2, 0, 835864, 27108, 3121, 262144⟩ := by
  decide +kernel

theorem context_11_27108_835864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27108 ⟨835864, by decide⟩ :=
  accepted_of_selected 11 27108 ⟨835864, by decide⟩ ⟨11, 2, 0, 835864, 27108, 3121, 262144⟩
    (by decide) selected_cut_32484

theorem selected_cut_32485 : selected 10 ⟨835865, by decide⟩
    (prefixPartial 11 27109) = some ⟨11, 2, 0, 835865, 27109, 5, 262144⟩ := by
  decide +kernel

theorem context_11_27109_835865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27109 ⟨835865, by decide⟩ :=
  accepted_of_selected 11 27109 ⟨835865, by decide⟩ ⟨11, 2, 0, 835865, 27109, 5, 262144⟩
    (by decide) selected_cut_32485

theorem selected_cut_32486 : selected 10 ⟨835889, by decide⟩
    (prefixPartial 11 27110) = some ⟨11, 2, 0, 835889, 27110, 1113, 262144⟩ := by
  decide +kernel

theorem context_11_27110_835889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27110 ⟨835889, by decide⟩ :=
  accepted_of_selected 11 27110 ⟨835889, by decide⟩ ⟨11, 2, 0, 835889, 27110, 1113, 262144⟩
    (by decide) selected_cut_32486

theorem selected_cut_32487 : selected 10 ⟨835890, by decide⟩
    (prefixPartial 11 27111) = some ⟨11, 2, 0, 835890, 27111, 5, 262144⟩ := by
  decide +kernel

theorem context_11_27111_835890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27111 ⟨835890, by decide⟩ :=
  accepted_of_selected 11 27111 ⟨835890, by decide⟩ ⟨11, 2, 0, 835890, 27111, 5, 262144⟩
    (by decide) selected_cut_32487

theorem unmarked_context_10_6777_835891 : frontier 11 ⟨835891, by decide⟩
    (prefixCache 10 6777) (prefixPartial 10 6777) = false := by
  decide +kernel

theorem node_context_10_6777_835891 : EJMOriginalGlobalDAGData.nodes 11 ⟨835891, by decide⟩ =
    .split (coordinate 10) (![⟨835864, by decide⟩,⟨835865, by decide⟩,⟨835889, by decide⟩,⟨835890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6777_835891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6777 ⟨835891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6777
    ⟨835891, by decide⟩ (by decide) (![⟨835864, by decide⟩,⟨835865, by decide⟩,⟨835889, by decide⟩,⟨835890, by decide⟩]) unmarked_context_10_6777_835891 node_context_10_6777_835891
  intro a
  fin_cases a
  · exact context_11_27108_835864
  · exact context_11_27109_835865
  · exact context_11_27110_835889
  · exact context_11_27111_835890

theorem selected_cut_32488 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 6778) = some ⟨10, 1, 0, 145424, 6778, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6778_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6778 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 6778 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 6778, 1, 1048576⟩
    (by decide) selected_cut_32488

theorem selected_cut_32489 : selected 10 ⟨835926, by decide⟩
    (prefixPartial 11 27116) = some ⟨11, 2, 0, 835926, 27116, 1821, 262144⟩ := by
  decide +kernel

theorem context_11_27116_835926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27116 ⟨835926, by decide⟩ :=
  accepted_of_selected 11 27116 ⟨835926, by decide⟩ ⟨11, 2, 0, 835926, 27116, 1821, 262144⟩
    (by decide) selected_cut_32489

theorem selected_cut_32490 : selected 10 ⟨835970, by decide⟩
    (prefixPartial 11 27117) = some ⟨11, 2, 0, 835970, 27117, 1985, 262144⟩ := by
  decide +kernel

theorem context_11_27117_835970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27117 ⟨835970, by decide⟩ :=
  accepted_of_selected 11 27117 ⟨835970, by decide⟩ ⟨11, 2, 0, 835970, 27117, 1985, 262144⟩
    (by decide) selected_cut_32490

theorem selected_cut_32491 : selected 10 ⟨835998, by decide⟩
    (prefixPartial 11 27118) = some ⟨11, 2, 0, 835998, 27118, 1021, 262144⟩ := by
  decide +kernel

theorem context_11_27118_835998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27118 ⟨835998, by decide⟩ :=
  accepted_of_selected 11 27118 ⟨835998, by decide⟩ ⟨11, 2, 0, 835998, 27118, 1021, 262144⟩
    (by decide) selected_cut_32491

theorem selected_cut_32492 : selected 10 ⟨836012, by decide⟩
    (prefixPartial 11 27119) = some ⟨11, 2, 0, 836012, 27119, 501, 262144⟩ := by
  decide +kernel

theorem context_11_27119_836012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27119 ⟨836012, by decide⟩ :=
  accepted_of_selected 11 27119 ⟨836012, by decide⟩ ⟨11, 2, 0, 836012, 27119, 501, 262144⟩
    (by decide) selected_cut_32492

theorem unmarked_context_10_6779_836013 : frontier 11 ⟨836013, by decide⟩
    (prefixCache 10 6779) (prefixPartial 10 6779) = false := by
  decide +kernel

theorem node_context_10_6779_836013 : EJMOriginalGlobalDAGData.nodes 11 ⟨836013, by decide⟩ =
    .split (coordinate 10) (![⟨835926, by decide⟩,⟨835970, by decide⟩,⟨835998, by decide⟩,⟨836012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6779_836013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6779 ⟨836013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6779
    ⟨836013, by decide⟩ (by decide) (![⟨835926, by decide⟩,⟨835970, by decide⟩,⟨835998, by decide⟩,⟨836012, by decide⟩]) unmarked_context_10_6779_836013 node_context_10_6779_836013
  intro a
  fin_cases a
  · exact context_11_27116_835926
  · exact context_11_27117_835970
  · exact context_11_27118_835998
  · exact context_11_27119_836012

theorem unmarked_context_9_1694_836014 : frontier 12 ⟨836014, by decide⟩
    (prefixCache 9 1694) (prefixPartial 9 1694) = false := by
  decide +kernel

theorem node_context_9_1694_836014 : EJMOriginalGlobalDAGData.nodes 12 ⟨836014, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨835891, by decide⟩,⟨145424, by decide⟩,⟨836013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1694_836014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1694 ⟨836014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1694
    ⟨836014, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨835891, by decide⟩,⟨145424, by decide⟩,⟨836013, by decide⟩]) unmarked_context_9_1694_836014 node_context_9_1694_836014
  intro a
  fin_cases a
  · exact context_10_6776_145424
  · exact context_10_6777_835891
  · exact context_10_6778_145424
  · exact context_10_6779_836013

theorem selected_cut_32493 : selected 12 ⟨836033, by decide⟩
    (prefixPartial 9 1695) = some ⟨9, 2, 0, 836033, 1695, 777, 4194304⟩ := by
  decide +kernel

theorem context_9_1695_836033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1695 ⟨836033, by decide⟩ :=
  accepted_of_selected 9 1695 ⟨836033, by decide⟩ ⟨9, 2, 0, 836033, 1695, 777, 4194304⟩
    (by decide) selected_cut_32493

theorem unmarked_context_8_423_836034 : frontier 13 ⟨836034, by decide⟩
    (prefixCache 8 423) (prefixPartial 8 423) = false := by
  decide +kernel

theorem node_context_8_423_836034 : EJMOriginalGlobalDAGData.nodes 13 ⟨836034, by decide⟩ =
    .split (coordinate 8) (![⟨834271, by decide⟩,⟨835772, by decide⟩,⟨836014, by decide⟩,⟨836033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_423_836034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 423 ⟨836034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 423
    ⟨836034, by decide⟩ (by decide) (![⟨834271, by decide⟩,⟨835772, by decide⟩,⟨836014, by decide⟩,⟨836033, by decide⟩]) unmarked_context_8_423_836034 node_context_8_423_836034
  intro a
  fin_cases a
  · exact context_9_1692_834271
  · exact context_9_1693_835772
  · exact context_9_1694_836014
  · exact context_9_1695_836033

theorem unmarked_context_7_105_836035 : frontier 14 ⟨836035, by decide⟩
    (prefixCache 7 105) (prefixPartial 7 105) = false := by
  decide +kernel

theorem node_context_7_105_836035 : EJMOriginalGlobalDAGData.nodes 14 ⟨836035, by decide⟩ =
    .split (coordinate 7) (![⟨820921, by decide⟩,⟨829801, by decide⟩,⟨158379, by decide⟩,⟨836034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_105_836035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 105 ⟨836035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 105
    ⟨836035, by decide⟩ (by decide) (![⟨820921, by decide⟩,⟨829801, by decide⟩,⟨158379, by decide⟩,⟨836034, by decide⟩]) unmarked_context_7_105_836035 node_context_7_105_836035
  intro a
  fin_cases a
  · exact context_8_420_820921
  · exact context_8_421_829801
  · exact context_8_422_158379
  · exact context_8_423_836034

theorem selected_cut_32494 : selected 14 ⟨676732, by decide⟩
    (prefixPartial 7 106) = some ⟨7, 1, 0, 676732, 106, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_106_676732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 106 ⟨676732, by decide⟩ :=
  accepted_of_selected 7 106 ⟨676732, by decide⟩ ⟨7, 1, 0, 676732, 106, 1, 67108864⟩
    (by decide) selected_cut_32494

theorem selected_cut_32495 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 27392) = some ⟨11, 1, 0, 434745, 27392, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27392_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27392 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 27392 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 27392, 1, 262144⟩
    (by decide) selected_cut_32495

theorem selected_cut_32496 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 109572) = some ⟨12, 1, 0, 448748, 109572, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109572_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109572 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 109572 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 109572, 1, 65536⟩
    (by decide) selected_cut_32496

theorem selected_cut_32497 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 109573) = some ⟨12, 1, 0, 34034, 109573, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109573_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109573 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 109573 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 109573, 1, 65536⟩
    (by decide) selected_cut_32497

theorem selected_cut_32498 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 109574) = some ⟨12, 1, 0, 763842, 109574, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109574_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109574 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 109574 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 109574, 1, 65536⟩
    (by decide) selected_cut_32498

theorem selected_cut_32499 : selected 8 ⟨836181, by decide⟩
    (prefixPartial 13 438300) = some ⟨13, 2, 0, 836181, 438300, 3613, 16384⟩ := by
  decide +kernel

theorem context_13_438300_836181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438300 ⟨836181, by decide⟩ :=
  accepted_of_selected 13 438300 ⟨836181, by decide⟩ ⟨13, 2, 0, 836181, 438300, 3613, 16384⟩
    (by decide) selected_cut_32499

theorem selected_cut_32500 : selected 8 ⟨836291, by decide⟩
    (prefixPartial 13 438301) = some ⟨13, 2, 0, 836291, 438301, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_438301_836291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438301 ⟨836291, by decide⟩ :=
  accepted_of_selected 13 438301 ⟨836291, by decide⟩ ⟨13, 2, 0, 836291, 438301, 2237, 16384⟩
    (by decide) selected_cut_32500

theorem selected_cut_32501 : selected 8 ⟨836347, by decide⟩
    (prefixPartial 13 438302) = some ⟨13, 2, 0, 836347, 438302, 677, 16384⟩ := by
  decide +kernel

theorem context_13_438302_836347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438302 ⟨836347, by decide⟩ :=
  accepted_of_selected 13 438302 ⟨836347, by decide⟩ ⟨13, 2, 0, 836347, 438302, 677, 16384⟩
    (by decide) selected_cut_32501

theorem selected_cut_32502 : selected 8 ⟨836350, by decide⟩
    (prefixPartial 13 438303) = some ⟨13, 2, 0, 836350, 438303, 133, 16384⟩ := by
  decide +kernel

theorem context_13_438303_836350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438303 ⟨836350, by decide⟩ :=
  accepted_of_selected 13 438303 ⟨836350, by decide⟩ ⟨13, 2, 0, 836350, 438303, 133, 16384⟩
    (by decide) selected_cut_32502

theorem unmarked_context_12_109575_836351 : frontier 9 ⟨836351, by decide⟩
    (prefixCache 12 109575) (prefixPartial 12 109575) = false := by
  decide +kernel

theorem node_context_12_109575_836351 : EJMOriginalGlobalDAGData.nodes 9 ⟨836351, by decide⟩ =
    .split (coordinate 12) (![⟨836181, by decide⟩,⟨836291, by decide⟩,⟨836347, by decide⟩,⟨836350, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109575_836351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109575 ⟨836351, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109575
    ⟨836351, by decide⟩ (by decide) (![⟨836181, by decide⟩,⟨836291, by decide⟩,⟨836347, by decide⟩,⟨836350, by decide⟩]) unmarked_context_12_109575_836351 node_context_12_109575_836351
  intro a
  fin_cases a
  · exact context_13_438300_836181
  · exact context_13_438301_836291
  · exact context_13_438302_836347
  · exact context_13_438303_836350

theorem unmarked_context_11_27393_836352 : frontier 10 ⟨836352, by decide⟩
    (prefixCache 11 27393) (prefixPartial 11 27393) = false := by
  decide +kernel

theorem node_context_11_27393_836352 : EJMOriginalGlobalDAGData.nodes 10 ⟨836352, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨763842, by decide⟩,⟨836351, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27393_836352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27393 ⟨836352, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27393
    ⟨836352, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨763842, by decide⟩,⟨836351, by decide⟩]) unmarked_context_11_27393_836352 node_context_11_27393_836352
  intro a
  fin_cases a
  · exact context_12_109572_448748
  · exact context_12_109573_34034
  · exact context_12_109574_763842
  · exact context_12_109575_836351

theorem selected_cut_32503 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 109576) = some ⟨12, 1, 0, 448748, 109576, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109576_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109576 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 109576 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 109576, 1, 65536⟩
    (by decide) selected_cut_32503

theorem selected_cut_32504 : selected 7 ⟨836368, by decide⟩
    (prefixPartial 14 1753232) = some ⟨14, 2, 0, 836368, 1753232, 257, 4096⟩ := by
  decide +kernel

theorem context_14_1753232_836368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1753232 ⟨836368, by decide⟩ :=
  accepted_of_selected 14 1753232 ⟨836368, by decide⟩ ⟨14, 2, 0, 836368, 1753232, 257, 4096⟩
    (by decide) selected_cut_32504

theorem selected_cut_32505 : selected 7 ⟨836404, by decide⟩
    (prefixPartial 14 1753233) = some ⟨14, 2, 0, 836404, 1753233, 1429, 4096⟩ := by
  decide +kernel

theorem context_14_1753233_836404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1753233 ⟨836404, by decide⟩ :=
  accepted_of_selected 14 1753233 ⟨836404, by decide⟩ ⟨14, 2, 0, 836404, 1753233, 1429, 4096⟩
    (by decide) selected_cut_32505

theorem selected_cut_32506 : selected 7 ⟨836458, by decide⟩
    (prefixPartial 14 1753234) = some ⟨14, 2, 0, 836458, 1753234, 1717, 4096⟩ := by
  decide +kernel

theorem context_14_1753234_836458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1753234 ⟨836458, by decide⟩ :=
  accepted_of_selected 14 1753234 ⟨836458, by decide⟩ ⟨14, 2, 0, 836458, 1753234, 1717, 4096⟩
    (by decide) selected_cut_32506

theorem selected_cut_32507 : selected 7 ⟨836489, by decide⟩
    (prefixPartial 14 1753235) = some ⟨14, 2, 0, 836489, 1753235, 1093, 4096⟩ := by
  decide +kernel

theorem context_14_1753235_836489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1753235 ⟨836489, by decide⟩ :=
  accepted_of_selected 14 1753235 ⟨836489, by decide⟩ ⟨14, 2, 0, 836489, 1753235, 1093, 4096⟩
    (by decide) selected_cut_32507

theorem unmarked_context_13_438308_836490 : frontier 8 ⟨836490, by decide⟩
    (prefixCache 13 438308) (prefixPartial 13 438308) = false := by
  decide +kernel

theorem node_context_13_438308_836490 : EJMOriginalGlobalDAGData.nodes 8 ⟨836490, by decide⟩ =
    .split (coordinate 13) (![⟨836368, by decide⟩,⟨836404, by decide⟩,⟨836458, by decide⟩,⟨836489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_438308_836490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438308 ⟨836490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 438308
    ⟨836490, by decide⟩ (by decide) (![⟨836368, by decide⟩,⟨836404, by decide⟩,⟨836458, by decide⟩,⟨836489, by decide⟩]) unmarked_context_13_438308_836490 node_context_13_438308_836490
  intro a
  fin_cases a
  · exact context_14_1753232_836368
  · exact context_14_1753233_836404
  · exact context_14_1753234_836458
  · exact context_14_1753235_836489

theorem selected_cut_32508 : selected 8 ⟨836589, by decide⟩
    (prefixPartial 13 438309) = some ⟨13, 2, 0, 836589, 438309, 3585, 16384⟩ := by
  decide +kernel

theorem context_13_438309_836589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438309 ⟨836589, by decide⟩ :=
  accepted_of_selected 13 438309 ⟨836589, by decide⟩ ⟨13, 2, 0, 836589, 438309, 3585, 16384⟩
    (by decide) selected_cut_32508

theorem selected_cut_32509 : selected 8 ⟨836711, by decide⟩
    (prefixPartial 13 438310) = some ⟨13, 2, 0, 836711, 438310, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_438310_836711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438310 ⟨836711, by decide⟩ :=
  accepted_of_selected 13 438310 ⟨836711, by decide⟩ ⟨13, 2, 0, 836711, 438310, 2729, 16384⟩
    (by decide) selected_cut_32509

theorem selected_cut_32510 : selected 8 ⟨836721, by decide⟩
    (prefixPartial 13 438311) = some ⟨13, 2, 0, 836721, 438311, 909, 16384⟩ := by
  decide +kernel

theorem context_13_438311_836721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438311 ⟨836721, by decide⟩ :=
  accepted_of_selected 13 438311 ⟨836721, by decide⟩ ⟨13, 2, 0, 836721, 438311, 909, 16384⟩
    (by decide) selected_cut_32510

theorem unmarked_context_12_109577_836722 : frontier 9 ⟨836722, by decide⟩
    (prefixCache 12 109577) (prefixPartial 12 109577) = false := by
  decide +kernel

theorem node_context_12_109577_836722 : EJMOriginalGlobalDAGData.nodes 9 ⟨836722, by decide⟩ =
    .split (coordinate 12) (![⟨836490, by decide⟩,⟨836589, by decide⟩,⟨836711, by decide⟩,⟨836721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109577_836722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109577 ⟨836722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109577
    ⟨836722, by decide⟩ (by decide) (![⟨836490, by decide⟩,⟨836589, by decide⟩,⟨836711, by decide⟩,⟨836721, by decide⟩]) unmarked_context_12_109577_836722 node_context_12_109577_836722
  intro a
  fin_cases a
  · exact context_13_438308_836490
  · exact context_13_438309_836589
  · exact context_13_438310_836711
  · exact context_13_438311_836721

theorem selected_cut_32511 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 109578) = some ⟨12, 1, 0, 763842, 109578, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109578_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109578 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 109578 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 109578, 1, 65536⟩
    (by decide) selected_cut_32511

theorem selected_cut_32512 : selected 9 ⟨604131, by decide⟩
    (prefixPartial 12 109579) = some ⟨12, 1, 0, 604131, 109579, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109579_604131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109579 ⟨604131, by decide⟩ :=
  accepted_of_selected 12 109579 ⟨604131, by decide⟩ ⟨12, 1, 0, 604131, 109579, 1, 65536⟩
    (by decide) selected_cut_32512

theorem unmarked_context_11_27394_836723 : frontier 10 ⟨836723, by decide⟩
    (prefixCache 11 27394) (prefixPartial 11 27394) = false := by
  decide +kernel

theorem node_context_11_27394_836723 : EJMOriginalGlobalDAGData.nodes 10 ⟨836723, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨836722, by decide⟩,⟨763842, by decide⟩,⟨604131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27394_836723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27394 ⟨836723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27394
    ⟨836723, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨836722, by decide⟩,⟨763842, by decide⟩,⟨604131, by decide⟩]) unmarked_context_11_27394_836723 node_context_11_27394_836723
  intro a
  fin_cases a
  · exact context_12_109576_448748
  · exact context_12_109577_836722
  · exact context_12_109578_763842
  · exact context_12_109579_604131

theorem selected_cut_32513 : selected 10 ⟨789341, by decide⟩
    (prefixPartial 11 27395) = some ⟨11, 1, 0, 789341, 27395, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27395_789341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27395 ⟨789341, by decide⟩ :=
  accepted_of_selected 11 27395 ⟨789341, by decide⟩ ⟨11, 1, 0, 789341, 27395, 1, 262144⟩
    (by decide) selected_cut_32513

theorem unmarked_context_10_6848_836724 : frontier 11 ⟨836724, by decide⟩
    (prefixCache 10 6848) (prefixPartial 10 6848) = false := by
  decide +kernel

theorem node_context_10_6848_836724 : EJMOriginalGlobalDAGData.nodes 11 ⟨836724, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨836352, by decide⟩,⟨836723, by decide⟩,⟨789341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6848_836724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6848 ⟨836724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6848
    ⟨836724, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨836352, by decide⟩,⟨836723, by decide⟩,⟨789341, by decide⟩]) unmarked_context_10_6848_836724 node_context_10_6848_836724
  intro a
  fin_cases a
  · exact context_11_27392_434745
  · exact context_11_27393_836352
  · exact context_11_27394_836723
  · exact context_11_27395_789341

theorem selected_cut_32514 : selected 9 ⟨789343, by decide⟩
    (prefixPartial 12 109584) = some ⟨12, 1, 0, 789343, 109584, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109584_789343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109584 ⟨789343, by decide⟩ :=
  accepted_of_selected 12 109584 ⟨789343, by decide⟩ ⟨12, 1, 0, 789343, 109584, 1, 65536⟩
    (by decide) selected_cut_32514

theorem selected_cut_32515 : selected 8 ⟨836766, by decide⟩
    (prefixPartial 13 438340) = some ⟨13, 2, 0, 836766, 438340, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_438340_836766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438340 ⟨836766, by decide⟩ :=
  accepted_of_selected 13 438340 ⟨836766, by decide⟩ ⟨13, 2, 0, 836766, 438340, 2233, 16384⟩
    (by decide) selected_cut_32515

theorem selected_cut_32516 : selected 8 ⟨836804, by decide⟩
    (prefixPartial 13 438341) = some ⟨13, 2, 0, 836804, 438341, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_438341_836804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438341 ⟨836804, by decide⟩ :=
  accepted_of_selected 13 438341 ⟨836804, by decide⟩ ⟨13, 2, 0, 836804, 438341, 2245, 16384⟩
    (by decide) selected_cut_32516

theorem selected_cut_32517 : selected 8 ⟨836846, by decide⟩
    (prefixPartial 13 438342) = some ⟨13, 2, 0, 836846, 438342, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_438342_836846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438342 ⟨836846, by decide⟩ :=
  accepted_of_selected 13 438342 ⟨836846, by decide⟩ ⟨13, 2, 0, 836846, 438342, 1553, 16384⟩
    (by decide) selected_cut_32517

theorem selected_cut_32518 : selected 8 ⟨836854, by decide⟩
    (prefixPartial 13 438343) = some ⟨13, 2, 0, 836854, 438343, 745, 16384⟩ := by
  decide +kernel

theorem context_13_438343_836854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438343 ⟨836854, by decide⟩ :=
  accepted_of_selected 13 438343 ⟨836854, by decide⟩ ⟨13, 2, 0, 836854, 438343, 745, 16384⟩
    (by decide) selected_cut_32518

theorem unmarked_context_12_109585_836855 : frontier 9 ⟨836855, by decide⟩
    (prefixCache 12 109585) (prefixPartial 12 109585) = false := by
  decide +kernel

theorem node_context_12_109585_836855 : EJMOriginalGlobalDAGData.nodes 9 ⟨836855, by decide⟩ =
    .split (coordinate 12) (![⟨836766, by decide⟩,⟨836804, by decide⟩,⟨836846, by decide⟩,⟨836854, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109585_836855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109585 ⟨836855, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109585
    ⟨836855, by decide⟩ (by decide) (![⟨836766, by decide⟩,⟨836804, by decide⟩,⟨836846, by decide⟩,⟨836854, by decide⟩]) unmarked_context_12_109585_836855 node_context_12_109585_836855
  intro a
  fin_cases a
  · exact context_13_438340_836766
  · exact context_13_438341_836804
  · exact context_13_438342_836846
  · exact context_13_438343_836854

theorem selected_cut_32519 : selected 8 ⟨836890, by decide⟩
    (prefixPartial 13 438344) = some ⟨13, 2, 0, 836890, 438344, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_438344_836890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438344 ⟨836890, by decide⟩ :=
  accepted_of_selected 13 438344 ⟨836890, by decide⟩ ⟨13, 2, 0, 836890, 438344, 1741, 16384⟩
    (by decide) selected_cut_32519

theorem selected_cut_32520 : selected 8 ⟨836916, by decide⟩
    (prefixPartial 13 438345) = some ⟨13, 2, 0, 836916, 438345, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_438345_836916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438345 ⟨836916, by decide⟩ :=
  accepted_of_selected 13 438345 ⟨836916, by decide⟩ ⟨13, 2, 0, 836916, 438345, 2097, 16384⟩
    (by decide) selected_cut_32520

theorem selected_cut_32521 : selected 8 ⟨836931, by decide⟩
    (prefixPartial 13 438346) = some ⟨13, 2, 0, 836931, 438346, 933, 16384⟩ := by
  decide +kernel

theorem context_13_438346_836931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438346 ⟨836931, by decide⟩ :=
  accepted_of_selected 13 438346 ⟨836931, by decide⟩ ⟨13, 2, 0, 836931, 438346, 933, 16384⟩
    (by decide) selected_cut_32521

theorem selected_cut_32522 : selected 8 ⟨836938, by decide⟩
    (prefixPartial 13 438347) = some ⟨13, 2, 0, 836938, 438347, 793, 16384⟩ := by
  decide +kernel

theorem context_13_438347_836938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438347 ⟨836938, by decide⟩ :=
  accepted_of_selected 13 438347 ⟨836938, by decide⟩ ⟨13, 2, 0, 836938, 438347, 793, 16384⟩
    (by decide) selected_cut_32522

theorem unmarked_context_12_109586_836939 : frontier 9 ⟨836939, by decide⟩
    (prefixCache 12 109586) (prefixPartial 12 109586) = false := by
  decide +kernel

theorem node_context_12_109586_836939 : EJMOriginalGlobalDAGData.nodes 9 ⟨836939, by decide⟩ =
    .split (coordinate 12) (![⟨836890, by decide⟩,⟨836916, by decide⟩,⟨836931, by decide⟩,⟨836938, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109586_836939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109586 ⟨836939, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109586
    ⟨836939, by decide⟩ (by decide) (![⟨836890, by decide⟩,⟨836916, by decide⟩,⟨836931, by decide⟩,⟨836938, by decide⟩]) unmarked_context_12_109586_836939 node_context_12_109586_836939
  intro a
  fin_cases a
  · exact context_13_438344_836890
  · exact context_13_438345_836916
  · exact context_13_438346_836931
  · exact context_13_438347_836938

theorem selected_cut_32523 : selected 8 ⟨836978, by decide⟩
    (prefixPartial 13 438348) = some ⟨13, 2, 0, 836978, 438348, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_438348_836978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438348 ⟨836978, by decide⟩ :=
  accepted_of_selected 13 438348 ⟨836978, by decide⟩ ⟨13, 2, 0, 836978, 438348, 2077, 16384⟩
    (by decide) selected_cut_32523

theorem selected_cut_32524 : selected 8 ⟨837004, by decide⟩
    (prefixPartial 13 438349) = some ⟨13, 2, 0, 837004, 438349, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_438349_837004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438349 ⟨837004, by decide⟩ :=
  accepted_of_selected 13 438349 ⟨837004, by decide⟩ ⟨13, 2, 0, 837004, 438349, 2337, 16384⟩
    (by decide) selected_cut_32524

theorem selected_cut_32525 : selected 8 ⟨837030, by decide⟩
    (prefixPartial 13 438350) = some ⟨13, 2, 0, 837030, 438350, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_438350_837030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438350 ⟨837030, by decide⟩ :=
  accepted_of_selected 13 438350 ⟨837030, by decide⟩ ⟨13, 2, 0, 837030, 438350, 1461, 16384⟩
    (by decide) selected_cut_32525

theorem selected_cut_32526 : selected 8 ⟨837036, by decide⟩
    (prefixPartial 13 438351) = some ⟨13, 2, 0, 837036, 438351, 681, 16384⟩ := by
  decide +kernel

theorem context_13_438351_837036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438351 ⟨837036, by decide⟩ :=
  accepted_of_selected 13 438351 ⟨837036, by decide⟩ ⟨13, 2, 0, 837036, 438351, 681, 16384⟩
    (by decide) selected_cut_32526

theorem unmarked_context_12_109587_837037 : frontier 9 ⟨837037, by decide⟩
    (prefixCache 12 109587) (prefixPartial 12 109587) = false := by
  decide +kernel

theorem node_context_12_109587_837037 : EJMOriginalGlobalDAGData.nodes 9 ⟨837037, by decide⟩ =
    .split (coordinate 12) (![⟨836978, by decide⟩,⟨837004, by decide⟩,⟨837030, by decide⟩,⟨837036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109587_837037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109587 ⟨837037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109587
    ⟨837037, by decide⟩ (by decide) (![⟨836978, by decide⟩,⟨837004, by decide⟩,⟨837030, by decide⟩,⟨837036, by decide⟩]) unmarked_context_12_109587_837037 node_context_12_109587_837037
  intro a
  fin_cases a
  · exact context_13_438348_836978
  · exact context_13_438349_837004
  · exact context_13_438350_837030
  · exact context_13_438351_837036

theorem unmarked_context_11_27396_837038 : frontier 10 ⟨837038, by decide⟩
    (prefixCache 11 27396) (prefixPartial 11 27396) = false := by
  decide +kernel

theorem node_context_11_27396_837038 : EJMOriginalGlobalDAGData.nodes 10 ⟨837038, by decide⟩ =
    .split (coordinate 11) (![⟨789343, by decide⟩,⟨836855, by decide⟩,⟨836939, by decide⟩,⟨837037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27396_837038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27396 ⟨837038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27396
    ⟨837038, by decide⟩ (by decide) (![⟨789343, by decide⟩,⟨836855, by decide⟩,⟨836939, by decide⟩,⟨837037, by decide⟩]) unmarked_context_11_27396_837038 node_context_11_27396_837038
  intro a
  fin_cases a
  · exact context_12_109584_789343
  · exact context_12_109585_836855
  · exact context_12_109586_836939
  · exact context_12_109587_837037

theorem selected_cut_32527 : selected 8 ⟨837065, by decide⟩
    (prefixPartial 13 438352) = some ⟨13, 2, 0, 837065, 438352, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_438352_837065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438352 ⟨837065, by decide⟩ :=
  accepted_of_selected 13 438352 ⟨837065, by decide⟩ ⟨13, 2, 0, 837065, 438352, 1353, 16384⟩
    (by decide) selected_cut_32527

theorem selected_cut_32528 : selected 8 ⟨837101, by decide⟩
    (prefixPartial 13 438353) = some ⟨13, 2, 0, 837101, 438353, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_438353_837101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438353 ⟨837101, by decide⟩ :=
  accepted_of_selected 13 438353 ⟨837101, by decide⟩ ⟨13, 2, 0, 837101, 438353, 2221, 16384⟩
    (by decide) selected_cut_32528

theorem selected_cut_32529 : selected 8 ⟨837130, by decide⟩
    (prefixPartial 13 438354) = some ⟨13, 2, 0, 837130, 438354, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_438354_837130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438354 ⟨837130, by decide⟩ :=
  accepted_of_selected 13 438354 ⟨837130, by decide⟩ ⟨13, 2, 0, 837130, 438354, 1441, 16384⟩
    (by decide) selected_cut_32529

theorem selected_cut_32530 : selected 8 ⟨837138, by decide⟩
    (prefixPartial 13 438355) = some ⟨13, 2, 0, 837138, 438355, 745, 16384⟩ := by
  decide +kernel

theorem context_13_438355_837138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438355 ⟨837138, by decide⟩ :=
  accepted_of_selected 13 438355 ⟨837138, by decide⟩ ⟨13, 2, 0, 837138, 438355, 745, 16384⟩
    (by decide) selected_cut_32530

theorem unmarked_context_12_109588_837139 : frontier 9 ⟨837139, by decide⟩
    (prefixCache 12 109588) (prefixPartial 12 109588) = false := by
  decide +kernel

theorem node_context_12_109588_837139 : EJMOriginalGlobalDAGData.nodes 9 ⟨837139, by decide⟩ =
    .split (coordinate 12) (![⟨837065, by decide⟩,⟨837101, by decide⟩,⟨837130, by decide⟩,⟨837138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109588_837139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109588 ⟨837139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109588
    ⟨837139, by decide⟩ (by decide) (![⟨837065, by decide⟩,⟨837101, by decide⟩,⟨837130, by decide⟩,⟨837138, by decide⟩]) unmarked_context_12_109588_837139 node_context_12_109588_837139
  intro a
  fin_cases a
  · exact context_13_438352_837065
  · exact context_13_438353_837101
  · exact context_13_438354_837130
  · exact context_13_438355_837138

theorem selected_cut_32531 : selected 8 ⟨837184, by decide⟩
    (prefixPartial 13 438356) = some ⟨13, 2, 0, 837184, 438356, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_438356_837184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438356 ⟨837184, by decide⟩ :=
  accepted_of_selected 13 438356 ⟨837184, by decide⟩ ⟨13, 2, 0, 837184, 438356, 2013, 16384⟩
    (by decide) selected_cut_32531

theorem selected_cut_32532 : selected 8 ⟨837208, by decide⟩
    (prefixPartial 13 438357) = some ⟨13, 2, 0, 837208, 438357, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_438357_837208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438357 ⟨837208, by decide⟩ :=
  accepted_of_selected 13 438357 ⟨837208, by decide⟩ ⟨13, 2, 0, 837208, 438357, 2109, 16384⟩
    (by decide) selected_cut_32532

theorem selected_cut_32533 : selected 8 ⟨837243, by decide⟩
    (prefixPartial 13 438358) = some ⟨13, 2, 0, 837243, 438358, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_438358_837243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438358 ⟨837243, by decide⟩ :=
  accepted_of_selected 13 438358 ⟨837243, by decide⟩ ⟨13, 2, 0, 837243, 438358, 1789, 16384⟩
    (by decide) selected_cut_32533

theorem selected_cut_32534 : selected 8 ⟨837250, by decide⟩
    (prefixPartial 13 438359) = some ⟨13, 2, 0, 837250, 438359, 817, 16384⟩ := by
  decide +kernel

theorem context_13_438359_837250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438359 ⟨837250, by decide⟩ :=
  accepted_of_selected 13 438359 ⟨837250, by decide⟩ ⟨13, 2, 0, 837250, 438359, 817, 16384⟩
    (by decide) selected_cut_32534

theorem unmarked_context_12_109589_837251 : frontier 9 ⟨837251, by decide⟩
    (prefixCache 12 109589) (prefixPartial 12 109589) = false := by
  decide +kernel

theorem node_context_12_109589_837251 : EJMOriginalGlobalDAGData.nodes 9 ⟨837251, by decide⟩ =
    .split (coordinate 12) (![⟨837184, by decide⟩,⟨837208, by decide⟩,⟨837243, by decide⟩,⟨837250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109589_837251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109589 ⟨837251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109589
    ⟨837251, by decide⟩ (by decide) (![⟨837184, by decide⟩,⟨837208, by decide⟩,⟨837243, by decide⟩,⟨837250, by decide⟩]) unmarked_context_12_109589_837251 node_context_12_109589_837251
  intro a
  fin_cases a
  · exact context_13_438356_837184
  · exact context_13_438357_837208
  · exact context_13_438358_837243
  · exact context_13_438359_837250

theorem selected_cut_32535 : selected 8 ⟨837282, by decide⟩
    (prefixPartial 13 438360) = some ⟨13, 2, 0, 837282, 438360, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_438360_837282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438360 ⟨837282, by decide⟩ :=
  accepted_of_selected 13 438360 ⟨837282, by decide⟩ ⟨13, 2, 0, 837282, 438360, 1713, 16384⟩
    (by decide) selected_cut_32535

theorem selected_cut_32536 : selected 8 ⟨837311, by decide⟩
    (prefixPartial 13 438361) = some ⟨13, 2, 0, 837311, 438361, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_438361_837311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438361 ⟨837311, by decide⟩ :=
  accepted_of_selected 13 438361 ⟨837311, by decide⟩ ⟨13, 2, 0, 837311, 438361, 2277, 16384⟩
    (by decide) selected_cut_32536

theorem selected_cut_32537 : selected 8 ⟨837332, by decide⟩
    (prefixPartial 13 438362) = some ⟨13, 2, 0, 837332, 438362, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_438362_837332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438362 ⟨837332, by decide⟩ :=
  accepted_of_selected 13 438362 ⟨837332, by decide⟩ ⟨13, 2, 0, 837332, 438362, 1245, 16384⟩
    (by decide) selected_cut_32537

theorem selected_cut_32538 : selected 8 ⟨837340, by decide⟩
    (prefixPartial 13 438363) = some ⟨13, 2, 0, 837340, 438363, 833, 16384⟩ := by
  decide +kernel

theorem context_13_438363_837340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438363 ⟨837340, by decide⟩ :=
  accepted_of_selected 13 438363 ⟨837340, by decide⟩ ⟨13, 2, 0, 837340, 438363, 833, 16384⟩
    (by decide) selected_cut_32538

theorem unmarked_context_12_109590_837341 : frontier 9 ⟨837341, by decide⟩
    (prefixCache 12 109590) (prefixPartial 12 109590) = false := by
  decide +kernel

theorem node_context_12_109590_837341 : EJMOriginalGlobalDAGData.nodes 9 ⟨837341, by decide⟩ =
    .split (coordinate 12) (![⟨837282, by decide⟩,⟨837311, by decide⟩,⟨837332, by decide⟩,⟨837340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109590_837341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109590 ⟨837341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109590
    ⟨837341, by decide⟩ (by decide) (![⟨837282, by decide⟩,⟨837311, by decide⟩,⟨837332, by decide⟩,⟨837340, by decide⟩]) unmarked_context_12_109590_837341 node_context_12_109590_837341
  intro a
  fin_cases a
  · exact context_13_438360_837282
  · exact context_13_438361_837311
  · exact context_13_438362_837332
  · exact context_13_438363_837340

theorem selected_cut_32539 : selected 8 ⟨837380, by decide⟩
    (prefixPartial 13 438364) = some ⟨13, 2, 0, 837380, 438364, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_438364_837380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438364 ⟨837380, by decide⟩ :=
  accepted_of_selected 13 438364 ⟨837380, by decide⟩ ⟨13, 2, 0, 837380, 438364, 1961, 16384⟩
    (by decide) selected_cut_32539

theorem selected_cut_32540 : selected 8 ⟨837413, by decide⟩
    (prefixPartial 13 438365) = some ⟨13, 2, 0, 837413, 438365, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_438365_837413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438365 ⟨837413, by decide⟩ :=
  accepted_of_selected 13 438365 ⟨837413, by decide⟩ ⟨13, 2, 0, 837413, 438365, 2453, 16384⟩
    (by decide) selected_cut_32540

theorem selected_cut_32541 : selected 8 ⟨837454, by decide⟩
    (prefixPartial 13 438366) = some ⟨13, 2, 0, 837454, 438366, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_438366_837454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438366 ⟨837454, by decide⟩ :=
  accepted_of_selected 13 438366 ⟨837454, by decide⟩ ⟨13, 2, 0, 837454, 438366, 1821, 16384⟩
    (by decide) selected_cut_32541

theorem selected_cut_32542 : selected 8 ⟨837462, by decide⟩
    (prefixPartial 13 438367) = some ⟨13, 2, 0, 837462, 438367, 825, 16384⟩ := by
  decide +kernel

theorem context_13_438367_837462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438367 ⟨837462, by decide⟩ :=
  accepted_of_selected 13 438367 ⟨837462, by decide⟩ ⟨13, 2, 0, 837462, 438367, 825, 16384⟩
    (by decide) selected_cut_32542

theorem unmarked_context_12_109591_837463 : frontier 9 ⟨837463, by decide⟩
    (prefixCache 12 109591) (prefixPartial 12 109591) = false := by
  decide +kernel

theorem node_context_12_109591_837463 : EJMOriginalGlobalDAGData.nodes 9 ⟨837463, by decide⟩ =
    .split (coordinate 12) (![⟨837380, by decide⟩,⟨837413, by decide⟩,⟨837454, by decide⟩,⟨837462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109591_837463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109591 ⟨837463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109591
    ⟨837463, by decide⟩ (by decide) (![⟨837380, by decide⟩,⟨837413, by decide⟩,⟨837454, by decide⟩,⟨837462, by decide⟩]) unmarked_context_12_109591_837463 node_context_12_109591_837463
  intro a
  fin_cases a
  · exact context_13_438364_837380
  · exact context_13_438365_837413
  · exact context_13_438366_837454
  · exact context_13_438367_837462

theorem unmarked_context_11_27397_837464 : frontier 10 ⟨837464, by decide⟩
    (prefixCache 11 27397) (prefixPartial 11 27397) = false := by
  decide +kernel

theorem node_context_11_27397_837464 : EJMOriginalGlobalDAGData.nodes 10 ⟨837464, by decide⟩ =
    .split (coordinate 11) (![⟨837139, by decide⟩,⟨837251, by decide⟩,⟨837341, by decide⟩,⟨837463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27397_837464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27397 ⟨837464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27397
    ⟨837464, by decide⟩ (by decide) (![⟨837139, by decide⟩,⟨837251, by decide⟩,⟨837341, by decide⟩,⟨837463, by decide⟩]) unmarked_context_11_27397_837464 node_context_11_27397_837464
  intro a
  fin_cases a
  · exact context_12_109588_837139
  · exact context_12_109589_837251
  · exact context_12_109590_837341
  · exact context_12_109591_837463

theorem selected_cut_32543 : selected 8 ⟨837484, by decide⟩
    (prefixPartial 13 438368) = some ⟨13, 2, 0, 837484, 438368, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_438368_837484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438368 ⟨837484, by decide⟩ :=
  accepted_of_selected 13 438368 ⟨837484, by decide⟩ ⟨13, 2, 0, 837484, 438368, 1281, 16384⟩
    (by decide) selected_cut_32543

theorem selected_cut_32544 : selected 8 ⟨837517, by decide⟩
    (prefixPartial 13 438369) = some ⟨13, 2, 0, 837517, 438369, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_438369_837517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438369 ⟨837517, by decide⟩ :=
  accepted_of_selected 13 438369 ⟨837517, by decide⟩ ⟨13, 2, 0, 837517, 438369, 2337, 16384⟩
    (by decide) selected_cut_32544

theorem selected_cut_32545 : selected 8 ⟨837557, by decide⟩
    (prefixPartial 13 438370) = some ⟨13, 2, 0, 837557, 438370, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_438370_837557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438370 ⟨837557, by decide⟩ :=
  accepted_of_selected 13 438370 ⟨837557, by decide⟩ ⟨13, 2, 0, 837557, 438370, 1489, 16384⟩
    (by decide) selected_cut_32545

theorem selected_cut_32546 : selected 8 ⟨837565, by decide⟩
    (prefixPartial 13 438371) = some ⟨13, 2, 0, 837565, 438371, 553, 16384⟩ := by
  decide +kernel

theorem context_13_438371_837565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438371 ⟨837565, by decide⟩ :=
  accepted_of_selected 13 438371 ⟨837565, by decide⟩ ⟨13, 2, 0, 837565, 438371, 553, 16384⟩
    (by decide) selected_cut_32546

theorem unmarked_context_12_109592_837566 : frontier 9 ⟨837566, by decide⟩
    (prefixCache 12 109592) (prefixPartial 12 109592) = false := by
  decide +kernel

theorem node_context_12_109592_837566 : EJMOriginalGlobalDAGData.nodes 9 ⟨837566, by decide⟩ =
    .split (coordinate 12) (![⟨837484, by decide⟩,⟨837517, by decide⟩,⟨837557, by decide⟩,⟨837565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109592_837566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109592 ⟨837566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109592
    ⟨837566, by decide⟩ (by decide) (![⟨837484, by decide⟩,⟨837517, by decide⟩,⟨837557, by decide⟩,⟨837565, by decide⟩]) unmarked_context_12_109592_837566 node_context_12_109592_837566
  intro a
  fin_cases a
  · exact context_13_438368_837484
  · exact context_13_438369_837517
  · exact context_13_438370_837557
  · exact context_13_438371_837565

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
