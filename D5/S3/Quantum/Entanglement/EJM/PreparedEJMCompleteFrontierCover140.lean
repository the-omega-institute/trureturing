/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover139
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_13443 : selected 8 ⟨352989, by decide⟩
    (prefixPartial 13 106782) = some ⟨13, 2, 0, 352989, 106782, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_106782_352989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106782 ⟨352989, by decide⟩ :=
  accepted_of_selected 13 106782 ⟨352989, by decide⟩ ⟨13, 2, 0, 352989, 106782, 1565, 16384⟩
    (by decide) selected_cut_13443

theorem selected_cut_13444 : selected 8 ⟨353000, by decide⟩
    (prefixPartial 13 106783) = some ⟨13, 2, 0, 353000, 106783, 957, 16384⟩ := by
  decide +kernel

theorem context_13_106783_353000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106783 ⟨353000, by decide⟩ :=
  accepted_of_selected 13 106783 ⟨353000, by decide⟩ ⟨13, 2, 0, 353000, 106783, 957, 16384⟩
    (by decide) selected_cut_13444

theorem unmarked_context_12_26695_353001 : frontier 9 ⟨353001, by decide⟩
    (prefixCache 12 26695) (prefixPartial 12 26695) = false := by
  decide +kernel

theorem node_context_12_26695_353001 : EJMOriginalGlobalDAGData.nodes 9 ⟨353001, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨352969, by decide⟩,⟨352989, by decide⟩,⟨353000, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26695_353001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26695 ⟨353001, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26695
    ⟨353001, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨352969, by decide⟩,⟨352989, by decide⟩,⟨353000, by decide⟩]) unmarked_context_12_26695_353001 node_context_12_26695_353001
  intro a
  fin_cases a
  · exact context_13_106780_3444
  · exact context_13_106781_352969
  · exact context_13_106782_352989
  · exact context_13_106783_353000

theorem unmarked_context_11_6673_353002 : frontier 10 ⟨353002, by decide⟩
    (prefixCache 11 6673) (prefixPartial 11 6673) = false := by
  decide +kernel

theorem node_context_11_6673_353002 : EJMOriginalGlobalDAGData.nodes 10 ⟨353002, by decide⟩ =
    .split (coordinate 11) (![⟨352859, by decide⟩,⟨268917, by decide⟩,⟨352931, by decide⟩,⟨353001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6673_353002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6673 ⟨353002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6673
    ⟨353002, by decide⟩ (by decide) (![⟨352859, by decide⟩,⟨268917, by decide⟩,⟨352931, by decide⟩,⟨353001, by decide⟩]) unmarked_context_11_6673_353002 node_context_11_6673_353002
  intro a
  fin_cases a
  · exact context_12_26692_352859
  · exact context_12_26693_268917
  · exact context_12_26694_352931
  · exact context_12_26695_353001

theorem selected_cut_13445 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106784) = some ⟨13, 1, 0, 3444, 106784, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106784_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106784 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106784 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106784, 1, 16384⟩
    (by decide) selected_cut_13445

theorem selected_cut_13446 : selected 8 ⟨353030, by decide⟩
    (prefixPartial 13 106785) = some ⟨13, 2, 0, 353030, 106785, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_106785_353030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106785 ⟨353030, by decide⟩ :=
  accepted_of_selected 13 106785 ⟨353030, by decide⟩ ⟨13, 2, 0, 353030, 106785, 2433, 16384⟩
    (by decide) selected_cut_13446

theorem selected_cut_13447 : selected 8 ⟨353053, by decide⟩
    (prefixPartial 13 106786) = some ⟨13, 2, 0, 353053, 106786, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_106786_353053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106786 ⟨353053, by decide⟩ :=
  accepted_of_selected 13 106786 ⟨353053, by decide⟩ ⟨13, 2, 0, 353053, 106786, 1521, 16384⟩
    (by decide) selected_cut_13447

theorem selected_cut_13448 : selected 8 ⟨353060, by decide⟩
    (prefixPartial 13 106787) = some ⟨13, 2, 0, 353060, 106787, 977, 16384⟩ := by
  decide +kernel

theorem context_13_106787_353060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106787 ⟨353060, by decide⟩ :=
  accepted_of_selected 13 106787 ⟨353060, by decide⟩ ⟨13, 2, 0, 353060, 106787, 977, 16384⟩
    (by decide) selected_cut_13448

theorem unmarked_context_12_26696_353061 : frontier 9 ⟨353061, by decide⟩
    (prefixCache 12 26696) (prefixPartial 12 26696) = false := by
  decide +kernel

theorem node_context_12_26696_353061 : EJMOriginalGlobalDAGData.nodes 9 ⟨353061, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353030, by decide⟩,⟨353053, by decide⟩,⟨353060, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26696_353061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26696 ⟨353061, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26696
    ⟨353061, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353030, by decide⟩,⟨353053, by decide⟩,⟨353060, by decide⟩]) unmarked_context_12_26696_353061 node_context_12_26696_353061
  intro a
  fin_cases a
  · exact context_13_106784_3444
  · exact context_13_106785_353030
  · exact context_13_106786_353053
  · exact context_13_106787_353060

theorem selected_cut_13449 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106788) = some ⟨13, 1, 0, 3444, 106788, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106788_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106788 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106788 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106788, 1, 16384⟩
    (by decide) selected_cut_13449

theorem selected_cut_13450 : selected 8 ⟨353104, by decide⟩
    (prefixPartial 13 106789) = some ⟨13, 2, 0, 353104, 106789, 2913, 16384⟩ := by
  decide +kernel

theorem context_13_106789_353104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106789 ⟨353104, by decide⟩ :=
  accepted_of_selected 13 106789 ⟨353104, by decide⟩ ⟨13, 2, 0, 353104, 106789, 2913, 16384⟩
    (by decide) selected_cut_13450

theorem selected_cut_13451 : selected 8 ⟨353127, by decide⟩
    (prefixPartial 13 106790) = some ⟨13, 2, 0, 353127, 106790, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_106790_353127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106790 ⟨353127, by decide⟩ :=
  accepted_of_selected 13 106790 ⟨353127, by decide⟩ ⟨13, 2, 0, 353127, 106790, 1837, 16384⟩
    (by decide) selected_cut_13451

theorem selected_cut_13452 : selected 8 ⟨353141, by decide⟩
    (prefixPartial 13 106791) = some ⟨13, 2, 0, 353141, 106791, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_106791_353141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106791 ⟨353141, by decide⟩ :=
  accepted_of_selected 13 106791 ⟨353141, by decide⟩ ⟨13, 2, 0, 353141, 106791, 1157, 16384⟩
    (by decide) selected_cut_13452

theorem unmarked_context_12_26697_353142 : frontier 9 ⟨353142, by decide⟩
    (prefixCache 12 26697) (prefixPartial 12 26697) = false := by
  decide +kernel

theorem node_context_12_26697_353142 : EJMOriginalGlobalDAGData.nodes 9 ⟨353142, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353104, by decide⟩,⟨353127, by decide⟩,⟨353141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26697_353142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26697 ⟨353142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26697
    ⟨353142, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353104, by decide⟩,⟨353127, by decide⟩,⟨353141, by decide⟩]) unmarked_context_12_26697_353142 node_context_12_26697_353142
  intro a
  fin_cases a
  · exact context_13_106788_3444
  · exact context_13_106789_353104
  · exact context_13_106790_353127
  · exact context_13_106791_353141

theorem selected_cut_13453 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106792) = some ⟨13, 1, 0, 3444, 106792, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106792_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106792 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106792 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106792, 1, 16384⟩
    (by decide) selected_cut_13453

theorem selected_cut_13454 : selected 8 ⟨353168, by decide⟩
    (prefixPartial 13 106793) = some ⟨13, 2, 0, 353168, 106793, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_106793_353168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106793 ⟨353168, by decide⟩ :=
  accepted_of_selected 13 106793 ⟨353168, by decide⟩ ⟨13, 2, 0, 353168, 106793, 2237, 16384⟩
    (by decide) selected_cut_13454

theorem selected_cut_13455 : selected 8 ⟨353189, by decide⟩
    (prefixPartial 13 106794) = some ⟨13, 2, 0, 353189, 106794, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_106794_353189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106794 ⟨353189, by decide⟩ :=
  accepted_of_selected 13 106794 ⟨353189, by decide⟩ ⟨13, 2, 0, 353189, 106794, 1337, 16384⟩
    (by decide) selected_cut_13455

theorem selected_cut_13456 : selected 8 ⟨353198, by decide⟩
    (prefixPartial 13 106795) = some ⟨13, 2, 0, 353198, 106795, 925, 16384⟩ := by
  decide +kernel

theorem context_13_106795_353198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106795 ⟨353198, by decide⟩ :=
  accepted_of_selected 13 106795 ⟨353198, by decide⟩ ⟨13, 2, 0, 353198, 106795, 925, 16384⟩
    (by decide) selected_cut_13456

theorem unmarked_context_12_26698_353199 : frontier 9 ⟨353199, by decide⟩
    (prefixCache 12 26698) (prefixPartial 12 26698) = false := by
  decide +kernel

theorem node_context_12_26698_353199 : EJMOriginalGlobalDAGData.nodes 9 ⟨353199, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353168, by decide⟩,⟨353189, by decide⟩,⟨353198, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26698_353199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26698 ⟨353199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26698
    ⟨353199, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353168, by decide⟩,⟨353189, by decide⟩,⟨353198, by decide⟩]) unmarked_context_12_26698_353199 node_context_12_26698_353199
  intro a
  fin_cases a
  · exact context_13_106792_3444
  · exact context_13_106793_353168
  · exact context_13_106794_353189
  · exact context_13_106795_353198

theorem selected_cut_13457 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106796) = some ⟨13, 1, 0, 3444, 106796, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106796_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106796 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106796 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106796, 1, 16384⟩
    (by decide) selected_cut_13457

theorem selected_cut_13458 : selected 8 ⟨353230, by decide⟩
    (prefixPartial 13 106797) = some ⟨13, 2, 0, 353230, 106797, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_106797_353230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106797 ⟨353230, by decide⟩ :=
  accepted_of_selected 13 106797 ⟨353230, by decide⟩ ⟨13, 2, 0, 353230, 106797, 2385, 16384⟩
    (by decide) selected_cut_13458

theorem selected_cut_13459 : selected 8 ⟨353249, by decide⟩
    (prefixPartial 13 106798) = some ⟨13, 2, 0, 353249, 106798, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_106798_353249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106798 ⟨353249, by decide⟩ :=
  accepted_of_selected 13 106798 ⟨353249, by decide⟩ ⟨13, 2, 0, 353249, 106798, 1469, 16384⟩
    (by decide) selected_cut_13459

theorem selected_cut_13460 : selected 8 ⟨353261, by decide⟩
    (prefixPartial 13 106799) = some ⟨13, 2, 0, 353261, 106799, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_106799_353261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106799 ⟨353261, by decide⟩ :=
  accepted_of_selected 13 106799 ⟨353261, by decide⟩ ⟨13, 2, 0, 353261, 106799, 1005, 16384⟩
    (by decide) selected_cut_13460

theorem unmarked_context_12_26699_353262 : frontier 9 ⟨353262, by decide⟩
    (prefixCache 12 26699) (prefixPartial 12 26699) = false := by
  decide +kernel

theorem node_context_12_26699_353262 : EJMOriginalGlobalDAGData.nodes 9 ⟨353262, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353230, by decide⟩,⟨353249, by decide⟩,⟨353261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26699_353262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26699 ⟨353262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26699
    ⟨353262, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353230, by decide⟩,⟨353249, by decide⟩,⟨353261, by decide⟩]) unmarked_context_12_26699_353262 node_context_12_26699_353262
  intro a
  fin_cases a
  · exact context_13_106796_3444
  · exact context_13_106797_353230
  · exact context_13_106798_353249
  · exact context_13_106799_353261

theorem unmarked_context_11_6674_353263 : frontier 10 ⟨353263, by decide⟩
    (prefixCache 11 6674) (prefixPartial 11 6674) = false := by
  decide +kernel

theorem node_context_11_6674_353263 : EJMOriginalGlobalDAGData.nodes 10 ⟨353263, by decide⟩ =
    .split (coordinate 11) (![⟨353061, by decide⟩,⟨353142, by decide⟩,⟨353199, by decide⟩,⟨353262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6674_353263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6674 ⟨353263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6674
    ⟨353263, by decide⟩ (by decide) (![⟨353061, by decide⟩,⟨353142, by decide⟩,⟨353199, by decide⟩,⟨353262, by decide⟩]) unmarked_context_11_6674_353263 node_context_11_6674_353263
  intro a
  fin_cases a
  · exact context_12_26696_353061
  · exact context_12_26697_353142
  · exact context_12_26698_353199
  · exact context_12_26699_353262

theorem selected_cut_13461 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106800) = some ⟨13, 1, 0, 3444, 106800, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106800_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106800 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106800 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106800, 1, 16384⟩
    (by decide) selected_cut_13461

theorem selected_cut_13462 : selected 8 ⟨353286, by decide⟩
    (prefixPartial 13 106801) = some ⟨13, 2, 0, 353286, 106801, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_106801_353286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106801 ⟨353286, by decide⟩ :=
  accepted_of_selected 13 106801 ⟨353286, by decide⟩ ⟨13, 2, 0, 353286, 106801, 1981, 16384⟩
    (by decide) selected_cut_13462

theorem selected_cut_13463 : selected 8 ⟨353305, by decide⟩
    (prefixPartial 13 106802) = some ⟨13, 2, 0, 353305, 106802, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_106802_353305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106802 ⟨353305, by decide⟩ :=
  accepted_of_selected 13 106802 ⟨353305, by decide⟩ ⟨13, 2, 0, 353305, 106802, 1333, 16384⟩
    (by decide) selected_cut_13463

theorem selected_cut_13464 : selected 8 ⟨353313, by decide⟩
    (prefixPartial 13 106803) = some ⟨13, 2, 0, 353313, 106803, 937, 16384⟩ := by
  decide +kernel

theorem context_13_106803_353313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106803 ⟨353313, by decide⟩ :=
  accepted_of_selected 13 106803 ⟨353313, by decide⟩ ⟨13, 2, 0, 353313, 106803, 937, 16384⟩
    (by decide) selected_cut_13464

theorem unmarked_context_12_26700_353314 : frontier 9 ⟨353314, by decide⟩
    (prefixCache 12 26700) (prefixPartial 12 26700) = false := by
  decide +kernel

theorem node_context_12_26700_353314 : EJMOriginalGlobalDAGData.nodes 9 ⟨353314, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353286, by decide⟩,⟨353305, by decide⟩,⟨353313, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26700_353314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26700 ⟨353314, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26700
    ⟨353314, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353286, by decide⟩,⟨353305, by decide⟩,⟨353313, by decide⟩]) unmarked_context_12_26700_353314 node_context_12_26700_353314
  intro a
  fin_cases a
  · exact context_13_106800_3444
  · exact context_13_106801_353286
  · exact context_13_106802_353305
  · exact context_13_106803_353313

theorem selected_cut_13465 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106804) = some ⟨13, 1, 0, 3444, 106804, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106804_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106804 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106804 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106804, 1, 16384⟩
    (by decide) selected_cut_13465

theorem selected_cut_13466 : selected 8 ⟨353355, by decide⟩
    (prefixPartial 13 106805) = some ⟨13, 2, 0, 353355, 106805, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_106805_353355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106805 ⟨353355, by decide⟩ :=
  accepted_of_selected 13 106805 ⟨353355, by decide⟩ ⟨13, 2, 0, 353355, 106805, 2509, 16384⟩
    (by decide) selected_cut_13466

theorem selected_cut_13467 : selected 8 ⟨353382, by decide⟩
    (prefixPartial 13 106806) = some ⟨13, 2, 0, 353382, 106806, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_106806_353382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106806 ⟨353382, by decide⟩ :=
  accepted_of_selected 13 106806 ⟨353382, by decide⟩ ⟨13, 2, 0, 353382, 106806, 1833, 16384⟩
    (by decide) selected_cut_13467

theorem selected_cut_13468 : selected 8 ⟨353403, by decide⟩
    (prefixPartial 13 106807) = some ⟨13, 2, 0, 353403, 106807, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_106807_353403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106807 ⟨353403, by decide⟩ :=
  accepted_of_selected 13 106807 ⟨353403, by decide⟩ ⟨13, 2, 0, 353403, 106807, 1129, 16384⟩
    (by decide) selected_cut_13468

theorem unmarked_context_12_26701_353404 : frontier 9 ⟨353404, by decide⟩
    (prefixCache 12 26701) (prefixPartial 12 26701) = false := by
  decide +kernel

theorem node_context_12_26701_353404 : EJMOriginalGlobalDAGData.nodes 9 ⟨353404, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353355, by decide⟩,⟨353382, by decide⟩,⟨353403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26701_353404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26701 ⟨353404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26701
    ⟨353404, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353355, by decide⟩,⟨353382, by decide⟩,⟨353403, by decide⟩]) unmarked_context_12_26701_353404 node_context_12_26701_353404
  intro a
  fin_cases a
  · exact context_13_106804_3444
  · exact context_13_106805_353355
  · exact context_13_106806_353382
  · exact context_13_106807_353403

theorem selected_cut_13469 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106808) = some ⟨13, 1, 0, 3444, 106808, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106808_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106808 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106808 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106808, 1, 16384⟩
    (by decide) selected_cut_13469

theorem selected_cut_13470 : selected 8 ⟨353425, by decide⟩
    (prefixPartial 13 106809) = some ⟨13, 2, 0, 353425, 106809, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_106809_353425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106809 ⟨353425, by decide⟩ :=
  accepted_of_selected 13 106809 ⟨353425, by decide⟩ ⟨13, 2, 0, 353425, 106809, 1969, 16384⟩
    (by decide) selected_cut_13470

theorem selected_cut_13471 : selected 8 ⟨353445, by decide⟩
    (prefixPartial 13 106810) = some ⟨13, 2, 0, 353445, 106810, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_106810_353445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106810 ⟨353445, by decide⟩ :=
  accepted_of_selected 13 106810 ⟨353445, by decide⟩ ⟨13, 2, 0, 353445, 106810, 1445, 16384⟩
    (by decide) selected_cut_13471

theorem selected_cut_13472 : selected 8 ⟨353458, by decide⟩
    (prefixPartial 13 106811) = some ⟨13, 2, 0, 353458, 106811, 885, 16384⟩ := by
  decide +kernel

theorem context_13_106811_353458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106811 ⟨353458, by decide⟩ :=
  accepted_of_selected 13 106811 ⟨353458, by decide⟩ ⟨13, 2, 0, 353458, 106811, 885, 16384⟩
    (by decide) selected_cut_13472

theorem unmarked_context_12_26702_353459 : frontier 9 ⟨353459, by decide⟩
    (prefixCache 12 26702) (prefixPartial 12 26702) = false := by
  decide +kernel

theorem node_context_12_26702_353459 : EJMOriginalGlobalDAGData.nodes 9 ⟨353459, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353425, by decide⟩,⟨353445, by decide⟩,⟨353458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26702_353459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26702 ⟨353459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26702
    ⟨353459, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353425, by decide⟩,⟨353445, by decide⟩,⟨353458, by decide⟩]) unmarked_context_12_26702_353459 node_context_12_26702_353459
  intro a
  fin_cases a
  · exact context_13_106808_3444
  · exact context_13_106809_353425
  · exact context_13_106810_353445
  · exact context_13_106811_353458

theorem selected_cut_13473 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106812) = some ⟨13, 1, 0, 3444, 106812, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106812_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106812 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106812 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106812, 1, 16384⟩
    (by decide) selected_cut_13473

theorem selected_cut_13474 : selected 8 ⟨353483, by decide⟩
    (prefixPartial 13 106813) = some ⟨13, 2, 0, 353483, 106813, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_106813_353483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106813 ⟨353483, by decide⟩ :=
  accepted_of_selected 13 106813 ⟨353483, by decide⟩ ⟨13, 2, 0, 353483, 106813, 1949, 16384⟩
    (by decide) selected_cut_13474

theorem selected_cut_13475 : selected 8 ⟨353502, by decide⟩
    (prefixPartial 13 106814) = some ⟨13, 2, 0, 353502, 106814, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_106814_353502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106814 ⟨353502, by decide⟩ :=
  accepted_of_selected 13 106814 ⟨353502, by decide⟩ ⟨13, 2, 0, 353502, 106814, 1425, 16384⟩
    (by decide) selected_cut_13475

theorem selected_cut_13476 : selected 8 ⟨353510, by decide⟩
    (prefixPartial 13 106815) = some ⟨13, 2, 0, 353510, 106815, 889, 16384⟩ := by
  decide +kernel

theorem context_13_106815_353510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106815 ⟨353510, by decide⟩ :=
  accepted_of_selected 13 106815 ⟨353510, by decide⟩ ⟨13, 2, 0, 353510, 106815, 889, 16384⟩
    (by decide) selected_cut_13476

theorem unmarked_context_12_26703_353511 : frontier 9 ⟨353511, by decide⟩
    (prefixCache 12 26703) (prefixPartial 12 26703) = false := by
  decide +kernel

theorem node_context_12_26703_353511 : EJMOriginalGlobalDAGData.nodes 9 ⟨353511, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353483, by decide⟩,⟨353502, by decide⟩,⟨353510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26703_353511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26703 ⟨353511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26703
    ⟨353511, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353483, by decide⟩,⟨353502, by decide⟩,⟨353510, by decide⟩]) unmarked_context_12_26703_353511 node_context_12_26703_353511
  intro a
  fin_cases a
  · exact context_13_106812_3444
  · exact context_13_106813_353483
  · exact context_13_106814_353502
  · exact context_13_106815_353510

theorem unmarked_context_11_6675_353512 : frontier 10 ⟨353512, by decide⟩
    (prefixCache 11 6675) (prefixPartial 11 6675) = false := by
  decide +kernel

theorem node_context_11_6675_353512 : EJMOriginalGlobalDAGData.nodes 10 ⟨353512, by decide⟩ =
    .split (coordinate 11) (![⟨353314, by decide⟩,⟨353404, by decide⟩,⟨353459, by decide⟩,⟨353511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6675_353512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6675 ⟨353512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6675
    ⟨353512, by decide⟩ (by decide) (![⟨353314, by decide⟩,⟨353404, by decide⟩,⟨353459, by decide⟩,⟨353511, by decide⟩]) unmarked_context_11_6675_353512 node_context_11_6675_353512
  intro a
  fin_cases a
  · exact context_12_26700_353314
  · exact context_12_26701_353404
  · exact context_12_26702_353459
  · exact context_12_26703_353511

theorem unmarked_context_10_1668_353513 : frontier 11 ⟨353513, by decide⟩
    (prefixCache 10 1668) (prefixPartial 10 1668) = false := by
  decide +kernel

theorem node_context_10_1668_353513 : EJMOriginalGlobalDAGData.nodes 11 ⟨353513, by decide⟩ =
    .split (coordinate 10) (![⟨352795, by decide⟩,⟨353002, by decide⟩,⟨353263, by decide⟩,⟨353512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1668_353513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1668 ⟨353513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1668
    ⟨353513, by decide⟩ (by decide) (![⟨352795, by decide⟩,⟨353002, by decide⟩,⟨353263, by decide⟩,⟨353512, by decide⟩]) unmarked_context_10_1668_353513 node_context_10_1668_353513
  intro a
  fin_cases a
  · exact context_11_6672_352795
  · exact context_11_6673_353002
  · exact context_11_6674_353263
  · exact context_11_6675_353512

theorem selected_cut_13477 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106816) = some ⟨13, 1, 0, 3444, 106816, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106816_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106816 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106816 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106816, 1, 16384⟩
    (by decide) selected_cut_13477

theorem selected_cut_13478 : selected 8 ⟨353575, by decide⟩
    (prefixPartial 13 106817) = some ⟨13, 2, 0, 353575, 106817, 3073, 16384⟩ := by
  decide +kernel

theorem context_13_106817_353575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106817 ⟨353575, by decide⟩ :=
  accepted_of_selected 13 106817 ⟨353575, by decide⟩ ⟨13, 2, 0, 353575, 106817, 3073, 16384⟩
    (by decide) selected_cut_13478

theorem selected_cut_13479 : selected 8 ⟨353603, by decide⟩
    (prefixPartial 13 106818) = some ⟨13, 2, 0, 353603, 106818, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_106818_353603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106818 ⟨353603, by decide⟩ :=
  accepted_of_selected 13 106818 ⟨353603, by decide⟩ ⟨13, 2, 0, 353603, 106818, 2301, 16384⟩
    (by decide) selected_cut_13479

theorem selected_cut_13480 : selected 8 ⟨353634, by decide⟩
    (prefixPartial 13 106819) = some ⟨13, 2, 0, 353634, 106819, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_106819_353634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106819 ⟨353634, by decide⟩ :=
  accepted_of_selected 13 106819 ⟨353634, by decide⟩ ⟨13, 2, 0, 353634, 106819, 1381, 16384⟩
    (by decide) selected_cut_13480

theorem unmarked_context_12_26704_353635 : frontier 9 ⟨353635, by decide⟩
    (prefixCache 12 26704) (prefixPartial 12 26704) = false := by
  decide +kernel

theorem node_context_12_26704_353635 : EJMOriginalGlobalDAGData.nodes 9 ⟨353635, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353575, by decide⟩,⟨353603, by decide⟩,⟨353634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26704_353635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26704 ⟨353635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26704
    ⟨353635, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353575, by decide⟩,⟨353603, by decide⟩,⟨353634, by decide⟩]) unmarked_context_12_26704_353635 node_context_12_26704_353635
  intro a
  fin_cases a
  · exact context_13_106816_3444
  · exact context_13_106817_353575
  · exact context_13_106818_353603
  · exact context_13_106819_353634

theorem selected_cut_13481 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 26705) = some ⟨12, 1, 0, 170504, 26705, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26705_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26705 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 26705 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 26705, 1, 65536⟩
    (by decide) selected_cut_13481

theorem selected_cut_13482 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106824) = some ⟨13, 1, 0, 3444, 106824, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106824_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106824 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106824 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106824, 1, 16384⟩
    (by decide) selected_cut_13482

theorem selected_cut_13483 : selected 8 ⟨353654, by decide⟩
    (prefixPartial 13 106825) = some ⟨13, 2, 0, 353654, 106825, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_106825_353654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106825 ⟨353654, by decide⟩ :=
  accepted_of_selected 13 106825 ⟨353654, by decide⟩ ⟨13, 2, 0, 353654, 106825, 1889, 16384⟩
    (by decide) selected_cut_13483

theorem selected_cut_13484 : selected 8 ⟨353676, by decide⟩
    (prefixPartial 13 106826) = some ⟨13, 2, 0, 353676, 106826, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_106826_353676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106826 ⟨353676, by decide⟩ :=
  accepted_of_selected 13 106826 ⟨353676, by decide⟩ ⟨13, 2, 0, 353676, 106826, 1505, 16384⟩
    (by decide) selected_cut_13484

theorem selected_cut_13485 : selected 8 ⟨353684, by decide⟩
    (prefixPartial 13 106827) = some ⟨13, 2, 0, 353684, 106827, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_106827_353684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106827 ⟨353684, by decide⟩ :=
  accepted_of_selected 13 106827 ⟨353684, by decide⟩ ⟨13, 2, 0, 353684, 106827, 1081, 16384⟩
    (by decide) selected_cut_13485

theorem unmarked_context_12_26706_353685 : frontier 9 ⟨353685, by decide⟩
    (prefixCache 12 26706) (prefixPartial 12 26706) = false := by
  decide +kernel

theorem node_context_12_26706_353685 : EJMOriginalGlobalDAGData.nodes 9 ⟨353685, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353654, by decide⟩,⟨353676, by decide⟩,⟨353684, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26706_353685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26706 ⟨353685, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26706
    ⟨353685, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353654, by decide⟩,⟨353676, by decide⟩,⟨353684, by decide⟩]) unmarked_context_12_26706_353685 node_context_12_26706_353685
  intro a
  fin_cases a
  · exact context_13_106824_3444
  · exact context_13_106825_353654
  · exact context_13_106826_353676
  · exact context_13_106827_353684

theorem selected_cut_13486 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106828) = some ⟨13, 1, 0, 3444, 106828, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106828_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106828 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106828 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106828, 1, 16384⟩
    (by decide) selected_cut_13486

theorem selected_cut_13487 : selected 8 ⟨353712, by decide⟩
    (prefixPartial 13 106829) = some ⟨13, 2, 0, 353712, 106829, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_106829_353712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106829 ⟨353712, by decide⟩ :=
  accepted_of_selected 13 106829 ⟨353712, by decide⟩ ⟨13, 2, 0, 353712, 106829, 1821, 16384⟩
    (by decide) selected_cut_13487

theorem selected_cut_13488 : selected 8 ⟨353731, by decide⟩
    (prefixPartial 13 106830) = some ⟨13, 2, 0, 353731, 106830, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_106830_353731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106830 ⟨353731, by decide⟩ :=
  accepted_of_selected 13 106830 ⟨353731, by decide⟩ ⟨13, 2, 0, 353731, 106830, 1585, 16384⟩
    (by decide) selected_cut_13488

theorem selected_cut_13489 : selected 8 ⟨353739, by decide⟩
    (prefixPartial 13 106831) = some ⟨13, 2, 0, 353739, 106831, 893, 16384⟩ := by
  decide +kernel

theorem context_13_106831_353739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106831 ⟨353739, by decide⟩ :=
  accepted_of_selected 13 106831 ⟨353739, by decide⟩ ⟨13, 2, 0, 353739, 106831, 893, 16384⟩
    (by decide) selected_cut_13489

theorem unmarked_context_12_26707_353740 : frontier 9 ⟨353740, by decide⟩
    (prefixCache 12 26707) (prefixPartial 12 26707) = false := by
  decide +kernel

theorem node_context_12_26707_353740 : EJMOriginalGlobalDAGData.nodes 9 ⟨353740, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353712, by decide⟩,⟨353731, by decide⟩,⟨353739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26707_353740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26707 ⟨353740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26707
    ⟨353740, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353712, by decide⟩,⟨353731, by decide⟩,⟨353739, by decide⟩]) unmarked_context_12_26707_353740 node_context_12_26707_353740
  intro a
  fin_cases a
  · exact context_13_106828_3444
  · exact context_13_106829_353712
  · exact context_13_106830_353731
  · exact context_13_106831_353739

theorem unmarked_context_11_6676_353741 : frontier 10 ⟨353741, by decide⟩
    (prefixCache 11 6676) (prefixPartial 11 6676) = false := by
  decide +kernel

theorem node_context_11_6676_353741 : EJMOriginalGlobalDAGData.nodes 10 ⟨353741, by decide⟩ =
    .split (coordinate 11) (![⟨353635, by decide⟩,⟨170504, by decide⟩,⟨353685, by decide⟩,⟨353740, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6676_353741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6676 ⟨353741, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6676
    ⟨353741, by decide⟩ (by decide) (![⟨353635, by decide⟩,⟨170504, by decide⟩,⟨353685, by decide⟩,⟨353740, by decide⟩]) unmarked_context_11_6676_353741 node_context_11_6676_353741
  intro a
  fin_cases a
  · exact context_12_26704_353635
  · exact context_12_26705_170504
  · exact context_12_26706_353685
  · exact context_12_26707_353740

theorem selected_cut_13490 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106832) = some ⟨13, 1, 0, 3444, 106832, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106832_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106832 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106832 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106832, 1, 16384⟩
    (by decide) selected_cut_13490

theorem selected_cut_13491 : selected 8 ⟨353757, by decide⟩
    (prefixPartial 13 106833) = some ⟨13, 2, 0, 353757, 106833, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_106833_353757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106833 ⟨353757, by decide⟩ :=
  accepted_of_selected 13 106833 ⟨353757, by decide⟩ ⟨13, 2, 0, 353757, 106833, 1677, 16384⟩
    (by decide) selected_cut_13491

theorem selected_cut_13492 : selected 8 ⟨353778, by decide⟩
    (prefixPartial 13 106834) = some ⟨13, 2, 0, 353778, 106834, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_106834_353778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106834 ⟨353778, by decide⟩ :=
  accepted_of_selected 13 106834 ⟨353778, by decide⟩ ⟨13, 2, 0, 353778, 106834, 1473, 16384⟩
    (by decide) selected_cut_13492

theorem selected_cut_13493 : selected 8 ⟨353790, by decide⟩
    (prefixPartial 13 106835) = some ⟨13, 2, 0, 353790, 106835, 973, 16384⟩ := by
  decide +kernel

theorem context_13_106835_353790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106835 ⟨353790, by decide⟩ :=
  accepted_of_selected 13 106835 ⟨353790, by decide⟩ ⟨13, 2, 0, 353790, 106835, 973, 16384⟩
    (by decide) selected_cut_13493

theorem unmarked_context_12_26708_353791 : frontier 9 ⟨353791, by decide⟩
    (prefixCache 12 26708) (prefixPartial 12 26708) = false := by
  decide +kernel

theorem node_context_12_26708_353791 : EJMOriginalGlobalDAGData.nodes 9 ⟨353791, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353757, by decide⟩,⟨353778, by decide⟩,⟨353790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26708_353791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26708 ⟨353791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26708
    ⟨353791, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353757, by decide⟩,⟨353778, by decide⟩,⟨353790, by decide⟩]) unmarked_context_12_26708_353791 node_context_12_26708_353791
  intro a
  fin_cases a
  · exact context_13_106832_3444
  · exact context_13_106833_353757
  · exact context_13_106834_353778
  · exact context_13_106835_353790

theorem selected_cut_13494 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 26709) = some ⟨12, 1, 0, 170504, 26709, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26709_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26709 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 26709 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 26709, 1, 65536⟩
    (by decide) selected_cut_13494

theorem selected_cut_13495 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106840) = some ⟨13, 1, 0, 3444, 106840, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106840_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106840 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106840 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106840, 1, 16384⟩
    (by decide) selected_cut_13495

theorem selected_cut_13496 : selected 8 ⟨353809, by decide⟩
    (prefixPartial 13 106841) = some ⟨13, 2, 0, 353809, 106841, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_106841_353809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106841 ⟨353809, by decide⟩ :=
  accepted_of_selected 13 106841 ⟨353809, by decide⟩ ⟨13, 2, 0, 353809, 106841, 1765, 16384⟩
    (by decide) selected_cut_13496

theorem selected_cut_13497 : selected 8 ⟨353830, by decide⟩
    (prefixPartial 13 106842) = some ⟨13, 2, 0, 353830, 106842, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_106842_353830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106842 ⟨353830, by decide⟩ :=
  accepted_of_selected 13 106842 ⟨353830, by decide⟩ ⟨13, 2, 0, 353830, 106842, 1861, 16384⟩
    (by decide) selected_cut_13497

theorem selected_cut_13498 : selected 8 ⟨353838, by decide⟩
    (prefixPartial 13 106843) = some ⟨13, 2, 0, 353838, 106843, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_106843_353838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106843 ⟨353838, by decide⟩ :=
  accepted_of_selected 13 106843 ⟨353838, by decide⟩ ⟨13, 2, 0, 353838, 106843, 1157, 16384⟩
    (by decide) selected_cut_13498

theorem unmarked_context_12_26710_353839 : frontier 9 ⟨353839, by decide⟩
    (prefixCache 12 26710) (prefixPartial 12 26710) = false := by
  decide +kernel

theorem node_context_12_26710_353839 : EJMOriginalGlobalDAGData.nodes 9 ⟨353839, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353809, by decide⟩,⟨353830, by decide⟩,⟨353838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26710_353839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26710 ⟨353839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26710
    ⟨353839, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353809, by decide⟩,⟨353830, by decide⟩,⟨353838, by decide⟩]) unmarked_context_12_26710_353839 node_context_12_26710_353839
  intro a
  fin_cases a
  · exact context_13_106840_3444
  · exact context_13_106841_353809
  · exact context_13_106842_353830
  · exact context_13_106843_353838

theorem selected_cut_13499 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106844) = some ⟨13, 1, 0, 3444, 106844, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106844_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106844 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106844 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106844, 1, 16384⟩
    (by decide) selected_cut_13499

theorem selected_cut_13500 : selected 8 ⟨353860, by decide⟩
    (prefixPartial 13 106845) = some ⟨13, 2, 0, 353860, 106845, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_106845_353860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106845 ⟨353860, by decide⟩ :=
  accepted_of_selected 13 106845 ⟨353860, by decide⟩ ⟨13, 2, 0, 353860, 106845, 1661, 16384⟩
    (by decide) selected_cut_13500

theorem selected_cut_13501 : selected 8 ⟨353883, by decide⟩
    (prefixPartial 13 106846) = some ⟨13, 2, 0, 353883, 106846, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_106846_353883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106846 ⟨353883, by decide⟩ :=
  accepted_of_selected 13 106846 ⟨353883, by decide⟩ ⟨13, 2, 0, 353883, 106846, 1885, 16384⟩
    (by decide) selected_cut_13501

theorem selected_cut_13502 : selected 8 ⟨353895, by decide⟩
    (prefixPartial 13 106847) = some ⟨13, 2, 0, 353895, 106847, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_106847_353895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106847 ⟨353895, by decide⟩ :=
  accepted_of_selected 13 106847 ⟨353895, by decide⟩ ⟨13, 2, 0, 353895, 106847, 1141, 16384⟩
    (by decide) selected_cut_13502

theorem unmarked_context_12_26711_353896 : frontier 9 ⟨353896, by decide⟩
    (prefixCache 12 26711) (prefixPartial 12 26711) = false := by
  decide +kernel

theorem node_context_12_26711_353896 : EJMOriginalGlobalDAGData.nodes 9 ⟨353896, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨353860, by decide⟩,⟨353883, by decide⟩,⟨353895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26711_353896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26711 ⟨353896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26711
    ⟨353896, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨353860, by decide⟩,⟨353883, by decide⟩,⟨353895, by decide⟩]) unmarked_context_12_26711_353896 node_context_12_26711_353896
  intro a
  fin_cases a
  · exact context_13_106844_3444
  · exact context_13_106845_353860
  · exact context_13_106846_353883
  · exact context_13_106847_353895

theorem unmarked_context_11_6677_353897 : frontier 10 ⟨353897, by decide⟩
    (prefixCache 11 6677) (prefixPartial 11 6677) = false := by
  decide +kernel

theorem node_context_11_6677_353897 : EJMOriginalGlobalDAGData.nodes 10 ⟨353897, by decide⟩ =
    .split (coordinate 11) (![⟨353791, by decide⟩,⟨170504, by decide⟩,⟨353839, by decide⟩,⟨353896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6677_353897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6677 ⟨353897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6677
    ⟨353897, by decide⟩ (by decide) (![⟨353791, by decide⟩,⟨170504, by decide⟩,⟨353839, by decide⟩,⟨353896, by decide⟩]) unmarked_context_11_6677_353897 node_context_11_6677_353897
  intro a
  fin_cases a
  · exact context_12_26708_353791
  · exact context_12_26709_170504
  · exact context_12_26710_353839
  · exact context_12_26711_353896

theorem selected_cut_13503 : selected 9 ⟨353942, by decide⟩
    (prefixPartial 12 26712) = some ⟨12, 2, 0, 353942, 26712, 4069, 65536⟩ := by
  decide +kernel

theorem context_12_26712_353942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26712 ⟨353942, by decide⟩ :=
  accepted_of_selected 12 26712 ⟨353942, by decide⟩ ⟨12, 2, 0, 353942, 26712, 4069, 65536⟩
    (by decide) selected_cut_13503

theorem selected_cut_13504 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 26713) = some ⟨12, 1, 0, 126371, 26713, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26713_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26713 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 26713 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 26713, 1, 65536⟩
    (by decide) selected_cut_13504

theorem selected_cut_13505 : selected 9 ⟨353988, by decide⟩
    (prefixPartial 12 26714) = some ⟨12, 2, 0, 353988, 26714, 4057, 65536⟩ := by
  decide +kernel

theorem context_12_26714_353988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26714 ⟨353988, by decide⟩ :=
  accepted_of_selected 12 26714 ⟨353988, by decide⟩ ⟨12, 2, 0, 353988, 26714, 4057, 65536⟩
    (by decide) selected_cut_13505

theorem selected_cut_13506 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106860) = some ⟨13, 1, 0, 3444, 106860, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106860_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106860 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106860 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106860, 1, 16384⟩
    (by decide) selected_cut_13506

theorem selected_cut_13507 : selected 8 ⟨354004, by decide⟩
    (prefixPartial 13 106861) = some ⟨13, 2, 0, 354004, 106861, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_106861_354004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106861 ⟨354004, by decide⟩ :=
  accepted_of_selected 13 106861 ⟨354004, by decide⟩ ⟨13, 2, 0, 354004, 106861, 1405, 16384⟩
    (by decide) selected_cut_13507

theorem selected_cut_13508 : selected 8 ⟨354026, by decide⟩
    (prefixPartial 13 106862) = some ⟨13, 2, 0, 354026, 106862, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_106862_354026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106862 ⟨354026, by decide⟩ :=
  accepted_of_selected 13 106862 ⟨354026, by decide⟩ ⟨13, 2, 0, 354026, 106862, 1745, 16384⟩
    (by decide) selected_cut_13508

theorem selected_cut_13509 : selected 8 ⟨354036, by decide⟩
    (prefixPartial 13 106863) = some ⟨13, 2, 0, 354036, 106863, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_106863_354036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106863 ⟨354036, by decide⟩ :=
  accepted_of_selected 13 106863 ⟨354036, by decide⟩ ⟨13, 2, 0, 354036, 106863, 1041, 16384⟩
    (by decide) selected_cut_13509

theorem unmarked_context_12_26715_354037 : frontier 9 ⟨354037, by decide⟩
    (prefixCache 12 26715) (prefixPartial 12 26715) = false := by
  decide +kernel

theorem node_context_12_26715_354037 : EJMOriginalGlobalDAGData.nodes 9 ⟨354037, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨354004, by decide⟩,⟨354026, by decide⟩,⟨354036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26715_354037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26715 ⟨354037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26715
    ⟨354037, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨354004, by decide⟩,⟨354026, by decide⟩,⟨354036, by decide⟩]) unmarked_context_12_26715_354037 node_context_12_26715_354037
  intro a
  fin_cases a
  · exact context_13_106860_3444
  · exact context_13_106861_354004
  · exact context_13_106862_354026
  · exact context_13_106863_354036

theorem unmarked_context_11_6678_354038 : frontier 10 ⟨354038, by decide⟩
    (prefixCache 11 6678) (prefixPartial 11 6678) = false := by
  decide +kernel

theorem node_context_11_6678_354038 : EJMOriginalGlobalDAGData.nodes 10 ⟨354038, by decide⟩ =
    .split (coordinate 11) (![⟨353942, by decide⟩,⟨126371, by decide⟩,⟨353988, by decide⟩,⟨354037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6678_354038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6678 ⟨354038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6678
    ⟨354038, by decide⟩ (by decide) (![⟨353942, by decide⟩,⟨126371, by decide⟩,⟨353988, by decide⟩,⟨354037, by decide⟩]) unmarked_context_11_6678_354038 node_context_11_6678_354038
  intro a
  fin_cases a
  · exact context_12_26712_353942
  · exact context_12_26713_126371
  · exact context_12_26714_353988
  · exact context_12_26715_354037

theorem selected_cut_13510 : selected 9 ⟨354078, by decide⟩
    (prefixPartial 12 26716) = some ⟨12, 2, 0, 354078, 26716, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_26716_354078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26716 ⟨354078, by decide⟩ :=
  accepted_of_selected 12 26716 ⟨354078, by decide⟩ ⟨12, 2, 0, 354078, 26716, 3537, 65536⟩
    (by decide) selected_cut_13510

theorem selected_cut_13511 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 26717) = some ⟨12, 1, 0, 320864, 26717, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26717_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26717 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 26717 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 26717, 1, 65536⟩
    (by decide) selected_cut_13511

theorem selected_cut_13512 : selected 9 ⟨354122, by decide⟩
    (prefixPartial 12 26718) = some ⟨12, 2, 0, 354122, 26718, 4053, 65536⟩ := by
  decide +kernel

theorem context_12_26718_354122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26718 ⟨354122, by decide⟩ :=
  accepted_of_selected 12 26718 ⟨354122, by decide⟩ ⟨12, 2, 0, 354122, 26718, 4053, 65536⟩
    (by decide) selected_cut_13512

theorem selected_cut_13513 : selected 9 ⟨354169, by decide⟩
    (prefixPartial 12 26719) = some ⟨12, 2, 0, 354169, 26719, 3889, 65536⟩ := by
  decide +kernel

theorem context_12_26719_354169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26719 ⟨354169, by decide⟩ :=
  accepted_of_selected 12 26719 ⟨354169, by decide⟩ ⟨12, 2, 0, 354169, 26719, 3889, 65536⟩
    (by decide) selected_cut_13513

theorem unmarked_context_11_6679_354170 : frontier 10 ⟨354170, by decide⟩
    (prefixCache 11 6679) (prefixPartial 11 6679) = false := by
  decide +kernel

theorem node_context_11_6679_354170 : EJMOriginalGlobalDAGData.nodes 10 ⟨354170, by decide⟩ =
    .split (coordinate 11) (![⟨354078, by decide⟩,⟨320864, by decide⟩,⟨354122, by decide⟩,⟨354169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6679_354170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6679 ⟨354170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6679
    ⟨354170, by decide⟩ (by decide) (![⟨354078, by decide⟩,⟨320864, by decide⟩,⟨354122, by decide⟩,⟨354169, by decide⟩]) unmarked_context_11_6679_354170 node_context_11_6679_354170
  intro a
  fin_cases a
  · exact context_12_26716_354078
  · exact context_12_26717_320864
  · exact context_12_26718_354122
  · exact context_12_26719_354169

theorem unmarked_context_10_1669_354171 : frontier 11 ⟨354171, by decide⟩
    (prefixCache 10 1669) (prefixPartial 10 1669) = false := by
  decide +kernel

theorem node_context_10_1669_354171 : EJMOriginalGlobalDAGData.nodes 11 ⟨354171, by decide⟩ =
    .split (coordinate 10) (![⟨353741, by decide⟩,⟨353897, by decide⟩,⟨354038, by decide⟩,⟨354170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1669_354171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1669 ⟨354171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1669
    ⟨354171, by decide⟩ (by decide) (![⟨353741, by decide⟩,⟨353897, by decide⟩,⟨354038, by decide⟩,⟨354170, by decide⟩]) unmarked_context_10_1669_354171 node_context_10_1669_354171
  intro a
  fin_cases a
  · exact context_11_6676_353741
  · exact context_11_6677_353897
  · exact context_11_6678_354038
  · exact context_11_6679_354170

theorem selected_cut_13514 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106880) = some ⟨13, 1, 0, 3444, 106880, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106880_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106880 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106880 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106880, 1, 16384⟩
    (by decide) selected_cut_13514

theorem selected_cut_13515 : selected 8 ⟨354212, by decide⟩
    (prefixPartial 13 106881) = some ⟨13, 2, 0, 354212, 106881, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_106881_354212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106881 ⟨354212, by decide⟩ :=
  accepted_of_selected 13 106881 ⟨354212, by decide⟩ ⟨13, 2, 0, 354212, 106881, 2201, 16384⟩
    (by decide) selected_cut_13515

theorem selected_cut_13516 : selected 8 ⟨354240, by decide⟩
    (prefixPartial 13 106882) = some ⟨13, 2, 0, 354240, 106882, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_106882_354240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106882 ⟨354240, by decide⟩ :=
  accepted_of_selected 13 106882 ⟨354240, by decide⟩ ⟨13, 2, 0, 354240, 106882, 2177, 16384⟩
    (by decide) selected_cut_13516

theorem selected_cut_13517 : selected 8 ⟨354250, by decide⟩
    (prefixPartial 13 106883) = some ⟨13, 2, 0, 354250, 106883, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_106883_354250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106883 ⟨354250, by decide⟩ :=
  accepted_of_selected 13 106883 ⟨354250, by decide⟩ ⟨13, 2, 0, 354250, 106883, 1245, 16384⟩
    (by decide) selected_cut_13517

theorem unmarked_context_12_26720_354251 : frontier 9 ⟨354251, by decide⟩
    (prefixCache 12 26720) (prefixPartial 12 26720) = false := by
  decide +kernel

theorem node_context_12_26720_354251 : EJMOriginalGlobalDAGData.nodes 9 ⟨354251, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨354212, by decide⟩,⟨354240, by decide⟩,⟨354250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26720_354251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26720 ⟨354251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26720
    ⟨354251, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨354212, by decide⟩,⟨354240, by decide⟩,⟨354250, by decide⟩]) unmarked_context_12_26720_354251 node_context_12_26720_354251
  intro a
  fin_cases a
  · exact context_13_106880_3444
  · exact context_13_106881_354212
  · exact context_13_106882_354240
  · exact context_13_106883_354250

theorem selected_cut_13518 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106884) = some ⟨13, 1, 0, 3444, 106884, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106884_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106884 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106884 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106884, 1, 16384⟩
    (by decide) selected_cut_13518

theorem selected_cut_13519 : selected 8 ⟨354269, by decide⟩
    (prefixPartial 13 106885) = some ⟨13, 2, 0, 354269, 106885, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_106885_354269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106885 ⟨354269, by decide⟩ :=
  accepted_of_selected 13 106885 ⟨354269, by decide⟩ ⟨13, 2, 0, 354269, 106885, 1709, 16384⟩
    (by decide) selected_cut_13519

theorem selected_cut_13520 : selected 8 ⟨354286, by decide⟩
    (prefixPartial 13 106886) = some ⟨13, 2, 0, 354286, 106886, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_106886_354286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106886 ⟨354286, by decide⟩ :=
  accepted_of_selected 13 106886 ⟨354286, by decide⟩ ⟨13, 2, 0, 354286, 106886, 1741, 16384⟩
    (by decide) selected_cut_13520

theorem selected_cut_13521 : selected 8 ⟨354294, by decide⟩
    (prefixPartial 13 106887) = some ⟨13, 2, 0, 354294, 106887, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_106887_354294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106887 ⟨354294, by decide⟩ :=
  accepted_of_selected 13 106887 ⟨354294, by decide⟩ ⟨13, 2, 0, 354294, 106887, 1189, 16384⟩
    (by decide) selected_cut_13521

theorem unmarked_context_12_26721_354295 : frontier 9 ⟨354295, by decide⟩
    (prefixCache 12 26721) (prefixPartial 12 26721) = false := by
  decide +kernel

theorem node_context_12_26721_354295 : EJMOriginalGlobalDAGData.nodes 9 ⟨354295, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨354269, by decide⟩,⟨354286, by decide⟩,⟨354294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26721_354295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26721 ⟨354295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26721
    ⟨354295, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨354269, by decide⟩,⟨354286, by decide⟩,⟨354294, by decide⟩]) unmarked_context_12_26721_354295 node_context_12_26721_354295
  intro a
  fin_cases a
  · exact context_13_106884_3444
  · exact context_13_106885_354269
  · exact context_13_106886_354286
  · exact context_13_106887_354294

theorem selected_cut_13522 : selected 9 ⟨354333, by decide⟩
    (prefixPartial 12 26722) = some ⟨12, 2, 0, 354333, 26722, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_26722_354333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26722 ⟨354333, by decide⟩ :=
  accepted_of_selected 12 26722 ⟨354333, by decide⟩ ⟨12, 2, 0, 354333, 26722, 3341, 65536⟩
    (by decide) selected_cut_13522

theorem selected_cut_13523 : selected 9 ⟨354377, by decide⟩
    (prefixPartial 12 26723) = some ⟨12, 2, 0, 354377, 26723, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_26723_354377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26723 ⟨354377, by decide⟩ :=
  accepted_of_selected 12 26723 ⟨354377, by decide⟩ ⟨12, 2, 0, 354377, 26723, 3405, 65536⟩
    (by decide) selected_cut_13523

theorem unmarked_context_11_6680_354378 : frontier 10 ⟨354378, by decide⟩
    (prefixCache 11 6680) (prefixPartial 11 6680) = false := by
  decide +kernel

theorem node_context_11_6680_354378 : EJMOriginalGlobalDAGData.nodes 10 ⟨354378, by decide⟩ =
    .split (coordinate 11) (![⟨354251, by decide⟩,⟨354295, by decide⟩,⟨354333, by decide⟩,⟨354377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6680_354378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6680 ⟨354378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6680
    ⟨354378, by decide⟩ (by decide) (![⟨354251, by decide⟩,⟨354295, by decide⟩,⟨354333, by decide⟩,⟨354377, by decide⟩]) unmarked_context_11_6680_354378 node_context_11_6680_354378
  intro a
  fin_cases a
  · exact context_12_26720_354251
  · exact context_12_26721_354295
  · exact context_12_26722_354333
  · exact context_12_26723_354377

theorem selected_cut_13524 : selected 9 ⟨354423, by decide⟩
    (prefixPartial 12 26724) = some ⟨12, 2, 0, 354423, 26724, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_26724_354423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26724 ⟨354423, by decide⟩ :=
  accepted_of_selected 12 26724 ⟨354423, by decide⟩ ⟨12, 2, 0, 354423, 26724, 3753, 65536⟩
    (by decide) selected_cut_13524

theorem selected_cut_13525 : selected 9 ⟨219808, by decide⟩
    (prefixPartial 12 26725) = some ⟨12, 1, 0, 219808, 26725, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26725_219808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26725 ⟨219808, by decide⟩ :=
  accepted_of_selected 12 26725 ⟨219808, by decide⟩ ⟨12, 1, 0, 219808, 26725, 1, 65536⟩
    (by decide) selected_cut_13525

theorem selected_cut_13526 : selected 9 ⟨354463, by decide⟩
    (prefixPartial 12 26726) = some ⟨12, 2, 0, 354463, 26726, 3885, 65536⟩ := by
  decide +kernel

theorem context_12_26726_354463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26726 ⟨354463, by decide⟩ :=
  accepted_of_selected 12 26726 ⟨354463, by decide⟩ ⟨12, 2, 0, 354463, 26726, 3885, 65536⟩
    (by decide) selected_cut_13526

theorem selected_cut_13527 : selected 9 ⟨354508, by decide⟩
    (prefixPartial 12 26727) = some ⟨12, 2, 0, 354508, 26727, 3985, 65536⟩ := by
  decide +kernel

theorem context_12_26727_354508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26727 ⟨354508, by decide⟩ :=
  accepted_of_selected 12 26727 ⟨354508, by decide⟩ ⟨12, 2, 0, 354508, 26727, 3985, 65536⟩
    (by decide) selected_cut_13527

theorem unmarked_context_11_6681_354509 : frontier 10 ⟨354509, by decide⟩
    (prefixCache 11 6681) (prefixPartial 11 6681) = false := by
  decide +kernel

theorem node_context_11_6681_354509 : EJMOriginalGlobalDAGData.nodes 10 ⟨354509, by decide⟩ =
    .split (coordinate 11) (![⟨354423, by decide⟩,⟨219808, by decide⟩,⟨354463, by decide⟩,⟨354508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6681_354509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6681 ⟨354509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6681
    ⟨354509, by decide⟩ (by decide) (![⟨354423, by decide⟩,⟨219808, by decide⟩,⟨354463, by decide⟩,⟨354508, by decide⟩]) unmarked_context_11_6681_354509 node_context_11_6681_354509
  intro a
  fin_cases a
  · exact context_12_26724_354423
  · exact context_12_26725_219808
  · exact context_12_26726_354463
  · exact context_12_26727_354508

theorem selected_cut_13528 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106912) = some ⟨13, 1, 0, 3444, 106912, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106912_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106912 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106912 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106912, 1, 16384⟩
    (by decide) selected_cut_13528

theorem selected_cut_13529 : selected 8 ⟨354530, by decide⟩
    (prefixPartial 13 106913) = some ⟨13, 2, 0, 354530, 106913, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_106913_354530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106913 ⟨354530, by decide⟩ :=
  accepted_of_selected 13 106913 ⟨354530, by decide⟩ ⟨13, 2, 0, 354530, 106913, 1509, 16384⟩
    (by decide) selected_cut_13529

theorem selected_cut_13530 : selected 8 ⟨354562, by decide⟩
    (prefixPartial 13 106914) = some ⟨13, 2, 0, 354562, 106914, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_106914_354562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106914 ⟨354562, by decide⟩ :=
  accepted_of_selected 13 106914 ⟨354562, by decide⟩ ⟨13, 2, 0, 354562, 106914, 2165, 16384⟩
    (by decide) selected_cut_13530

theorem selected_cut_13531 : selected 8 ⟨354585, by decide⟩
    (prefixPartial 13 106915) = some ⟨13, 2, 0, 354585, 106915, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_106915_354585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106915 ⟨354585, by decide⟩ :=
  accepted_of_selected 13 106915 ⟨354585, by decide⟩ ⟨13, 2, 0, 354585, 106915, 1209, 16384⟩
    (by decide) selected_cut_13531

theorem unmarked_context_12_26728_354586 : frontier 9 ⟨354586, by decide⟩
    (prefixCache 12 26728) (prefixPartial 12 26728) = false := by
  decide +kernel

theorem node_context_12_26728_354586 : EJMOriginalGlobalDAGData.nodes 9 ⟨354586, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨354530, by decide⟩,⟨354562, by decide⟩,⟨354585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26728_354586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26728 ⟨354586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26728
    ⟨354586, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨354530, by decide⟩,⟨354562, by decide⟩,⟨354585, by decide⟩]) unmarked_context_12_26728_354586 node_context_12_26728_354586
  intro a
  fin_cases a
  · exact context_13_106912_3444
  · exact context_13_106913_354530
  · exact context_13_106914_354562
  · exact context_13_106915_354585

theorem selected_cut_13532 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106916) = some ⟨13, 1, 0, 3444, 106916, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106916_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106916 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106916 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106916, 1, 16384⟩
    (by decide) selected_cut_13532

theorem selected_cut_13533 : selected 8 ⟨354628, by decide⟩
    (prefixPartial 13 106917) = some ⟨13, 2, 0, 354628, 106917, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_106917_354628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106917 ⟨354628, by decide⟩ :=
  accepted_of_selected 13 106917 ⟨354628, by decide⟩ ⟨13, 2, 0, 354628, 106917, 1805, 16384⟩
    (by decide) selected_cut_13533

theorem selected_cut_13534 : selected 8 ⟨354696, by decide⟩
    (prefixPartial 13 106918) = some ⟨13, 2, 0, 354696, 106918, 2857, 16384⟩ := by
  decide +kernel

theorem context_13_106918_354696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106918 ⟨354696, by decide⟩ :=
  accepted_of_selected 13 106918 ⟨354696, by decide⟩ ⟨13, 2, 0, 354696, 106918, 2857, 16384⟩
    (by decide) selected_cut_13534

theorem selected_cut_13535 : selected 8 ⟨354744, by decide⟩
    (prefixPartial 13 106919) = some ⟨13, 2, 0, 354744, 106919, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_106919_354744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106919 ⟨354744, by decide⟩ :=
  accepted_of_selected 13 106919 ⟨354744, by decide⟩ ⟨13, 2, 0, 354744, 106919, 1689, 16384⟩
    (by decide) selected_cut_13535

theorem unmarked_context_12_26729_354745 : frontier 9 ⟨354745, by decide⟩
    (prefixCache 12 26729) (prefixPartial 12 26729) = false := by
  decide +kernel

theorem node_context_12_26729_354745 : EJMOriginalGlobalDAGData.nodes 9 ⟨354745, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨354628, by decide⟩,⟨354696, by decide⟩,⟨354744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26729_354745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26729 ⟨354745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26729
    ⟨354745, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨354628, by decide⟩,⟨354696, by decide⟩,⟨354744, by decide⟩]) unmarked_context_12_26729_354745 node_context_12_26729_354745
  intro a
  fin_cases a
  · exact context_13_106916_3444
  · exact context_13_106917_354628
  · exact context_13_106918_354696
  · exact context_13_106919_354744

theorem selected_cut_13536 : selected 9 ⟨93922, by decide⟩
    (prefixPartial 12 26730) = some ⟨12, 1, 0, 93922, 26730, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26730_93922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26730 ⟨93922, by decide⟩ :=
  accepted_of_selected 12 26730 ⟨93922, by decide⟩ ⟨12, 1, 0, 93922, 26730, 1, 65536⟩
    (by decide) selected_cut_13536

theorem selected_cut_13537 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106924) = some ⟨13, 1, 0, 3444, 106924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106924, 1, 16384⟩
    (by decide) selected_cut_13537

theorem selected_cut_13538 : selected 8 ⟨354763, by decide⟩
    (prefixPartial 13 106925) = some ⟨13, 2, 0, 354763, 106925, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_106925_354763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106925 ⟨354763, by decide⟩ :=
  accepted_of_selected 13 106925 ⟨354763, by decide⟩ ⟨13, 2, 0, 354763, 106925, 1313, 16384⟩
    (by decide) selected_cut_13538

theorem selected_cut_13539 : selected 8 ⟨354784, by decide⟩
    (prefixPartial 13 106926) = some ⟨13, 2, 0, 354784, 106926, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_106926_354784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106926 ⟨354784, by decide⟩ :=
  accepted_of_selected 13 106926 ⟨354784, by decide⟩ ⟨13, 2, 0, 354784, 106926, 2233, 16384⟩
    (by decide) selected_cut_13539

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
