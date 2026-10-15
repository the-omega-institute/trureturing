/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover395
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_18795_1021530 : frontier 11 ⟨1021530, by decide⟩
    (prefixCache 10 18795) (prefixPartial 10 18795) = false := by
  decide +kernel

theorem node_context_10_18795_1021530 : EJMOriginalGlobalDAGData.nodes 11 ⟨1021530, by decide⟩ =
    .split (coordinate 10) (![⟨1021422, by decide⟩,⟨1021456, by decide⟩,⟨1021490, by decide⟩,⟨1021529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18795_1021530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18795 ⟨1021530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18795
    ⟨1021530, by decide⟩ (by decide) (![⟨1021422, by decide⟩,⟨1021456, by decide⟩,⟨1021490, by decide⟩,⟨1021529, by decide⟩]) unmarked_context_10_18795_1021530 node_context_10_18795_1021530
  intro a
  fin_cases a
  · exact context_11_75180_1021422
  · exact context_11_75181_1021456
  · exact context_11_75182_1021490
  · exact context_11_75183_1021529

theorem unmarked_context_9_4698_1021531 : frontier 12 ⟨1021531, by decide⟩
    (prefixCache 9 4698) (prefixPartial 9 4698) = false := by
  decide +kernel

theorem node_context_9_4698_1021531 : EJMOriginalGlobalDAGData.nodes 12 ⟨1021531, by decide⟩ =
    .split (coordinate 9) (![⟨1021059, by decide⟩,⟨1021245, by decide⟩,⟨1021375, by decide⟩,⟨1021530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4698_1021531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4698 ⟨1021531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4698
    ⟨1021531, by decide⟩ (by decide) (![⟨1021059, by decide⟩,⟨1021245, by decide⟩,⟨1021375, by decide⟩,⟨1021530, by decide⟩]) unmarked_context_9_4698_1021531 node_context_9_4698_1021531
  intro a
  fin_cases a
  · exact context_10_18792_1021059
  · exact context_10_18793_1021245
  · exact context_10_18794_1021375
  · exact context_10_18795_1021530

theorem selected_cut_38020 : selected 10 ⟨1021573, by decide⟩
    (prefixPartial 11 75184) = some ⟨11, 2, 0, 1021573, 75184, 2845, 262144⟩ := by
  decide +kernel

theorem context_11_75184_1021573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75184 ⟨1021573, by decide⟩ :=
  accepted_of_selected 11 75184 ⟨1021573, by decide⟩ ⟨11, 2, 0, 1021573, 75184, 2845, 262144⟩
    (by decide) selected_cut_38020

theorem selected_cut_38021 : selected 10 ⟨1021618, by decide⟩
    (prefixPartial 11 75185) = some ⟨11, 2, 0, 1021618, 75185, 2541, 262144⟩ := by
  decide +kernel

theorem context_11_75185_1021618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75185 ⟨1021618, by decide⟩ :=
  accepted_of_selected 11 75185 ⟨1021618, by decide⟩ ⟨11, 2, 0, 1021618, 75185, 2541, 262144⟩
    (by decide) selected_cut_38021

theorem selected_cut_38022 : selected 10 ⟨1021651, by decide⟩
    (prefixPartial 11 75186) = some ⟨11, 2, 0, 1021651, 75186, 1701, 262144⟩ := by
  decide +kernel

theorem context_11_75186_1021651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75186 ⟨1021651, by decide⟩ :=
  accepted_of_selected 11 75186 ⟨1021651, by decide⟩ ⟨11, 2, 0, 1021651, 75186, 1701, 262144⟩
    (by decide) selected_cut_38022

theorem selected_cut_38023 : selected 10 ⟨1021696, by decide⟩
    (prefixPartial 11 75187) = some ⟨11, 2, 0, 1021696, 75187, 1785, 262144⟩ := by
  decide +kernel

theorem context_11_75187_1021696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75187 ⟨1021696, by decide⟩ :=
  accepted_of_selected 11 75187 ⟨1021696, by decide⟩ ⟨11, 2, 0, 1021696, 75187, 1785, 262144⟩
    (by decide) selected_cut_38023

theorem unmarked_context_10_18796_1021697 : frontier 11 ⟨1021697, by decide⟩
    (prefixCache 10 18796) (prefixPartial 10 18796) = false := by
  decide +kernel

theorem node_context_10_18796_1021697 : EJMOriginalGlobalDAGData.nodes 11 ⟨1021697, by decide⟩ =
    .split (coordinate 10) (![⟨1021573, by decide⟩,⟨1021618, by decide⟩,⟨1021651, by decide⟩,⟨1021696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18796_1021697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18796 ⟨1021697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18796
    ⟨1021697, by decide⟩ (by decide) (![⟨1021573, by decide⟩,⟨1021618, by decide⟩,⟨1021651, by decide⟩,⟨1021696, by decide⟩]) unmarked_context_10_18796_1021697 node_context_10_18796_1021697
  intro a
  fin_cases a
  · exact context_11_75184_1021573
  · exact context_11_75185_1021618
  · exact context_11_75186_1021651
  · exact context_11_75187_1021696

theorem selected_cut_38024 : selected 11 ⟨1021756, by decide⟩
    (prefixPartial 10 18797) = some ⟨10, 2, 0, 1021756, 18797, 3497, 1048576⟩ := by
  decide +kernel

theorem context_10_18797_1021756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18797 ⟨1021756, by decide⟩ :=
  accepted_of_selected 10 18797 ⟨1021756, by decide⟩ ⟨10, 2, 0, 1021756, 18797, 3497, 1048576⟩
    (by decide) selected_cut_38024

theorem selected_cut_38025 : selected 11 ⟨1021815, by decide⟩
    (prefixPartial 10 18798) = some ⟨10, 2, 0, 1021815, 18798, 2717, 1048576⟩ := by
  decide +kernel

theorem context_10_18798_1021815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18798 ⟨1021815, by decide⟩ :=
  accepted_of_selected 10 18798 ⟨1021815, by decide⟩ ⟨10, 2, 0, 1021815, 18798, 2717, 1048576⟩
    (by decide) selected_cut_38025

theorem selected_cut_38026 : selected 11 ⟨1021846, by decide⟩
    (prefixPartial 10 18799) = some ⟨10, 2, 0, 1021846, 18799, 577, 1048576⟩ := by
  decide +kernel

theorem context_10_18799_1021846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18799 ⟨1021846, by decide⟩ :=
  accepted_of_selected 10 18799 ⟨1021846, by decide⟩ ⟨10, 2, 0, 1021846, 18799, 577, 1048576⟩
    (by decide) selected_cut_38026

theorem unmarked_context_9_4699_1021847 : frontier 12 ⟨1021847, by decide⟩
    (prefixCache 9 4699) (prefixPartial 9 4699) = false := by
  decide +kernel

theorem node_context_9_4699_1021847 : EJMOriginalGlobalDAGData.nodes 12 ⟨1021847, by decide⟩ =
    .split (coordinate 9) (![⟨1021697, by decide⟩,⟨1021756, by decide⟩,⟨1021815, by decide⟩,⟨1021846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4699_1021847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4699 ⟨1021847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4699
    ⟨1021847, by decide⟩ (by decide) (![⟨1021697, by decide⟩,⟨1021756, by decide⟩,⟨1021815, by decide⟩,⟨1021846, by decide⟩]) unmarked_context_9_4699_1021847 node_context_9_4699_1021847
  intro a
  fin_cases a
  · exact context_10_18796_1021697
  · exact context_10_18797_1021756
  · exact context_10_18798_1021815
  · exact context_10_18799_1021846

theorem unmarked_context_8_1174_1021848 : frontier 13 ⟨1021848, by decide⟩
    (prefixCache 8 1174) (prefixPartial 8 1174) = false := by
  decide +kernel

theorem node_context_8_1174_1021848 : EJMOriginalGlobalDAGData.nodes 13 ⟨1021848, by decide⟩ =
    .split (coordinate 8) (![⟨1018665, by decide⟩,⟨1020680, by decide⟩,⟨1021531, by decide⟩,⟨1021847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1174_1021848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1174 ⟨1021848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1174
    ⟨1021848, by decide⟩ (by decide) (![⟨1018665, by decide⟩,⟨1020680, by decide⟩,⟨1021531, by decide⟩,⟨1021847, by decide⟩]) unmarked_context_8_1174_1021848 node_context_8_1174_1021848
  intro a
  fin_cases a
  · exact context_9_4696_1018665
  · exact context_9_4697_1020680
  · exact context_9_4698_1021531
  · exact context_9_4699_1021847

theorem selected_cut_38027 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 75200) = some ⟨11, 1, 0, 167448, 75200, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75200_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75200 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 75200 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 75200, 1, 262144⟩
    (by decide) selected_cut_38027

theorem selected_cut_38028 : selected 8 ⟨1021873, by decide⟩
    (prefixPartial 13 1203216) = some ⟨13, 2, 0, 1021873, 1203216, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_1203216_1021873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203216 ⟨1021873, by decide⟩ :=
  accepted_of_selected 13 1203216 ⟨1021873, by decide⟩ ⟨13, 2, 0, 1021873, 1203216, 1333, 16384⟩
    (by decide) selected_cut_38028

theorem selected_cut_38029 : selected 8 ⟨1021897, by decide⟩
    (prefixPartial 13 1203217) = some ⟨13, 2, 0, 1021897, 1203217, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_1203217_1021897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203217 ⟨1021897, by decide⟩ :=
  accepted_of_selected 13 1203217 ⟨1021897, by decide⟩ ⟨13, 2, 0, 1021897, 1203217, 1289, 16384⟩
    (by decide) selected_cut_38029

theorem selected_cut_38030 : selected 8 ⟨1021936, by decide⟩
    (prefixPartial 13 1203218) = some ⟨13, 2, 0, 1021936, 1203218, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_1203218_1021936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203218 ⟨1021936, by decide⟩ :=
  accepted_of_selected 13 1203218 ⟨1021936, by decide⟩ ⟨13, 2, 0, 1021936, 1203218, 1105, 16384⟩
    (by decide) selected_cut_38030

theorem selected_cut_38031 : selected 8 ⟨1021944, by decide⟩
    (prefixPartial 13 1203219) = some ⟨13, 2, 0, 1021944, 1203219, 537, 16384⟩ := by
  decide +kernel

theorem context_13_1203219_1021944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203219 ⟨1021944, by decide⟩ :=
  accepted_of_selected 13 1203219 ⟨1021944, by decide⟩ ⟨13, 2, 0, 1021944, 1203219, 537, 16384⟩
    (by decide) selected_cut_38031

theorem unmarked_context_12_300804_1021945 : frontier 9 ⟨1021945, by decide⟩
    (prefixCache 12 300804) (prefixPartial 12 300804) = false := by
  decide +kernel

theorem node_context_12_300804_1021945 : EJMOriginalGlobalDAGData.nodes 9 ⟨1021945, by decide⟩ =
    .split (coordinate 12) (![⟨1021873, by decide⟩,⟨1021897, by decide⟩,⟨1021936, by decide⟩,⟨1021944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300804_1021945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300804 ⟨1021945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300804
    ⟨1021945, by decide⟩ (by decide) (![⟨1021873, by decide⟩,⟨1021897, by decide⟩,⟨1021936, by decide⟩,⟨1021944, by decide⟩]) unmarked_context_12_300804_1021945 node_context_12_300804_1021945
  intro a
  fin_cases a
  · exact context_13_1203216_1021873
  · exact context_13_1203217_1021897
  · exact context_13_1203218_1021936
  · exact context_13_1203219_1021944

theorem selected_cut_38032 : selected 9 ⟨1022017, by decide⟩
    (prefixPartial 12 300805) = some ⟨12, 2, 0, 1022017, 300805, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_300805_1022017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300805 ⟨1022017, by decide⟩ :=
  accepted_of_selected 12 300805 ⟨1022017, by decide⟩ ⟨12, 2, 0, 1022017, 300805, 3693, 65536⟩
    (by decide) selected_cut_38032

theorem selected_cut_38033 : selected 9 ⟨1022081, by decide⟩
    (prefixPartial 12 300806) = some ⟨12, 2, 0, 1022081, 300806, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_300806_1022081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300806 ⟨1022081, by decide⟩ :=
  accepted_of_selected 12 300806 ⟨1022081, by decide⟩ ⟨12, 2, 0, 1022081, 300806, 3805, 65536⟩
    (by decide) selected_cut_38033

theorem selected_cut_38034 : selected 9 ⟨1022135, by decide⟩
    (prefixPartial 12 300807) = some ⟨12, 2, 0, 1022135, 300807, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_300807_1022135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300807 ⟨1022135, by decide⟩ :=
  accepted_of_selected 12 300807 ⟨1022135, by decide⟩ ⟨12, 2, 0, 1022135, 300807, 3657, 65536⟩
    (by decide) selected_cut_38034

theorem unmarked_context_11_75201_1022136 : frontier 10 ⟨1022136, by decide⟩
    (prefixCache 11 75201) (prefixPartial 11 75201) = false := by
  decide +kernel

theorem node_context_11_75201_1022136 : EJMOriginalGlobalDAGData.nodes 10 ⟨1022136, by decide⟩ =
    .split (coordinate 11) (![⟨1021945, by decide⟩,⟨1022017, by decide⟩,⟨1022081, by decide⟩,⟨1022135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75201_1022136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75201 ⟨1022136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75201
    ⟨1022136, by decide⟩ (by decide) (![⟨1021945, by decide⟩,⟨1022017, by decide⟩,⟨1022081, by decide⟩,⟨1022135, by decide⟩]) unmarked_context_11_75201_1022136 node_context_11_75201_1022136
  intro a
  fin_cases a
  · exact context_12_300804_1021945
  · exact context_12_300805_1022017
  · exact context_12_300806_1022081
  · exact context_12_300807_1022135

theorem selected_cut_38035 : selected 8 ⟨1022159, by decide⟩
    (prefixPartial 13 1203232) = some ⟨13, 2, 0, 1022159, 1203232, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_1203232_1022159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203232 ⟨1022159, by decide⟩ :=
  accepted_of_selected 13 1203232 ⟨1022159, by decide⟩ ⟨13, 2, 0, 1022159, 1203232, 1297, 16384⟩
    (by decide) selected_cut_38035

theorem selected_cut_38036 : selected 8 ⟨1022190, by decide⟩
    (prefixPartial 13 1203233) = some ⟨13, 2, 0, 1022190, 1203233, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_1203233_1022190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203233 ⟨1022190, by decide⟩ :=
  accepted_of_selected 13 1203233 ⟨1022190, by decide⟩ ⟨13, 2, 0, 1022190, 1203233, 1529, 16384⟩
    (by decide) selected_cut_38036

theorem selected_cut_38037 : selected 8 ⟨1022227, by decide⟩
    (prefixPartial 13 1203234) = some ⟨13, 2, 0, 1022227, 1203234, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_1203234_1022227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203234 ⟨1022227, by decide⟩ :=
  accepted_of_selected 13 1203234 ⟨1022227, by decide⟩ ⟨13, 2, 0, 1022227, 1203234, 1121, 16384⟩
    (by decide) selected_cut_38037

theorem selected_cut_38038 : selected 8 ⟨1022234, by decide⟩
    (prefixPartial 13 1203235) = some ⟨13, 2, 0, 1022234, 1203235, 577, 16384⟩ := by
  decide +kernel

theorem context_13_1203235_1022234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203235 ⟨1022234, by decide⟩ :=
  accepted_of_selected 13 1203235 ⟨1022234, by decide⟩ ⟨13, 2, 0, 1022234, 1203235, 577, 16384⟩
    (by decide) selected_cut_38038

theorem unmarked_context_12_300808_1022235 : frontier 9 ⟨1022235, by decide⟩
    (prefixCache 12 300808) (prefixPartial 12 300808) = false := by
  decide +kernel

theorem node_context_12_300808_1022235 : EJMOriginalGlobalDAGData.nodes 9 ⟨1022235, by decide⟩ =
    .split (coordinate 12) (![⟨1022159, by decide⟩,⟨1022190, by decide⟩,⟨1022227, by decide⟩,⟨1022234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300808_1022235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300808 ⟨1022235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300808
    ⟨1022235, by decide⟩ (by decide) (![⟨1022159, by decide⟩,⟨1022190, by decide⟩,⟨1022227, by decide⟩,⟨1022234, by decide⟩]) unmarked_context_12_300808_1022235 node_context_12_300808_1022235
  intro a
  fin_cases a
  · exact context_13_1203232_1022159
  · exact context_13_1203233_1022190
  · exact context_13_1203234_1022227
  · exact context_13_1203235_1022234

theorem selected_cut_38039 : selected 8 ⟨1022259, by decide⟩
    (prefixPartial 13 1203236) = some ⟨13, 2, 0, 1022259, 1203236, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_1203236_1022259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203236 ⟨1022259, by decide⟩ :=
  accepted_of_selected 13 1203236 ⟨1022259, by decide⟩ ⟨13, 2, 0, 1022259, 1203236, 1377, 16384⟩
    (by decide) selected_cut_38039

theorem selected_cut_38040 : selected 8 ⟨1022283, by decide⟩
    (prefixPartial 13 1203237) = some ⟨13, 2, 0, 1022283, 1203237, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_1203237_1022283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203237 ⟨1022283, by decide⟩ :=
  accepted_of_selected 13 1203237 ⟨1022283, by decide⟩ ⟨13, 2, 0, 1022283, 1203237, 1457, 16384⟩
    (by decide) selected_cut_38040

theorem selected_cut_38041 : selected 8 ⟨1022311, by decide⟩
    (prefixPartial 13 1203238) = some ⟨13, 2, 0, 1022311, 1203238, 909, 16384⟩ := by
  decide +kernel

theorem context_13_1203238_1022311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203238 ⟨1022311, by decide⟩ :=
  accepted_of_selected 13 1203238 ⟨1022311, by decide⟩ ⟨13, 2, 0, 1022311, 1203238, 909, 16384⟩
    (by decide) selected_cut_38041

theorem selected_cut_38042 : selected 8 ⟨1022317, by decide⟩
    (prefixPartial 13 1203239) = some ⟨13, 2, 0, 1022317, 1203239, 493, 16384⟩ := by
  decide +kernel

theorem context_13_1203239_1022317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203239 ⟨1022317, by decide⟩ :=
  accepted_of_selected 13 1203239 ⟨1022317, by decide⟩ ⟨13, 2, 0, 1022317, 1203239, 493, 16384⟩
    (by decide) selected_cut_38042

theorem unmarked_context_12_300809_1022318 : frontier 9 ⟨1022318, by decide⟩
    (prefixCache 12 300809) (prefixPartial 12 300809) = false := by
  decide +kernel

theorem node_context_12_300809_1022318 : EJMOriginalGlobalDAGData.nodes 9 ⟨1022318, by decide⟩ =
    .split (coordinate 12) (![⟨1022259, by decide⟩,⟨1022283, by decide⟩,⟨1022311, by decide⟩,⟨1022317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300809_1022318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300809 ⟨1022318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300809
    ⟨1022318, by decide⟩ (by decide) (![⟨1022259, by decide⟩,⟨1022283, by decide⟩,⟨1022311, by decide⟩,⟨1022317, by decide⟩]) unmarked_context_12_300809_1022318 node_context_12_300809_1022318
  intro a
  fin_cases a
  · exact context_13_1203236_1022259
  · exact context_13_1203237_1022283
  · exact context_13_1203238_1022311
  · exact context_13_1203239_1022317

theorem selected_cut_38043 : selected 8 ⟨1022339, by decide⟩
    (prefixPartial 13 1203240) = some ⟨13, 2, 0, 1022339, 1203240, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_1203240_1022339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203240 ⟨1022339, by decide⟩ :=
  accepted_of_selected 13 1203240 ⟨1022339, by decide⟩ ⟨13, 2, 0, 1022339, 1203240, 1333, 16384⟩
    (by decide) selected_cut_38043

theorem selected_cut_38044 : selected 8 ⟨1022361, by decide⟩
    (prefixPartial 13 1203241) = some ⟨13, 2, 0, 1022361, 1203241, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_1203241_1022361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203241 ⟨1022361, by decide⟩ :=
  accepted_of_selected 13 1203241 ⟨1022361, by decide⟩ ⟨13, 2, 0, 1022361, 1203241, 1489, 16384⟩
    (by decide) selected_cut_38044

theorem selected_cut_38045 : selected 8 ⟨1022379, by decide⟩
    (prefixPartial 13 1203242) = some ⟨13, 2, 0, 1022379, 1203242, 897, 16384⟩ := by
  decide +kernel

theorem context_13_1203242_1022379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203242 ⟨1022379, by decide⟩ :=
  accepted_of_selected 13 1203242 ⟨1022379, by decide⟩ ⟨13, 2, 0, 1022379, 1203242, 897, 16384⟩
    (by decide) selected_cut_38045

theorem selected_cut_38046 : selected 8 ⟨1022387, by decide⟩
    (prefixPartial 13 1203243) = some ⟨13, 2, 0, 1022387, 1203243, 517, 16384⟩ := by
  decide +kernel

theorem context_13_1203243_1022387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203243 ⟨1022387, by decide⟩ :=
  accepted_of_selected 13 1203243 ⟨1022387, by decide⟩ ⟨13, 2, 0, 1022387, 1203243, 517, 16384⟩
    (by decide) selected_cut_38046

theorem unmarked_context_12_300810_1022388 : frontier 9 ⟨1022388, by decide⟩
    (prefixCache 12 300810) (prefixPartial 12 300810) = false := by
  decide +kernel

theorem node_context_12_300810_1022388 : EJMOriginalGlobalDAGData.nodes 9 ⟨1022388, by decide⟩ =
    .split (coordinate 12) (![⟨1022339, by decide⟩,⟨1022361, by decide⟩,⟨1022379, by decide⟩,⟨1022387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300810_1022388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300810 ⟨1022388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300810
    ⟨1022388, by decide⟩ (by decide) (![⟨1022339, by decide⟩,⟨1022361, by decide⟩,⟨1022379, by decide⟩,⟨1022387, by decide⟩]) unmarked_context_12_300810_1022388 node_context_12_300810_1022388
  intro a
  fin_cases a
  · exact context_13_1203240_1022339
  · exact context_13_1203241_1022361
  · exact context_13_1203242_1022379
  · exact context_13_1203243_1022387

theorem selected_cut_38047 : selected 8 ⟨1022406, by decide⟩
    (prefixPartial 13 1203244) = some ⟨13, 2, 0, 1022406, 1203244, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_1203244_1022406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203244 ⟨1022406, by decide⟩ :=
  accepted_of_selected 13 1203244 ⟨1022406, by decide⟩ ⟨13, 2, 0, 1022406, 1203244, 1353, 16384⟩
    (by decide) selected_cut_38047

theorem selected_cut_38048 : selected 8 ⟨1022429, by decide⟩
    (prefixPartial 13 1203245) = some ⟨13, 2, 0, 1022429, 1203245, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_1203245_1022429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203245 ⟨1022429, by decide⟩ :=
  accepted_of_selected 13 1203245 ⟨1022429, by decide⟩ ⟨13, 2, 0, 1022429, 1203245, 1485, 16384⟩
    (by decide) selected_cut_38048

theorem selected_cut_38049 : selected 8 ⟨1022453, by decide⟩
    (prefixPartial 13 1203246) = some ⟨13, 2, 0, 1022453, 1203246, 969, 16384⟩ := by
  decide +kernel

theorem context_13_1203246_1022453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203246 ⟨1022453, by decide⟩ :=
  accepted_of_selected 13 1203246 ⟨1022453, by decide⟩ ⟨13, 2, 0, 1022453, 1203246, 969, 16384⟩
    (by decide) selected_cut_38049

theorem selected_cut_38050 : selected 8 ⟨1022458, by decide⟩
    (prefixPartial 13 1203247) = some ⟨13, 2, 0, 1022458, 1203247, 541, 16384⟩ := by
  decide +kernel

theorem context_13_1203247_1022458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203247 ⟨1022458, by decide⟩ :=
  accepted_of_selected 13 1203247 ⟨1022458, by decide⟩ ⟨13, 2, 0, 1022458, 1203247, 541, 16384⟩
    (by decide) selected_cut_38050

theorem unmarked_context_12_300811_1022459 : frontier 9 ⟨1022459, by decide⟩
    (prefixCache 12 300811) (prefixPartial 12 300811) = false := by
  decide +kernel

theorem node_context_12_300811_1022459 : EJMOriginalGlobalDAGData.nodes 9 ⟨1022459, by decide⟩ =
    .split (coordinate 12) (![⟨1022406, by decide⟩,⟨1022429, by decide⟩,⟨1022453, by decide⟩,⟨1022458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300811_1022459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300811 ⟨1022459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300811
    ⟨1022459, by decide⟩ (by decide) (![⟨1022406, by decide⟩,⟨1022429, by decide⟩,⟨1022453, by decide⟩,⟨1022458, by decide⟩]) unmarked_context_12_300811_1022459 node_context_12_300811_1022459
  intro a
  fin_cases a
  · exact context_13_1203244_1022406
  · exact context_13_1203245_1022429
  · exact context_13_1203246_1022453
  · exact context_13_1203247_1022458

theorem unmarked_context_11_75202_1022460 : frontier 10 ⟨1022460, by decide⟩
    (prefixCache 11 75202) (prefixPartial 11 75202) = false := by
  decide +kernel

theorem node_context_11_75202_1022460 : EJMOriginalGlobalDAGData.nodes 10 ⟨1022460, by decide⟩ =
    .split (coordinate 11) (![⟨1022235, by decide⟩,⟨1022318, by decide⟩,⟨1022388, by decide⟩,⟨1022459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75202_1022460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75202 ⟨1022460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75202
    ⟨1022460, by decide⟩ (by decide) (![⟨1022235, by decide⟩,⟨1022318, by decide⟩,⟨1022388, by decide⟩,⟨1022459, by decide⟩]) unmarked_context_11_75202_1022460 node_context_11_75202_1022460
  intro a
  fin_cases a
  · exact context_12_300808_1022235
  · exact context_12_300809_1022318
  · exact context_12_300810_1022388
  · exact context_12_300811_1022459

theorem selected_cut_38051 : selected 8 ⟨1022478, by decide⟩
    (prefixPartial 13 1203248) = some ⟨13, 2, 0, 1022478, 1203248, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_1203248_1022478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203248 ⟨1022478, by decide⟩ :=
  accepted_of_selected 13 1203248 ⟨1022478, by decide⟩ ⟨13, 2, 0, 1022478, 1203248, 1249, 16384⟩
    (by decide) selected_cut_38051

theorem selected_cut_38052 : selected 8 ⟨1022495, by decide⟩
    (prefixPartial 13 1203249) = some ⟨13, 2, 0, 1022495, 1203249, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_1203249_1022495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203249 ⟨1022495, by decide⟩ :=
  accepted_of_selected 13 1203249 ⟨1022495, by decide⟩ ⟨13, 2, 0, 1022495, 1203249, 1385, 16384⟩
    (by decide) selected_cut_38052

theorem selected_cut_38053 : selected 8 ⟨1022513, by decide⟩
    (prefixPartial 13 1203250) = some ⟨13, 2, 0, 1022513, 1203250, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_1203250_1022513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203250 ⟨1022513, by decide⟩ :=
  accepted_of_selected 13 1203250 ⟨1022513, by decide⟩ ⟨13, 2, 0, 1022513, 1203250, 1001, 16384⟩
    (by decide) selected_cut_38053

theorem selected_cut_38054 : selected 8 ⟨1022521, by decide⟩
    (prefixPartial 13 1203251) = some ⟨13, 2, 0, 1022521, 1203251, 669, 16384⟩ := by
  decide +kernel

theorem context_13_1203251_1022521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203251 ⟨1022521, by decide⟩ :=
  accepted_of_selected 13 1203251 ⟨1022521, by decide⟩ ⟨13, 2, 0, 1022521, 1203251, 669, 16384⟩
    (by decide) selected_cut_38054

theorem unmarked_context_12_300812_1022522 : frontier 9 ⟨1022522, by decide⟩
    (prefixCache 12 300812) (prefixPartial 12 300812) = false := by
  decide +kernel

theorem node_context_12_300812_1022522 : EJMOriginalGlobalDAGData.nodes 9 ⟨1022522, by decide⟩ =
    .split (coordinate 12) (![⟨1022478, by decide⟩,⟨1022495, by decide⟩,⟨1022513, by decide⟩,⟨1022521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300812_1022522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300812 ⟨1022522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300812
    ⟨1022522, by decide⟩ (by decide) (![⟨1022478, by decide⟩,⟨1022495, by decide⟩,⟨1022513, by decide⟩,⟨1022521, by decide⟩]) unmarked_context_12_300812_1022522 node_context_12_300812_1022522
  intro a
  fin_cases a
  · exact context_13_1203248_1022478
  · exact context_13_1203249_1022495
  · exact context_13_1203250_1022513
  · exact context_13_1203251_1022521

theorem selected_cut_38055 : selected 8 ⟨1022544, by decide⟩
    (prefixPartial 13 1203252) = some ⟨13, 2, 0, 1022544, 1203252, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_1203252_1022544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203252 ⟨1022544, by decide⟩ :=
  accepted_of_selected 13 1203252 ⟨1022544, by decide⟩ ⟨13, 2, 0, 1022544, 1203252, 1373, 16384⟩
    (by decide) selected_cut_38055

theorem selected_cut_38056 : selected 8 ⟨1022571, by decide⟩
    (prefixPartial 13 1203253) = some ⟨13, 2, 0, 1022571, 1203253, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_1203253_1022571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203253 ⟨1022571, by decide⟩ :=
  accepted_of_selected 13 1203253 ⟨1022571, by decide⟩ ⟨13, 2, 0, 1022571, 1203253, 1445, 16384⟩
    (by decide) selected_cut_38056

theorem selected_cut_38057 : selected 8 ⟨1022589, by decide⟩
    (prefixPartial 13 1203254) = some ⟨13, 2, 0, 1022589, 1203254, 853, 16384⟩ := by
  decide +kernel

theorem context_13_1203254_1022589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203254 ⟨1022589, by decide⟩ :=
  accepted_of_selected 13 1203254 ⟨1022589, by decide⟩ ⟨13, 2, 0, 1022589, 1203254, 853, 16384⟩
    (by decide) selected_cut_38057

theorem selected_cut_38058 : selected 8 ⟨1022595, by decide⟩
    (prefixPartial 13 1203255) = some ⟨13, 2, 0, 1022595, 1203255, 517, 16384⟩ := by
  decide +kernel

theorem context_13_1203255_1022595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203255 ⟨1022595, by decide⟩ :=
  accepted_of_selected 13 1203255 ⟨1022595, by decide⟩ ⟨13, 2, 0, 1022595, 1203255, 517, 16384⟩
    (by decide) selected_cut_38058

theorem unmarked_context_12_300813_1022596 : frontier 9 ⟨1022596, by decide⟩
    (prefixCache 12 300813) (prefixPartial 12 300813) = false := by
  decide +kernel

theorem node_context_12_300813_1022596 : EJMOriginalGlobalDAGData.nodes 9 ⟨1022596, by decide⟩ =
    .split (coordinate 12) (![⟨1022544, by decide⟩,⟨1022571, by decide⟩,⟨1022589, by decide⟩,⟨1022595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300813_1022596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300813 ⟨1022596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300813
    ⟨1022596, by decide⟩ (by decide) (![⟨1022544, by decide⟩,⟨1022571, by decide⟩,⟨1022589, by decide⟩,⟨1022595, by decide⟩]) unmarked_context_12_300813_1022596 node_context_12_300813_1022596
  intro a
  fin_cases a
  · exact context_13_1203252_1022544
  · exact context_13_1203253_1022571
  · exact context_13_1203254_1022589
  · exact context_13_1203255_1022595

theorem selected_cut_38059 : selected 8 ⟨1022616, by decide⟩
    (prefixPartial 13 1203256) = some ⟨13, 2, 0, 1022616, 1203256, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_1203256_1022616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203256 ⟨1022616, by decide⟩ :=
  accepted_of_selected 13 1203256 ⟨1022616, by decide⟩ ⟨13, 2, 0, 1022616, 1203256, 1385, 16384⟩
    (by decide) selected_cut_38059

theorem selected_cut_38060 : selected 8 ⟨1022641, by decide⟩
    (prefixPartial 13 1203257) = some ⟨13, 2, 0, 1022641, 1203257, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_1203257_1022641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203257 ⟨1022641, by decide⟩ :=
  accepted_of_selected 13 1203257 ⟨1022641, by decide⟩ ⟨13, 2, 0, 1022641, 1203257, 1477, 16384⟩
    (by decide) selected_cut_38060

theorem selected_cut_38061 : selected 8 ⟨1022659, by decide⟩
    (prefixPartial 13 1203258) = some ⟨13, 2, 0, 1022659, 1203258, 873, 16384⟩ := by
  decide +kernel

theorem context_13_1203258_1022659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203258 ⟨1022659, by decide⟩ :=
  accepted_of_selected 13 1203258 ⟨1022659, by decide⟩ ⟨13, 2, 0, 1022659, 1203258, 873, 16384⟩
    (by decide) selected_cut_38061

theorem selected_cut_38062 : selected 8 ⟨1022666, by decide⟩
    (prefixPartial 13 1203259) = some ⟨13, 2, 0, 1022666, 1203259, 565, 16384⟩ := by
  decide +kernel

theorem context_13_1203259_1022666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1203259 ⟨1022666, by decide⟩ :=
  accepted_of_selected 13 1203259 ⟨1022666, by decide⟩ ⟨13, 2, 0, 1022666, 1203259, 565, 16384⟩
    (by decide) selected_cut_38062

theorem unmarked_context_12_300814_1022667 : frontier 9 ⟨1022667, by decide⟩
    (prefixCache 12 300814) (prefixPartial 12 300814) = false := by
  decide +kernel

theorem node_context_12_300814_1022667 : EJMOriginalGlobalDAGData.nodes 9 ⟨1022667, by decide⟩ =
    .split (coordinate 12) (![⟨1022616, by decide⟩,⟨1022641, by decide⟩,⟨1022659, by decide⟩,⟨1022666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300814_1022667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300814 ⟨1022667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300814
    ⟨1022667, by decide⟩ (by decide) (![⟨1022616, by decide⟩,⟨1022641, by decide⟩,⟨1022659, by decide⟩,⟨1022666, by decide⟩]) unmarked_context_12_300814_1022667 node_context_12_300814_1022667
  intro a
  fin_cases a
  · exact context_13_1203256_1022616
  · exact context_13_1203257_1022641
  · exact context_13_1203258_1022659
  · exact context_13_1203259_1022666

theorem selected_cut_38063 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 300815) = some ⟨12, 1, 0, 903806, 300815, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300815_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300815 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 300815 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 300815, 1, 65536⟩
    (by decide) selected_cut_38063

theorem unmarked_context_11_75203_1022668 : frontier 10 ⟨1022668, by decide⟩
    (prefixCache 11 75203) (prefixPartial 11 75203) = false := by
  decide +kernel

theorem node_context_11_75203_1022668 : EJMOriginalGlobalDAGData.nodes 10 ⟨1022668, by decide⟩ =
    .split (coordinate 11) (![⟨1022522, by decide⟩,⟨1022596, by decide⟩,⟨1022667, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75203_1022668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75203 ⟨1022668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75203
    ⟨1022668, by decide⟩ (by decide) (![⟨1022522, by decide⟩,⟨1022596, by decide⟩,⟨1022667, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75203_1022668 node_context_11_75203_1022668
  intro a
  fin_cases a
  · exact context_12_300812_1022522
  · exact context_12_300813_1022596
  · exact context_12_300814_1022667
  · exact context_12_300815_903806

theorem unmarked_context_10_18800_1022669 : frontier 11 ⟨1022669, by decide⟩
    (prefixCache 10 18800) (prefixPartial 10 18800) = false := by
  decide +kernel

theorem node_context_10_18800_1022669 : EJMOriginalGlobalDAGData.nodes 11 ⟨1022669, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨1022136, by decide⟩,⟨1022460, by decide⟩,⟨1022668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18800_1022669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18800 ⟨1022669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18800
    ⟨1022669, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨1022136, by decide⟩,⟨1022460, by decide⟩,⟨1022668, by decide⟩]) unmarked_context_10_18800_1022669 node_context_10_18800_1022669
  intro a
  fin_cases a
  · exact context_11_75200_167448
  · exact context_11_75201_1022136
  · exact context_11_75202_1022460
  · exact context_11_75203_1022668

theorem selected_cut_38064 : selected 9 ⟨1022724, by decide⟩
    (prefixPartial 12 300816) = some ⟨12, 2, 0, 1022724, 300816, 3225, 65536⟩ := by
  decide +kernel

theorem context_12_300816_1022724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300816 ⟨1022724, by decide⟩ :=
  accepted_of_selected 12 300816 ⟨1022724, by decide⟩ ⟨12, 2, 0, 1022724, 300816, 3225, 65536⟩
    (by decide) selected_cut_38064

theorem selected_cut_38065 : selected 9 ⟨1022765, by decide⟩
    (prefixPartial 12 300817) = some ⟨12, 2, 0, 1022765, 300817, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_300817_1022765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300817 ⟨1022765, by decide⟩ :=
  accepted_of_selected 12 300817 ⟨1022765, by decide⟩ ⟨12, 2, 0, 1022765, 300817, 2861, 65536⟩
    (by decide) selected_cut_38065

theorem selected_cut_38066 : selected 9 ⟨1022813, by decide⟩
    (prefixPartial 12 300818) = some ⟨12, 2, 0, 1022813, 300818, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_300818_1022813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300818 ⟨1022813, by decide⟩ :=
  accepted_of_selected 12 300818 ⟨1022813, by decide⟩ ⟨12, 2, 0, 1022813, 300818, 3077, 65536⟩
    (by decide) selected_cut_38066

theorem selected_cut_38067 : selected 9 ⟨1022859, by decide⟩
    (prefixPartial 12 300819) = some ⟨12, 2, 0, 1022859, 300819, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_300819_1022859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300819 ⟨1022859, by decide⟩ :=
  accepted_of_selected 12 300819 ⟨1022859, by decide⟩ ⟨12, 2, 0, 1022859, 300819, 2957, 65536⟩
    (by decide) selected_cut_38067

theorem unmarked_context_11_75204_1022860 : frontier 10 ⟨1022860, by decide⟩
    (prefixCache 11 75204) (prefixPartial 11 75204) = false := by
  decide +kernel

theorem node_context_11_75204_1022860 : EJMOriginalGlobalDAGData.nodes 10 ⟨1022860, by decide⟩ =
    .split (coordinate 11) (![⟨1022724, by decide⟩,⟨1022765, by decide⟩,⟨1022813, by decide⟩,⟨1022859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75204_1022860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75204 ⟨1022860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75204
    ⟨1022860, by decide⟩ (by decide) (![⟨1022724, by decide⟩,⟨1022765, by decide⟩,⟨1022813, by decide⟩,⟨1022859, by decide⟩]) unmarked_context_11_75204_1022860 node_context_11_75204_1022860
  intro a
  fin_cases a
  · exact context_12_300816_1022724
  · exact context_12_300817_1022765
  · exact context_12_300818_1022813
  · exact context_12_300819_1022859

theorem selected_cut_38068 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 75205) = some ⟨11, 1, 0, 892405, 75205, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75205_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75205 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 75205 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 75205, 1, 262144⟩
    (by decide) selected_cut_38068

theorem selected_cut_38069 : selected 9 ⟨1022909, by decide⟩
    (prefixPartial 12 300824) = some ⟨12, 2, 0, 1022909, 300824, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_300824_1022909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300824 ⟨1022909, by decide⟩ :=
  accepted_of_selected 12 300824 ⟨1022909, by decide⟩ ⟨12, 2, 0, 1022909, 300824, 3573, 65536⟩
    (by decide) selected_cut_38069

theorem selected_cut_38070 : selected 9 ⟨1022959, by decide⟩
    (prefixPartial 12 300825) = some ⟨12, 2, 0, 1022959, 300825, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_300825_1022959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300825 ⟨1022959, by decide⟩ :=
  accepted_of_selected 12 300825 ⟨1022959, by decide⟩ ⟨12, 2, 0, 1022959, 300825, 3197, 65536⟩
    (by decide) selected_cut_38070

theorem selected_cut_38071 : selected 9 ⟨1023007, by decide⟩
    (prefixPartial 12 300826) = some ⟨12, 2, 0, 1023007, 300826, 3225, 65536⟩ := by
  decide +kernel

theorem context_12_300826_1023007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300826 ⟨1023007, by decide⟩ :=
  accepted_of_selected 12 300826 ⟨1023007, by decide⟩ ⟨12, 2, 0, 1023007, 300826, 3225, 65536⟩
    (by decide) selected_cut_38071

theorem selected_cut_38072 : selected 9 ⟨1023050, by decide⟩
    (prefixPartial 12 300827) = some ⟨12, 2, 0, 1023050, 300827, 3385, 65536⟩ := by
  decide +kernel

theorem context_12_300827_1023050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300827 ⟨1023050, by decide⟩ :=
  accepted_of_selected 12 300827 ⟨1023050, by decide⟩ ⟨12, 2, 0, 1023050, 300827, 3385, 65536⟩
    (by decide) selected_cut_38072

theorem unmarked_context_11_75206_1023051 : frontier 10 ⟨1023051, by decide⟩
    (prefixCache 11 75206) (prefixPartial 11 75206) = false := by
  decide +kernel

theorem node_context_11_75206_1023051 : EJMOriginalGlobalDAGData.nodes 10 ⟨1023051, by decide⟩ =
    .split (coordinate 11) (![⟨1022909, by decide⟩,⟨1022959, by decide⟩,⟨1023007, by decide⟩,⟨1023050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75206_1023051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75206 ⟨1023051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75206
    ⟨1023051, by decide⟩ (by decide) (![⟨1022909, by decide⟩,⟨1022959, by decide⟩,⟨1023007, by decide⟩,⟨1023050, by decide⟩]) unmarked_context_11_75206_1023051 node_context_11_75206_1023051
  intro a
  fin_cases a
  · exact context_12_300824_1022909
  · exact context_12_300825_1022959
  · exact context_12_300826_1023007
  · exact context_12_300827_1023050

theorem selected_cut_38073 : selected 9 ⟨1023110, by decide⟩
    (prefixPartial 12 300828) = some ⟨12, 2, 0, 1023110, 300828, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_300828_1023110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300828 ⟨1023110, by decide⟩ :=
  accepted_of_selected 12 300828 ⟨1023110, by decide⟩ ⟨12, 2, 0, 1023110, 300828, 3569, 65536⟩
    (by decide) selected_cut_38073

theorem selected_cut_38074 : selected 9 ⟨1023159, by decide⟩
    (prefixPartial 12 300829) = some ⟨12, 2, 0, 1023159, 300829, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_300829_1023159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300829 ⟨1023159, by decide⟩ :=
  accepted_of_selected 12 300829 ⟨1023159, by decide⟩ ⟨12, 2, 0, 1023159, 300829, 3117, 65536⟩
    (by decide) selected_cut_38074

theorem selected_cut_38075 : selected 9 ⟨1023212, by decide⟩
    (prefixPartial 12 300830) = some ⟨12, 2, 0, 1023212, 300830, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_300830_1023212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300830 ⟨1023212, by decide⟩ :=
  accepted_of_selected 12 300830 ⟨1023212, by decide⟩ ⟨12, 2, 0, 1023212, 300830, 3505, 65536⟩
    (by decide) selected_cut_38075

theorem selected_cut_38076 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 300831) = some ⟨12, 1, 0, 903806, 300831, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300831_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300831 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 300831 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 300831, 1, 65536⟩
    (by decide) selected_cut_38076

theorem unmarked_context_11_75207_1023213 : frontier 10 ⟨1023213, by decide⟩
    (prefixCache 11 75207) (prefixPartial 11 75207) = false := by
  decide +kernel

theorem node_context_11_75207_1023213 : EJMOriginalGlobalDAGData.nodes 10 ⟨1023213, by decide⟩ =
    .split (coordinate 11) (![⟨1023110, by decide⟩,⟨1023159, by decide⟩,⟨1023212, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75207_1023213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75207 ⟨1023213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75207
    ⟨1023213, by decide⟩ (by decide) (![⟨1023110, by decide⟩,⟨1023159, by decide⟩,⟨1023212, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75207_1023213 node_context_11_75207_1023213
  intro a
  fin_cases a
  · exact context_12_300828_1023110
  · exact context_12_300829_1023159
  · exact context_12_300830_1023212
  · exact context_12_300831_903806

theorem unmarked_context_10_18801_1023214 : frontier 11 ⟨1023214, by decide⟩
    (prefixCache 10 18801) (prefixPartial 10 18801) = false := by
  decide +kernel

theorem node_context_10_18801_1023214 : EJMOriginalGlobalDAGData.nodes 11 ⟨1023214, by decide⟩ =
    .split (coordinate 10) (![⟨1022860, by decide⟩,⟨892405, by decide⟩,⟨1023051, by decide⟩,⟨1023213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18801_1023214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18801 ⟨1023214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18801
    ⟨1023214, by decide⟩ (by decide) (![⟨1022860, by decide⟩,⟨892405, by decide⟩,⟨1023051, by decide⟩,⟨1023213, by decide⟩]) unmarked_context_10_18801_1023214 node_context_10_18801_1023214
  intro a
  fin_cases a
  · exact context_11_75204_1022860
  · exact context_11_75205_892405
  · exact context_11_75206_1023051
  · exact context_11_75207_1023213

theorem selected_cut_38077 : selected 9 ⟨1023274, by decide⟩
    (prefixPartial 12 300832) = some ⟨12, 2, 0, 1023274, 300832, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_300832_1023274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300832 ⟨1023274, by decide⟩ :=
  accepted_of_selected 12 300832 ⟨1023274, by decide⟩ ⟨12, 2, 0, 1023274, 300832, 3473, 65536⟩
    (by decide) selected_cut_38077

theorem selected_cut_38078 : selected 9 ⟨1023329, by decide⟩
    (prefixPartial 12 300833) = some ⟨12, 2, 0, 1023329, 300833, 3309, 65536⟩ := by
  decide +kernel

theorem context_12_300833_1023329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300833 ⟨1023329, by decide⟩ :=
  accepted_of_selected 12 300833 ⟨1023329, by decide⟩ ⟨12, 2, 0, 1023329, 300833, 3309, 65536⟩
    (by decide) selected_cut_38078

theorem selected_cut_38079 : selected 9 ⟨1023384, by decide⟩
    (prefixPartial 12 300834) = some ⟨12, 2, 0, 1023384, 300834, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_300834_1023384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300834 ⟨1023384, by decide⟩ :=
  accepted_of_selected 12 300834 ⟨1023384, by decide⟩ ⟨12, 2, 0, 1023384, 300834, 3441, 65536⟩
    (by decide) selected_cut_38079

theorem selected_cut_38080 : selected 9 ⟨1023439, by decide⟩
    (prefixPartial 12 300835) = some ⟨12, 2, 0, 1023439, 300835, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_300835_1023439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300835 ⟨1023439, by decide⟩ :=
  accepted_of_selected 12 300835 ⟨1023439, by decide⟩ ⟨12, 2, 0, 1023439, 300835, 3397, 65536⟩
    (by decide) selected_cut_38080

theorem unmarked_context_11_75208_1023440 : frontier 10 ⟨1023440, by decide⟩
    (prefixCache 11 75208) (prefixPartial 11 75208) = false := by
  decide +kernel

theorem node_context_11_75208_1023440 : EJMOriginalGlobalDAGData.nodes 10 ⟨1023440, by decide⟩ =
    .split (coordinate 11) (![⟨1023274, by decide⟩,⟨1023329, by decide⟩,⟨1023384, by decide⟩,⟨1023439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75208_1023440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75208 ⟨1023440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75208
    ⟨1023440, by decide⟩ (by decide) (![⟨1023274, by decide⟩,⟨1023329, by decide⟩,⟨1023384, by decide⟩,⟨1023439, by decide⟩]) unmarked_context_11_75208_1023440 node_context_11_75208_1023440
  intro a
  fin_cases a
  · exact context_12_300832_1023274
  · exact context_12_300833_1023329
  · exact context_12_300834_1023384
  · exact context_12_300835_1023439

theorem selected_cut_38081 : selected 9 ⟨1023494, by decide⟩
    (prefixPartial 12 300836) = some ⟨12, 2, 0, 1023494, 300836, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_300836_1023494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300836 ⟨1023494, by decide⟩ :=
  accepted_of_selected 12 300836 ⟨1023494, by decide⟩ ⟨12, 2, 0, 1023494, 300836, 3497, 65536⟩
    (by decide) selected_cut_38081

theorem selected_cut_38082 : selected 9 ⟨1023548, by decide⟩
    (prefixPartial 12 300837) = some ⟨12, 2, 0, 1023548, 300837, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_300837_1023548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300837 ⟨1023548, by decide⟩ :=
  accepted_of_selected 12 300837 ⟨1023548, by decide⟩ ⟨12, 2, 0, 1023548, 300837, 3245, 65536⟩
    (by decide) selected_cut_38082

theorem selected_cut_38083 : selected 9 ⟨1023597, by decide⟩
    (prefixPartial 12 300838) = some ⟨12, 2, 0, 1023597, 300838, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_300838_1023597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300838 ⟨1023597, by decide⟩ :=
  accepted_of_selected 12 300838 ⟨1023597, by decide⟩ ⟨12, 2, 0, 1023597, 300838, 3149, 65536⟩
    (by decide) selected_cut_38083

theorem selected_cut_38084 : selected 9 ⟨1023638, by decide⟩
    (prefixPartial 12 300839) = some ⟨12, 2, 0, 1023638, 300839, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_300839_1023638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300839 ⟨1023638, by decide⟩ :=
  accepted_of_selected 12 300839 ⟨1023638, by decide⟩ ⟨12, 2, 0, 1023638, 300839, 3205, 65536⟩
    (by decide) selected_cut_38084

theorem unmarked_context_11_75209_1023639 : frontier 10 ⟨1023639, by decide⟩
    (prefixCache 11 75209) (prefixPartial 11 75209) = false := by
  decide +kernel

theorem node_context_11_75209_1023639 : EJMOriginalGlobalDAGData.nodes 10 ⟨1023639, by decide⟩ =
    .split (coordinate 11) (![⟨1023494, by decide⟩,⟨1023548, by decide⟩,⟨1023597, by decide⟩,⟨1023638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75209_1023639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75209 ⟨1023639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75209
    ⟨1023639, by decide⟩ (by decide) (![⟨1023494, by decide⟩,⟨1023548, by decide⟩,⟨1023597, by decide⟩,⟨1023638, by decide⟩]) unmarked_context_11_75209_1023639 node_context_11_75209_1023639
  intro a
  fin_cases a
  · exact context_12_300836_1023494
  · exact context_12_300837_1023548
  · exact context_12_300838_1023597
  · exact context_12_300839_1023638

theorem selected_cut_38085 : selected 9 ⟨1023698, by decide⟩
    (prefixPartial 12 300840) = some ⟨12, 2, 0, 1023698, 300840, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_300840_1023698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300840 ⟨1023698, by decide⟩ :=
  accepted_of_selected 12 300840 ⟨1023698, by decide⟩ ⟨12, 2, 0, 1023698, 300840, 3757, 65536⟩
    (by decide) selected_cut_38085

theorem selected_cut_38086 : selected 9 ⟨1023768, by decide⟩
    (prefixPartial 12 300841) = some ⟨12, 2, 0, 1023768, 300841, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_300841_1023768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300841 ⟨1023768, by decide⟩ :=
  accepted_of_selected 12 300841 ⟨1023768, by decide⟩ ⟨12, 2, 0, 1023768, 300841, 3737, 65536⟩
    (by decide) selected_cut_38086

theorem selected_cut_38087 : selected 9 ⟨1023821, by decide⟩
    (prefixPartial 12 300842) = some ⟨12, 2, 0, 1023821, 300842, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_300842_1023821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300842 ⟨1023821, by decide⟩ :=
  accepted_of_selected 12 300842 ⟨1023821, by decide⟩ ⟨12, 2, 0, 1023821, 300842, 3453, 65536⟩
    (by decide) selected_cut_38087

theorem selected_cut_38088 : selected 9 ⟨1023879, by decide⟩
    (prefixPartial 12 300843) = some ⟨12, 2, 0, 1023879, 300843, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_300843_1023879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300843 ⟨1023879, by decide⟩ :=
  accepted_of_selected 12 300843 ⟨1023879, by decide⟩ ⟨12, 2, 0, 1023879, 300843, 3749, 65536⟩
    (by decide) selected_cut_38088

theorem unmarked_context_11_75210_1023880 : frontier 10 ⟨1023880, by decide⟩
    (prefixCache 11 75210) (prefixPartial 11 75210) = false := by
  decide +kernel

theorem node_context_11_75210_1023880 : EJMOriginalGlobalDAGData.nodes 10 ⟨1023880, by decide⟩ =
    .split (coordinate 11) (![⟨1023698, by decide⟩,⟨1023768, by decide⟩,⟨1023821, by decide⟩,⟨1023879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75210_1023880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75210 ⟨1023880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75210
    ⟨1023880, by decide⟩ (by decide) (![⟨1023698, by decide⟩,⟨1023768, by decide⟩,⟨1023821, by decide⟩,⟨1023879, by decide⟩]) unmarked_context_11_75210_1023880 node_context_11_75210_1023880
  intro a
  fin_cases a
  · exact context_12_300840_1023698
  · exact context_12_300841_1023768
  · exact context_12_300842_1023821
  · exact context_12_300843_1023879

theorem selected_cut_38089 : selected 9 ⟨1023931, by decide⟩
    (prefixPartial 12 300844) = some ⟨12, 2, 0, 1023931, 300844, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_300844_1023931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300844 ⟨1023931, by decide⟩ :=
  accepted_of_selected 12 300844 ⟨1023931, by decide⟩ ⟨12, 2, 0, 1023931, 300844, 3373, 65536⟩
    (by decide) selected_cut_38089

theorem selected_cut_38090 : selected 9 ⟨1023991, by decide⟩
    (prefixPartial 12 300845) = some ⟨12, 2, 0, 1023991, 300845, 3489, 65536⟩ := by
  decide +kernel

theorem context_12_300845_1023991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300845 ⟨1023991, by decide⟩ :=
  accepted_of_selected 12 300845 ⟨1023991, by decide⟩ ⟨12, 2, 0, 1023991, 300845, 3489, 65536⟩
    (by decide) selected_cut_38090

theorem selected_cut_38091 : selected 9 ⟨1024053, by decide⟩
    (prefixPartial 12 300846) = some ⟨12, 2, 0, 1024053, 300846, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_300846_1024053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300846 ⟨1024053, by decide⟩ :=
  accepted_of_selected 12 300846 ⟨1024053, by decide⟩ ⟨12, 2, 0, 1024053, 300846, 3493, 65536⟩
    (by decide) selected_cut_38091

theorem selected_cut_38092 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 300847) = some ⟨12, 1, 0, 903806, 300847, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300847_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300847 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 300847 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 300847, 1, 65536⟩
    (by decide) selected_cut_38092

theorem unmarked_context_11_75211_1024054 : frontier 10 ⟨1024054, by decide⟩
    (prefixCache 11 75211) (prefixPartial 11 75211) = false := by
  decide +kernel

theorem node_context_11_75211_1024054 : EJMOriginalGlobalDAGData.nodes 10 ⟨1024054, by decide⟩ =
    .split (coordinate 11) (![⟨1023931, by decide⟩,⟨1023991, by decide⟩,⟨1024053, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75211_1024054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75211 ⟨1024054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75211
    ⟨1024054, by decide⟩ (by decide) (![⟨1023931, by decide⟩,⟨1023991, by decide⟩,⟨1024053, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75211_1024054 node_context_11_75211_1024054
  intro a
  fin_cases a
  · exact context_12_300844_1023931
  · exact context_12_300845_1023991
  · exact context_12_300846_1024053
  · exact context_12_300847_903806

theorem unmarked_context_10_18802_1024055 : frontier 11 ⟨1024055, by decide⟩
    (prefixCache 10 18802) (prefixPartial 10 18802) = false := by
  decide +kernel

theorem node_context_10_18802_1024055 : EJMOriginalGlobalDAGData.nodes 11 ⟨1024055, by decide⟩ =
    .split (coordinate 10) (![⟨1023440, by decide⟩,⟨1023639, by decide⟩,⟨1023880, by decide⟩,⟨1024054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18802_1024055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18802 ⟨1024055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18802
    ⟨1024055, by decide⟩ (by decide) (![⟨1023440, by decide⟩,⟨1023639, by decide⟩,⟨1023880, by decide⟩,⟨1024054, by decide⟩]) unmarked_context_10_18802_1024055 node_context_10_18802_1024055
  intro a
  fin_cases a
  · exact context_11_75208_1023440
  · exact context_11_75209_1023639
  · exact context_11_75210_1023880
  · exact context_11_75211_1024054

theorem selected_cut_38093 : selected 9 ⟨1024108, by decide⟩
    (prefixPartial 12 300848) = some ⟨12, 2, 0, 1024108, 300848, 3213, 65536⟩ := by
  decide +kernel

theorem context_12_300848_1024108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300848 ⟨1024108, by decide⟩ :=
  accepted_of_selected 12 300848 ⟨1024108, by decide⟩ ⟨12, 2, 0, 1024108, 300848, 3213, 65536⟩
    (by decide) selected_cut_38093

theorem selected_cut_38094 : selected 9 ⟨1024159, by decide⟩
    (prefixPartial 12 300849) = some ⟨12, 2, 0, 1024159, 300849, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_300849_1024159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300849 ⟨1024159, by decide⟩ :=
  accepted_of_selected 12 300849 ⟨1024159, by decide⟩ ⟨12, 2, 0, 1024159, 300849, 3145, 65536⟩
    (by decide) selected_cut_38094

theorem selected_cut_38095 : selected 9 ⟨1024220, by decide⟩
    (prefixPartial 12 300850) = some ⟨12, 2, 0, 1024220, 300850, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_300850_1024220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300850 ⟨1024220, by decide⟩ :=
  accepted_of_selected 12 300850 ⟨1024220, by decide⟩ ⟨12, 2, 0, 1024220, 300850, 3277, 65536⟩
    (by decide) selected_cut_38095

theorem selected_cut_38096 : selected 9 ⟨1024270, by decide⟩
    (prefixPartial 12 300851) = some ⟨12, 2, 0, 1024270, 300851, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_300851_1024270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300851 ⟨1024270, by decide⟩ :=
  accepted_of_selected 12 300851 ⟨1024270, by decide⟩ ⟨12, 2, 0, 1024270, 300851, 3085, 65536⟩
    (by decide) selected_cut_38096

theorem unmarked_context_11_75212_1024271 : frontier 10 ⟨1024271, by decide⟩
    (prefixCache 11 75212) (prefixPartial 11 75212) = false := by
  decide +kernel

theorem node_context_11_75212_1024271 : EJMOriginalGlobalDAGData.nodes 10 ⟨1024271, by decide⟩ =
    .split (coordinate 11) (![⟨1024108, by decide⟩,⟨1024159, by decide⟩,⟨1024220, by decide⟩,⟨1024270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75212_1024271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75212 ⟨1024271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75212
    ⟨1024271, by decide⟩ (by decide) (![⟨1024108, by decide⟩,⟨1024159, by decide⟩,⟨1024220, by decide⟩,⟨1024270, by decide⟩]) unmarked_context_11_75212_1024271 node_context_11_75212_1024271
  intro a
  fin_cases a
  · exact context_12_300848_1024108
  · exact context_12_300849_1024159
  · exact context_12_300850_1024220
  · exact context_12_300851_1024270

theorem selected_cut_38097 : selected 9 ⟨1024324, by decide⟩
    (prefixPartial 12 300852) = some ⟨12, 2, 0, 1024324, 300852, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_300852_1024324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300852 ⟨1024324, by decide⟩ :=
  accepted_of_selected 12 300852 ⟨1024324, by decide⟩ ⟨12, 2, 0, 1024324, 300852, 3197, 65536⟩
    (by decide) selected_cut_38097

theorem selected_cut_38098 : selected 9 ⟨1024372, by decide⟩
    (prefixPartial 12 300853) = some ⟨12, 2, 0, 1024372, 300853, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_300853_1024372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300853 ⟨1024372, by decide⟩ :=
  accepted_of_selected 12 300853 ⟨1024372, by decide⟩ ⟨12, 2, 0, 1024372, 300853, 3065, 65536⟩
    (by decide) selected_cut_38098

theorem selected_cut_38099 : selected 9 ⟨1024420, by decide⟩
    (prefixPartial 12 300854) = some ⟨12, 2, 0, 1024420, 300854, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_300854_1024420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300854 ⟨1024420, by decide⟩ :=
  accepted_of_selected 12 300854 ⟨1024420, by decide⟩ ⟨12, 2, 0, 1024420, 300854, 3021, 65536⟩
    (by decide) selected_cut_38099

theorem selected_cut_38100 : selected 9 ⟨1024464, by decide⟩
    (prefixPartial 12 300855) = some ⟨12, 2, 0, 1024464, 300855, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_300855_1024464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300855 ⟨1024464, by decide⟩ :=
  accepted_of_selected 12 300855 ⟨1024464, by decide⟩ ⟨12, 2, 0, 1024464, 300855, 2985, 65536⟩
    (by decide) selected_cut_38100

theorem unmarked_context_11_75213_1024465 : frontier 10 ⟨1024465, by decide⟩
    (prefixCache 11 75213) (prefixPartial 11 75213) = false := by
  decide +kernel

theorem node_context_11_75213_1024465 : EJMOriginalGlobalDAGData.nodes 10 ⟨1024465, by decide⟩ =
    .split (coordinate 11) (![⟨1024324, by decide⟩,⟨1024372, by decide⟩,⟨1024420, by decide⟩,⟨1024464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75213_1024465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75213 ⟨1024465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75213
    ⟨1024465, by decide⟩ (by decide) (![⟨1024324, by decide⟩,⟨1024372, by decide⟩,⟨1024420, by decide⟩,⟨1024464, by decide⟩]) unmarked_context_11_75213_1024465 node_context_11_75213_1024465
  intro a
  fin_cases a
  · exact context_12_300852_1024324
  · exact context_12_300853_1024372
  · exact context_12_300854_1024420
  · exact context_12_300855_1024464

theorem selected_cut_38101 : selected 9 ⟨1024524, by decide⟩
    (prefixPartial 12 300856) = some ⟨12, 2, 0, 1024524, 300856, 3345, 65536⟩ := by
  decide +kernel

theorem context_12_300856_1024524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300856 ⟨1024524, by decide⟩ :=
  accepted_of_selected 12 300856 ⟨1024524, by decide⟩ ⟨12, 2, 0, 1024524, 300856, 3345, 65536⟩
    (by decide) selected_cut_38101

theorem selected_cut_38102 : selected 9 ⟨1024584, by decide⟩
    (prefixPartial 12 300857) = some ⟨12, 2, 0, 1024584, 300857, 3309, 65536⟩ := by
  decide +kernel

theorem context_12_300857_1024584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300857 ⟨1024584, by decide⟩ :=
  accepted_of_selected 12 300857 ⟨1024584, by decide⟩ ⟨12, 2, 0, 1024584, 300857, 3309, 65536⟩
    (by decide) selected_cut_38102

theorem selected_cut_38103 : selected 9 ⟨1024637, by decide⟩
    (prefixPartial 12 300858) = some ⟨12, 2, 0, 1024637, 300858, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_300858_1024637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300858 ⟨1024637, by decide⟩ :=
  accepted_of_selected 12 300858 ⟨1024637, by decide⟩ ⟨12, 2, 0, 1024637, 300858, 3257, 65536⟩
    (by decide) selected_cut_38103

theorem selected_cut_38104 : selected 9 ⟨1024686, by decide⟩
    (prefixPartial 12 300859) = some ⟨12, 2, 0, 1024686, 300859, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_300859_1024686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300859 ⟨1024686, by decide⟩ :=
  accepted_of_selected 12 300859 ⟨1024686, by decide⟩ ⟨12, 2, 0, 1024686, 300859, 3221, 65536⟩
    (by decide) selected_cut_38104

theorem unmarked_context_11_75214_1024687 : frontier 10 ⟨1024687, by decide⟩
    (prefixCache 11 75214) (prefixPartial 11 75214) = false := by
  decide +kernel

theorem node_context_11_75214_1024687 : EJMOriginalGlobalDAGData.nodes 10 ⟨1024687, by decide⟩ =
    .split (coordinate 11) (![⟨1024524, by decide⟩,⟨1024584, by decide⟩,⟨1024637, by decide⟩,⟨1024686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75214_1024687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75214 ⟨1024687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75214
    ⟨1024687, by decide⟩ (by decide) (![⟨1024524, by decide⟩,⟨1024584, by decide⟩,⟨1024637, by decide⟩,⟨1024686, by decide⟩]) unmarked_context_11_75214_1024687 node_context_11_75214_1024687
  intro a
  fin_cases a
  · exact context_12_300856_1024524
  · exact context_12_300857_1024584
  · exact context_12_300858_1024637
  · exact context_12_300859_1024686

theorem selected_cut_38105 : selected 9 ⟨1024734, by decide⟩
    (prefixPartial 12 300860) = some ⟨12, 2, 0, 1024734, 300860, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_300860_1024734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300860 ⟨1024734, by decide⟩ :=
  accepted_of_selected 12 300860 ⟨1024734, by decide⟩ ⟨12, 2, 0, 1024734, 300860, 3025, 65536⟩
    (by decide) selected_cut_38105

theorem selected_cut_38106 : selected 9 ⟨1024791, by decide⟩
    (prefixPartial 12 300861) = some ⟨12, 2, 0, 1024791, 300861, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_300861_1024791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300861 ⟨1024791, by decide⟩ :=
  accepted_of_selected 12 300861 ⟨1024791, by decide⟩ ⟨12, 2, 0, 1024791, 300861, 3037, 65536⟩
    (by decide) selected_cut_38106

theorem selected_cut_38107 : selected 9 ⟨1024851, by decide⟩
    (prefixPartial 12 300862) = some ⟨12, 2, 0, 1024851, 300862, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_300862_1024851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300862 ⟨1024851, by decide⟩ :=
  accepted_of_selected 12 300862 ⟨1024851, by decide⟩ ⟨12, 2, 0, 1024851, 300862, 3233, 65536⟩
    (by decide) selected_cut_38107

theorem selected_cut_38108 : selected 9 ⟨762108, by decide⟩
    (prefixPartial 12 300863) = some ⟨12, 1, 0, 762108, 300863, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300863_762108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300863 ⟨762108, by decide⟩ :=
  accepted_of_selected 12 300863 ⟨762108, by decide⟩ ⟨12, 1, 0, 762108, 300863, 1, 65536⟩
    (by decide) selected_cut_38108

theorem unmarked_context_11_75215_1024852 : frontier 10 ⟨1024852, by decide⟩
    (prefixCache 11 75215) (prefixPartial 11 75215) = false := by
  decide +kernel

theorem node_context_11_75215_1024852 : EJMOriginalGlobalDAGData.nodes 10 ⟨1024852, by decide⟩ =
    .split (coordinate 11) (![⟨1024734, by decide⟩,⟨1024791, by decide⟩,⟨1024851, by decide⟩,⟨762108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75215_1024852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75215 ⟨1024852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75215
    ⟨1024852, by decide⟩ (by decide) (![⟨1024734, by decide⟩,⟨1024791, by decide⟩,⟨1024851, by decide⟩,⟨762108, by decide⟩]) unmarked_context_11_75215_1024852 node_context_11_75215_1024852
  intro a
  fin_cases a
  · exact context_12_300860_1024734
  · exact context_12_300861_1024791
  · exact context_12_300862_1024851
  · exact context_12_300863_762108

theorem unmarked_context_10_18803_1024853 : frontier 11 ⟨1024853, by decide⟩
    (prefixCache 10 18803) (prefixPartial 10 18803) = false := by
  decide +kernel

theorem node_context_10_18803_1024853 : EJMOriginalGlobalDAGData.nodes 11 ⟨1024853, by decide⟩ =
    .split (coordinate 10) (![⟨1024271, by decide⟩,⟨1024465, by decide⟩,⟨1024687, by decide⟩,⟨1024852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18803_1024853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18803 ⟨1024853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18803
    ⟨1024853, by decide⟩ (by decide) (![⟨1024271, by decide⟩,⟨1024465, by decide⟩,⟨1024687, by decide⟩,⟨1024852, by decide⟩]) unmarked_context_10_18803_1024853 node_context_10_18803_1024853
  intro a
  fin_cases a
  · exact context_11_75212_1024271
  · exact context_11_75213_1024465
  · exact context_11_75214_1024687
  · exact context_11_75215_1024852

theorem unmarked_context_9_4700_1024854 : frontier 12 ⟨1024854, by decide⟩
    (prefixCache 9 4700) (prefixPartial 9 4700) = false := by
  decide +kernel

theorem node_context_9_4700_1024854 : EJMOriginalGlobalDAGData.nodes 12 ⟨1024854, by decide⟩ =
    .split (coordinate 9) (![⟨1022669, by decide⟩,⟨1023214, by decide⟩,⟨1024055, by decide⟩,⟨1024853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4700_1024854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4700 ⟨1024854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4700
    ⟨1024854, by decide⟩ (by decide) (![⟨1022669, by decide⟩,⟨1023214, by decide⟩,⟨1024055, by decide⟩,⟨1024853, by decide⟩]) unmarked_context_9_4700_1024854 node_context_9_4700_1024854
  intro a
  fin_cases a
  · exact context_10_18800_1022669
  · exact context_10_18801_1023214
  · exact context_10_18802_1024055
  · exact context_10_18803_1024853

theorem selected_cut_38109 : selected 9 ⟨1024986, by decide⟩
    (prefixPartial 12 300864) = some ⟨12, 2, 0, 1024986, 300864, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_300864_1024986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300864 ⟨1024986, by decide⟩ :=
  accepted_of_selected 12 300864 ⟨1024986, by decide⟩ ⟨12, 2, 0, 1024986, 300864, 1621, 65536⟩
    (by decide) selected_cut_38109

theorem selected_cut_38110 : selected 9 ⟨1025022, by decide⟩
    (prefixPartial 12 300865) = some ⟨12, 2, 0, 1025022, 300865, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_300865_1025022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300865 ⟨1025022, by decide⟩ :=
  accepted_of_selected 12 300865 ⟨1025022, by decide⟩ ⟨12, 2, 0, 1025022, 300865, 2425, 65536⟩
    (by decide) selected_cut_38110

theorem selected_cut_38111 : selected 9 ⟨1025070, by decide⟩
    (prefixPartial 12 300866) = some ⟨12, 2, 0, 1025070, 300866, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_300866_1025070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300866 ⟨1025070, by decide⟩ :=
  accepted_of_selected 12 300866 ⟨1025070, by decide⟩ ⟨12, 2, 0, 1025070, 300866, 2797, 65536⟩
    (by decide) selected_cut_38111

theorem selected_cut_38112 : selected 9 ⟨1025107, by decide⟩
    (prefixPartial 12 300867) = some ⟨12, 2, 0, 1025107, 300867, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_300867_1025107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300867 ⟨1025107, by decide⟩ :=
  accepted_of_selected 12 300867 ⟨1025107, by decide⟩ ⟨12, 2, 0, 1025107, 300867, 2581, 65536⟩
    (by decide) selected_cut_38112

theorem unmarked_context_11_75216_1025108 : frontier 10 ⟨1025108, by decide⟩
    (prefixCache 11 75216) (prefixPartial 11 75216) = false := by
  decide +kernel

theorem node_context_11_75216_1025108 : EJMOriginalGlobalDAGData.nodes 10 ⟨1025108, by decide⟩ =
    .split (coordinate 11) (![⟨1024986, by decide⟩,⟨1025022, by decide⟩,⟨1025070, by decide⟩,⟨1025107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75216_1025108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75216 ⟨1025108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75216
    ⟨1025108, by decide⟩ (by decide) (![⟨1024986, by decide⟩,⟨1025022, by decide⟩,⟨1025070, by decide⟩,⟨1025107, by decide⟩]) unmarked_context_11_75216_1025108 node_context_11_75216_1025108
  intro a
  fin_cases a
  · exact context_12_300864_1024986
  · exact context_12_300865_1025022
  · exact context_12_300866_1025070
  · exact context_12_300867_1025107

theorem selected_cut_38113 : selected 9 ⟨1025168, by decide⟩
    (prefixPartial 12 300868) = some ⟨12, 2, 0, 1025168, 300868, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_300868_1025168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300868 ⟨1025168, by decide⟩ :=
  accepted_of_selected 12 300868 ⟨1025168, by decide⟩ ⟨12, 2, 0, 1025168, 300868, 2945, 65536⟩
    (by decide) selected_cut_38113

theorem selected_cut_38114 : selected 9 ⟨1025203, by decide⟩
    (prefixPartial 12 300869) = some ⟨12, 2, 0, 1025203, 300869, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_300869_1025203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300869 ⟨1025203, by decide⟩ :=
  accepted_of_selected 12 300869 ⟨1025203, by decide⟩ ⟨12, 2, 0, 1025203, 300869, 2293, 65536⟩
    (by decide) selected_cut_38114

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
