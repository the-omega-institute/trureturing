/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover058
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_20771_174678 : frontier 9 ⟨174678, by decide⟩
    (prefixCache 12 20771) (prefixPartial 12 20771) = false := by
  decide +kernel

theorem node_context_12_20771_174678 : EJMOriginalGlobalDAGData.nodes 9 ⟨174678, by decide⟩ =
    .split (coordinate 12) (![⟨174621, by decide⟩,⟨174648, by decide⟩,⟨174666, by decide⟩,⟨174677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20771_174678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20771 ⟨174678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20771
    ⟨174678, by decide⟩ (by decide) (![⟨174621, by decide⟩,⟨174648, by decide⟩,⟨174666, by decide⟩,⟨174677, by decide⟩]) unmarked_context_12_20771_174678 node_context_12_20771_174678
  intro a
  fin_cases a
  · exact context_13_83084_174621
  · exact context_13_83085_174648
  · exact context_13_83086_174666
  · exact context_13_83087_174677

theorem unmarked_context_11_5192_174679 : frontier 10 ⟨174679, by decide⟩
    (prefixCache 11 5192) (prefixPartial 11 5192) = false := by
  decide +kernel

theorem node_context_11_5192_174679 : EJMOriginalGlobalDAGData.nodes 10 ⟨174679, by decide⟩ =
    .split (coordinate 11) (![⟨174449, by decide⟩,⟨174519, by decide⟩,⟨174599, by decide⟩,⟨174678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5192_174679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5192 ⟨174679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5192
    ⟨174679, by decide⟩ (by decide) (![⟨174449, by decide⟩,⟨174519, by decide⟩,⟨174599, by decide⟩,⟨174678, by decide⟩]) unmarked_context_11_5192_174679 node_context_11_5192_174679
  intro a
  fin_cases a
  · exact context_12_20768_174449
  · exact context_12_20769_174519
  · exact context_12_20770_174599
  · exact context_12_20771_174678

theorem selected_cut_05667 : selected 9 ⟨174738, by decide⟩
    (prefixPartial 12 20772) = some ⟨12, 2, 0, 174738, 20772, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_20772_174738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20772 ⟨174738, by decide⟩ :=
  accepted_of_selected 12 20772 ⟨174738, by decide⟩ ⟨12, 2, 0, 174738, 20772, 3917, 65536⟩
    (by decide) selected_cut_05667

theorem selected_cut_05668 : selected 8 ⟨174758, by decide⟩
    (prefixPartial 13 83092) = some ⟨13, 2, 0, 174758, 83092, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_83092_174758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83092 ⟨174758, by decide⟩ :=
  accepted_of_selected 13 83092 ⟨174758, by decide⟩ ⟨13, 2, 0, 174758, 83092, 1205, 16384⟩
    (by decide) selected_cut_05668

theorem selected_cut_05669 : selected 8 ⟨174785, by decide⟩
    (prefixPartial 13 83093) = some ⟨13, 2, 0, 174785, 83093, 3081, 16384⟩ := by
  decide +kernel

theorem context_13_83093_174785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83093 ⟨174785, by decide⟩ :=
  accepted_of_selected 13 83093 ⟨174785, by decide⟩ ⟨13, 2, 0, 174785, 83093, 3081, 16384⟩
    (by decide) selected_cut_05669

theorem selected_cut_05670 : selected 8 ⟨174805, by decide⟩
    (prefixPartial 13 83094) = some ⟨13, 2, 0, 174805, 83094, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_83094_174805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83094 ⟨174805, by decide⟩ :=
  accepted_of_selected 13 83094 ⟨174805, by decide⟩ ⟨13, 2, 0, 174805, 83094, 1889, 16384⟩
    (by decide) selected_cut_05670

theorem selected_cut_05671 : selected 8 ⟨174815, by decide⟩
    (prefixPartial 13 83095) = some ⟨13, 2, 0, 174815, 83095, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_83095_174815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83095 ⟨174815, by decide⟩ :=
  accepted_of_selected 13 83095 ⟨174815, by decide⟩ ⟨13, 2, 0, 174815, 83095, 1061, 16384⟩
    (by decide) selected_cut_05671

theorem unmarked_context_12_20773_174816 : frontier 9 ⟨174816, by decide⟩
    (prefixCache 12 20773) (prefixPartial 12 20773) = false := by
  decide +kernel

theorem node_context_12_20773_174816 : EJMOriginalGlobalDAGData.nodes 9 ⟨174816, by decide⟩ =
    .split (coordinate 12) (![⟨174758, by decide⟩,⟨174785, by decide⟩,⟨174805, by decide⟩,⟨174815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20773_174816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20773 ⟨174816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20773
    ⟨174816, by decide⟩ (by decide) (![⟨174758, by decide⟩,⟨174785, by decide⟩,⟨174805, by decide⟩,⟨174815, by decide⟩]) unmarked_context_12_20773_174816 node_context_12_20773_174816
  intro a
  fin_cases a
  · exact context_13_83092_174758
  · exact context_13_83093_174785
  · exact context_13_83094_174805
  · exact context_13_83095_174815

theorem selected_cut_05672 : selected 8 ⟨174835, by decide⟩
    (prefixPartial 13 83096) = some ⟨13, 2, 0, 174835, 83096, 793, 16384⟩ := by
  decide +kernel

theorem context_13_83096_174835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83096 ⟨174835, by decide⟩ :=
  accepted_of_selected 13 83096 ⟨174835, by decide⟩ ⟨13, 2, 0, 174835, 83096, 793, 16384⟩
    (by decide) selected_cut_05672

theorem selected_cut_05673 : selected 8 ⟨174860, by decide⟩
    (prefixPartial 13 83097) = some ⟨13, 2, 0, 174860, 83097, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_83097_174860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83097 ⟨174860, by decide⟩ :=
  accepted_of_selected 13 83097 ⟨174860, by decide⟩ ⟨13, 2, 0, 174860, 83097, 2401, 16384⟩
    (by decide) selected_cut_05673

theorem selected_cut_05674 : selected 8 ⟨174878, by decide⟩
    (prefixPartial 13 83098) = some ⟨13, 2, 0, 174878, 83098, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_83098_174878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83098 ⟨174878, by decide⟩ :=
  accepted_of_selected 13 83098 ⟨174878, by decide⟩ ⟨13, 2, 0, 174878, 83098, 1217, 16384⟩
    (by decide) selected_cut_05674

theorem selected_cut_05675 : selected 8 ⟨174886, by decide⟩
    (prefixPartial 13 83099) = some ⟨13, 2, 0, 174886, 83099, 761, 16384⟩ := by
  decide +kernel

theorem context_13_83099_174886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83099 ⟨174886, by decide⟩ :=
  accepted_of_selected 13 83099 ⟨174886, by decide⟩ ⟨13, 2, 0, 174886, 83099, 761, 16384⟩
    (by decide) selected_cut_05675

theorem unmarked_context_12_20774_174887 : frontier 9 ⟨174887, by decide⟩
    (prefixCache 12 20774) (prefixPartial 12 20774) = false := by
  decide +kernel

theorem node_context_12_20774_174887 : EJMOriginalGlobalDAGData.nodes 9 ⟨174887, by decide⟩ =
    .split (coordinate 12) (![⟨174835, by decide⟩,⟨174860, by decide⟩,⟨174878, by decide⟩,⟨174886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20774_174887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20774 ⟨174887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20774
    ⟨174887, by decide⟩ (by decide) (![⟨174835, by decide⟩,⟨174860, by decide⟩,⟨174878, by decide⟩,⟨174886, by decide⟩]) unmarked_context_12_20774_174887 node_context_12_20774_174887
  intro a
  fin_cases a
  · exact context_13_83096_174835
  · exact context_13_83097_174860
  · exact context_13_83098_174878
  · exact context_13_83099_174886

theorem selected_cut_05676 : selected 8 ⟨174901, by decide⟩
    (prefixPartial 13 83100) = some ⟨13, 2, 0, 174901, 83100, 733, 16384⟩ := by
  decide +kernel

theorem context_13_83100_174901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83100 ⟨174901, by decide⟩ :=
  accepted_of_selected 13 83100 ⟨174901, by decide⟩ ⟨13, 2, 0, 174901, 83100, 733, 16384⟩
    (by decide) selected_cut_05676

theorem selected_cut_05677 : selected 8 ⟨174928, by decide⟩
    (prefixPartial 13 83101) = some ⟨13, 2, 0, 174928, 83101, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_83101_174928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83101 ⟨174928, by decide⟩ :=
  accepted_of_selected 13 83101 ⟨174928, by decide⟩ ⟨13, 2, 0, 174928, 83101, 2229, 16384⟩
    (by decide) selected_cut_05677

theorem selected_cut_05678 : selected 8 ⟨174943, by decide⟩
    (prefixPartial 13 83102) = some ⟨13, 2, 0, 174943, 83102, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_83102_174943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83102 ⟨174943, by decide⟩ :=
  accepted_of_selected 13 83102 ⟨174943, by decide⟩ ⟨13, 2, 0, 174943, 83102, 1105, 16384⟩
    (by decide) selected_cut_05678

theorem selected_cut_05679 : selected 8 ⟨174951, by decide⟩
    (prefixPartial 13 83103) = some ⟨13, 2, 0, 174951, 83103, 709, 16384⟩ := by
  decide +kernel

theorem context_13_83103_174951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83103 ⟨174951, by decide⟩ :=
  accepted_of_selected 13 83103 ⟨174951, by decide⟩ ⟨13, 2, 0, 174951, 83103, 709, 16384⟩
    (by decide) selected_cut_05679

theorem unmarked_context_12_20775_174952 : frontier 9 ⟨174952, by decide⟩
    (prefixCache 12 20775) (prefixPartial 12 20775) = false := by
  decide +kernel

theorem node_context_12_20775_174952 : EJMOriginalGlobalDAGData.nodes 9 ⟨174952, by decide⟩ =
    .split (coordinate 12) (![⟨174901, by decide⟩,⟨174928, by decide⟩,⟨174943, by decide⟩,⟨174951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20775_174952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20775 ⟨174952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20775
    ⟨174952, by decide⟩ (by decide) (![⟨174901, by decide⟩,⟨174928, by decide⟩,⟨174943, by decide⟩,⟨174951, by decide⟩]) unmarked_context_12_20775_174952 node_context_12_20775_174952
  intro a
  fin_cases a
  · exact context_13_83100_174901
  · exact context_13_83101_174928
  · exact context_13_83102_174943
  · exact context_13_83103_174951

theorem unmarked_context_11_5193_174953 : frontier 10 ⟨174953, by decide⟩
    (prefixCache 11 5193) (prefixPartial 11 5193) = false := by
  decide +kernel

theorem node_context_11_5193_174953 : EJMOriginalGlobalDAGData.nodes 10 ⟨174953, by decide⟩ =
    .split (coordinate 11) (![⟨174738, by decide⟩,⟨174816, by decide⟩,⟨174887, by decide⟩,⟨174952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5193_174953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5193 ⟨174953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5193
    ⟨174953, by decide⟩ (by decide) (![⟨174738, by decide⟩,⟨174816, by decide⟩,⟨174887, by decide⟩,⟨174952, by decide⟩]) unmarked_context_11_5193_174953 node_context_11_5193_174953
  intro a
  fin_cases a
  · exact context_12_20772_174738
  · exact context_12_20773_174816
  · exact context_12_20774_174887
  · exact context_12_20775_174952

theorem selected_cut_05680 : selected 8 ⟨174972, by decide⟩
    (prefixPartial 13 83104) = some ⟨13, 2, 0, 174972, 83104, 789, 16384⟩ := by
  decide +kernel

theorem context_13_83104_174972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83104 ⟨174972, by decide⟩ :=
  accepted_of_selected 13 83104 ⟨174972, by decide⟩ ⟨13, 2, 0, 174972, 83104, 789, 16384⟩
    (by decide) selected_cut_05680

theorem selected_cut_05681 : selected 8 ⟨174998, by decide⟩
    (prefixPartial 13 83105) = some ⟨13, 2, 0, 174998, 83105, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_83105_174998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83105 ⟨174998, by decide⟩ :=
  accepted_of_selected 13 83105 ⟨174998, by decide⟩ ⟨13, 2, 0, 174998, 83105, 2061, 16384⟩
    (by decide) selected_cut_05681

theorem selected_cut_05682 : selected 8 ⟨175019, by decide⟩
    (prefixPartial 13 83106) = some ⟨13, 2, 0, 175019, 83106, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_83106_175019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83106 ⟨175019, by decide⟩ :=
  accepted_of_selected 13 83106 ⟨175019, by decide⟩ ⟨13, 2, 0, 175019, 83106, 1445, 16384⟩
    (by decide) selected_cut_05682

theorem selected_cut_05683 : selected 8 ⟨175029, by decide⟩
    (prefixPartial 13 83107) = some ⟨13, 2, 0, 175029, 83107, 741, 16384⟩ := by
  decide +kernel

theorem context_13_83107_175029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83107 ⟨175029, by decide⟩ :=
  accepted_of_selected 13 83107 ⟨175029, by decide⟩ ⟨13, 2, 0, 175029, 83107, 741, 16384⟩
    (by decide) selected_cut_05683

theorem unmarked_context_12_20776_175030 : frontier 9 ⟨175030, by decide⟩
    (prefixCache 12 20776) (prefixPartial 12 20776) = false := by
  decide +kernel

theorem node_context_12_20776_175030 : EJMOriginalGlobalDAGData.nodes 9 ⟨175030, by decide⟩ =
    .split (coordinate 12) (![⟨174972, by decide⟩,⟨174998, by decide⟩,⟨175019, by decide⟩,⟨175029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20776_175030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20776 ⟨175030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20776
    ⟨175030, by decide⟩ (by decide) (![⟨174972, by decide⟩,⟨174998, by decide⟩,⟨175019, by decide⟩,⟨175029, by decide⟩]) unmarked_context_12_20776_175030 node_context_12_20776_175030
  intro a
  fin_cases a
  · exact context_13_83104_174972
  · exact context_13_83105_174998
  · exact context_13_83106_175019
  · exact context_13_83107_175029

theorem selected_cut_05684 : selected 8 ⟨175044, by decide⟩
    (prefixPartial 13 83108) = some ⟨13, 2, 0, 175044, 83108, 753, 16384⟩ := by
  decide +kernel

theorem context_13_83108_175044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83108 ⟨175044, by decide⟩ :=
  accepted_of_selected 13 83108 ⟨175044, by decide⟩ ⟨13, 2, 0, 175044, 83108, 753, 16384⟩
    (by decide) selected_cut_05684

theorem selected_cut_05685 : selected 8 ⟨175071, by decide⟩
    (prefixPartial 13 83109) = some ⟨13, 2, 0, 175071, 83109, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_83109_175071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83109 ⟨175071, by decide⟩ :=
  accepted_of_selected 13 83109 ⟨175071, by decide⟩ ⟨13, 2, 0, 175071, 83109, 2109, 16384⟩
    (by decide) selected_cut_05685

theorem selected_cut_05686 : selected 8 ⟨175092, by decide⟩
    (prefixPartial 13 83110) = some ⟨13, 2, 0, 175092, 83110, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_83110_175092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83110 ⟨175092, by decide⟩ :=
  accepted_of_selected 13 83110 ⟨175092, by decide⟩ ⟨13, 2, 0, 175092, 83110, 1485, 16384⟩
    (by decide) selected_cut_05686

theorem selected_cut_05687 : selected 8 ⟨175102, by decide⟩
    (prefixPartial 13 83111) = some ⟨13, 2, 0, 175102, 83111, 869, 16384⟩ := by
  decide +kernel

theorem context_13_83111_175102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83111 ⟨175102, by decide⟩ :=
  accepted_of_selected 13 83111 ⟨175102, by decide⟩ ⟨13, 2, 0, 175102, 83111, 869, 16384⟩
    (by decide) selected_cut_05687

theorem unmarked_context_12_20777_175103 : frontier 9 ⟨175103, by decide⟩
    (prefixCache 12 20777) (prefixPartial 12 20777) = false := by
  decide +kernel

theorem node_context_12_20777_175103 : EJMOriginalGlobalDAGData.nodes 9 ⟨175103, by decide⟩ =
    .split (coordinate 12) (![⟨175044, by decide⟩,⟨175071, by decide⟩,⟨175092, by decide⟩,⟨175102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20777_175103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20777 ⟨175103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20777
    ⟨175103, by decide⟩ (by decide) (![⟨175044, by decide⟩,⟨175071, by decide⟩,⟨175092, by decide⟩,⟨175102, by decide⟩]) unmarked_context_12_20777_175103 node_context_12_20777_175103
  intro a
  fin_cases a
  · exact context_13_83108_175044
  · exact context_13_83109_175071
  · exact context_13_83110_175092
  · exact context_13_83111_175102

theorem selected_cut_05688 : selected 8 ⟨175115, by decide⟩
    (prefixPartial 13 83112) = some ⟨13, 2, 0, 175115, 83112, 789, 16384⟩ := by
  decide +kernel

theorem context_13_83112_175115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83112 ⟨175115, by decide⟩ :=
  accepted_of_selected 13 83112 ⟨175115, by decide⟩ ⟨13, 2, 0, 175115, 83112, 789, 16384⟩
    (by decide) selected_cut_05688

theorem selected_cut_05689 : selected 8 ⟨175148, by decide⟩
    (prefixPartial 13 83113) = some ⟨13, 2, 0, 175148, 83113, 2777, 16384⟩ := by
  decide +kernel

theorem context_13_83113_175148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83113 ⟨175148, by decide⟩ :=
  accepted_of_selected 13 83113 ⟨175148, by decide⟩ ⟨13, 2, 0, 175148, 83113, 2777, 16384⟩
    (by decide) selected_cut_05689

theorem selected_cut_05690 : selected 8 ⟨175169, by decide⟩
    (prefixPartial 13 83114) = some ⟨13, 2, 0, 175169, 83114, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_83114_175169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83114 ⟨175169, by decide⟩ :=
  accepted_of_selected 13 83114 ⟨175169, by decide⟩ ⟨13, 2, 0, 175169, 83114, 1557, 16384⟩
    (by decide) selected_cut_05690

theorem selected_cut_05691 : selected 8 ⟨175178, by decide⟩
    (prefixPartial 13 83115) = some ⟨13, 2, 0, 175178, 83115, 809, 16384⟩ := by
  decide +kernel

theorem context_13_83115_175178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83115 ⟨175178, by decide⟩ :=
  accepted_of_selected 13 83115 ⟨175178, by decide⟩ ⟨13, 2, 0, 175178, 83115, 809, 16384⟩
    (by decide) selected_cut_05691

theorem unmarked_context_12_20778_175179 : frontier 9 ⟨175179, by decide⟩
    (prefixCache 12 20778) (prefixPartial 12 20778) = false := by
  decide +kernel

theorem node_context_12_20778_175179 : EJMOriginalGlobalDAGData.nodes 9 ⟨175179, by decide⟩ =
    .split (coordinate 12) (![⟨175115, by decide⟩,⟨175148, by decide⟩,⟨175169, by decide⟩,⟨175178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20778_175179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20778 ⟨175179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20778
    ⟨175179, by decide⟩ (by decide) (![⟨175115, by decide⟩,⟨175148, by decide⟩,⟨175169, by decide⟩,⟨175178, by decide⟩]) unmarked_context_12_20778_175179 node_context_12_20778_175179
  intro a
  fin_cases a
  · exact context_13_83112_175115
  · exact context_13_83113_175148
  · exact context_13_83114_175169
  · exact context_13_83115_175178

theorem selected_cut_05692 : selected 8 ⟨175188, by decide⟩
    (prefixPartial 13 83116) = some ⟨13, 2, 0, 175188, 83116, 653, 16384⟩ := by
  decide +kernel

theorem context_13_83116_175188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83116 ⟨175188, by decide⟩ :=
  accepted_of_selected 13 83116 ⟨175188, by decide⟩ ⟨13, 2, 0, 175188, 83116, 653, 16384⟩
    (by decide) selected_cut_05692

theorem selected_cut_05693 : selected 8 ⟨175228, by decide⟩
    (prefixPartial 13 83117) = some ⟨13, 2, 0, 175228, 83117, 2721, 16384⟩ := by
  decide +kernel

theorem context_13_83117_175228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83117 ⟨175228, by decide⟩ :=
  accepted_of_selected 13 83117 ⟨175228, by decide⟩ ⟨13, 2, 0, 175228, 83117, 2721, 16384⟩
    (by decide) selected_cut_05693

theorem selected_cut_05694 : selected 8 ⟨175246, by decide⟩
    (prefixPartial 13 83118) = some ⟨13, 2, 0, 175246, 83118, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_83118_175246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83118 ⟨175246, by decide⟩ :=
  accepted_of_selected 13 83118 ⟨175246, by decide⟩ ⟨13, 2, 0, 175246, 83118, 1533, 16384⟩
    (by decide) selected_cut_05694

theorem selected_cut_05695 : selected 8 ⟨175255, by decide⟩
    (prefixPartial 13 83119) = some ⟨13, 2, 0, 175255, 83119, 893, 16384⟩ := by
  decide +kernel

theorem context_13_83119_175255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83119 ⟨175255, by decide⟩ :=
  accepted_of_selected 13 83119 ⟨175255, by decide⟩ ⟨13, 2, 0, 175255, 83119, 893, 16384⟩
    (by decide) selected_cut_05695

theorem unmarked_context_12_20779_175256 : frontier 9 ⟨175256, by decide⟩
    (prefixCache 12 20779) (prefixPartial 12 20779) = false := by
  decide +kernel

theorem node_context_12_20779_175256 : EJMOriginalGlobalDAGData.nodes 9 ⟨175256, by decide⟩ =
    .split (coordinate 12) (![⟨175188, by decide⟩,⟨175228, by decide⟩,⟨175246, by decide⟩,⟨175255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20779_175256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20779 ⟨175256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20779
    ⟨175256, by decide⟩ (by decide) (![⟨175188, by decide⟩,⟨175228, by decide⟩,⟨175246, by decide⟩,⟨175255, by decide⟩]) unmarked_context_12_20779_175256 node_context_12_20779_175256
  intro a
  fin_cases a
  · exact context_13_83116_175188
  · exact context_13_83117_175228
  · exact context_13_83118_175246
  · exact context_13_83119_175255

theorem unmarked_context_11_5194_175257 : frontier 10 ⟨175257, by decide⟩
    (prefixCache 11 5194) (prefixPartial 11 5194) = false := by
  decide +kernel

theorem node_context_11_5194_175257 : EJMOriginalGlobalDAGData.nodes 10 ⟨175257, by decide⟩ =
    .split (coordinate 11) (![⟨175030, by decide⟩,⟨175103, by decide⟩,⟨175179, by decide⟩,⟨175256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5194_175257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5194 ⟨175257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5194
    ⟨175257, by decide⟩ (by decide) (![⟨175030, by decide⟩,⟨175103, by decide⟩,⟨175179, by decide⟩,⟨175256, by decide⟩]) unmarked_context_11_5194_175257 node_context_11_5194_175257
  intro a
  fin_cases a
  · exact context_12_20776_175030
  · exact context_12_20777_175103
  · exact context_12_20778_175179
  · exact context_12_20779_175256

theorem selected_cut_05696 : selected 8 ⟨175264, by decide⟩
    (prefixPartial 13 83120) = some ⟨13, 2, 0, 175264, 83120, 429, 16384⟩ := by
  decide +kernel

theorem context_13_83120_175264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83120 ⟨175264, by decide⟩ :=
  accepted_of_selected 13 83120 ⟨175264, by decide⟩ ⟨13, 2, 0, 175264, 83120, 429, 16384⟩
    (by decide) selected_cut_05696

theorem selected_cut_05697 : selected 8 ⟨175289, by decide⟩
    (prefixPartial 13 83121) = some ⟨13, 2, 0, 175289, 83121, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_83121_175289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83121 ⟨175289, by decide⟩ :=
  accepted_of_selected 13 83121 ⟨175289, by decide⟩ ⟨13, 2, 0, 175289, 83121, 2077, 16384⟩
    (by decide) selected_cut_05697

theorem selected_cut_05698 : selected 8 ⟨175310, by decide⟩
    (prefixPartial 13 83122) = some ⟨13, 2, 0, 175310, 83122, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_83122_175310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83122 ⟨175310, by decide⟩ :=
  accepted_of_selected 13 83122 ⟨175310, by decide⟩ ⟨13, 2, 0, 175310, 83122, 1517, 16384⟩
    (by decide) selected_cut_05698

theorem selected_cut_05699 : selected 8 ⟨175318, by decide⟩
    (prefixPartial 13 83123) = some ⟨13, 2, 0, 175318, 83123, 969, 16384⟩ := by
  decide +kernel

theorem context_13_83123_175318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83123 ⟨175318, by decide⟩ :=
  accepted_of_selected 13 83123 ⟨175318, by decide⟩ ⟨13, 2, 0, 175318, 83123, 969, 16384⟩
    (by decide) selected_cut_05699

theorem unmarked_context_12_20780_175319 : frontier 9 ⟨175319, by decide⟩
    (prefixCache 12 20780) (prefixPartial 12 20780) = false := by
  decide +kernel

theorem node_context_12_20780_175319 : EJMOriginalGlobalDAGData.nodes 9 ⟨175319, by decide⟩ =
    .split (coordinate 12) (![⟨175264, by decide⟩,⟨175289, by decide⟩,⟨175310, by decide⟩,⟨175318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20780_175319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20780 ⟨175319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20780
    ⟨175319, by decide⟩ (by decide) (![⟨175264, by decide⟩,⟨175289, by decide⟩,⟨175310, by decide⟩,⟨175318, by decide⟩]) unmarked_context_12_20780_175319 node_context_12_20780_175319
  intro a
  fin_cases a
  · exact context_13_83120_175264
  · exact context_13_83121_175289
  · exact context_13_83122_175310
  · exact context_13_83123_175318

theorem selected_cut_05700 : selected 8 ⟨175327, by decide⟩
    (prefixPartial 13 83124) = some ⟨13, 2, 0, 175327, 83124, 361, 16384⟩ := by
  decide +kernel

theorem context_13_83124_175327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83124 ⟨175327, by decide⟩ :=
  accepted_of_selected 13 83124 ⟨175327, by decide⟩ ⟨13, 2, 0, 175327, 83124, 361, 16384⟩
    (by decide) selected_cut_05700

theorem selected_cut_05701 : selected 8 ⟨175355, by decide⟩
    (prefixPartial 13 83125) = some ⟨13, 2, 0, 175355, 83125, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_83125_175355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83125 ⟨175355, by decide⟩ :=
  accepted_of_selected 13 83125 ⟨175355, by decide⟩ ⟨13, 2, 0, 175355, 83125, 2097, 16384⟩
    (by decide) selected_cut_05701

theorem selected_cut_05702 : selected 8 ⟨175374, by decide⟩
    (prefixPartial 13 83126) = some ⟨13, 2, 0, 175374, 83126, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_83126_175374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83126 ⟨175374, by decide⟩ :=
  accepted_of_selected 13 83126 ⟨175374, by decide⟩ ⟨13, 2, 0, 175374, 83126, 1613, 16384⟩
    (by decide) selected_cut_05702

theorem selected_cut_05703 : selected 8 ⟨175382, by decide⟩
    (prefixPartial 13 83127) = some ⟨13, 2, 0, 175382, 83127, 945, 16384⟩ := by
  decide +kernel

theorem context_13_83127_175382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83127 ⟨175382, by decide⟩ :=
  accepted_of_selected 13 83127 ⟨175382, by decide⟩ ⟨13, 2, 0, 175382, 83127, 945, 16384⟩
    (by decide) selected_cut_05703

theorem unmarked_context_12_20781_175383 : frontier 9 ⟨175383, by decide⟩
    (prefixCache 12 20781) (prefixPartial 12 20781) = false := by
  decide +kernel

theorem node_context_12_20781_175383 : EJMOriginalGlobalDAGData.nodes 9 ⟨175383, by decide⟩ =
    .split (coordinate 12) (![⟨175327, by decide⟩,⟨175355, by decide⟩,⟨175374, by decide⟩,⟨175382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20781_175383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20781 ⟨175383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20781
    ⟨175383, by decide⟩ (by decide) (![⟨175327, by decide⟩,⟨175355, by decide⟩,⟨175374, by decide⟩,⟨175382, by decide⟩]) unmarked_context_12_20781_175383 node_context_12_20781_175383
  intro a
  fin_cases a
  · exact context_13_83124_175327
  · exact context_13_83125_175355
  · exact context_13_83126_175374
  · exact context_13_83127_175382

theorem selected_cut_05704 : selected 8 ⟨175391, by decide⟩
    (prefixPartial 13 83128) = some ⟨13, 2, 0, 175391, 83128, 289, 16384⟩ := by
  decide +kernel

theorem context_13_83128_175391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83128 ⟨175391, by decide⟩ :=
  accepted_of_selected 13 83128 ⟨175391, by decide⟩ ⟨13, 2, 0, 175391, 83128, 289, 16384⟩
    (by decide) selected_cut_05704

theorem selected_cut_05705 : selected 8 ⟨175420, by decide⟩
    (prefixPartial 13 83129) = some ⟨13, 2, 0, 175420, 83129, 2853, 16384⟩ := by
  decide +kernel

theorem context_13_83129_175420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83129 ⟨175420, by decide⟩ :=
  accepted_of_selected 13 83129 ⟨175420, by decide⟩ ⟨13, 2, 0, 175420, 83129, 2853, 16384⟩
    (by decide) selected_cut_05705

theorem selected_cut_05706 : selected 8 ⟨175440, by decide⟩
    (prefixPartial 13 83130) = some ⟨13, 2, 0, 175440, 83130, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_83130_175440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83130 ⟨175440, by decide⟩ :=
  accepted_of_selected 13 83130 ⟨175440, by decide⟩ ⟨13, 2, 0, 175440, 83130, 1805, 16384⟩
    (by decide) selected_cut_05706

theorem selected_cut_05707 : selected 8 ⟨175448, by decide⟩
    (prefixPartial 13 83131) = some ⟨13, 2, 0, 175448, 83131, 945, 16384⟩ := by
  decide +kernel

theorem context_13_83131_175448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83131 ⟨175448, by decide⟩ :=
  accepted_of_selected 13 83131 ⟨175448, by decide⟩ ⟨13, 2, 0, 175448, 83131, 945, 16384⟩
    (by decide) selected_cut_05707

theorem unmarked_context_12_20782_175449 : frontier 9 ⟨175449, by decide⟩
    (prefixCache 12 20782) (prefixPartial 12 20782) = false := by
  decide +kernel

theorem node_context_12_20782_175449 : EJMOriginalGlobalDAGData.nodes 9 ⟨175449, by decide⟩ =
    .split (coordinate 12) (![⟨175391, by decide⟩,⟨175420, by decide⟩,⟨175440, by decide⟩,⟨175448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20782_175449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20782 ⟨175449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20782
    ⟨175449, by decide⟩ (by decide) (![⟨175391, by decide⟩,⟨175420, by decide⟩,⟨175440, by decide⟩,⟨175448, by decide⟩]) unmarked_context_12_20782_175449 node_context_12_20782_175449
  intro a
  fin_cases a
  · exact context_13_83128_175391
  · exact context_13_83129_175420
  · exact context_13_83130_175440
  · exact context_13_83131_175448

theorem selected_cut_05708 : selected 8 ⟨175456, by decide⟩
    (prefixPartial 13 83132) = some ⟨13, 2, 0, 175456, 83132, 137, 16384⟩ := by
  decide +kernel

theorem context_13_83132_175456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83132 ⟨175456, by decide⟩ :=
  accepted_of_selected 13 83132 ⟨175456, by decide⟩ ⟨13, 2, 0, 175456, 83132, 137, 16384⟩
    (by decide) selected_cut_05708

theorem selected_cut_05709 : selected 8 ⟨175484, by decide⟩
    (prefixPartial 13 83133) = some ⟨13, 2, 0, 175484, 83133, 2681, 16384⟩ := by
  decide +kernel

theorem context_13_83133_175484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83133 ⟨175484, by decide⟩ :=
  accepted_of_selected 13 83133 ⟨175484, by decide⟩ ⟨13, 2, 0, 175484, 83133, 2681, 16384⟩
    (by decide) selected_cut_05709

theorem selected_cut_05710 : selected 8 ⟨175503, by decide⟩
    (prefixPartial 13 83134) = some ⟨13, 2, 0, 175503, 83134, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_83134_175503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83134 ⟨175503, by decide⟩ :=
  accepted_of_selected 13 83134 ⟨175503, by decide⟩ ⟨13, 2, 0, 175503, 83134, 1557, 16384⟩
    (by decide) selected_cut_05710

theorem selected_cut_05711 : selected 8 ⟨175515, by decide⟩
    (prefixPartial 13 83135) = some ⟨13, 2, 0, 175515, 83135, 957, 16384⟩ := by
  decide +kernel

theorem context_13_83135_175515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83135 ⟨175515, by decide⟩ :=
  accepted_of_selected 13 83135 ⟨175515, by decide⟩ ⟨13, 2, 0, 175515, 83135, 957, 16384⟩
    (by decide) selected_cut_05711

theorem unmarked_context_12_20783_175516 : frontier 9 ⟨175516, by decide⟩
    (prefixCache 12 20783) (prefixPartial 12 20783) = false := by
  decide +kernel

theorem node_context_12_20783_175516 : EJMOriginalGlobalDAGData.nodes 9 ⟨175516, by decide⟩ =
    .split (coordinate 12) (![⟨175456, by decide⟩,⟨175484, by decide⟩,⟨175503, by decide⟩,⟨175515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20783_175516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20783 ⟨175516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20783
    ⟨175516, by decide⟩ (by decide) (![⟨175456, by decide⟩,⟨175484, by decide⟩,⟨175503, by decide⟩,⟨175515, by decide⟩]) unmarked_context_12_20783_175516 node_context_12_20783_175516
  intro a
  fin_cases a
  · exact context_13_83132_175456
  · exact context_13_83133_175484
  · exact context_13_83134_175503
  · exact context_13_83135_175515

theorem unmarked_context_11_5195_175517 : frontier 10 ⟨175517, by decide⟩
    (prefixCache 11 5195) (prefixPartial 11 5195) = false := by
  decide +kernel

theorem node_context_11_5195_175517 : EJMOriginalGlobalDAGData.nodes 10 ⟨175517, by decide⟩ =
    .split (coordinate 11) (![⟨175319, by decide⟩,⟨175383, by decide⟩,⟨175449, by decide⟩,⟨175516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5195_175517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5195 ⟨175517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5195
    ⟨175517, by decide⟩ (by decide) (![⟨175319, by decide⟩,⟨175383, by decide⟩,⟨175449, by decide⟩,⟨175516, by decide⟩]) unmarked_context_11_5195_175517 node_context_11_5195_175517
  intro a
  fin_cases a
  · exact context_12_20780_175319
  · exact context_12_20781_175383
  · exact context_12_20782_175449
  · exact context_12_20783_175516

theorem unmarked_context_10_1298_175518 : frontier 11 ⟨175518, by decide⟩
    (prefixCache 10 1298) (prefixPartial 10 1298) = false := by
  decide +kernel

theorem node_context_10_1298_175518 : EJMOriginalGlobalDAGData.nodes 11 ⟨175518, by decide⟩ =
    .split (coordinate 10) (![⟨174679, by decide⟩,⟨174953, by decide⟩,⟨175257, by decide⟩,⟨175517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1298_175518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1298 ⟨175518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1298
    ⟨175518, by decide⟩ (by decide) (![⟨174679, by decide⟩,⟨174953, by decide⟩,⟨175257, by decide⟩,⟨175517, by decide⟩]) unmarked_context_10_1298_175518 node_context_10_1298_175518
  intro a
  fin_cases a
  · exact context_11_5192_174679
  · exact context_11_5193_174953
  · exact context_11_5194_175257
  · exact context_11_5195_175517

theorem selected_cut_05712 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 1299) = some ⟨10, 1, 0, 3440, 1299, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1299_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1299 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 1299 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 1299, 1, 1048576⟩
    (by decide) selected_cut_05712

theorem unmarked_context_9_324_175519 : frontier 12 ⟨175519, by decide⟩
    (prefixCache 9 324) (prefixPartial 9 324) = false := by
  decide +kernel

theorem node_context_9_324_175519 : EJMOriginalGlobalDAGData.nodes 12 ⟨175519, by decide⟩ =
    .split (coordinate 9) (![⟨173618, by decide⟩,⟨174383, by decide⟩,⟨175518, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_324_175519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 324 ⟨175519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 324
    ⟨175519, by decide⟩ (by decide) (![⟨173618, by decide⟩,⟨174383, by decide⟩,⟨175518, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_324_175519 node_context_9_324_175519
  intro a
  fin_cases a
  · exact context_10_1296_173618
  · exact context_10_1297_174383
  · exact context_10_1298_175518
  · exact context_10_1299_3440

theorem selected_cut_05713 : selected 9 ⟨175609, by decide⟩
    (prefixPartial 12 20800) = some ⟨12, 2, 0, 175609, 20800, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_20800_175609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20800 ⟨175609, by decide⟩ :=
  accepted_of_selected 12 20800 ⟨175609, by decide⟩ ⟨12, 2, 0, 175609, 20800, 1385, 65536⟩
    (by decide) selected_cut_05713

theorem selected_cut_05714 : selected 9 ⟨175672, by decide⟩
    (prefixPartial 12 20801) = some ⟨12, 2, 0, 175672, 20801, 4017, 65536⟩ := by
  decide +kernel

theorem context_12_20801_175672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20801 ⟨175672, by decide⟩ :=
  accepted_of_selected 12 20801 ⟨175672, by decide⟩ ⟨12, 2, 0, 175672, 20801, 4017, 65536⟩
    (by decide) selected_cut_05714

theorem selected_cut_05715 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 83208) = some ⟨13, 1, 0, 3444, 83208, 1, 16384⟩ := by
  decide +kernel

theorem context_13_83208_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83208 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 83208 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 83208, 1, 16384⟩
    (by decide) selected_cut_05715

theorem selected_cut_05716 : selected 8 ⟨175706, by decide⟩
    (prefixPartial 13 83209) = some ⟨13, 2, 0, 175706, 83209, 2837, 16384⟩ := by
  decide +kernel

theorem context_13_83209_175706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83209 ⟨175706, by decide⟩ :=
  accepted_of_selected 13 83209 ⟨175706, by decide⟩ ⟨13, 2, 0, 175706, 83209, 2837, 16384⟩
    (by decide) selected_cut_05716

theorem selected_cut_05717 : selected 8 ⟨175731, by decide⟩
    (prefixPartial 13 83210) = some ⟨13, 2, 0, 175731, 83210, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_83210_175731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83210 ⟨175731, by decide⟩ :=
  accepted_of_selected 13 83210 ⟨175731, by decide⟩ ⟨13, 2, 0, 175731, 83210, 2333, 16384⟩
    (by decide) selected_cut_05717

theorem selected_cut_05718 : selected 8 ⟨175743, by decide⟩
    (prefixPartial 13 83211) = some ⟨13, 2, 0, 175743, 83211, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_83211_175743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83211 ⟨175743, by decide⟩ :=
  accepted_of_selected 13 83211 ⟨175743, by decide⟩ ⟨13, 2, 0, 175743, 83211, 1097, 16384⟩
    (by decide) selected_cut_05718

theorem unmarked_context_12_20802_175744 : frontier 9 ⟨175744, by decide⟩
    (prefixCache 12 20802) (prefixPartial 12 20802) = false := by
  decide +kernel

theorem node_context_12_20802_175744 : EJMOriginalGlobalDAGData.nodes 9 ⟨175744, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨175706, by decide⟩,⟨175731, by decide⟩,⟨175743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20802_175744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20802 ⟨175744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20802
    ⟨175744, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨175706, by decide⟩,⟨175731, by decide⟩,⟨175743, by decide⟩]) unmarked_context_12_20802_175744 node_context_12_20802_175744
  intro a
  fin_cases a
  · exact context_13_83208_3444
  · exact context_13_83209_175706
  · exact context_13_83210_175731
  · exact context_13_83211_175743

theorem selected_cut_05719 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20803) = some ⟨12, 1, 0, 893, 20803, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20803_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20803 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20803 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20803, 1, 65536⟩
    (by decide) selected_cut_05719

theorem unmarked_context_11_5200_175745 : frontier 10 ⟨175745, by decide⟩
    (prefixCache 11 5200) (prefixPartial 11 5200) = false := by
  decide +kernel

theorem node_context_11_5200_175745 : EJMOriginalGlobalDAGData.nodes 10 ⟨175745, by decide⟩ =
    .split (coordinate 11) (![⟨175609, by decide⟩,⟨175672, by decide⟩,⟨175744, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5200_175745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5200 ⟨175745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5200
    ⟨175745, by decide⟩ (by decide) (![⟨175609, by decide⟩,⟨175672, by decide⟩,⟨175744, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5200_175745 node_context_11_5200_175745
  intro a
  fin_cases a
  · exact context_12_20800_175609
  · exact context_12_20801_175672
  · exact context_12_20802_175744
  · exact context_12_20803_893

theorem selected_cut_05720 : selected 9 ⟨175765, by decide⟩
    (prefixPartial 12 20804) = some ⟨12, 2, 0, 175765, 20804, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_20804_175765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20804 ⟨175765, by decide⟩ :=
  accepted_of_selected 12 20804 ⟨175765, by decide⟩ ⟨12, 2, 0, 175765, 20804, 1345, 65536⟩
    (by decide) selected_cut_05720

theorem selected_cut_05721 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 20805) = some ⟨12, 1, 0, 126884, 20805, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20805_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20805 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 20805 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 20805, 1, 65536⟩
    (by decide) selected_cut_05721

theorem selected_cut_05722 : selected 9 ⟨175816, by decide⟩
    (prefixPartial 12 20806) = some ⟨12, 2, 0, 175816, 20806, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_20806_175816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20806 ⟨175816, by decide⟩ :=
  accepted_of_selected 12 20806 ⟨175816, by decide⟩ ⟨12, 2, 0, 175816, 20806, 3365, 65536⟩
    (by decide) selected_cut_05722

theorem selected_cut_05723 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20807) = some ⟨12, 1, 0, 893, 20807, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20807_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20807 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20807 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20807, 1, 65536⟩
    (by decide) selected_cut_05723

theorem unmarked_context_11_5201_175817 : frontier 10 ⟨175817, by decide⟩
    (prefixCache 11 5201) (prefixPartial 11 5201) = false := by
  decide +kernel

theorem node_context_11_5201_175817 : EJMOriginalGlobalDAGData.nodes 10 ⟨175817, by decide⟩ =
    .split (coordinate 11) (![⟨175765, by decide⟩,⟨126884, by decide⟩,⟨175816, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5201_175817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5201 ⟨175817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5201
    ⟨175817, by decide⟩ (by decide) (![⟨175765, by decide⟩,⟨126884, by decide⟩,⟨175816, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5201_175817 node_context_11_5201_175817
  intro a
  fin_cases a
  · exact context_12_20804_175765
  · exact context_12_20805_126884
  · exact context_12_20806_175816
  · exact context_12_20807_893

theorem selected_cut_05724 : selected 9 ⟨175859, by decide⟩
    (prefixPartial 12 20808) = some ⟨12, 2, 0, 175859, 20808, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_20808_175859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20808 ⟨175859, by decide⟩ :=
  accepted_of_selected 12 20808 ⟨175859, by decide⟩ ⟨12, 2, 0, 175859, 20808, 3373, 65536⟩
    (by decide) selected_cut_05724

theorem selected_cut_05725 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 83236) = some ⟨13, 1, 0, 3444, 83236, 1, 16384⟩ := by
  decide +kernel

theorem context_13_83236_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83236 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 83236 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 83236, 1, 16384⟩
    (by decide) selected_cut_05725

theorem selected_cut_05726 : selected 8 ⟨175886, by decide⟩
    (prefixPartial 13 83237) = some ⟨13, 2, 0, 175886, 83237, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_83237_175886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83237 ⟨175886, by decide⟩ :=
  accepted_of_selected 13 83237 ⟨175886, by decide⟩ ⟨13, 2, 0, 175886, 83237, 2125, 16384⟩
    (by decide) selected_cut_05726

theorem selected_cut_05727 : selected 8 ⟨175911, by decide⟩
    (prefixPartial 13 83238) = some ⟨13, 2, 0, 175911, 83238, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_83238_175911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83238 ⟨175911, by decide⟩ :=
  accepted_of_selected 13 83238 ⟨175911, by decide⟩ ⟨13, 2, 0, 175911, 83238, 2313, 16384⟩
    (by decide) selected_cut_05727

theorem selected_cut_05728 : selected 8 ⟨175923, by decide⟩
    (prefixPartial 13 83239) = some ⟨13, 2, 0, 175923, 83239, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_83239_175923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83239 ⟨175923, by decide⟩ :=
  accepted_of_selected 13 83239 ⟨175923, by decide⟩ ⟨13, 2, 0, 175923, 83239, 1141, 16384⟩
    (by decide) selected_cut_05728

theorem unmarked_context_12_20809_175924 : frontier 9 ⟨175924, by decide⟩
    (prefixCache 12 20809) (prefixPartial 12 20809) = false := by
  decide +kernel

theorem node_context_12_20809_175924 : EJMOriginalGlobalDAGData.nodes 9 ⟨175924, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨175886, by decide⟩,⟨175911, by decide⟩,⟨175923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20809_175924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20809 ⟨175924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20809
    ⟨175924, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨175886, by decide⟩,⟨175911, by decide⟩,⟨175923, by decide⟩]) unmarked_context_12_20809_175924 node_context_12_20809_175924
  intro a
  fin_cases a
  · exact context_13_83236_3444
  · exact context_13_83237_175886
  · exact context_13_83238_175911
  · exact context_13_83239_175923

theorem selected_cut_05729 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 83240) = some ⟨13, 1, 0, 3444, 83240, 1, 16384⟩ := by
  decide +kernel

theorem context_13_83240_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83240 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 83240 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 83240, 1, 16384⟩
    (by decide) selected_cut_05729

theorem selected_cut_05730 : selected 8 ⟨175944, by decide⟩
    (prefixPartial 13 83241) = some ⟨13, 2, 0, 175944, 83241, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_83241_175944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83241 ⟨175944, by decide⟩ :=
  accepted_of_selected 13 83241 ⟨175944, by decide⟩ ⟨13, 2, 0, 175944, 83241, 1769, 16384⟩
    (by decide) selected_cut_05730

theorem selected_cut_05731 : selected 8 ⟨175965, by decide⟩
    (prefixPartial 13 83242) = some ⟨13, 2, 0, 175965, 83242, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_83242_175965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83242 ⟨175965, by decide⟩ :=
  accepted_of_selected 13 83242 ⟨175965, by decide⟩ ⟨13, 2, 0, 175965, 83242, 1889, 16384⟩
    (by decide) selected_cut_05731

theorem selected_cut_05732 : selected 8 ⟨175975, by decide⟩
    (prefixPartial 13 83243) = some ⟨13, 2, 0, 175975, 83243, 789, 16384⟩ := by
  decide +kernel

theorem context_13_83243_175975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83243 ⟨175975, by decide⟩ :=
  accepted_of_selected 13 83243 ⟨175975, by decide⟩ ⟨13, 2, 0, 175975, 83243, 789, 16384⟩
    (by decide) selected_cut_05732

theorem unmarked_context_12_20810_175976 : frontier 9 ⟨175976, by decide⟩
    (prefixCache 12 20810) (prefixPartial 12 20810) = false := by
  decide +kernel

theorem node_context_12_20810_175976 : EJMOriginalGlobalDAGData.nodes 9 ⟨175976, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨175944, by decide⟩,⟨175965, by decide⟩,⟨175975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20810_175976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20810 ⟨175976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20810
    ⟨175976, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨175944, by decide⟩,⟨175965, by decide⟩,⟨175975, by decide⟩]) unmarked_context_12_20810_175976 node_context_12_20810_175976
  intro a
  fin_cases a
  · exact context_13_83240_3444
  · exact context_13_83241_175944
  · exact context_13_83242_175965
  · exact context_13_83243_175975

theorem selected_cut_05733 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 83244) = some ⟨13, 1, 0, 3444, 83244, 1, 16384⟩ := by
  decide +kernel

theorem context_13_83244_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83244 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 83244 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 83244, 1, 16384⟩
    (by decide) selected_cut_05733

theorem selected_cut_05734 : selected 8 ⟨175998, by decide⟩
    (prefixPartial 13 83245) = some ⟨13, 2, 0, 175998, 83245, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_83245_175998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83245 ⟨175998, by decide⟩ :=
  accepted_of_selected 13 83245 ⟨175998, by decide⟩ ⟨13, 2, 0, 175998, 83245, 1709, 16384⟩
    (by decide) selected_cut_05734

theorem selected_cut_05735 : selected 8 ⟨176020, by decide⟩
    (prefixPartial 13 83246) = some ⟨13, 2, 0, 176020, 83246, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_83246_176020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83246 ⟨176020, by decide⟩ :=
  accepted_of_selected 13 83246 ⟨176020, by decide⟩ ⟨13, 2, 0, 176020, 83246, 1777, 16384⟩
    (by decide) selected_cut_05735

theorem selected_cut_05736 : selected 8 ⟨176029, by decide⟩
    (prefixPartial 13 83247) = some ⟨13, 2, 0, 176029, 83247, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_83247_176029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83247 ⟨176029, by decide⟩ :=
  accepted_of_selected 13 83247 ⟨176029, by decide⟩ ⟨13, 2, 0, 176029, 83247, 1017, 16384⟩
    (by decide) selected_cut_05736

theorem unmarked_context_12_20811_176030 : frontier 9 ⟨176030, by decide⟩
    (prefixCache 12 20811) (prefixPartial 12 20811) = false := by
  decide +kernel

theorem node_context_12_20811_176030 : EJMOriginalGlobalDAGData.nodes 9 ⟨176030, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨175998, by decide⟩,⟨176020, by decide⟩,⟨176029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20811_176030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20811 ⟨176030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20811
    ⟨176030, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨175998, by decide⟩,⟨176020, by decide⟩,⟨176029, by decide⟩]) unmarked_context_12_20811_176030 node_context_12_20811_176030
  intro a
  fin_cases a
  · exact context_13_83244_3444
  · exact context_13_83245_175998
  · exact context_13_83246_176020
  · exact context_13_83247_176029

theorem unmarked_context_11_5202_176031 : frontier 10 ⟨176031, by decide⟩
    (prefixCache 11 5202) (prefixPartial 11 5202) = false := by
  decide +kernel

theorem node_context_11_5202_176031 : EJMOriginalGlobalDAGData.nodes 10 ⟨176031, by decide⟩ =
    .split (coordinate 11) (![⟨175859, by decide⟩,⟨175924, by decide⟩,⟨175976, by decide⟩,⟨176030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5202_176031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5202 ⟨176031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5202
    ⟨176031, by decide⟩ (by decide) (![⟨175859, by decide⟩,⟨175924, by decide⟩,⟨175976, by decide⟩,⟨176030, by decide⟩]) unmarked_context_11_5202_176031 node_context_11_5202_176031
  intro a
  fin_cases a
  · exact context_12_20808_175859
  · exact context_12_20809_175924
  · exact context_12_20810_175976
  · exact context_12_20811_176030

theorem selected_cut_05737 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5203) = some ⟨11, 1, 0, 1736, 5203, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5203_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5203 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5203 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5203, 1, 262144⟩
    (by decide) selected_cut_05737

theorem unmarked_context_10_1300_176032 : frontier 11 ⟨176032, by decide⟩
    (prefixCache 10 1300) (prefixPartial 10 1300) = false := by
  decide +kernel

theorem node_context_10_1300_176032 : EJMOriginalGlobalDAGData.nodes 11 ⟨176032, by decide⟩ =
    .split (coordinate 10) (![⟨175745, by decide⟩,⟨175817, by decide⟩,⟨176031, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1300_176032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1300 ⟨176032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1300
    ⟨176032, by decide⟩ (by decide) (![⟨175745, by decide⟩,⟨175817, by decide⟩,⟨176031, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1300_176032 node_context_10_1300_176032
  intro a
  fin_cases a
  · exact context_11_5200_175745
  · exact context_11_5201_175817
  · exact context_11_5202_176031
  · exact context_11_5203_1736

theorem selected_cut_05738 : selected 9 ⟨176059, by decide⟩
    (prefixPartial 12 20816) = some ⟨12, 2, 0, 176059, 20816, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_20816_176059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20816 ⟨176059, by decide⟩ :=
  accepted_of_selected 12 20816 ⟨176059, by decide⟩ ⟨12, 2, 0, 176059, 20816, 1501, 65536⟩
    (by decide) selected_cut_05738

theorem selected_cut_05739 : selected 9 ⟨176108, by decide⟩
    (prefixPartial 12 20817) = some ⟨12, 2, 0, 176108, 20817, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_20817_176108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20817 ⟨176108, by decide⟩ :=
  accepted_of_selected 12 20817 ⟨176108, by decide⟩ ⟨12, 2, 0, 176108, 20817, 1161, 65536⟩
    (by decide) selected_cut_05739

theorem selected_cut_05740 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 83272) = some ⟨13, 1, 0, 3444, 83272, 1, 16384⟩ := by
  decide +kernel

theorem context_13_83272_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83272 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 83272 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 83272, 1, 16384⟩
    (by decide) selected_cut_05740

theorem selected_cut_05741 : selected 8 ⟨176125, by decide⟩
    (prefixPartial 13 83273) = some ⟨13, 2, 0, 176125, 83273, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_83273_176125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83273 ⟨176125, by decide⟩ :=
  accepted_of_selected 13 83273 ⟨176125, by decide⟩ ⟨13, 2, 0, 176125, 83273, 1597, 16384⟩
    (by decide) selected_cut_05741

theorem selected_cut_05742 : selected 8 ⟨176148, by decide⟩
    (prefixPartial 13 83274) = some ⟨13, 2, 0, 176148, 83274, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_83274_176148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83274 ⟨176148, by decide⟩ :=
  accepted_of_selected 13 83274 ⟨176148, by decide⟩ ⟨13, 2, 0, 176148, 83274, 1833, 16384⟩
    (by decide) selected_cut_05742

theorem selected_cut_05743 : selected 8 ⟨176158, by decide⟩
    (prefixPartial 13 83275) = some ⟨13, 2, 0, 176158, 83275, 841, 16384⟩ := by
  decide +kernel

theorem context_13_83275_176158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83275 ⟨176158, by decide⟩ :=
  accepted_of_selected 13 83275 ⟨176158, by decide⟩ ⟨13, 2, 0, 176158, 83275, 841, 16384⟩
    (by decide) selected_cut_05743

theorem unmarked_context_12_20818_176159 : frontier 9 ⟨176159, by decide⟩
    (prefixCache 12 20818) (prefixPartial 12 20818) = false := by
  decide +kernel

theorem node_context_12_20818_176159 : EJMOriginalGlobalDAGData.nodes 9 ⟨176159, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨176125, by decide⟩,⟨176148, by decide⟩,⟨176158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20818_176159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20818 ⟨176159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20818
    ⟨176159, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨176125, by decide⟩,⟨176148, by decide⟩,⟨176158, by decide⟩]) unmarked_context_12_20818_176159 node_context_12_20818_176159
  intro a
  fin_cases a
  · exact context_13_83272_3444
  · exact context_13_83273_176125
  · exact context_13_83274_176148
  · exact context_13_83275_176158

theorem selected_cut_05744 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20819) = some ⟨12, 1, 0, 893, 20819, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20819_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20819 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20819 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20819, 1, 65536⟩
    (by decide) selected_cut_05744

theorem unmarked_context_11_5204_176160 : frontier 10 ⟨176160, by decide⟩
    (prefixCache 11 5204) (prefixPartial 11 5204) = false := by
  decide +kernel

theorem node_context_11_5204_176160 : EJMOriginalGlobalDAGData.nodes 10 ⟨176160, by decide⟩ =
    .split (coordinate 11) (![⟨176059, by decide⟩,⟨176108, by decide⟩,⟨176159, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5204_176160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5204 ⟨176160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5204
    ⟨176160, by decide⟩ (by decide) (![⟨176059, by decide⟩,⟨176108, by decide⟩,⟨176159, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5204_176160 node_context_11_5204_176160
  intro a
  fin_cases a
  · exact context_12_20816_176059
  · exact context_12_20817_176108
  · exact context_12_20818_176159
  · exact context_12_20819_893

theorem selected_cut_05745 : selected 9 ⟨176182, by decide⟩
    (prefixPartial 12 20820) = some ⟨12, 2, 0, 176182, 20820, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_20820_176182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20820 ⟨176182, by decide⟩ :=
  accepted_of_selected 12 20820 ⟨176182, by decide⟩ ⟨12, 2, 0, 176182, 20820, 1309, 65536⟩
    (by decide) selected_cut_05745

theorem selected_cut_05746 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 20821) = some ⟨12, 1, 0, 170504, 20821, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20821_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20821 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 20821 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 20821, 1, 65536⟩
    (by decide) selected_cut_05746

theorem selected_cut_05747 : selected 9 ⟨176225, by decide⟩
    (prefixPartial 12 20822) = some ⟨12, 2, 0, 176225, 20822, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_20822_176225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20822 ⟨176225, by decide⟩ :=
  accepted_of_selected 12 20822 ⟨176225, by decide⟩ ⟨12, 2, 0, 176225, 20822, 3453, 65536⟩
    (by decide) selected_cut_05747

theorem selected_cut_05748 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20823) = some ⟨12, 1, 0, 893, 20823, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20823_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20823 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20823 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20823, 1, 65536⟩
    (by decide) selected_cut_05748

theorem unmarked_context_11_5205_176226 : frontier 10 ⟨176226, by decide⟩
    (prefixCache 11 5205) (prefixPartial 11 5205) = false := by
  decide +kernel

theorem node_context_11_5205_176226 : EJMOriginalGlobalDAGData.nodes 10 ⟨176226, by decide⟩ =
    .split (coordinate 11) (![⟨176182, by decide⟩,⟨170504, by decide⟩,⟨176225, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5205_176226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5205 ⟨176226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5205
    ⟨176226, by decide⟩ (by decide) (![⟨176182, by decide⟩,⟨170504, by decide⟩,⟨176225, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5205_176226 node_context_11_5205_176226
  intro a
  fin_cases a
  · exact context_12_20820_176182
  · exact context_12_20821_170504
  · exact context_12_20822_176225
  · exact context_12_20823_893

theorem selected_cut_05749 : selected 9 ⟨176268, by decide⟩
    (prefixPartial 12 20824) = some ⟨12, 2, 0, 176268, 20824, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_20824_176268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20824 ⟨176268, by decide⟩ :=
  accepted_of_selected 12 20824 ⟨176268, by decide⟩ ⟨12, 2, 0, 176268, 20824, 3185, 65536⟩
    (by decide) selected_cut_05749

theorem selected_cut_05750 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 83300) = some ⟨13, 1, 0, 3444, 83300, 1, 16384⟩ := by
  decide +kernel

theorem context_13_83300_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83300 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 83300 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 83300, 1, 16384⟩
    (by decide) selected_cut_05750

theorem selected_cut_05751 : selected 8 ⟨176284, by decide⟩
    (prefixPartial 13 83301) = some ⟨13, 2, 0, 176284, 83301, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_83301_176284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83301 ⟨176284, by decide⟩ :=
  accepted_of_selected 13 83301 ⟨176284, by decide⟩ ⟨13, 2, 0, 176284, 83301, 1437, 16384⟩
    (by decide) selected_cut_05751

theorem selected_cut_05752 : selected 8 ⟨176321, by decide⟩
    (prefixPartial 13 83302) = some ⟨13, 2, 0, 176321, 83302, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_83302_176321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83302 ⟨176321, by decide⟩ :=
  accepted_of_selected 13 83302 ⟨176321, by decide⟩ ⟨13, 2, 0, 176321, 83302, 2377, 16384⟩
    (by decide) selected_cut_05752

theorem selected_cut_05753 : selected 8 ⟨176335, by decide⟩
    (prefixPartial 13 83303) = some ⟨13, 2, 0, 176335, 83303, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_83303_176335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83303 ⟨176335, by decide⟩ :=
  accepted_of_selected 13 83303 ⟨176335, by decide⟩ ⟨13, 2, 0, 176335, 83303, 1077, 16384⟩
    (by decide) selected_cut_05753

theorem unmarked_context_12_20825_176336 : frontier 9 ⟨176336, by decide⟩
    (prefixCache 12 20825) (prefixPartial 12 20825) = false := by
  decide +kernel

theorem node_context_12_20825_176336 : EJMOriginalGlobalDAGData.nodes 9 ⟨176336, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨176284, by decide⟩,⟨176321, by decide⟩,⟨176335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20825_176336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20825 ⟨176336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20825
    ⟨176336, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨176284, by decide⟩,⟨176321, by decide⟩,⟨176335, by decide⟩]) unmarked_context_12_20825_176336 node_context_12_20825_176336
  intro a
  fin_cases a
  · exact context_13_83300_3444
  · exact context_13_83301_176284
  · exact context_13_83302_176321
  · exact context_13_83303_176335

theorem selected_cut_05754 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 83304) = some ⟨13, 1, 0, 3444, 83304, 1, 16384⟩ := by
  decide +kernel

theorem context_13_83304_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83304 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 83304 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 83304, 1, 16384⟩
    (by decide) selected_cut_05754

theorem selected_cut_05755 : selected 8 ⟨176351, by decide⟩
    (prefixPartial 13 83305) = some ⟨13, 2, 0, 176351, 83305, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_83305_176351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83305 ⟨176351, by decide⟩ :=
  accepted_of_selected 13 83305 ⟨176351, by decide⟩ ⟨13, 2, 0, 176351, 83305, 1357, 16384⟩
    (by decide) selected_cut_05755

theorem selected_cut_05756 : selected 8 ⟨176374, by decide⟩
    (prefixPartial 13 83306) = some ⟨13, 2, 0, 176374, 83306, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_83306_176374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83306 ⟨176374, by decide⟩ :=
  accepted_of_selected 13 83306 ⟨176374, by decide⟩ ⟨13, 2, 0, 176374, 83306, 1957, 16384⟩
    (by decide) selected_cut_05756

theorem selected_cut_05757 : selected 8 ⟨176384, by decide⟩
    (prefixPartial 13 83307) = some ⟨13, 2, 0, 176384, 83307, 921, 16384⟩ := by
  decide +kernel

theorem context_13_83307_176384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83307 ⟨176384, by decide⟩ :=
  accepted_of_selected 13 83307 ⟨176384, by decide⟩ ⟨13, 2, 0, 176384, 83307, 921, 16384⟩
    (by decide) selected_cut_05757

theorem unmarked_context_12_20826_176385 : frontier 9 ⟨176385, by decide⟩
    (prefixCache 12 20826) (prefixPartial 12 20826) = false := by
  decide +kernel

theorem node_context_12_20826_176385 : EJMOriginalGlobalDAGData.nodes 9 ⟨176385, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨176351, by decide⟩,⟨176374, by decide⟩,⟨176384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20826_176385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20826 ⟨176385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20826
    ⟨176385, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨176351, by decide⟩,⟨176374, by decide⟩,⟨176384, by decide⟩]) unmarked_context_12_20826_176385 node_context_12_20826_176385
  intro a
  fin_cases a
  · exact context_13_83304_3444
  · exact context_13_83305_176351
  · exact context_13_83306_176374
  · exact context_13_83307_176384

theorem selected_cut_05758 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 83308) = some ⟨13, 1, 0, 3444, 83308, 1, 16384⟩ := by
  decide +kernel

theorem context_13_83308_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83308 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 83308 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 83308, 1, 16384⟩
    (by decide) selected_cut_05758

theorem selected_cut_05759 : selected 8 ⟨176403, by decide⟩
    (prefixPartial 13 83309) = some ⟨13, 2, 0, 176403, 83309, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_83309_176403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83309 ⟨176403, by decide⟩ :=
  accepted_of_selected 13 83309 ⟨176403, by decide⟩ ⟨13, 2, 0, 176403, 83309, 1325, 16384⟩
    (by decide) selected_cut_05759

theorem selected_cut_05760 : selected 8 ⟨176427, by decide⟩
    (prefixPartial 13 83310) = some ⟨13, 2, 0, 176427, 83310, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_83310_176427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83310 ⟨176427, by decide⟩ :=
  accepted_of_selected 13 83310 ⟨176427, by decide⟩ ⟨13, 2, 0, 176427, 83310, 2133, 16384⟩
    (by decide) selected_cut_05760

theorem selected_cut_05761 : selected 8 ⟨176435, by decide⟩
    (prefixPartial 13 83311) = some ⟨13, 2, 0, 176435, 83311, 945, 16384⟩ := by
  decide +kernel

theorem context_13_83311_176435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83311 ⟨176435, by decide⟩ :=
  accepted_of_selected 13 83311 ⟨176435, by decide⟩ ⟨13, 2, 0, 176435, 83311, 945, 16384⟩
    (by decide) selected_cut_05761

theorem unmarked_context_12_20827_176436 : frontier 9 ⟨176436, by decide⟩
    (prefixCache 12 20827) (prefixPartial 12 20827) = false := by
  decide +kernel

theorem node_context_12_20827_176436 : EJMOriginalGlobalDAGData.nodes 9 ⟨176436, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨176403, by decide⟩,⟨176427, by decide⟩,⟨176435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20827_176436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20827 ⟨176436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20827
    ⟨176436, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨176403, by decide⟩,⟨176427, by decide⟩,⟨176435, by decide⟩]) unmarked_context_12_20827_176436 node_context_12_20827_176436
  intro a
  fin_cases a
  · exact context_13_83308_3444
  · exact context_13_83309_176403
  · exact context_13_83310_176427
  · exact context_13_83311_176435

theorem unmarked_context_11_5206_176437 : frontier 10 ⟨176437, by decide⟩
    (prefixCache 11 5206) (prefixPartial 11 5206) = false := by
  decide +kernel

theorem node_context_11_5206_176437 : EJMOriginalGlobalDAGData.nodes 10 ⟨176437, by decide⟩ =
    .split (coordinate 11) (![⟨176268, by decide⟩,⟨176336, by decide⟩,⟨176385, by decide⟩,⟨176436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5206_176437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5206 ⟨176437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5206
    ⟨176437, by decide⟩ (by decide) (![⟨176268, by decide⟩,⟨176336, by decide⟩,⟨176385, by decide⟩,⟨176436, by decide⟩]) unmarked_context_11_5206_176437 node_context_11_5206_176437
  intro a
  fin_cases a
  · exact context_12_20824_176268
  · exact context_12_20825_176336
  · exact context_12_20826_176385
  · exact context_12_20827_176436

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
