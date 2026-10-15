/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover319
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_105009_780335 : frontier 9 ⟨780335, by decide⟩
    (prefixCache 12 105009) (prefixPartial 12 105009) = false := by
  decide +kernel

theorem node_context_12_105009_780335 : EJMOriginalGlobalDAGData.nodes 9 ⟨780335, by decide⟩ =
    .split (coordinate 12) (![⟨780258, by decide⟩,⟨780303, by decide⟩,⟨780318, by decide⟩,⟨780334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105009_780335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105009 ⟨780335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105009
    ⟨780335, by decide⟩ (by decide) (![⟨780258, by decide⟩,⟨780303, by decide⟩,⟨780318, by decide⟩,⟨780334, by decide⟩]) unmarked_context_12_105009_780335 node_context_12_105009_780335
  intro a
  fin_cases a
  · exact context_13_420036_780258
  · exact context_13_420037_780303
  · exact context_13_420038_780318
  · exact context_13_420039_780334

theorem selected_cut_30724 : selected 8 ⟨780348, by decide⟩
    (prefixPartial 13 420040) = some ⟨13, 2, 0, 780348, 420040, 741, 16384⟩ := by
  decide +kernel

theorem context_13_420040_780348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420040 ⟨780348, by decide⟩ :=
  accepted_of_selected 13 420040 ⟨780348, by decide⟩ ⟨13, 2, 0, 780348, 420040, 741, 16384⟩
    (by decide) selected_cut_30724

theorem selected_cut_30725 : selected 8 ⟨780376, by decide⟩
    (prefixPartial 13 420041) = some ⟨13, 2, 0, 780376, 420041, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_420041_780376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420041 ⟨780376, by decide⟩ :=
  accepted_of_selected 13 420041 ⟨780376, by decide⟩ ⟨13, 2, 0, 780376, 420041, 1825, 16384⟩
    (by decide) selected_cut_30725

theorem selected_cut_30726 : selected 8 ⟨780389, by decide⟩
    (prefixPartial 13 420042) = some ⟨13, 2, 0, 780389, 420042, 705, 16384⟩ := by
  decide +kernel

theorem context_13_420042_780389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420042 ⟨780389, by decide⟩ :=
  accepted_of_selected 13 420042 ⟨780389, by decide⟩ ⟨13, 2, 0, 780389, 420042, 705, 16384⟩
    (by decide) selected_cut_30726

theorem selected_cut_30727 : selected 8 ⟨780400, by decide⟩
    (prefixPartial 13 420043) = some ⟨13, 2, 0, 780400, 420043, 877, 16384⟩ := by
  decide +kernel

theorem context_13_420043_780400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420043 ⟨780400, by decide⟩ :=
  accepted_of_selected 13 420043 ⟨780400, by decide⟩ ⟨13, 2, 0, 780400, 420043, 877, 16384⟩
    (by decide) selected_cut_30727

theorem unmarked_context_12_105010_780401 : frontier 9 ⟨780401, by decide⟩
    (prefixCache 12 105010) (prefixPartial 12 105010) = false := by
  decide +kernel

theorem node_context_12_105010_780401 : EJMOriginalGlobalDAGData.nodes 9 ⟨780401, by decide⟩ =
    .split (coordinate 12) (![⟨780348, by decide⟩,⟨780376, by decide⟩,⟨780389, by decide⟩,⟨780400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105010_780401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105010 ⟨780401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105010
    ⟨780401, by decide⟩ (by decide) (![⟨780348, by decide⟩,⟨780376, by decide⟩,⟨780389, by decide⟩,⟨780400, by decide⟩]) unmarked_context_12_105010_780401 node_context_12_105010_780401
  intro a
  fin_cases a
  · exact context_13_420040_780348
  · exact context_13_420041_780376
  · exact context_13_420042_780389
  · exact context_13_420043_780400

theorem selected_cut_30728 : selected 8 ⟨780423, by decide⟩
    (prefixPartial 13 420044) = some ⟨13, 2, 0, 780423, 420044, 933, 16384⟩ := by
  decide +kernel

theorem context_13_420044_780423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420044 ⟨780423, by decide⟩ :=
  accepted_of_selected 13 420044 ⟨780423, by decide⟩ ⟨13, 2, 0, 780423, 420044, 933, 16384⟩
    (by decide) selected_cut_30728

theorem selected_cut_30729 : selected 8 ⟨780468, by decide⟩
    (prefixPartial 13 420045) = some ⟨13, 2, 0, 780468, 420045, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_420045_780468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420045 ⟨780468, by decide⟩ :=
  accepted_of_selected 13 420045 ⟨780468, by decide⟩ ⟨13, 2, 0, 780468, 420045, 2213, 16384⟩
    (by decide) selected_cut_30729

theorem selected_cut_30730 : selected 8 ⟨780492, by decide⟩
    (prefixPartial 13 420046) = some ⟨13, 2, 0, 780492, 420046, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_420046_780492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420046 ⟨780492, by decide⟩ :=
  accepted_of_selected 13 420046 ⟨780492, by decide⟩ ⟨13, 2, 0, 780492, 420046, 1033, 16384⟩
    (by decide) selected_cut_30730

theorem selected_cut_30731 : selected 8 ⟨780504, by decide⟩
    (prefixPartial 13 420047) = some ⟨13, 2, 0, 780504, 420047, 969, 16384⟩ := by
  decide +kernel

theorem context_13_420047_780504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420047 ⟨780504, by decide⟩ :=
  accepted_of_selected 13 420047 ⟨780504, by decide⟩ ⟨13, 2, 0, 780504, 420047, 969, 16384⟩
    (by decide) selected_cut_30731

theorem unmarked_context_12_105011_780505 : frontier 9 ⟨780505, by decide⟩
    (prefixCache 12 105011) (prefixPartial 12 105011) = false := by
  decide +kernel

theorem node_context_12_105011_780505 : EJMOriginalGlobalDAGData.nodes 9 ⟨780505, by decide⟩ =
    .split (coordinate 12) (![⟨780423, by decide⟩,⟨780468, by decide⟩,⟨780492, by decide⟩,⟨780504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105011_780505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105011 ⟨780505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105011
    ⟨780505, by decide⟩ (by decide) (![⟨780423, by decide⟩,⟨780468, by decide⟩,⟨780492, by decide⟩,⟨780504, by decide⟩]) unmarked_context_12_105011_780505 node_context_12_105011_780505
  intro a
  fin_cases a
  · exact context_13_420044_780423
  · exact context_13_420045_780468
  · exact context_13_420046_780492
  · exact context_13_420047_780504

theorem unmarked_context_11_26252_780506 : frontier 10 ⟨780506, by decide⟩
    (prefixCache 11 26252) (prefixPartial 11 26252) = false := by
  decide +kernel

theorem node_context_11_26252_780506 : EJMOriginalGlobalDAGData.nodes 10 ⟨780506, by decide⟩ =
    .split (coordinate 11) (![⟨780236, by decide⟩,⟨780335, by decide⟩,⟨780401, by decide⟩,⟨780505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26252_780506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26252 ⟨780506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26252
    ⟨780506, by decide⟩ (by decide) (![⟨780236, by decide⟩,⟨780335, by decide⟩,⟨780401, by decide⟩,⟨780505, by decide⟩]) unmarked_context_11_26252_780506 node_context_11_26252_780506
  intro a
  fin_cases a
  · exact context_12_105008_780236
  · exact context_12_105009_780335
  · exact context_12_105010_780401
  · exact context_12_105011_780505

theorem selected_cut_30732 : selected 8 ⟨780520, by decide⟩
    (prefixPartial 13 420048) = some ⟨13, 2, 0, 780520, 420048, 657, 16384⟩ := by
  decide +kernel

theorem context_13_420048_780520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420048 ⟨780520, by decide⟩ :=
  accepted_of_selected 13 420048 ⟨780520, by decide⟩ ⟨13, 2, 0, 780520, 420048, 657, 16384⟩
    (by decide) selected_cut_30732

theorem selected_cut_30733 : selected 8 ⟨780556, by decide⟩
    (prefixPartial 13 420049) = some ⟨13, 2, 0, 780556, 420049, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_420049_780556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420049 ⟨780556, by decide⟩ :=
  accepted_of_selected 13 420049 ⟨780556, by decide⟩ ⟨13, 2, 0, 780556, 420049, 1853, 16384⟩
    (by decide) selected_cut_30733

theorem selected_cut_30734 : selected 8 ⟨780573, by decide⟩
    (prefixPartial 13 420050) = some ⟨13, 2, 0, 780573, 420050, 985, 16384⟩ := by
  decide +kernel

theorem context_13_420050_780573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420050 ⟨780573, by decide⟩ :=
  accepted_of_selected 13 420050 ⟨780573, by decide⟩ ⟨13, 2, 0, 780573, 420050, 985, 16384⟩
    (by decide) selected_cut_30734

theorem selected_cut_30735 : selected 8 ⟨780588, by decide⟩
    (prefixPartial 13 420051) = some ⟨13, 2, 0, 780588, 420051, 905, 16384⟩ := by
  decide +kernel

theorem context_13_420051_780588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420051 ⟨780588, by decide⟩ :=
  accepted_of_selected 13 420051 ⟨780588, by decide⟩ ⟨13, 2, 0, 780588, 420051, 905, 16384⟩
    (by decide) selected_cut_30735

theorem unmarked_context_12_105012_780589 : frontier 9 ⟨780589, by decide⟩
    (prefixCache 12 105012) (prefixPartial 12 105012) = false := by
  decide +kernel

theorem node_context_12_105012_780589 : EJMOriginalGlobalDAGData.nodes 9 ⟨780589, by decide⟩ =
    .split (coordinate 12) (![⟨780520, by decide⟩,⟨780556, by decide⟩,⟨780573, by decide⟩,⟨780588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105012_780589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105012 ⟨780589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105012
    ⟨780589, by decide⟩ (by decide) (![⟨780520, by decide⟩,⟨780556, by decide⟩,⟨780573, by decide⟩,⟨780588, by decide⟩]) unmarked_context_12_105012_780589 node_context_12_105012_780589
  intro a
  fin_cases a
  · exact context_13_420048_780520
  · exact context_13_420049_780556
  · exact context_13_420050_780573
  · exact context_13_420051_780588

theorem selected_cut_30736 : selected 8 ⟨780606, by decide⟩
    (prefixPartial 13 420052) = some ⟨13, 2, 0, 780606, 420052, 689, 16384⟩ := by
  decide +kernel

theorem context_13_420052_780606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420052 ⟨780606, by decide⟩ :=
  accepted_of_selected 13 420052 ⟨780606, by decide⟩ ⟨13, 2, 0, 780606, 420052, 689, 16384⟩
    (by decide) selected_cut_30736

theorem selected_cut_30737 : selected 8 ⟨780640, by decide⟩
    (prefixPartial 13 420053) = some ⟨13, 2, 0, 780640, 420053, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_420053_780640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420053 ⟨780640, by decide⟩ :=
  accepted_of_selected 13 420053 ⟨780640, by decide⟩ ⟨13, 2, 0, 780640, 420053, 1849, 16384⟩
    (by decide) selected_cut_30737

theorem selected_cut_30738 : selected 8 ⟨780652, by decide⟩
    (prefixPartial 13 420054) = some ⟨13, 2, 0, 780652, 420054, 805, 16384⟩ := by
  decide +kernel

theorem context_13_420054_780652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420054 ⟨780652, by decide⟩ :=
  accepted_of_selected 13 420054 ⟨780652, by decide⟩ ⟨13, 2, 0, 780652, 420054, 805, 16384⟩
    (by decide) selected_cut_30738

theorem selected_cut_30739 : selected 8 ⟨780667, by decide⟩
    (prefixPartial 13 420055) = some ⟨13, 2, 0, 780667, 420055, 949, 16384⟩ := by
  decide +kernel

theorem context_13_420055_780667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420055 ⟨780667, by decide⟩ :=
  accepted_of_selected 13 420055 ⟨780667, by decide⟩ ⟨13, 2, 0, 780667, 420055, 949, 16384⟩
    (by decide) selected_cut_30739

theorem unmarked_context_12_105013_780668 : frontier 9 ⟨780668, by decide⟩
    (prefixCache 12 105013) (prefixPartial 12 105013) = false := by
  decide +kernel

theorem node_context_12_105013_780668 : EJMOriginalGlobalDAGData.nodes 9 ⟨780668, by decide⟩ =
    .split (coordinate 12) (![⟨780606, by decide⟩,⟨780640, by decide⟩,⟨780652, by decide⟩,⟨780667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105013_780668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105013 ⟨780668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105013
    ⟨780668, by decide⟩ (by decide) (![⟨780606, by decide⟩,⟨780640, by decide⟩,⟨780652, by decide⟩,⟨780667, by decide⟩]) unmarked_context_12_105013_780668 node_context_12_105013_780668
  intro a
  fin_cases a
  · exact context_13_420052_780606
  · exact context_13_420053_780640
  · exact context_13_420054_780652
  · exact context_13_420055_780667

theorem selected_cut_30740 : selected 9 ⟨780744, by decide⟩
    (prefixPartial 12 105014) = some ⟨12, 2, 0, 780744, 105014, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_105014_780744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105014 ⟨780744, by decide⟩ :=
  accepted_of_selected 12 105014 ⟨780744, by decide⟩ ⟨12, 2, 0, 780744, 105014, 3881, 65536⟩
    (by decide) selected_cut_30740

theorem selected_cut_30741 : selected 8 ⟨780758, by decide⟩
    (prefixPartial 13 420060) = some ⟨13, 2, 0, 780758, 420060, 593, 16384⟩ := by
  decide +kernel

theorem context_13_420060_780758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420060 ⟨780758, by decide⟩ :=
  accepted_of_selected 13 420060 ⟨780758, by decide⟩ ⟨13, 2, 0, 780758, 420060, 593, 16384⟩
    (by decide) selected_cut_30741

theorem selected_cut_30742 : selected 8 ⟨780810, by decide⟩
    (prefixPartial 13 420061) = some ⟨13, 2, 0, 780810, 420061, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_420061_780810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420061 ⟨780810, by decide⟩ :=
  accepted_of_selected 13 420061 ⟨780810, by decide⟩ ⟨13, 2, 0, 780810, 420061, 1973, 16384⟩
    (by decide) selected_cut_30742

theorem selected_cut_30743 : selected 8 ⟨780839, by decide⟩
    (prefixPartial 13 420062) = some ⟨13, 2, 0, 780839, 420062, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_420062_780839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420062 ⟨780839, by decide⟩ :=
  accepted_of_selected 13 420062 ⟨780839, by decide⟩ ⟨13, 2, 0, 780839, 420062, 1209, 16384⟩
    (by decide) selected_cut_30743

theorem selected_cut_30744 : selected 8 ⟨780851, by decide⟩
    (prefixPartial 13 420063) = some ⟨13, 2, 0, 780851, 420063, 833, 16384⟩ := by
  decide +kernel

theorem context_13_420063_780851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420063 ⟨780851, by decide⟩ :=
  accepted_of_selected 13 420063 ⟨780851, by decide⟩ ⟨13, 2, 0, 780851, 420063, 833, 16384⟩
    (by decide) selected_cut_30744

theorem unmarked_context_12_105015_780852 : frontier 9 ⟨780852, by decide⟩
    (prefixCache 12 105015) (prefixPartial 12 105015) = false := by
  decide +kernel

theorem node_context_12_105015_780852 : EJMOriginalGlobalDAGData.nodes 9 ⟨780852, by decide⟩ =
    .split (coordinate 12) (![⟨780758, by decide⟩,⟨780810, by decide⟩,⟨780839, by decide⟩,⟨780851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105015_780852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105015 ⟨780852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105015
    ⟨780852, by decide⟩ (by decide) (![⟨780758, by decide⟩,⟨780810, by decide⟩,⟨780839, by decide⟩,⟨780851, by decide⟩]) unmarked_context_12_105015_780852 node_context_12_105015_780852
  intro a
  fin_cases a
  · exact context_13_420060_780758
  · exact context_13_420061_780810
  · exact context_13_420062_780839
  · exact context_13_420063_780851

theorem unmarked_context_11_26253_780853 : frontier 10 ⟨780853, by decide⟩
    (prefixCache 11 26253) (prefixPartial 11 26253) = false := by
  decide +kernel

theorem node_context_11_26253_780853 : EJMOriginalGlobalDAGData.nodes 10 ⟨780853, by decide⟩ =
    .split (coordinate 11) (![⟨780589, by decide⟩,⟨780668, by decide⟩,⟨780744, by decide⟩,⟨780852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26253_780853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26253 ⟨780853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26253
    ⟨780853, by decide⟩ (by decide) (![⟨780589, by decide⟩,⟨780668, by decide⟩,⟨780744, by decide⟩,⟨780852, by decide⟩]) unmarked_context_11_26253_780853 node_context_11_26253_780853
  intro a
  fin_cases a
  · exact context_12_105012_780589
  · exact context_12_105013_780668
  · exact context_12_105014_780744
  · exact context_12_105015_780852

theorem selected_cut_30745 : selected 9 ⟨780913, by decide⟩
    (prefixPartial 12 105016) = some ⟨12, 2, 0, 780913, 105016, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_105016_780913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105016 ⟨780913, by decide⟩ :=
  accepted_of_selected 12 105016 ⟨780913, by decide⟩ ⟨12, 2, 0, 780913, 105016, 3429, 65536⟩
    (by decide) selected_cut_30745

theorem selected_cut_30746 : selected 9 ⟨780979, by decide⟩
    (prefixPartial 12 105017) = some ⟨12, 2, 0, 780979, 105017, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_105017_780979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105017 ⟨780979, by decide⟩ :=
  accepted_of_selected 12 105017 ⟨780979, by decide⟩ ⟨12, 2, 0, 780979, 105017, 3753, 65536⟩
    (by decide) selected_cut_30746

theorem selected_cut_30747 : selected 9 ⟨662655, by decide⟩
    (prefixPartial 12 105018) = some ⟨12, 1, 0, 662655, 105018, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105018_662655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105018 ⟨662655, by decide⟩ :=
  accepted_of_selected 12 105018 ⟨662655, by decide⟩ ⟨12, 1, 0, 662655, 105018, 1, 65536⟩
    (by decide) selected_cut_30747

theorem selected_cut_30748 : selected 9 ⟨781037, by decide⟩
    (prefixPartial 12 105019) = some ⟨12, 2, 0, 781037, 105019, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_105019_781037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105019 ⟨781037, by decide⟩ :=
  accepted_of_selected 12 105019 ⟨781037, by decide⟩ ⟨12, 2, 0, 781037, 105019, 3989, 65536⟩
    (by decide) selected_cut_30748

theorem unmarked_context_11_26254_781038 : frontier 10 ⟨781038, by decide⟩
    (prefixCache 11 26254) (prefixPartial 11 26254) = false := by
  decide +kernel

theorem node_context_11_26254_781038 : EJMOriginalGlobalDAGData.nodes 10 ⟨781038, by decide⟩ =
    .split (coordinate 11) (![⟨780913, by decide⟩,⟨780979, by decide⟩,⟨662655, by decide⟩,⟨781037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26254_781038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26254 ⟨781038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26254
    ⟨781038, by decide⟩ (by decide) (![⟨780913, by decide⟩,⟨780979, by decide⟩,⟨662655, by decide⟩,⟨781037, by decide⟩]) unmarked_context_11_26254_781038 node_context_11_26254_781038
  intro a
  fin_cases a
  · exact context_12_105016_780913
  · exact context_12_105017_780979
  · exact context_12_105018_662655
  · exact context_12_105019_781037

theorem selected_cut_30749 : selected 9 ⟨781099, by decide⟩
    (prefixPartial 12 105020) = some ⟨12, 2, 0, 781099, 105020, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_105020_781099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105020 ⟨781099, by decide⟩ :=
  accepted_of_selected 12 105020 ⟨781099, by decide⟩ ⟨12, 2, 0, 781099, 105020, 3705, 65536⟩
    (by decide) selected_cut_30749

theorem selected_cut_30750 : selected 9 ⟨781169, by decide⟩
    (prefixPartial 12 105021) = some ⟨12, 2, 0, 781169, 105021, 3853, 65536⟩ := by
  decide +kernel

theorem context_12_105021_781169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105021 ⟨781169, by decide⟩ :=
  accepted_of_selected 12 105021 ⟨781169, by decide⟩ ⟨12, 2, 0, 781169, 105021, 3853, 65536⟩
    (by decide) selected_cut_30750

theorem selected_cut_30751 : selected 9 ⟨781234, by decide⟩
    (prefixPartial 12 105022) = some ⟨12, 2, 0, 781234, 105022, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_105022_781234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105022 ⟨781234, by decide⟩ :=
  accepted_of_selected 12 105022 ⟨781234, by decide⟩ ⟨12, 2, 0, 781234, 105022, 3409, 65536⟩
    (by decide) selected_cut_30751

theorem selected_cut_30752 : selected 9 ⟨781290, by decide⟩
    (prefixPartial 12 105023) = some ⟨12, 2, 0, 781290, 105023, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_105023_781290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105023 ⟨781290, by decide⟩ :=
  accepted_of_selected 12 105023 ⟨781290, by decide⟩ ⟨12, 2, 0, 781290, 105023, 3913, 65536⟩
    (by decide) selected_cut_30752

theorem unmarked_context_11_26255_781291 : frontier 10 ⟨781291, by decide⟩
    (prefixCache 11 26255) (prefixPartial 11 26255) = false := by
  decide +kernel

theorem node_context_11_26255_781291 : EJMOriginalGlobalDAGData.nodes 10 ⟨781291, by decide⟩ =
    .split (coordinate 11) (![⟨781099, by decide⟩,⟨781169, by decide⟩,⟨781234, by decide⟩,⟨781290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26255_781291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26255 ⟨781291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26255
    ⟨781291, by decide⟩ (by decide) (![⟨781099, by decide⟩,⟨781169, by decide⟩,⟨781234, by decide⟩,⟨781290, by decide⟩]) unmarked_context_11_26255_781291 node_context_11_26255_781291
  intro a
  fin_cases a
  · exact context_12_105020_781099
  · exact context_12_105021_781169
  · exact context_12_105022_781234
  · exact context_12_105023_781290

theorem unmarked_context_10_6563_781292 : frontier 11 ⟨781292, by decide⟩
    (prefixCache 10 6563) (prefixPartial 10 6563) = false := by
  decide +kernel

theorem node_context_10_6563_781292 : EJMOriginalGlobalDAGData.nodes 11 ⟨781292, by decide⟩ =
    .split (coordinate 10) (![⟨780506, by decide⟩,⟨780853, by decide⟩,⟨781038, by decide⟩,⟨781291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6563_781292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6563 ⟨781292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6563
    ⟨781292, by decide⟩ (by decide) (![⟨780506, by decide⟩,⟨780853, by decide⟩,⟨781038, by decide⟩,⟨781291, by decide⟩]) unmarked_context_10_6563_781292 node_context_10_6563_781292
  intro a
  fin_cases a
  · exact context_11_26252_780506
  · exact context_11_26253_780853
  · exact context_11_26254_781038
  · exact context_11_26255_781291

theorem unmarked_context_9_1640_781293 : frontier 12 ⟨781293, by decide⟩
    (prefixCache 9 1640) (prefixPartial 9 1640) = false := by
  decide +kernel

theorem node_context_9_1640_781293 : EJMOriginalGlobalDAGData.nodes 12 ⟨781293, by decide⟩ =
    .split (coordinate 9) (![⟨777810, by decide⟩,⟨779334, by decide⟩,⟨780162, by decide⟩,⟨781292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1640_781293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1640 ⟨781293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1640
    ⟨781293, by decide⟩ (by decide) (![⟨777810, by decide⟩,⟨779334, by decide⟩,⟨780162, by decide⟩,⟨781292, by decide⟩]) unmarked_context_9_1640_781293 node_context_9_1640_781293
  intro a
  fin_cases a
  · exact context_10_6560_777810
  · exact context_10_6561_779334
  · exact context_10_6562_780162
  · exact context_10_6563_781292

theorem selected_cut_30753 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 6564) = some ⟨10, 1, 0, 3442, 6564, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6564_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6564 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 6564 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 6564, 1, 1048576⟩
    (by decide) selected_cut_30753

theorem selected_cut_30754 : selected 9 ⟨781347, by decide⟩
    (prefixPartial 12 105040) = some ⟨12, 2, 0, 781347, 105040, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_105040_781347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105040 ⟨781347, by decide⟩ :=
  accepted_of_selected 12 105040 ⟨781347, by decide⟩ ⟨12, 2, 0, 781347, 105040, 1657, 65536⟩
    (by decide) selected_cut_30754

theorem selected_cut_30755 : selected 9 ⟨781415, by decide⟩
    (prefixPartial 12 105041) = some ⟨12, 2, 0, 781415, 105041, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_105041_781415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105041 ⟨781415, by decide⟩ :=
  accepted_of_selected 12 105041 ⟨781415, by decide⟩ ⟨12, 2, 0, 781415, 105041, 2989, 65536⟩
    (by decide) selected_cut_30755

theorem selected_cut_30756 : selected 9 ⟨781465, by decide⟩
    (prefixPartial 12 105042) = some ⟨12, 2, 0, 781465, 105042, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_105042_781465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105042 ⟨781465, by decide⟩ :=
  accepted_of_selected 12 105042 ⟨781465, by decide⟩ ⟨12, 2, 0, 781465, 105042, 2713, 65536⟩
    (by decide) selected_cut_30756

theorem selected_cut_30757 : selected 9 ⟨781534, by decide⟩
    (prefixPartial 12 105043) = some ⟨12, 2, 0, 781534, 105043, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_105043_781534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105043 ⟨781534, by decide⟩ :=
  accepted_of_selected 12 105043 ⟨781534, by decide⟩ ⟨12, 2, 0, 781534, 105043, 3149, 65536⟩
    (by decide) selected_cut_30757

theorem unmarked_context_11_26260_781535 : frontier 10 ⟨781535, by decide⟩
    (prefixCache 11 26260) (prefixPartial 11 26260) = false := by
  decide +kernel

theorem node_context_11_26260_781535 : EJMOriginalGlobalDAGData.nodes 10 ⟨781535, by decide⟩ =
    .split (coordinate 11) (![⟨781347, by decide⟩,⟨781415, by decide⟩,⟨781465, by decide⟩,⟨781534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26260_781535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26260 ⟨781535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26260
    ⟨781535, by decide⟩ (by decide) (![⟨781347, by decide⟩,⟨781415, by decide⟩,⟨781465, by decide⟩,⟨781534, by decide⟩]) unmarked_context_11_26260_781535 node_context_11_26260_781535
  intro a
  fin_cases a
  · exact context_12_105040_781347
  · exact context_12_105041_781415
  · exact context_12_105042_781465
  · exact context_12_105043_781534

theorem selected_cut_30758 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 105044) = some ⟨12, 1, 0, 895, 105044, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105044_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105044 ⟨895, by decide⟩ :=
  accepted_of_selected 12 105044 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 105044, 1, 65536⟩
    (by decide) selected_cut_30758

theorem selected_cut_30759 : selected 9 ⟨781573, by decide⟩
    (prefixPartial 12 105045) = some ⟨12, 2, 0, 781573, 105045, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_105045_781573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105045 ⟨781573, by decide⟩ :=
  accepted_of_selected 12 105045 ⟨781573, by decide⟩ ⟨12, 2, 0, 781573, 105045, 1377, 65536⟩
    (by decide) selected_cut_30759

theorem selected_cut_30760 : selected 9 ⟨781616, by decide⟩
    (prefixPartial 12 105046) = some ⟨12, 2, 0, 781616, 105046, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_105046_781616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105046 ⟨781616, by decide⟩ :=
  accepted_of_selected 12 105046 ⟨781616, by decide⟩ ⟨12, 2, 0, 781616, 105046, 2421, 65536⟩
    (by decide) selected_cut_30760

theorem selected_cut_30761 : selected 9 ⟨781665, by decide⟩
    (prefixPartial 12 105047) = some ⟨12, 2, 0, 781665, 105047, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_105047_781665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105047 ⟨781665, by decide⟩ :=
  accepted_of_selected 12 105047 ⟨781665, by decide⟩ ⟨12, 2, 0, 781665, 105047, 2653, 65536⟩
    (by decide) selected_cut_30761

theorem unmarked_context_11_26261_781666 : frontier 10 ⟨781666, by decide⟩
    (prefixCache 11 26261) (prefixPartial 11 26261) = false := by
  decide +kernel

theorem node_context_11_26261_781666 : EJMOriginalGlobalDAGData.nodes 10 ⟨781666, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨781573, by decide⟩,⟨781616, by decide⟩,⟨781665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26261_781666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26261 ⟨781666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26261
    ⟨781666, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨781573, by decide⟩,⟨781616, by decide⟩,⟨781665, by decide⟩]) unmarked_context_11_26261_781666 node_context_11_26261_781666
  intro a
  fin_cases a
  · exact context_12_105044_895
  · exact context_12_105045_781573
  · exact context_12_105046_781616
  · exact context_12_105047_781665

theorem selected_cut_30762 : selected 10 ⟨781708, by decide⟩
    (prefixPartial 11 26262) = some ⟨11, 2, 0, 781708, 26262, 2609, 262144⟩ := by
  decide +kernel

theorem context_11_26262_781708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26262 ⟨781708, by decide⟩ :=
  accepted_of_selected 11 26262 ⟨781708, by decide⟩ ⟨11, 2, 0, 781708, 26262, 2609, 262144⟩
    (by decide) selected_cut_30762

theorem selected_cut_30763 : selected 10 ⟨781748, by decide⟩
    (prefixPartial 11 26263) = some ⟨11, 2, 0, 781748, 26263, 1685, 262144⟩ := by
  decide +kernel

theorem context_11_26263_781748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26263 ⟨781748, by decide⟩ :=
  accepted_of_selected 11 26263 ⟨781748, by decide⟩ ⟨11, 2, 0, 781748, 26263, 1685, 262144⟩
    (by decide) selected_cut_30763

theorem unmarked_context_10_6565_781749 : frontier 11 ⟨781749, by decide⟩
    (prefixCache 10 6565) (prefixPartial 10 6565) = false := by
  decide +kernel

theorem node_context_10_6565_781749 : EJMOriginalGlobalDAGData.nodes 11 ⟨781749, by decide⟩ =
    .split (coordinate 10) (![⟨781535, by decide⟩,⟨781666, by decide⟩,⟨781708, by decide⟩,⟨781748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6565_781749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6565 ⟨781749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6565
    ⟨781749, by decide⟩ (by decide) (![⟨781535, by decide⟩,⟨781666, by decide⟩,⟨781708, by decide⟩,⟨781748, by decide⟩]) unmarked_context_10_6565_781749 node_context_10_6565_781749
  intro a
  fin_cases a
  · exact context_11_26260_781535
  · exact context_11_26261_781666
  · exact context_11_26262_781708
  · exact context_11_26263_781748

theorem selected_cut_30764 : selected 9 ⟨781788, by decide⟩
    (prefixPartial 12 105056) = some ⟨12, 2, 0, 781788, 105056, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_105056_781788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105056 ⟨781788, by decide⟩ :=
  accepted_of_selected 12 105056 ⟨781788, by decide⟩ ⟨12, 2, 0, 781788, 105056, 2145, 65536⟩
    (by decide) selected_cut_30764

theorem selected_cut_30765 : selected 9 ⟨781828, by decide⟩
    (prefixPartial 12 105057) = some ⟨12, 2, 0, 781828, 105057, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_105057_781828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105057 ⟨781828, by decide⟩ :=
  accepted_of_selected 12 105057 ⟨781828, by decide⟩ ⟨12, 2, 0, 781828, 105057, 2109, 65536⟩
    (by decide) selected_cut_30765

theorem selected_cut_30766 : selected 9 ⟨781859, by decide⟩
    (prefixPartial 12 105058) = some ⟨12, 2, 0, 781859, 105058, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_105058_781859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105058 ⟨781859, by decide⟩ :=
  accepted_of_selected 12 105058 ⟨781859, by decide⟩ ⟨12, 2, 0, 781859, 105058, 1793, 65536⟩
    (by decide) selected_cut_30766

theorem selected_cut_30767 : selected 9 ⟨781897, by decide⟩
    (prefixPartial 12 105059) = some ⟨12, 2, 0, 781897, 105059, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_105059_781897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105059 ⟨781897, by decide⟩ :=
  accepted_of_selected 12 105059 ⟨781897, by decide⟩ ⟨12, 2, 0, 781897, 105059, 2293, 65536⟩
    (by decide) selected_cut_30767

theorem unmarked_context_11_26264_781898 : frontier 10 ⟨781898, by decide⟩
    (prefixCache 11 26264) (prefixPartial 11 26264) = false := by
  decide +kernel

theorem node_context_11_26264_781898 : EJMOriginalGlobalDAGData.nodes 10 ⟨781898, by decide⟩ =
    .split (coordinate 11) (![⟨781788, by decide⟩,⟨781828, by decide⟩,⟨781859, by decide⟩,⟨781897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26264_781898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26264 ⟨781898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26264
    ⟨781898, by decide⟩ (by decide) (![⟨781788, by decide⟩,⟨781828, by decide⟩,⟨781859, by decide⟩,⟨781897, by decide⟩]) unmarked_context_11_26264_781898 node_context_11_26264_781898
  intro a
  fin_cases a
  · exact context_12_105056_781788
  · exact context_12_105057_781828
  · exact context_12_105058_781859
  · exact context_12_105059_781897

theorem selected_cut_30768 : selected 9 ⟨781942, by decide⟩
    (prefixPartial 12 105060) = some ⟨12, 2, 0, 781942, 105060, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_105060_781942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105060 ⟨781942, by decide⟩ :=
  accepted_of_selected 12 105060 ⟨781942, by decide⟩ ⟨12, 2, 0, 781942, 105060, 2245, 65536⟩
    (by decide) selected_cut_30768

theorem selected_cut_30769 : selected 9 ⟨781975, by decide⟩
    (prefixPartial 12 105061) = some ⟨12, 2, 0, 781975, 105061, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_105061_781975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105061 ⟨781975, by decide⟩ :=
  accepted_of_selected 12 105061 ⟨781975, by decide⟩ ⟨12, 2, 0, 781975, 105061, 1793, 65536⟩
    (by decide) selected_cut_30769

theorem selected_cut_30770 : selected 9 ⟨782004, by decide⟩
    (prefixPartial 12 105062) = some ⟨12, 2, 0, 782004, 105062, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_105062_782004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105062 ⟨782004, by decide⟩ :=
  accepted_of_selected 12 105062 ⟨782004, by decide⟩ ⟨12, 2, 0, 782004, 105062, 1737, 65536⟩
    (by decide) selected_cut_30770

theorem selected_cut_30771 : selected 9 ⟨782047, by decide⟩
    (prefixPartial 12 105063) = some ⟨12, 2, 0, 782047, 105063, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_105063_782047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105063 ⟨782047, by decide⟩ :=
  accepted_of_selected 12 105063 ⟨782047, by decide⟩ ⟨12, 2, 0, 782047, 105063, 2061, 65536⟩
    (by decide) selected_cut_30771

theorem unmarked_context_11_26265_782048 : frontier 10 ⟨782048, by decide⟩
    (prefixCache 11 26265) (prefixPartial 11 26265) = false := by
  decide +kernel

theorem node_context_11_26265_782048 : EJMOriginalGlobalDAGData.nodes 10 ⟨782048, by decide⟩ =
    .split (coordinate 11) (![⟨781942, by decide⟩,⟨781975, by decide⟩,⟨782004, by decide⟩,⟨782047, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26265_782048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26265 ⟨782048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26265
    ⟨782048, by decide⟩ (by decide) (![⟨781942, by decide⟩,⟨781975, by decide⟩,⟨782004, by decide⟩,⟨782047, by decide⟩]) unmarked_context_11_26265_782048 node_context_11_26265_782048
  intro a
  fin_cases a
  · exact context_12_105060_781942
  · exact context_12_105061_781975
  · exact context_12_105062_782004
  · exact context_12_105063_782047

theorem selected_cut_30772 : selected 10 ⟨782050, by decide⟩
    (prefixPartial 11 26266) = some ⟨11, 2, 0, 782050, 26266, 5, 262144⟩ := by
  decide +kernel

theorem context_11_26266_782050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26266 ⟨782050, by decide⟩ :=
  accepted_of_selected 11 26266 ⟨782050, by decide⟩ ⟨11, 2, 0, 782050, 26266, 5, 262144⟩
    (by decide) selected_cut_30772

theorem selected_cut_30773 : selected 9 ⟨782084, by decide⟩
    (prefixPartial 12 105068) = some ⟨12, 2, 0, 782084, 105068, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_105068_782084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105068 ⟨782084, by decide⟩ :=
  accepted_of_selected 12 105068 ⟨782084, by decide⟩ ⟨12, 2, 0, 782084, 105068, 2073, 65536⟩
    (by decide) selected_cut_30773

theorem selected_cut_30774 : selected 9 ⟨782115, by decide⟩
    (prefixPartial 12 105069) = some ⟨12, 2, 0, 782115, 105069, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_105069_782115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105069 ⟨782115, by decide⟩ :=
  accepted_of_selected 12 105069 ⟨782115, by decide⟩ ⟨12, 2, 0, 782115, 105069, 1737, 65536⟩
    (by decide) selected_cut_30774

theorem selected_cut_30775 : selected 9 ⟨782140, by decide⟩
    (prefixPartial 12 105070) = some ⟨12, 2, 0, 782140, 105070, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_105070_782140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105070 ⟨782140, by decide⟩ :=
  accepted_of_selected 12 105070 ⟨782140, by decide⟩ ⟨12, 2, 0, 782140, 105070, 1517, 65536⟩
    (by decide) selected_cut_30775

theorem selected_cut_30776 : selected 9 ⟨782169, by decide⟩
    (prefixPartial 12 105071) = some ⟨12, 2, 0, 782169, 105071, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_105071_782169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105071 ⟨782169, by decide⟩ :=
  accepted_of_selected 12 105071 ⟨782169, by decide⟩ ⟨12, 2, 0, 782169, 105071, 1873, 65536⟩
    (by decide) selected_cut_30776

theorem unmarked_context_11_26267_782170 : frontier 10 ⟨782170, by decide⟩
    (prefixCache 11 26267) (prefixPartial 11 26267) = false := by
  decide +kernel

theorem node_context_11_26267_782170 : EJMOriginalGlobalDAGData.nodes 10 ⟨782170, by decide⟩ =
    .split (coordinate 11) (![⟨782084, by decide⟩,⟨782115, by decide⟩,⟨782140, by decide⟩,⟨782169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26267_782170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26267 ⟨782170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26267
    ⟨782170, by decide⟩ (by decide) (![⟨782084, by decide⟩,⟨782115, by decide⟩,⟨782140, by decide⟩,⟨782169, by decide⟩]) unmarked_context_11_26267_782170 node_context_11_26267_782170
  intro a
  fin_cases a
  · exact context_12_105068_782084
  · exact context_12_105069_782115
  · exact context_12_105070_782140
  · exact context_12_105071_782169

theorem unmarked_context_10_6566_782171 : frontier 11 ⟨782171, by decide⟩
    (prefixCache 10 6566) (prefixPartial 10 6566) = false := by
  decide +kernel

theorem node_context_10_6566_782171 : EJMOriginalGlobalDAGData.nodes 11 ⟨782171, by decide⟩ =
    .split (coordinate 10) (![⟨781898, by decide⟩,⟨782048, by decide⟩,⟨782050, by decide⟩,⟨782170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6566_782171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6566 ⟨782171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6566
    ⟨782171, by decide⟩ (by decide) (![⟨781898, by decide⟩,⟨782048, by decide⟩,⟨782050, by decide⟩,⟨782170, by decide⟩]) unmarked_context_10_6566_782171 node_context_10_6566_782171
  intro a
  fin_cases a
  · exact context_11_26264_781898
  · exact context_11_26265_782048
  · exact context_11_26266_782050
  · exact context_11_26267_782170

theorem selected_cut_30777 : selected 9 ⟨782208, by decide⟩
    (prefixPartial 12 105072) = some ⟨12, 2, 0, 782208, 105072, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_105072_782208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105072 ⟨782208, by decide⟩ :=
  accepted_of_selected 12 105072 ⟨782208, by decide⟩ ⟨12, 2, 0, 782208, 105072, 1709, 65536⟩
    (by decide) selected_cut_30777

theorem selected_cut_30778 : selected 9 ⟨782240, by decide⟩
    (prefixPartial 12 105073) = some ⟨12, 2, 0, 782240, 105073, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_105073_782240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105073 ⟨782240, by decide⟩ :=
  accepted_of_selected 12 105073 ⟨782240, by decide⟩ ⟨12, 2, 0, 782240, 105073, 1785, 65536⟩
    (by decide) selected_cut_30778

theorem selected_cut_30779 : selected 9 ⟨782265, by decide⟩
    (prefixPartial 12 105074) = some ⟨12, 2, 0, 782265, 105074, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_105074_782265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105074 ⟨782265, by decide⟩ :=
  accepted_of_selected 12 105074 ⟨782265, by decide⟩ ⟨12, 2, 0, 782265, 105074, 1525, 65536⟩
    (by decide) selected_cut_30779

theorem selected_cut_30780 : selected 9 ⟨782310, by decide⟩
    (prefixPartial 12 105075) = some ⟨12, 2, 0, 782310, 105075, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_105075_782310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105075 ⟨782310, by decide⟩ :=
  accepted_of_selected 12 105075 ⟨782310, by decide⟩ ⟨12, 2, 0, 782310, 105075, 1841, 65536⟩
    (by decide) selected_cut_30780

theorem unmarked_context_11_26268_782311 : frontier 10 ⟨782311, by decide⟩
    (prefixCache 11 26268) (prefixPartial 11 26268) = false := by
  decide +kernel

theorem node_context_11_26268_782311 : EJMOriginalGlobalDAGData.nodes 10 ⟨782311, by decide⟩ =
    .split (coordinate 11) (![⟨782208, by decide⟩,⟨782240, by decide⟩,⟨782265, by decide⟩,⟨782310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26268_782311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26268 ⟨782311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26268
    ⟨782311, by decide⟩ (by decide) (![⟨782208, by decide⟩,⟨782240, by decide⟩,⟨782265, by decide⟩,⟨782310, by decide⟩]) unmarked_context_11_26268_782311 node_context_11_26268_782311
  intro a
  fin_cases a
  · exact context_12_105072_782208
  · exact context_12_105073_782240
  · exact context_12_105074_782265
  · exact context_12_105075_782310

theorem selected_cut_30781 : selected 9 ⟨782349, by decide⟩
    (prefixPartial 12 105076) = some ⟨12, 2, 0, 782349, 105076, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_105076_782349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105076 ⟨782349, by decide⟩ :=
  accepted_of_selected 12 105076 ⟨782349, by decide⟩ ⟨12, 2, 0, 782349, 105076, 1601, 65536⟩
    (by decide) selected_cut_30781

theorem selected_cut_30782 : selected 9 ⟨782378, by decide⟩
    (prefixPartial 12 105077) = some ⟨12, 2, 0, 782378, 105077, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_105077_782378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105077 ⟨782378, by decide⟩ :=
  accepted_of_selected 12 105077 ⟨782378, by decide⟩ ⟨12, 2, 0, 782378, 105077, 1329, 65536⟩
    (by decide) selected_cut_30782

theorem selected_cut_30783 : selected 9 ⟨782409, by decide⟩
    (prefixPartial 12 105078) = some ⟨12, 2, 0, 782409, 105078, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_105078_782409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105078 ⟨782409, by decide⟩ :=
  accepted_of_selected 12 105078 ⟨782409, by decide⟩ ⟨12, 2, 0, 782409, 105078, 1309, 65536⟩
    (by decide) selected_cut_30783

theorem selected_cut_30784 : selected 9 ⟨782451, by decide⟩
    (prefixPartial 12 105079) = some ⟨12, 2, 0, 782451, 105079, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_105079_782451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105079 ⟨782451, by decide⟩ :=
  accepted_of_selected 12 105079 ⟨782451, by decide⟩ ⟨12, 2, 0, 782451, 105079, 1497, 65536⟩
    (by decide) selected_cut_30784

theorem unmarked_context_11_26269_782452 : frontier 10 ⟨782452, by decide⟩
    (prefixCache 11 26269) (prefixPartial 11 26269) = false := by
  decide +kernel

theorem node_context_11_26269_782452 : EJMOriginalGlobalDAGData.nodes 10 ⟨782452, by decide⟩ =
    .split (coordinate 11) (![⟨782349, by decide⟩,⟨782378, by decide⟩,⟨782409, by decide⟩,⟨782451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26269_782452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26269 ⟨782452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26269
    ⟨782452, by decide⟩ (by decide) (![⟨782349, by decide⟩,⟨782378, by decide⟩,⟨782409, by decide⟩,⟨782451, by decide⟩]) unmarked_context_11_26269_782452 node_context_11_26269_782452
  intro a
  fin_cases a
  · exact context_12_105076_782349
  · exact context_12_105077_782378
  · exact context_12_105078_782409
  · exact context_12_105079_782451

theorem selected_cut_30785 : selected 10 ⟨782522, by decide⟩
    (prefixPartial 11 26270) = some ⟨11, 2, 0, 782522, 26270, 3785, 262144⟩ := by
  decide +kernel

theorem context_11_26270_782522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26270 ⟨782522, by decide⟩ :=
  accepted_of_selected 11 26270 ⟨782522, by decide⟩ ⟨11, 2, 0, 782522, 26270, 3785, 262144⟩
    (by decide) selected_cut_30785

theorem selected_cut_30786 : selected 9 ⟨782540, by decide⟩
    (prefixPartial 12 105084) = some ⟨12, 2, 0, 782540, 105084, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_105084_782540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105084 ⟨782540, by decide⟩ :=
  accepted_of_selected 12 105084 ⟨782540, by decide⟩ ⟨12, 2, 0, 782540, 105084, 1197, 65536⟩
    (by decide) selected_cut_30786

theorem selected_cut_30787 : selected 9 ⟨782560, by decide⟩
    (prefixPartial 12 105085) = some ⟨12, 2, 0, 782560, 105085, 1081, 65536⟩ := by
  decide +kernel

theorem context_12_105085_782560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105085 ⟨782560, by decide⟩ :=
  accepted_of_selected 12 105085 ⟨782560, by decide⟩ ⟨12, 2, 0, 782560, 105085, 1081, 65536⟩
    (by decide) selected_cut_30787

theorem selected_cut_30788 : selected 9 ⟨782577, by decide⟩
    (prefixPartial 12 105086) = some ⟨12, 2, 0, 782577, 105086, 965, 65536⟩ := by
  decide +kernel

theorem context_12_105086_782577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105086 ⟨782577, by decide⟩ :=
  accepted_of_selected 12 105086 ⟨782577, by decide⟩ ⟨12, 2, 0, 782577, 105086, 965, 65536⟩
    (by decide) selected_cut_30788

theorem selected_cut_30789 : selected 9 ⟨782596, by decide⟩
    (prefixPartial 12 105087) = some ⟨12, 2, 0, 782596, 105087, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_105087_782596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105087 ⟨782596, by decide⟩ :=
  accepted_of_selected 12 105087 ⟨782596, by decide⟩ ⟨12, 2, 0, 782596, 105087, 1137, 65536⟩
    (by decide) selected_cut_30789

theorem unmarked_context_11_26271_782597 : frontier 10 ⟨782597, by decide⟩
    (prefixCache 11 26271) (prefixPartial 11 26271) = false := by
  decide +kernel

theorem node_context_11_26271_782597 : EJMOriginalGlobalDAGData.nodes 10 ⟨782597, by decide⟩ =
    .split (coordinate 11) (![⟨782540, by decide⟩,⟨782560, by decide⟩,⟨782577, by decide⟩,⟨782596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26271_782597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26271 ⟨782597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26271
    ⟨782597, by decide⟩ (by decide) (![⟨782540, by decide⟩,⟨782560, by decide⟩,⟨782577, by decide⟩,⟨782596, by decide⟩]) unmarked_context_11_26271_782597 node_context_11_26271_782597
  intro a
  fin_cases a
  · exact context_12_105084_782540
  · exact context_12_105085_782560
  · exact context_12_105086_782577
  · exact context_12_105087_782596

theorem unmarked_context_10_6567_782598 : frontier 11 ⟨782598, by decide⟩
    (prefixCache 10 6567) (prefixPartial 10 6567) = false := by
  decide +kernel

theorem node_context_10_6567_782598 : EJMOriginalGlobalDAGData.nodes 11 ⟨782598, by decide⟩ =
    .split (coordinate 10) (![⟨782311, by decide⟩,⟨782452, by decide⟩,⟨782522, by decide⟩,⟨782597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6567_782598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6567 ⟨782598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6567
    ⟨782598, by decide⟩ (by decide) (![⟨782311, by decide⟩,⟨782452, by decide⟩,⟨782522, by decide⟩,⟨782597, by decide⟩]) unmarked_context_10_6567_782598 node_context_10_6567_782598
  intro a
  fin_cases a
  · exact context_11_26268_782311
  · exact context_11_26269_782452
  · exact context_11_26270_782522
  · exact context_11_26271_782597

theorem unmarked_context_9_1641_782599 : frontier 12 ⟨782599, by decide⟩
    (prefixCache 9 1641) (prefixPartial 9 1641) = false := by
  decide +kernel

theorem node_context_9_1641_782599 : EJMOriginalGlobalDAGData.nodes 12 ⟨782599, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨781749, by decide⟩,⟨782171, by decide⟩,⟨782598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1641_782599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1641 ⟨782599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1641
    ⟨782599, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨781749, by decide⟩,⟨782171, by decide⟩,⟨782598, by decide⟩]) unmarked_context_9_1641_782599 node_context_9_1641_782599
  intro a
  fin_cases a
  · exact context_10_6564_3442
  · exact context_10_6565_781749
  · exact context_10_6566_782171
  · exact context_10_6567_782598

theorem selected_cut_30790 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 6568) = some ⟨10, 1, 0, 3442, 6568, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6568_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6568 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 6568 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 6568, 1, 1048576⟩
    (by decide) selected_cut_30790

theorem selected_cut_30791 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 6569) = some ⟨10, 1, 0, 3442, 6569, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6569_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6569 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 6569 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 6569, 1, 1048576⟩
    (by decide) selected_cut_30791

theorem selected_cut_30792 : selected 11 ⟨782673, by decide⟩
    (prefixPartial 10 6570) = some ⟨10, 2, 0, 782673, 6570, 3061, 1048576⟩ := by
  decide +kernel

theorem context_10_6570_782673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6570 ⟨782673, by decide⟩ :=
  accepted_of_selected 10 6570 ⟨782673, by decide⟩ ⟨10, 2, 0, 782673, 6570, 3061, 1048576⟩
    (by decide) selected_cut_30792

theorem selected_cut_30793 : selected 10 ⟨782720, by decide⟩
    (prefixPartial 11 26284) = some ⟨11, 2, 0, 782720, 26284, 1857, 262144⟩ := by
  decide +kernel

theorem context_11_26284_782720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26284 ⟨782720, by decide⟩ :=
  accepted_of_selected 11 26284 ⟨782720, by decide⟩ ⟨11, 2, 0, 782720, 26284, 1857, 262144⟩
    (by decide) selected_cut_30793

theorem selected_cut_30794 : selected 10 ⟨782758, by decide⟩
    (prefixPartial 11 26285) = some ⟨11, 2, 0, 782758, 26285, 1393, 262144⟩ := by
  decide +kernel

theorem context_11_26285_782758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26285 ⟨782758, by decide⟩ :=
  accepted_of_selected 11 26285 ⟨782758, by decide⟩ ⟨11, 2, 0, 782758, 26285, 1393, 262144⟩
    (by decide) selected_cut_30794

theorem selected_cut_30795 : selected 10 ⟨782787, by decide⟩
    (prefixPartial 11 26286) = some ⟨11, 2, 0, 782787, 26286, 1093, 262144⟩ := by
  decide +kernel

theorem context_11_26286_782787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26286 ⟨782787, by decide⟩ :=
  accepted_of_selected 11 26286 ⟨782787, by decide⟩ ⟨11, 2, 0, 782787, 26286, 1093, 262144⟩
    (by decide) selected_cut_30795

theorem selected_cut_30796 : selected 10 ⟨782817, by decide⟩
    (prefixPartial 11 26287) = some ⟨11, 2, 0, 782817, 26287, 861, 262144⟩ := by
  decide +kernel

theorem context_11_26287_782817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26287 ⟨782817, by decide⟩ :=
  accepted_of_selected 11 26287 ⟨782817, by decide⟩ ⟨11, 2, 0, 782817, 26287, 861, 262144⟩
    (by decide) selected_cut_30796

theorem unmarked_context_10_6571_782818 : frontier 11 ⟨782818, by decide⟩
    (prefixCache 10 6571) (prefixPartial 10 6571) = false := by
  decide +kernel

theorem node_context_10_6571_782818 : EJMOriginalGlobalDAGData.nodes 11 ⟨782818, by decide⟩ =
    .split (coordinate 10) (![⟨782720, by decide⟩,⟨782758, by decide⟩,⟨782787, by decide⟩,⟨782817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6571_782818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6571 ⟨782818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6571
    ⟨782818, by decide⟩ (by decide) (![⟨782720, by decide⟩,⟨782758, by decide⟩,⟨782787, by decide⟩,⟨782817, by decide⟩]) unmarked_context_10_6571_782818 node_context_10_6571_782818
  intro a
  fin_cases a
  · exact context_11_26284_782720
  · exact context_11_26285_782758
  · exact context_11_26286_782787
  · exact context_11_26287_782817

theorem unmarked_context_9_1642_782819 : frontier 12 ⟨782819, by decide⟩
    (prefixCache 9 1642) (prefixPartial 9 1642) = false := by
  decide +kernel

theorem node_context_9_1642_782819 : EJMOriginalGlobalDAGData.nodes 12 ⟨782819, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨782673, by decide⟩,⟨782818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1642_782819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1642 ⟨782819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1642
    ⟨782819, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨782673, by decide⟩,⟨782818, by decide⟩]) unmarked_context_9_1642_782819 node_context_9_1642_782819
  intro a
  fin_cases a
  · exact context_10_6568_3442
  · exact context_10_6569_3442
  · exact context_10_6570_782673
  · exact context_10_6571_782818

theorem selected_cut_30797 : selected 12 ⟨782852, by decide⟩
    (prefixPartial 9 1643) = some ⟨9, 2, 0, 782852, 1643, 989, 4194304⟩ := by
  decide +kernel

theorem context_9_1643_782852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1643 ⟨782852, by decide⟩ :=
  accepted_of_selected 9 1643 ⟨782852, by decide⟩ ⟨9, 2, 0, 782852, 1643, 989, 4194304⟩
    (by decide) selected_cut_30797

theorem unmarked_context_8_410_782853 : frontier 13 ⟨782853, by decide⟩
    (prefixCache 8 410) (prefixPartial 8 410) = false := by
  decide +kernel

theorem node_context_8_410_782853 : EJMOriginalGlobalDAGData.nodes 13 ⟨782853, by decide⟩ =
    .split (coordinate 8) (![⟨781293, by decide⟩,⟨782599, by decide⟩,⟨782819, by decide⟩,⟨782852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_410_782853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 410 ⟨782853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 410
    ⟨782853, by decide⟩ (by decide) (![⟨781293, by decide⟩,⟨782599, by decide⟩,⟨782819, by decide⟩,⟨782852, by decide⟩]) unmarked_context_8_410_782853 node_context_8_410_782853
  intro a
  fin_cases a
  · exact context_9_1640_781293
  · exact context_9_1641_782599
  · exact context_9_1642_782819
  · exact context_9_1643_782852

theorem selected_cut_30798 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 26304) = some ⟨11, 1, 0, 434745, 26304, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26304_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26304 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 26304 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 26304, 1, 262144⟩
    (by decide) selected_cut_30798

theorem selected_cut_30799 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 105220) = some ⟨12, 1, 0, 895, 105220, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105220_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105220 ⟨895, by decide⟩ :=
  accepted_of_selected 12 105220 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 105220, 1, 65536⟩
    (by decide) selected_cut_30799

theorem selected_cut_30800 : selected 8 ⟨782963, by decide⟩
    (prefixPartial 13 420884) = some ⟨13, 2, 0, 782963, 420884, 2909, 16384⟩ := by
  decide +kernel

theorem context_13_420884_782963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420884 ⟨782963, by decide⟩ :=
  accepted_of_selected 13 420884 ⟨782963, by decide⟩ ⟨13, 2, 0, 782963, 420884, 2909, 16384⟩
    (by decide) selected_cut_30800

theorem selected_cut_30801 : selected 8 ⟨783037, by decide⟩
    (prefixPartial 13 420885) = some ⟨13, 2, 0, 783037, 420885, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_420885_783037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420885 ⟨783037, by decide⟩ :=
  accepted_of_selected 13 420885 ⟨783037, by decide⟩ ⟨13, 2, 0, 783037, 420885, 1833, 16384⟩
    (by decide) selected_cut_30801

theorem selected_cut_30802 : selected 8 ⟨783077, by decide⟩
    (prefixPartial 13 420886) = some ⟨13, 2, 0, 783077, 420886, 501, 16384⟩ := by
  decide +kernel

theorem context_13_420886_783077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420886 ⟨783077, by decide⟩ :=
  accepted_of_selected 13 420886 ⟨783077, by decide⟩ ⟨13, 2, 0, 783077, 420886, 501, 16384⟩
    (by decide) selected_cut_30802

theorem selected_cut_30803 : selected 8 ⟨783080, by decide⟩
    (prefixPartial 13 420887) = some ⟨13, 2, 0, 783080, 420887, 97, 16384⟩ := by
  decide +kernel

theorem context_13_420887_783080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420887 ⟨783080, by decide⟩ :=
  accepted_of_selected 13 420887 ⟨783080, by decide⟩ ⟨13, 2, 0, 783080, 420887, 97, 16384⟩
    (by decide) selected_cut_30803

theorem unmarked_context_12_105221_783081 : frontier 9 ⟨783081, by decide⟩
    (prefixCache 12 105221) (prefixPartial 12 105221) = false := by
  decide +kernel

theorem node_context_12_105221_783081 : EJMOriginalGlobalDAGData.nodes 9 ⟨783081, by decide⟩ =
    .split (coordinate 12) (![⟨782963, by decide⟩,⟨783037, by decide⟩,⟨783077, by decide⟩,⟨783080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105221_783081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105221 ⟨783081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105221
    ⟨783081, by decide⟩ (by decide) (![⟨782963, by decide⟩,⟨783037, by decide⟩,⟨783077, by decide⟩,⟨783080, by decide⟩]) unmarked_context_12_105221_783081 node_context_12_105221_783081
  intro a
  fin_cases a
  · exact context_13_420884_782963
  · exact context_13_420885_783037
  · exact context_13_420886_783077
  · exact context_13_420887_783080

theorem selected_cut_30804 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 105222) = some ⟨12, 1, 0, 763842, 105222, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105222_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105222 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 105222 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 105222, 1, 65536⟩
    (by decide) selected_cut_30804

theorem selected_cut_30805 : selected 8 ⟨783139, by decide⟩
    (prefixPartial 13 420892) = some ⟨13, 2, 0, 783139, 420892, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_420892_783139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420892 ⟨783139, by decide⟩ :=
  accepted_of_selected 13 420892 ⟨783139, by decide⟩ ⟨13, 2, 0, 783139, 420892, 2545, 16384⟩
    (by decide) selected_cut_30805

theorem selected_cut_30806 : selected 8 ⟨783237, by decide⟩
    (prefixPartial 13 420893) = some ⟨13, 2, 0, 783237, 420893, 3793, 16384⟩ := by
  decide +kernel

theorem context_13_420893_783237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420893 ⟨783237, by decide⟩ :=
  accepted_of_selected 13 420893 ⟨783237, by decide⟩ ⟨13, 2, 0, 783237, 420893, 3793, 16384⟩
    (by decide) selected_cut_30806

theorem selected_cut_30807 : selected 8 ⟨783293, by decide⟩
    (prefixPartial 13 420894) = some ⟨13, 2, 0, 783293, 420894, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_420894_783293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420894 ⟨783293, by decide⟩ :=
  accepted_of_selected 13 420894 ⟨783293, by decide⟩ ⟨13, 2, 0, 783293, 420894, 1881, 16384⟩
    (by decide) selected_cut_30807

theorem selected_cut_30808 : selected 8 ⟨783305, by decide⟩
    (prefixPartial 13 420895) = some ⟨13, 2, 0, 783305, 420895, 877, 16384⟩ := by
  decide +kernel

theorem context_13_420895_783305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420895 ⟨783305, by decide⟩ :=
  accepted_of_selected 13 420895 ⟨783305, by decide⟩ ⟨13, 2, 0, 783305, 420895, 877, 16384⟩
    (by decide) selected_cut_30808

theorem unmarked_context_12_105223_783306 : frontier 9 ⟨783306, by decide⟩
    (prefixCache 12 105223) (prefixPartial 12 105223) = false := by
  decide +kernel

theorem node_context_12_105223_783306 : EJMOriginalGlobalDAGData.nodes 9 ⟨783306, by decide⟩ =
    .split (coordinate 12) (![⟨783139, by decide⟩,⟨783237, by decide⟩,⟨783293, by decide⟩,⟨783305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105223_783306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105223 ⟨783306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105223
    ⟨783306, by decide⟩ (by decide) (![⟨783139, by decide⟩,⟨783237, by decide⟩,⟨783293, by decide⟩,⟨783305, by decide⟩]) unmarked_context_12_105223_783306 node_context_12_105223_783306
  intro a
  fin_cases a
  · exact context_13_420892_783139
  · exact context_13_420893_783237
  · exact context_13_420894_783293
  · exact context_13_420895_783305

theorem unmarked_context_11_26305_783307 : frontier 10 ⟨783307, by decide⟩
    (prefixCache 11 26305) (prefixPartial 11 26305) = false := by
  decide +kernel

theorem node_context_11_26305_783307 : EJMOriginalGlobalDAGData.nodes 10 ⟨783307, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨783081, by decide⟩,⟨763842, by decide⟩,⟨783306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26305_783307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26305 ⟨783307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26305
    ⟨783307, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨783081, by decide⟩,⟨763842, by decide⟩,⟨783306, by decide⟩]) unmarked_context_11_26305_783307 node_context_11_26305_783307
  intro a
  fin_cases a
  · exact context_12_105220_895
  · exact context_12_105221_783081
  · exact context_12_105222_763842
  · exact context_12_105223_783306

theorem selected_cut_30809 : selected 10 ⟨764169, by decide⟩
    (prefixPartial 11 26306) = some ⟨11, 1, 0, 764169, 26306, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26306_764169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26306 ⟨764169, by decide⟩ :=
  accepted_of_selected 11 26306 ⟨764169, by decide⟩ ⟨11, 1, 0, 764169, 26306, 1, 262144⟩
    (by decide) selected_cut_30809

theorem selected_cut_30810 : selected 10 ⟨783308, by decide⟩
    (prefixPartial 11 26307) = some ⟨11, 2, 0, 783308, 26307, 5, 262144⟩ := by
  decide +kernel

theorem context_11_26307_783308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26307 ⟨783308, by decide⟩ :=
  accepted_of_selected 11 26307 ⟨783308, by decide⟩ ⟨11, 2, 0, 783308, 26307, 5, 262144⟩
    (by decide) selected_cut_30810

theorem unmarked_context_10_6576_783309 : frontier 11 ⟨783309, by decide⟩
    (prefixCache 10 6576) (prefixPartial 10 6576) = false := by
  decide +kernel

theorem node_context_10_6576_783309 : EJMOriginalGlobalDAGData.nodes 11 ⟨783309, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨783307, by decide⟩,⟨764169, by decide⟩,⟨783308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6576_783309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6576 ⟨783309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6576
    ⟨783309, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨783307, by decide⟩,⟨764169, by decide⟩,⟨783308, by decide⟩]) unmarked_context_10_6576_783309 node_context_10_6576_783309
  intro a
  fin_cases a
  · exact context_11_26304_434745
  · exact context_11_26305_783307
  · exact context_11_26306_764169
  · exact context_11_26307_783308

theorem selected_cut_30811 : selected 8 ⟨783343, by decide⟩
    (prefixPartial 13 420928) = some ⟨13, 2, 0, 783343, 420928, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_420928_783343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420928 ⟨783343, by decide⟩ :=
  accepted_of_selected 13 420928 ⟨783343, by decide⟩ ⟨13, 2, 0, 783343, 420928, 1793, 16384⟩
    (by decide) selected_cut_30811

theorem selected_cut_30812 : selected 8 ⟨783364, by decide⟩
    (prefixPartial 13 420929) = some ⟨13, 2, 0, 783364, 420929, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_420929_783364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420929 ⟨783364, by decide⟩ :=
  accepted_of_selected 13 420929 ⟨783364, by decide⟩ ⟨13, 2, 0, 783364, 420929, 1577, 16384⟩
    (by decide) selected_cut_30812

theorem selected_cut_30813 : selected 8 ⟨783389, by decide⟩
    (prefixPartial 13 420930) = some ⟨13, 2, 0, 783389, 420930, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_420930_783389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420930 ⟨783389, by decide⟩ :=
  accepted_of_selected 13 420930 ⟨783389, by decide⟩ ⟨13, 2, 0, 783389, 420930, 1125, 16384⟩
    (by decide) selected_cut_30813

theorem selected_cut_30814 : selected 8 ⟨783396, by decide⟩
    (prefixPartial 13 420931) = some ⟨13, 2, 0, 783396, 420931, 633, 16384⟩ := by
  decide +kernel

theorem context_13_420931_783396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420931 ⟨783396, by decide⟩ :=
  accepted_of_selected 13 420931 ⟨783396, by decide⟩ ⟨13, 2, 0, 783396, 420931, 633, 16384⟩
    (by decide) selected_cut_30814

theorem unmarked_context_12_105232_783397 : frontier 9 ⟨783397, by decide⟩
    (prefixCache 12 105232) (prefixPartial 12 105232) = false := by
  decide +kernel

theorem node_context_12_105232_783397 : EJMOriginalGlobalDAGData.nodes 9 ⟨783397, by decide⟩ =
    .split (coordinate 12) (![⟨783343, by decide⟩,⟨783364, by decide⟩,⟨783389, by decide⟩,⟨783396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105232_783397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105232 ⟨783397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105232
    ⟨783397, by decide⟩ (by decide) (![⟨783343, by decide⟩,⟨783364, by decide⟩,⟨783389, by decide⟩,⟨783396, by decide⟩]) unmarked_context_12_105232_783397 node_context_12_105232_783397
  intro a
  fin_cases a
  · exact context_13_420928_783343
  · exact context_13_420929_783364
  · exact context_13_420930_783389
  · exact context_13_420931_783396

theorem selected_cut_30815 : selected 8 ⟨783440, by decide⟩
    (prefixPartial 13 420932) = some ⟨13, 2, 0, 783440, 420932, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_420932_783440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420932 ⟨783440, by decide⟩ :=
  accepted_of_selected 13 420932 ⟨783440, by decide⟩ ⟨13, 2, 0, 783440, 420932, 2389, 16384⟩
    (by decide) selected_cut_30815

theorem selected_cut_30816 : selected 8 ⟨783474, by decide⟩
    (prefixPartial 13 420933) = some ⟨13, 2, 0, 783474, 420933, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_420933_783474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420933 ⟨783474, by decide⟩ :=
  accepted_of_selected 13 420933 ⟨783474, by decide⟩ ⟨13, 2, 0, 783474, 420933, 2177, 16384⟩
    (by decide) selected_cut_30816

theorem selected_cut_30817 : selected 8 ⟨783502, by decide⟩
    (prefixPartial 13 420934) = some ⟨13, 2, 0, 783502, 420934, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_420934_783502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420934 ⟨783502, by decide⟩ :=
  accepted_of_selected 13 420934 ⟨783502, by decide⟩ ⟨13, 2, 0, 783502, 420934, 1337, 16384⟩
    (by decide) selected_cut_30817

theorem selected_cut_30818 : selected 8 ⟨783510, by decide⟩
    (prefixPartial 13 420935) = some ⟨13, 2, 0, 783510, 420935, 685, 16384⟩ := by
  decide +kernel

theorem context_13_420935_783510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420935 ⟨783510, by decide⟩ :=
  accepted_of_selected 13 420935 ⟨783510, by decide⟩ ⟨13, 2, 0, 783510, 420935, 685, 16384⟩
    (by decide) selected_cut_30818

theorem unmarked_context_12_105233_783511 : frontier 9 ⟨783511, by decide⟩
    (prefixCache 12 105233) (prefixPartial 12 105233) = false := by
  decide +kernel

theorem node_context_12_105233_783511 : EJMOriginalGlobalDAGData.nodes 9 ⟨783511, by decide⟩ =
    .split (coordinate 12) (![⟨783440, by decide⟩,⟨783474, by decide⟩,⟨783502, by decide⟩,⟨783510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105233_783511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105233 ⟨783511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105233
    ⟨783511, by decide⟩ (by decide) (![⟨783440, by decide⟩,⟨783474, by decide⟩,⟨783502, by decide⟩,⟨783510, by decide⟩]) unmarked_context_12_105233_783511 node_context_12_105233_783511
  intro a
  fin_cases a
  · exact context_13_420932_783440
  · exact context_13_420933_783474
  · exact context_13_420934_783502
  · exact context_13_420935_783510

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
