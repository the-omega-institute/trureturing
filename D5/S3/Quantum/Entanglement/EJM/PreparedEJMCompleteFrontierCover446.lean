/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover445
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_42819 : selected 9 ⟨1169866, by decide⟩
    (prefixPartial 12 338784) = some ⟨12, 2, 0, 1169866, 338784, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_338784_1169866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338784 ⟨1169866, by decide⟩ :=
  accepted_of_selected 12 338784 ⟨1169866, by decide⟩ ⟨12, 2, 0, 1169866, 338784, 1621, 65536⟩
    (by decide) selected_cut_42819

theorem selected_cut_42820 : selected 9 ⟨1169893, by decide⟩
    (prefixPartial 12 338785) = some ⟨12, 2, 0, 1169893, 338785, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_338785_1169893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338785 ⟨1169893, by decide⟩ :=
  accepted_of_selected 12 338785 ⟨1169893, by decide⟩ ⟨12, 2, 0, 1169893, 338785, 1713, 65536⟩
    (by decide) selected_cut_42820

theorem selected_cut_42821 : selected 9 ⟨1169923, by decide⟩
    (prefixPartial 12 338786) = some ⟨12, 2, 0, 1169923, 338786, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_338786_1169923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338786 ⟨1169923, by decide⟩ :=
  accepted_of_selected 12 338786 ⟨1169923, by decide⟩ ⟨12, 2, 0, 1169923, 338786, 1749, 65536⟩
    (by decide) selected_cut_42821

theorem selected_cut_42822 : selected 9 ⟨1169951, by decide⟩
    (prefixPartial 12 338787) = some ⟨12, 2, 0, 1169951, 338787, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_338787_1169951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338787 ⟨1169951, by decide⟩ :=
  accepted_of_selected 12 338787 ⟨1169951, by decide⟩ ⟨12, 2, 0, 1169951, 338787, 1801, 65536⟩
    (by decide) selected_cut_42822

theorem unmarked_context_11_84696_1169952 : frontier 10 ⟨1169952, by decide⟩
    (prefixCache 11 84696) (prefixPartial 11 84696) = false := by
  decide +kernel

theorem node_context_11_84696_1169952 : EJMOriginalGlobalDAGData.nodes 10 ⟨1169952, by decide⟩ =
    .split (coordinate 11) (![⟨1169866, by decide⟩,⟨1169893, by decide⟩,⟨1169923, by decide⟩,⟨1169951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84696_1169952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84696 ⟨1169952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84696
    ⟨1169952, by decide⟩ (by decide) (![⟨1169866, by decide⟩,⟨1169893, by decide⟩,⟨1169923, by decide⟩,⟨1169951, by decide⟩]) unmarked_context_11_84696_1169952 node_context_11_84696_1169952
  intro a
  fin_cases a
  · exact context_12_338784_1169866
  · exact context_12_338785_1169893
  · exact context_12_338786_1169923
  · exact context_12_338787_1169951

theorem selected_cut_42823 : selected 9 ⟨1169974, by decide⟩
    (prefixPartial 12 338788) = some ⟨12, 2, 0, 1169974, 338788, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_338788_1169974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338788 ⟨1169974, by decide⟩ :=
  accepted_of_selected 12 338788 ⟨1169974, by decide⟩ ⟨12, 2, 0, 1169974, 338788, 1561, 65536⟩
    (by decide) selected_cut_42823

theorem selected_cut_42824 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 338789) = some ⟨12, 1, 0, 642794, 338789, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338789_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338789 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 338789 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 338789, 1, 65536⟩
    (by decide) selected_cut_42824

theorem selected_cut_42825 : selected 9 ⟨1169992, by decide⟩
    (prefixPartial 12 338790) = some ⟨12, 2, 0, 1169992, 338790, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_338790_1169992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338790 ⟨1169992, by decide⟩ :=
  accepted_of_selected 12 338790 ⟨1169992, by decide⟩ ⟨12, 2, 0, 1169992, 338790, 1521, 65536⟩
    (by decide) selected_cut_42825

theorem selected_cut_42826 : selected 9 ⟨1170017, by decide⟩
    (prefixPartial 12 338791) = some ⟨12, 2, 0, 1170017, 338791, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_338791_1170017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338791 ⟨1170017, by decide⟩ :=
  accepted_of_selected 12 338791 ⟨1170017, by decide⟩ ⟨12, 2, 0, 1170017, 338791, 1721, 65536⟩
    (by decide) selected_cut_42826

theorem unmarked_context_11_84697_1170018 : frontier 10 ⟨1170018, by decide⟩
    (prefixCache 11 84697) (prefixPartial 11 84697) = false := by
  decide +kernel

theorem node_context_11_84697_1170018 : EJMOriginalGlobalDAGData.nodes 10 ⟨1170018, by decide⟩ =
    .split (coordinate 11) (![⟨1169974, by decide⟩,⟨642794, by decide⟩,⟨1169992, by decide⟩,⟨1170017, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84697_1170018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84697 ⟨1170018, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84697
    ⟨1170018, by decide⟩ (by decide) (![⟨1169974, by decide⟩,⟨642794, by decide⟩,⟨1169992, by decide⟩,⟨1170017, by decide⟩]) unmarked_context_11_84697_1170018 node_context_11_84697_1170018
  intro a
  fin_cases a
  · exact context_12_338788_1169974
  · exact context_12_338789_642794
  · exact context_12_338790_1169992
  · exact context_12_338791_1170017

theorem selected_cut_42827 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 84698) = some ⟨11, 1, 0, 900587, 84698, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84698_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84698 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 84698 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 84698, 1, 262144⟩
    (by decide) selected_cut_42827

theorem selected_cut_42828 : selected 10 ⟨1170069, by decide⟩
    (prefixPartial 11 84699) = some ⟨11, 2, 0, 1170069, 84699, 4017, 262144⟩ := by
  decide +kernel

theorem context_11_84699_1170069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84699 ⟨1170069, by decide⟩ :=
  accepted_of_selected 11 84699 ⟨1170069, by decide⟩ ⟨11, 2, 0, 1170069, 84699, 4017, 262144⟩
    (by decide) selected_cut_42828

theorem unmarked_context_10_21174_1170070 : frontier 11 ⟨1170070, by decide⟩
    (prefixCache 10 21174) (prefixPartial 10 21174) = false := by
  decide +kernel

theorem node_context_10_21174_1170070 : EJMOriginalGlobalDAGData.nodes 11 ⟨1170070, by decide⟩ =
    .split (coordinate 10) (![⟨1169952, by decide⟩,⟨1170018, by decide⟩,⟨900587, by decide⟩,⟨1170069, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21174_1170070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21174 ⟨1170070, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21174
    ⟨1170070, by decide⟩ (by decide) (![⟨1169952, by decide⟩,⟨1170018, by decide⟩,⟨900587, by decide⟩,⟨1170069, by decide⟩]) unmarked_context_10_21174_1170070 node_context_10_21174_1170070
  intro a
  fin_cases a
  · exact context_11_84696_1169952
  · exact context_11_84697_1170018
  · exact context_11_84698_900587
  · exact context_11_84699_1170069

theorem selected_cut_42829 : selected 9 ⟨1170107, by decide⟩
    (prefixPartial 12 338800) = some ⟨12, 2, 0, 1170107, 338800, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_338800_1170107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338800 ⟨1170107, by decide⟩ :=
  accepted_of_selected 12 338800 ⟨1170107, by decide⟩ ⟨12, 2, 0, 1170107, 338800, 1933, 65536⟩
    (by decide) selected_cut_42829

theorem selected_cut_42830 : selected 9 ⟨1170137, by decide⟩
    (prefixPartial 12 338801) = some ⟨12, 2, 0, 1170137, 338801, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_338801_1170137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338801 ⟨1170137, by decide⟩ :=
  accepted_of_selected 12 338801 ⟨1170137, by decide⟩ ⟨12, 2, 0, 1170137, 338801, 2065, 65536⟩
    (by decide) selected_cut_42830

theorem selected_cut_42831 : selected 9 ⟨1170179, by decide⟩
    (prefixPartial 12 338802) = some ⟨12, 2, 0, 1170179, 338802, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_338802_1170179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338802 ⟨1170179, by decide⟩ :=
  accepted_of_selected 12 338802 ⟨1170179, by decide⟩ ⟨12, 2, 0, 1170179, 338802, 2185, 65536⟩
    (by decide) selected_cut_42831

theorem selected_cut_42832 : selected 9 ⟨1170224, by decide⟩
    (prefixPartial 12 338803) = some ⟨12, 2, 0, 1170224, 338803, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_338803_1170224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338803 ⟨1170224, by decide⟩ :=
  accepted_of_selected 12 338803 ⟨1170224, by decide⟩ ⟨12, 2, 0, 1170224, 338803, 2249, 65536⟩
    (by decide) selected_cut_42832

theorem unmarked_context_11_84700_1170225 : frontier 10 ⟨1170225, by decide⟩
    (prefixCache 11 84700) (prefixPartial 11 84700) = false := by
  decide +kernel

theorem node_context_11_84700_1170225 : EJMOriginalGlobalDAGData.nodes 10 ⟨1170225, by decide⟩ =
    .split (coordinate 11) (![⟨1170107, by decide⟩,⟨1170137, by decide⟩,⟨1170179, by decide⟩,⟨1170224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84700_1170225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84700 ⟨1170225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84700
    ⟨1170225, by decide⟩ (by decide) (![⟨1170107, by decide⟩,⟨1170137, by decide⟩,⟨1170179, by decide⟩,⟨1170224, by decide⟩]) unmarked_context_11_84700_1170225 node_context_11_84700_1170225
  intro a
  fin_cases a
  · exact context_12_338800_1170107
  · exact context_12_338801_1170137
  · exact context_12_338802_1170179
  · exact context_12_338803_1170224

theorem selected_cut_42833 : selected 9 ⟨1170258, by decide⟩
    (prefixPartial 12 338804) = some ⟨12, 2, 0, 1170258, 338804, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_338804_1170258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338804 ⟨1170258, by decide⟩ :=
  accepted_of_selected 12 338804 ⟨1170258, by decide⟩ ⟨12, 2, 0, 1170258, 338804, 1761, 65536⟩
    (by decide) selected_cut_42833

theorem selected_cut_42834 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 338805) = some ⟨12, 1, 0, 642794, 338805, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338805_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338805 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 338805 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 338805, 1, 65536⟩
    (by decide) selected_cut_42834

theorem selected_cut_42835 : selected 9 ⟨1170286, by decide⟩
    (prefixPartial 12 338806) = some ⟨12, 2, 0, 1170286, 338806, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_338806_1170286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338806 ⟨1170286, by decide⟩ :=
  accepted_of_selected 12 338806 ⟨1170286, by decide⟩ ⟨12, 2, 0, 1170286, 338806, 1805, 65536⟩
    (by decide) selected_cut_42835

theorem selected_cut_42836 : selected 9 ⟨1170315, by decide⟩
    (prefixPartial 12 338807) = some ⟨12, 2, 0, 1170315, 338807, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_338807_1170315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338807 ⟨1170315, by decide⟩ :=
  accepted_of_selected 12 338807 ⟨1170315, by decide⟩ ⟨12, 2, 0, 1170315, 338807, 1989, 65536⟩
    (by decide) selected_cut_42836

theorem unmarked_context_11_84701_1170316 : frontier 10 ⟨1170316, by decide⟩
    (prefixCache 11 84701) (prefixPartial 11 84701) = false := by
  decide +kernel

theorem node_context_11_84701_1170316 : EJMOriginalGlobalDAGData.nodes 10 ⟨1170316, by decide⟩ =
    .split (coordinate 11) (![⟨1170258, by decide⟩,⟨642794, by decide⟩,⟨1170286, by decide⟩,⟨1170315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84701_1170316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84701 ⟨1170316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84701
    ⟨1170316, by decide⟩ (by decide) (![⟨1170258, by decide⟩,⟨642794, by decide⟩,⟨1170286, by decide⟩,⟨1170315, by decide⟩]) unmarked_context_11_84701_1170316 node_context_11_84701_1170316
  intro a
  fin_cases a
  · exact context_12_338804_1170258
  · exact context_12_338805_642794
  · exact context_12_338806_1170286
  · exact context_12_338807_1170315

theorem selected_cut_42837 : selected 9 ⟨1170339, by decide⟩
    (prefixPartial 12 338808) = some ⟨12, 2, 0, 1170339, 338808, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_338808_1170339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338808 ⟨1170339, by decide⟩ :=
  accepted_of_selected 12 338808 ⟨1170339, by decide⟩ ⟨12, 2, 0, 1170339, 338808, 1409, 65536⟩
    (by decide) selected_cut_42837

theorem selected_cut_42838 : selected 9 ⟨1170356, by decide⟩
    (prefixPartial 12 338809) = some ⟨12, 2, 0, 1170356, 338809, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_338809_1170356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338809 ⟨1170356, by decide⟩ :=
  accepted_of_selected 12 338809 ⟨1170356, by decide⟩ ⟨12, 2, 0, 1170356, 338809, 1469, 65536⟩
    (by decide) selected_cut_42838

theorem selected_cut_42839 : selected 9 ⟨1170379, by decide⟩
    (prefixPartial 12 338810) = some ⟨12, 2, 0, 1170379, 338810, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_338810_1170379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338810 ⟨1170379, by decide⟩ :=
  accepted_of_selected 12 338810 ⟨1170379, by decide⟩ ⟨12, 2, 0, 1170379, 338810, 1433, 65536⟩
    (by decide) selected_cut_42839

theorem selected_cut_42840 : selected 9 ⟨1170403, by decide⟩
    (prefixPartial 12 338811) = some ⟨12, 2, 0, 1170403, 338811, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_338811_1170403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338811 ⟨1170403, by decide⟩ :=
  accepted_of_selected 12 338811 ⟨1170403, by decide⟩ ⟨12, 2, 0, 1170403, 338811, 1505, 65536⟩
    (by decide) selected_cut_42840

theorem unmarked_context_11_84702_1170404 : frontier 10 ⟨1170404, by decide⟩
    (prefixCache 11 84702) (prefixPartial 11 84702) = false := by
  decide +kernel

theorem node_context_11_84702_1170404 : EJMOriginalGlobalDAGData.nodes 10 ⟨1170404, by decide⟩ =
    .split (coordinate 11) (![⟨1170339, by decide⟩,⟨1170356, by decide⟩,⟨1170379, by decide⟩,⟨1170403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84702_1170404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84702 ⟨1170404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84702
    ⟨1170404, by decide⟩ (by decide) (![⟨1170339, by decide⟩,⟨1170356, by decide⟩,⟨1170379, by decide⟩,⟨1170403, by decide⟩]) unmarked_context_11_84702_1170404 node_context_11_84702_1170404
  intro a
  fin_cases a
  · exact context_12_338808_1170339
  · exact context_12_338809_1170356
  · exact context_12_338810_1170379
  · exact context_12_338811_1170403

theorem selected_cut_42841 : selected 10 ⟨1170473, by decide⟩
    (prefixPartial 11 84703) = some ⟨11, 2, 0, 1170473, 84703, 2981, 262144⟩ := by
  decide +kernel

theorem context_11_84703_1170473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84703 ⟨1170473, by decide⟩ :=
  accepted_of_selected 11 84703 ⟨1170473, by decide⟩ ⟨11, 2, 0, 1170473, 84703, 2981, 262144⟩
    (by decide) selected_cut_42841

theorem unmarked_context_10_21175_1170474 : frontier 11 ⟨1170474, by decide⟩
    (prefixCache 10 21175) (prefixPartial 10 21175) = false := by
  decide +kernel

theorem node_context_10_21175_1170474 : EJMOriginalGlobalDAGData.nodes 11 ⟨1170474, by decide⟩ =
    .split (coordinate 10) (![⟨1170225, by decide⟩,⟨1170316, by decide⟩,⟨1170404, by decide⟩,⟨1170473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21175_1170474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21175 ⟨1170474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21175
    ⟨1170474, by decide⟩ (by decide) (![⟨1170225, by decide⟩,⟨1170316, by decide⟩,⟨1170404, by decide⟩,⟨1170473, by decide⟩]) unmarked_context_10_21175_1170474 node_context_10_21175_1170474
  intro a
  fin_cases a
  · exact context_11_84700_1170225
  · exact context_11_84701_1170316
  · exact context_11_84702_1170404
  · exact context_11_84703_1170473

theorem unmarked_context_9_5293_1170475 : frontier 12 ⟨1170475, by decide⟩
    (prefixCache 9 5293) (prefixPartial 9 5293) = false := by
  decide +kernel

theorem node_context_9_5293_1170475 : EJMOriginalGlobalDAGData.nodes 12 ⟨1170475, by decide⟩ =
    .split (coordinate 9) (![⟨1169840, by decide⟩,⟨893098, by decide⟩,⟨1170070, by decide⟩,⟨1170474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5293_1170475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5293 ⟨1170475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5293
    ⟨1170475, by decide⟩ (by decide) (![⟨1169840, by decide⟩,⟨893098, by decide⟩,⟨1170070, by decide⟩,⟨1170474, by decide⟩]) unmarked_context_9_5293_1170475 node_context_9_5293_1170475
  intro a
  fin_cases a
  · exact context_10_21172_1169840
  · exact context_10_21173_893098
  · exact context_10_21174_1170070
  · exact context_10_21175_1170474

theorem selected_cut_42842 : selected 9 ⟨1120586, by decide⟩
    (prefixPartial 12 338816) = some ⟨12, 1, 0, 1120586, 338816, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338816_1120586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338816 ⟨1120586, by decide⟩ :=
  accepted_of_selected 12 338816 ⟨1120586, by decide⟩ ⟨12, 1, 0, 1120586, 338816, 1, 65536⟩
    (by decide) selected_cut_42842

theorem selected_cut_42843 : selected 9 ⟨1170497, by decide⟩
    (prefixPartial 12 338817) = some ⟨12, 2, 0, 1170497, 338817, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_338817_1170497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338817 ⟨1170497, by decide⟩ :=
  accepted_of_selected 12 338817 ⟨1170497, by decide⟩ ⟨12, 2, 0, 1170497, 338817, 1437, 65536⟩
    (by decide) selected_cut_42843

theorem selected_cut_42844 : selected 9 ⟨1170520, by decide⟩
    (prefixPartial 12 338818) = some ⟨12, 2, 0, 1170520, 338818, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_338818_1170520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338818 ⟨1170520, by decide⟩ :=
  accepted_of_selected 12 338818 ⟨1170520, by decide⟩ ⟨12, 2, 0, 1170520, 338818, 1385, 65536⟩
    (by decide) selected_cut_42844

theorem selected_cut_42845 : selected 9 ⟨1170540, by decide⟩
    (prefixPartial 12 338819) = some ⟨12, 2, 0, 1170540, 338819, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_338819_1170540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338819 ⟨1170540, by decide⟩ :=
  accepted_of_selected 12 338819 ⟨1170540, by decide⟩ ⟨12, 2, 0, 1170540, 338819, 1349, 65536⟩
    (by decide) selected_cut_42845

theorem unmarked_context_11_84704_1170541 : frontier 10 ⟨1170541, by decide⟩
    (prefixCache 11 84704) (prefixPartial 11 84704) = false := by
  decide +kernel

theorem node_context_11_84704_1170541 : EJMOriginalGlobalDAGData.nodes 10 ⟨1170541, by decide⟩ =
    .split (coordinate 11) (![⟨1120586, by decide⟩,⟨1170497, by decide⟩,⟨1170520, by decide⟩,⟨1170540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84704_1170541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84704 ⟨1170541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84704
    ⟨1170541, by decide⟩ (by decide) (![⟨1120586, by decide⟩,⟨1170497, by decide⟩,⟨1170520, by decide⟩,⟨1170540, by decide⟩]) unmarked_context_11_84704_1170541 node_context_11_84704_1170541
  intro a
  fin_cases a
  · exact context_12_338816_1120586
  · exact context_12_338817_1170497
  · exact context_12_338818_1170520
  · exact context_12_338819_1170540

theorem selected_cut_42846 : selected 9 ⟨1170558, by decide⟩
    (prefixPartial 12 338820) = some ⟨12, 2, 0, 1170558, 338820, 1141, 65536⟩ := by
  decide +kernel

theorem context_12_338820_1170558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338820 ⟨1170558, by decide⟩ :=
  accepted_of_selected 12 338820 ⟨1170558, by decide⟩ ⟨12, 2, 0, 1170558, 338820, 1141, 65536⟩
    (by decide) selected_cut_42846

theorem selected_cut_42847 : selected 9 ⟨1170577, by decide⟩
    (prefixPartial 12 338821) = some ⟨12, 2, 0, 1170577, 338821, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_338821_1170577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338821 ⟨1170577, by decide⟩ :=
  accepted_of_selected 12 338821 ⟨1170577, by decide⟩ ⟨12, 2, 0, 1170577, 338821, 1325, 65536⟩
    (by decide) selected_cut_42847

theorem selected_cut_42848 : selected 9 ⟨1170597, by decide⟩
    (prefixPartial 12 338822) = some ⟨12, 2, 0, 1170597, 338822, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_338822_1170597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338822 ⟨1170597, by decide⟩ :=
  accepted_of_selected 12 338822 ⟨1170597, by decide⟩ ⟨12, 2, 0, 1170597, 338822, 1285, 65536⟩
    (by decide) selected_cut_42848

theorem selected_cut_42849 : selected 9 ⟨1170620, by decide⟩
    (prefixPartial 12 338823) = some ⟨12, 2, 0, 1170620, 338823, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_338823_1170620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338823 ⟨1170620, by decide⟩ :=
  accepted_of_selected 12 338823 ⟨1170620, by decide⟩ ⟨12, 2, 0, 1170620, 338823, 1345, 65536⟩
    (by decide) selected_cut_42849

theorem unmarked_context_11_84705_1170621 : frontier 10 ⟨1170621, by decide⟩
    (prefixCache 11 84705) (prefixPartial 11 84705) = false := by
  decide +kernel

theorem node_context_11_84705_1170621 : EJMOriginalGlobalDAGData.nodes 10 ⟨1170621, by decide⟩ =
    .split (coordinate 11) (![⟨1170558, by decide⟩,⟨1170577, by decide⟩,⟨1170597, by decide⟩,⟨1170620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84705_1170621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84705 ⟨1170621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84705
    ⟨1170621, by decide⟩ (by decide) (![⟨1170558, by decide⟩,⟨1170577, by decide⟩,⟨1170597, by decide⟩,⟨1170620, by decide⟩]) unmarked_context_11_84705_1170621 node_context_11_84705_1170621
  intro a
  fin_cases a
  · exact context_12_338820_1170558
  · exact context_12_338821_1170577
  · exact context_12_338822_1170597
  · exact context_12_338823_1170620

theorem selected_cut_42850 : selected 10 ⟨1170667, by decide⟩
    (prefixPartial 11 84706) = some ⟨11, 2, 0, 1170667, 84706, 3341, 262144⟩ := by
  decide +kernel

theorem context_11_84706_1170667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84706 ⟨1170667, by decide⟩ :=
  accepted_of_selected 11 84706 ⟨1170667, by decide⟩ ⟨11, 2, 0, 1170667, 84706, 3341, 262144⟩
    (by decide) selected_cut_42850

theorem selected_cut_42851 : selected 10 ⟨1170709, by decide⟩
    (prefixPartial 11 84707) = some ⟨11, 2, 0, 1170709, 84707, 3273, 262144⟩ := by
  decide +kernel

theorem context_11_84707_1170709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84707 ⟨1170709, by decide⟩ :=
  accepted_of_selected 11 84707 ⟨1170709, by decide⟩ ⟨11, 2, 0, 1170709, 84707, 3273, 262144⟩
    (by decide) selected_cut_42851

theorem unmarked_context_10_21176_1170710 : frontier 11 ⟨1170710, by decide⟩
    (prefixCache 10 21176) (prefixPartial 10 21176) = false := by
  decide +kernel

theorem node_context_10_21176_1170710 : EJMOriginalGlobalDAGData.nodes 11 ⟨1170710, by decide⟩ =
    .split (coordinate 10) (![⟨1170541, by decide⟩,⟨1170621, by decide⟩,⟨1170667, by decide⟩,⟨1170709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21176_1170710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21176 ⟨1170710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21176
    ⟨1170710, by decide⟩ (by decide) (![⟨1170541, by decide⟩,⟨1170621, by decide⟩,⟨1170667, by decide⟩,⟨1170709, by decide⟩]) unmarked_context_10_21176_1170710 node_context_10_21176_1170710
  intro a
  fin_cases a
  · exact context_11_84704_1170541
  · exact context_11_84705_1170621
  · exact context_11_84706_1170667
  · exact context_11_84707_1170709

theorem selected_cut_42852 : selected 9 ⟨1170730, by decide⟩
    (prefixPartial 12 338832) = some ⟨12, 2, 0, 1170730, 338832, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_338832_1170730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338832 ⟨1170730, by decide⟩ :=
  accepted_of_selected 12 338832 ⟨1170730, by decide⟩ ⟨12, 2, 0, 1170730, 338832, 1137, 65536⟩
    (by decide) selected_cut_42852

theorem selected_cut_42853 : selected 9 ⟨1170750, by decide⟩
    (prefixPartial 12 338833) = some ⟨12, 2, 0, 1170750, 338833, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_338833_1170750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338833 ⟨1170750, by decide⟩ :=
  accepted_of_selected 12 338833 ⟨1170750, by decide⟩ ⟨12, 2, 0, 1170750, 338833, 1373, 65536⟩
    (by decide) selected_cut_42853

theorem selected_cut_42854 : selected 9 ⟨1170778, by decide⟩
    (prefixPartial 12 338834) = some ⟨12, 2, 0, 1170778, 338834, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_338834_1170778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338834 ⟨1170778, by decide⟩ :=
  accepted_of_selected 12 338834 ⟨1170778, by decide⟩ ⟨12, 2, 0, 1170778, 338834, 1413, 65536⟩
    (by decide) selected_cut_42854

theorem selected_cut_42855 : selected 9 ⟨1170795, by decide⟩
    (prefixPartial 12 338835) = some ⟨12, 2, 0, 1170795, 338835, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_338835_1170795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338835 ⟨1170795, by decide⟩ :=
  accepted_of_selected 12 338835 ⟨1170795, by decide⟩ ⟨12, 2, 0, 1170795, 338835, 1201, 65536⟩
    (by decide) selected_cut_42855

theorem unmarked_context_11_84708_1170796 : frontier 10 ⟨1170796, by decide⟩
    (prefixCache 11 84708) (prefixPartial 11 84708) = false := by
  decide +kernel

theorem node_context_11_84708_1170796 : EJMOriginalGlobalDAGData.nodes 10 ⟨1170796, by decide⟩ =
    .split (coordinate 11) (![⟨1170730, by decide⟩,⟨1170750, by decide⟩,⟨1170778, by decide⟩,⟨1170795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84708_1170796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84708 ⟨1170796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84708
    ⟨1170796, by decide⟩ (by decide) (![⟨1170730, by decide⟩,⟨1170750, by decide⟩,⟨1170778, by decide⟩,⟨1170795, by decide⟩]) unmarked_context_11_84708_1170796 node_context_11_84708_1170796
  intro a
  fin_cases a
  · exact context_12_338832_1170730
  · exact context_12_338833_1170750
  · exact context_12_338834_1170778
  · exact context_12_338835_1170795

theorem selected_cut_42856 : selected 10 ⟨1170835, by decide⟩
    (prefixPartial 11 84709) = some ⟨11, 2, 0, 1170835, 84709, 1401, 262144⟩ := by
  decide +kernel

theorem context_11_84709_1170835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84709 ⟨1170835, by decide⟩ :=
  accepted_of_selected 11 84709 ⟨1170835, by decide⟩ ⟨11, 2, 0, 1170835, 84709, 1401, 262144⟩
    (by decide) selected_cut_42856

theorem selected_cut_42857 : selected 10 ⟨1170891, by decide⟩
    (prefixPartial 11 84710) = some ⟨11, 2, 0, 1170891, 84710, 2885, 262144⟩ := by
  decide +kernel

theorem context_11_84710_1170891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84710 ⟨1170891, by decide⟩ :=
  accepted_of_selected 11 84710 ⟨1170891, by decide⟩ ⟨11, 2, 0, 1170891, 84710, 2885, 262144⟩
    (by decide) selected_cut_42857

theorem selected_cut_42858 : selected 10 ⟨1170942, by decide⟩
    (prefixPartial 11 84711) = some ⟨11, 2, 0, 1170942, 84711, 2901, 262144⟩ := by
  decide +kernel

theorem context_11_84711_1170942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84711 ⟨1170942, by decide⟩ :=
  accepted_of_selected 11 84711 ⟨1170942, by decide⟩ ⟨11, 2, 0, 1170942, 84711, 2901, 262144⟩
    (by decide) selected_cut_42858

theorem unmarked_context_10_21177_1170943 : frontier 11 ⟨1170943, by decide⟩
    (prefixCache 10 21177) (prefixPartial 10 21177) = false := by
  decide +kernel

theorem node_context_10_21177_1170943 : EJMOriginalGlobalDAGData.nodes 11 ⟨1170943, by decide⟩ =
    .split (coordinate 10) (![⟨1170796, by decide⟩,⟨1170835, by decide⟩,⟨1170891, by decide⟩,⟨1170942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21177_1170943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21177 ⟨1170943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21177
    ⟨1170943, by decide⟩ (by decide) (![⟨1170796, by decide⟩,⟨1170835, by decide⟩,⟨1170891, by decide⟩,⟨1170942, by decide⟩]) unmarked_context_10_21177_1170943 node_context_10_21177_1170943
  intro a
  fin_cases a
  · exact context_11_84708_1170796
  · exact context_11_84709_1170835
  · exact context_11_84710_1170891
  · exact context_11_84711_1170942

theorem selected_cut_42859 : selected 10 ⟨1170975, by decide⟩
    (prefixPartial 11 84712) = some ⟨11, 2, 0, 1170975, 84712, 2337, 262144⟩ := by
  decide +kernel

theorem context_11_84712_1170975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84712 ⟨1170975, by decide⟩ :=
  accepted_of_selected 11 84712 ⟨1170975, by decide⟩ ⟨11, 2, 0, 1170975, 84712, 2337, 262144⟩
    (by decide) selected_cut_42859

theorem selected_cut_42860 : selected 10 ⟨1170997, by decide⟩
    (prefixPartial 11 84713) = some ⟨11, 2, 0, 1170997, 84713, 1089, 262144⟩ := by
  decide +kernel

theorem context_11_84713_1170997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84713 ⟨1170997, by decide⟩ :=
  accepted_of_selected 11 84713 ⟨1170997, by decide⟩ ⟨11, 2, 0, 1170997, 84713, 1089, 262144⟩
    (by decide) selected_cut_42860

theorem selected_cut_42861 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84714) = some ⟨11, 1, 0, 1109453, 84714, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84714_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84714 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84714 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84714, 1, 262144⟩
    (by decide) selected_cut_42861

theorem selected_cut_42862 : selected 10 ⟨1171016, by decide⟩
    (prefixPartial 11 84715) = some ⟨11, 2, 0, 1171016, 84715, 1413, 262144⟩ := by
  decide +kernel

theorem context_11_84715_1171016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84715 ⟨1171016, by decide⟩ :=
  accepted_of_selected 11 84715 ⟨1171016, by decide⟩ ⟨11, 2, 0, 1171016, 84715, 1413, 262144⟩
    (by decide) selected_cut_42862

theorem unmarked_context_10_21178_1171017 : frontier 11 ⟨1171017, by decide⟩
    (prefixCache 10 21178) (prefixPartial 10 21178) = false := by
  decide +kernel

theorem node_context_10_21178_1171017 : EJMOriginalGlobalDAGData.nodes 11 ⟨1171017, by decide⟩ =
    .split (coordinate 10) (![⟨1170975, by decide⟩,⟨1170997, by decide⟩,⟨1109453, by decide⟩,⟨1171016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21178_1171017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21178 ⟨1171017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21178
    ⟨1171017, by decide⟩ (by decide) (![⟨1170975, by decide⟩,⟨1170997, by decide⟩,⟨1109453, by decide⟩,⟨1171016, by decide⟩]) unmarked_context_10_21178_1171017 node_context_10_21178_1171017
  intro a
  fin_cases a
  · exact context_11_84712_1170975
  · exact context_11_84713_1170997
  · exact context_11_84714_1109453
  · exact context_11_84715_1171016

theorem selected_cut_42863 : selected 10 ⟨1171082, by decide⟩
    (prefixPartial 11 84716) = some ⟨11, 2, 0, 1171082, 84716, 3841, 262144⟩ := by
  decide +kernel

theorem context_11_84716_1171082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84716 ⟨1171082, by decide⟩ :=
  accepted_of_selected 11 84716 ⟨1171082, by decide⟩ ⟨11, 2, 0, 1171082, 84716, 3841, 262144⟩
    (by decide) selected_cut_42863

theorem selected_cut_42864 : selected 10 ⟨1171132, by decide⟩
    (prefixPartial 11 84717) = some ⟨11, 2, 0, 1171132, 84717, 3313, 262144⟩ := by
  decide +kernel

theorem context_11_84717_1171132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84717 ⟨1171132, by decide⟩ :=
  accepted_of_selected 11 84717 ⟨1171132, by decide⟩ ⟨11, 2, 0, 1171132, 84717, 3313, 262144⟩
    (by decide) selected_cut_42864

theorem selected_cut_42865 : selected 10 ⟨1171171, by decide⟩
    (prefixPartial 11 84718) = some ⟨11, 2, 0, 1171171, 84718, 2049, 262144⟩ := by
  decide +kernel

theorem context_11_84718_1171171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84718 ⟨1171171, by decide⟩ :=
  accepted_of_selected 11 84718 ⟨1171171, by decide⟩ ⟨11, 2, 0, 1171171, 84718, 2049, 262144⟩
    (by decide) selected_cut_42865

theorem selected_cut_42866 : selected 10 ⟨1171200, by decide⟩
    (prefixPartial 11 84719) = some ⟨11, 2, 0, 1171200, 84719, 1377, 262144⟩ := by
  decide +kernel

theorem context_11_84719_1171200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84719 ⟨1171200, by decide⟩ :=
  accepted_of_selected 11 84719 ⟨1171200, by decide⟩ ⟨11, 2, 0, 1171200, 84719, 1377, 262144⟩
    (by decide) selected_cut_42866

theorem unmarked_context_10_21179_1171201 : frontier 11 ⟨1171201, by decide⟩
    (prefixCache 10 21179) (prefixPartial 10 21179) = false := by
  decide +kernel

theorem node_context_10_21179_1171201 : EJMOriginalGlobalDAGData.nodes 11 ⟨1171201, by decide⟩ =
    .split (coordinate 10) (![⟨1171082, by decide⟩,⟨1171132, by decide⟩,⟨1171171, by decide⟩,⟨1171200, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21179_1171201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21179 ⟨1171201, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21179
    ⟨1171201, by decide⟩ (by decide) (![⟨1171082, by decide⟩,⟨1171132, by decide⟩,⟨1171171, by decide⟩,⟨1171200, by decide⟩]) unmarked_context_10_21179_1171201 node_context_10_21179_1171201
  intro a
  fin_cases a
  · exact context_11_84716_1171082
  · exact context_11_84717_1171132
  · exact context_11_84718_1171171
  · exact context_11_84719_1171200

theorem unmarked_context_9_5294_1171202 : frontier 12 ⟨1171202, by decide⟩
    (prefixCache 9 5294) (prefixPartial 9 5294) = false := by
  decide +kernel

theorem node_context_9_5294_1171202 : EJMOriginalGlobalDAGData.nodes 12 ⟨1171202, by decide⟩ =
    .split (coordinate 9) (![⟨1170710, by decide⟩,⟨1170943, by decide⟩,⟨1171017, by decide⟩,⟨1171201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5294_1171202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5294 ⟨1171202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5294
    ⟨1171202, by decide⟩ (by decide) (![⟨1170710, by decide⟩,⟨1170943, by decide⟩,⟨1171017, by decide⟩,⟨1171201, by decide⟩]) unmarked_context_9_5294_1171202 node_context_9_5294_1171202
  intro a
  fin_cases a
  · exact context_10_21176_1170710
  · exact context_10_21177_1170943
  · exact context_10_21178_1171017
  · exact context_10_21179_1171201

theorem selected_cut_42867 : selected 10 ⟨1171217, by decide⟩
    (prefixPartial 11 84720) = some ⟨11, 2, 0, 1171217, 84720, 1133, 262144⟩ := by
  decide +kernel

theorem context_11_84720_1171217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84720 ⟨1171217, by decide⟩ :=
  accepted_of_selected 11 84720 ⟨1171217, by decide⟩ ⟨11, 2, 0, 1171217, 84720, 1133, 262144⟩
    (by decide) selected_cut_42867

theorem selected_cut_42868 : selected 10 ⟨1171244, by decide⟩
    (prefixPartial 11 84721) = some ⟨11, 2, 0, 1171244, 84721, 1817, 262144⟩ := by
  decide +kernel

theorem context_11_84721_1171244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84721 ⟨1171244, by decide⟩ :=
  accepted_of_selected 11 84721 ⟨1171244, by decide⟩ ⟨11, 2, 0, 1171244, 84721, 1817, 262144⟩
    (by decide) selected_cut_42868

theorem selected_cut_42869 : selected 10 ⟨1171266, by decide⟩
    (prefixPartial 11 84722) = some ⟨11, 2, 0, 1171266, 84722, 1549, 262144⟩ := by
  decide +kernel

theorem context_11_84722_1171266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84722 ⟨1171266, by decide⟩ :=
  accepted_of_selected 11 84722 ⟨1171266, by decide⟩ ⟨11, 2, 0, 1171266, 84722, 1549, 262144⟩
    (by decide) selected_cut_42869

theorem selected_cut_42870 : selected 10 ⟨1171281, by decide⟩
    (prefixPartial 11 84723) = some ⟨11, 2, 0, 1171281, 84723, 1185, 262144⟩ := by
  decide +kernel

theorem context_11_84723_1171281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84723 ⟨1171281, by decide⟩ :=
  accepted_of_selected 11 84723 ⟨1171281, by decide⟩ ⟨11, 2, 0, 1171281, 84723, 1185, 262144⟩
    (by decide) selected_cut_42870

theorem unmarked_context_10_21180_1171282 : frontier 11 ⟨1171282, by decide⟩
    (prefixCache 10 21180) (prefixPartial 10 21180) = false := by
  decide +kernel

theorem node_context_10_21180_1171282 : EJMOriginalGlobalDAGData.nodes 11 ⟨1171282, by decide⟩ =
    .split (coordinate 10) (![⟨1171217, by decide⟩,⟨1171244, by decide⟩,⟨1171266, by decide⟩,⟨1171281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21180_1171282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21180 ⟨1171282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21180
    ⟨1171282, by decide⟩ (by decide) (![⟨1171217, by decide⟩,⟨1171244, by decide⟩,⟨1171266, by decide⟩,⟨1171281, by decide⟩]) unmarked_context_10_21180_1171282 node_context_10_21180_1171282
  intro a
  fin_cases a
  · exact context_11_84720_1171217
  · exact context_11_84721_1171244
  · exact context_11_84722_1171266
  · exact context_11_84723_1171281

theorem selected_cut_42871 : selected 11 ⟨1171336, by decide⟩
    (prefixPartial 10 21181) = some ⟨10, 2, 0, 1171336, 21181, 3709, 1048576⟩ := by
  decide +kernel

theorem context_10_21181_1171336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21181 ⟨1171336, by decide⟩ :=
  accepted_of_selected 10 21181 ⟨1171336, by decide⟩ ⟨10, 2, 0, 1171336, 21181, 3709, 1048576⟩
    (by decide) selected_cut_42871

theorem selected_cut_42872 : selected 11 ⟨1171376, by decide⟩
    (prefixPartial 10 21182) = some ⟨10, 2, 0, 1171376, 21182, 1745, 1048576⟩ := by
  decide +kernel

theorem context_10_21182_1171376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21182 ⟨1171376, by decide⟩ :=
  accepted_of_selected 10 21182 ⟨1171376, by decide⟩ ⟨10, 2, 0, 1171376, 21182, 1745, 1048576⟩
    (by decide) selected_cut_42872

theorem selected_cut_42873 : selected 11 ⟨1171407, by decide⟩
    (prefixPartial 10 21183) = some ⟨10, 2, 0, 1171407, 21183, 441, 1048576⟩ := by
  decide +kernel

theorem context_10_21183_1171407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21183 ⟨1171407, by decide⟩ :=
  accepted_of_selected 10 21183 ⟨1171407, by decide⟩ ⟨10, 2, 0, 1171407, 21183, 441, 1048576⟩
    (by decide) selected_cut_42873

theorem unmarked_context_9_5295_1171408 : frontier 12 ⟨1171408, by decide⟩
    (prefixCache 9 5295) (prefixPartial 9 5295) = false := by
  decide +kernel

theorem node_context_9_5295_1171408 : EJMOriginalGlobalDAGData.nodes 12 ⟨1171408, by decide⟩ =
    .split (coordinate 9) (![⟨1171282, by decide⟩,⟨1171336, by decide⟩,⟨1171376, by decide⟩,⟨1171407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5295_1171408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5295 ⟨1171408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5295
    ⟨1171408, by decide⟩ (by decide) (![⟨1171282, by decide⟩,⟨1171336, by decide⟩,⟨1171376, by decide⟩,⟨1171407, by decide⟩]) unmarked_context_9_5295_1171408 node_context_9_5295_1171408
  intro a
  fin_cases a
  · exact context_10_21180_1171282
  · exact context_10_21181_1171336
  · exact context_10_21182_1171376
  · exact context_10_21183_1171407

theorem unmarked_context_8_1323_1171409 : frontier 13 ⟨1171409, by decide⟩
    (prefixCache 8 1323) (prefixPartial 8 1323) = false := by
  decide +kernel

theorem node_context_8_1323_1171409 : EJMOriginalGlobalDAGData.nodes 13 ⟨1171409, by decide⟩ =
    .split (coordinate 8) (![⟨1169519, by decide⟩,⟨1170475, by decide⟩,⟨1171202, by decide⟩,⟨1171408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1323_1171409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1323 ⟨1171409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1323
    ⟨1171409, by decide⟩ (by decide) (![⟨1169519, by decide⟩,⟨1170475, by decide⟩,⟨1171202, by decide⟩,⟨1171408, by decide⟩]) unmarked_context_8_1323_1171409 node_context_8_1323_1171409
  intro a
  fin_cases a
  · exact context_9_5292_1169519
  · exact context_9_5293_1170475
  · exact context_9_5294_1171202
  · exact context_9_5295_1171408

theorem unmarked_context_7_330_1171410 : frontier 14 ⟨1171410, by decide⟩
    (prefixCache 7 330) (prefixPartial 7 330) = false := by
  decide +kernel

theorem node_context_7_330_1171410 : EJMOriginalGlobalDAGData.nodes 14 ⟨1171410, by decide⟩ =
    .split (coordinate 7) (![⟨1161435, by decide⟩,⟨1164296, by decide⟩,⟨1167729, by decide⟩,⟨1171409, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_330_1171410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 330 ⟨1171410, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 330
    ⟨1171410, by decide⟩ (by decide) (![⟨1161435, by decide⟩,⟨1164296, by decide⟩,⟨1167729, by decide⟩,⟨1171409, by decide⟩]) unmarked_context_7_330_1171410 node_context_7_330_1171410
  intro a
  fin_cases a
  · exact context_8_1320_1161435
  · exact context_8_1321_1164296
  · exact context_8_1322_1167729
  · exact context_8_1323_1171409

theorem selected_cut_42874 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84736) = some ⟨11, 1, 0, 434745, 84736, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84736_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84736 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84736 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84736, 1, 262144⟩
    (by decide) selected_cut_42874

theorem selected_cut_42875 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 338948) = some ⟨12, 1, 0, 448748, 338948, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338948_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338948 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 338948 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 338948, 1, 65536⟩
    (by decide) selected_cut_42875

theorem selected_cut_42876 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 338949) = some ⟨12, 1, 0, 34034, 338949, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338949_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338949 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 338949 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 338949, 1, 65536⟩
    (by decide) selected_cut_42876

theorem selected_cut_42877 : selected 9 ⟨1171493, by decide⟩
    (prefixPartial 12 338950) = some ⟨12, 2, 0, 1171493, 338950, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_338950_1171493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338950 ⟨1171493, by decide⟩ :=
  accepted_of_selected 12 338950 ⟨1171493, by decide⟩ ⟨12, 2, 0, 1171493, 338950, 2861, 65536⟩
    (by decide) selected_cut_42877

theorem selected_cut_42878 : selected 9 ⟨1171555, by decide⟩
    (prefixPartial 12 338951) = some ⟨12, 2, 0, 1171555, 338951, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_338951_1171555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338951 ⟨1171555, by decide⟩ :=
  accepted_of_selected 12 338951 ⟨1171555, by decide⟩ ⟨12, 2, 0, 1171555, 338951, 3041, 65536⟩
    (by decide) selected_cut_42878

theorem unmarked_context_11_84737_1171556 : frontier 10 ⟨1171556, by decide⟩
    (prefixCache 11 84737) (prefixPartial 11 84737) = false := by
  decide +kernel

theorem node_context_11_84737_1171556 : EJMOriginalGlobalDAGData.nodes 10 ⟨1171556, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1171493, by decide⟩,⟨1171555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84737_1171556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84737 ⟨1171556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84737
    ⟨1171556, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1171493, by decide⟩,⟨1171555, by decide⟩]) unmarked_context_11_84737_1171556 node_context_11_84737_1171556
  intro a
  fin_cases a
  · exact context_12_338948_448748
  · exact context_12_338949_34034
  · exact context_12_338950_1171493
  · exact context_12_338951_1171555

theorem selected_cut_42879 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 338952) = some ⟨12, 1, 0, 448748, 338952, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338952_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338952 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 338952 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 338952, 1, 65536⟩
    (by decide) selected_cut_42879

theorem selected_cut_42880 : selected 9 ⟨1171642, by decide⟩
    (prefixPartial 12 338953) = some ⟨12, 2, 0, 1171642, 338953, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_338953_1171642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338953 ⟨1171642, by decide⟩ :=
  accepted_of_selected 12 338953 ⟨1171642, by decide⟩ ⟨12, 2, 0, 1171642, 338953, 3265, 65536⟩
    (by decide) selected_cut_42880

theorem selected_cut_42881 : selected 9 ⟨1171702, by decide⟩
    (prefixPartial 12 338954) = some ⟨12, 2, 0, 1171702, 338954, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_338954_1171702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338954 ⟨1171702, by decide⟩ :=
  accepted_of_selected 12 338954 ⟨1171702, by decide⟩ ⟨12, 2, 0, 1171702, 338954, 2789, 65536⟩
    (by decide) selected_cut_42881

theorem selected_cut_42882 : selected 9 ⟨1171774, by decide⟩
    (prefixPartial 12 338955) = some ⟨12, 2, 0, 1171774, 338955, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_338955_1171774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338955 ⟨1171774, by decide⟩ :=
  accepted_of_selected 12 338955 ⟨1171774, by decide⟩ ⟨12, 2, 0, 1171774, 338955, 3181, 65536⟩
    (by decide) selected_cut_42882

theorem unmarked_context_11_84738_1171775 : frontier 10 ⟨1171775, by decide⟩
    (prefixCache 11 84738) (prefixPartial 11 84738) = false := by
  decide +kernel

theorem node_context_11_84738_1171775 : EJMOriginalGlobalDAGData.nodes 10 ⟨1171775, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1171642, by decide⟩,⟨1171702, by decide⟩,⟨1171774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84738_1171775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84738 ⟨1171775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84738
    ⟨1171775, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1171642, by decide⟩,⟨1171702, by decide⟩,⟨1171774, by decide⟩]) unmarked_context_11_84738_1171775 node_context_11_84738_1171775
  intro a
  fin_cases a
  · exact context_12_338952_448748
  · exact context_12_338953_1171642
  · exact context_12_338954_1171702
  · exact context_12_338955_1171774

theorem selected_cut_42883 : selected 10 ⟨1171824, by decide⟩
    (prefixPartial 11 84739) = some ⟨11, 2, 0, 1171824, 84739, 2737, 262144⟩ := by
  decide +kernel

theorem context_11_84739_1171824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84739 ⟨1171824, by decide⟩ :=
  accepted_of_selected 11 84739 ⟨1171824, by decide⟩ ⟨11, 2, 0, 1171824, 84739, 2737, 262144⟩
    (by decide) selected_cut_42883

theorem unmarked_context_10_21184_1171825 : frontier 11 ⟨1171825, by decide⟩
    (prefixCache 10 21184) (prefixPartial 10 21184) = false := by
  decide +kernel

theorem node_context_10_21184_1171825 : EJMOriginalGlobalDAGData.nodes 11 ⟨1171825, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1171556, by decide⟩,⟨1171775, by decide⟩,⟨1171824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21184_1171825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21184 ⟨1171825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21184
    ⟨1171825, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1171556, by decide⟩,⟨1171775, by decide⟩,⟨1171824, by decide⟩]) unmarked_context_10_21184_1171825 node_context_10_21184_1171825
  intro a
  fin_cases a
  · exact context_11_84736_434745
  · exact context_11_84737_1171556
  · exact context_11_84738_1171775
  · exact context_11_84739_1171824

theorem selected_cut_42884 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338960) = some ⟨12, 1, 0, 1108174, 338960, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338960_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338960 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338960 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338960, 1, 65536⟩
    (by decide) selected_cut_42884

theorem selected_cut_42885 : selected 9 ⟨1171889, by decide⟩
    (prefixPartial 12 338961) = some ⟨12, 2, 0, 1171889, 338961, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_338961_1171889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338961 ⟨1171889, by decide⟩ :=
  accepted_of_selected 12 338961 ⟨1171889, by decide⟩ ⟨12, 2, 0, 1171889, 338961, 2801, 65536⟩
    (by decide) selected_cut_42885

theorem selected_cut_42886 : selected 9 ⟨1171941, by decide⟩
    (prefixPartial 12 338962) = some ⟨12, 2, 0, 1171941, 338962, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_338962_1171941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338962 ⟨1171941, by decide⟩ :=
  accepted_of_selected 12 338962 ⟨1171941, by decide⟩ ⟨12, 2, 0, 1171941, 338962, 2597, 65536⟩
    (by decide) selected_cut_42886

theorem selected_cut_42887 : selected 9 ⟨1172001, by decide⟩
    (prefixPartial 12 338963) = some ⟨12, 2, 0, 1172001, 338963, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_338963_1172001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338963 ⟨1172001, by decide⟩ :=
  accepted_of_selected 12 338963 ⟨1172001, by decide⟩ ⟨12, 2, 0, 1172001, 338963, 2857, 65536⟩
    (by decide) selected_cut_42887

theorem unmarked_context_11_84740_1172002 : frontier 10 ⟨1172002, by decide⟩
    (prefixCache 11 84740) (prefixPartial 11 84740) = false := by
  decide +kernel

theorem node_context_11_84740_1172002 : EJMOriginalGlobalDAGData.nodes 10 ⟨1172002, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1171889, by decide⟩,⟨1171941, by decide⟩,⟨1172001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84740_1172002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84740 ⟨1172002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84740
    ⟨1172002, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1171889, by decide⟩,⟨1171941, by decide⟩,⟨1172001, by decide⟩]) unmarked_context_11_84740_1172002 node_context_11_84740_1172002
  intro a
  fin_cases a
  · exact context_12_338960_1108174
  · exact context_12_338961_1171889
  · exact context_12_338962_1171941
  · exact context_12_338963_1172001

theorem selected_cut_42888 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338964) = some ⟨12, 1, 0, 1108174, 338964, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338964_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338964 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338964 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338964, 1, 65536⟩
    (by decide) selected_cut_42888

theorem selected_cut_42889 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 338965) = some ⟨12, 1, 0, 1172003, 338965, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338965_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338965 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 338965 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 338965, 1, 65536⟩
    (by decide) selected_cut_42889

theorem selected_cut_42890 : selected 9 ⟨1172066, by decide⟩
    (prefixPartial 12 338966) = some ⟨12, 2, 0, 1172066, 338966, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_338966_1172066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338966 ⟨1172066, by decide⟩ :=
  accepted_of_selected 12 338966 ⟨1172066, by decide⟩ ⟨12, 2, 0, 1172066, 338966, 3053, 65536⟩
    (by decide) selected_cut_42890

theorem selected_cut_42891 : selected 9 ⟨1172135, by decide⟩
    (prefixPartial 12 338967) = some ⟨12, 2, 0, 1172135, 338967, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_338967_1172135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338967 ⟨1172135, by decide⟩ :=
  accepted_of_selected 12 338967 ⟨1172135, by decide⟩ ⟨12, 2, 0, 1172135, 338967, 3257, 65536⟩
    (by decide) selected_cut_42891

theorem unmarked_context_11_84741_1172136 : frontier 10 ⟨1172136, by decide⟩
    (prefixCache 11 84741) (prefixPartial 11 84741) = false := by
  decide +kernel

theorem node_context_11_84741_1172136 : EJMOriginalGlobalDAGData.nodes 10 ⟨1172136, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1172003, by decide⟩,⟨1172066, by decide⟩,⟨1172135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84741_1172136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84741 ⟨1172136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84741
    ⟨1172136, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1172003, by decide⟩,⟨1172066, by decide⟩,⟨1172135, by decide⟩]) unmarked_context_11_84741_1172136 node_context_11_84741_1172136
  intro a
  fin_cases a
  · exact context_12_338964_1108174
  · exact context_12_338965_1172003
  · exact context_12_338966_1172066
  · exact context_12_338967_1172135

theorem selected_cut_42892 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338968) = some ⟨12, 1, 0, 1108174, 338968, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338968_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338968 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338968 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338968, 1, 65536⟩
    (by decide) selected_cut_42892

theorem selected_cut_42893 : selected 9 ⟨1172199, by decide⟩
    (prefixPartial 12 338969) = some ⟨12, 2, 0, 1172199, 338969, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_338969_1172199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338969 ⟨1172199, by decide⟩ :=
  accepted_of_selected 12 338969 ⟨1172199, by decide⟩ ⟨12, 2, 0, 1172199, 338969, 2957, 65536⟩
    (by decide) selected_cut_42893

theorem selected_cut_42894 : selected 9 ⟨1172244, by decide⟩
    (prefixPartial 12 338970) = some ⟨12, 2, 0, 1172244, 338970, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_338970_1172244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338970 ⟨1172244, by decide⟩ :=
  accepted_of_selected 12 338970 ⟨1172244, by decide⟩ ⟨12, 2, 0, 1172244, 338970, 2665, 65536⟩
    (by decide) selected_cut_42894

theorem selected_cut_42895 : selected 9 ⟨1172302, by decide⟩
    (prefixPartial 12 338971) = some ⟨12, 2, 0, 1172302, 338971, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_338971_1172302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338971 ⟨1172302, by decide⟩ :=
  accepted_of_selected 12 338971 ⟨1172302, by decide⟩ ⟨12, 2, 0, 1172302, 338971, 3069, 65536⟩
    (by decide) selected_cut_42895

theorem unmarked_context_11_84742_1172303 : frontier 10 ⟨1172303, by decide⟩
    (prefixCache 11 84742) (prefixPartial 11 84742) = false := by
  decide +kernel

theorem node_context_11_84742_1172303 : EJMOriginalGlobalDAGData.nodes 10 ⟨1172303, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1172199, by decide⟩,⟨1172244, by decide⟩,⟨1172302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84742_1172303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84742 ⟨1172303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84742
    ⟨1172303, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1172199, by decide⟩,⟨1172244, by decide⟩,⟨1172302, by decide⟩]) unmarked_context_11_84742_1172303 node_context_11_84742_1172303
  intro a
  fin_cases a
  · exact context_12_338968_1108174
  · exact context_12_338969_1172199
  · exact context_12_338970_1172244
  · exact context_12_338971_1172302

theorem selected_cut_42896 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338972) = some ⟨12, 1, 0, 1108174, 338972, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338972_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338972 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338972 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338972, 1, 65536⟩
    (by decide) selected_cut_42896

theorem selected_cut_42897 : selected 9 ⟨1172354, by decide⟩
    (prefixPartial 12 338973) = some ⟨12, 2, 0, 1172354, 338973, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_338973_1172354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338973 ⟨1172354, by decide⟩ :=
  accepted_of_selected 12 338973 ⟨1172354, by decide⟩ ⟨12, 2, 0, 1172354, 338973, 2797, 65536⟩
    (by decide) selected_cut_42897

theorem selected_cut_42898 : selected 9 ⟨1172409, by decide⟩
    (prefixPartial 12 338974) = some ⟨12, 2, 0, 1172409, 338974, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_338974_1172409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338974 ⟨1172409, by decide⟩ :=
  accepted_of_selected 12 338974 ⟨1172409, by decide⟩ ⟨12, 2, 0, 1172409, 338974, 2733, 65536⟩
    (by decide) selected_cut_42898

theorem selected_cut_42899 : selected 9 ⟨1172461, by decide⟩
    (prefixPartial 12 338975) = some ⟨12, 2, 0, 1172461, 338975, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_338975_1172461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338975 ⟨1172461, by decide⟩ :=
  accepted_of_selected 12 338975 ⟨1172461, by decide⟩ ⟨12, 2, 0, 1172461, 338975, 2845, 65536⟩
    (by decide) selected_cut_42899

theorem unmarked_context_11_84743_1172462 : frontier 10 ⟨1172462, by decide⟩
    (prefixCache 11 84743) (prefixPartial 11 84743) = false := by
  decide +kernel

theorem node_context_11_84743_1172462 : EJMOriginalGlobalDAGData.nodes 10 ⟨1172462, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1172354, by decide⟩,⟨1172409, by decide⟩,⟨1172461, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84743_1172462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84743 ⟨1172462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84743
    ⟨1172462, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1172354, by decide⟩,⟨1172409, by decide⟩,⟨1172461, by decide⟩]) unmarked_context_11_84743_1172462 node_context_11_84743_1172462
  intro a
  fin_cases a
  · exact context_12_338972_1108174
  · exact context_12_338973_1172354
  · exact context_12_338974_1172409
  · exact context_12_338975_1172461

theorem unmarked_context_10_21185_1172463 : frontier 11 ⟨1172463, by decide⟩
    (prefixCache 10 21185) (prefixPartial 10 21185) = false := by
  decide +kernel

theorem node_context_10_21185_1172463 : EJMOriginalGlobalDAGData.nodes 11 ⟨1172463, by decide⟩ =
    .split (coordinate 10) (![⟨1172002, by decide⟩,⟨1172136, by decide⟩,⟨1172303, by decide⟩,⟨1172462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21185_1172463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21185 ⟨1172463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21185
    ⟨1172463, by decide⟩ (by decide) (![⟨1172002, by decide⟩,⟨1172136, by decide⟩,⟨1172303, by decide⟩,⟨1172462, by decide⟩]) unmarked_context_10_21185_1172463 node_context_10_21185_1172463
  intro a
  fin_cases a
  · exact context_11_84740_1172002
  · exact context_11_84741_1172136
  · exact context_11_84742_1172303
  · exact context_11_84743_1172462

theorem selected_cut_42900 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338976) = some ⟨12, 1, 0, 1108174, 338976, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338976_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338976 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338976 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338976, 1, 65536⟩
    (by decide) selected_cut_42900

theorem selected_cut_42901 : selected 9 ⟨1172517, by decide⟩
    (prefixPartial 12 338977) = some ⟨12, 2, 0, 1172517, 338977, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_338977_1172517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338977 ⟨1172517, by decide⟩ :=
  accepted_of_selected 12 338977 ⟨1172517, by decide⟩ ⟨12, 2, 0, 1172517, 338977, 2801, 65536⟩
    (by decide) selected_cut_42901

theorem selected_cut_42902 : selected 9 ⟨1172573, by decide⟩
    (prefixPartial 12 338978) = some ⟨12, 2, 0, 1172573, 338978, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_338978_1172573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338978 ⟨1172573, by decide⟩ :=
  accepted_of_selected 12 338978 ⟨1172573, by decide⟩ ⟨12, 2, 0, 1172573, 338978, 2589, 65536⟩
    (by decide) selected_cut_42902

theorem selected_cut_42903 : selected 9 ⟨1172637, by decide⟩
    (prefixPartial 12 338979) = some ⟨12, 2, 0, 1172637, 338979, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_338979_1172637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338979 ⟨1172637, by decide⟩ :=
  accepted_of_selected 12 338979 ⟨1172637, by decide⟩ ⟨12, 2, 0, 1172637, 338979, 2885, 65536⟩
    (by decide) selected_cut_42903

theorem unmarked_context_11_84744_1172638 : frontier 10 ⟨1172638, by decide⟩
    (prefixCache 11 84744) (prefixPartial 11 84744) = false := by
  decide +kernel

theorem node_context_11_84744_1172638 : EJMOriginalGlobalDAGData.nodes 10 ⟨1172638, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1172517, by decide⟩,⟨1172573, by decide⟩,⟨1172637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84744_1172638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84744 ⟨1172638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84744
    ⟨1172638, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1172517, by decide⟩,⟨1172573, by decide⟩,⟨1172637, by decide⟩]) unmarked_context_11_84744_1172638 node_context_11_84744_1172638
  intro a
  fin_cases a
  · exact context_12_338976_1108174
  · exact context_12_338977_1172517
  · exact context_12_338978_1172573
  · exact context_12_338979_1172637

theorem selected_cut_42904 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338980) = some ⟨12, 1, 0, 1108174, 338980, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338980_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338980 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338980 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338980, 1, 65536⟩
    (by decide) selected_cut_42904

theorem selected_cut_42905 : selected 9 ⟨1172714, by decide⟩
    (prefixPartial 12 338981) = some ⟨12, 2, 0, 1172714, 338981, 3153, 65536⟩ := by
  decide +kernel

theorem context_12_338981_1172714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338981 ⟨1172714, by decide⟩ :=
  accepted_of_selected 12 338981 ⟨1172714, by decide⟩ ⟨12, 2, 0, 1172714, 338981, 3153, 65536⟩
    (by decide) selected_cut_42905

theorem selected_cut_42906 : selected 9 ⟨1172786, by decide⟩
    (prefixPartial 12 338982) = some ⟨12, 2, 0, 1172786, 338982, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_338982_1172786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338982 ⟨1172786, by decide⟩ :=
  accepted_of_selected 12 338982 ⟨1172786, by decide⟩ ⟨12, 2, 0, 1172786, 338982, 3185, 65536⟩
    (by decide) selected_cut_42906

theorem selected_cut_42907 : selected 9 ⟨1172856, by decide⟩
    (prefixPartial 12 338983) = some ⟨12, 2, 0, 1172856, 338983, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_338983_1172856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338983 ⟨1172856, by decide⟩ :=
  accepted_of_selected 12 338983 ⟨1172856, by decide⟩ ⟨12, 2, 0, 1172856, 338983, 3397, 65536⟩
    (by decide) selected_cut_42907

theorem unmarked_context_11_84745_1172857 : frontier 10 ⟨1172857, by decide⟩
    (prefixCache 11 84745) (prefixPartial 11 84745) = false := by
  decide +kernel

theorem node_context_11_84745_1172857 : EJMOriginalGlobalDAGData.nodes 10 ⟨1172857, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1172714, by decide⟩,⟨1172786, by decide⟩,⟨1172856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84745_1172857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84745 ⟨1172857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84745
    ⟨1172857, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1172714, by decide⟩,⟨1172786, by decide⟩,⟨1172856, by decide⟩]) unmarked_context_11_84745_1172857 node_context_11_84745_1172857
  intro a
  fin_cases a
  · exact context_12_338980_1108174
  · exact context_12_338981_1172714
  · exact context_12_338982_1172786
  · exact context_12_338983_1172856

theorem selected_cut_42908 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338984) = some ⟨12, 1, 0, 1108174, 338984, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338984_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338984 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338984 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338984, 1, 65536⟩
    (by decide) selected_cut_42908

theorem selected_cut_42909 : selected 9 ⟨1172909, by decide⟩
    (prefixPartial 12 338985) = some ⟨12, 2, 0, 1172909, 338985, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_338985_1172909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338985 ⟨1172909, by decide⟩ :=
  accepted_of_selected 12 338985 ⟨1172909, by decide⟩ ⟨12, 2, 0, 1172909, 338985, 2877, 65536⟩
    (by decide) selected_cut_42909

theorem selected_cut_42910 : selected 9 ⟨1172910, by decide⟩
    (prefixPartial 12 338986) = some ⟨12, 1, 0, 1172910, 338986, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338986_1172910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338986 ⟨1172910, by decide⟩ :=
  accepted_of_selected 12 338986 ⟨1172910, by decide⟩ ⟨12, 1, 0, 1172910, 338986, 1, 65536⟩
    (by decide) selected_cut_42910

theorem selected_cut_42911 : selected 9 ⟨1172973, by decide⟩
    (prefixPartial 12 338987) = some ⟨12, 2, 0, 1172973, 338987, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_338987_1172973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338987 ⟨1172973, by decide⟩ :=
  accepted_of_selected 12 338987 ⟨1172973, by decide⟩ ⟨12, 2, 0, 1172973, 338987, 3165, 65536⟩
    (by decide) selected_cut_42911

theorem unmarked_context_11_84746_1172974 : frontier 10 ⟨1172974, by decide⟩
    (prefixCache 11 84746) (prefixPartial 11 84746) = false := by
  decide +kernel

theorem node_context_11_84746_1172974 : EJMOriginalGlobalDAGData.nodes 10 ⟨1172974, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1172909, by decide⟩,⟨1172910, by decide⟩,⟨1172973, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84746_1172974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84746 ⟨1172974, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84746
    ⟨1172974, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1172909, by decide⟩,⟨1172910, by decide⟩,⟨1172973, by decide⟩]) unmarked_context_11_84746_1172974 node_context_11_84746_1172974
  intro a
  fin_cases a
  · exact context_12_338984_1108174
  · exact context_12_338985_1172909
  · exact context_12_338986_1172910
  · exact context_12_338987_1172973

theorem selected_cut_42912 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338988) = some ⟨12, 1, 0, 1108174, 338988, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338988_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338988 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338988 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338988, 1, 65536⟩
    (by decide) selected_cut_42912

theorem selected_cut_42913 : selected 9 ⟨1173014, by decide⟩
    (prefixPartial 12 338989) = some ⟨12, 2, 0, 1173014, 338989, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_338989_1173014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338989 ⟨1173014, by decide⟩ :=
  accepted_of_selected 12 338989 ⟨1173014, by decide⟩ ⟨12, 2, 0, 1173014, 338989, 2657, 65536⟩
    (by decide) selected_cut_42913

theorem selected_cut_42914 : selected 9 ⟨1173066, by decide⟩
    (prefixPartial 12 338990) = some ⟨12, 2, 0, 1173066, 338990, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_338990_1173066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338990 ⟨1173066, by decide⟩ :=
  accepted_of_selected 12 338990 ⟨1173066, by decide⟩ ⟨12, 2, 0, 1173066, 338990, 2569, 65536⟩
    (by decide) selected_cut_42914

theorem selected_cut_42915 : selected 9 ⟨1173117, by decide⟩
    (prefixPartial 12 338991) = some ⟨12, 2, 0, 1173117, 338991, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_338991_1173117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338991 ⟨1173117, by decide⟩ :=
  accepted_of_selected 12 338991 ⟨1173117, by decide⟩ ⟨12, 2, 0, 1173117, 338991, 2841, 65536⟩
    (by decide) selected_cut_42915

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
