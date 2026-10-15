/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover466
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_44836 : selected 10 ⟨1235979, by decide⟩
    (prefixPartial 11 88795) = some ⟨11, 2, 0, 1235979, 88795, 2273, 262144⟩ := by
  decide +kernel

theorem context_11_88795_1235979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88795 ⟨1235979, by decide⟩ :=
  accepted_of_selected 11 88795 ⟨1235979, by decide⟩ ⟨11, 2, 0, 1235979, 88795, 2273, 262144⟩
    (by decide) selected_cut_44836

theorem unmarked_context_10_22198_1235980 : frontier 11 ⟨1235980, by decide⟩
    (prefixCache 10 22198) (prefixPartial 10 22198) = false := by
  decide +kernel

theorem node_context_10_22198_1235980 : EJMOriginalGlobalDAGData.nodes 11 ⟨1235980, by decide⟩ =
    .split (coordinate 10) (![⟨1235898, by decide⟩,⟨1235948, by decide⟩,⟨900587, by decide⟩,⟨1235979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22198_1235980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22198 ⟨1235980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22198
    ⟨1235980, by decide⟩ (by decide) (![⟨1235898, by decide⟩,⟨1235948, by decide⟩,⟨900587, by decide⟩,⟨1235979, by decide⟩]) unmarked_context_10_22198_1235980 node_context_10_22198_1235980
  intro a
  fin_cases a
  · exact context_11_88792_1235898
  · exact context_11_88793_1235948
  · exact context_11_88794_900587
  · exact context_11_88795_1235979

theorem selected_cut_44837 : selected 9 ⟨1236003, by decide⟩
    (prefixPartial 12 355184) = some ⟨12, 2, 0, 1236003, 355184, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_355184_1236003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355184 ⟨1236003, by decide⟩ :=
  accepted_of_selected 12 355184 ⟨1236003, by decide⟩ ⟨12, 2, 0, 1236003, 355184, 1417, 65536⟩
    (by decide) selected_cut_44837

theorem selected_cut_44838 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 355185) = some ⟨12, 1, 0, 896706, 355185, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355185_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355185 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 355185 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 355185, 1, 65536⟩
    (by decide) selected_cut_44838

theorem selected_cut_44839 : selected 9 ⟨1236033, by decide⟩
    (prefixPartial 12 355186) = some ⟨12, 2, 0, 1236033, 355186, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_355186_1236033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355186 ⟨1236033, by decide⟩ :=
  accepted_of_selected 12 355186 ⟨1236033, by decide⟩ ⟨12, 2, 0, 1236033, 355186, 1557, 65536⟩
    (by decide) selected_cut_44839

theorem selected_cut_44840 : selected 9 ⟨1236054, by decide⟩
    (prefixPartial 12 355187) = some ⟨12, 2, 0, 1236054, 355187, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_355187_1236054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355187 ⟨1236054, by decide⟩ :=
  accepted_of_selected 12 355187 ⟨1236054, by decide⟩ ⟨12, 2, 0, 1236054, 355187, 1361, 65536⟩
    (by decide) selected_cut_44840

theorem unmarked_context_11_88796_1236055 : frontier 10 ⟨1236055, by decide⟩
    (prefixCache 11 88796) (prefixPartial 11 88796) = false := by
  decide +kernel

theorem node_context_11_88796_1236055 : EJMOriginalGlobalDAGData.nodes 10 ⟨1236055, by decide⟩ =
    .split (coordinate 11) (![⟨1236003, by decide⟩,⟨896706, by decide⟩,⟨1236033, by decide⟩,⟨1236054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88796_1236055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88796 ⟨1236055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88796
    ⟨1236055, by decide⟩ (by decide) (![⟨1236003, by decide⟩,⟨896706, by decide⟩,⟨1236033, by decide⟩,⟨1236054, by decide⟩]) unmarked_context_11_88796_1236055 node_context_11_88796_1236055
  intro a
  fin_cases a
  · exact context_12_355184_1236003
  · exact context_12_355185_896706
  · exact context_12_355186_1236033
  · exact context_12_355187_1236054

theorem selected_cut_44841 : selected 10 ⟨1236120, by decide⟩
    (prefixPartial 11 88797) = some ⟨11, 2, 0, 1236120, 88797, 3897, 262144⟩ := by
  decide +kernel

theorem context_11_88797_1236120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88797 ⟨1236120, by decide⟩ :=
  accepted_of_selected 11 88797 ⟨1236120, by decide⟩ ⟨11, 2, 0, 1236120, 88797, 3897, 262144⟩
    (by decide) selected_cut_44841

theorem selected_cut_44842 : selected 10 ⟨1236162, by decide⟩
    (prefixPartial 11 88798) = some ⟨11, 2, 0, 1236162, 88798, 2565, 262144⟩ := by
  decide +kernel

theorem context_11_88798_1236162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88798 ⟨1236162, by decide⟩ :=
  accepted_of_selected 11 88798 ⟨1236162, by decide⟩ ⟨11, 2, 0, 1236162, 88798, 2565, 262144⟩
    (by decide) selected_cut_44842

theorem selected_cut_44843 : selected 10 ⟨1236177, by decide⟩
    (prefixPartial 11 88799) = some ⟨11, 2, 0, 1236177, 88799, 1165, 262144⟩ := by
  decide +kernel

theorem context_11_88799_1236177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88799 ⟨1236177, by decide⟩ :=
  accepted_of_selected 11 88799 ⟨1236177, by decide⟩ ⟨11, 2, 0, 1236177, 88799, 1165, 262144⟩
    (by decide) selected_cut_44843

theorem unmarked_context_10_22199_1236178 : frontier 11 ⟨1236178, by decide⟩
    (prefixCache 10 22199) (prefixPartial 10 22199) = false := by
  decide +kernel

theorem node_context_10_22199_1236178 : EJMOriginalGlobalDAGData.nodes 11 ⟨1236178, by decide⟩ =
    .split (coordinate 10) (![⟨1236055, by decide⟩,⟨1236120, by decide⟩,⟨1236162, by decide⟩,⟨1236177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22199_1236178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22199 ⟨1236178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22199
    ⟨1236178, by decide⟩ (by decide) (![⟨1236055, by decide⟩,⟨1236120, by decide⟩,⟨1236162, by decide⟩,⟨1236177, by decide⟩]) unmarked_context_10_22199_1236178 node_context_10_22199_1236178
  intro a
  fin_cases a
  · exact context_11_88796_1236055
  · exact context_11_88797_1236120
  · exact context_11_88798_1236162
  · exact context_11_88799_1236177

theorem unmarked_context_9_5549_1236179 : frontier 12 ⟨1236179, by decide⟩
    (prefixCache 9 5549) (prefixPartial 9 5549) = false := by
  decide +kernel

theorem node_context_9_5549_1236179 : EJMOriginalGlobalDAGData.nodes 12 ⟨1236179, by decide⟩ =
    .split (coordinate 9) (![⟨1235845, by decide⟩,⟨893098, by decide⟩,⟨1235980, by decide⟩,⟨1236178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5549_1236179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5549 ⟨1236179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5549
    ⟨1236179, by decide⟩ (by decide) (![⟨1235845, by decide⟩,⟨893098, by decide⟩,⟨1235980, by decide⟩,⟨1236178, by decide⟩]) unmarked_context_9_5549_1236179 node_context_9_5549_1236179
  intro a
  fin_cases a
  · exact context_10_22196_1235845
  · exact context_10_22197_893098
  · exact context_10_22198_1235980
  · exact context_10_22199_1236178

theorem selected_cut_44844 : selected 10 ⟨1236230, by decide⟩
    (prefixPartial 11 88800) = some ⟨11, 2, 0, 1236230, 88800, 3377, 262144⟩ := by
  decide +kernel

theorem context_11_88800_1236230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88800 ⟨1236230, by decide⟩ :=
  accepted_of_selected 11 88800 ⟨1236230, by decide⟩ ⟨11, 2, 0, 1236230, 88800, 3377, 262144⟩
    (by decide) selected_cut_44844

theorem selected_cut_44845 : selected 9 ⟨1236245, by decide⟩
    (prefixPartial 12 355204) = some ⟨12, 2, 0, 1236245, 355204, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_355204_1236245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355204 ⟨1236245, by decide⟩ :=
  accepted_of_selected 12 355204 ⟨1236245, by decide⟩ ⟨12, 2, 0, 1236245, 355204, 1213, 65536⟩
    (by decide) selected_cut_44845

theorem selected_cut_44846 : selected 9 ⟨1236260, by decide⟩
    (prefixPartial 12 355205) = some ⟨12, 2, 0, 1236260, 355205, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_355205_1236260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355205 ⟨1236260, by decide⟩ :=
  accepted_of_selected 12 355205 ⟨1236260, by decide⟩ ⟨12, 2, 0, 1236260, 355205, 1069, 65536⟩
    (by decide) selected_cut_44846

theorem selected_cut_44847 : selected 9 ⟨1236280, by decide⟩
    (prefixPartial 12 355206) = some ⟨12, 2, 0, 1236280, 355206, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_355206_1236280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355206 ⟨1236280, by decide⟩ :=
  accepted_of_selected 12 355206 ⟨1236280, by decide⟩ ⟨12, 2, 0, 1236280, 355206, 1149, 65536⟩
    (by decide) selected_cut_44847

theorem selected_cut_44848 : selected 9 ⟨1236296, by decide⟩
    (prefixPartial 12 355207) = some ⟨12, 2, 0, 1236296, 355207, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_355207_1236296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355207 ⟨1236296, by decide⟩ :=
  accepted_of_selected 12 355207 ⟨1236296, by decide⟩ ⟨12, 2, 0, 1236296, 355207, 1125, 65536⟩
    (by decide) selected_cut_44848

theorem unmarked_context_11_88801_1236297 : frontier 10 ⟨1236297, by decide⟩
    (prefixCache 11 88801) (prefixPartial 11 88801) = false := by
  decide +kernel

theorem node_context_11_88801_1236297 : EJMOriginalGlobalDAGData.nodes 10 ⟨1236297, by decide⟩ =
    .split (coordinate 11) (![⟨1236245, by decide⟩,⟨1236260, by decide⟩,⟨1236280, by decide⟩,⟨1236296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88801_1236297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88801 ⟨1236297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88801
    ⟨1236297, by decide⟩ (by decide) (![⟨1236245, by decide⟩,⟨1236260, by decide⟩,⟨1236280, by decide⟩,⟨1236296, by decide⟩]) unmarked_context_11_88801_1236297 node_context_11_88801_1236297
  intro a
  fin_cases a
  · exact context_12_355204_1236245
  · exact context_12_355205_1236260
  · exact context_12_355206_1236280
  · exact context_12_355207_1236296

theorem selected_cut_44849 : selected 10 ⟨1236343, by decide⟩
    (prefixPartial 11 88802) = some ⟨11, 2, 0, 1236343, 88802, 3237, 262144⟩ := by
  decide +kernel

theorem context_11_88802_1236343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88802 ⟨1236343, by decide⟩ :=
  accepted_of_selected 11 88802 ⟨1236343, by decide⟩ ⟨11, 2, 0, 1236343, 88802, 3237, 262144⟩
    (by decide) selected_cut_44849

theorem selected_cut_44850 : selected 10 ⟨1236391, by decide⟩
    (prefixPartial 11 88803) = some ⟨11, 2, 0, 1236391, 88803, 2933, 262144⟩ := by
  decide +kernel

theorem context_11_88803_1236391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88803 ⟨1236391, by decide⟩ :=
  accepted_of_selected 11 88803 ⟨1236391, by decide⟩ ⟨11, 2, 0, 1236391, 88803, 2933, 262144⟩
    (by decide) selected_cut_44850

theorem unmarked_context_10_22200_1236392 : frontier 11 ⟨1236392, by decide⟩
    (prefixCache 10 22200) (prefixPartial 10 22200) = false := by
  decide +kernel

theorem node_context_10_22200_1236392 : EJMOriginalGlobalDAGData.nodes 11 ⟨1236392, by decide⟩ =
    .split (coordinate 10) (![⟨1236230, by decide⟩,⟨1236297, by decide⟩,⟨1236343, by decide⟩,⟨1236391, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22200_1236392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22200 ⟨1236392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22200
    ⟨1236392, by decide⟩ (by decide) (![⟨1236230, by decide⟩,⟨1236297, by decide⟩,⟨1236343, by decide⟩,⟨1236391, by decide⟩]) unmarked_context_10_22200_1236392 node_context_10_22200_1236392
  intro a
  fin_cases a
  · exact context_11_88800_1236230
  · exact context_11_88801_1236297
  · exact context_11_88802_1236343
  · exact context_11_88803_1236391

theorem selected_cut_44851 : selected 10 ⟨1236461, by decide⟩
    (prefixPartial 11 88804) = some ⟨11, 2, 0, 1236461, 88804, 3885, 262144⟩ := by
  decide +kernel

theorem context_11_88804_1236461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88804 ⟨1236461, by decide⟩ :=
  accepted_of_selected 11 88804 ⟨1236461, by decide⟩ ⟨11, 2, 0, 1236461, 88804, 3885, 262144⟩
    (by decide) selected_cut_44851

theorem selected_cut_44852 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 88805) = some ⟨11, 1, 0, 1192826, 88805, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88805_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88805 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 88805 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 88805, 1, 262144⟩
    (by decide) selected_cut_44852

theorem selected_cut_44853 : selected 10 ⟨1236508, by decide⟩
    (prefixPartial 11 88806) = some ⟨11, 2, 0, 1236508, 88806, 2665, 262144⟩ := by
  decide +kernel

theorem context_11_88806_1236508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88806 ⟨1236508, by decide⟩ :=
  accepted_of_selected 11 88806 ⟨1236508, by decide⟩ ⟨11, 2, 0, 1236508, 88806, 2665, 262144⟩
    (by decide) selected_cut_44853

theorem selected_cut_44854 : selected 10 ⟨1236534, by decide⟩
    (prefixPartial 11 88807) = some ⟨11, 2, 0, 1236534, 88807, 1577, 262144⟩ := by
  decide +kernel

theorem context_11_88807_1236534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88807 ⟨1236534, by decide⟩ :=
  accepted_of_selected 11 88807 ⟨1236534, by decide⟩ ⟨11, 2, 0, 1236534, 88807, 1577, 262144⟩
    (by decide) selected_cut_44854

theorem unmarked_context_10_22201_1236535 : frontier 11 ⟨1236535, by decide⟩
    (prefixCache 10 22201) (prefixPartial 10 22201) = false := by
  decide +kernel

theorem node_context_10_22201_1236535 : EJMOriginalGlobalDAGData.nodes 11 ⟨1236535, by decide⟩ =
    .split (coordinate 10) (![⟨1236461, by decide⟩,⟨1192826, by decide⟩,⟨1236508, by decide⟩,⟨1236534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22201_1236535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22201 ⟨1236535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22201
    ⟨1236535, by decide⟩ (by decide) (![⟨1236461, by decide⟩,⟨1192826, by decide⟩,⟨1236508, by decide⟩,⟨1236534, by decide⟩]) unmarked_context_10_22201_1236535 node_context_10_22201_1236535
  intro a
  fin_cases a
  · exact context_11_88804_1236461
  · exact context_11_88805_1192826
  · exact context_11_88806_1236508
  · exact context_11_88807_1236534

theorem selected_cut_44855 : selected 11 ⟨1236572, by decide⟩
    (prefixPartial 10 22202) = some ⟨10, 2, 0, 1236572, 22202, 2089, 1048576⟩ := by
  decide +kernel

theorem context_10_22202_1236572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22202 ⟨1236572, by decide⟩ :=
  accepted_of_selected 10 22202 ⟨1236572, by decide⟩ ⟨10, 2, 0, 1236572, 22202, 2089, 1048576⟩
    (by decide) selected_cut_44855

theorem selected_cut_44856 : selected 10 ⟨1236635, by decide⟩
    (prefixPartial 11 88812) = some ⟨11, 2, 0, 1236635, 88812, 3521, 262144⟩ := by
  decide +kernel

theorem context_11_88812_1236635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88812 ⟨1236635, by decide⟩ :=
  accepted_of_selected 11 88812 ⟨1236635, by decide⟩ ⟨11, 2, 0, 1236635, 88812, 3521, 262144⟩
    (by decide) selected_cut_44856

theorem selected_cut_44857 : selected 10 ⟨1236672, by decide⟩
    (prefixPartial 11 88813) = some ⟨11, 2, 0, 1236672, 88813, 2857, 262144⟩ := by
  decide +kernel

theorem context_11_88813_1236672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88813 ⟨1236672, by decide⟩ :=
  accepted_of_selected 11 88813 ⟨1236672, by decide⟩ ⟨11, 2, 0, 1236672, 88813, 2857, 262144⟩
    (by decide) selected_cut_44857

theorem selected_cut_44858 : selected 10 ⟨1236715, by decide⟩
    (prefixPartial 11 88814) = some ⟨11, 2, 0, 1236715, 88814, 2141, 262144⟩ := by
  decide +kernel

theorem context_11_88814_1236715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88814 ⟨1236715, by decide⟩ :=
  accepted_of_selected 11 88814 ⟨1236715, by decide⟩ ⟨11, 2, 0, 1236715, 88814, 2141, 262144⟩
    (by decide) selected_cut_44858

theorem selected_cut_44859 : selected 10 ⟨1236746, by decide⟩
    (prefixPartial 11 88815) = some ⟨11, 2, 0, 1236746, 88815, 1365, 262144⟩ := by
  decide +kernel

theorem context_11_88815_1236746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88815 ⟨1236746, by decide⟩ :=
  accepted_of_selected 11 88815 ⟨1236746, by decide⟩ ⟨11, 2, 0, 1236746, 88815, 1365, 262144⟩
    (by decide) selected_cut_44859

theorem unmarked_context_10_22203_1236747 : frontier 11 ⟨1236747, by decide⟩
    (prefixCache 10 22203) (prefixPartial 10 22203) = false := by
  decide +kernel

theorem node_context_10_22203_1236747 : EJMOriginalGlobalDAGData.nodes 11 ⟨1236747, by decide⟩ =
    .split (coordinate 10) (![⟨1236635, by decide⟩,⟨1236672, by decide⟩,⟨1236715, by decide⟩,⟨1236746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22203_1236747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22203 ⟨1236747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22203
    ⟨1236747, by decide⟩ (by decide) (![⟨1236635, by decide⟩,⟨1236672, by decide⟩,⟨1236715, by decide⟩,⟨1236746, by decide⟩]) unmarked_context_10_22203_1236747 node_context_10_22203_1236747
  intro a
  fin_cases a
  · exact context_11_88812_1236635
  · exact context_11_88813_1236672
  · exact context_11_88814_1236715
  · exact context_11_88815_1236746

theorem unmarked_context_9_5550_1236748 : frontier 12 ⟨1236748, by decide⟩
    (prefixCache 9 5550) (prefixPartial 9 5550) = false := by
  decide +kernel

theorem node_context_9_5550_1236748 : EJMOriginalGlobalDAGData.nodes 12 ⟨1236748, by decide⟩ =
    .split (coordinate 9) (![⟨1236392, by decide⟩,⟨1236535, by decide⟩,⟨1236572, by decide⟩,⟨1236747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5550_1236748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5550 ⟨1236748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5550
    ⟨1236748, by decide⟩ (by decide) (![⟨1236392, by decide⟩,⟨1236535, by decide⟩,⟨1236572, by decide⟩,⟨1236747, by decide⟩]) unmarked_context_9_5550_1236748 node_context_9_5550_1236748
  intro a
  fin_cases a
  · exact context_10_22200_1236392
  · exact context_10_22201_1236535
  · exact context_10_22202_1236572
  · exact context_10_22203_1236747

theorem selected_cut_44860 : selected 10 ⟨1236761, by decide⟩
    (prefixPartial 11 88816) = some ⟨11, 2, 0, 1236761, 88816, 1193, 262144⟩ := by
  decide +kernel

theorem context_11_88816_1236761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88816 ⟨1236761, by decide⟩ :=
  accepted_of_selected 11 88816 ⟨1236761, by decide⟩ ⟨11, 2, 0, 1236761, 88816, 1193, 262144⟩
    (by decide) selected_cut_44860

theorem selected_cut_44861 : selected 10 ⟨1236773, by decide⟩
    (prefixPartial 11 88817) = some ⟨11, 2, 0, 1236773, 88817, 797, 262144⟩ := by
  decide +kernel

theorem context_11_88817_1236773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88817 ⟨1236773, by decide⟩ :=
  accepted_of_selected 11 88817 ⟨1236773, by decide⟩ ⟨11, 2, 0, 1236773, 88817, 797, 262144⟩
    (by decide) selected_cut_44861

theorem selected_cut_44862 : selected 10 ⟨1236792, by decide⟩
    (prefixPartial 11 88818) = some ⟨11, 2, 0, 1236792, 88818, 1549, 262144⟩ := by
  decide +kernel

theorem context_11_88818_1236792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88818 ⟨1236792, by decide⟩ :=
  accepted_of_selected 11 88818 ⟨1236792, by decide⟩ ⟨11, 2, 0, 1236792, 88818, 1549, 262144⟩
    (by decide) selected_cut_44862

theorem selected_cut_44863 : selected 10 ⟨1236814, by decide⟩
    (prefixPartial 11 88819) = some ⟨11, 2, 0, 1236814, 88819, 1153, 262144⟩ := by
  decide +kernel

theorem context_11_88819_1236814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88819 ⟨1236814, by decide⟩ :=
  accepted_of_selected 11 88819 ⟨1236814, by decide⟩ ⟨11, 2, 0, 1236814, 88819, 1153, 262144⟩
    (by decide) selected_cut_44863

theorem unmarked_context_10_22204_1236815 : frontier 11 ⟨1236815, by decide⟩
    (prefixCache 10 22204) (prefixPartial 10 22204) = false := by
  decide +kernel

theorem node_context_10_22204_1236815 : EJMOriginalGlobalDAGData.nodes 11 ⟨1236815, by decide⟩ =
    .split (coordinate 10) (![⟨1236761, by decide⟩,⟨1236773, by decide⟩,⟨1236792, by decide⟩,⟨1236814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22204_1236815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22204 ⟨1236815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22204
    ⟨1236815, by decide⟩ (by decide) (![⟨1236761, by decide⟩,⟨1236773, by decide⟩,⟨1236792, by decide⟩,⟨1236814, by decide⟩]) unmarked_context_10_22204_1236815 node_context_10_22204_1236815
  intro a
  fin_cases a
  · exact context_11_88816_1236761
  · exact context_11_88817_1236773
  · exact context_11_88818_1236792
  · exact context_11_88819_1236814

theorem selected_cut_44864 : selected 11 ⟨1236866, by decide⟩
    (prefixPartial 10 22205) = some ⟨10, 2, 0, 1236866, 22205, 3021, 1048576⟩ := by
  decide +kernel

theorem context_10_22205_1236866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22205 ⟨1236866, by decide⟩ :=
  accepted_of_selected 10 22205 ⟨1236866, by decide⟩ ⟨10, 2, 0, 1236866, 22205, 3021, 1048576⟩
    (by decide) selected_cut_44864

theorem selected_cut_44865 : selected 11 ⟨1236898, by decide⟩
    (prefixPartial 10 22206) = some ⟨10, 2, 0, 1236898, 22206, 1345, 1048576⟩ := by
  decide +kernel

theorem context_10_22206_1236898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22206 ⟨1236898, by decide⟩ :=
  accepted_of_selected 10 22206 ⟨1236898, by decide⟩ ⟨10, 2, 0, 1236898, 22206, 1345, 1048576⟩
    (by decide) selected_cut_44865

theorem selected_cut_44866 : selected 11 ⟨1236919, by decide⟩
    (prefixPartial 10 22207) = some ⟨10, 2, 0, 1236919, 22207, 361, 1048576⟩ := by
  decide +kernel

theorem context_10_22207_1236919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22207 ⟨1236919, by decide⟩ :=
  accepted_of_selected 10 22207 ⟨1236919, by decide⟩ ⟨10, 2, 0, 1236919, 22207, 361, 1048576⟩
    (by decide) selected_cut_44866

theorem unmarked_context_9_5551_1236920 : frontier 12 ⟨1236920, by decide⟩
    (prefixCache 9 5551) (prefixPartial 9 5551) = false := by
  decide +kernel

theorem node_context_9_5551_1236920 : EJMOriginalGlobalDAGData.nodes 12 ⟨1236920, by decide⟩ =
    .split (coordinate 9) (![⟨1236815, by decide⟩,⟨1236866, by decide⟩,⟨1236898, by decide⟩,⟨1236919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5551_1236920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5551 ⟨1236920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5551
    ⟨1236920, by decide⟩ (by decide) (![⟨1236815, by decide⟩,⟨1236866, by decide⟩,⟨1236898, by decide⟩,⟨1236919, by decide⟩]) unmarked_context_9_5551_1236920 node_context_9_5551_1236920
  intro a
  fin_cases a
  · exact context_10_22204_1236815
  · exact context_10_22205_1236866
  · exact context_10_22206_1236898
  · exact context_10_22207_1236919

theorem unmarked_context_8_1387_1236921 : frontier 13 ⟨1236921, by decide⟩
    (prefixCache 8 1387) (prefixPartial 8 1387) = false := by
  decide +kernel

theorem node_context_8_1387_1236921 : EJMOriginalGlobalDAGData.nodes 13 ⟨1236921, by decide⟩ =
    .split (coordinate 8) (![⟨1235595, by decide⟩,⟨1236179, by decide⟩,⟨1236748, by decide⟩,⟨1236920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1387_1236921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1387 ⟨1236921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1387
    ⟨1236921, by decide⟩ (by decide) (![⟨1235595, by decide⟩,⟨1236179, by decide⟩,⟨1236748, by decide⟩,⟨1236920, by decide⟩]) unmarked_context_8_1387_1236921 node_context_8_1387_1236921
  intro a
  fin_cases a
  · exact context_9_5548_1235595
  · exact context_9_5549_1236179
  · exact context_9_5550_1236748
  · exact context_9_5551_1236920

theorem unmarked_context_7_346_1236922 : frontier 14 ⟨1236922, by decide⟩
    (prefixCache 7 346) (prefixPartial 7 346) = false := by
  decide +kernel

theorem node_context_7_346_1236922 : EJMOriginalGlobalDAGData.nodes 14 ⟨1236922, by decide⟩ =
    .split (coordinate 7) (![⟨1227329, by decide⟩,⟨1230154, by decide⟩,⟨1233700, by decide⟩,⟨1236921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_346_1236922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 346 ⟨1236922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 346
    ⟨1236922, by decide⟩ (by decide) (![⟨1227329, by decide⟩,⟨1230154, by decide⟩,⟨1233700, by decide⟩,⟨1236921, by decide⟩]) unmarked_context_7_346_1236922 node_context_7_346_1236922
  intro a
  fin_cases a
  · exact context_8_1384_1227329
  · exact context_8_1385_1230154
  · exact context_8_1386_1233700
  · exact context_8_1387_1236921

theorem selected_cut_44867 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88832) = some ⟨11, 1, 0, 434745, 88832, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88832_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88832 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88832 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88832, 1, 262144⟩
    (by decide) selected_cut_44867

theorem selected_cut_44868 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 355332) = some ⟨12, 1, 0, 448748, 355332, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355332_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355332 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 355332 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 355332, 1, 65536⟩
    (by decide) selected_cut_44868

theorem selected_cut_44869 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 355333) = some ⟨12, 1, 0, 34034, 355333, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355333_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355333 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 355333 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 355333, 1, 65536⟩
    (by decide) selected_cut_44869

theorem selected_cut_44870 : selected 9 ⟨1237055, by decide⟩
    (prefixPartial 12 355334) = some ⟨12, 2, 0, 1237055, 355334, 3345, 65536⟩ := by
  decide +kernel

theorem context_12_355334_1237055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355334 ⟨1237055, by decide⟩ :=
  accepted_of_selected 12 355334 ⟨1237055, by decide⟩ ⟨12, 2, 0, 1237055, 355334, 3345, 65536⟩
    (by decide) selected_cut_44870

theorem selected_cut_44871 : selected 9 ⟨1237170, by decide⟩
    (prefixPartial 12 355335) = some ⟨12, 2, 0, 1237170, 355335, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_355335_1237170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355335 ⟨1237170, by decide⟩ :=
  accepted_of_selected 12 355335 ⟨1237170, by decide⟩ ⟨12, 2, 0, 1237170, 355335, 3585, 65536⟩
    (by decide) selected_cut_44871

theorem unmarked_context_11_88833_1237171 : frontier 10 ⟨1237171, by decide⟩
    (prefixCache 11 88833) (prefixPartial 11 88833) = false := by
  decide +kernel

theorem node_context_11_88833_1237171 : EJMOriginalGlobalDAGData.nodes 10 ⟨1237171, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1237055, by decide⟩,⟨1237170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88833_1237171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88833 ⟨1237171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88833
    ⟨1237171, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1237055, by decide⟩,⟨1237170, by decide⟩]) unmarked_context_11_88833_1237171 node_context_11_88833_1237171
  intro a
  fin_cases a
  · exact context_12_355332_448748
  · exact context_12_355333_34034
  · exact context_12_355334_1237055
  · exact context_12_355335_1237170

theorem selected_cut_44872 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 355336) = some ⟨12, 1, 0, 448748, 355336, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355336_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355336 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 355336 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 355336, 1, 65536⟩
    (by decide) selected_cut_44872

theorem selected_cut_44873 : selected 9 ⟨1237266, by decide⟩
    (prefixPartial 12 355337) = some ⟨12, 2, 0, 1237266, 355337, 3393, 65536⟩ := by
  decide +kernel

theorem context_12_355337_1237266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355337 ⟨1237266, by decide⟩ :=
  accepted_of_selected 12 355337 ⟨1237266, by decide⟩ ⟨12, 2, 0, 1237266, 355337, 3393, 65536⟩
    (by decide) selected_cut_44873

theorem selected_cut_44874 : selected 9 ⟨1237353, by decide⟩
    (prefixPartial 12 355338) = some ⟨12, 2, 0, 1237353, 355338, 3377, 65536⟩ := by
  decide +kernel

theorem context_12_355338_1237353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355338 ⟨1237353, by decide⟩ :=
  accepted_of_selected 12 355338 ⟨1237353, by decide⟩ ⟨12, 2, 0, 1237353, 355338, 3377, 65536⟩
    (by decide) selected_cut_44874

theorem selected_cut_44875 : selected 9 ⟨1237489, by decide⟩
    (prefixPartial 12 355339) = some ⟨12, 2, 0, 1237489, 355339, 3993, 65536⟩ := by
  decide +kernel

theorem context_12_355339_1237489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355339 ⟨1237489, by decide⟩ :=
  accepted_of_selected 12 355339 ⟨1237489, by decide⟩ ⟨12, 2, 0, 1237489, 355339, 3993, 65536⟩
    (by decide) selected_cut_44875

theorem unmarked_context_11_88834_1237490 : frontier 10 ⟨1237490, by decide⟩
    (prefixCache 11 88834) (prefixPartial 11 88834) = false := by
  decide +kernel

theorem node_context_11_88834_1237490 : EJMOriginalGlobalDAGData.nodes 10 ⟨1237490, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1237266, by decide⟩,⟨1237353, by decide⟩,⟨1237489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88834_1237490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88834 ⟨1237490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88834
    ⟨1237490, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1237266, by decide⟩,⟨1237353, by decide⟩,⟨1237489, by decide⟩]) unmarked_context_11_88834_1237490 node_context_11_88834_1237490
  intro a
  fin_cases a
  · exact context_12_355336_448748
  · exact context_12_355337_1237266
  · exact context_12_355338_1237353
  · exact context_12_355339_1237489

theorem selected_cut_44876 : selected 10 ⟨1237576, by decide⟩
    (prefixPartial 11 88835) = some ⟨11, 2, 0, 1237576, 88835, 3329, 262144⟩ := by
  decide +kernel

theorem context_11_88835_1237576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88835 ⟨1237576, by decide⟩ :=
  accepted_of_selected 11 88835 ⟨1237576, by decide⟩ ⟨11, 2, 0, 1237576, 88835, 3329, 262144⟩
    (by decide) selected_cut_44876

theorem unmarked_context_10_22208_1237577 : frontier 11 ⟨1237577, by decide⟩
    (prefixCache 10 22208) (prefixPartial 10 22208) = false := by
  decide +kernel

theorem node_context_10_22208_1237577 : EJMOriginalGlobalDAGData.nodes 11 ⟨1237577, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1237171, by decide⟩,⟨1237490, by decide⟩,⟨1237576, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22208_1237577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22208 ⟨1237577, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22208
    ⟨1237577, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1237171, by decide⟩,⟨1237490, by decide⟩,⟨1237576, by decide⟩]) unmarked_context_10_22208_1237577 node_context_10_22208_1237577
  intro a
  fin_cases a
  · exact context_11_88832_434745
  · exact context_11_88833_1237171
  · exact context_11_88834_1237490
  · exact context_11_88835_1237576

theorem selected_cut_44877 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 355344) = some ⟨12, 1, 0, 435160, 355344, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355344_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355344 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 355344 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 355344, 1, 65536⟩
    (by decide) selected_cut_44877

theorem selected_cut_44878 : selected 9 ⟨1237648, by decide⟩
    (prefixPartial 12 355345) = some ⟨12, 2, 0, 1237648, 355345, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_355345_1237648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355345 ⟨1237648, by decide⟩ :=
  accepted_of_selected 12 355345 ⟨1237648, by decide⟩ ⟨12, 2, 0, 1237648, 355345, 2909, 65536⟩
    (by decide) selected_cut_44878

theorem selected_cut_44879 : selected 9 ⟨1237741, by decide⟩
    (prefixPartial 12 355346) = some ⟨12, 2, 0, 1237741, 355346, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_355346_1237741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355346 ⟨1237741, by decide⟩ :=
  accepted_of_selected 12 355346 ⟨1237741, by decide⟩ ⟨12, 2, 0, 1237741, 355346, 3189, 65536⟩
    (by decide) selected_cut_44879

theorem selected_cut_44880 : selected 9 ⟨1237824, by decide⟩
    (prefixPartial 12 355347) = some ⟨12, 2, 0, 1237824, 355347, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_355347_1237824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355347 ⟨1237824, by decide⟩ :=
  accepted_of_selected 12 355347 ⟨1237824, by decide⟩ ⟨12, 2, 0, 1237824, 355347, 3265, 65536⟩
    (by decide) selected_cut_44880

theorem unmarked_context_11_88836_1237825 : frontier 10 ⟨1237825, by decide⟩
    (prefixCache 11 88836) (prefixPartial 11 88836) = false := by
  decide +kernel

theorem node_context_11_88836_1237825 : EJMOriginalGlobalDAGData.nodes 10 ⟨1237825, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1237648, by decide⟩,⟨1237741, by decide⟩,⟨1237824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88836_1237825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88836 ⟨1237825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88836
    ⟨1237825, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1237648, by decide⟩,⟨1237741, by decide⟩,⟨1237824, by decide⟩]) unmarked_context_11_88836_1237825 node_context_11_88836_1237825
  intro a
  fin_cases a
  · exact context_12_355344_435160
  · exact context_12_355345_1237648
  · exact context_12_355346_1237741
  · exact context_12_355347_1237824

theorem selected_cut_44881 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 355348) = some ⟨12, 1, 0, 435160, 355348, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355348_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355348 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 355348 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 355348, 1, 65536⟩
    (by decide) selected_cut_44881

theorem selected_cut_44882 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 355349) = some ⟨12, 1, 0, 1172003, 355349, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355349_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355349 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 355349 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 355349, 1, 65536⟩
    (by decide) selected_cut_44882

theorem selected_cut_44883 : selected 9 ⟨1237895, by decide⟩
    (prefixPartial 12 355350) = some ⟨12, 2, 0, 1237895, 355350, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_355350_1237895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355350 ⟨1237895, by decide⟩ :=
  accepted_of_selected 12 355350 ⟨1237895, by decide⟩ ⟨12, 2, 0, 1237895, 355350, 3141, 65536⟩
    (by decide) selected_cut_44883

theorem selected_cut_44884 : selected 9 ⟨1237962, by decide⟩
    (prefixPartial 12 355351) = some ⟨12, 2, 0, 1237962, 355351, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_355351_1237962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355351 ⟨1237962, by decide⟩ :=
  accepted_of_selected 12 355351 ⟨1237962, by decide⟩ ⟨12, 2, 0, 1237962, 355351, 3273, 65536⟩
    (by decide) selected_cut_44884

theorem unmarked_context_11_88837_1237963 : frontier 10 ⟨1237963, by decide⟩
    (prefixCache 11 88837) (prefixPartial 11 88837) = false := by
  decide +kernel

theorem node_context_11_88837_1237963 : EJMOriginalGlobalDAGData.nodes 10 ⟨1237963, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1172003, by decide⟩,⟨1237895, by decide⟩,⟨1237962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88837_1237963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88837 ⟨1237963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88837
    ⟨1237963, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1172003, by decide⟩,⟨1237895, by decide⟩,⟨1237962, by decide⟩]) unmarked_context_11_88837_1237963 node_context_11_88837_1237963
  intro a
  fin_cases a
  · exact context_12_355348_435160
  · exact context_12_355349_1172003
  · exact context_12_355350_1237895
  · exact context_12_355351_1237962

theorem selected_cut_44885 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 355352) = some ⟨12, 1, 0, 449505, 355352, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355352_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355352 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 355352 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 355352, 1, 65536⟩
    (by decide) selected_cut_44885

theorem selected_cut_44886 : selected 9 ⟨1238022, by decide⟩
    (prefixPartial 12 355353) = some ⟨12, 2, 0, 1238022, 355353, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_355353_1238022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355353 ⟨1238022, by decide⟩ :=
  accepted_of_selected 12 355353 ⟨1238022, by decide⟩ ⟨12, 2, 0, 1238022, 355353, 2969, 65536⟩
    (by decide) selected_cut_44886

theorem selected_cut_44887 : selected 9 ⟨1238092, by decide⟩
    (prefixPartial 12 355354) = some ⟨12, 2, 0, 1238092, 355354, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_355354_1238092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355354 ⟨1238092, by decide⟩ :=
  accepted_of_selected 12 355354 ⟨1238092, by decide⟩ ⟨12, 2, 0, 1238092, 355354, 3245, 65536⟩
    (by decide) selected_cut_44887

theorem selected_cut_44888 : selected 9 ⟨1238163, by decide⟩
    (prefixPartial 12 355355) = some ⟨12, 2, 0, 1238163, 355355, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_355355_1238163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355355 ⟨1238163, by decide⟩ :=
  accepted_of_selected 12 355355 ⟨1238163, by decide⟩ ⟨12, 2, 0, 1238163, 355355, 3621, 65536⟩
    (by decide) selected_cut_44888

theorem unmarked_context_11_88838_1238164 : frontier 10 ⟨1238164, by decide⟩
    (prefixCache 11 88838) (prefixPartial 11 88838) = false := by
  decide +kernel

theorem node_context_11_88838_1238164 : EJMOriginalGlobalDAGData.nodes 10 ⟨1238164, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨1238022, by decide⟩,⟨1238092, by decide⟩,⟨1238163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88838_1238164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88838 ⟨1238164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88838
    ⟨1238164, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨1238022, by decide⟩,⟨1238092, by decide⟩,⟨1238163, by decide⟩]) unmarked_context_11_88838_1238164 node_context_11_88838_1238164
  intro a
  fin_cases a
  · exact context_12_355352_449505
  · exact context_12_355353_1238022
  · exact context_12_355354_1238092
  · exact context_12_355355_1238163

theorem selected_cut_44889 : selected 9 ⟨539296, by decide⟩
    (prefixPartial 12 355356) = some ⟨12, 1, 0, 539296, 355356, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355356_539296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355356 ⟨539296, by decide⟩ :=
  accepted_of_selected 12 355356 ⟨539296, by decide⟩ ⟨12, 1, 0, 539296, 355356, 1, 65536⟩
    (by decide) selected_cut_44889

theorem selected_cut_44890 : selected 9 ⟨1238223, by decide⟩
    (prefixPartial 12 355357) = some ⟨12, 2, 0, 1238223, 355357, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_355357_1238223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355357 ⟨1238223, by decide⟩ :=
  accepted_of_selected 12 355357 ⟨1238223, by decide⟩ ⟨12, 2, 0, 1238223, 355357, 2789, 65536⟩
    (by decide) selected_cut_44890

theorem selected_cut_44891 : selected 9 ⟨1238305, by decide⟩
    (prefixPartial 12 355358) = some ⟨12, 2, 0, 1238305, 355358, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_355358_1238305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355358 ⟨1238305, by decide⟩ :=
  accepted_of_selected 12 355358 ⟨1238305, by decide⟩ ⟨12, 2, 0, 1238305, 355358, 3205, 65536⟩
    (by decide) selected_cut_44891

theorem selected_cut_44892 : selected 9 ⟨1238369, by decide⟩
    (prefixPartial 12 355359) = some ⟨12, 2, 0, 1238369, 355359, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_355359_1238369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355359 ⟨1238369, by decide⟩ :=
  accepted_of_selected 12 355359 ⟨1238369, by decide⟩ ⟨12, 2, 0, 1238369, 355359, 3061, 65536⟩
    (by decide) selected_cut_44892

theorem unmarked_context_11_88839_1238370 : frontier 10 ⟨1238370, by decide⟩
    (prefixCache 11 88839) (prefixPartial 11 88839) = false := by
  decide +kernel

theorem node_context_11_88839_1238370 : EJMOriginalGlobalDAGData.nodes 10 ⟨1238370, by decide⟩ =
    .split (coordinate 11) (![⟨539296, by decide⟩,⟨1238223, by decide⟩,⟨1238305, by decide⟩,⟨1238369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88839_1238370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88839 ⟨1238370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88839
    ⟨1238370, by decide⟩ (by decide) (![⟨539296, by decide⟩,⟨1238223, by decide⟩,⟨1238305, by decide⟩,⟨1238369, by decide⟩]) unmarked_context_11_88839_1238370 node_context_11_88839_1238370
  intro a
  fin_cases a
  · exact context_12_355356_539296
  · exact context_12_355357_1238223
  · exact context_12_355358_1238305
  · exact context_12_355359_1238369

theorem unmarked_context_10_22209_1238371 : frontier 11 ⟨1238371, by decide⟩
    (prefixCache 10 22209) (prefixPartial 10 22209) = false := by
  decide +kernel

theorem node_context_10_22209_1238371 : EJMOriginalGlobalDAGData.nodes 11 ⟨1238371, by decide⟩ =
    .split (coordinate 10) (![⟨1237825, by decide⟩,⟨1237963, by decide⟩,⟨1238164, by decide⟩,⟨1238370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22209_1238371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22209 ⟨1238371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22209
    ⟨1238371, by decide⟩ (by decide) (![⟨1237825, by decide⟩,⟨1237963, by decide⟩,⟨1238164, by decide⟩,⟨1238370, by decide⟩]) unmarked_context_10_22209_1238371 node_context_10_22209_1238371
  intro a
  fin_cases a
  · exact context_11_88836_1237825
  · exact context_11_88837_1237963
  · exact context_11_88838_1238164
  · exact context_11_88839_1238370

theorem selected_cut_44893 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 355360) = some ⟨12, 1, 0, 985390, 355360, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355360_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355360 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 355360 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 355360, 1, 65536⟩
    (by decide) selected_cut_44893

theorem selected_cut_44894 : selected 9 ⟨1238420, by decide⟩
    (prefixPartial 12 355361) = some ⟨12, 2, 0, 1238420, 355361, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_355361_1238420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355361 ⟨1238420, by decide⟩ :=
  accepted_of_selected 12 355361 ⟨1238420, by decide⟩ ⟨12, 2, 0, 1238420, 355361, 2825, 65536⟩
    (by decide) selected_cut_44894

theorem selected_cut_44895 : selected 9 ⟨1238485, by decide⟩
    (prefixPartial 12 355362) = some ⟨12, 2, 0, 1238485, 355362, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_355362_1238485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355362 ⟨1238485, by decide⟩ :=
  accepted_of_selected 12 355362 ⟨1238485, by decide⟩ ⟨12, 2, 0, 1238485, 355362, 2941, 65536⟩
    (by decide) selected_cut_44895

theorem selected_cut_44896 : selected 9 ⟨1238568, by decide⟩
    (prefixPartial 12 355363) = some ⟨12, 2, 0, 1238568, 355363, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_355363_1238568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355363 ⟨1238568, by decide⟩ :=
  accepted_of_selected 12 355363 ⟨1238568, by decide⟩ ⟨12, 2, 0, 1238568, 355363, 3117, 65536⟩
    (by decide) selected_cut_44896

theorem unmarked_context_11_88840_1238569 : frontier 10 ⟨1238569, by decide⟩
    (prefixCache 11 88840) (prefixPartial 11 88840) = false := by
  decide +kernel

theorem node_context_11_88840_1238569 : EJMOriginalGlobalDAGData.nodes 10 ⟨1238569, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1238420, by decide⟩,⟨1238485, by decide⟩,⟨1238568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88840_1238569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88840 ⟨1238569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88840
    ⟨1238569, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1238420, by decide⟩,⟨1238485, by decide⟩,⟨1238568, by decide⟩]) unmarked_context_11_88840_1238569 node_context_11_88840_1238569
  intro a
  fin_cases a
  · exact context_12_355360_985390
  · exact context_12_355361_1238420
  · exact context_12_355362_1238485
  · exact context_12_355363_1238568

theorem selected_cut_44897 : selected 9 ⟨1197509, by decide⟩
    (prefixPartial 12 355364) = some ⟨12, 1, 0, 1197509, 355364, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355364_1197509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355364 ⟨1197509, by decide⟩ :=
  accepted_of_selected 12 355364 ⟨1197509, by decide⟩ ⟨12, 1, 0, 1197509, 355364, 1, 65536⟩
    (by decide) selected_cut_44897

theorem selected_cut_44898 : selected 9 ⟨719134, by decide⟩
    (prefixPartial 12 355365) = some ⟨12, 1, 0, 719134, 355365, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355365_719134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355365 ⟨719134, by decide⟩ :=
  accepted_of_selected 12 355365 ⟨719134, by decide⟩ ⟨12, 1, 0, 719134, 355365, 1, 65536⟩
    (by decide) selected_cut_44898

theorem selected_cut_44899 : selected 9 ⟨1238637, by decide⟩
    (prefixPartial 12 355366) = some ⟨12, 2, 0, 1238637, 355366, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_355366_1238637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355366 ⟨1238637, by decide⟩ :=
  accepted_of_selected 12 355366 ⟨1238637, by decide⟩ ⟨12, 2, 0, 1238637, 355366, 2873, 65536⟩
    (by decide) selected_cut_44899

theorem selected_cut_44900 : selected 9 ⟨1238705, by decide⟩
    (prefixPartial 12 355367) = some ⟨12, 2, 0, 1238705, 355367, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_355367_1238705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355367 ⟨1238705, by decide⟩ :=
  accepted_of_selected 12 355367 ⟨1238705, by decide⟩ ⟨12, 2, 0, 1238705, 355367, 3125, 65536⟩
    (by decide) selected_cut_44900

theorem unmarked_context_11_88841_1238706 : frontier 10 ⟨1238706, by decide⟩
    (prefixCache 11 88841) (prefixPartial 11 88841) = false := by
  decide +kernel

theorem node_context_11_88841_1238706 : EJMOriginalGlobalDAGData.nodes 10 ⟨1238706, by decide⟩ =
    .split (coordinate 11) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1238637, by decide⟩,⟨1238705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88841_1238706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88841 ⟨1238706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88841
    ⟨1238706, by decide⟩ (by decide) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1238637, by decide⟩,⟨1238705, by decide⟩]) unmarked_context_11_88841_1238706 node_context_11_88841_1238706
  intro a
  fin_cases a
  · exact context_12_355364_1197509
  · exact context_12_355365_719134
  · exact context_12_355366_1238637
  · exact context_12_355367_1238705

theorem selected_cut_44901 : selected 9 ⟨1238771, by decide⟩
    (prefixPartial 12 355368) = some ⟨12, 2, 0, 1238771, 355368, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_355368_1238771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355368 ⟨1238771, by decide⟩ :=
  accepted_of_selected 12 355368 ⟨1238771, by decide⟩ ⟨12, 2, 0, 1238771, 355368, 2785, 65536⟩
    (by decide) selected_cut_44901

theorem selected_cut_44902 : selected 9 ⟨1238827, by decide⟩
    (prefixPartial 12 355369) = some ⟨12, 2, 0, 1238827, 355369, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_355369_1238827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355369 ⟨1238827, by decide⟩ :=
  accepted_of_selected 12 355369 ⟨1238827, by decide⟩ ⟨12, 2, 0, 1238827, 355369, 2849, 65536⟩
    (by decide) selected_cut_44902

theorem selected_cut_44903 : selected 9 ⟨1172910, by decide⟩
    (prefixPartial 12 355370) = some ⟨12, 1, 0, 1172910, 355370, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355370_1172910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355370 ⟨1172910, by decide⟩ :=
  accepted_of_selected 12 355370 ⟨1172910, by decide⟩ ⟨12, 1, 0, 1172910, 355370, 1, 65536⟩
    (by decide) selected_cut_44903

theorem selected_cut_44904 : selected 9 ⟨1238894, by decide⟩
    (prefixPartial 12 355371) = some ⟨12, 2, 0, 1238894, 355371, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_355371_1238894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355371 ⟨1238894, by decide⟩ :=
  accepted_of_selected 12 355371 ⟨1238894, by decide⟩ ⟨12, 2, 0, 1238894, 355371, 3333, 65536⟩
    (by decide) selected_cut_44904

theorem unmarked_context_11_88842_1238895 : frontier 10 ⟨1238895, by decide⟩
    (prefixCache 11 88842) (prefixPartial 11 88842) = false := by
  decide +kernel

theorem node_context_11_88842_1238895 : EJMOriginalGlobalDAGData.nodes 10 ⟨1238895, by decide⟩ =
    .split (coordinate 11) (![⟨1238771, by decide⟩,⟨1238827, by decide⟩,⟨1172910, by decide⟩,⟨1238894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88842_1238895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88842 ⟨1238895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88842
    ⟨1238895, by decide⟩ (by decide) (![⟨1238771, by decide⟩,⟨1238827, by decide⟩,⟨1172910, by decide⟩,⟨1238894, by decide⟩]) unmarked_context_11_88842_1238895 node_context_11_88842_1238895
  intro a
  fin_cases a
  · exact context_12_355368_1238771
  · exact context_12_355369_1238827
  · exact context_12_355370_1172910
  · exact context_12_355371_1238894

theorem selected_cut_44905 : selected 9 ⟨1238946, by decide⟩
    (prefixPartial 12 355372) = some ⟨12, 2, 0, 1238946, 355372, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_355372_1238946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355372 ⟨1238946, by decide⟩ :=
  accepted_of_selected 12 355372 ⟨1238946, by decide⟩ ⟨12, 2, 0, 1238946, 355372, 2553, 65536⟩
    (by decide) selected_cut_44905

theorem selected_cut_44906 : selected 9 ⟨1238996, by decide⟩
    (prefixPartial 12 355373) = some ⟨12, 2, 0, 1238996, 355373, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_355373_1238996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355373 ⟨1238996, by decide⟩ :=
  accepted_of_selected 12 355373 ⟨1238996, by decide⟩ ⟨12, 2, 0, 1238996, 355373, 2581, 65536⟩
    (by decide) selected_cut_44906

theorem selected_cut_44907 : selected 9 ⟨1239058, by decide⟩
    (prefixPartial 12 355374) = some ⟨12, 2, 0, 1239058, 355374, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_355374_1239058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355374 ⟨1239058, by decide⟩ :=
  accepted_of_selected 12 355374 ⟨1239058, by decide⟩ ⟨12, 2, 0, 1239058, 355374, 2817, 65536⟩
    (by decide) selected_cut_44907

theorem selected_cut_44908 : selected 9 ⟨1239118, by decide⟩
    (prefixPartial 12 355375) = some ⟨12, 2, 0, 1239118, 355375, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_355375_1239118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355375 ⟨1239118, by decide⟩ :=
  accepted_of_selected 12 355375 ⟨1239118, by decide⟩ ⟨12, 2, 0, 1239118, 355375, 2897, 65536⟩
    (by decide) selected_cut_44908

theorem unmarked_context_11_88843_1239119 : frontier 10 ⟨1239119, by decide⟩
    (prefixCache 11 88843) (prefixPartial 11 88843) = false := by
  decide +kernel

theorem node_context_11_88843_1239119 : EJMOriginalGlobalDAGData.nodes 10 ⟨1239119, by decide⟩ =
    .split (coordinate 11) (![⟨1238946, by decide⟩,⟨1238996, by decide⟩,⟨1239058, by decide⟩,⟨1239118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88843_1239119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88843 ⟨1239119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88843
    ⟨1239119, by decide⟩ (by decide) (![⟨1238946, by decide⟩,⟨1238996, by decide⟩,⟨1239058, by decide⟩,⟨1239118, by decide⟩]) unmarked_context_11_88843_1239119 node_context_11_88843_1239119
  intro a
  fin_cases a
  · exact context_12_355372_1238946
  · exact context_12_355373_1238996
  · exact context_12_355374_1239058
  · exact context_12_355375_1239118

theorem unmarked_context_10_22210_1239120 : frontier 11 ⟨1239120, by decide⟩
    (prefixCache 10 22210) (prefixPartial 10 22210) = false := by
  decide +kernel

theorem node_context_10_22210_1239120 : EJMOriginalGlobalDAGData.nodes 11 ⟨1239120, by decide⟩ =
    .split (coordinate 10) (![⟨1238569, by decide⟩,⟨1238706, by decide⟩,⟨1238895, by decide⟩,⟨1239119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22210_1239120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22210 ⟨1239120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22210
    ⟨1239120, by decide⟩ (by decide) (![⟨1238569, by decide⟩,⟨1238706, by decide⟩,⟨1238895, by decide⟩,⟨1239119, by decide⟩]) unmarked_context_10_22210_1239120 node_context_10_22210_1239120
  intro a
  fin_cases a
  · exact context_11_88840_1238569
  · exact context_11_88841_1238706
  · exact context_11_88842_1238895
  · exact context_11_88843_1239119

theorem selected_cut_44909 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 355376) = some ⟨12, 1, 0, 985390, 355376, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355376_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355376 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 355376 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 355376, 1, 65536⟩
    (by decide) selected_cut_44909

theorem selected_cut_44910 : selected 9 ⟨1239162, by decide⟩
    (prefixPartial 12 355377) = some ⟨12, 2, 0, 1239162, 355377, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_355377_1239162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355377 ⟨1239162, by decide⟩ :=
  accepted_of_selected 12 355377 ⟨1239162, by decide⟩ ⟨12, 2, 0, 1239162, 355377, 2269, 65536⟩
    (by decide) selected_cut_44910

theorem selected_cut_44911 : selected 9 ⟨1239218, by decide⟩
    (prefixPartial 12 355378) = some ⟨12, 2, 0, 1239218, 355378, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_355378_1239218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355378 ⟨1239218, by decide⟩ :=
  accepted_of_selected 12 355378 ⟨1239218, by decide⟩ ⟨12, 2, 0, 1239218, 355378, 2517, 65536⟩
    (by decide) selected_cut_44911

theorem selected_cut_44912 : selected 9 ⟨1239270, by decide⟩
    (prefixPartial 12 355379) = some ⟨12, 2, 0, 1239270, 355379, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_355379_1239270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355379 ⟨1239270, by decide⟩ :=
  accepted_of_selected 12 355379 ⟨1239270, by decide⟩ ⟨12, 2, 0, 1239270, 355379, 2565, 65536⟩
    (by decide) selected_cut_44912

theorem unmarked_context_11_88844_1239271 : frontier 10 ⟨1239271, by decide⟩
    (prefixCache 11 88844) (prefixPartial 11 88844) = false := by
  decide +kernel

theorem node_context_11_88844_1239271 : EJMOriginalGlobalDAGData.nodes 10 ⟨1239271, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1239162, by decide⟩,⟨1239218, by decide⟩,⟨1239270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88844_1239271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88844 ⟨1239271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88844
    ⟨1239271, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1239162, by decide⟩,⟨1239218, by decide⟩,⟨1239270, by decide⟩]) unmarked_context_11_88844_1239271 node_context_11_88844_1239271
  intro a
  fin_cases a
  · exact context_12_355376_985390
  · exact context_12_355377_1239162
  · exact context_12_355378_1239218
  · exact context_12_355379_1239270

theorem selected_cut_44913 : selected 9 ⟨1197509, by decide⟩
    (prefixPartial 12 355380) = some ⟨12, 1, 0, 1197509, 355380, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355380_1197509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355380 ⟨1197509, by decide⟩ :=
  accepted_of_selected 12 355380 ⟨1197509, by decide⟩ ⟨12, 1, 0, 1197509, 355380, 1, 65536⟩
    (by decide) selected_cut_44913

theorem selected_cut_44914 : selected 9 ⟨719134, by decide⟩
    (prefixPartial 12 355381) = some ⟨12, 1, 0, 719134, 355381, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355381_719134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355381 ⟨719134, by decide⟩ :=
  accepted_of_selected 12 355381 ⟨719134, by decide⟩ ⟨12, 1, 0, 719134, 355381, 1, 65536⟩
    (by decide) selected_cut_44914

theorem selected_cut_44915 : selected 9 ⟨1239323, by decide⟩
    (prefixPartial 12 355382) = some ⟨12, 2, 0, 1239323, 355382, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_355382_1239323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355382 ⟨1239323, by decide⟩ :=
  accepted_of_selected 12 355382 ⟨1239323, by decide⟩ ⟨12, 2, 0, 1239323, 355382, 2425, 65536⟩
    (by decide) selected_cut_44915

theorem selected_cut_44916 : selected 9 ⟨1239370, by decide⟩
    (prefixPartial 12 355383) = some ⟨12, 2, 0, 1239370, 355383, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_355383_1239370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355383 ⟨1239370, by decide⟩ :=
  accepted_of_selected 12 355383 ⟨1239370, by decide⟩ ⟨12, 2, 0, 1239370, 355383, 2489, 65536⟩
    (by decide) selected_cut_44916

theorem unmarked_context_11_88845_1239371 : frontier 10 ⟨1239371, by decide⟩
    (prefixCache 11 88845) (prefixPartial 11 88845) = false := by
  decide +kernel

theorem node_context_11_88845_1239371 : EJMOriginalGlobalDAGData.nodes 10 ⟨1239371, by decide⟩ =
    .split (coordinate 11) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1239323, by decide⟩,⟨1239370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88845_1239371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88845 ⟨1239371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88845
    ⟨1239371, by decide⟩ (by decide) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1239323, by decide⟩,⟨1239370, by decide⟩]) unmarked_context_11_88845_1239371 node_context_11_88845_1239371
  intro a
  fin_cases a
  · exact context_12_355380_1197509
  · exact context_12_355381_719134
  · exact context_12_355382_1239323
  · exact context_12_355383_1239370

theorem selected_cut_44917 : selected 9 ⟨1239415, by decide⟩
    (prefixPartial 12 355384) = some ⟨12, 2, 0, 1239415, 355384, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_355384_1239415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355384 ⟨1239415, by decide⟩ :=
  accepted_of_selected 12 355384 ⟨1239415, by decide⟩ ⟨12, 2, 0, 1239415, 355384, 2245, 65536⟩
    (by decide) selected_cut_44917

theorem selected_cut_44918 : selected 9 ⟨1239451, by decide⟩
    (prefixPartial 12 355385) = some ⟨12, 2, 0, 1239451, 355385, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_355385_1239451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355385 ⟨1239451, by decide⟩ :=
  accepted_of_selected 12 355385 ⟨1239451, by decide⟩ ⟨12, 2, 0, 1239451, 355385, 2145, 65536⟩
    (by decide) selected_cut_44918

theorem selected_cut_44919 : selected 9 ⟨1239511, by decide⟩
    (prefixPartial 12 355386) = some ⟨12, 2, 0, 1239511, 355386, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_355386_1239511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355386 ⟨1239511, by decide⟩ :=
  accepted_of_selected 12 355386 ⟨1239511, by decide⟩ ⟨12, 2, 0, 1239511, 355386, 2433, 65536⟩
    (by decide) selected_cut_44919

theorem selected_cut_44920 : selected 9 ⟨1239565, by decide⟩
    (prefixPartial 12 355387) = some ⟨12, 2, 0, 1239565, 355387, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_355387_1239565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355387 ⟨1239565, by decide⟩ :=
  accepted_of_selected 12 355387 ⟨1239565, by decide⟩ ⟨12, 2, 0, 1239565, 355387, 2581, 65536⟩
    (by decide) selected_cut_44920

theorem unmarked_context_11_88846_1239566 : frontier 10 ⟨1239566, by decide⟩
    (prefixCache 11 88846) (prefixPartial 11 88846) = false := by
  decide +kernel

theorem node_context_11_88846_1239566 : EJMOriginalGlobalDAGData.nodes 10 ⟨1239566, by decide⟩ =
    .split (coordinate 11) (![⟨1239415, by decide⟩,⟨1239451, by decide⟩,⟨1239511, by decide⟩,⟨1239565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88846_1239566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88846 ⟨1239566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88846
    ⟨1239566, by decide⟩ (by decide) (![⟨1239415, by decide⟩,⟨1239451, by decide⟩,⟨1239511, by decide⟩,⟨1239565, by decide⟩]) unmarked_context_11_88846_1239566 node_context_11_88846_1239566
  intro a
  fin_cases a
  · exact context_12_355384_1239415
  · exact context_12_355385_1239451
  · exact context_12_355386_1239511
  · exact context_12_355387_1239565

theorem selected_cut_44921 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 88847) = some ⟨11, 1, 0, 977886, 88847, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88847_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88847 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 88847 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 88847, 1, 262144⟩
    (by decide) selected_cut_44921

theorem unmarked_context_10_22211_1239567 : frontier 11 ⟨1239567, by decide⟩
    (prefixCache 10 22211) (prefixPartial 10 22211) = false := by
  decide +kernel

theorem node_context_10_22211_1239567 : EJMOriginalGlobalDAGData.nodes 11 ⟨1239567, by decide⟩ =
    .split (coordinate 10) (![⟨1239271, by decide⟩,⟨1239371, by decide⟩,⟨1239566, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22211_1239567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22211 ⟨1239567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22211
    ⟨1239567, by decide⟩ (by decide) (![⟨1239271, by decide⟩,⟨1239371, by decide⟩,⟨1239566, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22211_1239567 node_context_10_22211_1239567
  intro a
  fin_cases a
  · exact context_11_88844_1239271
  · exact context_11_88845_1239371
  · exact context_11_88846_1239566
  · exact context_11_88847_977886

theorem unmarked_context_9_5552_1239568 : frontier 12 ⟨1239568, by decide⟩
    (prefixCache 9 5552) (prefixPartial 9 5552) = false := by
  decide +kernel

theorem node_context_9_5552_1239568 : EJMOriginalGlobalDAGData.nodes 12 ⟨1239568, by decide⟩ =
    .split (coordinate 9) (![⟨1237577, by decide⟩,⟨1238371, by decide⟩,⟨1239120, by decide⟩,⟨1239567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5552_1239568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5552 ⟨1239568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5552
    ⟨1239568, by decide⟩ (by decide) (![⟨1237577, by decide⟩,⟨1238371, by decide⟩,⟨1239120, by decide⟩,⟨1239567, by decide⟩]) unmarked_context_9_5552_1239568 node_context_9_5552_1239568
  intro a
  fin_cases a
  · exact context_10_22208_1237577
  · exact context_10_22209_1238371
  · exact context_10_22210_1239120
  · exact context_10_22211_1239567

theorem selected_cut_44922 : selected 10 ⟨1239619, by decide⟩
    (prefixPartial 11 88848) = some ⟨11, 2, 0, 1239619, 88848, 1941, 262144⟩ := by
  decide +kernel

theorem context_11_88848_1239619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88848 ⟨1239619, by decide⟩ :=
  accepted_of_selected 11 88848 ⟨1239619, by decide⟩ ⟨11, 2, 0, 1239619, 88848, 1941, 262144⟩
    (by decide) selected_cut_44922

theorem selected_cut_44923 : selected 9 ⟨1239651, by decide⟩
    (prefixPartial 12 355396) = some ⟨12, 2, 0, 1239651, 355396, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_355396_1239651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355396 ⟨1239651, by decide⟩ :=
  accepted_of_selected 12 355396 ⟨1239651, by decide⟩ ⟨12, 2, 0, 1239651, 355396, 1601, 65536⟩
    (by decide) selected_cut_44923

theorem selected_cut_44924 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 355397) = some ⟨12, 1, 0, 896706, 355397, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355397_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355397 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 355397 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 355397, 1, 65536⟩
    (by decide) selected_cut_44924

theorem selected_cut_44925 : selected 9 ⟨1239681, by decide⟩
    (prefixPartial 12 355398) = some ⟨12, 2, 0, 1239681, 355398, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_355398_1239681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355398 ⟨1239681, by decide⟩ :=
  accepted_of_selected 12 355398 ⟨1239681, by decide⟩ ⟨12, 2, 0, 1239681, 355398, 1733, 65536⟩
    (by decide) selected_cut_44925

theorem selected_cut_44926 : selected 9 ⟨1239712, by decide⟩
    (prefixPartial 12 355399) = some ⟨12, 2, 0, 1239712, 355399, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_355399_1239712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355399 ⟨1239712, by decide⟩ :=
  accepted_of_selected 12 355399 ⟨1239712, by decide⟩ ⟨12, 2, 0, 1239712, 355399, 1737, 65536⟩
    (by decide) selected_cut_44926

theorem unmarked_context_11_88849_1239713 : frontier 10 ⟨1239713, by decide⟩
    (prefixCache 11 88849) (prefixPartial 11 88849) = false := by
  decide +kernel

theorem node_context_11_88849_1239713 : EJMOriginalGlobalDAGData.nodes 10 ⟨1239713, by decide⟩ =
    .split (coordinate 11) (![⟨1239651, by decide⟩,⟨896706, by decide⟩,⟨1239681, by decide⟩,⟨1239712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88849_1239713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88849 ⟨1239713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88849
    ⟨1239713, by decide⟩ (by decide) (![⟨1239651, by decide⟩,⟨896706, by decide⟩,⟨1239681, by decide⟩,⟨1239712, by decide⟩]) unmarked_context_11_88849_1239713 node_context_11_88849_1239713
  intro a
  fin_cases a
  · exact context_12_355396_1239651
  · exact context_12_355397_896706
  · exact context_12_355398_1239681
  · exact context_12_355399_1239712

theorem selected_cut_44927 : selected 9 ⟨1239747, by decide⟩
    (prefixPartial 12 355400) = some ⟨12, 2, 0, 1239747, 355400, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_355400_1239747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355400 ⟨1239747, by decide⟩ :=
  accepted_of_selected 12 355400 ⟨1239747, by decide⟩ ⟨12, 2, 0, 1239747, 355400, 1649, 65536⟩
    (by decide) selected_cut_44927

theorem selected_cut_44928 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 355401) = some ⟨12, 1, 0, 896706, 355401, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355401_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355401 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 355401 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 355401, 1, 65536⟩
    (by decide) selected_cut_44928

theorem selected_cut_44929 : selected 9 ⟨1239785, by decide⟩
    (prefixPartial 12 355402) = some ⟨12, 2, 0, 1239785, 355402, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_355402_1239785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355402 ⟨1239785, by decide⟩ :=
  accepted_of_selected 12 355402 ⟨1239785, by decide⟩ ⟨12, 2, 0, 1239785, 355402, 1765, 65536⟩
    (by decide) selected_cut_44929

theorem selected_cut_44930 : selected 9 ⟨1239830, by decide⟩
    (prefixPartial 12 355403) = some ⟨12, 2, 0, 1239830, 355403, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_355403_1239830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355403 ⟨1239830, by decide⟩ :=
  accepted_of_selected 12 355403 ⟨1239830, by decide⟩ ⟨12, 2, 0, 1239830, 355403, 1877, 65536⟩
    (by decide) selected_cut_44930

theorem unmarked_context_11_88850_1239831 : frontier 10 ⟨1239831, by decide⟩
    (prefixCache 11 88850) (prefixPartial 11 88850) = false := by
  decide +kernel

theorem node_context_11_88850_1239831 : EJMOriginalGlobalDAGData.nodes 10 ⟨1239831, by decide⟩ =
    .split (coordinate 11) (![⟨1239747, by decide⟩,⟨896706, by decide⟩,⟨1239785, by decide⟩,⟨1239830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88850_1239831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88850 ⟨1239831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88850
    ⟨1239831, by decide⟩ (by decide) (![⟨1239747, by decide⟩,⟨896706, by decide⟩,⟨1239785, by decide⟩,⟨1239830, by decide⟩]) unmarked_context_11_88850_1239831 node_context_11_88850_1239831
  intro a
  fin_cases a
  · exact context_12_355400_1239747
  · exact context_12_355401_896706
  · exact context_12_355402_1239785
  · exact context_12_355403_1239830

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
