/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover538
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_51747 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 284826) = some ⟨11, 1, 0, 1468743, 284826, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284826_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284826 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 284826 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 284826, 1, 262144⟩
    (by decide) selected_cut_51747

theorem selected_cut_51748 : selected 10 ⟨1495706, by decide⟩
    (prefixPartial 11 284827) = some ⟨11, 2, 0, 1495706, 284827, 1365, 262144⟩ := by
  decide +kernel

theorem context_11_284827_1495706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284827 ⟨1495706, by decide⟩ :=
  accepted_of_selected 11 284827 ⟨1495706, by decide⟩ ⟨11, 2, 0, 1495706, 284827, 1365, 262144⟩
    (by decide) selected_cut_51748

theorem unmarked_context_10_71206_1495707 : frontier 11 ⟨1495707, by decide⟩
    (prefixCache 10 71206) (prefixPartial 10 71206) = false := by
  decide +kernel

theorem node_context_10_71206_1495707 : EJMOriginalGlobalDAGData.nodes 11 ⟨1495707, by decide⟩ =
    .split (coordinate 10) (![⟨1495655, by decide⟩,⟨1495682, by decide⟩,⟨1468743, by decide⟩,⟨1495706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71206_1495707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71206 ⟨1495707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71206
    ⟨1495707, by decide⟩ (by decide) (![⟨1495655, by decide⟩,⟨1495682, by decide⟩,⟨1468743, by decide⟩,⟨1495706, by decide⟩]) unmarked_context_10_71206_1495707 node_context_10_71206_1495707
  intro a
  fin_cases a
  · exact context_11_284824_1495655
  · exact context_11_284825_1495682
  · exact context_11_284826_1468743
  · exact context_11_284827_1495706

theorem selected_cut_51749 : selected 10 ⟨1495737, by decide⟩
    (prefixPartial 11 284828) = some ⟨11, 2, 0, 1495737, 284828, 1425, 262144⟩ := by
  decide +kernel

theorem context_11_284828_1495737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284828 ⟨1495737, by decide⟩ :=
  accepted_of_selected 11 284828 ⟨1495737, by decide⟩ ⟨11, 2, 0, 1495737, 284828, 1425, 262144⟩
    (by decide) selected_cut_51749

theorem selected_cut_51750 : selected 10 ⟨1495768, by decide⟩
    (prefixPartial 11 284829) = some ⟨11, 2, 0, 1495768, 284829, 1809, 262144⟩ := by
  decide +kernel

theorem context_11_284829_1495768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284829 ⟨1495768, by decide⟩ :=
  accepted_of_selected 11 284829 ⟨1495768, by decide⟩ ⟨11, 2, 0, 1495768, 284829, 1809, 262144⟩
    (by decide) selected_cut_51750

theorem selected_cut_51751 : selected 10 ⟨1495787, by decide⟩
    (prefixPartial 11 284830) = some ⟨11, 2, 0, 1495787, 284830, 1105, 262144⟩ := by
  decide +kernel

theorem context_11_284830_1495787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284830 ⟨1495787, by decide⟩ :=
  accepted_of_selected 11 284830 ⟨1495787, by decide⟩ ⟨11, 2, 0, 1495787, 284830, 1105, 262144⟩
    (by decide) selected_cut_51751

theorem selected_cut_51752 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 284831) = some ⟨11, 1, 0, 1470044, 284831, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284831_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284831 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 284831 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 284831, 1, 262144⟩
    (by decide) selected_cut_51752

theorem unmarked_context_10_71207_1495788 : frontier 11 ⟨1495788, by decide⟩
    (prefixCache 10 71207) (prefixPartial 10 71207) = false := by
  decide +kernel

theorem node_context_10_71207_1495788 : EJMOriginalGlobalDAGData.nodes 11 ⟨1495788, by decide⟩ =
    .split (coordinate 10) (![⟨1495737, by decide⟩,⟨1495768, by decide⟩,⟨1495787, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71207_1495788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71207 ⟨1495788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71207
    ⟨1495788, by decide⟩ (by decide) (![⟨1495737, by decide⟩,⟨1495768, by decide⟩,⟨1495787, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71207_1495788 node_context_10_71207_1495788
  intro a
  fin_cases a
  · exact context_11_284828_1495737
  · exact context_11_284829_1495768
  · exact context_11_284830_1495787
  · exact context_11_284831_1470044

theorem unmarked_context_9_17801_1495789 : frontier 12 ⟨1495789, by decide⟩
    (prefixCache 9 17801) (prefixPartial 9 17801) = false := by
  decide +kernel

theorem node_context_9_17801_1495789 : EJMOriginalGlobalDAGData.nodes 12 ⟨1495789, by decide⟩ =
    .split (coordinate 9) (![⟨1495597, by decide⟩,⟨1468874, by decide⟩,⟨1495707, by decide⟩,⟨1495788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17801_1495789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17801 ⟨1495789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17801
    ⟨1495789, by decide⟩ (by decide) (![⟨1495597, by decide⟩,⟨1468874, by decide⟩,⟨1495707, by decide⟩,⟨1495788, by decide⟩]) unmarked_context_9_17801_1495789 node_context_9_17801_1495789
  intro a
  fin_cases a
  · exact context_10_71204_1495597
  · exact context_10_71205_1468874
  · exact context_10_71206_1495707
  · exact context_10_71207_1495788

theorem selected_cut_51753 : selected 11 ⟨1495826, by decide⟩
    (prefixPartial 10 71208) = some ⟨10, 2, 0, 1495826, 71208, 2181, 1048576⟩ := by
  decide +kernel

theorem context_10_71208_1495826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71208 ⟨1495826, by decide⟩ :=
  accepted_of_selected 10 71208 ⟨1495826, by decide⟩ ⟨10, 2, 0, 1495826, 71208, 2181, 1048576⟩
    (by decide) selected_cut_51753

theorem selected_cut_51754 : selected 11 ⟨1495877, by decide⟩
    (prefixPartial 10 71209) = some ⟨10, 2, 0, 1495877, 71209, 2937, 1048576⟩ := by
  decide +kernel

theorem context_10_71209_1495877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71209 ⟨1495877, by decide⟩ :=
  accepted_of_selected 10 71209 ⟨1495877, by decide⟩ ⟨10, 2, 0, 1495877, 71209, 2937, 1048576⟩
    (by decide) selected_cut_51754

theorem selected_cut_51755 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71210) = some ⟨10, 1, 0, 1469103, 71210, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71210_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71210 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71210 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71210, 1, 1048576⟩
    (by decide) selected_cut_51755

theorem selected_cut_51756 : selected 11 ⟨1495930, by decide⟩
    (prefixPartial 10 71211) = some ⟨10, 2, 0, 1495930, 71211, 2493, 1048576⟩ := by
  decide +kernel

theorem context_10_71211_1495930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71211 ⟨1495930, by decide⟩ :=
  accepted_of_selected 10 71211 ⟨1495930, by decide⟩ ⟨10, 2, 0, 1495930, 71211, 2493, 1048576⟩
    (by decide) selected_cut_51756

theorem unmarked_context_9_17802_1495931 : frontier 12 ⟨1495931, by decide⟩
    (prefixCache 9 17802) (prefixPartial 9 17802) = false := by
  decide +kernel

theorem node_context_9_17802_1495931 : EJMOriginalGlobalDAGData.nodes 12 ⟨1495931, by decide⟩ =
    .split (coordinate 9) (![⟨1495826, by decide⟩,⟨1495877, by decide⟩,⟨1469103, by decide⟩,⟨1495930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17802_1495931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17802 ⟨1495931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17802
    ⟨1495931, by decide⟩ (by decide) (![⟨1495826, by decide⟩,⟨1495877, by decide⟩,⟨1469103, by decide⟩,⟨1495930, by decide⟩]) unmarked_context_9_17802_1495931 node_context_9_17802_1495931
  intro a
  fin_cases a
  · exact context_10_71208_1495826
  · exact context_10_71209_1495877
  · exact context_10_71210_1469103
  · exact context_10_71211_1495930

theorem selected_cut_51757 : selected 12 ⟨1495963, by decide⟩
    (prefixPartial 9 17803) = some ⟨9, 2, 0, 1495963, 17803, 2185, 4194304⟩ := by
  decide +kernel

theorem context_9_17803_1495963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17803 ⟨1495963, by decide⟩ :=
  accepted_of_selected 9 17803 ⟨1495963, by decide⟩ ⟨9, 2, 0, 1495963, 17803, 2185, 4194304⟩
    (by decide) selected_cut_51757

theorem unmarked_context_8_4450_1495964 : frontier 13 ⟨1495964, by decide⟩
    (prefixCache 8 4450) (prefixPartial 8 4450) = false := by
  decide +kernel

theorem node_context_8_4450_1495964 : EJMOriginalGlobalDAGData.nodes 13 ⟨1495964, by decide⟩ =
    .split (coordinate 8) (![⟨1495554, by decide⟩,⟨1495789, by decide⟩,⟨1495931, by decide⟩,⟨1495963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4450_1495964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4450 ⟨1495964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4450
    ⟨1495964, by decide⟩ (by decide) (![⟨1495554, by decide⟩,⟨1495789, by decide⟩,⟨1495931, by decide⟩,⟨1495963, by decide⟩]) unmarked_context_8_4450_1495964 node_context_8_4450_1495964
  intro a
  fin_cases a
  · exact context_9_17800_1495554
  · exact context_9_17801_1495789
  · exact context_9_17802_1495931
  · exact context_9_17803_1495963

theorem selected_cut_51758 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71216) = some ⟨10, 1, 0, 1468246, 71216, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71216_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71216 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71216 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71216, 1, 1048576⟩
    (by decide) selected_cut_51758

theorem selected_cut_51759 : selected 10 ⟨1496043, by decide⟩
    (prefixPartial 11 284868) = some ⟨11, 2, 0, 1496043, 284868, 3089, 262144⟩ := by
  decide +kernel

theorem context_11_284868_1496043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284868 ⟨1496043, by decide⟩ :=
  accepted_of_selected 11 284868 ⟨1496043, by decide⟩ ⟨11, 2, 0, 1496043, 284868, 3089, 262144⟩
    (by decide) selected_cut_51759

theorem selected_cut_51760 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 284869) = some ⟨11, 1, 0, 1468419, 284869, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284869_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284869 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 284869 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 284869, 1, 262144⟩
    (by decide) selected_cut_51760

theorem selected_cut_51761 : selected 10 ⟨1496141, by decide⟩
    (prefixPartial 11 284870) = some ⟨11, 2, 0, 1496141, 284870, 3357, 262144⟩ := by
  decide +kernel

theorem context_11_284870_1496141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284870 ⟨1496141, by decide⟩ :=
  accepted_of_selected 11 284870 ⟨1496141, by decide⟩ ⟨11, 2, 0, 1496141, 284870, 3357, 262144⟩
    (by decide) selected_cut_51761

theorem selected_cut_51762 : selected 10 ⟨1496182, by decide⟩
    (prefixPartial 11 284871) = some ⟨11, 2, 0, 1496182, 284871, 1605, 262144⟩ := by
  decide +kernel

theorem context_11_284871_1496182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284871 ⟨1496182, by decide⟩ :=
  accepted_of_selected 11 284871 ⟨1496182, by decide⟩ ⟨11, 2, 0, 1496182, 284871, 1605, 262144⟩
    (by decide) selected_cut_51762

theorem unmarked_context_10_71217_1496183 : frontier 11 ⟨1496183, by decide⟩
    (prefixCache 10 71217) (prefixPartial 10 71217) = false := by
  decide +kernel

theorem node_context_10_71217_1496183 : EJMOriginalGlobalDAGData.nodes 11 ⟨1496183, by decide⟩ =
    .split (coordinate 10) (![⟨1496043, by decide⟩,⟨1468419, by decide⟩,⟨1496141, by decide⟩,⟨1496182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71217_1496183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71217 ⟨1496183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71217
    ⟨1496183, by decide⟩ (by decide) (![⟨1496043, by decide⟩,⟨1468419, by decide⟩,⟨1496141, by decide⟩,⟨1496182, by decide⟩]) unmarked_context_10_71217_1496183 node_context_10_71217_1496183
  intro a
  fin_cases a
  · exact context_11_284868_1496043
  · exact context_11_284869_1468419
  · exact context_11_284870_1496141
  · exact context_11_284871_1496182

theorem selected_cut_51763 : selected 10 ⟨1496281, by decide⟩
    (prefixPartial 11 284872) = some ⟨11, 2, 0, 1496281, 284872, 4045, 262144⟩ := by
  decide +kernel

theorem context_11_284872_1496281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284872 ⟨1496281, by decide⟩ :=
  accepted_of_selected 11 284872 ⟨1496281, by decide⟩ ⟨11, 2, 0, 1496281, 284872, 4045, 262144⟩
    (by decide) selected_cut_51763

theorem selected_cut_51764 : selected 10 ⟨1496351, by decide⟩
    (prefixPartial 11 284873) = some ⟨11, 2, 0, 1496351, 284873, 2813, 262144⟩ := by
  decide +kernel

theorem context_11_284873_1496351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284873 ⟨1496351, by decide⟩ :=
  accepted_of_selected 11 284873 ⟨1496351, by decide⟩ ⟨11, 2, 0, 1496351, 284873, 2813, 262144⟩
    (by decide) selected_cut_51764

theorem selected_cut_51765 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 284874) = some ⟨11, 1, 0, 1468743, 284874, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284874_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284874 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 284874 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 284874, 1, 262144⟩
    (by decide) selected_cut_51765

theorem selected_cut_51766 : selected 10 ⟨1496414, by decide⟩
    (prefixPartial 11 284875) = some ⟨11, 2, 0, 1496414, 284875, 2645, 262144⟩ := by
  decide +kernel

theorem context_11_284875_1496414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284875 ⟨1496414, by decide⟩ :=
  accepted_of_selected 11 284875 ⟨1496414, by decide⟩ ⟨11, 2, 0, 1496414, 284875, 2645, 262144⟩
    (by decide) selected_cut_51766

theorem unmarked_context_10_71218_1496415 : frontier 11 ⟨1496415, by decide⟩
    (prefixCache 10 71218) (prefixPartial 10 71218) = false := by
  decide +kernel

theorem node_context_10_71218_1496415 : EJMOriginalGlobalDAGData.nodes 11 ⟨1496415, by decide⟩ =
    .split (coordinate 10) (![⟨1496281, by decide⟩,⟨1496351, by decide⟩,⟨1468743, by decide⟩,⟨1496414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71218_1496415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71218 ⟨1496415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71218
    ⟨1496415, by decide⟩ (by decide) (![⟨1496281, by decide⟩,⟨1496351, by decide⟩,⟨1468743, by decide⟩,⟨1496414, by decide⟩]) unmarked_context_10_71218_1496415 node_context_10_71218_1496415
  intro a
  fin_cases a
  · exact context_11_284872_1496281
  · exact context_11_284873_1496351
  · exact context_11_284874_1468743
  · exact context_11_284875_1496414

theorem selected_cut_51767 : selected 10 ⟨1496485, by decide⟩
    (prefixPartial 11 284876) = some ⟨11, 2, 0, 1496485, 284876, 2521, 262144⟩ := by
  decide +kernel

theorem context_11_284876_1496485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284876 ⟨1496485, by decide⟩ :=
  accepted_of_selected 11 284876 ⟨1496485, by decide⟩ ⟨11, 2, 0, 1496485, 284876, 2521, 262144⟩
    (by decide) selected_cut_51767

theorem selected_cut_51768 : selected 10 ⟨1496555, by decide⟩
    (prefixPartial 11 284877) = some ⟨11, 2, 0, 1496555, 284877, 2641, 262144⟩ := by
  decide +kernel

theorem context_11_284877_1496555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284877 ⟨1496555, by decide⟩ :=
  accepted_of_selected 11 284877 ⟨1496555, by decide⟩ ⟨11, 2, 0, 1496555, 284877, 2641, 262144⟩
    (by decide) selected_cut_51768

theorem selected_cut_51769 : selected 10 ⟨1496629, by decide⟩
    (prefixPartial 11 284878) = some ⟨11, 2, 0, 1496629, 284878, 2353, 262144⟩ := by
  decide +kernel

theorem context_11_284878_1496629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284878 ⟨1496629, by decide⟩ :=
  accepted_of_selected 11 284878 ⟨1496629, by decide⟩ ⟨11, 2, 0, 1496629, 284878, 2353, 262144⟩
    (by decide) selected_cut_51769

theorem selected_cut_51770 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 284879) = some ⟨11, 1, 0, 1470044, 284879, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284879_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284879 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 284879 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 284879, 1, 262144⟩
    (by decide) selected_cut_51770

theorem unmarked_context_10_71219_1496630 : frontier 11 ⟨1496630, by decide⟩
    (prefixCache 10 71219) (prefixPartial 10 71219) = false := by
  decide +kernel

theorem node_context_10_71219_1496630 : EJMOriginalGlobalDAGData.nodes 11 ⟨1496630, by decide⟩ =
    .split (coordinate 10) (![⟨1496485, by decide⟩,⟨1496555, by decide⟩,⟨1496629, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71219_1496630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71219 ⟨1496630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71219
    ⟨1496630, by decide⟩ (by decide) (![⟨1496485, by decide⟩,⟨1496555, by decide⟩,⟨1496629, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71219_1496630 node_context_10_71219_1496630
  intro a
  fin_cases a
  · exact context_11_284876_1496485
  · exact context_11_284877_1496555
  · exact context_11_284878_1496629
  · exact context_11_284879_1470044

theorem unmarked_context_9_17804_1496631 : frontier 12 ⟨1496631, by decide⟩
    (prefixCache 9 17804) (prefixPartial 9 17804) = false := by
  decide +kernel

theorem node_context_9_17804_1496631 : EJMOriginalGlobalDAGData.nodes 12 ⟨1496631, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1496183, by decide⟩,⟨1496415, by decide⟩,⟨1496630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17804_1496631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17804 ⟨1496631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17804
    ⟨1496631, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1496183, by decide⟩,⟨1496415, by decide⟩,⟨1496630, by decide⟩]) unmarked_context_9_17804_1496631 node_context_9_17804_1496631
  intro a
  fin_cases a
  · exact context_10_71216_1468246
  · exact context_10_71217_1496183
  · exact context_10_71218_1496415
  · exact context_10_71219_1496630

theorem selected_cut_51771 : selected 11 ⟨1496695, by decide⟩
    (prefixPartial 10 71220) = some ⟨10, 2, 0, 1496695, 71220, 3101, 1048576⟩ := by
  decide +kernel

theorem context_10_71220_1496695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71220 ⟨1496695, by decide⟩ :=
  accepted_of_selected 10 71220 ⟨1496695, by decide⟩ ⟨10, 2, 0, 1496695, 71220, 3101, 1048576⟩
    (by decide) selected_cut_51771

theorem selected_cut_51772 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71221) = some ⟨10, 1, 0, 1468874, 71221, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71221_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71221 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71221 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71221, 1, 1048576⟩
    (by decide) selected_cut_51772

theorem selected_cut_51773 : selected 10 ⟨1496737, by decide⟩
    (prefixPartial 11 284888) = some ⟨11, 2, 0, 1496737, 284888, 1633, 262144⟩ := by
  decide +kernel

theorem context_11_284888_1496737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284888 ⟨1496737, by decide⟩ :=
  accepted_of_selected 11 284888 ⟨1496737, by decide⟩ ⟨11, 2, 0, 1496737, 284888, 1633, 262144⟩
    (by decide) selected_cut_51773

theorem selected_cut_51774 : selected 10 ⟨1496779, by decide⟩
    (prefixPartial 11 284889) = some ⟨11, 2, 0, 1496779, 284889, 2241, 262144⟩ := by
  decide +kernel

theorem context_11_284889_1496779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284889 ⟨1496779, by decide⟩ :=
  accepted_of_selected 11 284889 ⟨1496779, by decide⟩ ⟨11, 2, 0, 1496779, 284889, 2241, 262144⟩
    (by decide) selected_cut_51774

theorem selected_cut_51775 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 284890) = some ⟨11, 1, 0, 1468743, 284890, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284890_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284890 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 284890 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 284890, 1, 262144⟩
    (by decide) selected_cut_51775

theorem selected_cut_51776 : selected 10 ⟨1496800, by decide⟩
    (prefixPartial 11 284891) = some ⟨11, 2, 0, 1496800, 284891, 1329, 262144⟩ := by
  decide +kernel

theorem context_11_284891_1496800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284891 ⟨1496800, by decide⟩ :=
  accepted_of_selected 11 284891 ⟨1496800, by decide⟩ ⟨11, 2, 0, 1496800, 284891, 1329, 262144⟩
    (by decide) selected_cut_51776

theorem unmarked_context_10_71222_1496801 : frontier 11 ⟨1496801, by decide⟩
    (prefixCache 10 71222) (prefixPartial 10 71222) = false := by
  decide +kernel

theorem node_context_10_71222_1496801 : EJMOriginalGlobalDAGData.nodes 11 ⟨1496801, by decide⟩ =
    .split (coordinate 10) (![⟨1496737, by decide⟩,⟨1496779, by decide⟩,⟨1468743, by decide⟩,⟨1496800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71222_1496801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71222 ⟨1496801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71222
    ⟨1496801, by decide⟩ (by decide) (![⟨1496737, by decide⟩,⟨1496779, by decide⟩,⟨1468743, by decide⟩,⟨1496800, by decide⟩]) unmarked_context_10_71222_1496801 node_context_10_71222_1496801
  intro a
  fin_cases a
  · exact context_11_284888_1496737
  · exact context_11_284889_1496779
  · exact context_11_284890_1468743
  · exact context_11_284891_1496800

theorem selected_cut_51777 : selected 11 ⟨1496878, by decide⟩
    (prefixPartial 10 71223) = some ⟨10, 2, 0, 1496878, 71223, 3381, 1048576⟩ := by
  decide +kernel

theorem context_10_71223_1496878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71223 ⟨1496878, by decide⟩ :=
  accepted_of_selected 10 71223 ⟨1496878, by decide⟩ ⟨10, 2, 0, 1496878, 71223, 3381, 1048576⟩
    (by decide) selected_cut_51777

theorem unmarked_context_9_17805_1496879 : frontier 12 ⟨1496879, by decide⟩
    (prefixCache 9 17805) (prefixPartial 9 17805) = false := by
  decide +kernel

theorem node_context_9_17805_1496879 : EJMOriginalGlobalDAGData.nodes 12 ⟨1496879, by decide⟩ =
    .split (coordinate 9) (![⟨1496695, by decide⟩,⟨1468874, by decide⟩,⟨1496801, by decide⟩,⟨1496878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17805_1496879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17805 ⟨1496879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17805
    ⟨1496879, by decide⟩ (by decide) (![⟨1496695, by decide⟩,⟨1468874, by decide⟩,⟨1496801, by decide⟩,⟨1496878, by decide⟩]) unmarked_context_9_17805_1496879 node_context_9_17805_1496879
  intro a
  fin_cases a
  · exact context_10_71220_1496695
  · exact context_10_71221_1468874
  · exact context_10_71222_1496801
  · exact context_10_71223_1496878

theorem selected_cut_51778 : selected 11 ⟨1496925, by decide⟩
    (prefixPartial 10 71224) = some ⟨10, 2, 0, 1496925, 71224, 2385, 1048576⟩ := by
  decide +kernel

theorem context_10_71224_1496925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71224 ⟨1496925, by decide⟩ :=
  accepted_of_selected 10 71224 ⟨1496925, by decide⟩ ⟨10, 2, 0, 1496925, 71224, 2385, 1048576⟩
    (by decide) selected_cut_51778

theorem selected_cut_51779 : selected 11 ⟨1496994, by decide⟩
    (prefixPartial 10 71225) = some ⟨10, 2, 0, 1496994, 71225, 3457, 1048576⟩ := by
  decide +kernel

theorem context_10_71225_1496994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71225 ⟨1496994, by decide⟩ :=
  accepted_of_selected 10 71225 ⟨1496994, by decide⟩ ⟨10, 2, 0, 1496994, 71225, 3457, 1048576⟩
    (by decide) selected_cut_51779

theorem selected_cut_51780 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71226) = some ⟨10, 1, 0, 1469103, 71226, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71226_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71226 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71226 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71226, 1, 1048576⟩
    (by decide) selected_cut_51780

theorem selected_cut_51781 : selected 11 ⟨1497065, by decide⟩
    (prefixPartial 10 71227) = some ⟨10, 2, 0, 1497065, 71227, 2401, 1048576⟩ := by
  decide +kernel

theorem context_10_71227_1497065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71227 ⟨1497065, by decide⟩ :=
  accepted_of_selected 10 71227 ⟨1497065, by decide⟩ ⟨10, 2, 0, 1497065, 71227, 2401, 1048576⟩
    (by decide) selected_cut_51781

theorem unmarked_context_9_17806_1497066 : frontier 12 ⟨1497066, by decide⟩
    (prefixCache 9 17806) (prefixPartial 9 17806) = false := by
  decide +kernel

theorem node_context_9_17806_1497066 : EJMOriginalGlobalDAGData.nodes 12 ⟨1497066, by decide⟩ =
    .split (coordinate 9) (![⟨1496925, by decide⟩,⟨1496994, by decide⟩,⟨1469103, by decide⟩,⟨1497065, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17806_1497066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17806 ⟨1497066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17806
    ⟨1497066, by decide⟩ (by decide) (![⟨1496925, by decide⟩,⟨1496994, by decide⟩,⟨1469103, by decide⟩,⟨1497065, by decide⟩]) unmarked_context_9_17806_1497066 node_context_9_17806_1497066
  intro a
  fin_cases a
  · exact context_10_71224_1496925
  · exact context_10_71225_1496994
  · exact context_10_71226_1469103
  · exact context_10_71227_1497065

theorem selected_cut_51782 : selected 12 ⟨1497118, by decide⟩
    (prefixPartial 9 17807) = some ⟨9, 2, 0, 1497118, 17807, 1965, 4194304⟩ := by
  decide +kernel

theorem context_9_17807_1497118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17807 ⟨1497118, by decide⟩ :=
  accepted_of_selected 9 17807 ⟨1497118, by decide⟩ ⟨9, 2, 0, 1497118, 17807, 1965, 4194304⟩
    (by decide) selected_cut_51782

theorem unmarked_context_8_4451_1497119 : frontier 13 ⟨1497119, by decide⟩
    (prefixCache 8 4451) (prefixPartial 8 4451) = false := by
  decide +kernel

theorem node_context_8_4451_1497119 : EJMOriginalGlobalDAGData.nodes 13 ⟨1497119, by decide⟩ =
    .split (coordinate 8) (![⟨1496631, by decide⟩,⟨1496879, by decide⟩,⟨1497066, by decide⟩,⟨1497118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4451_1497119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4451 ⟨1497119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4451
    ⟨1497119, by decide⟩ (by decide) (![⟨1496631, by decide⟩,⟨1496879, by decide⟩,⟨1497066, by decide⟩,⟨1497118, by decide⟩]) unmarked_context_8_4451_1497119 node_context_8_4451_1497119
  intro a
  fin_cases a
  · exact context_9_17804_1496631
  · exact context_9_17805_1496879
  · exact context_9_17806_1497066
  · exact context_9_17807_1497118

theorem unmarked_context_7_1112_1497120 : frontier 14 ⟨1497120, by decide⟩
    (prefixCache 7 1112) (prefixPartial 7 1112) = false := by
  decide +kernel

theorem node_context_7_1112_1497120 : EJMOriginalGlobalDAGData.nodes 14 ⟨1497120, by decide⟩ =
    .split (coordinate 7) (![⟨1493897, by decide⟩,⟨1494973, by decide⟩,⟨1495964, by decide⟩,⟨1497119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1112_1497120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1112 ⟨1497120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1112
    ⟨1497120, by decide⟩ (by decide) (![⟨1493897, by decide⟩,⟨1494973, by decide⟩,⟨1495964, by decide⟩,⟨1497119, by decide⟩]) unmarked_context_7_1112_1497120 node_context_7_1112_1497120
  intro a
  fin_cases a
  · exact context_8_4448_1493897
  · exact context_8_4449_1494973
  · exact context_8_4450_1495964
  · exact context_8_4451_1497119

theorem selected_cut_51783 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71232) = some ⟨10, 1, 0, 1468246, 71232, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71232_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71232 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71232 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71232, 1, 1048576⟩
    (by decide) selected_cut_51783

theorem selected_cut_51784 : selected 10 ⟨1497214, by decide⟩
    (prefixPartial 11 284932) = some ⟨11, 2, 0, 1497214, 284932, 2825, 262144⟩ := by
  decide +kernel

theorem context_11_284932_1497214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284932 ⟨1497214, by decide⟩ :=
  accepted_of_selected 11 284932 ⟨1497214, by decide⟩ ⟨11, 2, 0, 1497214, 284932, 2825, 262144⟩
    (by decide) selected_cut_51784

theorem selected_cut_51785 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 284933) = some ⟨11, 1, 0, 1468419, 284933, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284933_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284933 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 284933 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 284933, 1, 262144⟩
    (by decide) selected_cut_51785

theorem selected_cut_51786 : selected 10 ⟨1497296, by decide⟩
    (prefixPartial 11 284934) = some ⟨11, 2, 0, 1497296, 284934, 3157, 262144⟩ := by
  decide +kernel

theorem context_11_284934_1497296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284934 ⟨1497296, by decide⟩ :=
  accepted_of_selected 11 284934 ⟨1497296, by decide⟩ ⟨11, 2, 0, 1497296, 284934, 3157, 262144⟩
    (by decide) selected_cut_51786

theorem selected_cut_51787 : selected 10 ⟨1497347, by decide⟩
    (prefixPartial 11 284935) = some ⟨11, 2, 0, 1497347, 284935, 2033, 262144⟩ := by
  decide +kernel

theorem context_11_284935_1497347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284935 ⟨1497347, by decide⟩ :=
  accepted_of_selected 11 284935 ⟨1497347, by decide⟩ ⟨11, 2, 0, 1497347, 284935, 2033, 262144⟩
    (by decide) selected_cut_51787

theorem unmarked_context_10_71233_1497348 : frontier 11 ⟨1497348, by decide⟩
    (prefixCache 10 71233) (prefixPartial 10 71233) = false := by
  decide +kernel

theorem node_context_10_71233_1497348 : EJMOriginalGlobalDAGData.nodes 11 ⟨1497348, by decide⟩ =
    .split (coordinate 10) (![⟨1497214, by decide⟩,⟨1468419, by decide⟩,⟨1497296, by decide⟩,⟨1497347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71233_1497348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71233 ⟨1497348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71233
    ⟨1497348, by decide⟩ (by decide) (![⟨1497214, by decide⟩,⟨1468419, by decide⟩,⟨1497296, by decide⟩,⟨1497347, by decide⟩]) unmarked_context_10_71233_1497348 node_context_10_71233_1497348
  intro a
  fin_cases a
  · exact context_11_284932_1497214
  · exact context_11_284933_1468419
  · exact context_11_284934_1497296
  · exact context_11_284935_1497347

theorem selected_cut_51788 : selected 10 ⟨1497389, by decide⟩
    (prefixPartial 11 284936) = some ⟨11, 2, 0, 1497389, 284936, 2193, 262144⟩ := by
  decide +kernel

theorem context_11_284936_1497389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284936 ⟨1497389, by decide⟩ :=
  accepted_of_selected 11 284936 ⟨1497389, by decide⟩ ⟨11, 2, 0, 1497389, 284936, 2193, 262144⟩
    (by decide) selected_cut_51788

theorem selected_cut_51789 : selected 10 ⟨1497427, by decide⟩
    (prefixPartial 11 284937) = some ⟨11, 2, 0, 1497427, 284937, 2161, 262144⟩ := by
  decide +kernel

theorem context_11_284937_1497427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284937 ⟨1497427, by decide⟩ :=
  accepted_of_selected 11 284937 ⟨1497427, by decide⟩ ⟨11, 2, 0, 1497427, 284937, 2161, 262144⟩
    (by decide) selected_cut_51789

theorem selected_cut_51790 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 284938) = some ⟨11, 1, 0, 1468743, 284938, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284938_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284938 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 284938 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 284938, 1, 262144⟩
    (by decide) selected_cut_51790

theorem selected_cut_51791 : selected 10 ⟨1497473, by decide⟩
    (prefixPartial 11 284939) = some ⟨11, 2, 0, 1497473, 284939, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_284939_1497473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284939 ⟨1497473, by decide⟩ :=
  accepted_of_selected 11 284939 ⟨1497473, by decide⟩ ⟨11, 2, 0, 1497473, 284939, 2173, 262144⟩
    (by decide) selected_cut_51791

theorem unmarked_context_10_71234_1497474 : frontier 11 ⟨1497474, by decide⟩
    (prefixCache 10 71234) (prefixPartial 10 71234) = false := by
  decide +kernel

theorem node_context_10_71234_1497474 : EJMOriginalGlobalDAGData.nodes 11 ⟨1497474, by decide⟩ =
    .split (coordinate 10) (![⟨1497389, by decide⟩,⟨1497427, by decide⟩,⟨1468743, by decide⟩,⟨1497473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71234_1497474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71234 ⟨1497474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71234
    ⟨1497474, by decide⟩ (by decide) (![⟨1497389, by decide⟩,⟨1497427, by decide⟩,⟨1468743, by decide⟩,⟨1497473, by decide⟩]) unmarked_context_10_71234_1497474 node_context_10_71234_1497474
  intro a
  fin_cases a
  · exact context_11_284936_1497389
  · exact context_11_284937_1497427
  · exact context_11_284938_1468743
  · exact context_11_284939_1497473

theorem selected_cut_51792 : selected 10 ⟨1497515, by decide⟩
    (prefixPartial 11 284940) = some ⟨11, 2, 0, 1497515, 284940, 2061, 262144⟩ := by
  decide +kernel

theorem context_11_284940_1497515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284940 ⟨1497515, by decide⟩ :=
  accepted_of_selected 11 284940 ⟨1497515, by decide⟩ ⟨11, 2, 0, 1497515, 284940, 2061, 262144⟩
    (by decide) selected_cut_51792

theorem selected_cut_51793 : selected 10 ⟨1497552, by decide⟩
    (prefixPartial 11 284941) = some ⟨11, 2, 0, 1497552, 284941, 2057, 262144⟩ := by
  decide +kernel

theorem context_11_284941_1497552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284941 ⟨1497552, by decide⟩ :=
  accepted_of_selected 11 284941 ⟨1497552, by decide⟩ ⟨11, 2, 0, 1497552, 284941, 2057, 262144⟩
    (by decide) selected_cut_51793

theorem selected_cut_51794 : selected 10 ⟨1497592, by decide⟩
    (prefixPartial 11 284942) = some ⟨11, 2, 0, 1497592, 284942, 2141, 262144⟩ := by
  decide +kernel

theorem context_11_284942_1497592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284942 ⟨1497592, by decide⟩ :=
  accepted_of_selected 11 284942 ⟨1497592, by decide⟩ ⟨11, 2, 0, 1497592, 284942, 2141, 262144⟩
    (by decide) selected_cut_51794

theorem selected_cut_51795 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 284943) = some ⟨11, 1, 0, 1470044, 284943, 1, 262144⟩ := by
  decide +kernel

theorem context_11_284943_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 284943 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 284943 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 284943, 1, 262144⟩
    (by decide) selected_cut_51795

theorem unmarked_context_10_71235_1497593 : frontier 11 ⟨1497593, by decide⟩
    (prefixCache 10 71235) (prefixPartial 10 71235) = false := by
  decide +kernel

theorem node_context_10_71235_1497593 : EJMOriginalGlobalDAGData.nodes 11 ⟨1497593, by decide⟩ =
    .split (coordinate 10) (![⟨1497515, by decide⟩,⟨1497552, by decide⟩,⟨1497592, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71235_1497593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71235 ⟨1497593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71235
    ⟨1497593, by decide⟩ (by decide) (![⟨1497515, by decide⟩,⟨1497552, by decide⟩,⟨1497592, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71235_1497593 node_context_10_71235_1497593
  intro a
  fin_cases a
  · exact context_11_284940_1497515
  · exact context_11_284941_1497552
  · exact context_11_284942_1497592
  · exact context_11_284943_1470044

theorem unmarked_context_9_17808_1497594 : frontier 12 ⟨1497594, by decide⟩
    (prefixCache 9 17808) (prefixPartial 9 17808) = false := by
  decide +kernel

theorem node_context_9_17808_1497594 : EJMOriginalGlobalDAGData.nodes 12 ⟨1497594, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1497348, by decide⟩,⟨1497474, by decide⟩,⟨1497593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17808_1497594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17808 ⟨1497594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17808
    ⟨1497594, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1497348, by decide⟩,⟨1497474, by decide⟩,⟨1497593, by decide⟩]) unmarked_context_9_17808_1497594 node_context_9_17808_1497594
  intro a
  fin_cases a
  · exact context_10_71232_1468246
  · exact context_10_71233_1497348
  · exact context_10_71234_1497474
  · exact context_10_71235_1497593

theorem selected_cut_51796 : selected 11 ⟨1497688, by decide⟩
    (prefixPartial 10 71236) = some ⟨10, 2, 0, 1497688, 71236, 2341, 1048576⟩ := by
  decide +kernel

theorem context_10_71236_1497688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71236 ⟨1497688, by decide⟩ :=
  accepted_of_selected 10 71236 ⟨1497688, by decide⟩ ⟨10, 2, 0, 1497688, 71236, 2341, 1048576⟩
    (by decide) selected_cut_51796

theorem selected_cut_51797 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71237) = some ⟨10, 1, 0, 1468874, 71237, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71237_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71237 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71237 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71237, 1, 1048576⟩
    (by decide) selected_cut_51797

theorem selected_cut_51798 : selected 11 ⟨1497792, by decide⟩
    (prefixPartial 10 71238) = some ⟨10, 2, 0, 1497792, 71238, 3721, 1048576⟩ := by
  decide +kernel

theorem context_10_71238_1497792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71238 ⟨1497792, by decide⟩ :=
  accepted_of_selected 10 71238 ⟨1497792, by decide⟩ ⟨10, 2, 0, 1497792, 71238, 3721, 1048576⟩
    (by decide) selected_cut_51798

theorem selected_cut_51799 : selected 11 ⟨1497876, by decide⟩
    (prefixPartial 10 71239) = some ⟨10, 2, 0, 1497876, 71239, 3421, 1048576⟩ := by
  decide +kernel

theorem context_10_71239_1497876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71239 ⟨1497876, by decide⟩ :=
  accepted_of_selected 10 71239 ⟨1497876, by decide⟩ ⟨10, 2, 0, 1497876, 71239, 3421, 1048576⟩
    (by decide) selected_cut_51799

theorem unmarked_context_9_17809_1497877 : frontier 12 ⟨1497877, by decide⟩
    (prefixCache 9 17809) (prefixPartial 9 17809) = false := by
  decide +kernel

theorem node_context_9_17809_1497877 : EJMOriginalGlobalDAGData.nodes 12 ⟨1497877, by decide⟩ =
    .split (coordinate 9) (![⟨1497688, by decide⟩,⟨1468874, by decide⟩,⟨1497792, by decide⟩,⟨1497876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17809_1497877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17809 ⟨1497877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17809
    ⟨1497877, by decide⟩ (by decide) (![⟨1497688, by decide⟩,⟨1468874, by decide⟩,⟨1497792, by decide⟩,⟨1497876, by decide⟩]) unmarked_context_9_17809_1497877 node_context_9_17809_1497877
  intro a
  fin_cases a
  · exact context_10_71236_1497688
  · exact context_10_71237_1468874
  · exact context_10_71238_1497792
  · exact context_10_71239_1497876

theorem selected_cut_51800 : selected 11 ⟨1497926, by decide⟩
    (prefixPartial 10 71240) = some ⟨10, 2, 0, 1497926, 71240, 3021, 1048576⟩ := by
  decide +kernel

theorem context_10_71240_1497926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71240 ⟨1497926, by decide⟩ :=
  accepted_of_selected 10 71240 ⟨1497926, by decide⟩ ⟨10, 2, 0, 1497926, 71240, 3021, 1048576⟩
    (by decide) selected_cut_51800

theorem selected_cut_51801 : selected 11 ⟨1498025, by decide⟩
    (prefixPartial 10 71241) = some ⟨10, 2, 0, 1498025, 71241, 3129, 1048576⟩ := by
  decide +kernel

theorem context_10_71241_1498025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71241 ⟨1498025, by decide⟩ :=
  accepted_of_selected 10 71241 ⟨1498025, by decide⟩ ⟨10, 2, 0, 1498025, 71241, 3129, 1048576⟩
    (by decide) selected_cut_51801

theorem selected_cut_51802 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71242) = some ⟨10, 1, 0, 1469103, 71242, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71242_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71242 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71242 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71242, 1, 1048576⟩
    (by decide) selected_cut_51802

theorem selected_cut_51803 : selected 11 ⟨1498077, by decide⟩
    (prefixPartial 10 71243) = some ⟨10, 2, 0, 1498077, 71243, 2121, 1048576⟩ := by
  decide +kernel

theorem context_10_71243_1498077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71243 ⟨1498077, by decide⟩ :=
  accepted_of_selected 10 71243 ⟨1498077, by decide⟩ ⟨10, 2, 0, 1498077, 71243, 2121, 1048576⟩
    (by decide) selected_cut_51803

theorem unmarked_context_9_17810_1498078 : frontier 12 ⟨1498078, by decide⟩
    (prefixCache 9 17810) (prefixPartial 9 17810) = false := by
  decide +kernel

theorem node_context_9_17810_1498078 : EJMOriginalGlobalDAGData.nodes 12 ⟨1498078, by decide⟩ =
    .split (coordinate 9) (![⟨1497926, by decide⟩,⟨1498025, by decide⟩,⟨1469103, by decide⟩,⟨1498077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17810_1498078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17810 ⟨1498078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17810
    ⟨1498078, by decide⟩ (by decide) (![⟨1497926, by decide⟩,⟨1498025, by decide⟩,⟨1469103, by decide⟩,⟨1498077, by decide⟩]) unmarked_context_9_17810_1498078 node_context_9_17810_1498078
  intro a
  fin_cases a
  · exact context_10_71240_1497926
  · exact context_10_71241_1498025
  · exact context_10_71242_1469103
  · exact context_10_71243_1498077

theorem selected_cut_51804 : selected 12 ⟨1498136, by decide⟩
    (prefixPartial 9 17811) = some ⟨9, 2, 0, 1498136, 17811, 2497, 4194304⟩ := by
  decide +kernel

theorem context_9_17811_1498136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17811 ⟨1498136, by decide⟩ :=
  accepted_of_selected 9 17811 ⟨1498136, by decide⟩ ⟨9, 2, 0, 1498136, 17811, 2497, 4194304⟩
    (by decide) selected_cut_51804

theorem unmarked_context_8_4452_1498137 : frontier 13 ⟨1498137, by decide⟩
    (prefixCache 8 4452) (prefixPartial 8 4452) = false := by
  decide +kernel

theorem node_context_8_4452_1498137 : EJMOriginalGlobalDAGData.nodes 13 ⟨1498137, by decide⟩ =
    .split (coordinate 8) (![⟨1497594, by decide⟩,⟨1497877, by decide⟩,⟨1498078, by decide⟩,⟨1498136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4452_1498137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4452 ⟨1498137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4452
    ⟨1498137, by decide⟩ (by decide) (![⟨1497594, by decide⟩,⟨1497877, by decide⟩,⟨1498078, by decide⟩,⟨1498136, by decide⟩]) unmarked_context_8_4452_1498137 node_context_8_4452_1498137
  intro a
  fin_cases a
  · exact context_9_17808_1497594
  · exact context_9_17809_1497877
  · exact context_9_17810_1498078
  · exact context_9_17811_1498136

theorem selected_cut_51805 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71248) = some ⟨10, 1, 0, 1468246, 71248, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71248_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71248 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71248 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71248, 1, 1048576⟩
    (by decide) selected_cut_51805

theorem selected_cut_51806 : selected 11 ⟨1498238, by decide⟩
    (prefixPartial 10 71249) = some ⟨10, 2, 0, 1498238, 71249, 3613, 1048576⟩ := by
  decide +kernel

theorem context_10_71249_1498238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71249 ⟨1498238, by decide⟩ :=
  accepted_of_selected 10 71249 ⟨1498238, by decide⟩ ⟨10, 2, 0, 1498238, 71249, 3613, 1048576⟩
    (by decide) selected_cut_51806

theorem selected_cut_51807 : selected 10 ⟨1498296, by decide⟩
    (prefixPartial 11 285000) = some ⟨11, 2, 0, 1498296, 285000, 2021, 262144⟩ := by
  decide +kernel

theorem context_11_285000_1498296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285000 ⟨1498296, by decide⟩ :=
  accepted_of_selected 11 285000 ⟨1498296, by decide⟩ ⟨11, 2, 0, 1498296, 285000, 2021, 262144⟩
    (by decide) selected_cut_51807

theorem selected_cut_51808 : selected 10 ⟨1498314, by decide⟩
    (prefixPartial 11 285001) = some ⟨11, 2, 0, 1498314, 285001, 837, 262144⟩ := by
  decide +kernel

theorem context_11_285001_1498314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285001 ⟨1498314, by decide⟩ :=
  accepted_of_selected 11 285001 ⟨1498314, by decide⟩ ⟨11, 2, 0, 1498314, 285001, 837, 262144⟩
    (by decide) selected_cut_51808

theorem selected_cut_51809 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 285002) = some ⟨11, 1, 0, 1468743, 285002, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285002_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285002 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 285002 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 285002, 1, 262144⟩
    (by decide) selected_cut_51809

theorem selected_cut_51810 : selected 10 ⟨1498351, by decide⟩
    (prefixPartial 11 285003) = some ⟨11, 2, 0, 1498351, 285003, 1833, 262144⟩ := by
  decide +kernel

theorem context_11_285003_1498351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285003 ⟨1498351, by decide⟩ :=
  accepted_of_selected 11 285003 ⟨1498351, by decide⟩ ⟨11, 2, 0, 1498351, 285003, 1833, 262144⟩
    (by decide) selected_cut_51810

theorem unmarked_context_10_71250_1498352 : frontier 11 ⟨1498352, by decide⟩
    (prefixCache 10 71250) (prefixPartial 10 71250) = false := by
  decide +kernel

theorem node_context_10_71250_1498352 : EJMOriginalGlobalDAGData.nodes 11 ⟨1498352, by decide⟩ =
    .split (coordinate 10) (![⟨1498296, by decide⟩,⟨1498314, by decide⟩,⟨1468743, by decide⟩,⟨1498351, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71250_1498352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71250 ⟨1498352, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71250
    ⟨1498352, by decide⟩ (by decide) (![⟨1498296, by decide⟩,⟨1498314, by decide⟩,⟨1468743, by decide⟩,⟨1498351, by decide⟩]) unmarked_context_10_71250_1498352 node_context_10_71250_1498352
  intro a
  fin_cases a
  · exact context_11_285000_1498296
  · exact context_11_285001_1498314
  · exact context_11_285002_1468743
  · exact context_11_285003_1498351

theorem selected_cut_51811 : selected 10 ⟨1498411, by decide⟩
    (prefixPartial 11 285004) = some ⟨11, 2, 0, 1498411, 285004, 1917, 262144⟩ := by
  decide +kernel

theorem context_11_285004_1498411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285004 ⟨1498411, by decide⟩ :=
  accepted_of_selected 11 285004 ⟨1498411, by decide⟩ ⟨11, 2, 0, 1498411, 285004, 1917, 262144⟩
    (by decide) selected_cut_51811

theorem selected_cut_51812 : selected 10 ⟨1498429, by decide⟩
    (prefixPartial 11 285005) = some ⟨11, 2, 0, 1498429, 285005, 717, 262144⟩ := by
  decide +kernel

theorem context_11_285005_1498429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285005 ⟨1498429, by decide⟩ :=
  accepted_of_selected 11 285005 ⟨1498429, by decide⟩ ⟨11, 2, 0, 1498429, 285005, 717, 262144⟩
    (by decide) selected_cut_51812

theorem selected_cut_51813 : selected 10 ⟨1498478, by decide⟩
    (prefixPartial 11 285006) = some ⟨11, 2, 0, 1498478, 285006, 1733, 262144⟩ := by
  decide +kernel

theorem context_11_285006_1498478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285006 ⟨1498478, by decide⟩ :=
  accepted_of_selected 11 285006 ⟨1498478, by decide⟩ ⟨11, 2, 0, 1498478, 285006, 1733, 262144⟩
    (by decide) selected_cut_51813

theorem selected_cut_51814 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 285007) = some ⟨11, 1, 0, 1470044, 285007, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285007_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285007 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 285007 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 285007, 1, 262144⟩
    (by decide) selected_cut_51814

theorem unmarked_context_10_71251_1498479 : frontier 11 ⟨1498479, by decide⟩
    (prefixCache 10 71251) (prefixPartial 10 71251) = false := by
  decide +kernel

theorem node_context_10_71251_1498479 : EJMOriginalGlobalDAGData.nodes 11 ⟨1498479, by decide⟩ =
    .split (coordinate 10) (![⟨1498411, by decide⟩,⟨1498429, by decide⟩,⟨1498478, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71251_1498479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71251 ⟨1498479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71251
    ⟨1498479, by decide⟩ (by decide) (![⟨1498411, by decide⟩,⟨1498429, by decide⟩,⟨1498478, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71251_1498479 node_context_10_71251_1498479
  intro a
  fin_cases a
  · exact context_11_285004_1498411
  · exact context_11_285005_1498429
  · exact context_11_285006_1498478
  · exact context_11_285007_1470044

theorem unmarked_context_9_17812_1498480 : frontier 12 ⟨1498480, by decide⟩
    (prefixCache 9 17812) (prefixPartial 9 17812) = false := by
  decide +kernel

theorem node_context_9_17812_1498480 : EJMOriginalGlobalDAGData.nodes 12 ⟨1498480, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1498238, by decide⟩,⟨1498352, by decide⟩,⟨1498479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17812_1498480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17812 ⟨1498480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17812
    ⟨1498480, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1498238, by decide⟩,⟨1498352, by decide⟩,⟨1498479, by decide⟩]) unmarked_context_9_17812_1498480 node_context_9_17812_1498480
  intro a
  fin_cases a
  · exact context_10_71248_1468246
  · exact context_10_71249_1498238
  · exact context_10_71250_1498352
  · exact context_10_71251_1498479

theorem selected_cut_51815 : selected 11 ⟨1498545, by decide⟩
    (prefixPartial 10 71252) = some ⟨10, 2, 0, 1498545, 71252, 1385, 1048576⟩ := by
  decide +kernel

theorem context_10_71252_1498545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71252 ⟨1498545, by decide⟩ :=
  accepted_of_selected 10 71252 ⟨1498545, by decide⟩ ⟨10, 2, 0, 1498545, 71252, 1385, 1048576⟩
    (by decide) selected_cut_51815

theorem selected_cut_51816 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71253) = some ⟨10, 1, 0, 1468874, 71253, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71253_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71253 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71253 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71253, 1, 1048576⟩
    (by decide) selected_cut_51816

theorem selected_cut_51817 : selected 11 ⟨1498623, by decide⟩
    (prefixPartial 10 71254) = some ⟨10, 2, 0, 1498623, 71254, 2957, 1048576⟩ := by
  decide +kernel

theorem context_10_71254_1498623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71254 ⟨1498623, by decide⟩ :=
  accepted_of_selected 10 71254 ⟨1498623, by decide⟩ ⟨10, 2, 0, 1498623, 71254, 2957, 1048576⟩
    (by decide) selected_cut_51817

theorem selected_cut_51818 : selected 11 ⟨1498681, by decide⟩
    (prefixPartial 10 71255) = some ⟨10, 2, 0, 1498681, 71255, 2685, 1048576⟩ := by
  decide +kernel

theorem context_10_71255_1498681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71255 ⟨1498681, by decide⟩ :=
  accepted_of_selected 10 71255 ⟨1498681, by decide⟩ ⟨10, 2, 0, 1498681, 71255, 2685, 1048576⟩
    (by decide) selected_cut_51818

theorem unmarked_context_9_17813_1498682 : frontier 12 ⟨1498682, by decide⟩
    (prefixCache 9 17813) (prefixPartial 9 17813) = false := by
  decide +kernel

theorem node_context_9_17813_1498682 : EJMOriginalGlobalDAGData.nodes 12 ⟨1498682, by decide⟩ =
    .split (coordinate 9) (![⟨1498545, by decide⟩,⟨1468874, by decide⟩,⟨1498623, by decide⟩,⟨1498681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17813_1498682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17813 ⟨1498682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17813
    ⟨1498682, by decide⟩ (by decide) (![⟨1498545, by decide⟩,⟨1468874, by decide⟩,⟨1498623, by decide⟩,⟨1498681, by decide⟩]) unmarked_context_9_17813_1498682 node_context_9_17813_1498682
  intro a
  fin_cases a
  · exact context_10_71252_1498545
  · exact context_10_71253_1468874
  · exact context_10_71254_1498623
  · exact context_10_71255_1498681

theorem selected_cut_51819 : selected 11 ⟨1498725, by decide⟩
    (prefixPartial 10 71256) = some ⟨10, 2, 0, 1498725, 71256, 2049, 1048576⟩ := by
  decide +kernel

theorem context_10_71256_1498725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71256 ⟨1498725, by decide⟩ :=
  accepted_of_selected 10 71256 ⟨1498725, by decide⟩ ⟨10, 2, 0, 1498725, 71256, 2049, 1048576⟩
    (by decide) selected_cut_51819

theorem selected_cut_51820 : selected 11 ⟨1498763, by decide⟩
    (prefixPartial 10 71257) = some ⟨10, 2, 0, 1498763, 71257, 2009, 1048576⟩ := by
  decide +kernel

theorem context_10_71257_1498763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71257 ⟨1498763, by decide⟩ :=
  accepted_of_selected 10 71257 ⟨1498763, by decide⟩ ⟨10, 2, 0, 1498763, 71257, 2009, 1048576⟩
    (by decide) selected_cut_51820

theorem selected_cut_51821 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71258) = some ⟨10, 1, 0, 1469103, 71258, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71258_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71258 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71258 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71258, 1, 1048576⟩
    (by decide) selected_cut_51821

theorem selected_cut_51822 : selected 11 ⟨1498797, by decide⟩
    (prefixPartial 10 71259) = some ⟨10, 2, 0, 1498797, 71259, 1301, 1048576⟩ := by
  decide +kernel

theorem context_10_71259_1498797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71259 ⟨1498797, by decide⟩ :=
  accepted_of_selected 10 71259 ⟨1498797, by decide⟩ ⟨10, 2, 0, 1498797, 71259, 1301, 1048576⟩
    (by decide) selected_cut_51822

theorem unmarked_context_9_17814_1498798 : frontier 12 ⟨1498798, by decide⟩
    (prefixCache 9 17814) (prefixPartial 9 17814) = false := by
  decide +kernel

theorem node_context_9_17814_1498798 : EJMOriginalGlobalDAGData.nodes 12 ⟨1498798, by decide⟩ =
    .split (coordinate 9) (![⟨1498725, by decide⟩,⟨1498763, by decide⟩,⟨1469103, by decide⟩,⟨1498797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17814_1498798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17814 ⟨1498798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17814
    ⟨1498798, by decide⟩ (by decide) (![⟨1498725, by decide⟩,⟨1498763, by decide⟩,⟨1469103, by decide⟩,⟨1498797, by decide⟩]) unmarked_context_9_17814_1498798 node_context_9_17814_1498798
  intro a
  fin_cases a
  · exact context_10_71256_1498725
  · exact context_10_71257_1498763
  · exact context_10_71258_1469103
  · exact context_10_71259_1498797

theorem selected_cut_51823 : selected 12 ⟨1498856, by decide⟩
    (prefixPartial 9 17815) = some ⟨9, 2, 0, 1498856, 17815, 1745, 4194304⟩ := by
  decide +kernel

theorem context_9_17815_1498856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17815 ⟨1498856, by decide⟩ :=
  accepted_of_selected 9 17815 ⟨1498856, by decide⟩ ⟨9, 2, 0, 1498856, 17815, 1745, 4194304⟩
    (by decide) selected_cut_51823

theorem unmarked_context_8_4453_1498857 : frontier 13 ⟨1498857, by decide⟩
    (prefixCache 8 4453) (prefixPartial 8 4453) = false := by
  decide +kernel

theorem node_context_8_4453_1498857 : EJMOriginalGlobalDAGData.nodes 13 ⟨1498857, by decide⟩ =
    .split (coordinate 8) (![⟨1498480, by decide⟩,⟨1498682, by decide⟩,⟨1498798, by decide⟩,⟨1498856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4453_1498857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4453 ⟨1498857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4453
    ⟨1498857, by decide⟩ (by decide) (![⟨1498480, by decide⟩,⟨1498682, by decide⟩,⟨1498798, by decide⟩,⟨1498856, by decide⟩]) unmarked_context_8_4453_1498857 node_context_8_4453_1498857
  intro a
  fin_cases a
  · exact context_9_17812_1498480
  · exact context_9_17813_1498682
  · exact context_9_17814_1498798
  · exact context_9_17815_1498856

theorem selected_cut_51824 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71264) = some ⟨10, 1, 0, 1468246, 71264, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71264_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71264 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71264 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71264, 1, 1048576⟩
    (by decide) selected_cut_51824

theorem selected_cut_51825 : selected 10 ⟨1498927, by decide⟩
    (prefixPartial 11 285060) = some ⟨11, 2, 0, 1498927, 285060, 3201, 262144⟩ := by
  decide +kernel

theorem context_11_285060_1498927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285060 ⟨1498927, by decide⟩ :=
  accepted_of_selected 11 285060 ⟨1498927, by decide⟩ ⟨11, 2, 0, 1498927, 285060, 3201, 262144⟩
    (by decide) selected_cut_51825

theorem selected_cut_51826 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 285061) = some ⟨11, 1, 0, 1468419, 285061, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285061_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285061 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 285061 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 285061, 1, 262144⟩
    (by decide) selected_cut_51826

theorem selected_cut_51827 : selected 10 ⟨1499033, by decide⟩
    (prefixPartial 11 285062) = some ⟨11, 2, 0, 1499033, 285062, 2729, 262144⟩ := by
  decide +kernel

theorem context_11_285062_1499033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285062 ⟨1499033, by decide⟩ :=
  accepted_of_selected 11 285062 ⟨1499033, by decide⟩ ⟨11, 2, 0, 1499033, 285062, 2729, 262144⟩
    (by decide) selected_cut_51827

theorem selected_cut_51828 : selected 10 ⟨1499099, by decide⟩
    (prefixPartial 11 285063) = some ⟨11, 2, 0, 1499099, 285063, 2825, 262144⟩ := by
  decide +kernel

theorem context_11_285063_1499099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285063 ⟨1499099, by decide⟩ :=
  accepted_of_selected 11 285063 ⟨1499099, by decide⟩ ⟨11, 2, 0, 1499099, 285063, 2825, 262144⟩
    (by decide) selected_cut_51828

theorem unmarked_context_10_71265_1499100 : frontier 11 ⟨1499100, by decide⟩
    (prefixCache 10 71265) (prefixPartial 10 71265) = false := by
  decide +kernel

theorem node_context_10_71265_1499100 : EJMOriginalGlobalDAGData.nodes 11 ⟨1499100, by decide⟩ =
    .split (coordinate 10) (![⟨1498927, by decide⟩,⟨1468419, by decide⟩,⟨1499033, by decide⟩,⟨1499099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71265_1499100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71265 ⟨1499100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71265
    ⟨1499100, by decide⟩ (by decide) (![⟨1498927, by decide⟩,⟨1468419, by decide⟩,⟨1499033, by decide⟩,⟨1499099, by decide⟩]) unmarked_context_10_71265_1499100 node_context_10_71265_1499100
  intro a
  fin_cases a
  · exact context_11_285060_1498927
  · exact context_11_285061_1468419
  · exact context_11_285062_1499033
  · exact context_11_285063_1499099

theorem selected_cut_51829 : selected 10 ⟨1499180, by decide⟩
    (prefixPartial 11 285064) = some ⟨11, 2, 0, 1499180, 285064, 3649, 262144⟩ := by
  decide +kernel

theorem context_11_285064_1499180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285064 ⟨1499180, by decide⟩ :=
  accepted_of_selected 11 285064 ⟨1499180, by decide⟩ ⟨11, 2, 0, 1499180, 285064, 3649, 262144⟩
    (by decide) selected_cut_51829

theorem selected_cut_51830 : selected 10 ⟨1499227, by decide⟩
    (prefixPartial 11 285065) = some ⟨11, 2, 0, 1499227, 285065, 1885, 262144⟩ := by
  decide +kernel

theorem context_11_285065_1499227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285065 ⟨1499227, by decide⟩ :=
  accepted_of_selected 11 285065 ⟨1499227, by decide⟩ ⟨11, 2, 0, 1499227, 285065, 1885, 262144⟩
    (by decide) selected_cut_51830

theorem selected_cut_51831 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 285066) = some ⟨11, 1, 0, 1468743, 285066, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285066_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285066 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 285066 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 285066, 1, 262144⟩
    (by decide) selected_cut_51831

theorem selected_cut_51832 : selected 10 ⟨1499272, by decide⟩
    (prefixPartial 11 285067) = some ⟨11, 2, 0, 1499272, 285067, 1957, 262144⟩ := by
  decide +kernel

theorem context_11_285067_1499272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285067 ⟨1499272, by decide⟩ :=
  accepted_of_selected 11 285067 ⟨1499272, by decide⟩ ⟨11, 2, 0, 1499272, 285067, 1957, 262144⟩
    (by decide) selected_cut_51832

theorem unmarked_context_10_71266_1499273 : frontier 11 ⟨1499273, by decide⟩
    (prefixCache 10 71266) (prefixPartial 10 71266) = false := by
  decide +kernel

theorem node_context_10_71266_1499273 : EJMOriginalGlobalDAGData.nodes 11 ⟨1499273, by decide⟩ =
    .split (coordinate 10) (![⟨1499180, by decide⟩,⟨1499227, by decide⟩,⟨1468743, by decide⟩,⟨1499272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71266_1499273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71266 ⟨1499273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71266
    ⟨1499273, by decide⟩ (by decide) (![⟨1499180, by decide⟩,⟨1499227, by decide⟩,⟨1468743, by decide⟩,⟨1499272, by decide⟩]) unmarked_context_10_71266_1499273 node_context_10_71266_1499273
  intro a
  fin_cases a
  · exact context_11_285064_1499180
  · exact context_11_285065_1499227
  · exact context_11_285066_1468743
  · exact context_11_285067_1499272

theorem selected_cut_51833 : selected 10 ⟨1499349, by decide⟩
    (prefixPartial 11 285068) = some ⟨11, 2, 0, 1499349, 285068, 2989, 262144⟩ := by
  decide +kernel

theorem context_11_285068_1499349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285068 ⟨1499349, by decide⟩ :=
  accepted_of_selected 11 285068 ⟨1499349, by decide⟩ ⟨11, 2, 0, 1499349, 285068, 2989, 262144⟩
    (by decide) selected_cut_51833

theorem selected_cut_51834 : selected 10 ⟨1499390, by decide⟩
    (prefixPartial 11 285069) = some ⟨11, 2, 0, 1499390, 285069, 1565, 262144⟩ := by
  decide +kernel

theorem context_11_285069_1499390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285069 ⟨1499390, by decide⟩ :=
  accepted_of_selected 11 285069 ⟨1499390, by decide⟩ ⟨11, 2, 0, 1499390, 285069, 1565, 262144⟩
    (by decide) selected_cut_51834

theorem selected_cut_51835 : selected 10 ⟨1499457, by decide⟩
    (prefixPartial 11 285070) = some ⟨11, 2, 0, 1499457, 285070, 613, 262144⟩ := by
  decide +kernel

theorem context_11_285070_1499457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285070 ⟨1499457, by decide⟩ :=
  accepted_of_selected 11 285070 ⟨1499457, by decide⟩ ⟨11, 2, 0, 1499457, 285070, 613, 262144⟩
    (by decide) selected_cut_51835

theorem selected_cut_51836 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 285071) = some ⟨11, 1, 0, 1470044, 285071, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285071_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285071 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 285071 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 285071, 1, 262144⟩
    (by decide) selected_cut_51836

theorem unmarked_context_10_71267_1499458 : frontier 11 ⟨1499458, by decide⟩
    (prefixCache 10 71267) (prefixPartial 10 71267) = false := by
  decide +kernel

theorem node_context_10_71267_1499458 : EJMOriginalGlobalDAGData.nodes 11 ⟨1499458, by decide⟩ =
    .split (coordinate 10) (![⟨1499349, by decide⟩,⟨1499390, by decide⟩,⟨1499457, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71267_1499458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71267 ⟨1499458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71267
    ⟨1499458, by decide⟩ (by decide) (![⟨1499349, by decide⟩,⟨1499390, by decide⟩,⟨1499457, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71267_1499458 node_context_10_71267_1499458
  intro a
  fin_cases a
  · exact context_11_285068_1499349
  · exact context_11_285069_1499390
  · exact context_11_285070_1499457
  · exact context_11_285071_1470044

theorem unmarked_context_9_17816_1499459 : frontier 12 ⟨1499459, by decide⟩
    (prefixCache 9 17816) (prefixPartial 9 17816) = false := by
  decide +kernel

theorem node_context_9_17816_1499459 : EJMOriginalGlobalDAGData.nodes 12 ⟨1499459, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1499100, by decide⟩,⟨1499273, by decide⟩,⟨1499458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17816_1499459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17816 ⟨1499459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17816
    ⟨1499459, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1499100, by decide⟩,⟨1499273, by decide⟩,⟨1499458, by decide⟩]) unmarked_context_9_17816_1499459 node_context_9_17816_1499459
  intro a
  fin_cases a
  · exact context_10_71264_1468246
  · exact context_10_71265_1499100
  · exact context_10_71266_1499273
  · exact context_10_71267_1499458

theorem selected_cut_51837 : selected 11 ⟨1499521, by decide⟩
    (prefixPartial 10 71268) = some ⟨10, 2, 0, 1499521, 71268, 1609, 1048576⟩ := by
  decide +kernel

theorem context_10_71268_1499521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71268 ⟨1499521, by decide⟩ :=
  accepted_of_selected 10 71268 ⟨1499521, by decide⟩ ⟨10, 2, 0, 1499521, 71268, 1609, 1048576⟩
    (by decide) selected_cut_51837

theorem selected_cut_51838 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71269) = some ⟨10, 1, 0, 1468874, 71269, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71269_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71269 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71269 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71269, 1, 1048576⟩
    (by decide) selected_cut_51838

theorem selected_cut_51839 : selected 11 ⟨1499651, by decide⟩
    (prefixPartial 10 71270) = some ⟨10, 2, 0, 1499651, 71270, 2593, 1048576⟩ := by
  decide +kernel

theorem context_10_71270_1499651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71270 ⟨1499651, by decide⟩ :=
  accepted_of_selected 10 71270 ⟨1499651, by decide⟩ ⟨10, 2, 0, 1499651, 71270, 2593, 1048576⟩
    (by decide) selected_cut_51839

theorem selected_cut_51840 : selected 11 ⟨1499696, by decide⟩
    (prefixPartial 10 71271) = some ⟨10, 2, 0, 1499696, 71271, 925, 1048576⟩ := by
  decide +kernel

theorem context_10_71271_1499696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71271 ⟨1499696, by decide⟩ :=
  accepted_of_selected 10 71271 ⟨1499696, by decide⟩ ⟨10, 2, 0, 1499696, 71271, 925, 1048576⟩
    (by decide) selected_cut_51840

theorem unmarked_context_9_17817_1499697 : frontier 12 ⟨1499697, by decide⟩
    (prefixCache 9 17817) (prefixPartial 9 17817) = false := by
  decide +kernel

theorem node_context_9_17817_1499697 : EJMOriginalGlobalDAGData.nodes 12 ⟨1499697, by decide⟩ =
    .split (coordinate 9) (![⟨1499521, by decide⟩,⟨1468874, by decide⟩,⟨1499651, by decide⟩,⟨1499696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17817_1499697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17817 ⟨1499697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17817
    ⟨1499697, by decide⟩ (by decide) (![⟨1499521, by decide⟩,⟨1468874, by decide⟩,⟨1499651, by decide⟩,⟨1499696, by decide⟩]) unmarked_context_9_17817_1499697 node_context_9_17817_1499697
  intro a
  fin_cases a
  · exact context_10_71268_1499521
  · exact context_10_71269_1468874
  · exact context_10_71270_1499651
  · exact context_10_71271_1499696

theorem selected_cut_51841 : selected 12 ⟨1499802, by decide⟩
    (prefixPartial 9 17818) = some ⟨9, 2, 0, 1499802, 17818, 1605, 4194304⟩ := by
  decide +kernel

theorem context_9_17818_1499802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17818 ⟨1499802, by decide⟩ :=
  accepted_of_selected 9 17818 ⟨1499802, by decide⟩ ⟨9, 2, 0, 1499802, 17818, 1605, 4194304⟩
    (by decide) selected_cut_51841

theorem selected_cut_51842 : selected 12 ⟨1499848, by decide⟩
    (prefixPartial 9 17819) = some ⟨9, 2, 0, 1499848, 17819, 497, 4194304⟩ := by
  decide +kernel

theorem context_9_17819_1499848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17819 ⟨1499848, by decide⟩ :=
  accepted_of_selected 9 17819 ⟨1499848, by decide⟩ ⟨9, 2, 0, 1499848, 17819, 497, 4194304⟩
    (by decide) selected_cut_51842

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
