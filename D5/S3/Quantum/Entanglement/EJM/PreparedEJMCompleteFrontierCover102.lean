/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover101
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_09794 : selected 9 ⟨269994, by decide⟩
    (prefixPartial 12 24668) = some ⟨12, 2, 0, 269994, 24668, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_24668_269994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24668 ⟨269994, by decide⟩ :=
  accepted_of_selected 12 24668 ⟨269994, by decide⟩ ⟨12, 2, 0, 269994, 24668, 2965, 65536⟩
    (by decide) selected_cut_09794

theorem selected_cut_09795 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98676) = some ⟨13, 1, 0, 3444, 98676, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98676_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98676 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98676 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98676, 1, 16384⟩
    (by decide) selected_cut_09795

theorem selected_cut_09796 : selected 8 ⟨270017, by decide⟩
    (prefixPartial 13 98677) = some ⟨13, 2, 0, 270017, 98677, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_98677_270017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98677 ⟨270017, by decide⟩ :=
  accepted_of_selected 13 98677 ⟨270017, by decide⟩ ⟨13, 2, 0, 270017, 98677, 1785, 16384⟩
    (by decide) selected_cut_09796

theorem selected_cut_09797 : selected 8 ⟨270052, by decide⟩
    (prefixPartial 13 98678) = some ⟨13, 2, 0, 270052, 98678, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_98678_270052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98678 ⟨270052, by decide⟩ :=
  accepted_of_selected 13 98678 ⟨270052, by decide⟩ ⟨13, 2, 0, 270052, 98678, 2417, 16384⟩
    (by decide) selected_cut_09797

theorem selected_cut_09798 : selected 8 ⟨270064, by decide⟩
    (prefixPartial 13 98679) = some ⟨13, 2, 0, 270064, 98679, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_98679_270064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98679 ⟨270064, by decide⟩ :=
  accepted_of_selected 13 98679 ⟨270064, by decide⟩ ⟨13, 2, 0, 270064, 98679, 1101, 16384⟩
    (by decide) selected_cut_09798

theorem unmarked_context_12_24669_270065 : frontier 9 ⟨270065, by decide⟩
    (prefixCache 12 24669) (prefixPartial 12 24669) = false := by
  decide +kernel

theorem node_context_12_24669_270065 : EJMOriginalGlobalDAGData.nodes 9 ⟨270065, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨270017, by decide⟩,⟨270052, by decide⟩,⟨270064, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24669_270065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24669 ⟨270065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24669
    ⟨270065, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨270017, by decide⟩,⟨270052, by decide⟩,⟨270064, by decide⟩]) unmarked_context_12_24669_270065 node_context_12_24669_270065
  intro a
  fin_cases a
  · exact context_13_98676_3444
  · exact context_13_98677_270017
  · exact context_13_98678_270052
  · exact context_13_98679_270064

theorem selected_cut_09799 : selected 9 ⟨270108, by decide⟩
    (prefixPartial 12 24670) = some ⟨12, 2, 0, 270108, 24670, 3841, 65536⟩ := by
  decide +kernel

theorem context_12_24670_270108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24670 ⟨270108, by decide⟩ :=
  accepted_of_selected 12 24670 ⟨270108, by decide⟩ ⟨12, 2, 0, 270108, 24670, 3841, 65536⟩
    (by decide) selected_cut_09799

theorem selected_cut_09800 : selected 9 ⟨270155, by decide⟩
    (prefixPartial 12 24671) = some ⟨12, 2, 0, 270155, 24671, 4069, 65536⟩ := by
  decide +kernel

theorem context_12_24671_270155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24671 ⟨270155, by decide⟩ :=
  accepted_of_selected 12 24671 ⟨270155, by decide⟩ ⟨12, 2, 0, 270155, 24671, 4069, 65536⟩
    (by decide) selected_cut_09800

theorem unmarked_context_11_6167_270156 : frontier 10 ⟨270156, by decide⟩
    (prefixCache 11 6167) (prefixPartial 11 6167) = false := by
  decide +kernel

theorem node_context_11_6167_270156 : EJMOriginalGlobalDAGData.nodes 10 ⟨270156, by decide⟩ =
    .split (coordinate 11) (![⟨269994, by decide⟩,⟨270065, by decide⟩,⟨270108, by decide⟩,⟨270155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6167_270156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6167 ⟨270156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6167
    ⟨270156, by decide⟩ (by decide) (![⟨269994, by decide⟩,⟨270065, by decide⟩,⟨270108, by decide⟩,⟨270155, by decide⟩]) unmarked_context_11_6167_270156 node_context_11_6167_270156
  intro a
  fin_cases a
  · exact context_12_24668_269994
  · exact context_12_24669_270065
  · exact context_12_24670_270108
  · exact context_12_24671_270155

theorem unmarked_context_10_1541_270157 : frontier 11 ⟨270157, by decide⟩
    (prefixCache 10 1541) (prefixPartial 10 1541) = false := by
  decide +kernel

theorem node_context_10_1541_270157 : EJMOriginalGlobalDAGData.nodes 11 ⟨270157, by decide⟩ =
    .split (coordinate 10) (![⟨269594, by decide⟩,⟨269739, by decide⟩,⟨269952, by decide⟩,⟨270156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1541_270157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1541 ⟨270157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1541
    ⟨270157, by decide⟩ (by decide) (![⟨269594, by decide⟩,⟨269739, by decide⟩,⟨269952, by decide⟩,⟨270156, by decide⟩]) unmarked_context_10_1541_270157 node_context_10_1541_270157
  intro a
  fin_cases a
  · exact context_11_6164_269594
  · exact context_11_6165_269739
  · exact context_11_6166_269952
  · exact context_11_6167_270156

theorem selected_cut_09801 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98688) = some ⟨13, 1, 0, 3444, 98688, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98688_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98688 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98688 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98688, 1, 16384⟩
    (by decide) selected_cut_09801

theorem selected_cut_09802 : selected 8 ⟨270171, by decide⟩
    (prefixPartial 13 98689) = some ⟨13, 2, 0, 270171, 98689, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_98689_270171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98689 ⟨270171, by decide⟩ :=
  accepted_of_selected 13 98689 ⟨270171, by decide⟩ ⟨13, 2, 0, 270171, 98689, 1705, 16384⟩
    (by decide) selected_cut_09802

theorem selected_cut_09803 : selected 8 ⟨270198, by decide⟩
    (prefixPartial 13 98690) = some ⟨13, 2, 0, 270198, 98690, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_98690_270198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98690 ⟨270198, by decide⟩ :=
  accepted_of_selected 13 98690 ⟨270198, by decide⟩ ⟨13, 2, 0, 270198, 98690, 2113, 16384⟩
    (by decide) selected_cut_09803

theorem selected_cut_09804 : selected 8 ⟨270205, by decide⟩
    (prefixPartial 13 98691) = some ⟨13, 2, 0, 270205, 98691, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_98691_270205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98691 ⟨270205, by decide⟩ :=
  accepted_of_selected 13 98691 ⟨270205, by decide⟩ ⟨13, 2, 0, 270205, 98691, 1037, 16384⟩
    (by decide) selected_cut_09804

theorem unmarked_context_12_24672_270206 : frontier 9 ⟨270206, by decide⟩
    (prefixCache 12 24672) (prefixPartial 12 24672) = false := by
  decide +kernel

theorem node_context_12_24672_270206 : EJMOriginalGlobalDAGData.nodes 9 ⟨270206, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨270171, by decide⟩,⟨270198, by decide⟩,⟨270205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24672_270206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24672 ⟨270206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24672
    ⟨270206, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨270171, by decide⟩,⟨270198, by decide⟩,⟨270205, by decide⟩]) unmarked_context_12_24672_270206 node_context_12_24672_270206
  intro a
  fin_cases a
  · exact context_13_98688_3444
  · exact context_13_98689_270171
  · exact context_13_98690_270198
  · exact context_13_98691_270205

theorem selected_cut_09805 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98692) = some ⟨13, 1, 0, 3444, 98692, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98692_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98692 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98692 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98692, 1, 16384⟩
    (by decide) selected_cut_09805

theorem selected_cut_09806 : selected 8 ⟨270219, by decide⟩
    (prefixPartial 13 98693) = some ⟨13, 2, 0, 270219, 98693, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_98693_270219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98693 ⟨270219, by decide⟩ :=
  accepted_of_selected 13 98693 ⟨270219, by decide⟩ ⟨13, 2, 0, 270219, 98693, 1549, 16384⟩
    (by decide) selected_cut_09806

theorem selected_cut_09807 : selected 8 ⟨270240, by decide⟩
    (prefixPartial 13 98694) = some ⟨13, 2, 0, 270240, 98694, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_98694_270240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98694 ⟨270240, by decide⟩ :=
  accepted_of_selected 13 98694 ⟨270240, by decide⟩ ⟨13, 2, 0, 270240, 98694, 2049, 16384⟩
    (by decide) selected_cut_09807

theorem selected_cut_09808 : selected 8 ⟨270249, by decide⟩
    (prefixPartial 13 98695) = some ⟨13, 2, 0, 270249, 98695, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_98695_270249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98695 ⟨270249, by decide⟩ :=
  accepted_of_selected 13 98695 ⟨270249, by decide⟩ ⟨13, 2, 0, 270249, 98695, 1041, 16384⟩
    (by decide) selected_cut_09808

theorem unmarked_context_12_24673_270250 : frontier 9 ⟨270250, by decide⟩
    (prefixCache 12 24673) (prefixPartial 12 24673) = false := by
  decide +kernel

theorem node_context_12_24673_270250 : EJMOriginalGlobalDAGData.nodes 9 ⟨270250, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨270219, by decide⟩,⟨270240, by decide⟩,⟨270249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24673_270250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24673 ⟨270250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24673
    ⟨270250, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨270219, by decide⟩,⟨270240, by decide⟩,⟨270249, by decide⟩]) unmarked_context_12_24673_270250 node_context_12_24673_270250
  intro a
  fin_cases a
  · exact context_13_98692_3444
  · exact context_13_98693_270219
  · exact context_13_98694_270240
  · exact context_13_98695_270249

theorem selected_cut_09809 : selected 9 ⟨270289, by decide⟩
    (prefixPartial 12 24674) = some ⟨12, 2, 0, 270289, 24674, 3361, 65536⟩ := by
  decide +kernel

theorem context_12_24674_270289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24674 ⟨270289, by decide⟩ :=
  accepted_of_selected 12 24674 ⟨270289, by decide⟩ ⟨12, 2, 0, 270289, 24674, 3361, 65536⟩
    (by decide) selected_cut_09809

theorem selected_cut_09810 : selected 9 ⟨270327, by decide⟩
    (prefixPartial 12 24675) = some ⟨12, 2, 0, 270327, 24675, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_24675_270327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24675 ⟨270327, by decide⟩ :=
  accepted_of_selected 12 24675 ⟨270327, by decide⟩ ⟨12, 2, 0, 270327, 24675, 3413, 65536⟩
    (by decide) selected_cut_09810

theorem unmarked_context_11_6168_270328 : frontier 10 ⟨270328, by decide⟩
    (prefixCache 11 6168) (prefixPartial 11 6168) = false := by
  decide +kernel

theorem node_context_11_6168_270328 : EJMOriginalGlobalDAGData.nodes 10 ⟨270328, by decide⟩ =
    .split (coordinate 11) (![⟨270206, by decide⟩,⟨270250, by decide⟩,⟨270289, by decide⟩,⟨270327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6168_270328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6168 ⟨270328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6168
    ⟨270328, by decide⟩ (by decide) (![⟨270206, by decide⟩,⟨270250, by decide⟩,⟨270289, by decide⟩,⟨270327, by decide⟩]) unmarked_context_11_6168_270328 node_context_11_6168_270328
  intro a
  fin_cases a
  · exact context_12_24672_270206
  · exact context_12_24673_270250
  · exact context_12_24674_270289
  · exact context_12_24675_270327

theorem selected_cut_09811 : selected 9 ⟨270365, by decide⟩
    (prefixPartial 12 24676) = some ⟨12, 2, 0, 270365, 24676, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_24676_270365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24676 ⟨270365, by decide⟩ :=
  accepted_of_selected 12 24676 ⟨270365, by decide⟩ ⟨12, 2, 0, 270365, 24676, 3041, 65536⟩
    (by decide) selected_cut_09811

theorem selected_cut_09812 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98708) = some ⟨13, 1, 0, 3444, 98708, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98708_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98708 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98708 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98708, 1, 16384⟩
    (by decide) selected_cut_09812

theorem selected_cut_09813 : selected 8 ⟨270379, by decide⟩
    (prefixPartial 13 98709) = some ⟨13, 2, 0, 270379, 98709, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_98709_270379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98709 ⟨270379, by decide⟩ :=
  accepted_of_selected 13 98709 ⟨270379, by decide⟩ ⟨13, 2, 0, 270379, 98709, 1401, 16384⟩
    (by decide) selected_cut_09813

theorem selected_cut_09814 : selected 8 ⟨270415, by decide⟩
    (prefixPartial 13 98710) = some ⟨13, 2, 0, 270415, 98710, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_98710_270415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98710 ⟨270415, by decide⟩ :=
  accepted_of_selected 13 98710 ⟨270415, by decide⟩ ⟨13, 2, 0, 270415, 98710, 2501, 16384⟩
    (by decide) selected_cut_09814

theorem selected_cut_09815 : selected 8 ⟨270420, by decide⟩
    (prefixPartial 13 98711) = some ⟨13, 2, 0, 270420, 98711, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_98711_270420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98711 ⟨270420, by decide⟩ :=
  accepted_of_selected 13 98711 ⟨270420, by decide⟩ ⟨13, 2, 0, 270420, 98711, 1077, 16384⟩
    (by decide) selected_cut_09815

theorem unmarked_context_12_24677_270421 : frontier 9 ⟨270421, by decide⟩
    (prefixCache 12 24677) (prefixPartial 12 24677) = false := by
  decide +kernel

theorem node_context_12_24677_270421 : EJMOriginalGlobalDAGData.nodes 9 ⟨270421, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨270379, by decide⟩,⟨270415, by decide⟩,⟨270420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24677_270421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24677 ⟨270421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24677
    ⟨270421, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨270379, by decide⟩,⟨270415, by decide⟩,⟨270420, by decide⟩]) unmarked_context_12_24677_270421 node_context_12_24677_270421
  intro a
  fin_cases a
  · exact context_13_98708_3444
  · exact context_13_98709_270379
  · exact context_13_98710_270415
  · exact context_13_98711_270420

theorem selected_cut_09816 : selected 9 ⟨270464, by decide⟩
    (prefixPartial 12 24678) = some ⟨12, 2, 0, 270464, 24678, 3949, 65536⟩ := by
  decide +kernel

theorem context_12_24678_270464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24678 ⟨270464, by decide⟩ :=
  accepted_of_selected 12 24678 ⟨270464, by decide⟩ ⟨12, 2, 0, 270464, 24678, 3949, 65536⟩
    (by decide) selected_cut_09816

theorem selected_cut_09817 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98716) = some ⟨13, 1, 0, 3444, 98716, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98716_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98716 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98716 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98716, 1, 16384⟩
    (by decide) selected_cut_09817

theorem selected_cut_09818 : selected 8 ⟨270477, by decide⟩
    (prefixPartial 13 98717) = some ⟨13, 2, 0, 270477, 98717, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_98717_270477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98717 ⟨270477, by decide⟩ :=
  accepted_of_selected 13 98717 ⟨270477, by decide⟩ ⟨13, 2, 0, 270477, 98717, 1213, 16384⟩
    (by decide) selected_cut_09818

theorem selected_cut_09819 : selected 8 ⟨270501, by decide⟩
    (prefixPartial 13 98718) = some ⟨13, 2, 0, 270501, 98718, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_98718_270501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98718 ⟨270501, by decide⟩ :=
  accepted_of_selected 13 98718 ⟨270501, by decide⟩ ⟨13, 2, 0, 270501, 98718, 1933, 16384⟩
    (by decide) selected_cut_09819

theorem selected_cut_09820 : selected 8 ⟨270511, by decide⟩
    (prefixPartial 13 98719) = some ⟨13, 2, 0, 270511, 98719, 949, 16384⟩ := by
  decide +kernel

theorem context_13_98719_270511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98719 ⟨270511, by decide⟩ :=
  accepted_of_selected 13 98719 ⟨270511, by decide⟩ ⟨13, 2, 0, 270511, 98719, 949, 16384⟩
    (by decide) selected_cut_09820

theorem unmarked_context_12_24679_270512 : frontier 9 ⟨270512, by decide⟩
    (prefixCache 12 24679) (prefixPartial 12 24679) = false := by
  decide +kernel

theorem node_context_12_24679_270512 : EJMOriginalGlobalDAGData.nodes 9 ⟨270512, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨270477, by decide⟩,⟨270501, by decide⟩,⟨270511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24679_270512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24679 ⟨270512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24679
    ⟨270512, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨270477, by decide⟩,⟨270501, by decide⟩,⟨270511, by decide⟩]) unmarked_context_12_24679_270512 node_context_12_24679_270512
  intro a
  fin_cases a
  · exact context_13_98716_3444
  · exact context_13_98717_270477
  · exact context_13_98718_270501
  · exact context_13_98719_270511

theorem unmarked_context_11_6169_270513 : frontier 10 ⟨270513, by decide⟩
    (prefixCache 11 6169) (prefixPartial 11 6169) = false := by
  decide +kernel

theorem node_context_11_6169_270513 : EJMOriginalGlobalDAGData.nodes 10 ⟨270513, by decide⟩ =
    .split (coordinate 11) (![⟨270365, by decide⟩,⟨270421, by decide⟩,⟨270464, by decide⟩,⟨270512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6169_270513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6169 ⟨270513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6169
    ⟨270513, by decide⟩ (by decide) (![⟨270365, by decide⟩,⟨270421, by decide⟩,⟨270464, by decide⟩,⟨270512, by decide⟩]) unmarked_context_11_6169_270513 node_context_11_6169_270513
  intro a
  fin_cases a
  · exact context_12_24676_270365
  · exact context_12_24677_270421
  · exact context_12_24678_270464
  · exact context_12_24679_270512

theorem selected_cut_09821 : selected 9 ⟨270549, by decide⟩
    (prefixPartial 12 24680) = some ⟨12, 2, 0, 270549, 24680, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_24680_270549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24680 ⟨270549, by decide⟩ :=
  accepted_of_selected 12 24680 ⟨270549, by decide⟩ ⟨12, 2, 0, 270549, 24680, 3169, 65536⟩
    (by decide) selected_cut_09821

theorem selected_cut_09822 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98724) = some ⟨13, 1, 0, 3444, 98724, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98724_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98724 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98724 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98724, 1, 16384⟩
    (by decide) selected_cut_09822

theorem selected_cut_09823 : selected 8 ⟨270563, by decide⟩
    (prefixPartial 13 98725) = some ⟨13, 2, 0, 270563, 98725, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_98725_270563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98725 ⟨270563, by decide⟩ :=
  accepted_of_selected 13 98725 ⟨270563, by decide⟩ ⟨13, 2, 0, 270563, 98725, 1297, 16384⟩
    (by decide) selected_cut_09823

theorem selected_cut_09824 : selected 8 ⟨270593, by decide⟩
    (prefixPartial 13 98726) = some ⟨13, 2, 0, 270593, 98726, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_98726_270593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98726 ⟨270593, by decide⟩ :=
  accepted_of_selected 13 98726 ⟨270593, by decide⟩ ⟨13, 2, 0, 270593, 98726, 2385, 16384⟩
    (by decide) selected_cut_09824

theorem selected_cut_09825 : selected 8 ⟨270601, by decide⟩
    (prefixPartial 13 98727) = some ⟨13, 2, 0, 270601, 98727, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_98727_270601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98727 ⟨270601, by decide⟩ :=
  accepted_of_selected 13 98727 ⟨270601, by decide⟩ ⟨13, 2, 0, 270601, 98727, 1033, 16384⟩
    (by decide) selected_cut_09825

theorem unmarked_context_12_24681_270602 : frontier 9 ⟨270602, by decide⟩
    (prefixCache 12 24681) (prefixPartial 12 24681) = false := by
  decide +kernel

theorem node_context_12_24681_270602 : EJMOriginalGlobalDAGData.nodes 9 ⟨270602, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨270563, by decide⟩,⟨270593, by decide⟩,⟨270601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24681_270602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24681 ⟨270602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24681
    ⟨270602, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨270563, by decide⟩,⟨270593, by decide⟩,⟨270601, by decide⟩]) unmarked_context_12_24681_270602 node_context_12_24681_270602
  intro a
  fin_cases a
  · exact context_13_98724_3444
  · exact context_13_98725_270563
  · exact context_13_98726_270593
  · exact context_13_98727_270601

theorem selected_cut_09826 : selected 9 ⟨270642, by decide⟩
    (prefixPartial 12 24682) = some ⟨12, 2, 0, 270642, 24682, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_24682_270642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24682 ⟨270642, by decide⟩ :=
  accepted_of_selected 12 24682 ⟨270642, by decide⟩ ⟨12, 2, 0, 270642, 24682, 3429, 65536⟩
    (by decide) selected_cut_09826

theorem selected_cut_09827 : selected 9 ⟨270679, by decide⟩
    (prefixPartial 12 24683) = some ⟨12, 2, 0, 270679, 24683, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_24683_270679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24683 ⟨270679, by decide⟩ :=
  accepted_of_selected 12 24683 ⟨270679, by decide⟩ ⟨12, 2, 0, 270679, 24683, 3821, 65536⟩
    (by decide) selected_cut_09827

theorem unmarked_context_11_6170_270680 : frontier 10 ⟨270680, by decide⟩
    (prefixCache 11 6170) (prefixPartial 11 6170) = false := by
  decide +kernel

theorem node_context_11_6170_270680 : EJMOriginalGlobalDAGData.nodes 10 ⟨270680, by decide⟩ =
    .split (coordinate 11) (![⟨270549, by decide⟩,⟨270602, by decide⟩,⟨270642, by decide⟩,⟨270679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6170_270680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6170 ⟨270680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6170
    ⟨270680, by decide⟩ (by decide) (![⟨270549, by decide⟩,⟨270602, by decide⟩,⟨270642, by decide⟩,⟨270679, by decide⟩]) unmarked_context_11_6170_270680 node_context_11_6170_270680
  intro a
  fin_cases a
  · exact context_12_24680_270549
  · exact context_12_24681_270602
  · exact context_12_24682_270642
  · exact context_12_24683_270679

theorem selected_cut_09828 : selected 9 ⟨270713, by decide⟩
    (prefixPartial 12 24684) = some ⟨12, 2, 0, 270713, 24684, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_24684_270713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24684 ⟨270713, by decide⟩ :=
  accepted_of_selected 12 24684 ⟨270713, by decide⟩ ⟨12, 2, 0, 270713, 24684, 3053, 65536⟩
    (by decide) selected_cut_09828

theorem selected_cut_09829 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98740) = some ⟨13, 1, 0, 3444, 98740, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98740_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98740 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98740 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98740, 1, 16384⟩
    (by decide) selected_cut_09829

theorem selected_cut_09830 : selected 8 ⟨270723, by decide⟩
    (prefixPartial 13 98741) = some ⟨13, 2, 0, 270723, 98741, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_98741_270723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98741 ⟨270723, by decide⟩ :=
  accepted_of_selected 13 98741 ⟨270723, by decide⟩ ⟨13, 2, 0, 270723, 98741, 1073, 16384⟩
    (by decide) selected_cut_09830

theorem selected_cut_09831 : selected 8 ⟨270747, by decide⟩
    (prefixPartial 13 98742) = some ⟨13, 2, 0, 270747, 98742, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_98742_270747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98742 ⟨270747, by decide⟩ :=
  accepted_of_selected 13 98742 ⟨270747, by decide⟩ ⟨13, 2, 0, 270747, 98742, 2425, 16384⟩
    (by decide) selected_cut_09831

theorem selected_cut_09832 : selected 8 ⟨270753, by decide⟩
    (prefixPartial 13 98743) = some ⟨13, 2, 0, 270753, 98743, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_98743_270753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98743 ⟨270753, by decide⟩ :=
  accepted_of_selected 13 98743 ⟨270753, by decide⟩ ⟨13, 2, 0, 270753, 98743, 1169, 16384⟩
    (by decide) selected_cut_09832

theorem unmarked_context_12_24685_270754 : frontier 9 ⟨270754, by decide⟩
    (prefixCache 12 24685) (prefixPartial 12 24685) = false := by
  decide +kernel

theorem node_context_12_24685_270754 : EJMOriginalGlobalDAGData.nodes 9 ⟨270754, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨270723, by decide⟩,⟨270747, by decide⟩,⟨270753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24685_270754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24685 ⟨270754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24685
    ⟨270754, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨270723, by decide⟩,⟨270747, by decide⟩,⟨270753, by decide⟩]) unmarked_context_12_24685_270754 node_context_12_24685_270754
  intro a
  fin_cases a
  · exact context_13_98740_3444
  · exact context_13_98741_270723
  · exact context_13_98742_270747
  · exact context_13_98743_270753

theorem selected_cut_09833 : selected 9 ⟨270794, by decide⟩
    (prefixPartial 12 24686) = some ⟨12, 2, 0, 270794, 24686, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_24686_270794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24686 ⟨270794, by decide⟩ :=
  accepted_of_selected 12 24686 ⟨270794, by decide⟩ ⟨12, 2, 0, 270794, 24686, 3665, 65536⟩
    (by decide) selected_cut_09833

theorem selected_cut_09834 : selected 9 ⟨270827, by decide⟩
    (prefixPartial 12 24687) = some ⟨12, 2, 0, 270827, 24687, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_24687_270827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24687 ⟨270827, by decide⟩ :=
  accepted_of_selected 12 24687 ⟨270827, by decide⟩ ⟨12, 2, 0, 270827, 24687, 3717, 65536⟩
    (by decide) selected_cut_09834

theorem unmarked_context_11_6171_270828 : frontier 10 ⟨270828, by decide⟩
    (prefixCache 11 6171) (prefixPartial 11 6171) = false := by
  decide +kernel

theorem node_context_11_6171_270828 : EJMOriginalGlobalDAGData.nodes 10 ⟨270828, by decide⟩ =
    .split (coordinate 11) (![⟨270713, by decide⟩,⟨270754, by decide⟩,⟨270794, by decide⟩,⟨270827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6171_270828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6171 ⟨270828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6171
    ⟨270828, by decide⟩ (by decide) (![⟨270713, by decide⟩,⟨270754, by decide⟩,⟨270794, by decide⟩,⟨270827, by decide⟩]) unmarked_context_11_6171_270828 node_context_11_6171_270828
  intro a
  fin_cases a
  · exact context_12_24684_270713
  · exact context_12_24685_270754
  · exact context_12_24686_270794
  · exact context_12_24687_270827

theorem unmarked_context_10_1542_270829 : frontier 11 ⟨270829, by decide⟩
    (prefixCache 10 1542) (prefixPartial 10 1542) = false := by
  decide +kernel

theorem node_context_10_1542_270829 : EJMOriginalGlobalDAGData.nodes 11 ⟨270829, by decide⟩ =
    .split (coordinate 10) (![⟨270328, by decide⟩,⟨270513, by decide⟩,⟨270680, by decide⟩,⟨270828, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1542_270829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1542 ⟨270829, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1542
    ⟨270829, by decide⟩ (by decide) (![⟨270328, by decide⟩,⟨270513, by decide⟩,⟨270680, by decide⟩,⟨270828, by decide⟩]) unmarked_context_10_1542_270829 node_context_10_1542_270829
  intro a
  fin_cases a
  · exact context_11_6168_270328
  · exact context_11_6169_270513
  · exact context_11_6170_270680
  · exact context_11_6171_270828

theorem selected_cut_09835 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98752) = some ⟨13, 1, 0, 3444, 98752, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98752_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98752 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98752 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98752, 1, 16384⟩
    (by decide) selected_cut_09835

theorem selected_cut_09836 : selected 8 ⟨270842, by decide⟩
    (prefixPartial 13 98753) = some ⟨13, 2, 0, 270842, 98753, 961, 16384⟩ := by
  decide +kernel

theorem context_13_98753_270842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98753 ⟨270842, by decide⟩ :=
  accepted_of_selected 13 98753 ⟨270842, by decide⟩ ⟨13, 2, 0, 270842, 98753, 961, 16384⟩
    (by decide) selected_cut_09836

theorem selected_cut_09837 : selected 8 ⟨270874, by decide⟩
    (prefixPartial 13 98754) = some ⟨13, 2, 0, 270874, 98754, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_98754_270874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98754 ⟨270874, by decide⟩ :=
  accepted_of_selected 13 98754 ⟨270874, by decide⟩ ⟨13, 2, 0, 270874, 98754, 2421, 16384⟩
    (by decide) selected_cut_09837

theorem selected_cut_09838 : selected 8 ⟨270885, by decide⟩
    (prefixPartial 13 98755) = some ⟨13, 2, 0, 270885, 98755, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_98755_270885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98755 ⟨270885, by decide⟩ :=
  accepted_of_selected 13 98755 ⟨270885, by decide⟩ ⟨13, 2, 0, 270885, 98755, 1037, 16384⟩
    (by decide) selected_cut_09838

theorem unmarked_context_12_24688_270886 : frontier 9 ⟨270886, by decide⟩
    (prefixCache 12 24688) (prefixPartial 12 24688) = false := by
  decide +kernel

theorem node_context_12_24688_270886 : EJMOriginalGlobalDAGData.nodes 9 ⟨270886, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨270842, by decide⟩,⟨270874, by decide⟩,⟨270885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24688_270886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24688 ⟨270886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24688
    ⟨270886, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨270842, by decide⟩,⟨270874, by decide⟩,⟨270885, by decide⟩]) unmarked_context_12_24688_270886 node_context_12_24688_270886
  intro a
  fin_cases a
  · exact context_13_98752_3444
  · exact context_13_98753_270842
  · exact context_13_98754_270874
  · exact context_13_98755_270885

theorem selected_cut_09839 : selected 9 ⟨270928, by decide⟩
    (prefixPartial 12 24689) = some ⟨12, 2, 0, 270928, 24689, 3997, 65536⟩ := by
  decide +kernel

theorem context_12_24689_270928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24689 ⟨270928, by decide⟩ :=
  accepted_of_selected 12 24689 ⟨270928, by decide⟩ ⟨12, 2, 0, 270928, 24689, 3997, 65536⟩
    (by decide) selected_cut_09839

theorem selected_cut_09840 : selected 9 ⟨270962, by decide⟩
    (prefixPartial 12 24690) = some ⟨12, 2, 0, 270962, 24690, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_24690_270962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24690 ⟨270962, by decide⟩ :=
  accepted_of_selected 12 24690 ⟨270962, by decide⟩ ⟨12, 2, 0, 270962, 24690, 2757, 65536⟩
    (by decide) selected_cut_09840

theorem selected_cut_09841 : selected 9 ⟨271000, by decide⟩
    (prefixPartial 12 24691) = some ⟨12, 2, 0, 271000, 24691, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_24691_271000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24691 ⟨271000, by decide⟩ :=
  accepted_of_selected 12 24691 ⟨271000, by decide⟩ ⟨12, 2, 0, 271000, 24691, 3461, 65536⟩
    (by decide) selected_cut_09841

theorem unmarked_context_11_6172_271001 : frontier 10 ⟨271001, by decide⟩
    (prefixCache 11 6172) (prefixPartial 11 6172) = false := by
  decide +kernel

theorem node_context_11_6172_271001 : EJMOriginalGlobalDAGData.nodes 10 ⟨271001, by decide⟩ =
    .split (coordinate 11) (![⟨270886, by decide⟩,⟨270928, by decide⟩,⟨270962, by decide⟩,⟨271000, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6172_271001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6172 ⟨271001, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6172
    ⟨271001, by decide⟩ (by decide) (![⟨270886, by decide⟩,⟨270928, by decide⟩,⟨270962, by decide⟩,⟨271000, by decide⟩]) unmarked_context_11_6172_271001 node_context_11_6172_271001
  intro a
  fin_cases a
  · exact context_12_24688_270886
  · exact context_12_24689_270928
  · exact context_12_24690_270962
  · exact context_12_24691_271000

theorem selected_cut_09842 : selected 9 ⟨271036, by decide⟩
    (prefixPartial 12 24692) = some ⟨12, 2, 0, 271036, 24692, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_24692_271036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24692 ⟨271036, by decide⟩ :=
  accepted_of_selected 12 24692 ⟨271036, by decide⟩ ⟨12, 2, 0, 271036, 24692, 2685, 65536⟩
    (by decide) selected_cut_09842

theorem selected_cut_09843 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98772) = some ⟨13, 1, 0, 3444, 98772, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98772_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98772 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98772 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98772, 1, 16384⟩
    (by decide) selected_cut_09843

theorem selected_cut_09844 : selected 8 ⟨271041, by decide⟩
    (prefixPartial 13 98773) = some ⟨13, 2, 0, 271041, 98773, 585, 16384⟩ := by
  decide +kernel

theorem context_13_98773_271041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98773 ⟨271041, by decide⟩ :=
  accepted_of_selected 13 98773 ⟨271041, by decide⟩ ⟨13, 2, 0, 271041, 98773, 585, 16384⟩
    (by decide) selected_cut_09844

theorem selected_cut_09845 : selected 8 ⟨271079, by decide⟩
    (prefixPartial 13 98774) = some ⟨13, 2, 0, 271079, 98774, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_98774_271079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98774 ⟨271079, by decide⟩ :=
  accepted_of_selected 13 98774 ⟨271079, by decide⟩ ⟨13, 2, 0, 271079, 98774, 2605, 16384⟩
    (by decide) selected_cut_09845

theorem selected_cut_09846 : selected 8 ⟨271087, by decide⟩
    (prefixPartial 13 98775) = some ⟨13, 2, 0, 271087, 98775, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_98775_271087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98775 ⟨271087, by decide⟩ :=
  accepted_of_selected 13 98775 ⟨271087, by decide⟩ ⟨13, 2, 0, 271087, 98775, 1205, 16384⟩
    (by decide) selected_cut_09846

theorem unmarked_context_12_24693_271088 : frontier 9 ⟨271088, by decide⟩
    (prefixCache 12 24693) (prefixPartial 12 24693) = false := by
  decide +kernel

theorem node_context_12_24693_271088 : EJMOriginalGlobalDAGData.nodes 9 ⟨271088, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨271041, by decide⟩,⟨271079, by decide⟩,⟨271087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24693_271088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24693 ⟨271088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24693
    ⟨271088, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨271041, by decide⟩,⟨271079, by decide⟩,⟨271087, by decide⟩]) unmarked_context_12_24693_271088 node_context_12_24693_271088
  intro a
  fin_cases a
  · exact context_13_98772_3444
  · exact context_13_98773_271041
  · exact context_13_98774_271079
  · exact context_13_98775_271087

theorem selected_cut_09847 : selected 9 ⟨271126, by decide⟩
    (prefixPartial 12 24694) = some ⟨12, 2, 0, 271126, 24694, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_24694_271126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24694 ⟨271126, by decide⟩ :=
  accepted_of_selected 12 24694 ⟨271126, by decide⟩ ⟨12, 2, 0, 271126, 24694, 3189, 65536⟩
    (by decide) selected_cut_09847

theorem selected_cut_09848 : selected 9 ⟨271172, by decide⟩
    (prefixPartial 12 24695) = some ⟨12, 2, 0, 271172, 24695, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_24695_271172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24695 ⟨271172, by decide⟩ :=
  accepted_of_selected 12 24695 ⟨271172, by decide⟩ ⟨12, 2, 0, 271172, 24695, 3917, 65536⟩
    (by decide) selected_cut_09848

theorem unmarked_context_11_6173_271173 : frontier 10 ⟨271173, by decide⟩
    (prefixCache 11 6173) (prefixPartial 11 6173) = false := by
  decide +kernel

theorem node_context_11_6173_271173 : EJMOriginalGlobalDAGData.nodes 10 ⟨271173, by decide⟩ =
    .split (coordinate 11) (![⟨271036, by decide⟩,⟨271088, by decide⟩,⟨271126, by decide⟩,⟨271172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6173_271173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6173 ⟨271173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6173
    ⟨271173, by decide⟩ (by decide) (![⟨271036, by decide⟩,⟨271088, by decide⟩,⟨271126, by decide⟩,⟨271172, by decide⟩]) unmarked_context_11_6173_271173 node_context_11_6173_271173
  intro a
  fin_cases a
  · exact context_12_24692_271036
  · exact context_12_24693_271088
  · exact context_12_24694_271126
  · exact context_12_24695_271172

theorem selected_cut_09849 : selected 9 ⟨271207, by decide⟩
    (prefixPartial 12 24696) = some ⟨12, 2, 0, 271207, 24696, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_24696_271207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24696 ⟨271207, by decide⟩ :=
  accepted_of_selected 12 24696 ⟨271207, by decide⟩ ⟨12, 2, 0, 271207, 24696, 3141, 65536⟩
    (by decide) selected_cut_09849

theorem selected_cut_09850 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98788) = some ⟨13, 1, 0, 3444, 98788, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98788_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98788 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98788 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98788, 1, 16384⟩
    (by decide) selected_cut_09850

theorem selected_cut_09851 : selected 8 ⟨271213, by decide⟩
    (prefixPartial 13 98789) = some ⟨13, 2, 0, 271213, 98789, 405, 16384⟩ := by
  decide +kernel

theorem context_13_98789_271213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98789 ⟨271213, by decide⟩ :=
  accepted_of_selected 13 98789 ⟨271213, by decide⟩ ⟨13, 2, 0, 271213, 98789, 405, 16384⟩
    (by decide) selected_cut_09851

theorem selected_cut_09852 : selected 8 ⟨271245, by decide⟩
    (prefixPartial 13 98790) = some ⟨13, 2, 0, 271245, 98790, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_98790_271245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98790 ⟨271245, by decide⟩ :=
  accepted_of_selected 13 98790 ⟨271245, by decide⟩ ⟨13, 2, 0, 271245, 98790, 2589, 16384⟩
    (by decide) selected_cut_09852

theorem selected_cut_09853 : selected 8 ⟨271253, by decide⟩
    (prefixPartial 13 98791) = some ⟨13, 2, 0, 271253, 98791, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_98791_271253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98791 ⟨271253, by decide⟩ :=
  accepted_of_selected 13 98791 ⟨271253, by decide⟩ ⟨13, 2, 0, 271253, 98791, 1137, 16384⟩
    (by decide) selected_cut_09853

theorem unmarked_context_12_24697_271254 : frontier 9 ⟨271254, by decide⟩
    (prefixCache 12 24697) (prefixPartial 12 24697) = false := by
  decide +kernel

theorem node_context_12_24697_271254 : EJMOriginalGlobalDAGData.nodes 9 ⟨271254, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨271213, by decide⟩,⟨271245, by decide⟩,⟨271253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24697_271254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24697 ⟨271254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24697
    ⟨271254, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨271213, by decide⟩,⟨271245, by decide⟩,⟨271253, by decide⟩]) unmarked_context_12_24697_271254 node_context_12_24697_271254
  intro a
  fin_cases a
  · exact context_13_98788_3444
  · exact context_13_98789_271213
  · exact context_13_98790_271245
  · exact context_13_98791_271253

theorem selected_cut_09854 : selected 9 ⟨271289, by decide⟩
    (prefixPartial 12 24698) = some ⟨12, 2, 0, 271289, 24698, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_24698_271289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24698 ⟨271289, by decide⟩ :=
  accepted_of_selected 12 24698 ⟨271289, by decide⟩ ⟨12, 2, 0, 271289, 24698, 2945, 65536⟩
    (by decide) selected_cut_09854

theorem selected_cut_09855 : selected 9 ⟨271322, by decide⟩
    (prefixPartial 12 24699) = some ⟨12, 2, 0, 271322, 24699, 3725, 65536⟩ := by
  decide +kernel

theorem context_12_24699_271322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24699 ⟨271322, by decide⟩ :=
  accepted_of_selected 12 24699 ⟨271322, by decide⟩ ⟨12, 2, 0, 271322, 24699, 3725, 65536⟩
    (by decide) selected_cut_09855

theorem unmarked_context_11_6174_271323 : frontier 10 ⟨271323, by decide⟩
    (prefixCache 11 6174) (prefixPartial 11 6174) = false := by
  decide +kernel

theorem node_context_11_6174_271323 : EJMOriginalGlobalDAGData.nodes 10 ⟨271323, by decide⟩ =
    .split (coordinate 11) (![⟨271207, by decide⟩,⟨271254, by decide⟩,⟨271289, by decide⟩,⟨271322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6174_271323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6174 ⟨271323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6174
    ⟨271323, by decide⟩ (by decide) (![⟨271207, by decide⟩,⟨271254, by decide⟩,⟨271289, by decide⟩,⟨271322, by decide⟩]) unmarked_context_11_6174_271323 node_context_11_6174_271323
  intro a
  fin_cases a
  · exact context_12_24696_271207
  · exact context_12_24697_271254
  · exact context_12_24698_271289
  · exact context_12_24699_271322

theorem selected_cut_09856 : selected 9 ⟨271355, by decide⟩
    (prefixPartial 12 24700) = some ⟨12, 2, 0, 271355, 24700, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_24700_271355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24700 ⟨271355, by decide⟩ :=
  accepted_of_selected 12 24700 ⟨271355, by decide⟩ ⟨12, 2, 0, 271355, 24700, 2525, 65536⟩
    (by decide) selected_cut_09856

theorem selected_cut_09857 : selected 9 ⟨271398, by decide⟩
    (prefixPartial 12 24701) = some ⟨12, 2, 0, 271398, 24701, 3873, 65536⟩ := by
  decide +kernel

theorem context_12_24701_271398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24701 ⟨271398, by decide⟩ :=
  accepted_of_selected 12 24701 ⟨271398, by decide⟩ ⟨12, 2, 0, 271398, 24701, 3873, 65536⟩
    (by decide) selected_cut_09857

theorem selected_cut_09858 : selected 9 ⟨271430, by decide⟩
    (prefixPartial 12 24702) = some ⟨12, 2, 0, 271430, 24702, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_24702_271430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24702 ⟨271430, by decide⟩ :=
  accepted_of_selected 12 24702 ⟨271430, by decide⟩ ⟨12, 2, 0, 271430, 24702, 2741, 65536⟩
    (by decide) selected_cut_09858

theorem selected_cut_09859 : selected 9 ⟨271472, by decide⟩
    (prefixPartial 12 24703) = some ⟨12, 2, 0, 271472, 24703, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_24703_271472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24703 ⟨271472, by decide⟩ :=
  accepted_of_selected 12 24703 ⟨271472, by decide⟩ ⟨12, 2, 0, 271472, 24703, 3313, 65536⟩
    (by decide) selected_cut_09859

theorem unmarked_context_11_6175_271473 : frontier 10 ⟨271473, by decide⟩
    (prefixCache 11 6175) (prefixPartial 11 6175) = false := by
  decide +kernel

theorem node_context_11_6175_271473 : EJMOriginalGlobalDAGData.nodes 10 ⟨271473, by decide⟩ =
    .split (coordinate 11) (![⟨271355, by decide⟩,⟨271398, by decide⟩,⟨271430, by decide⟩,⟨271472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6175_271473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6175 ⟨271473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6175
    ⟨271473, by decide⟩ (by decide) (![⟨271355, by decide⟩,⟨271398, by decide⟩,⟨271430, by decide⟩,⟨271472, by decide⟩]) unmarked_context_11_6175_271473 node_context_11_6175_271473
  intro a
  fin_cases a
  · exact context_12_24700_271355
  · exact context_12_24701_271398
  · exact context_12_24702_271430
  · exact context_12_24703_271472

theorem unmarked_context_10_1543_271474 : frontier 11 ⟨271474, by decide⟩
    (prefixCache 10 1543) (prefixPartial 10 1543) = false := by
  decide +kernel

theorem node_context_10_1543_271474 : EJMOriginalGlobalDAGData.nodes 11 ⟨271474, by decide⟩ =
    .split (coordinate 10) (![⟨271001, by decide⟩,⟨271173, by decide⟩,⟨271323, by decide⟩,⟨271473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1543_271474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1543 ⟨271474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1543
    ⟨271474, by decide⟩ (by decide) (![⟨271001, by decide⟩,⟨271173, by decide⟩,⟨271323, by decide⟩,⟨271473, by decide⟩]) unmarked_context_10_1543_271474 node_context_10_1543_271474
  intro a
  fin_cases a
  · exact context_11_6172_271001
  · exact context_11_6173_271173
  · exact context_11_6174_271323
  · exact context_11_6175_271473

theorem unmarked_context_9_385_271475 : frontier 12 ⟨271475, by decide⟩
    (prefixCache 9 385) (prefixPartial 9 385) = false := by
  decide +kernel

theorem node_context_9_385_271475 : EJMOriginalGlobalDAGData.nodes 12 ⟨271475, by decide⟩ =
    .split (coordinate 9) (![⟨269447, by decide⟩,⟨270157, by decide⟩,⟨270829, by decide⟩,⟨271474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_385_271475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 385 ⟨271475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 385
    ⟨271475, by decide⟩ (by decide) (![⟨269447, by decide⟩,⟨270157, by decide⟩,⟨270829, by decide⟩,⟨271474, by decide⟩]) unmarked_context_9_385_271475 node_context_9_385_271475
  intro a
  fin_cases a
  · exact context_10_1540_269447
  · exact context_10_1541_270157
  · exact context_10_1542_270829
  · exact context_10_1543_271474

theorem selected_cut_09860 : selected 9 ⟨169790, by decide⟩
    (prefixPartial 12 24704) = some ⟨12, 1, 0, 169790, 24704, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24704_169790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24704 ⟨169790, by decide⟩ :=
  accepted_of_selected 12 24704 ⟨169790, by decide⟩ ⟨12, 1, 0, 169790, 24704, 1, 65536⟩
    (by decide) selected_cut_09860

theorem selected_cut_09861 : selected 9 ⟨271509, by decide⟩
    (prefixPartial 12 24705) = some ⟨12, 2, 0, 271509, 24705, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_24705_271509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24705 ⟨271509, by decide⟩ :=
  accepted_of_selected 12 24705 ⟨271509, by decide⟩ ⟨12, 2, 0, 271509, 24705, 2897, 65536⟩
    (by decide) selected_cut_09861

theorem selected_cut_09862 : selected 9 ⟨271540, by decide⟩
    (prefixPartial 12 24706) = some ⟨12, 2, 0, 271540, 24706, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_24706_271540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24706 ⟨271540, by decide⟩ :=
  accepted_of_selected 12 24706 ⟨271540, by decide⟩ ⟨12, 2, 0, 271540, 24706, 2781, 65536⟩
    (by decide) selected_cut_09862

theorem selected_cut_09863 : selected 9 ⟨271574, by decide⟩
    (prefixPartial 12 24707) = some ⟨12, 2, 0, 271574, 24707, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_24707_271574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24707 ⟨271574, by decide⟩ :=
  accepted_of_selected 12 24707 ⟨271574, by decide⟩ ⟨12, 2, 0, 271574, 24707, 2873, 65536⟩
    (by decide) selected_cut_09863

theorem unmarked_context_11_6176_271575 : frontier 10 ⟨271575, by decide⟩
    (prefixCache 11 6176) (prefixPartial 11 6176) = false := by
  decide +kernel

theorem node_context_11_6176_271575 : EJMOriginalGlobalDAGData.nodes 10 ⟨271575, by decide⟩ =
    .split (coordinate 11) (![⟨169790, by decide⟩,⟨271509, by decide⟩,⟨271540, by decide⟩,⟨271574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6176_271575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6176 ⟨271575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6176
    ⟨271575, by decide⟩ (by decide) (![⟨169790, by decide⟩,⟨271509, by decide⟩,⟨271540, by decide⟩,⟨271574, by decide⟩]) unmarked_context_11_6176_271575 node_context_11_6176_271575
  intro a
  fin_cases a
  · exact context_12_24704_169790
  · exact context_12_24705_271509
  · exact context_12_24706_271540
  · exact context_12_24707_271574

theorem selected_cut_09864 : selected 9 ⟨271598, by decide⟩
    (prefixPartial 12 24708) = some ⟨12, 2, 0, 271598, 24708, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_24708_271598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24708 ⟨271598, by decide⟩ :=
  accepted_of_selected 12 24708 ⟨271598, by decide⟩ ⟨12, 2, 0, 271598, 24708, 1637, 65536⟩
    (by decide) selected_cut_09864

theorem selected_cut_09865 : selected 9 ⟨271627, by decide⟩
    (prefixPartial 12 24709) = some ⟨12, 2, 0, 271627, 24709, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_24709_271627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24709 ⟨271627, by decide⟩ :=
  accepted_of_selected 12 24709 ⟨271627, by decide⟩ ⟨12, 2, 0, 271627, 24709, 2109, 65536⟩
    (by decide) selected_cut_09865

theorem selected_cut_09866 : selected 9 ⟨271656, by decide⟩
    (prefixPartial 12 24710) = some ⟨12, 2, 0, 271656, 24710, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_24710_271656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24710 ⟨271656, by decide⟩ :=
  accepted_of_selected 12 24710 ⟨271656, by decide⟩ ⟨12, 2, 0, 271656, 24710, 2109, 65536⟩
    (by decide) selected_cut_09866

theorem selected_cut_09867 : selected 9 ⟨271688, by decide⟩
    (prefixPartial 12 24711) = some ⟨12, 2, 0, 271688, 24711, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_24711_271688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24711 ⟨271688, by decide⟩ :=
  accepted_of_selected 12 24711 ⟨271688, by decide⟩ ⟨12, 2, 0, 271688, 24711, 2325, 65536⟩
    (by decide) selected_cut_09867

theorem unmarked_context_11_6177_271689 : frontier 10 ⟨271689, by decide⟩
    (prefixCache 11 6177) (prefixPartial 11 6177) = false := by
  decide +kernel

theorem node_context_11_6177_271689 : EJMOriginalGlobalDAGData.nodes 10 ⟨271689, by decide⟩ =
    .split (coordinate 11) (![⟨271598, by decide⟩,⟨271627, by decide⟩,⟨271656, by decide⟩,⟨271688, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6177_271689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6177 ⟨271689, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6177
    ⟨271689, by decide⟩ (by decide) (![⟨271598, by decide⟩,⟨271627, by decide⟩,⟨271656, by decide⟩,⟨271688, by decide⟩]) unmarked_context_11_6177_271689 node_context_11_6177_271689
  intro a
  fin_cases a
  · exact context_12_24708_271598
  · exact context_12_24709_271627
  · exact context_12_24710_271656
  · exact context_12_24711_271688

theorem selected_cut_09868 : selected 9 ⟨271713, by decide⟩
    (prefixPartial 12 24712) = some ⟨12, 2, 0, 271713, 24712, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_24712_271713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24712 ⟨271713, by decide⟩ :=
  accepted_of_selected 12 24712 ⟨271713, by decide⟩ ⟨12, 2, 0, 271713, 24712, 1917, 65536⟩
    (by decide) selected_cut_09868

theorem selected_cut_09869 : selected 9 ⟨271742, by decide⟩
    (prefixPartial 12 24713) = some ⟨12, 2, 0, 271742, 24713, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_24713_271742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24713 ⟨271742, by decide⟩ :=
  accepted_of_selected 12 24713 ⟨271742, by decide⟩ ⟨12, 2, 0, 271742, 24713, 2217, 65536⟩
    (by decide) selected_cut_09869

theorem selected_cut_09870 : selected 9 ⟨271771, by decide⟩
    (prefixPartial 12 24714) = some ⟨12, 2, 0, 271771, 24714, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_24714_271771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24714 ⟨271771, by decide⟩ :=
  accepted_of_selected 12 24714 ⟨271771, by decide⟩ ⟨12, 2, 0, 271771, 24714, 2105, 65536⟩
    (by decide) selected_cut_09870

theorem selected_cut_09871 : selected 9 ⟨271800, by decide⟩
    (prefixPartial 12 24715) = some ⟨12, 2, 0, 271800, 24715, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_24715_271800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24715 ⟨271800, by decide⟩ :=
  accepted_of_selected 12 24715 ⟨271800, by decide⟩ ⟨12, 2, 0, 271800, 24715, 2433, 65536⟩
    (by decide) selected_cut_09871

theorem unmarked_context_11_6178_271801 : frontier 10 ⟨271801, by decide⟩
    (prefixCache 11 6178) (prefixPartial 11 6178) = false := by
  decide +kernel

theorem node_context_11_6178_271801 : EJMOriginalGlobalDAGData.nodes 10 ⟨271801, by decide⟩ =
    .split (coordinate 11) (![⟨271713, by decide⟩,⟨271742, by decide⟩,⟨271771, by decide⟩,⟨271800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6178_271801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6178 ⟨271801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6178
    ⟨271801, by decide⟩ (by decide) (![⟨271713, by decide⟩,⟨271742, by decide⟩,⟨271771, by decide⟩,⟨271800, by decide⟩]) unmarked_context_11_6178_271801 node_context_11_6178_271801
  intro a
  fin_cases a
  · exact context_12_24712_271713
  · exact context_12_24713_271742
  · exact context_12_24714_271771
  · exact context_12_24715_271800

theorem selected_cut_09872 : selected 9 ⟨271822, by decide⟩
    (prefixPartial 12 24716) = some ⟨12, 2, 0, 271822, 24716, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_24716_271822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24716 ⟨271822, by decide⟩ :=
  accepted_of_selected 12 24716 ⟨271822, by decide⟩ ⟨12, 2, 0, 271822, 24716, 1541, 65536⟩
    (by decide) selected_cut_09872

theorem selected_cut_09873 : selected 9 ⟨271850, by decide⟩
    (prefixPartial 12 24717) = some ⟨12, 2, 0, 271850, 24717, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_24717_271850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24717 ⟨271850, by decide⟩ :=
  accepted_of_selected 12 24717 ⟨271850, by decide⟩ ⟨12, 2, 0, 271850, 24717, 1829, 65536⟩
    (by decide) selected_cut_09873

theorem selected_cut_09874 : selected 9 ⟨271878, by decide⟩
    (prefixPartial 12 24718) = some ⟨12, 2, 0, 271878, 24718, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_24718_271878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24718 ⟨271878, by decide⟩ :=
  accepted_of_selected 12 24718 ⟨271878, by decide⟩ ⟨12, 2, 0, 271878, 24718, 1845, 65536⟩
    (by decide) selected_cut_09874

theorem selected_cut_09875 : selected 9 ⟨271904, by decide⟩
    (prefixPartial 12 24719) = some ⟨12, 2, 0, 271904, 24719, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_24719_271904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24719 ⟨271904, by decide⟩ :=
  accepted_of_selected 12 24719 ⟨271904, by decide⟩ ⟨12, 2, 0, 271904, 24719, 2065, 65536⟩
    (by decide) selected_cut_09875

theorem unmarked_context_11_6179_271905 : frontier 10 ⟨271905, by decide⟩
    (prefixCache 11 6179) (prefixPartial 11 6179) = false := by
  decide +kernel

theorem node_context_11_6179_271905 : EJMOriginalGlobalDAGData.nodes 10 ⟨271905, by decide⟩ =
    .split (coordinate 11) (![⟨271822, by decide⟩,⟨271850, by decide⟩,⟨271878, by decide⟩,⟨271904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6179_271905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6179 ⟨271905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6179
    ⟨271905, by decide⟩ (by decide) (![⟨271822, by decide⟩,⟨271850, by decide⟩,⟨271878, by decide⟩,⟨271904, by decide⟩]) unmarked_context_11_6179_271905 node_context_11_6179_271905
  intro a
  fin_cases a
  · exact context_12_24716_271822
  · exact context_12_24717_271850
  · exact context_12_24718_271878
  · exact context_12_24719_271904

theorem unmarked_context_10_1544_271906 : frontier 11 ⟨271906, by decide⟩
    (prefixCache 10 1544) (prefixPartial 10 1544) = false := by
  decide +kernel

theorem node_context_10_1544_271906 : EJMOriginalGlobalDAGData.nodes 11 ⟨271906, by decide⟩ =
    .split (coordinate 10) (![⟨271575, by decide⟩,⟨271689, by decide⟩,⟨271801, by decide⟩,⟨271905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1544_271906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1544 ⟨271906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1544
    ⟨271906, by decide⟩ (by decide) (![⟨271575, by decide⟩,⟨271689, by decide⟩,⟨271801, by decide⟩,⟨271905, by decide⟩]) unmarked_context_10_1544_271906 node_context_10_1544_271906
  intro a
  fin_cases a
  · exact context_11_6176_271575
  · exact context_11_6177_271689
  · exact context_11_6178_271801
  · exact context_11_6179_271905

theorem selected_cut_09876 : selected 9 ⟨271934, by decide⟩
    (prefixPartial 12 24720) = some ⟨12, 2, 0, 271934, 24720, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_24720_271934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24720 ⟨271934, by decide⟩ :=
  accepted_of_selected 12 24720 ⟨271934, by decide⟩ ⟨12, 2, 0, 271934, 24720, 2849, 65536⟩
    (by decide) selected_cut_09876

theorem selected_cut_09877 : selected 9 ⟨271961, by decide⟩
    (prefixPartial 12 24721) = some ⟨12, 2, 0, 271961, 24721, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_24721_271961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24721 ⟨271961, by decide⟩ :=
  accepted_of_selected 12 24721 ⟨271961, by decide⟩ ⟨12, 2, 0, 271961, 24721, 2245, 65536⟩
    (by decide) selected_cut_09877

theorem selected_cut_09878 : selected 9 ⟨271987, by decide⟩
    (prefixPartial 12 24722) = some ⟨12, 2, 0, 271987, 24722, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_24722_271987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24722 ⟨271987, by decide⟩ :=
  accepted_of_selected 12 24722 ⟨271987, by decide⟩ ⟨12, 2, 0, 271987, 24722, 2121, 65536⟩
    (by decide) selected_cut_09878

theorem selected_cut_09879 : selected 9 ⟨272009, by decide⟩
    (prefixPartial 12 24723) = some ⟨12, 2, 0, 272009, 24723, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_24723_272009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24723 ⟨272009, by decide⟩ :=
  accepted_of_selected 12 24723 ⟨272009, by decide⟩ ⟨12, 2, 0, 272009, 24723, 2169, 65536⟩
    (by decide) selected_cut_09879

theorem unmarked_context_11_6180_272010 : frontier 10 ⟨272010, by decide⟩
    (prefixCache 11 6180) (prefixPartial 11 6180) = false := by
  decide +kernel

theorem node_context_11_6180_272010 : EJMOriginalGlobalDAGData.nodes 10 ⟨272010, by decide⟩ =
    .split (coordinate 11) (![⟨271934, by decide⟩,⟨271961, by decide⟩,⟨271987, by decide⟩,⟨272009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6180_272010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6180 ⟨272010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6180
    ⟨272010, by decide⟩ (by decide) (![⟨271934, by decide⟩,⟨271961, by decide⟩,⟨271987, by decide⟩,⟨272009, by decide⟩]) unmarked_context_11_6180_272010 node_context_11_6180_272010
  intro a
  fin_cases a
  · exact context_12_24720_271934
  · exact context_12_24721_271961
  · exact context_12_24722_271987
  · exact context_12_24723_272009

theorem selected_cut_09880 : selected 9 ⟨272031, by decide⟩
    (prefixPartial 12 24724) = some ⟨12, 2, 0, 272031, 24724, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_24724_272031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24724 ⟨272031, by decide⟩ :=
  accepted_of_selected 12 24724 ⟨272031, by decide⟩ ⟨12, 2, 0, 272031, 24724, 1885, 65536⟩
    (by decide) selected_cut_09880

theorem selected_cut_09881 : selected 9 ⟨272059, by decide⟩
    (prefixPartial 12 24725) = some ⟨12, 2, 0, 272059, 24725, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_24725_272059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24725 ⟨272059, by decide⟩ :=
  accepted_of_selected 12 24725 ⟨272059, by decide⟩ ⟨12, 2, 0, 272059, 24725, 2401, 65536⟩
    (by decide) selected_cut_09881

theorem selected_cut_09882 : selected 9 ⟨272079, by decide⟩
    (prefixPartial 12 24726) = some ⟨12, 2, 0, 272079, 24726, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_24726_272079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24726 ⟨272079, by decide⟩ :=
  accepted_of_selected 12 24726 ⟨272079, by decide⟩ ⟨12, 2, 0, 272079, 24726, 2245, 65536⟩
    (by decide) selected_cut_09882

theorem selected_cut_09883 : selected 9 ⟨272098, by decide⟩
    (prefixPartial 12 24727) = some ⟨12, 2, 0, 272098, 24727, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_24727_272098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24727 ⟨272098, by decide⟩ :=
  accepted_of_selected 12 24727 ⟨272098, by decide⟩ ⟨12, 2, 0, 272098, 24727, 2445, 65536⟩
    (by decide) selected_cut_09883

theorem unmarked_context_11_6181_272099 : frontier 10 ⟨272099, by decide⟩
    (prefixCache 11 6181) (prefixPartial 11 6181) = false := by
  decide +kernel

theorem node_context_11_6181_272099 : EJMOriginalGlobalDAGData.nodes 10 ⟨272099, by decide⟩ =
    .split (coordinate 11) (![⟨272031, by decide⟩,⟨272059, by decide⟩,⟨272079, by decide⟩,⟨272098, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6181_272099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6181 ⟨272099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6181
    ⟨272099, by decide⟩ (by decide) (![⟨272031, by decide⟩,⟨272059, by decide⟩,⟨272079, by decide⟩,⟨272098, by decide⟩]) unmarked_context_11_6181_272099 node_context_11_6181_272099
  intro a
  fin_cases a
  · exact context_12_24724_272031
  · exact context_12_24725_272059
  · exact context_12_24726_272079
  · exact context_12_24727_272098

theorem selected_cut_09884 : selected 9 ⟨272125, by decide⟩
    (prefixPartial 12 24728) = some ⟨12, 2, 0, 272125, 24728, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_24728_272125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24728 ⟨272125, by decide⟩ :=
  accepted_of_selected 12 24728 ⟨272125, by decide⟩ ⟨12, 2, 0, 272125, 24728, 2073, 65536⟩
    (by decide) selected_cut_09884

theorem selected_cut_09885 : selected 9 ⟨272153, by decide⟩
    (prefixPartial 12 24729) = some ⟨12, 2, 0, 272153, 24729, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_24729_272153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24729 ⟨272153, by decide⟩ :=
  accepted_of_selected 12 24729 ⟨272153, by decide⟩ ⟨12, 2, 0, 272153, 24729, 2365, 65536⟩
    (by decide) selected_cut_09885

theorem selected_cut_09886 : selected 9 ⟨272173, by decide⟩
    (prefixPartial 12 24730) = some ⟨12, 2, 0, 272173, 24730, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_24730_272173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24730 ⟨272173, by decide⟩ :=
  accepted_of_selected 12 24730 ⟨272173, by decide⟩ ⟨12, 2, 0, 272173, 24730, 2177, 65536⟩
    (by decide) selected_cut_09886

theorem selected_cut_09887 : selected 9 ⟨272195, by decide⟩
    (prefixPartial 12 24731) = some ⟨12, 2, 0, 272195, 24731, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_24731_272195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24731 ⟨272195, by decide⟩ :=
  accepted_of_selected 12 24731 ⟨272195, by decide⟩ ⟨12, 2, 0, 272195, 24731, 2357, 65536⟩
    (by decide) selected_cut_09887

theorem unmarked_context_11_6182_272196 : frontier 10 ⟨272196, by decide⟩
    (prefixCache 11 6182) (prefixPartial 11 6182) = false := by
  decide +kernel

theorem node_context_11_6182_272196 : EJMOriginalGlobalDAGData.nodes 10 ⟨272196, by decide⟩ =
    .split (coordinate 11) (![⟨272125, by decide⟩,⟨272153, by decide⟩,⟨272173, by decide⟩,⟨272195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6182_272196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6182 ⟨272196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6182
    ⟨272196, by decide⟩ (by decide) (![⟨272125, by decide⟩,⟨272153, by decide⟩,⟨272173, by decide⟩,⟨272195, by decide⟩]) unmarked_context_11_6182_272196 node_context_11_6182_272196
  intro a
  fin_cases a
  · exact context_12_24728_272125
  · exact context_12_24729_272153
  · exact context_12_24730_272173
  · exact context_12_24731_272195

theorem selected_cut_09888 : selected 9 ⟨272216, by decide⟩
    (prefixPartial 12 24732) = some ⟨12, 2, 0, 272216, 24732, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_24732_272216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24732 ⟨272216, by decide⟩ :=
  accepted_of_selected 12 24732 ⟨272216, by decide⟩ ⟨12, 2, 0, 272216, 24732, 1589, 65536⟩
    (by decide) selected_cut_09888

theorem selected_cut_09889 : selected 9 ⟨272240, by decide⟩
    (prefixPartial 12 24733) = some ⟨12, 2, 0, 272240, 24733, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_24733_272240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24733 ⟨272240, by decide⟩ :=
  accepted_of_selected 12 24733 ⟨272240, by decide⟩ ⟨12, 2, 0, 272240, 24733, 1921, 65536⟩
    (by decide) selected_cut_09889

theorem selected_cut_09890 : selected 9 ⟨272264, by decide⟩
    (prefixPartial 12 24734) = some ⟨12, 2, 0, 272264, 24734, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_24734_272264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24734 ⟨272264, by decide⟩ :=
  accepted_of_selected 12 24734 ⟨272264, by decide⟩ ⟨12, 2, 0, 272264, 24734, 1833, 65536⟩
    (by decide) selected_cut_09890

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
