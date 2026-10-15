/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover273
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_26307 : selected 9 ⟨665467, by decide⟩
    (prefixPartial 12 88707) = some ⟨12, 2, 0, 665467, 88707, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_88707_665467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88707 ⟨665467, by decide⟩ :=
  accepted_of_selected 12 88707 ⟨665467, by decide⟩ ⟨12, 2, 0, 665467, 88707, 1617, 65536⟩
    (by decide) selected_cut_26307

theorem unmarked_context_11_22176_665468 : frontier 10 ⟨665468, by decide⟩
    (prefixCache 11 22176) (prefixPartial 11 22176) = false := by
  decide +kernel

theorem node_context_11_22176_665468 : EJMOriginalGlobalDAGData.nodes 10 ⟨665468, by decide⟩ =
    .split (coordinate 11) (![⟨665402, by decide⟩,⟨665425, by decide⟩,⟨665447, by decide⟩,⟨665467, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22176_665468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22176 ⟨665468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22176
    ⟨665468, by decide⟩ (by decide) (![⟨665402, by decide⟩,⟨665425, by decide⟩,⟨665447, by decide⟩,⟨665467, by decide⟩]) unmarked_context_11_22176_665468 node_context_11_22176_665468
  intro a
  fin_cases a
  · exact context_12_88704_665402
  · exact context_12_88705_665425
  · exact context_12_88706_665447
  · exact context_12_88707_665467

theorem selected_cut_26308 : selected 9 ⟨665489, by decide⟩
    (prefixPartial 12 88708) = some ⟨12, 2, 0, 665489, 88708, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_88708_665489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88708 ⟨665489, by decide⟩ :=
  accepted_of_selected 12 88708 ⟨665489, by decide⟩ ⟨12, 2, 0, 665489, 88708, 1569, 65536⟩
    (by decide) selected_cut_26308

theorem selected_cut_26309 : selected 9 ⟨665508, by decide⟩
    (prefixPartial 12 88709) = some ⟨12, 2, 0, 665508, 88709, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_88709_665508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88709 ⟨665508, by decide⟩ :=
  accepted_of_selected 12 88709 ⟨665508, by decide⟩ ⟨12, 2, 0, 665508, 88709, 1421, 65536⟩
    (by decide) selected_cut_26309

theorem selected_cut_26310 : selected 9 ⟨665530, by decide⟩
    (prefixPartial 12 88710) = some ⟨12, 2, 0, 665530, 88710, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_88710_665530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88710 ⟨665530, by decide⟩ :=
  accepted_of_selected 12 88710 ⟨665530, by decide⟩ ⟨12, 2, 0, 665530, 88710, 1533, 65536⟩
    (by decide) selected_cut_26310

theorem selected_cut_26311 : selected 9 ⟨665549, by decide⟩
    (prefixPartial 12 88711) = some ⟨12, 2, 0, 665549, 88711, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_88711_665549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88711 ⟨665549, by decide⟩ :=
  accepted_of_selected 12 88711 ⟨665549, by decide⟩ ⟨12, 2, 0, 665549, 88711, 1513, 65536⟩
    (by decide) selected_cut_26311

theorem unmarked_context_11_22177_665550 : frontier 10 ⟨665550, by decide⟩
    (prefixCache 11 22177) (prefixPartial 11 22177) = false := by
  decide +kernel

theorem node_context_11_22177_665550 : EJMOriginalGlobalDAGData.nodes 10 ⟨665550, by decide⟩ =
    .split (coordinate 11) (![⟨665489, by decide⟩,⟨665508, by decide⟩,⟨665530, by decide⟩,⟨665549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22177_665550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22177 ⟨665550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22177
    ⟨665550, by decide⟩ (by decide) (![⟨665489, by decide⟩,⟨665508, by decide⟩,⟨665530, by decide⟩,⟨665549, by decide⟩]) unmarked_context_11_22177_665550 node_context_11_22177_665550
  intro a
  fin_cases a
  · exact context_12_88708_665489
  · exact context_12_88709_665508
  · exact context_12_88710_665530
  · exact context_12_88711_665549

theorem selected_cut_26312 : selected 9 ⟨665566, by decide⟩
    (prefixPartial 12 88712) = some ⟨12, 2, 0, 665566, 88712, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_88712_665566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88712 ⟨665566, by decide⟩ :=
  accepted_of_selected 12 88712 ⟨665566, by decide⟩ ⟨12, 2, 0, 665566, 88712, 1381, 65536⟩
    (by decide) selected_cut_26312

theorem selected_cut_26313 : selected 9 ⟨665585, by decide⟩
    (prefixPartial 12 88713) = some ⟨12, 2, 0, 665585, 88713, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_88713_665585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88713 ⟨665585, by decide⟩ :=
  accepted_of_selected 12 88713 ⟨665585, by decide⟩ ⟨12, 2, 0, 665585, 88713, 1441, 65536⟩
    (by decide) selected_cut_26313

theorem selected_cut_26314 : selected 9 ⟨663554, by decide⟩
    (prefixPartial 12 88714) = some ⟨12, 1, 0, 663554, 88714, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88714_663554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88714 ⟨663554, by decide⟩ :=
  accepted_of_selected 12 88714 ⟨663554, by decide⟩ ⟨12, 1, 0, 663554, 88714, 1, 65536⟩
    (by decide) selected_cut_26314

theorem selected_cut_26315 : selected 9 ⟨665601, by decide⟩
    (prefixPartial 12 88715) = some ⟨12, 2, 0, 665601, 88715, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_88715_665601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88715 ⟨665601, by decide⟩ :=
  accepted_of_selected 12 88715 ⟨665601, by decide⟩ ⟨12, 2, 0, 665601, 88715, 1397, 65536⟩
    (by decide) selected_cut_26315

theorem unmarked_context_11_22178_665602 : frontier 10 ⟨665602, by decide⟩
    (prefixCache 11 22178) (prefixPartial 11 22178) = false := by
  decide +kernel

theorem node_context_11_22178_665602 : EJMOriginalGlobalDAGData.nodes 10 ⟨665602, by decide⟩ =
    .split (coordinate 11) (![⟨665566, by decide⟩,⟨665585, by decide⟩,⟨663554, by decide⟩,⟨665601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22178_665602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22178 ⟨665602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22178
    ⟨665602, by decide⟩ (by decide) (![⟨665566, by decide⟩,⟨665585, by decide⟩,⟨663554, by decide⟩,⟨665601, by decide⟩]) unmarked_context_11_22178_665602 node_context_11_22178_665602
  intro a
  fin_cases a
  · exact context_12_88712_665566
  · exact context_12_88713_665585
  · exact context_12_88714_663554
  · exact context_12_88715_665601

theorem selected_cut_26316 : selected 9 ⟨665622, by decide⟩
    (prefixPartial 12 88716) = some ⟨12, 2, 0, 665622, 88716, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_88716_665622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88716 ⟨665622, by decide⟩ :=
  accepted_of_selected 12 88716 ⟨665622, by decide⟩ ⟨12, 2, 0, 665622, 88716, 1701, 65536⟩
    (by decide) selected_cut_26316

theorem selected_cut_26317 : selected 9 ⟨665638, by decide⟩
    (prefixPartial 12 88717) = some ⟨12, 2, 0, 665638, 88717, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_88717_665638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88717 ⟨665638, by decide⟩ :=
  accepted_of_selected 12 88717 ⟨665638, by decide⟩ ⟨12, 2, 0, 665638, 88717, 1693, 65536⟩
    (by decide) selected_cut_26317

theorem selected_cut_26318 : selected 9 ⟨665658, by decide⟩
    (prefixPartial 12 88718) = some ⟨12, 2, 0, 665658, 88718, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_88718_665658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88718 ⟨665658, by decide⟩ :=
  accepted_of_selected 12 88718 ⟨665658, by decide⟩ ⟨12, 2, 0, 665658, 88718, 1685, 65536⟩
    (by decide) selected_cut_26318

theorem selected_cut_26319 : selected 9 ⟨665674, by decide⟩
    (prefixPartial 12 88719) = some ⟨12, 2, 0, 665674, 88719, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_88719_665674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88719 ⟨665674, by decide⟩ :=
  accepted_of_selected 12 88719 ⟨665674, by decide⟩ ⟨12, 2, 0, 665674, 88719, 1733, 65536⟩
    (by decide) selected_cut_26319

theorem unmarked_context_11_22179_665675 : frontier 10 ⟨665675, by decide⟩
    (prefixCache 11 22179) (prefixPartial 11 22179) = false := by
  decide +kernel

theorem node_context_11_22179_665675 : EJMOriginalGlobalDAGData.nodes 10 ⟨665675, by decide⟩ =
    .split (coordinate 11) (![⟨665622, by decide⟩,⟨665638, by decide⟩,⟨665658, by decide⟩,⟨665674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22179_665675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22179 ⟨665675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22179
    ⟨665675, by decide⟩ (by decide) (![⟨665622, by decide⟩,⟨665638, by decide⟩,⟨665658, by decide⟩,⟨665674, by decide⟩]) unmarked_context_11_22179_665675 node_context_11_22179_665675
  intro a
  fin_cases a
  · exact context_12_88716_665622
  · exact context_12_88717_665638
  · exact context_12_88718_665658
  · exact context_12_88719_665674

theorem unmarked_context_10_5544_665676 : frontier 11 ⟨665676, by decide⟩
    (prefixCache 10 5544) (prefixPartial 10 5544) = false := by
  decide +kernel

theorem node_context_10_5544_665676 : EJMOriginalGlobalDAGData.nodes 11 ⟨665676, by decide⟩ =
    .split (coordinate 10) (![⟨665468, by decide⟩,⟨665550, by decide⟩,⟨665602, by decide⟩,⟨665675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5544_665676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5544 ⟨665676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5544
    ⟨665676, by decide⟩ (by decide) (![⟨665468, by decide⟩,⟨665550, by decide⟩,⟨665602, by decide⟩,⟨665675, by decide⟩]) unmarked_context_10_5544_665676 node_context_10_5544_665676
  intro a
  fin_cases a
  · exact context_11_22176_665468
  · exact context_11_22177_665550
  · exact context_11_22178_665602
  · exact context_11_22179_665675

theorem selected_cut_26320 : selected 9 ⟨665697, by decide⟩
    (prefixPartial 12 88720) = some ⟨12, 2, 0, 665697, 88720, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_88720_665697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88720 ⟨665697, by decide⟩ :=
  accepted_of_selected 12 88720 ⟨665697, by decide⟩ ⟨12, 2, 0, 665697, 88720, 1581, 65536⟩
    (by decide) selected_cut_26320

theorem selected_cut_26321 : selected 9 ⟨665719, by decide⟩
    (prefixPartial 12 88721) = some ⟨12, 2, 0, 665719, 88721, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_88721_665719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88721 ⟨665719, by decide⟩ :=
  accepted_of_selected 12 88721 ⟨665719, by decide⟩ ⟨12, 2, 0, 665719, 88721, 1785, 65536⟩
    (by decide) selected_cut_26321

theorem selected_cut_26322 : selected 9 ⟨665739, by decide⟩
    (prefixPartial 12 88722) = some ⟨12, 2, 0, 665739, 88722, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_88722_665739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88722 ⟨665739, by decide⟩ :=
  accepted_of_selected 12 88722 ⟨665739, by decide⟩ ⟨12, 2, 0, 665739, 88722, 1721, 65536⟩
    (by decide) selected_cut_26322

theorem selected_cut_26323 : selected 9 ⟨665763, by decide⟩
    (prefixPartial 12 88723) = some ⟨12, 2, 0, 665763, 88723, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_88723_665763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88723 ⟨665763, by decide⟩ :=
  accepted_of_selected 12 88723 ⟨665763, by decide⟩ ⟨12, 2, 0, 665763, 88723, 1765, 65536⟩
    (by decide) selected_cut_26323

theorem unmarked_context_11_22180_665764 : frontier 10 ⟨665764, by decide⟩
    (prefixCache 11 22180) (prefixPartial 11 22180) = false := by
  decide +kernel

theorem node_context_11_22180_665764 : EJMOriginalGlobalDAGData.nodes 10 ⟨665764, by decide⟩ =
    .split (coordinate 11) (![⟨665697, by decide⟩,⟨665719, by decide⟩,⟨665739, by decide⟩,⟨665763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22180_665764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22180 ⟨665764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22180
    ⟨665764, by decide⟩ (by decide) (![⟨665697, by decide⟩,⟨665719, by decide⟩,⟨665739, by decide⟩,⟨665763, by decide⟩]) unmarked_context_11_22180_665764 node_context_11_22180_665764
  intro a
  fin_cases a
  · exact context_12_88720_665697
  · exact context_12_88721_665719
  · exact context_12_88722_665739
  · exact context_12_88723_665763

theorem selected_cut_26324 : selected 9 ⟨665787, by decide⟩
    (prefixPartial 12 88724) = some ⟨12, 2, 0, 665787, 88724, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_88724_665787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88724 ⟨665787, by decide⟩ :=
  accepted_of_selected 12 88724 ⟨665787, by decide⟩ ⟨12, 2, 0, 665787, 88724, 1689, 65536⟩
    (by decide) selected_cut_26324

theorem selected_cut_26325 : selected 9 ⟨665803, by decide⟩
    (prefixPartial 12 88725) = some ⟨12, 2, 0, 665803, 88725, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_88725_665803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88725 ⟨665803, by decide⟩ :=
  accepted_of_selected 12 88725 ⟨665803, by decide⟩ ⟨12, 2, 0, 665803, 88725, 1469, 65536⟩
    (by decide) selected_cut_26325

theorem selected_cut_26326 : selected 9 ⟨665825, by decide⟩
    (prefixPartial 12 88726) = some ⟨12, 2, 0, 665825, 88726, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_88726_665825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88726 ⟨665825, by decide⟩ :=
  accepted_of_selected 12 88726 ⟨665825, by decide⟩ ⟨12, 2, 0, 665825, 88726, 1641, 65536⟩
    (by decide) selected_cut_26326

theorem selected_cut_26327 : selected 9 ⟨665841, by decide⟩
    (prefixPartial 12 88727) = some ⟨12, 2, 0, 665841, 88727, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_88727_665841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88727 ⟨665841, by decide⟩ :=
  accepted_of_selected 12 88727 ⟨665841, by decide⟩ ⟨12, 2, 0, 665841, 88727, 1565, 65536⟩
    (by decide) selected_cut_26327

theorem unmarked_context_11_22181_665842 : frontier 10 ⟨665842, by decide⟩
    (prefixCache 11 22181) (prefixPartial 11 22181) = false := by
  decide +kernel

theorem node_context_11_22181_665842 : EJMOriginalGlobalDAGData.nodes 10 ⟨665842, by decide⟩ =
    .split (coordinate 11) (![⟨665787, by decide⟩,⟨665803, by decide⟩,⟨665825, by decide⟩,⟨665841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22181_665842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22181 ⟨665842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22181
    ⟨665842, by decide⟩ (by decide) (![⟨665787, by decide⟩,⟨665803, by decide⟩,⟨665825, by decide⟩,⟨665841, by decide⟩]) unmarked_context_11_22181_665842 node_context_11_22181_665842
  intro a
  fin_cases a
  · exact context_12_88724_665787
  · exact context_12_88725_665803
  · exact context_12_88726_665825
  · exact context_12_88727_665841

theorem selected_cut_26328 : selected 9 ⟨665862, by decide⟩
    (prefixPartial 12 88728) = some ⟨12, 2, 0, 665862, 88728, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_88728_665862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88728 ⟨665862, by decide⟩ :=
  accepted_of_selected 12 88728 ⟨665862, by decide⟩ ⟨12, 2, 0, 665862, 88728, 1473, 65536⟩
    (by decide) selected_cut_26328

theorem selected_cut_26329 : selected 9 ⟨665880, by decide⟩
    (prefixPartial 12 88729) = some ⟨12, 2, 0, 665880, 88729, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_88729_665880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88729 ⟨665880, by decide⟩ :=
  accepted_of_selected 12 88729 ⟨665880, by decide⟩ ⟨12, 2, 0, 665880, 88729, 1537, 65536⟩
    (by decide) selected_cut_26329

theorem selected_cut_26330 : selected 9 ⟨660636, by decide⟩
    (prefixPartial 12 88730) = some ⟨12, 1, 0, 660636, 88730, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88730_660636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88730 ⟨660636, by decide⟩ :=
  accepted_of_selected 12 88730 ⟨660636, by decide⟩ ⟨12, 1, 0, 660636, 88730, 1, 65536⟩
    (by decide) selected_cut_26330

theorem selected_cut_26331 : selected 9 ⟨665896, by decide⟩
    (prefixPartial 12 88731) = some ⟨12, 2, 0, 665896, 88731, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_88731_665896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88731 ⟨665896, by decide⟩ :=
  accepted_of_selected 12 88731 ⟨665896, by decide⟩ ⟨12, 2, 0, 665896, 88731, 1485, 65536⟩
    (by decide) selected_cut_26331

theorem unmarked_context_11_22182_665897 : frontier 10 ⟨665897, by decide⟩
    (prefixCache 11 22182) (prefixPartial 11 22182) = false := by
  decide +kernel

theorem node_context_11_22182_665897 : EJMOriginalGlobalDAGData.nodes 10 ⟨665897, by decide⟩ =
    .split (coordinate 11) (![⟨665862, by decide⟩,⟨665880, by decide⟩,⟨660636, by decide⟩,⟨665896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22182_665897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22182 ⟨665897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22182
    ⟨665897, by decide⟩ (by decide) (![⟨665862, by decide⟩,⟨665880, by decide⟩,⟨660636, by decide⟩,⟨665896, by decide⟩]) unmarked_context_11_22182_665897 node_context_11_22182_665897
  intro a
  fin_cases a
  · exact context_12_88728_665862
  · exact context_12_88729_665880
  · exact context_12_88730_660636
  · exact context_12_88731_665896

theorem selected_cut_26332 : selected 9 ⟨665919, by decide⟩
    (prefixPartial 12 88732) = some ⟨12, 2, 0, 665919, 88732, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_88732_665919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88732 ⟨665919, by decide⟩ :=
  accepted_of_selected 12 88732 ⟨665919, by decide⟩ ⟨12, 2, 0, 665919, 88732, 1701, 65536⟩
    (by decide) selected_cut_26332

theorem selected_cut_26333 : selected 9 ⟨665941, by decide⟩
    (prefixPartial 12 88733) = some ⟨12, 2, 0, 665941, 88733, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_88733_665941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88733 ⟨665941, by decide⟩ :=
  accepted_of_selected 12 88733 ⟨665941, by decide⟩ ⟨12, 2, 0, 665941, 88733, 1657, 65536⟩
    (by decide) selected_cut_26333

theorem selected_cut_26334 : selected 9 ⟨665961, by decide⟩
    (prefixPartial 12 88734) = some ⟨12, 2, 0, 665961, 88734, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_88734_665961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88734 ⟨665961, by decide⟩ :=
  accepted_of_selected 12 88734 ⟨665961, by decide⟩ ⟨12, 2, 0, 665961, 88734, 1641, 65536⟩
    (by decide) selected_cut_26334

theorem selected_cut_26335 : selected 9 ⟨665980, by decide⟩
    (prefixPartial 12 88735) = some ⟨12, 2, 0, 665980, 88735, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_88735_665980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88735 ⟨665980, by decide⟩ :=
  accepted_of_selected 12 88735 ⟨665980, by decide⟩ ⟨12, 2, 0, 665980, 88735, 1645, 65536⟩
    (by decide) selected_cut_26335

theorem unmarked_context_11_22183_665981 : frontier 10 ⟨665981, by decide⟩
    (prefixCache 11 22183) (prefixPartial 11 22183) = false := by
  decide +kernel

theorem node_context_11_22183_665981 : EJMOriginalGlobalDAGData.nodes 10 ⟨665981, by decide⟩ =
    .split (coordinate 11) (![⟨665919, by decide⟩,⟨665941, by decide⟩,⟨665961, by decide⟩,⟨665980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22183_665981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22183 ⟨665981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22183
    ⟨665981, by decide⟩ (by decide) (![⟨665919, by decide⟩,⟨665941, by decide⟩,⟨665961, by decide⟩,⟨665980, by decide⟩]) unmarked_context_11_22183_665981 node_context_11_22183_665981
  intro a
  fin_cases a
  · exact context_12_88732_665919
  · exact context_12_88733_665941
  · exact context_12_88734_665961
  · exact context_12_88735_665980

theorem unmarked_context_10_5545_665982 : frontier 11 ⟨665982, by decide⟩
    (prefixCache 10 5545) (prefixPartial 10 5545) = false := by
  decide +kernel

theorem node_context_10_5545_665982 : EJMOriginalGlobalDAGData.nodes 11 ⟨665982, by decide⟩ =
    .split (coordinate 10) (![⟨665764, by decide⟩,⟨665842, by decide⟩,⟨665897, by decide⟩,⟨665981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5545_665982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5545 ⟨665982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5545
    ⟨665982, by decide⟩ (by decide) (![⟨665764, by decide⟩,⟨665842, by decide⟩,⟨665897, by decide⟩,⟨665981, by decide⟩]) unmarked_context_10_5545_665982 node_context_10_5545_665982
  intro a
  fin_cases a
  · exact context_11_22180_665764
  · exact context_11_22181_665842
  · exact context_11_22182_665897
  · exact context_11_22183_665981

theorem selected_cut_26336 : selected 9 ⟨665999, by decide⟩
    (prefixPartial 12 88736) = some ⟨12, 2, 0, 665999, 88736, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_88736_665999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88736 ⟨665999, by decide⟩ :=
  accepted_of_selected 12 88736 ⟨665999, by decide⟩ ⟨12, 2, 0, 665999, 88736, 1217, 65536⟩
    (by decide) selected_cut_26336

theorem selected_cut_26337 : selected 9 ⟨666013, by decide⟩
    (prefixPartial 12 88737) = some ⟨12, 2, 0, 666013, 88737, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_88737_666013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88737 ⟨666013, by decide⟩ :=
  accepted_of_selected 12 88737 ⟨666013, by decide⟩ ⟨12, 2, 0, 666013, 88737, 1253, 65536⟩
    (by decide) selected_cut_26337

theorem selected_cut_26338 : selected 9 ⟨666029, by decide⟩
    (prefixPartial 12 88738) = some ⟨12, 2, 0, 666029, 88738, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_88738_666029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88738 ⟨666029, by decide⟩ :=
  accepted_of_selected 12 88738 ⟨666029, by decide⟩ ⟨12, 2, 0, 666029, 88738, 1149, 65536⟩
    (by decide) selected_cut_26338

theorem selected_cut_26339 : selected 9 ⟨666041, by decide⟩
    (prefixPartial 12 88739) = some ⟨12, 2, 0, 666041, 88739, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_88739_666041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88739 ⟨666041, by decide⟩ :=
  accepted_of_selected 12 88739 ⟨666041, by decide⟩ ⟨12, 2, 0, 666041, 88739, 1245, 65536⟩
    (by decide) selected_cut_26339

theorem unmarked_context_11_22184_666042 : frontier 10 ⟨666042, by decide⟩
    (prefixCache 11 22184) (prefixPartial 11 22184) = false := by
  decide +kernel

theorem node_context_11_22184_666042 : EJMOriginalGlobalDAGData.nodes 10 ⟨666042, by decide⟩ =
    .split (coordinate 11) (![⟨665999, by decide⟩,⟨666013, by decide⟩,⟨666029, by decide⟩,⟨666041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22184_666042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22184 ⟨666042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22184
    ⟨666042, by decide⟩ (by decide) (![⟨665999, by decide⟩,⟨666013, by decide⟩,⟨666029, by decide⟩,⟨666041, by decide⟩]) unmarked_context_11_22184_666042 node_context_11_22184_666042
  intro a
  fin_cases a
  · exact context_12_88736_665999
  · exact context_12_88737_666013
  · exact context_12_88738_666029
  · exact context_12_88739_666041

theorem selected_cut_26340 : selected 9 ⟨666057, by decide⟩
    (prefixPartial 12 88740) = some ⟨12, 2, 0, 666057, 88740, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_88740_666057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88740 ⟨666057, by decide⟩ :=
  accepted_of_selected 12 88740 ⟨666057, by decide⟩ ⟨12, 2, 0, 666057, 88740, 1261, 65536⟩
    (by decide) selected_cut_26340

theorem selected_cut_26341 : selected 9 ⟨666070, by decide⟩
    (prefixPartial 12 88741) = some ⟨12, 2, 0, 666070, 88741, 1041, 65536⟩ := by
  decide +kernel

theorem context_12_88741_666070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88741 ⟨666070, by decide⟩ :=
  accepted_of_selected 12 88741 ⟨666070, by decide⟩ ⟨12, 2, 0, 666070, 88741, 1041, 65536⟩
    (by decide) selected_cut_26341

theorem selected_cut_26342 : selected 9 ⟨666084, by decide⟩
    (prefixPartial 12 88742) = some ⟨12, 2, 0, 666084, 88742, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_88742_666084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88742 ⟨666084, by decide⟩ :=
  accepted_of_selected 12 88742 ⟨666084, by decide⟩ ⟨12, 2, 0, 666084, 88742, 1145, 65536⟩
    (by decide) selected_cut_26342

theorem selected_cut_26343 : selected 9 ⟨666098, by decide⟩
    (prefixPartial 12 88743) = some ⟨12, 2, 0, 666098, 88743, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_88743_666098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88743 ⟨666098, by decide⟩ :=
  accepted_of_selected 12 88743 ⟨666098, by decide⟩ ⟨12, 2, 0, 666098, 88743, 1137, 65536⟩
    (by decide) selected_cut_26343

theorem unmarked_context_11_22185_666099 : frontier 10 ⟨666099, by decide⟩
    (prefixCache 11 22185) (prefixPartial 11 22185) = false := by
  decide +kernel

theorem node_context_11_22185_666099 : EJMOriginalGlobalDAGData.nodes 10 ⟨666099, by decide⟩ =
    .split (coordinate 11) (![⟨666057, by decide⟩,⟨666070, by decide⟩,⟨666084, by decide⟩,⟨666098, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22185_666099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22185 ⟨666099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22185
    ⟨666099, by decide⟩ (by decide) (![⟨666057, by decide⟩,⟨666070, by decide⟩,⟨666084, by decide⟩,⟨666098, by decide⟩]) unmarked_context_11_22185_666099 node_context_11_22185_666099
  intro a
  fin_cases a
  · exact context_12_88740_666057
  · exact context_12_88741_666070
  · exact context_12_88742_666084
  · exact context_12_88743_666098

theorem selected_cut_26344 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 22186) = some ⟨11, 1, 0, 479708, 22186, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22186_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22186 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 22186 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 22186, 1, 262144⟩
    (by decide) selected_cut_26344

theorem selected_cut_26345 : selected 9 ⟨666116, by decide⟩
    (prefixPartial 12 88748) = some ⟨12, 2, 0, 666116, 88748, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_88748_666116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88748 ⟨666116, by decide⟩ :=
  accepted_of_selected 12 88748 ⟨666116, by decide⟩ ⟨12, 2, 0, 666116, 88748, 1385, 65536⟩
    (by decide) selected_cut_26345

theorem selected_cut_26346 : selected 9 ⟨666131, by decide⟩
    (prefixPartial 12 88749) = some ⟨12, 2, 0, 666131, 88749, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_88749_666131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88749 ⟨666131, by decide⟩ :=
  accepted_of_selected 12 88749 ⟨666131, by decide⟩ ⟨12, 2, 0, 666131, 88749, 1265, 65536⟩
    (by decide) selected_cut_26346

theorem selected_cut_26347 : selected 9 ⟨666147, by decide⟩
    (prefixPartial 12 88750) = some ⟨12, 2, 0, 666147, 88750, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_88750_666147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88750 ⟨666147, by decide⟩ :=
  accepted_of_selected 12 88750 ⟨666147, by decide⟩ ⟨12, 2, 0, 666147, 88750, 1153, 65536⟩
    (by decide) selected_cut_26347

theorem selected_cut_26348 : selected 9 ⟨666163, by decide⟩
    (prefixPartial 12 88751) = some ⟨12, 2, 0, 666163, 88751, 1249, 65536⟩ := by
  decide +kernel

theorem context_12_88751_666163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88751 ⟨666163, by decide⟩ :=
  accepted_of_selected 12 88751 ⟨666163, by decide⟩ ⟨12, 2, 0, 666163, 88751, 1249, 65536⟩
    (by decide) selected_cut_26348

theorem unmarked_context_11_22187_666164 : frontier 10 ⟨666164, by decide⟩
    (prefixCache 11 22187) (prefixPartial 11 22187) = false := by
  decide +kernel

theorem node_context_11_22187_666164 : EJMOriginalGlobalDAGData.nodes 10 ⟨666164, by decide⟩ =
    .split (coordinate 11) (![⟨666116, by decide⟩,⟨666131, by decide⟩,⟨666147, by decide⟩,⟨666163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22187_666164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22187 ⟨666164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22187
    ⟨666164, by decide⟩ (by decide) (![⟨666116, by decide⟩,⟨666131, by decide⟩,⟨666147, by decide⟩,⟨666163, by decide⟩]) unmarked_context_11_22187_666164 node_context_11_22187_666164
  intro a
  fin_cases a
  · exact context_12_88748_666116
  · exact context_12_88749_666131
  · exact context_12_88750_666147
  · exact context_12_88751_666163

theorem unmarked_context_10_5546_666165 : frontier 11 ⟨666165, by decide⟩
    (prefixCache 10 5546) (prefixPartial 10 5546) = false := by
  decide +kernel

theorem node_context_10_5546_666165 : EJMOriginalGlobalDAGData.nodes 11 ⟨666165, by decide⟩ =
    .split (coordinate 10) (![⟨666042, by decide⟩,⟨666099, by decide⟩,⟨479708, by decide⟩,⟨666164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5546_666165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5546 ⟨666165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5546
    ⟨666165, by decide⟩ (by decide) (![⟨666042, by decide⟩,⟨666099, by decide⟩,⟨479708, by decide⟩,⟨666164, by decide⟩]) unmarked_context_10_5546_666165 node_context_10_5546_666165
  intro a
  fin_cases a
  · exact context_11_22184_666042
  · exact context_11_22185_666099
  · exact context_11_22186_479708
  · exact context_11_22187_666164

theorem selected_cut_26349 : selected 9 ⟨666175, by decide⟩
    (prefixPartial 12 88752) = some ⟨12, 2, 0, 666175, 88752, 985, 65536⟩ := by
  decide +kernel

theorem context_12_88752_666175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88752 ⟨666175, by decide⟩ :=
  accepted_of_selected 12 88752 ⟨666175, by decide⟩ ⟨12, 2, 0, 666175, 88752, 985, 65536⟩
    (by decide) selected_cut_26349

theorem selected_cut_26350 : selected 9 ⟨666185, by decide⟩
    (prefixPartial 12 88753) = some ⟨12, 2, 0, 666185, 88753, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_88753_666185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88753 ⟨666185, by decide⟩ :=
  accepted_of_selected 12 88753 ⟨666185, by decide⟩ ⟨12, 2, 0, 666185, 88753, 1109, 65536⟩
    (by decide) selected_cut_26350

theorem selected_cut_26351 : selected 9 ⟨666195, by decide⟩
    (prefixPartial 12 88754) = some ⟨12, 2, 0, 666195, 88754, 1009, 65536⟩ := by
  decide +kernel

theorem context_12_88754_666195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88754 ⟨666195, by decide⟩ :=
  accepted_of_selected 12 88754 ⟨666195, by decide⟩ ⟨12, 2, 0, 666195, 88754, 1009, 65536⟩
    (by decide) selected_cut_26351

theorem selected_cut_26352 : selected 9 ⟨666209, by decide⟩
    (prefixPartial 12 88755) = some ⟨12, 2, 0, 666209, 88755, 1045, 65536⟩ := by
  decide +kernel

theorem context_12_88755_666209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88755 ⟨666209, by decide⟩ :=
  accepted_of_selected 12 88755 ⟨666209, by decide⟩ ⟨12, 2, 0, 666209, 88755, 1045, 65536⟩
    (by decide) selected_cut_26352

theorem unmarked_context_11_22188_666210 : frontier 10 ⟨666210, by decide⟩
    (prefixCache 11 22188) (prefixPartial 11 22188) = false := by
  decide +kernel

theorem node_context_11_22188_666210 : EJMOriginalGlobalDAGData.nodes 10 ⟨666210, by decide⟩ =
    .split (coordinate 11) (![⟨666175, by decide⟩,⟨666185, by decide⟩,⟨666195, by decide⟩,⟨666209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22188_666210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22188 ⟨666210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22188
    ⟨666210, by decide⟩ (by decide) (![⟨666175, by decide⟩,⟨666185, by decide⟩,⟨666195, by decide⟩,⟨666209, by decide⟩]) unmarked_context_11_22188_666210 node_context_11_22188_666210
  intro a
  fin_cases a
  · exact context_12_88752_666175
  · exact context_12_88753_666185
  · exact context_12_88754_666195
  · exact context_12_88755_666209

theorem selected_cut_26353 : selected 10 ⟨666255, by decide⟩
    (prefixPartial 11 22189) = some ⟨11, 2, 0, 666255, 22189, 3981, 262144⟩ := by
  decide +kernel

theorem context_11_22189_666255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22189 ⟨666255, by decide⟩ :=
  accepted_of_selected 11 22189 ⟨666255, by decide⟩ ⟨11, 2, 0, 666255, 22189, 3981, 262144⟩
    (by decide) selected_cut_26353

theorem selected_cut_26354 : selected 10 ⟨666289, by decide⟩
    (prefixPartial 11 22190) = some ⟨11, 2, 0, 666289, 22190, 2621, 262144⟩ := by
  decide +kernel

theorem context_11_22190_666289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22190 ⟨666289, by decide⟩ :=
  accepted_of_selected 11 22190 ⟨666289, by decide⟩ ⟨11, 2, 0, 666289, 22190, 2621, 262144⟩
    (by decide) selected_cut_26354

theorem selected_cut_26355 : selected 10 ⟨666333, by decide⟩
    (prefixPartial 11 22191) = some ⟨11, 2, 0, 666333, 22191, 3705, 262144⟩ := by
  decide +kernel

theorem context_11_22191_666333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22191 ⟨666333, by decide⟩ :=
  accepted_of_selected 11 22191 ⟨666333, by decide⟩ ⟨11, 2, 0, 666333, 22191, 3705, 262144⟩
    (by decide) selected_cut_26355

theorem unmarked_context_10_5547_666334 : frontier 11 ⟨666334, by decide⟩
    (prefixCache 10 5547) (prefixPartial 10 5547) = false := by
  decide +kernel

theorem node_context_10_5547_666334 : EJMOriginalGlobalDAGData.nodes 11 ⟨666334, by decide⟩ =
    .split (coordinate 10) (![⟨666210, by decide⟩,⟨666255, by decide⟩,⟨666289, by decide⟩,⟨666333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5547_666334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5547 ⟨666334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5547
    ⟨666334, by decide⟩ (by decide) (![⟨666210, by decide⟩,⟨666255, by decide⟩,⟨666289, by decide⟩,⟨666333, by decide⟩]) unmarked_context_10_5547_666334 node_context_10_5547_666334
  intro a
  fin_cases a
  · exact context_11_22188_666210
  · exact context_11_22189_666255
  · exact context_11_22190_666289
  · exact context_11_22191_666333

theorem unmarked_context_9_1386_666335 : frontier 12 ⟨666335, by decide⟩
    (prefixCache 9 1386) (prefixPartial 9 1386) = false := by
  decide +kernel

theorem node_context_9_1386_666335 : EJMOriginalGlobalDAGData.nodes 12 ⟨666335, by decide⟩ =
    .split (coordinate 9) (![⟨665676, by decide⟩,⟨665982, by decide⟩,⟨666165, by decide⟩,⟨666334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1386_666335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1386 ⟨666335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1386
    ⟨666335, by decide⟩ (by decide) (![⟨665676, by decide⟩,⟨665982, by decide⟩,⟨666165, by decide⟩,⟨666334, by decide⟩]) unmarked_context_9_1386_666335 node_context_9_1386_666335
  intro a
  fin_cases a
  · exact context_10_5544_665676
  · exact context_10_5545_665982
  · exact context_10_5546_666165
  · exact context_10_5547_666334

theorem selected_cut_26356 : selected 9 ⟨666346, by decide⟩
    (prefixPartial 12 88768) = some ⟨12, 2, 0, 666346, 88768, 1029, 65536⟩ := by
  decide +kernel

theorem context_12_88768_666346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88768 ⟨666346, by decide⟩ :=
  accepted_of_selected 12 88768 ⟨666346, by decide⟩ ⟨12, 2, 0, 666346, 88768, 1029, 65536⟩
    (by decide) selected_cut_26356

theorem selected_cut_26357 : selected 9 ⟨666362, by decide⟩
    (prefixPartial 12 88769) = some ⟨12, 2, 0, 666362, 88769, 1081, 65536⟩ := by
  decide +kernel

theorem context_12_88769_666362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88769 ⟨666362, by decide⟩ :=
  accepted_of_selected 12 88769 ⟨666362, by decide⟩ ⟨12, 2, 0, 666362, 88769, 1081, 65536⟩
    (by decide) selected_cut_26357

theorem selected_cut_26358 : selected 9 ⟨666376, by decide⟩
    (prefixPartial 12 88770) = some ⟨12, 2, 0, 666376, 88770, 1081, 65536⟩ := by
  decide +kernel

theorem context_12_88770_666376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88770 ⟨666376, by decide⟩ :=
  accepted_of_selected 12 88770 ⟨666376, by decide⟩ ⟨12, 2, 0, 666376, 88770, 1081, 65536⟩
    (by decide) selected_cut_26358

theorem selected_cut_26359 : selected 9 ⟨666385, by decide⟩
    (prefixPartial 12 88771) = some ⟨12, 2, 0, 666385, 88771, 1017, 65536⟩ := by
  decide +kernel

theorem context_12_88771_666385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88771 ⟨666385, by decide⟩ :=
  accepted_of_selected 12 88771 ⟨666385, by decide⟩ ⟨12, 2, 0, 666385, 88771, 1017, 65536⟩
    (by decide) selected_cut_26359

theorem unmarked_context_11_22192_666386 : frontier 10 ⟨666386, by decide⟩
    (prefixCache 11 22192) (prefixPartial 11 22192) = false := by
  decide +kernel

theorem node_context_11_22192_666386 : EJMOriginalGlobalDAGData.nodes 10 ⟨666386, by decide⟩ =
    .split (coordinate 11) (![⟨666346, by decide⟩,⟨666362, by decide⟩,⟨666376, by decide⟩,⟨666385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22192_666386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22192 ⟨666386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22192
    ⟨666386, by decide⟩ (by decide) (![⟨666346, by decide⟩,⟨666362, by decide⟩,⟨666376, by decide⟩,⟨666385, by decide⟩]) unmarked_context_11_22192_666386 node_context_11_22192_666386
  intro a
  fin_cases a
  · exact context_12_88768_666346
  · exact context_12_88769_666362
  · exact context_12_88770_666376
  · exact context_12_88771_666385

theorem selected_cut_26360 : selected 10 ⟨666440, by decide⟩
    (prefixPartial 11 22193) = some ⟨11, 2, 0, 666440, 22193, 3829, 262144⟩ := by
  decide +kernel

theorem context_11_22193_666440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22193 ⟨666440, by decide⟩ :=
  accepted_of_selected 11 22193 ⟨666440, by decide⟩ ⟨11, 2, 0, 666440, 22193, 3829, 262144⟩
    (by decide) selected_cut_26360

theorem selected_cut_26361 : selected 10 ⟨666462, by decide⟩
    (prefixPartial 11 22194) = some ⟨11, 2, 0, 666462, 22194, 2313, 262144⟩ := by
  decide +kernel

theorem context_11_22194_666462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22194 ⟨666462, by decide⟩ :=
  accepted_of_selected 11 22194 ⟨666462, by decide⟩ ⟨11, 2, 0, 666462, 22194, 2313, 262144⟩
    (by decide) selected_cut_26361

theorem selected_cut_26362 : selected 10 ⟨666520, by decide⟩
    (prefixPartial 11 22195) = some ⟨11, 2, 0, 666520, 22195, 3593, 262144⟩ := by
  decide +kernel

theorem context_11_22195_666520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22195 ⟨666520, by decide⟩ :=
  accepted_of_selected 11 22195 ⟨666520, by decide⟩ ⟨11, 2, 0, 666520, 22195, 3593, 262144⟩
    (by decide) selected_cut_26362

theorem unmarked_context_10_5548_666521 : frontier 11 ⟨666521, by decide⟩
    (prefixCache 10 5548) (prefixPartial 10 5548) = false := by
  decide +kernel

theorem node_context_10_5548_666521 : EJMOriginalGlobalDAGData.nodes 11 ⟨666521, by decide⟩ =
    .split (coordinate 10) (![⟨666386, by decide⟩,⟨666440, by decide⟩,⟨666462, by decide⟩,⟨666520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5548_666521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5548 ⟨666521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5548
    ⟨666521, by decide⟩ (by decide) (![⟨666386, by decide⟩,⟨666440, by decide⟩,⟨666462, by decide⟩,⟨666520, by decide⟩]) unmarked_context_10_5548_666521 node_context_10_5548_666521
  intro a
  fin_cases a
  · exact context_11_22192_666386
  · exact context_11_22193_666440
  · exact context_11_22194_666462
  · exact context_11_22195_666520

theorem selected_cut_26363 : selected 10 ⟨666564, by decide⟩
    (prefixPartial 11 22196) = some ⟨11, 2, 0, 666564, 22196, 2909, 262144⟩ := by
  decide +kernel

theorem context_11_22196_666564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22196 ⟨666564, by decide⟩ :=
  accepted_of_selected 11 22196 ⟨666564, by decide⟩ ⟨11, 2, 0, 666564, 22196, 2909, 262144⟩
    (by decide) selected_cut_26363

theorem selected_cut_26364 : selected 10 ⟨666596, by decide⟩
    (prefixPartial 11 22197) = some ⟨11, 2, 0, 666596, 22197, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_22197_666596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22197 ⟨666596, by decide⟩ :=
  accepted_of_selected 11 22197 ⟨666596, by decide⟩ ⟨11, 2, 0, 666596, 22197, 2413, 262144⟩
    (by decide) selected_cut_26364

theorem selected_cut_26365 : selected 10 ⟨666613, by decide⟩
    (prefixPartial 11 22198) = some ⟨11, 2, 0, 666613, 22198, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_22198_666613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22198 ⟨666613, by decide⟩ :=
  accepted_of_selected 11 22198 ⟨666613, by decide⟩ ⟨11, 2, 0, 666613, 22198, 1537, 262144⟩
    (by decide) selected_cut_26365

theorem selected_cut_26366 : selected 10 ⟨666645, by decide⟩
    (prefixPartial 11 22199) = some ⟨11, 2, 0, 666645, 22199, 2049, 262144⟩ := by
  decide +kernel

theorem context_11_22199_666645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22199 ⟨666645, by decide⟩ :=
  accepted_of_selected 11 22199 ⟨666645, by decide⟩ ⟨11, 2, 0, 666645, 22199, 2049, 262144⟩
    (by decide) selected_cut_26366

theorem unmarked_context_10_5549_666646 : frontier 11 ⟨666646, by decide⟩
    (prefixCache 10 5549) (prefixPartial 10 5549) = false := by
  decide +kernel

theorem node_context_10_5549_666646 : EJMOriginalGlobalDAGData.nodes 11 ⟨666646, by decide⟩ =
    .split (coordinate 10) (![⟨666564, by decide⟩,⟨666596, by decide⟩,⟨666613, by decide⟩,⟨666645, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5549_666646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5549 ⟨666646, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5549
    ⟨666646, by decide⟩ (by decide) (![⟨666564, by decide⟩,⟨666596, by decide⟩,⟨666613, by decide⟩,⟨666645, by decide⟩]) unmarked_context_10_5549_666646 node_context_10_5549_666646
  intro a
  fin_cases a
  · exact context_11_22196_666564
  · exact context_11_22197_666596
  · exact context_11_22198_666613
  · exact context_11_22199_666645

theorem selected_cut_26367 : selected 11 ⟨666690, by decide⟩
    (prefixPartial 10 5550) = some ⟨10, 2, 0, 666690, 5550, 3265, 1048576⟩ := by
  decide +kernel

theorem context_10_5550_666690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5550 ⟨666690, by decide⟩ :=
  accepted_of_selected 10 5550 ⟨666690, by decide⟩ ⟨10, 2, 0, 666690, 5550, 3265, 1048576⟩
    (by decide) selected_cut_26367

theorem selected_cut_26368 : selected 11 ⟨666725, by decide⟩
    (prefixPartial 10 5551) = some ⟨10, 2, 0, 666725, 5551, 1389, 1048576⟩ := by
  decide +kernel

theorem context_10_5551_666725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5551 ⟨666725, by decide⟩ :=
  accepted_of_selected 10 5551 ⟨666725, by decide⟩ ⟨10, 2, 0, 666725, 5551, 1389, 1048576⟩
    (by decide) selected_cut_26368

theorem unmarked_context_9_1387_666726 : frontier 12 ⟨666726, by decide⟩
    (prefixCache 9 1387) (prefixPartial 9 1387) = false := by
  decide +kernel

theorem node_context_9_1387_666726 : EJMOriginalGlobalDAGData.nodes 12 ⟨666726, by decide⟩ =
    .split (coordinate 9) (![⟨666521, by decide⟩,⟨666646, by decide⟩,⟨666690, by decide⟩,⟨666725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1387_666726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1387 ⟨666726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1387
    ⟨666726, by decide⟩ (by decide) (![⟨666521, by decide⟩,⟨666646, by decide⟩,⟨666690, by decide⟩,⟨666725, by decide⟩]) unmarked_context_9_1387_666726 node_context_9_1387_666726
  intro a
  fin_cases a
  · exact context_10_5548_666521
  · exact context_10_5549_666646
  · exact context_10_5550_666690
  · exact context_10_5551_666725

theorem unmarked_context_8_346_666727 : frontier 13 ⟨666727, by decide⟩
    (prefixCache 8 346) (prefixPartial 8 346) = false := by
  decide +kernel

theorem node_context_8_346_666727 : EJMOriginalGlobalDAGData.nodes 13 ⟨666727, by decide⟩ =
    .split (coordinate 8) (![⟨663042, by decide⟩,⟨665385, by decide⟩,⟨666335, by decide⟩,⟨666726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_346_666727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 346 ⟨666727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 346
    ⟨666727, by decide⟩ (by decide) (![⟨663042, by decide⟩,⟨665385, by decide⟩,⟨666335, by decide⟩,⟨666726, by decide⟩]) unmarked_context_8_346_666727 node_context_8_346_666727
  intro a
  fin_cases a
  · exact context_9_1384_663042
  · exact context_9_1385_665385
  · exact context_9_1386_666335
  · exact context_9_1387_666726

theorem selected_cut_26369 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 22208) = some ⟨11, 1, 0, 434745, 22208, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22208_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22208 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 22208 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 22208, 1, 262144⟩
    (by decide) selected_cut_26369

theorem selected_cut_26370 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 88836) = some ⟨12, 1, 0, 448748, 88836, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88836_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88836 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 88836 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 88836, 1, 65536⟩
    (by decide) selected_cut_26370

theorem selected_cut_26371 : selected 8 ⟨666816, by decide⟩
    (prefixPartial 13 355348) = some ⟨13, 2, 0, 666816, 355348, 4053, 16384⟩ := by
  decide +kernel

theorem context_13_355348_666816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355348 ⟨666816, by decide⟩ :=
  accepted_of_selected 13 355348 ⟨666816, by decide⟩ ⟨13, 2, 0, 666816, 355348, 4053, 16384⟩
    (by decide) selected_cut_26371

theorem selected_cut_26372 : selected 8 ⟨666883, by decide⟩
    (prefixPartial 13 355349) = some ⟨13, 2, 0, 666883, 355349, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_355349_666883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355349 ⟨666883, by decide⟩ :=
  accepted_of_selected 13 355349 ⟨666883, by decide⟩ ⟨13, 2, 0, 666883, 355349, 2813, 16384⟩
    (by decide) selected_cut_26372

theorem selected_cut_26373 : selected 8 ⟨666905, by decide⟩
    (prefixPartial 13 355350) = some ⟨13, 2, 0, 666905, 355350, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_355350_666905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355350 ⟨666905, by decide⟩ :=
  accepted_of_selected 13 355350 ⟨666905, by decide⟩ ⟨13, 2, 0, 666905, 355350, 1645, 16384⟩
    (by decide) selected_cut_26373

theorem selected_cut_26374 : selected 8 ⟨666912, by decide⟩
    (prefixPartial 13 355351) = some ⟨13, 2, 0, 666912, 355351, 841, 16384⟩ := by
  decide +kernel

theorem context_13_355351_666912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355351 ⟨666912, by decide⟩ :=
  accepted_of_selected 13 355351 ⟨666912, by decide⟩ ⟨13, 2, 0, 666912, 355351, 841, 16384⟩
    (by decide) selected_cut_26374

theorem unmarked_context_12_88837_666913 : frontier 9 ⟨666913, by decide⟩
    (prefixCache 12 88837) (prefixPartial 12 88837) = false := by
  decide +kernel

theorem node_context_12_88837_666913 : EJMOriginalGlobalDAGData.nodes 9 ⟨666913, by decide⟩ =
    .split (coordinate 12) (![⟨666816, by decide⟩,⟨666883, by decide⟩,⟨666905, by decide⟩,⟨666912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88837_666913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88837 ⟨666913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88837
    ⟨666913, by decide⟩ (by decide) (![⟨666816, by decide⟩,⟨666883, by decide⟩,⟨666905, by decide⟩,⟨666912, by decide⟩]) unmarked_context_12_88837_666913 node_context_12_88837_666913
  intro a
  fin_cases a
  · exact context_13_355348_666816
  · exact context_13_355349_666883
  · exact context_13_355350_666905
  · exact context_13_355351_666912

theorem selected_cut_26375 : selected 7 ⟨666942, by decide⟩
    (prefixPartial 14 1421408) = some ⟨14, 2, 0, 666942, 1421408, 949, 4096⟩ := by
  decide +kernel

theorem context_14_1421408_666942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1421408 ⟨666942, by decide⟩ :=
  accepted_of_selected 14 1421408 ⟨666942, by decide⟩ ⟨14, 2, 0, 666942, 1421408, 949, 4096⟩
    (by decide) selected_cut_26375

theorem selected_cut_26376 : selected 7 ⟨666968, by decide⟩
    (prefixPartial 14 1421409) = some ⟨14, 2, 0, 666968, 1421409, 1433, 4096⟩ := by
  decide +kernel

theorem context_14_1421409_666968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1421409 ⟨666968, by decide⟩ :=
  accepted_of_selected 14 1421409 ⟨666968, by decide⟩ ⟨14, 2, 0, 666968, 1421409, 1433, 4096⟩
    (by decide) selected_cut_26376

theorem selected_cut_26377 : selected 7 ⟨666990, by decide⟩
    (prefixPartial 14 1421410) = some ⟨14, 2, 0, 666990, 1421410, 1225, 4096⟩ := by
  decide +kernel

theorem context_14_1421410_666990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1421410 ⟨666990, by decide⟩ :=
  accepted_of_selected 14 1421410 ⟨666990, by decide⟩ ⟨14, 2, 0, 666990, 1421410, 1225, 4096⟩
    (by decide) selected_cut_26377

theorem selected_cut_26378 : selected 7 ⟨667002, by decide⟩
    (prefixPartial 14 1421411) = some ⟨14, 2, 0, 667002, 1421411, 853, 4096⟩ := by
  decide +kernel

theorem context_14_1421411_667002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1421411 ⟨667002, by decide⟩ :=
  accepted_of_selected 14 1421411 ⟨667002, by decide⟩ ⟨14, 2, 0, 667002, 1421411, 853, 4096⟩
    (by decide) selected_cut_26378

theorem unmarked_context_13_355352_667003 : frontier 8 ⟨667003, by decide⟩
    (prefixCache 13 355352) (prefixPartial 13 355352) = false := by
  decide +kernel

theorem node_context_13_355352_667003 : EJMOriginalGlobalDAGData.nodes 8 ⟨667003, by decide⟩ =
    .split (coordinate 13) (![⟨666942, by decide⟩,⟨666968, by decide⟩,⟨666990, by decide⟩,⟨667002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_355352_667003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355352 ⟨667003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 355352
    ⟨667003, by decide⟩ (by decide) (![⟨666942, by decide⟩,⟨666968, by decide⟩,⟨666990, by decide⟩,⟨667002, by decide⟩]) unmarked_context_13_355352_667003 node_context_13_355352_667003
  intro a
  fin_cases a
  · exact context_14_1421408_666942
  · exact context_14_1421409_666968
  · exact context_14_1421410_666990
  · exact context_14_1421411_667002

theorem selected_cut_26379 : selected 8 ⟨667076, by decide⟩
    (prefixPartial 13 355353) = some ⟨13, 2, 0, 667076, 355353, 3313, 16384⟩ := by
  decide +kernel

theorem context_13_355353_667076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355353 ⟨667076, by decide⟩ :=
  accepted_of_selected 13 355353 ⟨667076, by decide⟩ ⟨13, 2, 0, 667076, 355353, 3313, 16384⟩
    (by decide) selected_cut_26379

theorem selected_cut_26380 : selected 8 ⟨667111, by decide⟩
    (prefixPartial 13 355354) = some ⟨13, 2, 0, 667111, 355354, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_355354_667111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355354 ⟨667111, by decide⟩ :=
  accepted_of_selected 13 355354 ⟨667111, by decide⟩ ⟨13, 2, 0, 667111, 355354, 2141, 16384⟩
    (by decide) selected_cut_26380

theorem selected_cut_26381 : selected 8 ⟨667136, by decide⟩
    (prefixPartial 13 355355) = some ⟨13, 2, 0, 667136, 355355, 905, 16384⟩ := by
  decide +kernel

theorem context_13_355355_667136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355355 ⟨667136, by decide⟩ :=
  accepted_of_selected 13 355355 ⟨667136, by decide⟩ ⟨13, 2, 0, 667136, 355355, 905, 16384⟩
    (by decide) selected_cut_26381

theorem unmarked_context_12_88838_667137 : frontier 9 ⟨667137, by decide⟩
    (prefixCache 12 88838) (prefixPartial 12 88838) = false := by
  decide +kernel

theorem node_context_12_88838_667137 : EJMOriginalGlobalDAGData.nodes 9 ⟨667137, by decide⟩ =
    .split (coordinate 12) (![⟨667003, by decide⟩,⟨667076, by decide⟩,⟨667111, by decide⟩,⟨667136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88838_667137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88838 ⟨667137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88838
    ⟨667137, by decide⟩ (by decide) (![⟨667003, by decide⟩,⟨667076, by decide⟩,⟨667111, by decide⟩,⟨667136, by decide⟩]) unmarked_context_12_88838_667137 node_context_12_88838_667137
  intro a
  fin_cases a
  · exact context_13_355352_667003
  · exact context_13_355353_667076
  · exact context_13_355354_667111
  · exact context_13_355355_667136

theorem selected_cut_26382 : selected 8 ⟨667206, by decide⟩
    (prefixPartial 13 355356) = some ⟨13, 2, 0, 667206, 355356, 3681, 16384⟩ := by
  decide +kernel

theorem context_13_355356_667206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355356 ⟨667206, by decide⟩ :=
  accepted_of_selected 13 355356 ⟨667206, by decide⟩ ⟨13, 2, 0, 667206, 355356, 3681, 16384⟩
    (by decide) selected_cut_26382

theorem selected_cut_26383 : selected 8 ⟨667272, by decide⟩
    (prefixPartial 13 355357) = some ⟨13, 2, 0, 667272, 355357, 3229, 16384⟩ := by
  decide +kernel

theorem context_13_355357_667272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355357 ⟨667272, by decide⟩ :=
  accepted_of_selected 13 355357 ⟨667272, by decide⟩ ⟨13, 2, 0, 667272, 355357, 3229, 16384⟩
    (by decide) selected_cut_26383

theorem selected_cut_26384 : selected 8 ⟨667296, by decide⟩
    (prefixPartial 13 355358) = some ⟨13, 2, 0, 667296, 355358, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_355358_667296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355358 ⟨667296, by decide⟩ :=
  accepted_of_selected 13 355358 ⟨667296, by decide⟩ ⟨13, 2, 0, 667296, 355358, 1929, 16384⟩
    (by decide) selected_cut_26384

theorem selected_cut_26385 : selected 8 ⟨667301, by decide⟩
    (prefixPartial 13 355359) = some ⟨13, 2, 0, 667301, 355359, 845, 16384⟩ := by
  decide +kernel

theorem context_13_355359_667301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355359 ⟨667301, by decide⟩ :=
  accepted_of_selected 13 355359 ⟨667301, by decide⟩ ⟨13, 2, 0, 667301, 355359, 845, 16384⟩
    (by decide) selected_cut_26385

theorem unmarked_context_12_88839_667302 : frontier 9 ⟨667302, by decide⟩
    (prefixCache 12 88839) (prefixPartial 12 88839) = false := by
  decide +kernel

theorem node_context_12_88839_667302 : EJMOriginalGlobalDAGData.nodes 9 ⟨667302, by decide⟩ =
    .split (coordinate 12) (![⟨667206, by decide⟩,⟨667272, by decide⟩,⟨667296, by decide⟩,⟨667301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88839_667302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88839 ⟨667302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88839
    ⟨667302, by decide⟩ (by decide) (![⟨667206, by decide⟩,⟨667272, by decide⟩,⟨667296, by decide⟩,⟨667301, by decide⟩]) unmarked_context_12_88839_667302 node_context_12_88839_667302
  intro a
  fin_cases a
  · exact context_13_355356_667206
  · exact context_13_355357_667272
  · exact context_13_355358_667296
  · exact context_13_355359_667301

theorem unmarked_context_11_22209_667303 : frontier 10 ⟨667303, by decide⟩
    (prefixCache 11 22209) (prefixPartial 11 22209) = false := by
  decide +kernel

theorem node_context_11_22209_667303 : EJMOriginalGlobalDAGData.nodes 10 ⟨667303, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨666913, by decide⟩,⟨667137, by decide⟩,⟨667302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22209_667303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22209 ⟨667303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22209
    ⟨667303, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨666913, by decide⟩,⟨667137, by decide⟩,⟨667302, by decide⟩]) unmarked_context_11_22209_667303 node_context_11_22209_667303
  intro a
  fin_cases a
  · exact context_12_88836_448748
  · exact context_12_88837_666913
  · exact context_12_88838_667137
  · exact context_12_88839_667302

theorem selected_cut_26386 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 88840) = some ⟨12, 1, 0, 448748, 88840, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88840_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88840 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 88840 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 88840, 1, 65536⟩
    (by decide) selected_cut_26386

theorem selected_cut_26387 : selected 8 ⟨667370, by decide⟩
    (prefixPartial 13 355364) = some ⟨13, 2, 0, 667370, 355364, 3653, 16384⟩ := by
  decide +kernel

theorem context_13_355364_667370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355364 ⟨667370, by decide⟩ :=
  accepted_of_selected 13 355364 ⟨667370, by decide⟩ ⟨13, 2, 0, 667370, 355364, 3653, 16384⟩
    (by decide) selected_cut_26387

theorem selected_cut_26388 : selected 8 ⟨667420, by decide⟩
    (prefixPartial 13 355365) = some ⟨13, 2, 0, 667420, 355365, 2705, 16384⟩ := by
  decide +kernel

theorem context_13_355365_667420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355365 ⟨667420, by decide⟩ :=
  accepted_of_selected 13 355365 ⟨667420, by decide⟩ ⟨13, 2, 0, 667420, 355365, 2705, 16384⟩
    (by decide) selected_cut_26388

theorem selected_cut_26389 : selected 8 ⟨667452, by decide⟩
    (prefixPartial 13 355366) = some ⟨13, 2, 0, 667452, 355366, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_355366_667452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355366 ⟨667452, by decide⟩ :=
  accepted_of_selected 13 355366 ⟨667452, by decide⟩ ⟨13, 2, 0, 667452, 355366, 2145, 16384⟩
    (by decide) selected_cut_26389

theorem selected_cut_26390 : selected 8 ⟨667457, by decide⟩
    (prefixPartial 13 355367) = some ⟨13, 2, 0, 667457, 355367, 805, 16384⟩ := by
  decide +kernel

theorem context_13_355367_667457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355367 ⟨667457, by decide⟩ :=
  accepted_of_selected 13 355367 ⟨667457, by decide⟩ ⟨13, 2, 0, 667457, 355367, 805, 16384⟩
    (by decide) selected_cut_26390

theorem unmarked_context_12_88841_667458 : frontier 9 ⟨667458, by decide⟩
    (prefixCache 12 88841) (prefixPartial 12 88841) = false := by
  decide +kernel

theorem node_context_12_88841_667458 : EJMOriginalGlobalDAGData.nodes 9 ⟨667458, by decide⟩ =
    .split (coordinate 12) (![⟨667370, by decide⟩,⟨667420, by decide⟩,⟨667452, by decide⟩,⟨667457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88841_667458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88841 ⟨667458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88841
    ⟨667458, by decide⟩ (by decide) (![⟨667370, by decide⟩,⟨667420, by decide⟩,⟨667452, by decide⟩,⟨667457, by decide⟩]) unmarked_context_12_88841_667458 node_context_12_88841_667458
  intro a
  fin_cases a
  · exact context_13_355364_667370
  · exact context_13_355365_667420
  · exact context_13_355366_667452
  · exact context_13_355367_667457

theorem selected_cut_26391 : selected 8 ⟨667543, by decide⟩
    (prefixPartial 13 355368) = some ⟨13, 2, 0, 667543, 355368, 3625, 16384⟩ := by
  decide +kernel

theorem context_13_355368_667543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355368 ⟨667543, by decide⟩ :=
  accepted_of_selected 13 355368 ⟨667543, by decide⟩ ⟨13, 2, 0, 667543, 355368, 3625, 16384⟩
    (by decide) selected_cut_26391

theorem selected_cut_26392 : selected 8 ⟨667593, by decide⟩
    (prefixPartial 13 355369) = some ⟨13, 2, 0, 667593, 355369, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_355369_667593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355369 ⟨667593, by decide⟩ :=
  accepted_of_selected 13 355369 ⟨667593, by decide⟩ ⟨13, 2, 0, 667593, 355369, 1653, 16384⟩
    (by decide) selected_cut_26392

theorem selected_cut_26393 : selected 8 ⟨667631, by decide⟩
    (prefixPartial 13 355370) = some ⟨13, 2, 0, 667631, 355370, 729, 16384⟩ := by
  decide +kernel

theorem context_13_355370_667631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355370 ⟨667631, by decide⟩ :=
  accepted_of_selected 13 355370 ⟨667631, by decide⟩ ⟨13, 2, 0, 667631, 355370, 729, 16384⟩
    (by decide) selected_cut_26393

theorem selected_cut_26394 : selected 8 ⟨667634, by decide⟩
    (prefixPartial 13 355371) = some ⟨13, 2, 0, 667634, 355371, 97, 16384⟩ := by
  decide +kernel

theorem context_13_355371_667634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355371 ⟨667634, by decide⟩ :=
  accepted_of_selected 13 355371 ⟨667634, by decide⟩ ⟨13, 2, 0, 667634, 355371, 97, 16384⟩
    (by decide) selected_cut_26394

theorem unmarked_context_12_88842_667635 : frontier 9 ⟨667635, by decide⟩
    (prefixCache 12 88842) (prefixPartial 12 88842) = false := by
  decide +kernel

theorem node_context_12_88842_667635 : EJMOriginalGlobalDAGData.nodes 9 ⟨667635, by decide⟩ =
    .split (coordinate 12) (![⟨667543, by decide⟩,⟨667593, by decide⟩,⟨667631, by decide⟩,⟨667634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88842_667635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88842 ⟨667635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88842
    ⟨667635, by decide⟩ (by decide) (![⟨667543, by decide⟩,⟨667593, by decide⟩,⟨667631, by decide⟩,⟨667634, by decide⟩]) unmarked_context_12_88842_667635 node_context_12_88842_667635
  intro a
  fin_cases a
  · exact context_13_355368_667543
  · exact context_13_355369_667593
  · exact context_13_355370_667631
  · exact context_13_355371_667634

theorem selected_cut_26395 : selected 8 ⟨667691, by decide⟩
    (prefixPartial 13 355372) = some ⟨13, 2, 0, 667691, 355372, 3585, 16384⟩ := by
  decide +kernel

theorem context_13_355372_667691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355372 ⟨667691, by decide⟩ :=
  accepted_of_selected 13 355372 ⟨667691, by decide⟩ ⟨13, 2, 0, 667691, 355372, 3585, 16384⟩
    (by decide) selected_cut_26395

theorem selected_cut_26396 : selected 8 ⟨667752, by decide⟩
    (prefixPartial 13 355373) = some ⟨13, 2, 0, 667752, 355373, 3429, 16384⟩ := by
  decide +kernel

theorem context_13_355373_667752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355373 ⟨667752, by decide⟩ :=
  accepted_of_selected 13 355373 ⟨667752, by decide⟩ ⟨13, 2, 0, 667752, 355373, 3429, 16384⟩
    (by decide) selected_cut_26396

theorem selected_cut_26397 : selected 8 ⟨667786, by decide⟩
    (prefixPartial 13 355374) = some ⟨13, 2, 0, 667786, 355374, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_355374_667786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355374 ⟨667786, by decide⟩ :=
  accepted_of_selected 13 355374 ⟨667786, by decide⟩ ⟨13, 2, 0, 667786, 355374, 2325, 16384⟩
    (by decide) selected_cut_26397

theorem selected_cut_26398 : selected 8 ⟨667795, by decide⟩
    (prefixPartial 13 355375) = some ⟨13, 2, 0, 667795, 355375, 857, 16384⟩ := by
  decide +kernel

theorem context_13_355375_667795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355375 ⟨667795, by decide⟩ :=
  accepted_of_selected 13 355375 ⟨667795, by decide⟩ ⟨13, 2, 0, 667795, 355375, 857, 16384⟩
    (by decide) selected_cut_26398

theorem unmarked_context_12_88843_667796 : frontier 9 ⟨667796, by decide⟩
    (prefixCache 12 88843) (prefixPartial 12 88843) = false := by
  decide +kernel

theorem node_context_12_88843_667796 : EJMOriginalGlobalDAGData.nodes 9 ⟨667796, by decide⟩ =
    .split (coordinate 12) (![⟨667691, by decide⟩,⟨667752, by decide⟩,⟨667786, by decide⟩,⟨667795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88843_667796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88843 ⟨667796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88843
    ⟨667796, by decide⟩ (by decide) (![⟨667691, by decide⟩,⟨667752, by decide⟩,⟨667786, by decide⟩,⟨667795, by decide⟩]) unmarked_context_12_88843_667796 node_context_12_88843_667796
  intro a
  fin_cases a
  · exact context_13_355372_667691
  · exact context_13_355373_667752
  · exact context_13_355374_667786
  · exact context_13_355375_667795

theorem unmarked_context_11_22210_667797 : frontier 10 ⟨667797, by decide⟩
    (prefixCache 11 22210) (prefixPartial 11 22210) = false := by
  decide +kernel

theorem node_context_11_22210_667797 : EJMOriginalGlobalDAGData.nodes 10 ⟨667797, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨667458, by decide⟩,⟨667635, by decide⟩,⟨667796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22210_667797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22210 ⟨667797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22210
    ⟨667797, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨667458, by decide⟩,⟨667635, by decide⟩,⟨667796, by decide⟩]) unmarked_context_11_22210_667797 node_context_11_22210_667797
  intro a
  fin_cases a
  · exact context_12_88840_448748
  · exact context_12_88841_667458
  · exact context_12_88842_667635
  · exact context_12_88843_667796

theorem selected_cut_26399 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 88844) = some ⟨12, 1, 0, 448748, 88844, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88844_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88844 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 88844 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 88844, 1, 65536⟩
    (by decide) selected_cut_26399

theorem selected_cut_26400 : selected 8 ⟨667855, by decide⟩
    (prefixPartial 13 355380) = some ⟨13, 2, 0, 667855, 355380, 3377, 16384⟩ := by
  decide +kernel

theorem context_13_355380_667855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355380 ⟨667855, by decide⟩ :=
  accepted_of_selected 13 355380 ⟨667855, by decide⟩ ⟨13, 2, 0, 667855, 355380, 3377, 16384⟩
    (by decide) selected_cut_26400

theorem selected_cut_26401 : selected 8 ⟨667901, by decide⟩
    (prefixPartial 13 355381) = some ⟨13, 2, 0, 667901, 355381, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_355381_667901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355381 ⟨667901, by decide⟩ :=
  accepted_of_selected 13 355381 ⟨667901, by decide⟩ ⟨13, 2, 0, 667901, 355381, 2629, 16384⟩
    (by decide) selected_cut_26401

theorem selected_cut_26402 : selected 8 ⟨667926, by decide⟩
    (prefixPartial 13 355382) = some ⟨13, 2, 0, 667926, 355382, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_355382_667926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355382 ⟨667926, by decide⟩ :=
  accepted_of_selected 13 355382 ⟨667926, by decide⟩ ⟨13, 2, 0, 667926, 355382, 2117, 16384⟩
    (by decide) selected_cut_26402

theorem selected_cut_26403 : selected 8 ⟨667935, by decide⟩
    (prefixPartial 13 355383) = some ⟨13, 2, 0, 667935, 355383, 845, 16384⟩ := by
  decide +kernel

theorem context_13_355383_667935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355383 ⟨667935, by decide⟩ :=
  accepted_of_selected 13 355383 ⟨667935, by decide⟩ ⟨13, 2, 0, 667935, 355383, 845, 16384⟩
    (by decide) selected_cut_26403

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
