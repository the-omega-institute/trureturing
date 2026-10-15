/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover057
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_05570 : selected 9 ⟨172199, by decide⟩
    (prefixPartial 12 20627) = some ⟨12, 2, 0, 172199, 20627, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_20627_172199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20627 ⟨172199, by decide⟩ :=
  accepted_of_selected 12 20627 ⟨172199, by decide⟩ ⟨12, 2, 0, 172199, 20627, 1881, 65536⟩
    (by decide) selected_cut_05570

theorem unmarked_context_11_5156_172200 : frontier 10 ⟨172200, by decide⟩
    (prefixCache 11 5156) (prefixPartial 11 5156) = false := by
  decide +kernel

theorem node_context_11_5156_172200 : EJMOriginalGlobalDAGData.nodes 10 ⟨172200, by decide⟩ =
    .split (coordinate 11) (![⟨172121, by decide⟩,⟨172153, by decide⟩,⟨172174, by decide⟩,⟨172199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5156_172200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5156 ⟨172200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5156
    ⟨172200, by decide⟩ (by decide) (![⟨172121, by decide⟩,⟨172153, by decide⟩,⟨172174, by decide⟩,⟨172199, by decide⟩]) unmarked_context_11_5156_172200 node_context_11_5156_172200
  intro a
  fin_cases a
  · exact context_12_20624_172121
  · exact context_12_20625_172153
  · exact context_12_20626_172174
  · exact context_12_20627_172199

theorem selected_cut_05571 : selected 9 ⟨172234, by decide⟩
    (prefixPartial 12 20628) = some ⟨12, 2, 0, 172234, 20628, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_20628_172234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20628 ⟨172234, by decide⟩ :=
  accepted_of_selected 12 20628 ⟨172234, by decide⟩ ⟨12, 2, 0, 172234, 20628, 1353, 65536⟩
    (by decide) selected_cut_05571

theorem selected_cut_05572 : selected 9 ⟨172263, by decide⟩
    (prefixPartial 12 20629) = some ⟨12, 2, 0, 172263, 20629, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_20629_172263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20629 ⟨172263, by decide⟩ :=
  accepted_of_selected 12 20629 ⟨172263, by decide⟩ ⟨12, 2, 0, 172263, 20629, 1653, 65536⟩
    (by decide) selected_cut_05572

theorem selected_cut_05573 : selected 9 ⟨172286, by decide⟩
    (prefixPartial 12 20630) = some ⟨12, 2, 0, 172286, 20630, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_20630_172286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20630 ⟨172286, by decide⟩ :=
  accepted_of_selected 12 20630 ⟨172286, by decide⟩ ⟨12, 2, 0, 172286, 20630, 1465, 65536⟩
    (by decide) selected_cut_05573

theorem selected_cut_05574 : selected 9 ⟨172311, by decide⟩
    (prefixPartial 12 20631) = some ⟨12, 2, 0, 172311, 20631, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_20631_172311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20631 ⟨172311, by decide⟩ :=
  accepted_of_selected 12 20631 ⟨172311, by decide⟩ ⟨12, 2, 0, 172311, 20631, 1597, 65536⟩
    (by decide) selected_cut_05574

theorem unmarked_context_11_5157_172312 : frontier 10 ⟨172312, by decide⟩
    (prefixCache 11 5157) (prefixPartial 11 5157) = false := by
  decide +kernel

theorem node_context_11_5157_172312 : EJMOriginalGlobalDAGData.nodes 10 ⟨172312, by decide⟩ =
    .split (coordinate 11) (![⟨172234, by decide⟩,⟨172263, by decide⟩,⟨172286, by decide⟩,⟨172311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5157_172312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5157 ⟨172312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5157
    ⟨172312, by decide⟩ (by decide) (![⟨172234, by decide⟩,⟨172263, by decide⟩,⟨172286, by decide⟩,⟨172311, by decide⟩]) unmarked_context_11_5157_172312 node_context_11_5157_172312
  intro a
  fin_cases a
  · exact context_12_20628_172234
  · exact context_12_20629_172263
  · exact context_12_20630_172286
  · exact context_12_20631_172311

theorem selected_cut_05575 : selected 9 ⟨172341, by decide⟩
    (prefixPartial 12 20632) = some ⟨12, 2, 0, 172341, 20632, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_20632_172341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20632 ⟨172341, by decide⟩ :=
  accepted_of_selected 12 20632 ⟨172341, by decide⟩ ⟨12, 2, 0, 172341, 20632, 1369, 65536⟩
    (by decide) selected_cut_05575

theorem selected_cut_05576 : selected 9 ⟨172377, by decide⟩
    (prefixPartial 12 20633) = some ⟨12, 2, 0, 172377, 20633, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_20633_172377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20633 ⟨172377, by decide⟩ :=
  accepted_of_selected 12 20633 ⟨172377, by decide⟩ ⟨12, 2, 0, 172377, 20633, 1749, 65536⟩
    (by decide) selected_cut_05576

theorem selected_cut_05577 : selected 9 ⟨172398, by decide⟩
    (prefixPartial 12 20634) = some ⟨12, 2, 0, 172398, 20634, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_20634_172398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20634 ⟨172398, by decide⟩ :=
  accepted_of_selected 12 20634 ⟨172398, by decide⟩ ⟨12, 2, 0, 172398, 20634, 1533, 65536⟩
    (by decide) selected_cut_05577

theorem selected_cut_05578 : selected 9 ⟨172421, by decide⟩
    (prefixPartial 12 20635) = some ⟨12, 2, 0, 172421, 20635, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_20635_172421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20635 ⟨172421, by decide⟩ :=
  accepted_of_selected 12 20635 ⟨172421, by decide⟩ ⟨12, 2, 0, 172421, 20635, 1653, 65536⟩
    (by decide) selected_cut_05578

theorem unmarked_context_11_5158_172422 : frontier 10 ⟨172422, by decide⟩
    (prefixCache 11 5158) (prefixPartial 11 5158) = false := by
  decide +kernel

theorem node_context_11_5158_172422 : EJMOriginalGlobalDAGData.nodes 10 ⟨172422, by decide⟩ =
    .split (coordinate 11) (![⟨172341, by decide⟩,⟨172377, by decide⟩,⟨172398, by decide⟩,⟨172421, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5158_172422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5158 ⟨172422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5158
    ⟨172422, by decide⟩ (by decide) (![⟨172341, by decide⟩,⟨172377, by decide⟩,⟨172398, by decide⟩,⟨172421, by decide⟩]) unmarked_context_11_5158_172422 node_context_11_5158_172422
  intro a
  fin_cases a
  · exact context_12_20632_172341
  · exact context_12_20633_172377
  · exact context_12_20634_172398
  · exact context_12_20635_172421

theorem selected_cut_05579 : selected 9 ⟨172443, by decide⟩
    (prefixPartial 12 20636) = some ⟨12, 2, 0, 172443, 20636, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_20636_172443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20636 ⟨172443, by decide⟩ :=
  accepted_of_selected 12 20636 ⟨172443, by decide⟩ ⟨12, 2, 0, 172443, 20636, 1097, 65536⟩
    (by decide) selected_cut_05579

theorem selected_cut_05580 : selected 9 ⟨172467, by decide⟩
    (prefixPartial 12 20637) = some ⟨12, 2, 0, 172467, 20637, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_20637_172467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20637 ⟨172467, by decide⟩ :=
  accepted_of_selected 12 20637 ⟨172467, by decide⟩ ⟨12, 2, 0, 172467, 20637, 1433, 65536⟩
    (by decide) selected_cut_05580

theorem selected_cut_05581 : selected 9 ⟨172487, by decide⟩
    (prefixPartial 12 20638) = some ⟨12, 2, 0, 172487, 20638, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_20638_172487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20638 ⟨172487, by decide⟩ :=
  accepted_of_selected 12 20638 ⟨172487, by decide⟩ ⟨12, 2, 0, 172487, 20638, 1265, 65536⟩
    (by decide) selected_cut_05581

theorem selected_cut_05582 : selected 9 ⟨172507, by decide⟩
    (prefixPartial 12 20639) = some ⟨12, 2, 0, 172507, 20639, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_20639_172507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20639 ⟨172507, by decide⟩ :=
  accepted_of_selected 12 20639 ⟨172507, by decide⟩ ⟨12, 2, 0, 172507, 20639, 1357, 65536⟩
    (by decide) selected_cut_05582

theorem unmarked_context_11_5159_172508 : frontier 10 ⟨172508, by decide⟩
    (prefixCache 11 5159) (prefixPartial 11 5159) = false := by
  decide +kernel

theorem node_context_11_5159_172508 : EJMOriginalGlobalDAGData.nodes 10 ⟨172508, by decide⟩ =
    .split (coordinate 11) (![⟨172443, by decide⟩,⟨172467, by decide⟩,⟨172487, by decide⟩,⟨172507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5159_172508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5159 ⟨172508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5159
    ⟨172508, by decide⟩ (by decide) (![⟨172443, by decide⟩,⟨172467, by decide⟩,⟨172487, by decide⟩,⟨172507, by decide⟩]) unmarked_context_11_5159_172508 node_context_11_5159_172508
  intro a
  fin_cases a
  · exact context_12_20636_172443
  · exact context_12_20637_172467
  · exact context_12_20638_172487
  · exact context_12_20639_172507

theorem unmarked_context_10_1289_172509 : frontier 11 ⟨172509, by decide⟩
    (prefixCache 10 1289) (prefixPartial 10 1289) = false := by
  decide +kernel

theorem node_context_10_1289_172509 : EJMOriginalGlobalDAGData.nodes 11 ⟨172509, by decide⟩ =
    .split (coordinate 10) (![⟨172200, by decide⟩,⟨172312, by decide⟩,⟨172422, by decide⟩,⟨172508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1289_172509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1289 ⟨172509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1289
    ⟨172509, by decide⟩ (by decide) (![⟨172200, by decide⟩,⟨172312, by decide⟩,⟨172422, by decide⟩,⟨172508, by decide⟩]) unmarked_context_10_1289_172509 node_context_10_1289_172509
  intro a
  fin_cases a
  · exact context_11_5156_172200
  · exact context_11_5157_172312
  · exact context_11_5158_172422
  · exact context_11_5159_172508

theorem selected_cut_05583 : selected 10 ⟨172575, by decide⟩
    (prefixPartial 11 5160) = some ⟨11, 2, 0, 172575, 5160, 3933, 262144⟩ := by
  decide +kernel

theorem context_11_5160_172575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5160 ⟨172575, by decide⟩ :=
  accepted_of_selected 11 5160 ⟨172575, by decide⟩ ⟨11, 2, 0, 172575, 5160, 3933, 262144⟩
    (by decide) selected_cut_05583

theorem selected_cut_05584 : selected 10 ⟨172628, by decide⟩
    (prefixPartial 11 5161) = some ⟨11, 2, 0, 172628, 5161, 2833, 262144⟩ := by
  decide +kernel

theorem context_11_5161_172628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5161 ⟨172628, by decide⟩ :=
  accepted_of_selected 11 5161 ⟨172628, by decide⟩ ⟨11, 2, 0, 172628, 5161, 2833, 262144⟩
    (by decide) selected_cut_05584

theorem selected_cut_05585 : selected 10 ⟨172689, by decide⟩
    (prefixPartial 11 5162) = some ⟨11, 2, 0, 172689, 5162, 3025, 262144⟩ := by
  decide +kernel

theorem context_11_5162_172689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5162 ⟨172689, by decide⟩ :=
  accepted_of_selected 11 5162 ⟨172689, by decide⟩ ⟨11, 2, 0, 172689, 5162, 3025, 262144⟩
    (by decide) selected_cut_05585

theorem selected_cut_05586 : selected 10 ⟨172749, by decide⟩
    (prefixPartial 11 5163) = some ⟨11, 2, 0, 172749, 5163, 2533, 262144⟩ := by
  decide +kernel

theorem context_11_5163_172749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5163 ⟨172749, by decide⟩ :=
  accepted_of_selected 11 5163 ⟨172749, by decide⟩ ⟨11, 2, 0, 172749, 5163, 2533, 262144⟩
    (by decide) selected_cut_05586

theorem unmarked_context_10_1290_172750 : frontier 11 ⟨172750, by decide⟩
    (prefixCache 10 1290) (prefixPartial 10 1290) = false := by
  decide +kernel

theorem node_context_10_1290_172750 : EJMOriginalGlobalDAGData.nodes 11 ⟨172750, by decide⟩ =
    .split (coordinate 10) (![⟨172575, by decide⟩,⟨172628, by decide⟩,⟨172689, by decide⟩,⟨172749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1290_172750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1290 ⟨172750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1290
    ⟨172750, by decide⟩ (by decide) (![⟨172575, by decide⟩,⟨172628, by decide⟩,⟨172689, by decide⟩,⟨172749, by decide⟩]) unmarked_context_10_1290_172750 node_context_10_1290_172750
  intro a
  fin_cases a
  · exact context_11_5160_172575
  · exact context_11_5161_172628
  · exact context_11_5162_172689
  · exact context_11_5163_172749

theorem selected_cut_05587 : selected 10 ⟨172786, by decide⟩
    (prefixPartial 11 5164) = some ⟨11, 2, 0, 172786, 5164, 1901, 262144⟩ := by
  decide +kernel

theorem context_11_5164_172786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5164 ⟨172786, by decide⟩ :=
  accepted_of_selected 11 5164 ⟨172786, by decide⟩ ⟨11, 2, 0, 172786, 5164, 1901, 262144⟩
    (by decide) selected_cut_05587

theorem selected_cut_05588 : selected 10 ⟨172813, by decide⟩
    (prefixPartial 11 5165) = some ⟨11, 2, 0, 172813, 5165, 1281, 262144⟩ := by
  decide +kernel

theorem context_11_5165_172813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5165 ⟨172813, by decide⟩ :=
  accepted_of_selected 11 5165 ⟨172813, by decide⟩ ⟨11, 2, 0, 172813, 5165, 1281, 262144⟩
    (by decide) selected_cut_05588

theorem selected_cut_05589 : selected 10 ⟨172843, by decide⟩
    (prefixPartial 11 5166) = some ⟨11, 2, 0, 172843, 5166, 909, 262144⟩ := by
  decide +kernel

theorem context_11_5166_172843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5166 ⟨172843, by decide⟩ :=
  accepted_of_selected 11 5166 ⟨172843, by decide⟩ ⟨11, 2, 0, 172843, 5166, 909, 262144⟩
    (by decide) selected_cut_05589

theorem selected_cut_05590 : selected 10 ⟨172862, by decide⟩
    (prefixPartial 11 5167) = some ⟨11, 2, 0, 172862, 5167, 361, 262144⟩ := by
  decide +kernel

theorem context_11_5167_172862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5167 ⟨172862, by decide⟩ :=
  accepted_of_selected 11 5167 ⟨172862, by decide⟩ ⟨11, 2, 0, 172862, 5167, 361, 262144⟩
    (by decide) selected_cut_05590

theorem unmarked_context_10_1291_172863 : frontier 11 ⟨172863, by decide⟩
    (prefixCache 10 1291) (prefixPartial 10 1291) = false := by
  decide +kernel

theorem node_context_10_1291_172863 : EJMOriginalGlobalDAGData.nodes 11 ⟨172863, by decide⟩ =
    .split (coordinate 10) (![⟨172786, by decide⟩,⟨172813, by decide⟩,⟨172843, by decide⟩,⟨172862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1291_172863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1291 ⟨172863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1291
    ⟨172863, by decide⟩ (by decide) (![⟨172786, by decide⟩,⟨172813, by decide⟩,⟨172843, by decide⟩,⟨172862, by decide⟩]) unmarked_context_10_1291_172863 node_context_10_1291_172863
  intro a
  fin_cases a
  · exact context_11_5164_172786
  · exact context_11_5165_172813
  · exact context_11_5166_172843
  · exact context_11_5167_172862

theorem unmarked_context_9_322_172864 : frontier 12 ⟨172864, by decide⟩
    (prefixCache 9 322) (prefixPartial 9 322) = false := by
  decide +kernel

theorem node_context_9_322_172864 : EJMOriginalGlobalDAGData.nodes 12 ⟨172864, by decide⟩ =
    .split (coordinate 9) (![⟨172073, by decide⟩,⟨172509, by decide⟩,⟨172750, by decide⟩,⟨172863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_322_172864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 322 ⟨172864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 322
    ⟨172864, by decide⟩ (by decide) (![⟨172073, by decide⟩,⟨172509, by decide⟩,⟨172750, by decide⟩,⟨172863, by decide⟩]) unmarked_context_9_322_172864 node_context_9_322_172864
  intro a
  fin_cases a
  · exact context_10_1288_172073
  · exact context_10_1289_172509
  · exact context_10_1290_172750
  · exact context_10_1291_172863

theorem selected_cut_05591 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 323) = some ⟨9, 1, 0, 4601, 323, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_323_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 323 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 323 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 323, 1, 4194304⟩
    (by decide) selected_cut_05591

theorem unmarked_context_8_80_172865 : frontier 13 ⟨172865, by decide⟩
    (prefixCache 8 80) (prefixPartial 8 80) = false := by
  decide +kernel

theorem node_context_8_80_172865 : EJMOriginalGlobalDAGData.nodes 13 ⟨172865, by decide⟩ =
    .split (coordinate 8) (![⟨169789, by decide⟩,⟨171603, by decide⟩,⟨172864, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_80_172865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 80 ⟨172865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 80
    ⟨172865, by decide⟩ (by decide) (![⟨169789, by decide⟩,⟨171603, by decide⟩,⟨172864, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_80_172865 node_context_8_80_172865
  intro a
  fin_cases a
  · exact context_9_320_169789
  · exact context_9_321_171603
  · exact context_9_322_172864
  · exact context_9_323_4601

theorem selected_cut_05592 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 5184) = some ⟨11, 1, 0, 167448, 5184, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5184_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5184 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 5184 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 5184, 1, 262144⟩
    (by decide) selected_cut_05592

theorem selected_cut_05593 : selected 9 ⟨172944, by decide⟩
    (prefixPartial 12 20740) = some ⟨12, 2, 0, 172944, 20740, 4089, 65536⟩ := by
  decide +kernel

theorem context_12_20740_172944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20740 ⟨172944, by decide⟩ :=
  accepted_of_selected 12 20740 ⟨172944, by decide⟩ ⟨12, 2, 0, 172944, 20740, 4089, 65536⟩
    (by decide) selected_cut_05593

theorem selected_cut_05594 : selected 8 ⟨172995, by decide⟩
    (prefixPartial 13 82964) = some ⟨13, 2, 0, 172995, 82964, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_82964_172995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82964 ⟨172995, by decide⟩ :=
  accepted_of_selected 13 82964 ⟨172995, by decide⟩ ⟨13, 2, 0, 172995, 82964, 2405, 16384⟩
    (by decide) selected_cut_05594

theorem selected_cut_05595 : selected 8 ⟨173030, by decide⟩
    (prefixPartial 13 82965) = some ⟨13, 2, 0, 173030, 82965, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_82965_173030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82965 ⟨173030, by decide⟩ :=
  accepted_of_selected 13 82965 ⟨173030, by decide⟩ ⟨13, 2, 0, 173030, 82965, 1941, 16384⟩
    (by decide) selected_cut_05595

theorem selected_cut_05596 : selected 8 ⟨173047, by decide⟩
    (prefixPartial 13 82966) = some ⟨13, 2, 0, 173047, 82966, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_82966_173047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82966 ⟨173047, by decide⟩ :=
  accepted_of_selected 13 82966 ⟨173047, by decide⟩ ⟨13, 2, 0, 173047, 82966, 2001, 16384⟩
    (by decide) selected_cut_05596

theorem selected_cut_05597 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 82967) = some ⟨13, 1, 0, 414, 82967, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82967_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82967 ⟨414, by decide⟩ :=
  accepted_of_selected 13 82967 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 82967, 1, 16384⟩
    (by decide) selected_cut_05597

theorem unmarked_context_12_20741_173048 : frontier 9 ⟨173048, by decide⟩
    (prefixCache 12 20741) (prefixPartial 12 20741) = false := by
  decide +kernel

theorem node_context_12_20741_173048 : EJMOriginalGlobalDAGData.nodes 9 ⟨173048, by decide⟩ =
    .split (coordinate 12) (![⟨172995, by decide⟩,⟨173030, by decide⟩,⟨173047, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20741_173048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20741 ⟨173048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20741
    ⟨173048, by decide⟩ (by decide) (![⟨172995, by decide⟩,⟨173030, by decide⟩,⟨173047, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_20741_173048 node_context_12_20741_173048
  intro a
  fin_cases a
  · exact context_13_82964_172995
  · exact context_13_82965_173030
  · exact context_13_82966_173047
  · exact context_13_82967_414

theorem selected_cut_05598 : selected 8 ⟨173105, by decide⟩
    (prefixPartial 13 82968) = some ⟨13, 2, 0, 173105, 82968, 3353, 16384⟩ := by
  decide +kernel

theorem context_13_82968_173105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82968 ⟨173105, by decide⟩ :=
  accepted_of_selected 13 82968 ⟨173105, by decide⟩ ⟨13, 2, 0, 173105, 82968, 3353, 16384⟩
    (by decide) selected_cut_05598

theorem selected_cut_05599 : selected 8 ⟨173130, by decide⟩
    (prefixPartial 13 82969) = some ⟨13, 2, 0, 173130, 82969, 2981, 16384⟩ := by
  decide +kernel

theorem context_13_82969_173130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82969 ⟨173130, by decide⟩ :=
  accepted_of_selected 13 82969 ⟨173130, by decide⟩ ⟨13, 2, 0, 173130, 82969, 2981, 16384⟩
    (by decide) selected_cut_05599

theorem selected_cut_05600 : selected 8 ⟨173150, by decide⟩
    (prefixPartial 13 82970) = some ⟨13, 2, 0, 173150, 82970, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_82970_173150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82970 ⟨173150, by decide⟩ :=
  accepted_of_selected 13 82970 ⟨173150, by decide⟩ ⟨13, 2, 0, 173150, 82970, 1845, 16384⟩
    (by decide) selected_cut_05600

theorem selected_cut_05601 : selected 8 ⟨173159, by decide⟩
    (prefixPartial 13 82971) = some ⟨13, 2, 0, 173159, 82971, 885, 16384⟩ := by
  decide +kernel

theorem context_13_82971_173159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82971 ⟨173159, by decide⟩ :=
  accepted_of_selected 13 82971 ⟨173159, by decide⟩ ⟨13, 2, 0, 173159, 82971, 885, 16384⟩
    (by decide) selected_cut_05601

theorem unmarked_context_12_20742_173160 : frontier 9 ⟨173160, by decide⟩
    (prefixCache 12 20742) (prefixPartial 12 20742) = false := by
  decide +kernel

theorem node_context_12_20742_173160 : EJMOriginalGlobalDAGData.nodes 9 ⟨173160, by decide⟩ =
    .split (coordinate 12) (![⟨173105, by decide⟩,⟨173130, by decide⟩,⟨173150, by decide⟩,⟨173159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20742_173160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20742 ⟨173160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20742
    ⟨173160, by decide⟩ (by decide) (![⟨173105, by decide⟩,⟨173130, by decide⟩,⟨173150, by decide⟩,⟨173159, by decide⟩]) unmarked_context_12_20742_173160 node_context_12_20742_173160
  intro a
  fin_cases a
  · exact context_13_82968_173105
  · exact context_13_82969_173130
  · exact context_13_82970_173150
  · exact context_13_82971_173159

theorem selected_cut_05602 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20743) = some ⟨12, 1, 0, 893, 20743, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20743_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20743 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20743 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20743, 1, 65536⟩
    (by decide) selected_cut_05602

theorem unmarked_context_11_5185_173161 : frontier 10 ⟨173161, by decide⟩
    (prefixCache 11 5185) (prefixPartial 11 5185) = false := by
  decide +kernel

theorem node_context_11_5185_173161 : EJMOriginalGlobalDAGData.nodes 10 ⟨173161, by decide⟩ =
    .split (coordinate 11) (![⟨172944, by decide⟩,⟨173048, by decide⟩,⟨173160, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5185_173161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5185 ⟨173161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5185
    ⟨173161, by decide⟩ (by decide) (![⟨172944, by decide⟩,⟨173048, by decide⟩,⟨173160, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5185_173161 node_context_11_5185_173161
  intro a
  fin_cases a
  · exact context_12_20740_172944
  · exact context_12_20741_173048
  · exact context_12_20742_173160
  · exact context_12_20743_893

theorem selected_cut_05603 : selected 8 ⟨173210, by decide⟩
    (prefixPartial 13 82976) = some ⟨13, 2, 0, 173210, 82976, 3237, 16384⟩ := by
  decide +kernel

theorem context_13_82976_173210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82976 ⟨173210, by decide⟩ :=
  accepted_of_selected 13 82976 ⟨173210, by decide⟩ ⟨13, 2, 0, 173210, 82976, 3237, 16384⟩
    (by decide) selected_cut_05603

theorem selected_cut_05604 : selected 8 ⟨173241, by decide⟩
    (prefixPartial 13 82977) = some ⟨13, 2, 0, 173241, 82977, 2957, 16384⟩ := by
  decide +kernel

theorem context_13_82977_173241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82977 ⟨173241, by decide⟩ :=
  accepted_of_selected 13 82977 ⟨173241, by decide⟩ ⟨13, 2, 0, 173241, 82977, 2957, 16384⟩
    (by decide) selected_cut_05604

theorem selected_cut_05605 : selected 8 ⟨173258, by decide⟩
    (prefixPartial 13 82978) = some ⟨13, 2, 0, 173258, 82978, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_82978_173258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82978 ⟨173258, by decide⟩ :=
  accepted_of_selected 13 82978 ⟨173258, by decide⟩ ⟨13, 2, 0, 173258, 82978, 2197, 16384⟩
    (by decide) selected_cut_05605

theorem selected_cut_05606 : selected 8 ⟨173264, by decide⟩
    (prefixPartial 13 82979) = some ⟨13, 2, 0, 173264, 82979, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_82979_173264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82979 ⟨173264, by decide⟩ :=
  accepted_of_selected 13 82979 ⟨173264, by decide⟩ ⟨13, 2, 0, 173264, 82979, 1053, 16384⟩
    (by decide) selected_cut_05606

theorem unmarked_context_12_20744_173265 : frontier 9 ⟨173265, by decide⟩
    (prefixCache 12 20744) (prefixPartial 12 20744) = false := by
  decide +kernel

theorem node_context_12_20744_173265 : EJMOriginalGlobalDAGData.nodes 9 ⟨173265, by decide⟩ =
    .split (coordinate 12) (![⟨173210, by decide⟩,⟨173241, by decide⟩,⟨173258, by decide⟩,⟨173264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20744_173265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20744 ⟨173265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20744
    ⟨173265, by decide⟩ (by decide) (![⟨173210, by decide⟩,⟨173241, by decide⟩,⟨173258, by decide⟩,⟨173264, by decide⟩]) unmarked_context_12_20744_173265 node_context_12_20744_173265
  intro a
  fin_cases a
  · exact context_13_82976_173210
  · exact context_13_82977_173241
  · exact context_13_82978_173258
  · exact context_13_82979_173264

theorem selected_cut_05607 : selected 8 ⟨173306, by decide⟩
    (prefixPartial 13 82980) = some ⟨13, 2, 0, 173306, 82980, 2949, 16384⟩ := by
  decide +kernel

theorem context_13_82980_173306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82980 ⟨173306, by decide⟩ :=
  accepted_of_selected 13 82980 ⟨173306, by decide⟩ ⟨13, 2, 0, 173306, 82980, 2949, 16384⟩
    (by decide) selected_cut_05607

theorem selected_cut_05608 : selected 8 ⟨173328, by decide⟩
    (prefixPartial 13 82981) = some ⟨13, 2, 0, 173328, 82981, 3045, 16384⟩ := by
  decide +kernel

theorem context_13_82981_173328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82981 ⟨173328, by decide⟩ :=
  accepted_of_selected 13 82981 ⟨173328, by decide⟩ ⟨13, 2, 0, 173328, 82981, 3045, 16384⟩
    (by decide) selected_cut_05608

theorem selected_cut_05609 : selected 8 ⟨173347, by decide⟩
    (prefixPartial 13 82982) = some ⟨13, 2, 0, 173347, 82982, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_82982_173347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82982 ⟨173347, by decide⟩ :=
  accepted_of_selected 13 82982 ⟨173347, by decide⟩ ⟨13, 2, 0, 173347, 82982, 2177, 16384⟩
    (by decide) selected_cut_05609

theorem selected_cut_05610 : selected 8 ⟨173355, by decide⟩
    (prefixPartial 13 82983) = some ⟨13, 2, 0, 173355, 82983, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_82983_173355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82983 ⟨173355, by decide⟩ :=
  accepted_of_selected 13 82983 ⟨173355, by decide⟩ ⟨13, 2, 0, 173355, 82983, 1105, 16384⟩
    (by decide) selected_cut_05610

theorem unmarked_context_12_20745_173356 : frontier 9 ⟨173356, by decide⟩
    (prefixCache 12 20745) (prefixPartial 12 20745) = false := by
  decide +kernel

theorem node_context_12_20745_173356 : EJMOriginalGlobalDAGData.nodes 9 ⟨173356, by decide⟩ =
    .split (coordinate 12) (![⟨173306, by decide⟩,⟨173328, by decide⟩,⟨173347, by decide⟩,⟨173355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20745_173356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20745 ⟨173356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20745
    ⟨173356, by decide⟩ (by decide) (![⟨173306, by decide⟩,⟨173328, by decide⟩,⟨173347, by decide⟩,⟨173355, by decide⟩]) unmarked_context_12_20745_173356 node_context_12_20745_173356
  intro a
  fin_cases a
  · exact context_13_82980_173306
  · exact context_13_82981_173328
  · exact context_13_82982_173347
  · exact context_13_82983_173355

theorem selected_cut_05611 : selected 8 ⟨173413, by decide⟩
    (prefixPartial 13 82984) = some ⟨13, 2, 0, 173413, 82984, 3557, 16384⟩ := by
  decide +kernel

theorem context_13_82984_173413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82984 ⟨173413, by decide⟩ :=
  accepted_of_selected 13 82984 ⟨173413, by decide⟩ ⟨13, 2, 0, 173413, 82984, 3557, 16384⟩
    (by decide) selected_cut_05611

theorem selected_cut_05612 : selected 8 ⟨173459, by decide⟩
    (prefixPartial 13 82985) = some ⟨13, 2, 0, 173459, 82985, 3681, 16384⟩ := by
  decide +kernel

theorem context_13_82985_173459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82985 ⟨173459, by decide⟩ :=
  accepted_of_selected 13 82985 ⟨173459, by decide⟩ ⟨13, 2, 0, 173459, 82985, 3681, 16384⟩
    (by decide) selected_cut_05612

theorem selected_cut_05613 : selected 8 ⟨173478, by decide⟩
    (prefixPartial 13 82986) = some ⟨13, 2, 0, 173478, 82986, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_82986_173478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82986 ⟨173478, by decide⟩ :=
  accepted_of_selected 13 82986 ⟨173478, by decide⟩ ⟨13, 2, 0, 173478, 82986, 2237, 16384⟩
    (by decide) selected_cut_05613

theorem selected_cut_05614 : selected 8 ⟨173485, by decide⟩
    (prefixPartial 13 82987) = some ⟨13, 2, 0, 173485, 82987, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_82987_173485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82987 ⟨173485, by decide⟩ :=
  accepted_of_selected 13 82987 ⟨173485, by decide⟩ ⟨13, 2, 0, 173485, 82987, 1025, 16384⟩
    (by decide) selected_cut_05614

theorem unmarked_context_12_20746_173486 : frontier 9 ⟨173486, by decide⟩
    (prefixCache 12 20746) (prefixPartial 12 20746) = false := by
  decide +kernel

theorem node_context_12_20746_173486 : EJMOriginalGlobalDAGData.nodes 9 ⟨173486, by decide⟩ =
    .split (coordinate 12) (![⟨173413, by decide⟩,⟨173459, by decide⟩,⟨173478, by decide⟩,⟨173485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20746_173486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20746 ⟨173486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20746
    ⟨173486, by decide⟩ (by decide) (![⟨173413, by decide⟩,⟨173459, by decide⟩,⟨173478, by decide⟩,⟨173485, by decide⟩]) unmarked_context_12_20746_173486 node_context_12_20746_173486
  intro a
  fin_cases a
  · exact context_13_82984_173413
  · exact context_13_82985_173459
  · exact context_13_82986_173478
  · exact context_13_82987_173485

theorem selected_cut_05615 : selected 8 ⟨173533, by decide⟩
    (prefixPartial 13 82988) = some ⟨13, 2, 0, 173533, 82988, 3381, 16384⟩ := by
  decide +kernel

theorem context_13_82988_173533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82988 ⟨173533, by decide⟩ :=
  accepted_of_selected 13 82988 ⟨173533, by decide⟩ ⟨13, 2, 0, 173533, 82988, 3381, 16384⟩
    (by decide) selected_cut_05615

theorem selected_cut_05616 : selected 8 ⟨173588, by decide⟩
    (prefixPartial 13 82989) = some ⟨13, 2, 0, 173588, 82989, 3725, 16384⟩ := by
  decide +kernel

theorem context_13_82989_173588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82989 ⟨173588, by decide⟩ :=
  accepted_of_selected 13 82989 ⟨173588, by decide⟩ ⟨13, 2, 0, 173588, 82989, 3725, 16384⟩
    (by decide) selected_cut_05616

theorem selected_cut_05617 : selected 8 ⟨173608, by decide⟩
    (prefixPartial 13 82990) = some ⟨13, 2, 0, 173608, 82990, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_82990_173608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82990 ⟨173608, by decide⟩ :=
  accepted_of_selected 13 82990 ⟨173608, by decide⟩ ⟨13, 2, 0, 173608, 82990, 2177, 16384⟩
    (by decide) selected_cut_05617

theorem selected_cut_05618 : selected 8 ⟨173615, by decide⟩
    (prefixPartial 13 82991) = some ⟨13, 2, 0, 173615, 82991, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_82991_173615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82991 ⟨173615, by decide⟩ :=
  accepted_of_selected 13 82991 ⟨173615, by decide⟩ ⟨13, 2, 0, 173615, 82991, 1181, 16384⟩
    (by decide) selected_cut_05618

theorem unmarked_context_12_20747_173616 : frontier 9 ⟨173616, by decide⟩
    (prefixCache 12 20747) (prefixPartial 12 20747) = false := by
  decide +kernel

theorem node_context_12_20747_173616 : EJMOriginalGlobalDAGData.nodes 9 ⟨173616, by decide⟩ =
    .split (coordinate 12) (![⟨173533, by decide⟩,⟨173588, by decide⟩,⟨173608, by decide⟩,⟨173615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20747_173616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20747 ⟨173616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20747
    ⟨173616, by decide⟩ (by decide) (![⟨173533, by decide⟩,⟨173588, by decide⟩,⟨173608, by decide⟩,⟨173615, by decide⟩]) unmarked_context_12_20747_173616 node_context_12_20747_173616
  intro a
  fin_cases a
  · exact context_13_82988_173533
  · exact context_13_82989_173588
  · exact context_13_82990_173608
  · exact context_13_82991_173615

theorem unmarked_context_11_5186_173617 : frontier 10 ⟨173617, by decide⟩
    (prefixCache 11 5186) (prefixPartial 11 5186) = false := by
  decide +kernel

theorem node_context_11_5186_173617 : EJMOriginalGlobalDAGData.nodes 10 ⟨173617, by decide⟩ =
    .split (coordinate 11) (![⟨173265, by decide⟩,⟨173356, by decide⟩,⟨173486, by decide⟩,⟨173616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5186_173617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5186 ⟨173617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5186
    ⟨173617, by decide⟩ (by decide) (![⟨173265, by decide⟩,⟨173356, by decide⟩,⟨173486, by decide⟩,⟨173616, by decide⟩]) unmarked_context_11_5186_173617 node_context_11_5186_173617
  intro a
  fin_cases a
  · exact context_12_20744_173265
  · exact context_12_20745_173356
  · exact context_12_20746_173486
  · exact context_12_20747_173616

theorem selected_cut_05619 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5187) = some ⟨11, 1, 0, 1736, 5187, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5187_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5187 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5187 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5187, 1, 262144⟩
    (by decide) selected_cut_05619

theorem unmarked_context_10_1296_173618 : frontier 11 ⟨173618, by decide⟩
    (prefixCache 10 1296) (prefixPartial 10 1296) = false := by
  decide +kernel

theorem node_context_10_1296_173618 : EJMOriginalGlobalDAGData.nodes 11 ⟨173618, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨173161, by decide⟩,⟨173617, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1296_173618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1296 ⟨173618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1296
    ⟨173618, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨173161, by decide⟩,⟨173617, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1296_173618 node_context_10_1296_173618
  intro a
  fin_cases a
  · exact context_11_5184_167448
  · exact context_11_5185_173161
  · exact context_11_5186_173617
  · exact context_11_5187_1736

theorem selected_cut_05620 : selected 9 ⟨173667, by decide⟩
    (prefixPartial 12 20752) = some ⟨12, 2, 0, 173667, 20752, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_20752_173667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20752 ⟨173667, by decide⟩ :=
  accepted_of_selected 12 20752 ⟨173667, by decide⟩ ⟨12, 2, 0, 173667, 20752, 2013, 65536⟩
    (by decide) selected_cut_05620

theorem selected_cut_05621 : selected 9 ⟨173711, by decide⟩
    (prefixPartial 12 20753) = some ⟨12, 2, 0, 173711, 20753, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_20753_173711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20753 ⟨173711, by decide⟩ :=
  accepted_of_selected 12 20753 ⟨173711, by decide⟩ ⟨12, 2, 0, 173711, 20753, 1925, 65536⟩
    (by decide) selected_cut_05621

theorem selected_cut_05622 : selected 8 ⟨173734, by decide⟩
    (prefixPartial 13 83016) = some ⟨13, 2, 0, 173734, 83016, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_83016_173734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83016 ⟨173734, by decide⟩ :=
  accepted_of_selected 13 83016 ⟨173734, by decide⟩ ⟨13, 2, 0, 173734, 83016, 1481, 16384⟩
    (by decide) selected_cut_05622

theorem selected_cut_05623 : selected 8 ⟨173767, by decide⟩
    (prefixPartial 13 83017) = some ⟨13, 2, 0, 173767, 83017, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_83017_173767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83017 ⟨173767, by decide⟩ :=
  accepted_of_selected 13 83017 ⟨173767, by decide⟩ ⟨13, 2, 0, 173767, 83017, 1881, 16384⟩
    (by decide) selected_cut_05623

theorem selected_cut_05624 : selected 8 ⟨173788, by decide⟩
    (prefixPartial 13 83018) = some ⟨13, 2, 0, 173788, 83018, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_83018_173788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83018 ⟨173788, by decide⟩ :=
  accepted_of_selected 13 83018 ⟨173788, by decide⟩ ⟨13, 2, 0, 173788, 83018, 1285, 16384⟩
    (by decide) selected_cut_05624

theorem selected_cut_05625 : selected 8 ⟨173793, by decide⟩
    (prefixPartial 13 83019) = some ⟨13, 2, 0, 173793, 83019, 649, 16384⟩ := by
  decide +kernel

theorem context_13_83019_173793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83019 ⟨173793, by decide⟩ :=
  accepted_of_selected 13 83019 ⟨173793, by decide⟩ ⟨13, 2, 0, 173793, 83019, 649, 16384⟩
    (by decide) selected_cut_05625

theorem unmarked_context_12_20754_173794 : frontier 9 ⟨173794, by decide⟩
    (prefixCache 12 20754) (prefixPartial 12 20754) = false := by
  decide +kernel

theorem node_context_12_20754_173794 : EJMOriginalGlobalDAGData.nodes 9 ⟨173794, by decide⟩ =
    .split (coordinate 12) (![⟨173734, by decide⟩,⟨173767, by decide⟩,⟨173788, by decide⟩,⟨173793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20754_173794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20754 ⟨173794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20754
    ⟨173794, by decide⟩ (by decide) (![⟨173734, by decide⟩,⟨173767, by decide⟩,⟨173788, by decide⟩,⟨173793, by decide⟩]) unmarked_context_12_20754_173794 node_context_12_20754_173794
  intro a
  fin_cases a
  · exact context_13_83016_173734
  · exact context_13_83017_173767
  · exact context_13_83018_173788
  · exact context_13_83019_173793

theorem selected_cut_05626 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20755) = some ⟨12, 1, 0, 893, 20755, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20755_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20755 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20755 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20755, 1, 65536⟩
    (by decide) selected_cut_05626

theorem unmarked_context_11_5188_173795 : frontier 10 ⟨173795, by decide⟩
    (prefixCache 11 5188) (prefixPartial 11 5188) = false := by
  decide +kernel

theorem node_context_11_5188_173795 : EJMOriginalGlobalDAGData.nodes 10 ⟨173795, by decide⟩ =
    .split (coordinate 11) (![⟨173667, by decide⟩,⟨173711, by decide⟩,⟨173794, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5188_173795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5188 ⟨173795, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5188
    ⟨173795, by decide⟩ (by decide) (![⟨173667, by decide⟩,⟨173711, by decide⟩,⟨173794, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5188_173795 node_context_11_5188_173795
  intro a
  fin_cases a
  · exact context_12_20752_173667
  · exact context_12_20753_173711
  · exact context_12_20754_173794
  · exact context_12_20755_893

theorem selected_cut_05627 : selected 9 ⟨173825, by decide⟩
    (prefixPartial 12 20756) = some ⟨12, 2, 0, 173825, 20756, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_20756_173825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20756 ⟨173825, by decide⟩ :=
  accepted_of_selected 12 20756 ⟨173825, by decide⟩ ⟨12, 2, 0, 173825, 20756, 1945, 65536⟩
    (by decide) selected_cut_05627

theorem selected_cut_05628 : selected 9 ⟨173962, by decide⟩
    (prefixPartial 12 20757) = some ⟨12, 2, 0, 173962, 20757, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_20757_173962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20757 ⟨173962, by decide⟩ :=
  accepted_of_selected 12 20757 ⟨173962, by decide⟩ ⟨12, 2, 0, 173962, 20757, 2225, 65536⟩
    (by decide) selected_cut_05628

theorem selected_cut_05629 : selected 8 ⟨173984, by decide⟩
    (prefixPartial 13 83032) = some ⟨13, 2, 0, 173984, 83032, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_83032_173984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83032 ⟨173984, by decide⟩ :=
  accepted_of_selected 13 83032 ⟨173984, by decide⟩ ⟨13, 2, 0, 173984, 83032, 1201, 16384⟩
    (by decide) selected_cut_05629

theorem selected_cut_05630 : selected 8 ⟨174009, by decide⟩
    (prefixPartial 13 83033) = some ⟨13, 2, 0, 174009, 83033, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_83033_174009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83033 ⟨174009, by decide⟩ :=
  accepted_of_selected 13 83033 ⟨174009, by decide⟩ ⟨13, 2, 0, 174009, 83033, 1837, 16384⟩
    (by decide) selected_cut_05630

theorem selected_cut_05631 : selected 8 ⟨174026, by decide⟩
    (prefixPartial 13 83034) = some ⟨13, 2, 0, 174026, 83034, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_83034_174026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83034 ⟨174026, by decide⟩ :=
  accepted_of_selected 13 83034 ⟨174026, by decide⟩ ⟨13, 2, 0, 174026, 83034, 1065, 16384⟩
    (by decide) selected_cut_05631

theorem selected_cut_05632 : selected 8 ⟨174031, by decide⟩
    (prefixPartial 13 83035) = some ⟨13, 2, 0, 174031, 83035, 645, 16384⟩ := by
  decide +kernel

theorem context_13_83035_174031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83035 ⟨174031, by decide⟩ :=
  accepted_of_selected 13 83035 ⟨174031, by decide⟩ ⟨13, 2, 0, 174031, 83035, 645, 16384⟩
    (by decide) selected_cut_05632

theorem unmarked_context_12_20758_174032 : frontier 9 ⟨174032, by decide⟩
    (prefixCache 12 20758) (prefixPartial 12 20758) = false := by
  decide +kernel

theorem node_context_12_20758_174032 : EJMOriginalGlobalDAGData.nodes 9 ⟨174032, by decide⟩ =
    .split (coordinate 12) (![⟨173984, by decide⟩,⟨174009, by decide⟩,⟨174026, by decide⟩,⟨174031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20758_174032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20758 ⟨174032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20758
    ⟨174032, by decide⟩ (by decide) (![⟨173984, by decide⟩,⟨174009, by decide⟩,⟨174026, by decide⟩,⟨174031, by decide⟩]) unmarked_context_12_20758_174032 node_context_12_20758_174032
  intro a
  fin_cases a
  · exact context_13_83032_173984
  · exact context_13_83033_174009
  · exact context_13_83034_174026
  · exact context_13_83035_174031

theorem selected_cut_05633 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20759) = some ⟨12, 1, 0, 893, 20759, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20759_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20759 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20759 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20759, 1, 65536⟩
    (by decide) selected_cut_05633

theorem unmarked_context_11_5189_174033 : frontier 10 ⟨174033, by decide⟩
    (prefixCache 11 5189) (prefixPartial 11 5189) = false := by
  decide +kernel

theorem node_context_11_5189_174033 : EJMOriginalGlobalDAGData.nodes 10 ⟨174033, by decide⟩ =
    .split (coordinate 11) (![⟨173825, by decide⟩,⟨173962, by decide⟩,⟨174032, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5189_174033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5189 ⟨174033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5189
    ⟨174033, by decide⟩ (by decide) (![⟨173825, by decide⟩,⟨173962, by decide⟩,⟨174032, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5189_174033 node_context_11_5189_174033
  intro a
  fin_cases a
  · exact context_12_20756_173825
  · exact context_12_20757_173962
  · exact context_12_20758_174032
  · exact context_12_20759_893

theorem selected_cut_05634 : selected 8 ⟨174060, by decide⟩
    (prefixPartial 13 83040) = some ⟨13, 2, 0, 174060, 83040, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_83040_174060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83040 ⟨174060, by decide⟩ :=
  accepted_of_selected 13 83040 ⟨174060, by decide⟩ ⟨13, 2, 0, 174060, 83040, 1449, 16384⟩
    (by decide) selected_cut_05634

theorem selected_cut_05635 : selected 8 ⟨174091, by decide⟩
    (prefixPartial 13 83041) = some ⟨13, 2, 0, 174091, 83041, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_83041_174091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83041 ⟨174091, by decide⟩ :=
  accepted_of_selected 13 83041 ⟨174091, by decide⟩ ⟨13, 2, 0, 174091, 83041, 1645, 16384⟩
    (by decide) selected_cut_05635

theorem selected_cut_05636 : selected 8 ⟨174110, by decide⟩
    (prefixPartial 13 83042) = some ⟨13, 2, 0, 174110, 83042, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_83042_174110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83042 ⟨174110, by decide⟩ :=
  accepted_of_selected 13 83042 ⟨174110, by decide⟩ ⟨13, 2, 0, 174110, 83042, 1361, 16384⟩
    (by decide) selected_cut_05636

theorem selected_cut_05637 : selected 8 ⟨174116, by decide⟩
    (prefixPartial 13 83043) = some ⟨13, 2, 0, 174116, 83043, 641, 16384⟩ := by
  decide +kernel

theorem context_13_83043_174116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83043 ⟨174116, by decide⟩ :=
  accepted_of_selected 13 83043 ⟨174116, by decide⟩ ⟨13, 2, 0, 174116, 83043, 641, 16384⟩
    (by decide) selected_cut_05637

theorem unmarked_context_12_20760_174117 : frontier 9 ⟨174117, by decide⟩
    (prefixCache 12 20760) (prefixPartial 12 20760) = false := by
  decide +kernel

theorem node_context_12_20760_174117 : EJMOriginalGlobalDAGData.nodes 9 ⟨174117, by decide⟩ =
    .split (coordinate 12) (![⟨174060, by decide⟩,⟨174091, by decide⟩,⟨174110, by decide⟩,⟨174116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20760_174117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20760 ⟨174117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20760
    ⟨174117, by decide⟩ (by decide) (![⟨174060, by decide⟩,⟨174091, by decide⟩,⟨174110, by decide⟩,⟨174116, by decide⟩]) unmarked_context_12_20760_174117 node_context_12_20760_174117
  intro a
  fin_cases a
  · exact context_13_83040_174060
  · exact context_13_83041_174091
  · exact context_13_83042_174110
  · exact context_13_83043_174116

theorem selected_cut_05638 : selected 8 ⟨174140, by decide⟩
    (prefixPartial 13 83044) = some ⟨13, 2, 0, 174140, 83044, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_83044_174140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83044 ⟨174140, by decide⟩ :=
  accepted_of_selected 13 83044 ⟨174140, by decide⟩ ⟨13, 2, 0, 174140, 83044, 1253, 16384⟩
    (by decide) selected_cut_05638

theorem selected_cut_05639 : selected 8 ⟨174166, by decide⟩
    (prefixPartial 13 83045) = some ⟨13, 2, 0, 174166, 83045, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_83045_174166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83045 ⟨174166, by decide⟩ :=
  accepted_of_selected 13 83045 ⟨174166, by decide⟩ ⟨13, 2, 0, 174166, 83045, 1485, 16384⟩
    (by decide) selected_cut_05639

theorem selected_cut_05640 : selected 8 ⟨174186, by decide⟩
    (prefixPartial 13 83046) = some ⟨13, 2, 0, 174186, 83046, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_83046_174186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83046 ⟨174186, by decide⟩ :=
  accepted_of_selected 13 83046 ⟨174186, by decide⟩ ⟨13, 2, 0, 174186, 83046, 1281, 16384⟩
    (by decide) selected_cut_05640

theorem selected_cut_05641 : selected 8 ⟨174195, by decide⟩
    (prefixPartial 13 83047) = some ⟨13, 2, 0, 174195, 83047, 709, 16384⟩ := by
  decide +kernel

theorem context_13_83047_174195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83047 ⟨174195, by decide⟩ :=
  accepted_of_selected 13 83047 ⟨174195, by decide⟩ ⟨13, 2, 0, 174195, 83047, 709, 16384⟩
    (by decide) selected_cut_05641

theorem unmarked_context_12_20761_174196 : frontier 9 ⟨174196, by decide⟩
    (prefixCache 12 20761) (prefixPartial 12 20761) = false := by
  decide +kernel

theorem node_context_12_20761_174196 : EJMOriginalGlobalDAGData.nodes 9 ⟨174196, by decide⟩ =
    .split (coordinate 12) (![⟨174140, by decide⟩,⟨174166, by decide⟩,⟨174186, by decide⟩,⟨174195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20761_174196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20761 ⟨174196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20761
    ⟨174196, by decide⟩ (by decide) (![⟨174140, by decide⟩,⟨174166, by decide⟩,⟨174186, by decide⟩,⟨174195, by decide⟩]) unmarked_context_12_20761_174196 node_context_12_20761_174196
  intro a
  fin_cases a
  · exact context_13_83044_174140
  · exact context_13_83045_174166
  · exact context_13_83046_174186
  · exact context_13_83047_174195

theorem selected_cut_05642 : selected 8 ⟨174228, by decide⟩
    (prefixPartial 13 83048) = some ⟨13, 2, 0, 174228, 83048, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_83048_174228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83048 ⟨174228, by decide⟩ :=
  accepted_of_selected 13 83048 ⟨174228, by decide⟩ ⟨13, 2, 0, 174228, 83048, 1749, 16384⟩
    (by decide) selected_cut_05642

theorem selected_cut_05643 : selected 8 ⟨174262, by decide⟩
    (prefixPartial 13 83049) = some ⟨13, 2, 0, 174262, 83049, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_83049_174262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83049 ⟨174262, by decide⟩ :=
  accepted_of_selected 13 83049 ⟨174262, by decide⟩ ⟨13, 2, 0, 174262, 83049, 2397, 16384⟩
    (by decide) selected_cut_05643

theorem selected_cut_05644 : selected 8 ⟨174282, by decide⟩
    (prefixPartial 13 83050) = some ⟨13, 2, 0, 174282, 83050, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_83050_174282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83050 ⟨174282, by decide⟩ :=
  accepted_of_selected 13 83050 ⟨174282, by decide⟩ ⟨13, 2, 0, 174282, 83050, 1377, 16384⟩
    (by decide) selected_cut_05644

theorem selected_cut_05645 : selected 8 ⟨174288, by decide⟩
    (prefixPartial 13 83051) = some ⟨13, 2, 0, 174288, 83051, 749, 16384⟩ := by
  decide +kernel

theorem context_13_83051_174288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83051 ⟨174288, by decide⟩ :=
  accepted_of_selected 13 83051 ⟨174288, by decide⟩ ⟨13, 2, 0, 174288, 83051, 749, 16384⟩
    (by decide) selected_cut_05645

theorem unmarked_context_12_20762_174289 : frontier 9 ⟨174289, by decide⟩
    (prefixCache 12 20762) (prefixPartial 12 20762) = false := by
  decide +kernel

theorem node_context_12_20762_174289 : EJMOriginalGlobalDAGData.nodes 9 ⟨174289, by decide⟩ =
    .split (coordinate 12) (![⟨174228, by decide⟩,⟨174262, by decide⟩,⟨174282, by decide⟩,⟨174288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20762_174289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20762 ⟨174289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20762
    ⟨174289, by decide⟩ (by decide) (![⟨174228, by decide⟩,⟨174262, by decide⟩,⟨174282, by decide⟩,⟨174288, by decide⟩]) unmarked_context_12_20762_174289 node_context_12_20762_174289
  intro a
  fin_cases a
  · exact context_13_83048_174228
  · exact context_13_83049_174262
  · exact context_13_83050_174282
  · exact context_13_83051_174288

theorem selected_cut_05646 : selected 8 ⟨174318, by decide⟩
    (prefixPartial 13 83052) = some ⟨13, 2, 0, 174318, 83052, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_83052_174318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83052 ⟨174318, by decide⟩ :=
  accepted_of_selected 13 83052 ⟨174318, by decide⟩ ⟨13, 2, 0, 174318, 83052, 1729, 16384⟩
    (by decide) selected_cut_05646

theorem selected_cut_05647 : selected 8 ⟨174353, by decide⟩
    (prefixPartial 13 83053) = some ⟨13, 2, 0, 174353, 83053, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_83053_174353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83053 ⟨174353, by decide⟩ :=
  accepted_of_selected 13 83053 ⟨174353, by decide⟩ ⟨13, 2, 0, 174353, 83053, 2385, 16384⟩
    (by decide) selected_cut_05647

theorem selected_cut_05648 : selected 8 ⟨174373, by decide⟩
    (prefixPartial 13 83054) = some ⟨13, 2, 0, 174373, 83054, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_83054_174373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83054 ⟨174373, by decide⟩ :=
  accepted_of_selected 13 83054 ⟨174373, by decide⟩ ⟨13, 2, 0, 174373, 83054, 1533, 16384⟩
    (by decide) selected_cut_05648

theorem selected_cut_05649 : selected 8 ⟨174380, by decide⟩
    (prefixPartial 13 83055) = some ⟨13, 2, 0, 174380, 83055, 741, 16384⟩ := by
  decide +kernel

theorem context_13_83055_174380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83055 ⟨174380, by decide⟩ :=
  accepted_of_selected 13 83055 ⟨174380, by decide⟩ ⟨13, 2, 0, 174380, 83055, 741, 16384⟩
    (by decide) selected_cut_05649

theorem unmarked_context_12_20763_174381 : frontier 9 ⟨174381, by decide⟩
    (prefixCache 12 20763) (prefixPartial 12 20763) = false := by
  decide +kernel

theorem node_context_12_20763_174381 : EJMOriginalGlobalDAGData.nodes 9 ⟨174381, by decide⟩ =
    .split (coordinate 12) (![⟨174318, by decide⟩,⟨174353, by decide⟩,⟨174373, by decide⟩,⟨174380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20763_174381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20763 ⟨174381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20763
    ⟨174381, by decide⟩ (by decide) (![⟨174318, by decide⟩,⟨174353, by decide⟩,⟨174373, by decide⟩,⟨174380, by decide⟩]) unmarked_context_12_20763_174381 node_context_12_20763_174381
  intro a
  fin_cases a
  · exact context_13_83052_174318
  · exact context_13_83053_174353
  · exact context_13_83054_174373
  · exact context_13_83055_174380

theorem unmarked_context_11_5190_174382 : frontier 10 ⟨174382, by decide⟩
    (prefixCache 11 5190) (prefixPartial 11 5190) = false := by
  decide +kernel

theorem node_context_11_5190_174382 : EJMOriginalGlobalDAGData.nodes 10 ⟨174382, by decide⟩ =
    .split (coordinate 11) (![⟨174117, by decide⟩,⟨174196, by decide⟩,⟨174289, by decide⟩,⟨174381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5190_174382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5190 ⟨174382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5190
    ⟨174382, by decide⟩ (by decide) (![⟨174117, by decide⟩,⟨174196, by decide⟩,⟨174289, by decide⟩,⟨174381, by decide⟩]) unmarked_context_11_5190_174382 node_context_11_5190_174382
  intro a
  fin_cases a
  · exact context_12_20760_174117
  · exact context_12_20761_174196
  · exact context_12_20762_174289
  · exact context_12_20763_174381

theorem selected_cut_05650 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5191) = some ⟨11, 1, 0, 1736, 5191, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5191_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5191 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5191 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5191, 1, 262144⟩
    (by decide) selected_cut_05650

theorem unmarked_context_10_1297_174383 : frontier 11 ⟨174383, by decide⟩
    (prefixCache 10 1297) (prefixPartial 10 1297) = false := by
  decide +kernel

theorem node_context_10_1297_174383 : EJMOriginalGlobalDAGData.nodes 11 ⟨174383, by decide⟩ =
    .split (coordinate 10) (![⟨173795, by decide⟩,⟨174033, by decide⟩,⟨174382, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1297_174383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1297 ⟨174383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1297
    ⟨174383, by decide⟩ (by decide) (![⟨173795, by decide⟩,⟨174033, by decide⟩,⟨174382, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1297_174383 node_context_10_1297_174383
  intro a
  fin_cases a
  · exact context_11_5188_173795
  · exact context_11_5189_174033
  · exact context_11_5190_174382
  · exact context_11_5191_1736

theorem selected_cut_05651 : selected 8 ⟨174407, by decide⟩
    (prefixPartial 13 83072) = some ⟨13, 2, 0, 174407, 83072, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_83072_174407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83072 ⟨174407, by decide⟩ :=
  accepted_of_selected 13 83072 ⟨174407, by decide⟩ ⟨13, 2, 0, 174407, 83072, 1265, 16384⟩
    (by decide) selected_cut_05651

theorem selected_cut_05652 : selected 8 ⟨174426, by decide⟩
    (prefixPartial 13 83073) = some ⟨13, 2, 0, 174426, 83073, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_83073_174426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83073 ⟨174426, by decide⟩ :=
  accepted_of_selected 13 83073 ⟨174426, by decide⟩ ⟨13, 2, 0, 174426, 83073, 1241, 16384⟩
    (by decide) selected_cut_05652

theorem selected_cut_05653 : selected 8 ⟨174443, by decide⟩
    (prefixPartial 13 83074) = some ⟨13, 2, 0, 174443, 83074, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_83074_174443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83074 ⟨174443, by decide⟩ :=
  accepted_of_selected 13 83074 ⟨174443, by decide⟩ ⟨13, 2, 0, 174443, 83074, 1049, 16384⟩
    (by decide) selected_cut_05653

theorem selected_cut_05654 : selected 8 ⟨174448, by decide⟩
    (prefixPartial 13 83075) = some ⟨13, 2, 0, 174448, 83075, 661, 16384⟩ := by
  decide +kernel

theorem context_13_83075_174448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83075 ⟨174448, by decide⟩ :=
  accepted_of_selected 13 83075 ⟨174448, by decide⟩ ⟨13, 2, 0, 174448, 83075, 661, 16384⟩
    (by decide) selected_cut_05654

theorem unmarked_context_12_20768_174449 : frontier 9 ⟨174449, by decide⟩
    (prefixCache 12 20768) (prefixPartial 12 20768) = false := by
  decide +kernel

theorem node_context_12_20768_174449 : EJMOriginalGlobalDAGData.nodes 9 ⟨174449, by decide⟩ =
    .split (coordinate 12) (![⟨174407, by decide⟩,⟨174426, by decide⟩,⟨174443, by decide⟩,⟨174448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20768_174449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20768 ⟨174449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20768
    ⟨174449, by decide⟩ (by decide) (![⟨174407, by decide⟩,⟨174426, by decide⟩,⟨174443, by decide⟩,⟨174448, by decide⟩]) unmarked_context_12_20768_174449 node_context_12_20768_174449
  intro a
  fin_cases a
  · exact context_13_83072_174407
  · exact context_13_83073_174426
  · exact context_13_83074_174443
  · exact context_13_83075_174448

theorem selected_cut_05655 : selected 8 ⟨174469, by decide⟩
    (prefixPartial 13 83076) = some ⟨13, 2, 0, 174469, 83076, 973, 16384⟩ := by
  decide +kernel

theorem context_13_83076_174469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83076 ⟨174469, by decide⟩ :=
  accepted_of_selected 13 83076 ⟨174469, by decide⟩ ⟨13, 2, 0, 174469, 83076, 973, 16384⟩
    (by decide) selected_cut_05655

theorem selected_cut_05656 : selected 8 ⟨174490, by decide⟩
    (prefixPartial 13 83077) = some ⟨13, 2, 0, 174490, 83077, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_83077_174490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83077 ⟨174490, by decide⟩ :=
  accepted_of_selected 13 83077 ⟨174490, by decide⟩ ⟨13, 2, 0, 174490, 83077, 1389, 16384⟩
    (by decide) selected_cut_05656

theorem selected_cut_05657 : selected 8 ⟨174510, by decide⟩
    (prefixPartial 13 83078) = some ⟨13, 2, 0, 174510, 83078, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_83078_174510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83078 ⟨174510, by decide⟩ :=
  accepted_of_selected 13 83078 ⟨174510, by decide⟩ ⟨13, 2, 0, 174510, 83078, 1173, 16384⟩
    (by decide) selected_cut_05657

theorem selected_cut_05658 : selected 8 ⟨174518, by decide⟩
    (prefixPartial 13 83079) = some ⟨13, 2, 0, 174518, 83079, 773, 16384⟩ := by
  decide +kernel

theorem context_13_83079_174518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83079 ⟨174518, by decide⟩ :=
  accepted_of_selected 13 83079 ⟨174518, by decide⟩ ⟨13, 2, 0, 174518, 83079, 773, 16384⟩
    (by decide) selected_cut_05658

theorem unmarked_context_12_20769_174519 : frontier 9 ⟨174519, by decide⟩
    (prefixCache 12 20769) (prefixPartial 12 20769) = false := by
  decide +kernel

theorem node_context_12_20769_174519 : EJMOriginalGlobalDAGData.nodes 9 ⟨174519, by decide⟩ =
    .split (coordinate 12) (![⟨174469, by decide⟩,⟨174490, by decide⟩,⟨174510, by decide⟩,⟨174518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20769_174519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20769 ⟨174519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20769
    ⟨174519, by decide⟩ (by decide) (![⟨174469, by decide⟩,⟨174490, by decide⟩,⟨174510, by decide⟩,⟨174518, by decide⟩]) unmarked_context_12_20769_174519 node_context_12_20769_174519
  intro a
  fin_cases a
  · exact context_13_83076_174469
  · exact context_13_83077_174490
  · exact context_13_83078_174510
  · exact context_13_83079_174518

theorem selected_cut_05659 : selected 8 ⟨174542, by decide⟩
    (prefixPartial 13 83080) = some ⟨13, 2, 0, 174542, 83080, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_83080_174542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83080 ⟨174542, by decide⟩ :=
  accepted_of_selected 13 83080 ⟨174542, by decide⟩ ⟨13, 2, 0, 174542, 83080, 1333, 16384⟩
    (by decide) selected_cut_05659

theorem selected_cut_05660 : selected 8 ⟨174566, by decide⟩
    (prefixPartial 13 83081) = some ⟨13, 2, 0, 174566, 83081, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_83081_174566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83081 ⟨174566, by decide⟩ :=
  accepted_of_selected 13 83081 ⟨174566, by decide⟩ ⟨13, 2, 0, 174566, 83081, 2213, 16384⟩
    (by decide) selected_cut_05660

theorem selected_cut_05661 : selected 8 ⟨174588, by decide⟩
    (prefixPartial 13 83082) = some ⟨13, 2, 0, 174588, 83082, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_83082_174588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83082 ⟨174588, by decide⟩ :=
  accepted_of_selected 13 83082 ⟨174588, by decide⟩ ⟨13, 2, 0, 174588, 83082, 1441, 16384⟩
    (by decide) selected_cut_05661

theorem selected_cut_05662 : selected 8 ⟨174598, by decide⟩
    (prefixPartial 13 83083) = some ⟨13, 2, 0, 174598, 83083, 821, 16384⟩ := by
  decide +kernel

theorem context_13_83083_174598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83083 ⟨174598, by decide⟩ :=
  accepted_of_selected 13 83083 ⟨174598, by decide⟩ ⟨13, 2, 0, 174598, 83083, 821, 16384⟩
    (by decide) selected_cut_05662

theorem unmarked_context_12_20770_174599 : frontier 9 ⟨174599, by decide⟩
    (prefixCache 12 20770) (prefixPartial 12 20770) = false := by
  decide +kernel

theorem node_context_12_20770_174599 : EJMOriginalGlobalDAGData.nodes 9 ⟨174599, by decide⟩ =
    .split (coordinate 12) (![⟨174542, by decide⟩,⟨174566, by decide⟩,⟨174588, by decide⟩,⟨174598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20770_174599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20770 ⟨174599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20770
    ⟨174599, by decide⟩ (by decide) (![⟨174542, by decide⟩,⟨174566, by decide⟩,⟨174588, by decide⟩,⟨174598, by decide⟩]) unmarked_context_12_20770_174599 node_context_12_20770_174599
  intro a
  fin_cases a
  · exact context_13_83080_174542
  · exact context_13_83081_174566
  · exact context_13_83082_174588
  · exact context_13_83083_174598

theorem selected_cut_05663 : selected 8 ⟨174621, by decide⟩
    (prefixPartial 13 83084) = some ⟨13, 2, 0, 174621, 83084, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_83084_174621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83084 ⟨174621, by decide⟩ :=
  accepted_of_selected 13 83084 ⟨174621, by decide⟩ ⟨13, 2, 0, 174621, 83084, 1249, 16384⟩
    (by decide) selected_cut_05663

theorem selected_cut_05664 : selected 8 ⟨174648, by decide⟩
    (prefixPartial 13 83085) = some ⟨13, 2, 0, 174648, 83085, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_83085_174648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83085 ⟨174648, by decide⟩ :=
  accepted_of_selected 13 83085 ⟨174648, by decide⟩ ⟨13, 2, 0, 174648, 83085, 2069, 16384⟩
    (by decide) selected_cut_05664

theorem selected_cut_05665 : selected 8 ⟨174666, by decide⟩
    (prefixPartial 13 83086) = some ⟨13, 2, 0, 174666, 83086, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_83086_174666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83086 ⟨174666, by decide⟩ :=
  accepted_of_selected 13 83086 ⟨174666, by decide⟩ ⟨13, 2, 0, 174666, 83086, 1309, 16384⟩
    (by decide) selected_cut_05665

theorem selected_cut_05666 : selected 8 ⟨174677, by decide⟩
    (prefixPartial 13 83087) = some ⟨13, 2, 0, 174677, 83087, 821, 16384⟩ := by
  decide +kernel

theorem context_13_83087_174677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 83087 ⟨174677, by decide⟩ :=
  accepted_of_selected 13 83087 ⟨174677, by decide⟩ ⟨13, 2, 0, 174677, 83087, 821, 16384⟩
    (by decide) selected_cut_05666

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
