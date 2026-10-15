/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover162
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_15651 : selected 8 ⟨401050, by decide⟩
    (prefixPartial 13 111657) = some ⟨13, 2, 0, 401050, 111657, 4053, 16384⟩ := by
  decide +kernel

theorem context_13_111657_401050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111657 ⟨401050, by decide⟩ :=
  accepted_of_selected 13 111657 ⟨401050, by decide⟩ ⟨13, 2, 0, 401050, 111657, 4053, 16384⟩
    (by decide) selected_cut_15651

theorem selected_cut_15652 : selected 8 ⟨401086, by decide⟩
    (prefixPartial 13 111658) = some ⟨13, 2, 0, 401086, 111658, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_111658_401086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111658 ⟨401086, by decide⟩ :=
  accepted_of_selected 13 111658 ⟨401086, by decide⟩ ⟨13, 2, 0, 401086, 111658, 2661, 16384⟩
    (by decide) selected_cut_15652

theorem selected_cut_15653 : selected 8 ⟨401103, by decide⟩
    (prefixPartial 13 111659) = some ⟨13, 2, 0, 401103, 111659, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_111659_401103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111659 ⟨401103, by decide⟩ :=
  accepted_of_selected 13 111659 ⟨401103, by decide⟩ ⟨13, 2, 0, 401103, 111659, 1289, 16384⟩
    (by decide) selected_cut_15653

theorem unmarked_context_12_27914_401104 : frontier 9 ⟨401104, by decide⟩
    (prefixCache 12 27914) (prefixPartial 12 27914) = false := by
  decide +kernel

theorem node_context_12_27914_401104 : EJMOriginalGlobalDAGData.nodes 9 ⟨401104, by decide⟩ =
    .split (coordinate 12) (![⟨400983, by decide⟩,⟨401050, by decide⟩,⟨401086, by decide⟩,⟨401103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27914_401104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27914 ⟨401104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27914
    ⟨401104, by decide⟩ (by decide) (![⟨400983, by decide⟩,⟨401050, by decide⟩,⟨401086, by decide⟩,⟨401103, by decide⟩]) unmarked_context_12_27914_401104 node_context_12_27914_401104
  intro a
  fin_cases a
  · exact context_13_111656_400983
  · exact context_13_111657_401050
  · exact context_13_111658_401086
  · exact context_13_111659_401103

theorem selected_cut_15654 : selected 7 ⟨401115, by decide⟩
    (prefixPartial 14 446640) = some ⟨14, 2, 0, 401115, 446640, 657, 4096⟩ := by
  decide +kernel

theorem context_14_446640_401115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446640 ⟨401115, by decide⟩ :=
  accepted_of_selected 14 446640 ⟨401115, by decide⟩ ⟨14, 2, 0, 401115, 446640, 657, 4096⟩
    (by decide) selected_cut_15654

theorem selected_cut_15655 : selected 7 ⟨401132, by decide⟩
    (prefixPartial 14 446641) = some ⟨14, 2, 0, 401132, 446641, 1041, 4096⟩ := by
  decide +kernel

theorem context_14_446641_401132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446641 ⟨401132, by decide⟩ :=
  accepted_of_selected 14 446641 ⟨401132, by decide⟩ ⟨14, 2, 0, 401132, 446641, 1041, 4096⟩
    (by decide) selected_cut_15655

theorem selected_cut_15656 : selected 7 ⟨401148, by decide⟩
    (prefixPartial 14 446642) = some ⟨14, 2, 0, 401148, 446642, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_446642_401148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446642 ⟨401148, by decide⟩ :=
  accepted_of_selected 14 446642 ⟨401148, by decide⟩ ⟨14, 2, 0, 401148, 446642, 1153, 4096⟩
    (by decide) selected_cut_15656

theorem selected_cut_15657 : selected 7 ⟨401171, by decide⟩
    (prefixPartial 14 446643) = some ⟨14, 2, 0, 401171, 446643, 1421, 4096⟩ := by
  decide +kernel

theorem context_14_446643_401171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446643 ⟨401171, by decide⟩ :=
  accepted_of_selected 14 446643 ⟨401171, by decide⟩ ⟨14, 2, 0, 401171, 446643, 1421, 4096⟩
    (by decide) selected_cut_15657

theorem unmarked_context_13_111660_401172 : frontier 8 ⟨401172, by decide⟩
    (prefixCache 13 111660) (prefixPartial 13 111660) = false := by
  decide +kernel

theorem node_context_13_111660_401172 : EJMOriginalGlobalDAGData.nodes 8 ⟨401172, by decide⟩ =
    .split (coordinate 13) (![⟨401115, by decide⟩,⟨401132, by decide⟩,⟨401148, by decide⟩,⟨401171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_111660_401172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111660 ⟨401172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 111660
    ⟨401172, by decide⟩ (by decide) (![⟨401115, by decide⟩,⟨401132, by decide⟩,⟨401148, by decide⟩,⟨401171, by decide⟩]) unmarked_context_13_111660_401172 node_context_13_111660_401172
  intro a
  fin_cases a
  · exact context_14_446640_401115
  · exact context_14_446641_401132
  · exact context_14_446642_401148
  · exact context_14_446643_401171

theorem selected_cut_15658 : selected 7 ⟨401202, by decide⟩
    (prefixPartial 14 446644) = some ⟨14, 2, 0, 401202, 446644, 1333, 4096⟩ := by
  decide +kernel

theorem context_14_446644_401202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446644 ⟨401202, by decide⟩ :=
  accepted_of_selected 14 446644 ⟨401202, by decide⟩ ⟨14, 2, 0, 401202, 446644, 1333, 4096⟩
    (by decide) selected_cut_15658

theorem selected_cut_15659 : selected 7 ⟨401213, by decide⟩
    (prefixPartial 14 446645) = some ⟨14, 2, 0, 401213, 446645, 669, 4096⟩ := by
  decide +kernel

theorem context_14_446645_401213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446645 ⟨401213, by decide⟩ :=
  accepted_of_selected 14 446645 ⟨401213, by decide⟩ ⟨14, 2, 0, 401213, 446645, 669, 4096⟩
    (by decide) selected_cut_15659

theorem selected_cut_15660 : selected 7 ⟨401242, by decide⟩
    (prefixPartial 14 446646) = some ⟨14, 2, 0, 401242, 446646, 1321, 4096⟩ := by
  decide +kernel

theorem context_14_446646_401242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446646 ⟨401242, by decide⟩ :=
  accepted_of_selected 14 446646 ⟨401242, by decide⟩ ⟨14, 2, 0, 401242, 446646, 1321, 4096⟩
    (by decide) selected_cut_15660

theorem selected_cut_15661 : selected 7 ⟨401268, by decide⟩
    (prefixPartial 14 446647) = some ⟨14, 2, 0, 401268, 446647, 1265, 4096⟩ := by
  decide +kernel

theorem context_14_446647_401268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446647 ⟨401268, by decide⟩ :=
  accepted_of_selected 14 446647 ⟨401268, by decide⟩ ⟨14, 2, 0, 401268, 446647, 1265, 4096⟩
    (by decide) selected_cut_15661

theorem unmarked_context_13_111661_401269 : frontier 8 ⟨401269, by decide⟩
    (prefixCache 13 111661) (prefixPartial 13 111661) = false := by
  decide +kernel

theorem node_context_13_111661_401269 : EJMOriginalGlobalDAGData.nodes 8 ⟨401269, by decide⟩ =
    .split (coordinate 13) (![⟨401202, by decide⟩,⟨401213, by decide⟩,⟨401242, by decide⟩,⟨401268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_111661_401269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111661 ⟨401269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 111661
    ⟨401269, by decide⟩ (by decide) (![⟨401202, by decide⟩,⟨401213, by decide⟩,⟨401242, by decide⟩,⟨401268, by decide⟩]) unmarked_context_13_111661_401269 node_context_13_111661_401269
  intro a
  fin_cases a
  · exact context_14_446644_401202
  · exact context_14_446645_401213
  · exact context_14_446646_401242
  · exact context_14_446647_401268

theorem selected_cut_15662 : selected 8 ⟨401320, by decide⟩
    (prefixPartial 13 111662) = some ⟨13, 2, 0, 401320, 111662, 2905, 16384⟩ := by
  decide +kernel

theorem context_13_111662_401320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111662 ⟨401320, by decide⟩ :=
  accepted_of_selected 13 111662 ⟨401320, by decide⟩ ⟨13, 2, 0, 401320, 111662, 2905, 16384⟩
    (by decide) selected_cut_15662

theorem selected_cut_15663 : selected 8 ⟨401349, by decide⟩
    (prefixPartial 13 111663) = some ⟨13, 2, 0, 401349, 111663, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_111663_401349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111663 ⟨401349, by decide⟩ :=
  accepted_of_selected 13 111663 ⟨401349, by decide⟩ ⟨13, 2, 0, 401349, 111663, 1353, 16384⟩
    (by decide) selected_cut_15663

theorem unmarked_context_12_27915_401350 : frontier 9 ⟨401350, by decide⟩
    (prefixCache 12 27915) (prefixPartial 12 27915) = false := by
  decide +kernel

theorem node_context_12_27915_401350 : EJMOriginalGlobalDAGData.nodes 9 ⟨401350, by decide⟩ =
    .split (coordinate 12) (![⟨401172, by decide⟩,⟨401269, by decide⟩,⟨401320, by decide⟩,⟨401349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27915_401350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27915 ⟨401350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27915
    ⟨401350, by decide⟩ (by decide) (![⟨401172, by decide⟩,⟨401269, by decide⟩,⟨401320, by decide⟩,⟨401349, by decide⟩]) unmarked_context_12_27915_401350 node_context_12_27915_401350
  intro a
  fin_cases a
  · exact context_13_111660_401172
  · exact context_13_111661_401269
  · exact context_13_111662_401320
  · exact context_13_111663_401349

theorem unmarked_context_11_6978_401351 : frontier 10 ⟨401351, by decide⟩
    (prefixCache 11 6978) (prefixPartial 11 6978) = false := by
  decide +kernel

theorem node_context_11_6978_401351 : EJMOriginalGlobalDAGData.nodes 10 ⟨401351, by decide⟩ =
    .split (coordinate 11) (![⟨400755, by decide⟩,⟨400906, by decide⟩,⟨401104, by decide⟩,⟨401350, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6978_401351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6978 ⟨401351, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6978
    ⟨401351, by decide⟩ (by decide) (![⟨400755, by decide⟩,⟨400906, by decide⟩,⟨401104, by decide⟩,⟨401350, by decide⟩]) unmarked_context_11_6978_401351 node_context_11_6978_401351
  intro a
  fin_cases a
  · exact context_12_27912_400755
  · exact context_12_27913_400906
  · exact context_12_27914_401104
  · exact context_12_27915_401350

theorem selected_cut_15664 : selected 9 ⟨390434, by decide⟩
    (prefixPartial 12 27916) = some ⟨12, 1, 0, 390434, 27916, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27916_390434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27916 ⟨390434, by decide⟩ :=
  accepted_of_selected 12 27916 ⟨390434, by decide⟩ ⟨12, 1, 0, 390434, 27916, 1, 65536⟩
    (by decide) selected_cut_15664

theorem selected_cut_15665 : selected 8 ⟨401385, by decide⟩
    (prefixPartial 13 111668) = some ⟨13, 2, 0, 401385, 111668, 3113, 16384⟩ := by
  decide +kernel

theorem context_13_111668_401385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111668 ⟨401385, by decide⟩ :=
  accepted_of_selected 13 111668 ⟨401385, by decide⟩ ⟨13, 2, 0, 401385, 111668, 3113, 16384⟩
    (by decide) selected_cut_15665

theorem selected_cut_15666 : selected 8 ⟨401429, by decide⟩
    (prefixPartial 13 111669) = some ⟨13, 2, 0, 401429, 111669, 3477, 16384⟩ := by
  decide +kernel

theorem context_13_111669_401429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111669 ⟨401429, by decide⟩ :=
  accepted_of_selected 13 111669 ⟨401429, by decide⟩ ⟨13, 2, 0, 401429, 111669, 3477, 16384⟩
    (by decide) selected_cut_15666

theorem selected_cut_15667 : selected 8 ⟨401462, by decide⟩
    (prefixPartial 13 111670) = some ⟨13, 2, 0, 401462, 111670, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_111670_401462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111670 ⟨401462, by decide⟩ :=
  accepted_of_selected 13 111670 ⟨401462, by decide⟩ ⟨13, 2, 0, 401462, 111670, 2481, 16384⟩
    (by decide) selected_cut_15667

theorem selected_cut_15668 : selected 8 ⟨401467, by decide⟩
    (prefixPartial 13 111671) = some ⟨13, 2, 0, 401467, 111671, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_111671_401467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111671 ⟨401467, by decide⟩ :=
  accepted_of_selected 13 111671 ⟨401467, by decide⟩ ⟨13, 2, 0, 401467, 111671, 1161, 16384⟩
    (by decide) selected_cut_15668

theorem unmarked_context_12_27917_401468 : frontier 9 ⟨401468, by decide⟩
    (prefixCache 12 27917) (prefixPartial 12 27917) = false := by
  decide +kernel

theorem node_context_12_27917_401468 : EJMOriginalGlobalDAGData.nodes 9 ⟨401468, by decide⟩ =
    .split (coordinate 12) (![⟨401385, by decide⟩,⟨401429, by decide⟩,⟨401462, by decide⟩,⟨401467, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27917_401468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27917 ⟨401468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27917
    ⟨401468, by decide⟩ (by decide) (![⟨401385, by decide⟩,⟨401429, by decide⟩,⟨401462, by decide⟩,⟨401467, by decide⟩]) unmarked_context_12_27917_401468 node_context_12_27917_401468
  intro a
  fin_cases a
  · exact context_13_111668_401385
  · exact context_13_111669_401429
  · exact context_13_111670_401462
  · exact context_13_111671_401467

theorem selected_cut_15669 : selected 8 ⟨401526, by decide⟩
    (prefixPartial 13 111672) = some ⟨13, 2, 0, 401526, 111672, 3757, 16384⟩ := by
  decide +kernel

theorem context_13_111672_401526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111672 ⟨401526, by decide⟩ :=
  accepted_of_selected 13 111672 ⟨401526, by decide⟩ ⟨13, 2, 0, 401526, 111672, 3757, 16384⟩
    (by decide) selected_cut_15669

theorem selected_cut_15670 : selected 7 ⟨401550, by decide⟩
    (prefixPartial 14 446692) = some ⟨14, 2, 0, 401550, 446692, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_446692_401550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446692 ⟨401550, by decide⟩ :=
  accepted_of_selected 14 446692 ⟨401550, by decide⟩ ⟨14, 2, 0, 401550, 446692, 1169, 4096⟩
    (by decide) selected_cut_15670

theorem selected_cut_15671 : selected 7 ⟨401559, by decide⟩
    (prefixPartial 14 446693) = some ⟨14, 2, 0, 401559, 446693, 745, 4096⟩ := by
  decide +kernel

theorem context_14_446693_401559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446693 ⟨401559, by decide⟩ :=
  accepted_of_selected 14 446693 ⟨401559, by decide⟩ ⟨14, 2, 0, 401559, 446693, 745, 4096⟩
    (by decide) selected_cut_15671

theorem selected_cut_15672 : selected 7 ⟨401579, by decide⟩
    (prefixPartial 14 446694) = some ⟨14, 2, 0, 401579, 446694, 1289, 4096⟩ := by
  decide +kernel

theorem context_14_446694_401579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446694 ⟨401579, by decide⟩ :=
  accepted_of_selected 14 446694 ⟨401579, by decide⟩ ⟨14, 2, 0, 401579, 446694, 1289, 4096⟩
    (by decide) selected_cut_15672

theorem selected_cut_15673 : selected 7 ⟨401601, by decide⟩
    (prefixPartial 14 446695) = some ⟨14, 2, 0, 401601, 446695, 1081, 4096⟩ := by
  decide +kernel

theorem context_14_446695_401601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446695 ⟨401601, by decide⟩ :=
  accepted_of_selected 14 446695 ⟨401601, by decide⟩ ⟨14, 2, 0, 401601, 446695, 1081, 4096⟩
    (by decide) selected_cut_15673

theorem unmarked_context_13_111673_401602 : frontier 8 ⟨401602, by decide⟩
    (prefixCache 13 111673) (prefixPartial 13 111673) = false := by
  decide +kernel

theorem node_context_13_111673_401602 : EJMOriginalGlobalDAGData.nodes 8 ⟨401602, by decide⟩ =
    .split (coordinate 13) (![⟨401550, by decide⟩,⟨401559, by decide⟩,⟨401579, by decide⟩,⟨401601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_111673_401602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111673 ⟨401602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 111673
    ⟨401602, by decide⟩ (by decide) (![⟨401550, by decide⟩,⟨401559, by decide⟩,⟨401579, by decide⟩,⟨401601, by decide⟩]) unmarked_context_13_111673_401602 node_context_13_111673_401602
  intro a
  fin_cases a
  · exact context_14_446692_401550
  · exact context_14_446693_401559
  · exact context_14_446694_401579
  · exact context_14_446695_401601

theorem selected_cut_15674 : selected 8 ⟨401640, by decide⟩
    (prefixPartial 13 111674) = some ⟨13, 2, 0, 401640, 111674, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_111674_401640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111674 ⟨401640, by decide⟩ :=
  accepted_of_selected 13 111674 ⟨401640, by decide⟩ ⟨13, 2, 0, 401640, 111674, 2521, 16384⟩
    (by decide) selected_cut_15674

theorem selected_cut_15675 : selected 8 ⟨401671, by decide⟩
    (prefixPartial 13 111675) = some ⟨13, 2, 0, 401671, 111675, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_111675_401671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111675 ⟨401671, by decide⟩ :=
  accepted_of_selected 13 111675 ⟨401671, by decide⟩ ⟨13, 2, 0, 401671, 111675, 1385, 16384⟩
    (by decide) selected_cut_15675

theorem unmarked_context_12_27918_401672 : frontier 9 ⟨401672, by decide⟩
    (prefixCache 12 27918) (prefixPartial 12 27918) = false := by
  decide +kernel

theorem node_context_12_27918_401672 : EJMOriginalGlobalDAGData.nodes 9 ⟨401672, by decide⟩ =
    .split (coordinate 12) (![⟨401526, by decide⟩,⟨401602, by decide⟩,⟨401640, by decide⟩,⟨401671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27918_401672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27918 ⟨401672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27918
    ⟨401672, by decide⟩ (by decide) (![⟨401526, by decide⟩,⟨401602, by decide⟩,⟨401640, by decide⟩,⟨401671, by decide⟩]) unmarked_context_12_27918_401672 node_context_12_27918_401672
  intro a
  fin_cases a
  · exact context_13_111672_401526
  · exact context_13_111673_401602
  · exact context_13_111674_401640
  · exact context_13_111675_401671

theorem selected_cut_15676 : selected 8 ⟨401722, by decide⟩
    (prefixPartial 13 111676) = some ⟨13, 2, 0, 401722, 111676, 3757, 16384⟩ := by
  decide +kernel

theorem context_13_111676_401722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111676 ⟨401722, by decide⟩ :=
  accepted_of_selected 13 111676 ⟨401722, by decide⟩ ⟨13, 2, 0, 401722, 111676, 3757, 16384⟩
    (by decide) selected_cut_15676

theorem selected_cut_15677 : selected 8 ⟨401771, by decide⟩
    (prefixPartial 13 111677) = some ⟨13, 2, 0, 401771, 111677, 3833, 16384⟩ := by
  decide +kernel

theorem context_13_111677_401771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111677 ⟨401771, by decide⟩ :=
  accepted_of_selected 13 111677 ⟨401771, by decide⟩ ⟨13, 2, 0, 401771, 111677, 3833, 16384⟩
    (by decide) selected_cut_15677

theorem selected_cut_15678 : selected 8 ⟨401812, by decide⟩
    (prefixPartial 13 111678) = some ⟨13, 2, 0, 401812, 111678, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_111678_401812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111678 ⟨401812, by decide⟩ :=
  accepted_of_selected 13 111678 ⟨401812, by decide⟩ ⟨13, 2, 0, 401812, 111678, 2749, 16384⟩
    (by decide) selected_cut_15678

theorem selected_cut_15679 : selected 8 ⟨401838, by decide⟩
    (prefixPartial 13 111679) = some ⟨13, 2, 0, 401838, 111679, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_111679_401838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111679 ⟨401838, by decide⟩ :=
  accepted_of_selected 13 111679 ⟨401838, by decide⟩ ⟨13, 2, 0, 401838, 111679, 1457, 16384⟩
    (by decide) selected_cut_15679

theorem unmarked_context_12_27919_401839 : frontier 9 ⟨401839, by decide⟩
    (prefixCache 12 27919) (prefixPartial 12 27919) = false := by
  decide +kernel

theorem node_context_12_27919_401839 : EJMOriginalGlobalDAGData.nodes 9 ⟨401839, by decide⟩ =
    .split (coordinate 12) (![⟨401722, by decide⟩,⟨401771, by decide⟩,⟨401812, by decide⟩,⟨401838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27919_401839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27919 ⟨401839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27919
    ⟨401839, by decide⟩ (by decide) (![⟨401722, by decide⟩,⟨401771, by decide⟩,⟨401812, by decide⟩,⟨401838, by decide⟩]) unmarked_context_12_27919_401839 node_context_12_27919_401839
  intro a
  fin_cases a
  · exact context_13_111676_401722
  · exact context_13_111677_401771
  · exact context_13_111678_401812
  · exact context_13_111679_401838

theorem unmarked_context_11_6979_401840 : frontier 10 ⟨401840, by decide⟩
    (prefixCache 11 6979) (prefixPartial 11 6979) = false := by
  decide +kernel

theorem node_context_11_6979_401840 : EJMOriginalGlobalDAGData.nodes 10 ⟨401840, by decide⟩ =
    .split (coordinate 11) (![⟨390434, by decide⟩,⟨401468, by decide⟩,⟨401672, by decide⟩,⟨401839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6979_401840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6979 ⟨401840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6979
    ⟨401840, by decide⟩ (by decide) (![⟨390434, by decide⟩,⟨401468, by decide⟩,⟨401672, by decide⟩,⟨401839, by decide⟩]) unmarked_context_11_6979_401840 node_context_11_6979_401840
  intro a
  fin_cases a
  · exact context_12_27916_390434
  · exact context_12_27917_401468
  · exact context_12_27918_401672
  · exact context_12_27919_401839

theorem unmarked_context_10_1744_401841 : frontier 11 ⟨401841, by decide⟩
    (prefixCache 10 1744) (prefixPartial 10 1744) = false := by
  decide +kernel

theorem node_context_10_1744_401841 : EJMOriginalGlobalDAGData.nodes 11 ⟨401841, by decide⟩ =
    .split (coordinate 10) (![⟨399669, by decide⟩,⟨400559, by decide⟩,⟨401351, by decide⟩,⟨401840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1744_401841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1744 ⟨401841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1744
    ⟨401841, by decide⟩ (by decide) (![⟨399669, by decide⟩,⟨400559, by decide⟩,⟨401351, by decide⟩,⟨401840, by decide⟩]) unmarked_context_10_1744_401841 node_context_10_1744_401841
  intro a
  fin_cases a
  · exact context_11_6976_399669
  · exact context_11_6977_400559
  · exact context_11_6978_401351
  · exact context_11_6979_401840

theorem selected_cut_15680 : selected 8 ⟨401860, by decide⟩
    (prefixPartial 13 111680) = some ⟨13, 2, 0, 401860, 111680, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_111680_401860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111680 ⟨401860, by decide⟩ :=
  accepted_of_selected 13 111680 ⟨401860, by decide⟩ ⟨13, 2, 0, 401860, 111680, 1701, 16384⟩
    (by decide) selected_cut_15680

theorem selected_cut_15681 : selected 8 ⟨401887, by decide⟩
    (prefixPartial 13 111681) = some ⟨13, 2, 0, 401887, 111681, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_111681_401887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111681 ⟨401887, by decide⟩ :=
  accepted_of_selected 13 111681 ⟨401887, by decide⟩ ⟨13, 2, 0, 401887, 111681, 2185, 16384⟩
    (by decide) selected_cut_15681

theorem selected_cut_15682 : selected 8 ⟨401913, by decide⟩
    (prefixPartial 13 111682) = some ⟨13, 2, 0, 401913, 111682, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_111682_401913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111682 ⟨401913, by decide⟩ :=
  accepted_of_selected 13 111682 ⟨401913, by decide⟩ ⟨13, 2, 0, 401913, 111682, 1449, 16384⟩
    (by decide) selected_cut_15682

theorem selected_cut_15683 : selected 8 ⟨401920, by decide⟩
    (prefixPartial 13 111683) = some ⟨13, 2, 0, 401920, 111683, 717, 16384⟩ := by
  decide +kernel

theorem context_13_111683_401920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111683 ⟨401920, by decide⟩ :=
  accepted_of_selected 13 111683 ⟨401920, by decide⟩ ⟨13, 2, 0, 401920, 111683, 717, 16384⟩
    (by decide) selected_cut_15683

theorem unmarked_context_12_27920_401921 : frontier 9 ⟨401921, by decide⟩
    (prefixCache 12 27920) (prefixPartial 12 27920) = false := by
  decide +kernel

theorem node_context_12_27920_401921 : EJMOriginalGlobalDAGData.nodes 9 ⟨401921, by decide⟩ =
    .split (coordinate 12) (![⟨401860, by decide⟩,⟨401887, by decide⟩,⟨401913, by decide⟩,⟨401920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27920_401921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27920 ⟨401921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27920
    ⟨401921, by decide⟩ (by decide) (![⟨401860, by decide⟩,⟨401887, by decide⟩,⟨401913, by decide⟩,⟨401920, by decide⟩]) unmarked_context_12_27920_401921 node_context_12_27920_401921
  intro a
  fin_cases a
  · exact context_13_111680_401860
  · exact context_13_111681_401887
  · exact context_13_111682_401913
  · exact context_13_111683_401920

theorem selected_cut_15684 : selected 8 ⟨401938, by decide⟩
    (prefixPartial 13 111684) = some ⟨13, 2, 0, 401938, 111684, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_111684_401938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111684 ⟨401938, by decide⟩ :=
  accepted_of_selected 13 111684 ⟨401938, by decide⟩ ⟨13, 2, 0, 401938, 111684, 1769, 16384⟩
    (by decide) selected_cut_15684

theorem selected_cut_15685 : selected 8 ⟨401962, by decide⟩
    (prefixPartial 13 111685) = some ⟨13, 2, 0, 401962, 111685, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_111685_401962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111685 ⟨401962, by decide⟩ :=
  accepted_of_selected 13 111685 ⟨401962, by decide⟩ ⟨13, 2, 0, 401962, 111685, 1861, 16384⟩
    (by decide) selected_cut_15685

theorem selected_cut_15686 : selected 8 ⟨401990, by decide⟩
    (prefixPartial 13 111686) = some ⟨13, 2, 0, 401990, 111686, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_111686_401990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111686 ⟨401990, by decide⟩ :=
  accepted_of_selected 13 111686 ⟨401990, by decide⟩ ⟨13, 2, 0, 401990, 111686, 1721, 16384⟩
    (by decide) selected_cut_15686

theorem selected_cut_15687 : selected 8 ⟨401996, by decide⟩
    (prefixPartial 13 111687) = some ⟨13, 2, 0, 401996, 111687, 933, 16384⟩ := by
  decide +kernel

theorem context_13_111687_401996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111687 ⟨401996, by decide⟩ :=
  accepted_of_selected 13 111687 ⟨401996, by decide⟩ ⟨13, 2, 0, 401996, 111687, 933, 16384⟩
    (by decide) selected_cut_15687

theorem unmarked_context_12_27921_401997 : frontier 9 ⟨401997, by decide⟩
    (prefixCache 12 27921) (prefixPartial 12 27921) = false := by
  decide +kernel

theorem node_context_12_27921_401997 : EJMOriginalGlobalDAGData.nodes 9 ⟨401997, by decide⟩ =
    .split (coordinate 12) (![⟨401938, by decide⟩,⟨401962, by decide⟩,⟨401990, by decide⟩,⟨401996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27921_401997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27921 ⟨401997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27921
    ⟨401997, by decide⟩ (by decide) (![⟨401938, by decide⟩,⟨401962, by decide⟩,⟨401990, by decide⟩,⟨401996, by decide⟩]) unmarked_context_12_27921_401997 node_context_12_27921_401997
  intro a
  fin_cases a
  · exact context_13_111684_401938
  · exact context_13_111685_401962
  · exact context_13_111686_401990
  · exact context_13_111687_401996

theorem selected_cut_15688 : selected 8 ⟨402028, by decide⟩
    (prefixPartial 13 111688) = some ⟨13, 2, 0, 402028, 111688, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_111688_402028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111688 ⟨402028, by decide⟩ :=
  accepted_of_selected 13 111688 ⟨402028, by decide⟩ ⟨13, 2, 0, 402028, 111688, 2205, 16384⟩
    (by decide) selected_cut_15688

theorem selected_cut_15689 : selected 8 ⟨402061, by decide⟩
    (prefixPartial 13 111689) = some ⟨13, 2, 0, 402061, 111689, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_111689_402061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111689 ⟨402061, by decide⟩ :=
  accepted_of_selected 13 111689 ⟨402061, by decide⟩ ⟨13, 2, 0, 402061, 111689, 2441, 16384⟩
    (by decide) selected_cut_15689

theorem selected_cut_15690 : selected 8 ⟨402086, by decide⟩
    (prefixPartial 13 111690) = some ⟨13, 2, 0, 402086, 111690, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_111690_402086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111690 ⟨402086, by decide⟩ :=
  accepted_of_selected 13 111690 ⟨402086, by decide⟩ ⟨13, 2, 0, 402086, 111690, 1877, 16384⟩
    (by decide) selected_cut_15690

theorem selected_cut_15691 : selected 8 ⟨402094, by decide⟩
    (prefixPartial 13 111691) = some ⟨13, 2, 0, 402094, 111691, 981, 16384⟩ := by
  decide +kernel

theorem context_13_111691_402094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111691 ⟨402094, by decide⟩ :=
  accepted_of_selected 13 111691 ⟨402094, by decide⟩ ⟨13, 2, 0, 402094, 111691, 981, 16384⟩
    (by decide) selected_cut_15691

theorem unmarked_context_12_27922_402095 : frontier 9 ⟨402095, by decide⟩
    (prefixCache 12 27922) (prefixPartial 12 27922) = false := by
  decide +kernel

theorem node_context_12_27922_402095 : EJMOriginalGlobalDAGData.nodes 9 ⟨402095, by decide⟩ =
    .split (coordinate 12) (![⟨402028, by decide⟩,⟨402061, by decide⟩,⟨402086, by decide⟩,⟨402094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27922_402095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27922 ⟨402095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27922
    ⟨402095, by decide⟩ (by decide) (![⟨402028, by decide⟩,⟨402061, by decide⟩,⟨402086, by decide⟩,⟨402094, by decide⟩]) unmarked_context_12_27922_402095 node_context_12_27922_402095
  intro a
  fin_cases a
  · exact context_13_111688_402028
  · exact context_13_111689_402061
  · exact context_13_111690_402086
  · exact context_13_111691_402094

theorem selected_cut_15692 : selected 8 ⟨402131, by decide⟩
    (prefixPartial 13 111692) = some ⟨13, 2, 0, 402131, 111692, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_111692_402131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111692 ⟨402131, by decide⟩ :=
  accepted_of_selected 13 111692 ⟨402131, by decide⟩ ⟨13, 2, 0, 402131, 111692, 2353, 16384⟩
    (by decide) selected_cut_15692

theorem selected_cut_15693 : selected 8 ⟨402165, by decide⟩
    (prefixPartial 13 111693) = some ⟨13, 2, 0, 402165, 111693, 2681, 16384⟩ := by
  decide +kernel

theorem context_13_111693_402165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111693 ⟨402165, by decide⟩ :=
  accepted_of_selected 13 111693 ⟨402165, by decide⟩ ⟨13, 2, 0, 402165, 111693, 2681, 16384⟩
    (by decide) selected_cut_15693

theorem selected_cut_15694 : selected 8 ⟨402193, by decide⟩
    (prefixPartial 13 111694) = some ⟨13, 2, 0, 402193, 111694, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_111694_402193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111694 ⟨402193, by decide⟩ :=
  accepted_of_selected 13 111694 ⟨402193, by decide⟩ ⟨13, 2, 0, 402193, 111694, 2125, 16384⟩
    (by decide) selected_cut_15694

theorem selected_cut_15695 : selected 8 ⟨402203, by decide⟩
    (prefixPartial 13 111695) = some ⟨13, 2, 0, 402203, 111695, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_111695_402203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111695 ⟨402203, by decide⟩ :=
  accepted_of_selected 13 111695 ⟨402203, by decide⟩ ⟨13, 2, 0, 402203, 111695, 1053, 16384⟩
    (by decide) selected_cut_15695

theorem unmarked_context_12_27923_402204 : frontier 9 ⟨402204, by decide⟩
    (prefixCache 12 27923) (prefixPartial 12 27923) = false := by
  decide +kernel

theorem node_context_12_27923_402204 : EJMOriginalGlobalDAGData.nodes 9 ⟨402204, by decide⟩ =
    .split (coordinate 12) (![⟨402131, by decide⟩,⟨402165, by decide⟩,⟨402193, by decide⟩,⟨402203, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27923_402204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27923 ⟨402204, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27923
    ⟨402204, by decide⟩ (by decide) (![⟨402131, by decide⟩,⟨402165, by decide⟩,⟨402193, by decide⟩,⟨402203, by decide⟩]) unmarked_context_12_27923_402204 node_context_12_27923_402204
  intro a
  fin_cases a
  · exact context_13_111692_402131
  · exact context_13_111693_402165
  · exact context_13_111694_402193
  · exact context_13_111695_402203

theorem unmarked_context_11_6980_402205 : frontier 10 ⟨402205, by decide⟩
    (prefixCache 11 6980) (prefixPartial 11 6980) = false := by
  decide +kernel

theorem node_context_11_6980_402205 : EJMOriginalGlobalDAGData.nodes 10 ⟨402205, by decide⟩ =
    .split (coordinate 11) (![⟨401921, by decide⟩,⟨401997, by decide⟩,⟨402095, by decide⟩,⟨402204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6980_402205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6980 ⟨402205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6980
    ⟨402205, by decide⟩ (by decide) (![⟨401921, by decide⟩,⟨401997, by decide⟩,⟨402095, by decide⟩,⟨402204, by decide⟩]) unmarked_context_11_6980_402205 node_context_11_6980_402205
  intro a
  fin_cases a
  · exact context_12_27920_401921
  · exact context_12_27921_401997
  · exact context_12_27922_402095
  · exact context_12_27923_402204

theorem selected_cut_15696 : selected 8 ⟨402226, by decide⟩
    (prefixPartial 13 111696) = some ⟨13, 2, 0, 402226, 111696, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_111696_402226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111696 ⟨402226, by decide⟩ :=
  accepted_of_selected 13 111696 ⟨402226, by decide⟩ ⟨13, 2, 0, 402226, 111696, 1533, 16384⟩
    (by decide) selected_cut_15696

theorem selected_cut_15697 : selected 8 ⟨402251, by decide⟩
    (prefixPartial 13 111697) = some ⟨13, 2, 0, 402251, 111697, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_111697_402251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111697 ⟨402251, by decide⟩ :=
  accepted_of_selected 13 111697 ⟨402251, by decide⟩ ⟨13, 2, 0, 402251, 111697, 1797, 16384⟩
    (by decide) selected_cut_15697

theorem selected_cut_15698 : selected 8 ⟨402270, by decide⟩
    (prefixPartial 13 111698) = some ⟨13, 2, 0, 402270, 111698, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_111698_402270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111698 ⟨402270, by decide⟩ :=
  accepted_of_selected 13 111698 ⟨402270, by decide⟩ ⟨13, 2, 0, 402270, 111698, 1337, 16384⟩
    (by decide) selected_cut_15698

theorem selected_cut_15699 : selected 8 ⟨402278, by decide⟩
    (prefixPartial 13 111699) = some ⟨13, 2, 0, 402278, 111699, 653, 16384⟩ := by
  decide +kernel

theorem context_13_111699_402278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111699 ⟨402278, by decide⟩ :=
  accepted_of_selected 13 111699 ⟨402278, by decide⟩ ⟨13, 2, 0, 402278, 111699, 653, 16384⟩
    (by decide) selected_cut_15699

theorem unmarked_context_12_27924_402279 : frontier 9 ⟨402279, by decide⟩
    (prefixCache 12 27924) (prefixPartial 12 27924) = false := by
  decide +kernel

theorem node_context_12_27924_402279 : EJMOriginalGlobalDAGData.nodes 9 ⟨402279, by decide⟩ =
    .split (coordinate 12) (![⟨402226, by decide⟩,⟨402251, by decide⟩,⟨402270, by decide⟩,⟨402278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27924_402279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27924 ⟨402279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27924
    ⟨402279, by decide⟩ (by decide) (![⟨402226, by decide⟩,⟨402251, by decide⟩,⟨402270, by decide⟩,⟨402278, by decide⟩]) unmarked_context_12_27924_402279 node_context_12_27924_402279
  intro a
  fin_cases a
  · exact context_13_111696_402226
  · exact context_13_111697_402251
  · exact context_13_111698_402270
  · exact context_13_111699_402278

theorem selected_cut_15700 : selected 9 ⟨402280, by decide⟩
    (prefixPartial 12 27925) = some ⟨12, 1, 0, 402280, 27925, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27925_402280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27925 ⟨402280, by decide⟩ :=
  accepted_of_selected 12 27925 ⟨402280, by decide⟩ ⟨12, 1, 0, 402280, 27925, 1, 65536⟩
    (by decide) selected_cut_15700

theorem selected_cut_15701 : selected 8 ⟨402308, by decide⟩
    (prefixPartial 13 111704) = some ⟨13, 2, 0, 402308, 111704, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_111704_402308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111704 ⟨402308, by decide⟩ :=
  accepted_of_selected 13 111704 ⟨402308, by decide⟩ ⟨13, 2, 0, 402308, 111704, 2009, 16384⟩
    (by decide) selected_cut_15701

theorem selected_cut_15702 : selected 8 ⟨402333, by decide⟩
    (prefixPartial 13 111705) = some ⟨13, 2, 0, 402333, 111705, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_111705_402333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111705 ⟨402333, by decide⟩ :=
  accepted_of_selected 13 111705 ⟨402333, by decide⟩ ⟨13, 2, 0, 402333, 111705, 2085, 16384⟩
    (by decide) selected_cut_15702

theorem selected_cut_15703 : selected 8 ⟨402355, by decide⟩
    (prefixPartial 13 111706) = some ⟨13, 2, 0, 402355, 111706, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_111706_402355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111706 ⟨402355, by decide⟩ :=
  accepted_of_selected 13 111706 ⟨402355, by decide⟩ ⟨13, 2, 0, 402355, 111706, 1625, 16384⟩
    (by decide) selected_cut_15703

theorem selected_cut_15704 : selected 8 ⟨402362, by decide⟩
    (prefixPartial 13 111707) = some ⟨13, 2, 0, 402362, 111707, 805, 16384⟩ := by
  decide +kernel

theorem context_13_111707_402362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111707 ⟨402362, by decide⟩ :=
  accepted_of_selected 13 111707 ⟨402362, by decide⟩ ⟨13, 2, 0, 402362, 111707, 805, 16384⟩
    (by decide) selected_cut_15704

theorem unmarked_context_12_27926_402363 : frontier 9 ⟨402363, by decide⟩
    (prefixCache 12 27926) (prefixPartial 12 27926) = false := by
  decide +kernel

theorem node_context_12_27926_402363 : EJMOriginalGlobalDAGData.nodes 9 ⟨402363, by decide⟩ =
    .split (coordinate 12) (![⟨402308, by decide⟩,⟨402333, by decide⟩,⟨402355, by decide⟩,⟨402362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27926_402363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27926 ⟨402363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27926
    ⟨402363, by decide⟩ (by decide) (![⟨402308, by decide⟩,⟨402333, by decide⟩,⟨402355, by decide⟩,⟨402362, by decide⟩]) unmarked_context_12_27926_402363 node_context_12_27926_402363
  intro a
  fin_cases a
  · exact context_13_111704_402308
  · exact context_13_111705_402333
  · exact context_13_111706_402355
  · exact context_13_111707_402362

theorem selected_cut_15705 : selected 8 ⟨402389, by decide⟩
    (prefixPartial 13 111708) = some ⟨13, 2, 0, 402389, 111708, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_111708_402389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111708 ⟨402389, by decide⟩ :=
  accepted_of_selected 13 111708 ⟨402389, by decide⟩ ⟨13, 2, 0, 402389, 111708, 2149, 16384⟩
    (by decide) selected_cut_15705

theorem selected_cut_15706 : selected 8 ⟨402417, by decide⟩
    (prefixPartial 13 111709) = some ⟨13, 2, 0, 402417, 111709, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_111709_402417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111709 ⟨402417, by decide⟩ :=
  accepted_of_selected 13 111709 ⟨402417, by decide⟩ ⟨13, 2, 0, 402417, 111709, 2229, 16384⟩
    (by decide) selected_cut_15706

theorem selected_cut_15707 : selected 8 ⟨402436, by decide⟩
    (prefixPartial 13 111710) = some ⟨13, 2, 0, 402436, 111710, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_111710_402436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111710 ⟨402436, by decide⟩ :=
  accepted_of_selected 13 111710 ⟨402436, by decide⟩ ⟨13, 2, 0, 402436, 111710, 1937, 16384⟩
    (by decide) selected_cut_15707

theorem selected_cut_15708 : selected 8 ⟨402446, by decide⟩
    (prefixPartial 13 111711) = some ⟨13, 2, 0, 402446, 111711, 905, 16384⟩ := by
  decide +kernel

theorem context_13_111711_402446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111711 ⟨402446, by decide⟩ :=
  accepted_of_selected 13 111711 ⟨402446, by decide⟩ ⟨13, 2, 0, 402446, 111711, 905, 16384⟩
    (by decide) selected_cut_15708

theorem unmarked_context_12_27927_402447 : frontier 9 ⟨402447, by decide⟩
    (prefixCache 12 27927) (prefixPartial 12 27927) = false := by
  decide +kernel

theorem node_context_12_27927_402447 : EJMOriginalGlobalDAGData.nodes 9 ⟨402447, by decide⟩ =
    .split (coordinate 12) (![⟨402389, by decide⟩,⟨402417, by decide⟩,⟨402436, by decide⟩,⟨402446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27927_402447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27927 ⟨402447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27927
    ⟨402447, by decide⟩ (by decide) (![⟨402389, by decide⟩,⟨402417, by decide⟩,⟨402436, by decide⟩,⟨402446, by decide⟩]) unmarked_context_12_27927_402447 node_context_12_27927_402447
  intro a
  fin_cases a
  · exact context_13_111708_402389
  · exact context_13_111709_402417
  · exact context_13_111710_402436
  · exact context_13_111711_402446

theorem unmarked_context_11_6981_402448 : frontier 10 ⟨402448, by decide⟩
    (prefixCache 11 6981) (prefixPartial 11 6981) = false := by
  decide +kernel

theorem node_context_11_6981_402448 : EJMOriginalGlobalDAGData.nodes 10 ⟨402448, by decide⟩ =
    .split (coordinate 11) (![⟨402279, by decide⟩,⟨402280, by decide⟩,⟨402363, by decide⟩,⟨402447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6981_402448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6981 ⟨402448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6981
    ⟨402448, by decide⟩ (by decide) (![⟨402279, by decide⟩,⟨402280, by decide⟩,⟨402363, by decide⟩,⟨402447, by decide⟩]) unmarked_context_11_6981_402448 node_context_11_6981_402448
  intro a
  fin_cases a
  · exact context_12_27924_402279
  · exact context_12_27925_402280
  · exact context_12_27926_402363
  · exact context_12_27927_402447

theorem selected_cut_15709 : selected 8 ⟨402468, by decide⟩
    (prefixPartial 13 111712) = some ⟨13, 2, 0, 402468, 111712, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_111712_402468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111712 ⟨402468, by decide⟩ :=
  accepted_of_selected 13 111712 ⟨402468, by decide⟩ ⟨13, 2, 0, 402468, 111712, 1549, 16384⟩
    (by decide) selected_cut_15709

theorem selected_cut_15710 : selected 8 ⟨402499, by decide⟩
    (prefixPartial 13 111713) = some ⟨13, 2, 0, 402499, 111713, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_111713_402499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111713 ⟨402499, by decide⟩ :=
  accepted_of_selected 13 111713 ⟨402499, by decide⟩ ⟨13, 2, 0, 402499, 111713, 2257, 16384⟩
    (by decide) selected_cut_15710

theorem selected_cut_15711 : selected 8 ⟨402518, by decide⟩
    (prefixPartial 13 111714) = some ⟨13, 2, 0, 402518, 111714, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_111714_402518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111714 ⟨402518, by decide⟩ :=
  accepted_of_selected 13 111714 ⟨402518, by decide⟩ ⟨13, 2, 0, 402518, 111714, 1489, 16384⟩
    (by decide) selected_cut_15711

theorem selected_cut_15712 : selected 8 ⟨402526, by decide⟩
    (prefixPartial 13 111715) = some ⟨13, 2, 0, 402526, 111715, 741, 16384⟩ := by
  decide +kernel

theorem context_13_111715_402526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111715 ⟨402526, by decide⟩ :=
  accepted_of_selected 13 111715 ⟨402526, by decide⟩ ⟨13, 2, 0, 402526, 111715, 741, 16384⟩
    (by decide) selected_cut_15712

theorem unmarked_context_12_27928_402527 : frontier 9 ⟨402527, by decide⟩
    (prefixCache 12 27928) (prefixPartial 12 27928) = false := by
  decide +kernel

theorem node_context_12_27928_402527 : EJMOriginalGlobalDAGData.nodes 9 ⟨402527, by decide⟩ =
    .split (coordinate 12) (![⟨402468, by decide⟩,⟨402499, by decide⟩,⟨402518, by decide⟩,⟨402526, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27928_402527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27928 ⟨402527, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27928
    ⟨402527, by decide⟩ (by decide) (![⟨402468, by decide⟩,⟨402499, by decide⟩,⟨402518, by decide⟩,⟨402526, by decide⟩]) unmarked_context_12_27928_402527 node_context_12_27928_402527
  intro a
  fin_cases a
  · exact context_13_111712_402468
  · exact context_13_111713_402499
  · exact context_13_111714_402518
  · exact context_13_111715_402526

theorem selected_cut_15713 : selected 8 ⟨402543, by decide⟩
    (prefixPartial 13 111716) = some ⟨13, 2, 0, 402543, 111716, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_111716_402543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111716 ⟨402543, by decide⟩ :=
  accepted_of_selected 13 111716 ⟨402543, by decide⟩ ⟨13, 2, 0, 402543, 111716, 1493, 16384⟩
    (by decide) selected_cut_15713

theorem selected_cut_15714 : selected 8 ⟨402567, by decide⟩
    (prefixPartial 13 111717) = some ⟨13, 2, 0, 402567, 111717, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_111717_402567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111717 ⟨402567, by decide⟩ :=
  accepted_of_selected 13 111717 ⟨402567, by decide⟩ ⟨13, 2, 0, 402567, 111717, 1749, 16384⟩
    (by decide) selected_cut_15714

theorem selected_cut_15715 : selected 8 ⟨402585, by decide⟩
    (prefixPartial 13 111718) = some ⟨13, 2, 0, 402585, 111718, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_111718_402585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111718 ⟨402585, by decide⟩ :=
  accepted_of_selected 13 111718 ⟨402585, by decide⟩ ⟨13, 2, 0, 402585, 111718, 1441, 16384⟩
    (by decide) selected_cut_15715

theorem selected_cut_15716 : selected 8 ⟨402593, by decide⟩
    (prefixPartial 13 111719) = some ⟨13, 2, 0, 402593, 111719, 877, 16384⟩ := by
  decide +kernel

theorem context_13_111719_402593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111719 ⟨402593, by decide⟩ :=
  accepted_of_selected 13 111719 ⟨402593, by decide⟩ ⟨13, 2, 0, 402593, 111719, 877, 16384⟩
    (by decide) selected_cut_15716

theorem unmarked_context_12_27929_402594 : frontier 9 ⟨402594, by decide⟩
    (prefixCache 12 27929) (prefixPartial 12 27929) = false := by
  decide +kernel

theorem node_context_12_27929_402594 : EJMOriginalGlobalDAGData.nodes 9 ⟨402594, by decide⟩ =
    .split (coordinate 12) (![⟨402543, by decide⟩,⟨402567, by decide⟩,⟨402585, by decide⟩,⟨402593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27929_402594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27929 ⟨402594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27929
    ⟨402594, by decide⟩ (by decide) (![⟨402543, by decide⟩,⟨402567, by decide⟩,⟨402585, by decide⟩,⟨402593, by decide⟩]) unmarked_context_12_27929_402594 node_context_12_27929_402594
  intro a
  fin_cases a
  · exact context_13_111716_402543
  · exact context_13_111717_402567
  · exact context_13_111718_402585
  · exact context_13_111719_402593

theorem selected_cut_15717 : selected 8 ⟨402628, by decide⟩
    (prefixPartial 13 111720) = some ⟨13, 2, 0, 402628, 111720, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_111720_402628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111720 ⟨402628, by decide⟩ :=
  accepted_of_selected 13 111720 ⟨402628, by decide⟩ ⟨13, 2, 0, 402628, 111720, 1881, 16384⟩
    (by decide) selected_cut_15717

theorem selected_cut_15718 : selected 8 ⟨402660, by decide⟩
    (prefixPartial 13 111721) = some ⟨13, 2, 0, 402660, 111721, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_111721_402660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111721 ⟨402660, by decide⟩ :=
  accepted_of_selected 13 111721 ⟨402660, by decide⟩ ⟨13, 2, 0, 402660, 111721, 2421, 16384⟩
    (by decide) selected_cut_15718

theorem selected_cut_15719 : selected 8 ⟨402684, by decide⟩
    (prefixPartial 13 111722) = some ⟨13, 2, 0, 402684, 111722, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_111722_402684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111722 ⟨402684, by decide⟩ :=
  accepted_of_selected 13 111722 ⟨402684, by decide⟩ ⟨13, 2, 0, 402684, 111722, 1593, 16384⟩
    (by decide) selected_cut_15719

theorem selected_cut_15720 : selected 8 ⟨402692, by decide⟩
    (prefixPartial 13 111723) = some ⟨13, 2, 0, 402692, 111723, 877, 16384⟩ := by
  decide +kernel

theorem context_13_111723_402692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111723 ⟨402692, by decide⟩ :=
  accepted_of_selected 13 111723 ⟨402692, by decide⟩ ⟨13, 2, 0, 402692, 111723, 877, 16384⟩
    (by decide) selected_cut_15720

theorem unmarked_context_12_27930_402693 : frontier 9 ⟨402693, by decide⟩
    (prefixCache 12 27930) (prefixPartial 12 27930) = false := by
  decide +kernel

theorem node_context_12_27930_402693 : EJMOriginalGlobalDAGData.nodes 9 ⟨402693, by decide⟩ =
    .split (coordinate 12) (![⟨402628, by decide⟩,⟨402660, by decide⟩,⟨402684, by decide⟩,⟨402692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27930_402693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27930 ⟨402693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27930
    ⟨402693, by decide⟩ (by decide) (![⟨402628, by decide⟩,⟨402660, by decide⟩,⟨402684, by decide⟩,⟨402692, by decide⟩]) unmarked_context_12_27930_402693 node_context_12_27930_402693
  intro a
  fin_cases a
  · exact context_13_111720_402628
  · exact context_13_111721_402660
  · exact context_13_111722_402684
  · exact context_13_111723_402692

theorem selected_cut_15721 : selected 8 ⟨402727, by decide⟩
    (prefixPartial 13 111724) = some ⟨13, 2, 0, 402727, 111724, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_111724_402727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111724 ⟨402727, by decide⟩ :=
  accepted_of_selected 13 111724 ⟨402727, by decide⟩ ⟨13, 2, 0, 402727, 111724, 2101, 16384⟩
    (by decide) selected_cut_15721

theorem selected_cut_15722 : selected 8 ⟨402767, by decide⟩
    (prefixPartial 13 111725) = some ⟨13, 2, 0, 402767, 111725, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_111725_402767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111725 ⟨402767, by decide⟩ :=
  accepted_of_selected 13 111725 ⟨402767, by decide⟩ ⟨13, 2, 0, 402767, 111725, 2813, 16384⟩
    (by decide) selected_cut_15722

theorem selected_cut_15723 : selected 8 ⟨402790, by decide⟩
    (prefixPartial 13 111726) = some ⟨13, 2, 0, 402790, 111726, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_111726_402790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111726 ⟨402790, by decide⟩ :=
  accepted_of_selected 13 111726 ⟨402790, by decide⟩ ⟨13, 2, 0, 402790, 111726, 1765, 16384⟩
    (by decide) selected_cut_15723

theorem selected_cut_15724 : selected 8 ⟨402797, by decide⟩
    (prefixPartial 13 111727) = some ⟨13, 2, 0, 402797, 111727, 993, 16384⟩ := by
  decide +kernel

theorem context_13_111727_402797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111727 ⟨402797, by decide⟩ :=
  accepted_of_selected 13 111727 ⟨402797, by decide⟩ ⟨13, 2, 0, 402797, 111727, 993, 16384⟩
    (by decide) selected_cut_15724

theorem unmarked_context_12_27931_402798 : frontier 9 ⟨402798, by decide⟩
    (prefixCache 12 27931) (prefixPartial 12 27931) = false := by
  decide +kernel

theorem node_context_12_27931_402798 : EJMOriginalGlobalDAGData.nodes 9 ⟨402798, by decide⟩ =
    .split (coordinate 12) (![⟨402727, by decide⟩,⟨402767, by decide⟩,⟨402790, by decide⟩,⟨402797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27931_402798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27931 ⟨402798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27931
    ⟨402798, by decide⟩ (by decide) (![⟨402727, by decide⟩,⟨402767, by decide⟩,⟨402790, by decide⟩,⟨402797, by decide⟩]) unmarked_context_12_27931_402798 node_context_12_27931_402798
  intro a
  fin_cases a
  · exact context_13_111724_402727
  · exact context_13_111725_402767
  · exact context_13_111726_402790
  · exact context_13_111727_402797

theorem unmarked_context_11_6982_402799 : frontier 10 ⟨402799, by decide⟩
    (prefixCache 11 6982) (prefixPartial 11 6982) = false := by
  decide +kernel

theorem node_context_11_6982_402799 : EJMOriginalGlobalDAGData.nodes 10 ⟨402799, by decide⟩ =
    .split (coordinate 11) (![⟨402527, by decide⟩,⟨402594, by decide⟩,⟨402693, by decide⟩,⟨402798, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6982_402799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6982 ⟨402799, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6982
    ⟨402799, by decide⟩ (by decide) (![⟨402527, by decide⟩,⟨402594, by decide⟩,⟨402693, by decide⟩,⟨402798, by decide⟩]) unmarked_context_11_6982_402799 node_context_11_6982_402799
  intro a
  fin_cases a
  · exact context_12_27928_402527
  · exact context_12_27929_402594
  · exact context_12_27930_402693
  · exact context_12_27931_402798

theorem selected_cut_15725 : selected 8 ⟨402814, by decide⟩
    (prefixPartial 13 111728) = some ⟨13, 2, 0, 402814, 111728, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_111728_402814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111728 ⟨402814, by decide⟩ :=
  accepted_of_selected 13 111728 ⟨402814, by decide⟩ ⟨13, 2, 0, 402814, 111728, 1241, 16384⟩
    (by decide) selected_cut_15725

theorem selected_cut_15726 : selected 8 ⟨402848, by decide⟩
    (prefixPartial 13 111729) = some ⟨13, 2, 0, 402848, 111729, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_111729_402848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111729 ⟨402848, by decide⟩ :=
  accepted_of_selected 13 111729 ⟨402848, by decide⟩ ⟨13, 2, 0, 402848, 111729, 2209, 16384⟩
    (by decide) selected_cut_15726

theorem selected_cut_15727 : selected 8 ⟨402864, by decide⟩
    (prefixPartial 13 111730) = some ⟨13, 2, 0, 402864, 111730, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_111730_402864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111730 ⟨402864, by decide⟩ :=
  accepted_of_selected 13 111730 ⟨402864, by decide⟩ ⟨13, 2, 0, 402864, 111730, 1465, 16384⟩
    (by decide) selected_cut_15727

theorem selected_cut_15728 : selected 8 ⟨402872, by decide⟩
    (prefixPartial 13 111731) = some ⟨13, 2, 0, 402872, 111731, 813, 16384⟩ := by
  decide +kernel

theorem context_13_111731_402872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111731 ⟨402872, by decide⟩ :=
  accepted_of_selected 13 111731 ⟨402872, by decide⟩ ⟨13, 2, 0, 402872, 111731, 813, 16384⟩
    (by decide) selected_cut_15728

theorem unmarked_context_12_27932_402873 : frontier 9 ⟨402873, by decide⟩
    (prefixCache 12 27932) (prefixPartial 12 27932) = false := by
  decide +kernel

theorem node_context_12_27932_402873 : EJMOriginalGlobalDAGData.nodes 9 ⟨402873, by decide⟩ =
    .split (coordinate 12) (![⟨402814, by decide⟩,⟨402848, by decide⟩,⟨402864, by decide⟩,⟨402872, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27932_402873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27932 ⟨402873, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27932
    ⟨402873, by decide⟩ (by decide) (![⟨402814, by decide⟩,⟨402848, by decide⟩,⟨402864, by decide⟩,⟨402872, by decide⟩]) unmarked_context_12_27932_402873 node_context_12_27932_402873
  intro a
  fin_cases a
  · exact context_13_111728_402814
  · exact context_13_111729_402848
  · exact context_13_111730_402864
  · exact context_13_111731_402872

theorem selected_cut_15729 : selected 8 ⟨402889, by decide⟩
    (prefixPartial 13 111732) = some ⟨13, 2, 0, 402889, 111732, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_111732_402889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111732 ⟨402889, by decide⟩ :=
  accepted_of_selected 13 111732 ⟨402889, by decide⟩ ⟨13, 2, 0, 402889, 111732, 1281, 16384⟩
    (by decide) selected_cut_15729

theorem selected_cut_15730 : selected 8 ⟨402911, by decide⟩
    (prefixPartial 13 111733) = some ⟨13, 2, 0, 402911, 111733, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_111733_402911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111733 ⟨402911, by decide⟩ :=
  accepted_of_selected 13 111733 ⟨402911, by decide⟩ ⟨13, 2, 0, 402911, 111733, 1889, 16384⟩
    (by decide) selected_cut_15730

theorem selected_cut_15731 : selected 8 ⟨402938, by decide⟩
    (prefixPartial 13 111734) = some ⟨13, 2, 0, 402938, 111734, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_111734_402938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111734 ⟨402938, by decide⟩ :=
  accepted_of_selected 13 111734 ⟨402938, by decide⟩ ⟨13, 2, 0, 402938, 111734, 1561, 16384⟩
    (by decide) selected_cut_15731

theorem selected_cut_15732 : selected 8 ⟨402945, by decide⟩
    (prefixPartial 13 111735) = some ⟨13, 2, 0, 402945, 111735, 857, 16384⟩ := by
  decide +kernel

theorem context_13_111735_402945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111735 ⟨402945, by decide⟩ :=
  accepted_of_selected 13 111735 ⟨402945, by decide⟩ ⟨13, 2, 0, 402945, 111735, 857, 16384⟩
    (by decide) selected_cut_15732

theorem unmarked_context_12_27933_402946 : frontier 9 ⟨402946, by decide⟩
    (prefixCache 12 27933) (prefixPartial 12 27933) = false := by
  decide +kernel

theorem node_context_12_27933_402946 : EJMOriginalGlobalDAGData.nodes 9 ⟨402946, by decide⟩ =
    .split (coordinate 12) (![⟨402889, by decide⟩,⟨402911, by decide⟩,⟨402938, by decide⟩,⟨402945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27933_402946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27933 ⟨402946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27933
    ⟨402946, by decide⟩ (by decide) (![⟨402889, by decide⟩,⟨402911, by decide⟩,⟨402938, by decide⟩,⟨402945, by decide⟩]) unmarked_context_12_27933_402946 node_context_12_27933_402946
  intro a
  fin_cases a
  · exact context_13_111732_402889
  · exact context_13_111733_402911
  · exact context_13_111734_402938
  · exact context_13_111735_402945

theorem selected_cut_15733 : selected 8 ⟨402976, by decide⟩
    (prefixPartial 13 111736) = some ⟨13, 2, 0, 402976, 111736, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_111736_402976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111736 ⟨402976, by decide⟩ :=
  accepted_of_selected 13 111736 ⟨402976, by decide⟩ ⟨13, 2, 0, 402976, 111736, 1581, 16384⟩
    (by decide) selected_cut_15733

theorem selected_cut_15734 : selected 8 ⟨403012, by decide⟩
    (prefixPartial 13 111737) = some ⟨13, 2, 0, 403012, 111737, 2565, 16384⟩ := by
  decide +kernel

theorem context_13_111737_403012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111737 ⟨403012, by decide⟩ :=
  accepted_of_selected 13 111737 ⟨403012, by decide⟩ ⟨13, 2, 0, 403012, 111737, 2565, 16384⟩
    (by decide) selected_cut_15734

theorem selected_cut_15735 : selected 8 ⟨403039, by decide⟩
    (prefixPartial 13 111738) = some ⟨13, 2, 0, 403039, 111738, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_111738_403039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111738 ⟨403039, by decide⟩ :=
  accepted_of_selected 13 111738 ⟨403039, by decide⟩ ⟨13, 2, 0, 403039, 111738, 1605, 16384⟩
    (by decide) selected_cut_15735

theorem selected_cut_15736 : selected 8 ⟨403049, by decide⟩
    (prefixPartial 13 111739) = some ⟨13, 2, 0, 403049, 111739, 905, 16384⟩ := by
  decide +kernel

theorem context_13_111739_403049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111739 ⟨403049, by decide⟩ :=
  accepted_of_selected 13 111739 ⟨403049, by decide⟩ ⟨13, 2, 0, 403049, 111739, 905, 16384⟩
    (by decide) selected_cut_15736

theorem unmarked_context_12_27934_403050 : frontier 9 ⟨403050, by decide⟩
    (prefixCache 12 27934) (prefixPartial 12 27934) = false := by
  decide +kernel

theorem node_context_12_27934_403050 : EJMOriginalGlobalDAGData.nodes 9 ⟨403050, by decide⟩ =
    .split (coordinate 12) (![⟨402976, by decide⟩,⟨403012, by decide⟩,⟨403039, by decide⟩,⟨403049, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27934_403050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27934 ⟨403050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27934
    ⟨403050, by decide⟩ (by decide) (![⟨402976, by decide⟩,⟨403012, by decide⟩,⟨403039, by decide⟩,⟨403049, by decide⟩]) unmarked_context_12_27934_403050 node_context_12_27934_403050
  intro a
  fin_cases a
  · exact context_13_111736_402976
  · exact context_13_111737_403012
  · exact context_13_111738_403039
  · exact context_13_111739_403049

theorem selected_cut_15737 : selected 8 ⟨403079, by decide⟩
    (prefixPartial 13 111740) = some ⟨13, 2, 0, 403079, 111740, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_111740_403079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111740 ⟨403079, by decide⟩ :=
  accepted_of_selected 13 111740 ⟨403079, by decide⟩ ⟨13, 2, 0, 403079, 111740, 1817, 16384⟩
    (by decide) selected_cut_15737

theorem selected_cut_15738 : selected 8 ⟨403109, by decide⟩
    (prefixPartial 13 111741) = some ⟨13, 2, 0, 403109, 111741, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_111741_403109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111741 ⟨403109, by decide⟩ :=
  accepted_of_selected 13 111741 ⟨403109, by decide⟩ ⟨13, 2, 0, 403109, 111741, 2533, 16384⟩
    (by decide) selected_cut_15738

theorem selected_cut_15739 : selected 8 ⟨403134, by decide⟩
    (prefixPartial 13 111742) = some ⟨13, 2, 0, 403134, 111742, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_111742_403134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111742 ⟨403134, by decide⟩ :=
  accepted_of_selected 13 111742 ⟨403134, by decide⟩ ⟨13, 2, 0, 403134, 111742, 1821, 16384⟩
    (by decide) selected_cut_15739

theorem selected_cut_15740 : selected 8 ⟨403141, by decide⟩
    (prefixPartial 13 111743) = some ⟨13, 2, 0, 403141, 111743, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_111743_403141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111743 ⟨403141, by decide⟩ :=
  accepted_of_selected 13 111743 ⟨403141, by decide⟩ ⟨13, 2, 0, 403141, 111743, 1061, 16384⟩
    (by decide) selected_cut_15740

theorem unmarked_context_12_27935_403142 : frontier 9 ⟨403142, by decide⟩
    (prefixCache 12 27935) (prefixPartial 12 27935) = false := by
  decide +kernel

theorem node_context_12_27935_403142 : EJMOriginalGlobalDAGData.nodes 9 ⟨403142, by decide⟩ =
    .split (coordinate 12) (![⟨403079, by decide⟩,⟨403109, by decide⟩,⟨403134, by decide⟩,⟨403141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27935_403142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27935 ⟨403142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27935
    ⟨403142, by decide⟩ (by decide) (![⟨403079, by decide⟩,⟨403109, by decide⟩,⟨403134, by decide⟩,⟨403141, by decide⟩]) unmarked_context_12_27935_403142 node_context_12_27935_403142
  intro a
  fin_cases a
  · exact context_13_111740_403079
  · exact context_13_111741_403109
  · exact context_13_111742_403134
  · exact context_13_111743_403141

theorem unmarked_context_11_6983_403143 : frontier 10 ⟨403143, by decide⟩
    (prefixCache 11 6983) (prefixPartial 11 6983) = false := by
  decide +kernel

theorem node_context_11_6983_403143 : EJMOriginalGlobalDAGData.nodes 10 ⟨403143, by decide⟩ =
    .split (coordinate 11) (![⟨402873, by decide⟩,⟨402946, by decide⟩,⟨403050, by decide⟩,⟨403142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6983_403143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6983 ⟨403143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6983
    ⟨403143, by decide⟩ (by decide) (![⟨402873, by decide⟩,⟨402946, by decide⟩,⟨403050, by decide⟩,⟨403142, by decide⟩]) unmarked_context_11_6983_403143 node_context_11_6983_403143
  intro a
  fin_cases a
  · exact context_12_27932_402873
  · exact context_12_27933_402946
  · exact context_12_27934_403050
  · exact context_12_27935_403142

theorem unmarked_context_10_1745_403144 : frontier 11 ⟨403144, by decide⟩
    (prefixCache 10 1745) (prefixPartial 10 1745) = false := by
  decide +kernel

theorem node_context_10_1745_403144 : EJMOriginalGlobalDAGData.nodes 11 ⟨403144, by decide⟩ =
    .split (coordinate 10) (![⟨402205, by decide⟩,⟨402448, by decide⟩,⟨402799, by decide⟩,⟨403143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1745_403144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1745 ⟨403144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1745
    ⟨403144, by decide⟩ (by decide) (![⟨402205, by decide⟩,⟨402448, by decide⟩,⟨402799, by decide⟩,⟨403143, by decide⟩]) unmarked_context_10_1745_403144 node_context_10_1745_403144
  intro a
  fin_cases a
  · exact context_11_6980_402205
  · exact context_11_6981_402448
  · exact context_11_6982_402799
  · exact context_11_6983_403143

theorem selected_cut_15741 : selected 8 ⟨403158, by decide⟩
    (prefixPartial 13 111744) = some ⟨13, 2, 0, 403158, 111744, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_111744_403158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111744 ⟨403158, by decide⟩ :=
  accepted_of_selected 13 111744 ⟨403158, by decide⟩ ⟨13, 2, 0, 403158, 111744, 1241, 16384⟩
    (by decide) selected_cut_15741

theorem selected_cut_15742 : selected 8 ⟨403180, by decide⟩
    (prefixPartial 13 111745) = some ⟨13, 2, 0, 403180, 111745, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_111745_403180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111745 ⟨403180, by decide⟩ :=
  accepted_of_selected 13 111745 ⟨403180, by decide⟩ ⟨13, 2, 0, 403180, 111745, 2437, 16384⟩
    (by decide) selected_cut_15742

theorem selected_cut_15743 : selected 8 ⟨403203, by decide⟩
    (prefixPartial 13 111746) = some ⟨13, 2, 0, 403203, 111746, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_111746_403203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111746 ⟨403203, by decide⟩ :=
  accepted_of_selected 13 111746 ⟨403203, by decide⟩ ⟨13, 2, 0, 403203, 111746, 1385, 16384⟩
    (by decide) selected_cut_15743

theorem selected_cut_15744 : selected 8 ⟨403211, by decide⟩
    (prefixPartial 13 111747) = some ⟨13, 2, 0, 403211, 111747, 829, 16384⟩ := by
  decide +kernel

theorem context_13_111747_403211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111747 ⟨403211, by decide⟩ :=
  accepted_of_selected 13 111747 ⟨403211, by decide⟩ ⟨13, 2, 0, 403211, 111747, 829, 16384⟩
    (by decide) selected_cut_15744

theorem unmarked_context_12_27936_403212 : frontier 9 ⟨403212, by decide⟩
    (prefixCache 12 27936) (prefixPartial 12 27936) = false := by
  decide +kernel

theorem node_context_12_27936_403212 : EJMOriginalGlobalDAGData.nodes 9 ⟨403212, by decide⟩ =
    .split (coordinate 12) (![⟨403158, by decide⟩,⟨403180, by decide⟩,⟨403203, by decide⟩,⟨403211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27936_403212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27936 ⟨403212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27936
    ⟨403212, by decide⟩ (by decide) (![⟨403158, by decide⟩,⟨403180, by decide⟩,⟨403203, by decide⟩,⟨403211, by decide⟩]) unmarked_context_12_27936_403212 node_context_12_27936_403212
  intro a
  fin_cases a
  · exact context_13_111744_403158
  · exact context_13_111745_403180
  · exact context_13_111746_403203
  · exact context_13_111747_403211

theorem selected_cut_15745 : selected 8 ⟨403224, by decide⟩
    (prefixPartial 13 111748) = some ⟨13, 2, 0, 403224, 111748, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_111748_403224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111748 ⟨403224, by decide⟩ :=
  accepted_of_selected 13 111748 ⟨403224, by decide⟩ ⟨13, 2, 0, 403224, 111748, 1373, 16384⟩
    (by decide) selected_cut_15745

theorem selected_cut_15746 : selected 8 ⟨403247, by decide⟩
    (prefixPartial 13 111749) = some ⟨13, 2, 0, 403247, 111749, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_111749_403247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111749 ⟨403247, by decide⟩ :=
  accepted_of_selected 13 111749 ⟨403247, by decide⟩ ⟨13, 2, 0, 403247, 111749, 2341, 16384⟩
    (by decide) selected_cut_15746

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
