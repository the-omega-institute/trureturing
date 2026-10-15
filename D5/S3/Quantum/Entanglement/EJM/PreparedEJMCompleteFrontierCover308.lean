/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover307
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_93702_746266 : frontier 9 ⟨746266, by decide⟩
    (prefixCache 12 93702) (prefixPartial 12 93702) = false := by
  decide +kernel

theorem node_context_12_93702_746266 : EJMOriginalGlobalDAGData.nodes 9 ⟨746266, by decide⟩ =
    .split (coordinate 12) (![⟨746181, by decide⟩,⟨746234, by decide⟩,⟨746255, by decide⟩,⟨746265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93702_746266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93702 ⟨746266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93702
    ⟨746266, by decide⟩ (by decide) (![⟨746181, by decide⟩,⟨746234, by decide⟩,⟨746255, by decide⟩,⟨746265, by decide⟩]) unmarked_context_12_93702_746266 node_context_12_93702_746266
  intro a
  fin_cases a
  · exact context_13_374808_746181
  · exact context_13_374809_746234
  · exact context_13_374810_746255
  · exact context_13_374811_746265

theorem selected_cut_29572 : selected 8 ⟨746368, by decide⟩
    (prefixPartial 13 374812) = some ⟨13, 2, 0, 746368, 374812, 4025, 16384⟩ := by
  decide +kernel

theorem context_13_374812_746368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374812 ⟨746368, by decide⟩ :=
  accepted_of_selected 13 374812 ⟨746368, by decide⟩ ⟨13, 2, 0, 746368, 374812, 4025, 16384⟩
    (by decide) selected_cut_29572

theorem selected_cut_29573 : selected 8 ⟨746433, by decide⟩
    (prefixPartial 13 374813) = some ⟨13, 2, 0, 746433, 374813, 2717, 16384⟩ := by
  decide +kernel

theorem context_13_374813_746433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374813 ⟨746433, by decide⟩ :=
  accepted_of_selected 13 374813 ⟨746433, by decide⟩ ⟨13, 2, 0, 746433, 374813, 2717, 16384⟩
    (by decide) selected_cut_29573

theorem selected_cut_29574 : selected 8 ⟨746475, by decide⟩
    (prefixPartial 13 374814) = some ⟨13, 2, 0, 746475, 374814, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_374814_746475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374814 ⟨746475, by decide⟩ :=
  accepted_of_selected 13 374814 ⟨746475, by decide⟩ ⟨13, 2, 0, 746475, 374814, 2177, 16384⟩
    (by decide) selected_cut_29574

theorem selected_cut_29575 : selected 8 ⟨746510, by decide⟩
    (prefixPartial 13 374815) = some ⟨13, 2, 0, 746510, 374815, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_374815_746510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374815 ⟨746510, by decide⟩ :=
  accepted_of_selected 13 374815 ⟨746510, by decide⟩ ⟨13, 2, 0, 746510, 374815, 1233, 16384⟩
    (by decide) selected_cut_29575

theorem unmarked_context_12_93703_746511 : frontier 9 ⟨746511, by decide⟩
    (prefixCache 12 93703) (prefixPartial 12 93703) = false := by
  decide +kernel

theorem node_context_12_93703_746511 : EJMOriginalGlobalDAGData.nodes 9 ⟨746511, by decide⟩ =
    .split (coordinate 12) (![⟨746368, by decide⟩,⟨746433, by decide⟩,⟨746475, by decide⟩,⟨746510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93703_746511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93703 ⟨746511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93703
    ⟨746511, by decide⟩ (by decide) (![⟨746368, by decide⟩,⟨746433, by decide⟩,⟨746475, by decide⟩,⟨746510, by decide⟩]) unmarked_context_12_93703_746511 node_context_12_93703_746511
  intro a
  fin_cases a
  · exact context_13_374812_746368
  · exact context_13_374813_746433
  · exact context_13_374814_746475
  · exact context_13_374815_746510

theorem unmarked_context_11_23425_746512 : frontier 10 ⟨746512, by decide⟩
    (prefixCache 11 23425) (prefixPartial 11 23425) = false := by
  decide +kernel

theorem node_context_11_23425_746512 : EJMOriginalGlobalDAGData.nodes 10 ⟨746512, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨746266, by decide⟩,⟨746511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23425_746512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23425 ⟨746512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23425
    ⟨746512, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨746266, by decide⟩,⟨746511, by decide⟩]) unmarked_context_11_23425_746512 node_context_11_23425_746512
  intro a
  fin_cases a
  · exact context_12_93700_448748
  · exact context_12_93701_34034
  · exact context_12_93702_746266
  · exact context_12_93703_746511

theorem selected_cut_29576 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 93704) = some ⟨12, 1, 0, 448748, 93704, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93704_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93704 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 93704 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 93704, 1, 65536⟩
    (by decide) selected_cut_29576

theorem selected_cut_29577 : selected 8 ⟨746580, by decide⟩
    (prefixPartial 13 374820) = some ⟨13, 2, 0, 746580, 374820, 3233, 16384⟩ := by
  decide +kernel

theorem context_13_374820_746580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374820 ⟨746580, by decide⟩ :=
  accepted_of_selected 13 374820 ⟨746580, by decide⟩ ⟨13, 2, 0, 746580, 374820, 3233, 16384⟩
    (by decide) selected_cut_29577

theorem selected_cut_29578 : selected 8 ⟨746642, by decide⟩
    (prefixPartial 13 374821) = some ⟨13, 2, 0, 746642, 374821, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_374821_746642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374821 ⟨746642, by decide⟩ :=
  accepted_of_selected 13 374821 ⟨746642, by decide⟩ ⟨13, 2, 0, 746642, 374821, 2337, 16384⟩
    (by decide) selected_cut_29578

theorem selected_cut_29579 : selected 8 ⟨746682, by decide⟩
    (prefixPartial 13 374822) = some ⟨13, 2, 0, 746682, 374822, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_374822_746682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374822 ⟨746682, by decide⟩ :=
  accepted_of_selected 13 374822 ⟨746682, by decide⟩ ⟨13, 2, 0, 746682, 374822, 2069, 16384⟩
    (by decide) selected_cut_29579

theorem selected_cut_29580 : selected 8 ⟨746717, by decide⟩
    (prefixPartial 13 374823) = some ⟨13, 2, 0, 746717, 374823, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_374823_746717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374823 ⟨746717, by decide⟩ :=
  accepted_of_selected 13 374823 ⟨746717, by decide⟩ ⟨13, 2, 0, 746717, 374823, 1297, 16384⟩
    (by decide) selected_cut_29580

theorem unmarked_context_12_93705_746718 : frontier 9 ⟨746718, by decide⟩
    (prefixCache 12 93705) (prefixPartial 12 93705) = false := by
  decide +kernel

theorem node_context_12_93705_746718 : EJMOriginalGlobalDAGData.nodes 9 ⟨746718, by decide⟩ =
    .split (coordinate 12) (![⟨746580, by decide⟩,⟨746642, by decide⟩,⟨746682, by decide⟩,⟨746717, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93705_746718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93705 ⟨746718, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93705
    ⟨746718, by decide⟩ (by decide) (![⟨746580, by decide⟩,⟨746642, by decide⟩,⟨746682, by decide⟩,⟨746717, by decide⟩]) unmarked_context_12_93705_746718 node_context_12_93705_746718
  intro a
  fin_cases a
  · exact context_13_374820_746580
  · exact context_13_374821_746642
  · exact context_13_374822_746682
  · exact context_13_374823_746717

theorem selected_cut_29581 : selected 7 ⟨746743, by decide⟩
    (prefixPartial 14 1499296) = some ⟨14, 2, 0, 746743, 1499296, 581, 4096⟩ := by
  decide +kernel

theorem context_14_1499296_746743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1499296 ⟨746743, by decide⟩ :=
  accepted_of_selected 14 1499296 ⟨746743, by decide⟩ ⟨14, 2, 0, 746743, 1499296, 581, 4096⟩
    (by decide) selected_cut_29581

theorem selected_cut_29582 : selected 7 ⟨746782, by decide⟩
    (prefixPartial 14 1499297) = some ⟨14, 2, 0, 746782, 1499297, 1653, 4096⟩ := by
  decide +kernel

theorem context_14_1499297_746782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1499297 ⟨746782, by decide⟩ :=
  accepted_of_selected 14 1499297 ⟨746782, by decide⟩ ⟨14, 2, 0, 746782, 1499297, 1653, 4096⟩
    (by decide) selected_cut_29582

theorem selected_cut_29583 : selected 7 ⟨746800, by decide⟩
    (prefixPartial 14 1499298) = some ⟨14, 2, 0, 746800, 1499298, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_1499298_746800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1499298 ⟨746800, by decide⟩ :=
  accepted_of_selected 14 1499298 ⟨746800, by decide⟩ ⟨14, 2, 0, 746800, 1499298, 1053, 4096⟩
    (by decide) selected_cut_29583

theorem selected_cut_29584 : selected 7 ⟨746828, by decide⟩
    (prefixPartial 14 1499299) = some ⟨14, 2, 0, 746828, 1499299, 1205, 4096⟩ := by
  decide +kernel

theorem context_14_1499299_746828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1499299 ⟨746828, by decide⟩ :=
  accepted_of_selected 14 1499299 ⟨746828, by decide⟩ ⟨14, 2, 0, 746828, 1499299, 1205, 4096⟩
    (by decide) selected_cut_29584

theorem unmarked_context_13_374824_746829 : frontier 8 ⟨746829, by decide⟩
    (prefixCache 13 374824) (prefixPartial 13 374824) = false := by
  decide +kernel

theorem node_context_13_374824_746829 : EJMOriginalGlobalDAGData.nodes 8 ⟨746829, by decide⟩ =
    .split (coordinate 13) (![⟨746743, by decide⟩,⟨746782, by decide⟩,⟨746800, by decide⟩,⟨746828, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_374824_746829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374824 ⟨746829, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 374824
    ⟨746829, by decide⟩ (by decide) (![⟨746743, by decide⟩,⟨746782, by decide⟩,⟨746800, by decide⟩,⟨746828, by decide⟩]) unmarked_context_13_374824_746829 node_context_13_374824_746829
  intro a
  fin_cases a
  · exact context_14_1499296_746743
  · exact context_14_1499297_746782
  · exact context_14_1499298_746800
  · exact context_14_1499299_746828

theorem selected_cut_29585 : selected 8 ⟨746960, by decide⟩
    (prefixPartial 13 374825) = some ⟨13, 2, 0, 746960, 374825, 3981, 16384⟩ := by
  decide +kernel

theorem context_13_374825_746960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374825 ⟨746960, by decide⟩ :=
  accepted_of_selected 13 374825 ⟨746960, by decide⟩ ⟨13, 2, 0, 746960, 374825, 3981, 16384⟩
    (by decide) selected_cut_29585

theorem selected_cut_29586 : selected 8 ⟨747062, by decide⟩
    (prefixPartial 13 374826) = some ⟨13, 2, 0, 747062, 374826, 3185, 16384⟩ := by
  decide +kernel

theorem context_13_374826_747062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374826 ⟨747062, by decide⟩ :=
  accepted_of_selected 13 374826 ⟨747062, by decide⟩ ⟨13, 2, 0, 747062, 374826, 3185, 16384⟩
    (by decide) selected_cut_29586

theorem selected_cut_29587 : selected 8 ⟨747143, by decide⟩
    (prefixPartial 13 374827) = some ⟨13, 2, 0, 747143, 374827, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_374827_747143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374827 ⟨747143, by decide⟩ :=
  accepted_of_selected 13 374827 ⟨747143, by decide⟩ ⟨13, 2, 0, 747143, 374827, 1817, 16384⟩
    (by decide) selected_cut_29587

theorem unmarked_context_12_93706_747144 : frontier 9 ⟨747144, by decide⟩
    (prefixCache 12 93706) (prefixPartial 12 93706) = false := by
  decide +kernel

theorem node_context_12_93706_747144 : EJMOriginalGlobalDAGData.nodes 9 ⟨747144, by decide⟩ =
    .split (coordinate 12) (![⟨746829, by decide⟩,⟨746960, by decide⟩,⟨747062, by decide⟩,⟨747143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93706_747144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93706 ⟨747144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93706
    ⟨747144, by decide⟩ (by decide) (![⟨746829, by decide⟩,⟨746960, by decide⟩,⟨747062, by decide⟩,⟨747143, by decide⟩]) unmarked_context_12_93706_747144 node_context_12_93706_747144
  intro a
  fin_cases a
  · exact context_13_374824_746829
  · exact context_13_374825_746960
  · exact context_13_374826_747062
  · exact context_13_374827_747143

theorem selected_cut_29588 : selected 8 ⟨747209, by decide⟩
    (prefixPartial 13 374828) = some ⟨13, 2, 0, 747209, 374828, 3205, 16384⟩ := by
  decide +kernel

theorem context_13_374828_747209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374828 ⟨747209, by decide⟩ :=
  accepted_of_selected 13 374828 ⟨747209, by decide⟩ ⟨13, 2, 0, 747209, 374828, 3205, 16384⟩
    (by decide) selected_cut_29588

theorem selected_cut_29589 : selected 8 ⟨747279, by decide⟩
    (prefixPartial 13 374829) = some ⟨13, 2, 0, 747279, 374829, 2829, 16384⟩ := by
  decide +kernel

theorem context_13_374829_747279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374829 ⟨747279, by decide⟩ :=
  accepted_of_selected 13 374829 ⟨747279, by decide⟩ ⟨13, 2, 0, 747279, 374829, 2829, 16384⟩
    (by decide) selected_cut_29589

theorem selected_cut_29590 : selected 8 ⟨747309, by decide⟩
    (prefixPartial 13 374830) = some ⟨13, 2, 0, 747309, 374830, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_374830_747309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374830 ⟨747309, by decide⟩ :=
  accepted_of_selected 13 374830 ⟨747309, by decide⟩ ⟨13, 2, 0, 747309, 374830, 2113, 16384⟩
    (by decide) selected_cut_29590

theorem selected_cut_29591 : selected 8 ⟨747331, by decide⟩
    (prefixPartial 13 374831) = some ⟨13, 2, 0, 747331, 374831, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_374831_747331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374831 ⟨747331, by decide⟩ :=
  accepted_of_selected 13 374831 ⟨747331, by decide⟩ ⟨13, 2, 0, 747331, 374831, 1297, 16384⟩
    (by decide) selected_cut_29591

theorem unmarked_context_12_93707_747332 : frontier 9 ⟨747332, by decide⟩
    (prefixCache 12 93707) (prefixPartial 12 93707) = false := by
  decide +kernel

theorem node_context_12_93707_747332 : EJMOriginalGlobalDAGData.nodes 9 ⟨747332, by decide⟩ =
    .split (coordinate 12) (![⟨747209, by decide⟩,⟨747279, by decide⟩,⟨747309, by decide⟩,⟨747331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93707_747332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93707 ⟨747332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93707
    ⟨747332, by decide⟩ (by decide) (![⟨747209, by decide⟩,⟨747279, by decide⟩,⟨747309, by decide⟩,⟨747331, by decide⟩]) unmarked_context_12_93707_747332 node_context_12_93707_747332
  intro a
  fin_cases a
  · exact context_13_374828_747209
  · exact context_13_374829_747279
  · exact context_13_374830_747309
  · exact context_13_374831_747331

theorem unmarked_context_11_23426_747333 : frontier 10 ⟨747333, by decide⟩
    (prefixCache 11 23426) (prefixPartial 11 23426) = false := by
  decide +kernel

theorem node_context_11_23426_747333 : EJMOriginalGlobalDAGData.nodes 10 ⟨747333, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨746718, by decide⟩,⟨747144, by decide⟩,⟨747332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23426_747333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23426 ⟨747333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23426
    ⟨747333, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨746718, by decide⟩,⟨747144, by decide⟩,⟨747332, by decide⟩]) unmarked_context_11_23426_747333 node_context_11_23426_747333
  intro a
  fin_cases a
  · exact context_12_93704_448748
  · exact context_12_93705_746718
  · exact context_12_93706_747144
  · exact context_12_93707_747332

theorem selected_cut_29592 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 93708) = some ⟨12, 1, 0, 448748, 93708, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93708_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93708 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 93708 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 93708, 1, 65536⟩
    (by decide) selected_cut_29592

theorem selected_cut_29593 : selected 9 ⟨390434, by decide⟩
    (prefixPartial 12 93709) = some ⟨12, 1, 0, 390434, 93709, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93709_390434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93709 ⟨390434, by decide⟩ :=
  accepted_of_selected 12 93709 ⟨390434, by decide⟩ ⟨12, 1, 0, 390434, 93709, 1, 65536⟩
    (by decide) selected_cut_29593

theorem selected_cut_29594 : selected 8 ⟨747391, by decide⟩
    (prefixPartial 13 374840) = some ⟨13, 2, 0, 747391, 374840, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_374840_747391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374840 ⟨747391, by decide⟩ :=
  accepted_of_selected 13 374840 ⟨747391, by decide⟩ ⟨13, 2, 0, 747391, 374840, 2477, 16384⟩
    (by decide) selected_cut_29594

theorem selected_cut_29595 : selected 8 ⟨747444, by decide⟩
    (prefixPartial 13 374841) = some ⟨13, 2, 0, 747444, 374841, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_374841_747444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374841 ⟨747444, by decide⟩ :=
  accepted_of_selected 13 374841 ⟨747444, by decide⟩ ⟨13, 2, 0, 747444, 374841, 1277, 16384⟩
    (by decide) selected_cut_29595

theorem selected_cut_29596 : selected 8 ⟨747458, by decide⟩
    (prefixPartial 13 374842) = some ⟨13, 2, 0, 747458, 374842, 609, 16384⟩ := by
  decide +kernel

theorem context_13_374842_747458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374842 ⟨747458, by decide⟩ :=
  accepted_of_selected 13 374842 ⟨747458, by decide⟩ ⟨13, 2, 0, 747458, 374842, 609, 16384⟩
    (by decide) selected_cut_29596

theorem selected_cut_29597 : selected 8 ⟨747470, by decide⟩
    (prefixPartial 13 374843) = some ⟨13, 2, 0, 747470, 374843, 189, 16384⟩ := by
  decide +kernel

theorem context_13_374843_747470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374843 ⟨747470, by decide⟩ :=
  accepted_of_selected 13 374843 ⟨747470, by decide⟩ ⟨13, 2, 0, 747470, 374843, 189, 16384⟩
    (by decide) selected_cut_29597

theorem unmarked_context_12_93710_747471 : frontier 9 ⟨747471, by decide⟩
    (prefixCache 12 93710) (prefixPartial 12 93710) = false := by
  decide +kernel

theorem node_context_12_93710_747471 : EJMOriginalGlobalDAGData.nodes 9 ⟨747471, by decide⟩ =
    .split (coordinate 12) (![⟨747391, by decide⟩,⟨747444, by decide⟩,⟨747458, by decide⟩,⟨747470, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93710_747471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93710 ⟨747471, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93710
    ⟨747471, by decide⟩ (by decide) (![⟨747391, by decide⟩,⟨747444, by decide⟩,⟨747458, by decide⟩,⟨747470, by decide⟩]) unmarked_context_12_93710_747471 node_context_12_93710_747471
  intro a
  fin_cases a
  · exact context_13_374840_747391
  · exact context_13_374841_747444
  · exact context_13_374842_747458
  · exact context_13_374843_747470

theorem selected_cut_29598 : selected 9 ⟨389061, by decide⟩
    (prefixPartial 12 93711) = some ⟨12, 1, 0, 389061, 93711, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93711_389061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93711 ⟨389061, by decide⟩ :=
  accepted_of_selected 12 93711 ⟨389061, by decide⟩ ⟨12, 1, 0, 389061, 93711, 1, 65536⟩
    (by decide) selected_cut_29598

theorem unmarked_context_11_23427_747472 : frontier 10 ⟨747472, by decide⟩
    (prefixCache 11 23427) (prefixPartial 11 23427) = false := by
  decide +kernel

theorem node_context_11_23427_747472 : EJMOriginalGlobalDAGData.nodes 10 ⟨747472, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨747471, by decide⟩,⟨389061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23427_747472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23427 ⟨747472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23427
    ⟨747472, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨747471, by decide⟩,⟨389061, by decide⟩]) unmarked_context_11_23427_747472 node_context_11_23427_747472
  intro a
  fin_cases a
  · exact context_12_93708_448748
  · exact context_12_93709_390434
  · exact context_12_93710_747471
  · exact context_12_93711_389061

theorem unmarked_context_10_5856_747473 : frontier 11 ⟨747473, by decide⟩
    (prefixCache 10 5856) (prefixPartial 10 5856) = false := by
  decide +kernel

theorem node_context_10_5856_747473 : EJMOriginalGlobalDAGData.nodes 11 ⟨747473, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨746512, by decide⟩,⟨747333, by decide⟩,⟨747472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5856_747473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5856 ⟨747473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5856
    ⟨747473, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨746512, by decide⟩,⟨747333, by decide⟩,⟨747472, by decide⟩]) unmarked_context_10_5856_747473 node_context_10_5856_747473
  intro a
  fin_cases a
  · exact context_11_23424_434745
  · exact context_11_23425_746512
  · exact context_11_23426_747333
  · exact context_11_23427_747472

theorem selected_cut_29599 : selected 8 ⟨747516, by decide⟩
    (prefixPartial 13 374848) = some ⟨13, 2, 0, 747516, 374848, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_374848_747516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374848 ⟨747516, by decide⟩ :=
  accepted_of_selected 13 374848 ⟨747516, by decide⟩ ⟨13, 2, 0, 747516, 374848, 2317, 16384⟩
    (by decide) selected_cut_29599

theorem selected_cut_29600 : selected 8 ⟨747537, by decide⟩
    (prefixPartial 13 374849) = some ⟨13, 2, 0, 747537, 374849, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_374849_747537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374849 ⟨747537, by decide⟩ :=
  accepted_of_selected 13 374849 ⟨747537, by decide⟩ ⟨13, 2, 0, 747537, 374849, 1577, 16384⟩
    (by decide) selected_cut_29600

theorem selected_cut_29601 : selected 8 ⟨747556, by decide⟩
    (prefixPartial 13 374850) = some ⟨13, 2, 0, 747556, 374850, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_374850_747556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374850 ⟨747556, by decide⟩ :=
  accepted_of_selected 13 374850 ⟨747556, by decide⟩ ⟨13, 2, 0, 747556, 374850, 1393, 16384⟩
    (by decide) selected_cut_29601

theorem selected_cut_29602 : selected 8 ⟨747566, by decide⟩
    (prefixPartial 13 374851) = some ⟨13, 2, 0, 747566, 374851, 885, 16384⟩ := by
  decide +kernel

theorem context_13_374851_747566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374851 ⟨747566, by decide⟩ :=
  accepted_of_selected 13 374851 ⟨747566, by decide⟩ ⟨13, 2, 0, 747566, 374851, 885, 16384⟩
    (by decide) selected_cut_29602

theorem unmarked_context_12_93712_747567 : frontier 9 ⟨747567, by decide⟩
    (prefixCache 12 93712) (prefixPartial 12 93712) = false := by
  decide +kernel

theorem node_context_12_93712_747567 : EJMOriginalGlobalDAGData.nodes 9 ⟨747567, by decide⟩ =
    .split (coordinate 12) (![⟨747516, by decide⟩,⟨747537, by decide⟩,⟨747556, by decide⟩,⟨747566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93712_747567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93712 ⟨747567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93712
    ⟨747567, by decide⟩ (by decide) (![⟨747516, by decide⟩,⟨747537, by decide⟩,⟨747556, by decide⟩,⟨747566, by decide⟩]) unmarked_context_12_93712_747567 node_context_12_93712_747567
  intro a
  fin_cases a
  · exact context_13_374848_747516
  · exact context_13_374849_747537
  · exact context_13_374850_747556
  · exact context_13_374851_747566

theorem selected_cut_29603 : selected 8 ⟨747614, by decide⟩
    (prefixPartial 13 374852) = some ⟨13, 2, 0, 747614, 374852, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_374852_747614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374852 ⟨747614, by decide⟩ :=
  accepted_of_selected 13 374852 ⟨747614, by decide⟩ ⟨13, 2, 0, 747614, 374852, 2501, 16384⟩
    (by decide) selected_cut_29603

theorem selected_cut_29604 : selected 8 ⟨747639, by decide⟩
    (prefixPartial 13 374853) = some ⟨13, 2, 0, 747639, 374853, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_374853_747639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374853 ⟨747639, by decide⟩ :=
  accepted_of_selected 13 374853 ⟨747639, by decide⟩ ⟨13, 2, 0, 747639, 374853, 1633, 16384⟩
    (by decide) selected_cut_29604

theorem selected_cut_29605 : selected 8 ⟨747662, by decide⟩
    (prefixPartial 13 374854) = some ⟨13, 2, 0, 747662, 374854, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_374854_747662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374854 ⟨747662, by decide⟩ :=
  accepted_of_selected 13 374854 ⟨747662, by decide⟩ ⟨13, 2, 0, 747662, 374854, 1645, 16384⟩
    (by decide) selected_cut_29605

theorem selected_cut_29606 : selected 8 ⟨747669, by decide⟩
    (prefixPartial 13 374855) = some ⟨13, 2, 0, 747669, 374855, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_374855_747669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374855 ⟨747669, by decide⟩ :=
  accepted_of_selected 13 374855 ⟨747669, by decide⟩ ⟨13, 2, 0, 747669, 374855, 1049, 16384⟩
    (by decide) selected_cut_29606

theorem unmarked_context_12_93713_747670 : frontier 9 ⟨747670, by decide⟩
    (prefixCache 12 93713) (prefixPartial 12 93713) = false := by
  decide +kernel

theorem node_context_12_93713_747670 : EJMOriginalGlobalDAGData.nodes 9 ⟨747670, by decide⟩ =
    .split (coordinate 12) (![⟨747614, by decide⟩,⟨747639, by decide⟩,⟨747662, by decide⟩,⟨747669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93713_747670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93713 ⟨747670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93713
    ⟨747670, by decide⟩ (by decide) (![⟨747614, by decide⟩,⟨747639, by decide⟩,⟨747662, by decide⟩,⟨747669, by decide⟩]) unmarked_context_12_93713_747670 node_context_12_93713_747670
  intro a
  fin_cases a
  · exact context_13_374852_747614
  · exact context_13_374853_747639
  · exact context_13_374854_747662
  · exact context_13_374855_747669

theorem selected_cut_29607 : selected 8 ⟨747702, by decide⟩
    (prefixPartial 13 374856) = some ⟨13, 2, 0, 747702, 374856, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_374856_747702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374856 ⟨747702, by decide⟩ :=
  accepted_of_selected 13 374856 ⟨747702, by decide⟩ ⟨13, 2, 0, 747702, 374856, 1997, 16384⟩
    (by decide) selected_cut_29607

theorem selected_cut_29608 : selected 8 ⟨747725, by decide⟩
    (prefixPartial 13 374857) = some ⟨13, 2, 0, 747725, 374857, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_374857_747725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374857 ⟨747725, by decide⟩ :=
  accepted_of_selected 13 374857 ⟨747725, by decide⟩ ⟨13, 2, 0, 747725, 374857, 1681, 16384⟩
    (by decide) selected_cut_29608

theorem selected_cut_29609 : selected 8 ⟨747744, by decide⟩
    (prefixPartial 13 374858) = some ⟨13, 2, 0, 747744, 374858, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_374858_747744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374858 ⟨747744, by decide⟩ :=
  accepted_of_selected 13 374858 ⟨747744, by decide⟩ ⟨13, 2, 0, 747744, 374858, 1313, 16384⟩
    (by decide) selected_cut_29609

theorem selected_cut_29610 : selected 8 ⟨747752, by decide⟩
    (prefixPartial 13 374859) = some ⟨13, 2, 0, 747752, 374859, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_374859_747752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374859 ⟨747752, by decide⟩ :=
  accepted_of_selected 13 374859 ⟨747752, by decide⟩ ⟨13, 2, 0, 747752, 374859, 1005, 16384⟩
    (by decide) selected_cut_29610

theorem unmarked_context_12_93714_747753 : frontier 9 ⟨747753, by decide⟩
    (prefixCache 12 93714) (prefixPartial 12 93714) = false := by
  decide +kernel

theorem node_context_12_93714_747753 : EJMOriginalGlobalDAGData.nodes 9 ⟨747753, by decide⟩ =
    .split (coordinate 12) (![⟨747702, by decide⟩,⟨747725, by decide⟩,⟨747744, by decide⟩,⟨747752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93714_747753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93714 ⟨747753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93714
    ⟨747753, by decide⟩ (by decide) (![⟨747702, by decide⟩,⟨747725, by decide⟩,⟨747744, by decide⟩,⟨747752, by decide⟩]) unmarked_context_12_93714_747753 node_context_12_93714_747753
  intro a
  fin_cases a
  · exact context_13_374856_747702
  · exact context_13_374857_747725
  · exact context_13_374858_747744
  · exact context_13_374859_747752

theorem selected_cut_29611 : selected 8 ⟨747792, by decide⟩
    (prefixPartial 13 374860) = some ⟨13, 2, 0, 747792, 374860, 2489, 16384⟩ := by
  decide +kernel

theorem context_13_374860_747792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374860 ⟨747792, by decide⟩ :=
  accepted_of_selected 13 374860 ⟨747792, by decide⟩ ⟨13, 2, 0, 747792, 374860, 2489, 16384⟩
    (by decide) selected_cut_29611

theorem selected_cut_29612 : selected 8 ⟨747823, by decide⟩
    (prefixPartial 13 374861) = some ⟨13, 2, 0, 747823, 374861, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_374861_747823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374861 ⟨747823, by decide⟩ :=
  accepted_of_selected 13 374861 ⟨747823, by decide⟩ ⟨13, 2, 0, 747823, 374861, 1993, 16384⟩
    (by decide) selected_cut_29612

theorem selected_cut_29613 : selected 8 ⟨747849, by decide⟩
    (prefixPartial 13 374862) = some ⟨13, 2, 0, 747849, 374862, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_374862_747849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374862 ⟨747849, by decide⟩ :=
  accepted_of_selected 13 374862 ⟨747849, by decide⟩ ⟨13, 2, 0, 747849, 374862, 1713, 16384⟩
    (by decide) selected_cut_29613

theorem selected_cut_29614 : selected 8 ⟨747869, by decide⟩
    (prefixPartial 13 374863) = some ⟨13, 2, 0, 747869, 374863, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_374863_747869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374863 ⟨747869, by decide⟩ :=
  accepted_of_selected 13 374863 ⟨747869, by decide⟩ ⟨13, 2, 0, 747869, 374863, 1041, 16384⟩
    (by decide) selected_cut_29614

theorem unmarked_context_12_93715_747870 : frontier 9 ⟨747870, by decide⟩
    (prefixCache 12 93715) (prefixPartial 12 93715) = false := by
  decide +kernel

theorem node_context_12_93715_747870 : EJMOriginalGlobalDAGData.nodes 9 ⟨747870, by decide⟩ =
    .split (coordinate 12) (![⟨747792, by decide⟩,⟨747823, by decide⟩,⟨747849, by decide⟩,⟨747869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93715_747870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93715 ⟨747870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93715
    ⟨747870, by decide⟩ (by decide) (![⟨747792, by decide⟩,⟨747823, by decide⟩,⟨747849, by decide⟩,⟨747869, by decide⟩]) unmarked_context_12_93715_747870 node_context_12_93715_747870
  intro a
  fin_cases a
  · exact context_13_374860_747792
  · exact context_13_374861_747823
  · exact context_13_374862_747849
  · exact context_13_374863_747869

theorem unmarked_context_11_23428_747871 : frontier 10 ⟨747871, by decide⟩
    (prefixCache 11 23428) (prefixPartial 11 23428) = false := by
  decide +kernel

theorem node_context_11_23428_747871 : EJMOriginalGlobalDAGData.nodes 10 ⟨747871, by decide⟩ =
    .split (coordinate 11) (![⟨747567, by decide⟩,⟨747670, by decide⟩,⟨747753, by decide⟩,⟨747870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23428_747871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23428 ⟨747871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23428
    ⟨747871, by decide⟩ (by decide) (![⟨747567, by decide⟩,⟨747670, by decide⟩,⟨747753, by decide⟩,⟨747870, by decide⟩]) unmarked_context_11_23428_747871 node_context_11_23428_747871
  intro a
  fin_cases a
  · exact context_12_93712_747567
  · exact context_12_93713_747670
  · exact context_12_93714_747753
  · exact context_12_93715_747870

theorem selected_cut_29615 : selected 8 ⟨747905, by decide⟩
    (prefixPartial 13 374864) = some ⟨13, 2, 0, 747905, 374864, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_374864_747905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374864 ⟨747905, by decide⟩ :=
  accepted_of_selected 13 374864 ⟨747905, by decide⟩ ⟨13, 2, 0, 747905, 374864, 2065, 16384⟩
    (by decide) selected_cut_29615

theorem selected_cut_29616 : selected 8 ⟨747941, by decide⟩
    (prefixPartial 13 374865) = some ⟨13, 2, 0, 747941, 374865, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_374865_747941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374865 ⟨747941, by decide⟩ :=
  accepted_of_selected 13 374865 ⟨747941, by decide⟩ ⟨13, 2, 0, 747941, 374865, 2001, 16384⟩
    (by decide) selected_cut_29616

theorem selected_cut_29617 : selected 8 ⟨747962, by decide⟩
    (prefixPartial 13 374866) = some ⟨13, 2, 0, 747962, 374866, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_374866_747962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374866 ⟨747962, by decide⟩ :=
  accepted_of_selected 13 374866 ⟨747962, by decide⟩ ⟨13, 2, 0, 747962, 374866, 1389, 16384⟩
    (by decide) selected_cut_29617

theorem selected_cut_29618 : selected 8 ⟨747969, by decide⟩
    (prefixPartial 13 374867) = some ⟨13, 2, 0, 747969, 374867, 917, 16384⟩ := by
  decide +kernel

theorem context_13_374867_747969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374867 ⟨747969, by decide⟩ :=
  accepted_of_selected 13 374867 ⟨747969, by decide⟩ ⟨13, 2, 0, 747969, 374867, 917, 16384⟩
    (by decide) selected_cut_29618

theorem unmarked_context_12_93716_747970 : frontier 9 ⟨747970, by decide⟩
    (prefixCache 12 93716) (prefixPartial 12 93716) = false := by
  decide +kernel

theorem node_context_12_93716_747970 : EJMOriginalGlobalDAGData.nodes 9 ⟨747970, by decide⟩ =
    .split (coordinate 12) (![⟨747905, by decide⟩,⟨747941, by decide⟩,⟨747962, by decide⟩,⟨747969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93716_747970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93716 ⟨747970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93716
    ⟨747970, by decide⟩ (by decide) (![⟨747905, by decide⟩,⟨747941, by decide⟩,⟨747962, by decide⟩,⟨747969, by decide⟩]) unmarked_context_12_93716_747970 node_context_12_93716_747970
  intro a
  fin_cases a
  · exact context_13_374864_747905
  · exact context_13_374865_747941
  · exact context_13_374866_747962
  · exact context_13_374867_747969

theorem selected_cut_29619 : selected 8 ⟨748003, by decide⟩
    (prefixPartial 13 374868) = some ⟨13, 2, 0, 748003, 374868, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_374868_748003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374868 ⟨748003, by decide⟩ :=
  accepted_of_selected 13 374868 ⟨748003, by decide⟩ ⟨13, 2, 0, 748003, 374868, 2225, 16384⟩
    (by decide) selected_cut_29619

theorem selected_cut_29620 : selected 8 ⟨748026, by decide⟩
    (prefixPartial 13 374869) = some ⟨13, 2, 0, 748026, 374869, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_374869_748026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374869 ⟨748026, by decide⟩ :=
  accepted_of_selected 13 374869 ⟨748026, by decide⟩ ⟨13, 2, 0, 748026, 374869, 1685, 16384⟩
    (by decide) selected_cut_29620

theorem selected_cut_29621 : selected 8 ⟨748049, by decide⟩
    (prefixPartial 13 374870) = some ⟨13, 2, 0, 748049, 374870, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_374870_748049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374870 ⟨748049, by decide⟩ :=
  accepted_of_selected 13 374870 ⟨748049, by decide⟩ ⟨13, 2, 0, 748049, 374870, 1577, 16384⟩
    (by decide) selected_cut_29621

theorem selected_cut_29622 : selected 8 ⟨748058, by decide⟩
    (prefixPartial 13 374871) = some ⟨13, 2, 0, 748058, 374871, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_374871_748058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374871 ⟨748058, by decide⟩ :=
  accepted_of_selected 13 374871 ⟨748058, by decide⟩ ⟨13, 2, 0, 748058, 374871, 1021, 16384⟩
    (by decide) selected_cut_29622

theorem unmarked_context_12_93717_748059 : frontier 9 ⟨748059, by decide⟩
    (prefixCache 12 93717) (prefixPartial 12 93717) = false := by
  decide +kernel

theorem node_context_12_93717_748059 : EJMOriginalGlobalDAGData.nodes 9 ⟨748059, by decide⟩ =
    .split (coordinate 12) (![⟨748003, by decide⟩,⟨748026, by decide⟩,⟨748049, by decide⟩,⟨748058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93717_748059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93717 ⟨748059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93717
    ⟨748059, by decide⟩ (by decide) (![⟨748003, by decide⟩,⟨748026, by decide⟩,⟨748049, by decide⟩,⟨748058, by decide⟩]) unmarked_context_12_93717_748059 node_context_12_93717_748059
  intro a
  fin_cases a
  · exact context_13_374868_748003
  · exact context_13_374869_748026
  · exact context_13_374870_748049
  · exact context_13_374871_748058

theorem selected_cut_29623 : selected 8 ⟨748087, by decide⟩
    (prefixPartial 13 374872) = some ⟨13, 2, 0, 748087, 374872, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_374872_748087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374872 ⟨748087, by decide⟩ :=
  accepted_of_selected 13 374872 ⟨748087, by decide⟩ ⟨13, 2, 0, 748087, 374872, 1865, 16384⟩
    (by decide) selected_cut_29623

theorem selected_cut_29624 : selected 8 ⟨748117, by decide⟩
    (prefixPartial 13 374873) = some ⟨13, 2, 0, 748117, 374873, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_374873_748117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374873 ⟨748117, by decide⟩ :=
  accepted_of_selected 13 374873 ⟨748117, by decide⟩ ⟨13, 2, 0, 748117, 374873, 1841, 16384⟩
    (by decide) selected_cut_29624

theorem selected_cut_29625 : selected 8 ⟨748136, by decide⟩
    (prefixPartial 13 374874) = some ⟨13, 2, 0, 748136, 374874, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_374874_748136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374874 ⟨748136, by decide⟩ :=
  accepted_of_selected 13 374874 ⟨748136, by decide⟩ ⟨13, 2, 0, 748136, 374874, 1329, 16384⟩
    (by decide) selected_cut_29625

theorem selected_cut_29626 : selected 8 ⟨748143, by decide⟩
    (prefixPartial 13 374875) = some ⟨13, 2, 0, 748143, 374875, 973, 16384⟩ := by
  decide +kernel

theorem context_13_374875_748143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374875 ⟨748143, by decide⟩ :=
  accepted_of_selected 13 374875 ⟨748143, by decide⟩ ⟨13, 2, 0, 748143, 374875, 973, 16384⟩
    (by decide) selected_cut_29626

theorem unmarked_context_12_93718_748144 : frontier 9 ⟨748144, by decide⟩
    (prefixCache 12 93718) (prefixPartial 12 93718) = false := by
  decide +kernel

theorem node_context_12_93718_748144 : EJMOriginalGlobalDAGData.nodes 9 ⟨748144, by decide⟩ =
    .split (coordinate 12) (![⟨748087, by decide⟩,⟨748117, by decide⟩,⟨748136, by decide⟩,⟨748143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93718_748144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93718 ⟨748144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93718
    ⟨748144, by decide⟩ (by decide) (![⟨748087, by decide⟩,⟨748117, by decide⟩,⟨748136, by decide⟩,⟨748143, by decide⟩]) unmarked_context_12_93718_748144 node_context_12_93718_748144
  intro a
  fin_cases a
  · exact context_13_374872_748087
  · exact context_13_374873_748117
  · exact context_13_374874_748136
  · exact context_13_374875_748143

theorem selected_cut_29627 : selected 8 ⟨748185, by decide⟩
    (prefixPartial 13 374876) = some ⟨13, 2, 0, 748185, 374876, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_374876_748185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374876 ⟨748185, by decide⟩ :=
  accepted_of_selected 13 374876 ⟨748185, by decide⟩ ⟨13, 2, 0, 748185, 374876, 2285, 16384⟩
    (by decide) selected_cut_29627

theorem selected_cut_29628 : selected 8 ⟨748216, by decide⟩
    (prefixPartial 13 374877) = some ⟨13, 2, 0, 748216, 374877, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_374877_748216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374877 ⟨748216, by decide⟩ :=
  accepted_of_selected 13 374877 ⟨748216, by decide⟩ ⟨13, 2, 0, 748216, 374877, 2085, 16384⟩
    (by decide) selected_cut_29628

theorem selected_cut_29629 : selected 8 ⟨748236, by decide⟩
    (prefixPartial 13 374878) = some ⟨13, 2, 0, 748236, 374878, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_374878_748236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374878 ⟨748236, by decide⟩ :=
  accepted_of_selected 13 374878 ⟨748236, by decide⟩ ⟨13, 2, 0, 748236, 374878, 1761, 16384⟩
    (by decide) selected_cut_29629

theorem selected_cut_29630 : selected 8 ⟨748242, by decide⟩
    (prefixPartial 13 374879) = some ⟨13, 2, 0, 748242, 374879, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_374879_748242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374879 ⟨748242, by decide⟩ :=
  accepted_of_selected 13 374879 ⟨748242, by decide⟩ ⟨13, 2, 0, 748242, 374879, 1005, 16384⟩
    (by decide) selected_cut_29630

theorem unmarked_context_12_93719_748243 : frontier 9 ⟨748243, by decide⟩
    (prefixCache 12 93719) (prefixPartial 12 93719) = false := by
  decide +kernel

theorem node_context_12_93719_748243 : EJMOriginalGlobalDAGData.nodes 9 ⟨748243, by decide⟩ =
    .split (coordinate 12) (![⟨748185, by decide⟩,⟨748216, by decide⟩,⟨748236, by decide⟩,⟨748242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93719_748243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93719 ⟨748243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93719
    ⟨748243, by decide⟩ (by decide) (![⟨748185, by decide⟩,⟨748216, by decide⟩,⟨748236, by decide⟩,⟨748242, by decide⟩]) unmarked_context_12_93719_748243 node_context_12_93719_748243
  intro a
  fin_cases a
  · exact context_13_374876_748185
  · exact context_13_374877_748216
  · exact context_13_374878_748236
  · exact context_13_374879_748242

theorem unmarked_context_11_23429_748244 : frontier 10 ⟨748244, by decide⟩
    (prefixCache 11 23429) (prefixPartial 11 23429) = false := by
  decide +kernel

theorem node_context_11_23429_748244 : EJMOriginalGlobalDAGData.nodes 10 ⟨748244, by decide⟩ =
    .split (coordinate 11) (![⟨747970, by decide⟩,⟨748059, by decide⟩,⟨748144, by decide⟩,⟨748243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23429_748244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23429 ⟨748244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23429
    ⟨748244, by decide⟩ (by decide) (![⟨747970, by decide⟩,⟨748059, by decide⟩,⟨748144, by decide⟩,⟨748243, by decide⟩]) unmarked_context_11_23429_748244 node_context_11_23429_748244
  intro a
  fin_cases a
  · exact context_12_93716_747970
  · exact context_12_93717_748059
  · exact context_12_93718_748144
  · exact context_12_93719_748243

theorem selected_cut_29631 : selected 8 ⟨748268, by decide⟩
    (prefixPartial 13 374880) = some ⟨13, 2, 0, 748268, 374880, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_374880_748268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374880 ⟨748268, by decide⟩ :=
  accepted_of_selected 13 374880 ⟨748268, by decide⟩ ⟨13, 2, 0, 748268, 374880, 1373, 16384⟩
    (by decide) selected_cut_29631

theorem selected_cut_29632 : selected 8 ⟨748297, by decide⟩
    (prefixPartial 13 374881) = some ⟨13, 2, 0, 748297, 374881, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_374881_748297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374881 ⟨748297, by decide⟩ :=
  accepted_of_selected 13 374881 ⟨748297, by decide⟩ ⟨13, 2, 0, 748297, 374881, 1669, 16384⟩
    (by decide) selected_cut_29632

theorem selected_cut_29633 : selected 8 ⟨748316, by decide⟩
    (prefixPartial 13 374882) = some ⟨13, 2, 0, 748316, 374882, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_374882_748316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374882 ⟨748316, by decide⟩ :=
  accepted_of_selected 13 374882 ⟨748316, by decide⟩ ⟨13, 2, 0, 748316, 374882, 1417, 16384⟩
    (by decide) selected_cut_29633

theorem selected_cut_29634 : selected 8 ⟨748326, by decide⟩
    (prefixPartial 13 374883) = some ⟨13, 2, 0, 748326, 374883, 921, 16384⟩ := by
  decide +kernel

theorem context_13_374883_748326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374883 ⟨748326, by decide⟩ :=
  accepted_of_selected 13 374883 ⟨748326, by decide⟩ ⟨13, 2, 0, 748326, 374883, 921, 16384⟩
    (by decide) selected_cut_29634

theorem unmarked_context_12_93720_748327 : frontier 9 ⟨748327, by decide⟩
    (prefixCache 12 93720) (prefixPartial 12 93720) = false := by
  decide +kernel

theorem node_context_12_93720_748327 : EJMOriginalGlobalDAGData.nodes 9 ⟨748327, by decide⟩ =
    .split (coordinate 12) (![⟨748268, by decide⟩,⟨748297, by decide⟩,⟨748316, by decide⟩,⟨748326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93720_748327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93720 ⟨748327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93720
    ⟨748327, by decide⟩ (by decide) (![⟨748268, by decide⟩,⟨748297, by decide⟩,⟨748316, by decide⟩,⟨748326, by decide⟩]) unmarked_context_12_93720_748327 node_context_12_93720_748327
  intro a
  fin_cases a
  · exact context_13_374880_748268
  · exact context_13_374881_748297
  · exact context_13_374882_748316
  · exact context_13_374883_748326

theorem selected_cut_29635 : selected 8 ⟨748353, by decide⟩
    (prefixPartial 13 374884) = some ⟨13, 2, 0, 748353, 374884, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_374884_748353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374884 ⟨748353, by decide⟩ :=
  accepted_of_selected 13 374884 ⟨748353, by decide⟩ ⟨13, 2, 0, 748353, 374884, 1817, 16384⟩
    (by decide) selected_cut_29635

theorem selected_cut_29636 : selected 8 ⟨748377, by decide⟩
    (prefixPartial 13 374885) = some ⟨13, 2, 0, 748377, 374885, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_374885_748377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374885 ⟨748377, by decide⟩ :=
  accepted_of_selected 13 374885 ⟨748377, by decide⟩ ⟨13, 2, 0, 748377, 374885, 1445, 16384⟩
    (by decide) selected_cut_29636

theorem selected_cut_29637 : selected 8 ⟨748396, by decide⟩
    (prefixPartial 13 374886) = some ⟨13, 2, 0, 748396, 374886, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_374886_748396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374886 ⟨748396, by decide⟩ :=
  accepted_of_selected 13 374886 ⟨748396, by decide⟩ ⟨13, 2, 0, 748396, 374886, 1689, 16384⟩
    (by decide) selected_cut_29637

theorem selected_cut_29638 : selected 8 ⟨748404, by decide⟩
    (prefixPartial 13 374887) = some ⟨13, 2, 0, 748404, 374887, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_374887_748404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374887 ⟨748404, by decide⟩ :=
  accepted_of_selected 13 374887 ⟨748404, by decide⟩ ⟨13, 2, 0, 748404, 374887, 1105, 16384⟩
    (by decide) selected_cut_29638

theorem unmarked_context_12_93721_748405 : frontier 9 ⟨748405, by decide⟩
    (prefixCache 12 93721) (prefixPartial 12 93721) = false := by
  decide +kernel

theorem node_context_12_93721_748405 : EJMOriginalGlobalDAGData.nodes 9 ⟨748405, by decide⟩ =
    .split (coordinate 12) (![⟨748353, by decide⟩,⟨748377, by decide⟩,⟨748396, by decide⟩,⟨748404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93721_748405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93721 ⟨748405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93721
    ⟨748405, by decide⟩ (by decide) (![⟨748353, by decide⟩,⟨748377, by decide⟩,⟨748396, by decide⟩,⟨748404, by decide⟩]) unmarked_context_12_93721_748405 node_context_12_93721_748405
  intro a
  fin_cases a
  · exact context_13_374884_748353
  · exact context_13_374885_748377
  · exact context_13_374886_748396
  · exact context_13_374887_748404

theorem selected_cut_29639 : selected 8 ⟨748455, by decide⟩
    (prefixPartial 13 374888) = some ⟨13, 2, 0, 748455, 374888, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_374888_748455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374888 ⟨748455, by decide⟩ :=
  accepted_of_selected 13 374888 ⟨748455, by decide⟩ ⟨13, 2, 0, 748455, 374888, 2337, 16384⟩
    (by decide) selected_cut_29639

theorem selected_cut_29640 : selected 8 ⟨748520, by decide⟩
    (prefixPartial 13 374889) = some ⟨13, 2, 0, 748520, 374889, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_374889_748520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374889 ⟨748520, by decide⟩ :=
  accepted_of_selected 13 374889 ⟨748520, by decide⟩ ⟨13, 2, 0, 748520, 374889, 2637, 16384⟩
    (by decide) selected_cut_29640

theorem selected_cut_29641 : selected 8 ⟨748556, by decide⟩
    (prefixPartial 13 374890) = some ⟨13, 2, 0, 748556, 374890, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_374890_748556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374890 ⟨748556, by decide⟩ :=
  accepted_of_selected 13 374890 ⟨748556, by decide⟩ ⟨13, 2, 0, 748556, 374890, 2189, 16384⟩
    (by decide) selected_cut_29641

theorem selected_cut_29642 : selected 8 ⟨748588, by decide⟩
    (prefixPartial 13 374891) = some ⟨13, 2, 0, 748588, 374891, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_374891_748588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374891 ⟨748588, by decide⟩ :=
  accepted_of_selected 13 374891 ⟨748588, by decide⟩ ⟨13, 2, 0, 748588, 374891, 1305, 16384⟩
    (by decide) selected_cut_29642

theorem unmarked_context_12_93722_748589 : frontier 9 ⟨748589, by decide⟩
    (prefixCache 12 93722) (prefixPartial 12 93722) = false := by
  decide +kernel

theorem node_context_12_93722_748589 : EJMOriginalGlobalDAGData.nodes 9 ⟨748589, by decide⟩ =
    .split (coordinate 12) (![⟨748455, by decide⟩,⟨748520, by decide⟩,⟨748556, by decide⟩,⟨748588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93722_748589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93722 ⟨748589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93722
    ⟨748589, by decide⟩ (by decide) (![⟨748455, by decide⟩,⟨748520, by decide⟩,⟨748556, by decide⟩,⟨748588, by decide⟩]) unmarked_context_12_93722_748589 node_context_12_93722_748589
  intro a
  fin_cases a
  · exact context_13_374888_748455
  · exact context_13_374889_748520
  · exact context_13_374890_748556
  · exact context_13_374891_748588

theorem selected_cut_29643 : selected 8 ⟨748619, by decide⟩
    (prefixPartial 13 374892) = some ⟨13, 2, 0, 748619, 374892, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_374892_748619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374892 ⟨748619, by decide⟩ :=
  accepted_of_selected 13 374892 ⟨748619, by decide⟩ ⟨13, 2, 0, 748619, 374892, 1637, 16384⟩
    (by decide) selected_cut_29643

theorem selected_cut_29644 : selected 8 ⟨748654, by decide⟩
    (prefixPartial 13 374893) = some ⟨13, 2, 0, 748654, 374893, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_374893_748654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374893 ⟨748654, by decide⟩ :=
  accepted_of_selected 13 374893 ⟨748654, by decide⟩ ⟨13, 2, 0, 748654, 374893, 1921, 16384⟩
    (by decide) selected_cut_29644

theorem selected_cut_29645 : selected 8 ⟨748676, by decide⟩
    (prefixPartial 13 374894) = some ⟨13, 2, 0, 748676, 374894, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_374894_748676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374894 ⟨748676, by decide⟩ :=
  accepted_of_selected 13 374894 ⟨748676, by decide⟩ ⟨13, 2, 0, 748676, 374894, 1677, 16384⟩
    (by decide) selected_cut_29645

theorem selected_cut_29646 : selected 8 ⟨748685, by decide⟩
    (prefixPartial 13 374895) = some ⟨13, 2, 0, 748685, 374895, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_374895_748685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374895 ⟨748685, by decide⟩ :=
  accepted_of_selected 13 374895 ⟨748685, by decide⟩ ⟨13, 2, 0, 748685, 374895, 1025, 16384⟩
    (by decide) selected_cut_29646

theorem unmarked_context_12_93723_748686 : frontier 9 ⟨748686, by decide⟩
    (prefixCache 12 93723) (prefixPartial 12 93723) = false := by
  decide +kernel

theorem node_context_12_93723_748686 : EJMOriginalGlobalDAGData.nodes 9 ⟨748686, by decide⟩ =
    .split (coordinate 12) (![⟨748619, by decide⟩,⟨748654, by decide⟩,⟨748676, by decide⟩,⟨748685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93723_748686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93723 ⟨748686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93723
    ⟨748686, by decide⟩ (by decide) (![⟨748619, by decide⟩,⟨748654, by decide⟩,⟨748676, by decide⟩,⟨748685, by decide⟩]) unmarked_context_12_93723_748686 node_context_12_93723_748686
  intro a
  fin_cases a
  · exact context_13_374892_748619
  · exact context_13_374893_748654
  · exact context_13_374894_748676
  · exact context_13_374895_748685

theorem unmarked_context_11_23430_748687 : frontier 10 ⟨748687, by decide⟩
    (prefixCache 11 23430) (prefixPartial 11 23430) = false := by
  decide +kernel

theorem node_context_11_23430_748687 : EJMOriginalGlobalDAGData.nodes 10 ⟨748687, by decide⟩ =
    .split (coordinate 11) (![⟨748327, by decide⟩,⟨748405, by decide⟩,⟨748589, by decide⟩,⟨748686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23430_748687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23430 ⟨748687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23430
    ⟨748687, by decide⟩ (by decide) (![⟨748327, by decide⟩,⟨748405, by decide⟩,⟨748589, by decide⟩,⟨748686, by decide⟩]) unmarked_context_11_23430_748687 node_context_11_23430_748687
  intro a
  fin_cases a
  · exact context_12_93720_748327
  · exact context_12_93721_748405
  · exact context_12_93722_748589
  · exact context_12_93723_748686

theorem selected_cut_29647 : selected 8 ⟨748706, by decide⟩
    (prefixPartial 13 374896) = some ⟨13, 2, 0, 748706, 374896, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_374896_748706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374896 ⟨748706, by decide⟩ :=
  accepted_of_selected 13 374896 ⟨748706, by decide⟩ ⟨13, 2, 0, 748706, 374896, 1309, 16384⟩
    (by decide) selected_cut_29647

theorem selected_cut_29648 : selected 8 ⟨748731, by decide⟩
    (prefixPartial 13 374897) = some ⟨13, 2, 0, 748731, 374897, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_374897_748731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374897 ⟨748731, by decide⟩ :=
  accepted_of_selected 13 374897 ⟨748731, by decide⟩ ⟨13, 2, 0, 748731, 374897, 1609, 16384⟩
    (by decide) selected_cut_29648

theorem selected_cut_29649 : selected 8 ⟨748744, by decide⟩
    (prefixPartial 13 374898) = some ⟨13, 2, 0, 748744, 374898, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_374898_748744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374898 ⟨748744, by decide⟩ :=
  accepted_of_selected 13 374898 ⟨748744, by decide⟩ ⟨13, 2, 0, 748744, 374898, 1305, 16384⟩
    (by decide) selected_cut_29649

theorem selected_cut_29650 : selected 8 ⟨748748, by decide⟩
    (prefixPartial 13 374899) = some ⟨13, 2, 0, 748748, 374899, 841, 16384⟩ := by
  decide +kernel

theorem context_13_374899_748748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374899 ⟨748748, by decide⟩ :=
  accepted_of_selected 13 374899 ⟨748748, by decide⟩ ⟨13, 2, 0, 748748, 374899, 841, 16384⟩
    (by decide) selected_cut_29650

theorem unmarked_context_12_93724_748749 : frontier 9 ⟨748749, by decide⟩
    (prefixCache 12 93724) (prefixPartial 12 93724) = false := by
  decide +kernel

theorem node_context_12_93724_748749 : EJMOriginalGlobalDAGData.nodes 9 ⟨748749, by decide⟩ =
    .split (coordinate 12) (![⟨748706, by decide⟩,⟨748731, by decide⟩,⟨748744, by decide⟩,⟨748748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93724_748749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93724 ⟨748749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93724
    ⟨748749, by decide⟩ (by decide) (![⟨748706, by decide⟩,⟨748731, by decide⟩,⟨748744, by decide⟩,⟨748748, by decide⟩]) unmarked_context_12_93724_748749 node_context_12_93724_748749
  intro a
  fin_cases a
  · exact context_13_374896_748706
  · exact context_13_374897_748731
  · exact context_13_374898_748744
  · exact context_13_374899_748748

theorem selected_cut_29651 : selected 8 ⟨748774, by decide⟩
    (prefixPartial 13 374900) = some ⟨13, 2, 0, 748774, 374900, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_374900_748774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374900 ⟨748774, by decide⟩ :=
  accepted_of_selected 13 374900 ⟨748774, by decide⟩ ⟨13, 2, 0, 748774, 374900, 1525, 16384⟩
    (by decide) selected_cut_29651

theorem selected_cut_29652 : selected 8 ⟨748807, by decide⟩
    (prefixPartial 13 374901) = some ⟨13, 2, 0, 748807, 374901, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_374901_748807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374901 ⟨748807, by decide⟩ :=
  accepted_of_selected 13 374901 ⟨748807, by decide⟩ ⟨13, 2, 0, 748807, 374901, 1517, 16384⟩
    (by decide) selected_cut_29652

theorem selected_cut_29653 : selected 8 ⟨748824, by decide⟩
    (prefixPartial 13 374902) = some ⟨13, 2, 0, 748824, 374902, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_374902_748824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374902 ⟨748824, by decide⟩ :=
  accepted_of_selected 13 374902 ⟨748824, by decide⟩ ⟨13, 2, 0, 748824, 374902, 1549, 16384⟩
    (by decide) selected_cut_29653

theorem selected_cut_29654 : selected 8 ⟨748831, by decide⟩
    (prefixPartial 13 374903) = some ⟨13, 2, 0, 748831, 374903, 973, 16384⟩ := by
  decide +kernel

theorem context_13_374903_748831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374903 ⟨748831, by decide⟩ :=
  accepted_of_selected 13 374903 ⟨748831, by decide⟩ ⟨13, 2, 0, 748831, 374903, 973, 16384⟩
    (by decide) selected_cut_29654

theorem unmarked_context_12_93725_748832 : frontier 9 ⟨748832, by decide⟩
    (prefixCache 12 93725) (prefixPartial 12 93725) = false := by
  decide +kernel

theorem node_context_12_93725_748832 : EJMOriginalGlobalDAGData.nodes 9 ⟨748832, by decide⟩ =
    .split (coordinate 12) (![⟨748774, by decide⟩,⟨748807, by decide⟩,⟨748824, by decide⟩,⟨748831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93725_748832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93725 ⟨748832, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93725
    ⟨748832, by decide⟩ (by decide) (![⟨748774, by decide⟩,⟨748807, by decide⟩,⟨748824, by decide⟩,⟨748831, by decide⟩]) unmarked_context_12_93725_748832 node_context_12_93725_748832
  intro a
  fin_cases a
  · exact context_13_374900_748774
  · exact context_13_374901_748807
  · exact context_13_374902_748824
  · exact context_13_374903_748831

theorem selected_cut_29655 : selected 8 ⟨748852, by decide⟩
    (prefixPartial 13 374904) = some ⟨13, 2, 0, 748852, 374904, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_374904_748852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374904 ⟨748852, by decide⟩ :=
  accepted_of_selected 13 374904 ⟨748852, by decide⟩ ⟨13, 2, 0, 748852, 374904, 1217, 16384⟩
    (by decide) selected_cut_29655

theorem selected_cut_29656 : selected 8 ⟨748878, by decide⟩
    (prefixPartial 13 374905) = some ⟨13, 2, 0, 748878, 374905, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_374905_748878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374905 ⟨748878, by decide⟩ :=
  accepted_of_selected 13 374905 ⟨748878, by decide⟩ ⟨13, 2, 0, 748878, 374905, 1657, 16384⟩
    (by decide) selected_cut_29656

theorem selected_cut_29657 : selected 8 ⟨748896, by decide⟩
    (prefixPartial 13 374906) = some ⟨13, 2, 0, 748896, 374906, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_374906_748896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374906 ⟨748896, by decide⟩ :=
  accepted_of_selected 13 374906 ⟨748896, by decide⟩ ⟨13, 2, 0, 748896, 374906, 1277, 16384⟩
    (by decide) selected_cut_29657

theorem selected_cut_29658 : selected 8 ⟨748901, by decide⟩
    (prefixPartial 13 374907) = some ⟨13, 2, 0, 748901, 374907, 989, 16384⟩ := by
  decide +kernel

theorem context_13_374907_748901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374907 ⟨748901, by decide⟩ :=
  accepted_of_selected 13 374907 ⟨748901, by decide⟩ ⟨13, 2, 0, 748901, 374907, 989, 16384⟩
    (by decide) selected_cut_29658

theorem unmarked_context_12_93726_748902 : frontier 9 ⟨748902, by decide⟩
    (prefixCache 12 93726) (prefixPartial 12 93726) = false := by
  decide +kernel

theorem node_context_12_93726_748902 : EJMOriginalGlobalDAGData.nodes 9 ⟨748902, by decide⟩ =
    .split (coordinate 12) (![⟨748852, by decide⟩,⟨748878, by decide⟩,⟨748896, by decide⟩,⟨748901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93726_748902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93726 ⟨748902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93726
    ⟨748902, by decide⟩ (by decide) (![⟨748852, by decide⟩,⟨748878, by decide⟩,⟨748896, by decide⟩,⟨748901, by decide⟩]) unmarked_context_12_93726_748902 node_context_12_93726_748902
  intro a
  fin_cases a
  · exact context_13_374904_748852
  · exact context_13_374905_748878
  · exact context_13_374906_748896
  · exact context_13_374907_748901

theorem selected_cut_29659 : selected 8 ⟨748923, by decide⟩
    (prefixPartial 13 374908) = some ⟨13, 2, 0, 748923, 374908, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_374908_748923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374908 ⟨748923, by decide⟩ :=
  accepted_of_selected 13 374908 ⟨748923, by decide⟩ ⟨13, 2, 0, 748923, 374908, 1469, 16384⟩
    (by decide) selected_cut_29659

theorem selected_cut_29660 : selected 8 ⟨748955, by decide⟩
    (prefixPartial 13 374909) = some ⟨13, 2, 0, 748955, 374909, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_374909_748955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374909 ⟨748955, by decide⟩ :=
  accepted_of_selected 13 374909 ⟨748955, by decide⟩ ⟨13, 2, 0, 748955, 374909, 1909, 16384⟩
    (by decide) selected_cut_29660

theorem selected_cut_29661 : selected 8 ⟨748973, by decide⟩
    (prefixPartial 13 374910) = some ⟨13, 2, 0, 748973, 374910, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_374910_748973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374910 ⟨748973, by decide⟩ :=
  accepted_of_selected 13 374910 ⟨748973, by decide⟩ ⟨13, 2, 0, 748973, 374910, 1629, 16384⟩
    (by decide) selected_cut_29661

theorem selected_cut_29662 : selected 8 ⟨748979, by decide⟩
    (prefixPartial 13 374911) = some ⟨13, 2, 0, 748979, 374911, 973, 16384⟩ := by
  decide +kernel

theorem context_13_374911_748979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374911 ⟨748979, by decide⟩ :=
  accepted_of_selected 13 374911 ⟨748979, by decide⟩ ⟨13, 2, 0, 748979, 374911, 973, 16384⟩
    (by decide) selected_cut_29662

theorem unmarked_context_12_93727_748980 : frontier 9 ⟨748980, by decide⟩
    (prefixCache 12 93727) (prefixPartial 12 93727) = false := by
  decide +kernel

theorem node_context_12_93727_748980 : EJMOriginalGlobalDAGData.nodes 9 ⟨748980, by decide⟩ =
    .split (coordinate 12) (![⟨748923, by decide⟩,⟨748955, by decide⟩,⟨748973, by decide⟩,⟨748979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93727_748980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93727 ⟨748980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93727
    ⟨748980, by decide⟩ (by decide) (![⟨748923, by decide⟩,⟨748955, by decide⟩,⟨748973, by decide⟩,⟨748979, by decide⟩]) unmarked_context_12_93727_748980 node_context_12_93727_748980
  intro a
  fin_cases a
  · exact context_13_374908_748923
  · exact context_13_374909_748955
  · exact context_13_374910_748973
  · exact context_13_374911_748979

theorem unmarked_context_11_23431_748981 : frontier 10 ⟨748981, by decide⟩
    (prefixCache 11 23431) (prefixPartial 11 23431) = false := by
  decide +kernel

theorem node_context_11_23431_748981 : EJMOriginalGlobalDAGData.nodes 10 ⟨748981, by decide⟩ =
    .split (coordinate 11) (![⟨748749, by decide⟩,⟨748832, by decide⟩,⟨748902, by decide⟩,⟨748980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23431_748981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23431 ⟨748981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23431
    ⟨748981, by decide⟩ (by decide) (![⟨748749, by decide⟩,⟨748832, by decide⟩,⟨748902, by decide⟩,⟨748980, by decide⟩]) unmarked_context_11_23431_748981 node_context_11_23431_748981
  intro a
  fin_cases a
  · exact context_12_93724_748749
  · exact context_12_93725_748832
  · exact context_12_93726_748902
  · exact context_12_93727_748980

theorem unmarked_context_10_5857_748982 : frontier 11 ⟨748982, by decide⟩
    (prefixCache 10 5857) (prefixPartial 10 5857) = false := by
  decide +kernel

theorem node_context_10_5857_748982 : EJMOriginalGlobalDAGData.nodes 11 ⟨748982, by decide⟩ =
    .split (coordinate 10) (![⟨747871, by decide⟩,⟨748244, by decide⟩,⟨748687, by decide⟩,⟨748981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5857_748982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5857 ⟨748982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5857
    ⟨748982, by decide⟩ (by decide) (![⟨747871, by decide⟩,⟨748244, by decide⟩,⟨748687, by decide⟩,⟨748981, by decide⟩]) unmarked_context_10_5857_748982 node_context_10_5857_748982
  intro a
  fin_cases a
  · exact context_11_23428_747871
  · exact context_11_23429_748244
  · exact context_11_23430_748687
  · exact context_11_23431_748981

theorem selected_cut_29663 : selected 8 ⟨749001, by decide⟩
    (prefixPartial 13 374912) = some ⟨13, 2, 0, 749001, 374912, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_374912_749001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374912 ⟨749001, by decide⟩ :=
  accepted_of_selected 13 374912 ⟨749001, by decide⟩ ⟨13, 2, 0, 749001, 374912, 1313, 16384⟩
    (by decide) selected_cut_29663

theorem selected_cut_29664 : selected 8 ⟨749024, by decide⟩
    (prefixPartial 13 374913) = some ⟨13, 2, 0, 749024, 374913, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_374913_749024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374913 ⟨749024, by decide⟩ :=
  accepted_of_selected 13 374913 ⟨749024, by decide⟩ ⟨13, 2, 0, 749024, 374913, 1481, 16384⟩
    (by decide) selected_cut_29664

theorem selected_cut_29665 : selected 8 ⟨749043, by decide⟩
    (prefixPartial 13 374914) = some ⟨13, 2, 0, 749043, 374914, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_374914_749043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374914 ⟨749043, by decide⟩ :=
  accepted_of_selected 13 374914 ⟨749043, by decide⟩ ⟨13, 2, 0, 749043, 374914, 1337, 16384⟩
    (by decide) selected_cut_29665

theorem selected_cut_29666 : selected 8 ⟨749050, by decide⟩
    (prefixPartial 13 374915) = some ⟨13, 2, 0, 749050, 374915, 645, 16384⟩ := by
  decide +kernel

theorem context_13_374915_749050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374915 ⟨749050, by decide⟩ :=
  accepted_of_selected 13 374915 ⟨749050, by decide⟩ ⟨13, 2, 0, 749050, 374915, 645, 16384⟩
    (by decide) selected_cut_29666

theorem unmarked_context_12_93728_749051 : frontier 9 ⟨749051, by decide⟩
    (prefixCache 12 93728) (prefixPartial 12 93728) = false := by
  decide +kernel

theorem node_context_12_93728_749051 : EJMOriginalGlobalDAGData.nodes 9 ⟨749051, by decide⟩ =
    .split (coordinate 12) (![⟨749001, by decide⟩,⟨749024, by decide⟩,⟨749043, by decide⟩,⟨749050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93728_749051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93728 ⟨749051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93728
    ⟨749051, by decide⟩ (by decide) (![⟨749001, by decide⟩,⟨749024, by decide⟩,⟨749043, by decide⟩,⟨749050, by decide⟩]) unmarked_context_12_93728_749051 node_context_12_93728_749051
  intro a
  fin_cases a
  · exact context_13_374912_749001
  · exact context_13_374913_749024
  · exact context_13_374914_749043
  · exact context_13_374915_749050

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
