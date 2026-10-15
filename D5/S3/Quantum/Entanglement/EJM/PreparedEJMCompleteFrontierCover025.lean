/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover024
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_5681_78157 : frontier 9 ⟨78157, by decide⟩
    (prefixCache 12 5681) (prefixPartial 12 5681) = false := by
  decide +kernel

theorem node_context_12_5681_78157 : EJMOriginalGlobalDAGData.nodes 9 ⟨78157, by decide⟩ =
    .split (coordinate 12) (![⟨78070, by decide⟩,⟨78120, by decide⟩,⟨78145, by decide⟩,⟨78156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5681_78157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5681 ⟨78157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5681
    ⟨78157, by decide⟩ (by decide) (![⟨78070, by decide⟩,⟨78120, by decide⟩,⟨78145, by decide⟩,⟨78156, by decide⟩]) unmarked_context_12_5681_78157 node_context_12_5681_78157
  intro a
  fin_cases a
  · exact context_13_22724_78070
  · exact context_13_22725_78120
  · exact context_13_22726_78145
  · exact context_13_22727_78156

theorem selected_cut_02403 : selected 8 ⟨78169, by decide⟩
    (prefixPartial 13 22728) = some ⟨13, 2, 0, 78169, 22728, 893, 16384⟩ := by
  decide +kernel

theorem context_13_22728_78169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22728 ⟨78169, by decide⟩ :=
  accepted_of_selected 13 22728 ⟨78169, by decide⟩ ⟨13, 2, 0, 78169, 22728, 893, 16384⟩
    (by decide) selected_cut_02403

theorem selected_cut_02404 : selected 8 ⟨78200, by decide⟩
    (prefixPartial 13 22729) = some ⟨13, 2, 0, 78200, 22729, 2977, 16384⟩ := by
  decide +kernel

theorem context_13_22729_78200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22729 ⟨78200, by decide⟩ :=
  accepted_of_selected 13 22729 ⟨78200, by decide⟩ ⟨13, 2, 0, 78200, 22729, 2977, 16384⟩
    (by decide) selected_cut_02404

theorem selected_cut_02405 : selected 8 ⟨78223, by decide⟩
    (prefixPartial 13 22730) = some ⟨13, 2, 0, 78223, 22730, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_22730_78223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22730 ⟨78223, by decide⟩ :=
  accepted_of_selected 13 22730 ⟨78223, by decide⟩ ⟨13, 2, 0, 78223, 22730, 1697, 16384⟩
    (by decide) selected_cut_02405

theorem selected_cut_02406 : selected 8 ⟨78234, by decide⟩
    (prefixPartial 13 22731) = some ⟨13, 2, 0, 78234, 22731, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_22731_78234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22731 ⟨78234, by decide⟩ :=
  accepted_of_selected 13 22731 ⟨78234, by decide⟩ ⟨13, 2, 0, 78234, 22731, 1129, 16384⟩
    (by decide) selected_cut_02406

theorem unmarked_context_12_5682_78235 : frontier 9 ⟨78235, by decide⟩
    (prefixCache 12 5682) (prefixPartial 12 5682) = false := by
  decide +kernel

theorem node_context_12_5682_78235 : EJMOriginalGlobalDAGData.nodes 9 ⟨78235, by decide⟩ =
    .split (coordinate 12) (![⟨78169, by decide⟩,⟨78200, by decide⟩,⟨78223, by decide⟩,⟨78234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5682_78235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5682 ⟨78235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5682
    ⟨78235, by decide⟩ (by decide) (![⟨78169, by decide⟩,⟨78200, by decide⟩,⟨78223, by decide⟩,⟨78234, by decide⟩]) unmarked_context_12_5682_78235 node_context_12_5682_78235
  intro a
  fin_cases a
  · exact context_13_22728_78169
  · exact context_13_22729_78200
  · exact context_13_22730_78223
  · exact context_13_22731_78234

theorem selected_cut_02407 : selected 8 ⟨78250, by decide⟩
    (prefixPartial 13 22732) = some ⟨13, 2, 0, 78250, 22732, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_22732_78250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22732 ⟨78250, by decide⟩ :=
  accepted_of_selected 13 22732 ⟨78250, by decide⟩ ⟨13, 2, 0, 78250, 22732, 1149, 16384⟩
    (by decide) selected_cut_02407

theorem selected_cut_02408 : selected 8 ⟨78300, by decide⟩
    (prefixPartial 13 22733) = some ⟨13, 2, 0, 78300, 22733, 3521, 16384⟩ := by
  decide +kernel

theorem context_13_22733_78300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22733 ⟨78300, by decide⟩ :=
  accepted_of_selected 13 22733 ⟨78300, by decide⟩ ⟨13, 2, 0, 78300, 22733, 3521, 16384⟩
    (by decide) selected_cut_02408

theorem selected_cut_02409 : selected 8 ⟨78328, by decide⟩
    (prefixPartial 13 22734) = some ⟨13, 2, 0, 78328, 22734, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_22734_78328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22734 ⟨78328, by decide⟩ :=
  accepted_of_selected 13 22734 ⟨78328, by decide⟩ ⟨13, 2, 0, 78328, 22734, 1961, 16384⟩
    (by decide) selected_cut_02409

theorem selected_cut_02410 : selected 8 ⟨78345, by decide⟩
    (prefixPartial 13 22735) = some ⟨13, 2, 0, 78345, 22735, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_22735_78345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22735 ⟨78345, by decide⟩ :=
  accepted_of_selected 13 22735 ⟨78345, by decide⟩ ⟨13, 2, 0, 78345, 22735, 1121, 16384⟩
    (by decide) selected_cut_02410

theorem unmarked_context_12_5683_78346 : frontier 9 ⟨78346, by decide⟩
    (prefixCache 12 5683) (prefixPartial 12 5683) = false := by
  decide +kernel

theorem node_context_12_5683_78346 : EJMOriginalGlobalDAGData.nodes 9 ⟨78346, by decide⟩ =
    .split (coordinate 12) (![⟨78250, by decide⟩,⟨78300, by decide⟩,⟨78328, by decide⟩,⟨78345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5683_78346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5683 ⟨78346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5683
    ⟨78346, by decide⟩ (by decide) (![⟨78250, by decide⟩,⟨78300, by decide⟩,⟨78328, by decide⟩,⟨78345, by decide⟩]) unmarked_context_12_5683_78346 node_context_12_5683_78346
  intro a
  fin_cases a
  · exact context_13_22732_78250
  · exact context_13_22733_78300
  · exact context_13_22734_78328
  · exact context_13_22735_78345

theorem unmarked_context_11_1420_78347 : frontier 10 ⟨78347, by decide⟩
    (prefixCache 11 1420) (prefixPartial 11 1420) = false := by
  decide +kernel

theorem node_context_11_1420_78347 : EJMOriginalGlobalDAGData.nodes 10 ⟨78347, by decide⟩ =
    .split (coordinate 11) (![⟨78057, by decide⟩,⟨78157, by decide⟩,⟨78235, by decide⟩,⟨78346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1420_78347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1420 ⟨78347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1420
    ⟨78347, by decide⟩ (by decide) (![⟨78057, by decide⟩,⟨78157, by decide⟩,⟨78235, by decide⟩,⟨78346, by decide⟩]) unmarked_context_11_1420_78347 node_context_11_1420_78347
  intro a
  fin_cases a
  · exact context_12_5680_78057
  · exact context_12_5681_78157
  · exact context_12_5682_78235
  · exact context_12_5683_78346

theorem selected_cut_02411 : selected 8 ⟨78363, by decide⟩
    (prefixPartial 13 22736) = some ⟨13, 2, 0, 78363, 22736, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_22736_78363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22736 ⟨78363, by decide⟩ :=
  accepted_of_selected 13 22736 ⟨78363, by decide⟩ ⟨13, 2, 0, 78363, 22736, 1141, 16384⟩
    (by decide) selected_cut_02411

theorem selected_cut_02412 : selected 7 ⟨78377, by decide⟩
    (prefixPartial 14 90948) = some ⟨14, 2, 0, 78377, 90948, 973, 4096⟩ := by
  decide +kernel

theorem context_14_90948_78377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90948 ⟨78377, by decide⟩ :=
  accepted_of_selected 14 90948 ⟨78377, by decide⟩ ⟨14, 2, 0, 78377, 90948, 973, 4096⟩
    (by decide) selected_cut_02412

theorem selected_cut_02413 : selected 7 ⟨78398, by decide⟩
    (prefixPartial 14 90949) = some ⟨14, 2, 0, 78398, 90949, 1313, 4096⟩ := by
  decide +kernel

theorem context_14_90949_78398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90949 ⟨78398, by decide⟩ :=
  accepted_of_selected 14 90949 ⟨78398, by decide⟩ ⟨14, 2, 0, 78398, 90949, 1313, 4096⟩
    (by decide) selected_cut_02413

theorem selected_cut_02414 : selected 7 ⟨78406, by decide⟩
    (prefixPartial 14 90950) = some ⟨14, 2, 0, 78406, 90950, 877, 4096⟩ := by
  decide +kernel

theorem context_14_90950_78406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90950 ⟨78406, by decide⟩ :=
  accepted_of_selected 14 90950 ⟨78406, by decide⟩ ⟨14, 2, 0, 78406, 90950, 877, 4096⟩
    (by decide) selected_cut_02414

theorem selected_cut_02415 : selected 7 ⟨78423, by decide⟩
    (prefixPartial 14 90951) = some ⟨14, 2, 0, 78423, 90951, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_90951_78423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 90951 ⟨78423, by decide⟩ :=
  accepted_of_selected 14 90951 ⟨78423, by decide⟩ ⟨14, 2, 0, 78423, 90951, 1021, 4096⟩
    (by decide) selected_cut_02415

theorem unmarked_context_13_22737_78424 : frontier 8 ⟨78424, by decide⟩
    (prefixCache 13 22737) (prefixPartial 13 22737) = false := by
  decide +kernel

theorem node_context_13_22737_78424 : EJMOriginalGlobalDAGData.nodes 8 ⟨78424, by decide⟩ =
    .split (coordinate 13) (![⟨78377, by decide⟩,⟨78398, by decide⟩,⟨78406, by decide⟩,⟨78423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22737_78424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22737 ⟨78424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22737
    ⟨78424, by decide⟩ (by decide) (![⟨78377, by decide⟩,⟨78398, by decide⟩,⟨78406, by decide⟩,⟨78423, by decide⟩]) unmarked_context_13_22737_78424 node_context_13_22737_78424
  intro a
  fin_cases a
  · exact context_14_90948_78377
  · exact context_14_90949_78398
  · exact context_14_90950_78406
  · exact context_14_90951_78423

theorem selected_cut_02416 : selected 8 ⟨78469, by decide⟩
    (prefixPartial 13 22738) = some ⟨13, 2, 0, 78469, 22738, 2585, 16384⟩ := by
  decide +kernel

theorem context_13_22738_78469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22738 ⟨78469, by decide⟩ :=
  accepted_of_selected 13 22738 ⟨78469, by decide⟩ ⟨13, 2, 0, 78469, 22738, 2585, 16384⟩
    (by decide) selected_cut_02416

theorem selected_cut_02417 : selected 8 ⟨78490, by decide⟩
    (prefixPartial 13 22739) = some ⟨13, 2, 0, 78490, 22739, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_22739_78490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22739 ⟨78490, by decide⟩ :=
  accepted_of_selected 13 22739 ⟨78490, by decide⟩ ⟨13, 2, 0, 78490, 22739, 1253, 16384⟩
    (by decide) selected_cut_02417

theorem unmarked_context_12_5684_78491 : frontier 9 ⟨78491, by decide⟩
    (prefixCache 12 5684) (prefixPartial 12 5684) = false := by
  decide +kernel

theorem node_context_12_5684_78491 : EJMOriginalGlobalDAGData.nodes 9 ⟨78491, by decide⟩ =
    .split (coordinate 12) (![⟨78363, by decide⟩,⟨78424, by decide⟩,⟨78469, by decide⟩,⟨78490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5684_78491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5684 ⟨78491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5684
    ⟨78491, by decide⟩ (by decide) (![⟨78363, by decide⟩,⟨78424, by decide⟩,⟨78469, by decide⟩,⟨78490, by decide⟩]) unmarked_context_12_5684_78491 node_context_12_5684_78491
  intro a
  fin_cases a
  · exact context_13_22736_78363
  · exact context_13_22737_78424
  · exact context_13_22738_78469
  · exact context_13_22739_78490

theorem selected_cut_02418 : selected 8 ⟨78505, by decide⟩
    (prefixPartial 13 22740) = some ⟨13, 2, 0, 78505, 22740, 801, 16384⟩ := by
  decide +kernel

theorem context_13_22740_78505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22740 ⟨78505, by decide⟩ :=
  accepted_of_selected 13 22740 ⟨78505, by decide⟩ ⟨13, 2, 0, 78505, 22740, 801, 16384⟩
    (by decide) selected_cut_02418

theorem selected_cut_02419 : selected 8 ⟨78552, by decide⟩
    (prefixPartial 13 22741) = some ⟨13, 2, 0, 78552, 22741, 2957, 16384⟩ := by
  decide +kernel

theorem context_13_22741_78552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22741 ⟨78552, by decide⟩ :=
  accepted_of_selected 13 22741 ⟨78552, by decide⟩ ⟨13, 2, 0, 78552, 22741, 2957, 16384⟩
    (by decide) selected_cut_02419

theorem selected_cut_02420 : selected 8 ⟨78579, by decide⟩
    (prefixPartial 13 22742) = some ⟨13, 2, 0, 78579, 22742, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_22742_78579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22742 ⟨78579, by decide⟩ :=
  accepted_of_selected 13 22742 ⟨78579, by decide⟩ ⟨13, 2, 0, 78579, 22742, 1929, 16384⟩
    (by decide) selected_cut_02420

theorem selected_cut_02421 : selected 8 ⟨78590, by decide⟩
    (prefixPartial 13 22743) = some ⟨13, 2, 0, 78590, 22743, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_22743_78590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22743 ⟨78590, by decide⟩ :=
  accepted_of_selected 13 22743 ⟨78590, by decide⟩ ⟨13, 2, 0, 78590, 22743, 1013, 16384⟩
    (by decide) selected_cut_02421

theorem unmarked_context_12_5685_78591 : frontier 9 ⟨78591, by decide⟩
    (prefixCache 12 5685) (prefixPartial 12 5685) = false := by
  decide +kernel

theorem node_context_12_5685_78591 : EJMOriginalGlobalDAGData.nodes 9 ⟨78591, by decide⟩ =
    .split (coordinate 12) (![⟨78505, by decide⟩,⟨78552, by decide⟩,⟨78579, by decide⟩,⟨78590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5685_78591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5685 ⟨78591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5685
    ⟨78591, by decide⟩ (by decide) (![⟨78505, by decide⟩,⟨78552, by decide⟩,⟨78579, by decide⟩,⟨78590, by decide⟩]) unmarked_context_12_5685_78591 node_context_12_5685_78591
  intro a
  fin_cases a
  · exact context_13_22740_78505
  · exact context_13_22741_78552
  · exact context_13_22742_78579
  · exact context_13_22743_78590

theorem selected_cut_02422 : selected 8 ⟨78602, by decide⟩
    (prefixPartial 13 22744) = some ⟨13, 2, 0, 78602, 22744, 725, 16384⟩ := by
  decide +kernel

theorem context_13_22744_78602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22744 ⟨78602, by decide⟩ :=
  accepted_of_selected 13 22744 ⟨78602, by decide⟩ ⟨13, 2, 0, 78602, 22744, 725, 16384⟩
    (by decide) selected_cut_02422

theorem selected_cut_02423 : selected 8 ⟨78631, by decide⟩
    (prefixPartial 13 22745) = some ⟨13, 2, 0, 78631, 22745, 2689, 16384⟩ := by
  decide +kernel

theorem context_13_22745_78631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22745 ⟨78631, by decide⟩ :=
  accepted_of_selected 13 22745 ⟨78631, by decide⟩ ⟨13, 2, 0, 78631, 22745, 2689, 16384⟩
    (by decide) selected_cut_02423

theorem selected_cut_02424 : selected 8 ⟨78652, by decide⟩
    (prefixPartial 13 22746) = some ⟨13, 2, 0, 78652, 22746, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_22746_78652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22746 ⟨78652, by decide⟩ :=
  accepted_of_selected 13 22746 ⟨78652, by decide⟩ ⟨13, 2, 0, 78652, 22746, 1717, 16384⟩
    (by decide) selected_cut_02424

theorem selected_cut_02425 : selected 8 ⟨78665, by decide⟩
    (prefixPartial 13 22747) = some ⟨13, 2, 0, 78665, 22747, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_22747_78665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22747 ⟨78665, by decide⟩ :=
  accepted_of_selected 13 22747 ⟨78665, by decide⟩ ⟨13, 2, 0, 78665, 22747, 1113, 16384⟩
    (by decide) selected_cut_02425

theorem unmarked_context_12_5686_78666 : frontier 9 ⟨78666, by decide⟩
    (prefixCache 12 5686) (prefixPartial 12 5686) = false := by
  decide +kernel

theorem node_context_12_5686_78666 : EJMOriginalGlobalDAGData.nodes 9 ⟨78666, by decide⟩ =
    .split (coordinate 12) (![⟨78602, by decide⟩,⟨78631, by decide⟩,⟨78652, by decide⟩,⟨78665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5686_78666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5686 ⟨78666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5686
    ⟨78666, by decide⟩ (by decide) (![⟨78602, by decide⟩,⟨78631, by decide⟩,⟨78652, by decide⟩,⟨78665, by decide⟩]) unmarked_context_12_5686_78666 node_context_12_5686_78666
  intro a
  fin_cases a
  · exact context_13_22744_78602
  · exact context_13_22745_78631
  · exact context_13_22746_78652
  · exact context_13_22747_78665

theorem selected_cut_02426 : selected 8 ⟨78678, by decide⟩
    (prefixPartial 13 22748) = some ⟨13, 2, 0, 78678, 22748, 929, 16384⟩ := by
  decide +kernel

theorem context_13_22748_78678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22748 ⟨78678, by decide⟩ :=
  accepted_of_selected 13 22748 ⟨78678, by decide⟩ ⟨13, 2, 0, 78678, 22748, 929, 16384⟩
    (by decide) selected_cut_02426

theorem selected_cut_02427 : selected 8 ⟨78721, by decide⟩
    (prefixPartial 13 22749) = some ⟨13, 2, 0, 78721, 22749, 3069, 16384⟩ := by
  decide +kernel

theorem context_13_22749_78721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22749 ⟨78721, by decide⟩ :=
  accepted_of_selected 13 22749 ⟨78721, by decide⟩ ⟨13, 2, 0, 78721, 22749, 3069, 16384⟩
    (by decide) selected_cut_02427

theorem selected_cut_02428 : selected 8 ⟨78754, by decide⟩
    (prefixPartial 13 22750) = some ⟨13, 2, 0, 78754, 22750, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_22750_78754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22750 ⟨78754, by decide⟩ :=
  accepted_of_selected 13 22750 ⟨78754, by decide⟩ ⟨13, 2, 0, 78754, 22750, 2257, 16384⟩
    (by decide) selected_cut_02428

theorem selected_cut_02429 : selected 8 ⟨78766, by decide⟩
    (prefixPartial 13 22751) = some ⟨13, 2, 0, 78766, 22751, 993, 16384⟩ := by
  decide +kernel

theorem context_13_22751_78766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22751 ⟨78766, by decide⟩ :=
  accepted_of_selected 13 22751 ⟨78766, by decide⟩ ⟨13, 2, 0, 78766, 22751, 993, 16384⟩
    (by decide) selected_cut_02429

theorem unmarked_context_12_5687_78767 : frontier 9 ⟨78767, by decide⟩
    (prefixCache 12 5687) (prefixPartial 12 5687) = false := by
  decide +kernel

theorem node_context_12_5687_78767 : EJMOriginalGlobalDAGData.nodes 9 ⟨78767, by decide⟩ =
    .split (coordinate 12) (![⟨78678, by decide⟩,⟨78721, by decide⟩,⟨78754, by decide⟩,⟨78766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5687_78767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5687 ⟨78767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5687
    ⟨78767, by decide⟩ (by decide) (![⟨78678, by decide⟩,⟨78721, by decide⟩,⟨78754, by decide⟩,⟨78766, by decide⟩]) unmarked_context_12_5687_78767 node_context_12_5687_78767
  intro a
  fin_cases a
  · exact context_13_22748_78678
  · exact context_13_22749_78721
  · exact context_13_22750_78754
  · exact context_13_22751_78766

theorem unmarked_context_11_1421_78768 : frontier 10 ⟨78768, by decide⟩
    (prefixCache 11 1421) (prefixPartial 11 1421) = false := by
  decide +kernel

theorem node_context_11_1421_78768 : EJMOriginalGlobalDAGData.nodes 10 ⟨78768, by decide⟩ =
    .split (coordinate 11) (![⟨78491, by decide⟩,⟨78591, by decide⟩,⟨78666, by decide⟩,⟨78767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1421_78768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1421 ⟨78768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1421
    ⟨78768, by decide⟩ (by decide) (![⟨78491, by decide⟩,⟨78591, by decide⟩,⟨78666, by decide⟩,⟨78767, by decide⟩]) unmarked_context_11_1421_78768 node_context_11_1421_78768
  intro a
  fin_cases a
  · exact context_12_5684_78491
  · exact context_12_5685_78591
  · exact context_12_5686_78666
  · exact context_12_5687_78767

theorem selected_cut_02430 : selected 8 ⟨78777, by decide⟩
    (prefixPartial 13 22752) = some ⟨13, 2, 0, 78777, 22752, 729, 16384⟩ := by
  decide +kernel

theorem context_13_22752_78777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22752 ⟨78777, by decide⟩ :=
  accepted_of_selected 13 22752 ⟨78777, by decide⟩ ⟨13, 2, 0, 78777, 22752, 729, 16384⟩
    (by decide) selected_cut_02430

theorem selected_cut_02431 : selected 8 ⟨78827, by decide⟩
    (prefixPartial 13 22753) = some ⟨13, 2, 0, 78827, 22753, 3941, 16384⟩ := by
  decide +kernel

theorem context_13_22753_78827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22753 ⟨78827, by decide⟩ :=
  accepted_of_selected 13 22753 ⟨78827, by decide⟩ ⟨13, 2, 0, 78827, 22753, 3941, 16384⟩
    (by decide) selected_cut_02431

theorem selected_cut_02432 : selected 8 ⟨78857, by decide⟩
    (prefixPartial 13 22754) = some ⟨13, 2, 0, 78857, 22754, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_22754_78857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22754 ⟨78857, by decide⟩ :=
  accepted_of_selected 13 22754 ⟨78857, by decide⟩ ⟨13, 2, 0, 78857, 22754, 2509, 16384⟩
    (by decide) selected_cut_02432

theorem selected_cut_02433 : selected 8 ⟨78879, by decide⟩
    (prefixPartial 13 22755) = some ⟨13, 2, 0, 78879, 22755, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_22755_78879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22755 ⟨78879, by decide⟩ :=
  accepted_of_selected 13 22755 ⟨78879, by decide⟩ ⟨13, 2, 0, 78879, 22755, 1405, 16384⟩
    (by decide) selected_cut_02433

theorem unmarked_context_12_5688_78880 : frontier 9 ⟨78880, by decide⟩
    (prefixCache 12 5688) (prefixPartial 12 5688) = false := by
  decide +kernel

theorem node_context_12_5688_78880 : EJMOriginalGlobalDAGData.nodes 9 ⟨78880, by decide⟩ =
    .split (coordinate 12) (![⟨78777, by decide⟩,⟨78827, by decide⟩,⟨78857, by decide⟩,⟨78879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5688_78880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5688 ⟨78880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5688
    ⟨78880, by decide⟩ (by decide) (![⟨78777, by decide⟩,⟨78827, by decide⟩,⟨78857, by decide⟩,⟨78879, by decide⟩]) unmarked_context_12_5688_78880 node_context_12_5688_78880
  intro a
  fin_cases a
  · exact context_13_22752_78777
  · exact context_13_22753_78827
  · exact context_13_22754_78857
  · exact context_13_22755_78879

theorem selected_cut_02434 : selected 8 ⟨78889, by decide⟩
    (prefixPartial 13 22756) = some ⟨13, 2, 0, 78889, 22756, 585, 16384⟩ := by
  decide +kernel

theorem context_13_22756_78889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22756 ⟨78889, by decide⟩ :=
  accepted_of_selected 13 22756 ⟨78889, by decide⟩ ⟨13, 2, 0, 78889, 22756, 585, 16384⟩
    (by decide) selected_cut_02434

theorem selected_cut_02435 : selected 8 ⟨78931, by decide⟩
    (prefixPartial 13 22757) = some ⟨13, 2, 0, 78931, 22757, 3233, 16384⟩ := by
  decide +kernel

theorem context_13_22757_78931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22757 ⟨78931, by decide⟩ :=
  accepted_of_selected 13 22757 ⟨78931, by decide⟩ ⟨13, 2, 0, 78931, 22757, 3233, 16384⟩
    (by decide) selected_cut_02435

theorem selected_cut_02436 : selected 8 ⟨78955, by decide⟩
    (prefixPartial 13 22758) = some ⟨13, 2, 0, 78955, 22758, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_22758_78955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22758 ⟨78955, by decide⟩ :=
  accepted_of_selected 13 22758 ⟨78955, by decide⟩ ⟨13, 2, 0, 78955, 22758, 2021, 16384⟩
    (by decide) selected_cut_02436

theorem selected_cut_02437 : selected 8 ⟨78965, by decide⟩
    (prefixPartial 13 22759) = some ⟨13, 2, 0, 78965, 22759, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_22759_78965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22759 ⟨78965, by decide⟩ :=
  accepted_of_selected 13 22759 ⟨78965, by decide⟩ ⟨13, 2, 0, 78965, 22759, 1165, 16384⟩
    (by decide) selected_cut_02437

theorem unmarked_context_12_5689_78966 : frontier 9 ⟨78966, by decide⟩
    (prefixCache 12 5689) (prefixPartial 12 5689) = false := by
  decide +kernel

theorem node_context_12_5689_78966 : EJMOriginalGlobalDAGData.nodes 9 ⟨78966, by decide⟩ =
    .split (coordinate 12) (![⟨78889, by decide⟩,⟨78931, by decide⟩,⟨78955, by decide⟩,⟨78965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5689_78966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5689 ⟨78966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5689
    ⟨78966, by decide⟩ (by decide) (![⟨78889, by decide⟩,⟨78931, by decide⟩,⟨78955, by decide⟩,⟨78965, by decide⟩]) unmarked_context_12_5689_78966 node_context_12_5689_78966
  intro a
  fin_cases a
  · exact context_13_22756_78889
  · exact context_13_22757_78931
  · exact context_13_22758_78955
  · exact context_13_22759_78965

theorem selected_cut_02438 : selected 8 ⟨78976, by decide⟩
    (prefixPartial 13 22760) = some ⟨13, 2, 0, 78976, 22760, 697, 16384⟩ := by
  decide +kernel

theorem context_13_22760_78976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22760 ⟨78976, by decide⟩ :=
  accepted_of_selected 13 22760 ⟨78976, by decide⟩ ⟨13, 2, 0, 78976, 22760, 697, 16384⟩
    (by decide) selected_cut_02438

theorem selected_cut_02439 : selected 7 ⟨78986, by decide⟩
    (prefixPartial 14 91044) = some ⟨14, 2, 0, 78986, 91044, 1029, 4096⟩ := by
  decide +kernel

theorem context_14_91044_78986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 91044 ⟨78986, by decide⟩ :=
  accepted_of_selected 14 91044 ⟨78986, by decide⟩ ⟨14, 2, 0, 78986, 91044, 1029, 4096⟩
    (by decide) selected_cut_02439

theorem selected_cut_02440 : selected 7 ⟨79012, by decide⟩
    (prefixPartial 14 91045) = some ⟨14, 2, 0, 79012, 91045, 1473, 4096⟩ := by
  decide +kernel

theorem context_14_91045_79012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 91045 ⟨79012, by decide⟩ :=
  accepted_of_selected 14 91045 ⟨79012, by decide⟩ ⟨14, 2, 0, 79012, 91045, 1473, 4096⟩
    (by decide) selected_cut_02440

theorem selected_cut_02441 : selected 7 ⟨79028, by decide⟩
    (prefixPartial 14 91046) = some ⟨14, 2, 0, 79028, 91046, 1265, 4096⟩ := by
  decide +kernel

theorem context_14_91046_79028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 91046 ⟨79028, by decide⟩ :=
  accepted_of_selected 14 91046 ⟨79028, by decide⟩ ⟨14, 2, 0, 79028, 91046, 1265, 4096⟩
    (by decide) selected_cut_02441

theorem selected_cut_02442 : selected 7 ⟨79044, by decide⟩
    (prefixPartial 14 91047) = some ⟨14, 2, 0, 79044, 91047, 1209, 4096⟩ := by
  decide +kernel

theorem context_14_91047_79044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 91047 ⟨79044, by decide⟩ :=
  accepted_of_selected 14 91047 ⟨79044, by decide⟩ ⟨14, 2, 0, 79044, 91047, 1209, 4096⟩
    (by decide) selected_cut_02442

theorem unmarked_context_13_22761_79045 : frontier 8 ⟨79045, by decide⟩
    (prefixCache 13 22761) (prefixPartial 13 22761) = false := by
  decide +kernel

theorem node_context_13_22761_79045 : EJMOriginalGlobalDAGData.nodes 8 ⟨79045, by decide⟩ =
    .split (coordinate 13) (![⟨78986, by decide⟩,⟨79012, by decide⟩,⟨79028, by decide⟩,⟨79044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22761_79045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22761 ⟨79045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22761
    ⟨79045, by decide⟩ (by decide) (![⟨78986, by decide⟩,⟨79012, by decide⟩,⟨79028, by decide⟩,⟨79044, by decide⟩]) unmarked_context_13_22761_79045 node_context_13_22761_79045
  intro a
  fin_cases a
  · exact context_14_91044_78986
  · exact context_14_91045_79012
  · exact context_14_91046_79028
  · exact context_14_91047_79044

theorem selected_cut_02443 : selected 8 ⟨79088, by decide⟩
    (prefixPartial 13 22762) = some ⟨13, 2, 0, 79088, 22762, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_22762_79088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22762 ⟨79088, by decide⟩ :=
  accepted_of_selected 13 22762 ⟨79088, by decide⟩ ⟨13, 2, 0, 79088, 22762, 3033, 16384⟩
    (by decide) selected_cut_02443

theorem selected_cut_02444 : selected 8 ⟨79124, by decide⟩
    (prefixPartial 13 22763) = some ⟨13, 2, 0, 79124, 22763, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_22763_79124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22763 ⟨79124, by decide⟩ :=
  accepted_of_selected 13 22763 ⟨79124, by decide⟩ ⟨13, 2, 0, 79124, 22763, 1753, 16384⟩
    (by decide) selected_cut_02444

theorem unmarked_context_12_5690_79125 : frontier 9 ⟨79125, by decide⟩
    (prefixCache 12 5690) (prefixPartial 12 5690) = false := by
  decide +kernel

theorem node_context_12_5690_79125 : EJMOriginalGlobalDAGData.nodes 9 ⟨79125, by decide⟩ =
    .split (coordinate 12) (![⟨78976, by decide⟩,⟨79045, by decide⟩,⟨79088, by decide⟩,⟨79124, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5690_79125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5690 ⟨79125, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5690
    ⟨79125, by decide⟩ (by decide) (![⟨78976, by decide⟩,⟨79045, by decide⟩,⟨79088, by decide⟩,⟨79124, by decide⟩]) unmarked_context_12_5690_79125 node_context_12_5690_79125
  intro a
  fin_cases a
  · exact context_13_22760_78976
  · exact context_13_22761_79045
  · exact context_13_22762_79088
  · exact context_13_22763_79124

theorem selected_cut_02445 : selected 8 ⟨79132, by decide⟩
    (prefixPartial 13 22764) = some ⟨13, 2, 0, 79132, 22764, 389, 16384⟩ := by
  decide +kernel

theorem context_13_22764_79132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22764 ⟨79132, by decide⟩ :=
  accepted_of_selected 13 22764 ⟨79132, by decide⟩ ⟨13, 2, 0, 79132, 22764, 389, 16384⟩
    (by decide) selected_cut_02445

theorem selected_cut_02446 : selected 8 ⟨79170, by decide⟩
    (prefixPartial 13 22765) = some ⟨13, 2, 0, 79170, 22765, 3425, 16384⟩ := by
  decide +kernel

theorem context_13_22765_79170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22765 ⟨79170, by decide⟩ :=
  accepted_of_selected 13 22765 ⟨79170, by decide⟩ ⟨13, 2, 0, 79170, 22765, 3425, 16384⟩
    (by decide) selected_cut_02446

theorem selected_cut_02447 : selected 8 ⟨79195, by decide⟩
    (prefixPartial 13 22766) = some ⟨13, 2, 0, 79195, 22766, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_22766_79195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22766 ⟨79195, by decide⟩ :=
  accepted_of_selected 13 22766 ⟨79195, by decide⟩ ⟨13, 2, 0, 79195, 22766, 2069, 16384⟩
    (by decide) selected_cut_02447

theorem selected_cut_02448 : selected 8 ⟨79205, by decide⟩
    (prefixPartial 13 22767) = some ⟨13, 2, 0, 79205, 22767, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_22767_79205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22767 ⟨79205, by decide⟩ :=
  accepted_of_selected 13 22767 ⟨79205, by decide⟩ ⟨13, 2, 0, 79205, 22767, 1109, 16384⟩
    (by decide) selected_cut_02448

theorem unmarked_context_12_5691_79206 : frontier 9 ⟨79206, by decide⟩
    (prefixCache 12 5691) (prefixPartial 12 5691) = false := by
  decide +kernel

theorem node_context_12_5691_79206 : EJMOriginalGlobalDAGData.nodes 9 ⟨79206, by decide⟩ =
    .split (coordinate 12) (![⟨79132, by decide⟩,⟨79170, by decide⟩,⟨79195, by decide⟩,⟨79205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5691_79206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5691 ⟨79206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5691
    ⟨79206, by decide⟩ (by decide) (![⟨79132, by decide⟩,⟨79170, by decide⟩,⟨79195, by decide⟩,⟨79205, by decide⟩]) unmarked_context_12_5691_79206 node_context_12_5691_79206
  intro a
  fin_cases a
  · exact context_13_22764_79132
  · exact context_13_22765_79170
  · exact context_13_22766_79195
  · exact context_13_22767_79205

theorem unmarked_context_11_1422_79207 : frontier 10 ⟨79207, by decide⟩
    (prefixCache 11 1422) (prefixPartial 11 1422) = false := by
  decide +kernel

theorem node_context_11_1422_79207 : EJMOriginalGlobalDAGData.nodes 10 ⟨79207, by decide⟩ =
    .split (coordinate 11) (![⟨78880, by decide⟩,⟨78966, by decide⟩,⟨79125, by decide⟩,⟨79206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1422_79207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1422 ⟨79207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1422
    ⟨79207, by decide⟩ (by decide) (![⟨78880, by decide⟩,⟨78966, by decide⟩,⟨79125, by decide⟩,⟨79206, by decide⟩]) unmarked_context_11_1422_79207 node_context_11_1422_79207
  intro a
  fin_cases a
  · exact context_12_5688_78880
  · exact context_12_5689_78966
  · exact context_12_5690_79125
  · exact context_12_5691_79206

theorem selected_cut_02449 : selected 8 ⟨79211, by decide⟩
    (prefixPartial 13 22768) = some ⟨13, 2, 0, 79211, 22768, 289, 16384⟩ := by
  decide +kernel

theorem context_13_22768_79211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22768 ⟨79211, by decide⟩ :=
  accepted_of_selected 13 22768 ⟨79211, by decide⟩ ⟨13, 2, 0, 79211, 22768, 289, 16384⟩
    (by decide) selected_cut_02449

theorem selected_cut_02450 : selected 8 ⟨79259, by decide⟩
    (prefixPartial 13 22769) = some ⟨13, 2, 0, 79259, 22769, 3973, 16384⟩ := by
  decide +kernel

theorem context_13_22769_79259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22769 ⟨79259, by decide⟩ :=
  accepted_of_selected 13 22769 ⟨79259, by decide⟩ ⟨13, 2, 0, 79259, 22769, 3973, 16384⟩
    (by decide) selected_cut_02450

theorem selected_cut_02451 : selected 8 ⟨79303, by decide⟩
    (prefixPartial 13 22770) = some ⟨13, 2, 0, 79303, 22770, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_22770_79303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22770 ⟨79303, by decide⟩ :=
  accepted_of_selected 13 22770 ⟨79303, by decide⟩ ⟨13, 2, 0, 79303, 22770, 2637, 16384⟩
    (by decide) selected_cut_02451

theorem selected_cut_02452 : selected 8 ⟨79319, by decide⟩
    (prefixPartial 13 22771) = some ⟨13, 2, 0, 79319, 22771, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_22771_79319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22771 ⟨79319, by decide⟩ :=
  accepted_of_selected 13 22771 ⟨79319, by decide⟩ ⟨13, 2, 0, 79319, 22771, 1189, 16384⟩
    (by decide) selected_cut_02452

theorem unmarked_context_12_5692_79320 : frontier 9 ⟨79320, by decide⟩
    (prefixCache 12 5692) (prefixPartial 12 5692) = false := by
  decide +kernel

theorem node_context_12_5692_79320 : EJMOriginalGlobalDAGData.nodes 9 ⟨79320, by decide⟩ =
    .split (coordinate 12) (![⟨79211, by decide⟩,⟨79259, by decide⟩,⟨79303, by decide⟩,⟨79319, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5692_79320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5692 ⟨79320, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5692
    ⟨79320, by decide⟩ (by decide) (![⟨79211, by decide⟩,⟨79259, by decide⟩,⟨79303, by decide⟩,⟨79319, by decide⟩]) unmarked_context_12_5692_79320 node_context_12_5692_79320
  intro a
  fin_cases a
  · exact context_13_22768_79211
  · exact context_13_22769_79259
  · exact context_13_22770_79303
  · exact context_13_22771_79319

theorem selected_cut_02453 : selected 8 ⟨79325, by decide⟩
    (prefixPartial 13 22772) = some ⟨13, 2, 0, 79325, 22772, 193, 16384⟩ := by
  decide +kernel

theorem context_13_22772_79325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22772 ⟨79325, by decide⟩ :=
  accepted_of_selected 13 22772 ⟨79325, by decide⟩ ⟨13, 2, 0, 79325, 22772, 193, 16384⟩
    (by decide) selected_cut_02453

theorem selected_cut_02454 : selected 8 ⟨79362, by decide⟩
    (prefixPartial 13 22773) = some ⟨13, 2, 0, 79362, 22773, 3133, 16384⟩ := by
  decide +kernel

theorem context_13_22773_79362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22773 ⟨79362, by decide⟩ :=
  accepted_of_selected 13 22773 ⟨79362, by decide⟩ ⟨13, 2, 0, 79362, 22773, 3133, 16384⟩
    (by decide) selected_cut_02454

theorem selected_cut_02455 : selected 8 ⟨79393, by decide⟩
    (prefixPartial 13 22774) = some ⟨13, 2, 0, 79393, 22774, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_22774_79393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22774 ⟨79393, by decide⟩ :=
  accepted_of_selected 13 22774 ⟨79393, by decide⟩ ⟨13, 2, 0, 79393, 22774, 2137, 16384⟩
    (by decide) selected_cut_02455

theorem selected_cut_02456 : selected 8 ⟨79404, by decide⟩
    (prefixPartial 13 22775) = some ⟨13, 2, 0, 79404, 22775, 981, 16384⟩ := by
  decide +kernel

theorem context_13_22775_79404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22775 ⟨79404, by decide⟩ :=
  accepted_of_selected 13 22775 ⟨79404, by decide⟩ ⟨13, 2, 0, 79404, 22775, 981, 16384⟩
    (by decide) selected_cut_02456

theorem unmarked_context_12_5693_79405 : frontier 9 ⟨79405, by decide⟩
    (prefixCache 12 5693) (prefixPartial 12 5693) = false := by
  decide +kernel

theorem node_context_12_5693_79405 : EJMOriginalGlobalDAGData.nodes 9 ⟨79405, by decide⟩ =
    .split (coordinate 12) (![⟨79325, by decide⟩,⟨79362, by decide⟩,⟨79393, by decide⟩,⟨79404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5693_79405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5693 ⟨79405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5693
    ⟨79405, by decide⟩ (by decide) (![⟨79325, by decide⟩,⟨79362, by decide⟩,⟨79393, by decide⟩,⟨79404, by decide⟩]) unmarked_context_12_5693_79405 node_context_12_5693_79405
  intro a
  fin_cases a
  · exact context_13_22772_79325
  · exact context_13_22773_79362
  · exact context_13_22774_79393
  · exact context_13_22775_79404

theorem selected_cut_02457 : selected 8 ⟨79410, by decide⟩
    (prefixPartial 13 22776) = some ⟨13, 2, 0, 79410, 22776, 141, 16384⟩ := by
  decide +kernel

theorem context_13_22776_79410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22776 ⟨79410, by decide⟩ :=
  accepted_of_selected 13 22776 ⟨79410, by decide⟩ ⟨13, 2, 0, 79410, 22776, 141, 16384⟩
    (by decide) selected_cut_02457

theorem selected_cut_02458 : selected 8 ⟨79439, by decide⟩
    (prefixPartial 13 22777) = some ⟨13, 2, 0, 79439, 22777, 2929, 16384⟩ := by
  decide +kernel

theorem context_13_22777_79439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22777 ⟨79439, by decide⟩ :=
  accepted_of_selected 13 22777 ⟨79439, by decide⟩ ⟨13, 2, 0, 79439, 22777, 2929, 16384⟩
    (by decide) selected_cut_02458

theorem selected_cut_02459 : selected 8 ⟨79460, by decide⟩
    (prefixPartial 13 22778) = some ⟨13, 2, 0, 79460, 22778, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_22778_79460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22778 ⟨79460, by decide⟩ :=
  accepted_of_selected 13 22778 ⟨79460, by decide⟩ ⟨13, 2, 0, 79460, 22778, 1845, 16384⟩
    (by decide) selected_cut_02459

theorem selected_cut_02460 : selected 8 ⟨79469, by decide⟩
    (prefixPartial 13 22779) = some ⟨13, 2, 0, 79469, 22779, 985, 16384⟩ := by
  decide +kernel

theorem context_13_22779_79469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22779 ⟨79469, by decide⟩ :=
  accepted_of_selected 13 22779 ⟨79469, by decide⟩ ⟨13, 2, 0, 79469, 22779, 985, 16384⟩
    (by decide) selected_cut_02460

theorem unmarked_context_12_5694_79470 : frontier 9 ⟨79470, by decide⟩
    (prefixCache 12 5694) (prefixPartial 12 5694) = false := by
  decide +kernel

theorem node_context_12_5694_79470 : EJMOriginalGlobalDAGData.nodes 9 ⟨79470, by decide⟩ =
    .split (coordinate 12) (![⟨79410, by decide⟩,⟨79439, by decide⟩,⟨79460, by decide⟩,⟨79469, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5694_79470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5694 ⟨79470, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5694
    ⟨79470, by decide⟩ (by decide) (![⟨79410, by decide⟩,⟨79439, by decide⟩,⟨79460, by decide⟩,⟨79469, by decide⟩]) unmarked_context_12_5694_79470 node_context_12_5694_79470
  intro a
  fin_cases a
  · exact context_13_22776_79410
  · exact context_13_22777_79439
  · exact context_13_22778_79460
  · exact context_13_22779_79469

theorem selected_cut_02461 : selected 8 ⟨79474, by decide⟩
    (prefixPartial 13 22780) = some ⟨13, 2, 0, 79474, 22780, 97, 16384⟩ := by
  decide +kernel

theorem context_13_22780_79474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22780 ⟨79474, by decide⟩ :=
  accepted_of_selected 13 22780 ⟨79474, by decide⟩ ⟨13, 2, 0, 79474, 22780, 97, 16384⟩
    (by decide) selected_cut_02461

theorem selected_cut_02462 : selected 8 ⟨79508, by decide⟩
    (prefixPartial 13 22781) = some ⟨13, 2, 0, 79508, 22781, 3025, 16384⟩ := by
  decide +kernel

theorem context_13_22781_79508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22781 ⟨79508, by decide⟩ :=
  accepted_of_selected 13 22781 ⟨79508, by decide⟩ ⟨13, 2, 0, 79508, 22781, 3025, 16384⟩
    (by decide) selected_cut_02462

theorem selected_cut_02463 : selected 8 ⟨79528, by decide⟩
    (prefixPartial 13 22782) = some ⟨13, 2, 0, 79528, 22782, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_22782_79528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22782 ⟨79528, by decide⟩ :=
  accepted_of_selected 13 22782 ⟨79528, by decide⟩ ⟨13, 2, 0, 79528, 22782, 2061, 16384⟩
    (by decide) selected_cut_02463

theorem selected_cut_02464 : selected 8 ⟨79539, by decide⟩
    (prefixPartial 13 22783) = some ⟨13, 2, 0, 79539, 22783, 993, 16384⟩ := by
  decide +kernel

theorem context_13_22783_79539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22783 ⟨79539, by decide⟩ :=
  accepted_of_selected 13 22783 ⟨79539, by decide⟩ ⟨13, 2, 0, 79539, 22783, 993, 16384⟩
    (by decide) selected_cut_02464

theorem unmarked_context_12_5695_79540 : frontier 9 ⟨79540, by decide⟩
    (prefixCache 12 5695) (prefixPartial 12 5695) = false := by
  decide +kernel

theorem node_context_12_5695_79540 : EJMOriginalGlobalDAGData.nodes 9 ⟨79540, by decide⟩ =
    .split (coordinate 12) (![⟨79474, by decide⟩,⟨79508, by decide⟩,⟨79528, by decide⟩,⟨79539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5695_79540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5695 ⟨79540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5695
    ⟨79540, by decide⟩ (by decide) (![⟨79474, by decide⟩,⟨79508, by decide⟩,⟨79528, by decide⟩,⟨79539, by decide⟩]) unmarked_context_12_5695_79540 node_context_12_5695_79540
  intro a
  fin_cases a
  · exact context_13_22780_79474
  · exact context_13_22781_79508
  · exact context_13_22782_79528
  · exact context_13_22783_79539

theorem unmarked_context_11_1423_79541 : frontier 10 ⟨79541, by decide⟩
    (prefixCache 11 1423) (prefixPartial 11 1423) = false := by
  decide +kernel

theorem node_context_11_1423_79541 : EJMOriginalGlobalDAGData.nodes 10 ⟨79541, by decide⟩ =
    .split (coordinate 11) (![⟨79320, by decide⟩,⟨79405, by decide⟩,⟨79470, by decide⟩,⟨79540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1423_79541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1423 ⟨79541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1423
    ⟨79541, by decide⟩ (by decide) (![⟨79320, by decide⟩,⟨79405, by decide⟩,⟨79470, by decide⟩,⟨79540, by decide⟩]) unmarked_context_11_1423_79541 node_context_11_1423_79541
  intro a
  fin_cases a
  · exact context_12_5692_79320
  · exact context_12_5693_79405
  · exact context_12_5694_79470
  · exact context_12_5695_79540

theorem unmarked_context_10_355_79542 : frontier 11 ⟨79542, by decide⟩
    (prefixCache 10 355) (prefixPartial 10 355) = false := by
  decide +kernel

theorem node_context_10_355_79542 : EJMOriginalGlobalDAGData.nodes 11 ⟨79542, by decide⟩ =
    .split (coordinate 10) (![⟨78347, by decide⟩,⟨78768, by decide⟩,⟨79207, by decide⟩,⟨79541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_355_79542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 355 ⟨79542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 355
    ⟨79542, by decide⟩ (by decide) (![⟨78347, by decide⟩,⟨78768, by decide⟩,⟨79207, by decide⟩,⟨79541, by decide⟩]) unmarked_context_10_355_79542 node_context_10_355_79542
  intro a
  fin_cases a
  · exact context_11_1420_78347
  · exact context_11_1421_78768
  · exact context_11_1422_79207
  · exact context_11_1423_79541

theorem unmarked_context_9_88_79543 : frontier 12 ⟨79543, by decide⟩
    (prefixCache 9 88) (prefixPartial 9 88) = false := by
  decide +kernel

theorem node_context_9_88_79543 : EJMOriginalGlobalDAGData.nodes 12 ⟨79543, by decide⟩ =
    .split (coordinate 9) (![⟨73943, by decide⟩,⟨76127, by decide⟩,⟨77937, by decide⟩,⟨79542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_88_79543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 88 ⟨79543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 88
    ⟨79543, by decide⟩ (by decide) (![⟨73943, by decide⟩,⟨76127, by decide⟩,⟨77937, by decide⟩,⟨79542, by decide⟩]) unmarked_context_9_88_79543 node_context_9_88_79543
  intro a
  fin_cases a
  · exact context_10_352_73943
  · exact context_10_353_76127
  · exact context_10_354_77937
  · exact context_10_355_79542

theorem selected_cut_02465 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22784) = some ⟨13, 1, 0, 3444, 22784, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22784_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22784 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22784 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22784, 1, 16384⟩
    (by decide) selected_cut_02465

theorem selected_cut_02466 : selected 8 ⟨79569, by decide⟩
    (prefixPartial 13 22785) = some ⟨13, 2, 0, 79569, 22785, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_22785_79569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22785 ⟨79569, by decide⟩ :=
  accepted_of_selected 13 22785 ⟨79569, by decide⟩ ⟨13, 2, 0, 79569, 22785, 2257, 16384⟩
    (by decide) selected_cut_02466

theorem selected_cut_02467 : selected 8 ⟨79589, by decide⟩
    (prefixPartial 13 22786) = some ⟨13, 2, 0, 79589, 22786, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_22786_79589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22786 ⟨79589, by decide⟩ :=
  accepted_of_selected 13 22786 ⟨79589, by decide⟩ ⟨13, 2, 0, 79589, 22786, 1905, 16384⟩
    (by decide) selected_cut_02467

theorem selected_cut_02468 : selected 8 ⟨79599, by decide⟩
    (prefixPartial 13 22787) = some ⟨13, 2, 0, 79599, 22787, 849, 16384⟩ := by
  decide +kernel

theorem context_13_22787_79599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22787 ⟨79599, by decide⟩ :=
  accepted_of_selected 13 22787 ⟨79599, by decide⟩ ⟨13, 2, 0, 79599, 22787, 849, 16384⟩
    (by decide) selected_cut_02468

theorem unmarked_context_12_5696_79600 : frontier 9 ⟨79600, by decide⟩
    (prefixCache 12 5696) (prefixPartial 12 5696) = false := by
  decide +kernel

theorem node_context_12_5696_79600 : EJMOriginalGlobalDAGData.nodes 9 ⟨79600, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨79569, by decide⟩,⟨79589, by decide⟩,⟨79599, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5696_79600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5696 ⟨79600, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5696
    ⟨79600, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨79569, by decide⟩,⟨79589, by decide⟩,⟨79599, by decide⟩]) unmarked_context_12_5696_79600 node_context_12_5696_79600
  intro a
  fin_cases a
  · exact context_13_22784_3444
  · exact context_13_22785_79569
  · exact context_13_22786_79589
  · exact context_13_22787_79599

theorem selected_cut_02469 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22788) = some ⟨13, 1, 0, 3444, 22788, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22788_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22788 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22788 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22788, 1, 16384⟩
    (by decide) selected_cut_02469

theorem selected_cut_02470 : selected 8 ⟨79630, by decide⟩
    (prefixPartial 13 22789) = some ⟨13, 2, 0, 79630, 22789, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_22789_79630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22789 ⟨79630, by decide⟩ :=
  accepted_of_selected 13 22789 ⟨79630, by decide⟩ ⟨13, 2, 0, 79630, 22789, 2561, 16384⟩
    (by decide) selected_cut_02470

theorem selected_cut_02471 : selected 8 ⟨79652, by decide⟩
    (prefixPartial 13 22790) = some ⟨13, 2, 0, 79652, 22790, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_22790_79652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22790 ⟨79652, by decide⟩ :=
  accepted_of_selected 13 22790 ⟨79652, by decide⟩ ⟨13, 2, 0, 79652, 22790, 1893, 16384⟩
    (by decide) selected_cut_02471

theorem selected_cut_02472 : selected 8 ⟨79662, by decide⟩
    (prefixPartial 13 22791) = some ⟨13, 2, 0, 79662, 22791, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_22791_79662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22791 ⟨79662, by decide⟩ :=
  accepted_of_selected 13 22791 ⟨79662, by decide⟩ ⟨13, 2, 0, 79662, 22791, 1045, 16384⟩
    (by decide) selected_cut_02472

theorem unmarked_context_12_5697_79663 : frontier 9 ⟨79663, by decide⟩
    (prefixCache 12 5697) (prefixPartial 12 5697) = false := by
  decide +kernel

theorem node_context_12_5697_79663 : EJMOriginalGlobalDAGData.nodes 9 ⟨79663, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨79630, by decide⟩,⟨79652, by decide⟩,⟨79662, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5697_79663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5697 ⟨79663, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5697
    ⟨79663, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨79630, by decide⟩,⟨79652, by decide⟩,⟨79662, by decide⟩]) unmarked_context_12_5697_79663 node_context_12_5697_79663
  intro a
  fin_cases a
  · exact context_13_22788_3444
  · exact context_13_22789_79630
  · exact context_13_22790_79652
  · exact context_13_22791_79662

theorem selected_cut_02473 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22792) = some ⟨13, 1, 0, 3444, 22792, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22792_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22792 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22792 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22792, 1, 16384⟩
    (by decide) selected_cut_02473

theorem selected_cut_02474 : selected 8 ⟨79693, by decide⟩
    (prefixPartial 13 22793) = some ⟨13, 2, 0, 79693, 22793, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_22793_79693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22793 ⟨79693, by decide⟩ :=
  accepted_of_selected 13 22793 ⟨79693, by decide⟩ ⟨13, 2, 0, 79693, 22793, 2773, 16384⟩
    (by decide) selected_cut_02474

theorem selected_cut_02475 : selected 8 ⟨79716, by decide⟩
    (prefixPartial 13 22794) = some ⟨13, 2, 0, 79716, 22794, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_22794_79716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22794 ⟨79716, by decide⟩ :=
  accepted_of_selected 13 22794 ⟨79716, by decide⟩ ⟨13, 2, 0, 79716, 22794, 1801, 16384⟩
    (by decide) selected_cut_02475

theorem selected_cut_02476 : selected 8 ⟨79730, by decide⟩
    (prefixPartial 13 22795) = some ⟨13, 2, 0, 79730, 22795, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_22795_79730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22795 ⟨79730, by decide⟩ :=
  accepted_of_selected 13 22795 ⟨79730, by decide⟩ ⟨13, 2, 0, 79730, 22795, 1077, 16384⟩
    (by decide) selected_cut_02476

theorem unmarked_context_12_5698_79731 : frontier 9 ⟨79731, by decide⟩
    (prefixCache 12 5698) (prefixPartial 12 5698) = false := by
  decide +kernel

theorem node_context_12_5698_79731 : EJMOriginalGlobalDAGData.nodes 9 ⟨79731, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨79693, by decide⟩,⟨79716, by decide⟩,⟨79730, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5698_79731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5698 ⟨79731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5698
    ⟨79731, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨79693, by decide⟩,⟨79716, by decide⟩,⟨79730, by decide⟩]) unmarked_context_12_5698_79731 node_context_12_5698_79731
  intro a
  fin_cases a
  · exact context_13_22792_3444
  · exact context_13_22793_79693
  · exact context_13_22794_79716
  · exact context_13_22795_79730

theorem selected_cut_02477 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22796) = some ⟨13, 1, 0, 3444, 22796, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22796_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22796 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22796 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22796, 1, 16384⟩
    (by decide) selected_cut_02477

theorem selected_cut_02478 : selected 8 ⟨79766, by decide⟩
    (prefixPartial 13 22797) = some ⟨13, 2, 0, 79766, 22797, 3065, 16384⟩ := by
  decide +kernel

theorem context_13_22797_79766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22797 ⟨79766, by decide⟩ :=
  accepted_of_selected 13 22797 ⟨79766, by decide⟩ ⟨13, 2, 0, 79766, 22797, 3065, 16384⟩
    (by decide) selected_cut_02478

theorem selected_cut_02479 : selected 8 ⟨79787, by decide⟩
    (prefixPartial 13 22798) = some ⟨13, 2, 0, 79787, 22798, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_22798_79787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22798 ⟨79787, by decide⟩ :=
  accepted_of_selected 13 22798 ⟨79787, by decide⟩ ⟨13, 2, 0, 79787, 22798, 2053, 16384⟩
    (by decide) selected_cut_02479

theorem selected_cut_02480 : selected 8 ⟨79795, by decide⟩
    (prefixPartial 13 22799) = some ⟨13, 2, 0, 79795, 22799, 937, 16384⟩ := by
  decide +kernel

theorem context_13_22799_79795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22799 ⟨79795, by decide⟩ :=
  accepted_of_selected 13 22799 ⟨79795, by decide⟩ ⟨13, 2, 0, 79795, 22799, 937, 16384⟩
    (by decide) selected_cut_02480

theorem unmarked_context_12_5699_79796 : frontier 9 ⟨79796, by decide⟩
    (prefixCache 12 5699) (prefixPartial 12 5699) = false := by
  decide +kernel

theorem node_context_12_5699_79796 : EJMOriginalGlobalDAGData.nodes 9 ⟨79796, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨79766, by decide⟩,⟨79787, by decide⟩,⟨79795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5699_79796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5699 ⟨79796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5699
    ⟨79796, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨79766, by decide⟩,⟨79787, by decide⟩,⟨79795, by decide⟩]) unmarked_context_12_5699_79796 node_context_12_5699_79796
  intro a
  fin_cases a
  · exact context_13_22796_3444
  · exact context_13_22797_79766
  · exact context_13_22798_79787
  · exact context_13_22799_79795

theorem unmarked_context_11_1424_79797 : frontier 10 ⟨79797, by decide⟩
    (prefixCache 11 1424) (prefixPartial 11 1424) = false := by
  decide +kernel

theorem node_context_11_1424_79797 : EJMOriginalGlobalDAGData.nodes 10 ⟨79797, by decide⟩ =
    .split (coordinate 11) (![⟨79600, by decide⟩,⟨79663, by decide⟩,⟨79731, by decide⟩,⟨79796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1424_79797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1424 ⟨79797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1424
    ⟨79797, by decide⟩ (by decide) (![⟨79600, by decide⟩,⟨79663, by decide⟩,⟨79731, by decide⟩,⟨79796, by decide⟩]) unmarked_context_11_1424_79797 node_context_11_1424_79797
  intro a
  fin_cases a
  · exact context_12_5696_79600
  · exact context_12_5697_79663
  · exact context_12_5698_79731
  · exact context_12_5699_79796

theorem selected_cut_02481 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22800) = some ⟨13, 1, 0, 3444, 22800, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22800_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22800 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22800 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22800, 1, 16384⟩
    (by decide) selected_cut_02481

theorem selected_cut_02482 : selected 8 ⟨79823, by decide⟩
    (prefixPartial 13 22801) = some ⟨13, 2, 0, 79823, 22801, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_22801_79823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22801 ⟨79823, by decide⟩ :=
  accepted_of_selected 13 22801 ⟨79823, by decide⟩ ⟨13, 2, 0, 79823, 22801, 2545, 16384⟩
    (by decide) selected_cut_02482

theorem selected_cut_02483 : selected 8 ⟨79845, by decide⟩
    (prefixPartial 13 22802) = some ⟨13, 2, 0, 79845, 22802, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_22802_79845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22802 ⟨79845, by decide⟩ :=
  accepted_of_selected 13 22802 ⟨79845, by decide⟩ ⟨13, 2, 0, 79845, 22802, 1869, 16384⟩
    (by decide) selected_cut_02483

theorem selected_cut_02484 : selected 8 ⟨79855, by decide⟩
    (prefixPartial 13 22803) = some ⟨13, 2, 0, 79855, 22803, 981, 16384⟩ := by
  decide +kernel

theorem context_13_22803_79855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22803 ⟨79855, by decide⟩ :=
  accepted_of_selected 13 22803 ⟨79855, by decide⟩ ⟨13, 2, 0, 79855, 22803, 981, 16384⟩
    (by decide) selected_cut_02484

theorem unmarked_context_12_5700_79856 : frontier 9 ⟨79856, by decide⟩
    (prefixCache 12 5700) (prefixPartial 12 5700) = false := by
  decide +kernel

theorem node_context_12_5700_79856 : EJMOriginalGlobalDAGData.nodes 9 ⟨79856, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨79823, by decide⟩,⟨79845, by decide⟩,⟨79855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5700_79856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5700 ⟨79856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5700
    ⟨79856, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨79823, by decide⟩,⟨79845, by decide⟩,⟨79855, by decide⟩]) unmarked_context_12_5700_79856 node_context_12_5700_79856
  intro a
  fin_cases a
  · exact context_13_22800_3444
  · exact context_13_22801_79823
  · exact context_13_22802_79845
  · exact context_13_22803_79855

theorem selected_cut_02485 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22804) = some ⟨13, 1, 0, 3444, 22804, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22804_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22804 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22804 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22804, 1, 16384⟩
    (by decide) selected_cut_02485

theorem selected_cut_02486 : selected 8 ⟨79880, by decide⟩
    (prefixPartial 13 22805) = some ⟨13, 2, 0, 79880, 22805, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_22805_79880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22805 ⟨79880, by decide⟩ :=
  accepted_of_selected 13 22805 ⟨79880, by decide⟩ ⟨13, 2, 0, 79880, 22805, 2449, 16384⟩
    (by decide) selected_cut_02486

theorem selected_cut_02487 : selected 8 ⟨79902, by decide⟩
    (prefixPartial 13 22806) = some ⟨13, 2, 0, 79902, 22806, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_22806_79902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22806 ⟨79902, by decide⟩ :=
  accepted_of_selected 13 22806 ⟨79902, by decide⟩ ⟨13, 2, 0, 79902, 22806, 1969, 16384⟩
    (by decide) selected_cut_02487

theorem selected_cut_02488 : selected 8 ⟨79911, by decide⟩
    (prefixPartial 13 22807) = some ⟨13, 2, 0, 79911, 22807, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_22807_79911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22807 ⟨79911, by decide⟩ :=
  accepted_of_selected 13 22807 ⟨79911, by decide⟩ ⟨13, 2, 0, 79911, 22807, 1089, 16384⟩
    (by decide) selected_cut_02488

theorem unmarked_context_12_5701_79912 : frontier 9 ⟨79912, by decide⟩
    (prefixCache 12 5701) (prefixPartial 12 5701) = false := by
  decide +kernel

theorem node_context_12_5701_79912 : EJMOriginalGlobalDAGData.nodes 9 ⟨79912, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨79880, by decide⟩,⟨79902, by decide⟩,⟨79911, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5701_79912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5701 ⟨79912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5701
    ⟨79912, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨79880, by decide⟩,⟨79902, by decide⟩,⟨79911, by decide⟩]) unmarked_context_12_5701_79912 node_context_12_5701_79912
  intro a
  fin_cases a
  · exact context_13_22804_3444
  · exact context_13_22805_79880
  · exact context_13_22806_79902
  · exact context_13_22807_79911

theorem selected_cut_02489 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22808) = some ⟨13, 1, 0, 3444, 22808, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22808_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22808 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22808 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22808, 1, 16384⟩
    (by decide) selected_cut_02489

theorem selected_cut_02490 : selected 8 ⟨79938, by decide⟩
    (prefixPartial 13 22809) = some ⟨13, 2, 0, 79938, 22809, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_22809_79938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22809 ⟨79938, by decide⟩ :=
  accepted_of_selected 13 22809 ⟨79938, by decide⟩ ⟨13, 2, 0, 79938, 22809, 2589, 16384⟩
    (by decide) selected_cut_02490

theorem selected_cut_02491 : selected 8 ⟨79956, by decide⟩
    (prefixPartial 13 22810) = some ⟨13, 2, 0, 79956, 22810, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_22810_79956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22810 ⟨79956, by decide⟩ :=
  accepted_of_selected 13 22810 ⟨79956, by decide⟩ ⟨13, 2, 0, 79956, 22810, 1897, 16384⟩
    (by decide) selected_cut_02491

theorem selected_cut_02492 : selected 8 ⟨79970, by decide⟩
    (prefixPartial 13 22811) = some ⟨13, 2, 0, 79970, 22811, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_22811_79970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22811 ⟨79970, by decide⟩ :=
  accepted_of_selected 13 22811 ⟨79970, by decide⟩ ⟨13, 2, 0, 79970, 22811, 1189, 16384⟩
    (by decide) selected_cut_02492

theorem unmarked_context_12_5702_79971 : frontier 9 ⟨79971, by decide⟩
    (prefixCache 12 5702) (prefixPartial 12 5702) = false := by
  decide +kernel

theorem node_context_12_5702_79971 : EJMOriginalGlobalDAGData.nodes 9 ⟨79971, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨79938, by decide⟩,⟨79956, by decide⟩,⟨79970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5702_79971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5702 ⟨79971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5702
    ⟨79971, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨79938, by decide⟩,⟨79956, by decide⟩,⟨79970, by decide⟩]) unmarked_context_12_5702_79971 node_context_12_5702_79971
  intro a
  fin_cases a
  · exact context_13_22808_3444
  · exact context_13_22809_79938
  · exact context_13_22810_79956
  · exact context_13_22811_79970

theorem selected_cut_02493 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22812) = some ⟨13, 1, 0, 3444, 22812, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22812_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22812 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22812 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22812, 1, 16384⟩
    (by decide) selected_cut_02493

theorem selected_cut_02494 : selected 8 ⟨80005, by decide⟩
    (prefixPartial 13 22813) = some ⟨13, 2, 0, 80005, 22813, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_22813_80005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22813 ⟨80005, by decide⟩ :=
  accepted_of_selected 13 22813 ⟨80005, by decide⟩ ⟨13, 2, 0, 80005, 22813, 2729, 16384⟩
    (by decide) selected_cut_02494

theorem selected_cut_02495 : selected 8 ⟨80034, by decide⟩
    (prefixPartial 13 22814) = some ⟨13, 2, 0, 80034, 22814, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_22814_80034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22814 ⟨80034, by decide⟩ :=
  accepted_of_selected 13 22814 ⟨80034, by decide⟩ ⟨13, 2, 0, 80034, 22814, 2313, 16384⟩
    (by decide) selected_cut_02495

theorem selected_cut_02496 : selected 8 ⟨80044, by decide⟩
    (prefixPartial 13 22815) = some ⟨13, 2, 0, 80044, 22815, 989, 16384⟩ := by
  decide +kernel

theorem context_13_22815_80044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22815 ⟨80044, by decide⟩ :=
  accepted_of_selected 13 22815 ⟨80044, by decide⟩ ⟨13, 2, 0, 80044, 22815, 989, 16384⟩
    (by decide) selected_cut_02496

theorem unmarked_context_12_5703_80045 : frontier 9 ⟨80045, by decide⟩
    (prefixCache 12 5703) (prefixPartial 12 5703) = false := by
  decide +kernel

theorem node_context_12_5703_80045 : EJMOriginalGlobalDAGData.nodes 9 ⟨80045, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80005, by decide⟩,⟨80034, by decide⟩,⟨80044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5703_80045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5703 ⟨80045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5703
    ⟨80045, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80005, by decide⟩,⟨80034, by decide⟩,⟨80044, by decide⟩]) unmarked_context_12_5703_80045 node_context_12_5703_80045
  intro a
  fin_cases a
  · exact context_13_22812_3444
  · exact context_13_22813_80005
  · exact context_13_22814_80034
  · exact context_13_22815_80044

theorem unmarked_context_11_1425_80046 : frontier 10 ⟨80046, by decide⟩
    (prefixCache 11 1425) (prefixPartial 11 1425) = false := by
  decide +kernel

theorem node_context_11_1425_80046 : EJMOriginalGlobalDAGData.nodes 10 ⟨80046, by decide⟩ =
    .split (coordinate 11) (![⟨79856, by decide⟩,⟨79912, by decide⟩,⟨79971, by decide⟩,⟨80045, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1425_80046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1425 ⟨80046, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1425
    ⟨80046, by decide⟩ (by decide) (![⟨79856, by decide⟩,⟨79912, by decide⟩,⟨79971, by decide⟩,⟨80045, by decide⟩]) unmarked_context_11_1425_80046 node_context_11_1425_80046
  intro a
  fin_cases a
  · exact context_12_5700_79856
  · exact context_12_5701_79912
  · exact context_12_5702_79971
  · exact context_12_5703_80045

theorem selected_cut_02497 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22816) = some ⟨13, 1, 0, 3444, 22816, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22816_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22816 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22816 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22816, 1, 16384⟩
    (by decide) selected_cut_02497

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
