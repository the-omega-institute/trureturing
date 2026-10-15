/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover340
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_32740 : selected 9 ⟨842963, by decide⟩
    (prefixPartial 12 109678) = some ⟨12, 2, 0, 842963, 109678, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_109678_842963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109678 ⟨842963, by decide⟩ :=
  accepted_of_selected 12 109678 ⟨842963, by decide⟩ ⟨12, 2, 0, 842963, 109678, 2917, 65536⟩
    (by decide) selected_cut_32740

theorem selected_cut_32741 : selected 9 ⟨843009, by decide⟩
    (prefixPartial 12 109679) = some ⟨12, 2, 0, 843009, 109679, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_109679_843009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109679 ⟨843009, by decide⟩ :=
  accepted_of_selected 12 109679 ⟨843009, by decide⟩ ⟨12, 2, 0, 843009, 109679, 2929, 65536⟩
    (by decide) selected_cut_32741

theorem unmarked_context_11_27419_843010 : frontier 10 ⟨843010, by decide⟩
    (prefixCache 11 27419) (prefixPartial 11 27419) = false := by
  decide +kernel

theorem node_context_11_27419_843010 : EJMOriginalGlobalDAGData.nodes 10 ⟨843010, by decide⟩ =
    .split (coordinate 11) (![⟨842881, by decide⟩,⟨842926, by decide⟩,⟨842963, by decide⟩,⟨843009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27419_843010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27419 ⟨843010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27419
    ⟨843010, by decide⟩ (by decide) (![⟨842881, by decide⟩,⟨842926, by decide⟩,⟨842963, by decide⟩,⟨843009, by decide⟩]) unmarked_context_11_27419_843010 node_context_11_27419_843010
  intro a
  fin_cases a
  · exact context_12_109676_842881
  · exact context_12_109677_842926
  · exact context_12_109678_842963
  · exact context_12_109679_843009

theorem unmarked_context_10_6854_843011 : frontier 11 ⟨843011, by decide⟩
    (prefixCache 10 6854) (prefixPartial 10 6854) = false := by
  decide +kernel

theorem node_context_10_6854_843011 : EJMOriginalGlobalDAGData.nodes 11 ⟨843011, by decide⟩ =
    .split (coordinate 10) (![⟨842479, by decide⟩,⟨842689, by decide⟩,⟨842843, by decide⟩,⟨843010, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6854_843011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6854 ⟨843011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6854
    ⟨843011, by decide⟩ (by decide) (![⟨842479, by decide⟩,⟨842689, by decide⟩,⟨842843, by decide⟩,⟨843010, by decide⟩]) unmarked_context_10_6854_843011 node_context_10_6854_843011
  intro a
  fin_cases a
  · exact context_11_27416_842479
  · exact context_11_27417_842689
  · exact context_11_27418_842843
  · exact context_11_27419_843010

theorem selected_cut_32742 : selected 9 ⟨792260, by decide⟩
    (prefixPartial 12 109680) = some ⟨12, 1, 0, 792260, 109680, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109680_792260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109680 ⟨792260, by decide⟩ :=
  accepted_of_selected 12 109680 ⟨792260, by decide⟩ ⟨12, 1, 0, 792260, 109680, 1, 65536⟩
    (by decide) selected_cut_32742

theorem selected_cut_32743 : selected 9 ⟨843046, by decide⟩
    (prefixPartial 12 109681) = some ⟨12, 2, 0, 843046, 109681, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_109681_843046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109681 ⟨843046, by decide⟩ :=
  accepted_of_selected 12 109681 ⟨843046, by decide⟩ ⟨12, 2, 0, 843046, 109681, 2605, 65536⟩
    (by decide) selected_cut_32743

theorem selected_cut_32744 : selected 9 ⟨843079, by decide⟩
    (prefixPartial 12 109682) = some ⟨12, 2, 0, 843079, 109682, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_109682_843079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109682 ⟨843079, by decide⟩ :=
  accepted_of_selected 12 109682 ⟨843079, by decide⟩ ⟨12, 2, 0, 843079, 109682, 2245, 65536⟩
    (by decide) selected_cut_32744

theorem selected_cut_32745 : selected 9 ⟨843119, by decide⟩
    (prefixPartial 12 109683) = some ⟨12, 2, 0, 843119, 109683, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_109683_843119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109683 ⟨843119, by decide⟩ :=
  accepted_of_selected 12 109683 ⟨843119, by decide⟩ ⟨12, 2, 0, 843119, 109683, 2589, 65536⟩
    (by decide) selected_cut_32745

theorem unmarked_context_11_27420_843120 : frontier 10 ⟨843120, by decide⟩
    (prefixCache 11 27420) (prefixPartial 11 27420) = false := by
  decide +kernel

theorem node_context_11_27420_843120 : EJMOriginalGlobalDAGData.nodes 10 ⟨843120, by decide⟩ =
    .split (coordinate 11) (![⟨792260, by decide⟩,⟨843046, by decide⟩,⟨843079, by decide⟩,⟨843119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27420_843120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27420 ⟨843120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27420
    ⟨843120, by decide⟩ (by decide) (![⟨792260, by decide⟩,⟨843046, by decide⟩,⟨843079, by decide⟩,⟨843119, by decide⟩]) unmarked_context_11_27420_843120 node_context_11_27420_843120
  intro a
  fin_cases a
  · exact context_12_109680_792260
  · exact context_12_109681_843046
  · exact context_12_109682_843079
  · exact context_12_109683_843119

theorem selected_cut_32746 : selected 9 ⟨843157, by decide⟩
    (prefixPartial 12 109684) = some ⟨12, 2, 0, 843157, 109684, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_109684_843157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109684 ⟨843157, by decide⟩ :=
  accepted_of_selected 12 109684 ⟨843157, by decide⟩ ⟨12, 2, 0, 843157, 109684, 2677, 65536⟩
    (by decide) selected_cut_32746

theorem selected_cut_32747 : selected 9 ⟨843197, by decide⟩
    (prefixPartial 12 109685) = some ⟨12, 2, 0, 843197, 109685, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_109685_843197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109685 ⟨843197, by decide⟩ :=
  accepted_of_selected 12 109685 ⟨843197, by decide⟩ ⟨12, 2, 0, 843197, 109685, 2657, 65536⟩
    (by decide) selected_cut_32747

theorem selected_cut_32748 : selected 9 ⟨843235, by decide⟩
    (prefixPartial 12 109686) = some ⟨12, 2, 0, 843235, 109686, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_109686_843235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109686 ⟨843235, by decide⟩ :=
  accepted_of_selected 12 109686 ⟨843235, by decide⟩ ⟨12, 2, 0, 843235, 109686, 2397, 65536⟩
    (by decide) selected_cut_32748

theorem selected_cut_32749 : selected 9 ⟨843284, by decide⟩
    (prefixPartial 12 109687) = some ⟨12, 2, 0, 843284, 109687, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_109687_843284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109687 ⟨843284, by decide⟩ :=
  accepted_of_selected 12 109687 ⟨843284, by decide⟩ ⟨12, 2, 0, 843284, 109687, 2801, 65536⟩
    (by decide) selected_cut_32749

theorem unmarked_context_11_27421_843285 : frontier 10 ⟨843285, by decide⟩
    (prefixCache 11 27421) (prefixPartial 11 27421) = false := by
  decide +kernel

theorem node_context_11_27421_843285 : EJMOriginalGlobalDAGData.nodes 10 ⟨843285, by decide⟩ =
    .split (coordinate 11) (![⟨843157, by decide⟩,⟨843197, by decide⟩,⟨843235, by decide⟩,⟨843284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27421_843285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27421 ⟨843285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27421
    ⟨843285, by decide⟩ (by decide) (![⟨843157, by decide⟩,⟨843197, by decide⟩,⟨843235, by decide⟩,⟨843284, by decide⟩]) unmarked_context_11_27421_843285 node_context_11_27421_843285
  intro a
  fin_cases a
  · exact context_12_109684_843157
  · exact context_12_109685_843197
  · exact context_12_109686_843235
  · exact context_12_109687_843284

theorem selected_cut_32750 : selected 9 ⟨843316, by decide⟩
    (prefixPartial 12 109688) = some ⟨12, 2, 0, 843316, 109688, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_109688_843316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109688 ⟨843316, by decide⟩ :=
  accepted_of_selected 12 109688 ⟨843316, by decide⟩ ⟨12, 2, 0, 843316, 109688, 2261, 65536⟩
    (by decide) selected_cut_32750

theorem selected_cut_32751 : selected 9 ⟨843344, by decide⟩
    (prefixPartial 12 109689) = some ⟨12, 2, 0, 843344, 109689, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_109689_843344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109689 ⟨843344, by decide⟩ :=
  accepted_of_selected 12 109689 ⟨843344, by decide⟩ ⟨12, 2, 0, 843344, 109689, 2361, 65536⟩
    (by decide) selected_cut_32751

theorem selected_cut_32752 : selected 9 ⟨843377, by decide⟩
    (prefixPartial 12 109690) = some ⟨12, 2, 0, 843377, 109690, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_109690_843377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109690 ⟨843377, by decide⟩ :=
  accepted_of_selected 12 109690 ⟨843377, by decide⟩ ⟨12, 2, 0, 843377, 109690, 1865, 65536⟩
    (by decide) selected_cut_32752

theorem selected_cut_32753 : selected 9 ⟨843404, by decide⟩
    (prefixPartial 12 109691) = some ⟨12, 2, 0, 843404, 109691, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_109691_843404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109691 ⟨843404, by decide⟩ :=
  accepted_of_selected 12 109691 ⟨843404, by decide⟩ ⟨12, 2, 0, 843404, 109691, 2205, 65536⟩
    (by decide) selected_cut_32753

theorem unmarked_context_11_27422_843405 : frontier 10 ⟨843405, by decide⟩
    (prefixCache 11 27422) (prefixPartial 11 27422) = false := by
  decide +kernel

theorem node_context_11_27422_843405 : EJMOriginalGlobalDAGData.nodes 10 ⟨843405, by decide⟩ =
    .split (coordinate 11) (![⟨843316, by decide⟩,⟨843344, by decide⟩,⟨843377, by decide⟩,⟨843404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27422_843405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27422 ⟨843405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27422
    ⟨843405, by decide⟩ (by decide) (![⟨843316, by decide⟩,⟨843344, by decide⟩,⟨843377, by decide⟩,⟨843404, by decide⟩]) unmarked_context_11_27422_843405 node_context_11_27422_843405
  intro a
  fin_cases a
  · exact context_12_109688_843316
  · exact context_12_109689_843344
  · exact context_12_109690_843377
  · exact context_12_109691_843404

theorem selected_cut_32754 : selected 10 ⟨843450, by decide⟩
    (prefixPartial 11 27423) = some ⟨11, 2, 0, 843450, 27423, 2713, 262144⟩ := by
  decide +kernel

theorem context_11_27423_843450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27423 ⟨843450, by decide⟩ :=
  accepted_of_selected 11 27423 ⟨843450, by decide⟩ ⟨11, 2, 0, 843450, 27423, 2713, 262144⟩
    (by decide) selected_cut_32754

theorem unmarked_context_10_6855_843451 : frontier 11 ⟨843451, by decide⟩
    (prefixCache 10 6855) (prefixPartial 10 6855) = false := by
  decide +kernel

theorem node_context_10_6855_843451 : EJMOriginalGlobalDAGData.nodes 11 ⟨843451, by decide⟩ =
    .split (coordinate 10) (![⟨843120, by decide⟩,⟨843285, by decide⟩,⟨843405, by decide⟩,⟨843450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6855_843451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6855 ⟨843451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6855
    ⟨843451, by decide⟩ (by decide) (![⟨843120, by decide⟩,⟨843285, by decide⟩,⟨843405, by decide⟩,⟨843450, by decide⟩]) unmarked_context_10_6855_843451 node_context_10_6855_843451
  intro a
  fin_cases a
  · exact context_11_27420_843120
  · exact context_11_27421_843285
  · exact context_11_27422_843405
  · exact context_11_27423_843450

theorem unmarked_context_9_1713_843452 : frontier 12 ⟨843452, by decide⟩
    (prefixCache 9 1713) (prefixPartial 9 1713) = false := by
  decide +kernel

theorem node_context_9_1713_843452 : EJMOriginalGlobalDAGData.nodes 12 ⟨843452, by decide⟩ =
    .split (coordinate 9) (![⟨841455, by decide⟩,⟨842197, by decide⟩,⟨843011, by decide⟩,⟨843451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1713_843452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1713 ⟨843452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1713
    ⟨843452, by decide⟩ (by decide) (![⟨841455, by decide⟩,⟨842197, by decide⟩,⟨843011, by decide⟩,⟨843451, by decide⟩]) unmarked_context_9_1713_843452 node_context_9_1713_843452
  intro a
  fin_cases a
  · exact context_10_6852_841455
  · exact context_10_6853_842197
  · exact context_10_6854_843011
  · exact context_10_6855_843451

theorem selected_cut_32755 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 109696) = some ⟨12, 1, 0, 450982, 109696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109696_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109696 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 109696 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 109696, 1, 65536⟩
    (by decide) selected_cut_32755

theorem selected_cut_32756 : selected 9 ⟨843490, by decide⟩
    (prefixPartial 12 109697) = some ⟨12, 2, 0, 843490, 109697, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_109697_843490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109697 ⟨843490, by decide⟩ :=
  accepted_of_selected 12 109697 ⟨843490, by decide⟩ ⟨12, 2, 0, 843490, 109697, 2273, 65536⟩
    (by decide) selected_cut_32756

theorem selected_cut_32757 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 109698) = some ⟨12, 1, 0, 813440, 109698, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109698_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109698 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 109698 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 109698, 1, 65536⟩
    (by decide) selected_cut_32757

theorem selected_cut_32758 : selected 9 ⟨843518, by decide⟩
    (prefixPartial 12 109699) = some ⟨12, 2, 0, 843518, 109699, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_109699_843518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109699 ⟨843518, by decide⟩ :=
  accepted_of_selected 12 109699 ⟨843518, by decide⟩ ⟨12, 2, 0, 843518, 109699, 2149, 65536⟩
    (by decide) selected_cut_32758

theorem unmarked_context_11_27424_843519 : frontier 10 ⟨843519, by decide⟩
    (prefixCache 11 27424) (prefixPartial 11 27424) = false := by
  decide +kernel

theorem node_context_11_27424_843519 : EJMOriginalGlobalDAGData.nodes 10 ⟨843519, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨843490, by decide⟩,⟨813440, by decide⟩,⟨843518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27424_843519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27424 ⟨843519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27424
    ⟨843519, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨843490, by decide⟩,⟨813440, by decide⟩,⟨843518, by decide⟩]) unmarked_context_11_27424_843519 node_context_11_27424_843519
  intro a
  fin_cases a
  · exact context_12_109696_450982
  · exact context_12_109697_843490
  · exact context_12_109698_813440
  · exact context_12_109699_843518

theorem selected_cut_32759 : selected 9 ⟨843550, by decide⟩
    (prefixPartial 12 109700) = some ⟨12, 2, 0, 843550, 109700, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_109700_843550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109700 ⟨843550, by decide⟩ :=
  accepted_of_selected 12 109700 ⟨843550, by decide⟩ ⟨12, 2, 0, 843550, 109700, 2149, 65536⟩
    (by decide) selected_cut_32759

theorem selected_cut_32760 : selected 9 ⟨843591, by decide⟩
    (prefixPartial 12 109701) = some ⟨12, 2, 0, 843591, 109701, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_109701_843591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109701 ⟨843591, by decide⟩ :=
  accepted_of_selected 12 109701 ⟨843591, by decide⟩ ⟨12, 2, 0, 843591, 109701, 2433, 65536⟩
    (by decide) selected_cut_32760

theorem selected_cut_32761 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 109702) = some ⟨12, 1, 0, 813440, 109702, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109702_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109702 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 109702 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 109702, 1, 65536⟩
    (by decide) selected_cut_32761

theorem selected_cut_32762 : selected 9 ⟨843634, by decide⟩
    (prefixPartial 12 109703) = some ⟨12, 2, 0, 843634, 109703, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_109703_843634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109703 ⟨843634, by decide⟩ :=
  accepted_of_selected 12 109703 ⟨843634, by decide⟩ ⟨12, 2, 0, 843634, 109703, 2533, 65536⟩
    (by decide) selected_cut_32762

theorem unmarked_context_11_27425_843635 : frontier 10 ⟨843635, by decide⟩
    (prefixCache 11 27425) (prefixPartial 11 27425) = false := by
  decide +kernel

theorem node_context_11_27425_843635 : EJMOriginalGlobalDAGData.nodes 10 ⟨843635, by decide⟩ =
    .split (coordinate 11) (![⟨843550, by decide⟩,⟨843591, by decide⟩,⟨813440, by decide⟩,⟨843634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27425_843635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27425 ⟨843635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27425
    ⟨843635, by decide⟩ (by decide) (![⟨843550, by decide⟩,⟨843591, by decide⟩,⟨813440, by decide⟩,⟨843634, by decide⟩]) unmarked_context_11_27425_843635 node_context_11_27425_843635
  intro a
  fin_cases a
  · exact context_12_109700_843550
  · exact context_12_109701_843591
  · exact context_12_109702_813440
  · exact context_12_109703_843634

theorem selected_cut_32763 : selected 9 ⟨843672, by decide⟩
    (prefixPartial 12 109704) = some ⟨12, 2, 0, 843672, 109704, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_109704_843672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109704 ⟨843672, by decide⟩ :=
  accepted_of_selected 12 109704 ⟨843672, by decide⟩ ⟨12, 2, 0, 843672, 109704, 2013, 65536⟩
    (by decide) selected_cut_32763

theorem selected_cut_32764 : selected 9 ⟨843723, by decide⟩
    (prefixPartial 12 109705) = some ⟨12, 2, 0, 843723, 109705, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_109705_843723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109705 ⟨843723, by decide⟩ :=
  accepted_of_selected 12 109705 ⟨843723, by decide⟩ ⟨12, 2, 0, 843723, 109705, 2337, 65536⟩
    (by decide) selected_cut_32764

theorem selected_cut_32765 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 109706) = some ⟨12, 1, 0, 813440, 109706, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109706_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109706 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 109706 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 109706, 1, 65536⟩
    (by decide) selected_cut_32765

theorem selected_cut_32766 : selected 9 ⟨843765, by decide⟩
    (prefixPartial 12 109707) = some ⟨12, 2, 0, 843765, 109707, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_109707_843765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109707 ⟨843765, by decide⟩ :=
  accepted_of_selected 12 109707 ⟨843765, by decide⟩ ⟨12, 2, 0, 843765, 109707, 2173, 65536⟩
    (by decide) selected_cut_32766

theorem unmarked_context_11_27426_843766 : frontier 10 ⟨843766, by decide⟩
    (prefixCache 11 27426) (prefixPartial 11 27426) = false := by
  decide +kernel

theorem node_context_11_27426_843766 : EJMOriginalGlobalDAGData.nodes 10 ⟨843766, by decide⟩ =
    .split (coordinate 11) (![⟨843672, by decide⟩,⟨843723, by decide⟩,⟨813440, by decide⟩,⟨843765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27426_843766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27426 ⟨843766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27426
    ⟨843766, by decide⟩ (by decide) (![⟨843672, by decide⟩,⟨843723, by decide⟩,⟨813440, by decide⟩,⟨843765, by decide⟩]) unmarked_context_11_27426_843766 node_context_11_27426_843766
  intro a
  fin_cases a
  · exact context_12_109704_843672
  · exact context_12_109705_843723
  · exact context_12_109706_813440
  · exact context_12_109707_843765

theorem selected_cut_32767 : selected 9 ⟨843797, by decide⟩
    (prefixPartial 12 109708) = some ⟨12, 2, 0, 843797, 109708, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_109708_843797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109708 ⟨843797, by decide⟩ :=
  accepted_of_selected 12 109708 ⟨843797, by decide⟩ ⟨12, 2, 0, 843797, 109708, 1821, 65536⟩
    (by decide) selected_cut_32767

theorem selected_cut_32768 : selected 9 ⟨843839, by decide⟩
    (prefixPartial 12 109709) = some ⟨12, 2, 0, 843839, 109709, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_109709_843839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109709 ⟨843839, by decide⟩ :=
  accepted_of_selected 12 109709 ⟨843839, by decide⟩ ⟨12, 2, 0, 843839, 109709, 2181, 65536⟩
    (by decide) selected_cut_32768

theorem selected_cut_32769 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 109710) = some ⟨12, 1, 0, 813440, 109710, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109710_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109710 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 109710 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 109710, 1, 65536⟩
    (by decide) selected_cut_32769

theorem selected_cut_32770 : selected 9 ⟨843862, by decide⟩
    (prefixPartial 12 109711) = some ⟨12, 2, 0, 843862, 109711, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_109711_843862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109711 ⟨843862, by decide⟩ :=
  accepted_of_selected 12 109711 ⟨843862, by decide⟩ ⟨12, 2, 0, 843862, 109711, 2033, 65536⟩
    (by decide) selected_cut_32770

theorem unmarked_context_11_27427_843863 : frontier 10 ⟨843863, by decide⟩
    (prefixCache 11 27427) (prefixPartial 11 27427) = false := by
  decide +kernel

theorem node_context_11_27427_843863 : EJMOriginalGlobalDAGData.nodes 10 ⟨843863, by decide⟩ =
    .split (coordinate 11) (![⟨843797, by decide⟩,⟨843839, by decide⟩,⟨813440, by decide⟩,⟨843862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27427_843863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27427 ⟨843863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27427
    ⟨843863, by decide⟩ (by decide) (![⟨843797, by decide⟩,⟨843839, by decide⟩,⟨813440, by decide⟩,⟨843862, by decide⟩]) unmarked_context_11_27427_843863 node_context_11_27427_843863
  intro a
  fin_cases a
  · exact context_12_109708_843797
  · exact context_12_109709_843839
  · exact context_12_109710_813440
  · exact context_12_109711_843862

theorem unmarked_context_10_6856_843864 : frontier 11 ⟨843864, by decide⟩
    (prefixCache 10 6856) (prefixPartial 10 6856) = false := by
  decide +kernel

theorem node_context_10_6856_843864 : EJMOriginalGlobalDAGData.nodes 11 ⟨843864, by decide⟩ =
    .split (coordinate 10) (![⟨843519, by decide⟩,⟨843635, by decide⟩,⟨843766, by decide⟩,⟨843863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6856_843864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6856 ⟨843864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6856
    ⟨843864, by decide⟩ (by decide) (![⟨843519, by decide⟩,⟨843635, by decide⟩,⟨843766, by decide⟩,⟨843863, by decide⟩]) unmarked_context_10_6856_843864 node_context_10_6856_843864
  intro a
  fin_cases a
  · exact context_11_27424_843519
  · exact context_11_27425_843635
  · exact context_11_27426_843766
  · exact context_11_27427_843863

theorem selected_cut_32771 : selected 9 ⟨769994, by decide⟩
    (prefixPartial 12 109712) = some ⟨12, 1, 0, 769994, 109712, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109712_769994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109712 ⟨769994, by decide⟩ :=
  accepted_of_selected 12 109712 ⟨769994, by decide⟩ ⟨12, 1, 0, 769994, 109712, 1, 65536⟩
    (by decide) selected_cut_32771

theorem selected_cut_32772 : selected 9 ⟨843909, by decide⟩
    (prefixPartial 12 109713) = some ⟨12, 2, 0, 843909, 109713, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_109713_843909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109713 ⟨843909, by decide⟩ :=
  accepted_of_selected 12 109713 ⟨843909, by decide⟩ ⟨12, 2, 0, 843909, 109713, 2581, 65536⟩
    (by decide) selected_cut_32772

theorem selected_cut_32773 : selected 9 ⟨813889, by decide⟩
    (prefixPartial 12 109714) = some ⟨12, 1, 0, 813889, 109714, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109714_813889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109714 ⟨813889, by decide⟩ :=
  accepted_of_selected 12 109714 ⟨813889, by decide⟩ ⟨12, 1, 0, 813889, 109714, 1, 65536⟩
    (by decide) selected_cut_32773

theorem selected_cut_32774 : selected 9 ⟨843947, by decide⟩
    (prefixPartial 12 109715) = some ⟨12, 2, 0, 843947, 109715, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_109715_843947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109715 ⟨843947, by decide⟩ :=
  accepted_of_selected 12 109715 ⟨843947, by decide⟩ ⟨12, 2, 0, 843947, 109715, 2321, 65536⟩
    (by decide) selected_cut_32774

theorem unmarked_context_11_27428_843948 : frontier 10 ⟨843948, by decide⟩
    (prefixCache 11 27428) (prefixPartial 11 27428) = false := by
  decide +kernel

theorem node_context_11_27428_843948 : EJMOriginalGlobalDAGData.nodes 10 ⟨843948, by decide⟩ =
    .split (coordinate 11) (![⟨769994, by decide⟩,⟨843909, by decide⟩,⟨813889, by decide⟩,⟨843947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27428_843948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27428 ⟨843948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27428
    ⟨843948, by decide⟩ (by decide) (![⟨769994, by decide⟩,⟨843909, by decide⟩,⟨813889, by decide⟩,⟨843947, by decide⟩]) unmarked_context_11_27428_843948 node_context_11_27428_843948
  intro a
  fin_cases a
  · exact context_12_109712_769994
  · exact context_12_109713_843909
  · exact context_12_109714_813889
  · exact context_12_109715_843947

theorem selected_cut_32775 : selected 9 ⟨843980, by decide⟩
    (prefixPartial 12 109716) = some ⟨12, 2, 0, 843980, 109716, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_109716_843980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109716 ⟨843980, by decide⟩ :=
  accepted_of_selected 12 109716 ⟨843980, by decide⟩ ⟨12, 2, 0, 843980, 109716, 2213, 65536⟩
    (by decide) selected_cut_32775

theorem selected_cut_32776 : selected 9 ⟨844009, by decide⟩
    (prefixPartial 12 109717) = some ⟨12, 2, 0, 844009, 109717, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_109717_844009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109717 ⟨844009, by decide⟩ :=
  accepted_of_selected 12 109717 ⟨844009, by decide⟩ ⟨12, 2, 0, 844009, 109717, 2437, 65536⟩
    (by decide) selected_cut_32776

theorem selected_cut_32777 : selected 9 ⟨813979, by decide⟩
    (prefixPartial 12 109718) = some ⟨12, 1, 0, 813979, 109718, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109718_813979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109718 ⟨813979, by decide⟩ :=
  accepted_of_selected 12 109718 ⟨813979, by decide⟩ ⟨12, 1, 0, 813979, 109718, 1, 65536⟩
    (by decide) selected_cut_32777

theorem selected_cut_32778 : selected 9 ⟨844056, by decide⟩
    (prefixPartial 12 109719) = some ⟨12, 2, 0, 844056, 109719, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_109719_844056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109719 ⟨844056, by decide⟩ :=
  accepted_of_selected 12 109719 ⟨844056, by decide⟩ ⟨12, 2, 0, 844056, 109719, 2445, 65536⟩
    (by decide) selected_cut_32778

theorem unmarked_context_11_27429_844057 : frontier 10 ⟨844057, by decide⟩
    (prefixCache 11 27429) (prefixPartial 11 27429) = false := by
  decide +kernel

theorem node_context_11_27429_844057 : EJMOriginalGlobalDAGData.nodes 10 ⟨844057, by decide⟩ =
    .split (coordinate 11) (![⟨843980, by decide⟩,⟨844009, by decide⟩,⟨813979, by decide⟩,⟨844056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27429_844057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27429 ⟨844057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27429
    ⟨844057, by decide⟩ (by decide) (![⟨843980, by decide⟩,⟨844009, by decide⟩,⟨813979, by decide⟩,⟨844056, by decide⟩]) unmarked_context_11_27429_844057 node_context_11_27429_844057
  intro a
  fin_cases a
  · exact context_12_109716_843980
  · exact context_12_109717_844009
  · exact context_12_109718_813979
  · exact context_12_109719_844056

theorem selected_cut_32779 : selected 9 ⟨844082, by decide⟩
    (prefixPartial 12 109720) = some ⟨12, 2, 0, 844082, 109720, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_109720_844082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109720 ⟨844082, by decide⟩ :=
  accepted_of_selected 12 109720 ⟨844082, by decide⟩ ⟨12, 2, 0, 844082, 109720, 1801, 65536⟩
    (by decide) selected_cut_32779

theorem selected_cut_32780 : selected 9 ⟨844135, by decide⟩
    (prefixPartial 12 109721) = some ⟨12, 2, 0, 844135, 109721, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_109721_844135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109721 ⟨844135, by decide⟩ :=
  accepted_of_selected 12 109721 ⟨844135, by decide⟩ ⟨12, 2, 0, 844135, 109721, 2305, 65536⟩
    (by decide) selected_cut_32780

theorem selected_cut_32781 : selected 9 ⟨813979, by decide⟩
    (prefixPartial 12 109722) = some ⟨12, 1, 0, 813979, 109722, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109722_813979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109722 ⟨813979, by decide⟩ :=
  accepted_of_selected 12 109722 ⟨813979, by decide⟩ ⟨12, 1, 0, 813979, 109722, 1, 65536⟩
    (by decide) selected_cut_32781

theorem selected_cut_32782 : selected 9 ⟨844175, by decide⟩
    (prefixPartial 12 109723) = some ⟨12, 2, 0, 844175, 109723, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_109723_844175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109723 ⟨844175, by decide⟩ :=
  accepted_of_selected 12 109723 ⟨844175, by decide⟩ ⟨12, 2, 0, 844175, 109723, 2001, 65536⟩
    (by decide) selected_cut_32782

theorem unmarked_context_11_27430_844176 : frontier 10 ⟨844176, by decide⟩
    (prefixCache 11 27430) (prefixPartial 11 27430) = false := by
  decide +kernel

theorem node_context_11_27430_844176 : EJMOriginalGlobalDAGData.nodes 10 ⟨844176, by decide⟩ =
    .split (coordinate 11) (![⟨844082, by decide⟩,⟨844135, by decide⟩,⟨813979, by decide⟩,⟨844175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27430_844176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27430 ⟨844176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27430
    ⟨844176, by decide⟩ (by decide) (![⟨844082, by decide⟩,⟨844135, by decide⟩,⟨813979, by decide⟩,⟨844175, by decide⟩]) unmarked_context_11_27430_844176 node_context_11_27430_844176
  intro a
  fin_cases a
  · exact context_12_109720_844082
  · exact context_12_109721_844135
  · exact context_12_109722_813979
  · exact context_12_109723_844175

theorem selected_cut_32783 : selected 9 ⟨844201, by decide⟩
    (prefixPartial 12 109724) = some ⟨12, 2, 0, 844201, 109724, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_109724_844201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109724 ⟨844201, by decide⟩ :=
  accepted_of_selected 12 109724 ⟨844201, by decide⟩ ⟨12, 2, 0, 844201, 109724, 1853, 65536⟩
    (by decide) selected_cut_32783

theorem selected_cut_32784 : selected 9 ⟨844235, by decide⟩
    (prefixPartial 12 109725) = some ⟨12, 2, 0, 844235, 109725, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_109725_844235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109725 ⟨844235, by decide⟩ :=
  accepted_of_selected 12 109725 ⟨844235, by decide⟩ ⟨12, 2, 0, 844235, 109725, 2141, 65536⟩
    (by decide) selected_cut_32784

theorem selected_cut_32785 : selected 9 ⟨844270, by decide⟩
    (prefixPartial 12 109726) = some ⟨12, 2, 0, 844270, 109726, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_109726_844270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109726 ⟨844270, by decide⟩ :=
  accepted_of_selected 12 109726 ⟨844270, by decide⟩ ⟨12, 2, 0, 844270, 109726, 2113, 65536⟩
    (by decide) selected_cut_32785

theorem selected_cut_32786 : selected 9 ⟨844290, by decide⟩
    (prefixPartial 12 109727) = some ⟨12, 2, 0, 844290, 109727, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_109727_844290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109727 ⟨844290, by decide⟩ :=
  accepted_of_selected 12 109727 ⟨844290, by decide⟩ ⟨12, 2, 0, 844290, 109727, 1833, 65536⟩
    (by decide) selected_cut_32786

theorem unmarked_context_11_27431_844291 : frontier 10 ⟨844291, by decide⟩
    (prefixCache 11 27431) (prefixPartial 11 27431) = false := by
  decide +kernel

theorem node_context_11_27431_844291 : EJMOriginalGlobalDAGData.nodes 10 ⟨844291, by decide⟩ =
    .split (coordinate 11) (![⟨844201, by decide⟩,⟨844235, by decide⟩,⟨844270, by decide⟩,⟨844290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27431_844291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27431 ⟨844291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27431
    ⟨844291, by decide⟩ (by decide) (![⟨844201, by decide⟩,⟨844235, by decide⟩,⟨844270, by decide⟩,⟨844290, by decide⟩]) unmarked_context_11_27431_844291 node_context_11_27431_844291
  intro a
  fin_cases a
  · exact context_12_109724_844201
  · exact context_12_109725_844235
  · exact context_12_109726_844270
  · exact context_12_109727_844290

theorem unmarked_context_10_6857_844292 : frontier 11 ⟨844292, by decide⟩
    (prefixCache 10 6857) (prefixPartial 10 6857) = false := by
  decide +kernel

theorem node_context_10_6857_844292 : EJMOriginalGlobalDAGData.nodes 11 ⟨844292, by decide⟩ =
    .split (coordinate 10) (![⟨843948, by decide⟩,⟨844057, by decide⟩,⟨844176, by decide⟩,⟨844291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6857_844292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6857 ⟨844292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6857
    ⟨844292, by decide⟩ (by decide) (![⟨843948, by decide⟩,⟨844057, by decide⟩,⟨844176, by decide⟩,⟨844291, by decide⟩]) unmarked_context_10_6857_844292 node_context_10_6857_844292
  intro a
  fin_cases a
  · exact context_11_27428_843948
  · exact context_11_27429_844057
  · exact context_11_27430_844176
  · exact context_11_27431_844291

theorem selected_cut_32787 : selected 10 ⟨844336, by decide⟩
    (prefixPartial 11 27432) = some ⟨11, 2, 0, 844336, 27432, 3181, 262144⟩ := by
  decide +kernel

theorem context_11_27432_844336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27432 ⟨844336, by decide⟩ :=
  accepted_of_selected 11 27432 ⟨844336, by decide⟩ ⟨11, 2, 0, 844336, 27432, 3181, 262144⟩
    (by decide) selected_cut_32787

theorem selected_cut_32788 : selected 9 ⟨844356, by decide⟩
    (prefixPartial 12 109732) = some ⟨12, 2, 0, 844356, 109732, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_109732_844356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109732 ⟨844356, by decide⟩ :=
  accepted_of_selected 12 109732 ⟨844356, by decide⟩ ⟨12, 2, 0, 844356, 109732, 1613, 65536⟩
    (by decide) selected_cut_32788

theorem selected_cut_32789 : selected 9 ⟨844370, by decide⟩
    (prefixPartial 12 109733) = some ⟨12, 2, 0, 844370, 109733, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_109733_844370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109733 ⟨844370, by decide⟩ :=
  accepted_of_selected 12 109733 ⟨844370, by decide⟩ ⟨12, 2, 0, 844370, 109733, 1713, 65536⟩
    (by decide) selected_cut_32789

theorem selected_cut_32790 : selected 9 ⟨769937, by decide⟩
    (prefixPartial 12 109734) = some ⟨12, 1, 0, 769937, 109734, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109734_769937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109734 ⟨769937, by decide⟩ :=
  accepted_of_selected 12 109734 ⟨769937, by decide⟩ ⟨12, 1, 0, 769937, 109734, 1, 65536⟩
    (by decide) selected_cut_32790

theorem selected_cut_32791 : selected 9 ⟨844392, by decide⟩
    (prefixPartial 12 109735) = some ⟨12, 2, 0, 844392, 109735, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_109735_844392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109735 ⟨844392, by decide⟩ :=
  accepted_of_selected 12 109735 ⟨844392, by decide⟩ ⟨12, 2, 0, 844392, 109735, 1709, 65536⟩
    (by decide) selected_cut_32791

theorem unmarked_context_11_27433_844393 : frontier 10 ⟨844393, by decide⟩
    (prefixCache 11 27433) (prefixPartial 11 27433) = false := by
  decide +kernel

theorem node_context_11_27433_844393 : EJMOriginalGlobalDAGData.nodes 10 ⟨844393, by decide⟩ =
    .split (coordinate 11) (![⟨844356, by decide⟩,⟨844370, by decide⟩,⟨769937, by decide⟩,⟨844392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27433_844393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27433 ⟨844393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27433
    ⟨844393, by decide⟩ (by decide) (![⟨844356, by decide⟩,⟨844370, by decide⟩,⟨769937, by decide⟩,⟨844392, by decide⟩]) unmarked_context_11_27433_844393 node_context_11_27433_844393
  intro a
  fin_cases a
  · exact context_12_109732_844356
  · exact context_12_109733_844370
  · exact context_12_109734_769937
  · exact context_12_109735_844392

theorem selected_cut_32792 : selected 9 ⟨844409, by decide⟩
    (prefixPartial 12 109736) = some ⟨12, 2, 0, 844409, 109736, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_109736_844409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109736 ⟨844409, by decide⟩ :=
  accepted_of_selected 12 109736 ⟨844409, by decide⟩ ⟨12, 2, 0, 844409, 109736, 1293, 65536⟩
    (by decide) selected_cut_32792

theorem selected_cut_32793 : selected 9 ⟨844426, by decide⟩
    (prefixPartial 12 109737) = some ⟨12, 2, 0, 844426, 109737, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_109737_844426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109737 ⟨844426, by decide⟩ :=
  accepted_of_selected 12 109737 ⟨844426, by decide⟩ ⟨12, 2, 0, 844426, 109737, 1513, 65536⟩
    (by decide) selected_cut_32793

theorem selected_cut_32794 : selected 9 ⟨769937, by decide⟩
    (prefixPartial 12 109738) = some ⟨12, 1, 0, 769937, 109738, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109738_769937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109738 ⟨769937, by decide⟩ :=
  accepted_of_selected 12 109738 ⟨769937, by decide⟩ ⟨12, 1, 0, 769937, 109738, 1, 65536⟩
    (by decide) selected_cut_32794

theorem selected_cut_32795 : selected 9 ⟨844448, by decide⟩
    (prefixPartial 12 109739) = some ⟨12, 2, 0, 844448, 109739, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_109739_844448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109739 ⟨844448, by decide⟩ :=
  accepted_of_selected 12 109739 ⟨844448, by decide⟩ ⟨12, 2, 0, 844448, 109739, 1361, 65536⟩
    (by decide) selected_cut_32795

theorem unmarked_context_11_27434_844449 : frontier 10 ⟨844449, by decide⟩
    (prefixCache 11 27434) (prefixPartial 11 27434) = false := by
  decide +kernel

theorem node_context_11_27434_844449 : EJMOriginalGlobalDAGData.nodes 10 ⟨844449, by decide⟩ =
    .split (coordinate 11) (![⟨844409, by decide⟩,⟨844426, by decide⟩,⟨769937, by decide⟩,⟨844448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27434_844449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27434 ⟨844449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27434
    ⟨844449, by decide⟩ (by decide) (![⟨844409, by decide⟩,⟨844426, by decide⟩,⟨769937, by decide⟩,⟨844448, by decide⟩]) unmarked_context_11_27434_844449 node_context_11_27434_844449
  intro a
  fin_cases a
  · exact context_12_109736_844409
  · exact context_12_109737_844426
  · exact context_12_109738_769937
  · exact context_12_109739_844448

theorem selected_cut_32796 : selected 9 ⟨844466, by decide⟩
    (prefixPartial 12 109740) = some ⟨12, 2, 0, 844466, 109740, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_109740_844466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109740 ⟨844466, by decide⟩ :=
  accepted_of_selected 12 109740 ⟨844466, by decide⟩ ⟨12, 2, 0, 844466, 109740, 1409, 65536⟩
    (by decide) selected_cut_32796

theorem selected_cut_32797 : selected 9 ⟨844485, by decide⟩
    (prefixPartial 12 109741) = some ⟨12, 2, 0, 844485, 109741, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_109741_844485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109741 ⟨844485, by decide⟩ :=
  accepted_of_selected 12 109741 ⟨844485, by decide⟩ ⟨12, 2, 0, 844485, 109741, 1509, 65536⟩
    (by decide) selected_cut_32797

theorem selected_cut_32798 : selected 9 ⟨769937, by decide⟩
    (prefixPartial 12 109742) = some ⟨12, 1, 0, 769937, 109742, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109742_769937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109742 ⟨769937, by decide⟩ :=
  accepted_of_selected 12 109742 ⟨769937, by decide⟩ ⟨12, 1, 0, 769937, 109742, 1, 65536⟩
    (by decide) selected_cut_32798

theorem selected_cut_32799 : selected 9 ⟨844512, by decide⟩
    (prefixPartial 12 109743) = some ⟨12, 2, 0, 844512, 109743, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_109743_844512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109743 ⟨844512, by decide⟩ :=
  accepted_of_selected 12 109743 ⟨844512, by decide⟩ ⟨12, 2, 0, 844512, 109743, 1473, 65536⟩
    (by decide) selected_cut_32799

theorem unmarked_context_11_27435_844513 : frontier 10 ⟨844513, by decide⟩
    (prefixCache 11 27435) (prefixPartial 11 27435) = false := by
  decide +kernel

theorem node_context_11_27435_844513 : EJMOriginalGlobalDAGData.nodes 10 ⟨844513, by decide⟩ =
    .split (coordinate 11) (![⟨844466, by decide⟩,⟨844485, by decide⟩,⟨769937, by decide⟩,⟨844512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27435_844513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27435 ⟨844513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27435
    ⟨844513, by decide⟩ (by decide) (![⟨844466, by decide⟩,⟨844485, by decide⟩,⟨769937, by decide⟩,⟨844512, by decide⟩]) unmarked_context_11_27435_844513 node_context_11_27435_844513
  intro a
  fin_cases a
  · exact context_12_109740_844466
  · exact context_12_109741_844485
  · exact context_12_109742_769937
  · exact context_12_109743_844512

theorem unmarked_context_10_6858_844514 : frontier 11 ⟨844514, by decide⟩
    (prefixCache 10 6858) (prefixPartial 10 6858) = false := by
  decide +kernel

theorem node_context_10_6858_844514 : EJMOriginalGlobalDAGData.nodes 11 ⟨844514, by decide⟩ =
    .split (coordinate 10) (![⟨844336, by decide⟩,⟨844393, by decide⟩,⟨844449, by decide⟩,⟨844513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6858_844514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6858 ⟨844514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6858
    ⟨844514, by decide⟩ (by decide) (![⟨844336, by decide⟩,⟨844393, by decide⟩,⟨844449, by decide⟩,⟨844513, by decide⟩]) unmarked_context_10_6858_844514 node_context_10_6858_844514
  intro a
  fin_cases a
  · exact context_11_27432_844336
  · exact context_11_27433_844393
  · exact context_11_27434_844449
  · exact context_11_27435_844513

theorem selected_cut_32800 : selected 10 ⟨844540, by decide⟩
    (prefixPartial 11 27436) = some ⟨11, 2, 0, 844540, 27436, 2545, 262144⟩ := by
  decide +kernel

theorem context_11_27436_844540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27436 ⟨844540, by decide⟩ :=
  accepted_of_selected 11 27436 ⟨844540, by decide⟩ ⟨11, 2, 0, 844540, 27436, 2545, 262144⟩
    (by decide) selected_cut_32800

theorem selected_cut_32801 : selected 9 ⟨844556, by decide⟩
    (prefixPartial 12 109748) = some ⟨12, 2, 0, 844556, 109748, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_109748_844556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109748 ⟨844556, by decide⟩ :=
  accepted_of_selected 12 109748 ⟨844556, by decide⟩ ⟨12, 2, 0, 844556, 109748, 1137, 65536⟩
    (by decide) selected_cut_32801

theorem selected_cut_32802 : selected 9 ⟨844574, by decide⟩
    (prefixPartial 12 109749) = some ⟨12, 2, 0, 844574, 109749, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_109749_844574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109749 ⟨844574, by decide⟩ :=
  accepted_of_selected 12 109749 ⟨844574, by decide⟩ ⟨12, 2, 0, 844574, 109749, 1225, 65536⟩
    (by decide) selected_cut_32802

theorem selected_cut_32803 : selected 9 ⟨844598, by decide⟩
    (prefixPartial 12 109750) = some ⟨12, 2, 0, 844598, 109750, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_109750_844598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109750 ⟨844598, by decide⟩ :=
  accepted_of_selected 12 109750 ⟨844598, by decide⟩ ⟨12, 2, 0, 844598, 109750, 1221, 65536⟩
    (by decide) selected_cut_32803

theorem selected_cut_32804 : selected 9 ⟨844611, by decide⟩
    (prefixPartial 12 109751) = some ⟨12, 2, 0, 844611, 109751, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_109751_844611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109751 ⟨844611, by decide⟩ :=
  accepted_of_selected 12 109751 ⟨844611, by decide⟩ ⟨12, 2, 0, 844611, 109751, 1181, 65536⟩
    (by decide) selected_cut_32804

theorem unmarked_context_11_27437_844612 : frontier 10 ⟨844612, by decide⟩
    (prefixCache 11 27437) (prefixPartial 11 27437) = false := by
  decide +kernel

theorem node_context_11_27437_844612 : EJMOriginalGlobalDAGData.nodes 10 ⟨844612, by decide⟩ =
    .split (coordinate 11) (![⟨844556, by decide⟩,⟨844574, by decide⟩,⟨844598, by decide⟩,⟨844611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27437_844612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27437 ⟨844612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27437
    ⟨844612, by decide⟩ (by decide) (![⟨844556, by decide⟩,⟨844574, by decide⟩,⟨844598, by decide⟩,⟨844611, by decide⟩]) unmarked_context_11_27437_844612 node_context_11_27437_844612
  intro a
  fin_cases a
  · exact context_12_109748_844556
  · exact context_12_109749_844574
  · exact context_12_109750_844598
  · exact context_12_109751_844611

theorem selected_cut_32805 : selected 10 ⟨844662, by decide⟩
    (prefixPartial 11 27438) = some ⟨11, 2, 0, 844662, 27438, 2953, 262144⟩ := by
  decide +kernel

theorem context_11_27438_844662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27438 ⟨844662, by decide⟩ :=
  accepted_of_selected 11 27438 ⟨844662, by decide⟩ ⟨11, 2, 0, 844662, 27438, 2953, 262144⟩
    (by decide) selected_cut_32805

theorem selected_cut_32806 : selected 10 ⟨844690, by decide⟩
    (prefixPartial 11 27439) = some ⟨11, 2, 0, 844690, 27439, 1237, 262144⟩ := by
  decide +kernel

theorem context_11_27439_844690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27439 ⟨844690, by decide⟩ :=
  accepted_of_selected 11 27439 ⟨844690, by decide⟩ ⟨11, 2, 0, 844690, 27439, 1237, 262144⟩
    (by decide) selected_cut_32806

theorem unmarked_context_10_6859_844691 : frontier 11 ⟨844691, by decide⟩
    (prefixCache 10 6859) (prefixPartial 10 6859) = false := by
  decide +kernel

theorem node_context_10_6859_844691 : EJMOriginalGlobalDAGData.nodes 11 ⟨844691, by decide⟩ =
    .split (coordinate 10) (![⟨844540, by decide⟩,⟨844612, by decide⟩,⟨844662, by decide⟩,⟨844690, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6859_844691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6859 ⟨844691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6859
    ⟨844691, by decide⟩ (by decide) (![⟨844540, by decide⟩,⟨844612, by decide⟩,⟨844662, by decide⟩,⟨844690, by decide⟩]) unmarked_context_10_6859_844691 node_context_10_6859_844691
  intro a
  fin_cases a
  · exact context_11_27436_844540
  · exact context_11_27437_844612
  · exact context_11_27438_844662
  · exact context_11_27439_844690

theorem unmarked_context_9_1714_844692 : frontier 12 ⟨844692, by decide⟩
    (prefixCache 9 1714) (prefixPartial 9 1714) = false := by
  decide +kernel

theorem node_context_9_1714_844692 : EJMOriginalGlobalDAGData.nodes 12 ⟨844692, by decide⟩ =
    .split (coordinate 9) (![⟨843864, by decide⟩,⟨844292, by decide⟩,⟨844514, by decide⟩,⟨844691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1714_844692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1714 ⟨844692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1714
    ⟨844692, by decide⟩ (by decide) (![⟨843864, by decide⟩,⟨844292, by decide⟩,⟨844514, by decide⟩,⟨844691, by decide⟩]) unmarked_context_9_1714_844692 node_context_9_1714_844692
  intro a
  fin_cases a
  · exact context_10_6856_843864
  · exact context_10_6857_844292
  · exact context_10_6858_844514
  · exact context_10_6859_844691

theorem selected_cut_32807 : selected 10 ⟨844713, by decide⟩
    (prefixPartial 11 27440) = some ⟨11, 2, 0, 844713, 27440, 2145, 262144⟩ := by
  decide +kernel

theorem context_11_27440_844713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27440 ⟨844713, by decide⟩ :=
  accepted_of_selected 11 27440 ⟨844713, by decide⟩ ⟨11, 2, 0, 844713, 27440, 2145, 262144⟩
    (by decide) selected_cut_32807

theorem selected_cut_32808 : selected 10 ⟨844751, by decide⟩
    (prefixPartial 11 27441) = some ⟨11, 2, 0, 844751, 27441, 2893, 262144⟩ := by
  decide +kernel

theorem context_11_27441_844751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27441 ⟨844751, by decide⟩ :=
  accepted_of_selected 11 27441 ⟨844751, by decide⟩ ⟨11, 2, 0, 844751, 27441, 2893, 262144⟩
    (by decide) selected_cut_32808

theorem selected_cut_32809 : selected 10 ⟨844783, by decide⟩
    (prefixPartial 11 27442) = some ⟨11, 2, 0, 844783, 27442, 2101, 262144⟩ := by
  decide +kernel

theorem context_11_27442_844783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27442 ⟨844783, by decide⟩ :=
  accepted_of_selected 11 27442 ⟨844783, by decide⟩ ⟨11, 2, 0, 844783, 27442, 2101, 262144⟩
    (by decide) selected_cut_32809

theorem selected_cut_32810 : selected 10 ⟨844817, by decide⟩
    (prefixPartial 11 27443) = some ⟨11, 2, 0, 844817, 27443, 2557, 262144⟩ := by
  decide +kernel

theorem context_11_27443_844817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27443 ⟨844817, by decide⟩ :=
  accepted_of_selected 11 27443 ⟨844817, by decide⟩ ⟨11, 2, 0, 844817, 27443, 2557, 262144⟩
    (by decide) selected_cut_32810

theorem unmarked_context_10_6860_844818 : frontier 11 ⟨844818, by decide⟩
    (prefixCache 10 6860) (prefixPartial 10 6860) = false := by
  decide +kernel

theorem node_context_10_6860_844818 : EJMOriginalGlobalDAGData.nodes 11 ⟨844818, by decide⟩ =
    .split (coordinate 10) (![⟨844713, by decide⟩,⟨844751, by decide⟩,⟨844783, by decide⟩,⟨844817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6860_844818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6860 ⟨844818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6860
    ⟨844818, by decide⟩ (by decide) (![⟨844713, by decide⟩,⟨844751, by decide⟩,⟨844783, by decide⟩,⟨844817, by decide⟩]) unmarked_context_10_6860_844818 node_context_10_6860_844818
  intro a
  fin_cases a
  · exact context_11_27440_844713
  · exact context_11_27441_844751
  · exact context_11_27442_844783
  · exact context_11_27443_844817

theorem selected_cut_32811 : selected 10 ⟨844837, by decide⟩
    (prefixPartial 11 27444) = some ⟨11, 2, 0, 844837, 27444, 2141, 262144⟩ := by
  decide +kernel

theorem context_11_27444_844837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27444 ⟨844837, by decide⟩ :=
  accepted_of_selected 11 27444 ⟨844837, by decide⟩ ⟨11, 2, 0, 844837, 27444, 2141, 262144⟩
    (by decide) selected_cut_32811

theorem selected_cut_32812 : selected 10 ⟨844861, by decide⟩
    (prefixPartial 11 27445) = some ⟨11, 2, 0, 844861, 27445, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_27445_844861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27445 ⟨844861, by decide⟩ :=
  accepted_of_selected 11 27445 ⟨844861, by decide⟩ ⟨11, 2, 0, 844861, 27445, 2173, 262144⟩
    (by decide) selected_cut_32812

theorem selected_cut_32813 : selected 10 ⟨844881, by decide⟩
    (prefixPartial 11 27446) = some ⟨11, 2, 0, 844881, 27446, 1629, 262144⟩ := by
  decide +kernel

theorem context_11_27446_844881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27446 ⟨844881, by decide⟩ :=
  accepted_of_selected 11 27446 ⟨844881, by decide⟩ ⟨11, 2, 0, 844881, 27446, 1629, 262144⟩
    (by decide) selected_cut_32813

theorem selected_cut_32814 : selected 10 ⟨844905, by decide⟩
    (prefixPartial 11 27447) = some ⟨11, 2, 0, 844905, 27447, 1705, 262144⟩ := by
  decide +kernel

theorem context_11_27447_844905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27447 ⟨844905, by decide⟩ :=
  accepted_of_selected 11 27447 ⟨844905, by decide⟩ ⟨11, 2, 0, 844905, 27447, 1705, 262144⟩
    (by decide) selected_cut_32814

theorem unmarked_context_10_6861_844906 : frontier 11 ⟨844906, by decide⟩
    (prefixCache 10 6861) (prefixPartial 10 6861) = false := by
  decide +kernel

theorem node_context_10_6861_844906 : EJMOriginalGlobalDAGData.nodes 11 ⟨844906, by decide⟩ =
    .split (coordinate 10) (![⟨844837, by decide⟩,⟨844861, by decide⟩,⟨844881, by decide⟩,⟨844905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6861_844906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6861 ⟨844906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6861
    ⟨844906, by decide⟩ (by decide) (![⟨844837, by decide⟩,⟨844861, by decide⟩,⟨844881, by decide⟩,⟨844905, by decide⟩]) unmarked_context_10_6861_844906 node_context_10_6861_844906
  intro a
  fin_cases a
  · exact context_11_27444_844837
  · exact context_11_27445_844861
  · exact context_11_27446_844881
  · exact context_11_27447_844905

theorem selected_cut_32815 : selected 11 ⟨844963, by decide⟩
    (prefixPartial 10 6862) = some ⟨10, 2, 0, 844963, 6862, 3957, 1048576⟩ := by
  decide +kernel

theorem context_10_6862_844963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6862 ⟨844963, by decide⟩ :=
  accepted_of_selected 10 6862 ⟨844963, by decide⟩ ⟨10, 2, 0, 844963, 6862, 3957, 1048576⟩
    (by decide) selected_cut_32815

theorem selected_cut_32816 : selected 11 ⟨844993, by decide⟩
    (prefixPartial 10 6863) = some ⟨10, 2, 0, 844993, 6863, 765, 1048576⟩ := by
  decide +kernel

theorem context_10_6863_844993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6863 ⟨844993, by decide⟩ :=
  accepted_of_selected 10 6863 ⟨844993, by decide⟩ ⟨10, 2, 0, 844993, 6863, 765, 1048576⟩
    (by decide) selected_cut_32816

theorem unmarked_context_9_1715_844994 : frontier 12 ⟨844994, by decide⟩
    (prefixCache 9 1715) (prefixPartial 9 1715) = false := by
  decide +kernel

theorem node_context_9_1715_844994 : EJMOriginalGlobalDAGData.nodes 12 ⟨844994, by decide⟩ =
    .split (coordinate 9) (![⟨844818, by decide⟩,⟨844906, by decide⟩,⟨844963, by decide⟩,⟨844993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1715_844994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1715 ⟨844994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1715
    ⟨844994, by decide⟩ (by decide) (![⟨844818, by decide⟩,⟨844906, by decide⟩,⟨844963, by decide⟩,⟨844993, by decide⟩]) unmarked_context_9_1715_844994 node_context_9_1715_844994
  intro a
  fin_cases a
  · exact context_10_6860_844818
  · exact context_10_6861_844906
  · exact context_10_6862_844963
  · exact context_10_6863_844993

theorem unmarked_context_8_428_844995 : frontier 13 ⟨844995, by decide⟩
    (prefixCache 8 428) (prefixPartial 8 428) = false := by
  decide +kernel

theorem node_context_8_428_844995 : EJMOriginalGlobalDAGData.nodes 13 ⟨844995, by decide⟩ =
    .split (coordinate 8) (![⟨840506, by decide⟩,⟨843452, by decide⟩,⟨844692, by decide⟩,⟨844994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_428_844995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 428 ⟨844995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 428
    ⟨844995, by decide⟩ (by decide) (![⟨840506, by decide⟩,⟨843452, by decide⟩,⟨844692, by decide⟩,⟨844994, by decide⟩]) unmarked_context_8_428_844995 node_context_8_428_844995
  intro a
  fin_cases a
  · exact context_9_1712_840506
  · exact context_9_1713_843452
  · exact context_9_1714_844692
  · exact context_9_1715_844994

theorem selected_cut_32817 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 27456) = some ⟨11, 1, 0, 434745, 27456, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27456_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27456 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 27456 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 27456, 1, 262144⟩
    (by decide) selected_cut_32817

theorem selected_cut_32818 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 109828) = some ⟨12, 1, 0, 448748, 109828, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109828_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109828 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 109828 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 109828, 1, 65536⟩
    (by decide) selected_cut_32818

theorem selected_cut_32819 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 109829) = some ⟨12, 1, 0, 34034, 109829, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109829_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109829 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 109829 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 109829, 1, 65536⟩
    (by decide) selected_cut_32819

theorem selected_cut_32820 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 109830) = some ⟨12, 1, 0, 763842, 109830, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109830_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109830 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 109830 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 109830, 1, 65536⟩
    (by decide) selected_cut_32820

theorem selected_cut_32821 : selected 8 ⟨845087, by decide⟩
    (prefixPartial 13 439324) = some ⟨13, 2, 0, 845087, 439324, 2877, 16384⟩ := by
  decide +kernel

theorem context_13_439324_845087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439324 ⟨845087, by decide⟩ :=
  accepted_of_selected 13 439324 ⟨845087, by decide⟩ ⟨13, 2, 0, 845087, 439324, 2877, 16384⟩
    (by decide) selected_cut_32821

theorem selected_cut_32822 : selected 8 ⟨845173, by decide⟩
    (prefixPartial 13 439325) = some ⟨13, 2, 0, 845173, 439325, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_439325_845173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439325 ⟨845173, by decide⟩ :=
  accepted_of_selected 13 439325 ⟨845173, by decide⟩ ⟨13, 2, 0, 845173, 439325, 1925, 16384⟩
    (by decide) selected_cut_32822

theorem selected_cut_32823 : selected 8 ⟨845209, by decide⟩
    (prefixPartial 13 439326) = some ⟨13, 2, 0, 845209, 439326, 585, 16384⟩ := by
  decide +kernel

theorem context_13_439326_845209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439326 ⟨845209, by decide⟩ :=
  accepted_of_selected 13 439326 ⟨845209, by decide⟩ ⟨13, 2, 0, 845209, 439326, 585, 16384⟩
    (by decide) selected_cut_32823

theorem selected_cut_32824 : selected 8 ⟨845214, by decide⟩
    (prefixPartial 13 439327) = some ⟨13, 2, 0, 845214, 439327, 137, 16384⟩ := by
  decide +kernel

theorem context_13_439327_845214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439327 ⟨845214, by decide⟩ :=
  accepted_of_selected 13 439327 ⟨845214, by decide⟩ ⟨13, 2, 0, 845214, 439327, 137, 16384⟩
    (by decide) selected_cut_32824

theorem unmarked_context_12_109831_845215 : frontier 9 ⟨845215, by decide⟩
    (prefixCache 12 109831) (prefixPartial 12 109831) = false := by
  decide +kernel

theorem node_context_12_109831_845215 : EJMOriginalGlobalDAGData.nodes 9 ⟨845215, by decide⟩ =
    .split (coordinate 12) (![⟨845087, by decide⟩,⟨845173, by decide⟩,⟨845209, by decide⟩,⟨845214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109831_845215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109831 ⟨845215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109831
    ⟨845215, by decide⟩ (by decide) (![⟨845087, by decide⟩,⟨845173, by decide⟩,⟨845209, by decide⟩,⟨845214, by decide⟩]) unmarked_context_12_109831_845215 node_context_12_109831_845215
  intro a
  fin_cases a
  · exact context_13_439324_845087
  · exact context_13_439325_845173
  · exact context_13_439326_845209
  · exact context_13_439327_845214

theorem unmarked_context_11_27457_845216 : frontier 10 ⟨845216, by decide⟩
    (prefixCache 11 27457) (prefixPartial 11 27457) = false := by
  decide +kernel

theorem node_context_11_27457_845216 : EJMOriginalGlobalDAGData.nodes 10 ⟨845216, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨763842, by decide⟩,⟨845215, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27457_845216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27457 ⟨845216, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27457
    ⟨845216, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨763842, by decide⟩,⟨845215, by decide⟩]) unmarked_context_11_27457_845216 node_context_11_27457_845216
  intro a
  fin_cases a
  · exact context_12_109828_448748
  · exact context_12_109829_34034
  · exact context_12_109830_763842
  · exact context_12_109831_845215

theorem selected_cut_32825 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 109832) = some ⟨12, 1, 0, 448748, 109832, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109832_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109832 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 109832 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 109832, 1, 65536⟩
    (by decide) selected_cut_32825

theorem selected_cut_32826 : selected 8 ⟨845306, by decide⟩
    (prefixPartial 13 439332) = some ⟨13, 2, 0, 845306, 439332, 3565, 16384⟩ := by
  decide +kernel

theorem context_13_439332_845306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439332 ⟨845306, by decide⟩ :=
  accepted_of_selected 13 439332 ⟨845306, by decide⟩ ⟨13, 2, 0, 845306, 439332, 3565, 16384⟩
    (by decide) selected_cut_32826

theorem selected_cut_32827 : selected 8 ⟨845357, by decide⟩
    (prefixPartial 13 439333) = some ⟨13, 2, 0, 845357, 439333, 2841, 16384⟩ := by
  decide +kernel

theorem context_13_439333_845357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439333 ⟨845357, by decide⟩ :=
  accepted_of_selected 13 439333 ⟨845357, by decide⟩ ⟨13, 2, 0, 845357, 439333, 2841, 16384⟩
    (by decide) selected_cut_32827

theorem selected_cut_32828 : selected 8 ⟨845466, by decide⟩
    (prefixPartial 13 439334) = some ⟨13, 2, 0, 845466, 439334, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_439334_845466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439334 ⟨845466, by decide⟩ :=
  accepted_of_selected 13 439334 ⟨845466, by decide⟩ ⟨13, 2, 0, 845466, 439334, 2245, 16384⟩
    (by decide) selected_cut_32828

theorem selected_cut_32829 : selected 8 ⟨845478, by decide⟩
    (prefixPartial 13 439335) = some ⟨13, 2, 0, 845478, 439335, 957, 16384⟩ := by
  decide +kernel

theorem context_13_439335_845478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439335 ⟨845478, by decide⟩ :=
  accepted_of_selected 13 439335 ⟨845478, by decide⟩ ⟨13, 2, 0, 845478, 439335, 957, 16384⟩
    (by decide) selected_cut_32829

theorem unmarked_context_12_109833_845479 : frontier 9 ⟨845479, by decide⟩
    (prefixCache 12 109833) (prefixPartial 12 109833) = false := by
  decide +kernel

theorem node_context_12_109833_845479 : EJMOriginalGlobalDAGData.nodes 9 ⟨845479, by decide⟩ =
    .split (coordinate 12) (![⟨845306, by decide⟩,⟨845357, by decide⟩,⟨845466, by decide⟩,⟨845478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109833_845479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109833 ⟨845479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109833
    ⟨845479, by decide⟩ (by decide) (![⟨845306, by decide⟩,⟨845357, by decide⟩,⟨845466, by decide⟩,⟨845478, by decide⟩]) unmarked_context_12_109833_845479 node_context_12_109833_845479
  intro a
  fin_cases a
  · exact context_13_439332_845306
  · exact context_13_439333_845357
  · exact context_13_439334_845466
  · exact context_13_439335_845478

theorem selected_cut_32830 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 109834) = some ⟨12, 1, 0, 763842, 109834, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109834_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109834 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 109834 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 109834, 1, 65536⟩
    (by decide) selected_cut_32830

theorem selected_cut_32831 : selected 9 ⟨604131, by decide⟩
    (prefixPartial 12 109835) = some ⟨12, 1, 0, 604131, 109835, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109835_604131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109835 ⟨604131, by decide⟩ :=
  accepted_of_selected 12 109835 ⟨604131, by decide⟩ ⟨12, 1, 0, 604131, 109835, 1, 65536⟩
    (by decide) selected_cut_32831

theorem unmarked_context_11_27458_845480 : frontier 10 ⟨845480, by decide⟩
    (prefixCache 11 27458) (prefixPartial 11 27458) = false := by
  decide +kernel

theorem node_context_11_27458_845480 : EJMOriginalGlobalDAGData.nodes 10 ⟨845480, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨845479, by decide⟩,⟨763842, by decide⟩,⟨604131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27458_845480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27458 ⟨845480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27458
    ⟨845480, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨845479, by decide⟩,⟨763842, by decide⟩,⟨604131, by decide⟩]) unmarked_context_11_27458_845480 node_context_11_27458_845480
  intro a
  fin_cases a
  · exact context_12_109832_448748
  · exact context_12_109833_845479
  · exact context_12_109834_763842
  · exact context_12_109835_604131

theorem selected_cut_32832 : selected 10 ⟨789341, by decide⟩
    (prefixPartial 11 27459) = some ⟨11, 1, 0, 789341, 27459, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27459_789341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27459 ⟨789341, by decide⟩ :=
  accepted_of_selected 11 27459 ⟨789341, by decide⟩ ⟨11, 1, 0, 789341, 27459, 1, 262144⟩
    (by decide) selected_cut_32832

theorem unmarked_context_10_6864_845481 : frontier 11 ⟨845481, by decide⟩
    (prefixCache 10 6864) (prefixPartial 10 6864) = false := by
  decide +kernel

theorem node_context_10_6864_845481 : EJMOriginalGlobalDAGData.nodes 11 ⟨845481, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨845216, by decide⟩,⟨845480, by decide⟩,⟨789341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6864_845481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6864 ⟨845481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6864
    ⟨845481, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨845216, by decide⟩,⟨845480, by decide⟩,⟨789341, by decide⟩]) unmarked_context_10_6864_845481 node_context_10_6864_845481
  intro a
  fin_cases a
  · exact context_11_27456_434745
  · exact context_11_27457_845216
  · exact context_11_27458_845480
  · exact context_11_27459_789341

theorem selected_cut_32833 : selected 8 ⟨845508, by decide⟩
    (prefixPartial 13 439360) = some ⟨13, 2, 0, 845508, 439360, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_439360_845508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439360 ⟨845508, by decide⟩ :=
  accepted_of_selected 13 439360 ⟨845508, by decide⟩ ⟨13, 2, 0, 845508, 439360, 1901, 16384⟩
    (by decide) selected_cut_32833

theorem selected_cut_32834 : selected 8 ⟨845532, by decide⟩
    (prefixPartial 13 439361) = some ⟨13, 2, 0, 845532, 439361, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_439361_845532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439361 ⟨845532, by decide⟩ :=
  accepted_of_selected 13 439361 ⟨845532, by decide⟩ ⟨13, 2, 0, 845532, 439361, 2301, 16384⟩
    (by decide) selected_cut_32834

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
