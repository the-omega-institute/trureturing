/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover025
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_02498 : selected 8 ⟨80072, by decide⟩
    (prefixPartial 13 22817) = some ⟨13, 2, 0, 80072, 22817, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_22817_80072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22817 ⟨80072, by decide⟩ :=
  accepted_of_selected 13 22817 ⟨80072, by decide⟩ ⟨13, 2, 0, 80072, 22817, 2349, 16384⟩
    (by decide) selected_cut_02498

theorem selected_cut_02499 : selected 8 ⟨80094, by decide⟩
    (prefixPartial 13 22818) = some ⟨13, 2, 0, 80094, 22818, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_22818_80094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22818 ⟨80094, by decide⟩ :=
  accepted_of_selected 13 22818 ⟨80094, by decide⟩ ⟨13, 2, 0, 80094, 22818, 1997, 16384⟩
    (by decide) selected_cut_02499

theorem selected_cut_02500 : selected 8 ⟨80105, by decide⟩
    (prefixPartial 13 22819) = some ⟨13, 2, 0, 80105, 22819, 913, 16384⟩ := by
  decide +kernel

theorem context_13_22819_80105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22819 ⟨80105, by decide⟩ :=
  accepted_of_selected 13 22819 ⟨80105, by decide⟩ ⟨13, 2, 0, 80105, 22819, 913, 16384⟩
    (by decide) selected_cut_02500

theorem unmarked_context_12_5704_80106 : frontier 9 ⟨80106, by decide⟩
    (prefixCache 12 5704) (prefixPartial 12 5704) = false := by
  decide +kernel

theorem node_context_12_5704_80106 : EJMOriginalGlobalDAGData.nodes 9 ⟨80106, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80072, by decide⟩,⟨80094, by decide⟩,⟨80105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5704_80106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5704 ⟨80106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5704
    ⟨80106, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80072, by decide⟩,⟨80094, by decide⟩,⟨80105, by decide⟩]) unmarked_context_12_5704_80106 node_context_12_5704_80106
  intro a
  fin_cases a
  · exact context_13_22816_3444
  · exact context_13_22817_80072
  · exact context_13_22818_80094
  · exact context_13_22819_80105

theorem selected_cut_02501 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22820) = some ⟨13, 1, 0, 3444, 22820, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22820_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22820 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22820 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22820, 1, 16384⟩
    (by decide) selected_cut_02501

theorem selected_cut_02502 : selected 8 ⟨80136, by decide⟩
    (prefixPartial 13 22821) = some ⟨13, 2, 0, 80136, 22821, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_22821_80136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22821 ⟨80136, by decide⟩ :=
  accepted_of_selected 13 22821 ⟨80136, by decide⟩ ⟨13, 2, 0, 80136, 22821, 2513, 16384⟩
    (by decide) selected_cut_02502

theorem selected_cut_02503 : selected 8 ⟨80158, by decide⟩
    (prefixPartial 13 22822) = some ⟨13, 2, 0, 80158, 22822, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_22822_80158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22822 ⟨80158, by decide⟩ :=
  accepted_of_selected 13 22822 ⟨80158, by decide⟩ ⟨13, 2, 0, 80158, 22822, 2109, 16384⟩
    (by decide) selected_cut_02503

theorem selected_cut_02504 : selected 8 ⟨80170, by decide⟩
    (prefixPartial 13 22823) = some ⟨13, 2, 0, 80170, 22823, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_22823_80170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22823 ⟨80170, by decide⟩ :=
  accepted_of_selected 13 22823 ⟨80170, by decide⟩ ⟨13, 2, 0, 80170, 22823, 1129, 16384⟩
    (by decide) selected_cut_02504

theorem unmarked_context_12_5705_80171 : frontier 9 ⟨80171, by decide⟩
    (prefixCache 12 5705) (prefixPartial 12 5705) = false := by
  decide +kernel

theorem node_context_12_5705_80171 : EJMOriginalGlobalDAGData.nodes 9 ⟨80171, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80136, by decide⟩,⟨80158, by decide⟩,⟨80170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5705_80171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5705 ⟨80171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5705
    ⟨80171, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80136, by decide⟩,⟨80158, by decide⟩,⟨80170, by decide⟩]) unmarked_context_12_5705_80171 node_context_12_5705_80171
  intro a
  fin_cases a
  · exact context_13_22820_3444
  · exact context_13_22821_80136
  · exact context_13_22822_80158
  · exact context_13_22823_80170

theorem selected_cut_02505 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22824) = some ⟨13, 1, 0, 3444, 22824, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22824_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22824 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22824 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22824, 1, 16384⟩
    (by decide) selected_cut_02505

theorem selected_cut_02506 : selected 7 ⟨80178, by decide⟩
    (prefixPartial 14 91300) = some ⟨14, 2, 0, 80178, 91300, 477, 4096⟩ := by
  decide +kernel

theorem context_14_91300_80178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 91300 ⟨80178, by decide⟩ :=
  accepted_of_selected 14 91300 ⟨80178, by decide⟩ ⟨14, 2, 0, 80178, 91300, 477, 4096⟩
    (by decide) selected_cut_02506

theorem selected_cut_02507 : selected 7 ⟨80193, by decide⟩
    (prefixPartial 14 91301) = some ⟨14, 2, 0, 80193, 91301, 1221, 4096⟩ := by
  decide +kernel

theorem context_14_91301_80193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 91301 ⟨80193, by decide⟩ :=
  accepted_of_selected 14 91301 ⟨80193, by decide⟩ ⟨14, 2, 0, 80193, 91301, 1221, 4096⟩
    (by decide) selected_cut_02507

theorem selected_cut_02508 : selected 7 ⟨80215, by decide⟩
    (prefixPartial 14 91302) = some ⟨14, 2, 0, 80215, 91302, 1385, 4096⟩ := by
  decide +kernel

theorem context_14_91302_80215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 91302 ⟨80215, by decide⟩ :=
  accepted_of_selected 14 91302 ⟨80215, by decide⟩ ⟨14, 2, 0, 80215, 91302, 1385, 4096⟩
    (by decide) selected_cut_02508

theorem selected_cut_02509 : selected 7 ⟨80231, by decide⟩
    (prefixPartial 14 91303) = some ⟨14, 2, 0, 80231, 91303, 1217, 4096⟩ := by
  decide +kernel

theorem context_14_91303_80231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 91303 ⟨80231, by decide⟩ :=
  accepted_of_selected 14 91303 ⟨80231, by decide⟩ ⟨14, 2, 0, 80231, 91303, 1217, 4096⟩
    (by decide) selected_cut_02509

theorem unmarked_context_13_22825_80232 : frontier 8 ⟨80232, by decide⟩
    (prefixCache 13 22825) (prefixPartial 13 22825) = false := by
  decide +kernel

theorem node_context_13_22825_80232 : EJMOriginalGlobalDAGData.nodes 8 ⟨80232, by decide⟩ =
    .split (coordinate 13) (![⟨80178, by decide⟩,⟨80193, by decide⟩,⟨80215, by decide⟩,⟨80231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_22825_80232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22825 ⟨80232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 22825
    ⟨80232, by decide⟩ (by decide) (![⟨80178, by decide⟩,⟨80193, by decide⟩,⟨80215, by decide⟩,⟨80231, by decide⟩]) unmarked_context_13_22825_80232 node_context_13_22825_80232
  intro a
  fin_cases a
  · exact context_14_91300_80178
  · exact context_14_91301_80193
  · exact context_14_91302_80215
  · exact context_14_91303_80231

theorem selected_cut_02510 : selected 8 ⟨80287, by decide⟩
    (prefixPartial 13 22826) = some ⟨13, 2, 0, 80287, 22826, 3357, 16384⟩ := by
  decide +kernel

theorem context_13_22826_80287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22826 ⟨80287, by decide⟩ :=
  accepted_of_selected 13 22826 ⟨80287, by decide⟩ ⟨13, 2, 0, 80287, 22826, 3357, 16384⟩
    (by decide) selected_cut_02510

theorem selected_cut_02511 : selected 8 ⟨80315, by decide⟩
    (prefixPartial 13 22827) = some ⟨13, 2, 0, 80315, 22827, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_22827_80315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22827 ⟨80315, by decide⟩ :=
  accepted_of_selected 13 22827 ⟨80315, by decide⟩ ⟨13, 2, 0, 80315, 22827, 1589, 16384⟩
    (by decide) selected_cut_02511

theorem unmarked_context_12_5706_80316 : frontier 9 ⟨80316, by decide⟩
    (prefixCache 12 5706) (prefixPartial 12 5706) = false := by
  decide +kernel

theorem node_context_12_5706_80316 : EJMOriginalGlobalDAGData.nodes 9 ⟨80316, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80232, by decide⟩,⟨80287, by decide⟩,⟨80315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5706_80316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5706 ⟨80316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5706
    ⟨80316, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80232, by decide⟩,⟨80287, by decide⟩,⟨80315, by decide⟩]) unmarked_context_12_5706_80316 node_context_12_5706_80316
  intro a
  fin_cases a
  · exact context_13_22824_3444
  · exact context_13_22825_80232
  · exact context_13_22826_80287
  · exact context_13_22827_80315

theorem selected_cut_02512 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22828) = some ⟨13, 1, 0, 3444, 22828, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22828_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22828 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22828 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22828, 1, 16384⟩
    (by decide) selected_cut_02512

theorem selected_cut_02513 : selected 8 ⟨80352, by decide⟩
    (prefixPartial 13 22829) = some ⟨13, 2, 0, 80352, 22829, 2889, 16384⟩ := by
  decide +kernel

theorem context_13_22829_80352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22829 ⟨80352, by decide⟩ :=
  accepted_of_selected 13 22829 ⟨80352, by decide⟩ ⟨13, 2, 0, 80352, 22829, 2889, 16384⟩
    (by decide) selected_cut_02513

theorem selected_cut_02514 : selected 8 ⟨80380, by decide⟩
    (prefixPartial 13 22830) = some ⟨13, 2, 0, 80380, 22830, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_22830_80380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22830 ⟨80380, by decide⟩ :=
  accepted_of_selected 13 22830 ⟨80380, by decide⟩ ⟨13, 2, 0, 80380, 22830, 2293, 16384⟩
    (by decide) selected_cut_02514

theorem selected_cut_02515 : selected 8 ⟨80387, by decide⟩
    (prefixPartial 13 22831) = some ⟨13, 2, 0, 80387, 22831, 957, 16384⟩ := by
  decide +kernel

theorem context_13_22831_80387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22831 ⟨80387, by decide⟩ :=
  accepted_of_selected 13 22831 ⟨80387, by decide⟩ ⟨13, 2, 0, 80387, 22831, 957, 16384⟩
    (by decide) selected_cut_02515

theorem unmarked_context_12_5707_80388 : frontier 9 ⟨80388, by decide⟩
    (prefixCache 12 5707) (prefixPartial 12 5707) = false := by
  decide +kernel

theorem node_context_12_5707_80388 : EJMOriginalGlobalDAGData.nodes 9 ⟨80388, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80352, by decide⟩,⟨80380, by decide⟩,⟨80387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5707_80388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5707 ⟨80388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5707
    ⟨80388, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80352, by decide⟩,⟨80380, by decide⟩,⟨80387, by decide⟩]) unmarked_context_12_5707_80388 node_context_12_5707_80388
  intro a
  fin_cases a
  · exact context_13_22828_3444
  · exact context_13_22829_80352
  · exact context_13_22830_80380
  · exact context_13_22831_80387

theorem unmarked_context_11_1426_80389 : frontier 10 ⟨80389, by decide⟩
    (prefixCache 11 1426) (prefixPartial 11 1426) = false := by
  decide +kernel

theorem node_context_11_1426_80389 : EJMOriginalGlobalDAGData.nodes 10 ⟨80389, by decide⟩ =
    .split (coordinate 11) (![⟨80106, by decide⟩,⟨80171, by decide⟩,⟨80316, by decide⟩,⟨80388, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1426_80389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1426 ⟨80389, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1426
    ⟨80389, by decide⟩ (by decide) (![⟨80106, by decide⟩,⟨80171, by decide⟩,⟨80316, by decide⟩,⟨80388, by decide⟩]) unmarked_context_11_1426_80389 node_context_11_1426_80389
  intro a
  fin_cases a
  · exact context_12_5704_80106
  · exact context_12_5705_80171
  · exact context_12_5706_80316
  · exact context_12_5707_80388

theorem selected_cut_02516 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22832) = some ⟨13, 1, 0, 3444, 22832, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22832_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22832 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22832 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22832, 1, 16384⟩
    (by decide) selected_cut_02516

theorem selected_cut_02517 : selected 8 ⟨80417, by decide⟩
    (prefixPartial 13 22833) = some ⟨13, 2, 0, 80417, 22833, 2393, 16384⟩ := by
  decide +kernel

theorem context_13_22833_80417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22833 ⟨80417, by decide⟩ :=
  accepted_of_selected 13 22833 ⟨80417, by decide⟩ ⟨13, 2, 0, 80417, 22833, 2393, 16384⟩
    (by decide) selected_cut_02517

theorem selected_cut_02518 : selected 8 ⟨80441, by decide⟩
    (prefixPartial 13 22834) = some ⟨13, 2, 0, 80441, 22834, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_22834_80441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22834 ⟨80441, by decide⟩ :=
  accepted_of_selected 13 22834 ⟨80441, by decide⟩ ⟨13, 2, 0, 80441, 22834, 2129, 16384⟩
    (by decide) selected_cut_02518

theorem selected_cut_02519 : selected 8 ⟨80451, by decide⟩
    (prefixPartial 13 22835) = some ⟨13, 2, 0, 80451, 22835, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_22835_80451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22835 ⟨80451, by decide⟩ :=
  accepted_of_selected 13 22835 ⟨80451, by decide⟩ ⟨13, 2, 0, 80451, 22835, 1157, 16384⟩
    (by decide) selected_cut_02519

theorem unmarked_context_12_5708_80452 : frontier 9 ⟨80452, by decide⟩
    (prefixCache 12 5708) (prefixPartial 12 5708) = false := by
  decide +kernel

theorem node_context_12_5708_80452 : EJMOriginalGlobalDAGData.nodes 9 ⟨80452, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80417, by decide⟩,⟨80441, by decide⟩,⟨80451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5708_80452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5708 ⟨80452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5708
    ⟨80452, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80417, by decide⟩,⟨80441, by decide⟩,⟨80451, by decide⟩]) unmarked_context_12_5708_80452 node_context_12_5708_80452
  intro a
  fin_cases a
  · exact context_13_22832_3444
  · exact context_13_22833_80417
  · exact context_13_22834_80441
  · exact context_13_22835_80451

theorem selected_cut_02520 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22836) = some ⟨13, 1, 0, 3444, 22836, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22836_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22836 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22836 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22836, 1, 16384⟩
    (by decide) selected_cut_02520

theorem selected_cut_02521 : selected 8 ⟨80486, by decide⟩
    (prefixPartial 13 22837) = some ⟨13, 2, 0, 80486, 22837, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_22837_80486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22837 ⟨80486, by decide⟩ :=
  accepted_of_selected 13 22837 ⟨80486, by decide⟩ ⟨13, 2, 0, 80486, 22837, 2493, 16384⟩
    (by decide) selected_cut_02521

theorem selected_cut_02522 : selected 8 ⟨80517, by decide⟩
    (prefixPartial 13 22838) = some ⟨13, 2, 0, 80517, 22838, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_22838_80517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22838 ⟨80517, by decide⟩ :=
  accepted_of_selected 13 22838 ⟨80517, by decide⟩ ⟨13, 2, 0, 80517, 22838, 2317, 16384⟩
    (by decide) selected_cut_02522

theorem selected_cut_02523 : selected 8 ⟨80531, by decide⟩
    (prefixPartial 13 22839) = some ⟨13, 2, 0, 80531, 22839, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_22839_80531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22839 ⟨80531, by decide⟩ :=
  accepted_of_selected 13 22839 ⟨80531, by decide⟩ ⟨13, 2, 0, 80531, 22839, 1237, 16384⟩
    (by decide) selected_cut_02523

theorem unmarked_context_12_5709_80532 : frontier 9 ⟨80532, by decide⟩
    (prefixCache 12 5709) (prefixPartial 12 5709) = false := by
  decide +kernel

theorem node_context_12_5709_80532 : EJMOriginalGlobalDAGData.nodes 9 ⟨80532, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80486, by decide⟩,⟨80517, by decide⟩,⟨80531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5709_80532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5709 ⟨80532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5709
    ⟨80532, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80486, by decide⟩,⟨80517, by decide⟩,⟨80531, by decide⟩]) unmarked_context_12_5709_80532 node_context_12_5709_80532
  intro a
  fin_cases a
  · exact context_13_22836_3444
  · exact context_13_22837_80486
  · exact context_13_22838_80517
  · exact context_13_22839_80531

theorem selected_cut_02524 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22840) = some ⟨13, 1, 0, 3444, 22840, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22840_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22840 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22840 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22840, 1, 16384⟩
    (by decide) selected_cut_02524

theorem selected_cut_02525 : selected 8 ⟨80564, by decide⟩
    (prefixPartial 13 22841) = some ⟨13, 2, 0, 80564, 22841, 2829, 16384⟩ := by
  decide +kernel

theorem context_13_22841_80564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22841 ⟨80564, by decide⟩ :=
  accepted_of_selected 13 22841 ⟨80564, by decide⟩ ⟨13, 2, 0, 80564, 22841, 2829, 16384⟩
    (by decide) selected_cut_02525

theorem selected_cut_02526 : selected 8 ⟨80590, by decide⟩
    (prefixPartial 13 22842) = some ⟨13, 2, 0, 80590, 22842, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_22842_80590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22842 ⟨80590, by decide⟩ :=
  accepted_of_selected 13 22842 ⟨80590, by decide⟩ ⟨13, 2, 0, 80590, 22842, 2133, 16384⟩
    (by decide) selected_cut_02526

theorem selected_cut_02527 : selected 8 ⟨80609, by decide⟩
    (prefixPartial 13 22843) = some ⟨13, 2, 0, 80609, 22843, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_22843_80609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22843 ⟨80609, by decide⟩ :=
  accepted_of_selected 13 22843 ⟨80609, by decide⟩ ⟨13, 2, 0, 80609, 22843, 1265, 16384⟩
    (by decide) selected_cut_02527

theorem unmarked_context_12_5710_80610 : frontier 9 ⟨80610, by decide⟩
    (prefixCache 12 5710) (prefixPartial 12 5710) = false := by
  decide +kernel

theorem node_context_12_5710_80610 : EJMOriginalGlobalDAGData.nodes 9 ⟨80610, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80564, by decide⟩,⟨80590, by decide⟩,⟨80609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5710_80610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5710 ⟨80610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5710
    ⟨80610, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80564, by decide⟩,⟨80590, by decide⟩,⟨80609, by decide⟩]) unmarked_context_12_5710_80610 node_context_12_5710_80610
  intro a
  fin_cases a
  · exact context_13_22840_3444
  · exact context_13_22841_80564
  · exact context_13_22842_80590
  · exact context_13_22843_80609

theorem selected_cut_02528 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22844) = some ⟨13, 1, 0, 3444, 22844, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22844_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22844 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22844 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22844, 1, 16384⟩
    (by decide) selected_cut_02528

theorem selected_cut_02529 : selected 8 ⟨80641, by decide⟩
    (prefixPartial 13 22845) = some ⟨13, 2, 0, 80641, 22845, 2713, 16384⟩ := by
  decide +kernel

theorem context_13_22845_80641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22845 ⟨80641, by decide⟩ :=
  accepted_of_selected 13 22845 ⟨80641, by decide⟩ ⟨13, 2, 0, 80641, 22845, 2713, 16384⟩
    (by decide) selected_cut_02529

theorem selected_cut_02530 : selected 8 ⟨80665, by decide⟩
    (prefixPartial 13 22846) = some ⟨13, 2, 0, 80665, 22846, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_22846_80665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22846 ⟨80665, by decide⟩ :=
  accepted_of_selected 13 22846 ⟨80665, by decide⟩ ⟨13, 2, 0, 80665, 22846, 2333, 16384⟩
    (by decide) selected_cut_02530

theorem selected_cut_02531 : selected 8 ⟨80674, by decide⟩
    (prefixPartial 13 22847) = some ⟨13, 2, 0, 80674, 22847, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_22847_80674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22847 ⟨80674, by decide⟩ :=
  accepted_of_selected 13 22847 ⟨80674, by decide⟩ ⟨13, 2, 0, 80674, 22847, 1157, 16384⟩
    (by decide) selected_cut_02531

theorem unmarked_context_12_5711_80675 : frontier 9 ⟨80675, by decide⟩
    (prefixCache 12 5711) (prefixPartial 12 5711) = false := by
  decide +kernel

theorem node_context_12_5711_80675 : EJMOriginalGlobalDAGData.nodes 9 ⟨80675, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80641, by decide⟩,⟨80665, by decide⟩,⟨80674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5711_80675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5711 ⟨80675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5711
    ⟨80675, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80641, by decide⟩,⟨80665, by decide⟩,⟨80674, by decide⟩]) unmarked_context_12_5711_80675 node_context_12_5711_80675
  intro a
  fin_cases a
  · exact context_13_22844_3444
  · exact context_13_22845_80641
  · exact context_13_22846_80665
  · exact context_13_22847_80674

theorem unmarked_context_11_1427_80676 : frontier 10 ⟨80676, by decide⟩
    (prefixCache 11 1427) (prefixPartial 11 1427) = false := by
  decide +kernel

theorem node_context_11_1427_80676 : EJMOriginalGlobalDAGData.nodes 10 ⟨80676, by decide⟩ =
    .split (coordinate 11) (![⟨80452, by decide⟩,⟨80532, by decide⟩,⟨80610, by decide⟩,⟨80675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1427_80676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1427 ⟨80676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1427
    ⟨80676, by decide⟩ (by decide) (![⟨80452, by decide⟩,⟨80532, by decide⟩,⟨80610, by decide⟩,⟨80675, by decide⟩]) unmarked_context_11_1427_80676 node_context_11_1427_80676
  intro a
  fin_cases a
  · exact context_12_5708_80452
  · exact context_12_5709_80532
  · exact context_12_5710_80610
  · exact context_12_5711_80675

theorem unmarked_context_10_356_80677 : frontier 11 ⟨80677, by decide⟩
    (prefixCache 10 356) (prefixPartial 10 356) = false := by
  decide +kernel

theorem node_context_10_356_80677 : EJMOriginalGlobalDAGData.nodes 11 ⟨80677, by decide⟩ =
    .split (coordinate 10) (![⟨79797, by decide⟩,⟨80046, by decide⟩,⟨80389, by decide⟩,⟨80676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_356_80677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 356 ⟨80677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 356
    ⟨80677, by decide⟩ (by decide) (![⟨79797, by decide⟩,⟨80046, by decide⟩,⟨80389, by decide⟩,⟨80676, by decide⟩]) unmarked_context_10_356_80677 node_context_10_356_80677
  intro a
  fin_cases a
  · exact context_11_1424_79797
  · exact context_11_1425_80046
  · exact context_11_1426_80389
  · exact context_11_1427_80676

theorem selected_cut_02532 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22848) = some ⟨13, 1, 0, 3444, 22848, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22848_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22848 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22848 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22848, 1, 16384⟩
    (by decide) selected_cut_02532

theorem selected_cut_02533 : selected 8 ⟨80696, by decide⟩
    (prefixPartial 13 22849) = some ⟨13, 2, 0, 80696, 22849, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_22849_80696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22849 ⟨80696, by decide⟩ :=
  accepted_of_selected 13 22849 ⟨80696, by decide⟩ ⟨13, 2, 0, 80696, 22849, 1549, 16384⟩
    (by decide) selected_cut_02533

theorem selected_cut_02534 : selected 8 ⟨80719, by decide⟩
    (prefixPartial 13 22850) = some ⟨13, 2, 0, 80719, 22850, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_22850_80719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22850 ⟨80719, by decide⟩ :=
  accepted_of_selected 13 22850 ⟨80719, by decide⟩ ⟨13, 2, 0, 80719, 22850, 1965, 16384⟩
    (by decide) selected_cut_02534

theorem selected_cut_02535 : selected 8 ⟨80728, by decide⟩
    (prefixPartial 13 22851) = some ⟨13, 2, 0, 80728, 22851, 913, 16384⟩ := by
  decide +kernel

theorem context_13_22851_80728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22851 ⟨80728, by decide⟩ :=
  accepted_of_selected 13 22851 ⟨80728, by decide⟩ ⟨13, 2, 0, 80728, 22851, 913, 16384⟩
    (by decide) selected_cut_02535

theorem unmarked_context_12_5712_80729 : frontier 9 ⟨80729, by decide⟩
    (prefixCache 12 5712) (prefixPartial 12 5712) = false := by
  decide +kernel

theorem node_context_12_5712_80729 : EJMOriginalGlobalDAGData.nodes 9 ⟨80729, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80696, by decide⟩,⟨80719, by decide⟩,⟨80728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5712_80729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5712 ⟨80729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5712
    ⟨80729, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80696, by decide⟩,⟨80719, by decide⟩,⟨80728, by decide⟩]) unmarked_context_12_5712_80729 node_context_12_5712_80729
  intro a
  fin_cases a
  · exact context_13_22848_3444
  · exact context_13_22849_80696
  · exact context_13_22850_80719
  · exact context_13_22851_80728

theorem selected_cut_02536 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22852) = some ⟨13, 1, 0, 3444, 22852, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22852_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22852 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22852 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22852, 1, 16384⟩
    (by decide) selected_cut_02536

theorem selected_cut_02537 : selected 8 ⟨80749, by decide⟩
    (prefixPartial 13 22853) = some ⟨13, 2, 0, 80749, 22853, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_22853_80749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22853 ⟨80749, by decide⟩ :=
  accepted_of_selected 13 22853 ⟨80749, by decide⟩ ⟨13, 2, 0, 80749, 22853, 1697, 16384⟩
    (by decide) selected_cut_02537

theorem selected_cut_02538 : selected 8 ⟨80774, by decide⟩
    (prefixPartial 13 22854) = some ⟨13, 2, 0, 80774, 22854, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_22854_80774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22854 ⟨80774, by decide⟩ :=
  accepted_of_selected 13 22854 ⟨80774, by decide⟩ ⟨13, 2, 0, 80774, 22854, 1913, 16384⟩
    (by decide) selected_cut_02538

theorem selected_cut_02539 : selected 8 ⟨80784, by decide⟩
    (prefixPartial 13 22855) = some ⟨13, 2, 0, 80784, 22855, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_22855_80784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22855 ⟨80784, by decide⟩ :=
  accepted_of_selected 13 22855 ⟨80784, by decide⟩ ⟨13, 2, 0, 80784, 22855, 1081, 16384⟩
    (by decide) selected_cut_02539

theorem unmarked_context_12_5713_80785 : frontier 9 ⟨80785, by decide⟩
    (prefixCache 12 5713) (prefixPartial 12 5713) = false := by
  decide +kernel

theorem node_context_12_5713_80785 : EJMOriginalGlobalDAGData.nodes 9 ⟨80785, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80749, by decide⟩,⟨80774, by decide⟩,⟨80784, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5713_80785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5713 ⟨80785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5713
    ⟨80785, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80749, by decide⟩,⟨80774, by decide⟩,⟨80784, by decide⟩]) unmarked_context_12_5713_80785 node_context_12_5713_80785
  intro a
  fin_cases a
  · exact context_13_22852_3444
  · exact context_13_22853_80749
  · exact context_13_22854_80774
  · exact context_13_22855_80784

theorem selected_cut_02540 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22856) = some ⟨13, 1, 0, 3444, 22856, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22856_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22856 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22856 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22856, 1, 16384⟩
    (by decide) selected_cut_02540

theorem selected_cut_02541 : selected 8 ⟨80805, by decide⟩
    (prefixPartial 13 22857) = some ⟨13, 2, 0, 80805, 22857, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_22857_80805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22857 ⟨80805, by decide⟩ :=
  accepted_of_selected 13 22857 ⟨80805, by decide⟩ ⟨13, 2, 0, 80805, 22857, 1925, 16384⟩
    (by decide) selected_cut_02541

theorem selected_cut_02542 : selected 8 ⟨80824, by decide⟩
    (prefixPartial 13 22858) = some ⟨13, 2, 0, 80824, 22858, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_22858_80824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22858 ⟨80824, by decide⟩ :=
  accepted_of_selected 13 22858 ⟨80824, by decide⟩ ⟨13, 2, 0, 80824, 22858, 1913, 16384⟩
    (by decide) selected_cut_02542

theorem selected_cut_02543 : selected 8 ⟨80839, by decide⟩
    (prefixPartial 13 22859) = some ⟨13, 2, 0, 80839, 22859, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_22859_80839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22859 ⟨80839, by decide⟩ :=
  accepted_of_selected 13 22859 ⟨80839, by decide⟩ ⟨13, 2, 0, 80839, 22859, 1125, 16384⟩
    (by decide) selected_cut_02543

theorem unmarked_context_12_5714_80840 : frontier 9 ⟨80840, by decide⟩
    (prefixCache 12 5714) (prefixPartial 12 5714) = false := by
  decide +kernel

theorem node_context_12_5714_80840 : EJMOriginalGlobalDAGData.nodes 9 ⟨80840, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80805, by decide⟩,⟨80824, by decide⟩,⟨80839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5714_80840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5714 ⟨80840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5714
    ⟨80840, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80805, by decide⟩,⟨80824, by decide⟩,⟨80839, by decide⟩]) unmarked_context_12_5714_80840 node_context_12_5714_80840
  intro a
  fin_cases a
  · exact context_13_22856_3444
  · exact context_13_22857_80805
  · exact context_13_22858_80824
  · exact context_13_22859_80839

theorem selected_cut_02544 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22860) = some ⟨13, 1, 0, 3444, 22860, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22860_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22860 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22860 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22860, 1, 16384⟩
    (by decide) selected_cut_02544

theorem selected_cut_02545 : selected 8 ⟨80870, by decide⟩
    (prefixPartial 13 22861) = some ⟨13, 2, 0, 80870, 22861, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_22861_80870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22861 ⟨80870, by decide⟩ :=
  accepted_of_selected 13 22861 ⟨80870, by decide⟩ ⟨13, 2, 0, 80870, 22861, 2153, 16384⟩
    (by decide) selected_cut_02545

theorem selected_cut_02546 : selected 8 ⟨80892, by decide⟩
    (prefixPartial 13 22862) = some ⟨13, 2, 0, 80892, 22862, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_22862_80892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22862 ⟨80892, by decide⟩ :=
  accepted_of_selected 13 22862 ⟨80892, by decide⟩ ⟨13, 2, 0, 80892, 22862, 2161, 16384⟩
    (by decide) selected_cut_02546

theorem selected_cut_02547 : selected 8 ⟨80905, by decide⟩
    (prefixPartial 13 22863) = some ⟨13, 2, 0, 80905, 22863, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_22863_80905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22863 ⟨80905, by decide⟩ :=
  accepted_of_selected 13 22863 ⟨80905, by decide⟩ ⟨13, 2, 0, 80905, 22863, 1037, 16384⟩
    (by decide) selected_cut_02547

theorem unmarked_context_12_5715_80906 : frontier 9 ⟨80906, by decide⟩
    (prefixCache 12 5715) (prefixPartial 12 5715) = false := by
  decide +kernel

theorem node_context_12_5715_80906 : EJMOriginalGlobalDAGData.nodes 9 ⟨80906, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80870, by decide⟩,⟨80892, by decide⟩,⟨80905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5715_80906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5715 ⟨80906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5715
    ⟨80906, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80870, by decide⟩,⟨80892, by decide⟩,⟨80905, by decide⟩]) unmarked_context_12_5715_80906 node_context_12_5715_80906
  intro a
  fin_cases a
  · exact context_13_22860_3444
  · exact context_13_22861_80870
  · exact context_13_22862_80892
  · exact context_13_22863_80905

theorem unmarked_context_11_1428_80907 : frontier 10 ⟨80907, by decide⟩
    (prefixCache 11 1428) (prefixPartial 11 1428) = false := by
  decide +kernel

theorem node_context_11_1428_80907 : EJMOriginalGlobalDAGData.nodes 10 ⟨80907, by decide⟩ =
    .split (coordinate 11) (![⟨80729, by decide⟩,⟨80785, by decide⟩,⟨80840, by decide⟩,⟨80906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1428_80907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1428 ⟨80907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1428
    ⟨80907, by decide⟩ (by decide) (![⟨80729, by decide⟩,⟨80785, by decide⟩,⟨80840, by decide⟩,⟨80906, by decide⟩]) unmarked_context_11_1428_80907 node_context_11_1428_80907
  intro a
  fin_cases a
  · exact context_12_5712_80729
  · exact context_12_5713_80785
  · exact context_12_5714_80840
  · exact context_12_5715_80906

theorem selected_cut_02548 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22864) = some ⟨13, 1, 0, 3444, 22864, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22864_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22864 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22864 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22864, 1, 16384⟩
    (by decide) selected_cut_02548

theorem selected_cut_02549 : selected 8 ⟨80969, by decide⟩
    (prefixPartial 13 22865) = some ⟨13, 2, 0, 80969, 22865, 3205, 16384⟩ := by
  decide +kernel

theorem context_13_22865_80969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22865 ⟨80969, by decide⟩ :=
  accepted_of_selected 13 22865 ⟨80969, by decide⟩ ⟨13, 2, 0, 80969, 22865, 3205, 16384⟩
    (by decide) selected_cut_02549

theorem selected_cut_02550 : selected 8 ⟨81023, by decide⟩
    (prefixPartial 13 22866) = some ⟨13, 2, 0, 81023, 22866, 3085, 16384⟩ := by
  decide +kernel

theorem context_13_22866_81023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22866 ⟨81023, by decide⟩ :=
  accepted_of_selected 13 22866 ⟨81023, by decide⟩ ⟨13, 2, 0, 81023, 22866, 3085, 16384⟩
    (by decide) selected_cut_02550

theorem selected_cut_02551 : selected 8 ⟨81053, by decide⟩
    (prefixPartial 13 22867) = some ⟨13, 2, 0, 81053, 22867, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_22867_81053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22867 ⟨81053, by decide⟩ :=
  accepted_of_selected 13 22867 ⟨81053, by decide⟩ ⟨13, 2, 0, 81053, 22867, 1541, 16384⟩
    (by decide) selected_cut_02551

theorem unmarked_context_12_5716_81054 : frontier 9 ⟨81054, by decide⟩
    (prefixCache 12 5716) (prefixPartial 12 5716) = false := by
  decide +kernel

theorem node_context_12_5716_81054 : EJMOriginalGlobalDAGData.nodes 9 ⟨81054, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨80969, by decide⟩,⟨81023, by decide⟩,⟨81053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5716_81054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5716 ⟨81054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5716
    ⟨81054, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨80969, by decide⟩,⟨81023, by decide⟩,⟨81053, by decide⟩]) unmarked_context_12_5716_81054 node_context_12_5716_81054
  intro a
  fin_cases a
  · exact context_13_22864_3444
  · exact context_13_22865_80969
  · exact context_13_22866_81023
  · exact context_13_22867_81053

theorem selected_cut_02552 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22868) = some ⟨13, 1, 0, 3444, 22868, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22868_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22868 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22868 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22868, 1, 16384⟩
    (by decide) selected_cut_02552

theorem selected_cut_02553 : selected 8 ⟨81098, by decide⟩
    (prefixPartial 13 22869) = some ⟨13, 2, 0, 81098, 22869, 3085, 16384⟩ := by
  decide +kernel

theorem context_13_22869_81098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22869 ⟨81098, by decide⟩ :=
  accepted_of_selected 13 22869 ⟨81098, by decide⟩ ⟨13, 2, 0, 81098, 22869, 3085, 16384⟩
    (by decide) selected_cut_02553

theorem selected_cut_02554 : selected 8 ⟨81151, by decide⟩
    (prefixPartial 13 22870) = some ⟨13, 2, 0, 81151, 22870, 3049, 16384⟩ := by
  decide +kernel

theorem context_13_22870_81151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22870 ⟨81151, by decide⟩ :=
  accepted_of_selected 13 22870 ⟨81151, by decide⟩ ⟨13, 2, 0, 81151, 22870, 3049, 16384⟩
    (by decide) selected_cut_02554

theorem selected_cut_02555 : selected 8 ⟨81177, by decide⟩
    (prefixPartial 13 22871) = some ⟨13, 2, 0, 81177, 22871, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_22871_81177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22871 ⟨81177, by decide⟩ :=
  accepted_of_selected 13 22871 ⟨81177, by decide⟩ ⟨13, 2, 0, 81177, 22871, 1661, 16384⟩
    (by decide) selected_cut_02555

theorem unmarked_context_12_5717_81178 : frontier 9 ⟨81178, by decide⟩
    (prefixCache 12 5717) (prefixPartial 12 5717) = false := by
  decide +kernel

theorem node_context_12_5717_81178 : EJMOriginalGlobalDAGData.nodes 9 ⟨81178, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨81098, by decide⟩,⟨81151, by decide⟩,⟨81177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5717_81178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5717 ⟨81178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5717
    ⟨81178, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨81098, by decide⟩,⟨81151, by decide⟩,⟨81177, by decide⟩]) unmarked_context_12_5717_81178 node_context_12_5717_81178
  intro a
  fin_cases a
  · exact context_13_22868_3444
  · exact context_13_22869_81098
  · exact context_13_22870_81151
  · exact context_13_22871_81177

theorem selected_cut_02556 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22872) = some ⟨13, 1, 0, 3444, 22872, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22872_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22872 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22872 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22872, 1, 16384⟩
    (by decide) selected_cut_02556

theorem selected_cut_02557 : selected 8 ⟨81227, by decide⟩
    (prefixPartial 13 22873) = some ⟨13, 2, 0, 81227, 22873, 3177, 16384⟩ := by
  decide +kernel

theorem context_13_22873_81227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22873 ⟨81227, by decide⟩ :=
  accepted_of_selected 13 22873 ⟨81227, by decide⟩ ⟨13, 2, 0, 81227, 22873, 3177, 16384⟩
    (by decide) selected_cut_02557

theorem selected_cut_02558 : selected 8 ⟨81276, by decide⟩
    (prefixPartial 13 22874) = some ⟨13, 2, 0, 81276, 22874, 2881, 16384⟩ := by
  decide +kernel

theorem context_13_22874_81276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22874 ⟨81276, by decide⟩ :=
  accepted_of_selected 13 22874 ⟨81276, by decide⟩ ⟨13, 2, 0, 81276, 22874, 2881, 16384⟩
    (by decide) selected_cut_02558

theorem selected_cut_02559 : selected 8 ⟨81326, by decide⟩
    (prefixPartial 13 22875) = some ⟨13, 2, 0, 81326, 22875, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_22875_81326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22875 ⟨81326, by decide⟩ :=
  accepted_of_selected 13 22875 ⟨81326, by decide⟩ ⟨13, 2, 0, 81326, 22875, 1905, 16384⟩
    (by decide) selected_cut_02559

theorem unmarked_context_12_5718_81327 : frontier 9 ⟨81327, by decide⟩
    (prefixCache 12 5718) (prefixPartial 12 5718) = false := by
  decide +kernel

theorem node_context_12_5718_81327 : EJMOriginalGlobalDAGData.nodes 9 ⟨81327, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨81227, by decide⟩,⟨81276, by decide⟩,⟨81326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5718_81327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5718 ⟨81327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5718
    ⟨81327, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨81227, by decide⟩,⟨81276, by decide⟩,⟨81326, by decide⟩]) unmarked_context_12_5718_81327 node_context_12_5718_81327
  intro a
  fin_cases a
  · exact context_13_22872_3444
  · exact context_13_22873_81227
  · exact context_13_22874_81276
  · exact context_13_22875_81326

theorem selected_cut_02560 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22876) = some ⟨13, 1, 0, 3444, 22876, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22876_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22876 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22876 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22876, 1, 16384⟩
    (by decide) selected_cut_02560

theorem selected_cut_02561 : selected 8 ⟨81388, by decide⟩
    (prefixPartial 13 22877) = some ⟨13, 2, 0, 81388, 22877, 3545, 16384⟩ := by
  decide +kernel

theorem context_13_22877_81388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22877 ⟨81388, by decide⟩ :=
  accepted_of_selected 13 22877 ⟨81388, by decide⟩ ⟨13, 2, 0, 81388, 22877, 3545, 16384⟩
    (by decide) selected_cut_02561

theorem selected_cut_02562 : selected 8 ⟨81474, by decide⟩
    (prefixPartial 13 22878) = some ⟨13, 2, 0, 81474, 22878, 3949, 16384⟩ := by
  decide +kernel

theorem context_13_22878_81474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22878 ⟨81474, by decide⟩ :=
  accepted_of_selected 13 22878 ⟨81474, by decide⟩ ⟨13, 2, 0, 81474, 22878, 3949, 16384⟩
    (by decide) selected_cut_02562

theorem selected_cut_02563 : selected 8 ⟨81507, by decide⟩
    (prefixPartial 13 22879) = some ⟨13, 2, 0, 81507, 22879, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_22879_81507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22879 ⟨81507, by decide⟩ :=
  accepted_of_selected 13 22879 ⟨81507, by decide⟩ ⟨13, 2, 0, 81507, 22879, 1597, 16384⟩
    (by decide) selected_cut_02563

theorem unmarked_context_12_5719_81508 : frontier 9 ⟨81508, by decide⟩
    (prefixCache 12 5719) (prefixPartial 12 5719) = false := by
  decide +kernel

theorem node_context_12_5719_81508 : EJMOriginalGlobalDAGData.nodes 9 ⟨81508, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨81388, by decide⟩,⟨81474, by decide⟩,⟨81507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5719_81508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5719 ⟨81508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5719
    ⟨81508, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨81388, by decide⟩,⟨81474, by decide⟩,⟨81507, by decide⟩]) unmarked_context_12_5719_81508 node_context_12_5719_81508
  intro a
  fin_cases a
  · exact context_13_22876_3444
  · exact context_13_22877_81388
  · exact context_13_22878_81474
  · exact context_13_22879_81507

theorem unmarked_context_11_1429_81509 : frontier 10 ⟨81509, by decide⟩
    (prefixCache 11 1429) (prefixPartial 11 1429) = false := by
  decide +kernel

theorem node_context_11_1429_81509 : EJMOriginalGlobalDAGData.nodes 10 ⟨81509, by decide⟩ =
    .split (coordinate 11) (![⟨81054, by decide⟩,⟨81178, by decide⟩,⟨81327, by decide⟩,⟨81508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1429_81509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1429 ⟨81509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1429
    ⟨81509, by decide⟩ (by decide) (![⟨81054, by decide⟩,⟨81178, by decide⟩,⟨81327, by decide⟩,⟨81508, by decide⟩]) unmarked_context_11_1429_81509 node_context_11_1429_81509
  intro a
  fin_cases a
  · exact context_12_5716_81054
  · exact context_12_5717_81178
  · exact context_12_5718_81327
  · exact context_12_5719_81508

theorem selected_cut_02564 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22880) = some ⟨13, 1, 0, 3444, 22880, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22880_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22880 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22880 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22880, 1, 16384⟩
    (by decide) selected_cut_02564

theorem selected_cut_02565 : selected 8 ⟨81523, by decide⟩
    (prefixPartial 13 22881) = some ⟨13, 2, 0, 81523, 22881, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_22881_81523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22881 ⟨81523, by decide⟩ :=
  accepted_of_selected 13 22881 ⟨81523, by decide⟩ ⟨13, 2, 0, 81523, 22881, 1481, 16384⟩
    (by decide) selected_cut_02565

theorem selected_cut_02566 : selected 8 ⟨81547, by decide⟩
    (prefixPartial 13 22882) = some ⟨13, 2, 0, 81547, 22882, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_22882_81547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22882 ⟨81547, by decide⟩ :=
  accepted_of_selected 13 22882 ⟨81547, by decide⟩ ⟨13, 2, 0, 81547, 22882, 2057, 16384⟩
    (by decide) selected_cut_02566

theorem selected_cut_02567 : selected 8 ⟨81560, by decide⟩
    (prefixPartial 13 22883) = some ⟨13, 2, 0, 81560, 22883, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_22883_81560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22883 ⟨81560, by decide⟩ :=
  accepted_of_selected 13 22883 ⟨81560, by decide⟩ ⟨13, 2, 0, 81560, 22883, 1029, 16384⟩
    (by decide) selected_cut_02567

theorem unmarked_context_12_5720_81561 : frontier 9 ⟨81561, by decide⟩
    (prefixCache 12 5720) (prefixPartial 12 5720) = false := by
  decide +kernel

theorem node_context_12_5720_81561 : EJMOriginalGlobalDAGData.nodes 9 ⟨81561, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨81523, by decide⟩,⟨81547, by decide⟩,⟨81560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5720_81561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5720 ⟨81561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5720
    ⟨81561, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨81523, by decide⟩,⟨81547, by decide⟩,⟨81560, by decide⟩]) unmarked_context_12_5720_81561 node_context_12_5720_81561
  intro a
  fin_cases a
  · exact context_13_22880_3444
  · exact context_13_22881_81523
  · exact context_13_22882_81547
  · exact context_13_22883_81560

theorem selected_cut_02568 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22884) = some ⟨13, 1, 0, 3444, 22884, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22884_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22884 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22884 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22884, 1, 16384⟩
    (by decide) selected_cut_02568

theorem selected_cut_02569 : selected 8 ⟨81580, by decide⟩
    (prefixPartial 13 22885) = some ⟨13, 2, 0, 81580, 22885, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_22885_81580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22885 ⟨81580, by decide⟩ :=
  accepted_of_selected 13 22885 ⟨81580, by decide⟩ ⟨13, 2, 0, 81580, 22885, 1537, 16384⟩
    (by decide) selected_cut_02569

theorem selected_cut_02570 : selected 8 ⟨81607, by decide⟩
    (prefixPartial 13 22886) = some ⟨13, 2, 0, 81607, 22886, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_22886_81607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22886 ⟨81607, by decide⟩ :=
  accepted_of_selected 13 22886 ⟨81607, by decide⟩ ⟨13, 2, 0, 81607, 22886, 2157, 16384⟩
    (by decide) selected_cut_02570

theorem selected_cut_02571 : selected 8 ⟨81624, by decide⟩
    (prefixPartial 13 22887) = some ⟨13, 2, 0, 81624, 22887, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_22887_81624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22887 ⟨81624, by decide⟩ :=
  accepted_of_selected 13 22887 ⟨81624, by decide⟩ ⟨13, 2, 0, 81624, 22887, 1205, 16384⟩
    (by decide) selected_cut_02571

theorem unmarked_context_12_5721_81625 : frontier 9 ⟨81625, by decide⟩
    (prefixCache 12 5721) (prefixPartial 12 5721) = false := by
  decide +kernel

theorem node_context_12_5721_81625 : EJMOriginalGlobalDAGData.nodes 9 ⟨81625, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨81580, by decide⟩,⟨81607, by decide⟩,⟨81624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5721_81625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5721 ⟨81625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5721
    ⟨81625, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨81580, by decide⟩,⟨81607, by decide⟩,⟨81624, by decide⟩]) unmarked_context_12_5721_81625 node_context_12_5721_81625
  intro a
  fin_cases a
  · exact context_13_22884_3444
  · exact context_13_22885_81580
  · exact context_13_22886_81607
  · exact context_13_22887_81624

theorem selected_cut_02572 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22888) = some ⟨13, 1, 0, 3444, 22888, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22888_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22888 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22888 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22888, 1, 16384⟩
    (by decide) selected_cut_02572

theorem selected_cut_02573 : selected 8 ⟨81663, by decide⟩
    (prefixPartial 13 22889) = some ⟨13, 2, 0, 81663, 22889, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_22889_81663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22889 ⟨81663, by decide⟩ :=
  accepted_of_selected 13 22889 ⟨81663, by decide⟩ ⟨13, 2, 0, 81663, 22889, 2657, 16384⟩
    (by decide) selected_cut_02573

theorem selected_cut_02574 : selected 8 ⟨81716, by decide⟩
    (prefixPartial 13 22890) = some ⟨13, 2, 0, 81716, 22890, 3441, 16384⟩ := by
  decide +kernel

theorem context_13_22890_81716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22890 ⟨81716, by decide⟩ :=
  accepted_of_selected 13 22890 ⟨81716, by decide⟩ ⟨13, 2, 0, 81716, 22890, 3441, 16384⟩
    (by decide) selected_cut_02574

theorem selected_cut_02575 : selected 8 ⟨81753, by decide⟩
    (prefixPartial 13 22891) = some ⟨13, 2, 0, 81753, 22891, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_22891_81753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22891 ⟨81753, by decide⟩ :=
  accepted_of_selected 13 22891 ⟨81753, by decide⟩ ⟨13, 2, 0, 81753, 22891, 1853, 16384⟩
    (by decide) selected_cut_02575

theorem unmarked_context_12_5722_81754 : frontier 9 ⟨81754, by decide⟩
    (prefixCache 12 5722) (prefixPartial 12 5722) = false := by
  decide +kernel

theorem node_context_12_5722_81754 : EJMOriginalGlobalDAGData.nodes 9 ⟨81754, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨81663, by decide⟩,⟨81716, by decide⟩,⟨81753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5722_81754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5722 ⟨81754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5722
    ⟨81754, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨81663, by decide⟩,⟨81716, by decide⟩,⟨81753, by decide⟩]) unmarked_context_12_5722_81754 node_context_12_5722_81754
  intro a
  fin_cases a
  · exact context_13_22888_3444
  · exact context_13_22889_81663
  · exact context_13_22890_81716
  · exact context_13_22891_81753

theorem selected_cut_02576 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22892) = some ⟨13, 1, 0, 3444, 22892, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22892_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22892 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22892 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22892, 1, 16384⟩
    (by decide) selected_cut_02576

theorem selected_cut_02577 : selected 8 ⟨81775, by decide⟩
    (prefixPartial 13 22893) = some ⟨13, 2, 0, 81775, 22893, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_22893_81775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22893 ⟨81775, by decide⟩ :=
  accepted_of_selected 13 22893 ⟨81775, by decide⟩ ⟨13, 2, 0, 81775, 22893, 1769, 16384⟩
    (by decide) selected_cut_02577

theorem selected_cut_02578 : selected 8 ⟨81804, by decide⟩
    (prefixPartial 13 22894) = some ⟨13, 2, 0, 81804, 22894, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_22894_81804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22894 ⟨81804, by decide⟩ :=
  accepted_of_selected 13 22894 ⟨81804, by decide⟩ ⟨13, 2, 0, 81804, 22894, 2365, 16384⟩
    (by decide) selected_cut_02578

theorem selected_cut_02579 : selected 8 ⟨81815, by decide⟩
    (prefixPartial 13 22895) = some ⟨13, 2, 0, 81815, 22895, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_22895_81815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22895 ⟨81815, by decide⟩ :=
  accepted_of_selected 13 22895 ⟨81815, by decide⟩ ⟨13, 2, 0, 81815, 22895, 1085, 16384⟩
    (by decide) selected_cut_02579

theorem unmarked_context_12_5723_81816 : frontier 9 ⟨81816, by decide⟩
    (prefixCache 12 5723) (prefixPartial 12 5723) = false := by
  decide +kernel

theorem node_context_12_5723_81816 : EJMOriginalGlobalDAGData.nodes 9 ⟨81816, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨81775, by decide⟩,⟨81804, by decide⟩,⟨81815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5723_81816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5723 ⟨81816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5723
    ⟨81816, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨81775, by decide⟩,⟨81804, by decide⟩,⟨81815, by decide⟩]) unmarked_context_12_5723_81816 node_context_12_5723_81816
  intro a
  fin_cases a
  · exact context_13_22892_3444
  · exact context_13_22893_81775
  · exact context_13_22894_81804
  · exact context_13_22895_81815

theorem unmarked_context_11_1430_81817 : frontier 10 ⟨81817, by decide⟩
    (prefixCache 11 1430) (prefixPartial 11 1430) = false := by
  decide +kernel

theorem node_context_11_1430_81817 : EJMOriginalGlobalDAGData.nodes 10 ⟨81817, by decide⟩ =
    .split (coordinate 11) (![⟨81561, by decide⟩,⟨81625, by decide⟩,⟨81754, by decide⟩,⟨81816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1430_81817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1430 ⟨81817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1430
    ⟨81817, by decide⟩ (by decide) (![⟨81561, by decide⟩,⟨81625, by decide⟩,⟨81754, by decide⟩,⟨81816, by decide⟩]) unmarked_context_11_1430_81817 node_context_11_1430_81817
  intro a
  fin_cases a
  · exact context_12_5720_81561
  · exact context_12_5721_81625
  · exact context_12_5722_81754
  · exact context_12_5723_81816

theorem selected_cut_02580 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22896) = some ⟨13, 1, 0, 3444, 22896, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22896_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22896 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22896 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22896, 1, 16384⟩
    (by decide) selected_cut_02580

theorem selected_cut_02581 : selected 8 ⟨81833, by decide⟩
    (prefixPartial 13 22897) = some ⟨13, 2, 0, 81833, 22897, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_22897_81833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22897 ⟨81833, by decide⟩ :=
  accepted_of_selected 13 22897 ⟨81833, by decide⟩ ⟨13, 2, 0, 81833, 22897, 1469, 16384⟩
    (by decide) selected_cut_02581

theorem selected_cut_02582 : selected 8 ⟨81860, by decide⟩
    (prefixPartial 13 22898) = some ⟨13, 2, 0, 81860, 22898, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_22898_81860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22898 ⟨81860, by decide⟩ :=
  accepted_of_selected 13 22898 ⟨81860, by decide⟩ ⟨13, 2, 0, 81860, 22898, 2285, 16384⟩
    (by decide) selected_cut_02582

theorem selected_cut_02583 : selected 8 ⟨81870, by decide⟩
    (prefixPartial 13 22899) = some ⟨13, 2, 0, 81870, 22899, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_22899_81870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22899 ⟨81870, by decide⟩ :=
  accepted_of_selected 13 22899 ⟨81870, by decide⟩ ⟨13, 2, 0, 81870, 22899, 1141, 16384⟩
    (by decide) selected_cut_02583

theorem unmarked_context_12_5724_81871 : frontier 9 ⟨81871, by decide⟩
    (prefixCache 12 5724) (prefixPartial 12 5724) = false := by
  decide +kernel

theorem node_context_12_5724_81871 : EJMOriginalGlobalDAGData.nodes 9 ⟨81871, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨81833, by decide⟩,⟨81860, by decide⟩,⟨81870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5724_81871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5724 ⟨81871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5724
    ⟨81871, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨81833, by decide⟩,⟨81860, by decide⟩,⟨81870, by decide⟩]) unmarked_context_12_5724_81871 node_context_12_5724_81871
  intro a
  fin_cases a
  · exact context_13_22896_3444
  · exact context_13_22897_81833
  · exact context_13_22898_81860
  · exact context_13_22899_81870

theorem selected_cut_02584 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22900) = some ⟨13, 1, 0, 3444, 22900, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22900_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22900 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22900 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22900, 1, 16384⟩
    (by decide) selected_cut_02584

theorem selected_cut_02585 : selected 8 ⟨81887, by decide⟩
    (prefixPartial 13 22901) = some ⟨13, 2, 0, 81887, 22901, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_22901_81887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22901 ⟨81887, by decide⟩ :=
  accepted_of_selected 13 22901 ⟨81887, by decide⟩ ⟨13, 2, 0, 81887, 22901, 1505, 16384⟩
    (by decide) selected_cut_02585

theorem selected_cut_02586 : selected 8 ⟨81919, by decide⟩
    (prefixPartial 13 22902) = some ⟨13, 2, 0, 81919, 22902, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_22902_81919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22902 ⟨81919, by decide⟩ :=
  accepted_of_selected 13 22902 ⟨81919, by decide⟩ ⟨13, 2, 0, 81919, 22902, 2437, 16384⟩
    (by decide) selected_cut_02586

theorem selected_cut_02587 : selected 8 ⟨81936, by decide⟩
    (prefixPartial 13 22903) = some ⟨13, 2, 0, 81936, 22903, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_22903_81936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22903 ⟨81936, by decide⟩ :=
  accepted_of_selected 13 22903 ⟨81936, by decide⟩ ⟨13, 2, 0, 81936, 22903, 1221, 16384⟩
    (by decide) selected_cut_02587

theorem unmarked_context_12_5725_81937 : frontier 9 ⟨81937, by decide⟩
    (prefixCache 12 5725) (prefixPartial 12 5725) = false := by
  decide +kernel

theorem node_context_12_5725_81937 : EJMOriginalGlobalDAGData.nodes 9 ⟨81937, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨81887, by decide⟩,⟨81919, by decide⟩,⟨81936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5725_81937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5725 ⟨81937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5725
    ⟨81937, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨81887, by decide⟩,⟨81919, by decide⟩,⟨81936, by decide⟩]) unmarked_context_12_5725_81937 node_context_12_5725_81937
  intro a
  fin_cases a
  · exact context_13_22900_3444
  · exact context_13_22901_81887
  · exact context_13_22902_81919
  · exact context_13_22903_81936

theorem selected_cut_02588 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22904) = some ⟨13, 1, 0, 3444, 22904, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22904_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22904 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22904 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22904, 1, 16384⟩
    (by decide) selected_cut_02588

theorem selected_cut_02589 : selected 8 ⟨81953, by decide⟩
    (prefixPartial 13 22905) = some ⟨13, 2, 0, 81953, 22905, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_22905_81953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22905 ⟨81953, by decide⟩ :=
  accepted_of_selected 13 22905 ⟨81953, by decide⟩ ⟨13, 2, 0, 81953, 22905, 1677, 16384⟩
    (by decide) selected_cut_02589

theorem selected_cut_02590 : selected 8 ⟨81977, by decide⟩
    (prefixPartial 13 22906) = some ⟨13, 2, 0, 81977, 22906, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_22906_81977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22906 ⟨81977, by decide⟩ :=
  accepted_of_selected 13 22906 ⟨81977, by decide⟩ ⟨13, 2, 0, 81977, 22906, 2185, 16384⟩
    (by decide) selected_cut_02590

theorem selected_cut_02591 : selected 8 ⟨81995, by decide⟩
    (prefixPartial 13 22907) = some ⟨13, 2, 0, 81995, 22907, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_22907_81995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22907 ⟨81995, by decide⟩ :=
  accepted_of_selected 13 22907 ⟨81995, by decide⟩ ⟨13, 2, 0, 81995, 22907, 1281, 16384⟩
    (by decide) selected_cut_02591

theorem unmarked_context_12_5726_81996 : frontier 9 ⟨81996, by decide⟩
    (prefixCache 12 5726) (prefixPartial 12 5726) = false := by
  decide +kernel

theorem node_context_12_5726_81996 : EJMOriginalGlobalDAGData.nodes 9 ⟨81996, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨81953, by decide⟩,⟨81977, by decide⟩,⟨81995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5726_81996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5726 ⟨81996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5726
    ⟨81996, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨81953, by decide⟩,⟨81977, by decide⟩,⟨81995, by decide⟩]) unmarked_context_12_5726_81996 node_context_12_5726_81996
  intro a
  fin_cases a
  · exact context_13_22904_3444
  · exact context_13_22905_81953
  · exact context_13_22906_81977
  · exact context_13_22907_81995

theorem selected_cut_02592 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 22908) = some ⟨13, 1, 0, 3444, 22908, 1, 16384⟩ := by
  decide +kernel

theorem context_13_22908_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22908 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 22908 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 22908, 1, 16384⟩
    (by decide) selected_cut_02592

theorem selected_cut_02593 : selected 8 ⟨82013, by decide⟩
    (prefixPartial 13 22909) = some ⟨13, 2, 0, 82013, 22909, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_22909_82013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22909 ⟨82013, by decide⟩ :=
  accepted_of_selected 13 22909 ⟨82013, by decide⟩ ⟨13, 2, 0, 82013, 22909, 1637, 16384⟩
    (by decide) selected_cut_02593

theorem selected_cut_02594 : selected 8 ⟨82039, by decide⟩
    (prefixPartial 13 22910) = some ⟨13, 2, 0, 82039, 22910, 2465, 16384⟩ := by
  decide +kernel

theorem context_13_22910_82039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22910 ⟨82039, by decide⟩ :=
  accepted_of_selected 13 22910 ⟨82039, by decide⟩ ⟨13, 2, 0, 82039, 22910, 2465, 16384⟩
    (by decide) selected_cut_02594

theorem selected_cut_02595 : selected 8 ⟨82051, by decide⟩
    (prefixPartial 13 22911) = some ⟨13, 2, 0, 82051, 22911, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_22911_82051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22911 ⟨82051, by decide⟩ :=
  accepted_of_selected 13 22911 ⟨82051, by decide⟩ ⟨13, 2, 0, 82051, 22911, 1169, 16384⟩
    (by decide) selected_cut_02595

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
