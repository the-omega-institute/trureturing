/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover080
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_07779 : selected 8 ⟨222682, by decide⟩
    (prefixPartial 13 90567) = some ⟨13, 2, 0, 222682, 90567, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_90567_222682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90567 ⟨222682, by decide⟩ :=
  accepted_of_selected 13 90567 ⟨222682, by decide⟩ ⟨13, 2, 0, 222682, 90567, 1121, 16384⟩
    (by decide) selected_cut_07779

theorem unmarked_context_12_22641_222683 : frontier 9 ⟨222683, by decide⟩
    (prefixCache 12 22641) (prefixPartial 12 22641) = false := by
  decide +kernel

theorem node_context_12_22641_222683 : EJMOriginalGlobalDAGData.nodes 9 ⟨222683, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨222643, by decide⟩,⟨222670, by decide⟩,⟨222682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22641_222683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22641 ⟨222683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22641
    ⟨222683, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨222643, by decide⟩,⟨222670, by decide⟩,⟨222682, by decide⟩]) unmarked_context_12_22641_222683 node_context_12_22641_222683
  intro a
  fin_cases a
  · exact context_13_90564_3444
  · exact context_13_90565_222643
  · exact context_13_90566_222670
  · exact context_13_90567_222682

theorem selected_cut_07780 : selected 9 ⟨222722, by decide⟩
    (prefixPartial 12 22642) = some ⟨12, 2, 0, 222722, 22642, 3381, 65536⟩ := by
  decide +kernel

theorem context_12_22642_222722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22642 ⟨222722, by decide⟩ :=
  accepted_of_selected 12 22642 ⟨222722, by decide⟩ ⟨12, 2, 0, 222722, 22642, 3381, 65536⟩
    (by decide) selected_cut_07780

theorem selected_cut_07781 : selected 9 ⟨222765, by decide⟩
    (prefixPartial 12 22643) = some ⟨12, 2, 0, 222765, 22643, 3701, 65536⟩ := by
  decide +kernel

theorem context_12_22643_222765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22643 ⟨222765, by decide⟩ :=
  accepted_of_selected 12 22643 ⟨222765, by decide⟩ ⟨12, 2, 0, 222765, 22643, 3701, 65536⟩
    (by decide) selected_cut_07781

theorem unmarked_context_11_5660_222766 : frontier 10 ⟨222766, by decide⟩
    (prefixCache 11 5660) (prefixPartial 11 5660) = false := by
  decide +kernel

theorem node_context_11_5660_222766 : EJMOriginalGlobalDAGData.nodes 10 ⟨222766, by decide⟩ =
    .split (coordinate 11) (![⟨222630, by decide⟩,⟨222683, by decide⟩,⟨222722, by decide⟩,⟨222765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5660_222766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5660 ⟨222766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5660
    ⟨222766, by decide⟩ (by decide) (![⟨222630, by decide⟩,⟨222683, by decide⟩,⟨222722, by decide⟩,⟨222765, by decide⟩]) unmarked_context_11_5660_222766 node_context_11_5660_222766
  intro a
  fin_cases a
  · exact context_12_22640_222630
  · exact context_12_22641_222683
  · exact context_12_22642_222722
  · exact context_12_22643_222765

theorem selected_cut_07782 : selected 9 ⟨222806, by decide⟩
    (prefixPartial 12 22644) = some ⟨12, 2, 0, 222806, 22644, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_22644_222806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22644 ⟨222806, by decide⟩ :=
  accepted_of_selected 12 22644 ⟨222806, by decide⟩ ⟨12, 2, 0, 222806, 22644, 3217, 65536⟩
    (by decide) selected_cut_07782

theorem selected_cut_07783 : selected 9 ⟨222858, by decide⟩
    (prefixPartial 12 22645) = some ⟨12, 2, 0, 222858, 22645, 3977, 65536⟩ := by
  decide +kernel

theorem context_12_22645_222858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22645 ⟨222858, by decide⟩ :=
  accepted_of_selected 12 22645 ⟨222858, by decide⟩ ⟨12, 2, 0, 222858, 22645, 3977, 65536⟩
    (by decide) selected_cut_07783

theorem selected_cut_07784 : selected 9 ⟨222896, by decide⟩
    (prefixPartial 12 22646) = some ⟨12, 2, 0, 222896, 22646, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_22646_222896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22646 ⟨222896, by decide⟩ :=
  accepted_of_selected 12 22646 ⟨222896, by decide⟩ ⟨12, 2, 0, 222896, 22646, 3357, 65536⟩
    (by decide) selected_cut_07784

theorem selected_cut_07785 : selected 9 ⟨222942, by decide⟩
    (prefixPartial 12 22647) = some ⟨12, 2, 0, 222942, 22647, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_22647_222942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22647 ⟨222942, by decide⟩ :=
  accepted_of_selected 12 22647 ⟨222942, by decide⟩ ⟨12, 2, 0, 222942, 22647, 3633, 65536⟩
    (by decide) selected_cut_07785

theorem unmarked_context_11_5661_222943 : frontier 10 ⟨222943, by decide⟩
    (prefixCache 11 5661) (prefixPartial 11 5661) = false := by
  decide +kernel

theorem node_context_11_5661_222943 : EJMOriginalGlobalDAGData.nodes 10 ⟨222943, by decide⟩ =
    .split (coordinate 11) (![⟨222806, by decide⟩,⟨222858, by decide⟩,⟨222896, by decide⟩,⟨222942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5661_222943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5661 ⟨222943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5661
    ⟨222943, by decide⟩ (by decide) (![⟨222806, by decide⟩,⟨222858, by decide⟩,⟨222896, by decide⟩,⟨222942, by decide⟩]) unmarked_context_11_5661_222943 node_context_11_5661_222943
  intro a
  fin_cases a
  · exact context_12_22644_222806
  · exact context_12_22645_222858
  · exact context_12_22646_222896
  · exact context_12_22647_222942

theorem selected_cut_07786 : selected 9 ⟨222982, by decide⟩
    (prefixPartial 12 22648) = some ⟨12, 2, 0, 222982, 22648, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_22648_222982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22648 ⟨222982, by decide⟩ :=
  accepted_of_selected 12 22648 ⟨222982, by decide⟩ ⟨12, 2, 0, 222982, 22648, 3449, 65536⟩
    (by decide) selected_cut_07786

theorem selected_cut_07787 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90596) = some ⟨13, 1, 0, 3444, 90596, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90596_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90596 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90596 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90596, 1, 16384⟩
    (by decide) selected_cut_07787

theorem selected_cut_07788 : selected 8 ⟨222990, by decide⟩
    (prefixPartial 13 90597) = some ⟨13, 2, 0, 222990, 90597, 433, 16384⟩ := by
  decide +kernel

theorem context_13_90597_222990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90597 ⟨222990, by decide⟩ :=
  accepted_of_selected 13 90597 ⟨222990, by decide⟩ ⟨13, 2, 0, 222990, 90597, 433, 16384⟩
    (by decide) selected_cut_07788

theorem selected_cut_07789 : selected 8 ⟨223021, by decide⟩
    (prefixPartial 13 90598) = some ⟨13, 2, 0, 223021, 90598, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_90598_223021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90598 ⟨223021, by decide⟩ :=
  accepted_of_selected 13 90598 ⟨223021, by decide⟩ ⟨13, 2, 0, 223021, 90598, 2605, 16384⟩
    (by decide) selected_cut_07789

theorem selected_cut_07790 : selected 8 ⟨223036, by decide⟩
    (prefixPartial 13 90599) = some ⟨13, 2, 0, 223036, 90599, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_90599_223036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90599 ⟨223036, by decide⟩ :=
  accepted_of_selected 13 90599 ⟨223036, by decide⟩ ⟨13, 2, 0, 223036, 90599, 1297, 16384⟩
    (by decide) selected_cut_07790

theorem unmarked_context_12_22649_223037 : frontier 9 ⟨223037, by decide⟩
    (prefixCache 12 22649) (prefixPartial 12 22649) = false := by
  decide +kernel

theorem node_context_12_22649_223037 : EJMOriginalGlobalDAGData.nodes 9 ⟨223037, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨222990, by decide⟩,⟨223021, by decide⟩,⟨223036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22649_223037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22649 ⟨223037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22649
    ⟨223037, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨222990, by decide⟩,⟨223021, by decide⟩,⟨223036, by decide⟩]) unmarked_context_12_22649_223037 node_context_12_22649_223037
  intro a
  fin_cases a
  · exact context_13_90596_3444
  · exact context_13_90597_222990
  · exact context_13_90598_223021
  · exact context_13_90599_223036

theorem selected_cut_07791 : selected 9 ⟨223084, by decide⟩
    (prefixPartial 12 22650) = some ⟨12, 2, 0, 223084, 22650, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_22650_223084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22650 ⟨223084, by decide⟩ :=
  accepted_of_selected 12 22650 ⟨223084, by decide⟩ ⟨12, 2, 0, 223084, 22650, 3373, 65536⟩
    (by decide) selected_cut_07791

theorem selected_cut_07792 : selected 9 ⟨223134, by decide⟩
    (prefixPartial 12 22651) = some ⟨12, 2, 0, 223134, 22651, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_22651_223134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22651 ⟨223134, by decide⟩ :=
  accepted_of_selected 12 22651 ⟨223134, by decide⟩ ⟨12, 2, 0, 223134, 22651, 3881, 65536⟩
    (by decide) selected_cut_07792

theorem unmarked_context_11_5662_223135 : frontier 10 ⟨223135, by decide⟩
    (prefixCache 11 5662) (prefixPartial 11 5662) = false := by
  decide +kernel

theorem node_context_11_5662_223135 : EJMOriginalGlobalDAGData.nodes 10 ⟨223135, by decide⟩ =
    .split (coordinate 11) (![⟨222982, by decide⟩,⟨223037, by decide⟩,⟨223084, by decide⟩,⟨223134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5662_223135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5662 ⟨223135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5662
    ⟨223135, by decide⟩ (by decide) (![⟨222982, by decide⟩,⟨223037, by decide⟩,⟨223084, by decide⟩,⟨223134, by decide⟩]) unmarked_context_11_5662_223135 node_context_11_5662_223135
  intro a
  fin_cases a
  · exact context_12_22648_222982
  · exact context_12_22649_223037
  · exact context_12_22650_223084
  · exact context_12_22651_223134

theorem selected_cut_07793 : selected 9 ⟨223166, by decide⟩
    (prefixPartial 12 22652) = some ⟨12, 2, 0, 223166, 22652, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_22652_223166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22652 ⟨223166, by decide⟩ :=
  accepted_of_selected 12 22652 ⟨223166, by decide⟩ ⟨12, 2, 0, 223166, 22652, 2829, 65536⟩
    (by decide) selected_cut_07793

theorem selected_cut_07794 : selected 9 ⟨223219, by decide⟩
    (prefixPartial 12 22653) = some ⟨12, 2, 0, 223219, 22653, 3689, 65536⟩ := by
  decide +kernel

theorem context_12_22653_223219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22653 ⟨223219, by decide⟩ :=
  accepted_of_selected 12 22653 ⟨223219, by decide⟩ ⟨12, 2, 0, 223219, 22653, 3689, 65536⟩
    (by decide) selected_cut_07794

theorem selected_cut_07795 : selected 9 ⟨223259, by decide⟩
    (prefixPartial 12 22654) = some ⟨12, 2, 0, 223259, 22654, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_22654_223259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22654 ⟨223259, by decide⟩ :=
  accepted_of_selected 12 22654 ⟨223259, by decide⟩ ⟨12, 2, 0, 223259, 22654, 3057, 65536⟩
    (by decide) selected_cut_07795

theorem selected_cut_07796 : selected 9 ⟨223298, by decide⟩
    (prefixPartial 12 22655) = some ⟨12, 2, 0, 223298, 22655, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_22655_223298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22655 ⟨223298, by decide⟩ :=
  accepted_of_selected 12 22655 ⟨223298, by decide⟩ ⟨12, 2, 0, 223298, 22655, 3069, 65536⟩
    (by decide) selected_cut_07796

theorem unmarked_context_11_5663_223299 : frontier 10 ⟨223299, by decide⟩
    (prefixCache 11 5663) (prefixPartial 11 5663) = false := by
  decide +kernel

theorem node_context_11_5663_223299 : EJMOriginalGlobalDAGData.nodes 10 ⟨223299, by decide⟩ =
    .split (coordinate 11) (![⟨223166, by decide⟩,⟨223219, by decide⟩,⟨223259, by decide⟩,⟨223298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5663_223299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5663 ⟨223299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5663
    ⟨223299, by decide⟩ (by decide) (![⟨223166, by decide⟩,⟨223219, by decide⟩,⟨223259, by decide⟩,⟨223298, by decide⟩]) unmarked_context_11_5663_223299 node_context_11_5663_223299
  intro a
  fin_cases a
  · exact context_12_22652_223166
  · exact context_12_22653_223219
  · exact context_12_22654_223259
  · exact context_12_22655_223298

theorem unmarked_context_10_1415_223300 : frontier 11 ⟨223300, by decide⟩
    (prefixCache 10 1415) (prefixPartial 10 1415) = false := by
  decide +kernel

theorem node_context_10_1415_223300 : EJMOriginalGlobalDAGData.nodes 11 ⟨223300, by decide⟩ =
    .split (coordinate 10) (![⟨222766, by decide⟩,⟨222943, by decide⟩,⟨223135, by decide⟩,⟨223299, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1415_223300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1415 ⟨223300, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1415
    ⟨223300, by decide⟩ (by decide) (![⟨222766, by decide⟩,⟨222943, by decide⟩,⟨223135, by decide⟩,⟨223299, by decide⟩]) unmarked_context_10_1415_223300 node_context_10_1415_223300
  intro a
  fin_cases a
  · exact context_11_5660_222766
  · exact context_11_5661_222943
  · exact context_11_5662_223135
  · exact context_11_5663_223299

theorem unmarked_context_9_353_223301 : frontier 12 ⟨223301, by decide⟩
    (prefixCache 9 353) (prefixPartial 9 353) = false := by
  decide +kernel

theorem node_context_9_353_223301 : EJMOriginalGlobalDAGData.nodes 12 ⟨223301, by decide⟩ =
    .split (coordinate 9) (![⟨220519, by decide⟩,⟨221500, by decide⟩,⟨222543, by decide⟩,⟨223300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_353_223301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 353 ⟨223301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 353
    ⟨223301, by decide⟩ (by decide) (![⟨220519, by decide⟩,⟨221500, by decide⟩,⟨222543, by decide⟩,⟨223300, by decide⟩]) unmarked_context_9_353_223301 node_context_9_353_223301
  intro a
  fin_cases a
  · exact context_10_1412_220519
  · exact context_10_1413_221500
  · exact context_10_1414_222543
  · exact context_10_1415_223300

theorem selected_cut_07797 : selected 9 ⟨223376, by decide⟩
    (prefixPartial 12 22656) = some ⟨12, 2, 0, 223376, 22656, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_22656_223376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22656 ⟨223376, by decide⟩ :=
  accepted_of_selected 12 22656 ⟨223376, by decide⟩ ⟨12, 2, 0, 223376, 22656, 1109, 65536⟩
    (by decide) selected_cut_07797

theorem selected_cut_07798 : selected 9 ⟨223404, by decide⟩
    (prefixPartial 12 22657) = some ⟨12, 2, 0, 223404, 22657, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_22657_223404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22657 ⟨223404, by decide⟩ :=
  accepted_of_selected 12 22657 ⟨223404, by decide⟩ ⟨12, 2, 0, 223404, 22657, 2265, 65536⟩
    (by decide) selected_cut_07798

theorem selected_cut_07799 : selected 9 ⟨223430, by decide⟩
    (prefixPartial 12 22658) = some ⟨12, 2, 0, 223430, 22658, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_22658_223430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22658 ⟨223430, by decide⟩ :=
  accepted_of_selected 12 22658 ⟨223430, by decide⟩ ⟨12, 2, 0, 223430, 22658, 2221, 65536⟩
    (by decide) selected_cut_07799

theorem selected_cut_07800 : selected 9 ⟨223451, by decide⟩
    (prefixPartial 12 22659) = some ⟨12, 2, 0, 223451, 22659, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_22659_223451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22659 ⟨223451, by decide⟩ :=
  accepted_of_selected 12 22659 ⟨223451, by decide⟩ ⟨12, 2, 0, 223451, 22659, 2101, 65536⟩
    (by decide) selected_cut_07800

theorem unmarked_context_11_5664_223452 : frontier 10 ⟨223452, by decide⟩
    (prefixCache 11 5664) (prefixPartial 11 5664) = false := by
  decide +kernel

theorem node_context_11_5664_223452 : EJMOriginalGlobalDAGData.nodes 10 ⟨223452, by decide⟩ =
    .split (coordinate 11) (![⟨223376, by decide⟩,⟨223404, by decide⟩,⟨223430, by decide⟩,⟨223451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5664_223452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5664 ⟨223452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5664
    ⟨223452, by decide⟩ (by decide) (![⟨223376, by decide⟩,⟨223404, by decide⟩,⟨223430, by decide⟩,⟨223451, by decide⟩]) unmarked_context_11_5664_223452 node_context_11_5664_223452
  intro a
  fin_cases a
  · exact context_12_22656_223376
  · exact context_12_22657_223404
  · exact context_12_22658_223430
  · exact context_12_22659_223451

theorem selected_cut_07801 : selected 9 ⟨223482, by decide⟩
    (prefixPartial 12 22660) = some ⟨12, 2, 0, 223482, 22660, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_22660_223482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22660 ⟨223482, by decide⟩ :=
  accepted_of_selected 12 22660 ⟨223482, by decide⟩ ⟨12, 2, 0, 223482, 22660, 2269, 65536⟩
    (by decide) selected_cut_07801

theorem selected_cut_07802 : selected 9 ⟨223516, by decide⟩
    (prefixPartial 12 22661) = some ⟨12, 2, 0, 223516, 22661, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_22661_223516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22661 ⟨223516, by decide⟩ :=
  accepted_of_selected 12 22661 ⟨223516, by decide⟩ ⟨12, 2, 0, 223516, 22661, 2193, 65536⟩
    (by decide) selected_cut_07802

theorem selected_cut_07803 : selected 9 ⟨223545, by decide⟩
    (prefixPartial 12 22662) = some ⟨12, 2, 0, 223545, 22662, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_22662_223545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22662 ⟨223545, by decide⟩ :=
  accepted_of_selected 12 22662 ⟨223545, by decide⟩ ⟨12, 2, 0, 223545, 22662, 2161, 65536⟩
    (by decide) selected_cut_07803

theorem selected_cut_07804 : selected 9 ⟨223567, by decide⟩
    (prefixPartial 12 22663) = some ⟨12, 2, 0, 223567, 22663, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_22663_223567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22663 ⟨223567, by decide⟩ :=
  accepted_of_selected 12 22663 ⟨223567, by decide⟩ ⟨12, 2, 0, 223567, 22663, 2109, 65536⟩
    (by decide) selected_cut_07804

theorem unmarked_context_11_5665_223568 : frontier 10 ⟨223568, by decide⟩
    (prefixCache 11 5665) (prefixPartial 11 5665) = false := by
  decide +kernel

theorem node_context_11_5665_223568 : EJMOriginalGlobalDAGData.nodes 10 ⟨223568, by decide⟩ =
    .split (coordinate 11) (![⟨223482, by decide⟩,⟨223516, by decide⟩,⟨223545, by decide⟩,⟨223567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5665_223568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5665 ⟨223568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5665
    ⟨223568, by decide⟩ (by decide) (![⟨223482, by decide⟩,⟨223516, by decide⟩,⟨223545, by decide⟩,⟨223567, by decide⟩]) unmarked_context_11_5665_223568 node_context_11_5665_223568
  intro a
  fin_cases a
  · exact context_12_22660_223482
  · exact context_12_22661_223516
  · exact context_12_22662_223545
  · exact context_12_22663_223567

theorem selected_cut_07805 : selected 9 ⟨223594, by decide⟩
    (prefixPartial 12 22664) = some ⟨12, 2, 0, 223594, 22664, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_22664_223594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22664 ⟨223594, by decide⟩ :=
  accepted_of_selected 12 22664 ⟨223594, by decide⟩ ⟨12, 2, 0, 223594, 22664, 2209, 65536⟩
    (by decide) selected_cut_07805

theorem selected_cut_07806 : selected 9 ⟨223627, by decide⟩
    (prefixPartial 12 22665) = some ⟨12, 2, 0, 223627, 22665, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_22665_223627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22665 ⟨223627, by decide⟩ :=
  accepted_of_selected 12 22665 ⟨223627, by decide⟩ ⟨12, 2, 0, 223627, 22665, 2241, 65536⟩
    (by decide) selected_cut_07806

theorem selected_cut_07807 : selected 9 ⟨223652, by decide⟩
    (prefixPartial 12 22666) = some ⟨12, 2, 0, 223652, 22666, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_22666_223652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22666 ⟨223652, by decide⟩ :=
  accepted_of_selected 12 22666 ⟨223652, by decide⟩ ⟨12, 2, 0, 223652, 22666, 2077, 65536⟩
    (by decide) selected_cut_07807

theorem selected_cut_07808 : selected 9 ⟨223680, by decide⟩
    (prefixPartial 12 22667) = some ⟨12, 2, 0, 223680, 22667, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_22667_223680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22667 ⟨223680, by decide⟩ :=
  accepted_of_selected 12 22667 ⟨223680, by decide⟩ ⟨12, 2, 0, 223680, 22667, 2081, 65536⟩
    (by decide) selected_cut_07808

theorem unmarked_context_11_5666_223681 : frontier 10 ⟨223681, by decide⟩
    (prefixCache 11 5666) (prefixPartial 11 5666) = false := by
  decide +kernel

theorem node_context_11_5666_223681 : EJMOriginalGlobalDAGData.nodes 10 ⟨223681, by decide⟩ =
    .split (coordinate 11) (![⟨223594, by decide⟩,⟨223627, by decide⟩,⟨223652, by decide⟩,⟨223680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5666_223681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5666 ⟨223681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5666
    ⟨223681, by decide⟩ (by decide) (![⟨223594, by decide⟩,⟨223627, by decide⟩,⟨223652, by decide⟩,⟨223680, by decide⟩]) unmarked_context_11_5666_223681 node_context_11_5666_223681
  intro a
  fin_cases a
  · exact context_12_22664_223594
  · exact context_12_22665_223627
  · exact context_12_22666_223652
  · exact context_12_22667_223680

theorem selected_cut_07809 : selected 9 ⟨223708, by decide⟩
    (prefixPartial 12 22668) = some ⟨12, 2, 0, 223708, 22668, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_22668_223708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22668 ⟨223708, by decide⟩ :=
  accepted_of_selected 12 22668 ⟨223708, by decide⟩ ⟨12, 2, 0, 223708, 22668, 2041, 65536⟩
    (by decide) selected_cut_07809

theorem selected_cut_07810 : selected 9 ⟨223736, by decide⟩
    (prefixPartial 12 22669) = some ⟨12, 2, 0, 223736, 22669, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_22669_223736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22669 ⟨223736, by decide⟩ :=
  accepted_of_selected 12 22669 ⟨223736, by decide⟩ ⟨12, 2, 0, 223736, 22669, 2041, 65536⟩
    (by decide) selected_cut_07810

theorem selected_cut_07811 : selected 9 ⟨223762, by decide⟩
    (prefixPartial 12 22670) = some ⟨12, 2, 0, 223762, 22670, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_22670_223762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22670 ⟨223762, by decide⟩ :=
  accepted_of_selected 12 22670 ⟨223762, by decide⟩ ⟨12, 2, 0, 223762, 22670, 2041, 65536⟩
    (by decide) selected_cut_07811

theorem selected_cut_07812 : selected 9 ⟨223787, by decide⟩
    (prefixPartial 12 22671) = some ⟨12, 2, 0, 223787, 22671, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_22671_223787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22671 ⟨223787, by decide⟩ :=
  accepted_of_selected 12 22671 ⟨223787, by decide⟩ ⟨12, 2, 0, 223787, 22671, 1873, 65536⟩
    (by decide) selected_cut_07812

theorem unmarked_context_11_5667_223788 : frontier 10 ⟨223788, by decide⟩
    (prefixCache 11 5667) (prefixPartial 11 5667) = false := by
  decide +kernel

theorem node_context_11_5667_223788 : EJMOriginalGlobalDAGData.nodes 10 ⟨223788, by decide⟩ =
    .split (coordinate 11) (![⟨223708, by decide⟩,⟨223736, by decide⟩,⟨223762, by decide⟩,⟨223787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5667_223788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5667 ⟨223788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5667
    ⟨223788, by decide⟩ (by decide) (![⟨223708, by decide⟩,⟨223736, by decide⟩,⟨223762, by decide⟩,⟨223787, by decide⟩]) unmarked_context_11_5667_223788 node_context_11_5667_223788
  intro a
  fin_cases a
  · exact context_12_22668_223708
  · exact context_12_22669_223736
  · exact context_12_22670_223762
  · exact context_12_22671_223787

theorem unmarked_context_10_1416_223789 : frontier 11 ⟨223789, by decide⟩
    (prefixCache 10 1416) (prefixPartial 10 1416) = false := by
  decide +kernel

theorem node_context_10_1416_223789 : EJMOriginalGlobalDAGData.nodes 11 ⟨223789, by decide⟩ =
    .split (coordinate 10) (![⟨223452, by decide⟩,⟨223568, by decide⟩,⟨223681, by decide⟩,⟨223788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1416_223789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1416 ⟨223789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1416
    ⟨223789, by decide⟩ (by decide) (![⟨223452, by decide⟩,⟨223568, by decide⟩,⟨223681, by decide⟩,⟨223788, by decide⟩]) unmarked_context_10_1416_223789 node_context_10_1416_223789
  intro a
  fin_cases a
  · exact context_11_5664_223452
  · exact context_11_5665_223568
  · exact context_11_5666_223681
  · exact context_11_5667_223788

theorem selected_cut_07813 : selected 9 ⟨223835, by decide⟩
    (prefixPartial 12 22672) = some ⟨12, 2, 0, 223835, 22672, 3325, 65536⟩ := by
  decide +kernel

theorem context_12_22672_223835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22672 ⟨223835, by decide⟩ :=
  accepted_of_selected 12 22672 ⟨223835, by decide⟩ ⟨12, 2, 0, 223835, 22672, 3325, 65536⟩
    (by decide) selected_cut_07813

theorem selected_cut_07814 : selected 9 ⟨223862, by decide⟩
    (prefixPartial 12 22673) = some ⟨12, 2, 0, 223862, 22673, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_22673_223862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22673 ⟨223862, by decide⟩ :=
  accepted_of_selected 12 22673 ⟨223862, by decide⟩ ⟨12, 2, 0, 223862, 22673, 2461, 65536⟩
    (by decide) selected_cut_07814

theorem selected_cut_07815 : selected 9 ⟨223889, by decide⟩
    (prefixPartial 12 22674) = some ⟨12, 2, 0, 223889, 22674, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_22674_223889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22674 ⟨223889, by decide⟩ :=
  accepted_of_selected 12 22674 ⟨223889, by decide⟩ ⟨12, 2, 0, 223889, 22674, 2561, 65536⟩
    (by decide) selected_cut_07815

theorem selected_cut_07816 : selected 9 ⟨223912, by decide⟩
    (prefixPartial 12 22675) = some ⟨12, 2, 0, 223912, 22675, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_22675_223912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22675 ⟨223912, by decide⟩ :=
  accepted_of_selected 12 22675 ⟨223912, by decide⟩ ⟨12, 2, 0, 223912, 22675, 2225, 65536⟩
    (by decide) selected_cut_07816

theorem unmarked_context_11_5668_223913 : frontier 10 ⟨223913, by decide⟩
    (prefixCache 11 5668) (prefixPartial 11 5668) = false := by
  decide +kernel

theorem node_context_11_5668_223913 : EJMOriginalGlobalDAGData.nodes 10 ⟨223913, by decide⟩ =
    .split (coordinate 11) (![⟨223835, by decide⟩,⟨223862, by decide⟩,⟨223889, by decide⟩,⟨223912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5668_223913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5668 ⟨223913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5668
    ⟨223913, by decide⟩ (by decide) (![⟨223835, by decide⟩,⟨223862, by decide⟩,⟨223889, by decide⟩,⟨223912, by decide⟩]) unmarked_context_11_5668_223913 node_context_11_5668_223913
  intro a
  fin_cases a
  · exact context_12_22672_223835
  · exact context_12_22673_223862
  · exact context_12_22674_223889
  · exact context_12_22675_223912

theorem selected_cut_07817 : selected 9 ⟨223938, by decide⟩
    (prefixPartial 12 22676) = some ⟨12, 2, 0, 223938, 22676, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_22676_223938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22676 ⟨223938, by decide⟩ :=
  accepted_of_selected 12 22676 ⟨223938, by decide⟩ ⟨12, 2, 0, 223938, 22676, 2177, 65536⟩
    (by decide) selected_cut_07817

theorem selected_cut_07818 : selected 9 ⟨223961, by decide⟩
    (prefixPartial 12 22677) = some ⟨12, 2, 0, 223961, 22677, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_22677_223961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22677 ⟨223961, by decide⟩ :=
  accepted_of_selected 12 22677 ⟨223961, by decide⟩ ⟨12, 2, 0, 223961, 22677, 2201, 65536⟩
    (by decide) selected_cut_07818

theorem selected_cut_07819 : selected 9 ⟨223989, by decide⟩
    (prefixPartial 12 22678) = some ⟨12, 2, 0, 223989, 22678, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_22678_223989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22678 ⟨223989, by decide⟩ :=
  accepted_of_selected 12 22678 ⟨223989, by decide⟩ ⟨12, 2, 0, 223989, 22678, 2277, 65536⟩
    (by decide) selected_cut_07819

theorem selected_cut_07820 : selected 9 ⟨224011, by decide⟩
    (prefixPartial 12 22679) = some ⟨12, 2, 0, 224011, 22679, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_22679_224011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22679 ⟨224011, by decide⟩ :=
  accepted_of_selected 12 22679 ⟨224011, by decide⟩ ⟨12, 2, 0, 224011, 22679, 2125, 65536⟩
    (by decide) selected_cut_07820

theorem unmarked_context_11_5669_224012 : frontier 10 ⟨224012, by decide⟩
    (prefixCache 11 5669) (prefixPartial 11 5669) = false := by
  decide +kernel

theorem node_context_11_5669_224012 : EJMOriginalGlobalDAGData.nodes 10 ⟨224012, by decide⟩ =
    .split (coordinate 11) (![⟨223938, by decide⟩,⟨223961, by decide⟩,⟨223989, by decide⟩,⟨224011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5669_224012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5669 ⟨224012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5669
    ⟨224012, by decide⟩ (by decide) (![⟨223938, by decide⟩,⟨223961, by decide⟩,⟨223989, by decide⟩,⟨224011, by decide⟩]) unmarked_context_11_5669_224012 node_context_11_5669_224012
  intro a
  fin_cases a
  · exact context_12_22676_223938
  · exact context_12_22677_223961
  · exact context_12_22678_223989
  · exact context_12_22679_224011

theorem selected_cut_07821 : selected 9 ⟨224035, by decide⟩
    (prefixPartial 12 22680) = some ⟨12, 2, 0, 224035, 22680, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_22680_224035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22680 ⟨224035, by decide⟩ :=
  accepted_of_selected 12 22680 ⟨224035, by decide⟩ ⟨12, 2, 0, 224035, 22680, 2101, 65536⟩
    (by decide) selected_cut_07821

theorem selected_cut_07822 : selected 9 ⟨224054, by decide⟩
    (prefixPartial 12 22681) = some ⟨12, 2, 0, 224054, 22681, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_22681_224054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22681 ⟨224054, by decide⟩ :=
  accepted_of_selected 12 22681 ⟨224054, by decide⟩ ⟨12, 2, 0, 224054, 22681, 2297, 65536⟩
    (by decide) selected_cut_07822

theorem selected_cut_07823 : selected 9 ⟨224076, by decide⟩
    (prefixPartial 12 22682) = some ⟨12, 2, 0, 224076, 22682, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_22682_224076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22682 ⟨224076, by decide⟩ :=
  accepted_of_selected 12 22682 ⟨224076, by decide⟩ ⟨12, 2, 0, 224076, 22682, 2205, 65536⟩
    (by decide) selected_cut_07823

theorem selected_cut_07824 : selected 9 ⟨224097, by decide⟩
    (prefixPartial 12 22683) = some ⟨12, 2, 0, 224097, 22683, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_22683_224097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22683 ⟨224097, by decide⟩ :=
  accepted_of_selected 12 22683 ⟨224097, by decide⟩ ⟨12, 2, 0, 224097, 22683, 2109, 65536⟩
    (by decide) selected_cut_07824

theorem unmarked_context_11_5670_224098 : frontier 10 ⟨224098, by decide⟩
    (prefixCache 11 5670) (prefixPartial 11 5670) = false := by
  decide +kernel

theorem node_context_11_5670_224098 : EJMOriginalGlobalDAGData.nodes 10 ⟨224098, by decide⟩ =
    .split (coordinate 11) (![⟨224035, by decide⟩,⟨224054, by decide⟩,⟨224076, by decide⟩,⟨224097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5670_224098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5670 ⟨224098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5670
    ⟨224098, by decide⟩ (by decide) (![⟨224035, by decide⟩,⟨224054, by decide⟩,⟨224076, by decide⟩,⟨224097, by decide⟩]) unmarked_context_11_5670_224098 node_context_11_5670_224098
  intro a
  fin_cases a
  · exact context_12_22680_224035
  · exact context_12_22681_224054
  · exact context_12_22682_224076
  · exact context_12_22683_224097

theorem selected_cut_07825 : selected 9 ⟨224121, by decide⟩
    (prefixPartial 12 22684) = some ⟨12, 2, 0, 224121, 22684, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_22684_224121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22684 ⟨224121, by decide⟩ :=
  accepted_of_selected 12 22684 ⟨224121, by decide⟩ ⟨12, 2, 0, 224121, 22684, 1865, 65536⟩
    (by decide) selected_cut_07825

theorem selected_cut_07826 : selected 9 ⟨224139, by decide⟩
    (prefixPartial 12 22685) = some ⟨12, 2, 0, 224139, 22685, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_22685_224139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22685 ⟨224139, by decide⟩ :=
  accepted_of_selected 12 22685 ⟨224139, by decide⟩ ⟨12, 2, 0, 224139, 22685, 2045, 65536⟩
    (by decide) selected_cut_07826

theorem selected_cut_07827 : selected 9 ⟨224159, by decide⟩
    (prefixPartial 12 22686) = some ⟨12, 2, 0, 224159, 22686, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_22686_224159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22686 ⟨224159, by decide⟩ :=
  accepted_of_selected 12 22686 ⟨224159, by decide⟩ ⟨12, 2, 0, 224159, 22686, 2101, 65536⟩
    (by decide) selected_cut_07827

theorem selected_cut_07828 : selected 9 ⟨224180, by decide⟩
    (prefixPartial 12 22687) = some ⟨12, 2, 0, 224180, 22687, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_22687_224180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22687 ⟨224180, by decide⟩ :=
  accepted_of_selected 12 22687 ⟨224180, by decide⟩ ⟨12, 2, 0, 224180, 22687, 1833, 65536⟩
    (by decide) selected_cut_07828

theorem unmarked_context_11_5671_224181 : frontier 10 ⟨224181, by decide⟩
    (prefixCache 11 5671) (prefixPartial 11 5671) = false := by
  decide +kernel

theorem node_context_11_5671_224181 : EJMOriginalGlobalDAGData.nodes 10 ⟨224181, by decide⟩ =
    .split (coordinate 11) (![⟨224121, by decide⟩,⟨224139, by decide⟩,⟨224159, by decide⟩,⟨224180, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5671_224181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5671 ⟨224181, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5671
    ⟨224181, by decide⟩ (by decide) (![⟨224121, by decide⟩,⟨224139, by decide⟩,⟨224159, by decide⟩,⟨224180, by decide⟩]) unmarked_context_11_5671_224181 node_context_11_5671_224181
  intro a
  fin_cases a
  · exact context_12_22684_224121
  · exact context_12_22685_224139
  · exact context_12_22686_224159
  · exact context_12_22687_224180

theorem unmarked_context_10_1417_224182 : frontier 11 ⟨224182, by decide⟩
    (prefixCache 10 1417) (prefixPartial 10 1417) = false := by
  decide +kernel

theorem node_context_10_1417_224182 : EJMOriginalGlobalDAGData.nodes 11 ⟨224182, by decide⟩ =
    .split (coordinate 10) (![⟨223913, by decide⟩,⟨224012, by decide⟩,⟨224098, by decide⟩,⟨224181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1417_224182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1417 ⟨224182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1417
    ⟨224182, by decide⟩ (by decide) (![⟨223913, by decide⟩,⟨224012, by decide⟩,⟨224098, by decide⟩,⟨224181, by decide⟩]) unmarked_context_10_1417_224182 node_context_10_1417_224182
  intro a
  fin_cases a
  · exact context_11_5668_223913
  · exact context_11_5669_224012
  · exact context_11_5670_224098
  · exact context_11_5671_224181

theorem selected_cut_07829 : selected 9 ⟨224204, by decide⟩
    (prefixPartial 12 22688) = some ⟨12, 2, 0, 224204, 22688, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_22688_224204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22688 ⟨224204, by decide⟩ :=
  accepted_of_selected 12 22688 ⟨224204, by decide⟩ ⟨12, 2, 0, 224204, 22688, 2397, 65536⟩
    (by decide) selected_cut_07829

theorem selected_cut_07830 : selected 9 ⟨224223, by decide⟩
    (prefixPartial 12 22689) = some ⟨12, 2, 0, 224223, 22689, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_22689_224223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22689 ⟨224223, by decide⟩ :=
  accepted_of_selected 12 22689 ⟨224223, by decide⟩ ⟨12, 2, 0, 224223, 22689, 1729, 65536⟩
    (by decide) selected_cut_07830

theorem selected_cut_07831 : selected 9 ⟨224244, by decide⟩
    (prefixPartial 12 22690) = some ⟨12, 2, 0, 224244, 22690, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_22690_224244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22690 ⟨224244, by decide⟩ :=
  accepted_of_selected 12 22690 ⟨224244, by decide⟩ ⟨12, 2, 0, 224244, 22690, 1657, 65536⟩
    (by decide) selected_cut_07831

theorem selected_cut_07832 : selected 9 ⟨224260, by decide⟩
    (prefixPartial 12 22691) = some ⟨12, 2, 0, 224260, 22691, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_22691_224260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22691 ⟨224260, by decide⟩ :=
  accepted_of_selected 12 22691 ⟨224260, by decide⟩ ⟨12, 2, 0, 224260, 22691, 1445, 65536⟩
    (by decide) selected_cut_07832

theorem unmarked_context_11_5672_224261 : frontier 10 ⟨224261, by decide⟩
    (prefixCache 11 5672) (prefixPartial 11 5672) = false := by
  decide +kernel

theorem node_context_11_5672_224261 : EJMOriginalGlobalDAGData.nodes 10 ⟨224261, by decide⟩ =
    .split (coordinate 11) (![⟨224204, by decide⟩,⟨224223, by decide⟩,⟨224244, by decide⟩,⟨224260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5672_224261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5672 ⟨224261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5672
    ⟨224261, by decide⟩ (by decide) (![⟨224204, by decide⟩,⟨224223, by decide⟩,⟨224244, by decide⟩,⟨224260, by decide⟩]) unmarked_context_11_5672_224261 node_context_11_5672_224261
  intro a
  fin_cases a
  · exact context_12_22688_224204
  · exact context_12_22689_224223
  · exact context_12_22690_224244
  · exact context_12_22691_224260

theorem selected_cut_07833 : selected 9 ⟨224283, by decide⟩
    (prefixPartial 12 22692) = some ⟨12, 2, 0, 224283, 22692, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_22692_224283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22692 ⟨224283, by decide⟩ :=
  accepted_of_selected 12 22692 ⟨224283, by decide⟩ ⟨12, 2, 0, 224283, 22692, 1561, 65536⟩
    (by decide) selected_cut_07833

theorem selected_cut_07834 : selected 9 ⟨224300, by decide⟩
    (prefixPartial 12 22693) = some ⟨12, 2, 0, 224300, 22693, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_22693_224300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22693 ⟨224300, by decide⟩ :=
  accepted_of_selected 12 22693 ⟨224300, by decide⟩ ⟨12, 2, 0, 224300, 22693, 1621, 65536⟩
    (by decide) selected_cut_07834

theorem selected_cut_07835 : selected 9 ⟨224320, by decide⟩
    (prefixPartial 12 22694) = some ⟨12, 2, 0, 224320, 22694, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_22694_224320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22694 ⟨224320, by decide⟩ :=
  accepted_of_selected 12 22694 ⟨224320, by decide⟩ ⟨12, 2, 0, 224320, 22694, 1545, 65536⟩
    (by decide) selected_cut_07835

theorem selected_cut_07836 : selected 9 ⟨224337, by decide⟩
    (prefixPartial 12 22695) = some ⟨12, 2, 0, 224337, 22695, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_22695_224337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22695 ⟨224337, by decide⟩ :=
  accepted_of_selected 12 22695 ⟨224337, by decide⟩ ⟨12, 2, 0, 224337, 22695, 1513, 65536⟩
    (by decide) selected_cut_07836

theorem unmarked_context_11_5673_224338 : frontier 10 ⟨224338, by decide⟩
    (prefixCache 11 5673) (prefixPartial 11 5673) = false := by
  decide +kernel

theorem node_context_11_5673_224338 : EJMOriginalGlobalDAGData.nodes 10 ⟨224338, by decide⟩ =
    .split (coordinate 11) (![⟨224283, by decide⟩,⟨224300, by decide⟩,⟨224320, by decide⟩,⟨224337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5673_224338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5673 ⟨224338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5673
    ⟨224338, by decide⟩ (by decide) (![⟨224283, by decide⟩,⟨224300, by decide⟩,⟨224320, by decide⟩,⟨224337, by decide⟩]) unmarked_context_11_5673_224338 node_context_11_5673_224338
  intro a
  fin_cases a
  · exact context_12_22692_224283
  · exact context_12_22693_224300
  · exact context_12_22694_224320
  · exact context_12_22695_224337

theorem selected_cut_07837 : selected 10 ⟨224389, by decide⟩
    (prefixPartial 11 5674) = some ⟨11, 2, 0, 224389, 5674, 3901, 262144⟩ := by
  decide +kernel

theorem context_11_5674_224389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5674 ⟨224389, by decide⟩ :=
  accepted_of_selected 11 5674 ⟨224389, by decide⟩ ⟨11, 2, 0, 224389, 5674, 3901, 262144⟩
    (by decide) selected_cut_07837

theorem selected_cut_07838 : selected 9 ⟨224406, by decide⟩
    (prefixPartial 12 22700) = some ⟨12, 2, 0, 224406, 22700, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_22700_224406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22700 ⟨224406, by decide⟩ :=
  accepted_of_selected 12 22700 ⟨224406, by decide⟩ ⟨12, 2, 0, 224406, 22700, 1477, 65536⟩
    (by decide) selected_cut_07838

theorem selected_cut_07839 : selected 9 ⟨224422, by decide⟩
    (prefixPartial 12 22701) = some ⟨12, 2, 0, 224422, 22701, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_22701_224422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22701 ⟨224422, by decide⟩ :=
  accepted_of_selected 12 22701 ⟨224422, by decide⟩ ⟨12, 2, 0, 224422, 22701, 1545, 65536⟩
    (by decide) selected_cut_07839

theorem selected_cut_07840 : selected 9 ⟨224442, by decide⟩
    (prefixPartial 12 22702) = some ⟨12, 2, 0, 224442, 22702, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_22702_224442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22702 ⟨224442, by decide⟩ :=
  accepted_of_selected 12 22702 ⟨224442, by decide⟩ ⟨12, 2, 0, 224442, 22702, 1429, 65536⟩
    (by decide) selected_cut_07840

theorem selected_cut_07841 : selected 9 ⟨224456, by decide⟩
    (prefixPartial 12 22703) = some ⟨12, 2, 0, 224456, 22703, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_22703_224456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22703 ⟨224456, by decide⟩ :=
  accepted_of_selected 12 22703 ⟨224456, by decide⟩ ⟨12, 2, 0, 224456, 22703, 1329, 65536⟩
    (by decide) selected_cut_07841

theorem unmarked_context_11_5675_224457 : frontier 10 ⟨224457, by decide⟩
    (prefixCache 11 5675) (prefixPartial 11 5675) = false := by
  decide +kernel

theorem node_context_11_5675_224457 : EJMOriginalGlobalDAGData.nodes 10 ⟨224457, by decide⟩ =
    .split (coordinate 11) (![⟨224406, by decide⟩,⟨224422, by decide⟩,⟨224442, by decide⟩,⟨224456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5675_224457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5675 ⟨224457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5675
    ⟨224457, by decide⟩ (by decide) (![⟨224406, by decide⟩,⟨224422, by decide⟩,⟨224442, by decide⟩,⟨224456, by decide⟩]) unmarked_context_11_5675_224457 node_context_11_5675_224457
  intro a
  fin_cases a
  · exact context_12_22700_224406
  · exact context_12_22701_224422
  · exact context_12_22702_224442
  · exact context_12_22703_224456

theorem unmarked_context_10_1418_224458 : frontier 11 ⟨224458, by decide⟩
    (prefixCache 10 1418) (prefixPartial 10 1418) = false := by
  decide +kernel

theorem node_context_10_1418_224458 : EJMOriginalGlobalDAGData.nodes 11 ⟨224458, by decide⟩ =
    .split (coordinate 10) (![⟨224261, by decide⟩,⟨224338, by decide⟩,⟨224389, by decide⟩,⟨224457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1418_224458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1418 ⟨224458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1418
    ⟨224458, by decide⟩ (by decide) (![⟨224261, by decide⟩,⟨224338, by decide⟩,⟨224389, by decide⟩,⟨224457, by decide⟩]) unmarked_context_10_1418_224458 node_context_10_1418_224458
  intro a
  fin_cases a
  · exact context_11_5672_224261
  · exact context_11_5673_224338
  · exact context_11_5674_224389
  · exact context_11_5675_224457

theorem selected_cut_07842 : selected 9 ⟨224484, by decide⟩
    (prefixPartial 12 22704) = some ⟨12, 2, 0, 224484, 22704, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_22704_224484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22704 ⟨224484, by decide⟩ :=
  accepted_of_selected 12 22704 ⟨224484, by decide⟩ ⟨12, 2, 0, 224484, 22704, 1921, 65536⟩
    (by decide) selected_cut_07842

theorem selected_cut_07843 : selected 9 ⟨224498, by decide⟩
    (prefixPartial 12 22705) = some ⟨12, 2, 0, 224498, 22705, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_22705_224498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22705 ⟨224498, by decide⟩ :=
  accepted_of_selected 12 22705 ⟨224498, by decide⟩ ⟨12, 2, 0, 224498, 22705, 1353, 65536⟩
    (by decide) selected_cut_07843

theorem selected_cut_07844 : selected 9 ⟨224510, by decide⟩
    (prefixPartial 12 22706) = some ⟨12, 2, 0, 224510, 22706, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_22706_224510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22706 ⟨224510, by decide⟩ :=
  accepted_of_selected 12 22706 ⟨224510, by decide⟩ ⟨12, 2, 0, 224510, 22706, 1253, 65536⟩
    (by decide) selected_cut_07844

theorem selected_cut_07845 : selected 9 ⟨224520, by decide⟩
    (prefixPartial 12 22707) = some ⟨12, 2, 0, 224520, 22707, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_22707_224520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22707 ⟨224520, by decide⟩ :=
  accepted_of_selected 12 22707 ⟨224520, by decide⟩ ⟨12, 2, 0, 224520, 22707, 1217, 65536⟩
    (by decide) selected_cut_07845

theorem unmarked_context_11_5676_224521 : frontier 10 ⟨224521, by decide⟩
    (prefixCache 11 5676) (prefixPartial 11 5676) = false := by
  decide +kernel

theorem node_context_11_5676_224521 : EJMOriginalGlobalDAGData.nodes 10 ⟨224521, by decide⟩ =
    .split (coordinate 11) (![⟨224484, by decide⟩,⟨224498, by decide⟩,⟨224510, by decide⟩,⟨224520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5676_224521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5676 ⟨224521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5676
    ⟨224521, by decide⟩ (by decide) (![⟨224484, by decide⟩,⟨224498, by decide⟩,⟨224510, by decide⟩,⟨224520, by decide⟩]) unmarked_context_11_5676_224521 node_context_11_5676_224521
  intro a
  fin_cases a
  · exact context_12_22704_224484
  · exact context_12_22705_224498
  · exact context_12_22706_224510
  · exact context_12_22707_224520

theorem selected_cut_07846 : selected 9 ⟨224539, by decide⟩
    (prefixPartial 12 22708) = some ⟨12, 2, 0, 224539, 22708, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_22708_224539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22708 ⟨224539, by decide⟩ :=
  accepted_of_selected 12 22708 ⟨224539, by decide⟩ ⟨12, 2, 0, 224539, 22708, 1345, 65536⟩
    (by decide) selected_cut_07846

theorem selected_cut_07847 : selected 9 ⟨224555, by decide⟩
    (prefixPartial 12 22709) = some ⟨12, 2, 0, 224555, 22709, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_22709_224555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22709 ⟨224555, by decide⟩ :=
  accepted_of_selected 12 22709 ⟨224555, by decide⟩ ⟨12, 2, 0, 224555, 22709, 1305, 65536⟩
    (by decide) selected_cut_07847

theorem selected_cut_07848 : selected 9 ⟨224569, by decide⟩
    (prefixPartial 12 22710) = some ⟨12, 2, 0, 224569, 22710, 1141, 65536⟩ := by
  decide +kernel

theorem context_12_22710_224569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22710 ⟨224569, by decide⟩ :=
  accepted_of_selected 12 22710 ⟨224569, by decide⟩ ⟨12, 2, 0, 224569, 22710, 1141, 65536⟩
    (by decide) selected_cut_07848

theorem selected_cut_07849 : selected 9 ⟨224584, by decide⟩
    (prefixPartial 12 22711) = some ⟨12, 2, 0, 224584, 22711, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_22711_224584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22711 ⟨224584, by decide⟩ :=
  accepted_of_selected 12 22711 ⟨224584, by decide⟩ ⟨12, 2, 0, 224584, 22711, 1241, 65536⟩
    (by decide) selected_cut_07849

theorem unmarked_context_11_5677_224585 : frontier 10 ⟨224585, by decide⟩
    (prefixCache 11 5677) (prefixPartial 11 5677) = false := by
  decide +kernel

theorem node_context_11_5677_224585 : EJMOriginalGlobalDAGData.nodes 10 ⟨224585, by decide⟩ =
    .split (coordinate 11) (![⟨224539, by decide⟩,⟨224555, by decide⟩,⟨224569, by decide⟩,⟨224584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5677_224585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5677 ⟨224585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5677
    ⟨224585, by decide⟩ (by decide) (![⟨224539, by decide⟩,⟨224555, by decide⟩,⟨224569, by decide⟩,⟨224584, by decide⟩]) unmarked_context_11_5677_224585 node_context_11_5677_224585
  intro a
  fin_cases a
  · exact context_12_22708_224539
  · exact context_12_22709_224555
  · exact context_12_22710_224569
  · exact context_12_22711_224584

theorem selected_cut_07850 : selected 9 ⟨224601, by decide⟩
    (prefixPartial 12 22712) = some ⟨12, 2, 0, 224601, 22712, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_22712_224601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22712 ⟨224601, by decide⟩ :=
  accepted_of_selected 12 22712 ⟨224601, by decide⟩ ⟨12, 2, 0, 224601, 22712, 1277, 65536⟩
    (by decide) selected_cut_07850

theorem selected_cut_07851 : selected 9 ⟨224617, by decide⟩
    (prefixPartial 12 22713) = some ⟨12, 2, 0, 224617, 22713, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_22713_224617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22713 ⟨224617, by decide⟩ :=
  accepted_of_selected 12 22713 ⟨224617, by decide⟩ ⟨12, 2, 0, 224617, 22713, 1321, 65536⟩
    (by decide) selected_cut_07851

theorem selected_cut_07852 : selected 9 ⟨224633, by decide⟩
    (prefixPartial 12 22714) = some ⟨12, 2, 0, 224633, 22714, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_22714_224633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22714 ⟨224633, by decide⟩ :=
  accepted_of_selected 12 22714 ⟨224633, by decide⟩ ⟨12, 2, 0, 224633, 22714, 1157, 65536⟩
    (by decide) selected_cut_07852

theorem selected_cut_07853 : selected 9 ⟨224648, by decide⟩
    (prefixPartial 12 22715) = some ⟨12, 2, 0, 224648, 22715, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_22715_224648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22715 ⟨224648, by decide⟩ :=
  accepted_of_selected 12 22715 ⟨224648, by decide⟩ ⟨12, 2, 0, 224648, 22715, 1241, 65536⟩
    (by decide) selected_cut_07853

theorem unmarked_context_11_5678_224649 : frontier 10 ⟨224649, by decide⟩
    (prefixCache 11 5678) (prefixPartial 11 5678) = false := by
  decide +kernel

theorem node_context_11_5678_224649 : EJMOriginalGlobalDAGData.nodes 10 ⟨224649, by decide⟩ =
    .split (coordinate 11) (![⟨224601, by decide⟩,⟨224617, by decide⟩,⟨224633, by decide⟩,⟨224648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5678_224649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5678 ⟨224649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5678
    ⟨224649, by decide⟩ (by decide) (![⟨224601, by decide⟩,⟨224617, by decide⟩,⟨224633, by decide⟩,⟨224648, by decide⟩]) unmarked_context_11_5678_224649 node_context_11_5678_224649
  intro a
  fin_cases a
  · exact context_12_22712_224601
  · exact context_12_22713_224617
  · exact context_12_22714_224633
  · exact context_12_22715_224648

theorem selected_cut_07854 : selected 10 ⟨224695, by decide⟩
    (prefixPartial 11 5679) = some ⟨11, 2, 0, 224695, 5679, 3857, 262144⟩ := by
  decide +kernel

theorem context_11_5679_224695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5679 ⟨224695, by decide⟩ :=
  accepted_of_selected 11 5679 ⟨224695, by decide⟩ ⟨11, 2, 0, 224695, 5679, 3857, 262144⟩
    (by decide) selected_cut_07854

theorem unmarked_context_10_1419_224696 : frontier 11 ⟨224696, by decide⟩
    (prefixCache 10 1419) (prefixPartial 10 1419) = false := by
  decide +kernel

theorem node_context_10_1419_224696 : EJMOriginalGlobalDAGData.nodes 11 ⟨224696, by decide⟩ =
    .split (coordinate 10) (![⟨224521, by decide⟩,⟨224585, by decide⟩,⟨224649, by decide⟩,⟨224695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1419_224696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1419 ⟨224696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1419
    ⟨224696, by decide⟩ (by decide) (![⟨224521, by decide⟩,⟨224585, by decide⟩,⟨224649, by decide⟩,⟨224695, by decide⟩]) unmarked_context_10_1419_224696 node_context_10_1419_224696
  intro a
  fin_cases a
  · exact context_11_5676_224521
  · exact context_11_5677_224585
  · exact context_11_5678_224649
  · exact context_11_5679_224695

theorem unmarked_context_9_354_224697 : frontier 12 ⟨224697, by decide⟩
    (prefixCache 9 354) (prefixPartial 9 354) = false := by
  decide +kernel

theorem node_context_9_354_224697 : EJMOriginalGlobalDAGData.nodes 12 ⟨224697, by decide⟩ =
    .split (coordinate 9) (![⟨223789, by decide⟩,⟨224182, by decide⟩,⟨224458, by decide⟩,⟨224696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_354_224697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 354 ⟨224697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 354
    ⟨224697, by decide⟩ (by decide) (![⟨223789, by decide⟩,⟨224182, by decide⟩,⟨224458, by decide⟩,⟨224696, by decide⟩]) unmarked_context_9_354_224697 node_context_9_354_224697
  intro a
  fin_cases a
  · exact context_10_1416_223789
  · exact context_10_1417_224182
  · exact context_10_1418_224458
  · exact context_10_1419_224696

theorem selected_cut_07855 : selected 9 ⟨224726, by decide⟩
    (prefixPartial 12 22720) = some ⟨12, 2, 0, 224726, 22720, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_22720_224726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22720 ⟨224726, by decide⟩ :=
  accepted_of_selected 12 22720 ⟨224726, by decide⟩ ⟨12, 2, 0, 224726, 22720, 1509, 65536⟩
    (by decide) selected_cut_07855

theorem selected_cut_07856 : selected 9 ⟨224738, by decide⟩
    (prefixPartial 12 22721) = some ⟨12, 2, 0, 224738, 22721, 977, 65536⟩ := by
  decide +kernel

theorem context_12_22721_224738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22721 ⟨224738, by decide⟩ :=
  accepted_of_selected 12 22721 ⟨224738, by decide⟩ ⟨12, 2, 0, 224738, 22721, 977, 65536⟩
    (by decide) selected_cut_07856

theorem selected_cut_07857 : selected 9 ⟨224747, by decide⟩
    (prefixPartial 12 22722) = some ⟨12, 2, 0, 224747, 22722, 937, 65536⟩ := by
  decide +kernel

theorem context_12_22722_224747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22722 ⟨224747, by decide⟩ :=
  accepted_of_selected 12 22722 ⟨224747, by decide⟩ ⟨12, 2, 0, 224747, 22722, 937, 65536⟩
    (by decide) selected_cut_07857

theorem selected_cut_07858 : selected 9 ⟨224753, by decide⟩
    (prefixPartial 12 22723) = some ⟨12, 2, 0, 224753, 22723, 889, 65536⟩ := by
  decide +kernel

theorem context_12_22723_224753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22723 ⟨224753, by decide⟩ :=
  accepted_of_selected 12 22723 ⟨224753, by decide⟩ ⟨12, 2, 0, 224753, 22723, 889, 65536⟩
    (by decide) selected_cut_07858

theorem unmarked_context_11_5680_224754 : frontier 10 ⟨224754, by decide⟩
    (prefixCache 11 5680) (prefixPartial 11 5680) = false := by
  decide +kernel

theorem node_context_11_5680_224754 : EJMOriginalGlobalDAGData.nodes 10 ⟨224754, by decide⟩ =
    .split (coordinate 11) (![⟨224726, by decide⟩,⟨224738, by decide⟩,⟨224747, by decide⟩,⟨224753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5680_224754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5680 ⟨224754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5680
    ⟨224754, by decide⟩ (by decide) (![⟨224726, by decide⟩,⟨224738, by decide⟩,⟨224747, by decide⟩,⟨224753, by decide⟩]) unmarked_context_11_5680_224754 node_context_11_5680_224754
  intro a
  fin_cases a
  · exact context_12_22720_224726
  · exact context_12_22721_224738
  · exact context_12_22722_224747
  · exact context_12_22723_224753

theorem selected_cut_07859 : selected 10 ⟨224791, by decide⟩
    (prefixPartial 11 5681) = some ⟨11, 2, 0, 224791, 5681, 3501, 262144⟩ := by
  decide +kernel

theorem context_11_5681_224791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5681 ⟨224791, by decide⟩ :=
  accepted_of_selected 11 5681 ⟨224791, by decide⟩ ⟨11, 2, 0, 224791, 5681, 3501, 262144⟩
    (by decide) selected_cut_07859

theorem selected_cut_07860 : selected 10 ⟨224824, by decide⟩
    (prefixPartial 11 5682) = some ⟨11, 2, 0, 224824, 5682, 3137, 262144⟩ := by
  decide +kernel

theorem context_11_5682_224824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5682 ⟨224824, by decide⟩ :=
  accepted_of_selected 11 5682 ⟨224824, by decide⟩ ⟨11, 2, 0, 224824, 5682, 3137, 262144⟩
    (by decide) selected_cut_07860

theorem selected_cut_07861 : selected 10 ⟨224855, by decide⟩
    (prefixPartial 11 5683) = some ⟨11, 2, 0, 224855, 5683, 3073, 262144⟩ := by
  decide +kernel

theorem context_11_5683_224855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5683 ⟨224855, by decide⟩ :=
  accepted_of_selected 11 5683 ⟨224855, by decide⟩ ⟨11, 2, 0, 224855, 5683, 3073, 262144⟩
    (by decide) selected_cut_07861

theorem unmarked_context_10_1420_224856 : frontier 11 ⟨224856, by decide⟩
    (prefixCache 10 1420) (prefixPartial 10 1420) = false := by
  decide +kernel

theorem node_context_10_1420_224856 : EJMOriginalGlobalDAGData.nodes 11 ⟨224856, by decide⟩ =
    .split (coordinate 10) (![⟨224754, by decide⟩,⟨224791, by decide⟩,⟨224824, by decide⟩,⟨224855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1420_224856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1420 ⟨224856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1420
    ⟨224856, by decide⟩ (by decide) (![⟨224754, by decide⟩,⟨224791, by decide⟩,⟨224824, by decide⟩,⟨224855, by decide⟩]) unmarked_context_10_1420_224856 node_context_10_1420_224856
  intro a
  fin_cases a
  · exact context_11_5680_224754
  · exact context_11_5681_224791
  · exact context_11_5682_224824
  · exact context_11_5683_224855

theorem selected_cut_07862 : selected 10 ⟨224913, by decide⟩
    (prefixPartial 11 5684) = some ⟨11, 2, 0, 224913, 5684, 3589, 262144⟩ := by
  decide +kernel

theorem context_11_5684_224913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5684 ⟨224913, by decide⟩ :=
  accepted_of_selected 11 5684 ⟨224913, by decide⟩ ⟨11, 2, 0, 224913, 5684, 3589, 262144⟩
    (by decide) selected_cut_07862

theorem selected_cut_07863 : selected 10 ⟨224942, by decide⟩
    (prefixPartial 11 5685) = some ⟨11, 2, 0, 224942, 5685, 2665, 262144⟩ := by
  decide +kernel

theorem context_11_5685_224942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5685 ⟨224942, by decide⟩ :=
  accepted_of_selected 11 5685 ⟨224942, by decide⟩ ⟨11, 2, 0, 224942, 5685, 2665, 262144⟩
    (by decide) selected_cut_07863

theorem selected_cut_07864 : selected 10 ⟨224964, by decide⟩
    (prefixPartial 11 5686) = some ⟨11, 2, 0, 224964, 5686, 2265, 262144⟩ := by
  decide +kernel

theorem context_11_5686_224964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5686 ⟨224964, by decide⟩ :=
  accepted_of_selected 11 5686 ⟨224964, by decide⟩ ⟨11, 2, 0, 224964, 5686, 2265, 262144⟩
    (by decide) selected_cut_07864

theorem selected_cut_07865 : selected 10 ⟨224984, by decide⟩
    (prefixPartial 11 5687) = some ⟨11, 2, 0, 224984, 5687, 1985, 262144⟩ := by
  decide +kernel

theorem context_11_5687_224984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5687 ⟨224984, by decide⟩ :=
  accepted_of_selected 11 5687 ⟨224984, by decide⟩ ⟨11, 2, 0, 224984, 5687, 1985, 262144⟩
    (by decide) selected_cut_07865

theorem unmarked_context_10_1421_224985 : frontier 11 ⟨224985, by decide⟩
    (prefixCache 10 1421) (prefixPartial 10 1421) = false := by
  decide +kernel

theorem node_context_10_1421_224985 : EJMOriginalGlobalDAGData.nodes 11 ⟨224985, by decide⟩ =
    .split (coordinate 10) (![⟨224913, by decide⟩,⟨224942, by decide⟩,⟨224964, by decide⟩,⟨224984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1421_224985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1421 ⟨224985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1421
    ⟨224985, by decide⟩ (by decide) (![⟨224913, by decide⟩,⟨224942, by decide⟩,⟨224964, by decide⟩,⟨224984, by decide⟩]) unmarked_context_10_1421_224985 node_context_10_1421_224985
  intro a
  fin_cases a
  · exact context_11_5684_224913
  · exact context_11_5685_224942
  · exact context_11_5686_224964
  · exact context_11_5687_224984

theorem selected_cut_07866 : selected 10 ⟨225006, by decide⟩
    (prefixPartial 11 5688) = some ⟨11, 2, 0, 225006, 5688, 1897, 262144⟩ := by
  decide +kernel

theorem context_11_5688_225006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5688 ⟨225006, by decide⟩ :=
  accepted_of_selected 11 5688 ⟨225006, by decide⟩ ⟨11, 2, 0, 225006, 5688, 1897, 262144⟩
    (by decide) selected_cut_07866

theorem selected_cut_07867 : selected 10 ⟨225019, by decide⟩
    (prefixPartial 11 5689) = some ⟨11, 2, 0, 225019, 5689, 1369, 262144⟩ := by
  decide +kernel

theorem context_11_5689_225019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5689 ⟨225019, by decide⟩ :=
  accepted_of_selected 11 5689 ⟨225019, by decide⟩ ⟨11, 2, 0, 225019, 5689, 1369, 262144⟩
    (by decide) selected_cut_07867

theorem selected_cut_07868 : selected 10 ⟨225041, by decide⟩
    (prefixPartial 11 5690) = some ⟨11, 2, 0, 225041, 5690, 1293, 262144⟩ := by
  decide +kernel

theorem context_11_5690_225041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5690 ⟨225041, by decide⟩ :=
  accepted_of_selected 11 5690 ⟨225041, by decide⟩ ⟨11, 2, 0, 225041, 5690, 1293, 262144⟩
    (by decide) selected_cut_07868

theorem selected_cut_07869 : selected 10 ⟨225058, by decide⟩
    (prefixPartial 11 5691) = some ⟨11, 2, 0, 225058, 5691, 857, 262144⟩ := by
  decide +kernel

theorem context_11_5691_225058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5691 ⟨225058, by decide⟩ :=
  accepted_of_selected 11 5691 ⟨225058, by decide⟩ ⟨11, 2, 0, 225058, 5691, 857, 262144⟩
    (by decide) selected_cut_07869

theorem unmarked_context_10_1422_225059 : frontier 11 ⟨225059, by decide⟩
    (prefixCache 10 1422) (prefixPartial 10 1422) = false := by
  decide +kernel

theorem node_context_10_1422_225059 : EJMOriginalGlobalDAGData.nodes 11 ⟨225059, by decide⟩ =
    .split (coordinate 10) (![⟨225006, by decide⟩,⟨225019, by decide⟩,⟨225041, by decide⟩,⟨225058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1422_225059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1422 ⟨225059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1422
    ⟨225059, by decide⟩ (by decide) (![⟨225006, by decide⟩,⟨225019, by decide⟩,⟨225041, by decide⟩,⟨225058, by decide⟩]) unmarked_context_10_1422_225059 node_context_10_1422_225059
  intro a
  fin_cases a
  · exact context_11_5688_225006
  · exact context_11_5689_225019
  · exact context_11_5690_225041
  · exact context_11_5691_225058

theorem selected_cut_07870 : selected 11 ⟨225088, by decide⟩
    (prefixPartial 10 1423) = some ⟨10, 2, 0, 225088, 1423, 1529, 1048576⟩ := by
  decide +kernel

theorem context_10_1423_225088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1423 ⟨225088, by decide⟩ :=
  accepted_of_selected 10 1423 ⟨225088, by decide⟩ ⟨10, 2, 0, 225088, 1423, 1529, 1048576⟩
    (by decide) selected_cut_07870

theorem unmarked_context_9_355_225089 : frontier 12 ⟨225089, by decide⟩
    (prefixCache 9 355) (prefixPartial 9 355) = false := by
  decide +kernel

theorem node_context_9_355_225089 : EJMOriginalGlobalDAGData.nodes 12 ⟨225089, by decide⟩ =
    .split (coordinate 9) (![⟨224856, by decide⟩,⟨224985, by decide⟩,⟨225059, by decide⟩,⟨225088, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_355_225089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 355 ⟨225089, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 355
    ⟨225089, by decide⟩ (by decide) (![⟨224856, by decide⟩,⟨224985, by decide⟩,⟨225059, by decide⟩,⟨225088, by decide⟩]) unmarked_context_9_355_225089 node_context_9_355_225089
  intro a
  fin_cases a
  · exact context_10_1420_224856
  · exact context_10_1421_224985
  · exact context_10_1422_225059
  · exact context_10_1423_225088

theorem unmarked_context_8_88_225090 : frontier 13 ⟨225090, by decide⟩
    (prefixCache 8 88) (prefixPartial 8 88) = false := by
  decide +kernel

theorem node_context_8_88_225090 : EJMOriginalGlobalDAGData.nodes 13 ⟨225090, by decide⟩ =
    .split (coordinate 8) (![⟨219365, by decide⟩,⟨223301, by decide⟩,⟨224697, by decide⟩,⟨225089, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_88_225090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 88 ⟨225090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 88
    ⟨225090, by decide⟩ (by decide) (![⟨219365, by decide⟩,⟨223301, by decide⟩,⟨224697, by decide⟩,⟨225089, by decide⟩]) unmarked_context_8_88_225090 node_context_8_88_225090
  intro a
  fin_cases a
  · exact context_9_352_219365
  · exact context_9_353_223301
  · exact context_9_354_224697
  · exact context_9_355_225089

theorem selected_cut_07871 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 22784) = some ⟨12, 1, 0, 34034, 22784, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22784_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22784 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 22784 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 22784, 1, 65536⟩
    (by decide) selected_cut_07871

theorem selected_cut_07872 : selected 8 ⟨225127, by decide⟩
    (prefixPartial 13 91140) = some ⟨13, 2, 0, 225127, 91140, 3489, 16384⟩ := by
  decide +kernel

theorem context_13_91140_225127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91140 ⟨225127, by decide⟩ :=
  accepted_of_selected 13 91140 ⟨225127, by decide⟩ ⟨13, 2, 0, 225127, 91140, 3489, 16384⟩
    (by decide) selected_cut_07872

theorem selected_cut_07873 : selected 8 ⟨225147, by decide⟩
    (prefixPartial 13 91141) = some ⟨13, 2, 0, 225147, 91141, 2801, 16384⟩ := by
  decide +kernel

theorem context_13_91141_225147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91141 ⟨225147, by decide⟩ :=
  accepted_of_selected 13 91141 ⟨225147, by decide⟩ ⟨13, 2, 0, 225147, 91141, 2801, 16384⟩
    (by decide) selected_cut_07873

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
