/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover134
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_12963 : selected 8 ⟨341117, by decide⟩
    (prefixPartial 13 105738) = some ⟨13, 2, 0, 341117, 105738, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_105738_341117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105738 ⟨341117, by decide⟩ :=
  accepted_of_selected 13 105738 ⟨341117, by decide⟩ ⟨13, 2, 0, 341117, 105738, 2001, 16384⟩
    (by decide) selected_cut_12963

theorem selected_cut_12964 : selected 8 ⟨341125, by decide⟩
    (prefixPartial 13 105739) = some ⟨13, 2, 0, 341125, 105739, 657, 16384⟩ := by
  decide +kernel

theorem context_13_105739_341125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105739 ⟨341125, by decide⟩ :=
  accepted_of_selected 13 105739 ⟨341125, by decide⟩ ⟨13, 2, 0, 341125, 105739, 657, 16384⟩
    (by decide) selected_cut_12964

theorem unmarked_context_12_26434_341126 : frontier 9 ⟨341126, by decide⟩
    (prefixCache 12 26434) (prefixPartial 12 26434) = false := by
  decide +kernel

theorem node_context_12_26434_341126 : EJMOriginalGlobalDAGData.nodes 9 ⟨341126, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨341088, by decide⟩,⟨341117, by decide⟩,⟨341125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26434_341126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26434 ⟨341126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26434
    ⟨341126, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨341088, by decide⟩,⟨341117, by decide⟩,⟨341125, by decide⟩]) unmarked_context_12_26434_341126 node_context_12_26434_341126
  intro a
  fin_cases a
  · exact context_13_105736_3444
  · exact context_13_105737_341088
  · exact context_13_105738_341117
  · exact context_13_105739_341125

theorem selected_cut_12965 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105740) = some ⟨13, 1, 0, 3444, 105740, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105740_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105740 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105740 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105740, 1, 16384⟩
    (by decide) selected_cut_12965

theorem selected_cut_12966 : selected 8 ⟨341176, by decide⟩
    (prefixPartial 13 105741) = some ⟨13, 2, 0, 341176, 105741, 3137, 16384⟩ := by
  decide +kernel

theorem context_13_105741_341176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105741 ⟨341176, by decide⟩ :=
  accepted_of_selected 13 105741 ⟨341176, by decide⟩ ⟨13, 2, 0, 341176, 105741, 3137, 16384⟩
    (by decide) selected_cut_12966

theorem selected_cut_12967 : selected 8 ⟨341197, by decide⟩
    (prefixPartial 13 105742) = some ⟨13, 2, 0, 341197, 105742, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_105742_341197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105742 ⟨341197, by decide⟩ :=
  accepted_of_selected 13 105742 ⟨341197, by decide⟩ ⟨13, 2, 0, 341197, 105742, 1933, 16384⟩
    (by decide) selected_cut_12967

theorem selected_cut_12968 : selected 8 ⟨341205, by decide⟩
    (prefixPartial 13 105743) = some ⟨13, 2, 0, 341205, 105743, 589, 16384⟩ := by
  decide +kernel

theorem context_13_105743_341205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105743 ⟨341205, by decide⟩ :=
  accepted_of_selected 13 105743 ⟨341205, by decide⟩ ⟨13, 2, 0, 341205, 105743, 589, 16384⟩
    (by decide) selected_cut_12968

theorem unmarked_context_12_26435_341206 : frontier 9 ⟨341206, by decide⟩
    (prefixCache 12 26435) (prefixPartial 12 26435) = false := by
  decide +kernel

theorem node_context_12_26435_341206 : EJMOriginalGlobalDAGData.nodes 9 ⟨341206, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨341176, by decide⟩,⟨341197, by decide⟩,⟨341205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26435_341206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26435 ⟨341206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26435
    ⟨341206, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨341176, by decide⟩,⟨341197, by decide⟩,⟨341205, by decide⟩]) unmarked_context_12_26435_341206 node_context_12_26435_341206
  intro a
  fin_cases a
  · exact context_13_105740_3444
  · exact context_13_105741_341176
  · exact context_13_105742_341197
  · exact context_13_105743_341205

theorem unmarked_context_11_6608_341207 : frontier 10 ⟨341207, by decide⟩
    (prefixCache 11 6608) (prefixPartial 11 6608) = false := by
  decide +kernel

theorem node_context_11_6608_341207 : EJMOriginalGlobalDAGData.nodes 10 ⟨341207, by decide⟩ =
    .split (coordinate 11) (![⟨340902, by decide⟩,⟨341042, by decide⟩,⟨341126, by decide⟩,⟨341206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6608_341207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6608 ⟨341207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6608
    ⟨341207, by decide⟩ (by decide) (![⟨340902, by decide⟩,⟨341042, by decide⟩,⟨341126, by decide⟩,⟨341206, by decide⟩]) unmarked_context_11_6608_341207 node_context_11_6608_341207
  intro a
  fin_cases a
  · exact context_12_26432_340902
  · exact context_12_26433_341042
  · exact context_12_26434_341126
  · exact context_12_26435_341206

theorem selected_cut_12969 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105744) = some ⟨13, 1, 0, 3444, 105744, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105744_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105744 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105744 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105744, 1, 16384⟩
    (by decide) selected_cut_12969

theorem selected_cut_12970 : selected 8 ⟨341243, by decide⟩
    (prefixPartial 13 105745) = some ⟨13, 2, 0, 341243, 105745, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_105745_341243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105745 ⟨341243, by decide⟩ :=
  accepted_of_selected 13 105745 ⟨341243, by decide⟩ ⟨13, 2, 0, 341243, 105745, 2745, 16384⟩
    (by decide) selected_cut_12970

theorem selected_cut_12971 : selected 8 ⟨341270, by decide⟩
    (prefixPartial 13 105746) = some ⟨13, 2, 0, 341270, 105746, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_105746_341270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105746 ⟨341270, by decide⟩ :=
  accepted_of_selected 13 105746 ⟨341270, by decide⟩ ⟨13, 2, 0, 341270, 105746, 1729, 16384⟩
    (by decide) selected_cut_12971

theorem selected_cut_12972 : selected 8 ⟨341280, by decide⟩
    (prefixPartial 13 105747) = some ⟨13, 2, 0, 341280, 105747, 805, 16384⟩ := by
  decide +kernel

theorem context_13_105747_341280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105747 ⟨341280, by decide⟩ :=
  accepted_of_selected 13 105747 ⟨341280, by decide⟩ ⟨13, 2, 0, 341280, 105747, 805, 16384⟩
    (by decide) selected_cut_12972

theorem unmarked_context_12_26436_341281 : frontier 9 ⟨341281, by decide⟩
    (prefixCache 12 26436) (prefixPartial 12 26436) = false := by
  decide +kernel

theorem node_context_12_26436_341281 : EJMOriginalGlobalDAGData.nodes 9 ⟨341281, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨341243, by decide⟩,⟨341270, by decide⟩,⟨341280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26436_341281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26436 ⟨341281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26436
    ⟨341281, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨341243, by decide⟩,⟨341270, by decide⟩,⟨341280, by decide⟩]) unmarked_context_12_26436_341281 node_context_12_26436_341281
  intro a
  fin_cases a
  · exact context_13_105744_3444
  · exact context_13_105745_341243
  · exact context_13_105746_341270
  · exact context_13_105747_341280

theorem selected_cut_12973 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105748) = some ⟨13, 1, 0, 3444, 105748, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105748_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105748 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105748 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105748, 1, 16384⟩
    (by decide) selected_cut_12973

theorem selected_cut_12974 : selected 8 ⟨341349, by decide⟩
    (prefixPartial 13 105749) = some ⟨13, 2, 0, 341349, 105749, 3789, 16384⟩ := by
  decide +kernel

theorem context_13_105749_341349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105749 ⟨341349, by decide⟩ :=
  accepted_of_selected 13 105749 ⟨341349, by decide⟩ ⟨13, 2, 0, 341349, 105749, 3789, 16384⟩
    (by decide) selected_cut_12974

theorem selected_cut_12975 : selected 8 ⟨341394, by decide⟩
    (prefixPartial 13 105750) = some ⟨13, 2, 0, 341394, 105750, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_105750_341394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105750 ⟨341394, by decide⟩ :=
  accepted_of_selected 13 105750 ⟨341394, by decide⟩ ⟨13, 2, 0, 341394, 105750, 2605, 16384⟩
    (by decide) selected_cut_12975

theorem selected_cut_12976 : selected 8 ⟨341407, by decide⟩
    (prefixPartial 13 105751) = some ⟨13, 2, 0, 341407, 105751, 985, 16384⟩ := by
  decide +kernel

theorem context_13_105751_341407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105751 ⟨341407, by decide⟩ :=
  accepted_of_selected 13 105751 ⟨341407, by decide⟩ ⟨13, 2, 0, 341407, 105751, 985, 16384⟩
    (by decide) selected_cut_12976

theorem unmarked_context_12_26437_341408 : frontier 9 ⟨341408, by decide⟩
    (prefixCache 12 26437) (prefixPartial 12 26437) = false := by
  decide +kernel

theorem node_context_12_26437_341408 : EJMOriginalGlobalDAGData.nodes 9 ⟨341408, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨341349, by decide⟩,⟨341394, by decide⟩,⟨341407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26437_341408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26437 ⟨341408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26437
    ⟨341408, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨341349, by decide⟩,⟨341394, by decide⟩,⟨341407, by decide⟩]) unmarked_context_12_26437_341408 node_context_12_26437_341408
  intro a
  fin_cases a
  · exact context_13_105748_3444
  · exact context_13_105749_341349
  · exact context_13_105750_341394
  · exact context_13_105751_341407

theorem selected_cut_12977 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105752) = some ⟨13, 1, 0, 3444, 105752, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105752_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105752 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105752 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105752, 1, 16384⟩
    (by decide) selected_cut_12977

theorem selected_cut_12978 : selected 8 ⟨341450, by decide⟩
    (prefixPartial 13 105753) = some ⟨13, 2, 0, 341450, 105753, 2817, 16384⟩ := by
  decide +kernel

theorem context_13_105753_341450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105753 ⟨341450, by decide⟩ :=
  accepted_of_selected 13 105753 ⟨341450, by decide⟩ ⟨13, 2, 0, 341450, 105753, 2817, 16384⟩
    (by decide) selected_cut_12978

theorem selected_cut_12979 : selected 8 ⟨341477, by decide⟩
    (prefixPartial 13 105754) = some ⟨13, 2, 0, 341477, 105754, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_105754_341477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105754 ⟨341477, by decide⟩ :=
  accepted_of_selected 13 105754 ⟨341477, by decide⟩ ⟨13, 2, 0, 341477, 105754, 1965, 16384⟩
    (by decide) selected_cut_12979

theorem selected_cut_12980 : selected 8 ⟨341488, by decide⟩
    (prefixPartial 13 105755) = some ⟨13, 2, 0, 341488, 105755, 817, 16384⟩ := by
  decide +kernel

theorem context_13_105755_341488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105755 ⟨341488, by decide⟩ :=
  accepted_of_selected 13 105755 ⟨341488, by decide⟩ ⟨13, 2, 0, 341488, 105755, 817, 16384⟩
    (by decide) selected_cut_12980

theorem unmarked_context_12_26438_341489 : frontier 9 ⟨341489, by decide⟩
    (prefixCache 12 26438) (prefixPartial 12 26438) = false := by
  decide +kernel

theorem node_context_12_26438_341489 : EJMOriginalGlobalDAGData.nodes 9 ⟨341489, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨341450, by decide⟩,⟨341477, by decide⟩,⟨341488, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26438_341489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26438 ⟨341489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26438
    ⟨341489, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨341450, by decide⟩,⟨341477, by decide⟩,⟨341488, by decide⟩]) unmarked_context_12_26438_341489 node_context_12_26438_341489
  intro a
  fin_cases a
  · exact context_13_105752_3444
  · exact context_13_105753_341450
  · exact context_13_105754_341477
  · exact context_13_105755_341488

theorem selected_cut_12981 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105756) = some ⟨13, 1, 0, 3444, 105756, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105756_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105756 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105756 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105756, 1, 16384⟩
    (by decide) selected_cut_12981

theorem selected_cut_12982 : selected 8 ⟨341544, by decide⟩
    (prefixPartial 13 105757) = some ⟨13, 2, 0, 341544, 105757, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_105757_341544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105757 ⟨341544, by decide⟩ :=
  accepted_of_selected 13 105757 ⟨341544, by decide⟩ ⟨13, 2, 0, 341544, 105757, 2813, 16384⟩
    (by decide) selected_cut_12982

theorem selected_cut_12983 : selected 8 ⟨341567, by decide⟩
    (prefixPartial 13 105758) = some ⟨13, 2, 0, 341567, 105758, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_105758_341567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105758 ⟨341567, by decide⟩ :=
  accepted_of_selected 13 105758 ⟨341567, by decide⟩ ⟨13, 2, 0, 341567, 105758, 1917, 16384⟩
    (by decide) selected_cut_12983

theorem selected_cut_12984 : selected 8 ⟨341577, by decide⟩
    (prefixPartial 13 105759) = some ⟨13, 2, 0, 341577, 105759, 713, 16384⟩ := by
  decide +kernel

theorem context_13_105759_341577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105759 ⟨341577, by decide⟩ :=
  accepted_of_selected 13 105759 ⟨341577, by decide⟩ ⟨13, 2, 0, 341577, 105759, 713, 16384⟩
    (by decide) selected_cut_12984

theorem unmarked_context_12_26439_341578 : frontier 9 ⟨341578, by decide⟩
    (prefixCache 12 26439) (prefixPartial 12 26439) = false := by
  decide +kernel

theorem node_context_12_26439_341578 : EJMOriginalGlobalDAGData.nodes 9 ⟨341578, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨341544, by decide⟩,⟨341567, by decide⟩,⟨341577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26439_341578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26439 ⟨341578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26439
    ⟨341578, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨341544, by decide⟩,⟨341567, by decide⟩,⟨341577, by decide⟩]) unmarked_context_12_26439_341578 node_context_12_26439_341578
  intro a
  fin_cases a
  · exact context_13_105756_3444
  · exact context_13_105757_341544
  · exact context_13_105758_341567
  · exact context_13_105759_341577

theorem unmarked_context_11_6609_341579 : frontier 10 ⟨341579, by decide⟩
    (prefixCache 11 6609) (prefixPartial 11 6609) = false := by
  decide +kernel

theorem node_context_11_6609_341579 : EJMOriginalGlobalDAGData.nodes 10 ⟨341579, by decide⟩ =
    .split (coordinate 11) (![⟨341281, by decide⟩,⟨341408, by decide⟩,⟨341489, by decide⟩,⟨341578, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6609_341579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6609 ⟨341579, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6609
    ⟨341579, by decide⟩ (by decide) (![⟨341281, by decide⟩,⟨341408, by decide⟩,⟨341489, by decide⟩,⟨341578, by decide⟩]) unmarked_context_11_6609_341579 node_context_11_6609_341579
  intro a
  fin_cases a
  · exact context_12_26436_341281
  · exact context_12_26437_341408
  · exact context_12_26438_341489
  · exact context_12_26439_341578

theorem selected_cut_12985 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105760) = some ⟨13, 1, 0, 3444, 105760, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105760_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105760 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105760 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105760, 1, 16384⟩
    (by decide) selected_cut_12985

theorem selected_cut_12986 : selected 8 ⟨341623, by decide⟩
    (prefixPartial 13 105761) = some ⟨13, 2, 0, 341623, 105761, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_105761_341623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105761 ⟨341623, by decide⟩ :=
  accepted_of_selected 13 105761 ⟨341623, by decide⟩ ⟨13, 2, 0, 341623, 105761, 2629, 16384⟩
    (by decide) selected_cut_12986

theorem selected_cut_12987 : selected 8 ⟨341655, by decide⟩
    (prefixPartial 13 105762) = some ⟨13, 2, 0, 341655, 105762, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_105762_341655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105762 ⟨341655, by decide⟩ :=
  accepted_of_selected 13 105762 ⟨341655, by decide⟩ ⟨13, 2, 0, 341655, 105762, 1977, 16384⟩
    (by decide) selected_cut_12987

theorem selected_cut_12988 : selected 8 ⟨341665, by decide⟩
    (prefixPartial 13 105763) = some ⟨13, 2, 0, 341665, 105763, 889, 16384⟩ := by
  decide +kernel

theorem context_13_105763_341665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105763 ⟨341665, by decide⟩ :=
  accepted_of_selected 13 105763 ⟨341665, by decide⟩ ⟨13, 2, 0, 341665, 105763, 889, 16384⟩
    (by decide) selected_cut_12988

theorem unmarked_context_12_26440_341666 : frontier 9 ⟨341666, by decide⟩
    (prefixCache 12 26440) (prefixPartial 12 26440) = false := by
  decide +kernel

theorem node_context_12_26440_341666 : EJMOriginalGlobalDAGData.nodes 9 ⟨341666, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨341623, by decide⟩,⟨341655, by decide⟩,⟨341665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26440_341666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26440 ⟨341666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26440
    ⟨341666, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨341623, by decide⟩,⟨341655, by decide⟩,⟨341665, by decide⟩]) unmarked_context_12_26440_341666 node_context_12_26440_341666
  intro a
  fin_cases a
  · exact context_13_105760_3444
  · exact context_13_105761_341623
  · exact context_13_105762_341655
  · exact context_13_105763_341665

theorem selected_cut_12989 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105764) = some ⟨13, 1, 0, 3444, 105764, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105764_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105764 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105764 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105764, 1, 16384⟩
    (by decide) selected_cut_12989

theorem selected_cut_12990 : selected 8 ⟨341747, by decide⟩
    (prefixPartial 13 105765) = some ⟨13, 2, 0, 341747, 105765, 4081, 16384⟩ := by
  decide +kernel

theorem context_13_105765_341747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105765 ⟨341747, by decide⟩ :=
  accepted_of_selected 13 105765 ⟨341747, by decide⟩ ⟨13, 2, 0, 341747, 105765, 4081, 16384⟩
    (by decide) selected_cut_12990

theorem selected_cut_12991 : selected 8 ⟨341796, by decide⟩
    (prefixPartial 13 105766) = some ⟨13, 2, 0, 341796, 105766, 2861, 16384⟩ := by
  decide +kernel

theorem context_13_105766_341796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105766 ⟨341796, by decide⟩ :=
  accepted_of_selected 13 105766 ⟨341796, by decide⟩ ⟨13, 2, 0, 341796, 105766, 2861, 16384⟩
    (by decide) selected_cut_12991

theorem selected_cut_12992 : selected 8 ⟨341827, by decide⟩
    (prefixPartial 13 105767) = some ⟨13, 2, 0, 341827, 105767, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_105767_341827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105767 ⟨341827, by decide⟩ :=
  accepted_of_selected 13 105767 ⟨341827, by decide⟩ ⟨13, 2, 0, 341827, 105767, 1241, 16384⟩
    (by decide) selected_cut_12992

theorem unmarked_context_12_26441_341828 : frontier 9 ⟨341828, by decide⟩
    (prefixCache 12 26441) (prefixPartial 12 26441) = false := by
  decide +kernel

theorem node_context_12_26441_341828 : EJMOriginalGlobalDAGData.nodes 9 ⟨341828, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨341747, by decide⟩,⟨341796, by decide⟩,⟨341827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26441_341828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26441 ⟨341828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26441
    ⟨341828, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨341747, by decide⟩,⟨341796, by decide⟩,⟨341827, by decide⟩]) unmarked_context_12_26441_341828 node_context_12_26441_341828
  intro a
  fin_cases a
  · exact context_13_105764_3444
  · exact context_13_105765_341747
  · exact context_13_105766_341796
  · exact context_13_105767_341827

theorem selected_cut_12993 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105768) = some ⟨13, 1, 0, 3444, 105768, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105768_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105768 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105768 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105768, 1, 16384⟩
    (by decide) selected_cut_12993

theorem selected_cut_12994 : selected 8 ⟨341869, by decide⟩
    (prefixPartial 13 105769) = some ⟨13, 2, 0, 341869, 105769, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_105769_341869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105769 ⟨341869, by decide⟩ :=
  accepted_of_selected 13 105769 ⟨341869, by decide⟩ ⟨13, 2, 0, 341869, 105769, 2613, 16384⟩
    (by decide) selected_cut_12994

theorem selected_cut_12995 : selected 8 ⟨341890, by decide⟩
    (prefixPartial 13 105770) = some ⟨13, 2, 0, 341890, 105770, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_105770_341890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105770 ⟨341890, by decide⟩ :=
  accepted_of_selected 13 105770 ⟨341890, by decide⟩ ⟨13, 2, 0, 341890, 105770, 1941, 16384⟩
    (by decide) selected_cut_12995

theorem selected_cut_12996 : selected 8 ⟨341900, by decide⟩
    (prefixPartial 13 105771) = some ⟨13, 2, 0, 341900, 105771, 865, 16384⟩ := by
  decide +kernel

theorem context_13_105771_341900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105771 ⟨341900, by decide⟩ :=
  accepted_of_selected 13 105771 ⟨341900, by decide⟩ ⟨13, 2, 0, 341900, 105771, 865, 16384⟩
    (by decide) selected_cut_12996

theorem unmarked_context_12_26442_341901 : frontier 9 ⟨341901, by decide⟩
    (prefixCache 12 26442) (prefixPartial 12 26442) = false := by
  decide +kernel

theorem node_context_12_26442_341901 : EJMOriginalGlobalDAGData.nodes 9 ⟨341901, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨341869, by decide⟩,⟨341890, by decide⟩,⟨341900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26442_341901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26442 ⟨341901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26442
    ⟨341901, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨341869, by decide⟩,⟨341890, by decide⟩,⟨341900, by decide⟩]) unmarked_context_12_26442_341901 node_context_12_26442_341901
  intro a
  fin_cases a
  · exact context_13_105768_3444
  · exact context_13_105769_341869
  · exact context_13_105770_341890
  · exact context_13_105771_341900

theorem selected_cut_12997 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105772) = some ⟨13, 1, 0, 3444, 105772, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105772_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105772 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105772 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105772, 1, 16384⟩
    (by decide) selected_cut_12997

theorem selected_cut_12998 : selected 8 ⟨341950, by decide⟩
    (prefixPartial 13 105773) = some ⟨13, 2, 0, 341950, 105773, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_105773_341950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105773 ⟨341950, by decide⟩ :=
  accepted_of_selected 13 105773 ⟨341950, by decide⟩ ⟨13, 2, 0, 341950, 105773, 2745, 16384⟩
    (by decide) selected_cut_12998

theorem selected_cut_12999 : selected 8 ⟨341970, by decide⟩
    (prefixPartial 13 105774) = some ⟨13, 2, 0, 341970, 105774, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_105774_341970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105774 ⟨341970, by decide⟩ :=
  accepted_of_selected 13 105774 ⟨341970, by decide⟩ ⟨13, 2, 0, 341970, 105774, 1709, 16384⟩
    (by decide) selected_cut_12999

theorem selected_cut_13000 : selected 8 ⟨341980, by decide⟩
    (prefixPartial 13 105775) = some ⟨13, 2, 0, 341980, 105775, 717, 16384⟩ := by
  decide +kernel

theorem context_13_105775_341980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105775 ⟨341980, by decide⟩ :=
  accepted_of_selected 13 105775 ⟨341980, by decide⟩ ⟨13, 2, 0, 341980, 105775, 717, 16384⟩
    (by decide) selected_cut_13000

theorem unmarked_context_12_26443_341981 : frontier 9 ⟨341981, by decide⟩
    (prefixCache 12 26443) (prefixPartial 12 26443) = false := by
  decide +kernel

theorem node_context_12_26443_341981 : EJMOriginalGlobalDAGData.nodes 9 ⟨341981, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨341950, by decide⟩,⟨341970, by decide⟩,⟨341980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26443_341981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26443 ⟨341981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26443
    ⟨341981, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨341950, by decide⟩,⟨341970, by decide⟩,⟨341980, by decide⟩]) unmarked_context_12_26443_341981 node_context_12_26443_341981
  intro a
  fin_cases a
  · exact context_13_105772_3444
  · exact context_13_105773_341950
  · exact context_13_105774_341970
  · exact context_13_105775_341980

theorem unmarked_context_11_6610_341982 : frontier 10 ⟨341982, by decide⟩
    (prefixCache 11 6610) (prefixPartial 11 6610) = false := by
  decide +kernel

theorem node_context_11_6610_341982 : EJMOriginalGlobalDAGData.nodes 10 ⟨341982, by decide⟩ =
    .split (coordinate 11) (![⟨341666, by decide⟩,⟨341828, by decide⟩,⟨341901, by decide⟩,⟨341981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6610_341982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6610 ⟨341982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6610
    ⟨341982, by decide⟩ (by decide) (![⟨341666, by decide⟩,⟨341828, by decide⟩,⟨341901, by decide⟩,⟨341981, by decide⟩]) unmarked_context_11_6610_341982 node_context_11_6610_341982
  intro a
  fin_cases a
  · exact context_12_26440_341666
  · exact context_12_26441_341828
  · exact context_12_26442_341901
  · exact context_12_26443_341981

theorem selected_cut_13001 : selected 9 ⟨342032, by decide⟩
    (prefixPartial 12 26444) = some ⟨12, 2, 0, 342032, 26444, 4033, 65536⟩ := by
  decide +kernel

theorem context_12_26444_342032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26444 ⟨342032, by decide⟩ :=
  accepted_of_selected 12 26444 ⟨342032, by decide⟩ ⟨12, 2, 0, 342032, 26444, 4033, 65536⟩
    (by decide) selected_cut_13001

theorem selected_cut_13002 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105780) = some ⟨13, 1, 0, 3444, 105780, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105780_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105780 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105780 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105780, 1, 16384⟩
    (by decide) selected_cut_13002

theorem selected_cut_13003 : selected 8 ⟨342085, by decide⟩
    (prefixPartial 13 105781) = some ⟨13, 2, 0, 342085, 105781, 2957, 16384⟩ := by
  decide +kernel

theorem context_13_105781_342085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105781 ⟨342085, by decide⟩ :=
  accepted_of_selected 13 105781 ⟨342085, by decide⟩ ⟨13, 2, 0, 342085, 105781, 2957, 16384⟩
    (by decide) selected_cut_13003

theorem selected_cut_13004 : selected 8 ⟨342140, by decide⟩
    (prefixPartial 13 105782) = some ⟨13, 2, 0, 342140, 105782, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_105782_342140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105782 ⟨342140, by decide⟩ :=
  accepted_of_selected 13 105782 ⟨342140, by decide⟩ ⟨13, 2, 0, 342140, 105782, 2601, 16384⟩
    (by decide) selected_cut_13004

theorem selected_cut_13005 : selected 8 ⟨342154, by decide⟩
    (prefixPartial 13 105783) = some ⟨13, 2, 0, 342154, 105783, 969, 16384⟩ := by
  decide +kernel

theorem context_13_105783_342154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105783 ⟨342154, by decide⟩ :=
  accepted_of_selected 13 105783 ⟨342154, by decide⟩ ⟨13, 2, 0, 342154, 105783, 969, 16384⟩
    (by decide) selected_cut_13005

theorem unmarked_context_12_26445_342155 : frontier 9 ⟨342155, by decide⟩
    (prefixCache 12 26445) (prefixPartial 12 26445) = false := by
  decide +kernel

theorem node_context_12_26445_342155 : EJMOriginalGlobalDAGData.nodes 9 ⟨342155, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨342085, by decide⟩,⟨342140, by decide⟩,⟨342154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26445_342155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26445 ⟨342155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26445
    ⟨342155, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨342085, by decide⟩,⟨342140, by decide⟩,⟨342154, by decide⟩]) unmarked_context_12_26445_342155 node_context_12_26445_342155
  intro a
  fin_cases a
  · exact context_13_105780_3444
  · exact context_13_105781_342085
  · exact context_13_105782_342140
  · exact context_13_105783_342154

theorem selected_cut_13006 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105784) = some ⟨13, 1, 0, 3444, 105784, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105784_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105784 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105784 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105784, 1, 16384⟩
    (by decide) selected_cut_13006

theorem selected_cut_13007 : selected 8 ⟨342185, by decide⟩
    (prefixPartial 13 105785) = some ⟨13, 2, 0, 342185, 105785, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_105785_342185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105785 ⟨342185, by decide⟩ :=
  accepted_of_selected 13 105785 ⟨342185, by decide⟩ ⟨13, 2, 0, 342185, 105785, 2181, 16384⟩
    (by decide) selected_cut_13007

theorem selected_cut_13008 : selected 8 ⟨342206, by decide⟩
    (prefixPartial 13 105786) = some ⟨13, 2, 0, 342206, 105786, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_105786_342206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105786 ⟨342206, by decide⟩ :=
  accepted_of_selected 13 105786 ⟨342206, by decide⟩ ⟨13, 2, 0, 342206, 105786, 1533, 16384⟩
    (by decide) selected_cut_13008

theorem selected_cut_13009 : selected 8 ⟨342212, by decide⟩
    (prefixPartial 13 105787) = some ⟨13, 2, 0, 342212, 105787, 653, 16384⟩ := by
  decide +kernel

theorem context_13_105787_342212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105787 ⟨342212, by decide⟩ :=
  accepted_of_selected 13 105787 ⟨342212, by decide⟩ ⟨13, 2, 0, 342212, 105787, 653, 16384⟩
    (by decide) selected_cut_13009

theorem unmarked_context_12_26446_342213 : frontier 9 ⟨342213, by decide⟩
    (prefixCache 12 26446) (prefixPartial 12 26446) = false := by
  decide +kernel

theorem node_context_12_26446_342213 : EJMOriginalGlobalDAGData.nodes 9 ⟨342213, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨342185, by decide⟩,⟨342206, by decide⟩,⟨342212, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26446_342213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26446 ⟨342213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26446
    ⟨342213, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨342185, by decide⟩,⟨342206, by decide⟩,⟨342212, by decide⟩]) unmarked_context_12_26446_342213 node_context_12_26446_342213
  intro a
  fin_cases a
  · exact context_13_105784_3444
  · exact context_13_105785_342185
  · exact context_13_105786_342206
  · exact context_13_105787_342212

theorem selected_cut_13010 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105788) = some ⟨13, 1, 0, 3444, 105788, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105788_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105788 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105788 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105788, 1, 16384⟩
    (by decide) selected_cut_13010

theorem selected_cut_13011 : selected 8 ⟨342284, by decide⟩
    (prefixPartial 13 105789) = some ⟨13, 2, 0, 342284, 105789, 3385, 16384⟩ := by
  decide +kernel

theorem context_13_105789_342284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105789 ⟨342284, by decide⟩ :=
  accepted_of_selected 13 105789 ⟨342284, by decide⟩ ⟨13, 2, 0, 342284, 105789, 3385, 16384⟩
    (by decide) selected_cut_13011

theorem selected_cut_13012 : selected 8 ⟨342332, by decide⟩
    (prefixPartial 13 105790) = some ⟨13, 2, 0, 342332, 105790, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_105790_342332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105790 ⟨342332, by decide⟩ :=
  accepted_of_selected 13 105790 ⟨342332, by decide⟩ ⟨13, 2, 0, 342332, 105790, 2601, 16384⟩
    (by decide) selected_cut_13012

theorem selected_cut_13013 : selected 8 ⟨342362, by decide⟩
    (prefixPartial 13 105791) = some ⟨13, 2, 0, 342362, 105791, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_105791_342362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105791 ⟨342362, by decide⟩ :=
  accepted_of_selected 13 105791 ⟨342362, by decide⟩ ⟨13, 2, 0, 342362, 105791, 1117, 16384⟩
    (by decide) selected_cut_13013

theorem unmarked_context_12_26447_342363 : frontier 9 ⟨342363, by decide⟩
    (prefixCache 12 26447) (prefixPartial 12 26447) = false := by
  decide +kernel

theorem node_context_12_26447_342363 : EJMOriginalGlobalDAGData.nodes 9 ⟨342363, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨342284, by decide⟩,⟨342332, by decide⟩,⟨342362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26447_342363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26447 ⟨342363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26447
    ⟨342363, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨342284, by decide⟩,⟨342332, by decide⟩,⟨342362, by decide⟩]) unmarked_context_12_26447_342363 node_context_12_26447_342363
  intro a
  fin_cases a
  · exact context_13_105788_3444
  · exact context_13_105789_342284
  · exact context_13_105790_342332
  · exact context_13_105791_342362

theorem unmarked_context_11_6611_342364 : frontier 10 ⟨342364, by decide⟩
    (prefixCache 11 6611) (prefixPartial 11 6611) = false := by
  decide +kernel

theorem node_context_11_6611_342364 : EJMOriginalGlobalDAGData.nodes 10 ⟨342364, by decide⟩ =
    .split (coordinate 11) (![⟨342032, by decide⟩,⟨342155, by decide⟩,⟨342213, by decide⟩,⟨342363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6611_342364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6611 ⟨342364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6611
    ⟨342364, by decide⟩ (by decide) (![⟨342032, by decide⟩,⟨342155, by decide⟩,⟨342213, by decide⟩,⟨342363, by decide⟩]) unmarked_context_11_6611_342364 node_context_11_6611_342364
  intro a
  fin_cases a
  · exact context_12_26444_342032
  · exact context_12_26445_342155
  · exact context_12_26446_342213
  · exact context_12_26447_342363

theorem unmarked_context_10_1652_342365 : frontier 11 ⟨342365, by decide⟩
    (prefixCache 10 1652) (prefixPartial 10 1652) = false := by
  decide +kernel

theorem node_context_10_1652_342365 : EJMOriginalGlobalDAGData.nodes 11 ⟨342365, by decide⟩ =
    .split (coordinate 10) (![⟨341207, by decide⟩,⟨341579, by decide⟩,⟨341982, by decide⟩,⟨342364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1652_342365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1652 ⟨342365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1652
    ⟨342365, by decide⟩ (by decide) (![⟨341207, by decide⟩,⟨341579, by decide⟩,⟨341982, by decide⟩,⟨342364, by decide⟩]) unmarked_context_10_1652_342365 node_context_10_1652_342365
  intro a
  fin_cases a
  · exact context_11_6608_341207
  · exact context_11_6609_341579
  · exact context_11_6610_341982
  · exact context_11_6611_342364

theorem selected_cut_13014 : selected 9 ⟨342407, by decide⟩
    (prefixPartial 12 26448) = some ⟨12, 2, 0, 342407, 26448, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_26448_342407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26448 ⟨342407, by decide⟩ :=
  accepted_of_selected 12 26448 ⟨342407, by decide⟩ ⟨12, 2, 0, 342407, 26448, 3665, 65536⟩
    (by decide) selected_cut_13014

theorem selected_cut_13015 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 26449) = some ⟨12, 1, 0, 170504, 26449, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26449_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26449 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 26449 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 26449, 1, 65536⟩
    (by decide) selected_cut_13015

theorem selected_cut_13016 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105800) = some ⟨13, 1, 0, 3444, 105800, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105800_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105800 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105800 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105800, 1, 16384⟩
    (by decide) selected_cut_13016

theorem selected_cut_13017 : selected 8 ⟨342436, by decide⟩
    (prefixPartial 13 105801) = some ⟨13, 2, 0, 342436, 105801, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_105801_342436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105801 ⟨342436, by decide⟩ :=
  accepted_of_selected 13 105801 ⟨342436, by decide⟩ ⟨13, 2, 0, 342436, 105801, 1881, 16384⟩
    (by decide) selected_cut_13017

theorem selected_cut_13018 : selected 8 ⟨342467, by decide⟩
    (prefixPartial 13 105802) = some ⟨13, 2, 0, 342467, 105802, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_105802_342467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105802 ⟨342467, by decide⟩ :=
  accepted_of_selected 13 105802 ⟨342467, by decide⟩ ⟨13, 2, 0, 342467, 105802, 1865, 16384⟩
    (by decide) selected_cut_13018

theorem selected_cut_13019 : selected 8 ⟨342474, by decide⟩
    (prefixPartial 13 105803) = some ⟨13, 2, 0, 342474, 105803, 649, 16384⟩ := by
  decide +kernel

theorem context_13_105803_342474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105803 ⟨342474, by decide⟩ :=
  accepted_of_selected 13 105803 ⟨342474, by decide⟩ ⟨13, 2, 0, 342474, 105803, 649, 16384⟩
    (by decide) selected_cut_13019

theorem unmarked_context_12_26450_342475 : frontier 9 ⟨342475, by decide⟩
    (prefixCache 12 26450) (prefixPartial 12 26450) = false := by
  decide +kernel

theorem node_context_12_26450_342475 : EJMOriginalGlobalDAGData.nodes 9 ⟨342475, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨342436, by decide⟩,⟨342467, by decide⟩,⟨342474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26450_342475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26450 ⟨342475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26450
    ⟨342475, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨342436, by decide⟩,⟨342467, by decide⟩,⟨342474, by decide⟩]) unmarked_context_12_26450_342475 node_context_12_26450_342475
  intro a
  fin_cases a
  · exact context_13_105800_3444
  · exact context_13_105801_342436
  · exact context_13_105802_342467
  · exact context_13_105803_342474

theorem selected_cut_13020 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105804) = some ⟨13, 1, 0, 3444, 105804, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105804_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105804 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105804 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105804, 1, 16384⟩
    (by decide) selected_cut_13020

theorem selected_cut_13021 : selected 8 ⟨342496, by decide⟩
    (prefixPartial 13 105805) = some ⟨13, 2, 0, 342496, 105805, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_105805_342496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105805 ⟨342496, by decide⟩ :=
  accepted_of_selected 13 105805 ⟨342496, by decide⟩ ⟨13, 2, 0, 342496, 105805, 1897, 16384⟩
    (by decide) selected_cut_13021

theorem selected_cut_13022 : selected 8 ⟨342516, by decide⟩
    (prefixPartial 13 105806) = some ⟨13, 2, 0, 342516, 105806, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_105806_342516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105806 ⟨342516, by decide⟩ :=
  accepted_of_selected 13 105806 ⟨342516, by decide⟩ ⟨13, 2, 0, 342516, 105806, 1769, 16384⟩
    (by decide) selected_cut_13022

theorem selected_cut_13023 : selected 8 ⟨342523, by decide⟩
    (prefixPartial 13 105807) = some ⟨13, 2, 0, 342523, 105807, 625, 16384⟩ := by
  decide +kernel

theorem context_13_105807_342523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105807 ⟨342523, by decide⟩ :=
  accepted_of_selected 13 105807 ⟨342523, by decide⟩ ⟨13, 2, 0, 342523, 105807, 625, 16384⟩
    (by decide) selected_cut_13023

theorem unmarked_context_12_26451_342524 : frontier 9 ⟨342524, by decide⟩
    (prefixCache 12 26451) (prefixPartial 12 26451) = false := by
  decide +kernel

theorem node_context_12_26451_342524 : EJMOriginalGlobalDAGData.nodes 9 ⟨342524, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨342496, by decide⟩,⟨342516, by decide⟩,⟨342523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26451_342524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26451 ⟨342524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26451
    ⟨342524, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨342496, by decide⟩,⟨342516, by decide⟩,⟨342523, by decide⟩]) unmarked_context_12_26451_342524 node_context_12_26451_342524
  intro a
  fin_cases a
  · exact context_13_105804_3444
  · exact context_13_105805_342496
  · exact context_13_105806_342516
  · exact context_13_105807_342523

theorem unmarked_context_11_6612_342525 : frontier 10 ⟨342525, by decide⟩
    (prefixCache 11 6612) (prefixPartial 11 6612) = false := by
  decide +kernel

theorem node_context_11_6612_342525 : EJMOriginalGlobalDAGData.nodes 10 ⟨342525, by decide⟩ =
    .split (coordinate 11) (![⟨342407, by decide⟩,⟨170504, by decide⟩,⟨342475, by decide⟩,⟨342524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6612_342525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6612 ⟨342525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6612
    ⟨342525, by decide⟩ (by decide) (![⟨342407, by decide⟩,⟨170504, by decide⟩,⟨342475, by decide⟩,⟨342524, by decide⟩]) unmarked_context_11_6612_342525 node_context_11_6612_342525
  intro a
  fin_cases a
  · exact context_12_26448_342407
  · exact context_12_26449_170504
  · exact context_12_26450_342475
  · exact context_12_26451_342524

theorem selected_cut_13024 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 26452) = some ⟨12, 1, 0, 308705, 26452, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26452_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26452 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 26452 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 26452, 1, 65536⟩
    (by decide) selected_cut_13024

theorem selected_cut_13025 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 26453) = some ⟨12, 1, 0, 170504, 26453, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26453_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26453 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 26453 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 26453, 1, 65536⟩
    (by decide) selected_cut_13025

theorem selected_cut_13026 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105816) = some ⟨13, 1, 0, 3444, 105816, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105816_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105816 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105816 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105816, 1, 16384⟩
    (by decide) selected_cut_13026

theorem selected_cut_13027 : selected 8 ⟨342598, by decide⟩
    (prefixPartial 13 105817) = some ⟨13, 2, 0, 342598, 105817, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_105817_342598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105817 ⟨342598, by decide⟩ :=
  accepted_of_selected 13 105817 ⟨342598, by decide⟩ ⟨13, 2, 0, 342598, 105817, 3033, 16384⟩
    (by decide) selected_cut_13027

theorem selected_cut_13028 : selected 8 ⟨342651, by decide⟩
    (prefixPartial 13 105818) = some ⟨13, 2, 0, 342651, 105818, 2609, 16384⟩ := by
  decide +kernel

theorem context_13_105818_342651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105818 ⟨342651, by decide⟩ :=
  accepted_of_selected 13 105818 ⟨342651, by decide⟩ ⟨13, 2, 0, 342651, 105818, 2609, 16384⟩
    (by decide) selected_cut_13028

theorem selected_cut_13029 : selected 8 ⟨342670, by decide⟩
    (prefixPartial 13 105819) = some ⟨13, 2, 0, 342670, 105819, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_105819_342670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105819 ⟨342670, by decide⟩ :=
  accepted_of_selected 13 105819 ⟨342670, by decide⟩ ⟨13, 2, 0, 342670, 105819, 1109, 16384⟩
    (by decide) selected_cut_13029

theorem unmarked_context_12_26454_342671 : frontier 9 ⟨342671, by decide⟩
    (prefixCache 12 26454) (prefixPartial 12 26454) = false := by
  decide +kernel

theorem node_context_12_26454_342671 : EJMOriginalGlobalDAGData.nodes 9 ⟨342671, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨342598, by decide⟩,⟨342651, by decide⟩,⟨342670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26454_342671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26454 ⟨342671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26454
    ⟨342671, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨342598, by decide⟩,⟨342651, by decide⟩,⟨342670, by decide⟩]) unmarked_context_12_26454_342671 node_context_12_26454_342671
  intro a
  fin_cases a
  · exact context_13_105816_3444
  · exact context_13_105817_342598
  · exact context_13_105818_342651
  · exact context_13_105819_342670

theorem selected_cut_13030 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105820) = some ⟨13, 1, 0, 3444, 105820, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105820_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105820 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105820 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105820, 1, 16384⟩
    (by decide) selected_cut_13030

theorem selected_cut_13031 : selected 8 ⟨342731, by decide⟩
    (prefixPartial 13 105821) = some ⟨13, 2, 0, 342731, 105821, 2797, 16384⟩ := by
  decide +kernel

theorem context_13_105821_342731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105821 ⟨342731, by decide⟩ :=
  accepted_of_selected 13 105821 ⟨342731, by decide⟩ ⟨13, 2, 0, 342731, 105821, 2797, 16384⟩
    (by decide) selected_cut_13031

theorem selected_cut_13032 : selected 8 ⟨342772, by decide⟩
    (prefixPartial 13 105822) = some ⟨13, 2, 0, 342772, 105822, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_105822_342772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105822 ⟨342772, by decide⟩ :=
  accepted_of_selected 13 105822 ⟨342772, by decide⟩ ⟨13, 2, 0, 342772, 105822, 2305, 16384⟩
    (by decide) selected_cut_13032

theorem selected_cut_13033 : selected 8 ⟨342780, by decide⟩
    (prefixPartial 13 105823) = some ⟨13, 2, 0, 342780, 105823, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_105823_342780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105823 ⟨342780, by decide⟩ :=
  accepted_of_selected 13 105823 ⟨342780, by decide⟩ ⟨13, 2, 0, 342780, 105823, 1001, 16384⟩
    (by decide) selected_cut_13033

theorem unmarked_context_12_26455_342781 : frontier 9 ⟨342781, by decide⟩
    (prefixCache 12 26455) (prefixPartial 12 26455) = false := by
  decide +kernel

theorem node_context_12_26455_342781 : EJMOriginalGlobalDAGData.nodes 9 ⟨342781, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨342731, by decide⟩,⟨342772, by decide⟩,⟨342780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26455_342781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26455 ⟨342781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26455
    ⟨342781, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨342731, by decide⟩,⟨342772, by decide⟩,⟨342780, by decide⟩]) unmarked_context_12_26455_342781 node_context_12_26455_342781
  intro a
  fin_cases a
  · exact context_13_105820_3444
  · exact context_13_105821_342731
  · exact context_13_105822_342772
  · exact context_13_105823_342780

theorem unmarked_context_11_6613_342782 : frontier 10 ⟨342782, by decide⟩
    (prefixCache 11 6613) (prefixPartial 11 6613) = false := by
  decide +kernel

theorem node_context_11_6613_342782 : EJMOriginalGlobalDAGData.nodes 10 ⟨342782, by decide⟩ =
    .split (coordinate 11) (![⟨308705, by decide⟩,⟨170504, by decide⟩,⟨342671, by decide⟩,⟨342781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6613_342782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6613 ⟨342782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6613
    ⟨342782, by decide⟩ (by decide) (![⟨308705, by decide⟩,⟨170504, by decide⟩,⟨342671, by decide⟩,⟨342781, by decide⟩]) unmarked_context_11_6613_342782 node_context_11_6613_342782
  intro a
  fin_cases a
  · exact context_12_26452_308705
  · exact context_12_26453_170504
  · exact context_12_26454_342671
  · exact context_12_26455_342781

theorem selected_cut_13034 : selected 9 ⟨342839, by decide⟩
    (prefixPartial 12 26456) = some ⟨12, 2, 0, 342839, 26456, 3905, 65536⟩ := by
  decide +kernel

theorem context_12_26456_342839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26456 ⟨342839, by decide⟩ :=
  accepted_of_selected 12 26456 ⟨342839, by decide⟩ ⟨12, 2, 0, 342839, 26456, 3905, 65536⟩
    (by decide) selected_cut_13034

theorem selected_cut_13035 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105828) = some ⟨13, 1, 0, 3444, 105828, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105828_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105828 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105828 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105828, 1, 16384⟩
    (by decide) selected_cut_13035

theorem selected_cut_13036 : selected 8 ⟨342882, by decide⟩
    (prefixPartial 13 105829) = some ⟨13, 2, 0, 342882, 105829, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_105829_342882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105829 ⟨342882, by decide⟩ :=
  accepted_of_selected 13 105829 ⟨342882, by decide⟩ ⟨13, 2, 0, 342882, 105829, 1985, 16384⟩
    (by decide) selected_cut_13036

theorem selected_cut_13037 : selected 8 ⟨342946, by decide⟩
    (prefixPartial 13 105830) = some ⟨13, 2, 0, 342946, 105830, 2717, 16384⟩ := by
  decide +kernel

theorem context_13_105830_342946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105830 ⟨342946, by decide⟩ :=
  accepted_of_selected 13 105830 ⟨342946, by decide⟩ ⟨13, 2, 0, 342946, 105830, 2717, 16384⟩
    (by decide) selected_cut_13037

theorem selected_cut_13038 : selected 8 ⟨342984, by decide⟩
    (prefixPartial 13 105831) = some ⟨13, 2, 0, 342984, 105831, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_105831_342984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105831 ⟨342984, by decide⟩ :=
  accepted_of_selected 13 105831 ⟨342984, by decide⟩ ⟨13, 2, 0, 342984, 105831, 1309, 16384⟩
    (by decide) selected_cut_13038

theorem unmarked_context_12_26457_342985 : frontier 9 ⟨342985, by decide⟩
    (prefixCache 12 26457) (prefixPartial 12 26457) = false := by
  decide +kernel

theorem node_context_12_26457_342985 : EJMOriginalGlobalDAGData.nodes 9 ⟨342985, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨342882, by decide⟩,⟨342946, by decide⟩,⟨342984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26457_342985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26457 ⟨342985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26457
    ⟨342985, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨342882, by decide⟩,⟨342946, by decide⟩,⟨342984, by decide⟩]) unmarked_context_12_26457_342985 node_context_12_26457_342985
  intro a
  fin_cases a
  · exact context_13_105828_3444
  · exact context_13_105829_342882
  · exact context_13_105830_342946
  · exact context_13_105831_342984

theorem selected_cut_13039 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105832) = some ⟨13, 1, 0, 3444, 105832, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105832_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105832 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105832 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105832, 1, 16384⟩
    (by decide) selected_cut_13039

theorem selected_cut_13040 : selected 8 ⟨343008, by decide⟩
    (prefixPartial 13 105833) = some ⟨13, 2, 0, 343008, 105833, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_105833_343008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105833 ⟨343008, by decide⟩ :=
  accepted_of_selected 13 105833 ⟨343008, by decide⟩ ⟨13, 2, 0, 343008, 105833, 1381, 16384⟩
    (by decide) selected_cut_13040

theorem selected_cut_13041 : selected 8 ⟨343033, by decide⟩
    (prefixPartial 13 105834) = some ⟨13, 2, 0, 343033, 105834, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_105834_343033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105834 ⟨343033, by decide⟩ :=
  accepted_of_selected 13 105834 ⟨343033, by decide⟩ ⟨13, 2, 0, 343033, 105834, 1929, 16384⟩
    (by decide) selected_cut_13041

theorem selected_cut_13042 : selected 8 ⟨343044, by decide⟩
    (prefixPartial 13 105835) = some ⟨13, 2, 0, 343044, 105835, 837, 16384⟩ := by
  decide +kernel

theorem context_13_105835_343044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105835 ⟨343044, by decide⟩ :=
  accepted_of_selected 13 105835 ⟨343044, by decide⟩ ⟨13, 2, 0, 343044, 105835, 837, 16384⟩
    (by decide) selected_cut_13042

theorem unmarked_context_12_26458_343045 : frontier 9 ⟨343045, by decide⟩
    (prefixCache 12 26458) (prefixPartial 12 26458) = false := by
  decide +kernel

theorem node_context_12_26458_343045 : EJMOriginalGlobalDAGData.nodes 9 ⟨343045, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨343008, by decide⟩,⟨343033, by decide⟩,⟨343044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26458_343045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26458 ⟨343045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26458
    ⟨343045, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨343008, by decide⟩,⟨343033, by decide⟩,⟨343044, by decide⟩]) unmarked_context_12_26458_343045 node_context_12_26458_343045
  intro a
  fin_cases a
  · exact context_13_105832_3444
  · exact context_13_105833_343008
  · exact context_13_105834_343033
  · exact context_13_105835_343044

theorem selected_cut_13043 : selected 9 ⟨343100, by decide⟩
    (prefixPartial 12 26459) = some ⟨12, 2, 0, 343100, 26459, 3853, 65536⟩ := by
  decide +kernel

theorem context_12_26459_343100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26459 ⟨343100, by decide⟩ :=
  accepted_of_selected 12 26459 ⟨343100, by decide⟩ ⟨12, 2, 0, 343100, 26459, 3853, 65536⟩
    (by decide) selected_cut_13043

theorem unmarked_context_11_6614_343101 : frontier 10 ⟨343101, by decide⟩
    (prefixCache 11 6614) (prefixPartial 11 6614) = false := by
  decide +kernel

theorem node_context_11_6614_343101 : EJMOriginalGlobalDAGData.nodes 10 ⟨343101, by decide⟩ =
    .split (coordinate 11) (![⟨342839, by decide⟩,⟨342985, by decide⟩,⟨343045, by decide⟩,⟨343100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6614_343101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6614 ⟨343101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6614
    ⟨343101, by decide⟩ (by decide) (![⟨342839, by decide⟩,⟨342985, by decide⟩,⟨343045, by decide⟩,⟨343100, by decide⟩]) unmarked_context_11_6614_343101 node_context_11_6614_343101
  intro a
  fin_cases a
  · exact context_12_26456_342839
  · exact context_12_26457_342985
  · exact context_12_26458_343045
  · exact context_12_26459_343100

theorem selected_cut_13044 : selected 9 ⟨343140, by decide⟩
    (prefixPartial 12 26460) = some ⟨12, 2, 0, 343140, 26460, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_26460_343140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26460 ⟨343140, by decide⟩ :=
  accepted_of_selected 12 26460 ⟨343140, by decide⟩ ⟨12, 2, 0, 343140, 26460, 3049, 65536⟩
    (by decide) selected_cut_13044

theorem selected_cut_13045 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105844) = some ⟨13, 1, 0, 3444, 105844, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105844_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105844 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105844 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105844, 1, 16384⟩
    (by decide) selected_cut_13045

theorem selected_cut_13046 : selected 8 ⟨343166, by decide⟩
    (prefixPartial 13 105845) = some ⟨13, 2, 0, 343166, 105845, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_105845_343166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105845 ⟨343166, by decide⟩ :=
  accepted_of_selected 13 105845 ⟨343166, by decide⟩ ⟨13, 2, 0, 343166, 105845, 1581, 16384⟩
    (by decide) selected_cut_13046

theorem selected_cut_13047 : selected 8 ⟨343219, by decide⟩
    (prefixPartial 13 105846) = some ⟨13, 2, 0, 343219, 105846, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_105846_343219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105846 ⟨343219, by decide⟩ :=
  accepted_of_selected 13 105846 ⟨343219, by decide⟩ ⟨13, 2, 0, 343219, 105846, 2525, 16384⟩
    (by decide) selected_cut_13047

theorem selected_cut_13048 : selected 8 ⟨343237, by decide⟩
    (prefixPartial 13 105847) = some ⟨13, 2, 0, 343237, 105847, 953, 16384⟩ := by
  decide +kernel

theorem context_13_105847_343237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105847 ⟨343237, by decide⟩ :=
  accepted_of_selected 13 105847 ⟨343237, by decide⟩ ⟨13, 2, 0, 343237, 105847, 953, 16384⟩
    (by decide) selected_cut_13048

theorem unmarked_context_12_26461_343238 : frontier 9 ⟨343238, by decide⟩
    (prefixCache 12 26461) (prefixPartial 12 26461) = false := by
  decide +kernel

theorem node_context_12_26461_343238 : EJMOriginalGlobalDAGData.nodes 9 ⟨343238, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨343166, by decide⟩,⟨343219, by decide⟩,⟨343237, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26461_343238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26461 ⟨343238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26461
    ⟨343238, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨343166, by decide⟩,⟨343219, by decide⟩,⟨343237, by decide⟩]) unmarked_context_12_26461_343238 node_context_12_26461_343238
  intro a
  fin_cases a
  · exact context_13_105844_3444
  · exact context_13_105845_343166
  · exact context_13_105846_343219
  · exact context_13_105847_343237

theorem selected_cut_13049 : selected 9 ⟨343279, by decide⟩
    (prefixPartial 12 26462) = some ⟨12, 2, 0, 343279, 26462, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_26462_343279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26462 ⟨343279, by decide⟩ :=
  accepted_of_selected 12 26462 ⟨343279, by decide⟩ ⟨12, 2, 0, 343279, 26462, 3321, 65536⟩
    (by decide) selected_cut_13049

theorem selected_cut_13050 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105852) = some ⟨13, 1, 0, 3444, 105852, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105852_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105852 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105852 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105852, 1, 16384⟩
    (by decide) selected_cut_13050

theorem selected_cut_13051 : selected 8 ⟨343309, by decide⟩
    (prefixPartial 13 105853) = some ⟨13, 2, 0, 343309, 105853, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_105853_343309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105853 ⟨343309, by decide⟩ :=
  accepted_of_selected 13 105853 ⟨343309, by decide⟩ ⟨13, 2, 0, 343309, 105853, 1833, 16384⟩
    (by decide) selected_cut_13051

theorem selected_cut_13052 : selected 8 ⟨343362, by decide⟩
    (prefixPartial 13 105854) = some ⟨13, 2, 0, 343362, 105854, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_105854_343362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105854 ⟨343362, by decide⟩ :=
  accepted_of_selected 13 105854 ⟨343362, by decide⟩ ⟨13, 2, 0, 343362, 105854, 2589, 16384⟩
    (by decide) selected_cut_13052

theorem selected_cut_13053 : selected 8 ⟨343385, by decide⟩
    (prefixPartial 13 105855) = some ⟨13, 2, 0, 343385, 105855, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_105855_343385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105855 ⟨343385, by decide⟩ :=
  accepted_of_selected 13 105855 ⟨343385, by decide⟩ ⟨13, 2, 0, 343385, 105855, 1105, 16384⟩
    (by decide) selected_cut_13053

theorem unmarked_context_12_26463_343386 : frontier 9 ⟨343386, by decide⟩
    (prefixCache 12 26463) (prefixPartial 12 26463) = false := by
  decide +kernel

theorem node_context_12_26463_343386 : EJMOriginalGlobalDAGData.nodes 9 ⟨343386, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨343309, by decide⟩,⟨343362, by decide⟩,⟨343385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26463_343386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26463 ⟨343386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26463
    ⟨343386, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨343309, by decide⟩,⟨343362, by decide⟩,⟨343385, by decide⟩]) unmarked_context_12_26463_343386 node_context_12_26463_343386
  intro a
  fin_cases a
  · exact context_13_105852_3444
  · exact context_13_105853_343309
  · exact context_13_105854_343362
  · exact context_13_105855_343385

theorem unmarked_context_11_6615_343387 : frontier 10 ⟨343387, by decide⟩
    (prefixCache 11 6615) (prefixPartial 11 6615) = false := by
  decide +kernel

theorem node_context_11_6615_343387 : EJMOriginalGlobalDAGData.nodes 10 ⟨343387, by decide⟩ =
    .split (coordinate 11) (![⟨343140, by decide⟩,⟨343238, by decide⟩,⟨343279, by decide⟩,⟨343386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6615_343387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6615 ⟨343387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6615
    ⟨343387, by decide⟩ (by decide) (![⟨343140, by decide⟩,⟨343238, by decide⟩,⟨343279, by decide⟩,⟨343386, by decide⟩]) unmarked_context_11_6615_343387 node_context_11_6615_343387
  intro a
  fin_cases a
  · exact context_12_26460_343140
  · exact context_12_26461_343238
  · exact context_12_26462_343279
  · exact context_12_26463_343386

theorem unmarked_context_10_1653_343388 : frontier 11 ⟨343388, by decide⟩
    (prefixCache 10 1653) (prefixPartial 10 1653) = false := by
  decide +kernel

theorem node_context_10_1653_343388 : EJMOriginalGlobalDAGData.nodes 11 ⟨343388, by decide⟩ =
    .split (coordinate 10) (![⟨342525, by decide⟩,⟨342782, by decide⟩,⟨343101, by decide⟩,⟨343387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1653_343388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1653 ⟨343388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1653
    ⟨343388, by decide⟩ (by decide) (![⟨342525, by decide⟩,⟨342782, by decide⟩,⟨343101, by decide⟩,⟨343387, by decide⟩]) unmarked_context_10_1653_343388 node_context_10_1653_343388
  intro a
  fin_cases a
  · exact context_11_6612_342525
  · exact context_11_6613_342782
  · exact context_11_6614_343101
  · exact context_11_6615_343387

theorem selected_cut_13054 : selected 9 ⟨343431, by decide⟩
    (prefixPartial 12 26464) = some ⟨12, 2, 0, 343431, 26464, 3681, 65536⟩ := by
  decide +kernel

theorem context_12_26464_343431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26464 ⟨343431, by decide⟩ :=
  accepted_of_selected 12 26464 ⟨343431, by decide⟩ ⟨12, 2, 0, 343431, 26464, 3681, 65536⟩
    (by decide) selected_cut_13054

theorem selected_cut_13055 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105860) = some ⟨13, 1, 0, 3444, 105860, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105860_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105860 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105860 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105860, 1, 16384⟩
    (by decide) selected_cut_13055

theorem selected_cut_13056 : selected 8 ⟨343485, by decide⟩
    (prefixPartial 13 105861) = some ⟨13, 2, 0, 343485, 105861, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_105861_343485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105861 ⟨343485, by decide⟩ :=
  accepted_of_selected 13 105861 ⟨343485, by decide⟩ ⟨13, 2, 0, 343485, 105861, 2385, 16384⟩
    (by decide) selected_cut_13056

theorem selected_cut_13057 : selected 8 ⟨343540, by decide⟩
    (prefixPartial 13 105862) = some ⟨13, 2, 0, 343540, 105862, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_105862_343540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105862 ⟨343540, by decide⟩ :=
  accepted_of_selected 13 105862 ⟨343540, by decide⟩ ⟨13, 2, 0, 343540, 105862, 2601, 16384⟩
    (by decide) selected_cut_13057

theorem selected_cut_13058 : selected 8 ⟨343549, by decide⟩
    (prefixPartial 13 105863) = some ⟨13, 2, 0, 343549, 105863, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_105863_343549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105863 ⟨343549, by decide⟩ :=
  accepted_of_selected 13 105863 ⟨343549, by decide⟩ ⟨13, 2, 0, 343549, 105863, 1017, 16384⟩
    (by decide) selected_cut_13058

theorem unmarked_context_12_26465_343550 : frontier 9 ⟨343550, by decide⟩
    (prefixCache 12 26465) (prefixPartial 12 26465) = false := by
  decide +kernel

theorem node_context_12_26465_343550 : EJMOriginalGlobalDAGData.nodes 9 ⟨343550, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨343485, by decide⟩,⟨343540, by decide⟩,⟨343549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26465_343550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26465 ⟨343550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26465
    ⟨343550, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨343485, by decide⟩,⟨343540, by decide⟩,⟨343549, by decide⟩]) unmarked_context_12_26465_343550 node_context_12_26465_343550
  intro a
  fin_cases a
  · exact context_13_105860_3444
  · exact context_13_105861_343485
  · exact context_13_105862_343540
  · exact context_13_105863_343549

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
