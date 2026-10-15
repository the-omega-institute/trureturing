/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover079
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_07682 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 22613) = some ⟨12, 1, 0, 170504, 22613, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22613_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22613 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 22613 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 22613, 1, 65536⟩
    (by decide) selected_cut_07682

theorem selected_cut_07683 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90456) = some ⟨13, 1, 0, 3444, 90456, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90456_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90456 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90456 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90456, 1, 16384⟩
    (by decide) selected_cut_07683

theorem selected_cut_07684 : selected 8 ⟨220865, by decide⟩
    (prefixPartial 13 90457) = some ⟨13, 2, 0, 220865, 90457, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_90457_220865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90457 ⟨220865, by decide⟩ :=
  accepted_of_selected 13 90457 ⟨220865, by decide⟩ ⟨13, 2, 0, 220865, 90457, 2129, 16384⟩
    (by decide) selected_cut_07684

theorem selected_cut_07685 : selected 8 ⟨220889, by decide⟩
    (prefixPartial 13 90458) = some ⟨13, 2, 0, 220889, 90458, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_90458_220889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90458 ⟨220889, by decide⟩ :=
  accepted_of_selected 13 90458 ⟨220889, by decide⟩ ⟨13, 2, 0, 220889, 90458, 2069, 16384⟩
    (by decide) selected_cut_07685

theorem selected_cut_07686 : selected 8 ⟨220900, by decide⟩
    (prefixPartial 13 90459) = some ⟨13, 2, 0, 220900, 90459, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_90459_220900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90459 ⟨220900, by decide⟩ :=
  accepted_of_selected 13 90459 ⟨220900, by decide⟩ ⟨13, 2, 0, 220900, 90459, 1165, 16384⟩
    (by decide) selected_cut_07686

theorem unmarked_context_12_22614_220901 : frontier 9 ⟨220901, by decide⟩
    (prefixCache 12 22614) (prefixPartial 12 22614) = false := by
  decide +kernel

theorem node_context_12_22614_220901 : EJMOriginalGlobalDAGData.nodes 9 ⟨220901, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220865, by decide⟩,⟨220889, by decide⟩,⟨220900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22614_220901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22614 ⟨220901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22614
    ⟨220901, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220865, by decide⟩,⟨220889, by decide⟩,⟨220900, by decide⟩]) unmarked_context_12_22614_220901 node_context_12_22614_220901
  intro a
  fin_cases a
  · exact context_13_90456_3444
  · exact context_13_90457_220865
  · exact context_13_90458_220889
  · exact context_13_90459_220900

theorem selected_cut_07687 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90460) = some ⟨13, 1, 0, 3444, 90460, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90460_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90460 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90460 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90460, 1, 16384⟩
    (by decide) selected_cut_07687

theorem selected_cut_07688 : selected 8 ⟨220929, by decide⟩
    (prefixPartial 13 90461) = some ⟨13, 2, 0, 220929, 90461, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_90461_220929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90461 ⟨220929, by decide⟩ :=
  accepted_of_selected 13 90461 ⟨220929, by decide⟩ ⟨13, 2, 0, 220929, 90461, 2193, 16384⟩
    (by decide) selected_cut_07688

theorem selected_cut_07689 : selected 8 ⟨220948, by decide⟩
    (prefixPartial 13 90462) = some ⟨13, 2, 0, 220948, 90462, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_90462_220948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90462 ⟨220948, by decide⟩ :=
  accepted_of_selected 13 90462 ⟨220948, by decide⟩ ⟨13, 2, 0, 220948, 90462, 1965, 16384⟩
    (by decide) selected_cut_07689

theorem selected_cut_07690 : selected 8 ⟨220960, by decide⟩
    (prefixPartial 13 90463) = some ⟨13, 2, 0, 220960, 90463, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_90463_220960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90463 ⟨220960, by decide⟩ :=
  accepted_of_selected 13 90463 ⟨220960, by decide⟩ ⟨13, 2, 0, 220960, 90463, 1125, 16384⟩
    (by decide) selected_cut_07690

theorem unmarked_context_12_22615_220961 : frontier 9 ⟨220961, by decide⟩
    (prefixCache 12 22615) (prefixPartial 12 22615) = false := by
  decide +kernel

theorem node_context_12_22615_220961 : EJMOriginalGlobalDAGData.nodes 9 ⟨220961, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220929, by decide⟩,⟨220948, by decide⟩,⟨220960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22615_220961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22615 ⟨220961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22615
    ⟨220961, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220929, by decide⟩,⟨220948, by decide⟩,⟨220960, by decide⟩]) unmarked_context_12_22615_220961 node_context_12_22615_220961
  intro a
  fin_cases a
  · exact context_13_90460_3444
  · exact context_13_90461_220929
  · exact context_13_90462_220948
  · exact context_13_90463_220960

theorem unmarked_context_11_5653_220962 : frontier 10 ⟨220962, by decide⟩
    (prefixCache 11 5653) (prefixPartial 11 5653) = false := by
  decide +kernel

theorem node_context_11_5653_220962 : EJMOriginalGlobalDAGData.nodes 10 ⟨220962, by decide⟩ =
    .split (coordinate 11) (![⟨220848, by decide⟩,⟨170504, by decide⟩,⟨220901, by decide⟩,⟨220961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5653_220962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5653 ⟨220962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5653
    ⟨220962, by decide⟩ (by decide) (![⟨220848, by decide⟩,⟨170504, by decide⟩,⟨220901, by decide⟩,⟨220961, by decide⟩]) unmarked_context_11_5653_220962 node_context_11_5653_220962
  intro a
  fin_cases a
  · exact context_12_22612_220848
  · exact context_12_22613_170504
  · exact context_12_22614_220901
  · exact context_12_22615_220961

theorem selected_cut_07691 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90464) = some ⟨13, 1, 0, 3444, 90464, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90464_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90464 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90464 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90464, 1, 16384⟩
    (by decide) selected_cut_07691

theorem selected_cut_07692 : selected 8 ⟨220986, by decide⟩
    (prefixPartial 13 90465) = some ⟨13, 2, 0, 220986, 90465, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_90465_220986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90465 ⟨220986, by decide⟩ :=
  accepted_of_selected 13 90465 ⟨220986, by decide⟩ ⟨13, 2, 0, 220986, 90465, 1905, 16384⟩
    (by decide) selected_cut_07692

theorem selected_cut_07693 : selected 8 ⟨221006, by decide⟩
    (prefixPartial 13 90466) = some ⟨13, 2, 0, 221006, 90466, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_90466_221006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90466 ⟨221006, by decide⟩ :=
  accepted_of_selected 13 90466 ⟨221006, by decide⟩ ⟨13, 2, 0, 221006, 90466, 1921, 16384⟩
    (by decide) selected_cut_07693

theorem selected_cut_07694 : selected 8 ⟨221018, by decide⟩
    (prefixPartial 13 90467) = some ⟨13, 2, 0, 221018, 90467, 957, 16384⟩ := by
  decide +kernel

theorem context_13_90467_221018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90467 ⟨221018, by decide⟩ :=
  accepted_of_selected 13 90467 ⟨221018, by decide⟩ ⟨13, 2, 0, 221018, 90467, 957, 16384⟩
    (by decide) selected_cut_07694

theorem unmarked_context_12_22616_221019 : frontier 9 ⟨221019, by decide⟩
    (prefixCache 12 22616) (prefixPartial 12 22616) = false := by
  decide +kernel

theorem node_context_12_22616_221019 : EJMOriginalGlobalDAGData.nodes 9 ⟨221019, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨220986, by decide⟩,⟨221006, by decide⟩,⟨221018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22616_221019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22616 ⟨221019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22616
    ⟨221019, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨220986, by decide⟩,⟨221006, by decide⟩,⟨221018, by decide⟩]) unmarked_context_12_22616_221019 node_context_12_22616_221019
  intro a
  fin_cases a
  · exact context_13_90464_3444
  · exact context_13_90465_220986
  · exact context_13_90466_221006
  · exact context_13_90467_221018

theorem selected_cut_07695 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90468) = some ⟨13, 1, 0, 3444, 90468, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90468_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90468 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90468 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90468, 1, 16384⟩
    (by decide) selected_cut_07695

theorem selected_cut_07696 : selected 8 ⟨221056, by decide⟩
    (prefixPartial 13 90469) = some ⟨13, 2, 0, 221056, 90469, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_90469_221056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90469 ⟨221056, by decide⟩ :=
  accepted_of_selected 13 90469 ⟨221056, by decide⟩ ⟨13, 2, 0, 221056, 90469, 2473, 16384⟩
    (by decide) selected_cut_07696

theorem selected_cut_07697 : selected 8 ⟨221095, by decide⟩
    (prefixPartial 13 90470) = some ⟨13, 2, 0, 221095, 90470, 2641, 16384⟩ := by
  decide +kernel

theorem context_13_90470_221095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90470 ⟨221095, by decide⟩ :=
  accepted_of_selected 13 90470 ⟨221095, by decide⟩ ⟨13, 2, 0, 221095, 90470, 2641, 16384⟩
    (by decide) selected_cut_07697

theorem selected_cut_07698 : selected 8 ⟨221106, by decide⟩
    (prefixPartial 13 90471) = some ⟨13, 2, 0, 221106, 90471, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_90471_221106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90471 ⟨221106, by decide⟩ :=
  accepted_of_selected 13 90471 ⟨221106, by decide⟩ ⟨13, 2, 0, 221106, 90471, 1269, 16384⟩
    (by decide) selected_cut_07698

theorem unmarked_context_12_22617_221107 : frontier 9 ⟨221107, by decide⟩
    (prefixCache 12 22617) (prefixPartial 12 22617) = false := by
  decide +kernel

theorem node_context_12_22617_221107 : EJMOriginalGlobalDAGData.nodes 9 ⟨221107, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221056, by decide⟩,⟨221095, by decide⟩,⟨221106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22617_221107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22617 ⟨221107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22617
    ⟨221107, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221056, by decide⟩,⟨221095, by decide⟩,⟨221106, by decide⟩]) unmarked_context_12_22617_221107 node_context_12_22617_221107
  intro a
  fin_cases a
  · exact context_13_90468_3444
  · exact context_13_90469_221056
  · exact context_13_90470_221095
  · exact context_13_90471_221106

theorem selected_cut_07699 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90472) = some ⟨13, 1, 0, 3444, 90472, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90472_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90472 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90472 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90472, 1, 16384⟩
    (by decide) selected_cut_07699

theorem selected_cut_07700 : selected 8 ⟨221128, by decide⟩
    (prefixPartial 13 90473) = some ⟨13, 2, 0, 221128, 90473, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_90473_221128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90473 ⟨221128, by decide⟩ :=
  accepted_of_selected 13 90473 ⟨221128, by decide⟩ ⟨13, 2, 0, 221128, 90473, 2045, 16384⟩
    (by decide) selected_cut_07700

theorem selected_cut_07701 : selected 8 ⟨221164, by decide⟩
    (prefixPartial 13 90474) = some ⟨13, 2, 0, 221164, 90474, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_90474_221164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90474 ⟨221164, by decide⟩ :=
  accepted_of_selected 13 90474 ⟨221164, by decide⟩ ⟨13, 2, 0, 221164, 90474, 2253, 16384⟩
    (by decide) selected_cut_07701

theorem selected_cut_07702 : selected 8 ⟨221176, by decide⟩
    (prefixPartial 13 90475) = some ⟨13, 2, 0, 221176, 90475, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_90475_221176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90475 ⟨221176, by decide⟩ :=
  accepted_of_selected 13 90475 ⟨221176, by decide⟩ ⟨13, 2, 0, 221176, 90475, 1105, 16384⟩
    (by decide) selected_cut_07702

theorem unmarked_context_12_22618_221177 : frontier 9 ⟨221177, by decide⟩
    (prefixCache 12 22618) (prefixPartial 12 22618) = false := by
  decide +kernel

theorem node_context_12_22618_221177 : EJMOriginalGlobalDAGData.nodes 9 ⟨221177, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221128, by decide⟩,⟨221164, by decide⟩,⟨221176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22618_221177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22618 ⟨221177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22618
    ⟨221177, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221128, by decide⟩,⟨221164, by decide⟩,⟨221176, by decide⟩]) unmarked_context_12_22618_221177 node_context_12_22618_221177
  intro a
  fin_cases a
  · exact context_13_90472_3444
  · exact context_13_90473_221128
  · exact context_13_90474_221164
  · exact context_13_90475_221176

theorem selected_cut_07703 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90476) = some ⟨13, 1, 0, 3444, 90476, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90476_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90476 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90476 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90476, 1, 16384⟩
    (by decide) selected_cut_07703

theorem selected_cut_07704 : selected 8 ⟨221199, by decide⟩
    (prefixPartial 13 90477) = some ⟨13, 2, 0, 221199, 90477, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_90477_221199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90477 ⟨221199, by decide⟩ :=
  accepted_of_selected 13 90477 ⟨221199, by decide⟩ ⟨13, 2, 0, 221199, 90477, 1929, 16384⟩
    (by decide) selected_cut_07704

theorem selected_cut_07705 : selected 8 ⟨221228, by decide⟩
    (prefixPartial 13 90478) = some ⟨13, 2, 0, 221228, 90478, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_90478_221228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90478 ⟨221228, by decide⟩ :=
  accepted_of_selected 13 90478 ⟨221228, by decide⟩ ⟨13, 2, 0, 221228, 90478, 2409, 16384⟩
    (by decide) selected_cut_07705

theorem selected_cut_07706 : selected 8 ⟨221240, by decide⟩
    (prefixPartial 13 90479) = some ⟨13, 2, 0, 221240, 90479, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_90479_221240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90479 ⟨221240, by decide⟩ :=
  accepted_of_selected 13 90479 ⟨221240, by decide⟩ ⟨13, 2, 0, 221240, 90479, 1101, 16384⟩
    (by decide) selected_cut_07706

theorem unmarked_context_12_22619_221241 : frontier 9 ⟨221241, by decide⟩
    (prefixCache 12 22619) (prefixPartial 12 22619) = false := by
  decide +kernel

theorem node_context_12_22619_221241 : EJMOriginalGlobalDAGData.nodes 9 ⟨221241, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221199, by decide⟩,⟨221228, by decide⟩,⟨221240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22619_221241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22619 ⟨221241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22619
    ⟨221241, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221199, by decide⟩,⟨221228, by decide⟩,⟨221240, by decide⟩]) unmarked_context_12_22619_221241 node_context_12_22619_221241
  intro a
  fin_cases a
  · exact context_13_90476_3444
  · exact context_13_90477_221199
  · exact context_13_90478_221228
  · exact context_13_90479_221240

theorem unmarked_context_11_5654_221242 : frontier 10 ⟨221242, by decide⟩
    (prefixCache 11 5654) (prefixPartial 11 5654) = false := by
  decide +kernel

theorem node_context_11_5654_221242 : EJMOriginalGlobalDAGData.nodes 10 ⟨221242, by decide⟩ =
    .split (coordinate 11) (![⟨221019, by decide⟩,⟨221107, by decide⟩,⟨221177, by decide⟩,⟨221241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5654_221242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5654 ⟨221242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5654
    ⟨221242, by decide⟩ (by decide) (![⟨221019, by decide⟩,⟨221107, by decide⟩,⟨221177, by decide⟩,⟨221241, by decide⟩]) unmarked_context_11_5654_221242 node_context_11_5654_221242
  intro a
  fin_cases a
  · exact context_12_22616_221019
  · exact context_12_22617_221107
  · exact context_12_22618_221177
  · exact context_12_22619_221241

theorem selected_cut_07707 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90480) = some ⟨13, 1, 0, 3444, 90480, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90480_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90480 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90480 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90480, 1, 16384⟩
    (by decide) selected_cut_07707

theorem selected_cut_07708 : selected 8 ⟨221260, by decide⟩
    (prefixPartial 13 90481) = some ⟨13, 2, 0, 221260, 90481, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_90481_221260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90481 ⟨221260, by decide⟩ :=
  accepted_of_selected 13 90481 ⟨221260, by decide⟩ ⟨13, 2, 0, 221260, 90481, 1721, 16384⟩
    (by decide) selected_cut_07708

theorem selected_cut_07709 : selected 8 ⟨221278, by decide⟩
    (prefixPartial 13 90482) = some ⟨13, 2, 0, 221278, 90482, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_90482_221278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90482 ⟨221278, by decide⟩ :=
  accepted_of_selected 13 90482 ⟨221278, by decide⟩ ⟨13, 2, 0, 221278, 90482, 1669, 16384⟩
    (by decide) selected_cut_07709

theorem selected_cut_07710 : selected 8 ⟨221290, by decide⟩
    (prefixPartial 13 90483) = some ⟨13, 2, 0, 221290, 90483, 997, 16384⟩ := by
  decide +kernel

theorem context_13_90483_221290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90483 ⟨221290, by decide⟩ :=
  accepted_of_selected 13 90483 ⟨221290, by decide⟩ ⟨13, 2, 0, 221290, 90483, 997, 16384⟩
    (by decide) selected_cut_07710

theorem unmarked_context_12_22620_221291 : frontier 9 ⟨221291, by decide⟩
    (prefixCache 12 22620) (prefixPartial 12 22620) = false := by
  decide +kernel

theorem node_context_12_22620_221291 : EJMOriginalGlobalDAGData.nodes 9 ⟨221291, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221260, by decide⟩,⟨221278, by decide⟩,⟨221290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22620_221291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22620 ⟨221291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22620
    ⟨221291, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221260, by decide⟩,⟨221278, by decide⟩,⟨221290, by decide⟩]) unmarked_context_12_22620_221291 node_context_12_22620_221291
  intro a
  fin_cases a
  · exact context_13_90480_3444
  · exact context_13_90481_221260
  · exact context_13_90482_221278
  · exact context_13_90483_221290

theorem selected_cut_07711 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90484) = some ⟨13, 1, 0, 3444, 90484, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90484_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90484 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90484 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90484, 1, 16384⟩
    (by decide) selected_cut_07711

theorem selected_cut_07712 : selected 8 ⟨221331, by decide⟩
    (prefixPartial 13 90485) = some ⟨13, 2, 0, 221331, 90485, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_90485_221331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90485 ⟨221331, by decide⟩ :=
  accepted_of_selected 13 90485 ⟨221331, by decide⟩ ⟨13, 2, 0, 221331, 90485, 2365, 16384⟩
    (by decide) selected_cut_07712

theorem selected_cut_07713 : selected 8 ⟨221361, by decide⟩
    (prefixPartial 13 90486) = some ⟨13, 2, 0, 221361, 90486, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_90486_221361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90486 ⟨221361, by decide⟩ :=
  accepted_of_selected 13 90486 ⟨221361, by decide⟩ ⟨13, 2, 0, 221361, 90486, 2381, 16384⟩
    (by decide) selected_cut_07713

theorem selected_cut_07714 : selected 8 ⟨221379, by decide⟩
    (prefixPartial 13 90487) = some ⟨13, 2, 0, 221379, 90487, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_90487_221379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90487 ⟨221379, by decide⟩ :=
  accepted_of_selected 13 90487 ⟨221379, by decide⟩ ⟨13, 2, 0, 221379, 90487, 1261, 16384⟩
    (by decide) selected_cut_07714

theorem unmarked_context_12_22621_221380 : frontier 9 ⟨221380, by decide⟩
    (prefixCache 12 22621) (prefixPartial 12 22621) = false := by
  decide +kernel

theorem node_context_12_22621_221380 : EJMOriginalGlobalDAGData.nodes 9 ⟨221380, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221331, by decide⟩,⟨221361, by decide⟩,⟨221379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22621_221380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22621 ⟨221380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22621
    ⟨221380, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221331, by decide⟩,⟨221361, by decide⟩,⟨221379, by decide⟩]) unmarked_context_12_22621_221380 node_context_12_22621_221380
  intro a
  fin_cases a
  · exact context_13_90484_3444
  · exact context_13_90485_221331
  · exact context_13_90486_221361
  · exact context_13_90487_221379

theorem selected_cut_07715 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90488) = some ⟨13, 1, 0, 3444, 90488, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90488_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90488 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90488 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90488, 1, 16384⟩
    (by decide) selected_cut_07715

theorem selected_cut_07716 : selected 8 ⟨221401, by decide⟩
    (prefixPartial 13 90489) = some ⟨13, 2, 0, 221401, 90489, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_90489_221401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90489 ⟨221401, by decide⟩ :=
  accepted_of_selected 13 90489 ⟨221401, by decide⟩ ⟨13, 2, 0, 221401, 90489, 1757, 16384⟩
    (by decide) selected_cut_07716

theorem selected_cut_07717 : selected 8 ⟨221426, by decide⟩
    (prefixPartial 13 90490) = some ⟨13, 2, 0, 221426, 90490, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_90490_221426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90490 ⟨221426, by decide⟩ :=
  accepted_of_selected 13 90490 ⟨221426, by decide⟩ ⟨13, 2, 0, 221426, 90490, 2253, 16384⟩
    (by decide) selected_cut_07717

theorem selected_cut_07718 : selected 8 ⟨221435, by decide⟩
    (prefixPartial 13 90491) = some ⟨13, 2, 0, 221435, 90491, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_90491_221435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90491 ⟨221435, by decide⟩ :=
  accepted_of_selected 13 90491 ⟨221435, by decide⟩ ⟨13, 2, 0, 221435, 90491, 1085, 16384⟩
    (by decide) selected_cut_07718

theorem unmarked_context_12_22622_221436 : frontier 9 ⟨221436, by decide⟩
    (prefixCache 12 22622) (prefixPartial 12 22622) = false := by
  decide +kernel

theorem node_context_12_22622_221436 : EJMOriginalGlobalDAGData.nodes 9 ⟨221436, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221401, by decide⟩,⟨221426, by decide⟩,⟨221435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22622_221436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22622 ⟨221436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22622
    ⟨221436, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221401, by decide⟩,⟨221426, by decide⟩,⟨221435, by decide⟩]) unmarked_context_12_22622_221436 node_context_12_22622_221436
  intro a
  fin_cases a
  · exact context_13_90488_3444
  · exact context_13_90489_221401
  · exact context_13_90490_221426
  · exact context_13_90491_221435

theorem selected_cut_07719 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90492) = some ⟨13, 1, 0, 3444, 90492, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90492_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90492 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90492 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90492, 1, 16384⟩
    (by decide) selected_cut_07719

theorem selected_cut_07720 : selected 8 ⟨221458, by decide⟩
    (prefixPartial 13 90493) = some ⟨13, 2, 0, 221458, 90493, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_90493_221458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90493 ⟨221458, by decide⟩ :=
  accepted_of_selected 13 90493 ⟨221458, by decide⟩ ⟨13, 2, 0, 221458, 90493, 1905, 16384⟩
    (by decide) selected_cut_07720

theorem selected_cut_07721 : selected 8 ⟨221484, by decide⟩
    (prefixPartial 13 90494) = some ⟨13, 2, 0, 221484, 90494, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_90494_221484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90494 ⟨221484, by decide⟩ :=
  accepted_of_selected 13 90494 ⟨221484, by decide⟩ ⟨13, 2, 0, 221484, 90494, 2113, 16384⟩
    (by decide) selected_cut_07721

theorem selected_cut_07722 : selected 8 ⟨221497, by decide⟩
    (prefixPartial 13 90495) = some ⟨13, 2, 0, 221497, 90495, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_90495_221497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90495 ⟨221497, by decide⟩ :=
  accepted_of_selected 13 90495 ⟨221497, by decide⟩ ⟨13, 2, 0, 221497, 90495, 1025, 16384⟩
    (by decide) selected_cut_07722

theorem unmarked_context_12_22623_221498 : frontier 9 ⟨221498, by decide⟩
    (prefixCache 12 22623) (prefixPartial 12 22623) = false := by
  decide +kernel

theorem node_context_12_22623_221498 : EJMOriginalGlobalDAGData.nodes 9 ⟨221498, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221458, by decide⟩,⟨221484, by decide⟩,⟨221497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22623_221498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22623 ⟨221498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22623
    ⟨221498, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221458, by decide⟩,⟨221484, by decide⟩,⟨221497, by decide⟩]) unmarked_context_12_22623_221498 node_context_12_22623_221498
  intro a
  fin_cases a
  · exact context_13_90492_3444
  · exact context_13_90493_221458
  · exact context_13_90494_221484
  · exact context_13_90495_221497

theorem unmarked_context_11_5655_221499 : frontier 10 ⟨221499, by decide⟩
    (prefixCache 11 5655) (prefixPartial 11 5655) = false := by
  decide +kernel

theorem node_context_11_5655_221499 : EJMOriginalGlobalDAGData.nodes 10 ⟨221499, by decide⟩ =
    .split (coordinate 11) (![⟨221291, by decide⟩,⟨221380, by decide⟩,⟨221436, by decide⟩,⟨221498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5655_221499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5655 ⟨221499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5655
    ⟨221499, by decide⟩ (by decide) (![⟨221291, by decide⟩,⟨221380, by decide⟩,⟨221436, by decide⟩,⟨221498, by decide⟩]) unmarked_context_11_5655_221499 node_context_11_5655_221499
  intro a
  fin_cases a
  · exact context_12_22620_221291
  · exact context_12_22621_221380
  · exact context_12_22622_221436
  · exact context_12_22623_221498

theorem unmarked_context_10_1413_221500 : frontier 11 ⟨221500, by decide⟩
    (prefixCache 10 1413) (prefixPartial 10 1413) = false := by
  decide +kernel

theorem node_context_10_1413_221500 : EJMOriginalGlobalDAGData.nodes 11 ⟨221500, by decide⟩ =
    .split (coordinate 10) (![⟨220795, by decide⟩,⟨220962, by decide⟩,⟨221242, by decide⟩,⟨221499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1413_221500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1413 ⟨221500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1413
    ⟨221500, by decide⟩ (by decide) (![⟨220795, by decide⟩,⟨220962, by decide⟩,⟨221242, by decide⟩,⟨221499, by decide⟩]) unmarked_context_10_1413_221500 node_context_10_1413_221500
  intro a
  fin_cases a
  · exact context_11_5652_220795
  · exact context_11_5653_220962
  · exact context_11_5654_221242
  · exact context_11_5655_221499

theorem selected_cut_07723 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90496) = some ⟨13, 1, 0, 3444, 90496, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90496_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90496 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90496 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90496, 1, 16384⟩
    (by decide) selected_cut_07723

theorem selected_cut_07724 : selected 8 ⟨221539, by decide⟩
    (prefixPartial 13 90497) = some ⟨13, 2, 0, 221539, 90497, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_90497_221539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90497 ⟨221539, by decide⟩ :=
  accepted_of_selected 13 90497 ⟨221539, by decide⟩ ⟨13, 2, 0, 221539, 90497, 2297, 16384⟩
    (by decide) selected_cut_07724

theorem selected_cut_07725 : selected 8 ⟨221574, by decide⟩
    (prefixPartial 13 90498) = some ⟨13, 2, 0, 221574, 90498, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_90498_221574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90498 ⟨221574, by decide⟩ :=
  accepted_of_selected 13 90498 ⟨221574, by decide⟩ ⟨13, 2, 0, 221574, 90498, 2421, 16384⟩
    (by decide) selected_cut_07725

theorem selected_cut_07726 : selected 8 ⟨221593, by decide⟩
    (prefixPartial 13 90499) = some ⟨13, 2, 0, 221593, 90499, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_90499_221593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90499 ⟨221593, by decide⟩ :=
  accepted_of_selected 13 90499 ⟨221593, by decide⟩ ⟨13, 2, 0, 221593, 90499, 1433, 16384⟩
    (by decide) selected_cut_07726

theorem unmarked_context_12_22624_221594 : frontier 9 ⟨221594, by decide⟩
    (prefixCache 12 22624) (prefixPartial 12 22624) = false := by
  decide +kernel

theorem node_context_12_22624_221594 : EJMOriginalGlobalDAGData.nodes 9 ⟨221594, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221539, by decide⟩,⟨221574, by decide⟩,⟨221593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22624_221594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22624 ⟨221594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22624
    ⟨221594, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221539, by decide⟩,⟨221574, by decide⟩,⟨221593, by decide⟩]) unmarked_context_12_22624_221594 node_context_12_22624_221594
  intro a
  fin_cases a
  · exact context_13_90496_3444
  · exact context_13_90497_221539
  · exact context_13_90498_221574
  · exact context_13_90499_221593

theorem selected_cut_07727 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90500) = some ⟨13, 1, 0, 3444, 90500, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90500_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90500 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90500 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90500, 1, 16384⟩
    (by decide) selected_cut_07727

theorem selected_cut_07728 : selected 8 ⟨221623, by decide⟩
    (prefixPartial 13 90501) = some ⟨13, 2, 0, 221623, 90501, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_90501_221623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90501 ⟨221623, by decide⟩ :=
  accepted_of_selected 13 90501 ⟨221623, by decide⟩ ⟨13, 2, 0, 221623, 90501, 1965, 16384⟩
    (by decide) selected_cut_07728

theorem selected_cut_07729 : selected 8 ⟨221644, by decide⟩
    (prefixPartial 13 90502) = some ⟨13, 2, 0, 221644, 90502, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_90502_221644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90502 ⟨221644, by decide⟩ :=
  accepted_of_selected 13 90502 ⟨221644, by decide⟩ ⟨13, 2, 0, 221644, 90502, 2013, 16384⟩
    (by decide) selected_cut_07729

theorem selected_cut_07730 : selected 8 ⟨221656, by decide⟩
    (prefixPartial 13 90503) = some ⟨13, 2, 0, 221656, 90503, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_90503_221656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90503 ⟨221656, by decide⟩ :=
  accepted_of_selected 13 90503 ⟨221656, by decide⟩ ⟨13, 2, 0, 221656, 90503, 1301, 16384⟩
    (by decide) selected_cut_07730

theorem unmarked_context_12_22625_221657 : frontier 9 ⟨221657, by decide⟩
    (prefixCache 12 22625) (prefixPartial 12 22625) = false := by
  decide +kernel

theorem node_context_12_22625_221657 : EJMOriginalGlobalDAGData.nodes 9 ⟨221657, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221623, by decide⟩,⟨221644, by decide⟩,⟨221656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22625_221657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22625 ⟨221657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22625
    ⟨221657, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221623, by decide⟩,⟨221644, by decide⟩,⟨221656, by decide⟩]) unmarked_context_12_22625_221657 node_context_12_22625_221657
  intro a
  fin_cases a
  · exact context_13_90500_3444
  · exact context_13_90501_221623
  · exact context_13_90502_221644
  · exact context_13_90503_221656

theorem selected_cut_07731 : selected 9 ⟨221704, by decide⟩
    (prefixPartial 12 22626) = some ⟨12, 2, 0, 221704, 22626, 4033, 65536⟩ := by
  decide +kernel

theorem context_12_22626_221704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22626 ⟨221704, by decide⟩ :=
  accepted_of_selected 12 22626 ⟨221704, by decide⟩ ⟨12, 2, 0, 221704, 22626, 4033, 65536⟩
    (by decide) selected_cut_07731

theorem selected_cut_07732 : selected 9 ⟨221747, by decide⟩
    (prefixPartial 12 22627) = some ⟨12, 2, 0, 221747, 22627, 4057, 65536⟩ := by
  decide +kernel

theorem context_12_22627_221747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22627 ⟨221747, by decide⟩ :=
  accepted_of_selected 12 22627 ⟨221747, by decide⟩ ⟨12, 2, 0, 221747, 22627, 4057, 65536⟩
    (by decide) selected_cut_07732

theorem unmarked_context_11_5656_221748 : frontier 10 ⟨221748, by decide⟩
    (prefixCache 11 5656) (prefixPartial 11 5656) = false := by
  decide +kernel

theorem node_context_11_5656_221748 : EJMOriginalGlobalDAGData.nodes 10 ⟨221748, by decide⟩ =
    .split (coordinate 11) (![⟨221594, by decide⟩,⟨221657, by decide⟩,⟨221704, by decide⟩,⟨221747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5656_221748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5656 ⟨221748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5656
    ⟨221748, by decide⟩ (by decide) (![⟨221594, by decide⟩,⟨221657, by decide⟩,⟨221704, by decide⟩,⟨221747, by decide⟩]) unmarked_context_11_5656_221748 node_context_11_5656_221748
  intro a
  fin_cases a
  · exact context_12_22624_221594
  · exact context_12_22625_221657
  · exact context_12_22626_221704
  · exact context_12_22627_221747

theorem selected_cut_07733 : selected 9 ⟨221794, by decide⟩
    (prefixPartial 12 22628) = some ⟨12, 2, 0, 221794, 22628, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_22628_221794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22628 ⟨221794, by decide⟩ :=
  accepted_of_selected 12 22628 ⟨221794, by decide⟩ ⟨12, 2, 0, 221794, 22628, 3897, 65536⟩
    (by decide) selected_cut_07733

theorem selected_cut_07734 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90516) = some ⟨13, 1, 0, 3444, 90516, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90516_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90516 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90516 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90516, 1, 16384⟩
    (by decide) selected_cut_07734

theorem selected_cut_07735 : selected 8 ⟨221818, by decide⟩
    (prefixPartial 13 90517) = some ⟨13, 2, 0, 221818, 90517, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_90517_221818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90517 ⟨221818, by decide⟩ :=
  accepted_of_selected 13 90517 ⟨221818, by decide⟩ ⟨13, 2, 0, 221818, 90517, 1649, 16384⟩
    (by decide) selected_cut_07735

theorem selected_cut_07736 : selected 8 ⟨221841, by decide⟩
    (prefixPartial 13 90518) = some ⟨13, 2, 0, 221841, 90518, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_90518_221841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90518 ⟨221841, by decide⟩ :=
  accepted_of_selected 13 90518 ⟨221841, by decide⟩ ⟨13, 2, 0, 221841, 90518, 2117, 16384⟩
    (by decide) selected_cut_07736

theorem selected_cut_07737 : selected 8 ⟨221853, by decide⟩
    (prefixPartial 13 90519) = some ⟨13, 2, 0, 221853, 90519, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_90519_221853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90519 ⟨221853, by decide⟩ :=
  accepted_of_selected 13 90519 ⟨221853, by decide⟩ ⟨13, 2, 0, 221853, 90519, 1289, 16384⟩
    (by decide) selected_cut_07737

theorem unmarked_context_12_22629_221854 : frontier 9 ⟨221854, by decide⟩
    (prefixCache 12 22629) (prefixPartial 12 22629) = false := by
  decide +kernel

theorem node_context_12_22629_221854 : EJMOriginalGlobalDAGData.nodes 9 ⟨221854, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221818, by decide⟩,⟨221841, by decide⟩,⟨221853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22629_221854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22629 ⟨221854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22629
    ⟨221854, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221818, by decide⟩,⟨221841, by decide⟩,⟨221853, by decide⟩]) unmarked_context_12_22629_221854 node_context_12_22629_221854
  intro a
  fin_cases a
  · exact context_13_90516_3444
  · exact context_13_90517_221818
  · exact context_13_90518_221841
  · exact context_13_90519_221853

theorem selected_cut_07738 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90520) = some ⟨13, 1, 0, 3444, 90520, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90520_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90520 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90520 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90520, 1, 16384⟩
    (by decide) selected_cut_07738

theorem selected_cut_07739 : selected 8 ⟨221867, by decide⟩
    (prefixPartial 13 90521) = some ⟨13, 2, 0, 221867, 90521, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_90521_221867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90521 ⟨221867, by decide⟩ :=
  accepted_of_selected 13 90521 ⟨221867, by decide⟩ ⟨13, 2, 0, 221867, 90521, 1377, 16384⟩
    (by decide) selected_cut_07739

theorem selected_cut_07740 : selected 8 ⟨221888, by decide⟩
    (prefixPartial 13 90522) = some ⟨13, 2, 0, 221888, 90522, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_90522_221888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90522 ⟨221888, by decide⟩ :=
  accepted_of_selected 13 90522 ⟨221888, by decide⟩ ⟨13, 2, 0, 221888, 90522, 1821, 16384⟩
    (by decide) selected_cut_07740

theorem selected_cut_07741 : selected 8 ⟨221896, by decide⟩
    (prefixPartial 13 90523) = some ⟨13, 2, 0, 221896, 90523, 997, 16384⟩ := by
  decide +kernel

theorem context_13_90523_221896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90523 ⟨221896, by decide⟩ :=
  accepted_of_selected 13 90523 ⟨221896, by decide⟩ ⟨13, 2, 0, 221896, 90523, 997, 16384⟩
    (by decide) selected_cut_07741

theorem unmarked_context_12_22630_221897 : frontier 9 ⟨221897, by decide⟩
    (prefixCache 12 22630) (prefixPartial 12 22630) = false := by
  decide +kernel

theorem node_context_12_22630_221897 : EJMOriginalGlobalDAGData.nodes 9 ⟨221897, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221867, by decide⟩,⟨221888, by decide⟩,⟨221896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22630_221897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22630 ⟨221897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22630
    ⟨221897, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221867, by decide⟩,⟨221888, by decide⟩,⟨221896, by decide⟩]) unmarked_context_12_22630_221897 node_context_12_22630_221897
  intro a
  fin_cases a
  · exact context_13_90520_3444
  · exact context_13_90521_221867
  · exact context_13_90522_221888
  · exact context_13_90523_221896

theorem selected_cut_07742 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90524) = some ⟨13, 1, 0, 3444, 90524, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90524_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90524 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90524 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90524, 1, 16384⟩
    (by decide) selected_cut_07742

theorem selected_cut_07743 : selected 8 ⟨221913, by decide⟩
    (prefixPartial 13 90525) = some ⟨13, 2, 0, 221913, 90525, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_90525_221913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90525 ⟨221913, by decide⟩ :=
  accepted_of_selected 13 90525 ⟨221913, by decide⟩ ⟨13, 2, 0, 221913, 90525, 1365, 16384⟩
    (by decide) selected_cut_07743

theorem selected_cut_07744 : selected 8 ⟨221936, by decide⟩
    (prefixPartial 13 90526) = some ⟨13, 2, 0, 221936, 90526, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_90526_221936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90526 ⟨221936, by decide⟩ :=
  accepted_of_selected 13 90526 ⟨221936, by decide⟩ ⟨13, 2, 0, 221936, 90526, 1853, 16384⟩
    (by decide) selected_cut_07744

theorem selected_cut_07745 : selected 8 ⟨221948, by decide⟩
    (prefixPartial 13 90527) = some ⟨13, 2, 0, 221948, 90527, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_90527_221948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90527 ⟨221948, by decide⟩ :=
  accepted_of_selected 13 90527 ⟨221948, by decide⟩ ⟨13, 2, 0, 221948, 90527, 1061, 16384⟩
    (by decide) selected_cut_07745

theorem unmarked_context_12_22631_221949 : frontier 9 ⟨221949, by decide⟩
    (prefixCache 12 22631) (prefixPartial 12 22631) = false := by
  decide +kernel

theorem node_context_12_22631_221949 : EJMOriginalGlobalDAGData.nodes 9 ⟨221949, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221913, by decide⟩,⟨221936, by decide⟩,⟨221948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22631_221949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22631 ⟨221949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22631
    ⟨221949, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221913, by decide⟩,⟨221936, by decide⟩,⟨221948, by decide⟩]) unmarked_context_12_22631_221949 node_context_12_22631_221949
  intro a
  fin_cases a
  · exact context_13_90524_3444
  · exact context_13_90525_221913
  · exact context_13_90526_221936
  · exact context_13_90527_221948

theorem unmarked_context_11_5657_221950 : frontier 10 ⟨221950, by decide⟩
    (prefixCache 11 5657) (prefixPartial 11 5657) = false := by
  decide +kernel

theorem node_context_11_5657_221950 : EJMOriginalGlobalDAGData.nodes 10 ⟨221950, by decide⟩ =
    .split (coordinate 11) (![⟨221794, by decide⟩,⟨221854, by decide⟩,⟨221897, by decide⟩,⟨221949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5657_221950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5657 ⟨221950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5657
    ⟨221950, by decide⟩ (by decide) (![⟨221794, by decide⟩,⟨221854, by decide⟩,⟨221897, by decide⟩,⟨221949, by decide⟩]) unmarked_context_11_5657_221950 node_context_11_5657_221950
  intro a
  fin_cases a
  · exact context_12_22628_221794
  · exact context_12_22629_221854
  · exact context_12_22630_221897
  · exact context_12_22631_221949

theorem selected_cut_07746 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90528) = some ⟨13, 1, 0, 3444, 90528, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90528_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90528 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90528 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90528, 1, 16384⟩
    (by decide) selected_cut_07746

theorem selected_cut_07747 : selected 8 ⟨221977, by decide⟩
    (prefixPartial 13 90529) = some ⟨13, 2, 0, 221977, 90529, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_90529_221977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90529 ⟨221977, by decide⟩ :=
  accepted_of_selected 13 90529 ⟨221977, by decide⟩ ⟨13, 2, 0, 221977, 90529, 1597, 16384⟩
    (by decide) selected_cut_07747

theorem selected_cut_07748 : selected 8 ⟨221998, by decide⟩
    (prefixPartial 13 90530) = some ⟨13, 2, 0, 221998, 90530, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_90530_221998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90530 ⟨221998, by decide⟩ :=
  accepted_of_selected 13 90530 ⟨221998, by decide⟩ ⟨13, 2, 0, 221998, 90530, 2305, 16384⟩
    (by decide) selected_cut_07748

theorem selected_cut_07749 : selected 8 ⟨222013, by decide⟩
    (prefixPartial 13 90531) = some ⟨13, 2, 0, 222013, 90531, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_90531_222013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90531 ⟨222013, by decide⟩ :=
  accepted_of_selected 13 90531 ⟨222013, by decide⟩ ⟨13, 2, 0, 222013, 90531, 1249, 16384⟩
    (by decide) selected_cut_07749

theorem unmarked_context_12_22632_222014 : frontier 9 ⟨222014, by decide⟩
    (prefixCache 12 22632) (prefixPartial 12 22632) = false := by
  decide +kernel

theorem node_context_12_22632_222014 : EJMOriginalGlobalDAGData.nodes 9 ⟨222014, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨221977, by decide⟩,⟨221998, by decide⟩,⟨222013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22632_222014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22632 ⟨222014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22632
    ⟨222014, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨221977, by decide⟩,⟨221998, by decide⟩,⟨222013, by decide⟩]) unmarked_context_12_22632_222014 node_context_12_22632_222014
  intro a
  fin_cases a
  · exact context_13_90528_3444
  · exact context_13_90529_221977
  · exact context_13_90530_221998
  · exact context_13_90531_222013

theorem selected_cut_07750 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90532) = some ⟨13, 1, 0, 3444, 90532, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90532_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90532 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90532 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90532, 1, 16384⟩
    (by decide) selected_cut_07750

theorem selected_cut_07751 : selected 8 ⟨222057, by decide⟩
    (prefixPartial 13 90533) = some ⟨13, 2, 0, 222057, 90533, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_90533_222057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90533 ⟨222057, by decide⟩ :=
  accepted_of_selected 13 90533 ⟨222057, by decide⟩ ⟨13, 2, 0, 222057, 90533, 2365, 16384⟩
    (by decide) selected_cut_07751

theorem selected_cut_07752 : selected 8 ⟨222112, by decide⟩
    (prefixPartial 13 90534) = some ⟨13, 2, 0, 222112, 90534, 2981, 16384⟩ := by
  decide +kernel

theorem context_13_90534_222112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90534 ⟨222112, by decide⟩ :=
  accepted_of_selected 13 90534 ⟨222112, by decide⟩ ⟨13, 2, 0, 222112, 90534, 2981, 16384⟩
    (by decide) selected_cut_07752

theorem selected_cut_07753 : selected 8 ⟨222152, by decide⟩
    (prefixPartial 13 90535) = some ⟨13, 2, 0, 222152, 90535, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_90535_222152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90535 ⟨222152, by decide⟩ :=
  accepted_of_selected 13 90535 ⟨222152, by decide⟩ ⟨13, 2, 0, 222152, 90535, 1777, 16384⟩
    (by decide) selected_cut_07753

theorem unmarked_context_12_22633_222153 : frontier 9 ⟨222153, by decide⟩
    (prefixCache 12 22633) (prefixPartial 12 22633) = false := by
  decide +kernel

theorem node_context_12_22633_222153 : EJMOriginalGlobalDAGData.nodes 9 ⟨222153, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨222057, by decide⟩,⟨222112, by decide⟩,⟨222152, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22633_222153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22633 ⟨222153, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22633
    ⟨222153, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨222057, by decide⟩,⟨222112, by decide⟩,⟨222152, by decide⟩]) unmarked_context_12_22633_222153 node_context_12_22633_222153
  intro a
  fin_cases a
  · exact context_13_90532_3444
  · exact context_13_90533_222057
  · exact context_13_90534_222112
  · exact context_13_90535_222152

theorem selected_cut_07754 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90536) = some ⟨13, 1, 0, 3444, 90536, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90536_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90536 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90536 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90536, 1, 16384⟩
    (by decide) selected_cut_07754

theorem selected_cut_07755 : selected 8 ⟨222185, by decide⟩
    (prefixPartial 13 90537) = some ⟨13, 2, 0, 222185, 90537, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_90537_222185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90537 ⟨222185, by decide⟩ :=
  accepted_of_selected 13 90537 ⟨222185, by decide⟩ ⟨13, 2, 0, 222185, 90537, 1665, 16384⟩
    (by decide) selected_cut_07755

theorem selected_cut_07756 : selected 8 ⟨222211, by decide⟩
    (prefixPartial 13 90538) = some ⟨13, 2, 0, 222211, 90538, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_90538_222211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90538 ⟨222211, by decide⟩ :=
  accepted_of_selected 13 90538 ⟨222211, by decide⟩ ⟨13, 2, 0, 222211, 90538, 2293, 16384⟩
    (by decide) selected_cut_07756

theorem selected_cut_07757 : selected 8 ⟨222232, by decide⟩
    (prefixPartial 13 90539) = some ⟨13, 2, 0, 222232, 90539, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_90539_222232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90539 ⟨222232, by decide⟩ :=
  accepted_of_selected 13 90539 ⟨222232, by decide⟩ ⟨13, 2, 0, 222232, 90539, 1329, 16384⟩
    (by decide) selected_cut_07757

theorem unmarked_context_12_22634_222233 : frontier 9 ⟨222233, by decide⟩
    (prefixCache 12 22634) (prefixPartial 12 22634) = false := by
  decide +kernel

theorem node_context_12_22634_222233 : EJMOriginalGlobalDAGData.nodes 9 ⟨222233, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨222185, by decide⟩,⟨222211, by decide⟩,⟨222232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22634_222233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22634 ⟨222233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22634
    ⟨222233, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨222185, by decide⟩,⟨222211, by decide⟩,⟨222232, by decide⟩]) unmarked_context_12_22634_222233 node_context_12_22634_222233
  intro a
  fin_cases a
  · exact context_13_90536_3444
  · exact context_13_90537_222185
  · exact context_13_90538_222211
  · exact context_13_90539_222232

theorem selected_cut_07758 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90540) = some ⟨13, 1, 0, 3444, 90540, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90540_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90540 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90540 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90540, 1, 16384⟩
    (by decide) selected_cut_07758

theorem selected_cut_07759 : selected 8 ⟨222261, by decide⟩
    (prefixPartial 13 90541) = some ⟨13, 2, 0, 222261, 90541, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_90541_222261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90541 ⟨222261, by decide⟩ :=
  accepted_of_selected 13 90541 ⟨222261, by decide⟩ ⟨13, 2, 0, 222261, 90541, 1549, 16384⟩
    (by decide) selected_cut_07759

theorem selected_cut_07760 : selected 8 ⟨222294, by decide⟩
    (prefixPartial 13 90542) = some ⟨13, 2, 0, 222294, 90542, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_90542_222294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90542 ⟨222294, by decide⟩ :=
  accepted_of_selected 13 90542 ⟨222294, by decide⟩ ⟨13, 2, 0, 222294, 90542, 2653, 16384⟩
    (by decide) selected_cut_07760

theorem selected_cut_07761 : selected 8 ⟨222312, by decide⟩
    (prefixPartial 13 90543) = some ⟨13, 2, 0, 222312, 90543, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_90543_222312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90543 ⟨222312, by decide⟩ :=
  accepted_of_selected 13 90543 ⟨222312, by decide⟩ ⟨13, 2, 0, 222312, 90543, 1353, 16384⟩
    (by decide) selected_cut_07761

theorem unmarked_context_12_22635_222313 : frontier 9 ⟨222313, by decide⟩
    (prefixCache 12 22635) (prefixPartial 12 22635) = false := by
  decide +kernel

theorem node_context_12_22635_222313 : EJMOriginalGlobalDAGData.nodes 9 ⟨222313, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨222261, by decide⟩,⟨222294, by decide⟩,⟨222312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22635_222313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22635 ⟨222313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22635
    ⟨222313, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨222261, by decide⟩,⟨222294, by decide⟩,⟨222312, by decide⟩]) unmarked_context_12_22635_222313 node_context_12_22635_222313
  intro a
  fin_cases a
  · exact context_13_90540_3444
  · exact context_13_90541_222261
  · exact context_13_90542_222294
  · exact context_13_90543_222312

theorem unmarked_context_11_5658_222314 : frontier 10 ⟨222314, by decide⟩
    (prefixCache 11 5658) (prefixPartial 11 5658) = false := by
  decide +kernel

theorem node_context_11_5658_222314 : EJMOriginalGlobalDAGData.nodes 10 ⟨222314, by decide⟩ =
    .split (coordinate 11) (![⟨222014, by decide⟩,⟨222153, by decide⟩,⟨222233, by decide⟩,⟨222313, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5658_222314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5658 ⟨222314, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5658
    ⟨222314, by decide⟩ (by decide) (![⟨222014, by decide⟩,⟨222153, by decide⟩,⟨222233, by decide⟩,⟨222313, by decide⟩]) unmarked_context_11_5658_222314 node_context_11_5658_222314
  intro a
  fin_cases a
  · exact context_12_22632_222014
  · exact context_12_22633_222153
  · exact context_12_22634_222233
  · exact context_12_22635_222313

theorem selected_cut_07762 : selected 9 ⟨222362, by decide⟩
    (prefixPartial 12 22636) = some ⟨12, 2, 0, 222362, 22636, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_22636_222362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22636 ⟨222362, by decide⟩ :=
  accepted_of_selected 12 22636 ⟨222362, by decide⟩ ⟨12, 2, 0, 222362, 22636, 3805, 65536⟩
    (by decide) selected_cut_07762

theorem selected_cut_07763 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90548) = some ⟨13, 1, 0, 3444, 90548, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90548_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90548 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90548 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90548, 1, 16384⟩
    (by decide) selected_cut_07763

theorem selected_cut_07764 : selected 8 ⟨222380, by decide⟩
    (prefixPartial 13 90549) = some ⟨13, 2, 0, 222380, 90549, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_90549_222380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90549 ⟨222380, by decide⟩ :=
  accepted_of_selected 13 90549 ⟨222380, by decide⟩ ⟨13, 2, 0, 222380, 90549, 1205, 16384⟩
    (by decide) selected_cut_07764

theorem selected_cut_07765 : selected 8 ⟨222413, by decide⟩
    (prefixPartial 13 90550) = some ⟨13, 2, 0, 222413, 90550, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_90550_222413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90550 ⟨222413, by decide⟩ :=
  accepted_of_selected 13 90550 ⟨222413, by decide⟩ ⟨13, 2, 0, 222413, 90550, 2453, 16384⟩
    (by decide) selected_cut_07765

theorem selected_cut_07766 : selected 8 ⟨222430, by decide⟩
    (prefixPartial 13 90551) = some ⟨13, 2, 0, 222430, 90551, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_90551_222430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90551 ⟨222430, by decide⟩ :=
  accepted_of_selected 13 90551 ⟨222430, by decide⟩ ⟨13, 2, 0, 222430, 90551, 1365, 16384⟩
    (by decide) selected_cut_07766

theorem unmarked_context_12_22637_222431 : frontier 9 ⟨222431, by decide⟩
    (prefixCache 12 22637) (prefixPartial 12 22637) = false := by
  decide +kernel

theorem node_context_12_22637_222431 : EJMOriginalGlobalDAGData.nodes 9 ⟨222431, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨222380, by decide⟩,⟨222413, by decide⟩,⟨222430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22637_222431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22637 ⟨222431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22637
    ⟨222431, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨222380, by decide⟩,⟨222413, by decide⟩,⟨222430, by decide⟩]) unmarked_context_12_22637_222431 node_context_12_22637_222431
  intro a
  fin_cases a
  · exact context_13_90548_3444
  · exact context_13_90549_222380
  · exact context_13_90550_222413
  · exact context_13_90551_222430

theorem selected_cut_07767 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90552) = some ⟨13, 1, 0, 3444, 90552, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90552_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90552 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90552 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90552, 1, 16384⟩
    (by decide) selected_cut_07767

theorem selected_cut_07768 : selected 8 ⟨222440, by decide⟩
    (prefixPartial 13 90553) = some ⟨13, 2, 0, 222440, 90553, 909, 16384⟩ := by
  decide +kernel

theorem context_13_90553_222440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90553 ⟨222440, by decide⟩ :=
  accepted_of_selected 13 90553 ⟨222440, by decide⟩ ⟨13, 2, 0, 222440, 90553, 909, 16384⟩
    (by decide) selected_cut_07768

theorem selected_cut_07769 : selected 8 ⟨222471, by decide⟩
    (prefixPartial 13 90554) = some ⟨13, 2, 0, 222471, 90554, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_90554_222471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90554 ⟨222471, by decide⟩ :=
  accepted_of_selected 13 90554 ⟨222471, by decide⟩ ⟨13, 2, 0, 222471, 90554, 2181, 16384⟩
    (by decide) selected_cut_07769

theorem selected_cut_07770 : selected 8 ⟨222481, by decide⟩
    (prefixPartial 13 90555) = some ⟨13, 2, 0, 222481, 90555, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_90555_222481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90555 ⟨222481, by decide⟩ :=
  accepted_of_selected 13 90555 ⟨222481, by decide⟩ ⟨13, 2, 0, 222481, 90555, 1061, 16384⟩
    (by decide) selected_cut_07770

theorem unmarked_context_12_22638_222482 : frontier 9 ⟨222482, by decide⟩
    (prefixCache 12 22638) (prefixPartial 12 22638) = false := by
  decide +kernel

theorem node_context_12_22638_222482 : EJMOriginalGlobalDAGData.nodes 9 ⟨222482, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨222440, by decide⟩,⟨222471, by decide⟩,⟨222481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22638_222482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22638 ⟨222482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22638
    ⟨222482, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨222440, by decide⟩,⟨222471, by decide⟩,⟨222481, by decide⟩]) unmarked_context_12_22638_222482 node_context_12_22638_222482
  intro a
  fin_cases a
  · exact context_13_90552_3444
  · exact context_13_90553_222440
  · exact context_13_90554_222471
  · exact context_13_90555_222481

theorem selected_cut_07771 : selected 9 ⟨222541, by decide⟩
    (prefixPartial 12 22639) = some ⟨12, 2, 0, 222541, 22639, 4085, 65536⟩ := by
  decide +kernel

theorem context_12_22639_222541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22639 ⟨222541, by decide⟩ :=
  accepted_of_selected 12 22639 ⟨222541, by decide⟩ ⟨12, 2, 0, 222541, 22639, 4085, 65536⟩
    (by decide) selected_cut_07771

theorem unmarked_context_11_5659_222542 : frontier 10 ⟨222542, by decide⟩
    (prefixCache 11 5659) (prefixPartial 11 5659) = false := by
  decide +kernel

theorem node_context_11_5659_222542 : EJMOriginalGlobalDAGData.nodes 10 ⟨222542, by decide⟩ =
    .split (coordinate 11) (![⟨222362, by decide⟩,⟨222431, by decide⟩,⟨222482, by decide⟩,⟨222541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5659_222542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5659 ⟨222542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5659
    ⟨222542, by decide⟩ (by decide) (![⟨222362, by decide⟩,⟨222431, by decide⟩,⟨222482, by decide⟩,⟨222541, by decide⟩]) unmarked_context_11_5659_222542 node_context_11_5659_222542
  intro a
  fin_cases a
  · exact context_12_22636_222362
  · exact context_12_22637_222431
  · exact context_12_22638_222482
  · exact context_12_22639_222541

theorem unmarked_context_10_1414_222543 : frontier 11 ⟨222543, by decide⟩
    (prefixCache 10 1414) (prefixPartial 10 1414) = false := by
  decide +kernel

theorem node_context_10_1414_222543 : EJMOriginalGlobalDAGData.nodes 11 ⟨222543, by decide⟩ =
    .split (coordinate 10) (![⟨221748, by decide⟩,⟨221950, by decide⟩,⟨222314, by decide⟩,⟨222542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1414_222543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1414 ⟨222543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1414
    ⟨222543, by decide⟩ (by decide) (![⟨221748, by decide⟩,⟨221950, by decide⟩,⟨222314, by decide⟩,⟨222542, by decide⟩]) unmarked_context_10_1414_222543 node_context_10_1414_222543
  intro a
  fin_cases a
  · exact context_11_5656_221748
  · exact context_11_5657_221950
  · exact context_11_5658_222314
  · exact context_11_5659_222542

theorem selected_cut_07772 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90560) = some ⟨13, 1, 0, 3444, 90560, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90560_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90560 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90560 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90560, 1, 16384⟩
    (by decide) selected_cut_07772

theorem selected_cut_07773 : selected 8 ⟨222566, by decide⟩
    (prefixPartial 13 90561) = some ⟨13, 2, 0, 222566, 90561, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_90561_222566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90561 ⟨222566, by decide⟩ :=
  accepted_of_selected 13 90561 ⟨222566, by decide⟩ ⟨13, 2, 0, 222566, 90561, 1089, 16384⟩
    (by decide) selected_cut_07773

theorem selected_cut_07774 : selected 8 ⟨222609, by decide⟩
    (prefixPartial 13 90562) = some ⟨13, 2, 0, 222609, 90562, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_90562_222609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90562 ⟨222609, by decide⟩ :=
  accepted_of_selected 13 90562 ⟨222609, by decide⟩ ⟨13, 2, 0, 222609, 90562, 2769, 16384⟩
    (by decide) selected_cut_07774

theorem selected_cut_07775 : selected 8 ⟨222629, by decide⟩
    (prefixPartial 13 90563) = some ⟨13, 2, 0, 222629, 90563, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_90563_222629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90563 ⟨222629, by decide⟩ :=
  accepted_of_selected 13 90563 ⟨222629, by decide⟩ ⟨13, 2, 0, 222629, 90563, 1317, 16384⟩
    (by decide) selected_cut_07775

theorem unmarked_context_12_22640_222630 : frontier 9 ⟨222630, by decide⟩
    (prefixCache 12 22640) (prefixPartial 12 22640) = false := by
  decide +kernel

theorem node_context_12_22640_222630 : EJMOriginalGlobalDAGData.nodes 9 ⟨222630, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨222566, by decide⟩,⟨222609, by decide⟩,⟨222629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22640_222630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22640 ⟨222630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22640
    ⟨222630, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨222566, by decide⟩,⟨222609, by decide⟩,⟨222629, by decide⟩]) unmarked_context_12_22640_222630 node_context_12_22640_222630
  intro a
  fin_cases a
  · exact context_13_90560_3444
  · exact context_13_90561_222566
  · exact context_13_90562_222609
  · exact context_13_90563_222629

theorem selected_cut_07776 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 90564) = some ⟨13, 1, 0, 3444, 90564, 1, 16384⟩ := by
  decide +kernel

theorem context_13_90564_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90564 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 90564 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 90564, 1, 16384⟩
    (by decide) selected_cut_07776

theorem selected_cut_07777 : selected 8 ⟨222643, by decide⟩
    (prefixPartial 13 90565) = some ⟨13, 2, 0, 222643, 90565, 817, 16384⟩ := by
  decide +kernel

theorem context_13_90565_222643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90565 ⟨222643, by decide⟩ :=
  accepted_of_selected 13 90565 ⟨222643, by decide⟩ ⟨13, 2, 0, 222643, 90565, 817, 16384⟩
    (by decide) selected_cut_07777

theorem selected_cut_07778 : selected 8 ⟨222670, by decide⟩
    (prefixPartial 13 90566) = some ⟨13, 2, 0, 222670, 90566, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_90566_222670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90566 ⟨222670, by decide⟩ :=
  accepted_of_selected 13 90566 ⟨222670, by decide⟩ ⟨13, 2, 0, 222670, 90566, 2337, 16384⟩
    (by decide) selected_cut_07778

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
