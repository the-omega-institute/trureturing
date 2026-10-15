/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover203
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_19588 : selected 8 ⟨501302, by decide⟩
    (prefixPartial 13 289021) = some ⟨13, 2, 0, 501302, 289021, 3145, 16384⟩ := by
  decide +kernel

theorem context_13_289021_501302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289021 ⟨501302, by decide⟩ :=
  accepted_of_selected 13 289021 ⟨501302, by decide⟩ ⟨13, 2, 0, 501302, 289021, 3145, 16384⟩
    (by decide) selected_cut_19588

theorem selected_cut_19589 : selected 8 ⟨501319, by decide⟩
    (prefixPartial 13 289022) = some ⟨13, 2, 0, 501319, 289022, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_289022_501319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289022 ⟨501319, by decide⟩ :=
  accepted_of_selected 13 289022 ⟨501319, by decide⟩ ⟨13, 2, 0, 501319, 289022, 1785, 16384⟩
    (by decide) selected_cut_19589

theorem selected_cut_19590 : selected 8 ⟨501329, by decide⟩
    (prefixPartial 13 289023) = some ⟨13, 2, 0, 501329, 289023, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_289023_501329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289023 ⟨501329, by decide⟩ :=
  accepted_of_selected 13 289023 ⟨501329, by decide⟩ ⟨13, 2, 0, 501329, 289023, 1093, 16384⟩
    (by decide) selected_cut_19590

theorem unmarked_context_12_72255_501330 : frontier 9 ⟨501330, by decide⟩
    (prefixCache 12 72255) (prefixPartial 12 72255) = false := by
  decide +kernel

theorem node_context_12_72255_501330 : EJMOriginalGlobalDAGData.nodes 9 ⟨501330, by decide⟩ =
    .split (coordinate 12) (![⟨501263, by decide⟩,⟨501302, by decide⟩,⟨501319, by decide⟩,⟨501329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72255_501330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72255 ⟨501330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72255
    ⟨501330, by decide⟩ (by decide) (![⟨501263, by decide⟩,⟨501302, by decide⟩,⟨501319, by decide⟩,⟨501329, by decide⟩]) unmarked_context_12_72255_501330 node_context_12_72255_501330
  intro a
  fin_cases a
  · exact context_13_289020_501263
  · exact context_13_289021_501302
  · exact context_13_289022_501319
  · exact context_13_289023_501329

theorem unmarked_context_11_18063_501331 : frontier 10 ⟨501331, by decide⟩
    (prefixCache 11 18063) (prefixPartial 11 18063) = false := by
  decide +kernel

theorem node_context_11_18063_501331 : EJMOriginalGlobalDAGData.nodes 10 ⟨501331, by decide⟩ =
    .split (coordinate 11) (![⟨501107, by decide⟩,⟨501187, by decide⟩,⟨501260, by decide⟩,⟨501330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18063_501331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18063 ⟨501331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18063
    ⟨501331, by decide⟩ (by decide) (![⟨501107, by decide⟩,⟨501187, by decide⟩,⟨501260, by decide⟩,⟨501330, by decide⟩]) unmarked_context_11_18063_501331 node_context_11_18063_501331
  intro a
  fin_cases a
  · exact context_12_72252_501107
  · exact context_12_72253_501187
  · exact context_12_72254_501260
  · exact context_12_72255_501330

theorem unmarked_context_10_4515_501332 : frontier 11 ⟨501332, by decide⟩
    (prefixCache 10 4515) (prefixPartial 10 4515) = false := by
  decide +kernel

theorem node_context_10_4515_501332 : EJMOriginalGlobalDAGData.nodes 11 ⟨501332, by decide⟩ =
    .split (coordinate 10) (![⟨499995, by decide⟩,⟨500393, by decide⟩,⟨500910, by decide⟩,⟨501331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4515_501332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4515 ⟨501332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4515
    ⟨501332, by decide⟩ (by decide) (![⟨499995, by decide⟩,⟨500393, by decide⟩,⟨500910, by decide⟩,⟨501331, by decide⟩]) unmarked_context_10_4515_501332 node_context_10_4515_501332
  intro a
  fin_cases a
  · exact context_11_18060_499995
  · exact context_11_18061_500393
  · exact context_11_18062_500910
  · exact context_11_18063_501331

theorem unmarked_context_9_1128_501333 : frontier 12 ⟨501333, by decide⟩
    (prefixCache 9 1128) (prefixPartial 9 1128) = false := by
  decide +kernel

theorem node_context_9_1128_501333 : EJMOriginalGlobalDAGData.nodes 12 ⟨501333, by decide⟩ =
    .split (coordinate 9) (![⟨496062, by decide⟩,⟨498317, by decide⟩,⟨499740, by decide⟩,⟨501332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1128_501333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1128 ⟨501333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1128
    ⟨501333, by decide⟩ (by decide) (![⟨496062, by decide⟩,⟨498317, by decide⟩,⟨499740, by decide⟩,⟨501332, by decide⟩]) unmarked_context_9_1128_501333 node_context_9_1128_501333
  intro a
  fin_cases a
  · exact context_10_4512_496062
  · exact context_10_4513_498317
  · exact context_10_4514_499740
  · exact context_10_4515_501332

theorem selected_cut_19591 : selected 9 ⟨501387, by decide⟩
    (prefixPartial 12 72256) = some ⟨12, 2, 0, 501387, 72256, 4017, 65536⟩ := by
  decide +kernel

theorem context_12_72256_501387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72256 ⟨501387, by decide⟩ :=
  accepted_of_selected 12 72256 ⟨501387, by decide⟩ ⟨12, 2, 0, 501387, 72256, 4017, 65536⟩
    (by decide) selected_cut_19591

theorem selected_cut_19592 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289028) = some ⟨13, 1, 0, 3444, 289028, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289028_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289028 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289028 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289028, 1, 16384⟩
    (by decide) selected_cut_19592

theorem selected_cut_19593 : selected 8 ⟨501419, by decide⟩
    (prefixPartial 13 289029) = some ⟨13, 2, 0, 501419, 289029, 2489, 16384⟩ := by
  decide +kernel

theorem context_13_289029_501419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289029 ⟨501419, by decide⟩ :=
  accepted_of_selected 13 289029 ⟨501419, by decide⟩ ⟨13, 2, 0, 501419, 289029, 2489, 16384⟩
    (by decide) selected_cut_19593

theorem selected_cut_19594 : selected 8 ⟨501437, by decide⟩
    (prefixPartial 13 289030) = some ⟨13, 2, 0, 501437, 289030, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_289030_501437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289030 ⟨501437, by decide⟩ :=
  accepted_of_selected 13 289030 ⟨501437, by decide⟩ ⟨13, 2, 0, 501437, 289030, 1153, 16384⟩
    (by decide) selected_cut_19594

theorem selected_cut_19595 : selected 8 ⟨501451, by decide⟩
    (prefixPartial 13 289031) = some ⟨13, 2, 0, 501451, 289031, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_289031_501451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289031 ⟨501451, by decide⟩ :=
  accepted_of_selected 13 289031 ⟨501451, by decide⟩ ⟨13, 2, 0, 501451, 289031, 1041, 16384⟩
    (by decide) selected_cut_19595

theorem unmarked_context_12_72257_501452 : frontier 9 ⟨501452, by decide⟩
    (prefixCache 12 72257) (prefixPartial 12 72257) = false := by
  decide +kernel

theorem node_context_12_72257_501452 : EJMOriginalGlobalDAGData.nodes 9 ⟨501452, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨501419, by decide⟩,⟨501437, by decide⟩,⟨501451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72257_501452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72257 ⟨501452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72257
    ⟨501452, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨501419, by decide⟩,⟨501437, by decide⟩,⟨501451, by decide⟩]) unmarked_context_12_72257_501452 node_context_12_72257_501452
  intro a
  fin_cases a
  · exact context_13_289028_3444
  · exact context_13_289029_501419
  · exact context_13_289030_501437
  · exact context_13_289031_501451

theorem selected_cut_19596 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289032) = some ⟨13, 1, 0, 3444, 289032, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289032_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289032 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289032 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289032, 1, 16384⟩
    (by decide) selected_cut_19596

theorem selected_cut_19597 : selected 8 ⟨501488, by decide⟩
    (prefixPartial 13 289033) = some ⟨13, 2, 0, 501488, 289033, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_289033_501488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289033 ⟨501488, by decide⟩ :=
  accepted_of_selected 13 289033 ⟨501488, by decide⟩ ⟨13, 2, 0, 501488, 289033, 2645, 16384⟩
    (by decide) selected_cut_19597

theorem selected_cut_19598 : selected 8 ⟨501506, by decide⟩
    (prefixPartial 13 289034) = some ⟨13, 2, 0, 501506, 289034, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_289034_501506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289034 ⟨501506, by decide⟩ :=
  accepted_of_selected 13 289034 ⟨501506, by decide⟩ ⟨13, 2, 0, 501506, 289034, 1313, 16384⟩
    (by decide) selected_cut_19598

theorem selected_cut_19599 : selected 8 ⟨501515, by decide⟩
    (prefixPartial 13 289035) = some ⟨13, 2, 0, 501515, 289035, 893, 16384⟩ := by
  decide +kernel

theorem context_13_289035_501515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289035 ⟨501515, by decide⟩ :=
  accepted_of_selected 13 289035 ⟨501515, by decide⟩ ⟨13, 2, 0, 501515, 289035, 893, 16384⟩
    (by decide) selected_cut_19599

theorem unmarked_context_12_72258_501516 : frontier 9 ⟨501516, by decide⟩
    (prefixCache 12 72258) (prefixPartial 12 72258) = false := by
  decide +kernel

theorem node_context_12_72258_501516 : EJMOriginalGlobalDAGData.nodes 9 ⟨501516, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨501488, by decide⟩,⟨501506, by decide⟩,⟨501515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72258_501516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72258 ⟨501516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72258
    ⟨501516, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨501488, by decide⟩,⟨501506, by decide⟩,⟨501515, by decide⟩]) unmarked_context_12_72258_501516 node_context_12_72258_501516
  intro a
  fin_cases a
  · exact context_13_289032_3444
  · exact context_13_289033_501488
  · exact context_13_289034_501506
  · exact context_13_289035_501515

theorem selected_cut_19600 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289036) = some ⟨13, 1, 0, 3444, 289036, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289036_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289036 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289036 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289036, 1, 16384⟩
    (by decide) selected_cut_19600

theorem selected_cut_19601 : selected 8 ⟨501553, by decide⟩
    (prefixPartial 13 289037) = some ⟨13, 2, 0, 501553, 289037, 2925, 16384⟩ := by
  decide +kernel

theorem context_13_289037_501553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289037 ⟨501553, by decide⟩ :=
  accepted_of_selected 13 289037 ⟨501553, by decide⟩ ⟨13, 2, 0, 501553, 289037, 2925, 16384⟩
    (by decide) selected_cut_19601

theorem selected_cut_19602 : selected 8 ⟨501572, by decide⟩
    (prefixPartial 13 289038) = some ⟨13, 2, 0, 501572, 289038, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_289038_501572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289038 ⟨501572, by decide⟩ :=
  accepted_of_selected 13 289038 ⟨501572, by decide⟩ ⟨13, 2, 0, 501572, 289038, 1385, 16384⟩
    (by decide) selected_cut_19602

theorem selected_cut_19603 : selected 8 ⟨501581, by decide⟩
    (prefixPartial 13 289039) = some ⟨13, 2, 0, 501581, 289039, 953, 16384⟩ := by
  decide +kernel

theorem context_13_289039_501581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289039 ⟨501581, by decide⟩ :=
  accepted_of_selected 13 289039 ⟨501581, by decide⟩ ⟨13, 2, 0, 501581, 289039, 953, 16384⟩
    (by decide) selected_cut_19603

theorem unmarked_context_12_72259_501582 : frontier 9 ⟨501582, by decide⟩
    (prefixCache 12 72259) (prefixPartial 12 72259) = false := by
  decide +kernel

theorem node_context_12_72259_501582 : EJMOriginalGlobalDAGData.nodes 9 ⟨501582, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨501553, by decide⟩,⟨501572, by decide⟩,⟨501581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72259_501582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72259 ⟨501582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72259
    ⟨501582, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨501553, by decide⟩,⟨501572, by decide⟩,⟨501581, by decide⟩]) unmarked_context_12_72259_501582 node_context_12_72259_501582
  intro a
  fin_cases a
  · exact context_13_289036_3444
  · exact context_13_289037_501553
  · exact context_13_289038_501572
  · exact context_13_289039_501581

theorem unmarked_context_11_18064_501583 : frontier 10 ⟨501583, by decide⟩
    (prefixCache 11 18064) (prefixPartial 11 18064) = false := by
  decide +kernel

theorem node_context_11_18064_501583 : EJMOriginalGlobalDAGData.nodes 10 ⟨501583, by decide⟩ =
    .split (coordinate 11) (![⟨501387, by decide⟩,⟨501452, by decide⟩,⟨501516, by decide⟩,⟨501582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18064_501583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18064 ⟨501583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18064
    ⟨501583, by decide⟩ (by decide) (![⟨501387, by decide⟩,⟨501452, by decide⟩,⟨501516, by decide⟩,⟨501582, by decide⟩]) unmarked_context_11_18064_501583 node_context_11_18064_501583
  intro a
  fin_cases a
  · exact context_12_72256_501387
  · exact context_12_72257_501452
  · exact context_12_72258_501516
  · exact context_12_72259_501582

theorem selected_cut_19604 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289040) = some ⟨13, 1, 0, 3444, 289040, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289040_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289040 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289040 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289040, 1, 16384⟩
    (by decide) selected_cut_19604

theorem selected_cut_19605 : selected 8 ⟨501618, by decide⟩
    (prefixPartial 13 289041) = some ⟨13, 2, 0, 501618, 289041, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_289041_501618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289041 ⟨501618, by decide⟩ :=
  accepted_of_selected 13 289041 ⟨501618, by decide⟩ ⟨13, 2, 0, 501618, 289041, 2497, 16384⟩
    (by decide) selected_cut_19605

theorem selected_cut_19606 : selected 8 ⟨501638, by decide⟩
    (prefixPartial 13 289042) = some ⟨13, 2, 0, 501638, 289042, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_289042_501638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289042 ⟨501638, by decide⟩ :=
  accepted_of_selected 13 289042 ⟨501638, by decide⟩ ⟨13, 2, 0, 501638, 289042, 1481, 16384⟩
    (by decide) selected_cut_19606

theorem selected_cut_19607 : selected 8 ⟨501646, by decide⟩
    (prefixPartial 13 289043) = some ⟨13, 2, 0, 501646, 289043, 877, 16384⟩ := by
  decide +kernel

theorem context_13_289043_501646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289043 ⟨501646, by decide⟩ :=
  accepted_of_selected 13 289043 ⟨501646, by decide⟩ ⟨13, 2, 0, 501646, 289043, 877, 16384⟩
    (by decide) selected_cut_19607

theorem unmarked_context_12_72260_501647 : frontier 9 ⟨501647, by decide⟩
    (prefixCache 12 72260) (prefixPartial 12 72260) = false := by
  decide +kernel

theorem node_context_12_72260_501647 : EJMOriginalGlobalDAGData.nodes 9 ⟨501647, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨501618, by decide⟩,⟨501638, by decide⟩,⟨501646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72260_501647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72260 ⟨501647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72260
    ⟨501647, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨501618, by decide⟩,⟨501638, by decide⟩,⟨501646, by decide⟩]) unmarked_context_12_72260_501647 node_context_12_72260_501647
  intro a
  fin_cases a
  · exact context_13_289040_3444
  · exact context_13_289041_501618
  · exact context_13_289042_501638
  · exact context_13_289043_501646

theorem selected_cut_19608 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289044) = some ⟨13, 1, 0, 3444, 289044, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289044_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289044 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289044 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289044, 1, 16384⟩
    (by decide) selected_cut_19608

theorem selected_cut_19609 : selected 8 ⟨501675, by decide⟩
    (prefixPartial 13 289045) = some ⟨13, 2, 0, 501675, 289045, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_289045_501675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289045 ⟨501675, by decide⟩ :=
  accepted_of_selected 13 289045 ⟨501675, by decide⟩ ⟨13, 2, 0, 501675, 289045, 2221, 16384⟩
    (by decide) selected_cut_19609

theorem selected_cut_19610 : selected 8 ⟨501693, by decide⟩
    (prefixPartial 13 289046) = some ⟨13, 2, 0, 501693, 289046, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_289046_501693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289046 ⟨501693, by decide⟩ :=
  accepted_of_selected 13 289046 ⟨501693, by decide⟩ ⟨13, 2, 0, 501693, 289046, 1313, 16384⟩
    (by decide) selected_cut_19610

theorem selected_cut_19611 : selected 8 ⟨501702, by decide⟩
    (prefixPartial 13 289047) = some ⟨13, 2, 0, 501702, 289047, 997, 16384⟩ := by
  decide +kernel

theorem context_13_289047_501702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289047 ⟨501702, by decide⟩ :=
  accepted_of_selected 13 289047 ⟨501702, by decide⟩ ⟨13, 2, 0, 501702, 289047, 997, 16384⟩
    (by decide) selected_cut_19611

theorem unmarked_context_12_72261_501703 : frontier 9 ⟨501703, by decide⟩
    (prefixCache 12 72261) (prefixPartial 12 72261) = false := by
  decide +kernel

theorem node_context_12_72261_501703 : EJMOriginalGlobalDAGData.nodes 9 ⟨501703, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨501675, by decide⟩,⟨501693, by decide⟩,⟨501702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72261_501703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72261 ⟨501703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72261
    ⟨501703, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨501675, by decide⟩,⟨501693, by decide⟩,⟨501702, by decide⟩]) unmarked_context_12_72261_501703 node_context_12_72261_501703
  intro a
  fin_cases a
  · exact context_13_289044_3444
  · exact context_13_289045_501675
  · exact context_13_289046_501693
  · exact context_13_289047_501702

theorem selected_cut_19612 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289048) = some ⟨13, 1, 0, 3444, 289048, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289048_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289048 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289048 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289048, 1, 16384⟩
    (by decide) selected_cut_19612

theorem selected_cut_19613 : selected 8 ⟨501740, by decide⟩
    (prefixPartial 13 289049) = some ⟨13, 2, 0, 501740, 289049, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_289049_501740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289049 ⟨501740, by decide⟩ :=
  accepted_of_selected 13 289049 ⟨501740, by decide⟩ ⟨13, 2, 0, 501740, 289049, 2485, 16384⟩
    (by decide) selected_cut_19613

theorem selected_cut_19614 : selected 8 ⟨501764, by decide⟩
    (prefixPartial 13 289050) = some ⟨13, 2, 0, 501764, 289050, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_289050_501764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289050 ⟨501764, by decide⟩ :=
  accepted_of_selected 13 289050 ⟨501764, by decide⟩ ⟨13, 2, 0, 501764, 289050, 1729, 16384⟩
    (by decide) selected_cut_19614

theorem selected_cut_19615 : selected 8 ⟨501771, by decide⟩
    (prefixPartial 13 289051) = some ⟨13, 2, 0, 501771, 289051, 893, 16384⟩ := by
  decide +kernel

theorem context_13_289051_501771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289051 ⟨501771, by decide⟩ :=
  accepted_of_selected 13 289051 ⟨501771, by decide⟩ ⟨13, 2, 0, 501771, 289051, 893, 16384⟩
    (by decide) selected_cut_19615

theorem unmarked_context_12_72262_501772 : frontier 9 ⟨501772, by decide⟩
    (prefixCache 12 72262) (prefixPartial 12 72262) = false := by
  decide +kernel

theorem node_context_12_72262_501772 : EJMOriginalGlobalDAGData.nodes 9 ⟨501772, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨501740, by decide⟩,⟨501764, by decide⟩,⟨501771, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72262_501772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72262 ⟨501772, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72262
    ⟨501772, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨501740, by decide⟩,⟨501764, by decide⟩,⟨501771, by decide⟩]) unmarked_context_12_72262_501772 node_context_12_72262_501772
  intro a
  fin_cases a
  · exact context_13_289048_3444
  · exact context_13_289049_501740
  · exact context_13_289050_501764
  · exact context_13_289051_501771

theorem selected_cut_19616 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289052) = some ⟨13, 1, 0, 3444, 289052, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289052_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289052 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289052 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289052, 1, 16384⟩
    (by decide) selected_cut_19616

theorem selected_cut_19617 : selected 8 ⟨501822, by decide⟩
    (prefixPartial 13 289053) = some ⟨13, 2, 0, 501822, 289053, 2697, 16384⟩ := by
  decide +kernel

theorem context_13_289053_501822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289053 ⟨501822, by decide⟩ :=
  accepted_of_selected 13 289053 ⟨501822, by decide⟩ ⟨13, 2, 0, 501822, 289053, 2697, 16384⟩
    (by decide) selected_cut_19617

theorem selected_cut_19618 : selected 8 ⟨501849, by decide⟩
    (prefixPartial 13 289054) = some ⟨13, 2, 0, 501849, 289054, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_289054_501849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289054 ⟨501849, by decide⟩ :=
  accepted_of_selected 13 289054 ⟨501849, by decide⟩ ⟨13, 2, 0, 501849, 289054, 1793, 16384⟩
    (by decide) selected_cut_19618

theorem selected_cut_19619 : selected 8 ⟨501859, by decide⟩
    (prefixPartial 13 289055) = some ⟨13, 2, 0, 501859, 289055, 997, 16384⟩ := by
  decide +kernel

theorem context_13_289055_501859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289055 ⟨501859, by decide⟩ :=
  accepted_of_selected 13 289055 ⟨501859, by decide⟩ ⟨13, 2, 0, 501859, 289055, 997, 16384⟩
    (by decide) selected_cut_19619

theorem unmarked_context_12_72263_501860 : frontier 9 ⟨501860, by decide⟩
    (prefixCache 12 72263) (prefixPartial 12 72263) = false := by
  decide +kernel

theorem node_context_12_72263_501860 : EJMOriginalGlobalDAGData.nodes 9 ⟨501860, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨501822, by decide⟩,⟨501849, by decide⟩,⟨501859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72263_501860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72263 ⟨501860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72263
    ⟨501860, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨501822, by decide⟩,⟨501849, by decide⟩,⟨501859, by decide⟩]) unmarked_context_12_72263_501860 node_context_12_72263_501860
  intro a
  fin_cases a
  · exact context_13_289052_3444
  · exact context_13_289053_501822
  · exact context_13_289054_501849
  · exact context_13_289055_501859

theorem unmarked_context_11_18065_501861 : frontier 10 ⟨501861, by decide⟩
    (prefixCache 11 18065) (prefixPartial 11 18065) = false := by
  decide +kernel

theorem node_context_11_18065_501861 : EJMOriginalGlobalDAGData.nodes 10 ⟨501861, by decide⟩ =
    .split (coordinate 11) (![⟨501647, by decide⟩,⟨501703, by decide⟩,⟨501772, by decide⟩,⟨501860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18065_501861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18065 ⟨501861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18065
    ⟨501861, by decide⟩ (by decide) (![⟨501647, by decide⟩,⟨501703, by decide⟩,⟨501772, by decide⟩,⟨501860, by decide⟩]) unmarked_context_11_18065_501861 node_context_11_18065_501861
  intro a
  fin_cases a
  · exact context_12_72260_501647
  · exact context_12_72261_501703
  · exact context_12_72262_501772
  · exact context_12_72263_501860

theorem selected_cut_19620 : selected 9 ⟨501912, by decide⟩
    (prefixPartial 12 72264) = some ⟨12, 2, 0, 501912, 72264, 3661, 65536⟩ := by
  decide +kernel

theorem context_12_72264_501912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72264 ⟨501912, by decide⟩ :=
  accepted_of_selected 12 72264 ⟨501912, by decide⟩ ⟨12, 2, 0, 501912, 72264, 3661, 65536⟩
    (by decide) selected_cut_19620

theorem selected_cut_19621 : selected 9 ⟨501963, by decide⟩
    (prefixPartial 12 72265) = some ⟨12, 2, 0, 501963, 72265, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_72265_501963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72265 ⟨501963, by decide⟩ :=
  accepted_of_selected 12 72265 ⟨501963, by decide⟩ ⟨12, 2, 0, 501963, 72265, 3657, 65536⟩
    (by decide) selected_cut_19621

theorem selected_cut_19622 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289064) = some ⟨13, 1, 0, 3444, 289064, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289064_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289064 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289064 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289064, 1, 16384⟩
    (by decide) selected_cut_19622

theorem selected_cut_19623 : selected 8 ⟨502044, by decide⟩
    (prefixPartial 13 289065) = some ⟨13, 2, 0, 502044, 289065, 3157, 16384⟩ := by
  decide +kernel

theorem context_13_289065_502044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289065 ⟨502044, by decide⟩ :=
  accepted_of_selected 13 289065 ⟨502044, by decide⟩ ⟨13, 2, 0, 502044, 289065, 3157, 16384⟩
    (by decide) selected_cut_19623

theorem selected_cut_19624 : selected 8 ⟨502103, by decide⟩
    (prefixPartial 13 289066) = some ⟨13, 2, 0, 502103, 289066, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_289066_502103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289066 ⟨502103, by decide⟩ :=
  accepted_of_selected 13 289066 ⟨502103, by decide⟩ ⟨13, 2, 0, 502103, 289066, 2281, 16384⟩
    (by decide) selected_cut_19624

theorem selected_cut_19625 : selected 8 ⟨502123, by decide⟩
    (prefixPartial 13 289067) = some ⟨13, 2, 0, 502123, 289067, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_289067_502123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289067 ⟨502123, by decide⟩ :=
  accepted_of_selected 13 289067 ⟨502123, by decide⟩ ⟨13, 2, 0, 502123, 289067, 1125, 16384⟩
    (by decide) selected_cut_19625

theorem unmarked_context_12_72266_502124 : frontier 9 ⟨502124, by decide⟩
    (prefixCache 12 72266) (prefixPartial 12 72266) = false := by
  decide +kernel

theorem node_context_12_72266_502124 : EJMOriginalGlobalDAGData.nodes 9 ⟨502124, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502044, by decide⟩,⟨502103, by decide⟩,⟨502123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72266_502124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72266 ⟨502124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72266
    ⟨502124, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502044, by decide⟩,⟨502103, by decide⟩,⟨502123, by decide⟩]) unmarked_context_12_72266_502124 node_context_12_72266_502124
  intro a
  fin_cases a
  · exact context_13_289064_3444
  · exact context_13_289065_502044
  · exact context_13_289066_502103
  · exact context_13_289067_502123

theorem selected_cut_19626 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289068) = some ⟨13, 1, 0, 3444, 289068, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289068_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289068 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289068 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289068, 1, 16384⟩
    (by decide) selected_cut_19626

theorem selected_cut_19627 : selected 8 ⟨502162, by decide⟩
    (prefixPartial 13 289069) = some ⟨13, 2, 0, 502162, 289069, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_289069_502162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289069 ⟨502162, by decide⟩ :=
  accepted_of_selected 13 289069 ⟨502162, by decide⟩ ⟨13, 2, 0, 502162, 289069, 2329, 16384⟩
    (by decide) selected_cut_19627

theorem selected_cut_19628 : selected 8 ⟨502178, by decide⟩
    (prefixPartial 13 289070) = some ⟨13, 2, 0, 502178, 289070, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_289070_502178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289070 ⟨502178, by decide⟩ :=
  accepted_of_selected 13 289070 ⟨502178, by decide⟩ ⟨13, 2, 0, 502178, 289070, 1453, 16384⟩
    (by decide) selected_cut_19628

theorem selected_cut_19629 : selected 8 ⟨502187, by decide⟩
    (prefixPartial 13 289071) = some ⟨13, 2, 0, 502187, 289071, 833, 16384⟩ := by
  decide +kernel

theorem context_13_289071_502187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289071 ⟨502187, by decide⟩ :=
  accepted_of_selected 13 289071 ⟨502187, by decide⟩ ⟨13, 2, 0, 502187, 289071, 833, 16384⟩
    (by decide) selected_cut_19629

theorem unmarked_context_12_72267_502188 : frontier 9 ⟨502188, by decide⟩
    (prefixCache 12 72267) (prefixPartial 12 72267) = false := by
  decide +kernel

theorem node_context_12_72267_502188 : EJMOriginalGlobalDAGData.nodes 9 ⟨502188, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502162, by decide⟩,⟨502178, by decide⟩,⟨502187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72267_502188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72267 ⟨502188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72267
    ⟨502188, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502162, by decide⟩,⟨502178, by decide⟩,⟨502187, by decide⟩]) unmarked_context_12_72267_502188 node_context_12_72267_502188
  intro a
  fin_cases a
  · exact context_13_289068_3444
  · exact context_13_289069_502162
  · exact context_13_289070_502178
  · exact context_13_289071_502187

theorem unmarked_context_11_18066_502189 : frontier 10 ⟨502189, by decide⟩
    (prefixCache 11 18066) (prefixPartial 11 18066) = false := by
  decide +kernel

theorem node_context_11_18066_502189 : EJMOriginalGlobalDAGData.nodes 10 ⟨502189, by decide⟩ =
    .split (coordinate 11) (![⟨501912, by decide⟩,⟨501963, by decide⟩,⟨502124, by decide⟩,⟨502188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18066_502189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18066 ⟨502189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18066
    ⟨502189, by decide⟩ (by decide) (![⟨501912, by decide⟩,⟨501963, by decide⟩,⟨502124, by decide⟩,⟨502188, by decide⟩]) unmarked_context_11_18066_502189 node_context_11_18066_502189
  intro a
  fin_cases a
  · exact context_12_72264_501912
  · exact context_12_72265_501963
  · exact context_12_72266_502124
  · exact context_12_72267_502188

theorem selected_cut_19630 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289072) = some ⟨13, 1, 0, 3444, 289072, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289072_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289072 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289072 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289072, 1, 16384⟩
    (by decide) selected_cut_19630

theorem selected_cut_19631 : selected 8 ⟨502217, by decide⟩
    (prefixPartial 13 289073) = some ⟨13, 2, 0, 502217, 289073, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_289073_502217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289073 ⟨502217, by decide⟩ :=
  accepted_of_selected 13 289073 ⟨502217, by decide⟩ ⟨13, 2, 0, 502217, 289073, 2381, 16384⟩
    (by decide) selected_cut_19631

theorem selected_cut_19632 : selected 8 ⟨502235, by decide⟩
    (prefixPartial 13 289074) = some ⟨13, 2, 0, 502235, 289074, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_289074_502235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289074 ⟨502235, by decide⟩ :=
  accepted_of_selected 13 289074 ⟨502235, by decide⟩ ⟨13, 2, 0, 502235, 289074, 1497, 16384⟩
    (by decide) selected_cut_19632

theorem selected_cut_19633 : selected 8 ⟨502243, by decide⟩
    (prefixPartial 13 289075) = some ⟨13, 2, 0, 502243, 289075, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_289075_502243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289075 ⟨502243, by decide⟩ :=
  accepted_of_selected 13 289075 ⟨502243, by decide⟩ ⟨13, 2, 0, 502243, 289075, 1009, 16384⟩
    (by decide) selected_cut_19633

theorem unmarked_context_12_72268_502244 : frontier 9 ⟨502244, by decide⟩
    (prefixCache 12 72268) (prefixPartial 12 72268) = false := by
  decide +kernel

theorem node_context_12_72268_502244 : EJMOriginalGlobalDAGData.nodes 9 ⟨502244, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502217, by decide⟩,⟨502235, by decide⟩,⟨502243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72268_502244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72268 ⟨502244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72268
    ⟨502244, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502217, by decide⟩,⟨502235, by decide⟩,⟨502243, by decide⟩]) unmarked_context_12_72268_502244 node_context_12_72268_502244
  intro a
  fin_cases a
  · exact context_13_289072_3444
  · exact context_13_289073_502217
  · exact context_13_289074_502235
  · exact context_13_289075_502243

theorem selected_cut_19634 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289076) = some ⟨13, 1, 0, 3444, 289076, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289076_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289076 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289076 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289076, 1, 16384⟩
    (by decide) selected_cut_19634

theorem selected_cut_19635 : selected 8 ⟨502270, by decide⟩
    (prefixPartial 13 289077) = some ⟨13, 2, 0, 502270, 289077, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_289077_502270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289077 ⟨502270, by decide⟩ :=
  accepted_of_selected 13 289077 ⟨502270, by decide⟩ ⟨13, 2, 0, 502270, 289077, 2081, 16384⟩
    (by decide) selected_cut_19635

theorem selected_cut_19636 : selected 8 ⟨502290, by decide⟩
    (prefixPartial 13 289078) = some ⟨13, 2, 0, 502290, 289078, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_289078_502290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289078 ⟨502290, by decide⟩ :=
  accepted_of_selected 13 289078 ⟨502290, by decide⟩ ⟨13, 2, 0, 502290, 289078, 1305, 16384⟩
    (by decide) selected_cut_19636

theorem selected_cut_19637 : selected 8 ⟨502301, by decide⟩
    (prefixPartial 13 289079) = some ⟨13, 2, 0, 502301, 289079, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_289079_502301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289079 ⟨502301, by decide⟩ :=
  accepted_of_selected 13 289079 ⟨502301, by decide⟩ ⟨13, 2, 0, 502301, 289079, 1133, 16384⟩
    (by decide) selected_cut_19637

theorem unmarked_context_12_72269_502302 : frontier 9 ⟨502302, by decide⟩
    (prefixCache 12 72269) (prefixPartial 12 72269) = false := by
  decide +kernel

theorem node_context_12_72269_502302 : EJMOriginalGlobalDAGData.nodes 9 ⟨502302, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502270, by decide⟩,⟨502290, by decide⟩,⟨502301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72269_502302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72269 ⟨502302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72269
    ⟨502302, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502270, by decide⟩,⟨502290, by decide⟩,⟨502301, by decide⟩]) unmarked_context_12_72269_502302 node_context_12_72269_502302
  intro a
  fin_cases a
  · exact context_13_289076_3444
  · exact context_13_289077_502270
  · exact context_13_289078_502290
  · exact context_13_289079_502301

theorem selected_cut_19638 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289080) = some ⟨13, 1, 0, 3444, 289080, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289080_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289080 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289080 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289080, 1, 16384⟩
    (by decide) selected_cut_19638

theorem selected_cut_19639 : selected 8 ⟨502336, by decide⟩
    (prefixPartial 13 289081) = some ⟨13, 2, 0, 502336, 289081, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_289081_502336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289081 ⟨502336, by decide⟩ :=
  accepted_of_selected 13 289081 ⟨502336, by decide⟩ ⟨13, 2, 0, 502336, 289081, 2553, 16384⟩
    (by decide) selected_cut_19639

theorem selected_cut_19640 : selected 8 ⟨502363, by decide⟩
    (prefixPartial 13 289082) = some ⟨13, 2, 0, 502363, 289082, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_289082_502363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289082 ⟨502363, by decide⟩ :=
  accepted_of_selected 13 289082 ⟨502363, by decide⟩ ⟨13, 2, 0, 502363, 289082, 1709, 16384⟩
    (by decide) selected_cut_19640

theorem selected_cut_19641 : selected 8 ⟨502375, by decide⟩
    (prefixPartial 13 289083) = some ⟨13, 2, 0, 502375, 289083, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_289083_502375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289083 ⟨502375, by decide⟩ :=
  accepted_of_selected 13 289083 ⟨502375, by decide⟩ ⟨13, 2, 0, 502375, 289083, 1001, 16384⟩
    (by decide) selected_cut_19641

theorem unmarked_context_12_72270_502376 : frontier 9 ⟨502376, by decide⟩
    (prefixCache 12 72270) (prefixPartial 12 72270) = false := by
  decide +kernel

theorem node_context_12_72270_502376 : EJMOriginalGlobalDAGData.nodes 9 ⟨502376, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502336, by decide⟩,⟨502363, by decide⟩,⟨502375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72270_502376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72270 ⟨502376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72270
    ⟨502376, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502336, by decide⟩,⟨502363, by decide⟩,⟨502375, by decide⟩]) unmarked_context_12_72270_502376 node_context_12_72270_502376
  intro a
  fin_cases a
  · exact context_13_289080_3444
  · exact context_13_289081_502336
  · exact context_13_289082_502363
  · exact context_13_289083_502375

theorem selected_cut_19642 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289084) = some ⟨13, 1, 0, 3444, 289084, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289084_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289084 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289084 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289084, 1, 16384⟩
    (by decide) selected_cut_19642

theorem selected_cut_19643 : selected 8 ⟨502404, by decide⟩
    (prefixPartial 13 289085) = some ⟨13, 2, 0, 502404, 289085, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_289085_502404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289085 ⟨502404, by decide⟩ :=
  accepted_of_selected 13 289085 ⟨502404, by decide⟩ ⟨13, 2, 0, 502404, 289085, 2505, 16384⟩
    (by decide) selected_cut_19643

theorem selected_cut_19644 : selected 8 ⟨502423, by decide⟩
    (prefixPartial 13 289086) = some ⟨13, 2, 0, 502423, 289086, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_289086_502423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289086 ⟨502423, by decide⟩ :=
  accepted_of_selected 13 289086 ⟨502423, by decide⟩ ⟨13, 2, 0, 502423, 289086, 1789, 16384⟩
    (by decide) selected_cut_19644

theorem selected_cut_19645 : selected 8 ⟨502428, by decide⟩
    (prefixPartial 13 289087) = some ⟨13, 2, 0, 502428, 289087, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_289087_502428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289087 ⟨502428, by decide⟩ :=
  accepted_of_selected 13 289087 ⟨502428, by decide⟩ ⟨13, 2, 0, 502428, 289087, 1113, 16384⟩
    (by decide) selected_cut_19645

theorem unmarked_context_12_72271_502429 : frontier 9 ⟨502429, by decide⟩
    (prefixCache 12 72271) (prefixPartial 12 72271) = false := by
  decide +kernel

theorem node_context_12_72271_502429 : EJMOriginalGlobalDAGData.nodes 9 ⟨502429, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502404, by decide⟩,⟨502423, by decide⟩,⟨502428, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72271_502429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72271 ⟨502429, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72271
    ⟨502429, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502404, by decide⟩,⟨502423, by decide⟩,⟨502428, by decide⟩]) unmarked_context_12_72271_502429 node_context_12_72271_502429
  intro a
  fin_cases a
  · exact context_13_289084_3444
  · exact context_13_289085_502404
  · exact context_13_289086_502423
  · exact context_13_289087_502428

theorem unmarked_context_11_18067_502430 : frontier 10 ⟨502430, by decide⟩
    (prefixCache 11 18067) (prefixPartial 11 18067) = false := by
  decide +kernel

theorem node_context_11_18067_502430 : EJMOriginalGlobalDAGData.nodes 10 ⟨502430, by decide⟩ =
    .split (coordinate 11) (![⟨502244, by decide⟩,⟨502302, by decide⟩,⟨502376, by decide⟩,⟨502429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18067_502430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18067 ⟨502430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18067
    ⟨502430, by decide⟩ (by decide) (![⟨502244, by decide⟩,⟨502302, by decide⟩,⟨502376, by decide⟩,⟨502429, by decide⟩]) unmarked_context_11_18067_502430 node_context_11_18067_502430
  intro a
  fin_cases a
  · exact context_12_72268_502244
  · exact context_12_72269_502302
  · exact context_12_72270_502376
  · exact context_12_72271_502429

theorem unmarked_context_10_4516_502431 : frontier 11 ⟨502431, by decide⟩
    (prefixCache 10 4516) (prefixPartial 10 4516) = false := by
  decide +kernel

theorem node_context_10_4516_502431 : EJMOriginalGlobalDAGData.nodes 11 ⟨502431, by decide⟩ =
    .split (coordinate 10) (![⟨501583, by decide⟩,⟨501861, by decide⟩,⟨502189, by decide⟩,⟨502430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4516_502431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4516 ⟨502431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4516
    ⟨502431, by decide⟩ (by decide) (![⟨501583, by decide⟩,⟨501861, by decide⟩,⟨502189, by decide⟩,⟨502430, by decide⟩]) unmarked_context_10_4516_502431 node_context_10_4516_502431
  intro a
  fin_cases a
  · exact context_11_18064_501583
  · exact context_11_18065_501861
  · exact context_11_18066_502189
  · exact context_11_18067_502430

theorem selected_cut_19646 : selected 9 ⟨502483, by decide⟩
    (prefixPartial 12 72272) = some ⟨12, 2, 0, 502483, 72272, 3685, 65536⟩ := by
  decide +kernel

theorem context_12_72272_502483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72272 ⟨502483, by decide⟩ :=
  accepted_of_selected 12 72272 ⟨502483, by decide⟩ ⟨12, 2, 0, 502483, 72272, 3685, 65536⟩
    (by decide) selected_cut_19646

theorem selected_cut_19647 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289092) = some ⟨13, 1, 0, 3444, 289092, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289092_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289092 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289092 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289092, 1, 16384⟩
    (by decide) selected_cut_19647

theorem selected_cut_19648 : selected 8 ⟨502514, by decide⟩
    (prefixPartial 13 289093) = some ⟨13, 2, 0, 502514, 289093, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_289093_502514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289093 ⟨502514, by decide⟩ :=
  accepted_of_selected 13 289093 ⟨502514, by decide⟩ ⟨13, 2, 0, 502514, 289093, 1953, 16384⟩
    (by decide) selected_cut_19648

theorem selected_cut_19649 : selected 8 ⟨502530, by decide⟩
    (prefixPartial 13 289094) = some ⟨13, 2, 0, 502530, 289094, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_289094_502530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289094 ⟨502530, by decide⟩ :=
  accepted_of_selected 13 289094 ⟨502530, by decide⟩ ⟨13, 2, 0, 502530, 289094, 1173, 16384⟩
    (by decide) selected_cut_19649

theorem selected_cut_19650 : selected 8 ⟨502550, by decide⟩
    (prefixPartial 13 289095) = some ⟨13, 2, 0, 502550, 289095, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_289095_502550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289095 ⟨502550, by decide⟩ :=
  accepted_of_selected 13 289095 ⟨502550, by decide⟩ ⟨13, 2, 0, 502550, 289095, 1073, 16384⟩
    (by decide) selected_cut_19650

theorem unmarked_context_12_72273_502551 : frontier 9 ⟨502551, by decide⟩
    (prefixCache 12 72273) (prefixPartial 12 72273) = false := by
  decide +kernel

theorem node_context_12_72273_502551 : EJMOriginalGlobalDAGData.nodes 9 ⟨502551, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502514, by decide⟩,⟨502530, by decide⟩,⟨502550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72273_502551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72273 ⟨502551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72273
    ⟨502551, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502514, by decide⟩,⟨502530, by decide⟩,⟨502550, by decide⟩]) unmarked_context_12_72273_502551 node_context_12_72273_502551
  intro a
  fin_cases a
  · exact context_13_289092_3444
  · exact context_13_289093_502514
  · exact context_13_289094_502530
  · exact context_13_289095_502550

theorem selected_cut_19651 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289096) = some ⟨13, 1, 0, 3444, 289096, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289096_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289096 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289096 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289096, 1, 16384⟩
    (by decide) selected_cut_19651

theorem selected_cut_19652 : selected 8 ⟨502578, by decide⟩
    (prefixPartial 13 289097) = some ⟨13, 2, 0, 502578, 289097, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_289097_502578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289097 ⟨502578, by decide⟩ :=
  accepted_of_selected 13 289097 ⟨502578, by decide⟩ ⟨13, 2, 0, 502578, 289097, 2153, 16384⟩
    (by decide) selected_cut_19652

theorem selected_cut_19653 : selected 8 ⟨502597, by decide⟩
    (prefixPartial 13 289098) = some ⟨13, 2, 0, 502597, 289098, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_289098_502597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289098 ⟨502597, by decide⟩ :=
  accepted_of_selected 13 289098 ⟨502597, by decide⟩ ⟨13, 2, 0, 502597, 289098, 1285, 16384⟩
    (by decide) selected_cut_19653

theorem selected_cut_19654 : selected 8 ⟨502609, by decide⟩
    (prefixPartial 13 289099) = some ⟨13, 2, 0, 502609, 289099, 965, 16384⟩ := by
  decide +kernel

theorem context_13_289099_502609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289099 ⟨502609, by decide⟩ :=
  accepted_of_selected 13 289099 ⟨502609, by decide⟩ ⟨13, 2, 0, 502609, 289099, 965, 16384⟩
    (by decide) selected_cut_19654

theorem unmarked_context_12_72274_502610 : frontier 9 ⟨502610, by decide⟩
    (prefixCache 12 72274) (prefixPartial 12 72274) = false := by
  decide +kernel

theorem node_context_12_72274_502610 : EJMOriginalGlobalDAGData.nodes 9 ⟨502610, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502578, by decide⟩,⟨502597, by decide⟩,⟨502609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72274_502610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72274 ⟨502610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72274
    ⟨502610, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502578, by decide⟩,⟨502597, by decide⟩,⟨502609, by decide⟩]) unmarked_context_12_72274_502610 node_context_12_72274_502610
  intro a
  fin_cases a
  · exact context_13_289096_3444
  · exact context_13_289097_502578
  · exact context_13_289098_502597
  · exact context_13_289099_502609

theorem selected_cut_19655 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289100) = some ⟨13, 1, 0, 3444, 289100, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289100_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289100 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289100 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289100, 1, 16384⟩
    (by decide) selected_cut_19655

theorem selected_cut_19656 : selected 8 ⟨502643, by decide⟩
    (prefixPartial 13 289101) = some ⟨13, 2, 0, 502643, 289101, 2393, 16384⟩ := by
  decide +kernel

theorem context_13_289101_502643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289101 ⟨502643, by decide⟩ :=
  accepted_of_selected 13 289101 ⟨502643, by decide⟩ ⟨13, 2, 0, 502643, 289101, 2393, 16384⟩
    (by decide) selected_cut_19656

theorem selected_cut_19657 : selected 8 ⟨502667, by decide⟩
    (prefixPartial 13 289102) = some ⟨13, 2, 0, 502667, 289102, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_289102_502667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289102 ⟨502667, by decide⟩ :=
  accepted_of_selected 13 289102 ⟨502667, by decide⟩ ⟨13, 2, 0, 502667, 289102, 1529, 16384⟩
    (by decide) selected_cut_19657

theorem selected_cut_19658 : selected 8 ⟨502679, by decide⟩
    (prefixPartial 13 289103) = some ⟨13, 2, 0, 502679, 289103, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_289103_502679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289103 ⟨502679, by decide⟩ :=
  accepted_of_selected 13 289103 ⟨502679, by decide⟩ ⟨13, 2, 0, 502679, 289103, 1009, 16384⟩
    (by decide) selected_cut_19658

theorem unmarked_context_12_72275_502680 : frontier 9 ⟨502680, by decide⟩
    (prefixCache 12 72275) (prefixPartial 12 72275) = false := by
  decide +kernel

theorem node_context_12_72275_502680 : EJMOriginalGlobalDAGData.nodes 9 ⟨502680, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502643, by decide⟩,⟨502667, by decide⟩,⟨502679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72275_502680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72275 ⟨502680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72275
    ⟨502680, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502643, by decide⟩,⟨502667, by decide⟩,⟨502679, by decide⟩]) unmarked_context_12_72275_502680 node_context_12_72275_502680
  intro a
  fin_cases a
  · exact context_13_289100_3444
  · exact context_13_289101_502643
  · exact context_13_289102_502667
  · exact context_13_289103_502679

theorem unmarked_context_11_18068_502681 : frontier 10 ⟨502681, by decide⟩
    (prefixCache 11 18068) (prefixPartial 11 18068) = false := by
  decide +kernel

theorem node_context_11_18068_502681 : EJMOriginalGlobalDAGData.nodes 10 ⟨502681, by decide⟩ =
    .split (coordinate 11) (![⟨502483, by decide⟩,⟨502551, by decide⟩,⟨502610, by decide⟩,⟨502680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18068_502681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18068 ⟨502681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18068
    ⟨502681, by decide⟩ (by decide) (![⟨502483, by decide⟩,⟨502551, by decide⟩,⟨502610, by decide⟩,⟨502680, by decide⟩]) unmarked_context_11_18068_502681 node_context_11_18068_502681
  intro a
  fin_cases a
  · exact context_12_72272_502483
  · exact context_12_72273_502551
  · exact context_12_72274_502610
  · exact context_12_72275_502680

theorem selected_cut_19659 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289104) = some ⟨13, 1, 0, 3444, 289104, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289104_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289104 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289104 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289104, 1, 16384⟩
    (by decide) selected_cut_19659

theorem selected_cut_19660 : selected 8 ⟨502709, by decide⟩
    (prefixPartial 13 289105) = some ⟨13, 2, 0, 502709, 289105, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_289105_502709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289105 ⟨502709, by decide⟩ :=
  accepted_of_selected 13 289105 ⟨502709, by decide⟩ ⟨13, 2, 0, 502709, 289105, 2093, 16384⟩
    (by decide) selected_cut_19660

theorem selected_cut_19661 : selected 8 ⟨502731, by decide⟩
    (prefixPartial 13 289106) = some ⟨13, 2, 0, 502731, 289106, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_289106_502731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289106 ⟨502731, by decide⟩ :=
  accepted_of_selected 13 289106 ⟨502731, by decide⟩ ⟨13, 2, 0, 502731, 289106, 1505, 16384⟩
    (by decide) selected_cut_19661

theorem selected_cut_19662 : selected 8 ⟨502738, by decide⟩
    (prefixPartial 13 289107) = some ⟨13, 2, 0, 502738, 289107, 981, 16384⟩ := by
  decide +kernel

theorem context_13_289107_502738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289107 ⟨502738, by decide⟩ :=
  accepted_of_selected 13 289107 ⟨502738, by decide⟩ ⟨13, 2, 0, 502738, 289107, 981, 16384⟩
    (by decide) selected_cut_19662

theorem unmarked_context_12_72276_502739 : frontier 9 ⟨502739, by decide⟩
    (prefixCache 12 72276) (prefixPartial 12 72276) = false := by
  decide +kernel

theorem node_context_12_72276_502739 : EJMOriginalGlobalDAGData.nodes 9 ⟨502739, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502709, by decide⟩,⟨502731, by decide⟩,⟨502738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72276_502739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72276 ⟨502739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72276
    ⟨502739, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502709, by decide⟩,⟨502731, by decide⟩,⟨502738, by decide⟩]) unmarked_context_12_72276_502739 node_context_12_72276_502739
  intro a
  fin_cases a
  · exact context_13_289104_3444
  · exact context_13_289105_502709
  · exact context_13_289106_502731
  · exact context_13_289107_502738

theorem selected_cut_19663 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289108) = some ⟨13, 1, 0, 3444, 289108, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289108_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289108 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289108 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289108, 1, 16384⟩
    (by decide) selected_cut_19663

theorem selected_cut_19664 : selected 8 ⟨502763, by decide⟩
    (prefixPartial 13 289109) = some ⟨13, 2, 0, 502763, 289109, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_289109_502763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289109 ⟨502763, by decide⟩ :=
  accepted_of_selected 13 289109 ⟨502763, by decide⟩ ⟨13, 2, 0, 502763, 289109, 1729, 16384⟩
    (by decide) selected_cut_19664

theorem selected_cut_19665 : selected 8 ⟨502781, by decide⟩
    (prefixPartial 13 289110) = some ⟨13, 2, 0, 502781, 289110, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_289110_502781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289110 ⟨502781, by decide⟩ :=
  accepted_of_selected 13 289110 ⟨502781, by decide⟩ ⟨13, 2, 0, 502781, 289110, 1341, 16384⟩
    (by decide) selected_cut_19665

theorem selected_cut_19666 : selected 8 ⟨502792, by decide⟩
    (prefixPartial 13 289111) = some ⟨13, 2, 0, 502792, 289111, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_289111_502792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289111 ⟨502792, by decide⟩ :=
  accepted_of_selected 13 289111 ⟨502792, by decide⟩ ⟨13, 2, 0, 502792, 289111, 1025, 16384⟩
    (by decide) selected_cut_19666

theorem unmarked_context_12_72277_502793 : frontier 9 ⟨502793, by decide⟩
    (prefixCache 12 72277) (prefixPartial 12 72277) = false := by
  decide +kernel

theorem node_context_12_72277_502793 : EJMOriginalGlobalDAGData.nodes 9 ⟨502793, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502763, by decide⟩,⟨502781, by decide⟩,⟨502792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72277_502793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72277 ⟨502793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72277
    ⟨502793, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502763, by decide⟩,⟨502781, by decide⟩,⟨502792, by decide⟩]) unmarked_context_12_72277_502793 node_context_12_72277_502793
  intro a
  fin_cases a
  · exact context_13_289108_3444
  · exact context_13_289109_502763
  · exact context_13_289110_502781
  · exact context_13_289111_502792

theorem selected_cut_19667 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289112) = some ⟨13, 1, 0, 3444, 289112, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289112_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289112 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289112 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289112, 1, 16384⟩
    (by decide) selected_cut_19667

theorem selected_cut_19668 : selected 8 ⟨502813, by decide⟩
    (prefixPartial 13 289113) = some ⟨13, 2, 0, 502813, 289113, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_289113_502813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289113 ⟨502813, by decide⟩ :=
  accepted_of_selected 13 289113 ⟨502813, by decide⟩ ⟨13, 2, 0, 502813, 289113, 2001, 16384⟩
    (by decide) selected_cut_19668

theorem selected_cut_19669 : selected 8 ⟨502837, by decide⟩
    (prefixPartial 13 289114) = some ⟨13, 2, 0, 502837, 289114, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_289114_502837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289114 ⟨502837, by decide⟩ :=
  accepted_of_selected 13 289114 ⟨502837, by decide⟩ ⟨13, 2, 0, 502837, 289114, 1657, 16384⟩
    (by decide) selected_cut_19669

theorem selected_cut_19670 : selected 8 ⟨502847, by decide⟩
    (prefixPartial 13 289115) = some ⟨13, 2, 0, 502847, 289115, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_289115_502847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289115 ⟨502847, by decide⟩ :=
  accepted_of_selected 13 289115 ⟨502847, by decide⟩ ⟨13, 2, 0, 502847, 289115, 1017, 16384⟩
    (by decide) selected_cut_19670

theorem unmarked_context_12_72278_502848 : frontier 9 ⟨502848, by decide⟩
    (prefixCache 12 72278) (prefixPartial 12 72278) = false := by
  decide +kernel

theorem node_context_12_72278_502848 : EJMOriginalGlobalDAGData.nodes 9 ⟨502848, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502813, by decide⟩,⟨502837, by decide⟩,⟨502847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72278_502848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72278 ⟨502848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72278
    ⟨502848, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502813, by decide⟩,⟨502837, by decide⟩,⟨502847, by decide⟩]) unmarked_context_12_72278_502848 node_context_12_72278_502848
  intro a
  fin_cases a
  · exact context_13_289112_3444
  · exact context_13_289113_502813
  · exact context_13_289114_502837
  · exact context_13_289115_502847

theorem selected_cut_19671 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289116) = some ⟨13, 1, 0, 3444, 289116, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289116_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289116 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289116 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289116, 1, 16384⟩
    (by decide) selected_cut_19671

theorem selected_cut_19672 : selected 8 ⟨502882, by decide⟩
    (prefixPartial 13 289117) = some ⟨13, 2, 0, 502882, 289117, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_289117_502882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289117 ⟨502882, by decide⟩ :=
  accepted_of_selected 13 289117 ⟨502882, by decide⟩ ⟨13, 2, 0, 502882, 289117, 2265, 16384⟩
    (by decide) selected_cut_19672

theorem selected_cut_19673 : selected 8 ⟨502912, by decide⟩
    (prefixPartial 13 289118) = some ⟨13, 2, 0, 502912, 289118, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_289118_502912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289118 ⟨502912, by decide⟩ :=
  accepted_of_selected 13 289118 ⟨502912, by decide⟩ ⟨13, 2, 0, 502912, 289118, 1917, 16384⟩
    (by decide) selected_cut_19673

theorem selected_cut_19674 : selected 8 ⟨502925, by decide⟩
    (prefixPartial 13 289119) = some ⟨13, 2, 0, 502925, 289119, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_289119_502925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289119 ⟨502925, by decide⟩ :=
  accepted_of_selected 13 289119 ⟨502925, by decide⟩ ⟨13, 2, 0, 502925, 289119, 1049, 16384⟩
    (by decide) selected_cut_19674

theorem unmarked_context_12_72279_502926 : frontier 9 ⟨502926, by decide⟩
    (prefixCache 12 72279) (prefixPartial 12 72279) = false := by
  decide +kernel

theorem node_context_12_72279_502926 : EJMOriginalGlobalDAGData.nodes 9 ⟨502926, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨502882, by decide⟩,⟨502912, by decide⟩,⟨502925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72279_502926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72279 ⟨502926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72279
    ⟨502926, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨502882, by decide⟩,⟨502912, by decide⟩,⟨502925, by decide⟩]) unmarked_context_12_72279_502926 node_context_12_72279_502926
  intro a
  fin_cases a
  · exact context_13_289116_3444
  · exact context_13_289117_502882
  · exact context_13_289118_502912
  · exact context_13_289119_502925

theorem unmarked_context_11_18069_502927 : frontier 10 ⟨502927, by decide⟩
    (prefixCache 11 18069) (prefixPartial 11 18069) = false := by
  decide +kernel

theorem node_context_11_18069_502927 : EJMOriginalGlobalDAGData.nodes 10 ⟨502927, by decide⟩ =
    .split (coordinate 11) (![⟨502739, by decide⟩,⟨502793, by decide⟩,⟨502848, by decide⟩,⟨502926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18069_502927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18069 ⟨502927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18069
    ⟨502927, by decide⟩ (by decide) (![⟨502739, by decide⟩,⟨502793, by decide⟩,⟨502848, by decide⟩,⟨502926, by decide⟩]) unmarked_context_11_18069_502927 node_context_11_18069_502927
  intro a
  fin_cases a
  · exact context_12_72276_502739
  · exact context_12_72277_502793
  · exact context_12_72278_502848
  · exact context_12_72279_502926

theorem selected_cut_19675 : selected 9 ⟨502977, by decide⟩
    (prefixPartial 12 72280) = some ⟨12, 2, 0, 502977, 72280, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_72280_502977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72280 ⟨502977, by decide⟩ :=
  accepted_of_selected 12 72280 ⟨502977, by decide⟩ ⟨12, 2, 0, 502977, 72280, 3757, 65536⟩
    (by decide) selected_cut_19675

theorem selected_cut_19676 : selected 9 ⟨503044, by decide⟩
    (prefixPartial 12 72281) = some ⟨12, 2, 0, 503044, 72281, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_72281_503044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72281 ⟨503044, by decide⟩ :=
  accepted_of_selected 12 72281 ⟨503044, by decide⟩ ⟨12, 2, 0, 503044, 72281, 3553, 65536⟩
    (by decide) selected_cut_19676

theorem selected_cut_19677 : selected 9 ⟨503155, by decide⟩
    (prefixPartial 12 72282) = some ⟨12, 2, 0, 503155, 72282, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_72282_503155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72282 ⟨503155, by decide⟩ :=
  accepted_of_selected 12 72282 ⟨503155, by decide⟩ ⟨12, 2, 0, 503155, 72282, 2669, 65536⟩
    (by decide) selected_cut_19677

theorem selected_cut_19678 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289132) = some ⟨13, 1, 0, 3444, 289132, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289132_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289132 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289132 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289132, 1, 16384⟩
    (by decide) selected_cut_19678

theorem selected_cut_19679 : selected 8 ⟨503185, by decide⟩
    (prefixPartial 13 289133) = some ⟨13, 2, 0, 503185, 289133, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_289133_503185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289133 ⟨503185, by decide⟩ :=
  accepted_of_selected 13 289133 ⟨503185, by decide⟩ ⟨13, 2, 0, 503185, 289133, 1797, 16384⟩
    (by decide) selected_cut_19679

theorem selected_cut_19680 : selected 8 ⟨503207, by decide⟩
    (prefixPartial 13 289134) = some ⟨13, 2, 0, 503207, 289134, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_289134_503207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289134 ⟨503207, by decide⟩ :=
  accepted_of_selected 13 289134 ⟨503207, by decide⟩ ⟨13, 2, 0, 503207, 289134, 1681, 16384⟩
    (by decide) selected_cut_19680

theorem selected_cut_19681 : selected 8 ⟨503218, by decide⟩
    (prefixPartial 13 289135) = some ⟨13, 2, 0, 503218, 289135, 949, 16384⟩ := by
  decide +kernel

theorem context_13_289135_503218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289135 ⟨503218, by decide⟩ :=
  accepted_of_selected 13 289135 ⟨503218, by decide⟩ ⟨13, 2, 0, 503218, 289135, 949, 16384⟩
    (by decide) selected_cut_19681

theorem unmarked_context_12_72283_503219 : frontier 9 ⟨503219, by decide⟩
    (prefixCache 12 72283) (prefixPartial 12 72283) = false := by
  decide +kernel

theorem node_context_12_72283_503219 : EJMOriginalGlobalDAGData.nodes 9 ⟨503219, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨503185, by decide⟩,⟨503207, by decide⟩,⟨503218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72283_503219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72283 ⟨503219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72283
    ⟨503219, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨503185, by decide⟩,⟨503207, by decide⟩,⟨503218, by decide⟩]) unmarked_context_12_72283_503219 node_context_12_72283_503219
  intro a
  fin_cases a
  · exact context_13_289132_3444
  · exact context_13_289133_503185
  · exact context_13_289134_503207
  · exact context_13_289135_503218

theorem unmarked_context_11_18070_503220 : frontier 10 ⟨503220, by decide⟩
    (prefixCache 11 18070) (prefixPartial 11 18070) = false := by
  decide +kernel

theorem node_context_11_18070_503220 : EJMOriginalGlobalDAGData.nodes 10 ⟨503220, by decide⟩ =
    .split (coordinate 11) (![⟨502977, by decide⟩,⟨503044, by decide⟩,⟨503155, by decide⟩,⟨503219, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18070_503220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18070 ⟨503220, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18070
    ⟨503220, by decide⟩ (by decide) (![⟨502977, by decide⟩,⟨503044, by decide⟩,⟨503155, by decide⟩,⟨503219, by decide⟩]) unmarked_context_11_18070_503220 node_context_11_18070_503220
  intro a
  fin_cases a
  · exact context_12_72280_502977
  · exact context_12_72281_503044
  · exact context_12_72282_503155
  · exact context_12_72283_503219

theorem selected_cut_19682 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289136) = some ⟨13, 1, 0, 3444, 289136, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289136_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289136 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289136 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289136, 1, 16384⟩
    (by decide) selected_cut_19682

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
