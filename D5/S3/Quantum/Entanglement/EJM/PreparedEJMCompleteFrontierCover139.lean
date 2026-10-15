/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover138
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_13347 : selected 8 ⟨351321, by decide⟩
    (prefixPartial 13 106677) = some ⟨13, 2, 0, 351321, 106677, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_106677_351321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106677 ⟨351321, by decide⟩ :=
  accepted_of_selected 13 106677 ⟨351321, by decide⟩ ⟨13, 2, 0, 351321, 106677, 1901, 16384⟩
    (by decide) selected_cut_13347

theorem selected_cut_13348 : selected 8 ⟨351337, by decide⟩
    (prefixPartial 13 106678) = some ⟨13, 2, 0, 351337, 106678, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_106678_351337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106678 ⟨351337, by decide⟩ :=
  accepted_of_selected 13 106678 ⟨351337, by decide⟩ ⟨13, 2, 0, 351337, 106678, 1201, 16384⟩
    (by decide) selected_cut_13348

theorem selected_cut_13349 : selected 8 ⟨351341, by decide⟩
    (prefixPartial 13 106679) = some ⟨13, 2, 0, 351341, 106679, 701, 16384⟩ := by
  decide +kernel

theorem context_13_106679_351341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106679 ⟨351341, by decide⟩ :=
  accepted_of_selected 13 106679 ⟨351341, by decide⟩ ⟨13, 2, 0, 351341, 106679, 701, 16384⟩
    (by decide) selected_cut_13349

theorem unmarked_context_12_26669_351342 : frontier 9 ⟨351342, by decide⟩
    (prefixCache 12 26669) (prefixPartial 12 26669) = false := by
  decide +kernel

theorem node_context_12_26669_351342 : EJMOriginalGlobalDAGData.nodes 9 ⟨351342, by decide⟩ =
    .split (coordinate 12) (![⟨351298, by decide⟩,⟨351321, by decide⟩,⟨351337, by decide⟩,⟨351341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26669_351342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26669 ⟨351342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26669
    ⟨351342, by decide⟩ (by decide) (![⟨351298, by decide⟩,⟨351321, by decide⟩,⟨351337, by decide⟩,⟨351341, by decide⟩]) unmarked_context_12_26669_351342 node_context_12_26669_351342
  intro a
  fin_cases a
  · exact context_13_106676_351298
  · exact context_13_106677_351321
  · exact context_13_106678_351337
  · exact context_13_106679_351341

theorem selected_cut_13350 : selected 8 ⟨351350, by decide⟩
    (prefixPartial 13 106680) = some ⟨13, 2, 0, 351350, 106680, 505, 16384⟩ := by
  decide +kernel

theorem context_13_106680_351350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106680 ⟨351350, by decide⟩ :=
  accepted_of_selected 13 106680 ⟨351350, by decide⟩ ⟨13, 2, 0, 351350, 106680, 505, 16384⟩
    (by decide) selected_cut_13350

theorem selected_cut_13351 : selected 8 ⟨351372, by decide⟩
    (prefixPartial 13 106681) = some ⟨13, 2, 0, 351372, 106681, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_106681_351372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106681 ⟨351372, by decide⟩ :=
  accepted_of_selected 13 106681 ⟨351372, by decide⟩ ⟨13, 2, 0, 351372, 106681, 2137, 16384⟩
    (by decide) selected_cut_13351

theorem selected_cut_13352 : selected 8 ⟨351387, by decide⟩
    (prefixPartial 13 106682) = some ⟨13, 2, 0, 351387, 106682, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_106682_351387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106682 ⟨351387, by decide⟩ :=
  accepted_of_selected 13 106682 ⟨351387, by decide⟩ ⟨13, 2, 0, 351387, 106682, 1137, 16384⟩
    (by decide) selected_cut_13352

theorem selected_cut_13353 : selected 8 ⟨351393, by decide⟩
    (prefixPartial 13 106683) = some ⟨13, 2, 0, 351393, 106683, 721, 16384⟩ := by
  decide +kernel

theorem context_13_106683_351393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106683 ⟨351393, by decide⟩ :=
  accepted_of_selected 13 106683 ⟨351393, by decide⟩ ⟨13, 2, 0, 351393, 106683, 721, 16384⟩
    (by decide) selected_cut_13353

theorem unmarked_context_12_26670_351394 : frontier 9 ⟨351394, by decide⟩
    (prefixCache 12 26670) (prefixPartial 12 26670) = false := by
  decide +kernel

theorem node_context_12_26670_351394 : EJMOriginalGlobalDAGData.nodes 9 ⟨351394, by decide⟩ =
    .split (coordinate 12) (![⟨351350, by decide⟩,⟨351372, by decide⟩,⟨351387, by decide⟩,⟨351393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26670_351394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26670 ⟨351394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26670
    ⟨351394, by decide⟩ (by decide) (![⟨351350, by decide⟩,⟨351372, by decide⟩,⟨351387, by decide⟩,⟨351393, by decide⟩]) unmarked_context_12_26670_351394 node_context_12_26670_351394
  intro a
  fin_cases a
  · exact context_13_106680_351350
  · exact context_13_106681_351372
  · exact context_13_106682_351387
  · exact context_13_106683_351393

theorem selected_cut_13354 : selected 8 ⟨351402, by decide⟩
    (prefixPartial 13 106684) = some ⟨13, 2, 0, 351402, 106684, 525, 16384⟩ := by
  decide +kernel

theorem context_13_106684_351402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106684 ⟨351402, by decide⟩ :=
  accepted_of_selected 13 106684 ⟨351402, by decide⟩ ⟨13, 2, 0, 351402, 106684, 525, 16384⟩
    (by decide) selected_cut_13354

theorem selected_cut_13355 : selected 8 ⟨351429, by decide⟩
    (prefixPartial 13 106685) = some ⟨13, 2, 0, 351429, 106685, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_106685_351429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106685 ⟨351429, by decide⟩ :=
  accepted_of_selected 13 106685 ⟨351429, by decide⟩ ⟨13, 2, 0, 351429, 106685, 2265, 16384⟩
    (by decide) selected_cut_13355

theorem selected_cut_13356 : selected 8 ⟨351445, by decide⟩
    (prefixPartial 13 106686) = some ⟨13, 2, 0, 351445, 106686, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_106686_351445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106686 ⟨351445, by decide⟩ :=
  accepted_of_selected 13 106686 ⟨351445, by decide⟩ ⟨13, 2, 0, 351445, 106686, 1121, 16384⟩
    (by decide) selected_cut_13356

theorem selected_cut_13357 : selected 8 ⟨351449, by decide⟩
    (prefixPartial 13 106687) = some ⟨13, 2, 0, 351449, 106687, 721, 16384⟩ := by
  decide +kernel

theorem context_13_106687_351449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106687 ⟨351449, by decide⟩ :=
  accepted_of_selected 13 106687 ⟨351449, by decide⟩ ⟨13, 2, 0, 351449, 106687, 721, 16384⟩
    (by decide) selected_cut_13357

theorem unmarked_context_12_26671_351450 : frontier 9 ⟨351450, by decide⟩
    (prefixCache 12 26671) (prefixPartial 12 26671) = false := by
  decide +kernel

theorem node_context_12_26671_351450 : EJMOriginalGlobalDAGData.nodes 9 ⟨351450, by decide⟩ =
    .split (coordinate 12) (![⟨351402, by decide⟩,⟨351429, by decide⟩,⟨351445, by decide⟩,⟨351449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26671_351450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26671 ⟨351450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26671
    ⟨351450, by decide⟩ (by decide) (![⟨351402, by decide⟩,⟨351429, by decide⟩,⟨351445, by decide⟩,⟨351449, by decide⟩]) unmarked_context_12_26671_351450 node_context_12_26671_351450
  intro a
  fin_cases a
  · exact context_13_106684_351402
  · exact context_13_106685_351429
  · exact context_13_106686_351445
  · exact context_13_106687_351449

theorem unmarked_context_11_6667_351451 : frontier 10 ⟨351451, by decide⟩
    (prefixCache 11 6667) (prefixPartial 11 6667) = false := by
  decide +kernel

theorem node_context_11_6667_351451 : EJMOriginalGlobalDAGData.nodes 10 ⟨351451, by decide⟩ =
    .split (coordinate 11) (![⟨351287, by decide⟩,⟨351342, by decide⟩,⟨351394, by decide⟩,⟨351450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6667_351451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6667 ⟨351451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6667
    ⟨351451, by decide⟩ (by decide) (![⟨351287, by decide⟩,⟨351342, by decide⟩,⟨351394, by decide⟩,⟨351450, by decide⟩]) unmarked_context_11_6667_351451 node_context_11_6667_351451
  intro a
  fin_cases a
  · exact context_12_26668_351287
  · exact context_12_26669_351342
  · exact context_12_26670_351394
  · exact context_12_26671_351450

theorem unmarked_context_10_1666_351452 : frontier 11 ⟨351452, by decide⟩
    (prefixCache 10 1666) (prefixPartial 10 1666) = false := by
  decide +kernel

theorem node_context_10_1666_351452 : EJMOriginalGlobalDAGData.nodes 11 ⟨351452, by decide⟩ =
    .split (coordinate 10) (![⟨350747, by decide⟩,⟨350977, by decide⟩,⟨351237, by decide⟩,⟨351451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1666_351452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1666 ⟨351452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1666
    ⟨351452, by decide⟩ (by decide) (![⟨350747, by decide⟩,⟨350977, by decide⟩,⟨351237, by decide⟩,⟨351451, by decide⟩]) unmarked_context_10_1666_351452 node_context_10_1666_351452
  intro a
  fin_cases a
  · exact context_11_6664_350747
  · exact context_11_6665_350977
  · exact context_11_6666_351237
  · exact context_11_6667_351451

theorem selected_cut_13358 : selected 8 ⟨351466, by decide⟩
    (prefixPartial 13 106688) = some ⟨13, 2, 0, 351466, 106688, 993, 16384⟩ := by
  decide +kernel

theorem context_13_106688_351466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106688 ⟨351466, by decide⟩ :=
  accepted_of_selected 13 106688 ⟨351466, by decide⟩ ⟨13, 2, 0, 351466, 106688, 993, 16384⟩
    (by decide) selected_cut_13358

theorem selected_cut_13359 : selected 8 ⟨351505, by decide⟩
    (prefixPartial 13 106689) = some ⟨13, 2, 0, 351505, 106689, 3357, 16384⟩ := by
  decide +kernel

theorem context_13_106689_351505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106689 ⟨351505, by decide⟩ :=
  accepted_of_selected 13 106689 ⟨351505, by decide⟩ ⟨13, 2, 0, 351505, 106689, 3357, 16384⟩
    (by decide) selected_cut_13359

theorem selected_cut_13360 : selected 8 ⟨351522, by decide⟩
    (prefixPartial 13 106690) = some ⟨13, 2, 0, 351522, 106690, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_106690_351522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106690 ⟨351522, by decide⟩ :=
  accepted_of_selected 13 106690 ⟨351522, by decide⟩ ⟨13, 2, 0, 351522, 106690, 2045, 16384⟩
    (by decide) selected_cut_13360

theorem selected_cut_13361 : selected 8 ⟨351534, by decide⟩
    (prefixPartial 13 106691) = some ⟨13, 2, 0, 351534, 106691, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_106691_351534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106691 ⟨351534, by decide⟩ :=
  accepted_of_selected 13 106691 ⟨351534, by decide⟩ ⟨13, 2, 0, 351534, 106691, 1161, 16384⟩
    (by decide) selected_cut_13361

theorem unmarked_context_12_26672_351535 : frontier 9 ⟨351535, by decide⟩
    (prefixCache 12 26672) (prefixPartial 12 26672) = false := by
  decide +kernel

theorem node_context_12_26672_351535 : EJMOriginalGlobalDAGData.nodes 9 ⟨351535, by decide⟩ =
    .split (coordinate 12) (![⟨351466, by decide⟩,⟨351505, by decide⟩,⟨351522, by decide⟩,⟨351534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26672_351535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26672 ⟨351535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26672
    ⟨351535, by decide⟩ (by decide) (![⟨351466, by decide⟩,⟨351505, by decide⟩,⟨351522, by decide⟩,⟨351534, by decide⟩]) unmarked_context_12_26672_351535 node_context_12_26672_351535
  intro a
  fin_cases a
  · exact context_13_106688_351466
  · exact context_13_106689_351505
  · exact context_13_106690_351522
  · exact context_13_106691_351534

theorem selected_cut_13362 : selected 8 ⟨351543, by decide⟩
    (prefixPartial 13 106692) = some ⟨13, 2, 0, 351543, 106692, 569, 16384⟩ := by
  decide +kernel

theorem context_13_106692_351543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106692 ⟨351543, by decide⟩ :=
  accepted_of_selected 13 106692 ⟨351543, by decide⟩ ⟨13, 2, 0, 351543, 106692, 569, 16384⟩
    (by decide) selected_cut_13362

theorem selected_cut_13363 : selected 8 ⟨351564, by decide⟩
    (prefixPartial 13 106693) = some ⟨13, 2, 0, 351564, 106693, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_106693_351564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106693 ⟨351564, by decide⟩ :=
  accepted_of_selected 13 106693 ⟨351564, by decide⟩ ⟨13, 2, 0, 351564, 106693, 1565, 16384⟩
    (by decide) selected_cut_13363

theorem selected_cut_13364 : selected 8 ⟨351578, by decide⟩
    (prefixPartial 13 106694) = some ⟨13, 2, 0, 351578, 106694, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_106694_351578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106694 ⟨351578, by decide⟩ :=
  accepted_of_selected 13 106694 ⟨351578, by decide⟩ ⟨13, 2, 0, 351578, 106694, 1257, 16384⟩
    (by decide) selected_cut_13364

theorem selected_cut_13365 : selected 8 ⟨351584, by decide⟩
    (prefixPartial 13 106695) = some ⟨13, 2, 0, 351584, 106695, 729, 16384⟩ := by
  decide +kernel

theorem context_13_106695_351584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106695 ⟨351584, by decide⟩ :=
  accepted_of_selected 13 106695 ⟨351584, by decide⟩ ⟨13, 2, 0, 351584, 106695, 729, 16384⟩
    (by decide) selected_cut_13365

theorem unmarked_context_12_26673_351585 : frontier 9 ⟨351585, by decide⟩
    (prefixCache 12 26673) (prefixPartial 12 26673) = false := by
  decide +kernel

theorem node_context_12_26673_351585 : EJMOriginalGlobalDAGData.nodes 9 ⟨351585, by decide⟩ =
    .split (coordinate 12) (![⟨351543, by decide⟩,⟨351564, by decide⟩,⟨351578, by decide⟩,⟨351584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26673_351585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26673 ⟨351585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26673
    ⟨351585, by decide⟩ (by decide) (![⟨351543, by decide⟩,⟨351564, by decide⟩,⟨351578, by decide⟩,⟨351584, by decide⟩]) unmarked_context_12_26673_351585 node_context_12_26673_351585
  intro a
  fin_cases a
  · exact context_13_106692_351543
  · exact context_13_106693_351564
  · exact context_13_106694_351578
  · exact context_13_106695_351584

theorem selected_cut_13366 : selected 8 ⟨351592, by decide⟩
    (prefixPartial 13 106696) = some ⟨13, 2, 0, 351592, 106696, 557, 16384⟩ := by
  decide +kernel

theorem context_13_106696_351592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106696 ⟨351592, by decide⟩ :=
  accepted_of_selected 13 106696 ⟨351592, by decide⟩ ⟨13, 2, 0, 351592, 106696, 557, 16384⟩
    (by decide) selected_cut_13366

theorem selected_cut_13367 : selected 8 ⟨351620, by decide⟩
    (prefixPartial 13 106697) = some ⟨13, 2, 0, 351620, 106697, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_106697_351620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106697 ⟨351620, by decide⟩ :=
  accepted_of_selected 13 106697 ⟨351620, by decide⟩ ⟨13, 2, 0, 351620, 106697, 1953, 16384⟩
    (by decide) selected_cut_13367

theorem selected_cut_13368 : selected 8 ⟨351636, by decide⟩
    (prefixPartial 13 106698) = some ⟨13, 2, 0, 351636, 106698, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_106698_351636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106698 ⟨351636, by decide⟩ :=
  accepted_of_selected 13 106698 ⟨351636, by decide⟩ ⟨13, 2, 0, 351636, 106698, 1281, 16384⟩
    (by decide) selected_cut_13368

theorem selected_cut_13369 : selected 8 ⟨351640, by decide⟩
    (prefixPartial 13 106699) = some ⟨13, 2, 0, 351640, 106699, 721, 16384⟩ := by
  decide +kernel

theorem context_13_106699_351640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106699 ⟨351640, by decide⟩ :=
  accepted_of_selected 13 106699 ⟨351640, by decide⟩ ⟨13, 2, 0, 351640, 106699, 721, 16384⟩
    (by decide) selected_cut_13369

theorem unmarked_context_12_26674_351641 : frontier 9 ⟨351641, by decide⟩
    (prefixCache 12 26674) (prefixPartial 12 26674) = false := by
  decide +kernel

theorem node_context_12_26674_351641 : EJMOriginalGlobalDAGData.nodes 9 ⟨351641, by decide⟩ =
    .split (coordinate 12) (![⟨351592, by decide⟩,⟨351620, by decide⟩,⟨351636, by decide⟩,⟨351640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26674_351641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26674 ⟨351641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26674
    ⟨351641, by decide⟩ (by decide) (![⟨351592, by decide⟩,⟨351620, by decide⟩,⟨351636, by decide⟩,⟨351640, by decide⟩]) unmarked_context_12_26674_351641 node_context_12_26674_351641
  intro a
  fin_cases a
  · exact context_13_106696_351592
  · exact context_13_106697_351620
  · exact context_13_106698_351636
  · exact context_13_106699_351640

theorem selected_cut_13370 : selected 8 ⟨351648, by decide⟩
    (prefixPartial 13 106700) = some ⟨13, 2, 0, 351648, 106700, 593, 16384⟩ := by
  decide +kernel

theorem context_13_106700_351648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106700 ⟨351648, by decide⟩ :=
  accepted_of_selected 13 106700 ⟨351648, by decide⟩ ⟨13, 2, 0, 351648, 106700, 593, 16384⟩
    (by decide) selected_cut_13370

theorem selected_cut_13371 : selected 8 ⟨351673, by decide⟩
    (prefixPartial 13 106701) = some ⟨13, 2, 0, 351673, 106701, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_106701_351673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106701 ⟨351673, by decide⟩ :=
  accepted_of_selected 13 106701 ⟨351673, by decide⟩ ⟨13, 2, 0, 351673, 106701, 2173, 16384⟩
    (by decide) selected_cut_13371

theorem selected_cut_13372 : selected 8 ⟨351688, by decide⟩
    (prefixPartial 13 106702) = some ⟨13, 2, 0, 351688, 106702, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_106702_351688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106702 ⟨351688, by decide⟩ :=
  accepted_of_selected 13 106702 ⟨351688, by decide⟩ ⟨13, 2, 0, 351688, 106702, 1337, 16384⟩
    (by decide) selected_cut_13372

theorem selected_cut_13373 : selected 8 ⟨351694, by decide⟩
    (prefixPartial 13 106703) = some ⟨13, 2, 0, 351694, 106703, 737, 16384⟩ := by
  decide +kernel

theorem context_13_106703_351694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106703 ⟨351694, by decide⟩ :=
  accepted_of_selected 13 106703 ⟨351694, by decide⟩ ⟨13, 2, 0, 351694, 106703, 737, 16384⟩
    (by decide) selected_cut_13373

theorem unmarked_context_12_26675_351695 : frontier 9 ⟨351695, by decide⟩
    (prefixCache 12 26675) (prefixPartial 12 26675) = false := by
  decide +kernel

theorem node_context_12_26675_351695 : EJMOriginalGlobalDAGData.nodes 9 ⟨351695, by decide⟩ =
    .split (coordinate 12) (![⟨351648, by decide⟩,⟨351673, by decide⟩,⟨351688, by decide⟩,⟨351694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26675_351695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26675 ⟨351695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26675
    ⟨351695, by decide⟩ (by decide) (![⟨351648, by decide⟩,⟨351673, by decide⟩,⟨351688, by decide⟩,⟨351694, by decide⟩]) unmarked_context_12_26675_351695 node_context_12_26675_351695
  intro a
  fin_cases a
  · exact context_13_106700_351648
  · exact context_13_106701_351673
  · exact context_13_106702_351688
  · exact context_13_106703_351694

theorem unmarked_context_11_6668_351696 : frontier 10 ⟨351696, by decide⟩
    (prefixCache 11 6668) (prefixPartial 11 6668) = false := by
  decide +kernel

theorem node_context_11_6668_351696 : EJMOriginalGlobalDAGData.nodes 10 ⟨351696, by decide⟩ =
    .split (coordinate 11) (![⟨351535, by decide⟩,⟨351585, by decide⟩,⟨351641, by decide⟩,⟨351695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6668_351696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6668 ⟨351696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6668
    ⟨351696, by decide⟩ (by decide) (![⟨351535, by decide⟩,⟨351585, by decide⟩,⟨351641, by decide⟩,⟨351695, by decide⟩]) unmarked_context_11_6668_351696 node_context_11_6668_351696
  intro a
  fin_cases a
  · exact context_12_26672_351535
  · exact context_12_26673_351585
  · exact context_12_26674_351641
  · exact context_12_26675_351695

theorem selected_cut_13374 : selected 8 ⟨351703, by decide⟩
    (prefixPartial 13 106704) = some ⟨13, 2, 0, 351703, 106704, 381, 16384⟩ := by
  decide +kernel

theorem context_13_106704_351703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106704 ⟨351703, by decide⟩ :=
  accepted_of_selected 13 106704 ⟨351703, by decide⟩ ⟨13, 2, 0, 351703, 106704, 381, 16384⟩
    (by decide) selected_cut_13374

theorem selected_cut_13375 : selected 8 ⟨351730, by decide⟩
    (prefixPartial 13 106705) = some ⟨13, 2, 0, 351730, 106705, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_106705_351730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106705 ⟨351730, by decide⟩ :=
  accepted_of_selected 13 106705 ⟨351730, by decide⟩ ⟨13, 2, 0, 351730, 106705, 2037, 16384⟩
    (by decide) selected_cut_13375

theorem selected_cut_13376 : selected 8 ⟨351744, by decide⟩
    (prefixPartial 13 106706) = some ⟨13, 2, 0, 351744, 106706, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_106706_351744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106706 ⟨351744, by decide⟩ :=
  accepted_of_selected 13 106706 ⟨351744, by decide⟩ ⟨13, 2, 0, 351744, 106706, 1369, 16384⟩
    (by decide) selected_cut_13376

theorem selected_cut_13377 : selected 8 ⟨351750, by decide⟩
    (prefixPartial 13 106707) = some ⟨13, 2, 0, 351750, 106707, 709, 16384⟩ := by
  decide +kernel

theorem context_13_106707_351750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106707 ⟨351750, by decide⟩ :=
  accepted_of_selected 13 106707 ⟨351750, by decide⟩ ⟨13, 2, 0, 351750, 106707, 709, 16384⟩
    (by decide) selected_cut_13377

theorem unmarked_context_12_26676_351751 : frontier 9 ⟨351751, by decide⟩
    (prefixCache 12 26676) (prefixPartial 12 26676) = false := by
  decide +kernel

theorem node_context_12_26676_351751 : EJMOriginalGlobalDAGData.nodes 9 ⟨351751, by decide⟩ =
    .split (coordinate 12) (![⟨351703, by decide⟩,⟨351730, by decide⟩,⟨351744, by decide⟩,⟨351750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26676_351751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26676 ⟨351751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26676
    ⟨351751, by decide⟩ (by decide) (![⟨351703, by decide⟩,⟨351730, by decide⟩,⟨351744, by decide⟩,⟨351750, by decide⟩]) unmarked_context_12_26676_351751 node_context_12_26676_351751
  intro a
  fin_cases a
  · exact context_13_106704_351703
  · exact context_13_106705_351730
  · exact context_13_106706_351744
  · exact context_13_106707_351750

theorem selected_cut_13378 : selected 8 ⟨351757, by decide⟩
    (prefixPartial 13 106708) = some ⟨13, 2, 0, 351757, 106708, 481, 16384⟩ := by
  decide +kernel

theorem context_13_106708_351757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106708 ⟨351757, by decide⟩ :=
  accepted_of_selected 13 106708 ⟨351757, by decide⟩ ⟨13, 2, 0, 351757, 106708, 481, 16384⟩
    (by decide) selected_cut_13378

theorem selected_cut_13379 : selected 8 ⟨351782, by decide⟩
    (prefixPartial 13 106709) = some ⟨13, 2, 0, 351782, 106709, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_106709_351782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106709 ⟨351782, by decide⟩ :=
  accepted_of_selected 13 106709 ⟨351782, by decide⟩ ⟨13, 2, 0, 351782, 106709, 1597, 16384⟩
    (by decide) selected_cut_13379

theorem selected_cut_13380 : selected 8 ⟨351799, by decide⟩
    (prefixPartial 13 106710) = some ⟨13, 2, 0, 351799, 106710, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_106710_351799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106710 ⟨351799, by decide⟩ :=
  accepted_of_selected 13 106710 ⟨351799, by decide⟩ ⟨13, 2, 0, 351799, 106710, 1541, 16384⟩
    (by decide) selected_cut_13380

theorem selected_cut_13381 : selected 8 ⟨351804, by decide⟩
    (prefixPartial 13 106711) = some ⟨13, 2, 0, 351804, 106711, 713, 16384⟩ := by
  decide +kernel

theorem context_13_106711_351804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106711 ⟨351804, by decide⟩ :=
  accepted_of_selected 13 106711 ⟨351804, by decide⟩ ⟨13, 2, 0, 351804, 106711, 713, 16384⟩
    (by decide) selected_cut_13381

theorem unmarked_context_12_26677_351805 : frontier 9 ⟨351805, by decide⟩
    (prefixCache 12 26677) (prefixPartial 12 26677) = false := by
  decide +kernel

theorem node_context_12_26677_351805 : EJMOriginalGlobalDAGData.nodes 9 ⟨351805, by decide⟩ =
    .split (coordinate 12) (![⟨351757, by decide⟩,⟨351782, by decide⟩,⟨351799, by decide⟩,⟨351804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26677_351805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26677 ⟨351805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26677
    ⟨351805, by decide⟩ (by decide) (![⟨351757, by decide⟩,⟨351782, by decide⟩,⟨351799, by decide⟩,⟨351804, by decide⟩]) unmarked_context_12_26677_351805 node_context_12_26677_351805
  intro a
  fin_cases a
  · exact context_13_106708_351757
  · exact context_13_106709_351782
  · exact context_13_106710_351799
  · exact context_13_106711_351804

theorem selected_cut_13382 : selected 8 ⟨351811, by decide⟩
    (prefixPartial 13 106712) = some ⟨13, 2, 0, 351811, 106712, 441, 16384⟩ := by
  decide +kernel

theorem context_13_106712_351811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106712 ⟨351811, by decide⟩ :=
  accepted_of_selected 13 106712 ⟨351811, by decide⟩ ⟨13, 2, 0, 351811, 106712, 441, 16384⟩
    (by decide) selected_cut_13382

theorem selected_cut_13383 : selected 8 ⟨351840, by decide⟩
    (prefixPartial 13 106713) = some ⟨13, 2, 0, 351840, 106713, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_106713_351840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106713 ⟨351840, by decide⟩ :=
  accepted_of_selected 13 106713 ⟨351840, by decide⟩ ⟨13, 2, 0, 351840, 106713, 2145, 16384⟩
    (by decide) selected_cut_13383

theorem selected_cut_13384 : selected 8 ⟨351855, by decide⟩
    (prefixPartial 13 106714) = some ⟨13, 2, 0, 351855, 106714, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_106714_351855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106714 ⟨351855, by decide⟩ :=
  accepted_of_selected 13 106714 ⟨351855, by decide⟩ ⟨13, 2, 0, 351855, 106714, 1473, 16384⟩
    (by decide) selected_cut_13384

theorem selected_cut_13385 : selected 8 ⟨351859, by decide⟩
    (prefixPartial 13 106715) = some ⟨13, 2, 0, 351859, 106715, 717, 16384⟩ := by
  decide +kernel

theorem context_13_106715_351859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106715 ⟨351859, by decide⟩ :=
  accepted_of_selected 13 106715 ⟨351859, by decide⟩ ⟨13, 2, 0, 351859, 106715, 717, 16384⟩
    (by decide) selected_cut_13385

theorem unmarked_context_12_26678_351860 : frontier 9 ⟨351860, by decide⟩
    (prefixCache 12 26678) (prefixPartial 12 26678) = false := by
  decide +kernel

theorem node_context_12_26678_351860 : EJMOriginalGlobalDAGData.nodes 9 ⟨351860, by decide⟩ =
    .split (coordinate 12) (![⟨351811, by decide⟩,⟨351840, by decide⟩,⟨351855, by decide⟩,⟨351859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26678_351860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26678 ⟨351860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26678
    ⟨351860, by decide⟩ (by decide) (![⟨351811, by decide⟩,⟨351840, by decide⟩,⟨351855, by decide⟩,⟨351859, by decide⟩]) unmarked_context_12_26678_351860 node_context_12_26678_351860
  intro a
  fin_cases a
  · exact context_13_106712_351811
  · exact context_13_106713_351840
  · exact context_13_106714_351855
  · exact context_13_106715_351859

theorem selected_cut_13386 : selected 8 ⟨351868, by decide⟩
    (prefixPartial 13 106716) = some ⟨13, 2, 0, 351868, 106716, 453, 16384⟩ := by
  decide +kernel

theorem context_13_106716_351868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106716 ⟨351868, by decide⟩ :=
  accepted_of_selected 13 106716 ⟨351868, by decide⟩ ⟨13, 2, 0, 351868, 106716, 453, 16384⟩
    (by decide) selected_cut_13386

theorem selected_cut_13387 : selected 8 ⟨351893, by decide⟩
    (prefixPartial 13 106717) = some ⟨13, 2, 0, 351893, 106717, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_106717_351893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106717 ⟨351893, by decide⟩ :=
  accepted_of_selected 13 106717 ⟨351893, by decide⟩ ⟨13, 2, 0, 351893, 106717, 2353, 16384⟩
    (by decide) selected_cut_13387

theorem selected_cut_13388 : selected 8 ⟨351913, by decide⟩
    (prefixPartial 13 106718) = some ⟨13, 2, 0, 351913, 106718, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_106718_351913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106718 ⟨351913, by decide⟩ :=
  accepted_of_selected 13 106718 ⟨351913, by decide⟩ ⟨13, 2, 0, 351913, 106718, 1557, 16384⟩
    (by decide) selected_cut_13388

theorem selected_cut_13389 : selected 8 ⟨351920, by decide⟩
    (prefixPartial 13 106719) = some ⟨13, 2, 0, 351920, 106719, 797, 16384⟩ := by
  decide +kernel

theorem context_13_106719_351920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106719 ⟨351920, by decide⟩ :=
  accepted_of_selected 13 106719 ⟨351920, by decide⟩ ⟨13, 2, 0, 351920, 106719, 797, 16384⟩
    (by decide) selected_cut_13389

theorem unmarked_context_12_26679_351921 : frontier 9 ⟨351921, by decide⟩
    (prefixCache 12 26679) (prefixPartial 12 26679) = false := by
  decide +kernel

theorem node_context_12_26679_351921 : EJMOriginalGlobalDAGData.nodes 9 ⟨351921, by decide⟩ =
    .split (coordinate 12) (![⟨351868, by decide⟩,⟨351893, by decide⟩,⟨351913, by decide⟩,⟨351920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26679_351921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26679 ⟨351921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26679
    ⟨351921, by decide⟩ (by decide) (![⟨351868, by decide⟩,⟨351893, by decide⟩,⟨351913, by decide⟩,⟨351920, by decide⟩]) unmarked_context_12_26679_351921 node_context_12_26679_351921
  intro a
  fin_cases a
  · exact context_13_106716_351868
  · exact context_13_106717_351893
  · exact context_13_106718_351913
  · exact context_13_106719_351920

theorem unmarked_context_11_6669_351922 : frontier 10 ⟨351922, by decide⟩
    (prefixCache 11 6669) (prefixPartial 11 6669) = false := by
  decide +kernel

theorem node_context_11_6669_351922 : EJMOriginalGlobalDAGData.nodes 10 ⟨351922, by decide⟩ =
    .split (coordinate 11) (![⟨351751, by decide⟩,⟨351805, by decide⟩,⟨351860, by decide⟩,⟨351921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6669_351922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6669 ⟨351922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6669
    ⟨351922, by decide⟩ (by decide) (![⟨351751, by decide⟩,⟨351805, by decide⟩,⟨351860, by decide⟩,⟨351921, by decide⟩]) unmarked_context_11_6669_351922 node_context_11_6669_351922
  intro a
  fin_cases a
  · exact context_12_26676_351751
  · exact context_12_26677_351805
  · exact context_12_26678_351860
  · exact context_12_26679_351921

theorem selected_cut_13390 : selected 8 ⟨351925, by decide⟩
    (prefixPartial 13 106720) = some ⟨13, 2, 0, 351925, 106720, 241, 16384⟩ := by
  decide +kernel

theorem context_13_106720_351925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106720 ⟨351925, by decide⟩ :=
  accepted_of_selected 13 106720 ⟨351925, by decide⟩ ⟨13, 2, 0, 351925, 106720, 241, 16384⟩
    (by decide) selected_cut_13390

theorem selected_cut_13391 : selected 8 ⟨351954, by decide⟩
    (prefixPartial 13 106721) = some ⟨13, 2, 0, 351954, 106721, 2465, 16384⟩ := by
  decide +kernel

theorem context_13_106721_351954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106721 ⟨351954, by decide⟩ :=
  accepted_of_selected 13 106721 ⟨351954, by decide⟩ ⟨13, 2, 0, 351954, 106721, 2465, 16384⟩
    (by decide) selected_cut_13391

theorem selected_cut_13392 : selected 8 ⟨351972, by decide⟩
    (prefixPartial 13 106722) = some ⟨13, 2, 0, 351972, 106722, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_106722_351972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106722 ⟨351972, by decide⟩ :=
  accepted_of_selected 13 106722 ⟨351972, by decide⟩ ⟨13, 2, 0, 351972, 106722, 1529, 16384⟩
    (by decide) selected_cut_13392

theorem selected_cut_13393 : selected 8 ⟨351979, by decide⟩
    (prefixPartial 13 106723) = some ⟨13, 2, 0, 351979, 106723, 893, 16384⟩ := by
  decide +kernel

theorem context_13_106723_351979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106723 ⟨351979, by decide⟩ :=
  accepted_of_selected 13 106723 ⟨351979, by decide⟩ ⟨13, 2, 0, 351979, 106723, 893, 16384⟩
    (by decide) selected_cut_13393

theorem unmarked_context_12_26680_351980 : frontier 9 ⟨351980, by decide⟩
    (prefixCache 12 26680) (prefixPartial 12 26680) = false := by
  decide +kernel

theorem node_context_12_26680_351980 : EJMOriginalGlobalDAGData.nodes 9 ⟨351980, by decide⟩ =
    .split (coordinate 12) (![⟨351925, by decide⟩,⟨351954, by decide⟩,⟨351972, by decide⟩,⟨351979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26680_351980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26680 ⟨351980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26680
    ⟨351980, by decide⟩ (by decide) (![⟨351925, by decide⟩,⟨351954, by decide⟩,⟨351972, by decide⟩,⟨351979, by decide⟩]) unmarked_context_12_26680_351980 node_context_12_26680_351980
  intro a
  fin_cases a
  · exact context_13_106720_351925
  · exact context_13_106721_351954
  · exact context_13_106722_351972
  · exact context_13_106723_351979

theorem selected_cut_13394 : selected 8 ⟨351984, by decide⟩
    (prefixPartial 13 106724) = some ⟨13, 2, 0, 351984, 106724, 269, 16384⟩ := by
  decide +kernel

theorem context_13_106724_351984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106724 ⟨351984, by decide⟩ :=
  accepted_of_selected 13 106724 ⟨351984, by decide⟩ ⟨13, 2, 0, 351984, 106724, 269, 16384⟩
    (by decide) selected_cut_13394

theorem selected_cut_13395 : selected 8 ⟨352009, by decide⟩
    (prefixPartial 13 106725) = some ⟨13, 2, 0, 352009, 106725, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_106725_352009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106725 ⟨352009, by decide⟩ :=
  accepted_of_selected 13 106725 ⟨352009, by decide⟩ ⟨13, 2, 0, 352009, 106725, 2073, 16384⟩
    (by decide) selected_cut_13395

theorem selected_cut_13396 : selected 8 ⟨352024, by decide⟩
    (prefixPartial 13 106726) = some ⟨13, 2, 0, 352024, 106726, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_106726_352024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106726 ⟨352024, by decide⟩ :=
  accepted_of_selected 13 106726 ⟨352024, by decide⟩ ⟨13, 2, 0, 352024, 106726, 1393, 16384⟩
    (by decide) selected_cut_13396

theorem selected_cut_13397 : selected 8 ⟨352030, by decide⟩
    (prefixPartial 13 106727) = some ⟨13, 2, 0, 352030, 106727, 773, 16384⟩ := by
  decide +kernel

theorem context_13_106727_352030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106727 ⟨352030, by decide⟩ :=
  accepted_of_selected 13 106727 ⟨352030, by decide⟩ ⟨13, 2, 0, 352030, 106727, 773, 16384⟩
    (by decide) selected_cut_13397

theorem unmarked_context_12_26681_352031 : frontier 9 ⟨352031, by decide⟩
    (prefixCache 12 26681) (prefixPartial 12 26681) = false := by
  decide +kernel

theorem node_context_12_26681_352031 : EJMOriginalGlobalDAGData.nodes 9 ⟨352031, by decide⟩ =
    .split (coordinate 12) (![⟨351984, by decide⟩,⟨352009, by decide⟩,⟨352024, by decide⟩,⟨352030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26681_352031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26681 ⟨352031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26681
    ⟨352031, by decide⟩ (by decide) (![⟨351984, by decide⟩,⟨352009, by decide⟩,⟨352024, by decide⟩,⟨352030, by decide⟩]) unmarked_context_12_26681_352031 node_context_12_26681_352031
  intro a
  fin_cases a
  · exact context_13_106724_351984
  · exact context_13_106725_352009
  · exact context_13_106726_352024
  · exact context_13_106727_352030

theorem selected_cut_13398 : selected 8 ⟨352035, by decide⟩
    (prefixPartial 13 106728) = some ⟨13, 2, 0, 352035, 106728, 189, 16384⟩ := by
  decide +kernel

theorem context_13_106728_352035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106728 ⟨352035, by decide⟩ :=
  accepted_of_selected 13 106728 ⟨352035, by decide⟩ ⟨13, 2, 0, 352035, 106728, 189, 16384⟩
    (by decide) selected_cut_13398

theorem selected_cut_13399 : selected 8 ⟨352069, by decide⟩
    (prefixPartial 13 106729) = some ⟨13, 2, 0, 352069, 106729, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_106729_352069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106729 ⟨352069, by decide⟩ :=
  accepted_of_selected 13 106729 ⟨352069, by decide⟩ ⟨13, 2, 0, 352069, 106729, 2317, 16384⟩
    (by decide) selected_cut_13399

theorem selected_cut_13400 : selected 8 ⟨352084, by decide⟩
    (prefixPartial 13 106730) = some ⟨13, 2, 0, 352084, 106730, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_106730_352084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106730 ⟨352084, by decide⟩ :=
  accepted_of_selected 13 106730 ⟨352084, by decide⟩ ⟨13, 2, 0, 352084, 106730, 1337, 16384⟩
    (by decide) selected_cut_13400

theorem selected_cut_13401 : selected 8 ⟨352091, by decide⟩
    (prefixPartial 13 106731) = some ⟨13, 2, 0, 352091, 106731, 777, 16384⟩ := by
  decide +kernel

theorem context_13_106731_352091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106731 ⟨352091, by decide⟩ :=
  accepted_of_selected 13 106731 ⟨352091, by decide⟩ ⟨13, 2, 0, 352091, 106731, 777, 16384⟩
    (by decide) selected_cut_13401

theorem unmarked_context_12_26682_352092 : frontier 9 ⟨352092, by decide⟩
    (prefixCache 12 26682) (prefixPartial 12 26682) = false := by
  decide +kernel

theorem node_context_12_26682_352092 : EJMOriginalGlobalDAGData.nodes 9 ⟨352092, by decide⟩ =
    .split (coordinate 12) (![⟨352035, by decide⟩,⟨352069, by decide⟩,⟨352084, by decide⟩,⟨352091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26682_352092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26682 ⟨352092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26682
    ⟨352092, by decide⟩ (by decide) (![⟨352035, by decide⟩,⟨352069, by decide⟩,⟨352084, by decide⟩,⟨352091, by decide⟩]) unmarked_context_12_26682_352092 node_context_12_26682_352092
  intro a
  fin_cases a
  · exact context_13_106728_352035
  · exact context_13_106729_352069
  · exact context_13_106730_352084
  · exact context_13_106731_352091

theorem selected_cut_13402 : selected 8 ⟨352098, by decide⟩
    (prefixPartial 13 106732) = some ⟨13, 2, 0, 352098, 106732, 185, 16384⟩ := by
  decide +kernel

theorem context_13_106732_352098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106732 ⟨352098, by decide⟩ :=
  accepted_of_selected 13 106732 ⟨352098, by decide⟩ ⟨13, 2, 0, 352098, 106732, 185, 16384⟩
    (by decide) selected_cut_13402

theorem selected_cut_13403 : selected 8 ⟨352124, by decide⟩
    (prefixPartial 13 106733) = some ⟨13, 2, 0, 352124, 106733, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_106733_352124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106733 ⟨352124, by decide⟩ :=
  accepted_of_selected 13 106733 ⟨352124, by decide⟩ ⟨13, 2, 0, 352124, 106733, 2657, 16384⟩
    (by decide) selected_cut_13403

theorem selected_cut_13404 : selected 8 ⟨352142, by decide⟩
    (prefixPartial 13 106734) = some ⟨13, 2, 0, 352142, 106734, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_106734_352142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106734 ⟨352142, by decide⟩ :=
  accepted_of_selected 13 106734 ⟨352142, by decide⟩ ⟨13, 2, 0, 352142, 106734, 1449, 16384⟩
    (by decide) selected_cut_13404

theorem selected_cut_13405 : selected 8 ⟨352150, by decide⟩
    (prefixPartial 13 106735) = some ⟨13, 2, 0, 352150, 106735, 869, 16384⟩ := by
  decide +kernel

theorem context_13_106735_352150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106735 ⟨352150, by decide⟩ :=
  accepted_of_selected 13 106735 ⟨352150, by decide⟩ ⟨13, 2, 0, 352150, 106735, 869, 16384⟩
    (by decide) selected_cut_13405

theorem unmarked_context_12_26683_352151 : frontier 9 ⟨352151, by decide⟩
    (prefixCache 12 26683) (prefixPartial 12 26683) = false := by
  decide +kernel

theorem node_context_12_26683_352151 : EJMOriginalGlobalDAGData.nodes 9 ⟨352151, by decide⟩ =
    .split (coordinate 12) (![⟨352098, by decide⟩,⟨352124, by decide⟩,⟨352142, by decide⟩,⟨352150, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26683_352151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26683 ⟨352151, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26683
    ⟨352151, by decide⟩ (by decide) (![⟨352098, by decide⟩,⟨352124, by decide⟩,⟨352142, by decide⟩,⟨352150, by decide⟩]) unmarked_context_12_26683_352151 node_context_12_26683_352151
  intro a
  fin_cases a
  · exact context_13_106732_352098
  · exact context_13_106733_352124
  · exact context_13_106734_352142
  · exact context_13_106735_352150

theorem unmarked_context_11_6670_352152 : frontier 10 ⟨352152, by decide⟩
    (prefixCache 11 6670) (prefixPartial 11 6670) = false := by
  decide +kernel

theorem node_context_11_6670_352152 : EJMOriginalGlobalDAGData.nodes 10 ⟨352152, by decide⟩ =
    .split (coordinate 11) (![⟨351980, by decide⟩,⟨352031, by decide⟩,⟨352092, by decide⟩,⟨352151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6670_352152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6670 ⟨352152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6670
    ⟨352152, by decide⟩ (by decide) (![⟨351980, by decide⟩,⟨352031, by decide⟩,⟨352092, by decide⟩,⟨352151, by decide⟩]) unmarked_context_11_6670_352152 node_context_11_6670_352152
  intro a
  fin_cases a
  · exact context_12_26680_351980
  · exact context_12_26681_352031
  · exact context_12_26682_352092
  · exact context_12_26683_352151

theorem selected_cut_13406 : selected 8 ⟨352156, by decide⟩
    (prefixPartial 13 106736) = some ⟨13, 2, 0, 352156, 106736, 117, 16384⟩ := by
  decide +kernel

theorem context_13_106736_352156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106736 ⟨352156, by decide⟩ :=
  accepted_of_selected 13 106736 ⟨352156, by decide⟩ ⟨13, 2, 0, 352156, 106736, 117, 16384⟩
    (by decide) selected_cut_13406

theorem selected_cut_13407 : selected 8 ⟨352187, by decide⟩
    (prefixPartial 13 106737) = some ⟨13, 2, 0, 352187, 106737, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_106737_352187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106737 ⟨352187, by decide⟩ :=
  accepted_of_selected 13 106737 ⟨352187, by decide⟩ ⟨13, 2, 0, 352187, 106737, 2033, 16384⟩
    (by decide) selected_cut_13407

theorem selected_cut_13408 : selected 8 ⟨352203, by decide⟩
    (prefixPartial 13 106738) = some ⟨13, 2, 0, 352203, 106738, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_106738_352203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106738 ⟨352203, by decide⟩ :=
  accepted_of_selected 13 106738 ⟨352203, by decide⟩ ⟨13, 2, 0, 352203, 106738, 1197, 16384⟩
    (by decide) selected_cut_13408

theorem selected_cut_13409 : selected 8 ⟨352210, by decide⟩
    (prefixPartial 13 106739) = some ⟨13, 2, 0, 352210, 106739, 761, 16384⟩ := by
  decide +kernel

theorem context_13_106739_352210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106739 ⟨352210, by decide⟩ :=
  accepted_of_selected 13 106739 ⟨352210, by decide⟩ ⟨13, 2, 0, 352210, 106739, 761, 16384⟩
    (by decide) selected_cut_13409

theorem unmarked_context_12_26684_352211 : frontier 9 ⟨352211, by decide⟩
    (prefixCache 12 26684) (prefixPartial 12 26684) = false := by
  decide +kernel

theorem node_context_12_26684_352211 : EJMOriginalGlobalDAGData.nodes 9 ⟨352211, by decide⟩ =
    .split (coordinate 12) (![⟨352156, by decide⟩,⟨352187, by decide⟩,⟨352203, by decide⟩,⟨352210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26684_352211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26684 ⟨352211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26684
    ⟨352211, by decide⟩ (by decide) (![⟨352156, by decide⟩,⟨352187, by decide⟩,⟨352203, by decide⟩,⟨352210, by decide⟩]) unmarked_context_12_26684_352211 node_context_12_26684_352211
  intro a
  fin_cases a
  · exact context_13_106736_352156
  · exact context_13_106737_352187
  · exact context_13_106738_352203
  · exact context_13_106739_352210

theorem selected_cut_13410 : selected 9 ⟨352260, by decide⟩
    (prefixPartial 12 26685) = some ⟨12, 2, 0, 352260, 26685, 4065, 65536⟩ := by
  decide +kernel

theorem context_12_26685_352260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26685 ⟨352260, by decide⟩ :=
  accepted_of_selected 12 26685 ⟨352260, by decide⟩ ⟨12, 2, 0, 352260, 26685, 4065, 65536⟩
    (by decide) selected_cut_13410

theorem selected_cut_13411 : selected 8 ⟨352263, by decide⟩
    (prefixPartial 13 106744) = some ⟨13, 2, 0, 352263, 106744, 77, 16384⟩ := by
  decide +kernel

theorem context_13_106744_352263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106744 ⟨352263, by decide⟩ :=
  accepted_of_selected 13 106744 ⟨352263, by decide⟩ ⟨13, 2, 0, 352263, 106744, 77, 16384⟩
    (by decide) selected_cut_13411

theorem selected_cut_13412 : selected 8 ⟨352293, by decide⟩
    (prefixPartial 13 106745) = some ⟨13, 2, 0, 352293, 106745, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_106745_352293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106745 ⟨352293, by decide⟩ :=
  accepted_of_selected 13 106745 ⟨352293, by decide⟩ ⟨13, 2, 0, 352293, 106745, 2277, 16384⟩
    (by decide) selected_cut_13412

theorem selected_cut_13413 : selected 8 ⟨352310, by decide⟩
    (prefixPartial 13 106746) = some ⟨13, 2, 0, 352310, 106746, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_106746_352310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106746 ⟨352310, by decide⟩ :=
  accepted_of_selected 13 106746 ⟨352310, by decide⟩ ⟨13, 2, 0, 352310, 106746, 1297, 16384⟩
    (by decide) selected_cut_13413

theorem selected_cut_13414 : selected 8 ⟨352314, by decide⟩
    (prefixPartial 13 106747) = some ⟨13, 2, 0, 352314, 106747, 693, 16384⟩ := by
  decide +kernel

theorem context_13_106747_352314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106747 ⟨352314, by decide⟩ :=
  accepted_of_selected 13 106747 ⟨352314, by decide⟩ ⟨13, 2, 0, 352314, 106747, 693, 16384⟩
    (by decide) selected_cut_13414

theorem unmarked_context_12_26686_352315 : frontier 9 ⟨352315, by decide⟩
    (prefixCache 12 26686) (prefixPartial 12 26686) = false := by
  decide +kernel

theorem node_context_12_26686_352315 : EJMOriginalGlobalDAGData.nodes 9 ⟨352315, by decide⟩ =
    .split (coordinate 12) (![⟨352263, by decide⟩,⟨352293, by decide⟩,⟨352310, by decide⟩,⟨352314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26686_352315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26686 ⟨352315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26686
    ⟨352315, by decide⟩ (by decide) (![⟨352263, by decide⟩,⟨352293, by decide⟩,⟨352310, by decide⟩,⟨352314, by decide⟩]) unmarked_context_12_26686_352315 node_context_12_26686_352315
  intro a
  fin_cases a
  · exact context_13_106744_352263
  · exact context_13_106745_352293
  · exact context_13_106746_352310
  · exact context_13_106747_352314

theorem selected_cut_13415 : selected 8 ⟨352319, by decide⟩
    (prefixPartial 13 106748) = some ⟨13, 2, 0, 352319, 106748, 49, 16384⟩ := by
  decide +kernel

theorem context_13_106748_352319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106748 ⟨352319, by decide⟩ :=
  accepted_of_selected 13 106748 ⟨352319, by decide⟩ ⟨13, 2, 0, 352319, 106748, 49, 16384⟩
    (by decide) selected_cut_13415

theorem selected_cut_13416 : selected 8 ⟨352347, by decide⟩
    (prefixPartial 13 106749) = some ⟨13, 2, 0, 352347, 106749, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_106749_352347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106749 ⟨352347, by decide⟩ :=
  accepted_of_selected 13 106749 ⟨352347, by decide⟩ ⟨13, 2, 0, 352347, 106749, 2329, 16384⟩
    (by decide) selected_cut_13416

theorem selected_cut_13417 : selected 8 ⟨352367, by decide⟩
    (prefixPartial 13 106750) = some ⟨13, 2, 0, 352367, 106750, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_106750_352367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106750 ⟨352367, by decide⟩ :=
  accepted_of_selected 13 106750 ⟨352367, by decide⟩ ⟨13, 2, 0, 352367, 106750, 1317, 16384⟩
    (by decide) selected_cut_13417

theorem selected_cut_13418 : selected 8 ⟨352372, by decide⟩
    (prefixPartial 13 106751) = some ⟨13, 2, 0, 352372, 106751, 745, 16384⟩ := by
  decide +kernel

theorem context_13_106751_352372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106751 ⟨352372, by decide⟩ :=
  accepted_of_selected 13 106751 ⟨352372, by decide⟩ ⟨13, 2, 0, 352372, 106751, 745, 16384⟩
    (by decide) selected_cut_13418

theorem unmarked_context_12_26687_352373 : frontier 9 ⟨352373, by decide⟩
    (prefixCache 12 26687) (prefixPartial 12 26687) = false := by
  decide +kernel

theorem node_context_12_26687_352373 : EJMOriginalGlobalDAGData.nodes 9 ⟨352373, by decide⟩ =
    .split (coordinate 12) (![⟨352319, by decide⟩,⟨352347, by decide⟩,⟨352367, by decide⟩,⟨352372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26687_352373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26687 ⟨352373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26687
    ⟨352373, by decide⟩ (by decide) (![⟨352319, by decide⟩,⟨352347, by decide⟩,⟨352367, by decide⟩,⟨352372, by decide⟩]) unmarked_context_12_26687_352373 node_context_12_26687_352373
  intro a
  fin_cases a
  · exact context_13_106748_352319
  · exact context_13_106749_352347
  · exact context_13_106750_352367
  · exact context_13_106751_352372

theorem unmarked_context_11_6671_352374 : frontier 10 ⟨352374, by decide⟩
    (prefixCache 11 6671) (prefixPartial 11 6671) = false := by
  decide +kernel

theorem node_context_11_6671_352374 : EJMOriginalGlobalDAGData.nodes 10 ⟨352374, by decide⟩ =
    .split (coordinate 11) (![⟨352211, by decide⟩,⟨352260, by decide⟩,⟨352315, by decide⟩,⟨352373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6671_352374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6671 ⟨352374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6671
    ⟨352374, by decide⟩ (by decide) (![⟨352211, by decide⟩,⟨352260, by decide⟩,⟨352315, by decide⟩,⟨352373, by decide⟩]) unmarked_context_11_6671_352374 node_context_11_6671_352374
  intro a
  fin_cases a
  · exact context_12_26684_352211
  · exact context_12_26685_352260
  · exact context_12_26686_352315
  · exact context_12_26687_352373

theorem unmarked_context_10_1667_352375 : frontier 11 ⟨352375, by decide⟩
    (prefixCache 10 1667) (prefixPartial 10 1667) = false := by
  decide +kernel

theorem node_context_10_1667_352375 : EJMOriginalGlobalDAGData.nodes 11 ⟨352375, by decide⟩ =
    .split (coordinate 10) (![⟨351696, by decide⟩,⟨351922, by decide⟩,⟨352152, by decide⟩,⟨352374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1667_352375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1667 ⟨352375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1667
    ⟨352375, by decide⟩ (by decide) (![⟨351696, by decide⟩,⟨351922, by decide⟩,⟨352152, by decide⟩,⟨352374, by decide⟩]) unmarked_context_10_1667_352375 node_context_10_1667_352375
  intro a
  fin_cases a
  · exact context_11_6668_351696
  · exact context_11_6669_351922
  · exact context_11_6670_352152
  · exact context_11_6671_352374

theorem unmarked_context_9_416_352376 : frontier 12 ⟨352376, by decide⟩
    (prefixCache 9 416) (prefixPartial 9 416) = false := by
  decide +kernel

theorem node_context_9_416_352376 : EJMOriginalGlobalDAGData.nodes 12 ⟨352376, by decide⟩ =
    .split (coordinate 9) (![⟨349439, by decide⟩,⟨350477, by decide⟩,⟨351452, by decide⟩,⟨352375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_416_352376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 416 ⟨352376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 416
    ⟨352376, by decide⟩ (by decide) (![⟨349439, by decide⟩,⟨350477, by decide⟩,⟨351452, by decide⟩,⟨352375, by decide⟩]) unmarked_context_9_416_352376 node_context_9_416_352376
  intro a
  fin_cases a
  · exact context_10_1664_349439
  · exact context_10_1665_350477
  · exact context_10_1666_351452
  · exact context_10_1667_352375

theorem selected_cut_13419 : selected 9 ⟨352589, by decide⟩
    (prefixPartial 12 26688) = some ⟨12, 2, 0, 352589, 26688, 3781, 65536⟩ := by
  decide +kernel

theorem context_12_26688_352589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26688 ⟨352589, by decide⟩ :=
  accepted_of_selected 12 26688 ⟨352589, by decide⟩ ⟨12, 2, 0, 352589, 26688, 3781, 65536⟩
    (by decide) selected_cut_13419

theorem selected_cut_13420 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106756) = some ⟨13, 1, 0, 3444, 106756, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106756_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106756 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106756 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106756, 1, 16384⟩
    (by decide) selected_cut_13420

theorem selected_cut_13421 : selected 8 ⟨352635, by decide⟩
    (prefixPartial 13 106757) = some ⟨13, 2, 0, 352635, 106757, 2953, 16384⟩ := by
  decide +kernel

theorem context_13_106757_352635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106757 ⟨352635, by decide⟩ :=
  accepted_of_selected 13 106757 ⟨352635, by decide⟩ ⟨13, 2, 0, 352635, 106757, 2953, 16384⟩
    (by decide) selected_cut_13421

theorem selected_cut_13422 : selected 8 ⟨352659, by decide⟩
    (prefixPartial 13 106758) = some ⟨13, 2, 0, 352659, 106758, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_106758_352659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106758 ⟨352659, by decide⟩ :=
  accepted_of_selected 13 106758 ⟨352659, by decide⟩ ⟨13, 2, 0, 352659, 106758, 1597, 16384⟩
    (by decide) selected_cut_13422

theorem selected_cut_13423 : selected 8 ⟨352672, by decide⟩
    (prefixPartial 13 106759) = some ⟨13, 2, 0, 352672, 106759, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_106759_352672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106759 ⟨352672, by decide⟩ :=
  accepted_of_selected 13 106759 ⟨352672, by decide⟩ ⟨13, 2, 0, 352672, 106759, 1053, 16384⟩
    (by decide) selected_cut_13423

theorem unmarked_context_12_26689_352673 : frontier 9 ⟨352673, by decide⟩
    (prefixCache 12 26689) (prefixPartial 12 26689) = false := by
  decide +kernel

theorem node_context_12_26689_352673 : EJMOriginalGlobalDAGData.nodes 9 ⟨352673, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨352635, by decide⟩,⟨352659, by decide⟩,⟨352672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26689_352673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26689 ⟨352673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26689
    ⟨352673, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨352635, by decide⟩,⟨352659, by decide⟩,⟨352672, by decide⟩]) unmarked_context_12_26689_352673 node_context_12_26689_352673
  intro a
  fin_cases a
  · exact context_13_106756_3444
  · exact context_13_106757_352635
  · exact context_13_106758_352659
  · exact context_13_106759_352672

theorem selected_cut_13424 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106760) = some ⟨13, 1, 0, 3444, 106760, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106760_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106760 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106760 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106760, 1, 16384⟩
    (by decide) selected_cut_13424

theorem selected_cut_13425 : selected 8 ⟨352705, by decide⟩
    (prefixPartial 13 106761) = some ⟨13, 2, 0, 352705, 106761, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_106761_352705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106761 ⟨352705, by decide⟩ :=
  accepted_of_selected 13 106761 ⟨352705, by decide⟩ ⟨13, 2, 0, 352705, 106761, 2577, 16384⟩
    (by decide) selected_cut_13425

theorem selected_cut_13426 : selected 8 ⟨352723, by decide⟩
    (prefixPartial 13 106762) = some ⟨13, 2, 0, 352723, 106762, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_106762_352723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106762 ⟨352723, by decide⟩ :=
  accepted_of_selected 13 106762 ⟨352723, by decide⟩ ⟨13, 2, 0, 352723, 106762, 1193, 16384⟩
    (by decide) selected_cut_13426

theorem selected_cut_13427 : selected 8 ⟨352732, by decide⟩
    (prefixPartial 13 106763) = some ⟨13, 2, 0, 352732, 106763, 809, 16384⟩ := by
  decide +kernel

theorem context_13_106763_352732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106763 ⟨352732, by decide⟩ :=
  accepted_of_selected 13 106763 ⟨352732, by decide⟩ ⟨13, 2, 0, 352732, 106763, 809, 16384⟩
    (by decide) selected_cut_13427

theorem unmarked_context_12_26690_352733 : frontier 9 ⟨352733, by decide⟩
    (prefixCache 12 26690) (prefixPartial 12 26690) = false := by
  decide +kernel

theorem node_context_12_26690_352733 : EJMOriginalGlobalDAGData.nodes 9 ⟨352733, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨352705, by decide⟩,⟨352723, by decide⟩,⟨352732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26690_352733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26690 ⟨352733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26690
    ⟨352733, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨352705, by decide⟩,⟨352723, by decide⟩,⟨352732, by decide⟩]) unmarked_context_12_26690_352733 node_context_12_26690_352733
  intro a
  fin_cases a
  · exact context_13_106760_3444
  · exact context_13_106761_352705
  · exact context_13_106762_352723
  · exact context_13_106763_352732

theorem selected_cut_13428 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106764) = some ⟨13, 1, 0, 3444, 106764, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106764_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106764 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106764 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106764, 1, 16384⟩
    (by decide) selected_cut_13428

theorem selected_cut_13429 : selected 8 ⟨352771, by decide⟩
    (prefixPartial 13 106765) = some ⟨13, 2, 0, 352771, 106765, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_106765_352771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106765 ⟨352771, by decide⟩ :=
  accepted_of_selected 13 106765 ⟨352771, by decide⟩ ⟨13, 2, 0, 352771, 106765, 2653, 16384⟩
    (by decide) selected_cut_13429

theorem selected_cut_13430 : selected 8 ⟨352787, by decide⟩
    (prefixPartial 13 106766) = some ⟨13, 2, 0, 352787, 106766, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_106766_352787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106766 ⟨352787, by decide⟩ :=
  accepted_of_selected 13 106766 ⟨352787, by decide⟩ ⟨13, 2, 0, 352787, 106766, 1161, 16384⟩
    (by decide) selected_cut_13430

theorem selected_cut_13431 : selected 8 ⟨352793, by decide⟩
    (prefixPartial 13 106767) = some ⟨13, 2, 0, 352793, 106767, 777, 16384⟩ := by
  decide +kernel

theorem context_13_106767_352793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106767 ⟨352793, by decide⟩ :=
  accepted_of_selected 13 106767 ⟨352793, by decide⟩ ⟨13, 2, 0, 352793, 106767, 777, 16384⟩
    (by decide) selected_cut_13431

theorem unmarked_context_12_26691_352794 : frontier 9 ⟨352794, by decide⟩
    (prefixCache 12 26691) (prefixPartial 12 26691) = false := by
  decide +kernel

theorem node_context_12_26691_352794 : EJMOriginalGlobalDAGData.nodes 9 ⟨352794, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨352771, by decide⟩,⟨352787, by decide⟩,⟨352793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26691_352794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26691 ⟨352794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26691
    ⟨352794, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨352771, by decide⟩,⟨352787, by decide⟩,⟨352793, by decide⟩]) unmarked_context_12_26691_352794 node_context_12_26691_352794
  intro a
  fin_cases a
  · exact context_13_106764_3444
  · exact context_13_106765_352771
  · exact context_13_106766_352787
  · exact context_13_106767_352793

theorem unmarked_context_11_6672_352795 : frontier 10 ⟨352795, by decide⟩
    (prefixCache 11 6672) (prefixPartial 11 6672) = false := by
  decide +kernel

theorem node_context_11_6672_352795 : EJMOriginalGlobalDAGData.nodes 10 ⟨352795, by decide⟩ =
    .split (coordinate 11) (![⟨352589, by decide⟩,⟨352673, by decide⟩,⟨352733, by decide⟩,⟨352794, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6672_352795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6672 ⟨352795, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6672
    ⟨352795, by decide⟩ (by decide) (![⟨352589, by decide⟩,⟨352673, by decide⟩,⟨352733, by decide⟩,⟨352794, by decide⟩]) unmarked_context_11_6672_352795 node_context_11_6672_352795
  intro a
  fin_cases a
  · exact context_12_26688_352589
  · exact context_12_26689_352673
  · exact context_12_26690_352733
  · exact context_12_26691_352794

theorem selected_cut_13432 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106768) = some ⟨13, 1, 0, 3444, 106768, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106768_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106768 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106768 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106768, 1, 16384⟩
    (by decide) selected_cut_13432

theorem selected_cut_13433 : selected 8 ⟨352831, by decide⟩
    (prefixPartial 13 106769) = some ⟨13, 2, 0, 352831, 106769, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_106769_352831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106769 ⟨352831, by decide⟩ :=
  accepted_of_selected 13 106769 ⟨352831, by decide⟩ ⟨13, 2, 0, 352831, 106769, 2677, 16384⟩
    (by decide) selected_cut_13433

theorem selected_cut_13434 : selected 8 ⟨352852, by decide⟩
    (prefixPartial 13 106770) = some ⟨13, 2, 0, 352852, 106770, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_106770_352852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106770 ⟨352852, by decide⟩ :=
  accepted_of_selected 13 106770 ⟨352852, by decide⟩ ⟨13, 2, 0, 352852, 106770, 1461, 16384⟩
    (by decide) selected_cut_13434

theorem selected_cut_13435 : selected 8 ⟨352858, by decide⟩
    (prefixPartial 13 106771) = some ⟨13, 2, 0, 352858, 106771, 877, 16384⟩ := by
  decide +kernel

theorem context_13_106771_352858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106771 ⟨352858, by decide⟩ :=
  accepted_of_selected 13 106771 ⟨352858, by decide⟩ ⟨13, 2, 0, 352858, 106771, 877, 16384⟩
    (by decide) selected_cut_13435

theorem unmarked_context_12_26692_352859 : frontier 9 ⟨352859, by decide⟩
    (prefixCache 12 26692) (prefixPartial 12 26692) = false := by
  decide +kernel

theorem node_context_12_26692_352859 : EJMOriginalGlobalDAGData.nodes 9 ⟨352859, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨352831, by decide⟩,⟨352852, by decide⟩,⟨352858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26692_352859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26692 ⟨352859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26692
    ⟨352859, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨352831, by decide⟩,⟨352852, by decide⟩,⟨352858, by decide⟩]) unmarked_context_12_26692_352859 node_context_12_26692_352859
  intro a
  fin_cases a
  · exact context_13_106768_3444
  · exact context_13_106769_352831
  · exact context_13_106770_352852
  · exact context_13_106771_352858

theorem selected_cut_13436 : selected 9 ⟨268917, by decide⟩
    (prefixPartial 12 26693) = some ⟨12, 1, 0, 268917, 26693, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26693_268917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26693 ⟨268917, by decide⟩ :=
  accepted_of_selected 12 26693 ⟨268917, by decide⟩ ⟨12, 1, 0, 268917, 26693, 1, 65536⟩
    (by decide) selected_cut_13436

theorem selected_cut_13437 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106776) = some ⟨13, 1, 0, 3444, 106776, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106776_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106776 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106776 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106776, 1, 16384⟩
    (by decide) selected_cut_13437

theorem selected_cut_13438 : selected 8 ⟨352901, by decide⟩
    (prefixPartial 13 106777) = some ⟨13, 2, 0, 352901, 106777, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_106777_352901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106777 ⟨352901, by decide⟩ :=
  accepted_of_selected 13 106777 ⟨352901, by decide⟩ ⟨13, 2, 0, 352901, 106777, 2669, 16384⟩
    (by decide) selected_cut_13438

theorem selected_cut_13439 : selected 8 ⟨352921, by decide⟩
    (prefixPartial 13 106778) = some ⟨13, 2, 0, 352921, 106778, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_106778_352921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106778 ⟨352921, by decide⟩ :=
  accepted_of_selected 13 106778 ⟨352921, by decide⟩ ⟨13, 2, 0, 352921, 106778, 1597, 16384⟩
    (by decide) selected_cut_13439

theorem selected_cut_13440 : selected 8 ⟨352930, by decide⟩
    (prefixPartial 13 106779) = some ⟨13, 2, 0, 352930, 106779, 881, 16384⟩ := by
  decide +kernel

theorem context_13_106779_352930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106779 ⟨352930, by decide⟩ :=
  accepted_of_selected 13 106779 ⟨352930, by decide⟩ ⟨13, 2, 0, 352930, 106779, 881, 16384⟩
    (by decide) selected_cut_13440

theorem unmarked_context_12_26694_352931 : frontier 9 ⟨352931, by decide⟩
    (prefixCache 12 26694) (prefixPartial 12 26694) = false := by
  decide +kernel

theorem node_context_12_26694_352931 : EJMOriginalGlobalDAGData.nodes 9 ⟨352931, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨352901, by decide⟩,⟨352921, by decide⟩,⟨352930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26694_352931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26694 ⟨352931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26694
    ⟨352931, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨352901, by decide⟩,⟨352921, by decide⟩,⟨352930, by decide⟩]) unmarked_context_12_26694_352931 node_context_12_26694_352931
  intro a
  fin_cases a
  · exact context_13_106776_3444
  · exact context_13_106777_352901
  · exact context_13_106778_352921
  · exact context_13_106779_352930

theorem selected_cut_13441 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 106780) = some ⟨13, 1, 0, 3444, 106780, 1, 16384⟩ := by
  decide +kernel

theorem context_13_106780_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106780 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 106780 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 106780, 1, 16384⟩
    (by decide) selected_cut_13441

theorem selected_cut_13442 : selected 8 ⟨352969, by decide⟩
    (prefixPartial 13 106781) = some ⟨13, 2, 0, 352969, 106781, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_106781_352969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106781 ⟨352969, by decide⟩ :=
  accepted_of_selected 13 106781 ⟨352969, by decide⟩ ⟨13, 2, 0, 352969, 106781, 2649, 16384⟩
    (by decide) selected_cut_13442

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
