/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover233
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_22467 : selected 9 ⟨571899, by decide⟩
    (prefixPartial 12 75657) = some ⟨12, 2, 0, 571899, 75657, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_75657_571899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75657 ⟨571899, by decide⟩ :=
  accepted_of_selected 12 75657 ⟨571899, by decide⟩ ⟨12, 2, 0, 571899, 75657, 2305, 65536⟩
    (by decide) selected_cut_22467

theorem selected_cut_22468 : selected 9 ⟨571934, by decide⟩
    (prefixPartial 12 75658) = some ⟨12, 2, 0, 571934, 75658, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_75658_571934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75658 ⟨571934, by decide⟩ :=
  accepted_of_selected 12 75658 ⟨571934, by decide⟩ ⟨12, 2, 0, 571934, 75658, 2305, 65536⟩
    (by decide) selected_cut_22468

theorem selected_cut_22469 : selected 9 ⟨571971, by decide⟩
    (prefixPartial 12 75659) = some ⟨12, 2, 0, 571971, 75659, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_75659_571971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75659 ⟨571971, by decide⟩ :=
  accepted_of_selected 12 75659 ⟨571971, by decide⟩ ⟨12, 2, 0, 571971, 75659, 2389, 65536⟩
    (by decide) selected_cut_22469

theorem unmarked_context_11_18914_571972 : frontier 10 ⟨571972, by decide⟩
    (prefixCache 11 18914) (prefixPartial 11 18914) = false := by
  decide +kernel

theorem node_context_11_18914_571972 : EJMOriginalGlobalDAGData.nodes 10 ⟨571972, by decide⟩ =
    .split (coordinate 11) (![⟨571868, by decide⟩,⟨571899, by decide⟩,⟨571934, by decide⟩,⟨571971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18914_571972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18914 ⟨571972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18914
    ⟨571972, by decide⟩ (by decide) (![⟨571868, by decide⟩,⟨571899, by decide⟩,⟨571934, by decide⟩,⟨571971, by decide⟩]) unmarked_context_11_18914_571972 node_context_11_18914_571972
  intro a
  fin_cases a
  · exact context_12_75656_571868
  · exact context_12_75657_571899
  · exact context_12_75658_571934
  · exact context_12_75659_571971

theorem selected_cut_22470 : selected 9 ⟨571989, by decide⟩
    (prefixPartial 12 75660) = some ⟨12, 2, 0, 571989, 75660, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_75660_571989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75660 ⟨571989, by decide⟩ :=
  accepted_of_selected 12 75660 ⟨571989, by decide⟩ ⟨12, 2, 0, 571989, 75660, 1917, 65536⟩
    (by decide) selected_cut_22470

theorem selected_cut_22471 : selected 9 ⟨572009, by decide⟩
    (prefixPartial 12 75661) = some ⟨12, 2, 0, 572009, 75661, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_75661_572009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75661 ⟨572009, by decide⟩ :=
  accepted_of_selected 12 75661 ⟨572009, by decide⟩ ⟨12, 2, 0, 572009, 75661, 2021, 65536⟩
    (by decide) selected_cut_22471

theorem selected_cut_22472 : selected 9 ⟨572033, by decide⟩
    (prefixPartial 12 75662) = some ⟨12, 2, 0, 572033, 75662, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_75662_572033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75662 ⟨572033, by decide⟩ :=
  accepted_of_selected 12 75662 ⟨572033, by decide⟩ ⟨12, 2, 0, 572033, 75662, 2005, 65536⟩
    (by decide) selected_cut_22472

theorem selected_cut_22473 : selected 9 ⟨572079, by decide⟩
    (prefixPartial 12 75663) = some ⟨12, 2, 0, 572079, 75663, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_75663_572079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75663 ⟨572079, by decide⟩ :=
  accepted_of_selected 12 75663 ⟨572079, by decide⟩ ⟨12, 2, 0, 572079, 75663, 3013, 65536⟩
    (by decide) selected_cut_22473

theorem unmarked_context_11_18915_572080 : frontier 10 ⟨572080, by decide⟩
    (prefixCache 11 18915) (prefixPartial 11 18915) = false := by
  decide +kernel

theorem node_context_11_18915_572080 : EJMOriginalGlobalDAGData.nodes 10 ⟨572080, by decide⟩ =
    .split (coordinate 11) (![⟨571989, by decide⟩,⟨572009, by decide⟩,⟨572033, by decide⟩,⟨572079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18915_572080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18915 ⟨572080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18915
    ⟨572080, by decide⟩ (by decide) (![⟨571989, by decide⟩,⟨572009, by decide⟩,⟨572033, by decide⟩,⟨572079, by decide⟩]) unmarked_context_11_18915_572080 node_context_11_18915_572080
  intro a
  fin_cases a
  · exact context_12_75660_571989
  · exact context_12_75661_572009
  · exact context_12_75662_572033
  · exact context_12_75663_572079

theorem unmarked_context_10_4728_572081 : frontier 11 ⟨572081, by decide⟩
    (prefixCache 10 4728) (prefixPartial 10 4728) = false := by
  decide +kernel

theorem node_context_10_4728_572081 : EJMOriginalGlobalDAGData.nodes 11 ⟨572081, by decide⟩ =
    .split (coordinate 10) (![⟨571736, by decide⟩,⟨571839, by decide⟩,⟨571972, by decide⟩,⟨572080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4728_572081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4728 ⟨572081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4728
    ⟨572081, by decide⟩ (by decide) (![⟨571736, by decide⟩,⟨571839, by decide⟩,⟨571972, by decide⟩,⟨572080, by decide⟩]) unmarked_context_10_4728_572081 node_context_10_4728_572081
  intro a
  fin_cases a
  · exact context_11_18912_571736
  · exact context_11_18913_571839
  · exact context_11_18914_571972
  · exact context_11_18915_572080

theorem selected_cut_22474 : selected 9 ⟨572107, by decide⟩
    (prefixPartial 12 75664) = some ⟨12, 2, 0, 572107, 75664, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_75664_572107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75664 ⟨572107, by decide⟩ :=
  accepted_of_selected 12 75664 ⟨572107, by decide⟩ ⟨12, 2, 0, 572107, 75664, 2061, 65536⟩
    (by decide) selected_cut_22474

theorem selected_cut_22475 : selected 9 ⟨572129, by decide⟩
    (prefixPartial 12 75665) = some ⟨12, 2, 0, 572129, 75665, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_75665_572129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75665 ⟨572129, by decide⟩ :=
  accepted_of_selected 12 75665 ⟨572129, by decide⟩ ⟨12, 2, 0, 572129, 75665, 1989, 65536⟩
    (by decide) selected_cut_22475

theorem selected_cut_22476 : selected 9 ⟨572155, by decide⟩
    (prefixPartial 12 75666) = some ⟨12, 2, 0, 572155, 75666, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_75666_572155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75666 ⟨572155, by decide⟩ :=
  accepted_of_selected 12 75666 ⟨572155, by decide⟩ ⟨12, 2, 0, 572155, 75666, 2249, 65536⟩
    (by decide) selected_cut_22476

theorem selected_cut_22477 : selected 9 ⟨572174, by decide⟩
    (prefixPartial 12 75667) = some ⟨12, 2, 0, 572174, 75667, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_75667_572174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75667 ⟨572174, by decide⟩ :=
  accepted_of_selected 12 75667 ⟨572174, by decide⟩ ⟨12, 2, 0, 572174, 75667, 2049, 65536⟩
    (by decide) selected_cut_22477

theorem unmarked_context_11_18916_572175 : frontier 10 ⟨572175, by decide⟩
    (prefixCache 11 18916) (prefixPartial 11 18916) = false := by
  decide +kernel

theorem node_context_11_18916_572175 : EJMOriginalGlobalDAGData.nodes 10 ⟨572175, by decide⟩ =
    .split (coordinate 11) (![⟨572107, by decide⟩,⟨572129, by decide⟩,⟨572155, by decide⟩,⟨572174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18916_572175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18916 ⟨572175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18916
    ⟨572175, by decide⟩ (by decide) (![⟨572107, by decide⟩,⟨572129, by decide⟩,⟨572155, by decide⟩,⟨572174, by decide⟩]) unmarked_context_11_18916_572175 node_context_11_18916_572175
  intro a
  fin_cases a
  · exact context_12_75664_572107
  · exact context_12_75665_572129
  · exact context_12_75666_572155
  · exact context_12_75667_572174

theorem selected_cut_22478 : selected 9 ⟨572224, by decide⟩
    (prefixPartial 12 75668) = some ⟨12, 2, 0, 572224, 75668, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_75668_572224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75668 ⟨572224, by decide⟩ :=
  accepted_of_selected 12 75668 ⟨572224, by decide⟩ ⟨12, 2, 0, 572224, 75668, 2989, 65536⟩
    (by decide) selected_cut_22478

theorem selected_cut_22479 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 75669) = some ⟨12, 1, 0, 449506, 75669, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75669_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75669 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 75669 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 75669, 1, 65536⟩
    (by decide) selected_cut_22479

theorem selected_cut_22480 : selected 9 ⟨572276, by decide⟩
    (prefixPartial 12 75670) = some ⟨12, 2, 0, 572276, 75670, 3133, 65536⟩ := by
  decide +kernel

theorem context_12_75670_572276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75670 ⟨572276, by decide⟩ :=
  accepted_of_selected 12 75670 ⟨572276, by decide⟩ ⟨12, 2, 0, 572276, 75670, 3133, 65536⟩
    (by decide) selected_cut_22480

theorem selected_cut_22481 : selected 9 ⟨572316, by decide⟩
    (prefixPartial 12 75671) = some ⟨12, 2, 0, 572316, 75671, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_75671_572316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75671 ⟨572316, by decide⟩ :=
  accepted_of_selected 12 75671 ⟨572316, by decide⟩ ⟨12, 2, 0, 572316, 75671, 2829, 65536⟩
    (by decide) selected_cut_22481

theorem unmarked_context_11_18917_572317 : frontier 10 ⟨572317, by decide⟩
    (prefixCache 11 18917) (prefixPartial 11 18917) = false := by
  decide +kernel

theorem node_context_11_18917_572317 : EJMOriginalGlobalDAGData.nodes 10 ⟨572317, by decide⟩ =
    .split (coordinate 11) (![⟨572224, by decide⟩,⟨449506, by decide⟩,⟨572276, by decide⟩,⟨572316, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18917_572317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18917 ⟨572317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18917
    ⟨572317, by decide⟩ (by decide) (![⟨572224, by decide⟩,⟨449506, by decide⟩,⟨572276, by decide⟩,⟨572316, by decide⟩]) unmarked_context_11_18917_572317 node_context_11_18917_572317
  intro a
  fin_cases a
  · exact context_12_75668_572224
  · exact context_12_75669_449506
  · exact context_12_75670_572276
  · exact context_12_75671_572316

theorem selected_cut_22482 : selected 9 ⟨572344, by decide⟩
    (prefixPartial 12 75672) = some ⟨12, 2, 0, 572344, 75672, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_75672_572344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75672 ⟨572344, by decide⟩ :=
  accepted_of_selected 12 75672 ⟨572344, by decide⟩ ⟨12, 2, 0, 572344, 75672, 2233, 65536⟩
    (by decide) selected_cut_22482

theorem selected_cut_22483 : selected 9 ⟨572368, by decide⟩
    (prefixPartial 12 75673) = some ⟨12, 2, 0, 572368, 75673, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_75673_572368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75673 ⟨572368, by decide⟩ :=
  accepted_of_selected 12 75673 ⟨572368, by decide⟩ ⟨12, 2, 0, 572368, 75673, 2121, 65536⟩
    (by decide) selected_cut_22483

theorem selected_cut_22484 : selected 9 ⟨572405, by decide⟩
    (prefixPartial 12 75674) = some ⟨12, 2, 0, 572405, 75674, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_75674_572405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75674 ⟨572405, by decide⟩ :=
  accepted_of_selected 12 75674 ⟨572405, by decide⟩ ⟨12, 2, 0, 572405, 75674, 2317, 65536⟩
    (by decide) selected_cut_22484

theorem selected_cut_22485 : selected 9 ⟨572433, by decide⟩
    (prefixPartial 12 75675) = some ⟨12, 2, 0, 572433, 75675, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_75675_572433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75675 ⟨572433, by decide⟩ :=
  accepted_of_selected 12 75675 ⟨572433, by decide⟩ ⟨12, 2, 0, 572433, 75675, 2061, 65536⟩
    (by decide) selected_cut_22485

theorem unmarked_context_11_18918_572434 : frontier 10 ⟨572434, by decide⟩
    (prefixCache 11 18918) (prefixPartial 11 18918) = false := by
  decide +kernel

theorem node_context_11_18918_572434 : EJMOriginalGlobalDAGData.nodes 10 ⟨572434, by decide⟩ =
    .split (coordinate 11) (![⟨572344, by decide⟩,⟨572368, by decide⟩,⟨572405, by decide⟩,⟨572433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18918_572434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18918 ⟨572434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18918
    ⟨572434, by decide⟩ (by decide) (![⟨572344, by decide⟩,⟨572368, by decide⟩,⟨572405, by decide⟩,⟨572433, by decide⟩]) unmarked_context_11_18918_572434 node_context_11_18918_572434
  intro a
  fin_cases a
  · exact context_12_75672_572344
  · exact context_12_75673_572368
  · exact context_12_75674_572405
  · exact context_12_75675_572433

theorem selected_cut_22486 : selected 9 ⟨572453, by decide⟩
    (prefixPartial 12 75676) = some ⟨12, 2, 0, 572453, 75676, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_75676_572453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75676 ⟨572453, by decide⟩ :=
  accepted_of_selected 12 75676 ⟨572453, by decide⟩ ⟨12, 2, 0, 572453, 75676, 1797, 65536⟩
    (by decide) selected_cut_22486

theorem selected_cut_22487 : selected 9 ⟨572472, by decide⟩
    (prefixPartial 12 75677) = some ⟨12, 2, 0, 572472, 75677, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_75677_572472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75677 ⟨572472, by decide⟩ :=
  accepted_of_selected 12 75677 ⟨572472, by decide⟩ ⟨12, 2, 0, 572472, 75677, 1685, 65536⟩
    (by decide) selected_cut_22487

theorem selected_cut_22488 : selected 9 ⟨572491, by decide⟩
    (prefixPartial 12 75678) = some ⟨12, 2, 0, 572491, 75678, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_75678_572491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75678 ⟨572491, by decide⟩ :=
  accepted_of_selected 12 75678 ⟨572491, by decide⟩ ⟨12, 2, 0, 572491, 75678, 1889, 65536⟩
    (by decide) selected_cut_22488

theorem selected_cut_22489 : selected 9 ⟨572535, by decide⟩
    (prefixPartial 12 75679) = some ⟨12, 2, 0, 572535, 75679, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_75679_572535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75679 ⟨572535, by decide⟩ :=
  accepted_of_selected 12 75679 ⟨572535, by decide⟩ ⟨12, 2, 0, 572535, 75679, 2525, 65536⟩
    (by decide) selected_cut_22489

theorem unmarked_context_11_18919_572536 : frontier 10 ⟨572536, by decide⟩
    (prefixCache 11 18919) (prefixPartial 11 18919) = false := by
  decide +kernel

theorem node_context_11_18919_572536 : EJMOriginalGlobalDAGData.nodes 10 ⟨572536, by decide⟩ =
    .split (coordinate 11) (![⟨572453, by decide⟩,⟨572472, by decide⟩,⟨572491, by decide⟩,⟨572535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18919_572536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18919 ⟨572536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18919
    ⟨572536, by decide⟩ (by decide) (![⟨572453, by decide⟩,⟨572472, by decide⟩,⟨572491, by decide⟩,⟨572535, by decide⟩]) unmarked_context_11_18919_572536 node_context_11_18919_572536
  intro a
  fin_cases a
  · exact context_12_75676_572453
  · exact context_12_75677_572472
  · exact context_12_75678_572491
  · exact context_12_75679_572535

theorem unmarked_context_10_4729_572537 : frontier 11 ⟨572537, by decide⟩
    (prefixCache 10 4729) (prefixPartial 10 4729) = false := by
  decide +kernel

theorem node_context_10_4729_572537 : EJMOriginalGlobalDAGData.nodes 11 ⟨572537, by decide⟩ =
    .split (coordinate 10) (![⟨572175, by decide⟩,⟨572317, by decide⟩,⟨572434, by decide⟩,⟨572536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4729_572537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4729 ⟨572537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4729
    ⟨572537, by decide⟩ (by decide) (![⟨572175, by decide⟩,⟨572317, by decide⟩,⟨572434, by decide⟩,⟨572536, by decide⟩]) unmarked_context_10_4729_572537 node_context_10_4729_572537
  intro a
  fin_cases a
  · exact context_11_18916_572175
  · exact context_11_18917_572317
  · exact context_11_18918_572434
  · exact context_11_18919_572536

theorem selected_cut_22490 : selected 9 ⟨572553, by decide⟩
    (prefixPartial 12 75680) = some ⟨12, 2, 0, 572553, 75680, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_75680_572553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75680 ⟨572553, by decide⟩ :=
  accepted_of_selected 12 75680 ⟨572553, by decide⟩ ⟨12, 2, 0, 572553, 75680, 1485, 65536⟩
    (by decide) selected_cut_22490

theorem selected_cut_22491 : selected 9 ⟨572567, by decide⟩
    (prefixPartial 12 75681) = some ⟨12, 2, 0, 572567, 75681, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_75681_572567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75681 ⟨572567, by decide⟩ :=
  accepted_of_selected 12 75681 ⟨572567, by decide⟩ ⟨12, 2, 0, 572567, 75681, 1449, 65536⟩
    (by decide) selected_cut_22491

theorem selected_cut_22492 : selected 9 ⟨572589, by decide⟩
    (prefixPartial 12 75682) = some ⟨12, 2, 0, 572589, 75682, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_75682_572589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75682 ⟨572589, by decide⟩ :=
  accepted_of_selected 12 75682 ⟨572589, by decide⟩ ⟨12, 2, 0, 572589, 75682, 1461, 65536⟩
    (by decide) selected_cut_22492

theorem selected_cut_22493 : selected 9 ⟨572601, by decide⟩
    (prefixPartial 12 75683) = some ⟨12, 2, 0, 572601, 75683, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_75683_572601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75683 ⟨572601, by decide⟩ :=
  accepted_of_selected 12 75683 ⟨572601, by decide⟩ ⟨12, 2, 0, 572601, 75683, 1421, 65536⟩
    (by decide) selected_cut_22493

theorem unmarked_context_11_18920_572602 : frontier 10 ⟨572602, by decide⟩
    (prefixCache 11 18920) (prefixPartial 11 18920) = false := by
  decide +kernel

theorem node_context_11_18920_572602 : EJMOriginalGlobalDAGData.nodes 10 ⟨572602, by decide⟩ =
    .split (coordinate 11) (![⟨572553, by decide⟩,⟨572567, by decide⟩,⟨572589, by decide⟩,⟨572601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18920_572602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18920 ⟨572602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18920
    ⟨572602, by decide⟩ (by decide) (![⟨572553, by decide⟩,⟨572567, by decide⟩,⟨572589, by decide⟩,⟨572601, by decide⟩]) unmarked_context_11_18920_572602 node_context_11_18920_572602
  intro a
  fin_cases a
  · exact context_12_75680_572553
  · exact context_12_75681_572567
  · exact context_12_75682_572589
  · exact context_12_75683_572601

theorem selected_cut_22494 : selected 9 ⟨572621, by decide⟩
    (prefixPartial 12 75684) = some ⟨12, 2, 0, 572621, 75684, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_75684_572621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75684 ⟨572621, by decide⟩ :=
  accepted_of_selected 12 75684 ⟨572621, by decide⟩ ⟨12, 2, 0, 572621, 75684, 1741, 65536⟩
    (by decide) selected_cut_22494

theorem selected_cut_22495 : selected 9 ⟨572638, by decide⟩
    (prefixPartial 12 75685) = some ⟨12, 2, 0, 572638, 75685, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_75685_572638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75685 ⟨572638, by decide⟩ :=
  accepted_of_selected 12 75685 ⟨572638, by decide⟩ ⟨12, 2, 0, 572638, 75685, 1481, 65536⟩
    (by decide) selected_cut_22495

theorem selected_cut_22496 : selected 9 ⟨572660, by decide⟩
    (prefixPartial 12 75686) = some ⟨12, 2, 0, 572660, 75686, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_75686_572660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75686 ⟨572660, by decide⟩ :=
  accepted_of_selected 12 75686 ⟨572660, by decide⟩ ⟨12, 2, 0, 572660, 75686, 1717, 65536⟩
    (by decide) selected_cut_22496

theorem selected_cut_22497 : selected 9 ⟨572673, by decide⟩
    (prefixPartial 12 75687) = some ⟨12, 2, 0, 572673, 75687, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_75687_572673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75687 ⟨572673, by decide⟩ :=
  accepted_of_selected 12 75687 ⟨572673, by decide⟩ ⟨12, 2, 0, 572673, 75687, 1533, 65536⟩
    (by decide) selected_cut_22497

theorem unmarked_context_11_18921_572674 : frontier 10 ⟨572674, by decide⟩
    (prefixCache 11 18921) (prefixPartial 11 18921) = false := by
  decide +kernel

theorem node_context_11_18921_572674 : EJMOriginalGlobalDAGData.nodes 10 ⟨572674, by decide⟩ =
    .split (coordinate 11) (![⟨572621, by decide⟩,⟨572638, by decide⟩,⟨572660, by decide⟩,⟨572673, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18921_572674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18921 ⟨572674, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18921
    ⟨572674, by decide⟩ (by decide) (![⟨572621, by decide⟩,⟨572638, by decide⟩,⟨572660, by decide⟩,⟨572673, by decide⟩]) unmarked_context_11_18921_572674 node_context_11_18921_572674
  intro a
  fin_cases a
  · exact context_12_75684_572621
  · exact context_12_75685_572638
  · exact context_12_75686_572660
  · exact context_12_75687_572673

theorem selected_cut_22498 : selected 9 ⟨572688, by decide⟩
    (prefixPartial 12 75688) = some ⟨12, 2, 0, 572688, 75688, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_75688_572688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75688 ⟨572688, by decide⟩ :=
  accepted_of_selected 12 75688 ⟨572688, by decide⟩ ⟨12, 2, 0, 572688, 75688, 1553, 65536⟩
    (by decide) selected_cut_22498

theorem selected_cut_22499 : selected 9 ⟨572705, by decide⟩
    (prefixPartial 12 75689) = some ⟨12, 2, 0, 572705, 75689, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_75689_572705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75689 ⟨572705, by decide⟩ :=
  accepted_of_selected 12 75689 ⟨572705, by decide⟩ ⟨12, 2, 0, 572705, 75689, 1461, 65536⟩
    (by decide) selected_cut_22499

theorem selected_cut_22500 : selected 9 ⟨572723, by decide⟩
    (prefixPartial 12 75690) = some ⟨12, 2, 0, 572723, 75690, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_75690_572723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75690 ⟨572723, by decide⟩ :=
  accepted_of_selected 12 75690 ⟨572723, by decide⟩ ⟨12, 2, 0, 572723, 75690, 1517, 65536⟩
    (by decide) selected_cut_22500

theorem selected_cut_22501 : selected 9 ⟨572743, by decide⟩
    (prefixPartial 12 75691) = some ⟨12, 2, 0, 572743, 75691, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_75691_572743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75691 ⟨572743, by decide⟩ :=
  accepted_of_selected 12 75691 ⟨572743, by decide⟩ ⟨12, 2, 0, 572743, 75691, 1365, 65536⟩
    (by decide) selected_cut_22501

theorem unmarked_context_11_18922_572744 : frontier 10 ⟨572744, by decide⟩
    (prefixCache 11 18922) (prefixPartial 11 18922) = false := by
  decide +kernel

theorem node_context_11_18922_572744 : EJMOriginalGlobalDAGData.nodes 10 ⟨572744, by decide⟩ =
    .split (coordinate 11) (![⟨572688, by decide⟩,⟨572705, by decide⟩,⟨572723, by decide⟩,⟨572743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18922_572744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18922 ⟨572744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18922
    ⟨572744, by decide⟩ (by decide) (![⟨572688, by decide⟩,⟨572705, by decide⟩,⟨572723, by decide⟩,⟨572743, by decide⟩]) unmarked_context_11_18922_572744 node_context_11_18922_572744
  intro a
  fin_cases a
  · exact context_12_75688_572688
  · exact context_12_75689_572705
  · exact context_12_75690_572723
  · exact context_12_75691_572743

theorem selected_cut_22502 : selected 9 ⟨572757, by decide⟩
    (prefixPartial 12 75692) = some ⟨12, 2, 0, 572757, 75692, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_75692_572757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75692 ⟨572757, by decide⟩ :=
  accepted_of_selected 12 75692 ⟨572757, by decide⟩ ⟨12, 2, 0, 572757, 75692, 1325, 65536⟩
    (by decide) selected_cut_22502

theorem selected_cut_22503 : selected 9 ⟨572770, by decide⟩
    (prefixPartial 12 75693) = some ⟨12, 2, 0, 572770, 75693, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_75693_572770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75693 ⟨572770, by decide⟩ :=
  accepted_of_selected 12 75693 ⟨572770, by decide⟩ ⟨12, 2, 0, 572770, 75693, 1281, 65536⟩
    (by decide) selected_cut_22503

theorem selected_cut_22504 : selected 9 ⟨572783, by decide⟩
    (prefixPartial 12 75694) = some ⟨12, 2, 0, 572783, 75694, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_75694_572783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75694 ⟨572783, by decide⟩ :=
  accepted_of_selected 12 75694 ⟨572783, by decide⟩ ⟨12, 2, 0, 572783, 75694, 1353, 65536⟩
    (by decide) selected_cut_22504

theorem selected_cut_22505 : selected 9 ⟨572809, by decide⟩
    (prefixPartial 12 75695) = some ⟨12, 2, 0, 572809, 75695, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_75695_572809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75695 ⟨572809, by decide⟩ :=
  accepted_of_selected 12 75695 ⟨572809, by decide⟩ ⟨12, 2, 0, 572809, 75695, 1769, 65536⟩
    (by decide) selected_cut_22505

theorem unmarked_context_11_18923_572810 : frontier 10 ⟨572810, by decide⟩
    (prefixCache 11 18923) (prefixPartial 11 18923) = false := by
  decide +kernel

theorem node_context_11_18923_572810 : EJMOriginalGlobalDAGData.nodes 10 ⟨572810, by decide⟩ =
    .split (coordinate 11) (![⟨572757, by decide⟩,⟨572770, by decide⟩,⟨572783, by decide⟩,⟨572809, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18923_572810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18923 ⟨572810, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18923
    ⟨572810, by decide⟩ (by decide) (![⟨572757, by decide⟩,⟨572770, by decide⟩,⟨572783, by decide⟩,⟨572809, by decide⟩]) unmarked_context_11_18923_572810 node_context_11_18923_572810
  intro a
  fin_cases a
  · exact context_12_75692_572757
  · exact context_12_75693_572770
  · exact context_12_75694_572783
  · exact context_12_75695_572809

theorem unmarked_context_10_4730_572811 : frontier 11 ⟨572811, by decide⟩
    (prefixCache 10 4730) (prefixPartial 10 4730) = false := by
  decide +kernel

theorem node_context_10_4730_572811 : EJMOriginalGlobalDAGData.nodes 11 ⟨572811, by decide⟩ =
    .split (coordinate 10) (![⟨572602, by decide⟩,⟨572674, by decide⟩,⟨572744, by decide⟩,⟨572810, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4730_572811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4730 ⟨572811, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4730
    ⟨572811, by decide⟩ (by decide) (![⟨572602, by decide⟩,⟨572674, by decide⟩,⟨572744, by decide⟩,⟨572810, by decide⟩]) unmarked_context_10_4730_572811 node_context_10_4730_572811
  intro a
  fin_cases a
  · exact context_11_18920_572602
  · exact context_11_18921_572674
  · exact context_11_18922_572744
  · exact context_11_18923_572810

theorem selected_cut_22506 : selected 9 ⟨572824, by decide⟩
    (prefixPartial 12 75696) = some ⟨12, 2, 0, 572824, 75696, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_75696_572824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75696 ⟨572824, by decide⟩ :=
  accepted_of_selected 12 75696 ⟨572824, by decide⟩ ⟨12, 2, 0, 572824, 75696, 1361, 65536⟩
    (by decide) selected_cut_22506

theorem selected_cut_22507 : selected 9 ⟨572838, by decide⟩
    (prefixPartial 12 75697) = some ⟨12, 2, 0, 572838, 75697, 1185, 65536⟩ := by
  decide +kernel

theorem context_12_75697_572838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75697 ⟨572838, by decide⟩ :=
  accepted_of_selected 12 75697 ⟨572838, by decide⟩ ⟨12, 2, 0, 572838, 75697, 1185, 65536⟩
    (by decide) selected_cut_22507

theorem selected_cut_22508 : selected 9 ⟨572853, by decide⟩
    (prefixPartial 12 75698) = some ⟨12, 2, 0, 572853, 75698, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_75698_572853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75698 ⟨572853, by decide⟩ :=
  accepted_of_selected 12 75698 ⟨572853, by decide⟩ ⟨12, 2, 0, 572853, 75698, 1353, 65536⟩
    (by decide) selected_cut_22508

theorem selected_cut_22509 : selected 9 ⟨572863, by decide⟩
    (prefixPartial 12 75699) = some ⟨12, 2, 0, 572863, 75699, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_75699_572863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75699 ⟨572863, by decide⟩ :=
  accepted_of_selected 12 75699 ⟨572863, by decide⟩ ⟨12, 2, 0, 572863, 75699, 1149, 65536⟩
    (by decide) selected_cut_22509

theorem unmarked_context_11_18924_572864 : frontier 10 ⟨572864, by decide⟩
    (prefixCache 11 18924) (prefixPartial 11 18924) = false := by
  decide +kernel

theorem node_context_11_18924_572864 : EJMOriginalGlobalDAGData.nodes 10 ⟨572864, by decide⟩ =
    .split (coordinate 11) (![⟨572824, by decide⟩,⟨572838, by decide⟩,⟨572853, by decide⟩,⟨572863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18924_572864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18924 ⟨572864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18924
    ⟨572864, by decide⟩ (by decide) (![⟨572824, by decide⟩,⟨572838, by decide⟩,⟨572853, by decide⟩,⟨572863, by decide⟩]) unmarked_context_11_18924_572864 node_context_11_18924_572864
  intro a
  fin_cases a
  · exact context_12_75696_572824
  · exact context_12_75697_572838
  · exact context_12_75698_572853
  · exact context_12_75699_572863

theorem selected_cut_22510 : selected 9 ⟨572881, by decide⟩
    (prefixPartial 12 75700) = some ⟨12, 2, 0, 572881, 75700, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_75700_572881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75700 ⟨572881, by decide⟩ :=
  accepted_of_selected 12 75700 ⟨572881, by decide⟩ ⟨12, 2, 0, 572881, 75700, 1421, 65536⟩
    (by decide) selected_cut_22510

theorem selected_cut_22511 : selected 9 ⟨572893, by decide⟩
    (prefixPartial 12 75701) = some ⟨12, 2, 0, 572893, 75701, 1185, 65536⟩ := by
  decide +kernel

theorem context_12_75701_572893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75701 ⟨572893, by decide⟩ :=
  accepted_of_selected 12 75701 ⟨572893, by decide⟩ ⟨12, 2, 0, 572893, 75701, 1185, 65536⟩
    (by decide) selected_cut_22511

theorem selected_cut_22512 : selected 9 ⟨572914, by decide⟩
    (prefixPartial 12 75702) = some ⟨12, 2, 0, 572914, 75702, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_75702_572914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75702 ⟨572914, by decide⟩ :=
  accepted_of_selected 12 75702 ⟨572914, by decide⟩ ⟨12, 2, 0, 572914, 75702, 1525, 65536⟩
    (by decide) selected_cut_22512

theorem selected_cut_22513 : selected 9 ⟨572928, by decide⟩
    (prefixPartial 12 75703) = some ⟨12, 2, 0, 572928, 75703, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_75703_572928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75703 ⟨572928, by decide⟩ :=
  accepted_of_selected 12 75703 ⟨572928, by decide⟩ ⟨12, 2, 0, 572928, 75703, 1301, 65536⟩
    (by decide) selected_cut_22513

theorem unmarked_context_11_18925_572929 : frontier 10 ⟨572929, by decide⟩
    (prefixCache 11 18925) (prefixPartial 11 18925) = false := by
  decide +kernel

theorem node_context_11_18925_572929 : EJMOriginalGlobalDAGData.nodes 10 ⟨572929, by decide⟩ =
    .split (coordinate 11) (![⟨572881, by decide⟩,⟨572893, by decide⟩,⟨572914, by decide⟩,⟨572928, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18925_572929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18925 ⟨572929, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18925
    ⟨572929, by decide⟩ (by decide) (![⟨572881, by decide⟩,⟨572893, by decide⟩,⟨572914, by decide⟩,⟨572928, by decide⟩]) unmarked_context_11_18925_572929 node_context_11_18925_572929
  intro a
  fin_cases a
  · exact context_12_75700_572881
  · exact context_12_75701_572893
  · exact context_12_75702_572914
  · exact context_12_75703_572928

theorem selected_cut_22514 : selected 9 ⟨572950, by decide⟩
    (prefixPartial 12 75704) = some ⟨12, 2, 0, 572950, 75704, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_75704_572950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75704 ⟨572950, by decide⟩ :=
  accepted_of_selected 12 75704 ⟨572950, by decide⟩ ⟨12, 2, 0, 572950, 75704, 1417, 65536⟩
    (by decide) selected_cut_22514

theorem selected_cut_22515 : selected 9 ⟨572967, by decide⟩
    (prefixPartial 12 75705) = some ⟨12, 2, 0, 572967, 75705, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_75705_572967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75705 ⟨572967, by decide⟩ :=
  accepted_of_selected 12 75705 ⟨572967, by decide⟩ ⟨12, 2, 0, 572967, 75705, 1253, 65536⟩
    (by decide) selected_cut_22515

theorem selected_cut_22516 : selected 9 ⟨572999, by decide⟩
    (prefixPartial 12 75706) = some ⟨12, 2, 0, 572999, 75706, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_75706_572999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75706 ⟨572999, by decide⟩ :=
  accepted_of_selected 12 75706 ⟨572999, by decide⟩ ⟨12, 2, 0, 572999, 75706, 1413, 65536⟩
    (by decide) selected_cut_22516

theorem selected_cut_22517 : selected 9 ⟨573015, by decide⟩
    (prefixPartial 12 75707) = some ⟨12, 2, 0, 573015, 75707, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_75707_573015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75707 ⟨573015, by decide⟩ :=
  accepted_of_selected 12 75707 ⟨573015, by decide⟩ ⟨12, 2, 0, 573015, 75707, 1181, 65536⟩
    (by decide) selected_cut_22517

theorem unmarked_context_11_18926_573016 : frontier 10 ⟨573016, by decide⟩
    (prefixCache 11 18926) (prefixPartial 11 18926) = false := by
  decide +kernel

theorem node_context_11_18926_573016 : EJMOriginalGlobalDAGData.nodes 10 ⟨573016, by decide⟩ =
    .split (coordinate 11) (![⟨572950, by decide⟩,⟨572967, by decide⟩,⟨572999, by decide⟩,⟨573015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18926_573016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18926 ⟨573016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18926
    ⟨573016, by decide⟩ (by decide) (![⟨572950, by decide⟩,⟨572967, by decide⟩,⟨572999, by decide⟩,⟨573015, by decide⟩]) unmarked_context_11_18926_573016 node_context_11_18926_573016
  intro a
  fin_cases a
  · exact context_12_75704_572950
  · exact context_12_75705_572967
  · exact context_12_75706_572999
  · exact context_12_75707_573015

theorem selected_cut_22518 : selected 10 ⟨573049, by decide⟩
    (prefixPartial 11 18927) = some ⟨11, 2, 0, 573049, 18927, 3037, 262144⟩ := by
  decide +kernel

theorem context_11_18927_573049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18927 ⟨573049, by decide⟩ :=
  accepted_of_selected 11 18927 ⟨573049, by decide⟩ ⟨11, 2, 0, 573049, 18927, 3037, 262144⟩
    (by decide) selected_cut_22518

theorem unmarked_context_10_4731_573050 : frontier 11 ⟨573050, by decide⟩
    (prefixCache 10 4731) (prefixPartial 10 4731) = false := by
  decide +kernel

theorem node_context_10_4731_573050 : EJMOriginalGlobalDAGData.nodes 11 ⟨573050, by decide⟩ =
    .split (coordinate 10) (![⟨572864, by decide⟩,⟨572929, by decide⟩,⟨573016, by decide⟩,⟨573049, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4731_573050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4731 ⟨573050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4731
    ⟨573050, by decide⟩ (by decide) (![⟨572864, by decide⟩,⟨572929, by decide⟩,⟨573016, by decide⟩,⟨573049, by decide⟩]) unmarked_context_10_4731_573050 node_context_10_4731_573050
  intro a
  fin_cases a
  · exact context_11_18924_572864
  · exact context_11_18925_572929
  · exact context_11_18926_573016
  · exact context_11_18927_573049

theorem unmarked_context_9_1182_573051 : frontier 12 ⟨573051, by decide⟩
    (prefixCache 9 1182) (prefixPartial 9 1182) = false := by
  decide +kernel

theorem node_context_9_1182_573051 : EJMOriginalGlobalDAGData.nodes 12 ⟨573051, by decide⟩ =
    .split (coordinate 9) (![⟨572081, by decide⟩,⟨572537, by decide⟩,⟨572811, by decide⟩,⟨573050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1182_573051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1182 ⟨573051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1182
    ⟨573051, by decide⟩ (by decide) (![⟨572081, by decide⟩,⟨572537, by decide⟩,⟨572811, by decide⟩,⟨573050, by decide⟩]) unmarked_context_9_1182_573051 node_context_9_1182_573051
  intro a
  fin_cases a
  · exact context_10_4728_572081
  · exact context_10_4729_572537
  · exact context_10_4730_572811
  · exact context_10_4731_573050

theorem selected_cut_22519 : selected 10 ⟨573073, by decide⟩
    (prefixPartial 11 18928) = some ⟨11, 2, 0, 573073, 18928, 2365, 262144⟩ := by
  decide +kernel

theorem context_11_18928_573073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18928 ⟨573073, by decide⟩ :=
  accepted_of_selected 11 18928 ⟨573073, by decide⟩ ⟨11, 2, 0, 573073, 18928, 2365, 262144⟩
    (by decide) selected_cut_22519

theorem selected_cut_22520 : selected 10 ⟨573102, by decide⟩
    (prefixPartial 11 18929) = some ⟨11, 2, 0, 573102, 18929, 2393, 262144⟩ := by
  decide +kernel

theorem context_11_18929_573102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18929 ⟨573102, by decide⟩ :=
  accepted_of_selected 11 18929 ⟨573102, by decide⟩ ⟨11, 2, 0, 573102, 18929, 2393, 262144⟩
    (by decide) selected_cut_22520

theorem selected_cut_22521 : selected 10 ⟨573127, by decide⟩
    (prefixPartial 11 18930) = some ⟨11, 2, 0, 573127, 18930, 2389, 262144⟩ := by
  decide +kernel

theorem context_11_18930_573127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18930 ⟨573127, by decide⟩ :=
  accepted_of_selected 11 18930 ⟨573127, by decide⟩ ⟨11, 2, 0, 573127, 18930, 2389, 262144⟩
    (by decide) selected_cut_22521

theorem selected_cut_22522 : selected 10 ⟨573148, by decide⟩
    (prefixPartial 11 18931) = some ⟨11, 2, 0, 573148, 18931, 1725, 262144⟩ := by
  decide +kernel

theorem context_11_18931_573148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18931 ⟨573148, by decide⟩ :=
  accepted_of_selected 11 18931 ⟨573148, by decide⟩ ⟨11, 2, 0, 573148, 18931, 1725, 262144⟩
    (by decide) selected_cut_22522

theorem unmarked_context_10_4732_573149 : frontier 11 ⟨573149, by decide⟩
    (prefixCache 10 4732) (prefixPartial 10 4732) = false := by
  decide +kernel

theorem node_context_10_4732_573149 : EJMOriginalGlobalDAGData.nodes 11 ⟨573149, by decide⟩ =
    .split (coordinate 10) (![⟨573073, by decide⟩,⟨573102, by decide⟩,⟨573127, by decide⟩,⟨573148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4732_573149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4732 ⟨573149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4732
    ⟨573149, by decide⟩ (by decide) (![⟨573073, by decide⟩,⟨573102, by decide⟩,⟨573127, by decide⟩,⟨573148, by decide⟩]) unmarked_context_10_4732_573149 node_context_10_4732_573149
  intro a
  fin_cases a
  · exact context_11_18928_573073
  · exact context_11_18929_573102
  · exact context_11_18930_573127
  · exact context_11_18931_573148

theorem selected_cut_22523 : selected 10 ⟨573168, by decide⟩
    (prefixPartial 11 18932) = some ⟨11, 2, 0, 573168, 18932, 2165, 262144⟩ := by
  decide +kernel

theorem context_11_18932_573168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18932 ⟨573168, by decide⟩ :=
  accepted_of_selected 11 18932 ⟨573168, by decide⟩ ⟨11, 2, 0, 573168, 18932, 2165, 262144⟩
    (by decide) selected_cut_22523

theorem selected_cut_22524 : selected 10 ⟨573193, by decide⟩
    (prefixPartial 11 18933) = some ⟨11, 2, 0, 573193, 18933, 2073, 262144⟩ := by
  decide +kernel

theorem context_11_18933_573193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18933 ⟨573193, by decide⟩ :=
  accepted_of_selected 11 18933 ⟨573193, by decide⟩ ⟨11, 2, 0, 573193, 18933, 2073, 262144⟩
    (by decide) selected_cut_22524

theorem selected_cut_22525 : selected 10 ⟨573212, by decide⟩
    (prefixPartial 11 18934) = some ⟨11, 2, 0, 573212, 18934, 1973, 262144⟩ := by
  decide +kernel

theorem context_11_18934_573212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18934 ⟨573212, by decide⟩ :=
  accepted_of_selected 11 18934 ⟨573212, by decide⟩ ⟨11, 2, 0, 573212, 18934, 1973, 262144⟩
    (by decide) selected_cut_22525

theorem selected_cut_22526 : selected 10 ⟨573232, by decide⟩
    (prefixPartial 11 18935) = some ⟨11, 2, 0, 573232, 18935, 1301, 262144⟩ := by
  decide +kernel

theorem context_11_18935_573232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18935 ⟨573232, by decide⟩ :=
  accepted_of_selected 11 18935 ⟨573232, by decide⟩ ⟨11, 2, 0, 573232, 18935, 1301, 262144⟩
    (by decide) selected_cut_22526

theorem unmarked_context_10_4733_573233 : frontier 11 ⟨573233, by decide⟩
    (prefixCache 10 4733) (prefixPartial 10 4733) = false := by
  decide +kernel

theorem node_context_10_4733_573233 : EJMOriginalGlobalDAGData.nodes 11 ⟨573233, by decide⟩ =
    .split (coordinate 10) (![⟨573168, by decide⟩,⟨573193, by decide⟩,⟨573212, by decide⟩,⟨573232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4733_573233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4733 ⟨573233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4733
    ⟨573233, by decide⟩ (by decide) (![⟨573168, by decide⟩,⟨573193, by decide⟩,⟨573212, by decide⟩,⟨573232, by decide⟩]) unmarked_context_10_4733_573233 node_context_10_4733_573233
  intro a
  fin_cases a
  · exact context_11_18932_573168
  · exact context_11_18933_573193
  · exact context_11_18934_573212
  · exact context_11_18935_573232

theorem selected_cut_22527 : selected 10 ⟨573250, by decide⟩
    (prefixPartial 11 18936) = some ⟨11, 2, 0, 573250, 18936, 1281, 262144⟩ := by
  decide +kernel

theorem context_11_18936_573250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18936 ⟨573250, by decide⟩ :=
  accepted_of_selected 11 18936 ⟨573250, by decide⟩ ⟨11, 2, 0, 573250, 18936, 1281, 262144⟩
    (by decide) selected_cut_22527

theorem selected_cut_22528 : selected 10 ⟨573266, by decide⟩
    (prefixPartial 11 18937) = some ⟨11, 2, 0, 573266, 18937, 1353, 262144⟩ := by
  decide +kernel

theorem context_11_18937_573266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18937 ⟨573266, by decide⟩ :=
  accepted_of_selected 11 18937 ⟨573266, by decide⟩ ⟨11, 2, 0, 573266, 18937, 1353, 262144⟩
    (by decide) selected_cut_22528

theorem selected_cut_22529 : selected 10 ⟨573284, by decide⟩
    (prefixPartial 11 18938) = some ⟨11, 2, 0, 573284, 18938, 1021, 262144⟩ := by
  decide +kernel

theorem context_11_18938_573284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18938 ⟨573284, by decide⟩ :=
  accepted_of_selected 11 18938 ⟨573284, by decide⟩ ⟨11, 2, 0, 573284, 18938, 1021, 262144⟩
    (by decide) selected_cut_22529

theorem selected_cut_22530 : selected 10 ⟨573296, by decide⟩
    (prefixPartial 11 18939) = some ⟨11, 2, 0, 573296, 18939, 685, 262144⟩ := by
  decide +kernel

theorem context_11_18939_573296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18939 ⟨573296, by decide⟩ :=
  accepted_of_selected 11 18939 ⟨573296, by decide⟩ ⟨11, 2, 0, 573296, 18939, 685, 262144⟩
    (by decide) selected_cut_22530

theorem unmarked_context_10_4734_573297 : frontier 11 ⟨573297, by decide⟩
    (prefixCache 10 4734) (prefixPartial 10 4734) = false := by
  decide +kernel

theorem node_context_10_4734_573297 : EJMOriginalGlobalDAGData.nodes 11 ⟨573297, by decide⟩ =
    .split (coordinate 10) (![⟨573250, by decide⟩,⟨573266, by decide⟩,⟨573284, by decide⟩,⟨573296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4734_573297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4734 ⟨573297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4734
    ⟨573297, by decide⟩ (by decide) (![⟨573250, by decide⟩,⟨573266, by decide⟩,⟨573284, by decide⟩,⟨573296, by decide⟩]) unmarked_context_10_4734_573297 node_context_10_4734_573297
  intro a
  fin_cases a
  · exact context_11_18936_573250
  · exact context_11_18937_573266
  · exact context_11_18938_573284
  · exact context_11_18939_573296

theorem selected_cut_22531 : selected 11 ⟨573348, by decide⟩
    (prefixPartial 10 4735) = some ⟨10, 2, 0, 573348, 4735, 1385, 1048576⟩ := by
  decide +kernel

theorem context_10_4735_573348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4735 ⟨573348, by decide⟩ :=
  accepted_of_selected 10 4735 ⟨573348, by decide⟩ ⟨10, 2, 0, 573348, 4735, 1385, 1048576⟩
    (by decide) selected_cut_22531

theorem unmarked_context_9_1183_573349 : frontier 12 ⟨573349, by decide⟩
    (prefixCache 9 1183) (prefixPartial 9 1183) = false := by
  decide +kernel

theorem node_context_9_1183_573349 : EJMOriginalGlobalDAGData.nodes 12 ⟨573349, by decide⟩ =
    .split (coordinate 9) (![⟨573149, by decide⟩,⟨573233, by decide⟩,⟨573297, by decide⟩,⟨573348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1183_573349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1183 ⟨573349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1183
    ⟨573349, by decide⟩ (by decide) (![⟨573149, by decide⟩,⟨573233, by decide⟩,⟨573297, by decide⟩,⟨573348, by decide⟩]) unmarked_context_9_1183_573349 node_context_9_1183_573349
  intro a
  fin_cases a
  · exact context_10_4732_573149
  · exact context_10_4733_573233
  · exact context_10_4734_573297
  · exact context_10_4735_573348

theorem unmarked_context_8_295_573350 : frontier 13 ⟨573350, by decide⟩
    (prefixCache 8 295) (prefixPartial 8 295) = false := by
  decide +kernel

theorem node_context_8_295_573350 : EJMOriginalGlobalDAGData.nodes 13 ⟨573350, by decide⟩ =
    .split (coordinate 8) (![⟨568144, by decide⟩,⟨571635, by decide⟩,⟨573051, by decide⟩,⟨573349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_295_573350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 295 ⟨573350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 295
    ⟨573350, by decide⟩ (by decide) (![⟨568144, by decide⟩,⟨571635, by decide⟩,⟨573051, by decide⟩,⟨573349, by decide⟩]) unmarked_context_8_295_573350 node_context_8_295_573350
  intro a
  fin_cases a
  · exact context_9_1180_568144
  · exact context_9_1181_571635
  · exact context_9_1182_573051
  · exact context_9_1183_573349

theorem unmarked_context_7_73_573351 : frontier 14 ⟨573351, by decide⟩
    (prefixCache 7 73) (prefixPartial 7 73) = false := by
  decide +kernel

theorem node_context_7_73_573351 : EJMOriginalGlobalDAGData.nodes 14 ⟨573351, by decide⟩ =
    .split (coordinate 7) (![⟨545538, by decide⟩,⟨555423, by decide⟩,⟨563736, by decide⟩,⟨573350, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_73_573351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 73 ⟨573351, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 73
    ⟨573351, by decide⟩ (by decide) (![⟨545538, by decide⟩,⟨555423, by decide⟩,⟨563736, by decide⟩,⟨573350, by decide⟩]) unmarked_context_7_73_573351 node_context_7_73_573351
  intro a
  fin_cases a
  · exact context_8_292_545538
  · exact context_8_293_555423
  · exact context_8_294_563736
  · exact context_8_295_573350

theorem selected_cut_22532 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 18944) = some ⟨11, 1, 0, 434745, 18944, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18944_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18944 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 18944 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 18944, 1, 262144⟩
    (by decide) selected_cut_22532

theorem selected_cut_22533 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 75780) = some ⟨12, 1, 0, 448748, 75780, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75780_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75780 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 75780 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 75780, 1, 65536⟩
    (by decide) selected_cut_22533

theorem selected_cut_22534 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 75781) = some ⟨12, 1, 0, 34034, 75781, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75781_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75781 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 75781 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 75781, 1, 65536⟩
    (by decide) selected_cut_22534

theorem selected_cut_22535 : selected 9 ⟨88909, by decide⟩
    (prefixPartial 12 75782) = some ⟨12, 1, 0, 88909, 75782, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75782_88909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75782 ⟨88909, by decide⟩ :=
  accepted_of_selected 12 75782 ⟨88909, by decide⟩ ⟨12, 1, 0, 88909, 75782, 1, 65536⟩
    (by decide) selected_cut_22535

theorem selected_cut_22536 : selected 8 ⟨573394, by decide⟩
    (prefixPartial 13 303132) = some ⟨13, 2, 0, 573394, 303132, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_303132_573394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303132 ⟨573394, by decide⟩ :=
  accepted_of_selected 13 303132 ⟨573394, by decide⟩ ⟨13, 2, 0, 573394, 303132, 2037, 16384⟩
    (by decide) selected_cut_22536

theorem selected_cut_22537 : selected 8 ⟨573435, by decide⟩
    (prefixPartial 13 303133) = some ⟨13, 2, 0, 573435, 303133, 2797, 16384⟩ := by
  decide +kernel

theorem context_13_303133_573435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303133 ⟨573435, by decide⟩ :=
  accepted_of_selected 13 303133 ⟨573435, by decide⟩ ⟨13, 2, 0, 573435, 303133, 2797, 16384⟩
    (by decide) selected_cut_22537

theorem selected_cut_22538 : selected 8 ⟨573463, by decide⟩
    (prefixPartial 13 303134) = some ⟨13, 2, 0, 573463, 303134, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_303134_573463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303134 ⟨573463, by decide⟩ :=
  accepted_of_selected 13 303134 ⟨573463, by decide⟩ ⟨13, 2, 0, 573463, 303134, 1833, 16384⟩
    (by decide) selected_cut_22538

theorem selected_cut_22539 : selected 8 ⟨573475, by decide⟩
    (prefixPartial 13 303135) = some ⟨13, 2, 0, 573475, 303135, 985, 16384⟩ := by
  decide +kernel

theorem context_13_303135_573475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303135 ⟨573475, by decide⟩ :=
  accepted_of_selected 13 303135 ⟨573475, by decide⟩ ⟨13, 2, 0, 573475, 303135, 985, 16384⟩
    (by decide) selected_cut_22539

theorem unmarked_context_12_75783_573476 : frontier 9 ⟨573476, by decide⟩
    (prefixCache 12 75783) (prefixPartial 12 75783) = false := by
  decide +kernel

theorem node_context_12_75783_573476 : EJMOriginalGlobalDAGData.nodes 9 ⟨573476, by decide⟩ =
    .split (coordinate 12) (![⟨573394, by decide⟩,⟨573435, by decide⟩,⟨573463, by decide⟩,⟨573475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75783_573476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75783 ⟨573476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75783
    ⟨573476, by decide⟩ (by decide) (![⟨573394, by decide⟩,⟨573435, by decide⟩,⟨573463, by decide⟩,⟨573475, by decide⟩]) unmarked_context_12_75783_573476 node_context_12_75783_573476
  intro a
  fin_cases a
  · exact context_13_303132_573394
  · exact context_13_303133_573435
  · exact context_13_303134_573463
  · exact context_13_303135_573475

theorem unmarked_context_11_18945_573477 : frontier 10 ⟨573477, by decide⟩
    (prefixCache 11 18945) (prefixPartial 11 18945) = false := by
  decide +kernel

theorem node_context_11_18945_573477 : EJMOriginalGlobalDAGData.nodes 10 ⟨573477, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨88909, by decide⟩,⟨573476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18945_573477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18945 ⟨573477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18945
    ⟨573477, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨88909, by decide⟩,⟨573476, by decide⟩]) unmarked_context_11_18945_573477 node_context_11_18945_573477
  intro a
  fin_cases a
  · exact context_12_75780_448748
  · exact context_12_75781_34034
  · exact context_12_75782_88909
  · exact context_12_75783_573476

theorem selected_cut_22540 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 75784) = some ⟨12, 1, 0, 448748, 75784, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75784_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75784 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 75784 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 75784, 1, 65536⟩
    (by decide) selected_cut_22540

theorem selected_cut_22541 : selected 8 ⟨573541, by decide⟩
    (prefixPartial 13 303140) = some ⟨13, 2, 0, 573541, 303140, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_303140_573541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303140 ⟨573541, by decide⟩ :=
  accepted_of_selected 13 303140 ⟨573541, by decide⟩ ⟨13, 2, 0, 573541, 303140, 2589, 16384⟩
    (by decide) selected_cut_22541

theorem selected_cut_22542 : selected 8 ⟨573569, by decide⟩
    (prefixPartial 13 303141) = some ⟨13, 2, 0, 573569, 303141, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_303141_573569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303141 ⟨573569, by decide⟩ :=
  accepted_of_selected 13 303141 ⟨573569, by decide⟩ ⟨13, 2, 0, 573569, 303141, 2281, 16384⟩
    (by decide) selected_cut_22542

theorem selected_cut_22543 : selected 8 ⟨573590, by decide⟩
    (prefixPartial 13 303142) = some ⟨13, 2, 0, 573590, 303142, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_303142_573590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303142 ⟨573590, by decide⟩ :=
  accepted_of_selected 13 303142 ⟨573590, by decide⟩ ⟨13, 2, 0, 573590, 303142, 1605, 16384⟩
    (by decide) selected_cut_22543

theorem selected_cut_22544 : selected 8 ⟨573605, by decide⟩
    (prefixPartial 13 303143) = some ⟨13, 2, 0, 573605, 303143, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_303143_573605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303143 ⟨573605, by decide⟩ :=
  accepted_of_selected 13 303143 ⟨573605, by decide⟩ ⟨13, 2, 0, 573605, 303143, 1125, 16384⟩
    (by decide) selected_cut_22544

theorem unmarked_context_12_75785_573606 : frontier 9 ⟨573606, by decide⟩
    (prefixCache 12 75785) (prefixPartial 12 75785) = false := by
  decide +kernel

theorem node_context_12_75785_573606 : EJMOriginalGlobalDAGData.nodes 9 ⟨573606, by decide⟩ =
    .split (coordinate 12) (![⟨573541, by decide⟩,⟨573569, by decide⟩,⟨573590, by decide⟩,⟨573605, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75785_573606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75785 ⟨573606, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75785
    ⟨573606, by decide⟩ (by decide) (![⟨573541, by decide⟩,⟨573569, by decide⟩,⟨573590, by decide⟩,⟨573605, by decide⟩]) unmarked_context_12_75785_573606 node_context_12_75785_573606
  intro a
  fin_cases a
  · exact context_13_303140_573541
  · exact context_13_303141_573569
  · exact context_13_303142_573590
  · exact context_13_303143_573605

theorem selected_cut_22545 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 75786) = some ⟨12, 1, 0, 524302, 75786, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75786_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75786 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 75786 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 75786, 1, 65536⟩
    (by decide) selected_cut_22545

theorem selected_cut_22546 : selected 9 ⟨573703, by decide⟩
    (prefixPartial 12 75787) = some ⟨12, 2, 0, 573703, 75787, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_75787_573703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75787 ⟨573703, by decide⟩ :=
  accepted_of_selected 12 75787 ⟨573703, by decide⟩ ⟨12, 2, 0, 573703, 75787, 3953, 65536⟩
    (by decide) selected_cut_22546

theorem unmarked_context_11_18946_573704 : frontier 10 ⟨573704, by decide⟩
    (prefixCache 11 18946) (prefixPartial 11 18946) = false := by
  decide +kernel

theorem node_context_11_18946_573704 : EJMOriginalGlobalDAGData.nodes 10 ⟨573704, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨573606, by decide⟩,⟨524302, by decide⟩,⟨573703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18946_573704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18946 ⟨573704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18946
    ⟨573704, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨573606, by decide⟩,⟨524302, by decide⟩,⟨573703, by decide⟩]) unmarked_context_11_18946_573704 node_context_11_18946_573704
  intro a
  fin_cases a
  · exact context_12_75784_448748
  · exact context_12_75785_573606
  · exact context_12_75786_524302
  · exact context_12_75787_573703

theorem selected_cut_22547 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 75788) = some ⟨12, 1, 0, 448748, 75788, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75788_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75788 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 75788 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 75788, 1, 65536⟩
    (by decide) selected_cut_22547

theorem selected_cut_22548 : selected 8 ⟨573751, by decide⟩
    (prefixPartial 13 303156) = some ⟨13, 2, 0, 573751, 303156, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_303156_573751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303156 ⟨573751, by decide⟩ :=
  accepted_of_selected 13 303156 ⟨573751, by decide⟩ ⟨13, 2, 0, 573751, 303156, 2281, 16384⟩
    (by decide) selected_cut_22548

theorem selected_cut_22549 : selected 8 ⟨573788, by decide⟩
    (prefixPartial 13 303157) = some ⟨13, 2, 0, 573788, 303157, 2713, 16384⟩ := by
  decide +kernel

theorem context_13_303157_573788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303157 ⟨573788, by decide⟩ :=
  accepted_of_selected 13 303157 ⟨573788, by decide⟩ ⟨13, 2, 0, 573788, 303157, 2713, 16384⟩
    (by decide) selected_cut_22549

theorem selected_cut_22550 : selected 8 ⟨573805, by decide⟩
    (prefixPartial 13 303158) = some ⟨13, 2, 0, 573805, 303158, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_303158_573805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303158 ⟨573805, by decide⟩ :=
  accepted_of_selected 13 303158 ⟨573805, by decide⟩ ⟨13, 2, 0, 573805, 303158, 1781, 16384⟩
    (by decide) selected_cut_22550

theorem selected_cut_22551 : selected 8 ⟨573821, by decide⟩
    (prefixPartial 13 303159) = some ⟨13, 2, 0, 573821, 303159, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_303159_573821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303159 ⟨573821, by decide⟩ :=
  accepted_of_selected 13 303159 ⟨573821, by decide⟩ ⟨13, 2, 0, 573821, 303159, 1149, 16384⟩
    (by decide) selected_cut_22551

theorem unmarked_context_12_75789_573822 : frontier 9 ⟨573822, by decide⟩
    (prefixCache 12 75789) (prefixPartial 12 75789) = false := by
  decide +kernel

theorem node_context_12_75789_573822 : EJMOriginalGlobalDAGData.nodes 9 ⟨573822, by decide⟩ =
    .split (coordinate 12) (![⟨573751, by decide⟩,⟨573788, by decide⟩,⟨573805, by decide⟩,⟨573821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75789_573822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75789 ⟨573822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75789
    ⟨573822, by decide⟩ (by decide) (![⟨573751, by decide⟩,⟨573788, by decide⟩,⟨573805, by decide⟩,⟨573821, by decide⟩]) unmarked_context_12_75789_573822 node_context_12_75789_573822
  intro a
  fin_cases a
  · exact context_13_303156_573751
  · exact context_13_303157_573788
  · exact context_13_303158_573805
  · exact context_13_303159_573821

theorem selected_cut_22552 : selected 9 ⟨573823, by decide⟩
    (prefixPartial 12 75790) = some ⟨12, 1, 0, 573823, 75790, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75790_573823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75790 ⟨573823, by decide⟩ :=
  accepted_of_selected 12 75790 ⟨573823, by decide⟩ ⟨12, 1, 0, 573823, 75790, 1, 65536⟩
    (by decide) selected_cut_22552

theorem selected_cut_22553 : selected 9 ⟨518278, by decide⟩
    (prefixPartial 12 75791) = some ⟨12, 1, 0, 518278, 75791, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75791_518278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75791 ⟨518278, by decide⟩ :=
  accepted_of_selected 12 75791 ⟨518278, by decide⟩ ⟨12, 1, 0, 518278, 75791, 1, 65536⟩
    (by decide) selected_cut_22553

theorem unmarked_context_11_18947_573824 : frontier 10 ⟨573824, by decide⟩
    (prefixCache 11 18947) (prefixPartial 11 18947) = false := by
  decide +kernel

theorem node_context_11_18947_573824 : EJMOriginalGlobalDAGData.nodes 10 ⟨573824, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨573822, by decide⟩,⟨573823, by decide⟩,⟨518278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18947_573824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18947 ⟨573824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18947
    ⟨573824, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨573822, by decide⟩,⟨573823, by decide⟩,⟨518278, by decide⟩]) unmarked_context_11_18947_573824 node_context_11_18947_573824
  intro a
  fin_cases a
  · exact context_12_75788_448748
  · exact context_12_75789_573822
  · exact context_12_75790_573823
  · exact context_12_75791_518278

theorem unmarked_context_10_4736_573825 : frontier 11 ⟨573825, by decide⟩
    (prefixCache 10 4736) (prefixPartial 10 4736) = false := by
  decide +kernel

theorem node_context_10_4736_573825 : EJMOriginalGlobalDAGData.nodes 11 ⟨573825, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨573477, by decide⟩,⟨573704, by decide⟩,⟨573824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4736_573825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4736 ⟨573825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4736
    ⟨573825, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨573477, by decide⟩,⟨573704, by decide⟩,⟨573824, by decide⟩]) unmarked_context_10_4736_573825 node_context_10_4736_573825
  intro a
  fin_cases a
  · exact context_11_18944_434745
  · exact context_11_18945_573477
  · exact context_11_18946_573704
  · exact context_11_18947_573824

theorem selected_cut_22554 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 75792) = some ⟨12, 1, 0, 435160, 75792, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75792_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75792 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 75792 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 75792, 1, 65536⟩
    (by decide) selected_cut_22554

theorem selected_cut_22555 : selected 8 ⟨573854, by decide⟩
    (prefixPartial 13 303172) = some ⟨13, 2, 0, 573854, 303172, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_303172_573854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303172 ⟨573854, by decide⟩ :=
  accepted_of_selected 13 303172 ⟨573854, by decide⟩ ⟨13, 2, 0, 573854, 303172, 1449, 16384⟩
    (by decide) selected_cut_22555

theorem selected_cut_22556 : selected 8 ⟨573874, by decide⟩
    (prefixPartial 13 303173) = some ⟨13, 2, 0, 573874, 303173, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_303173_573874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303173 ⟨573874, by decide⟩ :=
  accepted_of_selected 13 303173 ⟨573874, by decide⟩ ⟨13, 2, 0, 573874, 303173, 1665, 16384⟩
    (by decide) selected_cut_22556

theorem selected_cut_22557 : selected 8 ⟨573890, by decide⟩
    (prefixPartial 13 303174) = some ⟨13, 2, 0, 573890, 303174, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_303174_573890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303174 ⟨573890, by decide⟩ :=
  accepted_of_selected 13 303174 ⟨573890, by decide⟩ ⟨13, 2, 0, 573890, 303174, 1233, 16384⟩
    (by decide) selected_cut_22557

theorem selected_cut_22558 : selected 8 ⟨573895, by decide⟩
    (prefixPartial 13 303175) = some ⟨13, 2, 0, 573895, 303175, 769, 16384⟩ := by
  decide +kernel

theorem context_13_303175_573895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303175 ⟨573895, by decide⟩ :=
  accepted_of_selected 13 303175 ⟨573895, by decide⟩ ⟨13, 2, 0, 573895, 303175, 769, 16384⟩
    (by decide) selected_cut_22558

theorem unmarked_context_12_75793_573896 : frontier 9 ⟨573896, by decide⟩
    (prefixCache 12 75793) (prefixPartial 12 75793) = false := by
  decide +kernel

theorem node_context_12_75793_573896 : EJMOriginalGlobalDAGData.nodes 9 ⟨573896, by decide⟩ =
    .split (coordinate 12) (![⟨573854, by decide⟩,⟨573874, by decide⟩,⟨573890, by decide⟩,⟨573895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75793_573896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75793 ⟨573896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75793
    ⟨573896, by decide⟩ (by decide) (![⟨573854, by decide⟩,⟨573874, by decide⟩,⟨573890, by decide⟩,⟨573895, by decide⟩]) unmarked_context_12_75793_573896 node_context_12_75793_573896
  intro a
  fin_cases a
  · exact context_13_303172_573854
  · exact context_13_303173_573874
  · exact context_13_303174_573890
  · exact context_13_303175_573895

theorem selected_cut_22559 : selected 8 ⟨573925, by decide⟩
    (prefixPartial 13 303176) = some ⟨13, 2, 0, 573925, 303176, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_303176_573925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303176 ⟨573925, by decide⟩ :=
  accepted_of_selected 13 303176 ⟨573925, by decide⟩ ⟨13, 2, 0, 573925, 303176, 1257, 16384⟩
    (by decide) selected_cut_22559

theorem selected_cut_22560 : selected 8 ⟨573946, by decide⟩
    (prefixPartial 13 303177) = some ⟨13, 2, 0, 573946, 303177, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_303177_573946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303177 ⟨573946, by decide⟩ :=
  accepted_of_selected 13 303177 ⟨573946, by decide⟩ ⟨13, 2, 0, 573946, 303177, 1661, 16384⟩
    (by decide) selected_cut_22560

theorem selected_cut_22561 : selected 8 ⟨573964, by decide⟩
    (prefixPartial 13 303178) = some ⟨13, 2, 0, 573964, 303178, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_303178_573964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303178 ⟨573964, by decide⟩ :=
  accepted_of_selected 13 303178 ⟨573964, by decide⟩ ⟨13, 2, 0, 573964, 303178, 1141, 16384⟩
    (by decide) selected_cut_22561

theorem selected_cut_22562 : selected 8 ⟨573970, by decide⟩
    (prefixPartial 13 303179) = some ⟨13, 2, 0, 573970, 303179, 737, 16384⟩ := by
  decide +kernel

theorem context_13_303179_573970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303179 ⟨573970, by decide⟩ :=
  accepted_of_selected 13 303179 ⟨573970, by decide⟩ ⟨13, 2, 0, 573970, 303179, 737, 16384⟩
    (by decide) selected_cut_22562

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
