/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover087
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_08450 : selected 7 ⟨236648, by decide⟩
    (prefixPartial 14 368720) = some ⟨14, 2, 0, 236648, 368720, 1165, 4096⟩ := by
  decide +kernel

theorem context_14_368720_236648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368720 ⟨236648, by decide⟩ :=
  accepted_of_selected 14 368720 ⟨236648, by decide⟩ ⟨14, 2, 0, 236648, 368720, 1165, 4096⟩
    (by decide) selected_cut_08450

theorem selected_cut_08451 : selected 7 ⟨236666, by decide⟩
    (prefixPartial 14 368721) = some ⟨14, 2, 0, 236666, 368721, 1213, 4096⟩ := by
  decide +kernel

theorem context_14_368721_236666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368721 ⟨236666, by decide⟩ :=
  accepted_of_selected 14 368721 ⟨236666, by decide⟩ ⟨14, 2, 0, 236666, 368721, 1213, 4096⟩
    (by decide) selected_cut_08451

theorem selected_cut_08452 : selected 7 ⟨236681, by decide⟩
    (prefixPartial 14 368722) = some ⟨14, 2, 0, 236681, 368722, 901, 4096⟩ := by
  decide +kernel

theorem context_14_368722_236681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368722 ⟨236681, by decide⟩ :=
  accepted_of_selected 14 368722 ⟨236681, by decide⟩ ⟨14, 2, 0, 236681, 368722, 901, 4096⟩
    (by decide) selected_cut_08452

theorem selected_cut_08453 : selected 7 ⟨236702, by decide⟩
    (prefixPartial 14 368723) = some ⟨14, 2, 0, 236702, 368723, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_368723_236702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368723 ⟨236702, by decide⟩ :=
  accepted_of_selected 14 368723 ⟨236702, by decide⟩ ⟨14, 2, 0, 236702, 368723, 1153, 4096⟩
    (by decide) selected_cut_08453

theorem unmarked_context_13_92180_236703 : frontier 8 ⟨236703, by decide⟩
    (prefixCache 13 92180) (prefixPartial 13 92180) = false := by
  decide +kernel

theorem node_context_13_92180_236703 : EJMOriginalGlobalDAGData.nodes 8 ⟨236703, by decide⟩ =
    .split (coordinate 13) (![⟨236648, by decide⟩,⟨236666, by decide⟩,⟨236681, by decide⟩,⟨236702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92180_236703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92180 ⟨236703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92180
    ⟨236703, by decide⟩ (by decide) (![⟨236648, by decide⟩,⟨236666, by decide⟩,⟨236681, by decide⟩,⟨236702, by decide⟩]) unmarked_context_13_92180_236703 node_context_13_92180_236703
  intro a
  fin_cases a
  · exact context_14_368720_236648
  · exact context_14_368721_236666
  · exact context_14_368722_236681
  · exact context_14_368723_236702

theorem selected_cut_08454 : selected 7 ⟨236727, by decide⟩
    (prefixPartial 14 368724) = some ⟨14, 2, 0, 236727, 368724, 1089, 4096⟩ := by
  decide +kernel

theorem context_14_368724_236727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368724 ⟨236727, by decide⟩ :=
  accepted_of_selected 14 368724 ⟨236727, by decide⟩ ⟨14, 2, 0, 236727, 368724, 1089, 4096⟩
    (by decide) selected_cut_08454

theorem selected_cut_08455 : selected 7 ⟨236763, by decide⟩
    (prefixPartial 14 368725) = some ⟨14, 2, 0, 236763, 368725, 1357, 4096⟩ := by
  decide +kernel

theorem context_14_368725_236763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368725 ⟨236763, by decide⟩ :=
  accepted_of_selected 14 368725 ⟨236763, by decide⟩ ⟨14, 2, 0, 236763, 368725, 1357, 4096⟩
    (by decide) selected_cut_08455

theorem selected_cut_08456 : selected 7 ⟨236783, by decide⟩
    (prefixPartial 14 368726) = some ⟨14, 2, 0, 236783, 368726, 949, 4096⟩ := by
  decide +kernel

theorem context_14_368726_236783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368726 ⟨236783, by decide⟩ :=
  accepted_of_selected 14 368726 ⟨236783, by decide⟩ ⟨14, 2, 0, 236783, 368726, 949, 4096⟩
    (by decide) selected_cut_08456

theorem selected_cut_08457 : selected 7 ⟨236797, by decide⟩
    (prefixPartial 14 368727) = some ⟨14, 2, 0, 236797, 368727, 953, 4096⟩ := by
  decide +kernel

theorem context_14_368727_236797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368727 ⟨236797, by decide⟩ :=
  accepted_of_selected 14 368727 ⟨236797, by decide⟩ ⟨14, 2, 0, 236797, 368727, 953, 4096⟩
    (by decide) selected_cut_08457

theorem unmarked_context_13_92181_236798 : frontier 8 ⟨236798, by decide⟩
    (prefixCache 13 92181) (prefixPartial 13 92181) = false := by
  decide +kernel

theorem node_context_13_92181_236798 : EJMOriginalGlobalDAGData.nodes 8 ⟨236798, by decide⟩ =
    .split (coordinate 13) (![⟨236727, by decide⟩,⟨236763, by decide⟩,⟨236783, by decide⟩,⟨236797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92181_236798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92181 ⟨236798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92181
    ⟨236798, by decide⟩ (by decide) (![⟨236727, by decide⟩,⟨236763, by decide⟩,⟨236783, by decide⟩,⟨236797, by decide⟩]) unmarked_context_13_92181_236798 node_context_13_92181_236798
  intro a
  fin_cases a
  · exact context_14_368724_236727
  · exact context_14_368725_236763
  · exact context_14_368726_236783
  · exact context_14_368727_236797

theorem selected_cut_08458 : selected 8 ⟨236828, by decide⟩
    (prefixPartial 13 92182) = some ⟨13, 2, 0, 236828, 92182, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_92182_236828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92182 ⟨236828, by decide⟩ :=
  accepted_of_selected 13 92182 ⟨236828, by decide⟩ ⟨13, 2, 0, 236828, 92182, 1861, 16384⟩
    (by decide) selected_cut_08458

theorem selected_cut_08459 : selected 8 ⟨236862, by decide⟩
    (prefixPartial 13 92183) = some ⟨13, 2, 0, 236862, 92183, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_92183_236862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92183 ⟨236862, by decide⟩ :=
  accepted_of_selected 13 92183 ⟨236862, by decide⟩ ⟨13, 2, 0, 236862, 92183, 1409, 16384⟩
    (by decide) selected_cut_08459

theorem unmarked_context_12_23045_236863 : frontier 9 ⟨236863, by decide⟩
    (prefixCache 12 23045) (prefixPartial 12 23045) = false := by
  decide +kernel

theorem node_context_12_23045_236863 : EJMOriginalGlobalDAGData.nodes 9 ⟨236863, by decide⟩ =
    .split (coordinate 12) (![⟨236703, by decide⟩,⟨236798, by decide⟩,⟨236828, by decide⟩,⟨236862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23045_236863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23045 ⟨236863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23045
    ⟨236863, by decide⟩ (by decide) (![⟨236703, by decide⟩,⟨236798, by decide⟩,⟨236828, by decide⟩,⟨236862, by decide⟩]) unmarked_context_12_23045_236863 node_context_12_23045_236863
  intro a
  fin_cases a
  · exact context_13_92180_236703
  · exact context_13_92181_236798
  · exact context_13_92182_236828
  · exact context_13_92183_236862

theorem selected_cut_08460 : selected 7 ⟨236887, by decide⟩
    (prefixPartial 14 368736) = some ⟨14, 2, 0, 236887, 368736, 1197, 4096⟩ := by
  decide +kernel

theorem context_14_368736_236887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368736 ⟨236887, by decide⟩ :=
  accepted_of_selected 14 368736 ⟨236887, by decide⟩ ⟨14, 2, 0, 236887, 368736, 1197, 4096⟩
    (by decide) selected_cut_08460

theorem selected_cut_08461 : selected 7 ⟨236905, by decide⟩
    (prefixPartial 14 368737) = some ⟨14, 2, 0, 236905, 368737, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_368737_236905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368737 ⟨236905, by decide⟩ :=
  accepted_of_selected 14 368737 ⟨236905, by decide⟩ ⟨14, 2, 0, 236905, 368737, 1181, 4096⟩
    (by decide) selected_cut_08461

theorem selected_cut_08462 : selected 7 ⟨236915, by decide⟩
    (prefixPartial 14 368738) = some ⟨14, 2, 0, 236915, 368738, 957, 4096⟩ := by
  decide +kernel

theorem context_14_368738_236915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368738 ⟨236915, by decide⟩ :=
  accepted_of_selected 14 368738 ⟨236915, by decide⟩ ⟨14, 2, 0, 236915, 368738, 957, 4096⟩
    (by decide) selected_cut_08462

theorem selected_cut_08463 : selected 7 ⟨236936, by decide⟩
    (prefixPartial 14 368739) = some ⟨14, 2, 0, 236936, 368739, 1249, 4096⟩ := by
  decide +kernel

theorem context_14_368739_236936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368739 ⟨236936, by decide⟩ :=
  accepted_of_selected 14 368739 ⟨236936, by decide⟩ ⟨14, 2, 0, 236936, 368739, 1249, 4096⟩
    (by decide) selected_cut_08463

theorem unmarked_context_13_92184_236937 : frontier 8 ⟨236937, by decide⟩
    (prefixCache 13 92184) (prefixPartial 13 92184) = false := by
  decide +kernel

theorem node_context_13_92184_236937 : EJMOriginalGlobalDAGData.nodes 8 ⟨236937, by decide⟩ =
    .split (coordinate 13) (![⟨236887, by decide⟩,⟨236905, by decide⟩,⟨236915, by decide⟩,⟨236936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92184_236937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92184 ⟨236937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92184
    ⟨236937, by decide⟩ (by decide) (![⟨236887, by decide⟩,⟨236905, by decide⟩,⟨236915, by decide⟩,⟨236936, by decide⟩]) unmarked_context_13_92184_236937 node_context_13_92184_236937
  intro a
  fin_cases a
  · exact context_14_368736_236887
  · exact context_14_368737_236905
  · exact context_14_368738_236915
  · exact context_14_368739_236936

theorem selected_cut_08464 : selected 7 ⟨236968, by decide⟩
    (prefixPartial 14 368740) = some ⟨14, 2, 0, 236968, 368740, 1385, 4096⟩ := by
  decide +kernel

theorem context_14_368740_236968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368740 ⟨236968, by decide⟩ :=
  accepted_of_selected 14 368740 ⟨236968, by decide⟩ ⟨14, 2, 0, 236968, 368740, 1385, 4096⟩
    (by decide) selected_cut_08464

theorem selected_cut_08465 : selected 7 ⟨237002, by decide⟩
    (prefixPartial 14 368741) = some ⟨14, 2, 0, 237002, 368741, 1349, 4096⟩ := by
  decide +kernel

theorem context_14_368741_237002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368741 ⟨237002, by decide⟩ :=
  accepted_of_selected 14 368741 ⟨237002, by decide⟩ ⟨14, 2, 0, 237002, 368741, 1349, 4096⟩
    (by decide) selected_cut_08465

theorem selected_cut_08466 : selected 7 ⟨237019, by decide⟩
    (prefixPartial 14 368742) = some ⟨14, 2, 0, 237019, 368742, 957, 4096⟩ := by
  decide +kernel

theorem context_14_368742_237019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368742 ⟨237019, by decide⟩ :=
  accepted_of_selected 14 368742 ⟨237019, by decide⟩ ⟨14, 2, 0, 237019, 368742, 957, 4096⟩
    (by decide) selected_cut_08466

theorem selected_cut_08467 : selected 7 ⟨237037, by decide⟩
    (prefixPartial 14 368743) = some ⟨14, 2, 0, 237037, 368743, 1045, 4096⟩ := by
  decide +kernel

theorem context_14_368743_237037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368743 ⟨237037, by decide⟩ :=
  accepted_of_selected 14 368743 ⟨237037, by decide⟩ ⟨14, 2, 0, 237037, 368743, 1045, 4096⟩
    (by decide) selected_cut_08467

theorem unmarked_context_13_92185_237038 : frontier 8 ⟨237038, by decide⟩
    (prefixCache 13 92185) (prefixPartial 13 92185) = false := by
  decide +kernel

theorem node_context_13_92185_237038 : EJMOriginalGlobalDAGData.nodes 8 ⟨237038, by decide⟩ =
    .split (coordinate 13) (![⟨236968, by decide⟩,⟨237002, by decide⟩,⟨237019, by decide⟩,⟨237037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92185_237038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92185 ⟨237038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92185
    ⟨237038, by decide⟩ (by decide) (![⟨236968, by decide⟩,⟨237002, by decide⟩,⟨237019, by decide⟩,⟨237037, by decide⟩]) unmarked_context_13_92185_237038 node_context_13_92185_237038
  intro a
  fin_cases a
  · exact context_14_368740_236968
  · exact context_14_368741_237002
  · exact context_14_368742_237019
  · exact context_14_368743_237037

theorem selected_cut_08468 : selected 8 ⟨237068, by decide⟩
    (prefixPartial 13 92186) = some ⟨13, 2, 0, 237068, 92186, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_92186_237068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92186 ⟨237068, by decide⟩ :=
  accepted_of_selected 13 92186 ⟨237068, by decide⟩ ⟨13, 2, 0, 237068, 92186, 2221, 16384⟩
    (by decide) selected_cut_08468

theorem selected_cut_08469 : selected 8 ⟨237094, by decide⟩
    (prefixPartial 13 92187) = some ⟨13, 2, 0, 237094, 92187, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_92187_237094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92187 ⟨237094, by decide⟩ :=
  accepted_of_selected 13 92187 ⟨237094, by decide⟩ ⟨13, 2, 0, 237094, 92187, 1457, 16384⟩
    (by decide) selected_cut_08469

theorem unmarked_context_12_23046_237095 : frontier 9 ⟨237095, by decide⟩
    (prefixCache 12 23046) (prefixPartial 12 23046) = false := by
  decide +kernel

theorem node_context_12_23046_237095 : EJMOriginalGlobalDAGData.nodes 9 ⟨237095, by decide⟩ =
    .split (coordinate 12) (![⟨236937, by decide⟩,⟨237038, by decide⟩,⟨237068, by decide⟩,⟨237094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23046_237095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23046 ⟨237095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23046
    ⟨237095, by decide⟩ (by decide) (![⟨236937, by decide⟩,⟨237038, by decide⟩,⟨237068, by decide⟩,⟨237094, by decide⟩]) unmarked_context_12_23046_237095 node_context_12_23046_237095
  intro a
  fin_cases a
  · exact context_13_92184_236937
  · exact context_13_92185_237038
  · exact context_13_92186_237068
  · exact context_13_92187_237094

theorem selected_cut_08470 : selected 7 ⟨237117, by decide⟩
    (prefixPartial 14 368752) = some ⟨14, 2, 0, 237117, 368752, 1333, 4096⟩ := by
  decide +kernel

theorem context_14_368752_237117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368752 ⟨237117, by decide⟩ :=
  accepted_of_selected 14 368752 ⟨237117, by decide⟩ ⟨14, 2, 0, 237117, 368752, 1333, 4096⟩
    (by decide) selected_cut_08470

theorem selected_cut_08471 : selected 7 ⟨237147, by decide⟩
    (prefixPartial 14 368753) = some ⟨14, 2, 0, 237147, 368753, 1517, 4096⟩ := by
  decide +kernel

theorem context_14_368753_237147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368753 ⟨237147, by decide⟩ :=
  accepted_of_selected 14 368753 ⟨237147, by decide⟩ ⟨14, 2, 0, 237147, 368753, 1517, 4096⟩
    (by decide) selected_cut_08471

theorem selected_cut_08472 : selected 7 ⟨237167, by decide⟩
    (prefixPartial 14 368754) = some ⟨14, 2, 0, 237167, 368754, 1149, 4096⟩ := by
  decide +kernel

theorem context_14_368754_237167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368754 ⟨237167, by decide⟩ :=
  accepted_of_selected 14 368754 ⟨237167, by decide⟩ ⟨14, 2, 0, 237167, 368754, 1149, 4096⟩
    (by decide) selected_cut_08472

theorem selected_cut_08473 : selected 7 ⟨237196, by decide⟩
    (prefixPartial 14 368755) = some ⟨14, 2, 0, 237196, 368755, 1585, 4096⟩ := by
  decide +kernel

theorem context_14_368755_237196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368755 ⟨237196, by decide⟩ :=
  accepted_of_selected 14 368755 ⟨237196, by decide⟩ ⟨14, 2, 0, 237196, 368755, 1585, 4096⟩
    (by decide) selected_cut_08473

theorem unmarked_context_13_92188_237197 : frontier 8 ⟨237197, by decide⟩
    (prefixCache 13 92188) (prefixPartial 13 92188) = false := by
  decide +kernel

theorem node_context_13_92188_237197 : EJMOriginalGlobalDAGData.nodes 8 ⟨237197, by decide⟩ =
    .split (coordinate 13) (![⟨237117, by decide⟩,⟨237147, by decide⟩,⟨237167, by decide⟩,⟨237196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92188_237197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92188 ⟨237197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92188
    ⟨237197, by decide⟩ (by decide) (![⟨237117, by decide⟩,⟨237147, by decide⟩,⟨237167, by decide⟩,⟨237196, by decide⟩]) unmarked_context_13_92188_237197 node_context_13_92188_237197
  intro a
  fin_cases a
  · exact context_14_368752_237117
  · exact context_14_368753_237147
  · exact context_14_368754_237167
  · exact context_14_368755_237196

theorem selected_cut_08474 : selected 7 ⟨237229, by decide⟩
    (prefixPartial 14 368756) = some ⟨14, 2, 0, 237229, 368756, 1461, 4096⟩ := by
  decide +kernel

theorem context_14_368756_237229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368756 ⟨237229, by decide⟩ :=
  accepted_of_selected 14 368756 ⟨237229, by decide⟩ ⟨14, 2, 0, 237229, 368756, 1461, 4096⟩
    (by decide) selected_cut_08474

theorem selected_cut_08475 : selected 7 ⟨237269, by decide⟩
    (prefixPartial 14 368757) = some ⟨14, 2, 0, 237269, 368757, 1545, 4096⟩ := by
  decide +kernel

theorem context_14_368757_237269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368757 ⟨237269, by decide⟩ :=
  accepted_of_selected 14 368757 ⟨237269, by decide⟩ ⟨14, 2, 0, 237269, 368757, 1545, 4096⟩
    (by decide) selected_cut_08475

theorem selected_cut_08476 : selected 7 ⟨237291, by decide⟩
    (prefixPartial 14 368758) = some ⟨14, 2, 0, 237291, 368758, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_368758_237291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368758 ⟨237291, by decide⟩ :=
  accepted_of_selected 14 368758 ⟨237291, by decide⟩ ⟨14, 2, 0, 237291, 368758, 1021, 4096⟩
    (by decide) selected_cut_08476

theorem selected_cut_08477 : selected 7 ⟨237312, by decide⟩
    (prefixPartial 14 368759) = some ⟨14, 2, 0, 237312, 368759, 1109, 4096⟩ := by
  decide +kernel

theorem context_14_368759_237312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368759 ⟨237312, by decide⟩ :=
  accepted_of_selected 14 368759 ⟨237312, by decide⟩ ⟨14, 2, 0, 237312, 368759, 1109, 4096⟩
    (by decide) selected_cut_08477

theorem unmarked_context_13_92189_237313 : frontier 8 ⟨237313, by decide⟩
    (prefixCache 13 92189) (prefixPartial 13 92189) = false := by
  decide +kernel

theorem node_context_13_92189_237313 : EJMOriginalGlobalDAGData.nodes 8 ⟨237313, by decide⟩ =
    .split (coordinate 13) (![⟨237229, by decide⟩,⟨237269, by decide⟩,⟨237291, by decide⟩,⟨237312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92189_237313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92189 ⟨237313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92189
    ⟨237313, by decide⟩ (by decide) (![⟨237229, by decide⟩,⟨237269, by decide⟩,⟨237291, by decide⟩,⟨237312, by decide⟩]) unmarked_context_13_92189_237313 node_context_13_92189_237313
  intro a
  fin_cases a
  · exact context_14_368756_237229
  · exact context_14_368757_237269
  · exact context_14_368758_237291
  · exact context_14_368759_237312

theorem selected_cut_08478 : selected 8 ⟨237344, by decide⟩
    (prefixPartial 13 92190) = some ⟨13, 2, 0, 237344, 92190, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_92190_237344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92190 ⟨237344, by decide⟩ :=
  accepted_of_selected 13 92190 ⟨237344, by decide⟩ ⟨13, 2, 0, 237344, 92190, 2281, 16384⟩
    (by decide) selected_cut_08478

theorem selected_cut_08479 : selected 8 ⟨237369, by decide⟩
    (prefixPartial 13 92191) = some ⟨13, 2, 0, 237369, 92191, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_92191_237369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92191 ⟨237369, by decide⟩ :=
  accepted_of_selected 13 92191 ⟨237369, by decide⟩ ⟨13, 2, 0, 237369, 92191, 1445, 16384⟩
    (by decide) selected_cut_08479

theorem unmarked_context_12_23047_237370 : frontier 9 ⟨237370, by decide⟩
    (prefixCache 12 23047) (prefixPartial 12 23047) = false := by
  decide +kernel

theorem node_context_12_23047_237370 : EJMOriginalGlobalDAGData.nodes 9 ⟨237370, by decide⟩ =
    .split (coordinate 12) (![⟨237197, by decide⟩,⟨237313, by decide⟩,⟨237344, by decide⟩,⟨237369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23047_237370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23047 ⟨237370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23047
    ⟨237370, by decide⟩ (by decide) (![⟨237197, by decide⟩,⟨237313, by decide⟩,⟨237344, by decide⟩,⟨237369, by decide⟩]) unmarked_context_12_23047_237370 node_context_12_23047_237370
  intro a
  fin_cases a
  · exact context_13_92188_237197
  · exact context_13_92189_237313
  · exact context_13_92190_237344
  · exact context_13_92191_237369

theorem unmarked_context_11_5761_237371 : frontier 10 ⟨237371, by decide⟩
    (prefixCache 11 5761) (prefixPartial 11 5761) = false := by
  decide +kernel

theorem node_context_11_5761_237371 : EJMOriginalGlobalDAGData.nodes 10 ⟨237371, by decide⟩ =
    .split (coordinate 11) (![⟨236625, by decide⟩,⟨236863, by decide⟩,⟨237095, by decide⟩,⟨237370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5761_237371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5761 ⟨237371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5761
    ⟨237371, by decide⟩ (by decide) (![⟨236625, by decide⟩,⟨236863, by decide⟩,⟨237095, by decide⟩,⟨237370, by decide⟩]) unmarked_context_11_5761_237371 node_context_11_5761_237371
  intro a
  fin_cases a
  · exact context_12_23044_236625
  · exact context_12_23045_236863
  · exact context_12_23046_237095
  · exact context_12_23047_237370

theorem selected_cut_08480 : selected 8 ⟨237415, by decide⟩
    (prefixPartial 13 92192) = some ⟨13, 2, 0, 237415, 92192, 3029, 16384⟩ := by
  decide +kernel

theorem context_13_92192_237415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92192 ⟨237415, by decide⟩ :=
  accepted_of_selected 13 92192 ⟨237415, by decide⟩ ⟨13, 2, 0, 237415, 92192, 3029, 16384⟩
    (by decide) selected_cut_08480

theorem selected_cut_08481 : selected 7 ⟨237446, by decide⟩
    (prefixPartial 14 368772) = some ⟨14, 2, 0, 237446, 368772, 1409, 4096⟩ := by
  decide +kernel

theorem context_14_368772_237446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368772 ⟨237446, by decide⟩ :=
  accepted_of_selected 14 368772 ⟨237446, by decide⟩ ⟨14, 2, 0, 237446, 368772, 1409, 4096⟩
    (by decide) selected_cut_08481

theorem selected_cut_08482 : selected 7 ⟨237474, by decide⟩
    (prefixPartial 14 368773) = some ⟨14, 2, 0, 237474, 368773, 1269, 4096⟩ := by
  decide +kernel

theorem context_14_368773_237474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368773 ⟨237474, by decide⟩ :=
  accepted_of_selected 14 368773 ⟨237474, by decide⟩ ⟨14, 2, 0, 237474, 368773, 1269, 4096⟩
    (by decide) selected_cut_08482

theorem selected_cut_08483 : selected 7 ⟨237486, by decide⟩
    (prefixPartial 14 368774) = some ⟨14, 2, 0, 237486, 368774, 781, 4096⟩ := by
  decide +kernel

theorem context_14_368774_237486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368774 ⟨237486, by decide⟩ :=
  accepted_of_selected 14 368774 ⟨237486, by decide⟩ ⟨14, 2, 0, 237486, 368774, 781, 4096⟩
    (by decide) selected_cut_08483

theorem selected_cut_08484 : selected 7 ⟨237501, by decide⟩
    (prefixPartial 14 368775) = some ⟨14, 2, 0, 237501, 368775, 965, 4096⟩ := by
  decide +kernel

theorem context_14_368775_237501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368775 ⟨237501, by decide⟩ :=
  accepted_of_selected 14 368775 ⟨237501, by decide⟩ ⟨14, 2, 0, 237501, 368775, 965, 4096⟩
    (by decide) selected_cut_08484

theorem unmarked_context_13_92193_237502 : frontier 8 ⟨237502, by decide⟩
    (prefixCache 13 92193) (prefixPartial 13 92193) = false := by
  decide +kernel

theorem node_context_13_92193_237502 : EJMOriginalGlobalDAGData.nodes 8 ⟨237502, by decide⟩ =
    .split (coordinate 13) (![⟨237446, by decide⟩,⟨237474, by decide⟩,⟨237486, by decide⟩,⟨237501, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92193_237502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92193 ⟨237502, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92193
    ⟨237502, by decide⟩ (by decide) (![⟨237446, by decide⟩,⟨237474, by decide⟩,⟨237486, by decide⟩,⟨237501, by decide⟩]) unmarked_context_13_92193_237502 node_context_13_92193_237502
  intro a
  fin_cases a
  · exact context_14_368772_237446
  · exact context_14_368773_237474
  · exact context_14_368774_237486
  · exact context_14_368775_237501

theorem selected_cut_08485 : selected 8 ⟨237548, by decide⟩
    (prefixPartial 13 92194) = some ⟨13, 2, 0, 237548, 92194, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_92194_237548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92194 ⟨237548, by decide⟩ :=
  accepted_of_selected 13 92194 ⟨237548, by decide⟩ ⟨13, 2, 0, 237548, 92194, 2357, 16384⟩
    (by decide) selected_cut_08485

theorem selected_cut_08486 : selected 8 ⟨237561, by decide⟩
    (prefixPartial 13 92195) = some ⟨13, 2, 0, 237561, 92195, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_92195_237561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92195 ⟨237561, by decide⟩ :=
  accepted_of_selected 13 92195 ⟨237561, by decide⟩ ⟨13, 2, 0, 237561, 92195, 1265, 16384⟩
    (by decide) selected_cut_08486

theorem unmarked_context_12_23048_237562 : frontier 9 ⟨237562, by decide⟩
    (prefixCache 12 23048) (prefixPartial 12 23048) = false := by
  decide +kernel

theorem node_context_12_23048_237562 : EJMOriginalGlobalDAGData.nodes 9 ⟨237562, by decide⟩ =
    .split (coordinate 12) (![⟨237415, by decide⟩,⟨237502, by decide⟩,⟨237548, by decide⟩,⟨237561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23048_237562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23048 ⟨237562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23048
    ⟨237562, by decide⟩ (by decide) (![⟨237415, by decide⟩,⟨237502, by decide⟩,⟨237548, by decide⟩,⟨237561, by decide⟩]) unmarked_context_12_23048_237562 node_context_12_23048_237562
  intro a
  fin_cases a
  · exact context_13_92192_237415
  · exact context_13_92193_237502
  · exact context_13_92194_237548
  · exact context_13_92195_237561

theorem selected_cut_08487 : selected 8 ⟨237626, by decide⟩
    (prefixPartial 13 92196) = some ⟨13, 2, 0, 237626, 92196, 3873, 16384⟩ := by
  decide +kernel

theorem context_13_92196_237626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92196 ⟨237626, by decide⟩ :=
  accepted_of_selected 13 92196 ⟨237626, by decide⟩ ⟨13, 2, 0, 237626, 92196, 3873, 16384⟩
    (by decide) selected_cut_08487

theorem selected_cut_08488 : selected 8 ⟨237700, by decide⟩
    (prefixPartial 13 92197) = some ⟨13, 2, 0, 237700, 92197, 3989, 16384⟩ := by
  decide +kernel

theorem context_13_92197_237700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92197 ⟨237700, by decide⟩ :=
  accepted_of_selected 13 92197 ⟨237700, by decide⟩ ⟨13, 2, 0, 237700, 92197, 3989, 16384⟩
    (by decide) selected_cut_08488

theorem selected_cut_08489 : selected 8 ⟨237742, by decide⟩
    (prefixPartial 13 92198) = some ⟨13, 2, 0, 237742, 92198, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_92198_237742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92198 ⟨237742, by decide⟩ :=
  accepted_of_selected 13 92198 ⟨237742, by decide⟩ ⟨13, 2, 0, 237742, 92198, 2097, 16384⟩
    (by decide) selected_cut_08489

theorem selected_cut_08490 : selected 8 ⟨237756, by decide⟩
    (prefixPartial 13 92199) = some ⟨13, 2, 0, 237756, 92199, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_92199_237756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92199 ⟨237756, by decide⟩ :=
  accepted_of_selected 13 92199 ⟨237756, by decide⟩ ⟨13, 2, 0, 237756, 92199, 1285, 16384⟩
    (by decide) selected_cut_08490

theorem unmarked_context_12_23049_237757 : frontier 9 ⟨237757, by decide⟩
    (prefixCache 12 23049) (prefixPartial 12 23049) = false := by
  decide +kernel

theorem node_context_12_23049_237757 : EJMOriginalGlobalDAGData.nodes 9 ⟨237757, by decide⟩ =
    .split (coordinate 12) (![⟨237626, by decide⟩,⟨237700, by decide⟩,⟨237742, by decide⟩,⟨237756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23049_237757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23049 ⟨237757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23049
    ⟨237757, by decide⟩ (by decide) (![⟨237626, by decide⟩,⟨237700, by decide⟩,⟨237742, by decide⟩,⟨237756, by decide⟩]) unmarked_context_12_23049_237757 node_context_12_23049_237757
  intro a
  fin_cases a
  · exact context_13_92196_237626
  · exact context_13_92197_237700
  · exact context_13_92198_237742
  · exact context_13_92199_237756

theorem selected_cut_08491 : selected 7 ⟨237784, by decide⟩
    (prefixPartial 14 368800) = some ⟨14, 2, 0, 237784, 368800, 1405, 4096⟩ := by
  decide +kernel

theorem context_14_368800_237784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368800 ⟨237784, by decide⟩ :=
  accepted_of_selected 14 368800 ⟨237784, by decide⟩ ⟨14, 2, 0, 237784, 368800, 1405, 4096⟩
    (by decide) selected_cut_08491

theorem selected_cut_08492 : selected 7 ⟨237824, by decide⟩
    (prefixPartial 14 368801) = some ⟨14, 2, 0, 237824, 368801, 1929, 4096⟩ := by
  decide +kernel

theorem context_14_368801_237824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368801 ⟨237824, by decide⟩ :=
  accepted_of_selected 14 368801 ⟨237824, by decide⟩ ⟨14, 2, 0, 237824, 368801, 1929, 4096⟩
    (by decide) selected_cut_08492

theorem selected_cut_08493 : selected 7 ⟨237845, by decide⟩
    (prefixPartial 14 368802) = some ⟨14, 2, 0, 237845, 368802, 1405, 4096⟩ := by
  decide +kernel

theorem context_14_368802_237845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368802 ⟨237845, by decide⟩ :=
  accepted_of_selected 14 368802 ⟨237845, by decide⟩ ⟨14, 2, 0, 237845, 368802, 1405, 4096⟩
    (by decide) selected_cut_08493

theorem selected_cut_08494 : selected 7 ⟨237881, by decide⟩
    (prefixPartial 14 368803) = some ⟨14, 2, 0, 237881, 368803, 1765, 4096⟩ := by
  decide +kernel

theorem context_14_368803_237881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368803 ⟨237881, by decide⟩ :=
  accepted_of_selected 14 368803 ⟨237881, by decide⟩ ⟨14, 2, 0, 237881, 368803, 1765, 4096⟩
    (by decide) selected_cut_08494

theorem unmarked_context_13_92200_237882 : frontier 8 ⟨237882, by decide⟩
    (prefixCache 13 92200) (prefixPartial 13 92200) = false := by
  decide +kernel

theorem node_context_13_92200_237882 : EJMOriginalGlobalDAGData.nodes 8 ⟨237882, by decide⟩ =
    .split (coordinate 13) (![⟨237784, by decide⟩,⟨237824, by decide⟩,⟨237845, by decide⟩,⟨237881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92200_237882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92200 ⟨237882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92200
    ⟨237882, by decide⟩ (by decide) (![⟨237784, by decide⟩,⟨237824, by decide⟩,⟨237845, by decide⟩,⟨237881, by decide⟩]) unmarked_context_13_92200_237882 node_context_13_92200_237882
  intro a
  fin_cases a
  · exact context_14_368800_237784
  · exact context_14_368801_237824
  · exact context_14_368802_237845
  · exact context_14_368803_237881

theorem selected_cut_08495 : selected 7 ⟨237925, by decide⟩
    (prefixPartial 14 368804) = some ⟨14, 2, 0, 237925, 368804, 2093, 4096⟩ := by
  decide +kernel

theorem context_14_368804_237925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368804 ⟨237925, by decide⟩ :=
  accepted_of_selected 14 368804 ⟨237925, by decide⟩ ⟨14, 2, 0, 237925, 368804, 2093, 4096⟩
    (by decide) selected_cut_08495

theorem selected_cut_08496 : selected 7 ⟨237978, by decide⟩
    (prefixPartial 14 368805) = some ⟨14, 2, 0, 237978, 368805, 2317, 4096⟩ := by
  decide +kernel

theorem context_14_368805_237978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368805 ⟨237978, by decide⟩ :=
  accepted_of_selected 14 368805 ⟨237978, by decide⟩ ⟨14, 2, 0, 237978, 368805, 2317, 4096⟩
    (by decide) selected_cut_08496

theorem selected_cut_08497 : selected 7 ⟨238018, by decide⟩
    (prefixPartial 14 368806) = some ⟨14, 2, 0, 238018, 368806, 1613, 4096⟩ := by
  decide +kernel

theorem context_14_368806_238018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368806 ⟨238018, by decide⟩ :=
  accepted_of_selected 14 368806 ⟨238018, by decide⟩ ⟨14, 2, 0, 238018, 368806, 1613, 4096⟩
    (by decide) selected_cut_08497

theorem selected_cut_08498 : selected 7 ⟨238044, by decide⟩
    (prefixPartial 14 368807) = some ⟨14, 2, 0, 238044, 368807, 1653, 4096⟩ := by
  decide +kernel

theorem context_14_368807_238044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368807 ⟨238044, by decide⟩ :=
  accepted_of_selected 14 368807 ⟨238044, by decide⟩ ⟨14, 2, 0, 238044, 368807, 1653, 4096⟩
    (by decide) selected_cut_08498

theorem unmarked_context_13_92201_238045 : frontier 8 ⟨238045, by decide⟩
    (prefixCache 13 92201) (prefixPartial 13 92201) = false := by
  decide +kernel

theorem node_context_13_92201_238045 : EJMOriginalGlobalDAGData.nodes 8 ⟨238045, by decide⟩ =
    .split (coordinate 13) (![⟨237925, by decide⟩,⟨237978, by decide⟩,⟨238018, by decide⟩,⟨238044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92201_238045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92201 ⟨238045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92201
    ⟨238045, by decide⟩ (by decide) (![⟨237925, by decide⟩,⟨237978, by decide⟩,⟨238018, by decide⟩,⟨238044, by decide⟩]) unmarked_context_13_92201_238045 node_context_13_92201_238045
  intro a
  fin_cases a
  · exact context_14_368804_237925
  · exact context_14_368805_237978
  · exact context_14_368806_238018
  · exact context_14_368807_238044

theorem selected_cut_08499 : selected 7 ⟨238076, by decide⟩
    (prefixPartial 14 368808) = some ⟨14, 2, 0, 238076, 368808, 1009, 4096⟩ := by
  decide +kernel

theorem context_14_368808_238076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368808 ⟨238076, by decide⟩ :=
  accepted_of_selected 14 368808 ⟨238076, by decide⟩ ⟨14, 2, 0, 238076, 368808, 1009, 4096⟩
    (by decide) selected_cut_08499

theorem selected_cut_08500 : selected 7 ⟨238126, by decide⟩
    (prefixPartial 14 368809) = some ⟨14, 2, 0, 238126, 368809, 1437, 4096⟩ := by
  decide +kernel

theorem context_14_368809_238126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368809 ⟨238126, by decide⟩ :=
  accepted_of_selected 14 368809 ⟨238126, by decide⟩ ⟨14, 2, 0, 238126, 368809, 1437, 4096⟩
    (by decide) selected_cut_08500

theorem selected_cut_08501 : selected 7 ⟨238145, by decide⟩
    (prefixPartial 14 368810) = some ⟨14, 2, 0, 238145, 368810, 753, 4096⟩ := by
  decide +kernel

theorem context_14_368810_238145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368810 ⟨238145, by decide⟩ :=
  accepted_of_selected 14 368810 ⟨238145, by decide⟩ ⟨14, 2, 0, 238145, 368810, 753, 4096⟩
    (by decide) selected_cut_08501

theorem selected_cut_08502 : selected 7 ⟨238178, by decide⟩
    (prefixPartial 14 368811) = some ⟨14, 2, 0, 238178, 368811, 1025, 4096⟩ := by
  decide +kernel

theorem context_14_368811_238178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368811 ⟨238178, by decide⟩ :=
  accepted_of_selected 14 368811 ⟨238178, by decide⟩ ⟨14, 2, 0, 238178, 368811, 1025, 4096⟩
    (by decide) selected_cut_08502

theorem unmarked_context_13_92202_238179 : frontier 8 ⟨238179, by decide⟩
    (prefixCache 13 92202) (prefixPartial 13 92202) = false := by
  decide +kernel

theorem node_context_13_92202_238179 : EJMOriginalGlobalDAGData.nodes 8 ⟨238179, by decide⟩ =
    .split (coordinate 13) (![⟨238076, by decide⟩,⟨238126, by decide⟩,⟨238145, by decide⟩,⟨238178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92202_238179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92202 ⟨238179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92202
    ⟨238179, by decide⟩ (by decide) (![⟨238076, by decide⟩,⟨238126, by decide⟩,⟨238145, by decide⟩,⟨238178, by decide⟩]) unmarked_context_13_92202_238179 node_context_13_92202_238179
  intro a
  fin_cases a
  · exact context_14_368808_238076
  · exact context_14_368809_238126
  · exact context_14_368810_238145
  · exact context_14_368811_238178

theorem selected_cut_08503 : selected 8 ⟨238245, by decide⟩
    (prefixPartial 13 92203) = some ⟨13, 2, 0, 238245, 92203, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_92203_238245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92203 ⟨238245, by decide⟩ :=
  accepted_of_selected 13 92203 ⟨238245, by decide⟩ ⟨13, 2, 0, 238245, 92203, 1893, 16384⟩
    (by decide) selected_cut_08503

theorem unmarked_context_12_23050_238246 : frontier 9 ⟨238246, by decide⟩
    (prefixCache 12 23050) (prefixPartial 12 23050) = false := by
  decide +kernel

theorem node_context_12_23050_238246 : EJMOriginalGlobalDAGData.nodes 9 ⟨238246, by decide⟩ =
    .split (coordinate 12) (![⟨237882, by decide⟩,⟨238045, by decide⟩,⟨238179, by decide⟩,⟨238245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23050_238246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23050 ⟨238246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23050
    ⟨238246, by decide⟩ (by decide) (![⟨237882, by decide⟩,⟨238045, by decide⟩,⟨238179, by decide⟩,⟨238245, by decide⟩]) unmarked_context_12_23050_238246 node_context_12_23050_238246
  intro a
  fin_cases a
  · exact context_13_92200_237882
  · exact context_13_92201_238045
  · exact context_13_92202_238179
  · exact context_13_92203_238245

theorem selected_cut_08504 : selected 7 ⟨238257, by decide⟩
    (prefixPartial 14 368816) = some ⟨14, 2, 0, 238257, 368816, 657, 4096⟩ := by
  decide +kernel

theorem context_14_368816_238257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368816 ⟨238257, by decide⟩ :=
  accepted_of_selected 14 368816 ⟨238257, by decide⟩ ⟨14, 2, 0, 238257, 368816, 657, 4096⟩
    (by decide) selected_cut_08504

theorem selected_cut_08505 : selected 7 ⟨238282, by decide⟩
    (prefixPartial 14 368817) = some ⟨14, 2, 0, 238282, 368817, 1453, 4096⟩ := by
  decide +kernel

theorem context_14_368817_238282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368817 ⟨238282, by decide⟩ :=
  accepted_of_selected 14 368817 ⟨238282, by decide⟩ ⟨14, 2, 0, 238282, 368817, 1453, 4096⟩
    (by decide) selected_cut_08505

theorem selected_cut_08506 : selected 7 ⟨238302, by decide⟩
    (prefixPartial 14 368818) = some ⟨14, 2, 0, 238302, 368818, 1141, 4096⟩ := by
  decide +kernel

theorem context_14_368818_238302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368818 ⟨238302, by decide⟩ :=
  accepted_of_selected 14 368818 ⟨238302, by decide⟩ ⟨14, 2, 0, 238302, 368818, 1141, 4096⟩
    (by decide) selected_cut_08506

theorem selected_cut_08507 : selected 7 ⟨238324, by decide⟩
    (prefixPartial 14 368819) = some ⟨14, 2, 0, 238324, 368819, 1269, 4096⟩ := by
  decide +kernel

theorem context_14_368819_238324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368819 ⟨238324, by decide⟩ :=
  accepted_of_selected 14 368819 ⟨238324, by decide⟩ ⟨14, 2, 0, 238324, 368819, 1269, 4096⟩
    (by decide) selected_cut_08507

theorem unmarked_context_13_92204_238325 : frontier 8 ⟨238325, by decide⟩
    (prefixCache 13 92204) (prefixPartial 13 92204) = false := by
  decide +kernel

theorem node_context_13_92204_238325 : EJMOriginalGlobalDAGData.nodes 8 ⟨238325, by decide⟩ =
    .split (coordinate 13) (![⟨238257, by decide⟩,⟨238282, by decide⟩,⟨238302, by decide⟩,⟨238324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92204_238325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92204 ⟨238325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92204
    ⟨238325, by decide⟩ (by decide) (![⟨238257, by decide⟩,⟨238282, by decide⟩,⟨238302, by decide⟩,⟨238324, by decide⟩]) unmarked_context_13_92204_238325 node_context_13_92204_238325
  intro a
  fin_cases a
  · exact context_14_368816_238257
  · exact context_14_368817_238282
  · exact context_14_368818_238302
  · exact context_14_368819_238324

theorem selected_cut_08508 : selected 7 ⟨238357, by decide⟩
    (prefixPartial 14 368820) = some ⟨14, 2, 0, 238357, 368820, 1405, 4096⟩ := by
  decide +kernel

theorem context_14_368820_238357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368820 ⟨238357, by decide⟩ :=
  accepted_of_selected 14 368820 ⟨238357, by decide⟩ ⟨14, 2, 0, 238357, 368820, 1405, 4096⟩
    (by decide) selected_cut_08508

theorem selected_cut_08509 : selected 7 ⟨238393, by decide⟩
    (prefixPartial 14 368821) = some ⟨14, 2, 0, 238393, 368821, 1553, 4096⟩ := by
  decide +kernel

theorem context_14_368821_238393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368821 ⟨238393, by decide⟩ :=
  accepted_of_selected 14 368821 ⟨238393, by decide⟩ ⟨14, 2, 0, 238393, 368821, 1553, 4096⟩
    (by decide) selected_cut_08509

theorem selected_cut_08510 : selected 7 ⟨238410, by decide⟩
    (prefixPartial 14 368822) = some ⟨14, 2, 0, 238410, 368822, 1009, 4096⟩ := by
  decide +kernel

theorem context_14_368822_238410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368822 ⟨238410, by decide⟩ :=
  accepted_of_selected 14 368822 ⟨238410, by decide⟩ ⟨14, 2, 0, 238410, 368822, 1009, 4096⟩
    (by decide) selected_cut_08510

theorem selected_cut_08511 : selected 7 ⟨238430, by decide⟩
    (prefixPartial 14 368823) = some ⟨14, 2, 0, 238430, 368823, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_368823_238430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368823 ⟨238430, by decide⟩ :=
  accepted_of_selected 14 368823 ⟨238430, by decide⟩ ⟨14, 2, 0, 238430, 368823, 1097, 4096⟩
    (by decide) selected_cut_08511

theorem unmarked_context_13_92205_238431 : frontier 8 ⟨238431, by decide⟩
    (prefixCache 13 92205) (prefixPartial 13 92205) = false := by
  decide +kernel

theorem node_context_13_92205_238431 : EJMOriginalGlobalDAGData.nodes 8 ⟨238431, by decide⟩ =
    .split (coordinate 13) (![⟨238357, by decide⟩,⟨238393, by decide⟩,⟨238410, by decide⟩,⟨238430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92205_238431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92205 ⟨238431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92205
    ⟨238431, by decide⟩ (by decide) (![⟨238357, by decide⟩,⟨238393, by decide⟩,⟨238410, by decide⟩,⟨238430, by decide⟩]) unmarked_context_13_92205_238431 node_context_13_92205_238431
  intro a
  fin_cases a
  · exact context_14_368820_238357
  · exact context_14_368821_238393
  · exact context_14_368822_238410
  · exact context_14_368823_238430

theorem selected_cut_08512 : selected 8 ⟨238469, by decide⟩
    (prefixPartial 13 92206) = some ⟨13, 2, 0, 238469, 92206, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_92206_238469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92206 ⟨238469, by decide⟩ :=
  accepted_of_selected 13 92206 ⟨238469, by decide⟩ ⟨13, 2, 0, 238469, 92206, 2345, 16384⟩
    (by decide) selected_cut_08512

theorem selected_cut_08513 : selected 8 ⟨238486, by decide⟩
    (prefixPartial 13 92207) = some ⟨13, 2, 0, 238486, 92207, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_92207_238486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92207 ⟨238486, by decide⟩ :=
  accepted_of_selected 13 92207 ⟨238486, by decide⟩ ⟨13, 2, 0, 238486, 92207, 1325, 16384⟩
    (by decide) selected_cut_08513

theorem unmarked_context_12_23051_238487 : frontier 9 ⟨238487, by decide⟩
    (prefixCache 12 23051) (prefixPartial 12 23051) = false := by
  decide +kernel

theorem node_context_12_23051_238487 : EJMOriginalGlobalDAGData.nodes 9 ⟨238487, by decide⟩ =
    .split (coordinate 12) (![⟨238325, by decide⟩,⟨238431, by decide⟩,⟨238469, by decide⟩,⟨238486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23051_238487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23051 ⟨238487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23051
    ⟨238487, by decide⟩ (by decide) (![⟨238325, by decide⟩,⟨238431, by decide⟩,⟨238469, by decide⟩,⟨238486, by decide⟩]) unmarked_context_12_23051_238487 node_context_12_23051_238487
  intro a
  fin_cases a
  · exact context_13_92204_238325
  · exact context_13_92205_238431
  · exact context_13_92206_238469
  · exact context_13_92207_238486

theorem unmarked_context_11_5762_238488 : frontier 10 ⟨238488, by decide⟩
    (prefixCache 11 5762) (prefixPartial 11 5762) = false := by
  decide +kernel

theorem node_context_11_5762_238488 : EJMOriginalGlobalDAGData.nodes 10 ⟨238488, by decide⟩ =
    .split (coordinate 11) (![⟨237562, by decide⟩,⟨237757, by decide⟩,⟨238246, by decide⟩,⟨238487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5762_238488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5762 ⟨238488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5762
    ⟨238488, by decide⟩ (by decide) (![⟨237562, by decide⟩,⟨237757, by decide⟩,⟨238246, by decide⟩,⟨238487, by decide⟩]) unmarked_context_11_5762_238488 node_context_11_5762_238488
  intro a
  fin_cases a
  · exact context_12_23048_237562
  · exact context_12_23049_237757
  · exact context_12_23050_238246
  · exact context_12_23051_238487

theorem selected_cut_08514 : selected 8 ⟨238539, by decide⟩
    (prefixPartial 13 92208) = some ⟨13, 2, 0, 238539, 92208, 2981, 16384⟩ := by
  decide +kernel

theorem context_13_92208_238539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92208 ⟨238539, by decide⟩ :=
  accepted_of_selected 13 92208 ⟨238539, by decide⟩ ⟨13, 2, 0, 238539, 92208, 2981, 16384⟩
    (by decide) selected_cut_08514

theorem selected_cut_08515 : selected 7 ⟨238571, by decide⟩
    (prefixPartial 14 368836) = some ⟨14, 2, 0, 238571, 368836, 1529, 4096⟩ := by
  decide +kernel

theorem context_14_368836_238571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368836 ⟨238571, by decide⟩ :=
  accepted_of_selected 14 368836 ⟨238571, by decide⟩ ⟨14, 2, 0, 238571, 368836, 1529, 4096⟩
    (by decide) selected_cut_08515

theorem selected_cut_08516 : selected 7 ⟨238604, by decide⟩
    (prefixPartial 14 368837) = some ⟨14, 2, 0, 238604, 368837, 1453, 4096⟩ := by
  decide +kernel

theorem context_14_368837_238604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368837 ⟨238604, by decide⟩ :=
  accepted_of_selected 14 368837 ⟨238604, by decide⟩ ⟨14, 2, 0, 238604, 368837, 1453, 4096⟩
    (by decide) selected_cut_08516

theorem selected_cut_08517 : selected 7 ⟨238618, by decide⟩
    (prefixPartial 14 368838) = some ⟨14, 2, 0, 238618, 368838, 933, 4096⟩ := by
  decide +kernel

theorem context_14_368838_238618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368838 ⟨238618, by decide⟩ :=
  accepted_of_selected 14 368838 ⟨238618, by decide⟩ ⟨14, 2, 0, 238618, 368838, 933, 4096⟩
    (by decide) selected_cut_08517

theorem selected_cut_08518 : selected 7 ⟨238639, by decide⟩
    (prefixPartial 14 368839) = some ⟨14, 2, 0, 238639, 368839, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_368839_238639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368839 ⟨238639, by decide⟩ :=
  accepted_of_selected 14 368839 ⟨238639, by decide⟩ ⟨14, 2, 0, 238639, 368839, 1169, 4096⟩
    (by decide) selected_cut_08518

theorem unmarked_context_13_92209_238640 : frontier 8 ⟨238640, by decide⟩
    (prefixCache 13 92209) (prefixPartial 13 92209) = false := by
  decide +kernel

theorem node_context_13_92209_238640 : EJMOriginalGlobalDAGData.nodes 8 ⟨238640, by decide⟩ =
    .split (coordinate 13) (![⟨238571, by decide⟩,⟨238604, by decide⟩,⟨238618, by decide⟩,⟨238639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92209_238640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92209 ⟨238640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92209
    ⟨238640, by decide⟩ (by decide) (![⟨238571, by decide⟩,⟨238604, by decide⟩,⟨238618, by decide⟩,⟨238639, by decide⟩]) unmarked_context_13_92209_238640 node_context_13_92209_238640
  intro a
  fin_cases a
  · exact context_14_368836_238571
  · exact context_14_368837_238604
  · exact context_14_368838_238618
  · exact context_14_368839_238639

theorem selected_cut_08519 : selected 8 ⟨238681, by decide⟩
    (prefixPartial 13 92210) = some ⟨13, 2, 0, 238681, 92210, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_92210_238681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92210 ⟨238681, by decide⟩ :=
  accepted_of_selected 13 92210 ⟨238681, by decide⟩ ⟨13, 2, 0, 238681, 92210, 2505, 16384⟩
    (by decide) selected_cut_08519

theorem selected_cut_08520 : selected 8 ⟨238705, by decide⟩
    (prefixPartial 13 92211) = some ⟨13, 2, 0, 238705, 92211, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_92211_238705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92211 ⟨238705, by decide⟩ :=
  accepted_of_selected 13 92211 ⟨238705, by decide⟩ ⟨13, 2, 0, 238705, 92211, 1413, 16384⟩
    (by decide) selected_cut_08520

theorem unmarked_context_12_23052_238706 : frontier 9 ⟨238706, by decide⟩
    (prefixCache 12 23052) (prefixPartial 12 23052) = false := by
  decide +kernel

theorem node_context_12_23052_238706 : EJMOriginalGlobalDAGData.nodes 9 ⟨238706, by decide⟩ =
    .split (coordinate 12) (![⟨238539, by decide⟩,⟨238640, by decide⟩,⟨238681, by decide⟩,⟨238705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23052_238706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23052 ⟨238706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23052
    ⟨238706, by decide⟩ (by decide) (![⟨238539, by decide⟩,⟨238640, by decide⟩,⟨238681, by decide⟩,⟨238705, by decide⟩]) unmarked_context_12_23052_238706 node_context_12_23052_238706
  intro a
  fin_cases a
  · exact context_13_92208_238539
  · exact context_13_92209_238640
  · exact context_13_92210_238681
  · exact context_13_92211_238705

theorem selected_cut_08521 : selected 8 ⟨238773, by decide⟩
    (prefixPartial 13 92212) = some ⟨13, 2, 0, 238773, 92212, 3853, 16384⟩ := by
  decide +kernel

theorem context_13_92212_238773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92212 ⟨238773, by decide⟩ :=
  accepted_of_selected 13 92212 ⟨238773, by decide⟩ ⟨13, 2, 0, 238773, 92212, 3853, 16384⟩
    (by decide) selected_cut_08521

theorem selected_cut_08522 : selected 7 ⟨238798, by decide⟩
    (prefixPartial 14 368852) = some ⟨14, 2, 0, 238798, 368852, 1213, 4096⟩ := by
  decide +kernel

theorem context_14_368852_238798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368852 ⟨238798, by decide⟩ :=
  accepted_of_selected 14 368852 ⟨238798, by decide⟩ ⟨14, 2, 0, 238798, 368852, 1213, 4096⟩
    (by decide) selected_cut_08522

theorem selected_cut_08523 : selected 7 ⟨238827, by decide⟩
    (prefixPartial 14 368853) = some ⟨14, 2, 0, 238827, 368853, 1421, 4096⟩ := by
  decide +kernel

theorem context_14_368853_238827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368853 ⟨238827, by decide⟩ :=
  accepted_of_selected 14 368853 ⟨238827, by decide⟩ ⟨14, 2, 0, 238827, 368853, 1421, 4096⟩
    (by decide) selected_cut_08523

theorem selected_cut_08524 : selected 7 ⟨238839, by decide⟩
    (prefixPartial 14 368854) = some ⟨14, 2, 0, 238839, 368854, 873, 4096⟩ := by
  decide +kernel

theorem context_14_368854_238839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368854 ⟨238839, by decide⟩ :=
  accepted_of_selected 14 368854 ⟨238839, by decide⟩ ⟨14, 2, 0, 238839, 368854, 873, 4096⟩
    (by decide) selected_cut_08524

theorem selected_cut_08525 : selected 7 ⟨238851, by decide⟩
    (prefixPartial 14 368855) = some ⟨14, 2, 0, 238851, 368855, 949, 4096⟩ := by
  decide +kernel

theorem context_14_368855_238851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368855 ⟨238851, by decide⟩ :=
  accepted_of_selected 14 368855 ⟨238851, by decide⟩ ⟨14, 2, 0, 238851, 368855, 949, 4096⟩
    (by decide) selected_cut_08525

theorem unmarked_context_13_92213_238852 : frontier 8 ⟨238852, by decide⟩
    (prefixCache 13 92213) (prefixPartial 13 92213) = false := by
  decide +kernel

theorem node_context_13_92213_238852 : EJMOriginalGlobalDAGData.nodes 8 ⟨238852, by decide⟩ =
    .split (coordinate 13) (![⟨238798, by decide⟩,⟨238827, by decide⟩,⟨238839, by decide⟩,⟨238851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92213_238852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92213 ⟨238852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92213
    ⟨238852, by decide⟩ (by decide) (![⟨238798, by decide⟩,⟨238827, by decide⟩,⟨238839, by decide⟩,⟨238851, by decide⟩]) unmarked_context_13_92213_238852 node_context_13_92213_238852
  intro a
  fin_cases a
  · exact context_14_368852_238798
  · exact context_14_368853_238827
  · exact context_14_368854_238839
  · exact context_14_368855_238851

theorem selected_cut_08526 : selected 8 ⟨238883, by decide⟩
    (prefixPartial 13 92214) = some ⟨13, 2, 0, 238883, 92214, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_92214_238883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92214 ⟨238883, by decide⟩ :=
  accepted_of_selected 13 92214 ⟨238883, by decide⟩ ⟨13, 2, 0, 238883, 92214, 2165, 16384⟩
    (by decide) selected_cut_08526

theorem selected_cut_08527 : selected 8 ⟨238902, by decide⟩
    (prefixPartial 13 92215) = some ⟨13, 2, 0, 238902, 92215, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_92215_238902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92215 ⟨238902, by decide⟩ :=
  accepted_of_selected 13 92215 ⟨238902, by decide⟩ ⟨13, 2, 0, 238902, 92215, 1297, 16384⟩
    (by decide) selected_cut_08527

theorem unmarked_context_12_23053_238903 : frontier 9 ⟨238903, by decide⟩
    (prefixCache 12 23053) (prefixPartial 12 23053) = false := by
  decide +kernel

theorem node_context_12_23053_238903 : EJMOriginalGlobalDAGData.nodes 9 ⟨238903, by decide⟩ =
    .split (coordinate 12) (![⟨238773, by decide⟩,⟨238852, by decide⟩,⟨238883, by decide⟩,⟨238902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23053_238903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23053 ⟨238903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23053
    ⟨238903, by decide⟩ (by decide) (![⟨238773, by decide⟩,⟨238852, by decide⟩,⟨238883, by decide⟩,⟨238902, by decide⟩]) unmarked_context_12_23053_238903 node_context_12_23053_238903
  intro a
  fin_cases a
  · exact context_13_92212_238773
  · exact context_13_92213_238852
  · exact context_13_92214_238883
  · exact context_13_92215_238902

theorem selected_cut_08528 : selected 8 ⟨238969, by decide⟩
    (prefixPartial 13 92216) = some ⟨13, 2, 0, 238969, 92216, 3809, 16384⟩ := by
  decide +kernel

theorem context_13_92216_238969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92216 ⟨238969, by decide⟩ :=
  accepted_of_selected 13 92216 ⟨238969, by decide⟩ ⟨13, 2, 0, 238969, 92216, 3809, 16384⟩
    (by decide) selected_cut_08528

theorem selected_cut_08529 : selected 7 ⟨239002, by decide⟩
    (prefixPartial 14 368868) = some ⟨14, 2, 0, 239002, 368868, 1501, 4096⟩ := by
  decide +kernel

theorem context_14_368868_239002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368868 ⟨239002, by decide⟩ :=
  accepted_of_selected 14 368868 ⟨239002, by decide⟩ ⟨14, 2, 0, 239002, 368868, 1501, 4096⟩
    (by decide) selected_cut_08529

theorem selected_cut_08530 : selected 7 ⟨239038, by decide⟩
    (prefixPartial 14 368869) = some ⟨14, 2, 0, 239038, 368869, 1581, 4096⟩ := by
  decide +kernel

theorem context_14_368869_239038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368869 ⟨239038, by decide⟩ :=
  accepted_of_selected 14 368869 ⟨239038, by decide⟩ ⟨14, 2, 0, 239038, 368869, 1581, 4096⟩
    (by decide) selected_cut_08530

theorem selected_cut_08531 : selected 7 ⟨239057, by decide⟩
    (prefixPartial 14 368870) = some ⟨14, 2, 0, 239057, 368870, 1017, 4096⟩ := by
  decide +kernel

theorem context_14_368870_239057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368870 ⟨239057, by decide⟩ :=
  accepted_of_selected 14 368870 ⟨239057, by decide⟩ ⟨14, 2, 0, 239057, 368870, 1017, 4096⟩
    (by decide) selected_cut_08531

theorem selected_cut_08532 : selected 7 ⟨239071, by decide⟩
    (prefixPartial 14 368871) = some ⟨14, 2, 0, 239071, 368871, 997, 4096⟩ := by
  decide +kernel

theorem context_14_368871_239071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368871 ⟨239071, by decide⟩ :=
  accepted_of_selected 14 368871 ⟨239071, by decide⟩ ⟨14, 2, 0, 239071, 368871, 997, 4096⟩
    (by decide) selected_cut_08532

theorem unmarked_context_13_92217_239072 : frontier 8 ⟨239072, by decide⟩
    (prefixCache 13 92217) (prefixPartial 13 92217) = false := by
  decide +kernel

theorem node_context_13_92217_239072 : EJMOriginalGlobalDAGData.nodes 8 ⟨239072, by decide⟩ =
    .split (coordinate 13) (![⟨239002, by decide⟩,⟨239038, by decide⟩,⟨239057, by decide⟩,⟨239071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92217_239072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92217 ⟨239072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92217
    ⟨239072, by decide⟩ (by decide) (![⟨239002, by decide⟩,⟨239038, by decide⟩,⟨239057, by decide⟩,⟨239071, by decide⟩]) unmarked_context_13_92217_239072 node_context_13_92217_239072
  intro a
  fin_cases a
  · exact context_14_368868_239002
  · exact context_14_368869_239038
  · exact context_14_368870_239057
  · exact context_14_368871_239071

theorem selected_cut_08533 : selected 8 ⟨239112, by decide⟩
    (prefixPartial 13 92218) = some ⟨13, 2, 0, 239112, 92218, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_92218_239112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92218 ⟨239112, by decide⟩ :=
  accepted_of_selected 13 92218 ⟨239112, by decide⟩ ⟨13, 2, 0, 239112, 92218, 2493, 16384⟩
    (by decide) selected_cut_08533

theorem selected_cut_08534 : selected 8 ⟨239125, by decide⟩
    (prefixPartial 13 92219) = some ⟨13, 2, 0, 239125, 92219, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_92219_239125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92219 ⟨239125, by decide⟩ :=
  accepted_of_selected 13 92219 ⟨239125, by decide⟩ ⟨13, 2, 0, 239125, 92219, 1341, 16384⟩
    (by decide) selected_cut_08534

theorem unmarked_context_12_23054_239126 : frontier 9 ⟨239126, by decide⟩
    (prefixCache 12 23054) (prefixPartial 12 23054) = false := by
  decide +kernel

theorem node_context_12_23054_239126 : EJMOriginalGlobalDAGData.nodes 9 ⟨239126, by decide⟩ =
    .split (coordinate 12) (![⟨238969, by decide⟩,⟨239072, by decide⟩,⟨239112, by decide⟩,⟨239125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23054_239126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23054 ⟨239126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23054
    ⟨239126, by decide⟩ (by decide) (![⟨238969, by decide⟩,⟨239072, by decide⟩,⟨239112, by decide⟩,⟨239125, by decide⟩]) unmarked_context_12_23054_239126 node_context_12_23054_239126
  intro a
  fin_cases a
  · exact context_13_92216_238969
  · exact context_13_92217_239072
  · exact context_13_92218_239112
  · exact context_13_92219_239125

theorem selected_cut_08535 : selected 7 ⟨239131, by decide⟩
    (prefixPartial 14 368880) = some ⟨14, 2, 0, 239131, 368880, 165, 4096⟩ := by
  decide +kernel

theorem context_14_368880_239131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368880 ⟨239131, by decide⟩ :=
  accepted_of_selected 14 368880 ⟨239131, by decide⟩ ⟨14, 2, 0, 239131, 368880, 165, 4096⟩
    (by decide) selected_cut_08535

theorem selected_cut_08536 : selected 7 ⟨239161, by decide⟩
    (prefixPartial 14 368881) = some ⟨14, 2, 0, 239161, 368881, 1685, 4096⟩ := by
  decide +kernel

theorem context_14_368881_239161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368881 ⟨239161, by decide⟩ :=
  accepted_of_selected 14 368881 ⟨239161, by decide⟩ ⟨14, 2, 0, 239161, 368881, 1685, 4096⟩
    (by decide) selected_cut_08536

theorem selected_cut_08537 : selected 7 ⟨239183, by decide⟩
    (prefixPartial 14 368882) = some ⟨14, 2, 0, 239183, 368882, 1249, 4096⟩ := by
  decide +kernel

theorem context_14_368882_239183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368882 ⟨239183, by decide⟩ :=
  accepted_of_selected 14 368882 ⟨239183, by decide⟩ ⟨14, 2, 0, 239183, 368882, 1249, 4096⟩
    (by decide) selected_cut_08537

theorem selected_cut_08538 : selected 7 ⟨239208, by decide⟩
    (prefixPartial 14 368883) = some ⟨14, 2, 0, 239208, 368883, 1265, 4096⟩ := by
  decide +kernel

theorem context_14_368883_239208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368883 ⟨239208, by decide⟩ :=
  accepted_of_selected 14 368883 ⟨239208, by decide⟩ ⟨14, 2, 0, 239208, 368883, 1265, 4096⟩
    (by decide) selected_cut_08538

theorem unmarked_context_13_92220_239209 : frontier 8 ⟨239209, by decide⟩
    (prefixCache 13 92220) (prefixPartial 13 92220) = false := by
  decide +kernel

theorem node_context_13_92220_239209 : EJMOriginalGlobalDAGData.nodes 8 ⟨239209, by decide⟩ =
    .split (coordinate 13) (![⟨239131, by decide⟩,⟨239161, by decide⟩,⟨239183, by decide⟩,⟨239208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92220_239209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92220 ⟨239209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92220
    ⟨239209, by decide⟩ (by decide) (![⟨239131, by decide⟩,⟨239161, by decide⟩,⟨239183, by decide⟩,⟨239208, by decide⟩]) unmarked_context_13_92220_239209 node_context_13_92220_239209
  intro a
  fin_cases a
  · exact context_14_368880_239131
  · exact context_14_368881_239161
  · exact context_14_368882_239183
  · exact context_14_368883_239208

theorem selected_cut_08539 : selected 7 ⟨239242, by decide⟩
    (prefixPartial 14 368884) = some ⟨14, 2, 0, 239242, 368884, 1541, 4096⟩ := by
  decide +kernel

theorem context_14_368884_239242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368884 ⟨239242, by decide⟩ :=
  accepted_of_selected 14 368884 ⟨239242, by decide⟩ ⟨14, 2, 0, 239242, 368884, 1541, 4096⟩
    (by decide) selected_cut_08539

theorem selected_cut_08540 : selected 7 ⟨239274, by decide⟩
    (prefixPartial 14 368885) = some ⟨14, 2, 0, 239274, 368885, 1489, 4096⟩ := by
  decide +kernel

theorem context_14_368885_239274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368885 ⟨239274, by decide⟩ :=
  accepted_of_selected 14 368885 ⟨239274, by decide⟩ ⟨14, 2, 0, 239274, 368885, 1489, 4096⟩
    (by decide) selected_cut_08540

theorem selected_cut_08541 : selected 7 ⟨239290, by decide⟩
    (prefixPartial 14 368886) = some ⟨14, 2, 0, 239290, 368886, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_368886_239290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368886 ⟨239290, by decide⟩ :=
  accepted_of_selected 14 368886 ⟨239290, by decide⟩ ⟨14, 2, 0, 239290, 368886, 1021, 4096⟩
    (by decide) selected_cut_08541

theorem selected_cut_08542 : selected 7 ⟨239308, by decide⟩
    (prefixPartial 14 368887) = some ⟨14, 2, 0, 239308, 368887, 1033, 4096⟩ := by
  decide +kernel

theorem context_14_368887_239308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368887 ⟨239308, by decide⟩ :=
  accepted_of_selected 14 368887 ⟨239308, by decide⟩ ⟨14, 2, 0, 239308, 368887, 1033, 4096⟩
    (by decide) selected_cut_08542

theorem unmarked_context_13_92221_239309 : frontier 8 ⟨239309, by decide⟩
    (prefixCache 13 92221) (prefixPartial 13 92221) = false := by
  decide +kernel

theorem node_context_13_92221_239309 : EJMOriginalGlobalDAGData.nodes 8 ⟨239309, by decide⟩ =
    .split (coordinate 13) (![⟨239242, by decide⟩,⟨239274, by decide⟩,⟨239290, by decide⟩,⟨239308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92221_239309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92221 ⟨239309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92221
    ⟨239309, by decide⟩ (by decide) (![⟨239242, by decide⟩,⟨239274, by decide⟩,⟨239290, by decide⟩,⟨239308, by decide⟩]) unmarked_context_13_92221_239309 node_context_13_92221_239309
  intro a
  fin_cases a
  · exact context_14_368884_239242
  · exact context_14_368885_239274
  · exact context_14_368886_239290
  · exact context_14_368887_239308

theorem selected_cut_08543 : selected 8 ⟨239337, by decide⟩
    (prefixPartial 13 92222) = some ⟨13, 2, 0, 239337, 92222, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_92222_239337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92222 ⟨239337, by decide⟩ :=
  accepted_of_selected 13 92222 ⟨239337, by decide⟩ ⟨13, 2, 0, 239337, 92222, 2333, 16384⟩
    (by decide) selected_cut_08543

theorem selected_cut_08544 : selected 8 ⟨239352, by decide⟩
    (prefixPartial 13 92223) = some ⟨13, 2, 0, 239352, 92223, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_92223_239352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92223 ⟨239352, by decide⟩ :=
  accepted_of_selected 13 92223 ⟨239352, by decide⟩ ⟨13, 2, 0, 239352, 92223, 1357, 16384⟩
    (by decide) selected_cut_08544

theorem unmarked_context_12_23055_239353 : frontier 9 ⟨239353, by decide⟩
    (prefixCache 12 23055) (prefixPartial 12 23055) = false := by
  decide +kernel

theorem node_context_12_23055_239353 : EJMOriginalGlobalDAGData.nodes 9 ⟨239353, by decide⟩ =
    .split (coordinate 12) (![⟨239209, by decide⟩,⟨239309, by decide⟩,⟨239337, by decide⟩,⟨239352, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23055_239353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23055 ⟨239353, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23055
    ⟨239353, by decide⟩ (by decide) (![⟨239209, by decide⟩,⟨239309, by decide⟩,⟨239337, by decide⟩,⟨239352, by decide⟩]) unmarked_context_12_23055_239353 node_context_12_23055_239353
  intro a
  fin_cases a
  · exact context_13_92220_239209
  · exact context_13_92221_239309
  · exact context_13_92222_239337
  · exact context_13_92223_239352

theorem unmarked_context_11_5763_239354 : frontier 10 ⟨239354, by decide⟩
    (prefixCache 11 5763) (prefixPartial 11 5763) = false := by
  decide +kernel

theorem node_context_11_5763_239354 : EJMOriginalGlobalDAGData.nodes 10 ⟨239354, by decide⟩ =
    .split (coordinate 11) (![⟨238706, by decide⟩,⟨238903, by decide⟩,⟨239126, by decide⟩,⟨239353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5763_239354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5763 ⟨239354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5763
    ⟨239354, by decide⟩ (by decide) (![⟨238706, by decide⟩,⟨238903, by decide⟩,⟨239126, by decide⟩,⟨239353, by decide⟩]) unmarked_context_11_5763_239354 node_context_11_5763_239354
  intro a
  fin_cases a
  · exact context_12_23052_238706
  · exact context_12_23053_238903
  · exact context_12_23054_239126
  · exact context_12_23055_239353

theorem unmarked_context_10_1440_239355 : frontier 11 ⟨239355, by decide⟩
    (prefixCache 10 1440) (prefixPartial 10 1440) = false := by
  decide +kernel

theorem node_context_10_1440_239355 : EJMOriginalGlobalDAGData.nodes 11 ⟨239355, by decide⟩ =
    .split (coordinate 10) (![⟨236289, by decide⟩,⟨237371, by decide⟩,⟨238488, by decide⟩,⟨239354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1440_239355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1440 ⟨239355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1440
    ⟨239355, by decide⟩ (by decide) (![⟨236289, by decide⟩,⟨237371, by decide⟩,⟨238488, by decide⟩,⟨239354, by decide⟩]) unmarked_context_10_1440_239355 node_context_10_1440_239355
  intro a
  fin_cases a
  · exact context_11_5760_236289
  · exact context_11_5761_237371
  · exact context_11_5762_238488
  · exact context_11_5763_239354

theorem selected_cut_08545 : selected 8 ⟨239383, by decide⟩
    (prefixPartial 13 92224) = some ⟨13, 2, 0, 239383, 92224, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_92224_239383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92224 ⟨239383, by decide⟩ :=
  accepted_of_selected 13 92224 ⟨239383, by decide⟩ ⟨13, 2, 0, 239383, 92224, 2113, 16384⟩
    (by decide) selected_cut_08545

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
