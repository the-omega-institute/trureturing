/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover129
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_12482 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104708) = some ⟨13, 1, 0, 3444, 104708, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104708_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104708 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104708 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104708, 1, 16384⟩
    (by decide) selected_cut_12482

theorem selected_cut_12483 : selected 8 ⟨329718, by decide⟩
    (prefixPartial 13 104709) = some ⟨13, 2, 0, 329718, 104709, 4073, 16384⟩ := by
  decide +kernel

theorem context_13_104709_329718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104709 ⟨329718, by decide⟩ :=
  accepted_of_selected 13 104709 ⟨329718, by decide⟩ ⟨13, 2, 0, 329718, 104709, 4073, 16384⟩
    (by decide) selected_cut_12483

theorem selected_cut_12484 : selected 8 ⟨329752, by decide⟩
    (prefixPartial 13 104710) = some ⟨13, 2, 0, 329752, 104710, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_104710_329752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104710 ⟨329752, by decide⟩ :=
  accepted_of_selected 13 104710 ⟨329752, by decide⟩ ⟨13, 2, 0, 329752, 104710, 2373, 16384⟩
    (by decide) selected_cut_12484

theorem selected_cut_12485 : selected 8 ⟨329762, by decide⟩
    (prefixPartial 13 104711) = some ⟨13, 2, 0, 329762, 104711, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_104711_329762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104711 ⟨329762, by decide⟩ :=
  accepted_of_selected 13 104711 ⟨329762, by decide⟩ ⟨13, 2, 0, 329762, 104711, 1281, 16384⟩
    (by decide) selected_cut_12485

theorem unmarked_context_12_26177_329763 : frontier 9 ⟨329763, by decide⟩
    (prefixCache 12 26177) (prefixPartial 12 26177) = false := by
  decide +kernel

theorem node_context_12_26177_329763 : EJMOriginalGlobalDAGData.nodes 9 ⟨329763, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨329718, by decide⟩,⟨329752, by decide⟩,⟨329762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26177_329763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26177 ⟨329763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26177
    ⟨329763, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨329718, by decide⟩,⟨329752, by decide⟩,⟨329762, by decide⟩]) unmarked_context_12_26177_329763 node_context_12_26177_329763
  intro a
  fin_cases a
  · exact context_13_104708_3444
  · exact context_13_104709_329718
  · exact context_13_104710_329752
  · exact context_13_104711_329762

theorem selected_cut_12486 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104712) = some ⟨13, 1, 0, 3444, 104712, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104712_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104712 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104712 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104712, 1, 16384⟩
    (by decide) selected_cut_12486

theorem selected_cut_12487 : selected 8 ⟨329792, by decide⟩
    (prefixPartial 13 104713) = some ⟨13, 2, 0, 329792, 104713, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_104713_329792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104713 ⟨329792, by decide⟩ :=
  accepted_of_selected 13 104713 ⟨329792, by decide⟩ ⟨13, 2, 0, 329792, 104713, 2605, 16384⟩
    (by decide) selected_cut_12487

theorem selected_cut_12488 : selected 8 ⟨329808, by decide⟩
    (prefixPartial 13 104714) = some ⟨13, 2, 0, 329808, 104714, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_104714_329808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104714 ⟨329808, by decide⟩ :=
  accepted_of_selected 13 104714 ⟨329808, by decide⟩ ⟨13, 2, 0, 329808, 104714, 1317, 16384⟩
    (by decide) selected_cut_12488

theorem selected_cut_12489 : selected 8 ⟨329816, by decide⟩
    (prefixPartial 13 104715) = some ⟨13, 2, 0, 329816, 104715, 817, 16384⟩ := by
  decide +kernel

theorem context_13_104715_329816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104715 ⟨329816, by decide⟩ :=
  accepted_of_selected 13 104715 ⟨329816, by decide⟩ ⟨13, 2, 0, 329816, 104715, 817, 16384⟩
    (by decide) selected_cut_12489

theorem unmarked_context_12_26178_329817 : frontier 9 ⟨329817, by decide⟩
    (prefixCache 12 26178) (prefixPartial 12 26178) = false := by
  decide +kernel

theorem node_context_12_26178_329817 : EJMOriginalGlobalDAGData.nodes 9 ⟨329817, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨329792, by decide⟩,⟨329808, by decide⟩,⟨329816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26178_329817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26178 ⟨329817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26178
    ⟨329817, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨329792, by decide⟩,⟨329808, by decide⟩,⟨329816, by decide⟩]) unmarked_context_12_26178_329817 node_context_12_26178_329817
  intro a
  fin_cases a
  · exact context_13_104712_3444
  · exact context_13_104713_329792
  · exact context_13_104714_329808
  · exact context_13_104715_329816

theorem selected_cut_12490 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104716) = some ⟨13, 1, 0, 3444, 104716, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104716_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104716 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104716 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104716, 1, 16384⟩
    (by decide) selected_cut_12490

theorem selected_cut_12491 : selected 8 ⟨329868, by decide⟩
    (prefixPartial 13 104717) = some ⟨13, 2, 0, 329868, 104717, 3261, 16384⟩ := by
  decide +kernel

theorem context_13_104717_329868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104717 ⟨329868, by decide⟩ :=
  accepted_of_selected 13 104717 ⟨329868, by decide⟩ ⟨13, 2, 0, 329868, 104717, 3261, 16384⟩
    (by decide) selected_cut_12491

theorem selected_cut_12492 : selected 8 ⟨329888, by decide⟩
    (prefixPartial 13 104718) = some ⟨13, 2, 0, 329888, 104718, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_104718_329888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104718 ⟨329888, by decide⟩ :=
  accepted_of_selected 13 104718 ⟨329888, by decide⟩ ⟨13, 2, 0, 329888, 104718, 1745, 16384⟩
    (by decide) selected_cut_12492

theorem selected_cut_12493 : selected 8 ⟨329900, by decide⟩
    (prefixPartial 13 104719) = some ⟨13, 2, 0, 329900, 104719, 901, 16384⟩ := by
  decide +kernel

theorem context_13_104719_329900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104719 ⟨329900, by decide⟩ :=
  accepted_of_selected 13 104719 ⟨329900, by decide⟩ ⟨13, 2, 0, 329900, 104719, 901, 16384⟩
    (by decide) selected_cut_12493

theorem unmarked_context_12_26179_329901 : frontier 9 ⟨329901, by decide⟩
    (prefixCache 12 26179) (prefixPartial 12 26179) = false := by
  decide +kernel

theorem node_context_12_26179_329901 : EJMOriginalGlobalDAGData.nodes 9 ⟨329901, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨329868, by decide⟩,⟨329888, by decide⟩,⟨329900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26179_329901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26179 ⟨329901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26179
    ⟨329901, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨329868, by decide⟩,⟨329888, by decide⟩,⟨329900, by decide⟩]) unmarked_context_12_26179_329901 node_context_12_26179_329901
  intro a
  fin_cases a
  · exact context_13_104716_3444
  · exact context_13_104717_329868
  · exact context_13_104718_329888
  · exact context_13_104719_329900

theorem unmarked_context_11_6544_329902 : frontier 10 ⟨329902, by decide⟩
    (prefixCache 11 6544) (prefixPartial 11 6544) = false := by
  decide +kernel

theorem node_context_11_6544_329902 : EJMOriginalGlobalDAGData.nodes 10 ⟨329902, by decide⟩ =
    .split (coordinate 11) (![⟨329647, by decide⟩,⟨329763, by decide⟩,⟨329817, by decide⟩,⟨329901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6544_329902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6544 ⟨329902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6544
    ⟨329902, by decide⟩ (by decide) (![⟨329647, by decide⟩,⟨329763, by decide⟩,⟨329817, by decide⟩,⟨329901, by decide⟩]) unmarked_context_11_6544_329902 node_context_11_6544_329902
  intro a
  fin_cases a
  · exact context_12_26176_329647
  · exact context_12_26177_329763
  · exact context_12_26178_329817
  · exact context_12_26179_329901

theorem selected_cut_12494 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104720) = some ⟨13, 1, 0, 3444, 104720, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104720_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104720 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104720 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104720, 1, 16384⟩
    (by decide) selected_cut_12494

theorem selected_cut_12495 : selected 8 ⟨329930, by decide⟩
    (prefixPartial 13 104721) = some ⟨13, 2, 0, 329930, 104721, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_104721_329930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104721 ⟨329930, by decide⟩ :=
  accepted_of_selected 13 104721 ⟨329930, by decide⟩ ⟨13, 2, 0, 329930, 104721, 2397, 16384⟩
    (by decide) selected_cut_12495

theorem selected_cut_12496 : selected 8 ⟨329947, by decide⟩
    (prefixPartial 13 104722) = some ⟨13, 2, 0, 329947, 104722, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_104722_329947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104722 ⟨329947, by decide⟩ :=
  accepted_of_selected 13 104722 ⟨329947, by decide⟩ ⟨13, 2, 0, 329947, 104722, 1425, 16384⟩
    (by decide) selected_cut_12496

theorem selected_cut_12497 : selected 8 ⟨329954, by decide⟩
    (prefixPartial 13 104723) = some ⟨13, 2, 0, 329954, 104723, 801, 16384⟩ := by
  decide +kernel

theorem context_13_104723_329954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104723 ⟨329954, by decide⟩ :=
  accepted_of_selected 13 104723 ⟨329954, by decide⟩ ⟨13, 2, 0, 329954, 104723, 801, 16384⟩
    (by decide) selected_cut_12497

theorem unmarked_context_12_26180_329955 : frontier 9 ⟨329955, by decide⟩
    (prefixCache 12 26180) (prefixPartial 12 26180) = false := by
  decide +kernel

theorem node_context_12_26180_329955 : EJMOriginalGlobalDAGData.nodes 9 ⟨329955, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨329930, by decide⟩,⟨329947, by decide⟩,⟨329954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26180_329955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26180 ⟨329955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26180
    ⟨329955, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨329930, by decide⟩,⟨329947, by decide⟩,⟨329954, by decide⟩]) unmarked_context_12_26180_329955 node_context_12_26180_329955
  intro a
  fin_cases a
  · exact context_13_104720_3444
  · exact context_13_104721_329930
  · exact context_13_104722_329947
  · exact context_13_104723_329954

theorem selected_cut_12498 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104724) = some ⟨13, 1, 0, 3444, 104724, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104724_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104724 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104724 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104724, 1, 16384⟩
    (by decide) selected_cut_12498

theorem selected_cut_12499 : selected 8 ⟨330008, by decide⟩
    (prefixPartial 13 104725) = some ⟨13, 2, 0, 330008, 104725, 3481, 16384⟩ := by
  decide +kernel

theorem context_13_104725_330008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104725 ⟨330008, by decide⟩ :=
  accepted_of_selected 13 104725 ⟨330008, by decide⟩ ⟨13, 2, 0, 330008, 104725, 3481, 16384⟩
    (by decide) selected_cut_12499

theorem selected_cut_12500 : selected 8 ⟨330030, by decide⟩
    (prefixPartial 13 104726) = some ⟨13, 2, 0, 330030, 104726, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_104726_330030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104726 ⟨330030, by decide⟩ :=
  accepted_of_selected 13 104726 ⟨330030, by decide⟩ ⟨13, 2, 0, 330030, 104726, 2329, 16384⟩
    (by decide) selected_cut_12500

theorem selected_cut_12501 : selected 8 ⟨330042, by decide⟩
    (prefixPartial 13 104727) = some ⟨13, 2, 0, 330042, 104727, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_104727_330042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104727 ⟨330042, by decide⟩ :=
  accepted_of_selected 13 104727 ⟨330042, by decide⟩ ⟨13, 2, 0, 330042, 104727, 1269, 16384⟩
    (by decide) selected_cut_12501

theorem unmarked_context_12_26181_330043 : frontier 9 ⟨330043, by decide⟩
    (prefixCache 12 26181) (prefixPartial 12 26181) = false := by
  decide +kernel

theorem node_context_12_26181_330043 : EJMOriginalGlobalDAGData.nodes 9 ⟨330043, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨330008, by decide⟩,⟨330030, by decide⟩,⟨330042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26181_330043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26181 ⟨330043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26181
    ⟨330043, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨330008, by decide⟩,⟨330030, by decide⟩,⟨330042, by decide⟩]) unmarked_context_12_26181_330043 node_context_12_26181_330043
  intro a
  fin_cases a
  · exact context_13_104724_3444
  · exact context_13_104725_330008
  · exact context_13_104726_330030
  · exact context_13_104727_330042

theorem selected_cut_12502 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104728) = some ⟨13, 1, 0, 3444, 104728, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104728_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104728 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104728 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104728, 1, 16384⟩
    (by decide) selected_cut_12502

theorem selected_cut_12503 : selected 8 ⟨330076, by decide⟩
    (prefixPartial 13 104729) = some ⟨13, 2, 0, 330076, 104729, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_104729_330076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104729 ⟨330076, by decide⟩ :=
  accepted_of_selected 13 104729 ⟨330076, by decide⟩ ⟨13, 2, 0, 330076, 104729, 2277, 16384⟩
    (by decide) selected_cut_12503

theorem selected_cut_12504 : selected 8 ⟨330092, by decide⟩
    (prefixPartial 13 104730) = some ⟨13, 2, 0, 330092, 104730, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_104730_330092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104730 ⟨330092, by decide⟩ :=
  accepted_of_selected 13 104730 ⟨330092, by decide⟩ ⟨13, 2, 0, 330092, 104730, 1445, 16384⟩
    (by decide) selected_cut_12504

theorem selected_cut_12505 : selected 8 ⟨330102, by decide⟩
    (prefixPartial 13 104731) = some ⟨13, 2, 0, 330102, 104731, 865, 16384⟩ := by
  decide +kernel

theorem context_13_104731_330102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104731 ⟨330102, by decide⟩ :=
  accepted_of_selected 13 104731 ⟨330102, by decide⟩ ⟨13, 2, 0, 330102, 104731, 865, 16384⟩
    (by decide) selected_cut_12505

theorem unmarked_context_12_26182_330103 : frontier 9 ⟨330103, by decide⟩
    (prefixCache 12 26182) (prefixPartial 12 26182) = false := by
  decide +kernel

theorem node_context_12_26182_330103 : EJMOriginalGlobalDAGData.nodes 9 ⟨330103, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨330076, by decide⟩,⟨330092, by decide⟩,⟨330102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26182_330103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26182 ⟨330103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26182
    ⟨330103, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨330076, by decide⟩,⟨330092, by decide⟩,⟨330102, by decide⟩]) unmarked_context_12_26182_330103 node_context_12_26182_330103
  intro a
  fin_cases a
  · exact context_13_104728_3444
  · exact context_13_104729_330076
  · exact context_13_104730_330092
  · exact context_13_104731_330102

theorem selected_cut_12506 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104732) = some ⟨13, 1, 0, 3444, 104732, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104732_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104732 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104732 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104732, 1, 16384⟩
    (by decide) selected_cut_12506

theorem selected_cut_12507 : selected 8 ⟨330146, by decide⟩
    (prefixPartial 13 104733) = some ⟨13, 2, 0, 330146, 104733, 2737, 16384⟩ := by
  decide +kernel

theorem context_13_104733_330146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104733 ⟨330146, by decide⟩ :=
  accepted_of_selected 13 104733 ⟨330146, by decide⟩ ⟨13, 2, 0, 330146, 104733, 2737, 16384⟩
    (by decide) selected_cut_12507

theorem selected_cut_12508 : selected 8 ⟨330166, by decide⟩
    (prefixPartial 13 104734) = some ⟨13, 2, 0, 330166, 104734, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_104734_330166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104734 ⟨330166, by decide⟩ :=
  accepted_of_selected 13 104734 ⟨330166, by decide⟩ ⟨13, 2, 0, 330166, 104734, 1685, 16384⟩
    (by decide) selected_cut_12508

theorem selected_cut_12509 : selected 8 ⟨330177, by decide⟩
    (prefixPartial 13 104735) = some ⟨13, 2, 0, 330177, 104735, 893, 16384⟩ := by
  decide +kernel

theorem context_13_104735_330177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104735 ⟨330177, by decide⟩ :=
  accepted_of_selected 13 104735 ⟨330177, by decide⟩ ⟨13, 2, 0, 330177, 104735, 893, 16384⟩
    (by decide) selected_cut_12509

theorem unmarked_context_12_26183_330178 : frontier 9 ⟨330178, by decide⟩
    (prefixCache 12 26183) (prefixPartial 12 26183) = false := by
  decide +kernel

theorem node_context_12_26183_330178 : EJMOriginalGlobalDAGData.nodes 9 ⟨330178, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨330146, by decide⟩,⟨330166, by decide⟩,⟨330177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26183_330178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26183 ⟨330178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26183
    ⟨330178, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨330146, by decide⟩,⟨330166, by decide⟩,⟨330177, by decide⟩]) unmarked_context_12_26183_330178 node_context_12_26183_330178
  intro a
  fin_cases a
  · exact context_13_104732_3444
  · exact context_13_104733_330146
  · exact context_13_104734_330166
  · exact context_13_104735_330177

theorem unmarked_context_11_6545_330179 : frontier 10 ⟨330179, by decide⟩
    (prefixCache 11 6545) (prefixPartial 11 6545) = false := by
  decide +kernel

theorem node_context_11_6545_330179 : EJMOriginalGlobalDAGData.nodes 10 ⟨330179, by decide⟩ =
    .split (coordinate 11) (![⟨329955, by decide⟩,⟨330043, by decide⟩,⟨330103, by decide⟩,⟨330178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6545_330179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6545 ⟨330179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6545
    ⟨330179, by decide⟩ (by decide) (![⟨329955, by decide⟩,⟨330043, by decide⟩,⟨330103, by decide⟩,⟨330178, by decide⟩]) unmarked_context_11_6545_330179 node_context_11_6545_330179
  intro a
  fin_cases a
  · exact context_12_26180_329955
  · exact context_12_26181_330043
  · exact context_12_26182_330103
  · exact context_12_26183_330178

theorem selected_cut_12510 : selected 9 ⟨330243, by decide⟩
    (prefixPartial 12 26184) = some ⟨12, 2, 0, 330243, 26184, 4009, 65536⟩ := by
  decide +kernel

theorem context_12_26184_330243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26184 ⟨330243, by decide⟩ :=
  accepted_of_selected 12 26184 ⟨330243, by decide⟩ ⟨12, 2, 0, 330243, 26184, 4009, 65536⟩
    (by decide) selected_cut_12510

theorem selected_cut_12511 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104740) = some ⟨13, 1, 0, 3444, 104740, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104740_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104740 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104740 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104740, 1, 16384⟩
    (by decide) selected_cut_12511

theorem selected_cut_12512 : selected 8 ⟨330303, by decide⟩
    (prefixPartial 13 104741) = some ⟨13, 2, 0, 330303, 104741, 3333, 16384⟩ := by
  decide +kernel

theorem context_13_104741_330303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104741 ⟨330303, by decide⟩ :=
  accepted_of_selected 13 104741 ⟨330303, by decide⟩ ⟨13, 2, 0, 330303, 104741, 3333, 16384⟩
    (by decide) selected_cut_12512

theorem selected_cut_12513 : selected 8 ⟨330327, by decide⟩
    (prefixPartial 13 104742) = some ⟨13, 2, 0, 330327, 104742, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_104742_330327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104742 ⟨330327, by decide⟩ :=
  accepted_of_selected 13 104742 ⟨330327, by decide⟩ ⟨13, 2, 0, 330327, 104742, 2185, 16384⟩
    (by decide) selected_cut_12513

theorem selected_cut_12514 : selected 8 ⟨330344, by decide⟩
    (prefixPartial 13 104743) = some ⟨13, 2, 0, 330344, 104743, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_104743_330344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104743 ⟨330344, by decide⟩ :=
  accepted_of_selected 13 104743 ⟨330344, by decide⟩ ⟨13, 2, 0, 330344, 104743, 1377, 16384⟩
    (by decide) selected_cut_12514

theorem unmarked_context_12_26185_330345 : frontier 9 ⟨330345, by decide⟩
    (prefixCache 12 26185) (prefixPartial 12 26185) = false := by
  decide +kernel

theorem node_context_12_26185_330345 : EJMOriginalGlobalDAGData.nodes 9 ⟨330345, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨330303, by decide⟩,⟨330327, by decide⟩,⟨330344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26185_330345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26185 ⟨330345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26185
    ⟨330345, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨330303, by decide⟩,⟨330327, by decide⟩,⟨330344, by decide⟩]) unmarked_context_12_26185_330345 node_context_12_26185_330345
  intro a
  fin_cases a
  · exact context_13_104740_3444
  · exact context_13_104741_330303
  · exact context_13_104742_330327
  · exact context_13_104743_330344

theorem selected_cut_12515 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104744) = some ⟨13, 1, 0, 3444, 104744, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104744_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104744 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104744 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104744, 1, 16384⟩
    (by decide) selected_cut_12515

theorem selected_cut_12516 : selected 8 ⟨330410, by decide⟩
    (prefixPartial 13 104745) = some ⟨13, 2, 0, 330410, 104745, 3545, 16384⟩ := by
  decide +kernel

theorem context_13_104745_330410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104745 ⟨330410, by decide⟩ :=
  accepted_of_selected 13 104745 ⟨330410, by decide⟩ ⟨13, 2, 0, 330410, 104745, 3545, 16384⟩
    (by decide) selected_cut_12516

theorem selected_cut_12517 : selected 8 ⟨330429, by decide⟩
    (prefixPartial 13 104746) = some ⟨13, 2, 0, 330429, 104746, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_104746_330429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104746 ⟨330429, by decide⟩ :=
  accepted_of_selected 13 104746 ⟨330429, by decide⟩ ⟨13, 2, 0, 330429, 104746, 2293, 16384⟩
    (by decide) selected_cut_12517

theorem selected_cut_12518 : selected 8 ⟨330435, by decide⟩
    (prefixPartial 13 104747) = some ⟨13, 2, 0, 330435, 104747, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_104747_330435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104747 ⟨330435, by decide⟩ :=
  accepted_of_selected 13 104747 ⟨330435, by decide⟩ ⟨13, 2, 0, 330435, 104747, 1245, 16384⟩
    (by decide) selected_cut_12518

theorem unmarked_context_12_26186_330436 : frontier 9 ⟨330436, by decide⟩
    (prefixCache 12 26186) (prefixPartial 12 26186) = false := by
  decide +kernel

theorem node_context_12_26186_330436 : EJMOriginalGlobalDAGData.nodes 9 ⟨330436, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨330410, by decide⟩,⟨330429, by decide⟩,⟨330435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26186_330436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26186 ⟨330436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26186
    ⟨330436, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨330410, by decide⟩,⟨330429, by decide⟩,⟨330435, by decide⟩]) unmarked_context_12_26186_330436 node_context_12_26186_330436
  intro a
  fin_cases a
  · exact context_13_104744_3444
  · exact context_13_104745_330410
  · exact context_13_104746_330429
  · exact context_13_104747_330435

theorem selected_cut_12519 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104748) = some ⟨13, 1, 0, 3444, 104748, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104748_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104748 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104748 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104748, 1, 16384⟩
    (by decide) selected_cut_12519

theorem selected_cut_12520 : selected 8 ⟨330480, by decide⟩
    (prefixPartial 13 104749) = some ⟨13, 2, 0, 330480, 104749, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_104749_330480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104749 ⟨330480, by decide⟩ :=
  accepted_of_selected 13 104749 ⟨330480, by decide⟩ ⟨13, 2, 0, 330480, 104749, 2573, 16384⟩
    (by decide) selected_cut_12520

theorem selected_cut_12521 : selected 8 ⟨330498, by decide⟩
    (prefixPartial 13 104750) = some ⟨13, 2, 0, 330498, 104750, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_104750_330498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104750 ⟨330498, by decide⟩ :=
  accepted_of_selected 13 104750 ⟨330498, by decide⟩ ⟨13, 2, 0, 330498, 104750, 1433, 16384⟩
    (by decide) selected_cut_12521

theorem selected_cut_12522 : selected 8 ⟨330509, by decide⟩
    (prefixPartial 13 104751) = some ⟨13, 2, 0, 330509, 104751, 861, 16384⟩ := by
  decide +kernel

theorem context_13_104751_330509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104751 ⟨330509, by decide⟩ :=
  accepted_of_selected 13 104751 ⟨330509, by decide⟩ ⟨13, 2, 0, 330509, 104751, 861, 16384⟩
    (by decide) selected_cut_12522

theorem unmarked_context_12_26187_330510 : frontier 9 ⟨330510, by decide⟩
    (prefixCache 12 26187) (prefixPartial 12 26187) = false := by
  decide +kernel

theorem node_context_12_26187_330510 : EJMOriginalGlobalDAGData.nodes 9 ⟨330510, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨330480, by decide⟩,⟨330498, by decide⟩,⟨330509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26187_330510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26187 ⟨330510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26187
    ⟨330510, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨330480, by decide⟩,⟨330498, by decide⟩,⟨330509, by decide⟩]) unmarked_context_12_26187_330510 node_context_12_26187_330510
  intro a
  fin_cases a
  · exact context_13_104748_3444
  · exact context_13_104749_330480
  · exact context_13_104750_330498
  · exact context_13_104751_330509

theorem unmarked_context_11_6546_330511 : frontier 10 ⟨330511, by decide⟩
    (prefixCache 11 6546) (prefixPartial 11 6546) = false := by
  decide +kernel

theorem node_context_11_6546_330511 : EJMOriginalGlobalDAGData.nodes 10 ⟨330511, by decide⟩ =
    .split (coordinate 11) (![⟨330243, by decide⟩,⟨330345, by decide⟩,⟨330436, by decide⟩,⟨330510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6546_330511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6546 ⟨330511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6546
    ⟨330511, by decide⟩ (by decide) (![⟨330243, by decide⟩,⟨330345, by decide⟩,⟨330436, by decide⟩,⟨330510, by decide⟩]) unmarked_context_11_6546_330511 node_context_11_6546_330511
  intro a
  fin_cases a
  · exact context_12_26184_330243
  · exact context_12_26185_330345
  · exact context_12_26186_330436
  · exact context_12_26187_330510

theorem selected_cut_12523 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104752) = some ⟨13, 1, 0, 3444, 104752, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104752_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104752 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104752 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104752, 1, 16384⟩
    (by decide) selected_cut_12523

theorem selected_cut_12524 : selected 8 ⟨330538, by decide⟩
    (prefixPartial 13 104753) = some ⟨13, 2, 0, 330538, 104753, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_104753_330538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104753 ⟨330538, by decide⟩ :=
  accepted_of_selected 13 104753 ⟨330538, by decide⟩ ⟨13, 2, 0, 330538, 104753, 1889, 16384⟩
    (by decide) selected_cut_12524

theorem selected_cut_12525 : selected 8 ⟨330558, by decide⟩
    (prefixPartial 13 104754) = some ⟨13, 2, 0, 330558, 104754, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_104754_330558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104754 ⟨330558, by decide⟩ :=
  accepted_of_selected 13 104754 ⟨330558, by decide⟩ ⟨13, 2, 0, 330558, 104754, 1465, 16384⟩
    (by decide) selected_cut_12525

theorem selected_cut_12526 : selected 8 ⟨330566, by decide⟩
    (prefixPartial 13 104755) = some ⟨13, 2, 0, 330566, 104755, 913, 16384⟩ := by
  decide +kernel

theorem context_13_104755_330566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104755 ⟨330566, by decide⟩ :=
  accepted_of_selected 13 104755 ⟨330566, by decide⟩ ⟨13, 2, 0, 330566, 104755, 913, 16384⟩
    (by decide) selected_cut_12526

theorem unmarked_context_12_26188_330567 : frontier 9 ⟨330567, by decide⟩
    (prefixCache 12 26188) (prefixPartial 12 26188) = false := by
  decide +kernel

theorem node_context_12_26188_330567 : EJMOriginalGlobalDAGData.nodes 9 ⟨330567, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨330538, by decide⟩,⟨330558, by decide⟩,⟨330566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26188_330567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26188 ⟨330567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26188
    ⟨330567, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨330538, by decide⟩,⟨330558, by decide⟩,⟨330566, by decide⟩]) unmarked_context_12_26188_330567 node_context_12_26188_330567
  intro a
  fin_cases a
  · exact context_13_104752_3444
  · exact context_13_104753_330538
  · exact context_13_104754_330558
  · exact context_13_104755_330566

theorem selected_cut_12527 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104756) = some ⟨13, 1, 0, 3444, 104756, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104756_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104756 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104756 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104756, 1, 16384⟩
    (by decide) selected_cut_12527

theorem selected_cut_12528 : selected 8 ⟨330625, by decide⟩
    (prefixPartial 13 104757) = some ⟨13, 2, 0, 330625, 104757, 3205, 16384⟩ := by
  decide +kernel

theorem context_13_104757_330625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104757 ⟨330625, by decide⟩ :=
  accepted_of_selected 13 104757 ⟨330625, by decide⟩ ⟨13, 2, 0, 330625, 104757, 3205, 16384⟩
    (by decide) selected_cut_12528

theorem selected_cut_12529 : selected 8 ⟨330663, by decide⟩
    (prefixPartial 13 104758) = some ⟨13, 2, 0, 330663, 104758, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_104758_330663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104758 ⟨330663, by decide⟩ :=
  accepted_of_selected 13 104758 ⟨330663, by decide⟩ ⟨13, 2, 0, 330663, 104758, 2461, 16384⟩
    (by decide) selected_cut_12529

theorem selected_cut_12530 : selected 8 ⟨330674, by decide⟩
    (prefixPartial 13 104759) = some ⟨13, 2, 0, 330674, 104759, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_104759_330674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104759 ⟨330674, by decide⟩ :=
  accepted_of_selected 13 104759 ⟨330674, by decide⟩ ⟨13, 2, 0, 330674, 104759, 1309, 16384⟩
    (by decide) selected_cut_12530

theorem unmarked_context_12_26189_330675 : frontier 9 ⟨330675, by decide⟩
    (prefixCache 12 26189) (prefixPartial 12 26189) = false := by
  decide +kernel

theorem node_context_12_26189_330675 : EJMOriginalGlobalDAGData.nodes 9 ⟨330675, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨330625, by decide⟩,⟨330663, by decide⟩,⟨330674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26189_330675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26189 ⟨330675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26189
    ⟨330675, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨330625, by decide⟩,⟨330663, by decide⟩,⟨330674, by decide⟩]) unmarked_context_12_26189_330675 node_context_12_26189_330675
  intro a
  fin_cases a
  · exact context_13_104756_3444
  · exact context_13_104757_330625
  · exact context_13_104758_330663
  · exact context_13_104759_330674

theorem selected_cut_12531 : selected 9 ⟨330738, by decide⟩
    (prefixPartial 12 26190) = some ⟨12, 2, 0, 330738, 26190, 3997, 65536⟩ := by
  decide +kernel

theorem context_12_26190_330738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26190 ⟨330738, by decide⟩ :=
  accepted_of_selected 12 26190 ⟨330738, by decide⟩ ⟨12, 2, 0, 330738, 26190, 3997, 65536⟩
    (by decide) selected_cut_12531

theorem selected_cut_12532 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104764) = some ⟨13, 1, 0, 3444, 104764, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104764_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104764 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104764 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104764, 1, 16384⟩
    (by decide) selected_cut_12532

theorem selected_cut_12533 : selected 8 ⟨330772, by decide⟩
    (prefixPartial 13 104765) = some ⟨13, 2, 0, 330772, 104765, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_104765_330772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104765 ⟨330772, by decide⟩ :=
  accepted_of_selected 13 104765 ⟨330772, by decide⟩ ⟨13, 2, 0, 330772, 104765, 2217, 16384⟩
    (by decide) selected_cut_12533

theorem selected_cut_12534 : selected 8 ⟨330792, by decide⟩
    (prefixPartial 13 104766) = some ⟨13, 2, 0, 330792, 104766, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_104766_330792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104766 ⟨330792, by decide⟩ :=
  accepted_of_selected 13 104766 ⟨330792, by decide⟩ ⟨13, 2, 0, 330792, 104766, 1665, 16384⟩
    (by decide) selected_cut_12534

theorem selected_cut_12535 : selected 8 ⟨330800, by decide⟩
    (prefixPartial 13 104767) = some ⟨13, 2, 0, 330800, 104767, 861, 16384⟩ := by
  decide +kernel

theorem context_13_104767_330800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104767 ⟨330800, by decide⟩ :=
  accepted_of_selected 13 104767 ⟨330800, by decide⟩ ⟨13, 2, 0, 330800, 104767, 861, 16384⟩
    (by decide) selected_cut_12535

theorem unmarked_context_12_26191_330801 : frontier 9 ⟨330801, by decide⟩
    (prefixCache 12 26191) (prefixPartial 12 26191) = false := by
  decide +kernel

theorem node_context_12_26191_330801 : EJMOriginalGlobalDAGData.nodes 9 ⟨330801, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨330772, by decide⟩,⟨330792, by decide⟩,⟨330800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26191_330801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26191 ⟨330801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26191
    ⟨330801, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨330772, by decide⟩,⟨330792, by decide⟩,⟨330800, by decide⟩]) unmarked_context_12_26191_330801 node_context_12_26191_330801
  intro a
  fin_cases a
  · exact context_13_104764_3444
  · exact context_13_104765_330772
  · exact context_13_104766_330792
  · exact context_13_104767_330800

theorem unmarked_context_11_6547_330802 : frontier 10 ⟨330802, by decide⟩
    (prefixCache 11 6547) (prefixPartial 11 6547) = false := by
  decide +kernel

theorem node_context_11_6547_330802 : EJMOriginalGlobalDAGData.nodes 10 ⟨330802, by decide⟩ =
    .split (coordinate 11) (![⟨330567, by decide⟩,⟨330675, by decide⟩,⟨330738, by decide⟩,⟨330801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6547_330802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6547 ⟨330802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6547
    ⟨330802, by decide⟩ (by decide) (![⟨330567, by decide⟩,⟨330675, by decide⟩,⟨330738, by decide⟩,⟨330801, by decide⟩]) unmarked_context_11_6547_330802 node_context_11_6547_330802
  intro a
  fin_cases a
  · exact context_12_26188_330567
  · exact context_12_26189_330675
  · exact context_12_26190_330738
  · exact context_12_26191_330801

theorem unmarked_context_10_1636_330803 : frontier 11 ⟨330803, by decide⟩
    (prefixCache 10 1636) (prefixPartial 10 1636) = false := by
  decide +kernel

theorem node_context_10_1636_330803 : EJMOriginalGlobalDAGData.nodes 11 ⟨330803, by decide⟩ =
    .split (coordinate 10) (![⟨329902, by decide⟩,⟨330179, by decide⟩,⟨330511, by decide⟩,⟨330802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1636_330803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1636 ⟨330803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1636
    ⟨330803, by decide⟩ (by decide) (![⟨329902, by decide⟩,⟨330179, by decide⟩,⟨330511, by decide⟩,⟨330802, by decide⟩]) unmarked_context_10_1636_330803 node_context_10_1636_330803
  intro a
  fin_cases a
  · exact context_11_6544_329902
  · exact context_11_6545_330179
  · exact context_11_6546_330511
  · exact context_11_6547_330802

theorem selected_cut_12536 : selected 9 ⟨330843, by decide⟩
    (prefixPartial 12 26192) = some ⟨12, 2, 0, 330843, 26192, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_26192_330843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26192 ⟨330843, by decide⟩ :=
  accepted_of_selected 12 26192 ⟨330843, by decide⟩ ⟨12, 2, 0, 330843, 26192, 3597, 65536⟩
    (by decide) selected_cut_12536

theorem selected_cut_12537 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 26193) = some ⟨12, 1, 0, 170504, 26193, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26193_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26193 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 26193 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 26193, 1, 65536⟩
    (by decide) selected_cut_12537

theorem selected_cut_12538 : selected 9 ⟨330883, by decide⟩
    (prefixPartial 12 26194) = some ⟨12, 2, 0, 330883, 26194, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_26194_330883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26194 ⟨330883, by decide⟩ :=
  accepted_of_selected 12 26194 ⟨330883, by decide⟩ ⟨12, 2, 0, 330883, 26194, 3761, 65536⟩
    (by decide) selected_cut_12538

theorem selected_cut_12539 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104780) = some ⟨13, 1, 0, 3444, 104780, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104780_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104780 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104780 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104780, 1, 16384⟩
    (by decide) selected_cut_12539

theorem selected_cut_12540 : selected 8 ⟨330912, by decide⟩
    (prefixPartial 13 104781) = some ⟨13, 2, 0, 330912, 104781, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_104781_330912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104781 ⟨330912, by decide⟩ :=
  accepted_of_selected 13 104781 ⟨330912, by decide⟩ ⟨13, 2, 0, 330912, 104781, 2145, 16384⟩
    (by decide) selected_cut_12540

theorem selected_cut_12541 : selected 8 ⟨330937, by decide⟩
    (prefixPartial 13 104782) = some ⟨13, 2, 0, 330937, 104782, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_104782_330937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104782 ⟨330937, by decide⟩ :=
  accepted_of_selected 13 104782 ⟨330937, by decide⟩ ⟨13, 2, 0, 330937, 104782, 1865, 16384⟩
    (by decide) selected_cut_12541

theorem selected_cut_12542 : selected 8 ⟨330944, by decide⟩
    (prefixPartial 13 104783) = some ⟨13, 2, 0, 330944, 104783, 909, 16384⟩ := by
  decide +kernel

theorem context_13_104783_330944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104783 ⟨330944, by decide⟩ :=
  accepted_of_selected 13 104783 ⟨330944, by decide⟩ ⟨13, 2, 0, 330944, 104783, 909, 16384⟩
    (by decide) selected_cut_12542

theorem unmarked_context_12_26195_330945 : frontier 9 ⟨330945, by decide⟩
    (prefixCache 12 26195) (prefixPartial 12 26195) = false := by
  decide +kernel

theorem node_context_12_26195_330945 : EJMOriginalGlobalDAGData.nodes 9 ⟨330945, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨330912, by decide⟩,⟨330937, by decide⟩,⟨330944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26195_330945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26195 ⟨330945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26195
    ⟨330945, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨330912, by decide⟩,⟨330937, by decide⟩,⟨330944, by decide⟩]) unmarked_context_12_26195_330945 node_context_12_26195_330945
  intro a
  fin_cases a
  · exact context_13_104780_3444
  · exact context_13_104781_330912
  · exact context_13_104782_330937
  · exact context_13_104783_330944

theorem unmarked_context_11_6548_330946 : frontier 10 ⟨330946, by decide⟩
    (prefixCache 11 6548) (prefixPartial 11 6548) = false := by
  decide +kernel

theorem node_context_11_6548_330946 : EJMOriginalGlobalDAGData.nodes 10 ⟨330946, by decide⟩ =
    .split (coordinate 11) (![⟨330843, by decide⟩,⟨170504, by decide⟩,⟨330883, by decide⟩,⟨330945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6548_330946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6548 ⟨330946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6548
    ⟨330946, by decide⟩ (by decide) (![⟨330843, by decide⟩,⟨170504, by decide⟩,⟨330883, by decide⟩,⟨330945, by decide⟩]) unmarked_context_11_6548_330946 node_context_11_6548_330946
  intro a
  fin_cases a
  · exact context_12_26192_330843
  · exact context_12_26193_170504
  · exact context_12_26194_330883
  · exact context_12_26195_330945

theorem selected_cut_12543 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 26196) = some ⟨12, 1, 0, 308705, 26196, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26196_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26196 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 26196 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 26196, 1, 65536⟩
    (by decide) selected_cut_12543

theorem selected_cut_12544 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 26197) = some ⟨12, 1, 0, 170504, 26197, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26197_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26197 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 26197 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 26197, 1, 65536⟩
    (by decide) selected_cut_12544

theorem selected_cut_12545 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104792) = some ⟨13, 1, 0, 3444, 104792, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104792_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104792 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104792 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104792, 1, 16384⟩
    (by decide) selected_cut_12545

theorem selected_cut_12546 : selected 8 ⟨330993, by decide⟩
    (prefixPartial 13 104793) = some ⟨13, 2, 0, 330993, 104793, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_104793_330993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104793 ⟨330993, by decide⟩ :=
  accepted_of_selected 13 104793 ⟨330993, by decide⟩ ⟨13, 2, 0, 330993, 104793, 2533, 16384⟩
    (by decide) selected_cut_12546

theorem selected_cut_12547 : selected 8 ⟨331011, by decide⟩
    (prefixPartial 13 104794) = some ⟨13, 2, 0, 331011, 104794, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_104794_331011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104794 ⟨331011, by decide⟩ :=
  accepted_of_selected 13 104794 ⟨331011, by decide⟩ ⟨13, 2, 0, 331011, 104794, 2061, 16384⟩
    (by decide) selected_cut_12547

theorem selected_cut_12548 : selected 8 ⟨331018, by decide⟩
    (prefixPartial 13 104795) = some ⟨13, 2, 0, 331018, 104795, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_104795_331018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104795 ⟨331018, by decide⟩ :=
  accepted_of_selected 13 104795 ⟨331018, by decide⟩ ⟨13, 2, 0, 331018, 104795, 1161, 16384⟩
    (by decide) selected_cut_12548

theorem unmarked_context_12_26198_331019 : frontier 9 ⟨331019, by decide⟩
    (prefixCache 12 26198) (prefixPartial 12 26198) = false := by
  decide +kernel

theorem node_context_12_26198_331019 : EJMOriginalGlobalDAGData.nodes 9 ⟨331019, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨330993, by decide⟩,⟨331011, by decide⟩,⟨331018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26198_331019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26198 ⟨331019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26198
    ⟨331019, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨330993, by decide⟩,⟨331011, by decide⟩,⟨331018, by decide⟩]) unmarked_context_12_26198_331019 node_context_12_26198_331019
  intro a
  fin_cases a
  · exact context_13_104792_3444
  · exact context_13_104793_330993
  · exact context_13_104794_331011
  · exact context_13_104795_331018

theorem selected_cut_12549 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104796) = some ⟨13, 1, 0, 3444, 104796, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104796_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104796 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104796 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104796, 1, 16384⟩
    (by decide) selected_cut_12549

theorem selected_cut_12550 : selected 8 ⟨331081, by decide⟩
    (prefixPartial 13 104797) = some ⟨13, 2, 0, 331081, 104797, 3157, 16384⟩ := by
  decide +kernel

theorem context_13_104797_331081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104797 ⟨331081, by decide⟩ :=
  accepted_of_selected 13 104797 ⟨331081, by decide⟩ ⟨13, 2, 0, 331081, 104797, 3157, 16384⟩
    (by decide) selected_cut_12550

theorem selected_cut_12551 : selected 8 ⟨331111, by decide⟩
    (prefixPartial 13 104798) = some ⟨13, 2, 0, 331111, 104798, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_104798_331111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104798 ⟨331111, by decide⟩ :=
  accepted_of_selected 13 104798 ⟨331111, by decide⟩ ⟨13, 2, 0, 331111, 104798, 2505, 16384⟩
    (by decide) selected_cut_12551

theorem selected_cut_12552 : selected 8 ⟨331122, by decide⟩
    (prefixPartial 13 104799) = some ⟨13, 2, 0, 331122, 104799, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_104799_331122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104799 ⟨331122, by decide⟩ :=
  accepted_of_selected 13 104799 ⟨331122, by decide⟩ ⟨13, 2, 0, 331122, 104799, 1285, 16384⟩
    (by decide) selected_cut_12552

theorem unmarked_context_12_26199_331123 : frontier 9 ⟨331123, by decide⟩
    (prefixCache 12 26199) (prefixPartial 12 26199) = false := by
  decide +kernel

theorem node_context_12_26199_331123 : EJMOriginalGlobalDAGData.nodes 9 ⟨331123, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨331081, by decide⟩,⟨331111, by decide⟩,⟨331122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26199_331123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26199 ⟨331123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26199
    ⟨331123, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨331081, by decide⟩,⟨331111, by decide⟩,⟨331122, by decide⟩]) unmarked_context_12_26199_331123 node_context_12_26199_331123
  intro a
  fin_cases a
  · exact context_13_104796_3444
  · exact context_13_104797_331081
  · exact context_13_104798_331111
  · exact context_13_104799_331122

theorem unmarked_context_11_6549_331124 : frontier 10 ⟨331124, by decide⟩
    (prefixCache 11 6549) (prefixPartial 11 6549) = false := by
  decide +kernel

theorem node_context_11_6549_331124 : EJMOriginalGlobalDAGData.nodes 10 ⟨331124, by decide⟩ =
    .split (coordinate 11) (![⟨308705, by decide⟩,⟨170504, by decide⟩,⟨331019, by decide⟩,⟨331123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6549_331124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6549 ⟨331124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6549
    ⟨331124, by decide⟩ (by decide) (![⟨308705, by decide⟩,⟨170504, by decide⟩,⟨331019, by decide⟩,⟨331123, by decide⟩]) unmarked_context_11_6549_331124 node_context_11_6549_331124
  intro a
  fin_cases a
  · exact context_12_26196_308705
  · exact context_12_26197_170504
  · exact context_12_26198_331019
  · exact context_12_26199_331123

theorem selected_cut_12553 : selected 9 ⟨331168, by decide⟩
    (prefixPartial 12 26200) = some ⟨12, 2, 0, 331168, 26200, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_26200_331168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26200 ⟨331168, by decide⟩ :=
  accepted_of_selected 12 26200 ⟨331168, by decide⟩ ⟨12, 2, 0, 331168, 26200, 3125, 65536⟩
    (by decide) selected_cut_12553

theorem selected_cut_12554 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104804) = some ⟨13, 1, 0, 3444, 104804, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104804_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104804 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104804 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104804, 1, 16384⟩
    (by decide) selected_cut_12554

theorem selected_cut_12555 : selected 8 ⟨331201, by decide⟩
    (prefixPartial 13 104805) = some ⟨13, 2, 0, 331201, 104805, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_104805_331201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104805 ⟨331201, by decide⟩ :=
  accepted_of_selected 13 104805 ⟨331201, by decide⟩ ⟨13, 2, 0, 331201, 104805, 1801, 16384⟩
    (by decide) selected_cut_12555

theorem selected_cut_12556 : selected 8 ⟨331228, by decide⟩
    (prefixPartial 13 104806) = some ⟨13, 2, 0, 331228, 104806, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_104806_331228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104806 ⟨331228, by decide⟩ :=
  accepted_of_selected 13 104806 ⟨331228, by decide⟩ ⟨13, 2, 0, 331228, 104806, 2205, 16384⟩
    (by decide) selected_cut_12556

theorem selected_cut_12557 : selected 8 ⟨331239, by decide⟩
    (prefixPartial 13 104807) = some ⟨13, 2, 0, 331239, 104807, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_104807_331239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104807 ⟨331239, by decide⟩ :=
  accepted_of_selected 13 104807 ⟨331239, by decide⟩ ⟨13, 2, 0, 331239, 104807, 1325, 16384⟩
    (by decide) selected_cut_12557

theorem unmarked_context_12_26201_331240 : frontier 9 ⟨331240, by decide⟩
    (prefixCache 12 26201) (prefixPartial 12 26201) = false := by
  decide +kernel

theorem node_context_12_26201_331240 : EJMOriginalGlobalDAGData.nodes 9 ⟨331240, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨331201, by decide⟩,⟨331228, by decide⟩,⟨331239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26201_331240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26201 ⟨331240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26201
    ⟨331240, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨331201, by decide⟩,⟨331228, by decide⟩,⟨331239, by decide⟩]) unmarked_context_12_26201_331240 node_context_12_26201_331240
  intro a
  fin_cases a
  · exact context_13_104804_3444
  · exact context_13_104805_331201
  · exact context_13_104806_331228
  · exact context_13_104807_331239

theorem selected_cut_12558 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104808) = some ⟨13, 1, 0, 3444, 104808, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104808_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104808 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104808 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104808, 1, 16384⟩
    (by decide) selected_cut_12558

theorem selected_cut_12559 : selected 8 ⟨331271, by decide⟩
    (prefixPartial 13 104809) = some ⟨13, 2, 0, 331271, 104809, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_104809_331271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104809 ⟨331271, by decide⟩ :=
  accepted_of_selected 13 104809 ⟨331271, by decide⟩ ⟨13, 2, 0, 331271, 104809, 2037, 16384⟩
    (by decide) selected_cut_12559

theorem selected_cut_12560 : selected 8 ⟨331295, by decide⟩
    (prefixPartial 13 104810) = some ⟨13, 2, 0, 331295, 104810, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_104810_331295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104810 ⟨331295, by decide⟩ :=
  accepted_of_selected 13 104810 ⟨331295, by decide⟩ ⟨13, 2, 0, 331295, 104810, 2389, 16384⟩
    (by decide) selected_cut_12560

theorem selected_cut_12561 : selected 8 ⟨331302, by decide⟩
    (prefixPartial 13 104811) = some ⟨13, 2, 0, 331302, 104811, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_104811_331302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104811 ⟨331302, by decide⟩ :=
  accepted_of_selected 13 104811 ⟨331302, by decide⟩ ⟨13, 2, 0, 331302, 104811, 1241, 16384⟩
    (by decide) selected_cut_12561

theorem unmarked_context_12_26202_331303 : frontier 9 ⟨331303, by decide⟩
    (prefixCache 12 26202) (prefixPartial 12 26202) = false := by
  decide +kernel

theorem node_context_12_26202_331303 : EJMOriginalGlobalDAGData.nodes 9 ⟨331303, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨331271, by decide⟩,⟨331295, by decide⟩,⟨331302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26202_331303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26202 ⟨331303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26202
    ⟨331303, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨331271, by decide⟩,⟨331295, by decide⟩,⟨331302, by decide⟩]) unmarked_context_12_26202_331303 node_context_12_26202_331303
  intro a
  fin_cases a
  · exact context_13_104808_3444
  · exact context_13_104809_331271
  · exact context_13_104810_331295
  · exact context_13_104811_331302

theorem selected_cut_12562 : selected 9 ⟨331357, by decide⟩
    (prefixPartial 12 26203) = some ⟨12, 2, 0, 331357, 26203, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_26203_331357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26203 ⟨331357, by decide⟩ :=
  accepted_of_selected 12 26203 ⟨331357, by decide⟩ ⟨12, 2, 0, 331357, 26203, 3941, 65536⟩
    (by decide) selected_cut_12562

theorem unmarked_context_11_6550_331358 : frontier 10 ⟨331358, by decide⟩
    (prefixCache 11 6550) (prefixPartial 11 6550) = false := by
  decide +kernel

theorem node_context_11_6550_331358 : EJMOriginalGlobalDAGData.nodes 10 ⟨331358, by decide⟩ =
    .split (coordinate 11) (![⟨331168, by decide⟩,⟨331240, by decide⟩,⟨331303, by decide⟩,⟨331357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6550_331358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6550 ⟨331358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6550
    ⟨331358, by decide⟩ (by decide) (![⟨331168, by decide⟩,⟨331240, by decide⟩,⟨331303, by decide⟩,⟨331357, by decide⟩]) unmarked_context_11_6550_331358 node_context_11_6550_331358
  intro a
  fin_cases a
  · exact context_12_26200_331168
  · exact context_12_26201_331240
  · exact context_12_26202_331303
  · exact context_12_26203_331357

theorem selected_cut_12563 : selected 9 ⟨331403, by decide⟩
    (prefixPartial 12 26204) = some ⟨12, 2, 0, 331403, 26204, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_26204_331403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26204 ⟨331403, by decide⟩ :=
  accepted_of_selected 12 26204 ⟨331403, by decide⟩ ⟨12, 2, 0, 331403, 26204, 3445, 65536⟩
    (by decide) selected_cut_12563

theorem selected_cut_12564 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104820) = some ⟨13, 1, 0, 3444, 104820, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104820_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104820 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104820 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104820, 1, 16384⟩
    (by decide) selected_cut_12564

theorem selected_cut_12565 : selected 8 ⟨331429, by decide⟩
    (prefixPartial 13 104821) = some ⟨13, 2, 0, 331429, 104821, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_104821_331429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104821 ⟨331429, by decide⟩ :=
  accepted_of_selected 13 104821 ⟨331429, by decide⟩ ⟨13, 2, 0, 331429, 104821, 1693, 16384⟩
    (by decide) selected_cut_12565

theorem selected_cut_12566 : selected 8 ⟨331469, by decide⟩
    (prefixPartial 13 104822) = some ⟨13, 2, 0, 331469, 104822, 2609, 16384⟩ := by
  decide +kernel

theorem context_13_104822_331469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104822 ⟨331469, by decide⟩ :=
  accepted_of_selected 13 104822 ⟨331469, by decide⟩ ⟨13, 2, 0, 331469, 104822, 2609, 16384⟩
    (by decide) selected_cut_12566

theorem selected_cut_12567 : selected 8 ⟨331478, by decide⟩
    (prefixPartial 13 104823) = some ⟨13, 2, 0, 331478, 104823, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_104823_331478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104823 ⟨331478, by decide⟩ :=
  accepted_of_selected 13 104823 ⟨331478, by decide⟩ ⟨13, 2, 0, 331478, 104823, 1229, 16384⟩
    (by decide) selected_cut_12567

theorem unmarked_context_12_26205_331479 : frontier 9 ⟨331479, by decide⟩
    (prefixCache 12 26205) (prefixPartial 12 26205) = false := by
  decide +kernel

theorem node_context_12_26205_331479 : EJMOriginalGlobalDAGData.nodes 9 ⟨331479, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨331429, by decide⟩,⟨331469, by decide⟩,⟨331478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26205_331479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26205 ⟨331479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26205
    ⟨331479, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨331429, by decide⟩,⟨331469, by decide⟩,⟨331478, by decide⟩]) unmarked_context_12_26205_331479 node_context_12_26205_331479
  intro a
  fin_cases a
  · exact context_13_104820_3444
  · exact context_13_104821_331429
  · exact context_13_104822_331469
  · exact context_13_104823_331478

theorem selected_cut_12568 : selected 9 ⟨331521, by decide⟩
    (prefixPartial 12 26206) = some ⟨12, 2, 0, 331521, 26206, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_26206_331521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26206 ⟨331521, by decide⟩ :=
  accepted_of_selected 12 26206 ⟨331521, by decide⟩ ⟨12, 2, 0, 331521, 26206, 3329, 65536⟩
    (by decide) selected_cut_12568

theorem selected_cut_12569 : selected 9 ⟨331573, by decide⟩
    (prefixPartial 12 26207) = some ⟨12, 2, 0, 331573, 26207, 3961, 65536⟩ := by
  decide +kernel

theorem context_12_26207_331573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26207 ⟨331573, by decide⟩ :=
  accepted_of_selected 12 26207 ⟨331573, by decide⟩ ⟨12, 2, 0, 331573, 26207, 3961, 65536⟩
    (by decide) selected_cut_12569

theorem unmarked_context_11_6551_331574 : frontier 10 ⟨331574, by decide⟩
    (prefixCache 11 6551) (prefixPartial 11 6551) = false := by
  decide +kernel

theorem node_context_11_6551_331574 : EJMOriginalGlobalDAGData.nodes 10 ⟨331574, by decide⟩ =
    .split (coordinate 11) (![⟨331403, by decide⟩,⟨331479, by decide⟩,⟨331521, by decide⟩,⟨331573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6551_331574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6551 ⟨331574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6551
    ⟨331574, by decide⟩ (by decide) (![⟨331403, by decide⟩,⟨331479, by decide⟩,⟨331521, by decide⟩,⟨331573, by decide⟩]) unmarked_context_11_6551_331574 node_context_11_6551_331574
  intro a
  fin_cases a
  · exact context_12_26204_331403
  · exact context_12_26205_331479
  · exact context_12_26206_331521
  · exact context_12_26207_331573

theorem unmarked_context_10_1637_331575 : frontier 11 ⟨331575, by decide⟩
    (prefixCache 10 1637) (prefixPartial 10 1637) = false := by
  decide +kernel

theorem node_context_10_1637_331575 : EJMOriginalGlobalDAGData.nodes 11 ⟨331575, by decide⟩ =
    .split (coordinate 10) (![⟨330946, by decide⟩,⟨331124, by decide⟩,⟨331358, by decide⟩,⟨331574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1637_331575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1637 ⟨331575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1637
    ⟨331575, by decide⟩ (by decide) (![⟨330946, by decide⟩,⟨331124, by decide⟩,⟨331358, by decide⟩,⟨331574, by decide⟩]) unmarked_context_10_1637_331575 node_context_10_1637_331575
  intro a
  fin_cases a
  · exact context_11_6548_330946
  · exact context_11_6549_331124
  · exact context_11_6550_331358
  · exact context_11_6551_331574

theorem selected_cut_12570 : selected 9 ⟨331613, by decide⟩
    (prefixPartial 12 26208) = some ⟨12, 2, 0, 331613, 26208, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_26208_331613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26208 ⟨331613, by decide⟩ :=
  accepted_of_selected 12 26208 ⟨331613, by decide⟩ ⟨12, 2, 0, 331613, 26208, 3513, 65536⟩
    (by decide) selected_cut_12570

theorem selected_cut_12571 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104836) = some ⟨13, 1, 0, 3444, 104836, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104836_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104836 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104836 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104836, 1, 16384⟩
    (by decide) selected_cut_12571

theorem selected_cut_12572 : selected 8 ⟨331649, by decide⟩
    (prefixPartial 13 104837) = some ⟨13, 2, 0, 331649, 104837, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_104837_331649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104837 ⟨331649, by decide⟩ :=
  accepted_of_selected 13 104837 ⟨331649, by decide⟩ ⟨13, 2, 0, 331649, 104837, 2277, 16384⟩
    (by decide) selected_cut_12572

theorem selected_cut_12573 : selected 8 ⟨331697, by decide⟩
    (prefixPartial 13 104838) = some ⟨13, 2, 0, 331697, 104838, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_104838_331697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104838 ⟨331697, by decide⟩ :=
  accepted_of_selected 13 104838 ⟨331697, by decide⟩ ⟨13, 2, 0, 331697, 104838, 2625, 16384⟩
    (by decide) selected_cut_12573

theorem selected_cut_12574 : selected 8 ⟨331714, by decide⟩
    (prefixPartial 13 104839) = some ⟨13, 2, 0, 331714, 104839, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_104839_331714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104839 ⟨331714, by decide⟩ :=
  accepted_of_selected 13 104839 ⟨331714, by decide⟩ ⟨13, 2, 0, 331714, 104839, 1409, 16384⟩
    (by decide) selected_cut_12574

theorem unmarked_context_12_26209_331715 : frontier 9 ⟨331715, by decide⟩
    (prefixCache 12 26209) (prefixPartial 12 26209) = false := by
  decide +kernel

theorem node_context_12_26209_331715 : EJMOriginalGlobalDAGData.nodes 9 ⟨331715, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨331649, by decide⟩,⟨331697, by decide⟩,⟨331714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26209_331715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26209 ⟨331715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26209
    ⟨331715, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨331649, by decide⟩,⟨331697, by decide⟩,⟨331714, by decide⟩]) unmarked_context_12_26209_331715 node_context_12_26209_331715
  intro a
  fin_cases a
  · exact context_13_104836_3444
  · exact context_13_104837_331649
  · exact context_13_104838_331697
  · exact context_13_104839_331714

theorem selected_cut_12575 : selected 9 ⟨331751, by decide⟩
    (prefixPartial 12 26210) = some ⟨12, 2, 0, 331751, 26210, 3377, 65536⟩ := by
  decide +kernel

theorem context_12_26210_331751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26210 ⟨331751, by decide⟩ :=
  accepted_of_selected 12 26210 ⟨331751, by decide⟩ ⟨12, 2, 0, 331751, 26210, 3377, 65536⟩
    (by decide) selected_cut_12575

theorem selected_cut_12576 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104844) = some ⟨13, 1, 0, 3444, 104844, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104844_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104844 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104844 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104844, 1, 16384⟩
    (by decide) selected_cut_12576

theorem selected_cut_12577 : selected 8 ⟨331781, by decide⟩
    (prefixPartial 13 104845) = some ⟨13, 2, 0, 331781, 104845, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_104845_331781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104845 ⟨331781, by decide⟩ :=
  accepted_of_selected 13 104845 ⟨331781, by decide⟩ ⟨13, 2, 0, 331781, 104845, 1721, 16384⟩
    (by decide) selected_cut_12577

theorem selected_cut_12578 : selected 8 ⟨331805, by decide⟩
    (prefixPartial 13 104846) = some ⟨13, 2, 0, 331805, 104846, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_104846_331805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104846 ⟨331805, by decide⟩ :=
  accepted_of_selected 13 104846 ⟨331805, by decide⟩ ⟨13, 2, 0, 331805, 104846, 1889, 16384⟩
    (by decide) selected_cut_12578

theorem selected_cut_12579 : selected 8 ⟨331810, by decide⟩
    (prefixPartial 13 104847) = some ⟨13, 2, 0, 331810, 104847, 961, 16384⟩ := by
  decide +kernel

theorem context_13_104847_331810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104847 ⟨331810, by decide⟩ :=
  accepted_of_selected 13 104847 ⟨331810, by decide⟩ ⟨13, 2, 0, 331810, 104847, 961, 16384⟩
    (by decide) selected_cut_12579

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
