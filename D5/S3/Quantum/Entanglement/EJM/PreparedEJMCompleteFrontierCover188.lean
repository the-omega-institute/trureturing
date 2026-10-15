/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover187
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_18050 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 71189) = some ⟨12, 1, 0, 449506, 71189, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71189_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71189 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 71189 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 71189, 1, 65536⟩
    (by decide) selected_cut_18050

theorem selected_cut_18051 : selected 8 ⟨463212, by decide⟩
    (prefixPartial 13 284760) = some ⟨13, 2, 0, 463212, 284760, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_284760_463212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284760 ⟨463212, by decide⟩ :=
  accepted_of_selected 13 284760 ⟨463212, by decide⟩ ⟨13, 2, 0, 463212, 284760, 2497, 16384⟩
    (by decide) selected_cut_18051

theorem selected_cut_18052 : selected 8 ⟨463238, by decide⟩
    (prefixPartial 13 284761) = some ⟨13, 2, 0, 463238, 284761, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_284761_463238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284761 ⟨463238, by decide⟩ :=
  accepted_of_selected 13 284761 ⟨463238, by decide⟩ ⟨13, 2, 0, 463238, 284761, 2329, 16384⟩
    (by decide) selected_cut_18052

theorem selected_cut_18053 : selected 8 ⟨463259, by decide⟩
    (prefixPartial 13 284762) = some ⟨13, 2, 0, 463259, 284762, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_284762_463259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284762 ⟨463259, by decide⟩ :=
  accepted_of_selected 13 284762 ⟨463259, by decide⟩ ⟨13, 2, 0, 463259, 284762, 1669, 16384⟩
    (by decide) selected_cut_18053

theorem selected_cut_18054 : selected 8 ⟨463270, by decide⟩
    (prefixPartial 13 284763) = some ⟨13, 2, 0, 463270, 284763, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_284763_463270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284763 ⟨463270, by decide⟩ :=
  accepted_of_selected 13 284763 ⟨463270, by decide⟩ ⟨13, 2, 0, 463270, 284763, 1089, 16384⟩
    (by decide) selected_cut_18054

theorem unmarked_context_12_71190_463271 : frontier 9 ⟨463271, by decide⟩
    (prefixCache 12 71190) (prefixPartial 12 71190) = false := by
  decide +kernel

theorem node_context_12_71190_463271 : EJMOriginalGlobalDAGData.nodes 9 ⟨463271, by decide⟩ =
    .split (coordinate 12) (![⟨463212, by decide⟩,⟨463238, by decide⟩,⟨463259, by decide⟩,⟨463270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71190_463271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71190 ⟨463271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71190
    ⟨463271, by decide⟩ (by decide) (![⟨463212, by decide⟩,⟨463238, by decide⟩,⟨463259, by decide⟩,⟨463270, by decide⟩]) unmarked_context_12_71190_463271 node_context_12_71190_463271
  intro a
  fin_cases a
  · exact context_13_284760_463212
  · exact context_13_284761_463238
  · exact context_13_284762_463259
  · exact context_13_284763_463270

theorem selected_cut_18055 : selected 8 ⟨463318, by decide⟩
    (prefixPartial 13 284764) = some ⟨13, 2, 0, 463318, 284764, 2825, 16384⟩ := by
  decide +kernel

theorem context_13_284764_463318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284764 ⟨463318, by decide⟩ :=
  accepted_of_selected 13 284764 ⟨463318, by decide⟩ ⟨13, 2, 0, 463318, 284764, 2825, 16384⟩
    (by decide) selected_cut_18055

theorem selected_cut_18056 : selected 8 ⟨463352, by decide⟩
    (prefixPartial 13 284765) = some ⟨13, 2, 0, 463352, 284765, 2581, 16384⟩ := by
  decide +kernel

theorem context_13_284765_463352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284765 ⟨463352, by decide⟩ :=
  accepted_of_selected 13 284765 ⟨463352, by decide⟩ ⟨13, 2, 0, 463352, 284765, 2581, 16384⟩
    (by decide) selected_cut_18056

theorem selected_cut_18057 : selected 8 ⟨463381, by decide⟩
    (prefixPartial 13 284766) = some ⟨13, 2, 0, 463381, 284766, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_284766_463381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284766 ⟨463381, by decide⟩ :=
  accepted_of_selected 13 284766 ⟨463381, by decide⟩ ⟨13, 2, 0, 463381, 284766, 1965, 16384⟩
    (by decide) selected_cut_18057

theorem selected_cut_18058 : selected 8 ⟨463394, by decide⟩
    (prefixPartial 13 284767) = some ⟨13, 2, 0, 463394, 284767, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_284767_463394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284767 ⟨463394, by decide⟩ :=
  accepted_of_selected 13 284767 ⟨463394, by decide⟩ ⟨13, 2, 0, 463394, 284767, 1093, 16384⟩
    (by decide) selected_cut_18058

theorem unmarked_context_12_71191_463395 : frontier 9 ⟨463395, by decide⟩
    (prefixCache 12 71191) (prefixPartial 12 71191) = false := by
  decide +kernel

theorem node_context_12_71191_463395 : EJMOriginalGlobalDAGData.nodes 9 ⟨463395, by decide⟩ =
    .split (coordinate 12) (![⟨463318, by decide⟩,⟨463352, by decide⟩,⟨463381, by decide⟩,⟨463394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71191_463395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71191 ⟨463395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71191
    ⟨463395, by decide⟩ (by decide) (![⟨463318, by decide⟩,⟨463352, by decide⟩,⟨463381, by decide⟩,⟨463394, by decide⟩]) unmarked_context_12_71191_463395 node_context_12_71191_463395
  intro a
  fin_cases a
  · exact context_13_284764_463318
  · exact context_13_284765_463352
  · exact context_13_284766_463381
  · exact context_13_284767_463394

theorem unmarked_context_11_17797_463396 : frontier 10 ⟨463396, by decide⟩
    (prefixCache 11 17797) (prefixPartial 11 17797) = false := by
  decide +kernel

theorem node_context_11_17797_463396 : EJMOriginalGlobalDAGData.nodes 10 ⟨463396, by decide⟩ =
    .split (coordinate 11) (![⟨463174, by decide⟩,⟨449506, by decide⟩,⟨463271, by decide⟩,⟨463395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17797_463396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17797 ⟨463396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17797
    ⟨463396, by decide⟩ (by decide) (![⟨463174, by decide⟩,⟨449506, by decide⟩,⟨463271, by decide⟩,⟨463395, by decide⟩]) unmarked_context_11_17797_463396 node_context_11_17797_463396
  intro a
  fin_cases a
  · exact context_12_71188_463174
  · exact context_12_71189_449506
  · exact context_12_71190_463271
  · exact context_12_71191_463395

theorem selected_cut_18059 : selected 8 ⟨463441, by decide⟩
    (prefixPartial 13 284768) = some ⟨13, 2, 0, 463441, 284768, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_284768_463441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284768 ⟨463441, by decide⟩ :=
  accepted_of_selected 13 284768 ⟨463441, by decide⟩ ⟨13, 2, 0, 463441, 284768, 2193, 16384⟩
    (by decide) selected_cut_18059

theorem selected_cut_18060 : selected 8 ⟨463467, by decide⟩
    (prefixPartial 13 284769) = some ⟨13, 2, 0, 463467, 284769, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_284769_463467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284769 ⟨463467, by decide⟩ :=
  accepted_of_selected 13 284769 ⟨463467, by decide⟩ ⟨13, 2, 0, 463467, 284769, 2469, 16384⟩
    (by decide) selected_cut_18060

theorem selected_cut_18061 : selected 8 ⟨463488, by decide⟩
    (prefixPartial 13 284770) = some ⟨13, 2, 0, 463488, 284770, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_284770_463488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284770 ⟨463488, by decide⟩ :=
  accepted_of_selected 13 284770 ⟨463488, by decide⟩ ⟨13, 2, 0, 463488, 284770, 1685, 16384⟩
    (by decide) selected_cut_18061

theorem selected_cut_18062 : selected 8 ⟨463498, by decide⟩
    (prefixPartial 13 284771) = some ⟨13, 2, 0, 463498, 284771, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_284771_463498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284771 ⟨463498, by decide⟩ :=
  accepted_of_selected 13 284771 ⟨463498, by decide⟩ ⟨13, 2, 0, 463498, 284771, 1081, 16384⟩
    (by decide) selected_cut_18062

theorem unmarked_context_12_71192_463499 : frontier 9 ⟨463499, by decide⟩
    (prefixCache 12 71192) (prefixPartial 12 71192) = false := by
  decide +kernel

theorem node_context_12_71192_463499 : EJMOriginalGlobalDAGData.nodes 9 ⟨463499, by decide⟩ =
    .split (coordinate 12) (![⟨463441, by decide⟩,⟨463467, by decide⟩,⟨463488, by decide⟩,⟨463498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71192_463499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71192 ⟨463499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71192
    ⟨463499, by decide⟩ (by decide) (![⟨463441, by decide⟩,⟨463467, by decide⟩,⟨463488, by decide⟩,⟨463498, by decide⟩]) unmarked_context_12_71192_463499 node_context_12_71192_463499
  intro a
  fin_cases a
  · exact context_13_284768_463441
  · exact context_13_284769_463467
  · exact context_13_284770_463488
  · exact context_13_284771_463498

theorem selected_cut_18063 : selected 8 ⟨463528, by decide⟩
    (prefixPartial 13 284772) = some ⟨13, 2, 0, 463528, 284772, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_284772_463528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284772 ⟨463528, by decide⟩ :=
  accepted_of_selected 13 284772 ⟨463528, by decide⟩ ⟨13, 2, 0, 463528, 284772, 1373, 16384⟩
    (by decide) selected_cut_18063

theorem selected_cut_18064 : selected 8 ⟨463551, by decide⟩
    (prefixPartial 13 284773) = some ⟨13, 2, 0, 463551, 284773, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_284773_463551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284773 ⟨463551, by decide⟩ :=
  accepted_of_selected 13 284773 ⟨463551, by decide⟩ ⟨13, 2, 0, 463551, 284773, 1641, 16384⟩
    (by decide) selected_cut_18064

theorem selected_cut_18065 : selected 8 ⟨463567, by decide⟩
    (prefixPartial 13 284774) = some ⟨13, 2, 0, 463567, 284774, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_284774_463567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284774 ⟨463567, by decide⟩ :=
  accepted_of_selected 13 284774 ⟨463567, by decide⟩ ⟨13, 2, 0, 463567, 284774, 1081, 16384⟩
    (by decide) selected_cut_18065

theorem selected_cut_18066 : selected 8 ⟨463574, by decide⟩
    (prefixPartial 13 284775) = some ⟨13, 2, 0, 463574, 284775, 845, 16384⟩ := by
  decide +kernel

theorem context_13_284775_463574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284775 ⟨463574, by decide⟩ :=
  accepted_of_selected 13 284775 ⟨463574, by decide⟩ ⟨13, 2, 0, 463574, 284775, 845, 16384⟩
    (by decide) selected_cut_18066

theorem unmarked_context_12_71193_463575 : frontier 9 ⟨463575, by decide⟩
    (prefixCache 12 71193) (prefixPartial 12 71193) = false := by
  decide +kernel

theorem node_context_12_71193_463575 : EJMOriginalGlobalDAGData.nodes 9 ⟨463575, by decide⟩ =
    .split (coordinate 12) (![⟨463528, by decide⟩,⟨463551, by decide⟩,⟨463567, by decide⟩,⟨463574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71193_463575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71193 ⟨463575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71193
    ⟨463575, by decide⟩ (by decide) (![⟨463528, by decide⟩,⟨463551, by decide⟩,⟨463567, by decide⟩,⟨463574, by decide⟩]) unmarked_context_12_71193_463575 node_context_12_71193_463575
  intro a
  fin_cases a
  · exact context_13_284772_463528
  · exact context_13_284773_463551
  · exact context_13_284774_463567
  · exact context_13_284775_463574

theorem selected_cut_18067 : selected 8 ⟨463615, by decide⟩
    (prefixPartial 13 284776) = some ⟨13, 2, 0, 463615, 284776, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_284776_463615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284776 ⟨463615, by decide⟩ :=
  accepted_of_selected 13 284776 ⟨463615, by decide⟩ ⟨13, 2, 0, 463615, 284776, 2593, 16384⟩
    (by decide) selected_cut_18067

theorem selected_cut_18068 : selected 8 ⟨463643, by decide⟩
    (prefixPartial 13 284777) = some ⟨13, 2, 0, 463643, 284777, 3225, 16384⟩ := by
  decide +kernel

theorem context_13_284777_463643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284777 ⟨463643, by decide⟩ :=
  accepted_of_selected 13 284777 ⟨463643, by decide⟩ ⟨13, 2, 0, 463643, 284777, 3225, 16384⟩
    (by decide) selected_cut_18068

theorem selected_cut_18069 : selected 8 ⟨463670, by decide⟩
    (prefixPartial 13 284778) = some ⟨13, 2, 0, 463670, 284778, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_284778_463670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284778 ⟨463670, by decide⟩ :=
  accepted_of_selected 13 284778 ⟨463670, by decide⟩ ⟨13, 2, 0, 463670, 284778, 2073, 16384⟩
    (by decide) selected_cut_18069

theorem selected_cut_18070 : selected 8 ⟨463686, by decide⟩
    (prefixPartial 13 284779) = some ⟨13, 2, 0, 463686, 284779, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_284779_463686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284779 ⟨463686, by decide⟩ :=
  accepted_of_selected 13 284779 ⟨463686, by decide⟩ ⟨13, 2, 0, 463686, 284779, 1277, 16384⟩
    (by decide) selected_cut_18070

theorem unmarked_context_12_71194_463687 : frontier 9 ⟨463687, by decide⟩
    (prefixCache 12 71194) (prefixPartial 12 71194) = false := by
  decide +kernel

theorem node_context_12_71194_463687 : EJMOriginalGlobalDAGData.nodes 9 ⟨463687, by decide⟩ =
    .split (coordinate 12) (![⟨463615, by decide⟩,⟨463643, by decide⟩,⟨463670, by decide⟩,⟨463686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71194_463687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71194 ⟨463687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71194
    ⟨463687, by decide⟩ (by decide) (![⟨463615, by decide⟩,⟨463643, by decide⟩,⟨463670, by decide⟩,⟨463686, by decide⟩]) unmarked_context_12_71194_463687 node_context_12_71194_463687
  intro a
  fin_cases a
  · exact context_13_284776_463615
  · exact context_13_284777_463643
  · exact context_13_284778_463670
  · exact context_13_284779_463686

theorem selected_cut_18071 : selected 8 ⟨463723, by decide⟩
    (prefixPartial 13 284780) = some ⟨13, 2, 0, 463723, 284780, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_284780_463723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284780 ⟨463723, by decide⟩ :=
  accepted_of_selected 13 284780 ⟨463723, by decide⟩ ⟨13, 2, 0, 463723, 284780, 1685, 16384⟩
    (by decide) selected_cut_18071

theorem selected_cut_18072 : selected 8 ⟨463753, by decide⟩
    (prefixPartial 13 284781) = some ⟨13, 2, 0, 463753, 284781, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_284781_463753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284781 ⟨463753, by decide⟩ :=
  accepted_of_selected 13 284781 ⟨463753, by decide⟩ ⟨13, 2, 0, 463753, 284781, 2257, 16384⟩
    (by decide) selected_cut_18072

theorem selected_cut_18073 : selected 8 ⟨463772, by decide⟩
    (prefixPartial 13 284782) = some ⟨13, 2, 0, 463772, 284782, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_284782_463772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284782 ⟨463772, by decide⟩ :=
  accepted_of_selected 13 284782 ⟨463772, by decide⟩ ⟨13, 2, 0, 463772, 284782, 1357, 16384⟩
    (by decide) selected_cut_18073

theorem selected_cut_18074 : selected 8 ⟨463776, by decide⟩
    (prefixPartial 13 284783) = some ⟨13, 2, 0, 463776, 284783, 837, 16384⟩ := by
  decide +kernel

theorem context_13_284783_463776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284783 ⟨463776, by decide⟩ :=
  accepted_of_selected 13 284783 ⟨463776, by decide⟩ ⟨13, 2, 0, 463776, 284783, 837, 16384⟩
    (by decide) selected_cut_18074

theorem unmarked_context_12_71195_463777 : frontier 9 ⟨463777, by decide⟩
    (prefixCache 12 71195) (prefixPartial 12 71195) = false := by
  decide +kernel

theorem node_context_12_71195_463777 : EJMOriginalGlobalDAGData.nodes 9 ⟨463777, by decide⟩ =
    .split (coordinate 12) (![⟨463723, by decide⟩,⟨463753, by decide⟩,⟨463772, by decide⟩,⟨463776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71195_463777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71195 ⟨463777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71195
    ⟨463777, by decide⟩ (by decide) (![⟨463723, by decide⟩,⟨463753, by decide⟩,⟨463772, by decide⟩,⟨463776, by decide⟩]) unmarked_context_12_71195_463777 node_context_12_71195_463777
  intro a
  fin_cases a
  · exact context_13_284780_463723
  · exact context_13_284781_463753
  · exact context_13_284782_463772
  · exact context_13_284783_463776

theorem unmarked_context_11_17798_463778 : frontier 10 ⟨463778, by decide⟩
    (prefixCache 11 17798) (prefixPartial 11 17798) = false := by
  decide +kernel

theorem node_context_11_17798_463778 : EJMOriginalGlobalDAGData.nodes 10 ⟨463778, by decide⟩ =
    .split (coordinate 11) (![⟨463499, by decide⟩,⟨463575, by decide⟩,⟨463687, by decide⟩,⟨463777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17798_463778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17798 ⟨463778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17798
    ⟨463778, by decide⟩ (by decide) (![⟨463499, by decide⟩,⟨463575, by decide⟩,⟨463687, by decide⟩,⟨463777, by decide⟩]) unmarked_context_11_17798_463778 node_context_11_17798_463778
  intro a
  fin_cases a
  · exact context_12_71192_463499
  · exact context_12_71193_463575
  · exact context_12_71194_463687
  · exact context_12_71195_463777

theorem selected_cut_18075 : selected 8 ⟨463812, by decide⟩
    (prefixPartial 13 284784) = some ⟨13, 2, 0, 463812, 284784, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_284784_463812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284784 ⟨463812, by decide⟩ :=
  accepted_of_selected 13 284784 ⟨463812, by decide⟩ ⟨13, 2, 0, 463812, 284784, 1865, 16384⟩
    (by decide) selected_cut_18075

theorem selected_cut_18076 : selected 8 ⟨463846, by decide⟩
    (prefixPartial 13 284785) = some ⟨13, 2, 0, 463846, 284785, 2881, 16384⟩ := by
  decide +kernel

theorem context_13_284785_463846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284785 ⟨463846, by decide⟩ :=
  accepted_of_selected 13 284785 ⟨463846, by decide⟩ ⟨13, 2, 0, 463846, 284785, 2881, 16384⟩
    (by decide) selected_cut_18076

theorem selected_cut_18077 : selected 8 ⟨463862, by decide⟩
    (prefixPartial 13 284786) = some ⟨13, 2, 0, 463862, 284786, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_284786_463862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284786 ⟨463862, by decide⟩ :=
  accepted_of_selected 13 284786 ⟨463862, by decide⟩ ⟨13, 2, 0, 463862, 284786, 1769, 16384⟩
    (by decide) selected_cut_18077

theorem selected_cut_18078 : selected 8 ⟨463869, by decide⟩
    (prefixPartial 13 284787) = some ⟨13, 2, 0, 463869, 284787, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_284787_463869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284787 ⟨463869, by decide⟩ :=
  accepted_of_selected 13 284787 ⟨463869, by decide⟩ ⟨13, 2, 0, 463869, 284787, 1049, 16384⟩
    (by decide) selected_cut_18078

theorem unmarked_context_12_71196_463870 : frontier 9 ⟨463870, by decide⟩
    (prefixCache 12 71196) (prefixPartial 12 71196) = false := by
  decide +kernel

theorem node_context_12_71196_463870 : EJMOriginalGlobalDAGData.nodes 9 ⟨463870, by decide⟩ =
    .split (coordinate 12) (![⟨463812, by decide⟩,⟨463846, by decide⟩,⟨463862, by decide⟩,⟨463869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71196_463870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71196 ⟨463870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71196
    ⟨463870, by decide⟩ (by decide) (![⟨463812, by decide⟩,⟨463846, by decide⟩,⟨463862, by decide⟩,⟨463869, by decide⟩]) unmarked_context_12_71196_463870 node_context_12_71196_463870
  intro a
  fin_cases a
  · exact context_13_284784_463812
  · exact context_13_284785_463846
  · exact context_13_284786_463862
  · exact context_13_284787_463869

theorem selected_cut_18079 : selected 8 ⟨463895, by decide⟩
    (prefixPartial 13 284788) = some ⟨13, 2, 0, 463895, 284788, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_284788_463895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284788 ⟨463895, by decide⟩ :=
  accepted_of_selected 13 284788 ⟨463895, by decide⟩ ⟨13, 2, 0, 463895, 284788, 1233, 16384⟩
    (by decide) selected_cut_18079

theorem selected_cut_18080 : selected 8 ⟨463919, by decide⟩
    (prefixPartial 13 284789) = some ⟨13, 2, 0, 463919, 284789, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_284789_463919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284789 ⟨463919, by decide⟩ :=
  accepted_of_selected 13 284789 ⟨463919, by decide⟩ ⟨13, 2, 0, 463919, 284789, 1849, 16384⟩
    (by decide) selected_cut_18080

theorem selected_cut_18081 : selected 8 ⟨463935, by decide⟩
    (prefixPartial 13 284790) = some ⟨13, 2, 0, 463935, 284790, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_284790_463935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284790 ⟨463935, by decide⟩ :=
  accepted_of_selected 13 284790 ⟨463935, by decide⟩ ⟨13, 2, 0, 463935, 284790, 1089, 16384⟩
    (by decide) selected_cut_18081

theorem selected_cut_18082 : selected 8 ⟨463941, by decide⟩
    (prefixPartial 13 284791) = some ⟨13, 2, 0, 463941, 284791, 781, 16384⟩ := by
  decide +kernel

theorem context_13_284791_463941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284791 ⟨463941, by decide⟩ :=
  accepted_of_selected 13 284791 ⟨463941, by decide⟩ ⟨13, 2, 0, 463941, 284791, 781, 16384⟩
    (by decide) selected_cut_18082

theorem unmarked_context_12_71197_463942 : frontier 9 ⟨463942, by decide⟩
    (prefixCache 12 71197) (prefixPartial 12 71197) = false := by
  decide +kernel

theorem node_context_12_71197_463942 : EJMOriginalGlobalDAGData.nodes 9 ⟨463942, by decide⟩ =
    .split (coordinate 12) (![⟨463895, by decide⟩,⟨463919, by decide⟩,⟨463935, by decide⟩,⟨463941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71197_463942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71197 ⟨463942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71197
    ⟨463942, by decide⟩ (by decide) (![⟨463895, by decide⟩,⟨463919, by decide⟩,⟨463935, by decide⟩,⟨463941, by decide⟩]) unmarked_context_12_71197_463942 node_context_12_71197_463942
  intro a
  fin_cases a
  · exact context_13_284788_463895
  · exact context_13_284789_463919
  · exact context_13_284790_463935
  · exact context_13_284791_463941

theorem selected_cut_18083 : selected 8 ⟨463966, by decide⟩
    (prefixPartial 13 284792) = some ⟨13, 2, 0, 463966, 284792, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_284792_463966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284792 ⟨463966, by decide⟩ :=
  accepted_of_selected 13 284792 ⟨463966, by decide⟩ ⟨13, 2, 0, 463966, 284792, 1317, 16384⟩
    (by decide) selected_cut_18083

theorem selected_cut_18084 : selected 8 ⟨463990, by decide⟩
    (prefixPartial 13 284793) = some ⟨13, 2, 0, 463990, 284793, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_284793_463990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284793 ⟨463990, by decide⟩ :=
  accepted_of_selected 13 284793 ⟨463990, by decide⟩ ⟨13, 2, 0, 463990, 284793, 2193, 16384⟩
    (by decide) selected_cut_18084

theorem selected_cut_18085 : selected 8 ⟨464004, by decide⟩
    (prefixPartial 13 284794) = some ⟨13, 2, 0, 464004, 284794, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_284794_464004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284794 ⟨464004, by decide⟩ :=
  accepted_of_selected 13 284794 ⟨464004, by decide⟩ ⟨13, 2, 0, 464004, 284794, 1269, 16384⟩
    (by decide) selected_cut_18085

theorem selected_cut_18086 : selected 8 ⟨464010, by decide⟩
    (prefixPartial 13 284795) = some ⟨13, 2, 0, 464010, 284795, 781, 16384⟩ := by
  decide +kernel

theorem context_13_284795_464010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284795 ⟨464010, by decide⟩ :=
  accepted_of_selected 13 284795 ⟨464010, by decide⟩ ⟨13, 2, 0, 464010, 284795, 781, 16384⟩
    (by decide) selected_cut_18086

theorem unmarked_context_12_71198_464011 : frontier 9 ⟨464011, by decide⟩
    (prefixCache 12 71198) (prefixPartial 12 71198) = false := by
  decide +kernel

theorem node_context_12_71198_464011 : EJMOriginalGlobalDAGData.nodes 9 ⟨464011, by decide⟩ =
    .split (coordinate 12) (![⟨463966, by decide⟩,⟨463990, by decide⟩,⟨464004, by decide⟩,⟨464010, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71198_464011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71198 ⟨464011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71198
    ⟨464011, by decide⟩ (by decide) (![⟨463966, by decide⟩,⟨463990, by decide⟩,⟨464004, by decide⟩,⟨464010, by decide⟩]) unmarked_context_12_71198_464011 node_context_12_71198_464011
  intro a
  fin_cases a
  · exact context_13_284792_463966
  · exact context_13_284793_463990
  · exact context_13_284794_464004
  · exact context_13_284795_464010

theorem selected_cut_18087 : selected 8 ⟨464042, by decide⟩
    (prefixPartial 13 284796) = some ⟨13, 2, 0, 464042, 284796, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_284796_464042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284796 ⟨464042, by decide⟩ :=
  accepted_of_selected 13 284796 ⟨464042, by decide⟩ ⟨13, 2, 0, 464042, 284796, 1509, 16384⟩
    (by decide) selected_cut_18087

theorem selected_cut_18088 : selected 8 ⟨464072, by decide⟩
    (prefixPartial 13 284797) = some ⟨13, 2, 0, 464072, 284797, 2393, 16384⟩ := by
  decide +kernel

theorem context_13_284797_464072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284797 ⟨464072, by decide⟩ :=
  accepted_of_selected 13 284797 ⟨464072, by decide⟩ ⟨13, 2, 0, 464072, 284797, 2393, 16384⟩
    (by decide) selected_cut_18088

theorem selected_cut_18089 : selected 8 ⟨464089, by decide⟩
    (prefixPartial 13 284798) = some ⟨13, 2, 0, 464089, 284798, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_284798_464089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284798 ⟨464089, by decide⟩ :=
  accepted_of_selected 13 284798 ⟨464089, by decide⟩ ⟨13, 2, 0, 464089, 284798, 1517, 16384⟩
    (by decide) selected_cut_18089

theorem selected_cut_18090 : selected 8 ⟨464097, by decide⟩
    (prefixPartial 13 284799) = some ⟨13, 2, 0, 464097, 284799, 853, 16384⟩ := by
  decide +kernel

theorem context_13_284799_464097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284799 ⟨464097, by decide⟩ :=
  accepted_of_selected 13 284799 ⟨464097, by decide⟩ ⟨13, 2, 0, 464097, 284799, 853, 16384⟩
    (by decide) selected_cut_18090

theorem unmarked_context_12_71199_464098 : frontier 9 ⟨464098, by decide⟩
    (prefixCache 12 71199) (prefixPartial 12 71199) = false := by
  decide +kernel

theorem node_context_12_71199_464098 : EJMOriginalGlobalDAGData.nodes 9 ⟨464098, by decide⟩ =
    .split (coordinate 12) (![⟨464042, by decide⟩,⟨464072, by decide⟩,⟨464089, by decide⟩,⟨464097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71199_464098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71199 ⟨464098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71199
    ⟨464098, by decide⟩ (by decide) (![⟨464042, by decide⟩,⟨464072, by decide⟩,⟨464089, by decide⟩,⟨464097, by decide⟩]) unmarked_context_12_71199_464098 node_context_12_71199_464098
  intro a
  fin_cases a
  · exact context_13_284796_464042
  · exact context_13_284797_464072
  · exact context_13_284798_464089
  · exact context_13_284799_464097

theorem unmarked_context_11_17799_464099 : frontier 10 ⟨464099, by decide⟩
    (prefixCache 11 17799) (prefixPartial 11 17799) = false := by
  decide +kernel

theorem node_context_11_17799_464099 : EJMOriginalGlobalDAGData.nodes 10 ⟨464099, by decide⟩ =
    .split (coordinate 11) (![⟨463870, by decide⟩,⟨463942, by decide⟩,⟨464011, by decide⟩,⟨464098, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17799_464099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17799 ⟨464099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17799
    ⟨464099, by decide⟩ (by decide) (![⟨463870, by decide⟩,⟨463942, by decide⟩,⟨464011, by decide⟩,⟨464098, by decide⟩]) unmarked_context_11_17799_464099 node_context_11_17799_464099
  intro a
  fin_cases a
  · exact context_12_71196_463870
  · exact context_12_71197_463942
  · exact context_12_71198_464011
  · exact context_12_71199_464098

theorem unmarked_context_10_4449_464100 : frontier 11 ⟨464100, by decide⟩
    (prefixCache 10 4449) (prefixPartial 10 4449) = false := by
  decide +kernel

theorem node_context_10_4449_464100 : EJMOriginalGlobalDAGData.nodes 11 ⟨464100, by decide⟩ =
    .split (coordinate 10) (![⟨462962, by decide⟩,⟨463396, by decide⟩,⟨463778, by decide⟩,⟨464099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4449_464100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4449 ⟨464100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4449
    ⟨464100, by decide⟩ (by decide) (![⟨462962, by decide⟩,⟨463396, by decide⟩,⟨463778, by decide⟩,⟨464099, by decide⟩]) unmarked_context_10_4449_464100 node_context_10_4449_464100
  intro a
  fin_cases a
  · exact context_11_17796_462962
  · exact context_11_17797_463396
  · exact context_11_17798_463778
  · exact context_11_17799_464099

theorem selected_cut_18091 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 71200) = some ⟨12, 1, 0, 435790, 71200, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71200_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71200 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 71200 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 71200, 1, 65536⟩
    (by decide) selected_cut_18091

theorem selected_cut_18092 : selected 8 ⟨464115, by decide⟩
    (prefixPartial 13 284804) = some ⟨13, 2, 0, 464115, 284804, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_284804_464115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284804 ⟨464115, by decide⟩ :=
  accepted_of_selected 13 284804 ⟨464115, by decide⟩ ⟨13, 2, 0, 464115, 284804, 1073, 16384⟩
    (by decide) selected_cut_18092

theorem selected_cut_18093 : selected 8 ⟨464145, by decide⟩
    (prefixPartial 13 284805) = some ⟨13, 2, 0, 464145, 284805, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_284805_464145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284805 ⟨464145, by decide⟩ :=
  accepted_of_selected 13 284805 ⟨464145, by decide⟩ ⟨13, 2, 0, 464145, 284805, 2029, 16384⟩
    (by decide) selected_cut_18093

theorem selected_cut_18094 : selected 8 ⟨464165, by decide⟩
    (prefixPartial 13 284806) = some ⟨13, 2, 0, 464165, 284806, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_284806_464165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284806 ⟨464165, by decide⟩ :=
  accepted_of_selected 13 284806 ⟨464165, by decide⟩ ⟨13, 2, 0, 464165, 284806, 1237, 16384⟩
    (by decide) selected_cut_18094

theorem selected_cut_18095 : selected 8 ⟨464170, by decide⟩
    (prefixPartial 13 284807) = some ⟨13, 2, 0, 464170, 284807, 785, 16384⟩ := by
  decide +kernel

theorem context_13_284807_464170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284807 ⟨464170, by decide⟩ :=
  accepted_of_selected 13 284807 ⟨464170, by decide⟩ ⟨13, 2, 0, 464170, 284807, 785, 16384⟩
    (by decide) selected_cut_18095

theorem unmarked_context_12_71201_464171 : frontier 9 ⟨464171, by decide⟩
    (prefixCache 12 71201) (prefixPartial 12 71201) = false := by
  decide +kernel

theorem node_context_12_71201_464171 : EJMOriginalGlobalDAGData.nodes 9 ⟨464171, by decide⟩ =
    .split (coordinate 12) (![⟨464115, by decide⟩,⟨464145, by decide⟩,⟨464165, by decide⟩,⟨464170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71201_464171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71201 ⟨464171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71201
    ⟨464171, by decide⟩ (by decide) (![⟨464115, by decide⟩,⟨464145, by decide⟩,⟨464165, by decide⟩,⟨464170, by decide⟩]) unmarked_context_12_71201_464171 node_context_12_71201_464171
  intro a
  fin_cases a
  · exact context_13_284804_464115
  · exact context_13_284805_464145
  · exact context_13_284806_464165
  · exact context_13_284807_464170

theorem selected_cut_18096 : selected 8 ⟨464189, by decide⟩
    (prefixPartial 13 284808) = some ⟨13, 2, 0, 464189, 284808, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_284808_464189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284808 ⟨464189, by decide⟩ :=
  accepted_of_selected 13 284808 ⟨464189, by decide⟩ ⟨13, 2, 0, 464189, 284808, 1013, 16384⟩
    (by decide) selected_cut_18096

theorem selected_cut_18097 : selected 8 ⟨464214, by decide⟩
    (prefixPartial 13 284809) = some ⟨13, 2, 0, 464214, 284809, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_284809_464214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284809 ⟨464214, by decide⟩ :=
  accepted_of_selected 13 284809 ⟨464214, by decide⟩ ⟨13, 2, 0, 464214, 284809, 1897, 16384⟩
    (by decide) selected_cut_18097

theorem selected_cut_18098 : selected 8 ⟨464232, by decide⟩
    (prefixPartial 13 284810) = some ⟨13, 2, 0, 464232, 284810, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_284810_464232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284810 ⟨464232, by decide⟩ :=
  accepted_of_selected 13 284810 ⟨464232, by decide⟩ ⟨13, 2, 0, 464232, 284810, 1229, 16384⟩
    (by decide) selected_cut_18098

theorem selected_cut_18099 : selected 8 ⟨464236, by decide⟩
    (prefixPartial 13 284811) = some ⟨13, 2, 0, 464236, 284811, 721, 16384⟩ := by
  decide +kernel

theorem context_13_284811_464236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284811 ⟨464236, by decide⟩ :=
  accepted_of_selected 13 284811 ⟨464236, by decide⟩ ⟨13, 2, 0, 464236, 284811, 721, 16384⟩
    (by decide) selected_cut_18099

theorem unmarked_context_12_71202_464237 : frontier 9 ⟨464237, by decide⟩
    (prefixCache 12 71202) (prefixPartial 12 71202) = false := by
  decide +kernel

theorem node_context_12_71202_464237 : EJMOriginalGlobalDAGData.nodes 9 ⟨464237, by decide⟩ =
    .split (coordinate 12) (![⟨464189, by decide⟩,⟨464214, by decide⟩,⟨464232, by decide⟩,⟨464236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71202_464237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71202 ⟨464237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71202
    ⟨464237, by decide⟩ (by decide) (![⟨464189, by decide⟩,⟨464214, by decide⟩,⟨464232, by decide⟩,⟨464236, by decide⟩]) unmarked_context_12_71202_464237 node_context_12_71202_464237
  intro a
  fin_cases a
  · exact context_13_284808_464189
  · exact context_13_284809_464214
  · exact context_13_284810_464232
  · exact context_13_284811_464236

theorem selected_cut_18100 : selected 8 ⟨464258, by decide⟩
    (prefixPartial 13 284812) = some ⟨13, 2, 0, 464258, 284812, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_284812_464258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284812 ⟨464258, by decide⟩ :=
  accepted_of_selected 13 284812 ⟨464258, by decide⟩ ⟨13, 2, 0, 464258, 284812, 1301, 16384⟩
    (by decide) selected_cut_18100

theorem selected_cut_18101 : selected 8 ⟨464290, by decide⟩
    (prefixPartial 13 284813) = some ⟨13, 2, 0, 464290, 284813, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_284813_464290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284813 ⟨464290, by decide⟩ :=
  accepted_of_selected 13 284813 ⟨464290, by decide⟩ ⟨13, 2, 0, 464290, 284813, 2201, 16384⟩
    (by decide) selected_cut_18101

theorem selected_cut_18102 : selected 8 ⟨464310, by decide⟩
    (prefixPartial 13 284814) = some ⟨13, 2, 0, 464310, 284814, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_284814_464310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284814 ⟨464310, by decide⟩ :=
  accepted_of_selected 13 284814 ⟨464310, by decide⟩ ⟨13, 2, 0, 464310, 284814, 1509, 16384⟩
    (by decide) selected_cut_18102

theorem selected_cut_18103 : selected 8 ⟨464314, by decide⟩
    (prefixPartial 13 284815) = some ⟨13, 2, 0, 464314, 284815, 725, 16384⟩ := by
  decide +kernel

theorem context_13_284815_464314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284815 ⟨464314, by decide⟩ :=
  accepted_of_selected 13 284815 ⟨464314, by decide⟩ ⟨13, 2, 0, 464314, 284815, 725, 16384⟩
    (by decide) selected_cut_18103

theorem unmarked_context_12_71203_464315 : frontier 9 ⟨464315, by decide⟩
    (prefixCache 12 71203) (prefixPartial 12 71203) = false := by
  decide +kernel

theorem node_context_12_71203_464315 : EJMOriginalGlobalDAGData.nodes 9 ⟨464315, by decide⟩ =
    .split (coordinate 12) (![⟨464258, by decide⟩,⟨464290, by decide⟩,⟨464310, by decide⟩,⟨464314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71203_464315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71203 ⟨464315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71203
    ⟨464315, by decide⟩ (by decide) (![⟨464258, by decide⟩,⟨464290, by decide⟩,⟨464310, by decide⟩,⟨464314, by decide⟩]) unmarked_context_12_71203_464315 node_context_12_71203_464315
  intro a
  fin_cases a
  · exact context_13_284812_464258
  · exact context_13_284813_464290
  · exact context_13_284814_464310
  · exact context_13_284815_464314

theorem unmarked_context_11_17800_464316 : frontier 10 ⟨464316, by decide⟩
    (prefixCache 11 17800) (prefixPartial 11 17800) = false := by
  decide +kernel

theorem node_context_11_17800_464316 : EJMOriginalGlobalDAGData.nodes 10 ⟨464316, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨464171, by decide⟩,⟨464237, by decide⟩,⟨464315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17800_464316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17800 ⟨464316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17800
    ⟨464316, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨464171, by decide⟩,⟨464237, by decide⟩,⟨464315, by decide⟩]) unmarked_context_11_17800_464316 node_context_11_17800_464316
  intro a
  fin_cases a
  · exact context_12_71200_435790
  · exact context_12_71201_464171
  · exact context_12_71202_464237
  · exact context_12_71203_464315

theorem selected_cut_18104 : selected 8 ⟨464345, by decide⟩
    (prefixPartial 13 284816) = some ⟨13, 2, 0, 464345, 284816, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_284816_464345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284816 ⟨464345, by decide⟩ :=
  accepted_of_selected 13 284816 ⟨464345, by decide⟩ ⟨13, 2, 0, 464345, 284816, 1345, 16384⟩
    (by decide) selected_cut_18104

theorem selected_cut_18105 : selected 8 ⟨464384, by decide⟩
    (prefixPartial 13 284817) = some ⟨13, 2, 0, 464384, 284817, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_284817_464384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284817 ⟨464384, by decide⟩ :=
  accepted_of_selected 13 284817 ⟨464384, by decide⟩ ⟨13, 2, 0, 464384, 284817, 2569, 16384⟩
    (by decide) selected_cut_18105

theorem selected_cut_18106 : selected 8 ⟨464423, by decide⟩
    (prefixPartial 13 284818) = some ⟨13, 2, 0, 464423, 284818, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_284818_464423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284818 ⟨464423, by decide⟩ :=
  accepted_of_selected 13 284818 ⟨464423, by decide⟩ ⟨13, 2, 0, 464423, 284818, 2009, 16384⟩
    (by decide) selected_cut_18106

theorem selected_cut_18107 : selected 8 ⟨464435, by decide⟩
    (prefixPartial 13 284819) = some ⟨13, 2, 0, 464435, 284819, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_284819_464435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284819 ⟨464435, by decide⟩ :=
  accepted_of_selected 13 284819 ⟨464435, by decide⟩ ⟨13, 2, 0, 464435, 284819, 1085, 16384⟩
    (by decide) selected_cut_18107

theorem unmarked_context_12_71204_464436 : frontier 9 ⟨464436, by decide⟩
    (prefixCache 12 71204) (prefixPartial 12 71204) = false := by
  decide +kernel

theorem node_context_12_71204_464436 : EJMOriginalGlobalDAGData.nodes 9 ⟨464436, by decide⟩ =
    .split (coordinate 12) (![⟨464345, by decide⟩,⟨464384, by decide⟩,⟨464423, by decide⟩,⟨464435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71204_464436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71204 ⟨464436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71204
    ⟨464436, by decide⟩ (by decide) (![⟨464345, by decide⟩,⟨464384, by decide⟩,⟨464423, by decide⟩,⟨464435, by decide⟩]) unmarked_context_12_71204_464436 node_context_12_71204_464436
  intro a
  fin_cases a
  · exact context_13_284816_464345
  · exact context_13_284817_464384
  · exact context_13_284818_464423
  · exact context_13_284819_464435

theorem selected_cut_18108 : selected 8 ⟨464454, by decide⟩
    (prefixPartial 13 284820) = some ⟨13, 2, 0, 464454, 284820, 961, 16384⟩ := by
  decide +kernel

theorem context_13_284820_464454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284820 ⟨464454, by decide⟩ :=
  accepted_of_selected 13 284820 ⟨464454, by decide⟩ ⟨13, 2, 0, 464454, 284820, 961, 16384⟩
    (by decide) selected_cut_18108

theorem selected_cut_18109 : selected 8 ⟨464478, by decide⟩
    (prefixPartial 13 284821) = some ⟨13, 2, 0, 464478, 284821, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_284821_464478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284821 ⟨464478, by decide⟩ :=
  accepted_of_selected 13 284821 ⟨464478, by decide⟩ ⟨13, 2, 0, 464478, 284821, 1577, 16384⟩
    (by decide) selected_cut_18109

theorem selected_cut_18110 : selected 8 ⟨464495, by decide⟩
    (prefixPartial 13 284822) = some ⟨13, 2, 0, 464495, 284822, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_284822_464495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284822 ⟨464495, by decide⟩ :=
  accepted_of_selected 13 284822 ⟨464495, by decide⟩ ⟨13, 2, 0, 464495, 284822, 1201, 16384⟩
    (by decide) selected_cut_18110

theorem selected_cut_18111 : selected 8 ⟨464501, by decide⟩
    (prefixPartial 13 284823) = some ⟨13, 2, 0, 464501, 284823, 745, 16384⟩ := by
  decide +kernel

theorem context_13_284823_464501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284823 ⟨464501, by decide⟩ :=
  accepted_of_selected 13 284823 ⟨464501, by decide⟩ ⟨13, 2, 0, 464501, 284823, 745, 16384⟩
    (by decide) selected_cut_18111

theorem unmarked_context_12_71205_464502 : frontier 9 ⟨464502, by decide⟩
    (prefixCache 12 71205) (prefixPartial 12 71205) = false := by
  decide +kernel

theorem node_context_12_71205_464502 : EJMOriginalGlobalDAGData.nodes 9 ⟨464502, by decide⟩ =
    .split (coordinate 12) (![⟨464454, by decide⟩,⟨464478, by decide⟩,⟨464495, by decide⟩,⟨464501, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71205_464502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71205 ⟨464502, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71205
    ⟨464502, by decide⟩ (by decide) (![⟨464454, by decide⟩,⟨464478, by decide⟩,⟨464495, by decide⟩,⟨464501, by decide⟩]) unmarked_context_12_71205_464502 node_context_12_71205_464502
  intro a
  fin_cases a
  · exact context_13_284820_464454
  · exact context_13_284821_464478
  · exact context_13_284822_464495
  · exact context_13_284823_464501

theorem selected_cut_18112 : selected 8 ⟨464522, by decide⟩
    (prefixPartial 13 284824) = some ⟨13, 2, 0, 464522, 284824, 969, 16384⟩ := by
  decide +kernel

theorem context_13_284824_464522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284824 ⟨464522, by decide⟩ :=
  accepted_of_selected 13 284824 ⟨464522, by decide⟩ ⟨13, 2, 0, 464522, 284824, 969, 16384⟩
    (by decide) selected_cut_18112

theorem selected_cut_18113 : selected 8 ⟨464543, by decide⟩
    (prefixPartial 13 284825) = some ⟨13, 2, 0, 464543, 284825, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_284825_464543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284825 ⟨464543, by decide⟩ :=
  accepted_of_selected 13 284825 ⟨464543, by decide⟩ ⟨13, 2, 0, 464543, 284825, 1665, 16384⟩
    (by decide) selected_cut_18113

theorem selected_cut_18114 : selected 8 ⟨464560, by decide⟩
    (prefixPartial 13 284826) = some ⟨13, 2, 0, 464560, 284826, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_284826_464560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284826 ⟨464560, by decide⟩ :=
  accepted_of_selected 13 284826 ⟨464560, by decide⟩ ⟨13, 2, 0, 464560, 284826, 1309, 16384⟩
    (by decide) selected_cut_18114

theorem selected_cut_18115 : selected 8 ⟨464569, by decide⟩
    (prefixPartial 13 284827) = some ⟨13, 2, 0, 464569, 284827, 793, 16384⟩ := by
  decide +kernel

theorem context_13_284827_464569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284827 ⟨464569, by decide⟩ :=
  accepted_of_selected 13 284827 ⟨464569, by decide⟩ ⟨13, 2, 0, 464569, 284827, 793, 16384⟩
    (by decide) selected_cut_18115

theorem unmarked_context_12_71206_464570 : frontier 9 ⟨464570, by decide⟩
    (prefixCache 12 71206) (prefixPartial 12 71206) = false := by
  decide +kernel

theorem node_context_12_71206_464570 : EJMOriginalGlobalDAGData.nodes 9 ⟨464570, by decide⟩ =
    .split (coordinate 12) (![⟨464522, by decide⟩,⟨464543, by decide⟩,⟨464560, by decide⟩,⟨464569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71206_464570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71206 ⟨464570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71206
    ⟨464570, by decide⟩ (by decide) (![⟨464522, by decide⟩,⟨464543, by decide⟩,⟨464560, by decide⟩,⟨464569, by decide⟩]) unmarked_context_12_71206_464570 node_context_12_71206_464570
  intro a
  fin_cases a
  · exact context_13_284824_464522
  · exact context_13_284825_464543
  · exact context_13_284826_464560
  · exact context_13_284827_464569

theorem selected_cut_18116 : selected 8 ⟨464593, by decide⟩
    (prefixPartial 13 284828) = some ⟨13, 2, 0, 464593, 284828, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_284828_464593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284828 ⟨464593, by decide⟩ :=
  accepted_of_selected 13 284828 ⟨464593, by decide⟩ ⟨13, 2, 0, 464593, 284828, 1165, 16384⟩
    (by decide) selected_cut_18116

theorem selected_cut_18117 : selected 8 ⟨464617, by decide⟩
    (prefixPartial 13 284829) = some ⟨13, 2, 0, 464617, 284829, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_284829_464617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284829 ⟨464617, by decide⟩ :=
  accepted_of_selected 13 284829 ⟨464617, by decide⟩ ⟨13, 2, 0, 464617, 284829, 1897, 16384⟩
    (by decide) selected_cut_18117

theorem selected_cut_18118 : selected 8 ⟨464642, by decide⟩
    (prefixPartial 13 284830) = some ⟨13, 2, 0, 464642, 284830, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_284830_464642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284830 ⟨464642, by decide⟩ :=
  accepted_of_selected 13 284830 ⟨464642, by decide⟩ ⟨13, 2, 0, 464642, 284830, 1653, 16384⟩
    (by decide) selected_cut_18118

theorem selected_cut_18119 : selected 8 ⟨464650, by decide⟩
    (prefixPartial 13 284831) = some ⟨13, 2, 0, 464650, 284831, 757, 16384⟩ := by
  decide +kernel

theorem context_13_284831_464650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284831 ⟨464650, by decide⟩ :=
  accepted_of_selected 13 284831 ⟨464650, by decide⟩ ⟨13, 2, 0, 464650, 284831, 757, 16384⟩
    (by decide) selected_cut_18119

theorem unmarked_context_12_71207_464651 : frontier 9 ⟨464651, by decide⟩
    (prefixCache 12 71207) (prefixPartial 12 71207) = false := by
  decide +kernel

theorem node_context_12_71207_464651 : EJMOriginalGlobalDAGData.nodes 9 ⟨464651, by decide⟩ =
    .split (coordinate 12) (![⟨464593, by decide⟩,⟨464617, by decide⟩,⟨464642, by decide⟩,⟨464650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71207_464651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71207 ⟨464651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71207
    ⟨464651, by decide⟩ (by decide) (![⟨464593, by decide⟩,⟨464617, by decide⟩,⟨464642, by decide⟩,⟨464650, by decide⟩]) unmarked_context_12_71207_464651 node_context_12_71207_464651
  intro a
  fin_cases a
  · exact context_13_284828_464593
  · exact context_13_284829_464617
  · exact context_13_284830_464642
  · exact context_13_284831_464650

theorem unmarked_context_11_17801_464652 : frontier 10 ⟨464652, by decide⟩
    (prefixCache 11 17801) (prefixPartial 11 17801) = false := by
  decide +kernel

theorem node_context_11_17801_464652 : EJMOriginalGlobalDAGData.nodes 10 ⟨464652, by decide⟩ =
    .split (coordinate 11) (![⟨464436, by decide⟩,⟨464502, by decide⟩,⟨464570, by decide⟩,⟨464651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17801_464652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17801 ⟨464652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17801
    ⟨464652, by decide⟩ (by decide) (![⟨464436, by decide⟩,⟨464502, by decide⟩,⟨464570, by decide⟩,⟨464651, by decide⟩]) unmarked_context_11_17801_464652 node_context_11_17801_464652
  intro a
  fin_cases a
  · exact context_12_71204_464436
  · exact context_12_71205_464502
  · exact context_12_71206_464570
  · exact context_12_71207_464651

theorem selected_cut_18120 : selected 9 ⟨464720, by decide⟩
    (prefixPartial 12 71208) = some ⟨12, 2, 0, 464720, 71208, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_71208_464720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71208 ⟨464720, by decide⟩ :=
  accepted_of_selected 12 71208 ⟨464720, by decide⟩ ⟨12, 2, 0, 464720, 71208, 3481, 65536⟩
    (by decide) selected_cut_18120

theorem selected_cut_18121 : selected 8 ⟨464732, by decide⟩
    (prefixPartial 13 284836) = some ⟨13, 2, 0, 464732, 284836, 769, 16384⟩ := by
  decide +kernel

theorem context_13_284836_464732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284836 ⟨464732, by decide⟩ :=
  accepted_of_selected 13 284836 ⟨464732, by decide⟩ ⟨13, 2, 0, 464732, 284836, 769, 16384⟩
    (by decide) selected_cut_18121

theorem selected_cut_18122 : selected 8 ⟨464758, by decide⟩
    (prefixPartial 13 284837) = some ⟨13, 2, 0, 464758, 284837, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_284837_464758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284837 ⟨464758, by decide⟩ :=
  accepted_of_selected 13 284837 ⟨464758, by decide⟩ ⟨13, 2, 0, 464758, 284837, 1849, 16384⟩
    (by decide) selected_cut_18122

theorem selected_cut_18123 : selected 8 ⟨464775, by decide⟩
    (prefixPartial 13 284838) = some ⟨13, 2, 0, 464775, 284838, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_284838_464775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284838 ⟨464775, by decide⟩ :=
  accepted_of_selected 13 284838 ⟨464775, by decide⟩ ⟨13, 2, 0, 464775, 284838, 1261, 16384⟩
    (by decide) selected_cut_18123

theorem selected_cut_18124 : selected 8 ⟨464783, by decide⟩
    (prefixPartial 13 284839) = some ⟨13, 2, 0, 464783, 284839, 849, 16384⟩ := by
  decide +kernel

theorem context_13_284839_464783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284839 ⟨464783, by decide⟩ :=
  accepted_of_selected 13 284839 ⟨464783, by decide⟩ ⟨13, 2, 0, 464783, 284839, 849, 16384⟩
    (by decide) selected_cut_18124

theorem unmarked_context_12_71209_464784 : frontier 9 ⟨464784, by decide⟩
    (prefixCache 12 71209) (prefixPartial 12 71209) = false := by
  decide +kernel

theorem node_context_12_71209_464784 : EJMOriginalGlobalDAGData.nodes 9 ⟨464784, by decide⟩ =
    .split (coordinate 12) (![⟨464732, by decide⟩,⟨464758, by decide⟩,⟨464775, by decide⟩,⟨464783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71209_464784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71209 ⟨464784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71209
    ⟨464784, by decide⟩ (by decide) (![⟨464732, by decide⟩,⟨464758, by decide⟩,⟨464775, by decide⟩,⟨464783, by decide⟩]) unmarked_context_12_71209_464784 node_context_12_71209_464784
  intro a
  fin_cases a
  · exact context_13_284836_464732
  · exact context_13_284837_464758
  · exact context_13_284838_464775
  · exact context_13_284839_464783

theorem selected_cut_18125 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 71210) = some ⟨12, 1, 0, 445248, 71210, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71210_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71210 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 71210 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 71210, 1, 65536⟩
    (by decide) selected_cut_18125

theorem selected_cut_18126 : selected 8 ⟨464800, by decide⟩
    (prefixPartial 13 284844) = some ⟨13, 2, 0, 464800, 284844, 937, 16384⟩ := by
  decide +kernel

theorem context_13_284844_464800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284844 ⟨464800, by decide⟩ :=
  accepted_of_selected 13 284844 ⟨464800, by decide⟩ ⟨13, 2, 0, 464800, 284844, 937, 16384⟩
    (by decide) selected_cut_18126

theorem selected_cut_18127 : selected 8 ⟨464829, by decide⟩
    (prefixPartial 13 284845) = some ⟨13, 2, 0, 464829, 284845, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_284845_464829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284845 ⟨464829, by decide⟩ :=
  accepted_of_selected 13 284845 ⟨464829, by decide⟩ ⟨13, 2, 0, 464829, 284845, 2177, 16384⟩
    (by decide) selected_cut_18127

theorem selected_cut_18128 : selected 8 ⟨464848, by decide⟩
    (prefixPartial 13 284846) = some ⟨13, 2, 0, 464848, 284846, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_284846_464848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284846 ⟨464848, by decide⟩ :=
  accepted_of_selected 13 284846 ⟨464848, by decide⟩ ⟨13, 2, 0, 464848, 284846, 1501, 16384⟩
    (by decide) selected_cut_18128

theorem selected_cut_18129 : selected 8 ⟨464854, by decide⟩
    (prefixPartial 13 284847) = some ⟨13, 2, 0, 464854, 284847, 769, 16384⟩ := by
  decide +kernel

theorem context_13_284847_464854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284847 ⟨464854, by decide⟩ :=
  accepted_of_selected 13 284847 ⟨464854, by decide⟩ ⟨13, 2, 0, 464854, 284847, 769, 16384⟩
    (by decide) selected_cut_18129

theorem unmarked_context_12_71211_464855 : frontier 9 ⟨464855, by decide⟩
    (prefixCache 12 71211) (prefixPartial 12 71211) = false := by
  decide +kernel

theorem node_context_12_71211_464855 : EJMOriginalGlobalDAGData.nodes 9 ⟨464855, by decide⟩ =
    .split (coordinate 12) (![⟨464800, by decide⟩,⟨464829, by decide⟩,⟨464848, by decide⟩,⟨464854, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71211_464855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71211 ⟨464855, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71211
    ⟨464855, by decide⟩ (by decide) (![⟨464800, by decide⟩,⟨464829, by decide⟩,⟨464848, by decide⟩,⟨464854, by decide⟩]) unmarked_context_12_71211_464855 node_context_12_71211_464855
  intro a
  fin_cases a
  · exact context_13_284844_464800
  · exact context_13_284845_464829
  · exact context_13_284846_464848
  · exact context_13_284847_464854

theorem unmarked_context_11_17802_464856 : frontier 10 ⟨464856, by decide⟩
    (prefixCache 11 17802) (prefixPartial 11 17802) = false := by
  decide +kernel

theorem node_context_11_17802_464856 : EJMOriginalGlobalDAGData.nodes 10 ⟨464856, by decide⟩ =
    .split (coordinate 11) (![⟨464720, by decide⟩,⟨464784, by decide⟩,⟨445248, by decide⟩,⟨464855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17802_464856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17802 ⟨464856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17802
    ⟨464856, by decide⟩ (by decide) (![⟨464720, by decide⟩,⟨464784, by decide⟩,⟨445248, by decide⟩,⟨464855, by decide⟩]) unmarked_context_11_17802_464856 node_context_11_17802_464856
  intro a
  fin_cases a
  · exact context_12_71208_464720
  · exact context_12_71209_464784
  · exact context_12_71210_445248
  · exact context_12_71211_464855

theorem selected_cut_18130 : selected 8 ⟨464878, by decide⟩
    (prefixPartial 13 284848) = some ⟨13, 2, 0, 464878, 284848, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_284848_464878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284848 ⟨464878, by decide⟩ :=
  accepted_of_selected 13 284848 ⟨464878, by decide⟩ ⟨13, 2, 0, 464878, 284848, 1049, 16384⟩
    (by decide) selected_cut_18130

theorem selected_cut_18131 : selected 8 ⟨464929, by decide⟩
    (prefixPartial 13 284849) = some ⟨13, 2, 0, 464929, 284849, 3141, 16384⟩ := by
  decide +kernel

theorem context_13_284849_464929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284849 ⟨464929, by decide⟩ :=
  accepted_of_selected 13 284849 ⟨464929, by decide⟩ ⟨13, 2, 0, 464929, 284849, 3141, 16384⟩
    (by decide) selected_cut_18131

theorem selected_cut_18132 : selected 8 ⟨464966, by decide⟩
    (prefixPartial 13 284850) = some ⟨13, 2, 0, 464966, 284850, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_284850_464966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284850 ⟨464966, by decide⟩ :=
  accepted_of_selected 13 284850 ⟨464966, by decide⟩ ⟨13, 2, 0, 464966, 284850, 2149, 16384⟩
    (by decide) selected_cut_18132

theorem selected_cut_18133 : selected 8 ⟨464977, by decide⟩
    (prefixPartial 13 284851) = some ⟨13, 2, 0, 464977, 284851, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_284851_464977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284851 ⟨464977, by decide⟩ :=
  accepted_of_selected 13 284851 ⟨464977, by decide⟩ ⟨13, 2, 0, 464977, 284851, 1025, 16384⟩
    (by decide) selected_cut_18133

theorem unmarked_context_12_71212_464978 : frontier 9 ⟨464978, by decide⟩
    (prefixCache 12 71212) (prefixPartial 12 71212) = false := by
  decide +kernel

theorem node_context_12_71212_464978 : EJMOriginalGlobalDAGData.nodes 9 ⟨464978, by decide⟩ =
    .split (coordinate 12) (![⟨464878, by decide⟩,⟨464929, by decide⟩,⟨464966, by decide⟩,⟨464977, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71212_464978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71212 ⟨464978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71212
    ⟨464978, by decide⟩ (by decide) (![⟨464878, by decide⟩,⟨464929, by decide⟩,⟨464966, by decide⟩,⟨464977, by decide⟩]) unmarked_context_12_71212_464978 node_context_12_71212_464978
  intro a
  fin_cases a
  · exact context_13_284848_464878
  · exact context_13_284849_464929
  · exact context_13_284850_464966
  · exact context_13_284851_464977

theorem selected_cut_18134 : selected 8 ⟨464991, by decide⟩
    (prefixPartial 13 284852) = some ⟨13, 2, 0, 464991, 284852, 821, 16384⟩ := by
  decide +kernel

theorem context_13_284852_464991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284852 ⟨464991, by decide⟩ :=
  accepted_of_selected 13 284852 ⟨464991, by decide⟩ ⟨13, 2, 0, 464991, 284852, 821, 16384⟩
    (by decide) selected_cut_18134

theorem selected_cut_18135 : selected 8 ⟨465019, by decide⟩
    (prefixPartial 13 284853) = some ⟨13, 2, 0, 465019, 284853, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_284853_465019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284853 ⟨465019, by decide⟩ :=
  accepted_of_selected 13 284853 ⟨465019, by decide⟩ ⟨13, 2, 0, 465019, 284853, 2105, 16384⟩
    (by decide) selected_cut_18135

theorem selected_cut_18136 : selected 8 ⟨465040, by decide⟩
    (prefixPartial 13 284854) = some ⟨13, 2, 0, 465040, 284854, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_284854_465040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284854 ⟨465040, by decide⟩ :=
  accepted_of_selected 13 284854 ⟨465040, by decide⟩ ⟨13, 2, 0, 465040, 284854, 1421, 16384⟩
    (by decide) selected_cut_18136

theorem selected_cut_18137 : selected 8 ⟨465046, by decide⟩
    (prefixPartial 13 284855) = some ⟨13, 2, 0, 465046, 284855, 797, 16384⟩ := by
  decide +kernel

theorem context_13_284855_465046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284855 ⟨465046, by decide⟩ :=
  accepted_of_selected 13 284855 ⟨465046, by decide⟩ ⟨13, 2, 0, 465046, 284855, 797, 16384⟩
    (by decide) selected_cut_18137

theorem unmarked_context_12_71213_465047 : frontier 9 ⟨465047, by decide⟩
    (prefixCache 12 71213) (prefixPartial 12 71213) = false := by
  decide +kernel

theorem node_context_12_71213_465047 : EJMOriginalGlobalDAGData.nodes 9 ⟨465047, by decide⟩ =
    .split (coordinate 12) (![⟨464991, by decide⟩,⟨465019, by decide⟩,⟨465040, by decide⟩,⟨465046, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71213_465047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71213 ⟨465047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71213
    ⟨465047, by decide⟩ (by decide) (![⟨464991, by decide⟩,⟨465019, by decide⟩,⟨465040, by decide⟩,⟨465046, by decide⟩]) unmarked_context_12_71213_465047 node_context_12_71213_465047
  intro a
  fin_cases a
  · exact context_13_284852_464991
  · exact context_13_284853_465019
  · exact context_13_284854_465040
  · exact context_13_284855_465046

theorem selected_cut_18138 : selected 8 ⟨465057, by decide⟩
    (prefixPartial 13 284856) = some ⟨13, 2, 0, 465057, 284856, 685, 16384⟩ := by
  decide +kernel

theorem context_13_284856_465057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284856 ⟨465057, by decide⟩ :=
  accepted_of_selected 13 284856 ⟨465057, by decide⟩ ⟨13, 2, 0, 465057, 284856, 685, 16384⟩
    (by decide) selected_cut_18138

theorem selected_cut_18139 : selected 8 ⟨465089, by decide⟩
    (prefixPartial 13 284857) = some ⟨13, 2, 0, 465089, 284857, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_284857_465089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284857 ⟨465089, by decide⟩ :=
  accepted_of_selected 13 284857 ⟨465089, by decide⟩ ⟨13, 2, 0, 465089, 284857, 2293, 16384⟩
    (by decide) selected_cut_18139

theorem selected_cut_18140 : selected 8 ⟨465110, by decide⟩
    (prefixPartial 13 284858) = some ⟨13, 2, 0, 465110, 284858, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_284858_465110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284858 ⟨465110, by decide⟩ :=
  accepted_of_selected 13 284858 ⟨465110, by decide⟩ ⟨13, 2, 0, 465110, 284858, 1505, 16384⟩
    (by decide) selected_cut_18140

theorem selected_cut_18141 : selected 8 ⟨465116, by decide⟩
    (prefixPartial 13 284859) = some ⟨13, 2, 0, 465116, 284859, 729, 16384⟩ := by
  decide +kernel

theorem context_13_284859_465116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284859 ⟨465116, by decide⟩ :=
  accepted_of_selected 13 284859 ⟨465116, by decide⟩ ⟨13, 2, 0, 465116, 284859, 729, 16384⟩
    (by decide) selected_cut_18141

theorem unmarked_context_12_71214_465117 : frontier 9 ⟨465117, by decide⟩
    (prefixCache 12 71214) (prefixPartial 12 71214) = false := by
  decide +kernel

theorem node_context_12_71214_465117 : EJMOriginalGlobalDAGData.nodes 9 ⟨465117, by decide⟩ =
    .split (coordinate 12) (![⟨465057, by decide⟩,⟨465089, by decide⟩,⟨465110, by decide⟩,⟨465116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71214_465117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71214 ⟨465117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71214
    ⟨465117, by decide⟩ (by decide) (![⟨465057, by decide⟩,⟨465089, by decide⟩,⟨465110, by decide⟩,⟨465116, by decide⟩]) unmarked_context_12_71214_465117 node_context_12_71214_465117
  intro a
  fin_cases a
  · exact context_13_284856_465057
  · exact context_13_284857_465089
  · exact context_13_284858_465110
  · exact context_13_284859_465116

theorem selected_cut_18142 : selected 8 ⟨465134, by decide⟩
    (prefixPartial 13 284860) = some ⟨13, 2, 0, 465134, 284860, 877, 16384⟩ := by
  decide +kernel

theorem context_13_284860_465134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284860 ⟨465134, by decide⟩ :=
  accepted_of_selected 13 284860 ⟨465134, by decide⟩ ⟨13, 2, 0, 465134, 284860, 877, 16384⟩
    (by decide) selected_cut_18142

theorem selected_cut_18143 : selected 8 ⟨465164, by decide⟩
    (prefixPartial 13 284861) = some ⟨13, 2, 0, 465164, 284861, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_284861_465164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284861 ⟨465164, by decide⟩ :=
  accepted_of_selected 13 284861 ⟨465164, by decide⟩ ⟨13, 2, 0, 465164, 284861, 2521, 16384⟩
    (by decide) selected_cut_18143

theorem selected_cut_18144 : selected 8 ⟨465188, by decide⟩
    (prefixPartial 13 284862) = some ⟨13, 2, 0, 465188, 284862, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_284862_465188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284862 ⟨465188, by decide⟩ :=
  accepted_of_selected 13 284862 ⟨465188, by decide⟩ ⟨13, 2, 0, 465188, 284862, 1793, 16384⟩
    (by decide) selected_cut_18144

theorem selected_cut_18145 : selected 8 ⟨465194, by decide⟩
    (prefixPartial 13 284863) = some ⟨13, 2, 0, 465194, 284863, 741, 16384⟩ := by
  decide +kernel

theorem context_13_284863_465194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284863 ⟨465194, by decide⟩ :=
  accepted_of_selected 13 284863 ⟨465194, by decide⟩ ⟨13, 2, 0, 465194, 284863, 741, 16384⟩
    (by decide) selected_cut_18145

theorem unmarked_context_12_71215_465195 : frontier 9 ⟨465195, by decide⟩
    (prefixCache 12 71215) (prefixPartial 12 71215) = false := by
  decide +kernel

theorem node_context_12_71215_465195 : EJMOriginalGlobalDAGData.nodes 9 ⟨465195, by decide⟩ =
    .split (coordinate 12) (![⟨465134, by decide⟩,⟨465164, by decide⟩,⟨465188, by decide⟩,⟨465194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71215_465195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71215 ⟨465195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71215
    ⟨465195, by decide⟩ (by decide) (![⟨465134, by decide⟩,⟨465164, by decide⟩,⟨465188, by decide⟩,⟨465194, by decide⟩]) unmarked_context_12_71215_465195 node_context_12_71215_465195
  intro a
  fin_cases a
  · exact context_13_284860_465134
  · exact context_13_284861_465164
  · exact context_13_284862_465188
  · exact context_13_284863_465194

theorem unmarked_context_11_17803_465196 : frontier 10 ⟨465196, by decide⟩
    (prefixCache 11 17803) (prefixPartial 11 17803) = false := by
  decide +kernel

theorem node_context_11_17803_465196 : EJMOriginalGlobalDAGData.nodes 10 ⟨465196, by decide⟩ =
    .split (coordinate 11) (![⟨464978, by decide⟩,⟨465047, by decide⟩,⟨465117, by decide⟩,⟨465195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17803_465196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17803 ⟨465196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17803
    ⟨465196, by decide⟩ (by decide) (![⟨464978, by decide⟩,⟨465047, by decide⟩,⟨465117, by decide⟩,⟨465195, by decide⟩]) unmarked_context_11_17803_465196 node_context_11_17803_465196
  intro a
  fin_cases a
  · exact context_12_71212_464978
  · exact context_12_71213_465047
  · exact context_12_71214_465117
  · exact context_12_71215_465195

theorem unmarked_context_10_4450_465197 : frontier 11 ⟨465197, by decide⟩
    (prefixCache 10 4450) (prefixPartial 10 4450) = false := by
  decide +kernel

theorem node_context_10_4450_465197 : EJMOriginalGlobalDAGData.nodes 11 ⟨465197, by decide⟩ =
    .split (coordinate 10) (![⟨464316, by decide⟩,⟨464652, by decide⟩,⟨464856, by decide⟩,⟨465196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4450_465197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4450 ⟨465197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4450
    ⟨465197, by decide⟩ (by decide) (![⟨464316, by decide⟩,⟨464652, by decide⟩,⟨464856, by decide⟩,⟨465196, by decide⟩]) unmarked_context_10_4450_465197 node_context_10_4450_465197
  intro a
  fin_cases a
  · exact context_11_17800_464316
  · exact context_11_17801_464652
  · exact context_11_17802_464856
  · exact context_11_17803_465196

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
