/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover283
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_5714_689583 : frontier 11 ⟨689583, by decide⟩
    (prefixCache 10 5714) (prefixPartial 10 5714) = false := by
  decide +kernel

theorem node_context_10_5714_689583 : EJMOriginalGlobalDAGData.nodes 11 ⟨689583, by decide⟩ =
    .split (coordinate 10) (![⟨688840, by decide⟩,⟨689033, by decide⟩,⟨689310, by decide⟩,⟨689582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5714_689583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5714 ⟨689583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5714
    ⟨689583, by decide⟩ (by decide) (![⟨688840, by decide⟩,⟨689033, by decide⟩,⟨689310, by decide⟩,⟨689582, by decide⟩]) unmarked_context_10_5714_689583 node_context_10_5714_689583
  intro a
  fin_cases a
  · exact context_11_22856_688840
  · exact context_11_22857_689033
  · exact context_11_22858_689310
  · exact context_11_22859_689582

theorem selected_cut_27267 : selected 8 ⟨689598, by decide⟩
    (prefixPartial 13 365760) = some ⟨13, 2, 0, 689598, 365760, 825, 16384⟩ := by
  decide +kernel

theorem context_13_365760_689598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365760 ⟨689598, by decide⟩ :=
  accepted_of_selected 13 365760 ⟨689598, by decide⟩ ⟨13, 2, 0, 689598, 365760, 825, 16384⟩
    (by decide) selected_cut_27267

theorem selected_cut_27268 : selected 8 ⟨689625, by decide⟩
    (prefixPartial 13 365761) = some ⟨13, 2, 0, 689625, 365761, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_365761_689625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365761 ⟨689625, by decide⟩ :=
  accepted_of_selected 13 365761 ⟨689625, by decide⟩ ⟨13, 2, 0, 689625, 365761, 1569, 16384⟩
    (by decide) selected_cut_27268

theorem selected_cut_27269 : selected 8 ⟨689644, by decide⟩
    (prefixPartial 13 365762) = some ⟨13, 2, 0, 689644, 365762, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_365762_689644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365762 ⟨689644, by decide⟩ :=
  accepted_of_selected 13 365762 ⟨689644, by decide⟩ ⟨13, 2, 0, 689644, 365762, 1665, 16384⟩
    (by decide) selected_cut_27269

theorem selected_cut_27270 : selected 8 ⟨689652, by decide⟩
    (prefixPartial 13 365763) = some ⟨13, 2, 0, 689652, 365763, 933, 16384⟩ := by
  decide +kernel

theorem context_13_365763_689652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365763 ⟨689652, by decide⟩ :=
  accepted_of_selected 13 365763 ⟨689652, by decide⟩ ⟨13, 2, 0, 689652, 365763, 933, 16384⟩
    (by decide) selected_cut_27270

theorem unmarked_context_12_91440_689653 : frontier 9 ⟨689653, by decide⟩
    (prefixCache 12 91440) (prefixPartial 12 91440) = false := by
  decide +kernel

theorem node_context_12_91440_689653 : EJMOriginalGlobalDAGData.nodes 9 ⟨689653, by decide⟩ =
    .split (coordinate 12) (![⟨689598, by decide⟩,⟨689625, by decide⟩,⟨689644, by decide⟩,⟨689652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91440_689653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91440 ⟨689653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91440
    ⟨689653, by decide⟩ (by decide) (![⟨689598, by decide⟩,⟨689625, by decide⟩,⟨689644, by decide⟩,⟨689652, by decide⟩]) unmarked_context_12_91440_689653 node_context_12_91440_689653
  intro a
  fin_cases a
  · exact context_13_365760_689598
  · exact context_13_365761_689625
  · exact context_13_365762_689644
  · exact context_13_365763_689652

theorem selected_cut_27271 : selected 8 ⟨689667, by decide⟩
    (prefixPartial 13 365764) = some ⟨13, 2, 0, 689667, 365764, 853, 16384⟩ := by
  decide +kernel

theorem context_13_365764_689667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365764 ⟨689667, by decide⟩ :=
  accepted_of_selected 13 365764 ⟨689667, by decide⟩ ⟨13, 2, 0, 689667, 365764, 853, 16384⟩
    (by decide) selected_cut_27271

theorem selected_cut_27272 : selected 8 ⟨689700, by decide⟩
    (prefixPartial 13 365765) = some ⟨13, 2, 0, 689700, 365765, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_365765_689700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365765 ⟨689700, by decide⟩ :=
  accepted_of_selected 13 365765 ⟨689700, by decide⟩ ⟨13, 2, 0, 689700, 365765, 1641, 16384⟩
    (by decide) selected_cut_27272

theorem selected_cut_27273 : selected 8 ⟨689719, by decide⟩
    (prefixPartial 13 365766) = some ⟨13, 2, 0, 689719, 365766, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_365766_689719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365766 ⟨689719, by decide⟩ :=
  accepted_of_selected 13 365766 ⟨689719, by decide⟩ ⟨13, 2, 0, 689719, 365766, 1501, 16384⟩
    (by decide) selected_cut_27273

theorem selected_cut_27274 : selected 8 ⟨689726, by decide⟩
    (prefixPartial 13 365767) = some ⟨13, 2, 0, 689726, 365767, 797, 16384⟩ := by
  decide +kernel

theorem context_13_365767_689726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365767 ⟨689726, by decide⟩ :=
  accepted_of_selected 13 365767 ⟨689726, by decide⟩ ⟨13, 2, 0, 689726, 365767, 797, 16384⟩
    (by decide) selected_cut_27274

theorem unmarked_context_12_91441_689727 : frontier 9 ⟨689727, by decide⟩
    (prefixCache 12 91441) (prefixPartial 12 91441) = false := by
  decide +kernel

theorem node_context_12_91441_689727 : EJMOriginalGlobalDAGData.nodes 9 ⟨689727, by decide⟩ =
    .split (coordinate 12) (![⟨689667, by decide⟩,⟨689700, by decide⟩,⟨689719, by decide⟩,⟨689726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91441_689727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91441 ⟨689727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91441
    ⟨689727, by decide⟩ (by decide) (![⟨689667, by decide⟩,⟨689700, by decide⟩,⟨689719, by decide⟩,⟨689726, by decide⟩]) unmarked_context_12_91441_689727 node_context_12_91441_689727
  intro a
  fin_cases a
  · exact context_13_365764_689667
  · exact context_13_365765_689700
  · exact context_13_365766_689719
  · exact context_13_365767_689726

theorem selected_cut_27275 : selected 8 ⟨689743, by decide⟩
    (prefixPartial 13 365768) = some ⟨13, 2, 0, 689743, 365768, 853, 16384⟩ := by
  decide +kernel

theorem context_13_365768_689743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365768 ⟨689743, by decide⟩ :=
  accepted_of_selected 13 365768 ⟨689743, by decide⟩ ⟨13, 2, 0, 689743, 365768, 853, 16384⟩
    (by decide) selected_cut_27275

theorem selected_cut_27276 : selected 8 ⟨689778, by decide⟩
    (prefixPartial 13 365769) = some ⟨13, 2, 0, 689778, 365769, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_365769_689778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365769 ⟨689778, by decide⟩ :=
  accepted_of_selected 13 365769 ⟨689778, by decide⟩ ⟨13, 2, 0, 689778, 365769, 1737, 16384⟩
    (by decide) selected_cut_27276

theorem selected_cut_27277 : selected 8 ⟨689798, by decide⟩
    (prefixPartial 13 365770) = some ⟨13, 2, 0, 689798, 365770, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_365770_689798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365770 ⟨689798, by decide⟩ :=
  accepted_of_selected 13 365770 ⟨689798, by decide⟩ ⟨13, 2, 0, 689798, 365770, 1661, 16384⟩
    (by decide) selected_cut_27277

theorem selected_cut_27278 : selected 8 ⟨689810, by decide⟩
    (prefixPartial 13 365771) = some ⟨13, 2, 0, 689810, 365771, 985, 16384⟩ := by
  decide +kernel

theorem context_13_365771_689810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365771 ⟨689810, by decide⟩ :=
  accepted_of_selected 13 365771 ⟨689810, by decide⟩ ⟨13, 2, 0, 689810, 365771, 985, 16384⟩
    (by decide) selected_cut_27278

theorem unmarked_context_12_91442_689811 : frontier 9 ⟨689811, by decide⟩
    (prefixCache 12 91442) (prefixPartial 12 91442) = false := by
  decide +kernel

theorem node_context_12_91442_689811 : EJMOriginalGlobalDAGData.nodes 9 ⟨689811, by decide⟩ =
    .split (coordinate 12) (![⟨689743, by decide⟩,⟨689778, by decide⟩,⟨689798, by decide⟩,⟨689810, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91442_689811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91442 ⟨689811, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91442
    ⟨689811, by decide⟩ (by decide) (![⟨689743, by decide⟩,⟨689778, by decide⟩,⟨689798, by decide⟩,⟨689810, by decide⟩]) unmarked_context_12_91442_689811 node_context_12_91442_689811
  intro a
  fin_cases a
  · exact context_13_365768_689743
  · exact context_13_365769_689778
  · exact context_13_365770_689798
  · exact context_13_365771_689810

theorem selected_cut_27279 : selected 8 ⟨689827, by decide⟩
    (prefixPartial 13 365772) = some ⟨13, 2, 0, 689827, 365772, 861, 16384⟩ := by
  decide +kernel

theorem context_13_365772_689827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365772 ⟨689827, by decide⟩ :=
  accepted_of_selected 13 365772 ⟨689827, by decide⟩ ⟨13, 2, 0, 689827, 365772, 861, 16384⟩
    (by decide) selected_cut_27279

theorem selected_cut_27280 : selected 8 ⟨689863, by decide⟩
    (prefixPartial 13 365773) = some ⟨13, 2, 0, 689863, 365773, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_365773_689863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365773 ⟨689863, by decide⟩ :=
  accepted_of_selected 13 365773 ⟨689863, by decide⟩ ⟨13, 2, 0, 689863, 365773, 2257, 16384⟩
    (by decide) selected_cut_27280

theorem selected_cut_27281 : selected 8 ⟨689887, by decide⟩
    (prefixPartial 13 365774) = some ⟨13, 2, 0, 689887, 365774, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_365774_689887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365774 ⟨689887, by decide⟩ :=
  accepted_of_selected 13 365774 ⟨689887, by decide⟩ ⟨13, 2, 0, 689887, 365774, 1845, 16384⟩
    (by decide) selected_cut_27281

theorem selected_cut_27282 : selected 8 ⟨689901, by decide⟩
    (prefixPartial 13 365775) = some ⟨13, 2, 0, 689901, 365775, 977, 16384⟩ := by
  decide +kernel

theorem context_13_365775_689901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365775 ⟨689901, by decide⟩ :=
  accepted_of_selected 13 365775 ⟨689901, by decide⟩ ⟨13, 2, 0, 689901, 365775, 977, 16384⟩
    (by decide) selected_cut_27282

theorem unmarked_context_12_91443_689902 : frontier 9 ⟨689902, by decide⟩
    (prefixCache 12 91443) (prefixPartial 12 91443) = false := by
  decide +kernel

theorem node_context_12_91443_689902 : EJMOriginalGlobalDAGData.nodes 9 ⟨689902, by decide⟩ =
    .split (coordinate 12) (![⟨689827, by decide⟩,⟨689863, by decide⟩,⟨689887, by decide⟩,⟨689901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91443_689902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91443 ⟨689902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91443
    ⟨689902, by decide⟩ (by decide) (![⟨689827, by decide⟩,⟨689863, by decide⟩,⟨689887, by decide⟩,⟨689901, by decide⟩]) unmarked_context_12_91443_689902 node_context_12_91443_689902
  intro a
  fin_cases a
  · exact context_13_365772_689827
  · exact context_13_365773_689863
  · exact context_13_365774_689887
  · exact context_13_365775_689901

theorem unmarked_context_11_22860_689903 : frontier 10 ⟨689903, by decide⟩
    (prefixCache 11 22860) (prefixPartial 11 22860) = false := by
  decide +kernel

theorem node_context_11_22860_689903 : EJMOriginalGlobalDAGData.nodes 10 ⟨689903, by decide⟩ =
    .split (coordinate 11) (![⟨689653, by decide⟩,⟨689727, by decide⟩,⟨689811, by decide⟩,⟨689902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22860_689903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22860 ⟨689903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22860
    ⟨689903, by decide⟩ (by decide) (![⟨689653, by decide⟩,⟨689727, by decide⟩,⟨689811, by decide⟩,⟨689902, by decide⟩]) unmarked_context_11_22860_689903 node_context_11_22860_689903
  intro a
  fin_cases a
  · exact context_12_91440_689653
  · exact context_12_91441_689727
  · exact context_12_91442_689811
  · exact context_12_91443_689902

theorem selected_cut_27283 : selected 9 ⟨689955, by decide⟩
    (prefixPartial 12 91444) = some ⟨12, 2, 0, 689955, 91444, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_91444_689955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91444 ⟨689955, by decide⟩ :=
  accepted_of_selected 12 91444 ⟨689955, by decide⟩ ⟨12, 2, 0, 689955, 91444, 3917, 65536⟩
    (by decide) selected_cut_27283

theorem selected_cut_27284 : selected 9 ⟨689956, by decide⟩
    (prefixPartial 12 91445) = some ⟨12, 1, 0, 689956, 91445, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91445_689956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91445 ⟨689956, by decide⟩ :=
  accepted_of_selected 12 91445 ⟨689956, by decide⟩ ⟨12, 1, 0, 689956, 91445, 1, 65536⟩
    (by decide) selected_cut_27284

theorem selected_cut_27285 : selected 9 ⟨690012, by decide⟩
    (prefixPartial 12 91446) = some ⟨12, 2, 0, 690012, 91446, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_91446_690012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91446 ⟨690012, by decide⟩ :=
  accepted_of_selected 12 91446 ⟨690012, by decide⟩ ⟨12, 2, 0, 690012, 91446, 3893, 65536⟩
    (by decide) selected_cut_27285

theorem selected_cut_27286 : selected 8 ⟨690022, by decide⟩
    (prefixPartial 13 365788) = some ⟨13, 2, 0, 690022, 365788, 505, 16384⟩ := by
  decide +kernel

theorem context_13_365788_690022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365788 ⟨690022, by decide⟩ :=
  accepted_of_selected 13 365788 ⟨690022, by decide⟩ ⟨13, 2, 0, 690022, 365788, 505, 16384⟩
    (by decide) selected_cut_27286

theorem selected_cut_27287 : selected 8 ⟨690048, by decide⟩
    (prefixPartial 13 365789) = some ⟨13, 2, 0, 690048, 365789, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_365789_690048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365789 ⟨690048, by decide⟩ :=
  accepted_of_selected 13 365789 ⟨690048, by decide⟩ ⟨13, 2, 0, 690048, 365789, 1857, 16384⟩
    (by decide) selected_cut_27287

theorem selected_cut_27288 : selected 8 ⟨690068, by decide⟩
    (prefixPartial 13 365790) = some ⟨13, 2, 0, 690068, 365790, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_365790_690068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365790 ⟨690068, by decide⟩ :=
  accepted_of_selected 13 365790 ⟨690068, by decide⟩ ⟨13, 2, 0, 690068, 365790, 1437, 16384⟩
    (by decide) selected_cut_27288

theorem selected_cut_27289 : selected 8 ⟨690074, by decide⟩
    (prefixPartial 13 365791) = some ⟨13, 2, 0, 690074, 365791, 713, 16384⟩ := by
  decide +kernel

theorem context_13_365791_690074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365791 ⟨690074, by decide⟩ :=
  accepted_of_selected 13 365791 ⟨690074, by decide⟩ ⟨13, 2, 0, 690074, 365791, 713, 16384⟩
    (by decide) selected_cut_27289

theorem unmarked_context_12_91447_690075 : frontier 9 ⟨690075, by decide⟩
    (prefixCache 12 91447) (prefixPartial 12 91447) = false := by
  decide +kernel

theorem node_context_12_91447_690075 : EJMOriginalGlobalDAGData.nodes 9 ⟨690075, by decide⟩ =
    .split (coordinate 12) (![⟨690022, by decide⟩,⟨690048, by decide⟩,⟨690068, by decide⟩,⟨690074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91447_690075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91447 ⟨690075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91447
    ⟨690075, by decide⟩ (by decide) (![⟨690022, by decide⟩,⟨690048, by decide⟩,⟨690068, by decide⟩,⟨690074, by decide⟩]) unmarked_context_12_91447_690075 node_context_12_91447_690075
  intro a
  fin_cases a
  · exact context_13_365788_690022
  · exact context_13_365789_690048
  · exact context_13_365790_690068
  · exact context_13_365791_690074

theorem unmarked_context_11_22861_690076 : frontier 10 ⟨690076, by decide⟩
    (prefixCache 11 22861) (prefixPartial 11 22861) = false := by
  decide +kernel

theorem node_context_11_22861_690076 : EJMOriginalGlobalDAGData.nodes 10 ⟨690076, by decide⟩ =
    .split (coordinate 11) (![⟨689955, by decide⟩,⟨689956, by decide⟩,⟨690012, by decide⟩,⟨690075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22861_690076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22861 ⟨690076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22861
    ⟨690076, by decide⟩ (by decide) (![⟨689955, by decide⟩,⟨689956, by decide⟩,⟨690012, by decide⟩,⟨690075, by decide⟩]) unmarked_context_11_22861_690076 node_context_11_22861_690076
  intro a
  fin_cases a
  · exact context_12_91444_689955
  · exact context_12_91445_689956
  · exact context_12_91446_690012
  · exact context_12_91447_690075

theorem selected_cut_27290 : selected 8 ⟨690085, by decide⟩
    (prefixPartial 13 365792) = some ⟨13, 2, 0, 690085, 365792, 501, 16384⟩ := by
  decide +kernel

theorem context_13_365792_690085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365792 ⟨690085, by decide⟩ :=
  accepted_of_selected 13 365792 ⟨690085, by decide⟩ ⟨13, 2, 0, 690085, 365792, 501, 16384⟩
    (by decide) selected_cut_27290

theorem selected_cut_27291 : selected 8 ⟨690107, by decide⟩
    (prefixPartial 13 365793) = some ⟨13, 2, 0, 690107, 365793, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_365793_690107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365793 ⟨690107, by decide⟩ :=
  accepted_of_selected 13 365793 ⟨690107, by decide⟩ ⟨13, 2, 0, 690107, 365793, 1861, 16384⟩
    (by decide) selected_cut_27291

theorem selected_cut_27292 : selected 8 ⟨690125, by decide⟩
    (prefixPartial 13 365794) = some ⟨13, 2, 0, 690125, 365794, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_365794_690125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365794 ⟨690125, by decide⟩ :=
  accepted_of_selected 13 365794 ⟨690125, by decide⟩ ⟨13, 2, 0, 690125, 365794, 1741, 16384⟩
    (by decide) selected_cut_27292

theorem selected_cut_27293 : selected 8 ⟨690132, by decide⟩
    (prefixPartial 13 365795) = some ⟨13, 2, 0, 690132, 365795, 949, 16384⟩ := by
  decide +kernel

theorem context_13_365795_690132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365795 ⟨690132, by decide⟩ :=
  accepted_of_selected 13 365795 ⟨690132, by decide⟩ ⟨13, 2, 0, 690132, 365795, 949, 16384⟩
    (by decide) selected_cut_27293

theorem unmarked_context_12_91448_690133 : frontier 9 ⟨690133, by decide⟩
    (prefixCache 12 91448) (prefixPartial 12 91448) = false := by
  decide +kernel

theorem node_context_12_91448_690133 : EJMOriginalGlobalDAGData.nodes 9 ⟨690133, by decide⟩ =
    .split (coordinate 12) (![⟨690085, by decide⟩,⟨690107, by decide⟩,⟨690125, by decide⟩,⟨690132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91448_690133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91448 ⟨690133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91448
    ⟨690133, by decide⟩ (by decide) (![⟨690085, by decide⟩,⟨690107, by decide⟩,⟨690125, by decide⟩,⟨690132, by decide⟩]) unmarked_context_12_91448_690133 node_context_12_91448_690133
  intro a
  fin_cases a
  · exact context_13_365792_690085
  · exact context_13_365793_690107
  · exact context_13_365794_690125
  · exact context_13_365795_690132

theorem selected_cut_27294 : selected 8 ⟨690145, by decide⟩
    (prefixPartial 13 365796) = some ⟨13, 2, 0, 690145, 365796, 561, 16384⟩ := by
  decide +kernel

theorem context_13_365796_690145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365796 ⟨690145, by decide⟩ :=
  accepted_of_selected 13 365796 ⟨690145, by decide⟩ ⟨13, 2, 0, 690145, 365796, 561, 16384⟩
    (by decide) selected_cut_27294

theorem selected_cut_27295 : selected 8 ⟨690170, by decide⟩
    (prefixPartial 13 365797) = some ⟨13, 2, 0, 690170, 365797, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_365797_690170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365797 ⟨690170, by decide⟩ :=
  accepted_of_selected 13 365797 ⟨690170, by decide⟩ ⟨13, 2, 0, 690170, 365797, 1765, 16384⟩
    (by decide) selected_cut_27295

theorem selected_cut_27296 : selected 8 ⟨690188, by decide⟩
    (prefixPartial 13 365798) = some ⟨13, 2, 0, 690188, 365798, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_365798_690188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365798 ⟨690188, by decide⟩ :=
  accepted_of_selected 13 365798 ⟨690188, by decide⟩ ⟨13, 2, 0, 690188, 365798, 1637, 16384⟩
    (by decide) selected_cut_27296

theorem selected_cut_27297 : selected 8 ⟨690195, by decide⟩
    (prefixPartial 13 365799) = some ⟨13, 2, 0, 690195, 365799, 825, 16384⟩ := by
  decide +kernel

theorem context_13_365799_690195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365799 ⟨690195, by decide⟩ :=
  accepted_of_selected 13 365799 ⟨690195, by decide⟩ ⟨13, 2, 0, 690195, 365799, 825, 16384⟩
    (by decide) selected_cut_27297

theorem unmarked_context_12_91449_690196 : frontier 9 ⟨690196, by decide⟩
    (prefixCache 12 91449) (prefixPartial 12 91449) = false := by
  decide +kernel

theorem node_context_12_91449_690196 : EJMOriginalGlobalDAGData.nodes 9 ⟨690196, by decide⟩ =
    .split (coordinate 12) (![⟨690145, by decide⟩,⟨690170, by decide⟩,⟨690188, by decide⟩,⟨690195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91449_690196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91449 ⟨690196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91449
    ⟨690196, by decide⟩ (by decide) (![⟨690145, by decide⟩,⟨690170, by decide⟩,⟨690188, by decide⟩,⟨690195, by decide⟩]) unmarked_context_12_91449_690196 node_context_12_91449_690196
  intro a
  fin_cases a
  · exact context_13_365796_690145
  · exact context_13_365797_690170
  · exact context_13_365798_690188
  · exact context_13_365799_690195

theorem selected_cut_27298 : selected 8 ⟨690205, by decide⟩
    (prefixPartial 13 365800) = some ⟨13, 2, 0, 690205, 365800, 437, 16384⟩ := by
  decide +kernel

theorem context_13_365800_690205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365800 ⟨690205, by decide⟩ :=
  accepted_of_selected 13 365800 ⟨690205, by decide⟩ ⟨13, 2, 0, 690205, 365800, 437, 16384⟩
    (by decide) selected_cut_27298

theorem selected_cut_27299 : selected 8 ⟨690230, by decide⟩
    (prefixPartial 13 365801) = some ⟨13, 2, 0, 690230, 365801, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_365801_690230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365801 ⟨690230, by decide⟩ :=
  accepted_of_selected 13 365801 ⟨690230, by decide⟩ ⟨13, 2, 0, 690230, 365801, 1789, 16384⟩
    (by decide) selected_cut_27299

theorem selected_cut_27300 : selected 8 ⟨690247, by decide⟩
    (prefixPartial 13 365802) = some ⟨13, 2, 0, 690247, 365802, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_365802_690247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365802 ⟨690247, by decide⟩ :=
  accepted_of_selected 13 365802 ⟨690247, by decide⟩ ⟨13, 2, 0, 690247, 365802, 1541, 16384⟩
    (by decide) selected_cut_27300

theorem selected_cut_27301 : selected 8 ⟨690255, by decide⟩
    (prefixPartial 13 365803) = some ⟨13, 2, 0, 690255, 365803, 933, 16384⟩ := by
  decide +kernel

theorem context_13_365803_690255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365803 ⟨690255, by decide⟩ :=
  accepted_of_selected 13 365803 ⟨690255, by decide⟩ ⟨13, 2, 0, 690255, 365803, 933, 16384⟩
    (by decide) selected_cut_27301

theorem unmarked_context_12_91450_690256 : frontier 9 ⟨690256, by decide⟩
    (prefixCache 12 91450) (prefixPartial 12 91450) = false := by
  decide +kernel

theorem node_context_12_91450_690256 : EJMOriginalGlobalDAGData.nodes 9 ⟨690256, by decide⟩ =
    .split (coordinate 12) (![⟨690205, by decide⟩,⟨690230, by decide⟩,⟨690247, by decide⟩,⟨690255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91450_690256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91450 ⟨690256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91450
    ⟨690256, by decide⟩ (by decide) (![⟨690205, by decide⟩,⟨690230, by decide⟩,⟨690247, by decide⟩,⟨690255, by decide⟩]) unmarked_context_12_91450_690256 node_context_12_91450_690256
  intro a
  fin_cases a
  · exact context_13_365800_690205
  · exact context_13_365801_690230
  · exact context_13_365802_690247
  · exact context_13_365803_690255

theorem selected_cut_27302 : selected 8 ⟨690264, by decide⟩
    (prefixPartial 13 365804) = some ⟨13, 2, 0, 690264, 365804, 369, 16384⟩ := by
  decide +kernel

theorem context_13_365804_690264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365804 ⟨690264, by decide⟩ :=
  accepted_of_selected 13 365804 ⟨690264, by decide⟩ ⟨13, 2, 0, 690264, 365804, 369, 16384⟩
    (by decide) selected_cut_27302

theorem selected_cut_27303 : selected 8 ⟨690296, by decide⟩
    (prefixPartial 13 365805) = some ⟨13, 2, 0, 690296, 365805, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_365805_690296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365805 ⟨690296, by decide⟩ :=
  accepted_of_selected 13 365805 ⟨690296, by decide⟩ ⟨13, 2, 0, 690296, 365805, 2373, 16384⟩
    (by decide) selected_cut_27303

theorem selected_cut_27304 : selected 8 ⟨690316, by decide⟩
    (prefixPartial 13 365806) = some ⟨13, 2, 0, 690316, 365806, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_365806_690316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365806 ⟨690316, by decide⟩ :=
  accepted_of_selected 13 365806 ⟨690316, by decide⟩ ⟨13, 2, 0, 690316, 365806, 1805, 16384⟩
    (by decide) selected_cut_27304

theorem selected_cut_27305 : selected 8 ⟨690326, by decide⟩
    (prefixPartial 13 365807) = some ⟨13, 2, 0, 690326, 365807, 857, 16384⟩ := by
  decide +kernel

theorem context_13_365807_690326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365807 ⟨690326, by decide⟩ :=
  accepted_of_selected 13 365807 ⟨690326, by decide⟩ ⟨13, 2, 0, 690326, 365807, 857, 16384⟩
    (by decide) selected_cut_27305

theorem unmarked_context_12_91451_690327 : frontier 9 ⟨690327, by decide⟩
    (prefixCache 12 91451) (prefixPartial 12 91451) = false := by
  decide +kernel

theorem node_context_12_91451_690327 : EJMOriginalGlobalDAGData.nodes 9 ⟨690327, by decide⟩ =
    .split (coordinate 12) (![⟨690264, by decide⟩,⟨690296, by decide⟩,⟨690316, by decide⟩,⟨690326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91451_690327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91451 ⟨690327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91451
    ⟨690327, by decide⟩ (by decide) (![⟨690264, by decide⟩,⟨690296, by decide⟩,⟨690316, by decide⟩,⟨690326, by decide⟩]) unmarked_context_12_91451_690327 node_context_12_91451_690327
  intro a
  fin_cases a
  · exact context_13_365804_690264
  · exact context_13_365805_690296
  · exact context_13_365806_690316
  · exact context_13_365807_690326

theorem unmarked_context_11_22862_690328 : frontier 10 ⟨690328, by decide⟩
    (prefixCache 11 22862) (prefixPartial 11 22862) = false := by
  decide +kernel

theorem node_context_11_22862_690328 : EJMOriginalGlobalDAGData.nodes 10 ⟨690328, by decide⟩ =
    .split (coordinate 11) (![⟨690133, by decide⟩,⟨690196, by decide⟩,⟨690256, by decide⟩,⟨690327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22862_690328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22862 ⟨690328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22862
    ⟨690328, by decide⟩ (by decide) (![⟨690133, by decide⟩,⟨690196, by decide⟩,⟨690256, by decide⟩,⟨690327, by decide⟩]) unmarked_context_11_22862_690328 node_context_11_22862_690328
  intro a
  fin_cases a
  · exact context_12_91448_690133
  · exact context_12_91449_690196
  · exact context_12_91450_690256
  · exact context_12_91451_690327

theorem selected_cut_27306 : selected 8 ⟨690332, by decide⟩
    (prefixPartial 13 365808) = some ⟨13, 2, 0, 690332, 365808, 173, 16384⟩ := by
  decide +kernel

theorem context_13_365808_690332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365808 ⟨690332, by decide⟩ :=
  accepted_of_selected 13 365808 ⟨690332, by decide⟩ ⟨13, 2, 0, 690332, 365808, 173, 16384⟩
    (by decide) selected_cut_27306

theorem selected_cut_27307 : selected 8 ⟨690354, by decide⟩
    (prefixPartial 13 365809) = some ⟨13, 2, 0, 690354, 365809, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_365809_690354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365809 ⟨690354, by decide⟩ :=
  accepted_of_selected 13 365809 ⟨690354, by decide⟩ ⟨13, 2, 0, 690354, 365809, 1913, 16384⟩
    (by decide) selected_cut_27307

theorem selected_cut_27308 : selected 8 ⟨690372, by decide⟩
    (prefixPartial 13 365810) = some ⟨13, 2, 0, 690372, 365810, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_365810_690372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365810 ⟨690372, by decide⟩ :=
  accepted_of_selected 13 365810 ⟨690372, by decide⟩ ⟨13, 2, 0, 690372, 365810, 1501, 16384⟩
    (by decide) selected_cut_27308

theorem selected_cut_27309 : selected 8 ⟨690379, by decide⟩
    (prefixPartial 13 365811) = some ⟨13, 2, 0, 690379, 365811, 969, 16384⟩ := by
  decide +kernel

theorem context_13_365811_690379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365811 ⟨690379, by decide⟩ :=
  accepted_of_selected 13 365811 ⟨690379, by decide⟩ ⟨13, 2, 0, 690379, 365811, 969, 16384⟩
    (by decide) selected_cut_27309

theorem unmarked_context_12_91452_690380 : frontier 9 ⟨690380, by decide⟩
    (prefixCache 12 91452) (prefixPartial 12 91452) = false := by
  decide +kernel

theorem node_context_12_91452_690380 : EJMOriginalGlobalDAGData.nodes 9 ⟨690380, by decide⟩ =
    .split (coordinate 12) (![⟨690332, by decide⟩,⟨690354, by decide⟩,⟨690372, by decide⟩,⟨690379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91452_690380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91452 ⟨690380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91452
    ⟨690380, by decide⟩ (by decide) (![⟨690332, by decide⟩,⟨690354, by decide⟩,⟨690372, by decide⟩,⟨690379, by decide⟩]) unmarked_context_12_91452_690380 node_context_12_91452_690380
  intro a
  fin_cases a
  · exact context_13_365808_690332
  · exact context_13_365809_690354
  · exact context_13_365810_690372
  · exact context_13_365811_690379

theorem selected_cut_27310 : selected 9 ⟨690431, by decide⟩
    (prefixPartial 12 91453) = some ⟨12, 2, 0, 690431, 91453, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_91453_690431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91453 ⟨690431, by decide⟩ :=
  accepted_of_selected 12 91453 ⟨690431, by decide⟩ ⟨12, 2, 0, 690431, 91453, 3933, 65536⟩
    (by decide) selected_cut_27310

theorem selected_cut_27311 : selected 8 ⟨690435, by decide⟩
    (prefixPartial 13 365816) = some ⟨13, 2, 0, 690435, 365816, 137, 16384⟩ := by
  decide +kernel

theorem context_13_365816_690435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365816 ⟨690435, by decide⟩ :=
  accepted_of_selected 13 365816 ⟨690435, by decide⟩ ⟨13, 2, 0, 690435, 365816, 137, 16384⟩
    (by decide) selected_cut_27311

theorem selected_cut_27312 : selected 8 ⟨690459, by decide⟩
    (prefixPartial 13 365817) = some ⟨13, 2, 0, 690459, 365817, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_365817_690459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365817 ⟨690459, by decide⟩ :=
  accepted_of_selected 13 365817 ⟨690459, by decide⟩ ⟨13, 2, 0, 690459, 365817, 1697, 16384⟩
    (by decide) selected_cut_27312

theorem selected_cut_27313 : selected 8 ⟨690477, by decide⟩
    (prefixPartial 13 365818) = some ⟨13, 2, 0, 690477, 365818, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_365818_690477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365818 ⟨690477, by decide⟩ :=
  accepted_of_selected 13 365818 ⟨690477, by decide⟩ ⟨13, 2, 0, 690477, 365818, 1309, 16384⟩
    (by decide) selected_cut_27313

theorem selected_cut_27314 : selected 8 ⟨690486, by decide⟩
    (prefixPartial 13 365819) = some ⟨13, 2, 0, 690486, 365819, 969, 16384⟩ := by
  decide +kernel

theorem context_13_365819_690486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365819 ⟨690486, by decide⟩ :=
  accepted_of_selected 13 365819 ⟨690486, by decide⟩ ⟨13, 2, 0, 690486, 365819, 969, 16384⟩
    (by decide) selected_cut_27314

theorem unmarked_context_12_91454_690487 : frontier 9 ⟨690487, by decide⟩
    (prefixCache 12 91454) (prefixPartial 12 91454) = false := by
  decide +kernel

theorem node_context_12_91454_690487 : EJMOriginalGlobalDAGData.nodes 9 ⟨690487, by decide⟩ =
    .split (coordinate 12) (![⟨690435, by decide⟩,⟨690459, by decide⟩,⟨690477, by decide⟩,⟨690486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91454_690487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91454 ⟨690487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91454
    ⟨690487, by decide⟩ (by decide) (![⟨690435, by decide⟩,⟨690459, by decide⟩,⟨690477, by decide⟩,⟨690486, by decide⟩]) unmarked_context_12_91454_690487 node_context_12_91454_690487
  intro a
  fin_cases a
  · exact context_13_365816_690435
  · exact context_13_365817_690459
  · exact context_13_365818_690477
  · exact context_13_365819_690486

theorem selected_cut_27315 : selected 8 ⟨690491, by decide⟩
    (prefixPartial 13 365820) = some ⟨13, 2, 0, 690491, 365820, 77, 16384⟩ := by
  decide +kernel

theorem context_13_365820_690491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365820 ⟨690491, by decide⟩ :=
  accepted_of_selected 13 365820 ⟨690491, by decide⟩ ⟨13, 2, 0, 690491, 365820, 77, 16384⟩
    (by decide) selected_cut_27315

theorem selected_cut_27316 : selected 8 ⟨690520, by decide⟩
    (prefixPartial 13 365821) = some ⟨13, 2, 0, 690520, 365821, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_365821_690520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365821 ⟨690520, by decide⟩ :=
  accepted_of_selected 13 365821 ⟨690520, by decide⟩ ⟨13, 2, 0, 690520, 365821, 2301, 16384⟩
    (by decide) selected_cut_27316

theorem selected_cut_27317 : selected 8 ⟨690540, by decide⟩
    (prefixPartial 13 365822) = some ⟨13, 2, 0, 690540, 365822, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_365822_690540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365822 ⟨690540, by decide⟩ :=
  accepted_of_selected 13 365822 ⟨690540, by decide⟩ ⟨13, 2, 0, 690540, 365822, 1597, 16384⟩
    (by decide) selected_cut_27317

theorem selected_cut_27318 : selected 8 ⟨690549, by decide⟩
    (prefixPartial 13 365823) = some ⟨13, 2, 0, 690549, 365823, 905, 16384⟩ := by
  decide +kernel

theorem context_13_365823_690549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365823 ⟨690549, by decide⟩ :=
  accepted_of_selected 13 365823 ⟨690549, by decide⟩ ⟨13, 2, 0, 690549, 365823, 905, 16384⟩
    (by decide) selected_cut_27318

theorem unmarked_context_12_91455_690550 : frontier 9 ⟨690550, by decide⟩
    (prefixCache 12 91455) (prefixPartial 12 91455) = false := by
  decide +kernel

theorem node_context_12_91455_690550 : EJMOriginalGlobalDAGData.nodes 9 ⟨690550, by decide⟩ =
    .split (coordinate 12) (![⟨690491, by decide⟩,⟨690520, by decide⟩,⟨690540, by decide⟩,⟨690549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91455_690550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91455 ⟨690550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91455
    ⟨690550, by decide⟩ (by decide) (![⟨690491, by decide⟩,⟨690520, by decide⟩,⟨690540, by decide⟩,⟨690549, by decide⟩]) unmarked_context_12_91455_690550 node_context_12_91455_690550
  intro a
  fin_cases a
  · exact context_13_365820_690491
  · exact context_13_365821_690520
  · exact context_13_365822_690540
  · exact context_13_365823_690549

theorem unmarked_context_11_22863_690551 : frontier 10 ⟨690551, by decide⟩
    (prefixCache 11 22863) (prefixPartial 11 22863) = false := by
  decide +kernel

theorem node_context_11_22863_690551 : EJMOriginalGlobalDAGData.nodes 10 ⟨690551, by decide⟩ =
    .split (coordinate 11) (![⟨690380, by decide⟩,⟨690431, by decide⟩,⟨690487, by decide⟩,⟨690550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22863_690551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22863 ⟨690551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22863
    ⟨690551, by decide⟩ (by decide) (![⟨690380, by decide⟩,⟨690431, by decide⟩,⟨690487, by decide⟩,⟨690550, by decide⟩]) unmarked_context_11_22863_690551 node_context_11_22863_690551
  intro a
  fin_cases a
  · exact context_12_91452_690380
  · exact context_12_91453_690431
  · exact context_12_91454_690487
  · exact context_12_91455_690550

theorem unmarked_context_10_5715_690552 : frontier 11 ⟨690552, by decide⟩
    (prefixCache 10 5715) (prefixPartial 10 5715) = false := by
  decide +kernel

theorem node_context_10_5715_690552 : EJMOriginalGlobalDAGData.nodes 11 ⟨690552, by decide⟩ =
    .split (coordinate 10) (![⟨689903, by decide⟩,⟨690076, by decide⟩,⟨690328, by decide⟩,⟨690551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5715_690552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5715 ⟨690552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5715
    ⟨690552, by decide⟩ (by decide) (![⟨689903, by decide⟩,⟨690076, by decide⟩,⟨690328, by decide⟩,⟨690551, by decide⟩]) unmarked_context_10_5715_690552 node_context_10_5715_690552
  intro a
  fin_cases a
  · exact context_11_22860_689903
  · exact context_11_22861_690076
  · exact context_11_22862_690328
  · exact context_11_22863_690551

theorem unmarked_context_9_1428_690553 : frontier 12 ⟨690553, by decide⟩
    (prefixCache 9 1428) (prefixPartial 9 1428) = false := by
  decide +kernel

theorem node_context_9_1428_690553 : EJMOriginalGlobalDAGData.nodes 12 ⟨690553, by decide⟩ =
    .split (coordinate 9) (![⟨687672, by decide⟩,⟨688522, by decide⟩,⟨689583, by decide⟩,⟨690552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1428_690553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1428 ⟨690553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1428
    ⟨690553, by decide⟩ (by decide) (![⟨687672, by decide⟩,⟨688522, by decide⟩,⟨689583, by decide⟩,⟨690552, by decide⟩]) unmarked_context_9_1428_690553 node_context_9_1428_690553
  intro a
  fin_cases a
  · exact context_10_5712_687672
  · exact context_10_5713_688522
  · exact context_10_5714_689583
  · exact context_10_5715_690552

theorem selected_cut_27319 : selected 9 ⟨690601, by decide⟩
    (prefixPartial 12 91456) = some ⟨12, 2, 0, 690601, 91456, 3381, 65536⟩ := by
  decide +kernel

theorem context_12_91456_690601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91456 ⟨690601, by decide⟩ :=
  accepted_of_selected 12 91456 ⟨690601, by decide⟩ ⟨12, 2, 0, 690601, 91456, 3381, 65536⟩
    (by decide) selected_cut_27319

theorem selected_cut_27320 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 91457) = some ⟨12, 1, 0, 170504, 91457, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91457_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91457 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 91457 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 91457, 1, 65536⟩
    (by decide) selected_cut_27320

theorem selected_cut_27321 : selected 9 ⟨690654, by decide⟩
    (prefixPartial 12 91458) = some ⟨12, 2, 0, 690654, 91458, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_91458_690654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91458 ⟨690654, by decide⟩ :=
  accepted_of_selected 12 91458 ⟨690654, by decide⟩ ⟨12, 2, 0, 690654, 91458, 3757, 65536⟩
    (by decide) selected_cut_27321

theorem selected_cut_27322 : selected 9 ⟨690701, by decide⟩
    (prefixPartial 12 91459) = some ⟨12, 2, 0, 690701, 91459, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_91459_690701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91459 ⟨690701, by decide⟩ :=
  accepted_of_selected 12 91459 ⟨690701, by decide⟩ ⟨12, 2, 0, 690701, 91459, 3861, 65536⟩
    (by decide) selected_cut_27322

theorem unmarked_context_11_22864_690702 : frontier 10 ⟨690702, by decide⟩
    (prefixCache 11 22864) (prefixPartial 11 22864) = false := by
  decide +kernel

theorem node_context_11_22864_690702 : EJMOriginalGlobalDAGData.nodes 10 ⟨690702, by decide⟩ =
    .split (coordinate 11) (![⟨690601, by decide⟩,⟨170504, by decide⟩,⟨690654, by decide⟩,⟨690701, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22864_690702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22864 ⟨690702, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22864
    ⟨690702, by decide⟩ (by decide) (![⟨690601, by decide⟩,⟨170504, by decide⟩,⟨690654, by decide⟩,⟨690701, by decide⟩]) unmarked_context_11_22864_690702 node_context_11_22864_690702
  intro a
  fin_cases a
  · exact context_12_91456_690601
  · exact context_12_91457_170504
  · exact context_12_91458_690654
  · exact context_12_91459_690701

theorem selected_cut_27323 : selected 9 ⟨690737, by decide⟩
    (prefixPartial 12 91460) = some ⟨12, 2, 0, 690737, 91460, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_91460_690737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91460 ⟨690737, by decide⟩ :=
  accepted_of_selected 12 91460 ⟨690737, by decide⟩ ⟨12, 2, 0, 690737, 91460, 2361, 65536⟩
    (by decide) selected_cut_27323

theorem selected_cut_27324 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 91461) = some ⟨12, 1, 0, 170504, 91461, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91461_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91461 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 91461 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 91461, 1, 65536⟩
    (by decide) selected_cut_27324

theorem selected_cut_27325 : selected 9 ⟨690773, by decide⟩
    (prefixPartial 12 91462) = some ⟨12, 2, 0, 690773, 91462, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_91462_690773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91462 ⟨690773, by decide⟩ :=
  accepted_of_selected 12 91462 ⟨690773, by decide⟩ ⟨12, 2, 0, 690773, 91462, 2373, 65536⟩
    (by decide) selected_cut_27325

theorem selected_cut_27326 : selected 9 ⟨690816, by decide⟩
    (prefixPartial 12 91463) = some ⟨12, 2, 0, 690816, 91463, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_91463_690816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91463 ⟨690816, by decide⟩ :=
  accepted_of_selected 12 91463 ⟨690816, by decide⟩ ⟨12, 2, 0, 690816, 91463, 2609, 65536⟩
    (by decide) selected_cut_27326

theorem unmarked_context_11_22865_690817 : frontier 10 ⟨690817, by decide⟩
    (prefixCache 11 22865) (prefixPartial 11 22865) = false := by
  decide +kernel

theorem node_context_11_22865_690817 : EJMOriginalGlobalDAGData.nodes 10 ⟨690817, by decide⟩ =
    .split (coordinate 11) (![⟨690737, by decide⟩,⟨170504, by decide⟩,⟨690773, by decide⟩,⟨690816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22865_690817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22865 ⟨690817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22865
    ⟨690817, by decide⟩ (by decide) (![⟨690737, by decide⟩,⟨170504, by decide⟩,⟨690773, by decide⟩,⟨690816, by decide⟩]) unmarked_context_11_22865_690817 node_context_11_22865_690817
  intro a
  fin_cases a
  · exact context_12_91460_690737
  · exact context_12_91461_170504
  · exact context_12_91462_690773
  · exact context_12_91463_690816

theorem selected_cut_27327 : selected 9 ⟨690861, by decide⟩
    (prefixPartial 12 91464) = some ⟨12, 2, 0, 690861, 91464, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_91464_690861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91464 ⟨690861, by decide⟩ :=
  accepted_of_selected 12 91464 ⟨690861, by decide⟩ ⟨12, 2, 0, 690861, 91464, 3321, 65536⟩
    (by decide) selected_cut_27327

theorem selected_cut_27328 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 91465) = some ⟨12, 1, 0, 126371, 91465, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91465_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91465 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 91465 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 91465, 1, 65536⟩
    (by decide) selected_cut_27328

theorem selected_cut_27329 : selected 9 ⟨690902, by decide⟩
    (prefixPartial 12 91466) = some ⟨12, 2, 0, 690902, 91466, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_91466_690902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91466 ⟨690902, by decide⟩ :=
  accepted_of_selected 12 91466 ⟨690902, by decide⟩ ⟨12, 2, 0, 690902, 91466, 3241, 65536⟩
    (by decide) selected_cut_27329

theorem selected_cut_27330 : selected 9 ⟨690953, by decide⟩
    (prefixPartial 12 91467) = some ⟨12, 2, 0, 690953, 91467, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_91467_690953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91467 ⟨690953, by decide⟩ :=
  accepted_of_selected 12 91467 ⟨690953, by decide⟩ ⟨12, 2, 0, 690953, 91467, 3445, 65536⟩
    (by decide) selected_cut_27330

theorem unmarked_context_11_22866_690954 : frontier 10 ⟨690954, by decide⟩
    (prefixCache 11 22866) (prefixPartial 11 22866) = false := by
  decide +kernel

theorem node_context_11_22866_690954 : EJMOriginalGlobalDAGData.nodes 10 ⟨690954, by decide⟩ =
    .split (coordinate 11) (![⟨690861, by decide⟩,⟨126371, by decide⟩,⟨690902, by decide⟩,⟨690953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22866_690954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22866 ⟨690954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22866
    ⟨690954, by decide⟩ (by decide) (![⟨690861, by decide⟩,⟨126371, by decide⟩,⟨690902, by decide⟩,⟨690953, by decide⟩]) unmarked_context_11_22866_690954 node_context_11_22866_690954
  intro a
  fin_cases a
  · exact context_12_91464_690861
  · exact context_12_91465_126371
  · exact context_12_91466_690902
  · exact context_12_91467_690953

theorem selected_cut_27331 : selected 9 ⟨690994, by decide⟩
    (prefixPartial 12 91468) = some ⟨12, 2, 0, 690994, 91468, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_91468_690994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91468 ⟨690994, by decide⟩ :=
  accepted_of_selected 12 91468 ⟨690994, by decide⟩ ⟨12, 2, 0, 690994, 91468, 3257, 65536⟩
    (by decide) selected_cut_27331

theorem selected_cut_27332 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 91469) = some ⟨12, 1, 0, 320864, 91469, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91469_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91469 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 91469 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 91469, 1, 65536⟩
    (by decide) selected_cut_27332

theorem selected_cut_27333 : selected 9 ⟨691037, by decide⟩
    (prefixPartial 12 91470) = some ⟨12, 2, 0, 691037, 91470, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_91470_691037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91470 ⟨691037, by decide⟩ :=
  accepted_of_selected 12 91470 ⟨691037, by decide⟩ ⟨12, 2, 0, 691037, 91470, 3029, 65536⟩
    (by decide) selected_cut_27333

theorem selected_cut_27334 : selected 9 ⟨691080, by decide⟩
    (prefixPartial 12 91471) = some ⟨12, 2, 0, 691080, 91471, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_91471_691080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91471 ⟨691080, by decide⟩ :=
  accepted_of_selected 12 91471 ⟨691080, by decide⟩ ⟨12, 2, 0, 691080, 91471, 3273, 65536⟩
    (by decide) selected_cut_27334

theorem unmarked_context_11_22867_691081 : frontier 10 ⟨691081, by decide⟩
    (prefixCache 11 22867) (prefixPartial 11 22867) = false := by
  decide +kernel

theorem node_context_11_22867_691081 : EJMOriginalGlobalDAGData.nodes 10 ⟨691081, by decide⟩ =
    .split (coordinate 11) (![⟨690994, by decide⟩,⟨320864, by decide⟩,⟨691037, by decide⟩,⟨691080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22867_691081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22867 ⟨691081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22867
    ⟨691081, by decide⟩ (by decide) (![⟨690994, by decide⟩,⟨320864, by decide⟩,⟨691037, by decide⟩,⟨691080, by decide⟩]) unmarked_context_11_22867_691081 node_context_11_22867_691081
  intro a
  fin_cases a
  · exact context_12_91468_690994
  · exact context_12_91469_320864
  · exact context_12_91470_691037
  · exact context_12_91471_691080

theorem unmarked_context_10_5716_691082 : frontier 11 ⟨691082, by decide⟩
    (prefixCache 10 5716) (prefixPartial 10 5716) = false := by
  decide +kernel

theorem node_context_10_5716_691082 : EJMOriginalGlobalDAGData.nodes 11 ⟨691082, by decide⟩ =
    .split (coordinate 10) (![⟨690702, by decide⟩,⟨690817, by decide⟩,⟨690954, by decide⟩,⟨691081, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5716_691082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5716 ⟨691082, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5716
    ⟨691082, by decide⟩ (by decide) (![⟨690702, by decide⟩,⟨690817, by decide⟩,⟨690954, by decide⟩,⟨691081, by decide⟩]) unmarked_context_10_5716_691082 node_context_10_5716_691082
  intro a
  fin_cases a
  · exact context_11_22864_690702
  · exact context_11_22865_690817
  · exact context_11_22866_690954
  · exact context_11_22867_691081

theorem selected_cut_27335 : selected 9 ⟨691122, by decide⟩
    (prefixPartial 12 91472) = some ⟨12, 2, 0, 691122, 91472, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_91472_691122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91472 ⟨691122, by decide⟩ :=
  accepted_of_selected 12 91472 ⟨691122, by decide⟩ ⟨12, 2, 0, 691122, 91472, 2909, 65536⟩
    (by decide) selected_cut_27335

theorem selected_cut_27336 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 91473) = some ⟨12, 1, 0, 642341, 91473, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91473_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91473 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 91473 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 91473, 1, 65536⟩
    (by decide) selected_cut_27336

theorem selected_cut_27337 : selected 9 ⟨691162, by decide⟩
    (prefixPartial 12 91474) = some ⟨12, 2, 0, 691162, 91474, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_91474_691162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91474 ⟨691162, by decide⟩ :=
  accepted_of_selected 12 91474 ⟨691162, by decide⟩ ⟨12, 2, 0, 691162, 91474, 3125, 65536⟩
    (by decide) selected_cut_27337

theorem selected_cut_27338 : selected 9 ⟨691201, by decide⟩
    (prefixPartial 12 91475) = some ⟨12, 2, 0, 691201, 91475, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_91475_691201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91475 ⟨691201, by decide⟩ :=
  accepted_of_selected 12 91475 ⟨691201, by decide⟩ ⟨12, 2, 0, 691201, 91475, 3269, 65536⟩
    (by decide) selected_cut_27338

theorem unmarked_context_11_22868_691202 : frontier 10 ⟨691202, by decide⟩
    (prefixCache 11 22868) (prefixPartial 11 22868) = false := by
  decide +kernel

theorem node_context_11_22868_691202 : EJMOriginalGlobalDAGData.nodes 10 ⟨691202, by decide⟩ =
    .split (coordinate 11) (![⟨691122, by decide⟩,⟨642341, by decide⟩,⟨691162, by decide⟩,⟨691201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22868_691202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22868 ⟨691202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22868
    ⟨691202, by decide⟩ (by decide) (![⟨691122, by decide⟩,⟨642341, by decide⟩,⟨691162, by decide⟩,⟨691201, by decide⟩]) unmarked_context_11_22868_691202 node_context_11_22868_691202
  intro a
  fin_cases a
  · exact context_12_91472_691122
  · exact context_12_91473_642341
  · exact context_12_91474_691162
  · exact context_12_91475_691201

theorem selected_cut_27339 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 22869) = some ⟨11, 1, 0, 451541, 22869, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22869_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22869 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 22869 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 22869, 1, 262144⟩
    (by decide) selected_cut_27339

theorem selected_cut_27340 : selected 9 ⟨691241, by decide⟩
    (prefixPartial 12 91480) = some ⟨12, 2, 0, 691241, 91480, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_91480_691241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91480 ⟨691241, by decide⟩ :=
  accepted_of_selected 12 91480 ⟨691241, by decide⟩ ⟨12, 2, 0, 691241, 91480, 2793, 65536⟩
    (by decide) selected_cut_27340

theorem selected_cut_27341 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 91481) = some ⟨12, 1, 0, 642341, 91481, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91481_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91481 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 91481 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 91481, 1, 65536⟩
    (by decide) selected_cut_27341

theorem selected_cut_27342 : selected 9 ⟨691278, by decide⟩
    (prefixPartial 12 91482) = some ⟨12, 2, 0, 691278, 91482, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_91482_691278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91482 ⟨691278, by decide⟩ :=
  accepted_of_selected 12 91482 ⟨691278, by decide⟩ ⟨12, 2, 0, 691278, 91482, 2641, 65536⟩
    (by decide) selected_cut_27342

theorem selected_cut_27343 : selected 9 ⟨691318, by decide⟩
    (prefixPartial 12 91483) = some ⟨12, 2, 0, 691318, 91483, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_91483_691318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91483 ⟨691318, by decide⟩ :=
  accepted_of_selected 12 91483 ⟨691318, by decide⟩ ⟨12, 2, 0, 691318, 91483, 2873, 65536⟩
    (by decide) selected_cut_27343

theorem unmarked_context_11_22870_691319 : frontier 10 ⟨691319, by decide⟩
    (prefixCache 11 22870) (prefixPartial 11 22870) = false := by
  decide +kernel

theorem node_context_11_22870_691319 : EJMOriginalGlobalDAGData.nodes 10 ⟨691319, by decide⟩ =
    .split (coordinate 11) (![⟨691241, by decide⟩,⟨642341, by decide⟩,⟨691278, by decide⟩,⟨691318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22870_691319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22870 ⟨691319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22870
    ⟨691319, by decide⟩ (by decide) (![⟨691241, by decide⟩,⟨642341, by decide⟩,⟨691278, by decide⟩,⟨691318, by decide⟩]) unmarked_context_11_22870_691319 node_context_11_22870_691319
  intro a
  fin_cases a
  · exact context_12_91480_691241
  · exact context_12_91481_642341
  · exact context_12_91482_691278
  · exact context_12_91483_691318

theorem selected_cut_27344 : selected 9 ⟨691360, by decide⟩
    (prefixPartial 12 91484) = some ⟨12, 2, 0, 691360, 91484, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_91484_691360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91484 ⟨691360, by decide⟩ :=
  accepted_of_selected 12 91484 ⟨691360, by decide⟩ ⟨12, 2, 0, 691360, 91484, 2865, 65536⟩
    (by decide) selected_cut_27344

theorem selected_cut_27345 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 91485) = some ⟨12, 1, 0, 642341, 91485, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91485_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91485 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 91485 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 91485, 1, 65536⟩
    (by decide) selected_cut_27345

theorem selected_cut_27346 : selected 9 ⟨691403, by decide⟩
    (prefixPartial 12 91486) = some ⟨12, 2, 0, 691403, 91486, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_91486_691403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91486 ⟨691403, by decide⟩ :=
  accepted_of_selected 12 91486 ⟨691403, by decide⟩ ⟨12, 2, 0, 691403, 91486, 2701, 65536⟩
    (by decide) selected_cut_27346

theorem selected_cut_27347 : selected 9 ⟨691440, by decide⟩
    (prefixPartial 12 91487) = some ⟨12, 2, 0, 691440, 91487, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_91487_691440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91487 ⟨691440, by decide⟩ :=
  accepted_of_selected 12 91487 ⟨691440, by decide⟩ ⟨12, 2, 0, 691440, 91487, 2797, 65536⟩
    (by decide) selected_cut_27347

theorem unmarked_context_11_22871_691441 : frontier 10 ⟨691441, by decide⟩
    (prefixCache 11 22871) (prefixPartial 11 22871) = false := by
  decide +kernel

theorem node_context_11_22871_691441 : EJMOriginalGlobalDAGData.nodes 10 ⟨691441, by decide⟩ =
    .split (coordinate 11) (![⟨691360, by decide⟩,⟨642341, by decide⟩,⟨691403, by decide⟩,⟨691440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22871_691441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22871 ⟨691441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22871
    ⟨691441, by decide⟩ (by decide) (![⟨691360, by decide⟩,⟨642341, by decide⟩,⟨691403, by decide⟩,⟨691440, by decide⟩]) unmarked_context_11_22871_691441 node_context_11_22871_691441
  intro a
  fin_cases a
  · exact context_12_91484_691360
  · exact context_12_91485_642341
  · exact context_12_91486_691403
  · exact context_12_91487_691440

theorem unmarked_context_10_5717_691442 : frontier 11 ⟨691442, by decide⟩
    (prefixCache 10 5717) (prefixPartial 10 5717) = false := by
  decide +kernel

theorem node_context_10_5717_691442 : EJMOriginalGlobalDAGData.nodes 11 ⟨691442, by decide⟩ =
    .split (coordinate 10) (![⟨691202, by decide⟩,⟨451541, by decide⟩,⟨691319, by decide⟩,⟨691441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5717_691442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5717 ⟨691442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5717
    ⟨691442, by decide⟩ (by decide) (![⟨691202, by decide⟩,⟨451541, by decide⟩,⟨691319, by decide⟩,⟨691441, by decide⟩]) unmarked_context_10_5717_691442 node_context_10_5717_691442
  intro a
  fin_cases a
  · exact context_11_22868_691202
  · exact context_11_22869_451541
  · exact context_11_22870_691319
  · exact context_11_22871_691441

theorem selected_cut_27348 : selected 9 ⟨691482, by decide⟩
    (prefixPartial 12 91488) = some ⟨12, 2, 0, 691482, 91488, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_91488_691482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91488 ⟨691482, by decide⟩ :=
  accepted_of_selected 12 91488 ⟨691482, by decide⟩ ⟨12, 2, 0, 691482, 91488, 3313, 65536⟩
    (by decide) selected_cut_27348

theorem selected_cut_27349 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 91489) = some ⟨12, 1, 0, 126884, 91489, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91489_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91489 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 91489 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 91489, 1, 65536⟩
    (by decide) selected_cut_27349

theorem selected_cut_27350 : selected 9 ⟨691524, by decide⟩
    (prefixPartial 12 91490) = some ⟨12, 2, 0, 691524, 91490, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_91490_691524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91490 ⟨691524, by decide⟩ :=
  accepted_of_selected 12 91490 ⟨691524, by decide⟩ ⟨12, 2, 0, 691524, 91490, 3189, 65536⟩
    (by decide) selected_cut_27350

theorem selected_cut_27351 : selected 9 ⟨691565, by decide⟩
    (prefixPartial 12 91491) = some ⟨12, 2, 0, 691565, 91491, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_91491_691565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91491 ⟨691565, by decide⟩ :=
  accepted_of_selected 12 91491 ⟨691565, by decide⟩ ⟨12, 2, 0, 691565, 91491, 3409, 65536⟩
    (by decide) selected_cut_27351

theorem unmarked_context_11_22872_691566 : frontier 10 ⟨691566, by decide⟩
    (prefixCache 11 22872) (prefixPartial 11 22872) = false := by
  decide +kernel

theorem node_context_11_22872_691566 : EJMOriginalGlobalDAGData.nodes 10 ⟨691566, by decide⟩ =
    .split (coordinate 11) (![⟨691482, by decide⟩,⟨126884, by decide⟩,⟨691524, by decide⟩,⟨691565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22872_691566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22872 ⟨691566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22872
    ⟨691566, by decide⟩ (by decide) (![⟨691482, by decide⟩,⟨126884, by decide⟩,⟨691524, by decide⟩,⟨691565, by decide⟩]) unmarked_context_11_22872_691566 node_context_11_22872_691566
  intro a
  fin_cases a
  · exact context_12_91488_691482
  · exact context_12_91489_126884
  · exact context_12_91490_691524
  · exact context_12_91491_691565

theorem selected_cut_27352 : selected 9 ⟨691596, by decide⟩
    (prefixPartial 12 91492) = some ⟨12, 2, 0, 691596, 91492, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_91492_691596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91492 ⟨691596, by decide⟩ :=
  accepted_of_selected 12 91492 ⟨691596, by decide⟩ ⟨12, 2, 0, 691596, 91492, 2141, 65536⟩
    (by decide) selected_cut_27352

theorem selected_cut_27353 : selected 9 ⟨688903, by decide⟩
    (prefixPartial 12 91493) = some ⟨12, 1, 0, 688903, 91493, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91493_688903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91493 ⟨688903, by decide⟩ :=
  accepted_of_selected 12 91493 ⟨688903, by decide⟩ ⟨12, 1, 0, 688903, 91493, 1, 65536⟩
    (by decide) selected_cut_27353

theorem selected_cut_27354 : selected 9 ⟨691631, by decide⟩
    (prefixPartial 12 91494) = some ⟨12, 2, 0, 691631, 91494, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_91494_691631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91494 ⟨691631, by decide⟩ :=
  accepted_of_selected 12 91494 ⟨691631, by decide⟩ ⟨12, 2, 0, 691631, 91494, 2069, 65536⟩
    (by decide) selected_cut_27354

theorem selected_cut_27355 : selected 9 ⟨691669, by decide⟩
    (prefixPartial 12 91495) = some ⟨12, 2, 0, 691669, 91495, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_91495_691669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91495 ⟨691669, by decide⟩ :=
  accepted_of_selected 12 91495 ⟨691669, by decide⟩ ⟨12, 2, 0, 691669, 91495, 2233, 65536⟩
    (by decide) selected_cut_27355

theorem unmarked_context_11_22873_691670 : frontier 10 ⟨691670, by decide⟩
    (prefixCache 11 22873) (prefixPartial 11 22873) = false := by
  decide +kernel

theorem node_context_11_22873_691670 : EJMOriginalGlobalDAGData.nodes 10 ⟨691670, by decide⟩ =
    .split (coordinate 11) (![⟨691596, by decide⟩,⟨688903, by decide⟩,⟨691631, by decide⟩,⟨691669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22873_691670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22873 ⟨691670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22873
    ⟨691670, by decide⟩ (by decide) (![⟨691596, by decide⟩,⟨688903, by decide⟩,⟨691631, by decide⟩,⟨691669, by decide⟩]) unmarked_context_11_22873_691670 node_context_11_22873_691670
  intro a
  fin_cases a
  · exact context_12_91492_691596
  · exact context_12_91493_688903
  · exact context_12_91494_691631
  · exact context_12_91495_691669

theorem selected_cut_27356 : selected 9 ⟨691708, by decide⟩
    (prefixPartial 12 91496) = some ⟨12, 2, 0, 691708, 91496, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_91496_691708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91496 ⟨691708, by decide⟩ :=
  accepted_of_selected 12 91496 ⟨691708, by decide⟩ ⟨12, 2, 0, 691708, 91496, 2929, 65536⟩
    (by decide) selected_cut_27356

theorem selected_cut_27357 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 91497) = some ⟨12, 1, 0, 691709, 91497, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91497_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91497 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 91497 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 91497, 1, 65536⟩
    (by decide) selected_cut_27357

theorem selected_cut_27358 : selected 9 ⟨691740, by decide⟩
    (prefixPartial 12 91498) = some ⟨12, 2, 0, 691740, 91498, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_91498_691740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91498 ⟨691740, by decide⟩ :=
  accepted_of_selected 12 91498 ⟨691740, by decide⟩ ⟨12, 2, 0, 691740, 91498, 2497, 65536⟩
    (by decide) selected_cut_27358

theorem selected_cut_27359 : selected 9 ⟨691779, by decide⟩
    (prefixPartial 12 91499) = some ⟨12, 2, 0, 691779, 91499, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_91499_691779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91499 ⟨691779, by decide⟩ :=
  accepted_of_selected 12 91499 ⟨691779, by decide⟩ ⟨12, 2, 0, 691779, 91499, 2821, 65536⟩
    (by decide) selected_cut_27359

theorem unmarked_context_11_22874_691780 : frontier 10 ⟨691780, by decide⟩
    (prefixCache 11 22874) (prefixPartial 11 22874) = false := by
  decide +kernel

theorem node_context_11_22874_691780 : EJMOriginalGlobalDAGData.nodes 10 ⟨691780, by decide⟩ =
    .split (coordinate 11) (![⟨691708, by decide⟩,⟨691709, by decide⟩,⟨691740, by decide⟩,⟨691779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22874_691780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22874 ⟨691780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22874
    ⟨691780, by decide⟩ (by decide) (![⟨691708, by decide⟩,⟨691709, by decide⟩,⟨691740, by decide⟩,⟨691779, by decide⟩]) unmarked_context_11_22874_691780 node_context_11_22874_691780
  intro a
  fin_cases a
  · exact context_12_91496_691708
  · exact context_12_91497_691709
  · exact context_12_91498_691740
  · exact context_12_91499_691779

theorem selected_cut_27360 : selected 9 ⟨691821, by decide⟩
    (prefixPartial 12 91500) = some ⟨12, 2, 0, 691821, 91500, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_91500_691821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91500 ⟨691821, by decide⟩ :=
  accepted_of_selected 12 91500 ⟨691821, by decide⟩ ⟨12, 2, 0, 691821, 91500, 3061, 65536⟩
    (by decide) selected_cut_27360

theorem selected_cut_27361 : selected 9 ⟨691822, by decide⟩
    (prefixPartial 12 91501) = some ⟨12, 1, 0, 691822, 91501, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91501_691822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91501 ⟨691822, by decide⟩ :=
  accepted_of_selected 12 91501 ⟨691822, by decide⟩ ⟨12, 1, 0, 691822, 91501, 1, 65536⟩
    (by decide) selected_cut_27361

theorem selected_cut_27362 : selected 9 ⟨691855, by decide⟩
    (prefixPartial 12 91502) = some ⟨12, 2, 0, 691855, 91502, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_91502_691855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91502 ⟨691855, by decide⟩ :=
  accepted_of_selected 12 91502 ⟨691855, by decide⟩ ⟨12, 2, 0, 691855, 91502, 2657, 65536⟩
    (by decide) selected_cut_27362

theorem selected_cut_27363 : selected 9 ⟨691893, by decide⟩
    (prefixPartial 12 91503) = some ⟨12, 2, 0, 691893, 91503, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_91503_691893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91503 ⟨691893, by decide⟩ :=
  accepted_of_selected 12 91503 ⟨691893, by decide⟩ ⟨12, 2, 0, 691893, 91503, 2889, 65536⟩
    (by decide) selected_cut_27363

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
