/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover016
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_01634 : selected 8 ⟨57520, by decide⟩
    (prefixPartial 13 18713) = some ⟨13, 2, 0, 57520, 18713, 3341, 16384⟩ := by
  decide +kernel

theorem context_13_18713_57520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18713 ⟨57520, by decide⟩ :=
  accepted_of_selected 13 18713 ⟨57520, by decide⟩ ⟨13, 2, 0, 57520, 18713, 3341, 16384⟩
    (by decide) selected_cut_01634

theorem selected_cut_01635 : selected 8 ⟨57546, by decide⟩
    (prefixPartial 13 18714) = some ⟨13, 2, 0, 57546, 18714, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_18714_57546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18714 ⟨57546, by decide⟩ :=
  accepted_of_selected 13 18714 ⟨57546, by decide⟩ ⟨13, 2, 0, 57546, 18714, 2313, 16384⟩
    (by decide) selected_cut_01635

theorem selected_cut_01636 : selected 8 ⟨57560, by decide⟩
    (prefixPartial 13 18715) = some ⟨13, 2, 0, 57560, 18715, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_18715_57560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18715 ⟨57560, by decide⟩ :=
  accepted_of_selected 13 18715 ⟨57560, by decide⟩ ⟨13, 2, 0, 57560, 18715, 1133, 16384⟩
    (by decide) selected_cut_01636

theorem unmarked_context_12_4678_57561 : frontier 9 ⟨57561, by decide⟩
    (prefixCache 12 4678) (prefixPartial 12 4678) = false := by
  decide +kernel

theorem node_context_12_4678_57561 : EJMOriginalGlobalDAGData.nodes 9 ⟨57561, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨57520, by decide⟩,⟨57546, by decide⟩,⟨57560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4678_57561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4678 ⟨57561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4678
    ⟨57561, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨57520, by decide⟩,⟨57546, by decide⟩,⟨57560, by decide⟩]) unmarked_context_12_4678_57561 node_context_12_4678_57561
  intro a
  fin_cases a
  · exact context_13_18712_3444
  · exact context_13_18713_57520
  · exact context_13_18714_57546
  · exact context_13_18715_57560

theorem selected_cut_01637 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18716) = some ⟨13, 1, 0, 3444, 18716, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18716_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18716 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18716 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18716, 1, 16384⟩
    (by decide) selected_cut_01637

theorem selected_cut_01638 : selected 8 ⟨57609, by decide⟩
    (prefixPartial 13 18717) = some ⟨13, 2, 0, 57609, 18717, 3341, 16384⟩ := by
  decide +kernel

theorem context_13_18717_57609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18717 ⟨57609, by decide⟩ :=
  accepted_of_selected 13 18717 ⟨57609, by decide⟩ ⟨13, 2, 0, 57609, 18717, 3341, 16384⟩
    (by decide) selected_cut_01638

theorem selected_cut_01639 : selected 8 ⟨57637, by decide⟩
    (prefixPartial 13 18718) = some ⟨13, 2, 0, 57637, 18718, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_18718_57637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18718 ⟨57637, by decide⟩ :=
  accepted_of_selected 13 18718 ⟨57637, by decide⟩ ⟨13, 2, 0, 57637, 18718, 2485, 16384⟩
    (by decide) selected_cut_01639

theorem selected_cut_01640 : selected 8 ⟨57653, by decide⟩
    (prefixPartial 13 18719) = some ⟨13, 2, 0, 57653, 18719, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_18719_57653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18719 ⟨57653, by decide⟩ :=
  accepted_of_selected 13 18719 ⟨57653, by decide⟩ ⟨13, 2, 0, 57653, 18719, 1149, 16384⟩
    (by decide) selected_cut_01640

theorem unmarked_context_12_4679_57654 : frontier 9 ⟨57654, by decide⟩
    (prefixCache 12 4679) (prefixPartial 12 4679) = false := by
  decide +kernel

theorem node_context_12_4679_57654 : EJMOriginalGlobalDAGData.nodes 9 ⟨57654, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨57609, by decide⟩,⟨57637, by decide⟩,⟨57653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4679_57654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4679 ⟨57654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4679
    ⟨57654, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨57609, by decide⟩,⟨57637, by decide⟩,⟨57653, by decide⟩]) unmarked_context_12_4679_57654 node_context_12_4679_57654
  intro a
  fin_cases a
  · exact context_13_18716_3444
  · exact context_13_18717_57609
  · exact context_13_18718_57637
  · exact context_13_18719_57653

theorem unmarked_context_11_1169_57655 : frontier 10 ⟨57655, by decide⟩
    (prefixCache 11 1169) (prefixPartial 11 1169) = false := by
  decide +kernel

theorem node_context_11_1169_57655 : EJMOriginalGlobalDAGData.nodes 10 ⟨57655, by decide⟩ =
    .split (coordinate 11) (![⟨57377, by decide⟩,⟨57471, by decide⟩,⟨57561, by decide⟩,⟨57654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1169_57655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1169 ⟨57655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1169
    ⟨57655, by decide⟩ (by decide) (![⟨57377, by decide⟩,⟨57471, by decide⟩,⟨57561, by decide⟩,⟨57654, by decide⟩]) unmarked_context_11_1169_57655 node_context_11_1169_57655
  intro a
  fin_cases a
  · exact context_12_4676_57377
  · exact context_12_4677_57471
  · exact context_12_4678_57561
  · exact context_12_4679_57654

theorem selected_cut_01641 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18720) = some ⟨13, 1, 0, 3444, 18720, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18720_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18720 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18720 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18720, 1, 16384⟩
    (by decide) selected_cut_01641

theorem selected_cut_01642 : selected 8 ⟨57679, by decide⟩
    (prefixPartial 13 18721) = some ⟨13, 2, 0, 57679, 18721, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_18721_57679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18721 ⟨57679, by decide⟩ :=
  accepted_of_selected 13 18721 ⟨57679, by decide⟩ ⟨13, 2, 0, 57679, 18721, 1901, 16384⟩
    (by decide) selected_cut_01642

theorem selected_cut_01643 : selected 8 ⟨57703, by decide⟩
    (prefixPartial 13 18722) = some ⟨13, 2, 0, 57703, 18722, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_18722_57703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18722 ⟨57703, by decide⟩ :=
  accepted_of_selected 13 18722 ⟨57703, by decide⟩ ⟨13, 2, 0, 57703, 18722, 1677, 16384⟩
    (by decide) selected_cut_01643

theorem selected_cut_01644 : selected 8 ⟨57710, by decide⟩
    (prefixPartial 13 18723) = some ⟨13, 2, 0, 57710, 18723, 793, 16384⟩ := by
  decide +kernel

theorem context_13_18723_57710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18723 ⟨57710, by decide⟩ :=
  accepted_of_selected 13 18723 ⟨57710, by decide⟩ ⟨13, 2, 0, 57710, 18723, 793, 16384⟩
    (by decide) selected_cut_01644

theorem unmarked_context_12_4680_57711 : frontier 9 ⟨57711, by decide⟩
    (prefixCache 12 4680) (prefixPartial 12 4680) = false := by
  decide +kernel

theorem node_context_12_4680_57711 : EJMOriginalGlobalDAGData.nodes 9 ⟨57711, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨57679, by decide⟩,⟨57703, by decide⟩,⟨57710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4680_57711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4680 ⟨57711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4680
    ⟨57711, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨57679, by decide⟩,⟨57703, by decide⟩,⟨57710, by decide⟩]) unmarked_context_12_4680_57711 node_context_12_4680_57711
  intro a
  fin_cases a
  · exact context_13_18720_3444
  · exact context_13_18721_57679
  · exact context_13_18722_57703
  · exact context_13_18723_57710

theorem selected_cut_01645 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18724) = some ⟨13, 1, 0, 3444, 18724, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18724_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18724 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18724 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18724, 1, 16384⟩
    (by decide) selected_cut_01645

theorem selected_cut_01646 : selected 8 ⟨57742, by decide⟩
    (prefixPartial 13 18725) = some ⟨13, 2, 0, 57742, 18725, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_18725_57742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18725 ⟨57742, by decide⟩ :=
  accepted_of_selected 13 18725 ⟨57742, by decide⟩ ⟨13, 2, 0, 57742, 18725, 2461, 16384⟩
    (by decide) selected_cut_01646

theorem selected_cut_01647 : selected 8 ⟨57763, by decide⟩
    (prefixPartial 13 18726) = some ⟨13, 2, 0, 57763, 18726, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_18726_57763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18726 ⟨57763, by decide⟩ :=
  accepted_of_selected 13 18726 ⟨57763, by decide⟩ ⟨13, 2, 0, 57763, 18726, 2201, 16384⟩
    (by decide) selected_cut_01647

theorem selected_cut_01648 : selected 8 ⟨57771, by decide⟩
    (prefixPartial 13 18727) = some ⟨13, 2, 0, 57771, 18727, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_18727_57771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18727 ⟨57771, by decide⟩ :=
  accepted_of_selected 13 18727 ⟨57771, by decide⟩ ⟨13, 2, 0, 57771, 18727, 1021, 16384⟩
    (by decide) selected_cut_01648

theorem unmarked_context_12_4681_57772 : frontier 9 ⟨57772, by decide⟩
    (prefixCache 12 4681) (prefixPartial 12 4681) = false := by
  decide +kernel

theorem node_context_12_4681_57772 : EJMOriginalGlobalDAGData.nodes 9 ⟨57772, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨57742, by decide⟩,⟨57763, by decide⟩,⟨57771, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4681_57772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4681 ⟨57772, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4681
    ⟨57772, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨57742, by decide⟩,⟨57763, by decide⟩,⟨57771, by decide⟩]) unmarked_context_12_4681_57772 node_context_12_4681_57772
  intro a
  fin_cases a
  · exact context_13_18724_3444
  · exact context_13_18725_57742
  · exact context_13_18726_57763
  · exact context_13_18727_57771

theorem selected_cut_01649 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18728) = some ⟨13, 1, 0, 3444, 18728, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18728_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18728 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18728 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18728, 1, 16384⟩
    (by decide) selected_cut_01649

theorem selected_cut_01650 : selected 8 ⟨57827, by decide⟩
    (prefixPartial 13 18729) = some ⟨13, 2, 0, 57827, 18729, 3929, 16384⟩ := by
  decide +kernel

theorem context_13_18729_57827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18729 ⟨57827, by decide⟩ :=
  accepted_of_selected 13 18729 ⟨57827, by decide⟩ ⟨13, 2, 0, 57827, 18729, 3929, 16384⟩
    (by decide) selected_cut_01650

theorem selected_cut_01651 : selected 8 ⟨57906, by decide⟩
    (prefixPartial 13 18730) = some ⟨13, 2, 0, 57906, 18730, 3693, 16384⟩ := by
  decide +kernel

theorem context_13_18730_57906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18730 ⟨57906, by decide⟩ :=
  accepted_of_selected 13 18730 ⟨57906, by decide⟩ ⟨13, 2, 0, 57906, 18730, 3693, 16384⟩
    (by decide) selected_cut_01651

theorem selected_cut_01652 : selected 8 ⟨57923, by decide⟩
    (prefixPartial 13 18731) = some ⟨13, 2, 0, 57923, 18731, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_18731_57923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18731 ⟨57923, by decide⟩ :=
  accepted_of_selected 13 18731 ⟨57923, by decide⟩ ⟨13, 2, 0, 57923, 18731, 1393, 16384⟩
    (by decide) selected_cut_01652

theorem unmarked_context_12_4682_57924 : frontier 9 ⟨57924, by decide⟩
    (prefixCache 12 4682) (prefixPartial 12 4682) = false := by
  decide +kernel

theorem node_context_12_4682_57924 : EJMOriginalGlobalDAGData.nodes 9 ⟨57924, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨57827, by decide⟩,⟨57906, by decide⟩,⟨57923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4682_57924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4682 ⟨57924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4682
    ⟨57924, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨57827, by decide⟩,⟨57906, by decide⟩,⟨57923, by decide⟩]) unmarked_context_12_4682_57924 node_context_12_4682_57924
  intro a
  fin_cases a
  · exact context_13_18728_3444
  · exact context_13_18729_57827
  · exact context_13_18730_57906
  · exact context_13_18731_57923

theorem selected_cut_01653 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18732) = some ⟨13, 1, 0, 3444, 18732, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18732_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18732 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18732 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18732, 1, 16384⟩
    (by decide) selected_cut_01653

theorem selected_cut_01654 : selected 8 ⟨57948, by decide⟩
    (prefixPartial 13 18733) = some ⟨13, 2, 0, 57948, 18733, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_18733_57948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18733 ⟨57948, by decide⟩ :=
  accepted_of_selected 13 18733 ⟨57948, by decide⟩ ⟨13, 2, 0, 57948, 18733, 2413, 16384⟩
    (by decide) selected_cut_01654

theorem selected_cut_01655 : selected 8 ⟨57966, by decide⟩
    (prefixPartial 13 18734) = some ⟨13, 2, 0, 57966, 18734, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_18734_57966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18734 ⟨57966, by decide⟩ :=
  accepted_of_selected 13 18734 ⟨57966, by decide⟩ ⟨13, 2, 0, 57966, 18734, 2281, 16384⟩
    (by decide) selected_cut_01655

theorem selected_cut_01656 : selected 8 ⟨57974, by decide⟩
    (prefixPartial 13 18735) = some ⟨13, 2, 0, 57974, 18735, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_18735_57974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18735 ⟨57974, by decide⟩ :=
  accepted_of_selected 13 18735 ⟨57974, by decide⟩ ⟨13, 2, 0, 57974, 18735, 1137, 16384⟩
    (by decide) selected_cut_01656

theorem unmarked_context_12_4683_57975 : frontier 9 ⟨57975, by decide⟩
    (prefixCache 12 4683) (prefixPartial 12 4683) = false := by
  decide +kernel

theorem node_context_12_4683_57975 : EJMOriginalGlobalDAGData.nodes 9 ⟨57975, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨57948, by decide⟩,⟨57966, by decide⟩,⟨57974, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4683_57975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4683 ⟨57975, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4683
    ⟨57975, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨57948, by decide⟩,⟨57966, by decide⟩,⟨57974, by decide⟩]) unmarked_context_12_4683_57975 node_context_12_4683_57975
  intro a
  fin_cases a
  · exact context_13_18732_3444
  · exact context_13_18733_57948
  · exact context_13_18734_57966
  · exact context_13_18735_57974

theorem unmarked_context_11_1170_57976 : frontier 10 ⟨57976, by decide⟩
    (prefixCache 11 1170) (prefixPartial 11 1170) = false := by
  decide +kernel

theorem node_context_11_1170_57976 : EJMOriginalGlobalDAGData.nodes 10 ⟨57976, by decide⟩ =
    .split (coordinate 11) (![⟨57711, by decide⟩,⟨57772, by decide⟩,⟨57924, by decide⟩,⟨57975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1170_57976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1170 ⟨57976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1170
    ⟨57976, by decide⟩ (by decide) (![⟨57711, by decide⟩,⟨57772, by decide⟩,⟨57924, by decide⟩,⟨57975, by decide⟩]) unmarked_context_11_1170_57976 node_context_11_1170_57976
  intro a
  fin_cases a
  · exact context_12_4680_57711
  · exact context_12_4681_57772
  · exact context_12_4682_57924
  · exact context_12_4683_57975

theorem selected_cut_01657 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18736) = some ⟨13, 1, 0, 3444, 18736, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18736_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18736 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18736 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18736, 1, 16384⟩
    (by decide) selected_cut_01657

theorem selected_cut_01658 : selected 8 ⟨57998, by decide⟩
    (prefixPartial 13 18737) = some ⟨13, 2, 0, 57998, 18737, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_18737_57998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18737 ⟨57998, by decide⟩ :=
  accepted_of_selected 13 18737 ⟨57998, by decide⟩ ⟨13, 2, 0, 57998, 18737, 2137, 16384⟩
    (by decide) selected_cut_01658

theorem selected_cut_01659 : selected 8 ⟨58017, by decide⟩
    (prefixPartial 13 18738) = some ⟨13, 2, 0, 58017, 18738, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_18738_58017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18738 ⟨58017, by decide⟩ :=
  accepted_of_selected 13 18738 ⟨58017, by decide⟩ ⟨13, 2, 0, 58017, 18738, 1745, 16384⟩
    (by decide) selected_cut_01659

theorem selected_cut_01660 : selected 8 ⟨58026, by decide⟩
    (prefixPartial 13 18739) = some ⟨13, 2, 0, 58026, 18739, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_18739_58026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18739 ⟨58026, by decide⟩ :=
  accepted_of_selected 13 18739 ⟨58026, by decide⟩ ⟨13, 2, 0, 58026, 18739, 1017, 16384⟩
    (by decide) selected_cut_01660

theorem unmarked_context_12_4684_58027 : frontier 9 ⟨58027, by decide⟩
    (prefixCache 12 4684) (prefixPartial 12 4684) = false := by
  decide +kernel

theorem node_context_12_4684_58027 : EJMOriginalGlobalDAGData.nodes 9 ⟨58027, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨57998, by decide⟩,⟨58017, by decide⟩,⟨58026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4684_58027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4684 ⟨58027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4684
    ⟨58027, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨57998, by decide⟩,⟨58017, by decide⟩,⟨58026, by decide⟩]) unmarked_context_12_4684_58027 node_context_12_4684_58027
  intro a
  fin_cases a
  · exact context_13_18736_3444
  · exact context_13_18737_57998
  · exact context_13_18738_58017
  · exact context_13_18739_58026

theorem selected_cut_01661 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18740) = some ⟨13, 1, 0, 3444, 18740, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18740_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18740 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18740 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18740, 1, 16384⟩
    (by decide) selected_cut_01661

theorem selected_cut_01662 : selected 8 ⟨58055, by decide⟩
    (prefixPartial 13 18741) = some ⟨13, 2, 0, 58055, 18741, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_18741_58055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18741 ⟨58055, by decide⟩ :=
  accepted_of_selected 13 18741 ⟨58055, by decide⟩ ⟨13, 2, 0, 58055, 18741, 2433, 16384⟩
    (by decide) selected_cut_01662

theorem selected_cut_01663 : selected 8 ⟨58075, by decide⟩
    (prefixPartial 13 18742) = some ⟨13, 2, 0, 58075, 18742, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_18742_58075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18742 ⟨58075, by decide⟩ :=
  accepted_of_selected 13 18742 ⟨58075, by decide⟩ ⟨13, 2, 0, 58075, 18742, 2353, 16384⟩
    (by decide) selected_cut_01663

theorem selected_cut_01664 : selected 8 ⟨58088, by decide⟩
    (prefixPartial 13 18743) = some ⟨13, 2, 0, 58088, 18743, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_18743_58088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18743 ⟨58088, by decide⟩ :=
  accepted_of_selected 13 18743 ⟨58088, by decide⟩ ⟨13, 2, 0, 58088, 18743, 1077, 16384⟩
    (by decide) selected_cut_01664

theorem unmarked_context_12_4685_58089 : frontier 9 ⟨58089, by decide⟩
    (prefixCache 12 4685) (prefixPartial 12 4685) = false := by
  decide +kernel

theorem node_context_12_4685_58089 : EJMOriginalGlobalDAGData.nodes 9 ⟨58089, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58055, by decide⟩,⟨58075, by decide⟩,⟨58088, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4685_58089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4685 ⟨58089, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4685
    ⟨58089, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58055, by decide⟩,⟨58075, by decide⟩,⟨58088, by decide⟩]) unmarked_context_12_4685_58089 node_context_12_4685_58089
  intro a
  fin_cases a
  · exact context_13_18740_3444
  · exact context_13_18741_58055
  · exact context_13_18742_58075
  · exact context_13_18743_58088

theorem selected_cut_01665 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18744) = some ⟨13, 1, 0, 3444, 18744, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18744_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18744 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18744 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18744, 1, 16384⟩
    (by decide) selected_cut_01665

theorem selected_cut_01666 : selected 8 ⟨58111, by decide⟩
    (prefixPartial 13 18745) = some ⟨13, 2, 0, 58111, 18745, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_18745_58111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18745 ⟨58111, by decide⟩ :=
  accepted_of_selected 13 18745 ⟨58111, by decide⟩ ⟨13, 2, 0, 58111, 18745, 2577, 16384⟩
    (by decide) selected_cut_01666

theorem selected_cut_01667 : selected 8 ⟨58134, by decide⟩
    (prefixPartial 13 18746) = some ⟨13, 2, 0, 58134, 18746, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_18746_58134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18746 ⟨58134, by decide⟩ :=
  accepted_of_selected 13 18746 ⟨58134, by decide⟩ ⟨13, 2, 0, 58134, 18746, 2365, 16384⟩
    (by decide) selected_cut_01667

theorem selected_cut_01668 : selected 8 ⟨58149, by decide⟩
    (prefixPartial 13 18747) = some ⟨13, 2, 0, 58149, 18747, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_18747_58149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18747 ⟨58149, by decide⟩ :=
  accepted_of_selected 13 18747 ⟨58149, by decide⟩ ⟨13, 2, 0, 58149, 18747, 1129, 16384⟩
    (by decide) selected_cut_01668

theorem unmarked_context_12_4686_58150 : frontier 9 ⟨58150, by decide⟩
    (prefixCache 12 4686) (prefixPartial 12 4686) = false := by
  decide +kernel

theorem node_context_12_4686_58150 : EJMOriginalGlobalDAGData.nodes 9 ⟨58150, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58111, by decide⟩,⟨58134, by decide⟩,⟨58149, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4686_58150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4686 ⟨58150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4686
    ⟨58150, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58111, by decide⟩,⟨58134, by decide⟩,⟨58149, by decide⟩]) unmarked_context_12_4686_58150 node_context_12_4686_58150
  intro a
  fin_cases a
  · exact context_13_18744_3444
  · exact context_13_18745_58111
  · exact context_13_18746_58134
  · exact context_13_18747_58149

theorem selected_cut_01669 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18748) = some ⟨13, 1, 0, 3444, 18748, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18748_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18748 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18748 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18748, 1, 16384⟩
    (by decide) selected_cut_01669

theorem selected_cut_01670 : selected 8 ⟨58171, by decide⟩
    (prefixPartial 13 18749) = some ⟨13, 2, 0, 58171, 18749, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_18749_58171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18749 ⟨58171, by decide⟩ :=
  accepted_of_selected 13 18749 ⟨58171, by decide⟩ ⟨13, 2, 0, 58171, 18749, 2289, 16384⟩
    (by decide) selected_cut_01670

theorem selected_cut_01671 : selected 8 ⟨58188, by decide⟩
    (prefixPartial 13 18750) = some ⟨13, 2, 0, 58188, 18750, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_18750_58188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18750 ⟨58188, by decide⟩ :=
  accepted_of_selected 13 18750 ⟨58188, by decide⟩ ⟨13, 2, 0, 58188, 18750, 2309, 16384⟩
    (by decide) selected_cut_01671

theorem selected_cut_01672 : selected 8 ⟨58199, by decide⟩
    (prefixPartial 13 18751) = some ⟨13, 2, 0, 58199, 18751, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_18751_58199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18751 ⟨58199, by decide⟩ :=
  accepted_of_selected 13 18751 ⟨58199, by decide⟩ ⟨13, 2, 0, 58199, 18751, 1209, 16384⟩
    (by decide) selected_cut_01672

theorem unmarked_context_12_4687_58200 : frontier 9 ⟨58200, by decide⟩
    (prefixCache 12 4687) (prefixPartial 12 4687) = false := by
  decide +kernel

theorem node_context_12_4687_58200 : EJMOriginalGlobalDAGData.nodes 9 ⟨58200, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58171, by decide⟩,⟨58188, by decide⟩,⟨58199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4687_58200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4687 ⟨58200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4687
    ⟨58200, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58171, by decide⟩,⟨58188, by decide⟩,⟨58199, by decide⟩]) unmarked_context_12_4687_58200 node_context_12_4687_58200
  intro a
  fin_cases a
  · exact context_13_18748_3444
  · exact context_13_18749_58171
  · exact context_13_18750_58188
  · exact context_13_18751_58199

theorem unmarked_context_11_1171_58201 : frontier 10 ⟨58201, by decide⟩
    (prefixCache 11 1171) (prefixPartial 11 1171) = false := by
  decide +kernel

theorem node_context_11_1171_58201 : EJMOriginalGlobalDAGData.nodes 10 ⟨58201, by decide⟩ =
    .split (coordinate 11) (![⟨58027, by decide⟩,⟨58089, by decide⟩,⟨58150, by decide⟩,⟨58200, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1171_58201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1171 ⟨58201, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1171
    ⟨58201, by decide⟩ (by decide) (![⟨58027, by decide⟩,⟨58089, by decide⟩,⟨58150, by decide⟩,⟨58200, by decide⟩]) unmarked_context_11_1171_58201 node_context_11_1171_58201
  intro a
  fin_cases a
  · exact context_12_4684_58027
  · exact context_12_4685_58089
  · exact context_12_4686_58150
  · exact context_12_4687_58200

theorem unmarked_context_10_292_58202 : frontier 11 ⟨58202, by decide⟩
    (prefixCache 10 292) (prefixPartial 10 292) = false := by
  decide +kernel

theorem node_context_10_292_58202 : EJMOriginalGlobalDAGData.nodes 11 ⟨58202, by decide⟩ =
    .split (coordinate 10) (![⟨57290, by decide⟩,⟨57655, by decide⟩,⟨57976, by decide⟩,⟨58201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_292_58202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 292 ⟨58202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 292
    ⟨58202, by decide⟩ (by decide) (![⟨57290, by decide⟩,⟨57655, by decide⟩,⟨57976, by decide⟩,⟨58201, by decide⟩]) unmarked_context_10_292_58202 node_context_10_292_58202
  intro a
  fin_cases a
  · exact context_11_1168_57290
  · exact context_11_1169_57655
  · exact context_11_1170_57976
  · exact context_11_1171_58201

theorem selected_cut_01673 : selected 9 ⟨58258, by decide⟩
    (prefixPartial 12 4688) = some ⟨12, 2, 0, 58258, 4688, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_4688_58258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4688 ⟨58258, by decide⟩ :=
  accepted_of_selected 12 4688 ⟨58258, by decide⟩ ⟨12, 2, 0, 58258, 4688, 3505, 65536⟩
    (by decide) selected_cut_01673

theorem selected_cut_01674 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18756) = some ⟨13, 1, 0, 3444, 18756, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18756_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18756 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18756 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18756, 1, 16384⟩
    (by decide) selected_cut_01674

theorem selected_cut_01675 : selected 8 ⟨58284, by decide⟩
    (prefixPartial 13 18757) = some ⟨13, 2, 0, 58284, 18757, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_18757_58284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18757 ⟨58284, by decide⟩ :=
  accepted_of_selected 13 18757 ⟨58284, by decide⟩ ⟨13, 2, 0, 58284, 18757, 2053, 16384⟩
    (by decide) selected_cut_01675

theorem selected_cut_01676 : selected 8 ⟨58308, by decide⟩
    (prefixPartial 13 18758) = some ⟨13, 2, 0, 58308, 18758, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_18758_58308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18758 ⟨58308, by decide⟩ :=
  accepted_of_selected 13 18758 ⟨58308, by decide⟩ ⟨13, 2, 0, 58308, 18758, 1789, 16384⟩
    (by decide) selected_cut_01676

theorem selected_cut_01677 : selected 8 ⟨58324, by decide⟩
    (prefixPartial 13 18759) = some ⟨13, 2, 0, 58324, 18759, 973, 16384⟩ := by
  decide +kernel

theorem context_13_18759_58324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18759 ⟨58324, by decide⟩ :=
  accepted_of_selected 13 18759 ⟨58324, by decide⟩ ⟨13, 2, 0, 58324, 18759, 973, 16384⟩
    (by decide) selected_cut_01677

theorem unmarked_context_12_4689_58325 : frontier 9 ⟨58325, by decide⟩
    (prefixCache 12 4689) (prefixPartial 12 4689) = false := by
  decide +kernel

theorem node_context_12_4689_58325 : EJMOriginalGlobalDAGData.nodes 9 ⟨58325, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58284, by decide⟩,⟨58308, by decide⟩,⟨58324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4689_58325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4689 ⟨58325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4689
    ⟨58325, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58284, by decide⟩,⟨58308, by decide⟩,⟨58324, by decide⟩]) unmarked_context_12_4689_58325 node_context_12_4689_58325
  intro a
  fin_cases a
  · exact context_13_18756_3444
  · exact context_13_18757_58284
  · exact context_13_18758_58308
  · exact context_13_18759_58324

theorem selected_cut_01678 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18760) = some ⟨13, 1, 0, 3444, 18760, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18760_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18760 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18760 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18760, 1, 16384⟩
    (by decide) selected_cut_01678

theorem selected_cut_01679 : selected 8 ⟨58348, by decide⟩
    (prefixPartial 13 18761) = some ⟨13, 2, 0, 58348, 18761, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_18761_58348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18761 ⟨58348, by decide⟩ :=
  accepted_of_selected 13 18761 ⟨58348, by decide⟩ ⟨13, 2, 0, 58348, 18761, 1901, 16384⟩
    (by decide) selected_cut_01679

theorem selected_cut_01680 : selected 8 ⟨58372, by decide⟩
    (prefixPartial 13 18762) = some ⟨13, 2, 0, 58372, 18762, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_18762_58372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18762 ⟨58372, by decide⟩ :=
  accepted_of_selected 13 18762 ⟨58372, by decide⟩ ⟨13, 2, 0, 58372, 18762, 1809, 16384⟩
    (by decide) selected_cut_01680

theorem selected_cut_01681 : selected 8 ⟨58383, by decide⟩
    (prefixPartial 13 18763) = some ⟨13, 2, 0, 58383, 18763, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_18763_58383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18763 ⟨58383, by decide⟩ :=
  accepted_of_selected 13 18763 ⟨58383, by decide⟩ ⟨13, 2, 0, 58383, 18763, 1013, 16384⟩
    (by decide) selected_cut_01681

theorem unmarked_context_12_4690_58384 : frontier 9 ⟨58384, by decide⟩
    (prefixCache 12 4690) (prefixPartial 12 4690) = false := by
  decide +kernel

theorem node_context_12_4690_58384 : EJMOriginalGlobalDAGData.nodes 9 ⟨58384, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58348, by decide⟩,⟨58372, by decide⟩,⟨58383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4690_58384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4690 ⟨58384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4690
    ⟨58384, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58348, by decide⟩,⟨58372, by decide⟩,⟨58383, by decide⟩]) unmarked_context_12_4690_58384 node_context_12_4690_58384
  intro a
  fin_cases a
  · exact context_13_18760_3444
  · exact context_13_18761_58348
  · exact context_13_18762_58372
  · exact context_13_18763_58383

theorem selected_cut_01682 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18764) = some ⟨13, 1, 0, 3444, 18764, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18764_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18764 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18764 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18764, 1, 16384⟩
    (by decide) selected_cut_01682

theorem selected_cut_01683 : selected 8 ⟨58413, by decide⟩
    (prefixPartial 13 18765) = some ⟨13, 2, 0, 58413, 18765, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_18765_58413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18765 ⟨58413, by decide⟩ :=
  accepted_of_selected 13 18765 ⟨58413, by decide⟩ ⟨13, 2, 0, 58413, 18765, 2017, 16384⟩
    (by decide) selected_cut_01683

theorem selected_cut_01684 : selected 8 ⟨58434, by decide⟩
    (prefixPartial 13 18766) = some ⟨13, 2, 0, 58434, 18766, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_18766_58434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18766 ⟨58434, by decide⟩ :=
  accepted_of_selected 13 18766 ⟨58434, by decide⟩ ⟨13, 2, 0, 58434, 18766, 1885, 16384⟩
    (by decide) selected_cut_01684

theorem selected_cut_01685 : selected 8 ⟨58453, by decide⟩
    (prefixPartial 13 18767) = some ⟨13, 2, 0, 58453, 18767, 997, 16384⟩ := by
  decide +kernel

theorem context_13_18767_58453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18767 ⟨58453, by decide⟩ :=
  accepted_of_selected 13 18767 ⟨58453, by decide⟩ ⟨13, 2, 0, 58453, 18767, 997, 16384⟩
    (by decide) selected_cut_01685

theorem unmarked_context_12_4691_58454 : frontier 9 ⟨58454, by decide⟩
    (prefixCache 12 4691) (prefixPartial 12 4691) = false := by
  decide +kernel

theorem node_context_12_4691_58454 : EJMOriginalGlobalDAGData.nodes 9 ⟨58454, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58413, by decide⟩,⟨58434, by decide⟩,⟨58453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4691_58454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4691 ⟨58454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4691
    ⟨58454, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58413, by decide⟩,⟨58434, by decide⟩,⟨58453, by decide⟩]) unmarked_context_12_4691_58454 node_context_12_4691_58454
  intro a
  fin_cases a
  · exact context_13_18764_3444
  · exact context_13_18765_58413
  · exact context_13_18766_58434
  · exact context_13_18767_58453

theorem unmarked_context_11_1172_58455 : frontier 10 ⟨58455, by decide⟩
    (prefixCache 11 1172) (prefixPartial 11 1172) = false := by
  decide +kernel

theorem node_context_11_1172_58455 : EJMOriginalGlobalDAGData.nodes 10 ⟨58455, by decide⟩ =
    .split (coordinate 11) (![⟨58258, by decide⟩,⟨58325, by decide⟩,⟨58384, by decide⟩,⟨58454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1172_58455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1172 ⟨58455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1172
    ⟨58455, by decide⟩ (by decide) (![⟨58258, by decide⟩,⟨58325, by decide⟩,⟨58384, by decide⟩,⟨58454, by decide⟩]) unmarked_context_11_1172_58455 node_context_11_1172_58455
  intro a
  fin_cases a
  · exact context_12_4688_58258
  · exact context_12_4689_58325
  · exact context_12_4690_58384
  · exact context_12_4691_58454

theorem selected_cut_01686 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18768) = some ⟨13, 1, 0, 3444, 18768, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18768_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18768 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18768 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18768, 1, 16384⟩
    (by decide) selected_cut_01686

theorem selected_cut_01687 : selected 8 ⟨58477, by decide⟩
    (prefixPartial 13 18769) = some ⟨13, 2, 0, 58477, 18769, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_18769_58477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18769 ⟨58477, by decide⟩ :=
  accepted_of_selected 13 18769 ⟨58477, by decide⟩ ⟨13, 2, 0, 58477, 18769, 1837, 16384⟩
    (by decide) selected_cut_01687

theorem selected_cut_01688 : selected 8 ⟨58501, by decide⟩
    (prefixPartial 13 18770) = some ⟨13, 2, 0, 58501, 18770, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_18770_58501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18770 ⟨58501, by decide⟩ :=
  accepted_of_selected 13 18770 ⟨58501, by decide⟩ ⟨13, 2, 0, 58501, 18770, 1813, 16384⟩
    (by decide) selected_cut_01688

theorem selected_cut_01689 : selected 8 ⟨58519, by decide⟩
    (prefixPartial 13 18771) = some ⟨13, 2, 0, 58519, 18771, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_18771_58519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18771 ⟨58519, by decide⟩ :=
  accepted_of_selected 13 18771 ⟨58519, by decide⟩ ⟨13, 2, 0, 58519, 18771, 1005, 16384⟩
    (by decide) selected_cut_01689

theorem unmarked_context_12_4692_58520 : frontier 9 ⟨58520, by decide⟩
    (prefixCache 12 4692) (prefixPartial 12 4692) = false := by
  decide +kernel

theorem node_context_12_4692_58520 : EJMOriginalGlobalDAGData.nodes 9 ⟨58520, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58477, by decide⟩,⟨58501, by decide⟩,⟨58519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4692_58520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4692 ⟨58520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4692
    ⟨58520, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58477, by decide⟩,⟨58501, by decide⟩,⟨58519, by decide⟩]) unmarked_context_12_4692_58520 node_context_12_4692_58520
  intro a
  fin_cases a
  · exact context_13_18768_3444
  · exact context_13_18769_58477
  · exact context_13_18770_58501
  · exact context_13_18771_58519

theorem selected_cut_01690 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18772) = some ⟨13, 1, 0, 3444, 18772, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18772_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18772 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18772 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18772, 1, 16384⟩
    (by decide) selected_cut_01690

theorem selected_cut_01691 : selected 8 ⟨58551, by decide⟩
    (prefixPartial 13 18773) = some ⟨13, 2, 0, 58551, 18773, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_18773_58551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18773 ⟨58551, by decide⟩ :=
  accepted_of_selected 13 18773 ⟨58551, by decide⟩ ⟨13, 2, 0, 58551, 18773, 2209, 16384⟩
    (by decide) selected_cut_01691

theorem selected_cut_01692 : selected 8 ⟨58572, by decide⟩
    (prefixPartial 13 18774) = some ⟨13, 2, 0, 58572, 18774, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_18774_58572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18774 ⟨58572, by decide⟩ :=
  accepted_of_selected 13 18774 ⟨58572, by decide⟩ ⟨13, 2, 0, 58572, 18774, 2337, 16384⟩
    (by decide) selected_cut_01692

theorem selected_cut_01693 : selected 8 ⟨58586, by decide⟩
    (prefixPartial 13 18775) = some ⟨13, 2, 0, 58586, 18775, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_18775_58586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18775 ⟨58586, by decide⟩ :=
  accepted_of_selected 13 18775 ⟨58586, by decide⟩ ⟨13, 2, 0, 58586, 18775, 1153, 16384⟩
    (by decide) selected_cut_01693

theorem unmarked_context_12_4693_58587 : frontier 9 ⟨58587, by decide⟩
    (prefixCache 12 4693) (prefixPartial 12 4693) = false := by
  decide +kernel

theorem node_context_12_4693_58587 : EJMOriginalGlobalDAGData.nodes 9 ⟨58587, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58551, by decide⟩,⟨58572, by decide⟩,⟨58586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4693_58587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4693 ⟨58587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4693
    ⟨58587, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58551, by decide⟩,⟨58572, by decide⟩,⟨58586, by decide⟩]) unmarked_context_12_4693_58587 node_context_12_4693_58587
  intro a
  fin_cases a
  · exact context_13_18772_3444
  · exact context_13_18773_58551
  · exact context_13_18774_58572
  · exact context_13_18775_58586

theorem selected_cut_01694 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18776) = some ⟨13, 1, 0, 3444, 18776, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18776_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18776 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18776 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18776, 1, 16384⟩
    (by decide) selected_cut_01694

theorem selected_cut_01695 : selected 8 ⟨58612, by decide⟩
    (prefixPartial 13 18777) = some ⟨13, 2, 0, 58612, 18777, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_18777_58612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18777 ⟨58612, by decide⟩ :=
  accepted_of_selected 13 18777 ⟨58612, by decide⟩ ⟨13, 2, 0, 58612, 18777, 2017, 16384⟩
    (by decide) selected_cut_01695

theorem selected_cut_01696 : selected 8 ⟨58634, by decide⟩
    (prefixPartial 13 18778) = some ⟨13, 2, 0, 58634, 18778, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_18778_58634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18778 ⟨58634, by decide⟩ :=
  accepted_of_selected 13 18778 ⟨58634, by decide⟩ ⟨13, 2, 0, 58634, 18778, 2241, 16384⟩
    (by decide) selected_cut_01696

theorem selected_cut_01697 : selected 8 ⟨58648, by decide⟩
    (prefixPartial 13 18779) = some ⟨13, 2, 0, 58648, 18779, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_18779_58648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18779 ⟨58648, by decide⟩ :=
  accepted_of_selected 13 18779 ⟨58648, by decide⟩ ⟨13, 2, 0, 58648, 18779, 1285, 16384⟩
    (by decide) selected_cut_01697

theorem unmarked_context_12_4694_58649 : frontier 9 ⟨58649, by decide⟩
    (prefixCache 12 4694) (prefixPartial 12 4694) = false := by
  decide +kernel

theorem node_context_12_4694_58649 : EJMOriginalGlobalDAGData.nodes 9 ⟨58649, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58612, by decide⟩,⟨58634, by decide⟩,⟨58648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4694_58649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4694 ⟨58649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4694
    ⟨58649, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58612, by decide⟩,⟨58634, by decide⟩,⟨58648, by decide⟩]) unmarked_context_12_4694_58649 node_context_12_4694_58649
  intro a
  fin_cases a
  · exact context_13_18776_3444
  · exact context_13_18777_58612
  · exact context_13_18778_58634
  · exact context_13_18779_58648

theorem selected_cut_01698 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18780) = some ⟨13, 1, 0, 3444, 18780, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18780_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18780 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18780 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18780, 1, 16384⟩
    (by decide) selected_cut_01698

theorem selected_cut_01699 : selected 8 ⟨58675, by decide⟩
    (prefixPartial 13 18781) = some ⟨13, 2, 0, 58675, 18781, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_18781_58675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18781 ⟨58675, by decide⟩ :=
  accepted_of_selected 13 18781 ⟨58675, by decide⟩ ⟨13, 2, 0, 58675, 18781, 2105, 16384⟩
    (by decide) selected_cut_01699

theorem selected_cut_01700 : selected 8 ⟨58707, by decide⟩
    (prefixPartial 13 18782) = some ⟨13, 2, 0, 58707, 18782, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_18782_58707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18782 ⟨58707, by decide⟩ :=
  accepted_of_selected 13 18782 ⟨58707, by decide⟩ ⟨13, 2, 0, 58707, 18782, 2649, 16384⟩
    (by decide) selected_cut_01700

theorem selected_cut_01701 : selected 8 ⟨58719, by decide⟩
    (prefixPartial 13 18783) = some ⟨13, 2, 0, 58719, 18783, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_18783_58719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18783 ⟨58719, by decide⟩ :=
  accepted_of_selected 13 18783 ⟨58719, by decide⟩ ⟨13, 2, 0, 58719, 18783, 1249, 16384⟩
    (by decide) selected_cut_01701

theorem unmarked_context_12_4695_58720 : frontier 9 ⟨58720, by decide⟩
    (prefixCache 12 4695) (prefixPartial 12 4695) = false := by
  decide +kernel

theorem node_context_12_4695_58720 : EJMOriginalGlobalDAGData.nodes 9 ⟨58720, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58675, by decide⟩,⟨58707, by decide⟩,⟨58719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4695_58720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4695 ⟨58720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4695
    ⟨58720, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58675, by decide⟩,⟨58707, by decide⟩,⟨58719, by decide⟩]) unmarked_context_12_4695_58720 node_context_12_4695_58720
  intro a
  fin_cases a
  · exact context_13_18780_3444
  · exact context_13_18781_58675
  · exact context_13_18782_58707
  · exact context_13_18783_58719

theorem unmarked_context_11_1173_58721 : frontier 10 ⟨58721, by decide⟩
    (prefixCache 11 1173) (prefixPartial 11 1173) = false := by
  decide +kernel

theorem node_context_11_1173_58721 : EJMOriginalGlobalDAGData.nodes 10 ⟨58721, by decide⟩ =
    .split (coordinate 11) (![⟨58520, by decide⟩,⟨58587, by decide⟩,⟨58649, by decide⟩,⟨58720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1173_58721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1173 ⟨58721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1173
    ⟨58721, by decide⟩ (by decide) (![⟨58520, by decide⟩,⟨58587, by decide⟩,⟨58649, by decide⟩,⟨58720, by decide⟩]) unmarked_context_11_1173_58721 node_context_11_1173_58721
  intro a
  fin_cases a
  · exact context_12_4692_58520
  · exact context_12_4693_58587
  · exact context_12_4694_58649
  · exact context_12_4695_58720

theorem selected_cut_01702 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18784) = some ⟨13, 1, 0, 3444, 18784, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18784_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18784 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18784 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18784, 1, 16384⟩
    (by decide) selected_cut_01702

theorem selected_cut_01703 : selected 8 ⟨58736, by decide⟩
    (prefixPartial 13 18785) = some ⟨13, 2, 0, 58736, 18785, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_18785_58736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18785 ⟨58736, by decide⟩ :=
  accepted_of_selected 13 18785 ⟨58736, by decide⟩ ⟨13, 2, 0, 58736, 18785, 1417, 16384⟩
    (by decide) selected_cut_01703

theorem selected_cut_01704 : selected 8 ⟨58760, by decide⟩
    (prefixPartial 13 18786) = some ⟨13, 2, 0, 58760, 18786, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_18786_58760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18786 ⟨58760, by decide⟩ :=
  accepted_of_selected 13 18786 ⟨58760, by decide⟩ ⟨13, 2, 0, 58760, 18786, 1765, 16384⟩
    (by decide) selected_cut_01704

theorem selected_cut_01705 : selected 8 ⟨58773, by decide⟩
    (prefixPartial 13 18787) = some ⟨13, 2, 0, 58773, 18787, 953, 16384⟩ := by
  decide +kernel

theorem context_13_18787_58773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18787 ⟨58773, by decide⟩ :=
  accepted_of_selected 13 18787 ⟨58773, by decide⟩ ⟨13, 2, 0, 58773, 18787, 953, 16384⟩
    (by decide) selected_cut_01705

theorem unmarked_context_12_4696_58774 : frontier 9 ⟨58774, by decide⟩
    (prefixCache 12 4696) (prefixPartial 12 4696) = false := by
  decide +kernel

theorem node_context_12_4696_58774 : EJMOriginalGlobalDAGData.nodes 9 ⟨58774, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58736, by decide⟩,⟨58760, by decide⟩,⟨58773, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4696_58774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4696 ⟨58774, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4696
    ⟨58774, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58736, by decide⟩,⟨58760, by decide⟩,⟨58773, by decide⟩]) unmarked_context_12_4696_58774 node_context_12_4696_58774
  intro a
  fin_cases a
  · exact context_13_18784_3444
  · exact context_13_18785_58736
  · exact context_13_18786_58760
  · exact context_13_18787_58773

theorem selected_cut_01706 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18788) = some ⟨13, 1, 0, 3444, 18788, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18788_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18788 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18788 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18788, 1, 16384⟩
    (by decide) selected_cut_01706

theorem selected_cut_01707 : selected 8 ⟨58797, by decide⟩
    (prefixPartial 13 18789) = some ⟨13, 2, 0, 58797, 18789, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_18789_58797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18789 ⟨58797, by decide⟩ :=
  accepted_of_selected 13 18789 ⟨58797, by decide⟩ ⟨13, 2, 0, 58797, 18789, 1937, 16384⟩
    (by decide) selected_cut_01707

theorem selected_cut_01708 : selected 8 ⟨58822, by decide⟩
    (prefixPartial 13 18790) = some ⟨13, 2, 0, 58822, 18790, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_18790_58822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18790 ⟨58822, by decide⟩ :=
  accepted_of_selected 13 18790 ⟨58822, by decide⟩ ⟨13, 2, 0, 58822, 18790, 2349, 16384⟩
    (by decide) selected_cut_01708

theorem selected_cut_01709 : selected 8 ⟨58838, by decide⟩
    (prefixPartial 13 18791) = some ⟨13, 2, 0, 58838, 18791, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_18791_58838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18791 ⟨58838, by decide⟩ :=
  accepted_of_selected 13 18791 ⟨58838, by decide⟩ ⟨13, 2, 0, 58838, 18791, 1197, 16384⟩
    (by decide) selected_cut_01709

theorem unmarked_context_12_4697_58839 : frontier 9 ⟨58839, by decide⟩
    (prefixCache 12 4697) (prefixPartial 12 4697) = false := by
  decide +kernel

theorem node_context_12_4697_58839 : EJMOriginalGlobalDAGData.nodes 9 ⟨58839, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58797, by decide⟩,⟨58822, by decide⟩,⟨58838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4697_58839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4697 ⟨58839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4697
    ⟨58839, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58797, by decide⟩,⟨58822, by decide⟩,⟨58838, by decide⟩]) unmarked_context_12_4697_58839 node_context_12_4697_58839
  intro a
  fin_cases a
  · exact context_13_18788_3444
  · exact context_13_18789_58797
  · exact context_13_18790_58822
  · exact context_13_18791_58838

theorem selected_cut_01710 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18792) = some ⟨13, 1, 0, 3444, 18792, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18792_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18792 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18792 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18792, 1, 16384⟩
    (by decide) selected_cut_01710

theorem selected_cut_01711 : selected 8 ⟨58887, by decide⟩
    (prefixPartial 13 18793) = some ⟨13, 2, 0, 58887, 18793, 2941, 16384⟩ := by
  decide +kernel

theorem context_13_18793_58887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18793 ⟨58887, by decide⟩ :=
  accepted_of_selected 13 18793 ⟨58887, by decide⟩ ⟨13, 2, 0, 58887, 18793, 2941, 16384⟩
    (by decide) selected_cut_01711

theorem selected_cut_01712 : selected 7 ⟨58902, by decide⟩
    (prefixPartial 14 75176) = some ⟨14, 2, 0, 58902, 75176, 1069, 4096⟩ := by
  decide +kernel

theorem context_14_75176_58902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 75176 ⟨58902, by decide⟩ :=
  accepted_of_selected 14 75176 ⟨58902, by decide⟩ ⟨14, 2, 0, 58902, 75176, 1069, 4096⟩
    (by decide) selected_cut_01712

theorem selected_cut_01713 : selected 7 ⟨58936, by decide⟩
    (prefixPartial 14 75177) = some ⟨14, 2, 0, 58936, 75177, 1333, 4096⟩ := by
  decide +kernel

theorem context_14_75177_58936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 75177 ⟨58936, by decide⟩ :=
  accepted_of_selected 14 75177 ⟨58936, by decide⟩ ⟨14, 2, 0, 58936, 75177, 1333, 4096⟩
    (by decide) selected_cut_01713

theorem selected_cut_01714 : selected 7 ⟨58955, by decide⟩
    (prefixPartial 14 75178) = some ⟨14, 2, 0, 58955, 75178, 917, 4096⟩ := by
  decide +kernel

theorem context_14_75178_58955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 75178 ⟨58955, by decide⟩ :=
  accepted_of_selected 14 75178 ⟨58955, by decide⟩ ⟨14, 2, 0, 58955, 75178, 917, 4096⟩
    (by decide) selected_cut_01714

theorem selected_cut_01715 : selected 7 ⟨58971, by decide⟩
    (prefixPartial 14 75179) = some ⟨14, 2, 0, 58971, 75179, 873, 4096⟩ := by
  decide +kernel

theorem context_14_75179_58971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 75179 ⟨58971, by decide⟩ :=
  accepted_of_selected 14 75179 ⟨58971, by decide⟩ ⟨14, 2, 0, 58971, 75179, 873, 4096⟩
    (by decide) selected_cut_01715

theorem unmarked_context_13_18794_58972 : frontier 8 ⟨58972, by decide⟩
    (prefixCache 13 18794) (prefixPartial 13 18794) = false := by
  decide +kernel

theorem node_context_13_18794_58972 : EJMOriginalGlobalDAGData.nodes 8 ⟨58972, by decide⟩ =
    .split (coordinate 13) (![⟨58902, by decide⟩,⟨58936, by decide⟩,⟨58955, by decide⟩,⟨58971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_18794_58972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18794 ⟨58972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 18794
    ⟨58972, by decide⟩ (by decide) (![⟨58902, by decide⟩,⟨58936, by decide⟩,⟨58955, by decide⟩,⟨58971, by decide⟩]) unmarked_context_13_18794_58972 node_context_13_18794_58972
  intro a
  fin_cases a
  · exact context_14_75176_58902
  · exact context_14_75177_58936
  · exact context_14_75178_58955
  · exact context_14_75179_58971

theorem selected_cut_01716 : selected 8 ⟨59020, by decide⟩
    (prefixPartial 13 18795) = some ⟨13, 2, 0, 59020, 18795, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_18795_59020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18795 ⟨59020, by decide⟩ :=
  accepted_of_selected 13 18795 ⟨59020, by decide⟩ ⟨13, 2, 0, 59020, 18795, 1813, 16384⟩
    (by decide) selected_cut_01716

theorem unmarked_context_12_4698_59021 : frontier 9 ⟨59021, by decide⟩
    (prefixCache 12 4698) (prefixPartial 12 4698) = false := by
  decide +kernel

theorem node_context_12_4698_59021 : EJMOriginalGlobalDAGData.nodes 9 ⟨59021, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨58887, by decide⟩,⟨58972, by decide⟩,⟨59020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4698_59021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4698 ⟨59021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4698
    ⟨59021, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨58887, by decide⟩,⟨58972, by decide⟩,⟨59020, by decide⟩]) unmarked_context_12_4698_59021 node_context_12_4698_59021
  intro a
  fin_cases a
  · exact context_13_18792_3444
  · exact context_13_18793_58887
  · exact context_13_18794_58972
  · exact context_13_18795_59020

theorem selected_cut_01717 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18796) = some ⟨13, 1, 0, 3444, 18796, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18796_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18796 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18796 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18796, 1, 16384⟩
    (by decide) selected_cut_01717

theorem selected_cut_01718 : selected 8 ⟨59045, by decide⟩
    (prefixPartial 13 18797) = some ⟨13, 2, 0, 59045, 18797, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_18797_59045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18797 ⟨59045, by decide⟩ :=
  accepted_of_selected 13 18797 ⟨59045, by decide⟩ ⟨13, 2, 0, 59045, 18797, 1825, 16384⟩
    (by decide) selected_cut_01718

theorem selected_cut_01719 : selected 8 ⟨59075, by decide⟩
    (prefixPartial 13 18798) = some ⟨13, 2, 0, 59075, 18798, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_18798_59075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18798 ⟨59075, by decide⟩ :=
  accepted_of_selected 13 18798 ⟨59075, by decide⟩ ⟨13, 2, 0, 59075, 18798, 2385, 16384⟩
    (by decide) selected_cut_01719

theorem selected_cut_01720 : selected 8 ⟨59086, by decide⟩
    (prefixPartial 13 18799) = some ⟨13, 2, 0, 59086, 18799, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_18799_59086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18799 ⟨59086, by decide⟩ :=
  accepted_of_selected 13 18799 ⟨59086, by decide⟩ ⟨13, 2, 0, 59086, 18799, 1189, 16384⟩
    (by decide) selected_cut_01720

theorem unmarked_context_12_4699_59087 : frontier 9 ⟨59087, by decide⟩
    (prefixCache 12 4699) (prefixPartial 12 4699) = false := by
  decide +kernel

theorem node_context_12_4699_59087 : EJMOriginalGlobalDAGData.nodes 9 ⟨59087, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59045, by decide⟩,⟨59075, by decide⟩,⟨59086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4699_59087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4699 ⟨59087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4699
    ⟨59087, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59045, by decide⟩,⟨59075, by decide⟩,⟨59086, by decide⟩]) unmarked_context_12_4699_59087 node_context_12_4699_59087
  intro a
  fin_cases a
  · exact context_13_18796_3444
  · exact context_13_18797_59045
  · exact context_13_18798_59075
  · exact context_13_18799_59086

theorem unmarked_context_11_1174_59088 : frontier 10 ⟨59088, by decide⟩
    (prefixCache 11 1174) (prefixPartial 11 1174) = false := by
  decide +kernel

theorem node_context_11_1174_59088 : EJMOriginalGlobalDAGData.nodes 10 ⟨59088, by decide⟩ =
    .split (coordinate 11) (![⟨58774, by decide⟩,⟨58839, by decide⟩,⟨59021, by decide⟩,⟨59087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1174_59088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1174 ⟨59088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1174
    ⟨59088, by decide⟩ (by decide) (![⟨58774, by decide⟩,⟨58839, by decide⟩,⟨59021, by decide⟩,⟨59087, by decide⟩]) unmarked_context_11_1174_59088 node_context_11_1174_59088
  intro a
  fin_cases a
  · exact context_12_4696_58774
  · exact context_12_4697_58839
  · exact context_12_4698_59021
  · exact context_12_4699_59087

theorem selected_cut_01721 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18800) = some ⟨13, 1, 0, 3444, 18800, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18800_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18800 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18800 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18800, 1, 16384⟩
    (by decide) selected_cut_01721

theorem selected_cut_01722 : selected 8 ⟨59104, by decide⟩
    (prefixPartial 13 18801) = some ⟨13, 2, 0, 59104, 18801, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_18801_59104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18801 ⟨59104, by decide⟩ :=
  accepted_of_selected 13 18801 ⟨59104, by decide⟩ ⟨13, 2, 0, 59104, 18801, 1505, 16384⟩
    (by decide) selected_cut_01722

theorem selected_cut_01723 : selected 8 ⟨59126, by decide⟩
    (prefixPartial 13 18802) = some ⟨13, 2, 0, 59126, 18802, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_18802_59126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18802 ⟨59126, by decide⟩ :=
  accepted_of_selected 13 18802 ⟨59126, by decide⟩ ⟨13, 2, 0, 59126, 18802, 2009, 16384⟩
    (by decide) selected_cut_01723

theorem selected_cut_01724 : selected 8 ⟨59143, by decide⟩
    (prefixPartial 13 18803) = some ⟨13, 2, 0, 59143, 18803, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_18803_59143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18803 ⟨59143, by decide⟩ :=
  accepted_of_selected 13 18803 ⟨59143, by decide⟩ ⟨13, 2, 0, 59143, 18803, 1117, 16384⟩
    (by decide) selected_cut_01724

theorem unmarked_context_12_4700_59144 : frontier 9 ⟨59144, by decide⟩
    (prefixCache 12 4700) (prefixPartial 12 4700) = false := by
  decide +kernel

theorem node_context_12_4700_59144 : EJMOriginalGlobalDAGData.nodes 9 ⟨59144, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59104, by decide⟩,⟨59126, by decide⟩,⟨59143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4700_59144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4700 ⟨59144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4700
    ⟨59144, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59104, by decide⟩,⟨59126, by decide⟩,⟨59143, by decide⟩]) unmarked_context_12_4700_59144 node_context_12_4700_59144
  intro a
  fin_cases a
  · exact context_13_18800_3444
  · exact context_13_18801_59104
  · exact context_13_18802_59126
  · exact context_13_18803_59143

theorem selected_cut_01725 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18804) = some ⟨13, 1, 0, 3444, 18804, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18804_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18804 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18804 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18804, 1, 16384⟩
    (by decide) selected_cut_01725

theorem selected_cut_01726 : selected 8 ⟨59169, by decide⟩
    (prefixPartial 13 18805) = some ⟨13, 2, 0, 59169, 18805, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_18805_59169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18805 ⟨59169, by decide⟩ :=
  accepted_of_selected 13 18805 ⟨59169, by decide⟩ ⟨13, 2, 0, 59169, 18805, 1885, 16384⟩
    (by decide) selected_cut_01726

theorem selected_cut_01727 : selected 8 ⟨59203, by decide⟩
    (prefixPartial 13 18806) = some ⟨13, 2, 0, 59203, 18806, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_18806_59203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18806 ⟨59203, by decide⟩ :=
  accepted_of_selected 13 18806 ⟨59203, by decide⟩ ⟨13, 2, 0, 59203, 18806, 2637, 16384⟩
    (by decide) selected_cut_01727

theorem selected_cut_01728 : selected 8 ⟨59228, by decide⟩
    (prefixPartial 13 18807) = some ⟨13, 2, 0, 59228, 18807, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_18807_59228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18807 ⟨59228, by decide⟩ :=
  accepted_of_selected 13 18807 ⟨59228, by decide⟩ ⟨13, 2, 0, 59228, 18807, 1293, 16384⟩
    (by decide) selected_cut_01728

theorem unmarked_context_12_4701_59229 : frontier 9 ⟨59229, by decide⟩
    (prefixCache 12 4701) (prefixPartial 12 4701) = false := by
  decide +kernel

theorem node_context_12_4701_59229 : EJMOriginalGlobalDAGData.nodes 9 ⟨59229, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨59169, by decide⟩,⟨59203, by decide⟩,⟨59228, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4701_59229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4701 ⟨59229, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4701
    ⟨59229, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨59169, by decide⟩,⟨59203, by decide⟩,⟨59228, by decide⟩]) unmarked_context_12_4701_59229 node_context_12_4701_59229
  intro a
  fin_cases a
  · exact context_13_18804_3444
  · exact context_13_18805_59169
  · exact context_13_18806_59203
  · exact context_13_18807_59228

theorem selected_cut_01729 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 18808) = some ⟨13, 1, 0, 3444, 18808, 1, 16384⟩ := by
  decide +kernel

theorem context_13_18808_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18808 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 18808 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 18808, 1, 16384⟩
    (by decide) selected_cut_01729

theorem selected_cut_01730 : selected 8 ⟨59248, by decide⟩
    (prefixPartial 13 18809) = some ⟨13, 2, 0, 59248, 18809, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_18809_59248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18809 ⟨59248, by decide⟩ :=
  accepted_of_selected 13 18809 ⟨59248, by decide⟩ ⟨13, 2, 0, 59248, 18809, 1769, 16384⟩
    (by decide) selected_cut_01730

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
