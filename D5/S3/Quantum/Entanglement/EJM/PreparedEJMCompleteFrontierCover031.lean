/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover030
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_02979 : selected 7 ⟨92536, by decide⟩
    (prefixPartial 14 106917) = some ⟨14, 2, 0, 92536, 106917, 1301, 4096⟩ := by
  decide +kernel

theorem context_14_106917_92536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106917 ⟨92536, by decide⟩ :=
  accepted_of_selected 14 106917 ⟨92536, by decide⟩ ⟨14, 2, 0, 92536, 106917, 1301, 4096⟩
    (by decide) selected_cut_02979

theorem selected_cut_02980 : selected 7 ⟨92571, by decide⟩
    (prefixPartial 14 106918) = some ⟨14, 2, 0, 92571, 106918, 1237, 4096⟩ := by
  decide +kernel

theorem context_14_106918_92571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106918 ⟨92571, by decide⟩ :=
  accepted_of_selected 14 106918 ⟨92571, by decide⟩ ⟨14, 2, 0, 92571, 106918, 1237, 4096⟩
    (by decide) selected_cut_02980

theorem selected_cut_02981 : selected 7 ⟨92595, by decide⟩
    (prefixPartial 14 106919) = some ⟨14, 2, 0, 92595, 106919, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_106919_92595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106919 ⟨92595, by decide⟩ :=
  accepted_of_selected 14 106919 ⟨92595, by decide⟩ ⟨14, 2, 0, 92595, 106919, 1021, 4096⟩
    (by decide) selected_cut_02981

theorem unmarked_context_13_26729_92596 : frontier 8 ⟨92596, by decide⟩
    (prefixCache 13 26729) (prefixPartial 13 26729) = false := by
  decide +kernel

theorem node_context_13_26729_92596 : EJMOriginalGlobalDAGData.nodes 8 ⟨92596, by decide⟩ =
    .split (coordinate 13) (![⟨92497, by decide⟩,⟨92536, by decide⟩,⟨92571, by decide⟩,⟨92595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26729_92596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26729 ⟨92596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26729
    ⟨92596, by decide⟩ (by decide) (![⟨92497, by decide⟩,⟨92536, by decide⟩,⟨92571, by decide⟩,⟨92595, by decide⟩]) unmarked_context_13_26729_92596 node_context_13_26729_92596
  intro a
  fin_cases a
  · exact context_14_106916_92497
  · exact context_14_106917_92536
  · exact context_14_106918_92571
  · exact context_14_106919_92595

theorem selected_cut_02982 : selected 8 ⟨92677, by decide⟩
    (prefixPartial 13 26730) = some ⟨13, 2, 0, 92677, 26730, 2997, 16384⟩ := by
  decide +kernel

theorem context_13_26730_92677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26730 ⟨92677, by decide⟩ :=
  accepted_of_selected 13 26730 ⟨92677, by decide⟩ ⟨13, 2, 0, 92677, 26730, 2997, 16384⟩
    (by decide) selected_cut_02982

theorem selected_cut_02983 : selected 8 ⟨92755, by decide⟩
    (prefixPartial 13 26731) = some ⟨13, 2, 0, 92755, 26731, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_26731_92755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26731 ⟨92755, by decide⟩ :=
  accepted_of_selected 13 26731 ⟨92755, by decide⟩ ⟨13, 2, 0, 92755, 26731, 1537, 16384⟩
    (by decide) selected_cut_02983

theorem unmarked_context_12_6682_92756 : frontier 9 ⟨92756, by decide⟩
    (prefixCache 12 6682) (prefixPartial 12 6682) = false := by
  decide +kernel

theorem node_context_12_6682_92756 : EJMOriginalGlobalDAGData.nodes 9 ⟨92756, by decide⟩ =
    .split (coordinate 12) (![⟨92477, by decide⟩,⟨92596, by decide⟩,⟨92677, by decide⟩,⟨92755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6682_92756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6682 ⟨92756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6682
    ⟨92756, by decide⟩ (by decide) (![⟨92477, by decide⟩,⟨92596, by decide⟩,⟨92677, by decide⟩,⟨92755, by decide⟩]) unmarked_context_12_6682_92756 node_context_12_6682_92756
  intro a
  fin_cases a
  · exact context_13_26728_92477
  · exact context_13_26729_92596
  · exact context_13_26730_92677
  · exact context_13_26731_92755

theorem selected_cut_02984 : selected 8 ⟨92817, by decide⟩
    (prefixPartial 13 26732) = some ⟨13, 2, 0, 92817, 26732, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_26732_92817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26732 ⟨92817, by decide⟩ :=
  accepted_of_selected 13 26732 ⟨92817, by decide⟩ ⟨13, 2, 0, 92817, 26732, 1857, 16384⟩
    (by decide) selected_cut_02984

theorem selected_cut_02985 : selected 8 ⟨92894, by decide⟩
    (prefixPartial 13 26733) = some ⟨13, 2, 0, 92894, 26733, 3337, 16384⟩ := by
  decide +kernel

theorem context_13_26733_92894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26733 ⟨92894, by decide⟩ :=
  accepted_of_selected 13 26733 ⟨92894, by decide⟩ ⟨13, 2, 0, 92894, 26733, 3337, 16384⟩
    (by decide) selected_cut_02985

theorem selected_cut_02986 : selected 8 ⟨92932, by decide⟩
    (prefixPartial 13 26734) = some ⟨13, 2, 0, 92932, 26734, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_26734_92932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26734 ⟨92932, by decide⟩ :=
  accepted_of_selected 13 26734 ⟨92932, by decide⟩ ⟨13, 2, 0, 92932, 26734, 1917, 16384⟩
    (by decide) selected_cut_02986

theorem selected_cut_02987 : selected 8 ⟨92965, by decide⟩
    (prefixPartial 13 26735) = some ⟨13, 2, 0, 92965, 26735, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_26735_92965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26735 ⟨92965, by decide⟩ :=
  accepted_of_selected 13 26735 ⟨92965, by decide⟩ ⟨13, 2, 0, 92965, 26735, 1249, 16384⟩
    (by decide) selected_cut_02987

theorem unmarked_context_12_6683_92966 : frontier 9 ⟨92966, by decide⟩
    (prefixCache 12 6683) (prefixPartial 12 6683) = false := by
  decide +kernel

theorem node_context_12_6683_92966 : EJMOriginalGlobalDAGData.nodes 9 ⟨92966, by decide⟩ =
    .split (coordinate 12) (![⟨92817, by decide⟩,⟨92894, by decide⟩,⟨92932, by decide⟩,⟨92965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6683_92966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6683 ⟨92966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6683
    ⟨92966, by decide⟩ (by decide) (![⟨92817, by decide⟩,⟨92894, by decide⟩,⟨92932, by decide⟩,⟨92965, by decide⟩]) unmarked_context_12_6683_92966 node_context_12_6683_92966
  intro a
  fin_cases a
  · exact context_13_26732_92817
  · exact context_13_26733_92894
  · exact context_13_26734_92932
  · exact context_13_26735_92965

theorem unmarked_context_11_1670_92967 : frontier 10 ⟨92967, by decide⟩
    (prefixCache 11 1670) (prefixPartial 11 1670) = false := by
  decide +kernel

theorem node_context_11_1670_92967 : EJMOriginalGlobalDAGData.nodes 10 ⟨92967, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨92379, by decide⟩,⟨92756, by decide⟩,⟨92966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1670_92967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1670 ⟨92967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1670
    ⟨92967, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨92379, by decide⟩,⟨92756, by decide⟩,⟨92966, by decide⟩]) unmarked_context_11_1670_92967 node_context_11_1670_92967
  intro a
  fin_cases a
  · exact context_12_6680_1738
  · exact context_12_6681_92379
  · exact context_12_6682_92756
  · exact context_12_6683_92966

theorem selected_cut_02988 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6684) = some ⟨12, 1, 0, 1738, 6684, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6684_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6684 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6684 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6684, 1, 65536⟩
    (by decide) selected_cut_02988

theorem selected_cut_02989 : selected 8 ⟨93012, by decide⟩
    (prefixPartial 13 26740) = some ⟨13, 2, 0, 93012, 26740, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_26740_93012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26740 ⟨93012, by decide⟩ :=
  accepted_of_selected 13 26740 ⟨93012, by decide⟩ ⟨13, 2, 0, 93012, 26740, 1317, 16384⟩
    (by decide) selected_cut_02989

theorem selected_cut_02990 : selected 8 ⟨93089, by decide⟩
    (prefixPartial 13 26741) = some ⟨13, 2, 0, 93089, 26741, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_26741_93089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26741 ⟨93089, by decide⟩ :=
  accepted_of_selected 13 26741 ⟨93089, by decide⟩ ⟨13, 2, 0, 93089, 26741, 2389, 16384⟩
    (by decide) selected_cut_02990

theorem selected_cut_02991 : selected 8 ⟨93120, by decide⟩
    (prefixPartial 13 26742) = some ⟨13, 2, 0, 93120, 26742, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_26742_93120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26742 ⟨93120, by decide⟩ :=
  accepted_of_selected 13 26742 ⟨93120, by decide⟩ ⟨13, 2, 0, 93120, 26742, 1433, 16384⟩
    (by decide) selected_cut_02991

theorem selected_cut_02992 : selected 8 ⟨93143, by decide⟩
    (prefixPartial 13 26743) = some ⟨13, 2, 0, 93143, 26743, 853, 16384⟩ := by
  decide +kernel

theorem context_13_26743_93143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26743 ⟨93143, by decide⟩ :=
  accepted_of_selected 13 26743 ⟨93143, by decide⟩ ⟨13, 2, 0, 93143, 26743, 853, 16384⟩
    (by decide) selected_cut_02992

theorem unmarked_context_12_6685_93144 : frontier 9 ⟨93144, by decide⟩
    (prefixCache 12 6685) (prefixPartial 12 6685) = false := by
  decide +kernel

theorem node_context_12_6685_93144 : EJMOriginalGlobalDAGData.nodes 9 ⟨93144, by decide⟩ =
    .split (coordinate 12) (![⟨93012, by decide⟩,⟨93089, by decide⟩,⟨93120, by decide⟩,⟨93143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6685_93144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6685 ⟨93144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6685
    ⟨93144, by decide⟩ (by decide) (![⟨93012, by decide⟩,⟨93089, by decide⟩,⟨93120, by decide⟩,⟨93143, by decide⟩]) unmarked_context_12_6685_93144 node_context_12_6685_93144
  intro a
  fin_cases a
  · exact context_13_26740_93012
  · exact context_13_26741_93089
  · exact context_13_26742_93120
  · exact context_13_26743_93143

theorem selected_cut_02993 : selected 8 ⟨93175, by decide⟩
    (prefixPartial 13 26744) = some ⟨13, 2, 0, 93175, 26744, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_26744_93175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26744 ⟨93175, by decide⟩ :=
  accepted_of_selected 13 26744 ⟨93175, by decide⟩ ⟨13, 2, 0, 93175, 26744, 1237, 16384⟩
    (by decide) selected_cut_02993

theorem selected_cut_02994 : selected 8 ⟨93234, by decide⟩
    (prefixPartial 13 26745) = some ⟨13, 2, 0, 93234, 26745, 3421, 16384⟩ := by
  decide +kernel

theorem context_13_26745_93234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26745 ⟨93234, by decide⟩ :=
  accepted_of_selected 13 26745 ⟨93234, by decide⟩ ⟨13, 2, 0, 93234, 26745, 3421, 16384⟩
    (by decide) selected_cut_02994

theorem selected_cut_02995 : selected 8 ⟨93269, by decide⟩
    (prefixPartial 13 26746) = some ⟨13, 2, 0, 93269, 26746, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_26746_93269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26746 ⟨93269, by decide⟩ :=
  accepted_of_selected 13 26746 ⟨93269, by decide⟩ ⟨13, 2, 0, 93269, 26746, 2045, 16384⟩
    (by decide) selected_cut_02995

theorem selected_cut_02996 : selected 8 ⟨93285, by decide⟩
    (prefixPartial 13 26747) = some ⟨13, 2, 0, 93285, 26747, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_26747_93285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26747 ⟨93285, by decide⟩ :=
  accepted_of_selected 13 26747 ⟨93285, by decide⟩ ⟨13, 2, 0, 93285, 26747, 1097, 16384⟩
    (by decide) selected_cut_02996

theorem unmarked_context_12_6686_93286 : frontier 9 ⟨93286, by decide⟩
    (prefixCache 12 6686) (prefixPartial 12 6686) = false := by
  decide +kernel

theorem node_context_12_6686_93286 : EJMOriginalGlobalDAGData.nodes 9 ⟨93286, by decide⟩ =
    .split (coordinate 12) (![⟨93175, by decide⟩,⟨93234, by decide⟩,⟨93269, by decide⟩,⟨93285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6686_93286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6686 ⟨93286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6686
    ⟨93286, by decide⟩ (by decide) (![⟨93175, by decide⟩,⟨93234, by decide⟩,⟨93269, by decide⟩,⟨93285, by decide⟩]) unmarked_context_12_6686_93286 node_context_12_6686_93286
  intro a
  fin_cases a
  · exact context_13_26744_93175
  · exact context_13_26745_93234
  · exact context_13_26746_93269
  · exact context_13_26747_93285

theorem selected_cut_02997 : selected 8 ⟨93334, by decide⟩
    (prefixPartial 13 26748) = some ⟨13, 2, 0, 93334, 26748, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_26748_93334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26748 ⟨93334, by decide⟩ :=
  accepted_of_selected 13 26748 ⟨93334, by decide⟩ ⟨13, 2, 0, 93334, 26748, 1445, 16384⟩
    (by decide) selected_cut_02997

theorem selected_cut_02998 : selected 8 ⟨93407, by decide⟩
    (prefixPartial 13 26749) = some ⟨13, 2, 0, 93407, 26749, 3681, 16384⟩ := by
  decide +kernel

theorem context_13_26749_93407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26749 ⟨93407, by decide⟩ :=
  accepted_of_selected 13 26749 ⟨93407, by decide⟩ ⟨13, 2, 0, 93407, 26749, 3681, 16384⟩
    (by decide) selected_cut_02998

theorem selected_cut_02999 : selected 8 ⟨93432, by decide⟩
    (prefixPartial 13 26750) = some ⟨13, 2, 0, 93432, 26750, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_26750_93432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26750 ⟨93432, by decide⟩ :=
  accepted_of_selected 13 26750 ⟨93432, by decide⟩ ⟨13, 2, 0, 93432, 26750, 2129, 16384⟩
    (by decide) selected_cut_02999

theorem selected_cut_03000 : selected 8 ⟨93450, by decide⟩
    (prefixPartial 13 26751) = some ⟨13, 2, 0, 93450, 26751, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_26751_93450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26751 ⟨93450, by decide⟩ :=
  accepted_of_selected 13 26751 ⟨93450, by decide⟩ ⟨13, 2, 0, 93450, 26751, 1269, 16384⟩
    (by decide) selected_cut_03000

theorem unmarked_context_12_6687_93451 : frontier 9 ⟨93451, by decide⟩
    (prefixCache 12 6687) (prefixPartial 12 6687) = false := by
  decide +kernel

theorem node_context_12_6687_93451 : EJMOriginalGlobalDAGData.nodes 9 ⟨93451, by decide⟩ =
    .split (coordinate 12) (![⟨93334, by decide⟩,⟨93407, by decide⟩,⟨93432, by decide⟩,⟨93450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6687_93451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6687 ⟨93451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6687
    ⟨93451, by decide⟩ (by decide) (![⟨93334, by decide⟩,⟨93407, by decide⟩,⟨93432, by decide⟩,⟨93450, by decide⟩]) unmarked_context_12_6687_93451 node_context_12_6687_93451
  intro a
  fin_cases a
  · exact context_13_26748_93334
  · exact context_13_26749_93407
  · exact context_13_26750_93432
  · exact context_13_26751_93450

theorem unmarked_context_11_1671_93452 : frontier 10 ⟨93452, by decide⟩
    (prefixCache 11 1671) (prefixPartial 11 1671) = false := by
  decide +kernel

theorem node_context_11_1671_93452 : EJMOriginalGlobalDAGData.nodes 10 ⟨93452, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨93144, by decide⟩,⟨93286, by decide⟩,⟨93451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1671_93452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1671 ⟨93452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1671
    ⟨93452, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨93144, by decide⟩,⟨93286, by decide⟩,⟨93451, by decide⟩]) unmarked_context_11_1671_93452 node_context_11_1671_93452
  intro a
  fin_cases a
  · exact context_12_6684_1738
  · exact context_12_6685_93144
  · exact context_12_6686_93286
  · exact context_12_6687_93451

theorem unmarked_context_10_417_93453 : frontier 11 ⟨93453, by decide⟩
    (prefixCache 10 417) (prefixPartial 10 417) = false := by
  decide +kernel

theorem node_context_10_417_93453 : EJMOriginalGlobalDAGData.nodes 11 ⟨93453, by decide⟩ =
    .split (coordinate 10) (![⟨91683, by decide⟩,⟨92176, by decide⟩,⟨92967, by decide⟩,⟨93452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_417_93453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 417 ⟨93453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 417
    ⟨93453, by decide⟩ (by decide) (![⟨91683, by decide⟩,⟨92176, by decide⟩,⟨92967, by decide⟩,⟨93452, by decide⟩]) unmarked_context_10_417_93453 node_context_10_417_93453
  intro a
  fin_cases a
  · exact context_11_1668_91683
  · exact context_11_1669_92176
  · exact context_11_1670_92967
  · exact context_11_1671_93452

theorem selected_cut_03001 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6688) = some ⟨12, 1, 0, 1738, 6688, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6688_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6688 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6688 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6688, 1, 65536⟩
    (by decide) selected_cut_03001

theorem selected_cut_03002 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6689) = some ⟨12, 1, 0, 1738, 6689, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6689_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6689 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6689 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6689, 1, 65536⟩
    (by decide) selected_cut_03002

theorem selected_cut_03003 : selected 8 ⟨93474, by decide⟩
    (prefixPartial 13 26760) = some ⟨13, 2, 0, 93474, 26760, 733, 16384⟩ := by
  decide +kernel

theorem context_13_26760_93474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26760 ⟨93474, by decide⟩ :=
  accepted_of_selected 13 26760 ⟨93474, by decide⟩ ⟨13, 2, 0, 93474, 26760, 733, 16384⟩
    (by decide) selected_cut_03003

theorem selected_cut_03004 : selected 8 ⟨93516, by decide⟩
    (prefixPartial 13 26761) = some ⟨13, 2, 0, 93516, 26761, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_26761_93516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26761 ⟨93516, by decide⟩ :=
  accepted_of_selected 13 26761 ⟨93516, by decide⟩ ⟨13, 2, 0, 93516, 26761, 1929, 16384⟩
    (by decide) selected_cut_03004

theorem selected_cut_03005 : selected 8 ⟨93536, by decide⟩
    (prefixPartial 13 26762) = some ⟨13, 2, 0, 93536, 26762, 989, 16384⟩ := by
  decide +kernel

theorem context_13_26762_93536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26762 ⟨93536, by decide⟩ :=
  accepted_of_selected 13 26762 ⟨93536, by decide⟩ ⟨13, 2, 0, 93536, 26762, 989, 16384⟩
    (by decide) selected_cut_03005

theorem selected_cut_03006 : selected 8 ⟨93548, by decide⟩
    (prefixPartial 13 26763) = some ⟨13, 2, 0, 93548, 26763, 813, 16384⟩ := by
  decide +kernel

theorem context_13_26763_93548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26763 ⟨93548, by decide⟩ :=
  accepted_of_selected 13 26763 ⟨93548, by decide⟩ ⟨13, 2, 0, 93548, 26763, 813, 16384⟩
    (by decide) selected_cut_03006

theorem unmarked_context_12_6690_93549 : frontier 9 ⟨93549, by decide⟩
    (prefixCache 12 6690) (prefixPartial 12 6690) = false := by
  decide +kernel

theorem node_context_12_6690_93549 : EJMOriginalGlobalDAGData.nodes 9 ⟨93549, by decide⟩ =
    .split (coordinate 12) (![⟨93474, by decide⟩,⟨93516, by decide⟩,⟨93536, by decide⟩,⟨93548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6690_93549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6690 ⟨93549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6690
    ⟨93549, by decide⟩ (by decide) (![⟨93474, by decide⟩,⟨93516, by decide⟩,⟨93536, by decide⟩,⟨93548, by decide⟩]) unmarked_context_12_6690_93549 node_context_12_6690_93549
  intro a
  fin_cases a
  · exact context_13_26760_93474
  · exact context_13_26761_93516
  · exact context_13_26762_93536
  · exact context_13_26763_93548

theorem selected_cut_03007 : selected 8 ⟨93584, by decide⟩
    (prefixPartial 13 26764) = some ⟨13, 2, 0, 93584, 26764, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_26764_93584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26764 ⟨93584, by decide⟩ :=
  accepted_of_selected 13 26764 ⟨93584, by decide⟩ ⟨13, 2, 0, 93584, 26764, 1025, 16384⟩
    (by decide) selected_cut_03007

theorem selected_cut_03008 : selected 8 ⟨93654, by decide⟩
    (prefixPartial 13 26765) = some ⟨13, 2, 0, 93654, 26765, 3425, 16384⟩ := by
  decide +kernel

theorem context_13_26765_93654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26765 ⟨93654, by decide⟩ :=
  accepted_of_selected 13 26765 ⟨93654, by decide⟩ ⟨13, 2, 0, 93654, 26765, 3425, 16384⟩
    (by decide) selected_cut_03008

theorem selected_cut_03009 : selected 8 ⟨93675, by decide⟩
    (prefixPartial 13 26766) = some ⟨13, 2, 0, 93675, 26766, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_26766_93675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26766 ⟨93675, by decide⟩ :=
  accepted_of_selected 13 26766 ⟨93675, by decide⟩ ⟨13, 2, 0, 93675, 26766, 1769, 16384⟩
    (by decide) selected_cut_03009

theorem selected_cut_03010 : selected 8 ⟨93694, by decide⟩
    (prefixPartial 13 26767) = some ⟨13, 2, 0, 93694, 26767, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_26767_93694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26767 ⟨93694, by decide⟩ :=
  accepted_of_selected 13 26767 ⟨93694, by decide⟩ ⟨13, 2, 0, 93694, 26767, 1277, 16384⟩
    (by decide) selected_cut_03010

theorem unmarked_context_12_6691_93695 : frontier 9 ⟨93695, by decide⟩
    (prefixCache 12 6691) (prefixPartial 12 6691) = false := by
  decide +kernel

theorem node_context_12_6691_93695 : EJMOriginalGlobalDAGData.nodes 9 ⟨93695, by decide⟩ =
    .split (coordinate 12) (![⟨93584, by decide⟩,⟨93654, by decide⟩,⟨93675, by decide⟩,⟨93694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6691_93695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6691 ⟨93695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6691
    ⟨93695, by decide⟩ (by decide) (![⟨93584, by decide⟩,⟨93654, by decide⟩,⟨93675, by decide⟩,⟨93694, by decide⟩]) unmarked_context_12_6691_93695 node_context_12_6691_93695
  intro a
  fin_cases a
  · exact context_13_26764_93584
  · exact context_13_26765_93654
  · exact context_13_26766_93675
  · exact context_13_26767_93694

theorem unmarked_context_11_1672_93696 : frontier 10 ⟨93696, by decide⟩
    (prefixCache 11 1672) (prefixPartial 11 1672) = false := by
  decide +kernel

theorem node_context_11_1672_93696 : EJMOriginalGlobalDAGData.nodes 10 ⟨93696, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨93549, by decide⟩,⟨93695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1672_93696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1672 ⟨93696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1672
    ⟨93696, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨93549, by decide⟩,⟨93695, by decide⟩]) unmarked_context_11_1672_93696 node_context_11_1672_93696
  intro a
  fin_cases a
  · exact context_12_6688_1738
  · exact context_12_6689_1738
  · exact context_12_6690_93549
  · exact context_12_6691_93695

theorem selected_cut_03011 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6692) = some ⟨12, 1, 0, 1738, 6692, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6692_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6692 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6692 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6692, 1, 65536⟩
    (by decide) selected_cut_03011

theorem selected_cut_03012 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6693) = some ⟨12, 1, 0, 1738, 6693, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6693_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6693 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6693 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6693, 1, 65536⟩
    (by decide) selected_cut_03012

theorem selected_cut_03013 : selected 8 ⟨93717, by decide⟩
    (prefixPartial 13 26776) = some ⟨13, 2, 0, 93717, 26776, 749, 16384⟩ := by
  decide +kernel

theorem context_13_26776_93717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26776 ⟨93717, by decide⟩ :=
  accepted_of_selected 13 26776 ⟨93717, by decide⟩ ⟨13, 2, 0, 93717, 26776, 749, 16384⟩
    (by decide) selected_cut_03013

theorem selected_cut_03014 : selected 8 ⟨93754, by decide⟩
    (prefixPartial 13 26777) = some ⟨13, 2, 0, 93754, 26777, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_26777_93754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26777 ⟨93754, by decide⟩ :=
  accepted_of_selected 13 26777 ⟨93754, by decide⟩ ⟨13, 2, 0, 93754, 26777, 1921, 16384⟩
    (by decide) selected_cut_03014

theorem selected_cut_03015 : selected 8 ⟨93775, by decide⟩
    (prefixPartial 13 26778) = some ⟨13, 2, 0, 93775, 26778, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_26778_93775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26778 ⟨93775, by decide⟩ :=
  accepted_of_selected 13 26778 ⟨93775, by decide⟩ ⟨13, 2, 0, 93775, 26778, 1173, 16384⟩
    (by decide) selected_cut_03015

theorem selected_cut_03016 : selected 8 ⟨93787, by decide⟩
    (prefixPartial 13 26779) = some ⟨13, 2, 0, 93787, 26779, 881, 16384⟩ := by
  decide +kernel

theorem context_13_26779_93787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26779 ⟨93787, by decide⟩ :=
  accepted_of_selected 13 26779 ⟨93787, by decide⟩ ⟨13, 2, 0, 93787, 26779, 881, 16384⟩
    (by decide) selected_cut_03016

theorem unmarked_context_12_6694_93788 : frontier 9 ⟨93788, by decide⟩
    (prefixCache 12 6694) (prefixPartial 12 6694) = false := by
  decide +kernel

theorem node_context_12_6694_93788 : EJMOriginalGlobalDAGData.nodes 9 ⟨93788, by decide⟩ =
    .split (coordinate 12) (![⟨93717, by decide⟩,⟨93754, by decide⟩,⟨93775, by decide⟩,⟨93787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6694_93788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6694 ⟨93788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6694
    ⟨93788, by decide⟩ (by decide) (![⟨93717, by decide⟩,⟨93754, by decide⟩,⟨93775, by decide⟩,⟨93787, by decide⟩]) unmarked_context_12_6694_93788 node_context_12_6694_93788
  intro a
  fin_cases a
  · exact context_13_26776_93717
  · exact context_13_26777_93754
  · exact context_13_26778_93775
  · exact context_13_26779_93787

theorem selected_cut_03017 : selected 8 ⟨93816, by decide⟩
    (prefixPartial 13 26780) = some ⟨13, 2, 0, 93816, 26780, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_26780_93816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26780 ⟨93816, by decide⟩ :=
  accepted_of_selected 13 26780 ⟨93816, by decide⟩ ⟨13, 2, 0, 93816, 26780, 1113, 16384⟩
    (by decide) selected_cut_03017

theorem selected_cut_03018 : selected 8 ⟨93870, by decide⟩
    (prefixPartial 13 26781) = some ⟨13, 2, 0, 93870, 26781, 3293, 16384⟩ := by
  decide +kernel

theorem context_13_26781_93870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26781 ⟨93870, by decide⟩ :=
  accepted_of_selected 13 26781 ⟨93870, by decide⟩ ⟨13, 2, 0, 93870, 26781, 3293, 16384⟩
    (by decide) selected_cut_03018

theorem selected_cut_03019 : selected 8 ⟨93902, by decide⟩
    (prefixPartial 13 26782) = some ⟨13, 2, 0, 93902, 26782, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_26782_93902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26782 ⟨93902, by decide⟩ :=
  accepted_of_selected 13 26782 ⟨93902, by decide⟩ ⟨13, 2, 0, 93902, 26782, 2293, 16384⟩
    (by decide) selected_cut_03019

theorem selected_cut_03020 : selected 8 ⟨93919, by decide⟩
    (prefixPartial 13 26783) = some ⟨13, 2, 0, 93919, 26783, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_26783_93919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26783 ⟨93919, by decide⟩ :=
  accepted_of_selected 13 26783 ⟨93919, by decide⟩ ⟨13, 2, 0, 93919, 26783, 1353, 16384⟩
    (by decide) selected_cut_03020

theorem unmarked_context_12_6695_93920 : frontier 9 ⟨93920, by decide⟩
    (prefixCache 12 6695) (prefixPartial 12 6695) = false := by
  decide +kernel

theorem node_context_12_6695_93920 : EJMOriginalGlobalDAGData.nodes 9 ⟨93920, by decide⟩ =
    .split (coordinate 12) (![⟨93816, by decide⟩,⟨93870, by decide⟩,⟨93902, by decide⟩,⟨93919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6695_93920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6695 ⟨93920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6695
    ⟨93920, by decide⟩ (by decide) (![⟨93816, by decide⟩,⟨93870, by decide⟩,⟨93902, by decide⟩,⟨93919, by decide⟩]) unmarked_context_12_6695_93920 node_context_12_6695_93920
  intro a
  fin_cases a
  · exact context_13_26780_93816
  · exact context_13_26781_93870
  · exact context_13_26782_93902
  · exact context_13_26783_93919

theorem unmarked_context_11_1673_93921 : frontier 10 ⟨93921, by decide⟩
    (prefixCache 11 1673) (prefixPartial 11 1673) = false := by
  decide +kernel

theorem node_context_11_1673_93921 : EJMOriginalGlobalDAGData.nodes 10 ⟨93921, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨93788, by decide⟩,⟨93920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1673_93921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1673 ⟨93921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1673
    ⟨93921, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨93788, by decide⟩,⟨93920, by decide⟩]) unmarked_context_11_1673_93921 node_context_11_1673_93921
  intro a
  fin_cases a
  · exact context_12_6692_1738
  · exact context_12_6693_1738
  · exact context_12_6694_93788
  · exact context_12_6695_93920

theorem selected_cut_03021 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6696) = some ⟨12, 1, 0, 1738, 6696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6696_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6696 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6696 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6696, 1, 65536⟩
    (by decide) selected_cut_03021

theorem selected_cut_03022 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6697) = some ⟨12, 1, 0, 1738, 6697, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6697_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6697 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6697 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6697, 1, 65536⟩
    (by decide) selected_cut_03022

theorem selected_cut_03023 : selected 9 ⟨93922, by decide⟩
    (prefixPartial 12 6698) = some ⟨12, 1, 0, 93922, 6698, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6698_93922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6698 ⟨93922, by decide⟩ :=
  accepted_of_selected 12 6698 ⟨93922, by decide⟩ ⟨12, 1, 0, 93922, 6698, 1, 65536⟩
    (by decide) selected_cut_03023

theorem selected_cut_03024 : selected 8 ⟨93974, by decide⟩
    (prefixPartial 13 26796) = some ⟨13, 2, 0, 93974, 26796, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_26796_93974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26796 ⟨93974, by decide⟩ :=
  accepted_of_selected 13 26796 ⟨93974, by decide⟩ ⟨13, 2, 0, 93974, 26796, 1169, 16384⟩
    (by decide) selected_cut_03024

theorem selected_cut_03025 : selected 7 ⟨94002, by decide⟩
    (prefixPartial 14 107188) = some ⟨14, 2, 0, 94002, 107188, 1353, 4096⟩ := by
  decide +kernel

theorem context_14_107188_94002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 107188 ⟨94002, by decide⟩ :=
  accepted_of_selected 14 107188 ⟨94002, by decide⟩ ⟨14, 2, 0, 94002, 107188, 1353, 4096⟩
    (by decide) selected_cut_03025

theorem selected_cut_03026 : selected 7 ⟨94045, by decide⟩
    (prefixPartial 14 107189) = some ⟨14, 2, 0, 94045, 107189, 1709, 4096⟩ := by
  decide +kernel

theorem context_14_107189_94045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 107189 ⟨94045, by decide⟩ :=
  accepted_of_selected 14 107189 ⟨94045, by decide⟩ ⟨14, 2, 0, 94045, 107189, 1709, 4096⟩
    (by decide) selected_cut_03026

theorem selected_cut_03027 : selected 7 ⟨94078, by decide⟩
    (prefixPartial 14 107190) = some ⟨14, 2, 0, 94078, 107190, 1101, 4096⟩ := by
  decide +kernel

theorem context_14_107190_94078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 107190 ⟨94078, by decide⟩ :=
  accepted_of_selected 14 107190 ⟨94078, by decide⟩ ⟨14, 2, 0, 94078, 107190, 1101, 4096⟩
    (by decide) selected_cut_03027

theorem selected_cut_03028 : selected 7 ⟨94104, by decide⟩
    (prefixPartial 14 107191) = some ⟨14, 2, 0, 94104, 107191, 1333, 4096⟩ := by
  decide +kernel

theorem context_14_107191_94104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 107191 ⟨94104, by decide⟩ :=
  accepted_of_selected 14 107191 ⟨94104, by decide⟩ ⟨14, 2, 0, 94104, 107191, 1333, 4096⟩
    (by decide) selected_cut_03028

theorem unmarked_context_13_26797_94105 : frontier 8 ⟨94105, by decide⟩
    (prefixCache 13 26797) (prefixPartial 13 26797) = false := by
  decide +kernel

theorem node_context_13_26797_94105 : EJMOriginalGlobalDAGData.nodes 8 ⟨94105, by decide⟩ =
    .split (coordinate 13) (![⟨94002, by decide⟩,⟨94045, by decide⟩,⟨94078, by decide⟩,⟨94104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26797_94105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26797 ⟨94105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26797
    ⟨94105, by decide⟩ (by decide) (![⟨94002, by decide⟩,⟨94045, by decide⟩,⟨94078, by decide⟩,⟨94104, by decide⟩]) unmarked_context_13_26797_94105 node_context_13_26797_94105
  intro a
  fin_cases a
  · exact context_14_107188_94002
  · exact context_14_107189_94045
  · exact context_14_107190_94078
  · exact context_14_107191_94104

theorem selected_cut_03029 : selected 8 ⟨94187, by decide⟩
    (prefixPartial 13 26798) = some ⟨13, 2, 0, 94187, 26798, 3209, 16384⟩ := by
  decide +kernel

theorem context_13_26798_94187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26798 ⟨94187, by decide⟩ :=
  accepted_of_selected 13 26798 ⟨94187, by decide⟩ ⟨13, 2, 0, 94187, 26798, 3209, 16384⟩
    (by decide) selected_cut_03029

theorem selected_cut_03030 : selected 8 ⟨94258, by decide⟩
    (prefixPartial 13 26799) = some ⟨13, 2, 0, 94258, 26799, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_26799_94258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26799 ⟨94258, by decide⟩ :=
  accepted_of_selected 13 26799 ⟨94258, by decide⟩ ⟨13, 2, 0, 94258, 26799, 1653, 16384⟩
    (by decide) selected_cut_03030

theorem unmarked_context_12_6699_94259 : frontier 9 ⟨94259, by decide⟩
    (prefixCache 12 6699) (prefixPartial 12 6699) = false := by
  decide +kernel

theorem node_context_12_6699_94259 : EJMOriginalGlobalDAGData.nodes 9 ⟨94259, by decide⟩ =
    .split (coordinate 12) (![⟨93974, by decide⟩,⟨94105, by decide⟩,⟨94187, by decide⟩,⟨94258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6699_94259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6699 ⟨94259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6699
    ⟨94259, by decide⟩ (by decide) (![⟨93974, by decide⟩,⟨94105, by decide⟩,⟨94187, by decide⟩,⟨94258, by decide⟩]) unmarked_context_12_6699_94259 node_context_12_6699_94259
  intro a
  fin_cases a
  · exact context_13_26796_93974
  · exact context_13_26797_94105
  · exact context_13_26798_94187
  · exact context_13_26799_94258

theorem unmarked_context_11_1674_94260 : frontier 10 ⟨94260, by decide⟩
    (prefixCache 11 1674) (prefixPartial 11 1674) = false := by
  decide +kernel

theorem node_context_11_1674_94260 : EJMOriginalGlobalDAGData.nodes 10 ⟨94260, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨93922, by decide⟩,⟨94259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1674_94260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1674 ⟨94260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1674
    ⟨94260, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨93922, by decide⟩,⟨94259, by decide⟩]) unmarked_context_11_1674_94260 node_context_11_1674_94260
  intro a
  fin_cases a
  · exact context_12_6696_1738
  · exact context_12_6697_1738
  · exact context_12_6698_93922
  · exact context_12_6699_94259

theorem selected_cut_03031 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6700) = some ⟨12, 1, 0, 1738, 6700, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6700_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6700 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6700 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6700, 1, 65536⟩
    (by decide) selected_cut_03031

theorem selected_cut_03032 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6701) = some ⟨12, 1, 0, 1738, 6701, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6701_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6701 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6701 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6701, 1, 65536⟩
    (by decide) selected_cut_03032

theorem selected_cut_03033 : selected 8 ⟨94273, by decide⟩
    (prefixPartial 13 26808) = some ⟨13, 2, 0, 94273, 26808, 357, 16384⟩ := by
  decide +kernel

theorem context_13_26808_94273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26808 ⟨94273, by decide⟩ :=
  accepted_of_selected 13 26808 ⟨94273, by decide⟩ ⟨13, 2, 0, 94273, 26808, 357, 16384⟩
    (by decide) selected_cut_03033

theorem selected_cut_03034 : selected 8 ⟨94314, by decide⟩
    (prefixPartial 13 26809) = some ⟨13, 2, 0, 94314, 26809, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_26809_94314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26809 ⟨94314, by decide⟩ :=
  accepted_of_selected 13 26809 ⟨94314, by decide⟩ ⟨13, 2, 0, 94314, 26809, 2273, 16384⟩
    (by decide) selected_cut_03034

theorem selected_cut_03035 : selected 8 ⟨94341, by decide⟩
    (prefixPartial 13 26810) = some ⟨13, 2, 0, 94341, 26810, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_26810_94341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26810 ⟨94341, by decide⟩ :=
  accepted_of_selected 13 26810 ⟨94341, by decide⟩ ⟨13, 2, 0, 94341, 26810, 1145, 16384⟩
    (by decide) selected_cut_03035

theorem selected_cut_03036 : selected 8 ⟨94351, by decide⟩
    (prefixPartial 13 26811) = some ⟨13, 2, 0, 94351, 26811, 733, 16384⟩ := by
  decide +kernel

theorem context_13_26811_94351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26811 ⟨94351, by decide⟩ :=
  accepted_of_selected 13 26811 ⟨94351, by decide⟩ ⟨13, 2, 0, 94351, 26811, 733, 16384⟩
    (by decide) selected_cut_03036

theorem unmarked_context_12_6702_94352 : frontier 9 ⟨94352, by decide⟩
    (prefixCache 12 6702) (prefixPartial 12 6702) = false := by
  decide +kernel

theorem node_context_12_6702_94352 : EJMOriginalGlobalDAGData.nodes 9 ⟨94352, by decide⟩ =
    .split (coordinate 12) (![⟨94273, by decide⟩,⟨94314, by decide⟩,⟨94341, by decide⟩,⟨94351, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6702_94352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6702 ⟨94352, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6702
    ⟨94352, by decide⟩ (by decide) (![⟨94273, by decide⟩,⟨94314, by decide⟩,⟨94341, by decide⟩,⟨94351, by decide⟩]) unmarked_context_12_6702_94352 node_context_12_6702_94352
  intro a
  fin_cases a
  · exact context_13_26808_94273
  · exact context_13_26809_94314
  · exact context_13_26810_94341
  · exact context_13_26811_94351

theorem selected_cut_03037 : selected 8 ⟨94370, by decide⟩
    (prefixPartial 13 26812) = some ⟨13, 2, 0, 94370, 26812, 397, 16384⟩ := by
  decide +kernel

theorem context_13_26812_94370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26812 ⟨94370, by decide⟩ :=
  accepted_of_selected 13 26812 ⟨94370, by decide⟩ ⟨13, 2, 0, 94370, 26812, 397, 16384⟩
    (by decide) selected_cut_03037

theorem selected_cut_03038 : selected 8 ⟨94433, by decide⟩
    (prefixPartial 13 26813) = some ⟨13, 2, 0, 94433, 26813, 3613, 16384⟩ := by
  decide +kernel

theorem context_13_26813_94433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26813 ⟨94433, by decide⟩ :=
  accepted_of_selected 13 26813 ⟨94433, by decide⟩ ⟨13, 2, 0, 94433, 26813, 3613, 16384⟩
    (by decide) selected_cut_03038

theorem selected_cut_03039 : selected 8 ⟨94455, by decide⟩
    (prefixPartial 13 26814) = some ⟨13, 2, 0, 94455, 26814, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_26814_94455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26814 ⟨94455, by decide⟩ :=
  accepted_of_selected 13 26814 ⟨94455, by decide⟩ ⟨13, 2, 0, 94455, 26814, 2061, 16384⟩
    (by decide) selected_cut_03039

theorem selected_cut_03040 : selected 8 ⟨94463, by decide⟩
    (prefixPartial 13 26815) = some ⟨13, 2, 0, 94463, 26815, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_26815_94463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26815 ⟨94463, by decide⟩ :=
  accepted_of_selected 13 26815 ⟨94463, by decide⟩ ⟨13, 2, 0, 94463, 26815, 1201, 16384⟩
    (by decide) selected_cut_03040

theorem unmarked_context_12_6703_94464 : frontier 9 ⟨94464, by decide⟩
    (prefixCache 12 6703) (prefixPartial 12 6703) = false := by
  decide +kernel

theorem node_context_12_6703_94464 : EJMOriginalGlobalDAGData.nodes 9 ⟨94464, by decide⟩ =
    .split (coordinate 12) (![⟨94370, by decide⟩,⟨94433, by decide⟩,⟨94455, by decide⟩,⟨94463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6703_94464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6703 ⟨94464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6703
    ⟨94464, by decide⟩ (by decide) (![⟨94370, by decide⟩,⟨94433, by decide⟩,⟨94455, by decide⟩,⟨94463, by decide⟩]) unmarked_context_12_6703_94464 node_context_12_6703_94464
  intro a
  fin_cases a
  · exact context_13_26812_94370
  · exact context_13_26813_94433
  · exact context_13_26814_94455
  · exact context_13_26815_94463

theorem unmarked_context_11_1675_94465 : frontier 10 ⟨94465, by decide⟩
    (prefixCache 11 1675) (prefixPartial 11 1675) = false := by
  decide +kernel

theorem node_context_11_1675_94465 : EJMOriginalGlobalDAGData.nodes 10 ⟨94465, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨94352, by decide⟩,⟨94464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1675_94465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1675 ⟨94465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1675
    ⟨94465, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨94352, by decide⟩,⟨94464, by decide⟩]) unmarked_context_11_1675_94465 node_context_11_1675_94465
  intro a
  fin_cases a
  · exact context_12_6700_1738
  · exact context_12_6701_1738
  · exact context_12_6702_94352
  · exact context_12_6703_94464

theorem unmarked_context_10_418_94466 : frontier 11 ⟨94466, by decide⟩
    (prefixCache 10 418) (prefixPartial 10 418) = false := by
  decide +kernel

theorem node_context_10_418_94466 : EJMOriginalGlobalDAGData.nodes 11 ⟨94466, by decide⟩ =
    .split (coordinate 10) (![⟨93696, by decide⟩,⟨93921, by decide⟩,⟨94260, by decide⟩,⟨94465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_418_94466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 418 ⟨94466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 418
    ⟨94466, by decide⟩ (by decide) (![⟨93696, by decide⟩,⟨93921, by decide⟩,⟨94260, by decide⟩,⟨94465, by decide⟩]) unmarked_context_10_418_94466 node_context_10_418_94466
  intro a
  fin_cases a
  · exact context_11_1672_93696
  · exact context_11_1673_93921
  · exact context_11_1674_94260
  · exact context_11_1675_94465

theorem selected_cut_03041 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6704) = some ⟨12, 1, 0, 1738, 6704, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6704_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6704 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6704 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6704, 1, 65536⟩
    (by decide) selected_cut_03041

theorem selected_cut_03042 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6705) = some ⟨12, 1, 0, 1738, 6705, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6705_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6705 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6705 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6705, 1, 65536⟩
    (by decide) selected_cut_03042

theorem selected_cut_03043 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6706) = some ⟨12, 1, 0, 1738, 6706, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6706_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6706 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6706 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6706, 1, 65536⟩
    (by decide) selected_cut_03043

theorem selected_cut_03044 : selected 8 ⟨94485, by decide⟩
    (prefixPartial 13 26828) = some ⟨13, 2, 0, 94485, 26828, 533, 16384⟩ := by
  decide +kernel

theorem context_13_26828_94485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26828 ⟨94485, by decide⟩ :=
  accepted_of_selected 13 26828 ⟨94485, by decide⟩ ⟨13, 2, 0, 94485, 26828, 533, 16384⟩
    (by decide) selected_cut_03044

theorem selected_cut_03045 : selected 8 ⟨94559, by decide⟩
    (prefixPartial 13 26829) = some ⟨13, 2, 0, 94559, 26829, 2489, 16384⟩ := by
  decide +kernel

theorem context_13_26829_94559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26829 ⟨94559, by decide⟩ :=
  accepted_of_selected 13 26829 ⟨94559, by decide⟩ ⟨13, 2, 0, 94559, 26829, 2489, 16384⟩
    (by decide) selected_cut_03045

theorem selected_cut_03046 : selected 8 ⟨94595, by decide⟩
    (prefixPartial 13 26830) = some ⟨13, 2, 0, 94595, 26830, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_26830_94595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26830 ⟨94595, by decide⟩ :=
  accepted_of_selected 13 26830 ⟨94595, by decide⟩ ⟨13, 2, 0, 94595, 26830, 1261, 16384⟩
    (by decide) selected_cut_03046

theorem selected_cut_03047 : selected 8 ⟨94639, by decide⟩
    (prefixPartial 13 26831) = some ⟨13, 2, 0, 94639, 26831, 993, 16384⟩ := by
  decide +kernel

theorem context_13_26831_94639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26831 ⟨94639, by decide⟩ :=
  accepted_of_selected 13 26831 ⟨94639, by decide⟩ ⟨13, 2, 0, 94639, 26831, 993, 16384⟩
    (by decide) selected_cut_03047

theorem unmarked_context_12_6707_94640 : frontier 9 ⟨94640, by decide⟩
    (prefixCache 12 6707) (prefixPartial 12 6707) = false := by
  decide +kernel

theorem node_context_12_6707_94640 : EJMOriginalGlobalDAGData.nodes 9 ⟨94640, by decide⟩ =
    .split (coordinate 12) (![⟨94485, by decide⟩,⟨94559, by decide⟩,⟨94595, by decide⟩,⟨94639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6707_94640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6707 ⟨94640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6707
    ⟨94640, by decide⟩ (by decide) (![⟨94485, by decide⟩,⟨94559, by decide⟩,⟨94595, by decide⟩,⟨94639, by decide⟩]) unmarked_context_12_6707_94640 node_context_12_6707_94640
  intro a
  fin_cases a
  · exact context_13_26828_94485
  · exact context_13_26829_94559
  · exact context_13_26830_94595
  · exact context_13_26831_94639

theorem unmarked_context_11_1676_94641 : frontier 10 ⟨94641, by decide⟩
    (prefixCache 11 1676) (prefixPartial 11 1676) = false := by
  decide +kernel

theorem node_context_11_1676_94641 : EJMOriginalGlobalDAGData.nodes 10 ⟨94641, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨1738, by decide⟩,⟨94640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1676_94641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1676 ⟨94641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1676
    ⟨94641, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨1738, by decide⟩,⟨94640, by decide⟩]) unmarked_context_11_1676_94641 node_context_11_1676_94641
  intro a
  fin_cases a
  · exact context_12_6704_1738
  · exact context_12_6705_1738
  · exact context_12_6706_1738
  · exact context_12_6707_94640

theorem selected_cut_03048 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6708) = some ⟨12, 1, 0, 1738, 6708, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6708_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6708 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6708 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6708, 1, 65536⟩
    (by decide) selected_cut_03048

theorem selected_cut_03049 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6709) = some ⟨12, 1, 0, 1738, 6709, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6709_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6709 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6709 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6709, 1, 65536⟩
    (by decide) selected_cut_03049

theorem selected_cut_03050 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6710) = some ⟨12, 1, 0, 1738, 6710, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6710_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6710 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6710 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6710, 1, 65536⟩
    (by decide) selected_cut_03050

theorem selected_cut_03051 : selected 8 ⟨94652, by decide⟩
    (prefixPartial 13 26844) = some ⟨13, 2, 0, 94652, 26844, 453, 16384⟩ := by
  decide +kernel

theorem context_13_26844_94652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26844 ⟨94652, by decide⟩ :=
  accepted_of_selected 13 26844 ⟨94652, by decide⟩ ⟨13, 2, 0, 94652, 26844, 453, 16384⟩
    (by decide) selected_cut_03051

theorem selected_cut_03052 : selected 8 ⟨94715, by decide⟩
    (prefixPartial 13 26845) = some ⟨13, 2, 0, 94715, 26845, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_26845_94715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26845 ⟨94715, by decide⟩ :=
  accepted_of_selected 13 26845 ⟨94715, by decide⟩ ⟨13, 2, 0, 94715, 26845, 2513, 16384⟩
    (by decide) selected_cut_03052

theorem selected_cut_03053 : selected 8 ⟨94765, by decide⟩
    (prefixPartial 13 26846) = some ⟨13, 2, 0, 94765, 26846, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_26846_94765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26846 ⟨94765, by decide⟩ :=
  accepted_of_selected 13 26846 ⟨94765, by decide⟩ ⟨13, 2, 0, 94765, 26846, 1697, 16384⟩
    (by decide) selected_cut_03053

theorem selected_cut_03054 : selected 8 ⟨94804, by decide⟩
    (prefixPartial 13 26847) = some ⟨13, 2, 0, 94804, 26847, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_26847_94804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26847 ⟨94804, by decide⟩ :=
  accepted_of_selected 13 26847 ⟨94804, by decide⟩ ⟨13, 2, 0, 94804, 26847, 1057, 16384⟩
    (by decide) selected_cut_03054

theorem unmarked_context_12_6711_94805 : frontier 9 ⟨94805, by decide⟩
    (prefixCache 12 6711) (prefixPartial 12 6711) = false := by
  decide +kernel

theorem node_context_12_6711_94805 : EJMOriginalGlobalDAGData.nodes 9 ⟨94805, by decide⟩ =
    .split (coordinate 12) (![⟨94652, by decide⟩,⟨94715, by decide⟩,⟨94765, by decide⟩,⟨94804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6711_94805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6711 ⟨94805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6711
    ⟨94805, by decide⟩ (by decide) (![⟨94652, by decide⟩,⟨94715, by decide⟩,⟨94765, by decide⟩,⟨94804, by decide⟩]) unmarked_context_12_6711_94805 node_context_12_6711_94805
  intro a
  fin_cases a
  · exact context_13_26844_94652
  · exact context_13_26845_94715
  · exact context_13_26846_94765
  · exact context_13_26847_94804

theorem unmarked_context_11_1677_94806 : frontier 10 ⟨94806, by decide⟩
    (prefixCache 11 1677) (prefixPartial 11 1677) = false := by
  decide +kernel

theorem node_context_11_1677_94806 : EJMOriginalGlobalDAGData.nodes 10 ⟨94806, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨1738, by decide⟩,⟨94805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1677_94806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1677 ⟨94806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1677
    ⟨94806, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨1738, by decide⟩,⟨94805, by decide⟩]) unmarked_context_11_1677_94806 node_context_11_1677_94806
  intro a
  fin_cases a
  · exact context_12_6708_1738
  · exact context_12_6709_1738
  · exact context_12_6710_1738
  · exact context_12_6711_94805

theorem selected_cut_03055 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6712) = some ⟨12, 1, 0, 1738, 6712, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6712_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6712 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6712 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6712, 1, 65536⟩
    (by decide) selected_cut_03055

theorem selected_cut_03056 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6713) = some ⟨12, 1, 0, 1738, 6713, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6713_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6713 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6713 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6713, 1, 65536⟩
    (by decide) selected_cut_03056

theorem selected_cut_03057 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6714) = some ⟨12, 1, 0, 1738, 6714, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6714_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6714 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6714 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6714, 1, 65536⟩
    (by decide) selected_cut_03057

theorem selected_cut_03058 : selected 8 ⟨94818, by decide⟩
    (prefixPartial 13 26860) = some ⟨13, 2, 0, 94818, 26860, 225, 16384⟩ := by
  decide +kernel

theorem context_13_26860_94818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26860 ⟨94818, by decide⟩ :=
  accepted_of_selected 13 26860 ⟨94818, by decide⟩ ⟨13, 2, 0, 94818, 26860, 225, 16384⟩
    (by decide) selected_cut_03058

theorem selected_cut_03059 : selected 8 ⟨94905, by decide⟩
    (prefixPartial 13 26861) = some ⟨13, 2, 0, 94905, 26861, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_26861_94905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26861 ⟨94905, by decide⟩ :=
  accepted_of_selected 13 26861 ⟨94905, by decide⟩ ⟨13, 2, 0, 94905, 26861, 2453, 16384⟩
    (by decide) selected_cut_03059

theorem selected_cut_03060 : selected 8 ⟨94945, by decide⟩
    (prefixPartial 13 26862) = some ⟨13, 2, 0, 94945, 26862, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_26862_94945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26862 ⟨94945, by decide⟩ :=
  accepted_of_selected 13 26862 ⟨94945, by decide⟩ ⟨13, 2, 0, 94945, 26862, 1285, 16384⟩
    (by decide) selected_cut_03060

theorem selected_cut_03061 : selected 8 ⟨94990, by decide⟩
    (prefixPartial 13 26863) = some ⟨13, 2, 0, 94990, 26863, 877, 16384⟩ := by
  decide +kernel

theorem context_13_26863_94990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26863 ⟨94990, by decide⟩ :=
  accepted_of_selected 13 26863 ⟨94990, by decide⟩ ⟨13, 2, 0, 94990, 26863, 877, 16384⟩
    (by decide) selected_cut_03061

theorem unmarked_context_12_6715_94991 : frontier 9 ⟨94991, by decide⟩
    (prefixCache 12 6715) (prefixPartial 12 6715) = false := by
  decide +kernel

theorem node_context_12_6715_94991 : EJMOriginalGlobalDAGData.nodes 9 ⟨94991, by decide⟩ =
    .split (coordinate 12) (![⟨94818, by decide⟩,⟨94905, by decide⟩,⟨94945, by decide⟩,⟨94990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6715_94991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6715 ⟨94991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6715
    ⟨94991, by decide⟩ (by decide) (![⟨94818, by decide⟩,⟨94905, by decide⟩,⟨94945, by decide⟩,⟨94990, by decide⟩]) unmarked_context_12_6715_94991 node_context_12_6715_94991
  intro a
  fin_cases a
  · exact context_13_26860_94818
  · exact context_13_26861_94905
  · exact context_13_26862_94945
  · exact context_13_26863_94990

theorem unmarked_context_11_1678_94992 : frontier 10 ⟨94992, by decide⟩
    (prefixCache 11 1678) (prefixPartial 11 1678) = false := by
  decide +kernel

theorem node_context_11_1678_94992 : EJMOriginalGlobalDAGData.nodes 10 ⟨94992, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨1738, by decide⟩,⟨94991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1678_94992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1678 ⟨94992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1678
    ⟨94992, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨1738, by decide⟩,⟨94991, by decide⟩]) unmarked_context_11_1678_94992 node_context_11_1678_94992
  intro a
  fin_cases a
  · exact context_12_6712_1738
  · exact context_12_6713_1738
  · exact context_12_6714_1738
  · exact context_12_6715_94991

theorem selected_cut_03062 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6716) = some ⟨12, 1, 0, 1738, 6716, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6716_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6716 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6716 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6716, 1, 65536⟩
    (by decide) selected_cut_03062

theorem selected_cut_03063 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6717) = some ⟨12, 1, 0, 1738, 6717, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6717_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6717 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6717 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6717, 1, 65536⟩
    (by decide) selected_cut_03063

theorem selected_cut_03064 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6718) = some ⟨12, 1, 0, 1738, 6718, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6718_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6718 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6718 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6718, 1, 65536⟩
    (by decide) selected_cut_03064

theorem selected_cut_03065 : selected 8 ⟨94997, by decide⟩
    (prefixPartial 13 26876) = some ⟨13, 2, 0, 94997, 26876, 101, 16384⟩ := by
  decide +kernel

theorem context_13_26876_94997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26876 ⟨94997, by decide⟩ :=
  accepted_of_selected 13 26876 ⟨94997, by decide⟩ ⟨13, 2, 0, 94997, 26876, 101, 16384⟩
    (by decide) selected_cut_03065

theorem selected_cut_03066 : selected 8 ⟨95055, by decide⟩
    (prefixPartial 13 26877) = some ⟨13, 2, 0, 95055, 26877, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_26877_95055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26877 ⟨95055, by decide⟩ :=
  accepted_of_selected 13 26877 ⟨95055, by decide⟩ ⟨13, 2, 0, 95055, 26877, 2373, 16384⟩
    (by decide) selected_cut_03066

theorem selected_cut_03067 : selected 8 ⟨95084, by decide⟩
    (prefixPartial 13 26878) = some ⟨13, 2, 0, 95084, 26878, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_26878_95084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26878 ⟨95084, by decide⟩ :=
  accepted_of_selected 13 26878 ⟨95084, by decide⟩ ⟨13, 2, 0, 95084, 26878, 1333, 16384⟩
    (by decide) selected_cut_03067

theorem selected_cut_03068 : selected 8 ⟨95113, by decide⟩
    (prefixPartial 13 26879) = some ⟨13, 2, 0, 95113, 26879, 917, 16384⟩ := by
  decide +kernel

theorem context_13_26879_95113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26879 ⟨95113, by decide⟩ :=
  accepted_of_selected 13 26879 ⟨95113, by decide⟩ ⟨13, 2, 0, 95113, 26879, 917, 16384⟩
    (by decide) selected_cut_03068

theorem unmarked_context_12_6719_95114 : frontier 9 ⟨95114, by decide⟩
    (prefixCache 12 6719) (prefixPartial 12 6719) = false := by
  decide +kernel

theorem node_context_12_6719_95114 : EJMOriginalGlobalDAGData.nodes 9 ⟨95114, by decide⟩ =
    .split (coordinate 12) (![⟨94997, by decide⟩,⟨95055, by decide⟩,⟨95084, by decide⟩,⟨95113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6719_95114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6719 ⟨95114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6719
    ⟨95114, by decide⟩ (by decide) (![⟨94997, by decide⟩,⟨95055, by decide⟩,⟨95084, by decide⟩,⟨95113, by decide⟩]) unmarked_context_12_6719_95114 node_context_12_6719_95114
  intro a
  fin_cases a
  · exact context_13_26876_94997
  · exact context_13_26877_95055
  · exact context_13_26878_95084
  · exact context_13_26879_95113

theorem unmarked_context_11_1679_95115 : frontier 10 ⟨95115, by decide⟩
    (prefixCache 11 1679) (prefixPartial 11 1679) = false := by
  decide +kernel

theorem node_context_11_1679_95115 : EJMOriginalGlobalDAGData.nodes 10 ⟨95115, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨1738, by decide⟩,⟨95114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1679_95115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1679 ⟨95115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1679
    ⟨95115, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨1738, by decide⟩,⟨95114, by decide⟩]) unmarked_context_11_1679_95115 node_context_11_1679_95115
  intro a
  fin_cases a
  · exact context_12_6716_1738
  · exact context_12_6717_1738
  · exact context_12_6718_1738
  · exact context_12_6719_95114

theorem unmarked_context_10_419_95116 : frontier 11 ⟨95116, by decide⟩
    (prefixCache 10 419) (prefixPartial 10 419) = false := by
  decide +kernel

theorem node_context_10_419_95116 : EJMOriginalGlobalDAGData.nodes 11 ⟨95116, by decide⟩ =
    .split (coordinate 10) (![⟨94641, by decide⟩,⟨94806, by decide⟩,⟨94992, by decide⟩,⟨95115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_419_95116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 419 ⟨95116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 419
    ⟨95116, by decide⟩ (by decide) (![⟨94641, by decide⟩,⟨94806, by decide⟩,⟨94992, by decide⟩,⟨95115, by decide⟩]) unmarked_context_10_419_95116 node_context_10_419_95116
  intro a
  fin_cases a
  · exact context_11_1676_94641
  · exact context_11_1677_94806
  · exact context_11_1678_94992
  · exact context_11_1679_95115

theorem unmarked_context_9_104_95117 : frontier 12 ⟨95117, by decide⟩
    (prefixCache 9 104) (prefixPartial 9 104) = false := by
  decide +kernel

theorem node_context_9_104_95117 : EJMOriginalGlobalDAGData.nodes 12 ⟨95117, by decide⟩ =
    .split (coordinate 9) (![⟨91050, by decide⟩,⟨93453, by decide⟩,⟨94466, by decide⟩,⟨95116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_104_95117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 104 ⟨95117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 104
    ⟨95117, by decide⟩ (by decide) (![⟨91050, by decide⟩,⟨93453, by decide⟩,⟨94466, by decide⟩,⟨95116, by decide⟩]) unmarked_context_9_104_95117 node_context_9_104_95117
  intro a
  fin_cases a
  · exact context_10_416_91050
  · exact context_10_417_93453
  · exact context_10_418_94466
  · exact context_10_419_95116

theorem selected_cut_03069 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26880) = some ⟨13, 1, 0, 3444, 26880, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26880_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26880 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26880 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26880, 1, 16384⟩
    (by decide) selected_cut_03069

theorem selected_cut_03070 : selected 8 ⟨95168, by decide⟩
    (prefixPartial 13 26881) = some ⟨13, 2, 0, 95168, 26881, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_26881_95168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26881 ⟨95168, by decide⟩ :=
  accepted_of_selected 13 26881 ⟨95168, by decide⟩ ⟨13, 2, 0, 95168, 26881, 2357, 16384⟩
    (by decide) selected_cut_03070

theorem selected_cut_03071 : selected 8 ⟨95193, by decide⟩
    (prefixPartial 13 26882) = some ⟨13, 2, 0, 95193, 26882, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_26882_95193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26882 ⟨95193, by decide⟩ :=
  accepted_of_selected 13 26882 ⟨95193, by decide⟩ ⟨13, 2, 0, 95193, 26882, 1377, 16384⟩
    (by decide) selected_cut_03071

theorem selected_cut_03072 : selected 8 ⟨95213, by decide⟩
    (prefixPartial 13 26883) = some ⟨13, 2, 0, 95213, 26883, 653, 16384⟩ := by
  decide +kernel

theorem context_13_26883_95213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26883 ⟨95213, by decide⟩ :=
  accepted_of_selected 13 26883 ⟨95213, by decide⟩ ⟨13, 2, 0, 95213, 26883, 653, 16384⟩
    (by decide) selected_cut_03072

theorem unmarked_context_12_6720_95214 : frontier 9 ⟨95214, by decide⟩
    (prefixCache 12 6720) (prefixPartial 12 6720) = false := by
  decide +kernel

theorem node_context_12_6720_95214 : EJMOriginalGlobalDAGData.nodes 9 ⟨95214, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨95168, by decide⟩,⟨95193, by decide⟩,⟨95213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6720_95214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6720 ⟨95214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6720
    ⟨95214, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨95168, by decide⟩,⟨95193, by decide⟩,⟨95213, by decide⟩]) unmarked_context_12_6720_95214 node_context_12_6720_95214
  intro a
  fin_cases a
  · exact context_13_26880_3444
  · exact context_13_26881_95168
  · exact context_13_26882_95193
  · exact context_13_26883_95213

theorem selected_cut_03073 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 26884) = some ⟨13, 1, 0, 3444, 26884, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26884_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26884 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 26884 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 26884, 1, 16384⟩
    (by decide) selected_cut_03073

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
