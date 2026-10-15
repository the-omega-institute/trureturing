/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover029
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_02882 : selected 7 ⟨88926, by decide⟩
    (prefixPartial 14 106640) = some ⟨14, 2, 0, 88926, 106640, 825, 4096⟩ := by
  decide +kernel

theorem context_14_106640_88926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106640 ⟨88926, by decide⟩ :=
  accepted_of_selected 14 106640 ⟨88926, by decide⟩ ⟨14, 2, 0, 88926, 106640, 825, 4096⟩
    (by decide) selected_cut_02882

theorem selected_cut_02883 : selected 7 ⟨88960, by decide⟩
    (prefixPartial 14 106641) = some ⟨14, 2, 0, 88960, 106641, 1469, 4096⟩ := by
  decide +kernel

theorem context_14_106641_88960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106641 ⟨88960, by decide⟩ :=
  accepted_of_selected 14 106641 ⟨88960, by decide⟩ ⟨14, 2, 0, 88960, 106641, 1469, 4096⟩
    (by decide) selected_cut_02883

theorem selected_cut_02884 : selected 7 ⟨88986, by decide⟩
    (prefixPartial 14 106642) = some ⟨14, 2, 0, 88986, 106642, 1277, 4096⟩ := by
  decide +kernel

theorem context_14_106642_88986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106642 ⟨88986, by decide⟩ :=
  accepted_of_selected 14 106642 ⟨88986, by decide⟩ ⟨14, 2, 0, 88986, 106642, 1277, 4096⟩
    (by decide) selected_cut_02884

theorem selected_cut_02885 : selected 7 ⟨89009, by decide⟩
    (prefixPartial 14 106643) = some ⟨14, 2, 0, 89009, 106643, 1397, 4096⟩ := by
  decide +kernel

theorem context_14_106643_89009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106643 ⟨89009, by decide⟩ :=
  accepted_of_selected 14 106643 ⟨89009, by decide⟩ ⟨14, 2, 0, 89009, 106643, 1397, 4096⟩
    (by decide) selected_cut_02885

theorem unmarked_context_13_26660_89010 : frontier 8 ⟨89010, by decide⟩
    (prefixCache 13 26660) (prefixPartial 13 26660) = false := by
  decide +kernel

theorem node_context_13_26660_89010 : EJMOriginalGlobalDAGData.nodes 8 ⟨89010, by decide⟩ =
    .split (coordinate 13) (![⟨88926, by decide⟩,⟨88960, by decide⟩,⟨88986, by decide⟩,⟨89009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26660_89010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26660 ⟨89010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26660
    ⟨89010, by decide⟩ (by decide) (![⟨88926, by decide⟩,⟨88960, by decide⟩,⟨88986, by decide⟩,⟨89009, by decide⟩]) unmarked_context_13_26660_89010 node_context_13_26660_89010
  intro a
  fin_cases a
  · exact context_14_106640_88926
  · exact context_14_106641_88960
  · exact context_14_106642_88986
  · exact context_14_106643_89009

theorem selected_cut_02886 : selected 7 ⟨89029, by decide⟩
    (prefixPartial 14 106644) = some ⟨14, 2, 0, 89029, 106644, 909, 4096⟩ := by
  decide +kernel

theorem context_14_106644_89029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106644 ⟨89029, by decide⟩ :=
  accepted_of_selected 14 106644 ⟨89029, by decide⟩ ⟨14, 2, 0, 89029, 106644, 909, 4096⟩
    (by decide) selected_cut_02886

theorem selected_cut_02887 : selected 7 ⟨89055, by decide⟩
    (prefixPartial 14 106645) = some ⟨14, 2, 0, 89055, 106645, 1305, 4096⟩ := by
  decide +kernel

theorem context_14_106645_89055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106645 ⟨89055, by decide⟩ :=
  accepted_of_selected 14 106645 ⟨89055, by decide⟩ ⟨14, 2, 0, 89055, 106645, 1305, 4096⟩
    (by decide) selected_cut_02887

theorem selected_cut_02888 : selected 7 ⟨89077, by decide⟩
    (prefixPartial 14 106646) = some ⟨14, 2, 0, 89077, 106646, 1205, 4096⟩ := by
  decide +kernel

theorem context_14_106646_89077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106646 ⟨89077, by decide⟩ :=
  accepted_of_selected 14 106646 ⟨89077, by decide⟩ ⟨14, 2, 0, 89077, 106646, 1205, 4096⟩
    (by decide) selected_cut_02888

theorem selected_cut_02889 : selected 7 ⟨89090, by decide⟩
    (prefixPartial 14 106647) = some ⟨14, 2, 0, 89090, 106647, 1009, 4096⟩ := by
  decide +kernel

theorem context_14_106647_89090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106647 ⟨89090, by decide⟩ :=
  accepted_of_selected 14 106647 ⟨89090, by decide⟩ ⟨14, 2, 0, 89090, 106647, 1009, 4096⟩
    (by decide) selected_cut_02889

theorem unmarked_context_13_26661_89091 : frontier 8 ⟨89091, by decide⟩
    (prefixCache 13 26661) (prefixPartial 13 26661) = false := by
  decide +kernel

theorem node_context_13_26661_89091 : EJMOriginalGlobalDAGData.nodes 8 ⟨89091, by decide⟩ =
    .split (coordinate 13) (![⟨89029, by decide⟩,⟨89055, by decide⟩,⟨89077, by decide⟩,⟨89090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26661_89091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26661 ⟨89091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26661
    ⟨89091, by decide⟩ (by decide) (![⟨89029, by decide⟩,⟨89055, by decide⟩,⟨89077, by decide⟩,⟨89090, by decide⟩]) unmarked_context_13_26661_89091 node_context_13_26661_89091
  intro a
  fin_cases a
  · exact context_14_106644_89029
  · exact context_14_106645_89055
  · exact context_14_106646_89077
  · exact context_14_106647_89090

theorem selected_cut_02890 : selected 8 ⟨89132, by decide⟩
    (prefixPartial 13 26662) = some ⟨13, 2, 0, 89132, 26662, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_26662_89132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26662 ⟨89132, by decide⟩ :=
  accepted_of_selected 13 26662 ⟨89132, by decide⟩ ⟨13, 2, 0, 89132, 26662, 2449, 16384⟩
    (by decide) selected_cut_02890

theorem selected_cut_02891 : selected 8 ⟨89167, by decide⟩
    (prefixPartial 13 26663) = some ⟨13, 2, 0, 89167, 26663, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_26663_89167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26663 ⟨89167, by decide⟩ :=
  accepted_of_selected 13 26663 ⟨89167, by decide⟩ ⟨13, 2, 0, 89167, 26663, 1561, 16384⟩
    (by decide) selected_cut_02891

theorem unmarked_context_12_6665_89168 : frontier 9 ⟨89168, by decide⟩
    (prefixCache 12 6665) (prefixPartial 12 6665) = false := by
  decide +kernel

theorem node_context_12_6665_89168 : EJMOriginalGlobalDAGData.nodes 9 ⟨89168, by decide⟩ =
    .split (coordinate 12) (![⟨89010, by decide⟩,⟨89091, by decide⟩,⟨89132, by decide⟩,⟨89167, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6665_89168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6665 ⟨89168, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6665
    ⟨89168, by decide⟩ (by decide) (![⟨89010, by decide⟩,⟨89091, by decide⟩,⟨89132, by decide⟩,⟨89167, by decide⟩]) unmarked_context_12_6665_89168 node_context_12_6665_89168
  intro a
  fin_cases a
  · exact context_13_26660_89010
  · exact context_13_26661_89091
  · exact context_13_26662_89132
  · exact context_13_26663_89167

theorem selected_cut_02892 : selected 7 ⟨89196, by decide⟩
    (prefixPartial 14 106656) = some ⟨14, 2, 0, 89196, 106656, 1349, 4096⟩ := by
  decide +kernel

theorem context_14_106656_89196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106656 ⟨89196, by decide⟩ :=
  accepted_of_selected 14 106656 ⟨89196, by decide⟩ ⟨14, 2, 0, 89196, 106656, 1349, 4096⟩
    (by decide) selected_cut_02892

theorem selected_cut_02893 : selected 7 ⟨89238, by decide⟩
    (prefixPartial 14 106657) = some ⟨14, 2, 0, 89238, 106657, 1613, 4096⟩ := by
  decide +kernel

theorem context_14_106657_89238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106657 ⟨89238, by decide⟩ :=
  accepted_of_selected 14 106657 ⟨89238, by decide⟩ ⟨14, 2, 0, 89238, 106657, 1613, 4096⟩
    (by decide) selected_cut_02893

theorem selected_cut_02894 : selected 7 ⟨89275, by decide⟩
    (prefixPartial 14 106658) = some ⟨14, 2, 0, 89275, 106658, 1785, 4096⟩ := by
  decide +kernel

theorem context_14_106658_89275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106658 ⟨89275, by decide⟩ :=
  accepted_of_selected 14 106658 ⟨89275, by decide⟩ ⟨14, 2, 0, 89275, 106658, 1785, 4096⟩
    (by decide) selected_cut_02894

theorem selected_cut_02895 : selected 7 ⟨89312, by decide⟩
    (prefixPartial 14 106659) = some ⟨14, 2, 0, 89312, 106659, 1785, 4096⟩ := by
  decide +kernel

theorem context_14_106659_89312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106659 ⟨89312, by decide⟩ :=
  accepted_of_selected 14 106659 ⟨89312, by decide⟩ ⟨14, 2, 0, 89312, 106659, 1785, 4096⟩
    (by decide) selected_cut_02895

theorem unmarked_context_13_26664_89313 : frontier 8 ⟨89313, by decide⟩
    (prefixCache 13 26664) (prefixPartial 13 26664) = false := by
  decide +kernel

theorem node_context_13_26664_89313 : EJMOriginalGlobalDAGData.nodes 8 ⟨89313, by decide⟩ =
    .split (coordinate 13) (![⟨89196, by decide⟩,⟨89238, by decide⟩,⟨89275, by decide⟩,⟨89312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26664_89313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26664 ⟨89313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26664
    ⟨89313, by decide⟩ (by decide) (![⟨89196, by decide⟩,⟨89238, by decide⟩,⟨89275, by decide⟩,⟨89312, by decide⟩]) unmarked_context_13_26664_89313 node_context_13_26664_89313
  intro a
  fin_cases a
  · exact context_14_106656_89196
  · exact context_14_106657_89238
  · exact context_14_106658_89275
  · exact context_14_106659_89312

theorem selected_cut_02896 : selected 7 ⟨89340, by decide⟩
    (prefixPartial 14 106660) = some ⟨14, 2, 0, 89340, 106660, 1269, 4096⟩ := by
  decide +kernel

theorem context_14_106660_89340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106660 ⟨89340, by decide⟩ :=
  accepted_of_selected 14 106660 ⟨89340, by decide⟩ ⟨14, 2, 0, 89340, 106660, 1269, 4096⟩
    (by decide) selected_cut_02896

theorem selected_cut_02897 : selected 7 ⟨89385, by decide⟩
    (prefixPartial 14 106661) = some ⟨14, 2, 0, 89385, 106661, 1897, 4096⟩ := by
  decide +kernel

theorem context_14_106661_89385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106661 ⟨89385, by decide⟩ :=
  accepted_of_selected 14 106661 ⟨89385, by decide⟩ ⟨14, 2, 0, 89385, 106661, 1897, 4096⟩
    (by decide) selected_cut_02897

theorem selected_cut_02898 : selected 7 ⟨89448, by decide⟩
    (prefixPartial 14 106662) = some ⟨14, 2, 0, 89448, 106662, 1893, 4096⟩ := by
  decide +kernel

theorem context_14_106662_89448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106662 ⟨89448, by decide⟩ :=
  accepted_of_selected 14 106662 ⟨89448, by decide⟩ ⟨14, 2, 0, 89448, 106662, 1893, 4096⟩
    (by decide) selected_cut_02898

theorem selected_cut_02899 : selected 7 ⟨89478, by decide⟩
    (prefixPartial 14 106663) = some ⟨14, 2, 0, 89478, 106663, 1577, 4096⟩ := by
  decide +kernel

theorem context_14_106663_89478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106663 ⟨89478, by decide⟩ :=
  accepted_of_selected 14 106663 ⟨89478, by decide⟩ ⟨14, 2, 0, 89478, 106663, 1577, 4096⟩
    (by decide) selected_cut_02899

theorem unmarked_context_13_26665_89479 : frontier 8 ⟨89479, by decide⟩
    (prefixCache 13 26665) (prefixPartial 13 26665) = false := by
  decide +kernel

theorem node_context_13_26665_89479 : EJMOriginalGlobalDAGData.nodes 8 ⟨89479, by decide⟩ =
    .split (coordinate 13) (![⟨89340, by decide⟩,⟨89385, by decide⟩,⟨89448, by decide⟩,⟨89478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26665_89479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26665 ⟨89479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26665
    ⟨89479, by decide⟩ (by decide) (![⟨89340, by decide⟩,⟨89385, by decide⟩,⟨89448, by decide⟩,⟨89478, by decide⟩]) unmarked_context_13_26665_89479 node_context_13_26665_89479
  intro a
  fin_cases a
  · exact context_14_106660_89340
  · exact context_14_106661_89385
  · exact context_14_106662_89448
  · exact context_14_106663_89478

theorem selected_cut_02900 : selected 7 ⟨89501, by decide⟩
    (prefixPartial 14 106664) = some ⟨14, 2, 0, 89501, 106664, 885, 4096⟩ := by
  decide +kernel

theorem context_14_106664_89501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106664 ⟨89501, by decide⟩ :=
  accepted_of_selected 14 106664 ⟨89501, by decide⟩ ⟨14, 2, 0, 89501, 106664, 885, 4096⟩
    (by decide) selected_cut_02900

theorem selected_cut_02901 : selected 7 ⟨89548, by decide⟩
    (prefixPartial 14 106665) = some ⟨14, 2, 0, 89548, 106665, 1457, 4096⟩ := by
  decide +kernel

theorem context_14_106665_89548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106665 ⟨89548, by decide⟩ :=
  accepted_of_selected 14 106665 ⟨89548, by decide⟩ ⟨14, 2, 0, 89548, 106665, 1457, 4096⟩
    (by decide) selected_cut_02901

theorem selected_cut_02902 : selected 7 ⟨89576, by decide⟩
    (prefixPartial 14 106666) = some ⟨14, 2, 0, 89576, 106666, 937, 4096⟩ := by
  decide +kernel

theorem context_14_106666_89576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106666 ⟨89576, by decide⟩ :=
  accepted_of_selected 14 106666 ⟨89576, by decide⟩ ⟨14, 2, 0, 89576, 106666, 937, 4096⟩
    (by decide) selected_cut_02902

theorem selected_cut_02903 : selected 7 ⟨89607, by decide⟩
    (prefixPartial 14 106667) = some ⟨14, 2, 0, 89607, 106667, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_106667_89607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106667 ⟨89607, by decide⟩ :=
  accepted_of_selected 14 106667 ⟨89607, by decide⟩ ⟨14, 2, 0, 89607, 106667, 1097, 4096⟩
    (by decide) selected_cut_02903

theorem unmarked_context_13_26666_89608 : frontier 8 ⟨89608, by decide⟩
    (prefixCache 13 26666) (prefixPartial 13 26666) = false := by
  decide +kernel

theorem node_context_13_26666_89608 : EJMOriginalGlobalDAGData.nodes 8 ⟨89608, by decide⟩ =
    .split (coordinate 13) (![⟨89501, by decide⟩,⟨89548, by decide⟩,⟨89576, by decide⟩,⟨89607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26666_89608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26666 ⟨89608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26666
    ⟨89608, by decide⟩ (by decide) (![⟨89501, by decide⟩,⟨89548, by decide⟩,⟨89576, by decide⟩,⟨89607, by decide⟩]) unmarked_context_13_26666_89608 node_context_13_26666_89608
  intro a
  fin_cases a
  · exact context_14_106664_89501
  · exact context_14_106665_89548
  · exact context_14_106666_89576
  · exact context_14_106667_89607

theorem selected_cut_02904 : selected 8 ⟨89696, by decide⟩
    (prefixPartial 13 26667) = some ⟨13, 2, 0, 89696, 26667, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_26667_89696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26667 ⟨89696, by decide⟩ :=
  accepted_of_selected 13 26667 ⟨89696, by decide⟩ ⟨13, 2, 0, 89696, 26667, 1957, 16384⟩
    (by decide) selected_cut_02904

theorem unmarked_context_12_6666_89697 : frontier 9 ⟨89697, by decide⟩
    (prefixCache 12 6666) (prefixPartial 12 6666) = false := by
  decide +kernel

theorem node_context_12_6666_89697 : EJMOriginalGlobalDAGData.nodes 9 ⟨89697, by decide⟩ =
    .split (coordinate 12) (![⟨89313, by decide⟩,⟨89479, by decide⟩,⟨89608, by decide⟩,⟨89696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6666_89697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6666 ⟨89697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6666
    ⟨89697, by decide⟩ (by decide) (![⟨89313, by decide⟩,⟨89479, by decide⟩,⟨89608, by decide⟩,⟨89696, by decide⟩]) unmarked_context_12_6666_89697 node_context_12_6666_89697
  intro a
  fin_cases a
  · exact context_13_26664_89313
  · exact context_13_26665_89479
  · exact context_13_26666_89608
  · exact context_13_26667_89696

theorem selected_cut_02905 : selected 7 ⟨89713, by decide⟩
    (prefixPartial 14 106672) = some ⟨14, 2, 0, 89713, 106672, 497, 4096⟩ := by
  decide +kernel

theorem context_14_106672_89713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106672 ⟨89713, by decide⟩ :=
  accepted_of_selected 14 106672 ⟨89713, by decide⟩ ⟨14, 2, 0, 89713, 106672, 497, 4096⟩
    (by decide) selected_cut_02905

theorem selected_cut_02906 : selected 7 ⟨89747, by decide⟩
    (prefixPartial 14 106673) = some ⟨14, 2, 0, 89747, 106673, 1361, 4096⟩ := by
  decide +kernel

theorem context_14_106673_89747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106673 ⟨89747, by decide⟩ :=
  accepted_of_selected 14 106673 ⟨89747, by decide⟩ ⟨14, 2, 0, 89747, 106673, 1361, 4096⟩
    (by decide) selected_cut_02906

theorem selected_cut_02907 : selected 7 ⟨89777, by decide⟩
    (prefixPartial 14 106674) = some ⟨14, 2, 0, 89777, 106674, 1065, 4096⟩ := by
  decide +kernel

theorem context_14_106674_89777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106674 ⟨89777, by decide⟩ :=
  accepted_of_selected 14 106674 ⟨89777, by decide⟩ ⟨14, 2, 0, 89777, 106674, 1065, 4096⟩
    (by decide) selected_cut_02907

theorem selected_cut_02908 : selected 7 ⟨89804, by decide⟩
    (prefixPartial 14 106675) = some ⟨14, 2, 0, 89804, 106675, 1345, 4096⟩ := by
  decide +kernel

theorem context_14_106675_89804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106675 ⟨89804, by decide⟩ :=
  accepted_of_selected 14 106675 ⟨89804, by decide⟩ ⟨14, 2, 0, 89804, 106675, 1345, 4096⟩
    (by decide) selected_cut_02908

theorem unmarked_context_13_26668_89805 : frontier 8 ⟨89805, by decide⟩
    (prefixCache 13 26668) (prefixPartial 13 26668) = false := by
  decide +kernel

theorem node_context_13_26668_89805 : EJMOriginalGlobalDAGData.nodes 8 ⟨89805, by decide⟩ =
    .split (coordinate 13) (![⟨89713, by decide⟩,⟨89747, by decide⟩,⟨89777, by decide⟩,⟨89804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26668_89805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26668 ⟨89805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26668
    ⟨89805, by decide⟩ (by decide) (![⟨89713, by decide⟩,⟨89747, by decide⟩,⟨89777, by decide⟩,⟨89804, by decide⟩]) unmarked_context_13_26668_89805 node_context_13_26668_89805
  intro a
  fin_cases a
  · exact context_14_106672_89713
  · exact context_14_106673_89747
  · exact context_14_106674_89777
  · exact context_14_106675_89804

theorem selected_cut_02909 : selected 7 ⟨89823, by decide⟩
    (prefixPartial 14 106676) = some ⟨14, 2, 0, 89823, 106676, 1133, 4096⟩ := by
  decide +kernel

theorem context_14_106676_89823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106676 ⟨89823, by decide⟩ :=
  accepted_of_selected 14 106676 ⟨89823, by decide⟩ ⟨14, 2, 0, 89823, 106676, 1133, 4096⟩
    (by decide) selected_cut_02909

theorem selected_cut_02910 : selected 7 ⟨89848, by decide⟩
    (prefixPartial 14 106677) = some ⟨14, 2, 0, 89848, 106677, 1365, 4096⟩ := by
  decide +kernel

theorem context_14_106677_89848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106677 ⟨89848, by decide⟩ :=
  accepted_of_selected 14 106677 ⟨89848, by decide⟩ ⟨14, 2, 0, 89848, 106677, 1365, 4096⟩
    (by decide) selected_cut_02910

theorem selected_cut_02911 : selected 7 ⟨89870, by decide⟩
    (prefixPartial 14 106678) = some ⟨14, 2, 0, 89870, 106678, 1269, 4096⟩ := by
  decide +kernel

theorem context_14_106678_89870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106678 ⟨89870, by decide⟩ :=
  accepted_of_selected 14 106678 ⟨89870, by decide⟩ ⟨14, 2, 0, 89870, 106678, 1269, 4096⟩
    (by decide) selected_cut_02911

theorem selected_cut_02912 : selected 7 ⟨89889, by decide⟩
    (prefixPartial 14 106679) = some ⟨14, 2, 0, 89889, 106679, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_106679_89889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106679 ⟨89889, by decide⟩ :=
  accepted_of_selected 14 106679 ⟨89889, by decide⟩ ⟨14, 2, 0, 89889, 106679, 1181, 4096⟩
    (by decide) selected_cut_02912

theorem unmarked_context_13_26669_89890 : frontier 8 ⟨89890, by decide⟩
    (prefixCache 13 26669) (prefixPartial 13 26669) = false := by
  decide +kernel

theorem node_context_13_26669_89890 : EJMOriginalGlobalDAGData.nodes 8 ⟨89890, by decide⟩ =
    .split (coordinate 13) (![⟨89823, by decide⟩,⟨89848, by decide⟩,⟨89870, by decide⟩,⟨89889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26669_89890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26669 ⟨89890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26669
    ⟨89890, by decide⟩ (by decide) (![⟨89823, by decide⟩,⟨89848, by decide⟩,⟨89870, by decide⟩,⟨89889, by decide⟩]) unmarked_context_13_26669_89890 node_context_13_26669_89890
  intro a
  fin_cases a
  · exact context_14_106676_89823
  · exact context_14_106677_89848
  · exact context_14_106678_89870
  · exact context_14_106679_89889

theorem selected_cut_02913 : selected 8 ⟨89923, by decide⟩
    (prefixPartial 13 26670) = some ⟨13, 2, 0, 89923, 26670, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_26670_89923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26670 ⟨89923, by decide⟩ :=
  accepted_of_selected 13 26670 ⟨89923, by decide⟩ ⟨13, 2, 0, 89923, 26670, 2573, 16384⟩
    (by decide) selected_cut_02913

theorem selected_cut_02914 : selected 8 ⟨89949, by decide⟩
    (prefixPartial 13 26671) = some ⟨13, 2, 0, 89949, 26671, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_26671_89949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26671 ⟨89949, by decide⟩ :=
  accepted_of_selected 13 26671 ⟨89949, by decide⟩ ⟨13, 2, 0, 89949, 26671, 1493, 16384⟩
    (by decide) selected_cut_02914

theorem unmarked_context_12_6667_89950 : frontier 9 ⟨89950, by decide⟩
    (prefixCache 12 6667) (prefixPartial 12 6667) = false := by
  decide +kernel

theorem node_context_12_6667_89950 : EJMOriginalGlobalDAGData.nodes 9 ⟨89950, by decide⟩ =
    .split (coordinate 12) (![⟨89805, by decide⟩,⟨89890, by decide⟩,⟨89923, by decide⟩,⟨89949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6667_89950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6667 ⟨89950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6667
    ⟨89950, by decide⟩ (by decide) (![⟨89805, by decide⟩,⟨89890, by decide⟩,⟨89923, by decide⟩,⟨89949, by decide⟩]) unmarked_context_12_6667_89950 node_context_12_6667_89950
  intro a
  fin_cases a
  · exact context_13_26668_89805
  · exact context_13_26669_89890
  · exact context_13_26670_89923
  · exact context_13_26671_89949

theorem unmarked_context_11_1666_89951 : frontier 10 ⟨89951, by decide⟩
    (prefixCache 11 1666) (prefixPartial 11 1666) = false := by
  decide +kernel

theorem node_context_11_1666_89951 : EJMOriginalGlobalDAGData.nodes 10 ⟨89951, by decide⟩ =
    .split (coordinate 11) (![⟨88909, by decide⟩,⟨89168, by decide⟩,⟨89697, by decide⟩,⟨89950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1666_89951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1666 ⟨89951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1666
    ⟨89951, by decide⟩ (by decide) (![⟨88909, by decide⟩,⟨89168, by decide⟩,⟨89697, by decide⟩,⟨89950, by decide⟩]) unmarked_context_11_1666_89951 node_context_11_1666_89951
  intro a
  fin_cases a
  · exact context_12_6664_88909
  · exact context_12_6665_89168
  · exact context_12_6666_89697
  · exact context_12_6667_89950

theorem selected_cut_02915 : selected 8 ⟨90023, by decide⟩
    (prefixPartial 13 26672) = some ⟨13, 2, 0, 90023, 26672, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_26672_90023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26672 ⟨90023, by decide⟩ :=
  accepted_of_selected 13 26672 ⟨90023, by decide⟩ ⟨13, 2, 0, 90023, 26672, 1181, 16384⟩
    (by decide) selected_cut_02915

theorem selected_cut_02916 : selected 7 ⟨90101, by decide⟩
    (prefixPartial 14 106692) = some ⟨14, 2, 0, 90101, 106692, 2229, 4096⟩ := by
  decide +kernel

theorem context_14_106692_90101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106692 ⟨90101, by decide⟩ :=
  accepted_of_selected 14 106692 ⟨90101, by decide⟩ ⟨14, 2, 0, 90101, 106692, 2229, 4096⟩
    (by decide) selected_cut_02916

theorem selected_cut_02917 : selected 7 ⟨90174, by decide⟩
    (prefixPartial 14 106693) = some ⟨14, 2, 0, 90174, 106693, 1401, 4096⟩ := by
  decide +kernel

theorem context_14_106693_90174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106693 ⟨90174, by decide⟩ :=
  accepted_of_selected 14 106693 ⟨90174, by decide⟩ ⟨14, 2, 0, 90174, 106693, 1401, 4096⟩
    (by decide) selected_cut_02917

theorem selected_cut_02918 : selected 7 ⟨90213, by decide⟩
    (prefixPartial 14 106694) = some ⟨14, 2, 0, 90213, 106694, 773, 4096⟩ := by
  decide +kernel

theorem context_14_106694_90213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106694 ⟨90213, by decide⟩ :=
  accepted_of_selected 14 106694 ⟨90213, by decide⟩ ⟨14, 2, 0, 90213, 106694, 773, 4096⟩
    (by decide) selected_cut_02918

theorem selected_cut_02919 : selected 7 ⟨90237, by decide⟩
    (prefixPartial 14 106695) = some ⟨14, 2, 0, 90237, 106695, 393, 4096⟩ := by
  decide +kernel

theorem context_14_106695_90237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106695 ⟨90237, by decide⟩ :=
  accepted_of_selected 14 106695 ⟨90237, by decide⟩ ⟨14, 2, 0, 90237, 106695, 393, 4096⟩
    (by decide) selected_cut_02919

theorem unmarked_context_13_26673_90238 : frontier 8 ⟨90238, by decide⟩
    (prefixCache 13 26673) (prefixPartial 13 26673) = false := by
  decide +kernel

theorem node_context_13_26673_90238 : EJMOriginalGlobalDAGData.nodes 8 ⟨90238, by decide⟩ =
    .split (coordinate 13) (![⟨90101, by decide⟩,⟨90174, by decide⟩,⟨90213, by decide⟩,⟨90237, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26673_90238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26673 ⟨90238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26673
    ⟨90238, by decide⟩ (by decide) (![⟨90101, by decide⟩,⟨90174, by decide⟩,⟨90213, by decide⟩,⟨90237, by decide⟩]) unmarked_context_13_26673_90238 node_context_13_26673_90238
  intro a
  fin_cases a
  · exact context_14_106692_90101
  · exact context_14_106693_90174
  · exact context_14_106694_90213
  · exact context_14_106695_90237

theorem selected_cut_02920 : selected 8 ⟨90315, by decide⟩
    (prefixPartial 13 26674) = some ⟨13, 2, 0, 90315, 26674, 805, 16384⟩ := by
  decide +kernel

theorem context_13_26674_90315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26674 ⟨90315, by decide⟩ :=
  accepted_of_selected 13 26674 ⟨90315, by decide⟩ ⟨13, 2, 0, 90315, 26674, 805, 16384⟩
    (by decide) selected_cut_02920

theorem selected_cut_02921 : selected 8 ⟨51129, by decide⟩
    (prefixPartial 13 26675) = some ⟨13, 1, 0, 51129, 26675, 1, 16384⟩ := by
  decide +kernel

theorem context_13_26675_51129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26675 ⟨51129, by decide⟩ :=
  accepted_of_selected 13 26675 ⟨51129, by decide⟩ ⟨13, 1, 0, 51129, 26675, 1, 16384⟩
    (by decide) selected_cut_02921

theorem unmarked_context_12_6668_90316 : frontier 9 ⟨90316, by decide⟩
    (prefixCache 12 6668) (prefixPartial 12 6668) = false := by
  decide +kernel

theorem node_context_12_6668_90316 : EJMOriginalGlobalDAGData.nodes 9 ⟨90316, by decide⟩ =
    .split (coordinate 12) (![⟨90023, by decide⟩,⟨90238, by decide⟩,⟨90315, by decide⟩,⟨51129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6668_90316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6668 ⟨90316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6668
    ⟨90316, by decide⟩ (by decide) (![⟨90023, by decide⟩,⟨90238, by decide⟩,⟨90315, by decide⟩,⟨51129, by decide⟩]) unmarked_context_12_6668_90316 node_context_12_6668_90316
  intro a
  fin_cases a
  · exact context_13_26672_90023
  · exact context_13_26673_90238
  · exact context_13_26674_90315
  · exact context_13_26675_51129

theorem selected_cut_02922 : selected 7 ⟨90331, by decide⟩
    (prefixPartial 14 106704) = some ⟨14, 2, 0, 90331, 106704, 433, 4096⟩ := by
  decide +kernel

theorem context_14_106704_90331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106704 ⟨90331, by decide⟩ :=
  accepted_of_selected 14 106704 ⟨90331, by decide⟩ ⟨14, 2, 0, 90331, 106704, 433, 4096⟩
    (by decide) selected_cut_02922

theorem selected_cut_02923 : selected 7 ⟨90372, by decide⟩
    (prefixPartial 14 106705) = some ⟨14, 2, 0, 90372, 106705, 1433, 4096⟩ := by
  decide +kernel

theorem context_14_106705_90372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106705 ⟨90372, by decide⟩ :=
  accepted_of_selected 14 106705 ⟨90372, by decide⟩ ⟨14, 2, 0, 90372, 106705, 1433, 4096⟩
    (by decide) selected_cut_02923

theorem selected_cut_02924 : selected 7 ⟨90404, by decide⟩
    (prefixPartial 14 106706) = some ⟨14, 2, 0, 90404, 106706, 1177, 4096⟩ := by
  decide +kernel

theorem context_14_106706_90404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106706 ⟨90404, by decide⟩ :=
  accepted_of_selected 14 106706 ⟨90404, by decide⟩ ⟨14, 2, 0, 90404, 106706, 1177, 4096⟩
    (by decide) selected_cut_02924

theorem selected_cut_02925 : selected 7 ⟨90430, by decide⟩
    (prefixPartial 14 106707) = some ⟨14, 2, 0, 90430, 106707, 1069, 4096⟩ := by
  decide +kernel

theorem context_14_106707_90430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106707 ⟨90430, by decide⟩ :=
  accepted_of_selected 14 106707 ⟨90430, by decide⟩ ⟨14, 2, 0, 90430, 106707, 1069, 4096⟩
    (by decide) selected_cut_02925

theorem unmarked_context_13_26676_90431 : frontier 8 ⟨90431, by decide⟩
    (prefixCache 13 26676) (prefixPartial 13 26676) = false := by
  decide +kernel

theorem node_context_13_26676_90431 : EJMOriginalGlobalDAGData.nodes 8 ⟨90431, by decide⟩ =
    .split (coordinate 13) (![⟨90331, by decide⟩,⟨90372, by decide⟩,⟨90404, by decide⟩,⟨90430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26676_90431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26676 ⟨90431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26676
    ⟨90431, by decide⟩ (by decide) (![⟨90331, by decide⟩,⟨90372, by decide⟩,⟨90404, by decide⟩,⟨90430, by decide⟩]) unmarked_context_13_26676_90431 node_context_13_26676_90431
  intro a
  fin_cases a
  · exact context_14_106704_90331
  · exact context_14_106705_90372
  · exact context_14_106706_90404
  · exact context_14_106707_90430

theorem selected_cut_02926 : selected 7 ⟨90448, by decide⟩
    (prefixPartial 14 106708) = some ⟨14, 2, 0, 90448, 106708, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_106708_90448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106708 ⟨90448, by decide⟩ :=
  accepted_of_selected 14 106708 ⟨90448, by decide⟩ ⟨14, 2, 0, 90448, 106708, 1181, 4096⟩
    (by decide) selected_cut_02926

theorem selected_cut_02927 : selected 7 ⟨90474, by decide⟩
    (prefixPartial 14 106709) = some ⟨14, 2, 0, 90474, 106709, 1481, 4096⟩ := by
  decide +kernel

theorem context_14_106709_90474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106709 ⟨90474, by decide⟩ :=
  accepted_of_selected 14 106709 ⟨90474, by decide⟩ ⟨14, 2, 0, 90474, 106709, 1481, 4096⟩
    (by decide) selected_cut_02927

theorem selected_cut_02928 : selected 7 ⟨90497, by decide⟩
    (prefixPartial 14 106710) = some ⟨14, 2, 0, 90497, 106710, 1437, 4096⟩ := by
  decide +kernel

theorem context_14_106710_90497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106710 ⟨90497, by decide⟩ :=
  accepted_of_selected 14 106710 ⟨90497, by decide⟩ ⟨14, 2, 0, 90497, 106710, 1437, 4096⟩
    (by decide) selected_cut_02928

theorem selected_cut_02929 : selected 7 ⟨90515, by decide⟩
    (prefixPartial 14 106711) = some ⟨14, 2, 0, 90515, 106711, 1177, 4096⟩ := by
  decide +kernel

theorem context_14_106711_90515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106711 ⟨90515, by decide⟩ :=
  accepted_of_selected 14 106711 ⟨90515, by decide⟩ ⟨14, 2, 0, 90515, 106711, 1177, 4096⟩
    (by decide) selected_cut_02929

theorem unmarked_context_13_26677_90516 : frontier 8 ⟨90516, by decide⟩
    (prefixCache 13 26677) (prefixPartial 13 26677) = false := by
  decide +kernel

theorem node_context_13_26677_90516 : EJMOriginalGlobalDAGData.nodes 8 ⟨90516, by decide⟩ =
    .split (coordinate 13) (![⟨90448, by decide⟩,⟨90474, by decide⟩,⟨90497, by decide⟩,⟨90515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26677_90516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26677 ⟨90516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26677
    ⟨90516, by decide⟩ (by decide) (![⟨90448, by decide⟩,⟨90474, by decide⟩,⟨90497, by decide⟩,⟨90515, by decide⟩]) unmarked_context_13_26677_90516 node_context_13_26677_90516
  intro a
  fin_cases a
  · exact context_14_106708_90448
  · exact context_14_106709_90474
  · exact context_14_106710_90497
  · exact context_14_106711_90515

theorem selected_cut_02930 : selected 8 ⟨90571, by decide⟩
    (prefixPartial 13 26678) = some ⟨13, 2, 0, 90571, 26678, 2905, 16384⟩ := by
  decide +kernel

theorem context_13_26678_90571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26678 ⟨90571, by decide⟩ :=
  accepted_of_selected 13 26678 ⟨90571, by decide⟩ ⟨13, 2, 0, 90571, 26678, 2905, 16384⟩
    (by decide) selected_cut_02930

theorem selected_cut_02931 : selected 8 ⟨90592, by decide⟩
    (prefixPartial 13 26679) = some ⟨13, 2, 0, 90592, 26679, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_26679_90592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26679 ⟨90592, by decide⟩ :=
  accepted_of_selected 13 26679 ⟨90592, by decide⟩ ⟨13, 2, 0, 90592, 26679, 1605, 16384⟩
    (by decide) selected_cut_02931

theorem unmarked_context_12_6669_90593 : frontier 9 ⟨90593, by decide⟩
    (prefixCache 12 6669) (prefixPartial 12 6669) = false := by
  decide +kernel

theorem node_context_12_6669_90593 : EJMOriginalGlobalDAGData.nodes 9 ⟨90593, by decide⟩ =
    .split (coordinate 12) (![⟨90431, by decide⟩,⟨90516, by decide⟩,⟨90571, by decide⟩,⟨90592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6669_90593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6669 ⟨90593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6669
    ⟨90593, by decide⟩ (by decide) (![⟨90431, by decide⟩,⟨90516, by decide⟩,⟨90571, by decide⟩,⟨90592, by decide⟩]) unmarked_context_12_6669_90593 node_context_12_6669_90593
  intro a
  fin_cases a
  · exact context_13_26676_90431
  · exact context_13_26677_90516
  · exact context_13_26678_90571
  · exact context_13_26679_90592

theorem selected_cut_02932 : selected 8 ⟨90662, by decide⟩
    (prefixPartial 13 26680) = some ⟨13, 2, 0, 90662, 26680, 3213, 16384⟩ := by
  decide +kernel

theorem context_13_26680_90662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26680 ⟨90662, by decide⟩ :=
  accepted_of_selected 13 26680 ⟨90662, by decide⟩ ⟨13, 2, 0, 90662, 26680, 3213, 16384⟩
    (by decide) selected_cut_02932

theorem selected_cut_02933 : selected 7 ⟨90676, by decide⟩
    (prefixPartial 14 106724) = some ⟨14, 2, 0, 90676, 106724, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_106724_90676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106724 ⟨90676, by decide⟩ :=
  accepted_of_selected 14 106724 ⟨90676, by decide⟩ ⟨14, 2, 0, 90676, 106724, 1053, 4096⟩
    (by decide) selected_cut_02933

theorem selected_cut_02934 : selected 7 ⟨90698, by decide⟩
    (prefixPartial 14 106725) = some ⟨14, 2, 0, 90698, 106725, 1349, 4096⟩ := by
  decide +kernel

theorem context_14_106725_90698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106725 ⟨90698, by decide⟩ :=
  accepted_of_selected 14 106725 ⟨90698, by decide⟩ ⟨14, 2, 0, 90698, 106725, 1349, 4096⟩
    (by decide) selected_cut_02934

theorem selected_cut_02935 : selected 7 ⟨90723, by decide⟩
    (prefixPartial 14 106726) = some ⟨14, 2, 0, 90723, 106726, 1397, 4096⟩ := by
  decide +kernel

theorem context_14_106726_90723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106726 ⟨90723, by decide⟩ :=
  accepted_of_selected 14 106726 ⟨90723, by decide⟩ ⟨14, 2, 0, 90723, 106726, 1397, 4096⟩
    (by decide) selected_cut_02935

theorem selected_cut_02936 : selected 7 ⟨90735, by decide⟩
    (prefixPartial 14 106727) = some ⟨14, 2, 0, 90735, 106727, 1017, 4096⟩ := by
  decide +kernel

theorem context_14_106727_90735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106727 ⟨90735, by decide⟩ :=
  accepted_of_selected 14 106727 ⟨90735, by decide⟩ ⟨14, 2, 0, 90735, 106727, 1017, 4096⟩
    (by decide) selected_cut_02936

theorem unmarked_context_13_26681_90736 : frontier 8 ⟨90736, by decide⟩
    (prefixCache 13 26681) (prefixPartial 13 26681) = false := by
  decide +kernel

theorem node_context_13_26681_90736 : EJMOriginalGlobalDAGData.nodes 8 ⟨90736, by decide⟩ =
    .split (coordinate 13) (![⟨90676, by decide⟩,⟨90698, by decide⟩,⟨90723, by decide⟩,⟨90735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26681_90736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26681 ⟨90736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26681
    ⟨90736, by decide⟩ (by decide) (![⟨90676, by decide⟩,⟨90698, by decide⟩,⟨90723, by decide⟩,⟨90735, by decide⟩]) unmarked_context_13_26681_90736 node_context_13_26681_90736
  intro a
  fin_cases a
  · exact context_14_106724_90676
  · exact context_14_106725_90698
  · exact context_14_106726_90723
  · exact context_14_106727_90735

theorem selected_cut_02937 : selected 8 ⟨90793, by decide⟩
    (prefixPartial 13 26682) = some ⟨13, 2, 0, 90793, 26682, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_26682_90793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26682 ⟨90793, by decide⟩ :=
  accepted_of_selected 13 26682 ⟨90793, by decide⟩ ⟨13, 2, 0, 90793, 26682, 2893, 16384⟩
    (by decide) selected_cut_02937

theorem selected_cut_02938 : selected 8 ⟨90819, by decide⟩
    (prefixPartial 13 26683) = some ⟨13, 2, 0, 90819, 26683, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_26683_90819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26683 ⟨90819, by decide⟩ :=
  accepted_of_selected 13 26683 ⟨90819, by decide⟩ ⟨13, 2, 0, 90819, 26683, 1409, 16384⟩
    (by decide) selected_cut_02938

theorem unmarked_context_12_6670_90820 : frontier 9 ⟨90820, by decide⟩
    (prefixCache 12 6670) (prefixPartial 12 6670) = false := by
  decide +kernel

theorem node_context_12_6670_90820 : EJMOriginalGlobalDAGData.nodes 9 ⟨90820, by decide⟩ =
    .split (coordinate 12) (![⟨90662, by decide⟩,⟨90736, by decide⟩,⟨90793, by decide⟩,⟨90819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6670_90820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6670 ⟨90820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6670
    ⟨90820, by decide⟩ (by decide) (![⟨90662, by decide⟩,⟨90736, by decide⟩,⟨90793, by decide⟩,⟨90819, by decide⟩]) unmarked_context_12_6670_90820 node_context_12_6670_90820
  intro a
  fin_cases a
  · exact context_13_26680_90662
  · exact context_13_26681_90736
  · exact context_13_26682_90793
  · exact context_13_26683_90819

theorem selected_cut_02939 : selected 8 ⟨90898, by decide⟩
    (prefixPartial 13 26684) = some ⟨13, 2, 0, 90898, 26684, 3705, 16384⟩ := by
  decide +kernel

theorem context_13_26684_90898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26684 ⟨90898, by decide⟩ :=
  accepted_of_selected 13 26684 ⟨90898, by decide⟩ ⟨13, 2, 0, 90898, 26684, 3705, 16384⟩
    (by decide) selected_cut_02939

theorem selected_cut_02940 : selected 7 ⟨90917, by decide⟩
    (prefixPartial 14 106740) = some ⟨14, 2, 0, 90917, 106740, 1385, 4096⟩ := by
  decide +kernel

theorem context_14_106740_90917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106740 ⟨90917, by decide⟩ :=
  accepted_of_selected 14 106740 ⟨90917, by decide⟩ ⟨14, 2, 0, 90917, 106740, 1385, 4096⟩
    (by decide) selected_cut_02940

theorem selected_cut_02941 : selected 7 ⟨90940, by decide⟩
    (prefixPartial 14 106741) = some ⟨14, 2, 0, 90940, 106741, 1365, 4096⟩ := by
  decide +kernel

theorem context_14_106741_90940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106741 ⟨90940, by decide⟩ :=
  accepted_of_selected 14 106741 ⟨90940, by decide⟩ ⟨14, 2, 0, 90940, 106741, 1365, 4096⟩
    (by decide) selected_cut_02941

theorem selected_cut_02942 : selected 7 ⟨90966, by decide⟩
    (prefixPartial 14 106742) = some ⟨14, 2, 0, 90966, 106742, 1425, 4096⟩ := by
  decide +kernel

theorem context_14_106742_90966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106742 ⟨90966, by decide⟩ :=
  accepted_of_selected 14 106742 ⟨90966, by decide⟩ ⟨14, 2, 0, 90966, 106742, 1425, 4096⟩
    (by decide) selected_cut_02942

theorem selected_cut_02943 : selected 7 ⟨90984, by decide⟩
    (prefixPartial 14 106743) = some ⟨14, 2, 0, 90984, 106743, 1173, 4096⟩ := by
  decide +kernel

theorem context_14_106743_90984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106743 ⟨90984, by decide⟩ :=
  accepted_of_selected 14 106743 ⟨90984, by decide⟩ ⟨14, 2, 0, 90984, 106743, 1173, 4096⟩
    (by decide) selected_cut_02943

theorem unmarked_context_13_26685_90985 : frontier 8 ⟨90985, by decide⟩
    (prefixCache 13 26685) (prefixPartial 13 26685) = false := by
  decide +kernel

theorem node_context_13_26685_90985 : EJMOriginalGlobalDAGData.nodes 8 ⟨90985, by decide⟩ =
    .split (coordinate 13) (![⟨90917, by decide⟩,⟨90940, by decide⟩,⟨90966, by decide⟩,⟨90984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26685_90985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26685 ⟨90985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26685
    ⟨90985, by decide⟩ (by decide) (![⟨90917, by decide⟩,⟨90940, by decide⟩,⟨90966, by decide⟩,⟨90984, by decide⟩]) unmarked_context_13_26685_90985 node_context_13_26685_90985
  intro a
  fin_cases a
  · exact context_14_106740_90917
  · exact context_14_106741_90940
  · exact context_14_106742_90966
  · exact context_14_106743_90984

theorem selected_cut_02944 : selected 8 ⟨91022, by decide⟩
    (prefixPartial 13 26686) = some ⟨13, 2, 0, 91022, 26686, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_26686_91022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26686 ⟨91022, by decide⟩ :=
  accepted_of_selected 13 26686 ⟨91022, by decide⟩ ⟨13, 2, 0, 91022, 26686, 2769, 16384⟩
    (by decide) selected_cut_02944

theorem selected_cut_02945 : selected 8 ⟨91047, by decide⟩
    (prefixPartial 13 26687) = some ⟨13, 2, 0, 91047, 26687, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_26687_91047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26687 ⟨91047, by decide⟩ :=
  accepted_of_selected 13 26687 ⟨91047, by decide⟩ ⟨13, 2, 0, 91047, 26687, 1569, 16384⟩
    (by decide) selected_cut_02945

theorem unmarked_context_12_6671_91048 : frontier 9 ⟨91048, by decide⟩
    (prefixCache 12 6671) (prefixPartial 12 6671) = false := by
  decide +kernel

theorem node_context_12_6671_91048 : EJMOriginalGlobalDAGData.nodes 9 ⟨91048, by decide⟩ =
    .split (coordinate 12) (![⟨90898, by decide⟩,⟨90985, by decide⟩,⟨91022, by decide⟩,⟨91047, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6671_91048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6671 ⟨91048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6671
    ⟨91048, by decide⟩ (by decide) (![⟨90898, by decide⟩,⟨90985, by decide⟩,⟨91022, by decide⟩,⟨91047, by decide⟩]) unmarked_context_12_6671_91048 node_context_12_6671_91048
  intro a
  fin_cases a
  · exact context_13_26684_90898
  · exact context_13_26685_90985
  · exact context_13_26686_91022
  · exact context_13_26687_91047

theorem unmarked_context_11_1667_91049 : frontier 10 ⟨91049, by decide⟩
    (prefixCache 11 1667) (prefixPartial 11 1667) = false := by
  decide +kernel

theorem node_context_11_1667_91049 : EJMOriginalGlobalDAGData.nodes 10 ⟨91049, by decide⟩ =
    .split (coordinate 11) (![⟨90316, by decide⟩,⟨90593, by decide⟩,⟨90820, by decide⟩,⟨91048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1667_91049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1667 ⟨91049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1667
    ⟨91049, by decide⟩ (by decide) (![⟨90316, by decide⟩,⟨90593, by decide⟩,⟨90820, by decide⟩,⟨91048, by decide⟩]) unmarked_context_11_1667_91049 node_context_11_1667_91049
  intro a
  fin_cases a
  · exact context_12_6668_90316
  · exact context_12_6669_90593
  · exact context_12_6670_90820
  · exact context_12_6671_91048

theorem unmarked_context_10_416_91050 : frontier 11 ⟨91050, by decide⟩
    (prefixCache 10 416) (prefixPartial 10 416) = false := by
  decide +kernel

theorem node_context_10_416_91050 : EJMOriginalGlobalDAGData.nodes 11 ⟨91050, by decide⟩ =
    .split (coordinate 10) (![⟨87383, by decide⟩,⟨88908, by decide⟩,⟨89951, by decide⟩,⟨91049, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_416_91050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 416 ⟨91050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 416
    ⟨91050, by decide⟩ (by decide) (![⟨87383, by decide⟩,⟨88908, by decide⟩,⟨89951, by decide⟩,⟨91049, by decide⟩]) unmarked_context_10_416_91050 node_context_10_416_91050
  intro a
  fin_cases a
  · exact context_11_1664_87383
  · exact context_11_1665_88908
  · exact context_11_1666_89951
  · exact context_11_1667_91049

theorem selected_cut_02946 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6672) = some ⟨12, 1, 0, 1738, 6672, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6672_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6672 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6672 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6672, 1, 65536⟩
    (by decide) selected_cut_02946

theorem selected_cut_02947 : selected 8 ⟨91125, by decide⟩
    (prefixPartial 13 26692) = some ⟨13, 2, 0, 91125, 26692, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_26692_91125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26692 ⟨91125, by decide⟩ :=
  accepted_of_selected 13 26692 ⟨91125, by decide⟩ ⟨13, 2, 0, 91125, 26692, 1981, 16384⟩
    (by decide) selected_cut_02947

theorem selected_cut_02948 : selected 8 ⟨91205, by decide⟩
    (prefixPartial 13 26693) = some ⟨13, 2, 0, 91205, 26693, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_26693_91205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26693 ⟨91205, by decide⟩ :=
  accepted_of_selected 13 26693 ⟨91205, by decide⟩ ⟨13, 2, 0, 91205, 26693, 2157, 16384⟩
    (by decide) selected_cut_02948

theorem selected_cut_02949 : selected 8 ⟨91240, by decide⟩
    (prefixPartial 13 26694) = some ⟨13, 2, 0, 91240, 26694, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_26694_91240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26694 ⟨91240, by decide⟩ :=
  accepted_of_selected 13 26694 ⟨91240, by decide⟩ ⟨13, 2, 0, 91240, 26694, 1117, 16384⟩
    (by decide) selected_cut_02949

theorem selected_cut_02950 : selected 8 ⟨91295, by decide⟩
    (prefixPartial 13 26695) = some ⟨13, 2, 0, 91295, 26695, 897, 16384⟩ := by
  decide +kernel

theorem context_13_26695_91295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26695 ⟨91295, by decide⟩ :=
  accepted_of_selected 13 26695 ⟨91295, by decide⟩ ⟨13, 2, 0, 91295, 26695, 897, 16384⟩
    (by decide) selected_cut_02950

theorem unmarked_context_12_6673_91296 : frontier 9 ⟨91296, by decide⟩
    (prefixCache 12 6673) (prefixPartial 12 6673) = false := by
  decide +kernel

theorem node_context_12_6673_91296 : EJMOriginalGlobalDAGData.nodes 9 ⟨91296, by decide⟩ =
    .split (coordinate 12) (![⟨91125, by decide⟩,⟨91205, by decide⟩,⟨91240, by decide⟩,⟨91295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6673_91296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6673 ⟨91296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6673
    ⟨91296, by decide⟩ (by decide) (![⟨91125, by decide⟩,⟨91205, by decide⟩,⟨91240, by decide⟩,⟨91295, by decide⟩]) unmarked_context_12_6673_91296 node_context_12_6673_91296
  intro a
  fin_cases a
  · exact context_13_26692_91125
  · exact context_13_26693_91205
  · exact context_13_26694_91240
  · exact context_13_26695_91295

theorem selected_cut_02951 : selected 8 ⟨91360, by decide⟩
    (prefixPartial 13 26696) = some ⟨13, 2, 0, 91360, 26696, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_26696_91360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26696 ⟨91360, by decide⟩ :=
  accepted_of_selected 13 26696 ⟨91360, by decide⟩ ⟨13, 2, 0, 91360, 26696, 2329, 16384⟩
    (by decide) selected_cut_02951

theorem selected_cut_02952 : selected 8 ⟨91425, by decide⟩
    (prefixPartial 13 26697) = some ⟨13, 2, 0, 91425, 26697, 2953, 16384⟩ := by
  decide +kernel

theorem context_13_26697_91425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26697 ⟨91425, by decide⟩ :=
  accepted_of_selected 13 26697 ⟨91425, by decide⟩ ⟨13, 2, 0, 91425, 26697, 2953, 16384⟩
    (by decide) selected_cut_02952

theorem selected_cut_02953 : selected 8 ⟨91448, by decide⟩
    (prefixPartial 13 26698) = some ⟨13, 2, 0, 91448, 26698, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_26698_91448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26698 ⟨91448, by decide⟩ :=
  accepted_of_selected 13 26698 ⟨91448, by decide⟩ ⟨13, 2, 0, 91448, 26698, 1665, 16384⟩
    (by decide) selected_cut_02953

theorem selected_cut_02954 : selected 8 ⟨91473, by decide⟩
    (prefixPartial 13 26699) = some ⟨13, 2, 0, 91473, 26699, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_26699_91473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26699 ⟨91473, by decide⟩ :=
  accepted_of_selected 13 26699 ⟨91473, by decide⟩ ⟨13, 2, 0, 91473, 26699, 1161, 16384⟩
    (by decide) selected_cut_02954

theorem unmarked_context_12_6674_91474 : frontier 9 ⟨91474, by decide⟩
    (prefixCache 12 6674) (prefixPartial 12 6674) = false := by
  decide +kernel

theorem node_context_12_6674_91474 : EJMOriginalGlobalDAGData.nodes 9 ⟨91474, by decide⟩ =
    .split (coordinate 12) (![⟨91360, by decide⟩,⟨91425, by decide⟩,⟨91448, by decide⟩,⟨91473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6674_91474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6674 ⟨91474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6674
    ⟨91474, by decide⟩ (by decide) (![⟨91360, by decide⟩,⟨91425, by decide⟩,⟨91448, by decide⟩,⟨91473, by decide⟩]) unmarked_context_12_6674_91474 node_context_12_6674_91474
  intro a
  fin_cases a
  · exact context_13_26696_91360
  · exact context_13_26697_91425
  · exact context_13_26698_91448
  · exact context_13_26699_91473

theorem selected_cut_02955 : selected 8 ⟨91547, by decide⟩
    (prefixPartial 13 26700) = some ⟨13, 2, 0, 91547, 26700, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_26700_91547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26700 ⟨91547, by decide⟩ :=
  accepted_of_selected 13 26700 ⟨91547, by decide⟩ ⟨13, 2, 0, 91547, 26700, 2757, 16384⟩
    (by decide) selected_cut_02955

theorem selected_cut_02956 : selected 8 ⟨91624, by decide⟩
    (prefixPartial 13 26701) = some ⟨13, 2, 0, 91624, 26701, 3501, 16384⟩ := by
  decide +kernel

theorem context_13_26701_91624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26701 ⟨91624, by decide⟩ :=
  accepted_of_selected 13 26701 ⟨91624, by decide⟩ ⟨13, 2, 0, 91624, 26701, 3501, 16384⟩
    (by decide) selected_cut_02956

theorem selected_cut_02957 : selected 8 ⟨91655, by decide⟩
    (prefixPartial 13 26702) = some ⟨13, 2, 0, 91655, 26702, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_26702_91655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26702 ⟨91655, by decide⟩ :=
  accepted_of_selected 13 26702 ⟨91655, by decide⟩ ⟨13, 2, 0, 91655, 26702, 1801, 16384⟩
    (by decide) selected_cut_02957

theorem selected_cut_02958 : selected 8 ⟨91681, by decide⟩
    (prefixPartial 13 26703) = some ⟨13, 2, 0, 91681, 26703, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_26703_91681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26703 ⟨91681, by decide⟩ :=
  accepted_of_selected 13 26703 ⟨91681, by decide⟩ ⟨13, 2, 0, 91681, 26703, 1297, 16384⟩
    (by decide) selected_cut_02958

theorem unmarked_context_12_6675_91682 : frontier 9 ⟨91682, by decide⟩
    (prefixCache 12 6675) (prefixPartial 12 6675) = false := by
  decide +kernel

theorem node_context_12_6675_91682 : EJMOriginalGlobalDAGData.nodes 9 ⟨91682, by decide⟩ =
    .split (coordinate 12) (![⟨91547, by decide⟩,⟨91624, by decide⟩,⟨91655, by decide⟩,⟨91681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6675_91682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6675 ⟨91682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6675
    ⟨91682, by decide⟩ (by decide) (![⟨91547, by decide⟩,⟨91624, by decide⟩,⟨91655, by decide⟩,⟨91681, by decide⟩]) unmarked_context_12_6675_91682 node_context_12_6675_91682
  intro a
  fin_cases a
  · exact context_13_26700_91547
  · exact context_13_26701_91624
  · exact context_13_26702_91655
  · exact context_13_26703_91681

theorem unmarked_context_11_1668_91683 : frontier 10 ⟨91683, by decide⟩
    (prefixCache 11 1668) (prefixPartial 11 1668) = false := by
  decide +kernel

theorem node_context_11_1668_91683 : EJMOriginalGlobalDAGData.nodes 10 ⟨91683, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨91296, by decide⟩,⟨91474, by decide⟩,⟨91682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1668_91683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1668 ⟨91683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1668
    ⟨91683, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨91296, by decide⟩,⟨91474, by decide⟩,⟨91682, by decide⟩]) unmarked_context_11_1668_91683 node_context_11_1668_91683
  intro a
  fin_cases a
  · exact context_12_6672_1738
  · exact context_12_6673_91296
  · exact context_12_6674_91474
  · exact context_12_6675_91682

theorem selected_cut_02959 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6676) = some ⟨12, 1, 0, 1738, 6676, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6676_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6676 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6676 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6676, 1, 65536⟩
    (by decide) selected_cut_02959

theorem selected_cut_02960 : selected 8 ⟨91730, by decide⟩
    (prefixPartial 13 26708) = some ⟨13, 2, 0, 91730, 26708, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_26708_91730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26708 ⟨91730, by decide⟩ :=
  accepted_of_selected 13 26708 ⟨91730, by decide⟩ ⟨13, 2, 0, 91730, 26708, 1721, 16384⟩
    (by decide) selected_cut_02960

theorem selected_cut_02961 : selected 8 ⟨91794, by decide⟩
    (prefixPartial 13 26709) = some ⟨13, 2, 0, 91794, 26709, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_26709_91794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26709 ⟨91794, by decide⟩ :=
  accepted_of_selected 13 26709 ⟨91794, by decide⟩ ⟨13, 2, 0, 91794, 26709, 2193, 16384⟩
    (by decide) selected_cut_02961

theorem selected_cut_02962 : selected 8 ⟨91830, by decide⟩
    (prefixPartial 13 26710) = some ⟨13, 2, 0, 91830, 26710, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_26710_91830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26710 ⟨91830, by decide⟩ :=
  accepted_of_selected 13 26710 ⟨91830, by decide⟩ ⟨13, 2, 0, 91830, 26710, 1293, 16384⟩
    (by decide) selected_cut_02962

theorem selected_cut_02963 : selected 8 ⟨91856, by decide⟩
    (prefixPartial 13 26711) = some ⟨13, 2, 0, 91856, 26711, 893, 16384⟩ := by
  decide +kernel

theorem context_13_26711_91856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26711 ⟨91856, by decide⟩ :=
  accepted_of_selected 13 26711 ⟨91856, by decide⟩ ⟨13, 2, 0, 91856, 26711, 893, 16384⟩
    (by decide) selected_cut_02963

theorem unmarked_context_12_6677_91857 : frontier 9 ⟨91857, by decide⟩
    (prefixCache 12 6677) (prefixPartial 12 6677) = false := by
  decide +kernel

theorem node_context_12_6677_91857 : EJMOriginalGlobalDAGData.nodes 9 ⟨91857, by decide⟩ =
    .split (coordinate 12) (![⟨91730, by decide⟩,⟨91794, by decide⟩,⟨91830, by decide⟩,⟨91856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6677_91857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6677 ⟨91857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6677
    ⟨91857, by decide⟩ (by decide) (![⟨91730, by decide⟩,⟨91794, by decide⟩,⟨91830, by decide⟩,⟨91856, by decide⟩]) unmarked_context_12_6677_91857 node_context_12_6677_91857
  intro a
  fin_cases a
  · exact context_13_26708_91730
  · exact context_13_26709_91794
  · exact context_13_26710_91830
  · exact context_13_26711_91856

theorem selected_cut_02964 : selected 8 ⟨91904, by decide⟩
    (prefixPartial 13 26712) = some ⟨13, 2, 0, 91904, 26712, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_26712_91904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26712 ⟨91904, by decide⟩ :=
  accepted_of_selected 13 26712 ⟨91904, by decide⟩ ⟨13, 2, 0, 91904, 26712, 1969, 16384⟩
    (by decide) selected_cut_02964

theorem selected_cut_02965 : selected 8 ⟨91950, by decide⟩
    (prefixPartial 13 26713) = some ⟨13, 2, 0, 91950, 26713, 2993, 16384⟩ := by
  decide +kernel

theorem context_13_26713_91950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26713 ⟨91950, by decide⟩ :=
  accepted_of_selected 13 26713 ⟨91950, by decide⟩ ⟨13, 2, 0, 91950, 26713, 2993, 16384⟩
    (by decide) selected_cut_02965

theorem selected_cut_02966 : selected 8 ⟨91981, by decide⟩
    (prefixPartial 13 26714) = some ⟨13, 2, 0, 91981, 26714, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_26714_91981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26714 ⟨91981, by decide⟩ :=
  accepted_of_selected 13 26714 ⟨91981, by decide⟩ ⟨13, 2, 0, 91981, 26714, 1929, 16384⟩
    (by decide) selected_cut_02966

theorem selected_cut_02967 : selected 8 ⟨91998, by decide⟩
    (prefixPartial 13 26715) = some ⟨13, 2, 0, 91998, 26715, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_26715_91998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26715 ⟨91998, by decide⟩ :=
  accepted_of_selected 13 26715 ⟨91998, by decide⟩ ⟨13, 2, 0, 91998, 26715, 1249, 16384⟩
    (by decide) selected_cut_02967

theorem unmarked_context_12_6678_91999 : frontier 9 ⟨91999, by decide⟩
    (prefixCache 12 6678) (prefixPartial 12 6678) = false := by
  decide +kernel

theorem node_context_12_6678_91999 : EJMOriginalGlobalDAGData.nodes 9 ⟨91999, by decide⟩ =
    .split (coordinate 12) (![⟨91904, by decide⟩,⟨91950, by decide⟩,⟨91981, by decide⟩,⟨91998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6678_91999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6678 ⟨91999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6678
    ⟨91999, by decide⟩ (by decide) (![⟨91904, by decide⟩,⟨91950, by decide⟩,⟨91981, by decide⟩,⟨91998, by decide⟩]) unmarked_context_12_6678_91999 node_context_12_6678_91999
  intro a
  fin_cases a
  · exact context_13_26712_91904
  · exact context_13_26713_91950
  · exact context_13_26714_91981
  · exact context_13_26715_91998

theorem selected_cut_02968 : selected 8 ⟨92059, by decide⟩
    (prefixPartial 13 26716) = some ⟨13, 2, 0, 92059, 26716, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_26716_92059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26716 ⟨92059, by decide⟩ :=
  accepted_of_selected 13 26716 ⟨92059, by decide⟩ ⟨13, 2, 0, 92059, 26716, 2577, 16384⟩
    (by decide) selected_cut_02968

theorem selected_cut_02969 : selected 8 ⟨92123, by decide⟩
    (prefixPartial 13 26717) = some ⟨13, 2, 0, 92123, 26717, 3517, 16384⟩ := by
  decide +kernel

theorem context_13_26717_92123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26717 ⟨92123, by decide⟩ :=
  accepted_of_selected 13 26717 ⟨92123, by decide⟩ ⟨13, 2, 0, 92123, 26717, 3517, 16384⟩
    (by decide) selected_cut_02969

theorem selected_cut_02970 : selected 8 ⟨92156, by decide⟩
    (prefixPartial 13 26718) = some ⟨13, 2, 0, 92156, 26718, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_26718_92156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26718 ⟨92156, by decide⟩ :=
  accepted_of_selected 13 26718 ⟨92156, by decide⟩ ⟨13, 2, 0, 92156, 26718, 2281, 16384⟩
    (by decide) selected_cut_02970

theorem selected_cut_02971 : selected 8 ⟨92174, by decide⟩
    (prefixPartial 13 26719) = some ⟨13, 2, 0, 92174, 26719, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_26719_92174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26719 ⟨92174, by decide⟩ :=
  accepted_of_selected 13 26719 ⟨92174, by decide⟩ ⟨13, 2, 0, 92174, 26719, 1337, 16384⟩
    (by decide) selected_cut_02971

theorem unmarked_context_12_6679_92175 : frontier 9 ⟨92175, by decide⟩
    (prefixCache 12 6679) (prefixPartial 12 6679) = false := by
  decide +kernel

theorem node_context_12_6679_92175 : EJMOriginalGlobalDAGData.nodes 9 ⟨92175, by decide⟩ =
    .split (coordinate 12) (![⟨92059, by decide⟩,⟨92123, by decide⟩,⟨92156, by decide⟩,⟨92174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6679_92175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6679 ⟨92175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6679
    ⟨92175, by decide⟩ (by decide) (![⟨92059, by decide⟩,⟨92123, by decide⟩,⟨92156, by decide⟩,⟨92174, by decide⟩]) unmarked_context_12_6679_92175 node_context_12_6679_92175
  intro a
  fin_cases a
  · exact context_13_26716_92059
  · exact context_13_26717_92123
  · exact context_13_26718_92156
  · exact context_13_26719_92174

theorem unmarked_context_11_1669_92176 : frontier 10 ⟨92176, by decide⟩
    (prefixCache 11 1669) (prefixPartial 11 1669) = false := by
  decide +kernel

theorem node_context_11_1669_92176 : EJMOriginalGlobalDAGData.nodes 10 ⟨92176, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨91857, by decide⟩,⟨91999, by decide⟩,⟨92175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1669_92176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1669 ⟨92176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1669
    ⟨92176, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨91857, by decide⟩,⟨91999, by decide⟩,⟨92175, by decide⟩]) unmarked_context_11_1669_92176 node_context_11_1669_92176
  intro a
  fin_cases a
  · exact context_12_6676_1738
  · exact context_12_6677_91857
  · exact context_12_6678_91999
  · exact context_12_6679_92175

theorem selected_cut_02972 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6680) = some ⟨12, 1, 0, 1738, 6680, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6680_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6680 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6680 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6680, 1, 65536⟩
    (by decide) selected_cut_02972

theorem selected_cut_02973 : selected 8 ⟨92229, by decide⟩
    (prefixPartial 13 26724) = some ⟨13, 2, 0, 92229, 26724, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_26724_92229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26724 ⟨92229, by decide⟩ :=
  accepted_of_selected 13 26724 ⟨92229, by decide⟩ ⟨13, 2, 0, 92229, 26724, 1625, 16384⟩
    (by decide) selected_cut_02973

theorem selected_cut_02974 : selected 8 ⟨92305, by decide⟩
    (prefixPartial 13 26725) = some ⟨13, 2, 0, 92305, 26725, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_26725_92305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26725 ⟨92305, by decide⟩ :=
  accepted_of_selected 13 26725 ⟨92305, by decide⟩ ⟨13, 2, 0, 92305, 26725, 1881, 16384⟩
    (by decide) selected_cut_02974

theorem selected_cut_02975 : selected 8 ⟨92340, by decide⟩
    (prefixPartial 13 26726) = some ⟨13, 2, 0, 92340, 26726, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_26726_92340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26726 ⟨92340, by decide⟩ :=
  accepted_of_selected 13 26726 ⟨92340, by decide⟩ ⟨13, 2, 0, 92340, 26726, 1217, 16384⟩
    (by decide) selected_cut_02975

theorem selected_cut_02976 : selected 8 ⟨92378, by decide⟩
    (prefixPartial 13 26727) = some ⟨13, 2, 0, 92378, 26727, 921, 16384⟩ := by
  decide +kernel

theorem context_13_26727_92378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26727 ⟨92378, by decide⟩ :=
  accepted_of_selected 13 26727 ⟨92378, by decide⟩ ⟨13, 2, 0, 92378, 26727, 921, 16384⟩
    (by decide) selected_cut_02976

theorem unmarked_context_12_6681_92379 : frontier 9 ⟨92379, by decide⟩
    (prefixCache 12 6681) (prefixPartial 12 6681) = false := by
  decide +kernel

theorem node_context_12_6681_92379 : EJMOriginalGlobalDAGData.nodes 9 ⟨92379, by decide⟩ =
    .split (coordinate 12) (![⟨92229, by decide⟩,⟨92305, by decide⟩,⟨92340, by decide⟩,⟨92378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6681_92379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6681 ⟨92379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6681
    ⟨92379, by decide⟩ (by decide) (![⟨92229, by decide⟩,⟨92305, by decide⟩,⟨92340, by decide⟩,⟨92378, by decide⟩]) unmarked_context_12_6681_92379 node_context_12_6681_92379
  intro a
  fin_cases a
  · exact context_13_26724_92229
  · exact context_13_26725_92305
  · exact context_13_26726_92340
  · exact context_13_26727_92378

theorem selected_cut_02977 : selected 8 ⟨92477, by decide⟩
    (prefixPartial 13 26728) = some ⟨13, 2, 0, 92477, 26728, 2697, 16384⟩ := by
  decide +kernel

theorem context_13_26728_92477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26728 ⟨92477, by decide⟩ :=
  accepted_of_selected 13 26728 ⟨92477, by decide⟩ ⟨13, 2, 0, 92477, 26728, 2697, 16384⟩
    (by decide) selected_cut_02977

theorem selected_cut_02978 : selected 7 ⟨92497, by decide⟩
    (prefixPartial 14 106916) = some ⟨14, 2, 0, 92497, 106916, 913, 4096⟩ := by
  decide +kernel

theorem context_14_106916_92497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106916 ⟨92497, by decide⟩ :=
  accepted_of_selected 14 106916 ⟨92497, by decide⟩ ⟨14, 2, 0, 92497, 106916, 913, 4096⟩
    (by decide) selected_cut_02978

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
