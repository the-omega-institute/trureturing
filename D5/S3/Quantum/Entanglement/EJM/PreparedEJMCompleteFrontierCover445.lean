/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover444
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_42724 : selected 9 ⟨1167213, by decide⟩
    (prefixPartial 12 338575) = some ⟨12, 2, 0, 1167213, 338575, 993, 65536⟩ := by
  decide +kernel

theorem context_12_338575_1167213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338575 ⟨1167213, by decide⟩ :=
  accepted_of_selected 12 338575 ⟨1167213, by decide⟩ ⟨12, 2, 0, 1167213, 338575, 993, 65536⟩
    (by decide) selected_cut_42724

theorem unmarked_context_11_84643_1167214 : frontier 10 ⟨1167214, by decide⟩
    (prefixCache 11 84643) (prefixPartial 11 84643) = false := by
  decide +kernel

theorem node_context_11_84643_1167214 : EJMOriginalGlobalDAGData.nodes 10 ⟨1167214, by decide⟩ =
    .split (coordinate 11) (![⟨1167167, by decide⟩,⟨1167185, by decide⟩,⟨1167200, by decide⟩,⟨1167213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84643_1167214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84643 ⟨1167214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84643
    ⟨1167214, by decide⟩ (by decide) (![⟨1167167, by decide⟩,⟨1167185, by decide⟩,⟨1167200, by decide⟩,⟨1167213, by decide⟩]) unmarked_context_11_84643_1167214 node_context_11_84643_1167214
  intro a
  fin_cases a
  · exact context_12_338572_1167167
  · exact context_12_338573_1167185
  · exact context_12_338574_1167200
  · exact context_12_338575_1167213

theorem unmarked_context_10_21160_1167215 : frontier 11 ⟨1167215, by decide⟩
    (prefixCache 10 21160) (prefixPartial 10 21160) = false := by
  decide +kernel

theorem node_context_10_21160_1167215 : EJMOriginalGlobalDAGData.nodes 11 ⟨1167215, by decide⟩ =
    .split (coordinate 10) (![⟨1167025, by decide⟩,⟨1167101, by decide⟩,⟨1167151, by decide⟩,⟨1167214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21160_1167215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21160 ⟨1167215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21160
    ⟨1167215, by decide⟩ (by decide) (![⟨1167025, by decide⟩,⟨1167101, by decide⟩,⟨1167151, by decide⟩,⟨1167214, by decide⟩]) unmarked_context_10_21160_1167215 node_context_10_21160_1167215
  intro a
  fin_cases a
  · exact context_11_84640_1167025
  · exact context_11_84641_1167101
  · exact context_11_84642_1167151
  · exact context_11_84643_1167214

theorem selected_cut_42725 : selected 10 ⟨1167246, by decide⟩
    (prefixPartial 11 84644) = some ⟨11, 2, 0, 1167246, 84644, 2101, 262144⟩ := by
  decide +kernel

theorem context_11_84644_1167246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84644 ⟨1167246, by decide⟩ :=
  accepted_of_selected 11 84644 ⟨1167246, by decide⟩ ⟨11, 2, 0, 1167246, 84644, 2101, 262144⟩
    (by decide) selected_cut_42725

theorem selected_cut_42726 : selected 10 ⟨1163822, by decide⟩
    (prefixPartial 11 84645) = some ⟨11, 2, 0, 1163822, 84645, 5, 262144⟩ := by
  decide +kernel

theorem context_11_84645_1163822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84645 ⟨1163822, by decide⟩ :=
  accepted_of_selected 11 84645 ⟨1163822, by decide⟩ ⟨11, 2, 0, 1163822, 84645, 5, 262144⟩
    (by decide) selected_cut_42726

theorem selected_cut_42727 : selected 10 ⟨1167280, by decide⟩
    (prefixPartial 11 84646) = some ⟨11, 2, 0, 1167280, 84646, 2433, 262144⟩ := by
  decide +kernel

theorem context_11_84646_1167280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84646 ⟨1167280, by decide⟩ :=
  accepted_of_selected 11 84646 ⟨1167280, by decide⟩ ⟨11, 2, 0, 1167280, 84646, 2433, 262144⟩
    (by decide) selected_cut_42727

theorem selected_cut_42728 : selected 10 ⟨1167327, by decide⟩
    (prefixPartial 11 84647) = some ⟨11, 2, 0, 1167327, 84647, 3425, 262144⟩ := by
  decide +kernel

theorem context_11_84647_1167327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84647 ⟨1167327, by decide⟩ :=
  accepted_of_selected 11 84647 ⟨1167327, by decide⟩ ⟨11, 2, 0, 1167327, 84647, 3425, 262144⟩
    (by decide) selected_cut_42728

theorem unmarked_context_10_21161_1167328 : frontier 11 ⟨1167328, by decide⟩
    (prefixCache 10 21161) (prefixPartial 10 21161) = false := by
  decide +kernel

theorem node_context_10_21161_1167328 : EJMOriginalGlobalDAGData.nodes 11 ⟨1167328, by decide⟩ =
    .split (coordinate 10) (![⟨1167246, by decide⟩,⟨1163822, by decide⟩,⟨1167280, by decide⟩,⟨1167327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21161_1167328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21161 ⟨1167328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21161
    ⟨1167328, by decide⟩ (by decide) (![⟨1167246, by decide⟩,⟨1163822, by decide⟩,⟨1167280, by decide⟩,⟨1167327, by decide⟩]) unmarked_context_10_21161_1167328 node_context_10_21161_1167328
  intro a
  fin_cases a
  · exact context_11_84644_1167246
  · exact context_11_84645_1163822
  · exact context_11_84646_1167280
  · exact context_11_84647_1167327

theorem selected_cut_42729 : selected 10 ⟨1167354, by decide⟩
    (prefixPartial 11 84648) = some ⟨11, 2, 0, 1167354, 84648, 1649, 262144⟩ := by
  decide +kernel

theorem context_11_84648_1167354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84648 ⟨1167354, by decide⟩ :=
  accepted_of_selected 11 84648 ⟨1167354, by decide⟩ ⟨11, 2, 0, 1167354, 84648, 1649, 262144⟩
    (by decide) selected_cut_42729

theorem selected_cut_42730 : selected 10 ⟨1167371, by decide⟩
    (prefixPartial 11 84649) = some ⟨11, 2, 0, 1167371, 84649, 901, 262144⟩ := by
  decide +kernel

theorem context_11_84649_1167371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84649 ⟨1167371, by decide⟩ :=
  accepted_of_selected 11 84649 ⟨1167371, by decide⟩ ⟨11, 2, 0, 1167371, 84649, 901, 262144⟩
    (by decide) selected_cut_42730

theorem selected_cut_42731 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84650) = some ⟨11, 1, 0, 1109453, 84650, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84650_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84650 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84650 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84650, 1, 262144⟩
    (by decide) selected_cut_42731

theorem selected_cut_42732 : selected 10 ⟨1167400, by decide⟩
    (prefixPartial 11 84651) = some ⟨11, 2, 0, 1167400, 84651, 2169, 262144⟩ := by
  decide +kernel

theorem context_11_84651_1167400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84651 ⟨1167400, by decide⟩ :=
  accepted_of_selected 11 84651 ⟨1167400, by decide⟩ ⟨11, 2, 0, 1167400, 84651, 2169, 262144⟩
    (by decide) selected_cut_42732

theorem unmarked_context_10_21162_1167401 : frontier 11 ⟨1167401, by decide⟩
    (prefixCache 10 21162) (prefixPartial 10 21162) = false := by
  decide +kernel

theorem node_context_10_21162_1167401 : EJMOriginalGlobalDAGData.nodes 11 ⟨1167401, by decide⟩ =
    .split (coordinate 10) (![⟨1167354, by decide⟩,⟨1167371, by decide⟩,⟨1109453, by decide⟩,⟨1167400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21162_1167401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21162 ⟨1167401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21162
    ⟨1167401, by decide⟩ (by decide) (![⟨1167354, by decide⟩,⟨1167371, by decide⟩,⟨1109453, by decide⟩,⟨1167400, by decide⟩]) unmarked_context_10_21162_1167401 node_context_10_21162_1167401
  intro a
  fin_cases a
  · exact context_11_84648_1167354
  · exact context_11_84649_1167371
  · exact context_11_84650_1109453
  · exact context_11_84651_1167400

theorem selected_cut_42733 : selected 10 ⟨1167433, by decide⟩
    (prefixPartial 11 84652) = some ⟨11, 2, 0, 1167433, 84652, 2225, 262144⟩ := by
  decide +kernel

theorem context_11_84652_1167433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84652 ⟨1167433, by decide⟩ :=
  accepted_of_selected 11 84652 ⟨1167433, by decide⟩ ⟨11, 2, 0, 1167433, 84652, 2225, 262144⟩
    (by decide) selected_cut_42733

theorem selected_cut_42734 : selected 10 ⟨1167473, by decide⟩
    (prefixPartial 11 84653) = some ⟨11, 2, 0, 1167473, 84653, 2809, 262144⟩ := by
  decide +kernel

theorem context_11_84653_1167473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84653 ⟨1167473, by decide⟩ :=
  accepted_of_selected 11 84653 ⟨1167473, by decide⟩ ⟨11, 2, 0, 1167473, 84653, 2809, 262144⟩
    (by decide) selected_cut_42734

theorem selected_cut_42735 : selected 10 ⟨1167497, by decide⟩
    (prefixPartial 11 84654) = some ⟨11, 2, 0, 1167497, 84654, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_84654_1167497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84654 ⟨1167497, by decide⟩ :=
  accepted_of_selected 11 84654 ⟨1167497, by decide⟩ ⟨11, 2, 0, 1167497, 84654, 1661, 262144⟩
    (by decide) selected_cut_42735

theorem selected_cut_42736 : selected 10 ⟨1167520, by decide⟩
    (prefixPartial 11 84655) = some ⟨11, 2, 0, 1167520, 84655, 1637, 262144⟩ := by
  decide +kernel

theorem context_11_84655_1167520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84655 ⟨1167520, by decide⟩ :=
  accepted_of_selected 11 84655 ⟨1167520, by decide⟩ ⟨11, 2, 0, 1167520, 84655, 1637, 262144⟩
    (by decide) selected_cut_42736

theorem unmarked_context_10_21163_1167521 : frontier 11 ⟨1167521, by decide⟩
    (prefixCache 10 21163) (prefixPartial 10 21163) = false := by
  decide +kernel

theorem node_context_10_21163_1167521 : EJMOriginalGlobalDAGData.nodes 11 ⟨1167521, by decide⟩ =
    .split (coordinate 10) (![⟨1167433, by decide⟩,⟨1167473, by decide⟩,⟨1167497, by decide⟩,⟨1167520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21163_1167521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21163 ⟨1167521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21163
    ⟨1167521, by decide⟩ (by decide) (![⟨1167433, by decide⟩,⟨1167473, by decide⟩,⟨1167497, by decide⟩,⟨1167520, by decide⟩]) unmarked_context_10_21163_1167521 node_context_10_21163_1167521
  intro a
  fin_cases a
  · exact context_11_84652_1167433
  · exact context_11_84653_1167473
  · exact context_11_84654_1167497
  · exact context_11_84655_1167520

theorem unmarked_context_9_5290_1167522 : frontier 12 ⟨1167522, by decide⟩
    (prefixCache 9 5290) (prefixPartial 9 5290) = false := by
  decide +kernel

theorem node_context_9_5290_1167522 : EJMOriginalGlobalDAGData.nodes 12 ⟨1167522, by decide⟩ =
    .split (coordinate 9) (![⟨1167215, by decide⟩,⟨1167328, by decide⟩,⟨1167401, by decide⟩,⟨1167521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5290_1167522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5290 ⟨1167522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5290
    ⟨1167522, by decide⟩ (by decide) (![⟨1167215, by decide⟩,⟨1167328, by decide⟩,⟨1167401, by decide⟩,⟨1167521, by decide⟩]) unmarked_context_9_5290_1167522 node_context_9_5290_1167522
  intro a
  fin_cases a
  · exact context_10_21160_1167215
  · exact context_10_21161_1167328
  · exact context_10_21162_1167401
  · exact context_10_21163_1167521

theorem selected_cut_42737 : selected 10 ⟨1167550, by decide⟩
    (prefixPartial 11 84656) = some ⟨11, 2, 0, 1167550, 84656, 2145, 262144⟩ := by
  decide +kernel

theorem context_11_84656_1167550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84656 ⟨1167550, by decide⟩ :=
  accepted_of_selected 11 84656 ⟨1167550, by decide⟩ ⟨11, 2, 0, 1167550, 84656, 2145, 262144⟩
    (by decide) selected_cut_42737

theorem selected_cut_42738 : selected 10 ⟨1167581, by decide⟩
    (prefixPartial 11 84657) = some ⟨11, 2, 0, 1167581, 84657, 2301, 262144⟩ := by
  decide +kernel

theorem context_11_84657_1167581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84657 ⟨1167581, by decide⟩ :=
  accepted_of_selected 11 84657 ⟨1167581, by decide⟩ ⟨11, 2, 0, 1167581, 84657, 2301, 262144⟩
    (by decide) selected_cut_42738

theorem selected_cut_42739 : selected 10 ⟨1167602, by decide⟩
    (prefixPartial 11 84658) = some ⟨11, 2, 0, 1167602, 84658, 1381, 262144⟩ := by
  decide +kernel

theorem context_11_84658_1167602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84658 ⟨1167602, by decide⟩ :=
  accepted_of_selected 11 84658 ⟨1167602, by decide⟩ ⟨11, 2, 0, 1167602, 84658, 1381, 262144⟩
    (by decide) selected_cut_42739

theorem selected_cut_42740 : selected 10 ⟨1167621, by decide⟩
    (prefixPartial 11 84659) = some ⟨11, 2, 0, 1167621, 84659, 1457, 262144⟩ := by
  decide +kernel

theorem context_11_84659_1167621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84659 ⟨1167621, by decide⟩ :=
  accepted_of_selected 11 84659 ⟨1167621, by decide⟩ ⟨11, 2, 0, 1167621, 84659, 1457, 262144⟩
    (by decide) selected_cut_42740

theorem unmarked_context_10_21164_1167622 : frontier 11 ⟨1167622, by decide⟩
    (prefixCache 10 21164) (prefixPartial 10 21164) = false := by
  decide +kernel

theorem node_context_10_21164_1167622 : EJMOriginalGlobalDAGData.nodes 11 ⟨1167622, by decide⟩ =
    .split (coordinate 10) (![⟨1167550, by decide⟩,⟨1167581, by decide⟩,⟨1167602, by decide⟩,⟨1167621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21164_1167622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21164 ⟨1167622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21164
    ⟨1167622, by decide⟩ (by decide) (![⟨1167550, by decide⟩,⟨1167581, by decide⟩,⟨1167602, by decide⟩,⟨1167621, by decide⟩]) unmarked_context_10_21164_1167622 node_context_10_21164_1167622
  intro a
  fin_cases a
  · exact context_11_84656_1167550
  · exact context_11_84657_1167581
  · exact context_11_84658_1167602
  · exact context_11_84659_1167621

theorem selected_cut_42741 : selected 10 ⟨1167640, by decide⟩
    (prefixPartial 11 84660) = some ⟨11, 2, 0, 1167640, 84660, 1613, 262144⟩ := by
  decide +kernel

theorem context_11_84660_1167640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84660 ⟨1167640, by decide⟩ :=
  accepted_of_selected 11 84660 ⟨1167640, by decide⟩ ⟨11, 2, 0, 1167640, 84660, 1613, 262144⟩
    (by decide) selected_cut_42741

theorem selected_cut_42742 : selected 10 ⟨1167655, by decide⟩
    (prefixPartial 11 84661) = some ⟨11, 2, 0, 1167655, 84661, 1089, 262144⟩ := by
  decide +kernel

theorem context_11_84661_1167655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84661 ⟨1167655, by decide⟩ :=
  accepted_of_selected 11 84661 ⟨1167655, by decide⟩ ⟨11, 2, 0, 1167655, 84661, 1089, 262144⟩
    (by decide) selected_cut_42742

theorem selected_cut_42743 : selected 10 ⟨1167666, by decide⟩
    (prefixPartial 11 84662) = some ⟨11, 2, 0, 1167666, 84662, 789, 262144⟩ := by
  decide +kernel

theorem context_11_84662_1167666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84662 ⟨1167666, by decide⟩ :=
  accepted_of_selected 11 84662 ⟨1167666, by decide⟩ ⟨11, 2, 0, 1167666, 84662, 789, 262144⟩
    (by decide) selected_cut_42743

theorem selected_cut_42744 : selected 10 ⟨1167681, by decide⟩
    (prefixPartial 11 84663) = some ⟨11, 2, 0, 1167681, 84663, 801, 262144⟩ := by
  decide +kernel

theorem context_11_84663_1167681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84663 ⟨1167681, by decide⟩ :=
  accepted_of_selected 11 84663 ⟨1167681, by decide⟩ ⟨11, 2, 0, 1167681, 84663, 801, 262144⟩
    (by decide) selected_cut_42744

theorem unmarked_context_10_21165_1167682 : frontier 11 ⟨1167682, by decide⟩
    (prefixCache 10 21165) (prefixPartial 10 21165) = false := by
  decide +kernel

theorem node_context_10_21165_1167682 : EJMOriginalGlobalDAGData.nodes 11 ⟨1167682, by decide⟩ =
    .split (coordinate 10) (![⟨1167640, by decide⟩,⟨1167655, by decide⟩,⟨1167666, by decide⟩,⟨1167681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21165_1167682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21165 ⟨1167682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21165
    ⟨1167682, by decide⟩ (by decide) (![⟨1167640, by decide⟩,⟨1167655, by decide⟩,⟨1167666, by decide⟩,⟨1167681, by decide⟩]) unmarked_context_10_21165_1167682 node_context_10_21165_1167682
  intro a
  fin_cases a
  · exact context_11_84660_1167640
  · exact context_11_84661_1167655
  · exact context_11_84662_1167666
  · exact context_11_84663_1167681

theorem selected_cut_42745 : selected 11 ⟨1167715, by decide⟩
    (prefixPartial 10 21166) = some ⟨10, 2, 0, 1167715, 21166, 1825, 1048576⟩ := by
  decide +kernel

theorem context_10_21166_1167715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21166 ⟨1167715, by decide⟩ :=
  accepted_of_selected 10 21166 ⟨1167715, by decide⟩ ⟨10, 2, 0, 1167715, 21166, 1825, 1048576⟩
    (by decide) selected_cut_42745

theorem selected_cut_42746 : selected 11 ⟨1167727, by decide⟩
    (prefixPartial 10 21167) = some ⟨10, 2, 0, 1167727, 21167, 529, 1048576⟩ := by
  decide +kernel

theorem context_10_21167_1167727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21167 ⟨1167727, by decide⟩ :=
  accepted_of_selected 10 21167 ⟨1167727, by decide⟩ ⟨10, 2, 0, 1167727, 21167, 529, 1048576⟩
    (by decide) selected_cut_42746

theorem unmarked_context_9_5291_1167728 : frontier 12 ⟨1167728, by decide⟩
    (prefixCache 9 5291) (prefixPartial 9 5291) = false := by
  decide +kernel

theorem node_context_9_5291_1167728 : EJMOriginalGlobalDAGData.nodes 12 ⟨1167728, by decide⟩ =
    .split (coordinate 9) (![⟨1167622, by decide⟩,⟨1167682, by decide⟩,⟨1167715, by decide⟩,⟨1167727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5291_1167728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5291 ⟨1167728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5291
    ⟨1167728, by decide⟩ (by decide) (![⟨1167622, by decide⟩,⟨1167682, by decide⟩,⟨1167715, by decide⟩,⟨1167727, by decide⟩]) unmarked_context_9_5291_1167728 node_context_9_5291_1167728
  intro a
  fin_cases a
  · exact context_10_21164_1167622
  · exact context_10_21165_1167682
  · exact context_10_21166_1167715
  · exact context_10_21167_1167727

theorem unmarked_context_8_1322_1167729 : frontier 13 ⟨1167729, by decide⟩
    (prefixCache 8 1322) (prefixPartial 8 1322) = false := by
  decide +kernel

theorem node_context_8_1322_1167729 : EJMOriginalGlobalDAGData.nodes 13 ⟨1167729, by decide⟩ =
    .split (coordinate 8) (![⟨1166066, by decide⟩,⟨1166980, by decide⟩,⟨1167522, by decide⟩,⟨1167728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1322_1167729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1322 ⟨1167729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1322
    ⟨1167729, by decide⟩ (by decide) (![⟨1166066, by decide⟩,⟨1166980, by decide⟩,⟨1167522, by decide⟩,⟨1167728, by decide⟩]) unmarked_context_8_1322_1167729 node_context_8_1322_1167729
  intro a
  fin_cases a
  · exact context_9_5288_1166066
  · exact context_9_5289_1166980
  · exact context_9_5290_1167522
  · exact context_9_5291_1167728

theorem selected_cut_42747 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84672) = some ⟨11, 1, 0, 434745, 84672, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84672_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84672 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84672 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84672, 1, 262144⟩
    (by decide) selected_cut_42747

theorem selected_cut_42748 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 338692) = some ⟨12, 1, 0, 448748, 338692, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338692_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338692 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 338692 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 338692, 1, 65536⟩
    (by decide) selected_cut_42748

theorem selected_cut_42749 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 338693) = some ⟨12, 1, 0, 34034, 338693, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338693_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338693 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 338693 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 338693, 1, 65536⟩
    (by decide) selected_cut_42749

theorem selected_cut_42750 : selected 9 ⟨1167784, by decide⟩
    (prefixPartial 12 338694) = some ⟨12, 2, 0, 1167784, 338694, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_338694_1167784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338694 ⟨1167784, by decide⟩ :=
  accepted_of_selected 12 338694 ⟨1167784, by decide⟩ ⟨12, 2, 0, 1167784, 338694, 3217, 65536⟩
    (by decide) selected_cut_42750

theorem selected_cut_42751 : selected 9 ⟨1167835, by decide⟩
    (prefixPartial 12 338695) = some ⟨12, 2, 0, 1167835, 338695, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_338695_1167835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338695 ⟨1167835, by decide⟩ :=
  accepted_of_selected 12 338695 ⟨1167835, by decide⟩ ⟨12, 2, 0, 1167835, 338695, 3161, 65536⟩
    (by decide) selected_cut_42751

theorem unmarked_context_11_84673_1167836 : frontier 10 ⟨1167836, by decide⟩
    (prefixCache 11 84673) (prefixPartial 11 84673) = false := by
  decide +kernel

theorem node_context_11_84673_1167836 : EJMOriginalGlobalDAGData.nodes 10 ⟨1167836, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1167784, by decide⟩,⟨1167835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84673_1167836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84673 ⟨1167836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84673
    ⟨1167836, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1167784, by decide⟩,⟨1167835, by decide⟩]) unmarked_context_11_84673_1167836 node_context_11_84673_1167836
  intro a
  fin_cases a
  · exact context_12_338692_448748
  · exact context_12_338693_34034
  · exact context_12_338694_1167784
  · exact context_12_338695_1167835

theorem selected_cut_42752 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 338696) = some ⟨12, 1, 0, 448748, 338696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338696_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338696 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 338696 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 338696, 1, 65536⟩
    (by decide) selected_cut_42752

theorem selected_cut_42753 : selected 9 ⟨1167888, by decide⟩
    (prefixPartial 12 338697) = some ⟨12, 2, 0, 1167888, 338697, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_338697_1167888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338697 ⟨1167888, by decide⟩ :=
  accepted_of_selected 12 338697 ⟨1167888, by decide⟩ ⟨12, 2, 0, 1167888, 338697, 3141, 65536⟩
    (by decide) selected_cut_42753

theorem selected_cut_42754 : selected 9 ⟨1167924, by decide⟩
    (prefixPartial 12 338698) = some ⟨12, 2, 0, 1167924, 338698, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_338698_1167924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338698 ⟨1167924, by decide⟩ :=
  accepted_of_selected 12 338698 ⟨1167924, by decide⟩ ⟨12, 2, 0, 1167924, 338698, 2773, 65536⟩
    (by decide) selected_cut_42754

theorem selected_cut_42755 : selected 9 ⟨1167972, by decide⟩
    (prefixPartial 12 338699) = some ⟨12, 2, 0, 1167972, 338699, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_338699_1167972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338699 ⟨1167972, by decide⟩ :=
  accepted_of_selected 12 338699 ⟨1167972, by decide⟩ ⟨12, 2, 0, 1167972, 338699, 2905, 65536⟩
    (by decide) selected_cut_42755

theorem unmarked_context_11_84674_1167973 : frontier 10 ⟨1167973, by decide⟩
    (prefixCache 11 84674) (prefixPartial 11 84674) = false := by
  decide +kernel

theorem node_context_11_84674_1167973 : EJMOriginalGlobalDAGData.nodes 10 ⟨1167973, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1167888, by decide⟩,⟨1167924, by decide⟩,⟨1167972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84674_1167973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84674 ⟨1167973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84674
    ⟨1167973, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1167888, by decide⟩,⟨1167924, by decide⟩,⟨1167972, by decide⟩]) unmarked_context_11_84674_1167973 node_context_11_84674_1167973
  intro a
  fin_cases a
  · exact context_12_338696_448748
  · exact context_12_338697_1167888
  · exact context_12_338698_1167924
  · exact context_12_338699_1167972

theorem selected_cut_42756 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 338700) = some ⟨12, 1, 0, 448748, 338700, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338700_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338700 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 338700 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 338700, 1, 65536⟩
    (by decide) selected_cut_42756

theorem selected_cut_42757 : selected 9 ⟨1168015, by decide⟩
    (prefixPartial 12 338701) = some ⟨12, 2, 0, 1168015, 338701, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_338701_1168015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338701 ⟨1168015, by decide⟩ :=
  accepted_of_selected 12 338701 ⟨1168015, by decide⟩ ⟨12, 2, 0, 1168015, 338701, 3017, 65536⟩
    (by decide) selected_cut_42757

theorem selected_cut_42758 : selected 9 ⟨1168057, by decide⟩
    (prefixPartial 12 338702) = some ⟨12, 2, 0, 1168057, 338702, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_338702_1168057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338702 ⟨1168057, by decide⟩ :=
  accepted_of_selected 12 338702 ⟨1168057, by decide⟩ ⟨12, 2, 0, 1168057, 338702, 3021, 65536⟩
    (by decide) selected_cut_42758

theorem selected_cut_42759 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 338703) = some ⟨12, 1, 0, 903806, 338703, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338703_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338703 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 338703 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 338703, 1, 65536⟩
    (by decide) selected_cut_42759

theorem unmarked_context_11_84675_1168058 : frontier 10 ⟨1168058, by decide⟩
    (prefixCache 11 84675) (prefixPartial 11 84675) = false := by
  decide +kernel

theorem node_context_11_84675_1168058 : EJMOriginalGlobalDAGData.nodes 10 ⟨1168058, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1168015, by decide⟩,⟨1168057, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84675_1168058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84675 ⟨1168058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84675
    ⟨1168058, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1168015, by decide⟩,⟨1168057, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84675_1168058 node_context_11_84675_1168058
  intro a
  fin_cases a
  · exact context_12_338700_448748
  · exact context_12_338701_1168015
  · exact context_12_338702_1168057
  · exact context_12_338703_903806

theorem unmarked_context_10_21168_1168059 : frontier 11 ⟨1168059, by decide⟩
    (prefixCache 10 21168) (prefixPartial 10 21168) = false := by
  decide +kernel

theorem node_context_10_21168_1168059 : EJMOriginalGlobalDAGData.nodes 11 ⟨1168059, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1167836, by decide⟩,⟨1167973, by decide⟩,⟨1168058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21168_1168059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21168 ⟨1168059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21168
    ⟨1168059, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1167836, by decide⟩,⟨1167973, by decide⟩,⟨1168058, by decide⟩]) unmarked_context_10_21168_1168059 node_context_10_21168_1168059
  intro a
  fin_cases a
  · exact context_11_84672_434745
  · exact context_11_84673_1167836
  · exact context_11_84674_1167973
  · exact context_11_84675_1168058

theorem selected_cut_42760 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338704) = some ⟨12, 1, 0, 1108174, 338704, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338704_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338704 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338704 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338704, 1, 65536⟩
    (by decide) selected_cut_42760

theorem selected_cut_42761 : selected 9 ⟨1168123, by decide⟩
    (prefixPartial 12 338705) = some ⟨12, 2, 0, 1168123, 338705, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_338705_1168123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338705 ⟨1168123, by decide⟩ :=
  accepted_of_selected 12 338705 ⟨1168123, by decide⟩ ⟨12, 2, 0, 1168123, 338705, 3749, 65536⟩
    (by decide) selected_cut_42761

theorem selected_cut_42762 : selected 9 ⟨1168198, by decide⟩
    (prefixPartial 12 338706) = some ⟨12, 2, 0, 1168198, 338706, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_338706_1168198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338706 ⟨1168198, by decide⟩ :=
  accepted_of_selected 12 338706 ⟨1168198, by decide⟩ ⟨12, 2, 0, 1168198, 338706, 3933, 65536⟩
    (by decide) selected_cut_42762

theorem selected_cut_42763 : selected 9 ⟨1168268, by decide⟩
    (prefixPartial 12 338707) = some ⟨12, 2, 0, 1168268, 338707, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_338707_1168268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338707 ⟨1168268, by decide⟩ :=
  accepted_of_selected 12 338707 ⟨1168268, by decide⟩ ⟨12, 2, 0, 1168268, 338707, 3821, 65536⟩
    (by decide) selected_cut_42763

theorem unmarked_context_11_84676_1168269 : frontier 10 ⟨1168269, by decide⟩
    (prefixCache 11 84676) (prefixPartial 11 84676) = false := by
  decide +kernel

theorem node_context_11_84676_1168269 : EJMOriginalGlobalDAGData.nodes 10 ⟨1168269, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1168123, by decide⟩,⟨1168198, by decide⟩,⟨1168268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84676_1168269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84676 ⟨1168269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84676
    ⟨1168269, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1168123, by decide⟩,⟨1168198, by decide⟩,⟨1168268, by decide⟩]) unmarked_context_11_84676_1168269 node_context_11_84676_1168269
  intro a
  fin_cases a
  · exact context_12_338704_1108174
  · exact context_12_338705_1168123
  · exact context_12_338706_1168198
  · exact context_12_338707_1168268

theorem selected_cut_42764 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338708) = some ⟨12, 1, 0, 1108174, 338708, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338708_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338708 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338708 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338708, 1, 65536⟩
    (by decide) selected_cut_42764

theorem selected_cut_42765 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 338709) = some ⟨12, 1, 0, 1118965, 338709, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338709_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338709 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 338709 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 338709, 1, 65536⟩
    (by decide) selected_cut_42765

theorem selected_cut_42766 : selected 9 ⟨1168327, by decide⟩
    (prefixPartial 12 338710) = some ⟨12, 2, 0, 1168327, 338710, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_338710_1168327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338710 ⟨1168327, by decide⟩ :=
  accepted_of_selected 12 338710 ⟨1168327, by decide⟩ ⟨12, 2, 0, 1168327, 338710, 3453, 65536⟩
    (by decide) selected_cut_42766

theorem selected_cut_42767 : selected 9 ⟨1168392, by decide⟩
    (prefixPartial 12 338711) = some ⟨12, 2, 0, 1168392, 338711, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_338711_1168392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338711 ⟨1168392, by decide⟩ :=
  accepted_of_selected 12 338711 ⟨1168392, by decide⟩ ⟨12, 2, 0, 1168392, 338711, 3537, 65536⟩
    (by decide) selected_cut_42767

theorem unmarked_context_11_84677_1168393 : frontier 10 ⟨1168393, by decide⟩
    (prefixCache 11 84677) (prefixPartial 11 84677) = false := by
  decide +kernel

theorem node_context_11_84677_1168393 : EJMOriginalGlobalDAGData.nodes 10 ⟨1168393, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1118965, by decide⟩,⟨1168327, by decide⟩,⟨1168392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84677_1168393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84677 ⟨1168393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84677
    ⟨1168393, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1118965, by decide⟩,⟨1168327, by decide⟩,⟨1168392, by decide⟩]) unmarked_context_11_84677_1168393 node_context_11_84677_1168393
  intro a
  fin_cases a
  · exact context_12_338708_1108174
  · exact context_12_338709_1118965
  · exact context_12_338710_1168327
  · exact context_12_338711_1168392

theorem selected_cut_42768 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338712) = some ⟨12, 1, 0, 1108174, 338712, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338712_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338712 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338712 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338712, 1, 65536⟩
    (by decide) selected_cut_42768

theorem selected_cut_42769 : selected 9 ⟨1168437, by decide⟩
    (prefixPartial 12 338713) = some ⟨12, 2, 0, 1168437, 338713, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_338713_1168437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338713 ⟨1168437, by decide⟩ :=
  accepted_of_selected 12 338713 ⟨1168437, by decide⟩ ⟨12, 2, 0, 1168437, 338713, 2961, 65536⟩
    (by decide) selected_cut_42769

theorem selected_cut_42770 : selected 9 ⟨1168482, by decide⟩
    (prefixPartial 12 338714) = some ⟨12, 2, 0, 1168482, 338714, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_338714_1168482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338714 ⟨1168482, by decide⟩ :=
  accepted_of_selected 12 338714 ⟨1168482, by decide⟩ ⟨12, 2, 0, 1168482, 338714, 2793, 65536⟩
    (by decide) selected_cut_42770

theorem selected_cut_42771 : selected 9 ⟨1168536, by decide⟩
    (prefixPartial 12 338715) = some ⟨12, 2, 0, 1168536, 338715, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_338715_1168536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338715 ⟨1168536, by decide⟩ :=
  accepted_of_selected 12 338715 ⟨1168536, by decide⟩ ⟨12, 2, 0, 1168536, 338715, 2945, 65536⟩
    (by decide) selected_cut_42771

theorem unmarked_context_11_84678_1168537 : frontier 10 ⟨1168537, by decide⟩
    (prefixCache 11 84678) (prefixPartial 11 84678) = false := by
  decide +kernel

theorem node_context_11_84678_1168537 : EJMOriginalGlobalDAGData.nodes 10 ⟨1168537, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1168437, by decide⟩,⟨1168482, by decide⟩,⟨1168536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84678_1168537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84678 ⟨1168537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84678
    ⟨1168537, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1168437, by decide⟩,⟨1168482, by decide⟩,⟨1168536, by decide⟩]) unmarked_context_11_84678_1168537 node_context_11_84678_1168537
  intro a
  fin_cases a
  · exact context_12_338712_1108174
  · exact context_12_338713_1168437
  · exact context_12_338714_1168482
  · exact context_12_338715_1168536

theorem selected_cut_42772 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338716) = some ⟨12, 1, 0, 1108174, 338716, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338716_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338716 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338716 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338716, 1, 65536⟩
    (by decide) selected_cut_42772

theorem selected_cut_42773 : selected 9 ⟨1168576, by decide⟩
    (prefixPartial 12 338717) = some ⟨12, 2, 0, 1168576, 338717, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_338717_1168576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338717 ⟨1168576, by decide⟩ :=
  accepted_of_selected 12 338717 ⟨1168576, by decide⟩ ⟨12, 2, 0, 1168576, 338717, 2793, 65536⟩
    (by decide) selected_cut_42773

theorem selected_cut_42774 : selected 9 ⟨1168618, by decide⟩
    (prefixPartial 12 338718) = some ⟨12, 2, 0, 1168618, 338718, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_338718_1168618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338718 ⟨1168618, by decide⟩ :=
  accepted_of_selected 12 338718 ⟨1168618, by decide⟩ ⟨12, 2, 0, 1168618, 338718, 3053, 65536⟩
    (by decide) selected_cut_42774

theorem selected_cut_42775 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 338719) = some ⟨12, 1, 0, 903806, 338719, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338719_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338719 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 338719 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 338719, 1, 65536⟩
    (by decide) selected_cut_42775

theorem unmarked_context_11_84679_1168619 : frontier 10 ⟨1168619, by decide⟩
    (prefixCache 11 84679) (prefixPartial 11 84679) = false := by
  decide +kernel

theorem node_context_11_84679_1168619 : EJMOriginalGlobalDAGData.nodes 10 ⟨1168619, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1168576, by decide⟩,⟨1168618, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84679_1168619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84679 ⟨1168619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84679
    ⟨1168619, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1168576, by decide⟩,⟨1168618, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84679_1168619 node_context_11_84679_1168619
  intro a
  fin_cases a
  · exact context_12_338716_1108174
  · exact context_12_338717_1168576
  · exact context_12_338718_1168618
  · exact context_12_338719_903806

theorem unmarked_context_10_21169_1168620 : frontier 11 ⟨1168620, by decide⟩
    (prefixCache 10 21169) (prefixPartial 10 21169) = false := by
  decide +kernel

theorem node_context_10_21169_1168620 : EJMOriginalGlobalDAGData.nodes 11 ⟨1168620, by decide⟩ =
    .split (coordinate 10) (![⟨1168269, by decide⟩,⟨1168393, by decide⟩,⟨1168537, by decide⟩,⟨1168619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21169_1168620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21169 ⟨1168620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21169
    ⟨1168620, by decide⟩ (by decide) (![⟨1168269, by decide⟩,⟨1168393, by decide⟩,⟨1168537, by decide⟩,⟨1168619, by decide⟩]) unmarked_context_10_21169_1168620 node_context_10_21169_1168620
  intro a
  fin_cases a
  · exact context_11_84676_1168269
  · exact context_11_84677_1168393
  · exact context_11_84678_1168537
  · exact context_11_84679_1168619

theorem selected_cut_42776 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338720) = some ⟨12, 1, 0, 1108174, 338720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338720_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338720 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338720 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338720, 1, 65536⟩
    (by decide) selected_cut_42776

theorem selected_cut_42777 : selected 9 ⟨1168672, by decide⟩
    (prefixPartial 12 338721) = some ⟨12, 2, 0, 1168672, 338721, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_338721_1168672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338721 ⟨1168672, by decide⟩ :=
  accepted_of_selected 12 338721 ⟨1168672, by decide⟩ ⟨12, 2, 0, 1168672, 338721, 2957, 65536⟩
    (by decide) selected_cut_42777

theorem selected_cut_42778 : selected 9 ⟨1168720, by decide⟩
    (prefixPartial 12 338722) = some ⟨12, 2, 0, 1168720, 338722, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_338722_1168720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338722 ⟨1168720, by decide⟩ :=
  accepted_of_selected 12 338722 ⟨1168720, by decide⟩ ⟨12, 2, 0, 1168720, 338722, 2969, 65536⟩
    (by decide) selected_cut_42778

theorem selected_cut_42779 : selected 9 ⟨1168769, by decide⟩
    (prefixPartial 12 338723) = some ⟨12, 2, 0, 1168769, 338723, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_338723_1168769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338723 ⟨1168769, by decide⟩ :=
  accepted_of_selected 12 338723 ⟨1168769, by decide⟩ ⟨12, 2, 0, 1168769, 338723, 2869, 65536⟩
    (by decide) selected_cut_42779

theorem unmarked_context_11_84680_1168770 : frontier 10 ⟨1168770, by decide⟩
    (prefixCache 11 84680) (prefixPartial 11 84680) = false := by
  decide +kernel

theorem node_context_11_84680_1168770 : EJMOriginalGlobalDAGData.nodes 10 ⟨1168770, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1168672, by decide⟩,⟨1168720, by decide⟩,⟨1168769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84680_1168770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84680 ⟨1168770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84680
    ⟨1168770, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1168672, by decide⟩,⟨1168720, by decide⟩,⟨1168769, by decide⟩]) unmarked_context_11_84680_1168770 node_context_11_84680_1168770
  intro a
  fin_cases a
  · exact context_12_338720_1108174
  · exact context_12_338721_1168672
  · exact context_12_338722_1168720
  · exact context_12_338723_1168769

theorem selected_cut_42780 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338724) = some ⟨12, 1, 0, 1108174, 338724, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338724_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338724 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338724 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338724, 1, 65536⟩
    (by decide) selected_cut_42780

theorem selected_cut_42781 : selected 9 ⟨1168814, by decide⟩
    (prefixPartial 12 338725) = some ⟨12, 2, 0, 1168814, 338725, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_338725_1168814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338725 ⟨1168814, by decide⟩ :=
  accepted_of_selected 12 338725 ⟨1168814, by decide⟩ ⟨12, 2, 0, 1168814, 338725, 2785, 65536⟩
    (by decide) selected_cut_42781

theorem selected_cut_42782 : selected 9 ⟨1168850, by decide⟩
    (prefixPartial 12 338726) = some ⟨12, 2, 0, 1168850, 338726, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_338726_1168850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338726 ⟨1168850, by decide⟩ :=
  accepted_of_selected 12 338726 ⟨1168850, by decide⟩ ⟨12, 2, 0, 1168850, 338726, 2637, 65536⟩
    (by decide) selected_cut_42782

theorem selected_cut_42783 : selected 9 ⟨1168898, by decide⟩
    (prefixPartial 12 338727) = some ⟨12, 2, 0, 1168898, 338727, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_338727_1168898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338727 ⟨1168898, by decide⟩ :=
  accepted_of_selected 12 338727 ⟨1168898, by decide⟩ ⟨12, 2, 0, 1168898, 338727, 2745, 65536⟩
    (by decide) selected_cut_42783

theorem unmarked_context_11_84681_1168899 : frontier 10 ⟨1168899, by decide⟩
    (prefixCache 11 84681) (prefixPartial 11 84681) = false := by
  decide +kernel

theorem node_context_11_84681_1168899 : EJMOriginalGlobalDAGData.nodes 10 ⟨1168899, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1168814, by decide⟩,⟨1168850, by decide⟩,⟨1168898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84681_1168899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84681 ⟨1168899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84681
    ⟨1168899, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1168814, by decide⟩,⟨1168850, by decide⟩,⟨1168898, by decide⟩]) unmarked_context_11_84681_1168899 node_context_11_84681_1168899
  intro a
  fin_cases a
  · exact context_12_338724_1108174
  · exact context_12_338725_1168814
  · exact context_12_338726_1168850
  · exact context_12_338727_1168898

theorem selected_cut_42784 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 84682) = some ⟨11, 1, 0, 900587, 84682, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84682_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84682 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 84682 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 84682, 1, 262144⟩
    (by decide) selected_cut_42784

theorem selected_cut_42785 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338732) = some ⟨12, 1, 0, 1108174, 338732, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338732_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338732 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338732 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338732, 1, 65536⟩
    (by decide) selected_cut_42785

theorem selected_cut_42786 : selected 9 ⟨1168927, by decide⟩
    (prefixPartial 12 338733) = some ⟨12, 2, 0, 1168927, 338733, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_338733_1168927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338733 ⟨1168927, by decide⟩ :=
  accepted_of_selected 12 338733 ⟨1168927, by decide⟩ ⟨12, 2, 0, 1168927, 338733, 2381, 65536⟩
    (by decide) selected_cut_42786

theorem selected_cut_42787 : selected 9 ⟨1168965, by decide⟩
    (prefixPartial 12 338734) = some ⟨12, 2, 0, 1168965, 338734, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_338734_1168965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338734 ⟨1168965, by decide⟩ :=
  accepted_of_selected 12 338734 ⟨1168965, by decide⟩ ⟨12, 2, 0, 1168965, 338734, 2517, 65536⟩
    (by decide) selected_cut_42787

theorem selected_cut_42788 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 338735) = some ⟨12, 1, 0, 903806, 338735, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338735_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338735 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 338735 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 338735, 1, 65536⟩
    (by decide) selected_cut_42788

theorem unmarked_context_11_84683_1168966 : frontier 10 ⟨1168966, by decide⟩
    (prefixCache 11 84683) (prefixPartial 11 84683) = false := by
  decide +kernel

theorem node_context_11_84683_1168966 : EJMOriginalGlobalDAGData.nodes 10 ⟨1168966, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1168927, by decide⟩,⟨1168965, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84683_1168966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84683 ⟨1168966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84683
    ⟨1168966, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1168927, by decide⟩,⟨1168965, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84683_1168966 node_context_11_84683_1168966
  intro a
  fin_cases a
  · exact context_12_338732_1108174
  · exact context_12_338733_1168927
  · exact context_12_338734_1168965
  · exact context_12_338735_903806

theorem unmarked_context_10_21170_1168967 : frontier 11 ⟨1168967, by decide⟩
    (prefixCache 10 21170) (prefixPartial 10 21170) = false := by
  decide +kernel

theorem node_context_10_21170_1168967 : EJMOriginalGlobalDAGData.nodes 11 ⟨1168967, by decide⟩ =
    .split (coordinate 10) (![⟨1168770, by decide⟩,⟨1168899, by decide⟩,⟨900587, by decide⟩,⟨1168966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21170_1168967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21170 ⟨1168967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21170
    ⟨1168967, by decide⟩ (by decide) (![⟨1168770, by decide⟩,⟨1168899, by decide⟩,⟨900587, by decide⟩,⟨1168966, by decide⟩]) unmarked_context_10_21170_1168967 node_context_10_21170_1168967
  intro a
  fin_cases a
  · exact context_11_84680_1168770
  · exact context_11_84681_1168899
  · exact context_11_84682_900587
  · exact context_11_84683_1168966

theorem selected_cut_42789 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338736) = some ⟨12, 1, 0, 1108174, 338736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338736_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338736 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338736 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338736, 1, 65536⟩
    (by decide) selected_cut_42789

theorem selected_cut_42790 : selected 9 ⟨1169026, by decide⟩
    (prefixPartial 12 338737) = some ⟨12, 2, 0, 1169026, 338737, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_338737_1169026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338737 ⟨1169026, by decide⟩ :=
  accepted_of_selected 12 338737 ⟨1169026, by decide⟩ ⟨12, 2, 0, 1169026, 338737, 3321, 65536⟩
    (by decide) selected_cut_42790

theorem selected_cut_42791 : selected 9 ⟨1169091, by decide⟩
    (prefixPartial 12 338738) = some ⟨12, 2, 0, 1169091, 338738, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_338738_1169091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338738 ⟨1169091, by decide⟩ :=
  accepted_of_selected 12 338738 ⟨1169091, by decide⟩ ⟨12, 2, 0, 1169091, 338738, 3413, 65536⟩
    (by decide) selected_cut_42791

theorem selected_cut_42792 : selected 9 ⟨1169148, by decide⟩
    (prefixPartial 12 338739) = some ⟨12, 2, 0, 1169148, 338739, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_338739_1169148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338739 ⟨1169148, by decide⟩ :=
  accepted_of_selected 12 338739 ⟨1169148, by decide⟩ ⟨12, 2, 0, 1169148, 338739, 3369, 65536⟩
    (by decide) selected_cut_42792

theorem unmarked_context_11_84684_1169149 : frontier 10 ⟨1169149, by decide⟩
    (prefixCache 11 84684) (prefixPartial 11 84684) = false := by
  decide +kernel

theorem node_context_11_84684_1169149 : EJMOriginalGlobalDAGData.nodes 10 ⟨1169149, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1169026, by decide⟩,⟨1169091, by decide⟩,⟨1169148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84684_1169149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84684 ⟨1169149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84684
    ⟨1169149, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1169026, by decide⟩,⟨1169091, by decide⟩,⟨1169148, by decide⟩]) unmarked_context_11_84684_1169149 node_context_11_84684_1169149
  intro a
  fin_cases a
  · exact context_12_338736_1108174
  · exact context_12_338737_1169026
  · exact context_12_338738_1169091
  · exact context_12_338739_1169148

theorem selected_cut_42793 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338740) = some ⟨12, 1, 0, 1108174, 338740, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338740_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338740 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338740 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338740, 1, 65536⟩
    (by decide) selected_cut_42793

theorem selected_cut_42794 : selected 9 ⟨1169192, by decide⟩
    (prefixPartial 12 338741) = some ⟨12, 2, 0, 1169192, 338741, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_338741_1169192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338741 ⟨1169192, by decide⟩ :=
  accepted_of_selected 12 338741 ⟨1169192, by decide⟩ ⟨12, 2, 0, 1169192, 338741, 2889, 65536⟩
    (by decide) selected_cut_42794

theorem selected_cut_42795 : selected 9 ⟨1169235, by decide⟩
    (prefixPartial 12 338742) = some ⟨12, 2, 0, 1169235, 338742, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_338742_1169235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338742 ⟨1169235, by decide⟩ :=
  accepted_of_selected 12 338742 ⟨1169235, by decide⟩ ⟨12, 2, 0, 1169235, 338742, 2865, 65536⟩
    (by decide) selected_cut_42795

theorem selected_cut_42796 : selected 9 ⟨1169285, by decide⟩
    (prefixPartial 12 338743) = some ⟨12, 2, 0, 1169285, 338743, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_338743_1169285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338743 ⟨1169285, by decide⟩ :=
  accepted_of_selected 12 338743 ⟨1169285, by decide⟩ ⟨12, 2, 0, 1169285, 338743, 3017, 65536⟩
    (by decide) selected_cut_42796

theorem unmarked_context_11_84685_1169286 : frontier 10 ⟨1169286, by decide⟩
    (prefixCache 11 84685) (prefixPartial 11 84685) = false := by
  decide +kernel

theorem node_context_11_84685_1169286 : EJMOriginalGlobalDAGData.nodes 10 ⟨1169286, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1169192, by decide⟩,⟨1169235, by decide⟩,⟨1169285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84685_1169286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84685 ⟨1169286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84685
    ⟨1169286, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1169192, by decide⟩,⟨1169235, by decide⟩,⟨1169285, by decide⟩]) unmarked_context_11_84685_1169286 node_context_11_84685_1169286
  intro a
  fin_cases a
  · exact context_12_338740_1108174
  · exact context_12_338741_1169192
  · exact context_12_338742_1169235
  · exact context_12_338743_1169285

theorem selected_cut_42797 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338744) = some ⟨12, 1, 0, 1108174, 338744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338744_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338744 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338744 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338744, 1, 65536⟩
    (by decide) selected_cut_42797

theorem selected_cut_42798 : selected 9 ⟨1169326, by decide⟩
    (prefixPartial 12 338745) = some ⟨12, 2, 0, 1169326, 338745, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_338745_1169326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338745 ⟨1169326, by decide⟩ :=
  accepted_of_selected 12 338745 ⟨1169326, by decide⟩ ⟨12, 2, 0, 1169326, 338745, 2705, 65536⟩
    (by decide) selected_cut_42798

theorem selected_cut_42799 : selected 9 ⟨1169394, by decide⟩
    (prefixPartial 12 338746) = some ⟨12, 2, 0, 1169394, 338746, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_338746_1169394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338746 ⟨1169394, by decide⟩ :=
  accepted_of_selected 12 338746 ⟨1169394, by decide⟩ ⟨12, 2, 0, 1169394, 338746, 1289, 65536⟩
    (by decide) selected_cut_42799

theorem selected_cut_42800 : selected 9 ⟨1169434, by decide⟩
    (prefixPartial 12 338747) = some ⟨12, 2, 0, 1169434, 338747, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_338747_1169434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338747 ⟨1169434, by decide⟩ :=
  accepted_of_selected 12 338747 ⟨1169434, by decide⟩ ⟨12, 2, 0, 1169434, 338747, 2581, 65536⟩
    (by decide) selected_cut_42800

theorem unmarked_context_11_84686_1169435 : frontier 10 ⟨1169435, by decide⟩
    (prefixCache 11 84686) (prefixPartial 11 84686) = false := by
  decide +kernel

theorem node_context_11_84686_1169435 : EJMOriginalGlobalDAGData.nodes 10 ⟨1169435, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1169326, by decide⟩,⟨1169394, by decide⟩,⟨1169434, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84686_1169435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84686 ⟨1169435, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84686
    ⟨1169435, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1169326, by decide⟩,⟨1169394, by decide⟩,⟨1169434, by decide⟩]) unmarked_context_11_84686_1169435 node_context_11_84686_1169435
  intro a
  fin_cases a
  · exact context_12_338744_1108174
  · exact context_12_338745_1169326
  · exact context_12_338746_1169394
  · exact context_12_338747_1169434

theorem selected_cut_42801 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338748) = some ⟨12, 1, 0, 1108174, 338748, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338748_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338748 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338748 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338748, 1, 65536⟩
    (by decide) selected_cut_42801

theorem selected_cut_42802 : selected 9 ⟨1169476, by decide⟩
    (prefixPartial 12 338749) = some ⟨12, 2, 0, 1169476, 338749, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_338749_1169476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338749 ⟨1169476, by decide⟩ :=
  accepted_of_selected 12 338749 ⟨1169476, by decide⟩ ⟨12, 2, 0, 1169476, 338749, 2533, 65536⟩
    (by decide) selected_cut_42802

theorem selected_cut_42803 : selected 9 ⟨1169516, by decide⟩
    (prefixPartial 12 338750) = some ⟨12, 2, 0, 1169516, 338750, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_338750_1169516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338750 ⟨1169516, by decide⟩ :=
  accepted_of_selected 12 338750 ⟨1169516, by decide⟩ ⟨12, 2, 0, 1169516, 338750, 2601, 65536⟩
    (by decide) selected_cut_42803

theorem selected_cut_42804 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 338751) = some ⟨12, 1, 0, 1120582, 338751, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338751_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338751 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 338751 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 338751, 1, 65536⟩
    (by decide) selected_cut_42804

theorem unmarked_context_11_84687_1169517 : frontier 10 ⟨1169517, by decide⟩
    (prefixCache 11 84687) (prefixPartial 11 84687) = false := by
  decide +kernel

theorem node_context_11_84687_1169517 : EJMOriginalGlobalDAGData.nodes 10 ⟨1169517, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1169476, by decide⟩,⟨1169516, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84687_1169517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84687 ⟨1169517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84687
    ⟨1169517, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1169476, by decide⟩,⟨1169516, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_84687_1169517 node_context_11_84687_1169517
  intro a
  fin_cases a
  · exact context_12_338748_1108174
  · exact context_12_338749_1169476
  · exact context_12_338750_1169516
  · exact context_12_338751_1120582

theorem unmarked_context_10_21171_1169518 : frontier 11 ⟨1169518, by decide⟩
    (prefixCache 10 21171) (prefixPartial 10 21171) = false := by
  decide +kernel

theorem node_context_10_21171_1169518 : EJMOriginalGlobalDAGData.nodes 11 ⟨1169518, by decide⟩ =
    .split (coordinate 10) (![⟨1169149, by decide⟩,⟨1169286, by decide⟩,⟨1169435, by decide⟩,⟨1169517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21171_1169518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21171 ⟨1169518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21171
    ⟨1169518, by decide⟩ (by decide) (![⟨1169149, by decide⟩,⟨1169286, by decide⟩,⟨1169435, by decide⟩,⟨1169517, by decide⟩]) unmarked_context_10_21171_1169518 node_context_10_21171_1169518
  intro a
  fin_cases a
  · exact context_11_84684_1169149
  · exact context_11_84685_1169286
  · exact context_11_84686_1169435
  · exact context_11_84687_1169517

theorem unmarked_context_9_5292_1169519 : frontier 12 ⟨1169519, by decide⟩
    (prefixCache 9 5292) (prefixPartial 9 5292) = false := by
  decide +kernel

theorem node_context_9_5292_1169519 : EJMOriginalGlobalDAGData.nodes 12 ⟨1169519, by decide⟩ =
    .split (coordinate 9) (![⟨1168059, by decide⟩,⟨1168620, by decide⟩,⟨1168967, by decide⟩,⟨1169518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5292_1169519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5292 ⟨1169519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5292
    ⟨1169519, by decide⟩ (by decide) (![⟨1168059, by decide⟩,⟨1168620, by decide⟩,⟨1168967, by decide⟩,⟨1169518, by decide⟩]) unmarked_context_9_5292_1169519 node_context_9_5292_1169519
  intro a
  fin_cases a
  · exact context_10_21168_1168059
  · exact context_10_21169_1168620
  · exact context_10_21170_1168967
  · exact context_10_21171_1169518

theorem selected_cut_42805 : selected 9 ⟨1120586, by decide⟩
    (prefixPartial 12 338752) = some ⟨12, 1, 0, 1120586, 338752, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338752_1120586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338752 ⟨1120586, by decide⟩ :=
  accepted_of_selected 12 338752 ⟨1120586, by decide⟩ ⟨12, 1, 0, 1120586, 338752, 1, 65536⟩
    (by decide) selected_cut_42805

theorem selected_cut_42806 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 338753) = some ⟨12, 1, 0, 170504, 338753, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338753_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338753 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 338753 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 338753, 1, 65536⟩
    (by decide) selected_cut_42806

theorem selected_cut_42807 : selected 9 ⟨1169550, by decide⟩
    (prefixPartial 12 338754) = some ⟨12, 2, 0, 1169550, 338754, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_338754_1169550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338754 ⟨1169550, by decide⟩ :=
  accepted_of_selected 12 338754 ⟨1169550, by decide⟩ ⟨12, 2, 0, 1169550, 338754, 2233, 65536⟩
    (by decide) selected_cut_42807

theorem selected_cut_42808 : selected 9 ⟨1169595, by decide⟩
    (prefixPartial 12 338755) = some ⟨12, 2, 0, 1169595, 338755, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_338755_1169595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338755 ⟨1169595, by decide⟩ :=
  accepted_of_selected 12 338755 ⟨1169595, by decide⟩ ⟨12, 2, 0, 1169595, 338755, 2373, 65536⟩
    (by decide) selected_cut_42808

theorem unmarked_context_11_84688_1169596 : frontier 10 ⟨1169596, by decide⟩
    (prefixCache 11 84688) (prefixPartial 11 84688) = false := by
  decide +kernel

theorem node_context_11_84688_1169596 : EJMOriginalGlobalDAGData.nodes 10 ⟨1169596, by decide⟩ =
    .split (coordinate 11) (![⟨1120586, by decide⟩,⟨170504, by decide⟩,⟨1169550, by decide⟩,⟨1169595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84688_1169596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84688 ⟨1169596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84688
    ⟨1169596, by decide⟩ (by decide) (![⟨1120586, by decide⟩,⟨170504, by decide⟩,⟨1169550, by decide⟩,⟨1169595, by decide⟩]) unmarked_context_11_84688_1169596 node_context_11_84688_1169596
  intro a
  fin_cases a
  · exact context_12_338752_1120586
  · exact context_12_338753_170504
  · exact context_12_338754_1169550
  · exact context_12_338755_1169595

theorem selected_cut_42809 : selected 9 ⟨1169623, by decide⟩
    (prefixPartial 12 338756) = some ⟨12, 2, 0, 1169623, 338756, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_338756_1169623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338756 ⟨1169623, by decide⟩ :=
  accepted_of_selected 12 338756 ⟨1169623, by decide⟩ ⟨12, 2, 0, 1169623, 338756, 1853, 65536⟩
    (by decide) selected_cut_42809

theorem selected_cut_42810 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 338757) = some ⟨12, 1, 0, 170504, 338757, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338757_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338757 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 338757 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 338757, 1, 65536⟩
    (by decide) selected_cut_42810

theorem selected_cut_42811 : selected 9 ⟨1169655, by decide⟩
    (prefixPartial 12 338758) = some ⟨12, 2, 0, 1169655, 338758, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_338758_1169655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338758 ⟨1169655, by decide⟩ :=
  accepted_of_selected 12 338758 ⟨1169655, by decide⟩ ⟨12, 2, 0, 1169655, 338758, 2097, 65536⟩
    (by decide) selected_cut_42811

theorem selected_cut_42812 : selected 9 ⟨1169686, by decide⟩
    (prefixPartial 12 338759) = some ⟨12, 2, 0, 1169686, 338759, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_338759_1169686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338759 ⟨1169686, by decide⟩ :=
  accepted_of_selected 12 338759 ⟨1169686, by decide⟩ ⟨12, 2, 0, 1169686, 338759, 2245, 65536⟩
    (by decide) selected_cut_42812

theorem unmarked_context_11_84689_1169687 : frontier 10 ⟨1169687, by decide⟩
    (prefixCache 11 84689) (prefixPartial 11 84689) = false := by
  decide +kernel

theorem node_context_11_84689_1169687 : EJMOriginalGlobalDAGData.nodes 10 ⟨1169687, by decide⟩ =
    .split (coordinate 11) (![⟨1169623, by decide⟩,⟨170504, by decide⟩,⟨1169655, by decide⟩,⟨1169686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84689_1169687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84689 ⟨1169687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84689
    ⟨1169687, by decide⟩ (by decide) (![⟨1169623, by decide⟩,⟨170504, by decide⟩,⟨1169655, by decide⟩,⟨1169686, by decide⟩]) unmarked_context_11_84689_1169687 node_context_11_84689_1169687
  intro a
  fin_cases a
  · exact context_12_338756_1169623
  · exact context_12_338757_170504
  · exact context_12_338758_1169655
  · exact context_12_338759_1169686

theorem selected_cut_42813 : selected 9 ⟨1169712, by decide⟩
    (prefixPartial 12 338760) = some ⟨12, 2, 0, 1169712, 338760, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_338760_1169712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338760 ⟨1169712, by decide⟩ :=
  accepted_of_selected 12 338760 ⟨1169712, by decide⟩ ⟨12, 2, 0, 1169712, 338760, 1661, 65536⟩
    (by decide) selected_cut_42813

theorem selected_cut_42814 : selected 9 ⟨1169732, by decide⟩
    (prefixPartial 12 338761) = some ⟨12, 2, 0, 1169732, 338761, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_338761_1169732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338761 ⟨1169732, by decide⟩ :=
  accepted_of_selected 12 338761 ⟨1169732, by decide⟩ ⟨12, 2, 0, 1169732, 338761, 1797, 65536⟩
    (by decide) selected_cut_42814

theorem selected_cut_42815 : selected 9 ⟨1169755, by decide⟩
    (prefixPartial 12 338762) = some ⟨12, 2, 0, 1169755, 338762, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_338762_1169755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338762 ⟨1169755, by decide⟩ :=
  accepted_of_selected 12 338762 ⟨1169755, by decide⟩ ⟨12, 2, 0, 1169755, 338762, 1713, 65536⟩
    (by decide) selected_cut_42815

theorem selected_cut_42816 : selected 9 ⟨1169787, by decide⟩
    (prefixPartial 12 338763) = some ⟨12, 2, 0, 1169787, 338763, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_338763_1169787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338763 ⟨1169787, by decide⟩ :=
  accepted_of_selected 12 338763 ⟨1169787, by decide⟩ ⟨12, 2, 0, 1169787, 338763, 1877, 65536⟩
    (by decide) selected_cut_42816

theorem unmarked_context_11_84690_1169788 : frontier 10 ⟨1169788, by decide⟩
    (prefixCache 11 84690) (prefixPartial 11 84690) = false := by
  decide +kernel

theorem node_context_11_84690_1169788 : EJMOriginalGlobalDAGData.nodes 10 ⟨1169788, by decide⟩ =
    .split (coordinate 11) (![⟨1169712, by decide⟩,⟨1169732, by decide⟩,⟨1169755, by decide⟩,⟨1169787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84690_1169788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84690 ⟨1169788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84690
    ⟨1169788, by decide⟩ (by decide) (![⟨1169712, by decide⟩,⟨1169732, by decide⟩,⟨1169755, by decide⟩,⟨1169787, by decide⟩]) unmarked_context_11_84690_1169788 node_context_11_84690_1169788
  intro a
  fin_cases a
  · exact context_12_338760_1169712
  · exact context_12_338761_1169732
  · exact context_12_338762_1169755
  · exact context_12_338763_1169787

theorem selected_cut_42817 : selected 10 ⟨1169839, by decide⟩
    (prefixPartial 11 84691) = some ⟨11, 2, 0, 1169839, 84691, 4021, 262144⟩ := by
  decide +kernel

theorem context_11_84691_1169839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84691 ⟨1169839, by decide⟩ :=
  accepted_of_selected 11 84691 ⟨1169839, by decide⟩ ⟨11, 2, 0, 1169839, 84691, 4021, 262144⟩
    (by decide) selected_cut_42817

theorem unmarked_context_10_21172_1169840 : frontier 11 ⟨1169840, by decide⟩
    (prefixCache 10 21172) (prefixPartial 10 21172) = false := by
  decide +kernel

theorem node_context_10_21172_1169840 : EJMOriginalGlobalDAGData.nodes 11 ⟨1169840, by decide⟩ =
    .split (coordinate 10) (![⟨1169596, by decide⟩,⟨1169687, by decide⟩,⟨1169788, by decide⟩,⟨1169839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21172_1169840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21172 ⟨1169840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21172
    ⟨1169840, by decide⟩ (by decide) (![⟨1169596, by decide⟩,⟨1169687, by decide⟩,⟨1169788, by decide⟩,⟨1169839, by decide⟩]) unmarked_context_10_21172_1169840 node_context_10_21172_1169840
  intro a
  fin_cases a
  · exact context_11_84688_1169596
  · exact context_11_84689_1169687
  · exact context_11_84690_1169788
  · exact context_11_84691_1169839

theorem selected_cut_42818 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21173) = some ⟨10, 1, 0, 893098, 21173, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21173_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21173 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21173 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21173, 1, 1048576⟩
    (by decide) selected_cut_42818

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
