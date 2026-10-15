/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover261
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_25156 : selected 8 ⟨635539, by decide⟩
    (prefixPartial 13 310573) = some ⟨13, 2, 0, 635539, 310573, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_310573_635539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310573 ⟨635539, by decide⟩ :=
  accepted_of_selected 13 310573 ⟨635539, by decide⟩ ⟨13, 2, 0, 635539, 310573, 2285, 16384⟩
    (by decide) selected_cut_25156

theorem selected_cut_25157 : selected 8 ⟨635561, by decide⟩
    (prefixPartial 13 310574) = some ⟨13, 2, 0, 635561, 310574, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_310574_635561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310574 ⟨635561, by decide⟩ :=
  accepted_of_selected 13 310574 ⟨635561, by decide⟩ ⟨13, 2, 0, 635561, 310574, 1497, 16384⟩
    (by decide) selected_cut_25157

theorem selected_cut_25158 : selected 8 ⟨635573, by decide⟩
    (prefixPartial 13 310575) = some ⟨13, 2, 0, 635573, 310575, 789, 16384⟩ := by
  decide +kernel

theorem context_13_310575_635573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310575 ⟨635573, by decide⟩ :=
  accepted_of_selected 13 310575 ⟨635573, by decide⟩ ⟨13, 2, 0, 635573, 310575, 789, 16384⟩
    (by decide) selected_cut_25158

theorem unmarked_context_12_77643_635574 : frontier 9 ⟨635574, by decide⟩
    (prefixCache 12 77643) (prefixPartial 12 77643) = false := by
  decide +kernel

theorem node_context_12_77643_635574 : EJMOriginalGlobalDAGData.nodes 9 ⟨635574, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨635539, by decide⟩,⟨635561, by decide⟩,⟨635573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77643_635574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77643 ⟨635574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77643
    ⟨635574, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨635539, by decide⟩,⟨635561, by decide⟩,⟨635573, by decide⟩]) unmarked_context_12_77643_635574 node_context_12_77643_635574
  intro a
  fin_cases a
  · exact context_13_310572_3444
  · exact context_13_310573_635539
  · exact context_13_310574_635561
  · exact context_13_310575_635573

theorem unmarked_context_11_19410_635575 : frontier 10 ⟨635575, by decide⟩
    (prefixCache 11 19410) (prefixPartial 11 19410) = false := by
  decide +kernel

theorem node_context_11_19410_635575 : EJMOriginalGlobalDAGData.nodes 10 ⟨635575, by decide⟩ =
    .split (coordinate 11) (![⟨635367, by decide⟩,⟨635428, by decide⟩,⟨635495, by decide⟩,⟨635574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19410_635575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19410 ⟨635575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19410
    ⟨635575, by decide⟩ (by decide) (![⟨635367, by decide⟩,⟨635428, by decide⟩,⟨635495, by decide⟩,⟨635574, by decide⟩]) unmarked_context_11_19410_635575 node_context_11_19410_635575
  intro a
  fin_cases a
  · exact context_12_77640_635367
  · exact context_12_77641_635428
  · exact context_12_77642_635495
  · exact context_12_77643_635574

theorem selected_cut_25159 : selected 9 ⟨635626, by decide⟩
    (prefixPartial 12 77644) = some ⟨12, 2, 0, 635626, 77644, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_77644_635626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77644 ⟨635626, by decide⟩ :=
  accepted_of_selected 12 77644 ⟨635626, by decide⟩ ⟨12, 2, 0, 635626, 77644, 3137, 65536⟩
    (by decide) selected_cut_25159

theorem selected_cut_25160 : selected 9 ⟨635671, by decide⟩
    (prefixPartial 12 77645) = some ⟨12, 2, 0, 635671, 77645, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_77645_635671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77645 ⟨635671, by decide⟩ :=
  accepted_of_selected 12 77645 ⟨635671, by decide⟩ ⟨12, 2, 0, 635671, 77645, 3237, 65536⟩
    (by decide) selected_cut_25160

theorem selected_cut_25161 : selected 9 ⟨635739, by decide⟩
    (prefixPartial 12 77646) = some ⟨12, 2, 0, 635739, 77646, 3525, 65536⟩ := by
  decide +kernel

theorem context_12_77646_635739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77646 ⟨635739, by decide⟩ :=
  accepted_of_selected 12 77646 ⟨635739, by decide⟩ ⟨12, 2, 0, 635739, 77646, 3525, 65536⟩
    (by decide) selected_cut_25161

theorem selected_cut_25162 : selected 9 ⟨635740, by decide⟩
    (prefixPartial 12 77647) = some ⟨12, 1, 0, 635740, 77647, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77647_635740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77647 ⟨635740, by decide⟩ :=
  accepted_of_selected 12 77647 ⟨635740, by decide⟩ ⟨12, 1, 0, 635740, 77647, 1, 65536⟩
    (by decide) selected_cut_25162

theorem unmarked_context_11_19411_635741 : frontier 10 ⟨635741, by decide⟩
    (prefixCache 11 19411) (prefixPartial 11 19411) = false := by
  decide +kernel

theorem node_context_11_19411_635741 : EJMOriginalGlobalDAGData.nodes 10 ⟨635741, by decide⟩ =
    .split (coordinate 11) (![⟨635626, by decide⟩,⟨635671, by decide⟩,⟨635739, by decide⟩,⟨635740, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19411_635741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19411 ⟨635741, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19411
    ⟨635741, by decide⟩ (by decide) (![⟨635626, by decide⟩,⟨635671, by decide⟩,⟨635739, by decide⟩,⟨635740, by decide⟩]) unmarked_context_11_19411_635741 node_context_11_19411_635741
  intro a
  fin_cases a
  · exact context_12_77644_635626
  · exact context_12_77645_635671
  · exact context_12_77646_635739
  · exact context_12_77647_635740

theorem unmarked_context_10_4852_635742 : frontier 11 ⟨635742, by decide⟩
    (prefixCache 10 4852) (prefixPartial 10 4852) = false := by
  decide +kernel

theorem node_context_10_4852_635742 : EJMOriginalGlobalDAGData.nodes 11 ⟨635742, by decide⟩ =
    .split (coordinate 10) (![⟨635027, by decide⟩,⟨635302, by decide⟩,⟨635575, by decide⟩,⟨635741, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4852_635742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4852 ⟨635742, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4852
    ⟨635742, by decide⟩ (by decide) (![⟨635027, by decide⟩,⟨635302, by decide⟩,⟨635575, by decide⟩,⟨635741, by decide⟩]) unmarked_context_10_4852_635742 node_context_10_4852_635742
  intro a
  fin_cases a
  · exact context_11_19408_635027
  · exact context_11_19409_635302
  · exact context_11_19410_635575
  · exact context_11_19411_635741

theorem selected_cut_25163 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310592) = some ⟨13, 1, 0, 3444, 310592, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310592_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310592 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310592 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310592, 1, 16384⟩
    (by decide) selected_cut_25163

theorem selected_cut_25164 : selected 8 ⟨635775, by decide⟩
    (prefixPartial 13 310593) = some ⟨13, 2, 0, 635775, 310593, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_310593_635775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310593 ⟨635775, by decide⟩ :=
  accepted_of_selected 13 310593 ⟨635775, by decide⟩ ⟨13, 2, 0, 635775, 310593, 1977, 16384⟩
    (by decide) selected_cut_25164

theorem selected_cut_25165 : selected 8 ⟨635794, by decide⟩
    (prefixPartial 13 310594) = some ⟨13, 2, 0, 635794, 310594, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_310594_635794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310594 ⟨635794, by decide⟩ :=
  accepted_of_selected 13 310594 ⟨635794, by decide⟩ ⟨13, 2, 0, 635794, 310594, 1641, 16384⟩
    (by decide) selected_cut_25165

theorem selected_cut_25166 : selected 8 ⟨635801, by decide⟩
    (prefixPartial 13 310595) = some ⟨13, 2, 0, 635801, 310595, 737, 16384⟩ := by
  decide +kernel

theorem context_13_310595_635801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310595 ⟨635801, by decide⟩ :=
  accepted_of_selected 13 310595 ⟨635801, by decide⟩ ⟨13, 2, 0, 635801, 310595, 737, 16384⟩
    (by decide) selected_cut_25166

theorem unmarked_context_12_77648_635802 : frontier 9 ⟨635802, by decide⟩
    (prefixCache 12 77648) (prefixPartial 12 77648) = false := by
  decide +kernel

theorem node_context_12_77648_635802 : EJMOriginalGlobalDAGData.nodes 9 ⟨635802, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨635775, by decide⟩,⟨635794, by decide⟩,⟨635801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77648_635802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77648 ⟨635802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77648
    ⟨635802, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨635775, by decide⟩,⟨635794, by decide⟩,⟨635801, by decide⟩]) unmarked_context_12_77648_635802 node_context_12_77648_635802
  intro a
  fin_cases a
  · exact context_13_310592_3444
  · exact context_13_310593_635775
  · exact context_13_310594_635794
  · exact context_13_310595_635801

theorem selected_cut_25167 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310596) = some ⟨13, 1, 0, 3444, 310596, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310596_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310596 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310596 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310596, 1, 16384⟩
    (by decide) selected_cut_25167

theorem selected_cut_25168 : selected 8 ⟨635828, by decide⟩
    (prefixPartial 13 310597) = some ⟨13, 2, 0, 635828, 310597, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_310597_635828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310597 ⟨635828, by decide⟩ :=
  accepted_of_selected 13 310597 ⟨635828, by decide⟩ ⟨13, 2, 0, 635828, 310597, 1953, 16384⟩
    (by decide) selected_cut_25168

theorem selected_cut_25169 : selected 8 ⟨635851, by decide⟩
    (prefixPartial 13 310598) = some ⟨13, 2, 0, 635851, 310598, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_310598_635851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310598 ⟨635851, by decide⟩ :=
  accepted_of_selected 13 310598 ⟨635851, by decide⟩ ⟨13, 2, 0, 635851, 310598, 1885, 16384⟩
    (by decide) selected_cut_25169

theorem selected_cut_25170 : selected 8 ⟨635856, by decide⟩
    (prefixPartial 13 310599) = some ⟨13, 2, 0, 635856, 310599, 609, 16384⟩ := by
  decide +kernel

theorem context_13_310599_635856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310599 ⟨635856, by decide⟩ :=
  accepted_of_selected 13 310599 ⟨635856, by decide⟩ ⟨13, 2, 0, 635856, 310599, 609, 16384⟩
    (by decide) selected_cut_25170

theorem unmarked_context_12_77649_635857 : frontier 9 ⟨635857, by decide⟩
    (prefixCache 12 77649) (prefixPartial 12 77649) = false := by
  decide +kernel

theorem node_context_12_77649_635857 : EJMOriginalGlobalDAGData.nodes 9 ⟨635857, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨635828, by decide⟩,⟨635851, by decide⟩,⟨635856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77649_635857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77649 ⟨635857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77649
    ⟨635857, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨635828, by decide⟩,⟨635851, by decide⟩,⟨635856, by decide⟩]) unmarked_context_12_77649_635857 node_context_12_77649_635857
  intro a
  fin_cases a
  · exact context_13_310596_3444
  · exact context_13_310597_635828
  · exact context_13_310598_635851
  · exact context_13_310599_635856

theorem selected_cut_25171 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310600) = some ⟨13, 1, 0, 3444, 310600, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310600_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310600 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310600 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310600, 1, 16384⟩
    (by decide) selected_cut_25171

theorem selected_cut_25172 : selected 8 ⟨635897, by decide⟩
    (prefixPartial 13 310601) = some ⟨13, 2, 0, 635897, 310601, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_310601_635897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310601 ⟨635897, by decide⟩ :=
  accepted_of_selected 13 310601 ⟨635897, by decide⟩ ⟨13, 2, 0, 635897, 310601, 2197, 16384⟩
    (by decide) selected_cut_25172

theorem selected_cut_25173 : selected 8 ⟨635932, by decide⟩
    (prefixPartial 13 310602) = some ⟨13, 2, 0, 635932, 310602, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_310602_635932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310602 ⟨635932, by decide⟩ :=
  accepted_of_selected 13 310602 ⟨635932, by decide⟩ ⟨13, 2, 0, 635932, 310602, 1985, 16384⟩
    (by decide) selected_cut_25173

theorem selected_cut_25174 : selected 8 ⟨635939, by decide⟩
    (prefixPartial 13 310603) = some ⟨13, 2, 0, 635939, 310603, 773, 16384⟩ := by
  decide +kernel

theorem context_13_310603_635939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310603 ⟨635939, by decide⟩ :=
  accepted_of_selected 13 310603 ⟨635939, by decide⟩ ⟨13, 2, 0, 635939, 310603, 773, 16384⟩
    (by decide) selected_cut_25174

theorem unmarked_context_12_77650_635940 : frontier 9 ⟨635940, by decide⟩
    (prefixCache 12 77650) (prefixPartial 12 77650) = false := by
  decide +kernel

theorem node_context_12_77650_635940 : EJMOriginalGlobalDAGData.nodes 9 ⟨635940, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨635897, by decide⟩,⟨635932, by decide⟩,⟨635939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77650_635940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77650 ⟨635940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77650
    ⟨635940, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨635897, by decide⟩,⟨635932, by decide⟩,⟨635939, by decide⟩]) unmarked_context_12_77650_635940 node_context_12_77650_635940
  intro a
  fin_cases a
  · exact context_13_310600_3444
  · exact context_13_310601_635897
  · exact context_13_310602_635932
  · exact context_13_310603_635939

theorem selected_cut_25175 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310604) = some ⟨13, 1, 0, 3444, 310604, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310604_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310604 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310604 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310604, 1, 16384⟩
    (by decide) selected_cut_25175

theorem selected_cut_25176 : selected 8 ⟨635967, by decide⟩
    (prefixPartial 13 310605) = some ⟨13, 2, 0, 635967, 310605, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_310605_635967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310605 ⟨635967, by decide⟩ :=
  accepted_of_selected 13 310605 ⟨635967, by decide⟩ ⟨13, 2, 0, 635967, 310605, 2053, 16384⟩
    (by decide) selected_cut_25176

theorem selected_cut_25177 : selected 8 ⟨635993, by decide⟩
    (prefixPartial 13 310606) = some ⟨13, 2, 0, 635993, 310606, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_310606_635993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310606 ⟨635993, by decide⟩ :=
  accepted_of_selected 13 310606 ⟨635993, by decide⟩ ⟨13, 2, 0, 635993, 310606, 1829, 16384⟩
    (by decide) selected_cut_25177

theorem selected_cut_25178 : selected 8 ⟨635997, by decide⟩
    (prefixPartial 13 310607) = some ⟨13, 2, 0, 635997, 310607, 685, 16384⟩ := by
  decide +kernel

theorem context_13_310607_635997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310607 ⟨635997, by decide⟩ :=
  accepted_of_selected 13 310607 ⟨635997, by decide⟩ ⟨13, 2, 0, 635997, 310607, 685, 16384⟩
    (by decide) selected_cut_25178

theorem unmarked_context_12_77651_635998 : frontier 9 ⟨635998, by decide⟩
    (prefixCache 12 77651) (prefixPartial 12 77651) = false := by
  decide +kernel

theorem node_context_12_77651_635998 : EJMOriginalGlobalDAGData.nodes 9 ⟨635998, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨635967, by decide⟩,⟨635993, by decide⟩,⟨635997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77651_635998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77651 ⟨635998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77651
    ⟨635998, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨635967, by decide⟩,⟨635993, by decide⟩,⟨635997, by decide⟩]) unmarked_context_12_77651_635998 node_context_12_77651_635998
  intro a
  fin_cases a
  · exact context_13_310604_3444
  · exact context_13_310605_635967
  · exact context_13_310606_635993
  · exact context_13_310607_635997

theorem unmarked_context_11_19412_635999 : frontier 10 ⟨635999, by decide⟩
    (prefixCache 11 19412) (prefixPartial 11 19412) = false := by
  decide +kernel

theorem node_context_11_19412_635999 : EJMOriginalGlobalDAGData.nodes 10 ⟨635999, by decide⟩ =
    .split (coordinate 11) (![⟨635802, by decide⟩,⟨635857, by decide⟩,⟨635940, by decide⟩,⟨635998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19412_635999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19412 ⟨635999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19412
    ⟨635999, by decide⟩ (by decide) (![⟨635802, by decide⟩,⟨635857, by decide⟩,⟨635940, by decide⟩,⟨635998, by decide⟩]) unmarked_context_11_19412_635999 node_context_11_19412_635999
  intro a
  fin_cases a
  · exact context_12_77648_635802
  · exact context_12_77649_635857
  · exact context_12_77650_635940
  · exact context_12_77651_635998

theorem selected_cut_25179 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310608) = some ⟨13, 1, 0, 3444, 310608, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310608_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310608 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310608 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310608, 1, 16384⟩
    (by decide) selected_cut_25179

theorem selected_cut_25180 : selected 8 ⟨636027, by decide⟩
    (prefixPartial 13 310609) = some ⟨13, 2, 0, 636027, 310609, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_310609_636027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310609 ⟨636027, by decide⟩ :=
  accepted_of_selected 13 310609 ⟨636027, by decide⟩ ⟨13, 2, 0, 636027, 310609, 1881, 16384⟩
    (by decide) selected_cut_25180

theorem selected_cut_25181 : selected 8 ⟨636047, by decide⟩
    (prefixPartial 13 310610) = some ⟨13, 2, 0, 636047, 310610, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_310610_636047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310610 ⟨636047, by decide⟩ :=
  accepted_of_selected 13 310610 ⟨636047, by decide⟩ ⟨13, 2, 0, 636047, 310610, 1809, 16384⟩
    (by decide) selected_cut_25181

theorem selected_cut_25182 : selected 8 ⟨636054, by decide⟩
    (prefixPartial 13 310611) = some ⟨13, 2, 0, 636054, 310611, 769, 16384⟩ := by
  decide +kernel

theorem context_13_310611_636054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310611 ⟨636054, by decide⟩ :=
  accepted_of_selected 13 310611 ⟨636054, by decide⟩ ⟨13, 2, 0, 636054, 310611, 769, 16384⟩
    (by decide) selected_cut_25182

theorem unmarked_context_12_77652_636055 : frontier 9 ⟨636055, by decide⟩
    (prefixCache 12 77652) (prefixPartial 12 77652) = false := by
  decide +kernel

theorem node_context_12_77652_636055 : EJMOriginalGlobalDAGData.nodes 9 ⟨636055, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨636027, by decide⟩,⟨636047, by decide⟩,⟨636054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77652_636055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77652 ⟨636055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77652
    ⟨636055, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨636027, by decide⟩,⟨636047, by decide⟩,⟨636054, by decide⟩]) unmarked_context_12_77652_636055 node_context_12_77652_636055
  intro a
  fin_cases a
  · exact context_13_310608_3444
  · exact context_13_310609_636027
  · exact context_13_310610_636047
  · exact context_13_310611_636054

theorem selected_cut_25183 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310612) = some ⟨13, 1, 0, 3444, 310612, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310612_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310612 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310612 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310612, 1, 16384⟩
    (by decide) selected_cut_25183

theorem selected_cut_25184 : selected 8 ⟨636076, by decide⟩
    (prefixPartial 13 310613) = some ⟨13, 2, 0, 636076, 310613, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_310613_636076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310613 ⟨636076, by decide⟩ :=
  accepted_of_selected 13 310613 ⟨636076, by decide⟩ ⟨13, 2, 0, 636076, 310613, 1625, 16384⟩
    (by decide) selected_cut_25184

theorem selected_cut_25185 : selected 8 ⟨636095, by decide⟩
    (prefixPartial 13 310614) = some ⟨13, 2, 0, 636095, 310614, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_310614_636095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310614 ⟨636095, by decide⟩ :=
  accepted_of_selected 13 310614 ⟨636095, by decide⟩ ⟨13, 2, 0, 636095, 310614, 1865, 16384⟩
    (by decide) selected_cut_25185

theorem selected_cut_25186 : selected 8 ⟨636103, by decide⟩
    (prefixPartial 13 310615) = some ⟨13, 2, 0, 636103, 310615, 669, 16384⟩ := by
  decide +kernel

theorem context_13_310615_636103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310615 ⟨636103, by decide⟩ :=
  accepted_of_selected 13 310615 ⟨636103, by decide⟩ ⟨13, 2, 0, 636103, 310615, 669, 16384⟩
    (by decide) selected_cut_25186

theorem unmarked_context_12_77653_636104 : frontier 9 ⟨636104, by decide⟩
    (prefixCache 12 77653) (prefixPartial 12 77653) = false := by
  decide +kernel

theorem node_context_12_77653_636104 : EJMOriginalGlobalDAGData.nodes 9 ⟨636104, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨636076, by decide⟩,⟨636095, by decide⟩,⟨636103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77653_636104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77653 ⟨636104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77653
    ⟨636104, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨636076, by decide⟩,⟨636095, by decide⟩,⟨636103, by decide⟩]) unmarked_context_12_77653_636104 node_context_12_77653_636104
  intro a
  fin_cases a
  · exact context_13_310612_3444
  · exact context_13_310613_636076
  · exact context_13_310614_636095
  · exact context_13_310615_636103

theorem selected_cut_25187 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310616) = some ⟨13, 1, 0, 3444, 310616, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310616_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310616 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310616 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310616, 1, 16384⟩
    (by decide) selected_cut_25187

theorem selected_cut_25188 : selected 8 ⟨636132, by decide⟩
    (prefixPartial 13 310617) = some ⟨13, 2, 0, 636132, 310617, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_310617_636132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310617 ⟨636132, by decide⟩ :=
  accepted_of_selected 13 310617 ⟨636132, by decide⟩ ⟨13, 2, 0, 636132, 310617, 1897, 16384⟩
    (by decide) selected_cut_25188

theorem selected_cut_25189 : selected 8 ⟨636162, by decide⟩
    (prefixPartial 13 310618) = some ⟨13, 2, 0, 636162, 310618, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_310618_636162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310618 ⟨636162, by decide⟩ :=
  accepted_of_selected 13 310618 ⟨636162, by decide⟩ ⟨13, 2, 0, 636162, 310618, 2005, 16384⟩
    (by decide) selected_cut_25189

theorem selected_cut_25190 : selected 8 ⟨636171, by decide⟩
    (prefixPartial 13 310619) = some ⟨13, 2, 0, 636171, 310619, 861, 16384⟩ := by
  decide +kernel

theorem context_13_310619_636171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310619 ⟨636171, by decide⟩ :=
  accepted_of_selected 13 310619 ⟨636171, by decide⟩ ⟨13, 2, 0, 636171, 310619, 861, 16384⟩
    (by decide) selected_cut_25190

theorem unmarked_context_12_77654_636172 : frontier 9 ⟨636172, by decide⟩
    (prefixCache 12 77654) (prefixPartial 12 77654) = false := by
  decide +kernel

theorem node_context_12_77654_636172 : EJMOriginalGlobalDAGData.nodes 9 ⟨636172, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨636132, by decide⟩,⟨636162, by decide⟩,⟨636171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77654_636172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77654 ⟨636172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77654
    ⟨636172, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨636132, by decide⟩,⟨636162, by decide⟩,⟨636171, by decide⟩]) unmarked_context_12_77654_636172 node_context_12_77654_636172
  intro a
  fin_cases a
  · exact context_13_310616_3444
  · exact context_13_310617_636132
  · exact context_13_310618_636162
  · exact context_13_310619_636171

theorem selected_cut_25191 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310620) = some ⟨13, 1, 0, 3444, 310620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310620, 1, 16384⟩
    (by decide) selected_cut_25191

theorem selected_cut_25192 : selected 8 ⟨636201, by decide⟩
    (prefixPartial 13 310621) = some ⟨13, 2, 0, 636201, 310621, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_310621_636201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310621 ⟨636201, by decide⟩ :=
  accepted_of_selected 13 310621 ⟨636201, by decide⟩ ⟨13, 2, 0, 636201, 310621, 1853, 16384⟩
    (by decide) selected_cut_25192

theorem selected_cut_25193 : selected 8 ⟨636233, by decide⟩
    (prefixPartial 13 310622) = some ⟨13, 2, 0, 636233, 310622, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_310622_636233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310622 ⟨636233, by decide⟩ :=
  accepted_of_selected 13 310622 ⟨636233, by decide⟩ ⟨13, 2, 0, 636233, 310622, 1877, 16384⟩
    (by decide) selected_cut_25193

theorem selected_cut_25194 : selected 8 ⟨636241, by decide⟩
    (prefixPartial 13 310623) = some ⟨13, 2, 0, 636241, 310623, 793, 16384⟩ := by
  decide +kernel

theorem context_13_310623_636241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310623 ⟨636241, by decide⟩ :=
  accepted_of_selected 13 310623 ⟨636241, by decide⟩ ⟨13, 2, 0, 636241, 310623, 793, 16384⟩
    (by decide) selected_cut_25194

theorem unmarked_context_12_77655_636242 : frontier 9 ⟨636242, by decide⟩
    (prefixCache 12 77655) (prefixPartial 12 77655) = false := by
  decide +kernel

theorem node_context_12_77655_636242 : EJMOriginalGlobalDAGData.nodes 9 ⟨636242, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨636201, by decide⟩,⟨636233, by decide⟩,⟨636241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77655_636242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77655 ⟨636242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77655
    ⟨636242, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨636201, by decide⟩,⟨636233, by decide⟩,⟨636241, by decide⟩]) unmarked_context_12_77655_636242 node_context_12_77655_636242
  intro a
  fin_cases a
  · exact context_13_310620_3444
  · exact context_13_310621_636201
  · exact context_13_310622_636233
  · exact context_13_310623_636241

theorem unmarked_context_11_19413_636243 : frontier 10 ⟨636243, by decide⟩
    (prefixCache 11 19413) (prefixPartial 11 19413) = false := by
  decide +kernel

theorem node_context_11_19413_636243 : EJMOriginalGlobalDAGData.nodes 10 ⟨636243, by decide⟩ =
    .split (coordinate 11) (![⟨636055, by decide⟩,⟨636104, by decide⟩,⟨636172, by decide⟩,⟨636242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19413_636243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19413 ⟨636243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19413
    ⟨636243, by decide⟩ (by decide) (![⟨636055, by decide⟩,⟨636104, by decide⟩,⟨636172, by decide⟩,⟨636242, by decide⟩]) unmarked_context_11_19413_636243 node_context_11_19413_636243
  intro a
  fin_cases a
  · exact context_12_77652_636055
  · exact context_12_77653_636104
  · exact context_12_77654_636172
  · exact context_12_77655_636242

theorem selected_cut_25195 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310624) = some ⟨13, 1, 0, 3444, 310624, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310624_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310624 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310624 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310624, 1, 16384⟩
    (by decide) selected_cut_25195

theorem selected_cut_25196 : selected 8 ⟨636272, by decide⟩
    (prefixPartial 13 310625) = some ⟨13, 2, 0, 636272, 310625, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_310625_636272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310625 ⟨636272, by decide⟩ :=
  accepted_of_selected 13 310625 ⟨636272, by decide⟩ ⟨13, 2, 0, 636272, 310625, 1637, 16384⟩
    (by decide) selected_cut_25196

theorem selected_cut_25197 : selected 8 ⟨636295, by decide⟩
    (prefixPartial 13 310626) = some ⟨13, 2, 0, 636295, 310626, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_310626_636295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310626 ⟨636295, by decide⟩ :=
  accepted_of_selected 13 310626 ⟨636295, by decide⟩ ⟨13, 2, 0, 636295, 310626, 1669, 16384⟩
    (by decide) selected_cut_25197

theorem selected_cut_25198 : selected 8 ⟨636303, by decide⟩
    (prefixPartial 13 310627) = some ⟨13, 2, 0, 636303, 310627, 813, 16384⟩ := by
  decide +kernel

theorem context_13_310627_636303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310627 ⟨636303, by decide⟩ :=
  accepted_of_selected 13 310627 ⟨636303, by decide⟩ ⟨13, 2, 0, 636303, 310627, 813, 16384⟩
    (by decide) selected_cut_25198

theorem unmarked_context_12_77656_636304 : frontier 9 ⟨636304, by decide⟩
    (prefixCache 12 77656) (prefixPartial 12 77656) = false := by
  decide +kernel

theorem node_context_12_77656_636304 : EJMOriginalGlobalDAGData.nodes 9 ⟨636304, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨636272, by decide⟩,⟨636295, by decide⟩,⟨636303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77656_636304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77656 ⟨636304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77656
    ⟨636304, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨636272, by decide⟩,⟨636295, by decide⟩,⟨636303, by decide⟩]) unmarked_context_12_77656_636304 node_context_12_77656_636304
  intro a
  fin_cases a
  · exact context_13_310624_3444
  · exact context_13_310625_636272
  · exact context_13_310626_636295
  · exact context_13_310627_636303

theorem selected_cut_25199 : selected 9 ⟨636384, by decide⟩
    (prefixPartial 12 77657) = some ⟨12, 2, 0, 636384, 77657, 4089, 65536⟩ := by
  decide +kernel

theorem context_12_77657_636384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77657 ⟨636384, by decide⟩ :=
  accepted_of_selected 12 77657 ⟨636384, by decide⟩ ⟨12, 2, 0, 636384, 77657, 4089, 65536⟩
    (by decide) selected_cut_25199

theorem selected_cut_25200 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310632) = some ⟨13, 1, 0, 3444, 310632, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310632_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310632 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310632 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310632, 1, 16384⟩
    (by decide) selected_cut_25200

theorem selected_cut_25201 : selected 8 ⟨636409, by decide⟩
    (prefixPartial 13 310633) = some ⟨13, 2, 0, 636409, 310633, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_310633_636409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310633 ⟨636409, by decide⟩ :=
  accepted_of_selected 13 310633 ⟨636409, by decide⟩ ⟨13, 2, 0, 636409, 310633, 1541, 16384⟩
    (by decide) selected_cut_25201

theorem selected_cut_25202 : selected 8 ⟨636434, by decide⟩
    (prefixPartial 13 310634) = some ⟨13, 2, 0, 636434, 310634, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_310634_636434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310634 ⟨636434, by decide⟩ :=
  accepted_of_selected 13 310634 ⟨636434, by decide⟩ ⟨13, 2, 0, 636434, 310634, 1977, 16384⟩
    (by decide) selected_cut_25202

theorem selected_cut_25203 : selected 8 ⟨636448, by decide⟩
    (prefixPartial 13 310635) = some ⟨13, 2, 0, 636448, 310635, 869, 16384⟩ := by
  decide +kernel

theorem context_13_310635_636448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310635 ⟨636448, by decide⟩ :=
  accepted_of_selected 13 310635 ⟨636448, by decide⟩ ⟨13, 2, 0, 636448, 310635, 869, 16384⟩
    (by decide) selected_cut_25203

theorem unmarked_context_12_77658_636449 : frontier 9 ⟨636449, by decide⟩
    (prefixCache 12 77658) (prefixPartial 12 77658) = false := by
  decide +kernel

theorem node_context_12_77658_636449 : EJMOriginalGlobalDAGData.nodes 9 ⟨636449, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨636409, by decide⟩,⟨636434, by decide⟩,⟨636448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77658_636449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77658 ⟨636449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77658
    ⟨636449, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨636409, by decide⟩,⟨636434, by decide⟩,⟨636448, by decide⟩]) unmarked_context_12_77658_636449 node_context_12_77658_636449
  intro a
  fin_cases a
  · exact context_13_310632_3444
  · exact context_13_310633_636409
  · exact context_13_310634_636434
  · exact context_13_310635_636448

theorem selected_cut_25204 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310636) = some ⟨13, 1, 0, 3444, 310636, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310636_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310636 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310636 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310636, 1, 16384⟩
    (by decide) selected_cut_25204

theorem selected_cut_25205 : selected 8 ⟨636473, by decide⟩
    (prefixPartial 13 310637) = some ⟨13, 2, 0, 636473, 310637, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_310637_636473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310637 ⟨636473, by decide⟩ :=
  accepted_of_selected 13 310637 ⟨636473, by decide⟩ ⟨13, 2, 0, 636473, 310637, 1537, 16384⟩
    (by decide) selected_cut_25205

theorem selected_cut_25206 : selected 8 ⟨636500, by decide⟩
    (prefixPartial 13 310638) = some ⟨13, 2, 0, 636500, 310638, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_310638_636500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310638 ⟨636500, by decide⟩ :=
  accepted_of_selected 13 310638 ⟨636500, by decide⟩ ⟨13, 2, 0, 636500, 310638, 1825, 16384⟩
    (by decide) selected_cut_25206

theorem selected_cut_25207 : selected 8 ⟨636510, by decide⟩
    (prefixPartial 13 310639) = some ⟨13, 2, 0, 636510, 310639, 789, 16384⟩ := by
  decide +kernel

theorem context_13_310639_636510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310639 ⟨636510, by decide⟩ :=
  accepted_of_selected 13 310639 ⟨636510, by decide⟩ ⟨13, 2, 0, 636510, 310639, 789, 16384⟩
    (by decide) selected_cut_25207

theorem unmarked_context_12_77659_636511 : frontier 9 ⟨636511, by decide⟩
    (prefixCache 12 77659) (prefixPartial 12 77659) = false := by
  decide +kernel

theorem node_context_12_77659_636511 : EJMOriginalGlobalDAGData.nodes 9 ⟨636511, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨636473, by decide⟩,⟨636500, by decide⟩,⟨636510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77659_636511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77659 ⟨636511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77659
    ⟨636511, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨636473, by decide⟩,⟨636500, by decide⟩,⟨636510, by decide⟩]) unmarked_context_12_77659_636511 node_context_12_77659_636511
  intro a
  fin_cases a
  · exact context_13_310636_3444
  · exact context_13_310637_636473
  · exact context_13_310638_636500
  · exact context_13_310639_636510

theorem unmarked_context_11_19414_636512 : frontier 10 ⟨636512, by decide⟩
    (prefixCache 11 19414) (prefixPartial 11 19414) = false := by
  decide +kernel

theorem node_context_11_19414_636512 : EJMOriginalGlobalDAGData.nodes 10 ⟨636512, by decide⟩ =
    .split (coordinate 11) (![⟨636304, by decide⟩,⟨636384, by decide⟩,⟨636449, by decide⟩,⟨636511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19414_636512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19414 ⟨636512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19414
    ⟨636512, by decide⟩ (by decide) (![⟨636304, by decide⟩,⟨636384, by decide⟩,⟨636449, by decide⟩,⟨636511, by decide⟩]) unmarked_context_11_19414_636512 node_context_11_19414_636512
  intro a
  fin_cases a
  · exact context_12_77656_636304
  · exact context_12_77657_636384
  · exact context_12_77658_636449
  · exact context_12_77659_636511

theorem selected_cut_25208 : selected 9 ⟨636564, by decide⟩
    (prefixPartial 12 77660) = some ⟨12, 2, 0, 636564, 77660, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_77660_636564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77660 ⟨636564, by decide⟩ :=
  accepted_of_selected 12 77660 ⟨636564, by decide⟩ ⟨12, 2, 0, 636564, 77660, 3205, 65536⟩
    (by decide) selected_cut_25208

theorem selected_cut_25209 : selected 9 ⟨636619, by decide⟩
    (prefixPartial 12 77661) = some ⟨12, 2, 0, 636619, 77661, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_77661_636619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77661 ⟨636619, by decide⟩ :=
  accepted_of_selected 12 77661 ⟨636619, by decide⟩ ⟨12, 2, 0, 636619, 77661, 3285, 65536⟩
    (by decide) selected_cut_25209

theorem selected_cut_25210 : selected 9 ⟨636669, by decide⟩
    (prefixPartial 12 77662) = some ⟨12, 2, 0, 636669, 77662, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_77662_636669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77662 ⟨636669, by decide⟩ :=
  accepted_of_selected 12 77662 ⟨636669, by decide⟩ ⟨12, 2, 0, 636669, 77662, 3509, 65536⟩
    (by decide) selected_cut_25210

theorem selected_cut_25211 : selected 9 ⟨345284, by decide⟩
    (prefixPartial 12 77663) = some ⟨12, 1, 0, 345284, 77663, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77663_345284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77663 ⟨345284, by decide⟩ :=
  accepted_of_selected 12 77663 ⟨345284, by decide⟩ ⟨12, 1, 0, 345284, 77663, 1, 65536⟩
    (by decide) selected_cut_25211

theorem unmarked_context_11_19415_636670 : frontier 10 ⟨636670, by decide⟩
    (prefixCache 11 19415) (prefixPartial 11 19415) = false := by
  decide +kernel

theorem node_context_11_19415_636670 : EJMOriginalGlobalDAGData.nodes 10 ⟨636670, by decide⟩ =
    .split (coordinate 11) (![⟨636564, by decide⟩,⟨636619, by decide⟩,⟨636669, by decide⟩,⟨345284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19415_636670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19415 ⟨636670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19415
    ⟨636670, by decide⟩ (by decide) (![⟨636564, by decide⟩,⟨636619, by decide⟩,⟨636669, by decide⟩,⟨345284, by decide⟩]) unmarked_context_11_19415_636670 node_context_11_19415_636670
  intro a
  fin_cases a
  · exact context_12_77660_636564
  · exact context_12_77661_636619
  · exact context_12_77662_636669
  · exact context_12_77663_345284

theorem unmarked_context_10_4853_636671 : frontier 11 ⟨636671, by decide⟩
    (prefixCache 10 4853) (prefixPartial 10 4853) = false := by
  decide +kernel

theorem node_context_10_4853_636671 : EJMOriginalGlobalDAGData.nodes 11 ⟨636671, by decide⟩ =
    .split (coordinate 10) (![⟨635999, by decide⟩,⟨636243, by decide⟩,⟨636512, by decide⟩,⟨636670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4853_636671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4853 ⟨636671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4853
    ⟨636671, by decide⟩ (by decide) (![⟨635999, by decide⟩,⟨636243, by decide⟩,⟨636512, by decide⟩,⟨636670, by decide⟩]) unmarked_context_10_4853_636671 node_context_10_4853_636671
  intro a
  fin_cases a
  · exact context_11_19412_635999
  · exact context_11_19413_636243
  · exact context_11_19414_636512
  · exact context_11_19415_636670

theorem selected_cut_25212 : selected 9 ⟨636730, by decide⟩
    (prefixPartial 12 77664) = some ⟨12, 2, 0, 636730, 77664, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_77664_636730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77664 ⟨636730, by decide⟩ :=
  accepted_of_selected 12 77664 ⟨636730, by decide⟩ ⟨12, 2, 0, 636730, 77664, 3577, 65536⟩
    (by decide) selected_cut_25212

theorem selected_cut_25213 : selected 9 ⟨636791, by decide⟩
    (prefixPartial 12 77665) = some ⟨12, 2, 0, 636791, 77665, 3645, 65536⟩ := by
  decide +kernel

theorem context_12_77665_636791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77665 ⟨636791, by decide⟩ :=
  accepted_of_selected 12 77665 ⟨636791, by decide⟩ ⟨12, 2, 0, 636791, 77665, 3645, 65536⟩
    (by decide) selected_cut_25213

theorem selected_cut_25214 : selected 9 ⟨636850, by decide⟩
    (prefixPartial 12 77666) = some ⟨12, 2, 0, 636850, 77666, 3937, 65536⟩ := by
  decide +kernel

theorem context_12_77666_636850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77666 ⟨636850, by decide⟩ :=
  accepted_of_selected 12 77666 ⟨636850, by decide⟩ ⟨12, 2, 0, 636850, 77666, 3937, 65536⟩
    (by decide) selected_cut_25214

theorem selected_cut_25215 : selected 9 ⟨636897, by decide⟩
    (prefixPartial 12 77667) = some ⟨12, 2, 0, 636897, 77667, 3725, 65536⟩ := by
  decide +kernel

theorem context_12_77667_636897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77667 ⟨636897, by decide⟩ :=
  accepted_of_selected 12 77667 ⟨636897, by decide⟩ ⟨12, 2, 0, 636897, 77667, 3725, 65536⟩
    (by decide) selected_cut_25215

theorem unmarked_context_11_19416_636898 : frontier 10 ⟨636898, by decide⟩
    (prefixCache 11 19416) (prefixPartial 11 19416) = false := by
  decide +kernel

theorem node_context_11_19416_636898 : EJMOriginalGlobalDAGData.nodes 10 ⟨636898, by decide⟩ =
    .split (coordinate 11) (![⟨636730, by decide⟩,⟨636791, by decide⟩,⟨636850, by decide⟩,⟨636897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19416_636898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19416 ⟨636898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19416
    ⟨636898, by decide⟩ (by decide) (![⟨636730, by decide⟩,⟨636791, by decide⟩,⟨636850, by decide⟩,⟨636897, by decide⟩]) unmarked_context_11_19416_636898 node_context_11_19416_636898
  intro a
  fin_cases a
  · exact context_12_77664_636730
  · exact context_12_77665_636791
  · exact context_12_77666_636850
  · exact context_12_77667_636897

theorem selected_cut_25216 : selected 9 ⟨636950, by decide⟩
    (prefixPartial 12 77668) = some ⟨12, 2, 0, 636950, 77668, 3849, 65536⟩ := by
  decide +kernel

theorem context_12_77668_636950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77668 ⟨636950, by decide⟩ :=
  accepted_of_selected 12 77668 ⟨636950, by decide⟩ ⟨12, 2, 0, 636950, 77668, 3849, 65536⟩
    (by decide) selected_cut_25216

theorem selected_cut_25217 : selected 9 ⟨637017, by decide⟩
    (prefixPartial 12 77669) = some ⟨12, 2, 0, 637017, 77669, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_77669_637017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77669 ⟨637017, by decide⟩ :=
  accepted_of_selected 12 77669 ⟨637017, by decide⟩ ⟨12, 2, 0, 637017, 77669, 3465, 65536⟩
    (by decide) selected_cut_25217

theorem selected_cut_25218 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310680) = some ⟨13, 1, 0, 3444, 310680, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310680_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310680 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310680 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310680, 1, 16384⟩
    (by decide) selected_cut_25218

theorem selected_cut_25219 : selected 8 ⟨637040, by decide⟩
    (prefixPartial 13 310681) = some ⟨13, 2, 0, 637040, 310681, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_310681_637040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310681 ⟨637040, by decide⟩ :=
  accepted_of_selected 13 310681 ⟨637040, by decide⟩ ⟨13, 2, 0, 637040, 310681, 1125, 16384⟩
    (by decide) selected_cut_25219

theorem selected_cut_25220 : selected 8 ⟨637072, by decide⟩
    (prefixPartial 13 310682) = some ⟨13, 2, 0, 637072, 310682, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_310682_637072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310682 ⟨637072, by decide⟩ :=
  accepted_of_selected 13 310682 ⟨637072, by decide⟩ ⟨13, 2, 0, 637072, 310682, 2037, 16384⟩
    (by decide) selected_cut_25220

theorem selected_cut_25221 : selected 8 ⟨637080, by decide⟩
    (prefixPartial 13 310683) = some ⟨13, 2, 0, 637080, 310683, 957, 16384⟩ := by
  decide +kernel

theorem context_13_310683_637080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310683 ⟨637080, by decide⟩ :=
  accepted_of_selected 13 310683 ⟨637080, by decide⟩ ⟨13, 2, 0, 637080, 310683, 957, 16384⟩
    (by decide) selected_cut_25221

theorem unmarked_context_12_77670_637081 : frontier 9 ⟨637081, by decide⟩
    (prefixCache 12 77670) (prefixPartial 12 77670) = false := by
  decide +kernel

theorem node_context_12_77670_637081 : EJMOriginalGlobalDAGData.nodes 9 ⟨637081, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨637040, by decide⟩,⟨637072, by decide⟩,⟨637080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77670_637081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77670 ⟨637081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77670
    ⟨637081, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨637040, by decide⟩,⟨637072, by decide⟩,⟨637080, by decide⟩]) unmarked_context_12_77670_637081 node_context_12_77670_637081
  intro a
  fin_cases a
  · exact context_13_310680_3444
  · exact context_13_310681_637040
  · exact context_13_310682_637072
  · exact context_13_310683_637080

theorem selected_cut_25222 : selected 9 ⟨637143, by decide⟩
    (prefixPartial 12 77671) = some ⟨12, 2, 0, 637143, 77671, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_77671_637143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77671 ⟨637143, by decide⟩ :=
  accepted_of_selected 12 77671 ⟨637143, by decide⟩ ⟨12, 2, 0, 637143, 77671, 3825, 65536⟩
    (by decide) selected_cut_25222

theorem unmarked_context_11_19417_637144 : frontier 10 ⟨637144, by decide⟩
    (prefixCache 11 19417) (prefixPartial 11 19417) = false := by
  decide +kernel

theorem node_context_11_19417_637144 : EJMOriginalGlobalDAGData.nodes 10 ⟨637144, by decide⟩ =
    .split (coordinate 11) (![⟨636950, by decide⟩,⟨637017, by decide⟩,⟨637081, by decide⟩,⟨637143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19417_637144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19417 ⟨637144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19417
    ⟨637144, by decide⟩ (by decide) (![⟨636950, by decide⟩,⟨637017, by decide⟩,⟨637081, by decide⟩,⟨637143, by decide⟩]) unmarked_context_11_19417_637144 node_context_11_19417_637144
  intro a
  fin_cases a
  · exact context_12_77668_636950
  · exact context_12_77669_637017
  · exact context_12_77670_637081
  · exact context_12_77671_637143

theorem selected_cut_25223 : selected 9 ⟨637189, by decide⟩
    (prefixPartial 12 77672) = some ⟨12, 2, 0, 637189, 77672, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_77672_637189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77672 ⟨637189, by decide⟩ :=
  accepted_of_selected 12 77672 ⟨637189, by decide⟩ ⟨12, 2, 0, 637189, 77672, 3369, 65536⟩
    (by decide) selected_cut_25223

theorem selected_cut_25224 : selected 9 ⟨637238, by decide⟩
    (prefixPartial 12 77673) = some ⟨12, 2, 0, 637238, 77673, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_77673_637238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77673 ⟨637238, by decide⟩ :=
  accepted_of_selected 12 77673 ⟨637238, by decide⟩ ⟨12, 2, 0, 637238, 77673, 3441, 65536⟩
    (by decide) selected_cut_25224

theorem selected_cut_25225 : selected 9 ⟨637281, by decide⟩
    (prefixPartial 12 77674) = some ⟨12, 2, 0, 637281, 77674, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_77674_637281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77674 ⟨637281, by decide⟩ :=
  accepted_of_selected 12 77674 ⟨637281, by decide⟩ ⟨12, 2, 0, 637281, 77674, 3573, 65536⟩
    (by decide) selected_cut_25225

theorem selected_cut_25226 : selected 9 ⟨637322, by decide⟩
    (prefixPartial 12 77675) = some ⟨12, 2, 0, 637322, 77675, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_77675_637322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77675 ⟨637322, by decide⟩ :=
  accepted_of_selected 12 77675 ⟨637322, by decide⟩ ⟨12, 2, 0, 637322, 77675, 3481, 65536⟩
    (by decide) selected_cut_25226

theorem unmarked_context_11_19418_637323 : frontier 10 ⟨637323, by decide⟩
    (prefixCache 11 19418) (prefixPartial 11 19418) = false := by
  decide +kernel

theorem node_context_11_19418_637323 : EJMOriginalGlobalDAGData.nodes 10 ⟨637323, by decide⟩ =
    .split (coordinate 11) (![⟨637189, by decide⟩,⟨637238, by decide⟩,⟨637281, by decide⟩,⟨637322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19418_637323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19418 ⟨637323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19418
    ⟨637323, by decide⟩ (by decide) (![⟨637189, by decide⟩,⟨637238, by decide⟩,⟨637281, by decide⟩,⟨637322, by decide⟩]) unmarked_context_11_19418_637323 node_context_11_19418_637323
  intro a
  fin_cases a
  · exact context_12_77672_637189
  · exact context_12_77673_637238
  · exact context_12_77674_637281
  · exact context_12_77675_637322

theorem selected_cut_25227 : selected 9 ⟨637360, by decide⟩
    (prefixPartial 12 77676) = some ⟨12, 2, 0, 637360, 77676, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_77676_637360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77676 ⟨637360, by decide⟩ :=
  accepted_of_selected 12 77676 ⟨637360, by decide⟩ ⟨12, 2, 0, 637360, 77676, 2557, 65536⟩
    (by decide) selected_cut_25227

theorem selected_cut_25228 : selected 9 ⟨637410, by decide⟩
    (prefixPartial 12 77677) = some ⟨12, 2, 0, 637410, 77677, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_77677_637410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77677 ⟨637410, by decide⟩ :=
  accepted_of_selected 12 77677 ⟨637410, by decide⟩ ⟨12, 2, 0, 637410, 77677, 2717, 65536⟩
    (by decide) selected_cut_25228

theorem selected_cut_25229 : selected 9 ⟨637453, by decide⟩
    (prefixPartial 12 77678) = some ⟨12, 2, 0, 637453, 77678, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_77678_637453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77678 ⟨637453, by decide⟩ :=
  accepted_of_selected 12 77678 ⟨637453, by decide⟩ ⟨12, 2, 0, 637453, 77678, 2945, 65536⟩
    (by decide) selected_cut_25229

theorem selected_cut_25230 : selected 9 ⟨637532, by decide⟩
    (prefixPartial 12 77679) = some ⟨12, 2, 0, 637532, 77679, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_77679_637532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77679 ⟨637532, by decide⟩ :=
  accepted_of_selected 12 77679 ⟨637532, by decide⟩ ⟨12, 2, 0, 637532, 77679, 1781, 65536⟩
    (by decide) selected_cut_25230

theorem unmarked_context_11_19419_637533 : frontier 10 ⟨637533, by decide⟩
    (prefixCache 11 19419) (prefixPartial 11 19419) = false := by
  decide +kernel

theorem node_context_11_19419_637533 : EJMOriginalGlobalDAGData.nodes 10 ⟨637533, by decide⟩ =
    .split (coordinate 11) (![⟨637360, by decide⟩,⟨637410, by decide⟩,⟨637453, by decide⟩,⟨637532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19419_637533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19419 ⟨637533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19419
    ⟨637533, by decide⟩ (by decide) (![⟨637360, by decide⟩,⟨637410, by decide⟩,⟨637453, by decide⟩,⟨637532, by decide⟩]) unmarked_context_11_19419_637533 node_context_11_19419_637533
  intro a
  fin_cases a
  · exact context_12_77676_637360
  · exact context_12_77677_637410
  · exact context_12_77678_637453
  · exact context_12_77679_637532

theorem unmarked_context_10_4854_637534 : frontier 11 ⟨637534, by decide⟩
    (prefixCache 10 4854) (prefixPartial 10 4854) = false := by
  decide +kernel

theorem node_context_10_4854_637534 : EJMOriginalGlobalDAGData.nodes 11 ⟨637534, by decide⟩ =
    .split (coordinate 10) (![⟨636898, by decide⟩,⟨637144, by decide⟩,⟨637323, by decide⟩,⟨637533, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4854_637534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4854 ⟨637534, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4854
    ⟨637534, by decide⟩ (by decide) (![⟨636898, by decide⟩,⟨637144, by decide⟩,⟨637323, by decide⟩,⟨637533, by decide⟩]) unmarked_context_10_4854_637534 node_context_10_4854_637534
  intro a
  fin_cases a
  · exact context_11_19416_636898
  · exact context_11_19417_637144
  · exact context_11_19418_637323
  · exact context_11_19419_637533

theorem selected_cut_25231 : selected 9 ⟨637590, by decide⟩
    (prefixPartial 12 77680) = some ⟨12, 2, 0, 637590, 77680, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_77680_637590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77680 ⟨637590, by decide⟩ :=
  accepted_of_selected 12 77680 ⟨637590, by decide⟩ ⟨12, 2, 0, 637590, 77680, 3201, 65536⟩
    (by decide) selected_cut_25231

theorem selected_cut_25232 : selected 9 ⟨637635, by decide⟩
    (prefixPartial 12 77681) = some ⟨12, 2, 0, 637635, 77681, 3381, 65536⟩ := by
  decide +kernel

theorem context_12_77681_637635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77681 ⟨637635, by decide⟩ :=
  accepted_of_selected 12 77681 ⟨637635, by decide⟩ ⟨12, 2, 0, 637635, 77681, 3381, 65536⟩
    (by decide) selected_cut_25232

theorem selected_cut_25233 : selected 9 ⟨637677, by decide⟩
    (prefixPartial 12 77682) = some ⟨12, 2, 0, 637677, 77682, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_77682_637677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77682 ⟨637677, by decide⟩ :=
  accepted_of_selected 12 77682 ⟨637677, by decide⟩ ⟨12, 2, 0, 637677, 77682, 3613, 65536⟩
    (by decide) selected_cut_25233

theorem selected_cut_25234 : selected 9 ⟨637714, by decide⟩
    (prefixPartial 12 77683) = some ⟨12, 2, 0, 637714, 77683, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_77683_637714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77683 ⟨637714, by decide⟩ :=
  accepted_of_selected 12 77683 ⟨637714, by decide⟩ ⟨12, 2, 0, 637714, 77683, 3029, 65536⟩
    (by decide) selected_cut_25234

theorem unmarked_context_11_19420_637715 : frontier 10 ⟨637715, by decide⟩
    (prefixCache 11 19420) (prefixPartial 11 19420) = false := by
  decide +kernel

theorem node_context_11_19420_637715 : EJMOriginalGlobalDAGData.nodes 10 ⟨637715, by decide⟩ =
    .split (coordinate 11) (![⟨637590, by decide⟩,⟨637635, by decide⟩,⟨637677, by decide⟩,⟨637714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19420_637715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19420 ⟨637715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19420
    ⟨637715, by decide⟩ (by decide) (![⟨637590, by decide⟩,⟨637635, by decide⟩,⟨637677, by decide⟩,⟨637714, by decide⟩]) unmarked_context_11_19420_637715 node_context_11_19420_637715
  intro a
  fin_cases a
  · exact context_12_77680_637590
  · exact context_12_77681_637635
  · exact context_12_77682_637677
  · exact context_12_77683_637714

theorem selected_cut_25235 : selected 9 ⟨637778, by decide⟩
    (prefixPartial 12 77684) = some ⟨12, 2, 0, 637778, 77684, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_77684_637778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77684 ⟨637778, by decide⟩ :=
  accepted_of_selected 12 77684 ⟨637778, by decide⟩ ⟨12, 2, 0, 637778, 77684, 3217, 65536⟩
    (by decide) selected_cut_25235

theorem selected_cut_25236 : selected 9 ⟨637832, by decide⟩
    (prefixPartial 12 77685) = some ⟨12, 2, 0, 637832, 77685, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_77685_637832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77685 ⟨637832, by decide⟩ :=
  accepted_of_selected 12 77685 ⟨637832, by decide⟩ ⟨12, 2, 0, 637832, 77685, 3141, 65536⟩
    (by decide) selected_cut_25236

theorem selected_cut_25237 : selected 9 ⟨637880, by decide⟩
    (prefixPartial 12 77686) = some ⟨12, 2, 0, 637880, 77686, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_77686_637880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77686 ⟨637880, by decide⟩ :=
  accepted_of_selected 12 77686 ⟨637880, by decide⟩ ⟨12, 2, 0, 637880, 77686, 3437, 65536⟩
    (by decide) selected_cut_25237

theorem selected_cut_25238 : selected 9 ⟨637913, by decide⟩
    (prefixPartial 12 77687) = some ⟨12, 2, 0, 637913, 77687, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_77687_637913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77687 ⟨637913, by decide⟩ :=
  accepted_of_selected 12 77687 ⟨637913, by decide⟩ ⟨12, 2, 0, 637913, 77687, 3009, 65536⟩
    (by decide) selected_cut_25238

theorem unmarked_context_11_19421_637914 : frontier 10 ⟨637914, by decide⟩
    (prefixCache 11 19421) (prefixPartial 11 19421) = false := by
  decide +kernel

theorem node_context_11_19421_637914 : EJMOriginalGlobalDAGData.nodes 10 ⟨637914, by decide⟩ =
    .split (coordinate 11) (![⟨637778, by decide⟩,⟨637832, by decide⟩,⟨637880, by decide⟩,⟨637913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19421_637914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19421 ⟨637914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19421
    ⟨637914, by decide⟩ (by decide) (![⟨637778, by decide⟩,⟨637832, by decide⟩,⟨637880, by decide⟩,⟨637913, by decide⟩]) unmarked_context_11_19421_637914 node_context_11_19421_637914
  intro a
  fin_cases a
  · exact context_12_77684_637778
  · exact context_12_77685_637832
  · exact context_12_77686_637880
  · exact context_12_77687_637913

theorem selected_cut_25239 : selected 9 ⟨637963, by decide⟩
    (prefixPartial 12 77688) = some ⟨12, 2, 0, 637963, 77688, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_77688_637963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77688 ⟨637963, by decide⟩ :=
  accepted_of_selected 12 77688 ⟨637963, by decide⟩ ⟨12, 2, 0, 637963, 77688, 2853, 65536⟩
    (by decide) selected_cut_25239

theorem selected_cut_25240 : selected 9 ⟨638007, by decide⟩
    (prefixPartial 12 77689) = some ⟨12, 2, 0, 638007, 77689, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_77689_638007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77689 ⟨638007, by decide⟩ :=
  accepted_of_selected 12 77689 ⟨638007, by decide⟩ ⟨12, 2, 0, 638007, 77689, 2965, 65536⟩
    (by decide) selected_cut_25240

theorem selected_cut_25241 : selected 9 ⟨638041, by decide⟩
    (prefixPartial 12 77690) = some ⟨12, 2, 0, 638041, 77690, 3153, 65536⟩ := by
  decide +kernel

theorem context_12_77690_638041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77690 ⟨638041, by decide⟩ :=
  accepted_of_selected 12 77690 ⟨638041, by decide⟩ ⟨12, 2, 0, 638041, 77690, 3153, 65536⟩
    (by decide) selected_cut_25241

theorem selected_cut_25242 : selected 9 ⟨638077, by decide⟩
    (prefixPartial 12 77691) = some ⟨12, 2, 0, 638077, 77691, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_77691_638077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77691 ⟨638077, by decide⟩ :=
  accepted_of_selected 12 77691 ⟨638077, by decide⟩ ⟨12, 2, 0, 638077, 77691, 2561, 65536⟩
    (by decide) selected_cut_25242

theorem unmarked_context_11_19422_638078 : frontier 10 ⟨638078, by decide⟩
    (prefixCache 11 19422) (prefixPartial 11 19422) = false := by
  decide +kernel

theorem node_context_11_19422_638078 : EJMOriginalGlobalDAGData.nodes 10 ⟨638078, by decide⟩ =
    .split (coordinate 11) (![⟨637963, by decide⟩,⟨638007, by decide⟩,⟨638041, by decide⟩,⟨638077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19422_638078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19422 ⟨638078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19422
    ⟨638078, by decide⟩ (by decide) (![⟨637963, by decide⟩,⟨638007, by decide⟩,⟨638041, by decide⟩,⟨638077, by decide⟩]) unmarked_context_11_19422_638078 node_context_11_19422_638078
  intro a
  fin_cases a
  · exact context_12_77688_637963
  · exact context_12_77689_638007
  · exact context_12_77690_638041
  · exact context_12_77691_638077

theorem selected_cut_25243 : selected 10 ⟨638110, by decide⟩
    (prefixPartial 11 19423) = some ⟨11, 2, 0, 638110, 19423, 1129, 262144⟩ := by
  decide +kernel

theorem context_11_19423_638110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19423 ⟨638110, by decide⟩ :=
  accepted_of_selected 11 19423 ⟨638110, by decide⟩ ⟨11, 2, 0, 638110, 19423, 1129, 262144⟩
    (by decide) selected_cut_25243

theorem unmarked_context_10_4855_638111 : frontier 11 ⟨638111, by decide⟩
    (prefixCache 10 4855) (prefixPartial 10 4855) = false := by
  decide +kernel

theorem node_context_10_4855_638111 : EJMOriginalGlobalDAGData.nodes 11 ⟨638111, by decide⟩ =
    .split (coordinate 10) (![⟨637715, by decide⟩,⟨637914, by decide⟩,⟨638078, by decide⟩,⟨638110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4855_638111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4855 ⟨638111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4855
    ⟨638111, by decide⟩ (by decide) (![⟨637715, by decide⟩,⟨637914, by decide⟩,⟨638078, by decide⟩,⟨638110, by decide⟩]) unmarked_context_10_4855_638111 node_context_10_4855_638111
  intro a
  fin_cases a
  · exact context_11_19420_637715
  · exact context_11_19421_637914
  · exact context_11_19422_638078
  · exact context_11_19423_638110

theorem unmarked_context_9_1213_638112 : frontier 12 ⟨638112, by decide⟩
    (prefixCache 9 1213) (prefixPartial 9 1213) = false := by
  decide +kernel

theorem node_context_9_1213_638112 : EJMOriginalGlobalDAGData.nodes 12 ⟨638112, by decide⟩ =
    .split (coordinate 9) (![⟨635742, by decide⟩,⟨636671, by decide⟩,⟨637534, by decide⟩,⟨638111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1213_638112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1213 ⟨638112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1213
    ⟨638112, by decide⟩ (by decide) (![⟨635742, by decide⟩,⟨636671, by decide⟩,⟨637534, by decide⟩,⟨638111, by decide⟩]) unmarked_context_9_1213_638112 node_context_9_1213_638112
  intro a
  fin_cases a
  · exact context_10_4852_635742
  · exact context_10_4853_636671
  · exact context_10_4854_637534
  · exact context_10_4855_638111

theorem selected_cut_25244 : selected 9 ⟨638148, by decide⟩
    (prefixPartial 12 77696) = some ⟨12, 2, 0, 638148, 77696, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_77696_638148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77696 ⟨638148, by decide⟩ :=
  accepted_of_selected 12 77696 ⟨638148, by decide⟩ ⟨12, 2, 0, 638148, 77696, 2321, 65536⟩
    (by decide) selected_cut_25244

theorem selected_cut_25245 : selected 9 ⟨638188, by decide⟩
    (prefixPartial 12 77697) = some ⟨12, 2, 0, 638188, 77697, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_77697_638188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77697 ⟨638188, by decide⟩ :=
  accepted_of_selected 12 77697 ⟨638188, by decide⟩ ⟨12, 2, 0, 638188, 77697, 2637, 65536⟩
    (by decide) selected_cut_25245

theorem selected_cut_25246 : selected 9 ⟨638217, by decide⟩
    (prefixPartial 12 77698) = some ⟨12, 2, 0, 638217, 77698, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_77698_638217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77698 ⟨638217, by decide⟩ :=
  accepted_of_selected 12 77698 ⟨638217, by decide⟩ ⟨12, 2, 0, 638217, 77698, 2361, 65536⟩
    (by decide) selected_cut_25246

theorem selected_cut_25247 : selected 9 ⟨638244, by decide⟩
    (prefixPartial 12 77699) = some ⟨12, 2, 0, 638244, 77699, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_77699_638244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77699 ⟨638244, by decide⟩ :=
  accepted_of_selected 12 77699 ⟨638244, by decide⟩ ⟨12, 2, 0, 638244, 77699, 2473, 65536⟩
    (by decide) selected_cut_25247

theorem unmarked_context_11_19424_638245 : frontier 10 ⟨638245, by decide⟩
    (prefixCache 11 19424) (prefixPartial 11 19424) = false := by
  decide +kernel

theorem node_context_11_19424_638245 : EJMOriginalGlobalDAGData.nodes 10 ⟨638245, by decide⟩ =
    .split (coordinate 11) (![⟨638148, by decide⟩,⟨638188, by decide⟩,⟨638217, by decide⟩,⟨638244, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19424_638245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19424 ⟨638245, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19424
    ⟨638245, by decide⟩ (by decide) (![⟨638148, by decide⟩,⟨638188, by decide⟩,⟨638217, by decide⟩,⟨638244, by decide⟩]) unmarked_context_11_19424_638245 node_context_11_19424_638245
  intro a
  fin_cases a
  · exact context_12_77696_638148
  · exact context_12_77697_638188
  · exact context_12_77698_638217
  · exact context_12_77699_638244

theorem selected_cut_25248 : selected 9 ⟨638276, by decide⟩
    (prefixPartial 12 77700) = some ⟨12, 2, 0, 638276, 77700, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_77700_638276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77700 ⟨638276, by decide⟩ :=
  accepted_of_selected 12 77700 ⟨638276, by decide⟩ ⟨12, 2, 0, 638276, 77700, 2349, 65536⟩
    (by decide) selected_cut_25248

theorem selected_cut_25249 : selected 9 ⟨638313, by decide⟩
    (prefixPartial 12 77701) = some ⟨12, 2, 0, 638313, 77701, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_77701_638313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77701 ⟨638313, by decide⟩ :=
  accepted_of_selected 12 77701 ⟨638313, by decide⟩ ⟨12, 2, 0, 638313, 77701, 2401, 65536⟩
    (by decide) selected_cut_25249

theorem selected_cut_25250 : selected 9 ⟨638337, by decide⟩
    (prefixPartial 12 77702) = some ⟨12, 2, 0, 638337, 77702, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_77702_638337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77702 ⟨638337, by decide⟩ :=
  accepted_of_selected 12 77702 ⟨638337, by decide⟩ ⟨12, 2, 0, 638337, 77702, 2293, 65536⟩
    (by decide) selected_cut_25250

theorem selected_cut_25251 : selected 9 ⟨638386, by decide⟩
    (prefixPartial 12 77703) = some ⟨12, 2, 0, 638386, 77703, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_77703_638386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77703 ⟨638386, by decide⟩ :=
  accepted_of_selected 12 77703 ⟨638386, by decide⟩ ⟨12, 2, 0, 638386, 77703, 2497, 65536⟩
    (by decide) selected_cut_25251

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
