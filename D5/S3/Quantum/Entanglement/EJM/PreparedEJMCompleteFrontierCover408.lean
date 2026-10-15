/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover407
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_39171 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 302640) = some ⟨12, 1, 0, 994572, 302640, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302640_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302640 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 302640 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 302640, 1, 65536⟩
    (by decide) selected_cut_39171

theorem selected_cut_39172 : selected 9 ⟨1061765, by decide⟩
    (prefixPartial 12 302641) = some ⟨12, 2, 0, 1061765, 302641, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_302641_1061765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302641 ⟨1061765, by decide⟩ :=
  accepted_of_selected 12 302641 ⟨1061765, by decide⟩ ⟨12, 2, 0, 1061765, 302641, 3549, 65536⟩
    (by decide) selected_cut_39172

theorem selected_cut_39173 : selected 9 ⟨1061808, by decide⟩
    (prefixPartial 12 302642) = some ⟨12, 2, 0, 1061808, 302642, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_302642_1061808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302642 ⟨1061808, by decide⟩ :=
  accepted_of_selected 12 302642 ⟨1061808, by decide⟩ ⟨12, 2, 0, 1061808, 302642, 2909, 65536⟩
    (by decide) selected_cut_39173

theorem selected_cut_39174 : selected 9 ⟨1061856, by decide⟩
    (prefixPartial 12 302643) = some ⟨12, 2, 0, 1061856, 302643, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_302643_1061856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302643 ⟨1061856, by decide⟩ :=
  accepted_of_selected 12 302643 ⟨1061856, by decide⟩ ⟨12, 2, 0, 1061856, 302643, 3313, 65536⟩
    (by decide) selected_cut_39174

theorem unmarked_context_11_75660_1061857 : frontier 10 ⟨1061857, by decide⟩
    (prefixCache 11 75660) (prefixPartial 11 75660) = false := by
  decide +kernel

theorem node_context_11_75660_1061857 : EJMOriginalGlobalDAGData.nodes 10 ⟨1061857, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1061765, by decide⟩,⟨1061808, by decide⟩,⟨1061856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75660_1061857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75660 ⟨1061857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75660
    ⟨1061857, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1061765, by decide⟩,⟨1061808, by decide⟩,⟨1061856, by decide⟩]) unmarked_context_11_75660_1061857 node_context_11_75660_1061857
  intro a
  fin_cases a
  · exact context_12_302640_994572
  · exact context_12_302641_1061765
  · exact context_12_302642_1061808
  · exact context_12_302643_1061856

theorem selected_cut_39175 : selected 9 ⟨1061918, by decide⟩
    (prefixPartial 12 302644) = some ⟨12, 2, 0, 1061918, 302644, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_302644_1061918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302644 ⟨1061918, by decide⟩ :=
  accepted_of_selected 12 302644 ⟨1061918, by decide⟩ ⟨12, 2, 0, 1061918, 302644, 3237, 65536⟩
    (by decide) selected_cut_39175

theorem selected_cut_39176 : selected 9 ⟨1061978, by decide⟩
    (prefixPartial 12 302645) = some ⟨12, 2, 0, 1061978, 302645, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_302645_1061978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302645 ⟨1061978, by decide⟩ :=
  accepted_of_selected 12 302645 ⟨1061978, by decide⟩ ⟨12, 2, 0, 1061978, 302645, 3521, 65536⟩
    (by decide) selected_cut_39176

theorem selected_cut_39177 : selected 9 ⟨1062019, by decide⟩
    (prefixPartial 12 302646) = some ⟨12, 2, 0, 1062019, 302646, 2921, 65536⟩ := by
  decide +kernel

theorem context_12_302646_1062019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302646 ⟨1062019, by decide⟩ :=
  accepted_of_selected 12 302646 ⟨1062019, by decide⟩ ⟨12, 2, 0, 1062019, 302646, 2921, 65536⟩
    (by decide) selected_cut_39177

theorem selected_cut_39178 : selected 9 ⟨1062084, by decide⟩
    (prefixPartial 12 302647) = some ⟨12, 2, 0, 1062084, 302647, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_302647_1062084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302647 ⟨1062084, by decide⟩ :=
  accepted_of_selected 12 302647 ⟨1062084, by decide⟩ ⟨12, 2, 0, 1062084, 302647, 3269, 65536⟩
    (by decide) selected_cut_39178

theorem unmarked_context_11_75661_1062085 : frontier 10 ⟨1062085, by decide⟩
    (prefixCache 11 75661) (prefixPartial 11 75661) = false := by
  decide +kernel

theorem node_context_11_75661_1062085 : EJMOriginalGlobalDAGData.nodes 10 ⟨1062085, by decide⟩ =
    .split (coordinate 11) (![⟨1061918, by decide⟩,⟨1061978, by decide⟩,⟨1062019, by decide⟩,⟨1062084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75661_1062085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75661 ⟨1062085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75661
    ⟨1062085, by decide⟩ (by decide) (![⟨1061918, by decide⟩,⟨1061978, by decide⟩,⟨1062019, by decide⟩,⟨1062084, by decide⟩]) unmarked_context_11_75661_1062085 node_context_11_75661_1062085
  intro a
  fin_cases a
  · exact context_12_302644_1061918
  · exact context_12_302645_1061978
  · exact context_12_302646_1062019
  · exact context_12_302647_1062084

theorem selected_cut_39179 : selected 9 ⟨1062119, by decide⟩
    (prefixPartial 12 302648) = some ⟨12, 2, 0, 1062119, 302648, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_302648_1062119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302648 ⟨1062119, by decide⟩ :=
  accepted_of_selected 12 302648 ⟨1062119, by decide⟩ ⟨12, 2, 0, 1062119, 302648, 2869, 65536⟩
    (by decide) selected_cut_39179

theorem selected_cut_39180 : selected 9 ⟨1062165, by decide⟩
    (prefixPartial 12 302649) = some ⟨12, 2, 0, 1062165, 302649, 3281, 65536⟩ := by
  decide +kernel

theorem context_12_302649_1062165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302649 ⟨1062165, by decide⟩ :=
  accepted_of_selected 12 302649 ⟨1062165, by decide⟩ ⟨12, 2, 0, 1062165, 302649, 3281, 65536⟩
    (by decide) selected_cut_39180

theorem selected_cut_39181 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 302650) = some ⟨12, 1, 0, 893903, 302650, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302650_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302650 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 302650 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 302650, 1, 65536⟩
    (by decide) selected_cut_39181

theorem selected_cut_39182 : selected 9 ⟨1062214, by decide⟩
    (prefixPartial 12 302651) = some ⟨12, 2, 0, 1062214, 302651, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_302651_1062214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302651 ⟨1062214, by decide⟩ :=
  accepted_of_selected 12 302651 ⟨1062214, by decide⟩ ⟨12, 2, 0, 1062214, 302651, 3185, 65536⟩
    (by decide) selected_cut_39182

theorem unmarked_context_11_75662_1062215 : frontier 10 ⟨1062215, by decide⟩
    (prefixCache 11 75662) (prefixPartial 11 75662) = false := by
  decide +kernel

theorem node_context_11_75662_1062215 : EJMOriginalGlobalDAGData.nodes 10 ⟨1062215, by decide⟩ =
    .split (coordinate 11) (![⟨1062119, by decide⟩,⟨1062165, by decide⟩,⟨893903, by decide⟩,⟨1062214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75662_1062215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75662 ⟨1062215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75662
    ⟨1062215, by decide⟩ (by decide) (![⟨1062119, by decide⟩,⟨1062165, by decide⟩,⟨893903, by decide⟩,⟨1062214, by decide⟩]) unmarked_context_11_75662_1062215 node_context_11_75662_1062215
  intro a
  fin_cases a
  · exact context_12_302648_1062119
  · exact context_12_302649_1062165
  · exact context_12_302650_893903
  · exact context_12_302651_1062214

theorem selected_cut_39183 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 75663) = some ⟨11, 1, 0, 977886, 75663, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75663_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75663 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 75663 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 75663, 1, 262144⟩
    (by decide) selected_cut_39183

theorem unmarked_context_10_18915_1062216 : frontier 11 ⟨1062216, by decide⟩
    (prefixCache 10 18915) (prefixPartial 10 18915) = false := by
  decide +kernel

theorem node_context_10_18915_1062216 : EJMOriginalGlobalDAGData.nodes 11 ⟨1062216, by decide⟩ =
    .split (coordinate 10) (![⟨1061857, by decide⟩,⟨1062085, by decide⟩,⟨1062215, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18915_1062216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18915 ⟨1062216, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18915
    ⟨1062216, by decide⟩ (by decide) (![⟨1061857, by decide⟩,⟨1062085, by decide⟩,⟨1062215, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18915_1062216 node_context_10_18915_1062216
  intro a
  fin_cases a
  · exact context_11_75660_1061857
  · exact context_11_75661_1062085
  · exact context_11_75662_1062215
  · exact context_11_75663_977886

theorem unmarked_context_9_4728_1062217 : frontier 12 ⟨1062217, by decide⟩
    (prefixCache 9 4728) (prefixPartial 9 4728) = false := by
  decide +kernel

theorem node_context_9_4728_1062217 : EJMOriginalGlobalDAGData.nodes 12 ⟨1062217, by decide⟩ =
    .split (coordinate 9) (![⟨1060003, by decide⟩,⟨1060864, by decide⟩,⟨1061705, by decide⟩,⟨1062216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4728_1062217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4728 ⟨1062217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4728
    ⟨1062217, by decide⟩ (by decide) (![⟨1060003, by decide⟩,⟨1060864, by decide⟩,⟨1061705, by decide⟩,⟨1062216, by decide⟩]) unmarked_context_9_4728_1062217 node_context_9_4728_1062217
  intro a
  fin_cases a
  · exact context_10_18912_1060003
  · exact context_10_18913_1060864
  · exact context_10_18914_1061705
  · exact context_10_18915_1062216

theorem selected_cut_39184 : selected 9 ⟨1062274, by decide⟩
    (prefixPartial 12 302656) = some ⟨12, 2, 0, 1062274, 302656, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_302656_1062274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302656 ⟨1062274, by decide⟩ :=
  accepted_of_selected 12 302656 ⟨1062274, by decide⟩ ⟨12, 2, 0, 1062274, 302656, 3257, 65536⟩
    (by decide) selected_cut_39184

theorem selected_cut_39185 : selected 9 ⟨1062336, by decide⟩
    (prefixPartial 12 302657) = some ⟨12, 2, 0, 1062336, 302657, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_302657_1062336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302657 ⟨1062336, by decide⟩ :=
  accepted_of_selected 12 302657 ⟨1062336, by decide⟩ ⟨12, 2, 0, 1062336, 302657, 3317, 65536⟩
    (by decide) selected_cut_39185

theorem selected_cut_39186 : selected 9 ⟨1062389, by decide⟩
    (prefixPartial 12 302658) = some ⟨12, 2, 0, 1062389, 302658, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_302658_1062389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302658 ⟨1062389, by decide⟩ :=
  accepted_of_selected 12 302658 ⟨1062389, by decide⟩ ⟨12, 2, 0, 1062389, 302658, 2841, 65536⟩
    (by decide) selected_cut_39186

theorem selected_cut_39187 : selected 9 ⟨1062431, by decide⟩
    (prefixPartial 12 302659) = some ⟨12, 2, 0, 1062431, 302659, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_302659_1062431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302659 ⟨1062431, by decide⟩ :=
  accepted_of_selected 12 302659 ⟨1062431, by decide⟩ ⟨12, 2, 0, 1062431, 302659, 2933, 65536⟩
    (by decide) selected_cut_39187

theorem unmarked_context_11_75664_1062432 : frontier 10 ⟨1062432, by decide⟩
    (prefixCache 11 75664) (prefixPartial 11 75664) = false := by
  decide +kernel

theorem node_context_11_75664_1062432 : EJMOriginalGlobalDAGData.nodes 10 ⟨1062432, by decide⟩ =
    .split (coordinate 11) (![⟨1062274, by decide⟩,⟨1062336, by decide⟩,⟨1062389, by decide⟩,⟨1062431, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75664_1062432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75664 ⟨1062432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75664
    ⟨1062432, by decide⟩ (by decide) (![⟨1062274, by decide⟩,⟨1062336, by decide⟩,⟨1062389, by decide⟩,⟨1062431, by decide⟩]) unmarked_context_11_75664_1062432 node_context_11_75664_1062432
  intro a
  fin_cases a
  · exact context_12_302656_1062274
  · exact context_12_302657_1062336
  · exact context_12_302658_1062389
  · exact context_12_302659_1062431

theorem selected_cut_39188 : selected 9 ⟨1062483, by decide⟩
    (prefixPartial 12 302660) = some ⟨12, 2, 0, 1062483, 302660, 3133, 65536⟩ := by
  decide +kernel

theorem context_12_302660_1062483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302660 ⟨1062483, by decide⟩ :=
  accepted_of_selected 12 302660 ⟨1062483, by decide⟩ ⟨12, 2, 0, 1062483, 302660, 3133, 65536⟩
    (by decide) selected_cut_39188

theorem selected_cut_39189 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 302661) = some ⟨12, 1, 0, 691709, 302661, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302661_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302661 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 302661 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 302661, 1, 65536⟩
    (by decide) selected_cut_39189

theorem selected_cut_39190 : selected 9 ⟨1062534, by decide⟩
    (prefixPartial 12 302662) = some ⟨12, 2, 0, 1062534, 302662, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_302662_1062534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302662 ⟨1062534, by decide⟩ :=
  accepted_of_selected 12 302662 ⟨1062534, by decide⟩ ⟨12, 2, 0, 1062534, 302662, 2885, 65536⟩
    (by decide) selected_cut_39190

theorem selected_cut_39191 : selected 9 ⟨1062584, by decide⟩
    (prefixPartial 12 302663) = some ⟨12, 2, 0, 1062584, 302663, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_302663_1062584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302663 ⟨1062584, by decide⟩ :=
  accepted_of_selected 12 302663 ⟨1062584, by decide⟩ ⟨12, 2, 0, 1062584, 302663, 2917, 65536⟩
    (by decide) selected_cut_39191

theorem unmarked_context_11_75665_1062585 : frontier 10 ⟨1062585, by decide⟩
    (prefixCache 11 75665) (prefixPartial 11 75665) = false := by
  decide +kernel

theorem node_context_11_75665_1062585 : EJMOriginalGlobalDAGData.nodes 10 ⟨1062585, by decide⟩ =
    .split (coordinate 11) (![⟨1062483, by decide⟩,⟨691709, by decide⟩,⟨1062534, by decide⟩,⟨1062584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75665_1062585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75665 ⟨1062585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75665
    ⟨1062585, by decide⟩ (by decide) (![⟨1062483, by decide⟩,⟨691709, by decide⟩,⟨1062534, by decide⟩,⟨1062584, by decide⟩]) unmarked_context_11_75665_1062585 node_context_11_75665_1062585
  intro a
  fin_cases a
  · exact context_12_302660_1062483
  · exact context_12_302661_691709
  · exact context_12_302662_1062534
  · exact context_12_302663_1062584

theorem selected_cut_39192 : selected 9 ⟨1062645, by decide⟩
    (prefixPartial 12 302664) = some ⟨12, 2, 0, 1062645, 302664, 3213, 65536⟩ := by
  decide +kernel

theorem context_12_302664_1062645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302664 ⟨1062645, by decide⟩ :=
  accepted_of_selected 12 302664 ⟨1062645, by decide⟩ ⟨12, 2, 0, 1062645, 302664, 3213, 65536⟩
    (by decide) selected_cut_39192

theorem selected_cut_39193 : selected 9 ⟨1062719, by decide⟩
    (prefixPartial 12 302665) = some ⟨12, 2, 0, 1062719, 302665, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_302665_1062719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302665 ⟨1062719, by decide⟩ :=
  accepted_of_selected 12 302665 ⟨1062719, by decide⟩ ⟨12, 2, 0, 1062719, 302665, 3397, 65536⟩
    (by decide) selected_cut_39193

theorem selected_cut_39194 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 302666) = some ⟨12, 1, 0, 893903, 302666, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302666_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302666 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 302666 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 302666, 1, 65536⟩
    (by decide) selected_cut_39194

theorem selected_cut_39195 : selected 9 ⟨1062769, by decide⟩
    (prefixPartial 12 302667) = some ⟨12, 2, 0, 1062769, 302667, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_302667_1062769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302667 ⟨1062769, by decide⟩ :=
  accepted_of_selected 12 302667 ⟨1062769, by decide⟩ ⟨12, 2, 0, 1062769, 302667, 3245, 65536⟩
    (by decide) selected_cut_39195

theorem unmarked_context_11_75666_1062770 : frontier 10 ⟨1062770, by decide⟩
    (prefixCache 11 75666) (prefixPartial 11 75666) = false := by
  decide +kernel

theorem node_context_11_75666_1062770 : EJMOriginalGlobalDAGData.nodes 10 ⟨1062770, by decide⟩ =
    .split (coordinate 11) (![⟨1062645, by decide⟩,⟨1062719, by decide⟩,⟨893903, by decide⟩,⟨1062769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75666_1062770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75666 ⟨1062770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75666
    ⟨1062770, by decide⟩ (by decide) (![⟨1062645, by decide⟩,⟨1062719, by decide⟩,⟨893903, by decide⟩,⟨1062769, by decide⟩]) unmarked_context_11_75666_1062770 node_context_11_75666_1062770
  intro a
  fin_cases a
  · exact context_12_302664_1062645
  · exact context_12_302665_1062719
  · exact context_12_302666_893903
  · exact context_12_302667_1062769

theorem selected_cut_39196 : selected 9 ⟨1062824, by decide⟩
    (prefixPartial 12 302668) = some ⟨12, 2, 0, 1062824, 302668, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_302668_1062824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302668 ⟨1062824, by decide⟩ :=
  accepted_of_selected 12 302668 ⟨1062824, by decide⟩ ⟨12, 2, 0, 1062824, 302668, 3197, 65536⟩
    (by decide) selected_cut_39196

theorem selected_cut_39197 : selected 9 ⟨1062879, by decide⟩
    (prefixPartial 12 302669) = some ⟨12, 2, 0, 1062879, 302669, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_302669_1062879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302669 ⟨1062879, by decide⟩ :=
  accepted_of_selected 12 302669 ⟨1062879, by decide⟩ ⟨12, 2, 0, 1062879, 302669, 3069, 65536⟩
    (by decide) selected_cut_39197

theorem selected_cut_39198 : selected 9 ⟨1062921, by decide⟩
    (prefixPartial 12 302670) = some ⟨12, 2, 0, 1062921, 302670, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_302670_1062921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302670 ⟨1062921, by decide⟩ :=
  accepted_of_selected 12 302670 ⟨1062921, by decide⟩ ⟨12, 2, 0, 1062921, 302670, 2897, 65536⟩
    (by decide) selected_cut_39198

theorem selected_cut_39199 : selected 9 ⟨1062957, by decide⟩
    (prefixPartial 12 302671) = some ⟨12, 2, 0, 1062957, 302671, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_302671_1062957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302671 ⟨1062957, by decide⟩ :=
  accepted_of_selected 12 302671 ⟨1062957, by decide⟩ ⟨12, 2, 0, 1062957, 302671, 2645, 65536⟩
    (by decide) selected_cut_39199

theorem unmarked_context_11_75667_1062958 : frontier 10 ⟨1062958, by decide⟩
    (prefixCache 11 75667) (prefixPartial 11 75667) = false := by
  decide +kernel

theorem node_context_11_75667_1062958 : EJMOriginalGlobalDAGData.nodes 10 ⟨1062958, by decide⟩ =
    .split (coordinate 11) (![⟨1062824, by decide⟩,⟨1062879, by decide⟩,⟨1062921, by decide⟩,⟨1062957, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75667_1062958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75667 ⟨1062958, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75667
    ⟨1062958, by decide⟩ (by decide) (![⟨1062824, by decide⟩,⟨1062879, by decide⟩,⟨1062921, by decide⟩,⟨1062957, by decide⟩]) unmarked_context_11_75667_1062958 node_context_11_75667_1062958
  intro a
  fin_cases a
  · exact context_12_302668_1062824
  · exact context_12_302669_1062879
  · exact context_12_302670_1062921
  · exact context_12_302671_1062957

theorem unmarked_context_10_18916_1062959 : frontier 11 ⟨1062959, by decide⟩
    (prefixCache 10 18916) (prefixPartial 10 18916) = false := by
  decide +kernel

theorem node_context_10_18916_1062959 : EJMOriginalGlobalDAGData.nodes 11 ⟨1062959, by decide⟩ =
    .split (coordinate 10) (![⟨1062432, by decide⟩,⟨1062585, by decide⟩,⟨1062770, by decide⟩,⟨1062958, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18916_1062959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18916 ⟨1062959, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18916
    ⟨1062959, by decide⟩ (by decide) (![⟨1062432, by decide⟩,⟨1062585, by decide⟩,⟨1062770, by decide⟩,⟨1062958, by decide⟩]) unmarked_context_10_18916_1062959 node_context_10_18916_1062959
  intro a
  fin_cases a
  · exact context_11_75664_1062432
  · exact context_11_75665_1062585
  · exact context_11_75666_1062770
  · exact context_11_75667_1062958

theorem selected_cut_39200 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18917) = some ⟨10, 1, 0, 893098, 18917, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18917_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18917 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18917 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18917, 1, 1048576⟩
    (by decide) selected_cut_39200

theorem selected_cut_39201 : selected 9 ⟨1062986, by decide⟩
    (prefixPartial 12 302688) = some ⟨12, 2, 0, 1062986, 302688, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_302688_1062986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302688 ⟨1062986, by decide⟩ :=
  accepted_of_selected 12 302688 ⟨1062986, by decide⟩ ⟨12, 2, 0, 1062986, 302688, 2173, 65536⟩
    (by decide) selected_cut_39201

theorem selected_cut_39202 : selected 9 ⟨1063034, by decide⟩
    (prefixPartial 12 302689) = some ⟨12, 2, 0, 1063034, 302689, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_302689_1063034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302689 ⟨1063034, by decide⟩ :=
  accepted_of_selected 12 302689 ⟨1063034, by decide⟩ ⟨12, 2, 0, 1063034, 302689, 2601, 65536⟩
    (by decide) selected_cut_39202

theorem selected_cut_39203 : selected 9 ⟨1063061, by decide⟩
    (prefixPartial 12 302690) = some ⟨12, 2, 0, 1063061, 302690, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_302690_1063061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302690 ⟨1063061, by decide⟩ :=
  accepted_of_selected 12 302690 ⟨1063061, by decide⟩ ⟨12, 2, 0, 1063061, 302690, 1937, 65536⟩
    (by decide) selected_cut_39203

theorem selected_cut_39204 : selected 9 ⟨1063091, by decide⟩
    (prefixPartial 12 302691) = some ⟨12, 2, 0, 1063091, 302691, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_302691_1063091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302691 ⟨1063091, by decide⟩ :=
  accepted_of_selected 12 302691 ⟨1063091, by decide⟩ ⟨12, 2, 0, 1063091, 302691, 2201, 65536⟩
    (by decide) selected_cut_39204

theorem unmarked_context_11_75672_1063092 : frontier 10 ⟨1063092, by decide⟩
    (prefixCache 11 75672) (prefixPartial 11 75672) = false := by
  decide +kernel

theorem node_context_11_75672_1063092 : EJMOriginalGlobalDAGData.nodes 10 ⟨1063092, by decide⟩ =
    .split (coordinate 11) (![⟨1062986, by decide⟩,⟨1063034, by decide⟩,⟨1063061, by decide⟩,⟨1063091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75672_1063092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75672 ⟨1063092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75672
    ⟨1063092, by decide⟩ (by decide) (![⟨1062986, by decide⟩,⟨1063034, by decide⟩,⟨1063061, by decide⟩,⟨1063091, by decide⟩]) unmarked_context_11_75672_1063092 node_context_11_75672_1063092
  intro a
  fin_cases a
  · exact context_12_302688_1062986
  · exact context_12_302689_1063034
  · exact context_12_302690_1063061
  · exact context_12_302691_1063091

theorem selected_cut_39205 : selected 9 ⟨1063122, by decide⟩
    (prefixPartial 12 302692) = some ⟨12, 2, 0, 1063122, 302692, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_302692_1063122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302692 ⟨1063122, by decide⟩ :=
  accepted_of_selected 12 302692 ⟨1063122, by decide⟩ ⟨12, 2, 0, 1063122, 302692, 1981, 65536⟩
    (by decide) selected_cut_39205

theorem selected_cut_39206 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 302693) = some ⟨12, 1, 0, 691709, 302693, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302693_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302693 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 302693 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 302693, 1, 65536⟩
    (by decide) selected_cut_39206

theorem selected_cut_39207 : selected 9 ⟨1063145, by decide⟩
    (prefixPartial 12 302694) = some ⟨12, 2, 0, 1063145, 302694, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_302694_1063145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302694 ⟨1063145, by decide⟩ :=
  accepted_of_selected 12 302694 ⟨1063145, by decide⟩ ⟨12, 2, 0, 1063145, 302694, 1853, 65536⟩
    (by decide) selected_cut_39207

theorem selected_cut_39208 : selected 9 ⟨1063170, by decide⟩
    (prefixPartial 12 302695) = some ⟨12, 2, 0, 1063170, 302695, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_302695_1063170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302695 ⟨1063170, by decide⟩ :=
  accepted_of_selected 12 302695 ⟨1063170, by decide⟩ ⟨12, 2, 0, 1063170, 302695, 1993, 65536⟩
    (by decide) selected_cut_39208

theorem unmarked_context_11_75673_1063171 : frontier 10 ⟨1063171, by decide⟩
    (prefixCache 11 75673) (prefixPartial 11 75673) = false := by
  decide +kernel

theorem node_context_11_75673_1063171 : EJMOriginalGlobalDAGData.nodes 10 ⟨1063171, by decide⟩ =
    .split (coordinate 11) (![⟨1063122, by decide⟩,⟨691709, by decide⟩,⟨1063145, by decide⟩,⟨1063170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75673_1063171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75673 ⟨1063171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75673
    ⟨1063171, by decide⟩ (by decide) (![⟨1063122, by decide⟩,⟨691709, by decide⟩,⟨1063145, by decide⟩,⟨1063170, by decide⟩]) unmarked_context_11_75673_1063171 node_context_11_75673_1063171
  intro a
  fin_cases a
  · exact context_12_302692_1063122
  · exact context_12_302693_691709
  · exact context_12_302694_1063145
  · exact context_12_302695_1063170

theorem selected_cut_39209 : selected 9 ⟨1063214, by decide⟩
    (prefixPartial 12 302696) = some ⟨12, 2, 0, 1063214, 302696, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_302696_1063214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302696 ⟨1063214, by decide⟩ :=
  accepted_of_selected 12 302696 ⟨1063214, by decide⟩ ⟨12, 2, 0, 1063214, 302696, 2169, 65536⟩
    (by decide) selected_cut_39209

theorem selected_cut_39210 : selected 9 ⟨1063276, by decide⟩
    (prefixPartial 12 302697) = some ⟨12, 2, 0, 1063276, 302697, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_302697_1063276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302697 ⟨1063276, by decide⟩ :=
  accepted_of_selected 12 302697 ⟨1063276, by decide⟩ ⟨12, 2, 0, 1063276, 302697, 2537, 65536⟩
    (by decide) selected_cut_39210

theorem selected_cut_39211 : selected 9 ⟨661672, by decide⟩
    (prefixPartial 12 302698) = some ⟨12, 1, 0, 661672, 302698, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302698_661672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302698 ⟨661672, by decide⟩ :=
  accepted_of_selected 12 302698 ⟨661672, by decide⟩ ⟨12, 1, 0, 661672, 302698, 1, 65536⟩
    (by decide) selected_cut_39211

theorem selected_cut_39212 : selected 9 ⟨1063312, by decide⟩
    (prefixPartial 12 302699) = some ⟨12, 2, 0, 1063312, 302699, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_302699_1063312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302699 ⟨1063312, by decide⟩ :=
  accepted_of_selected 12 302699 ⟨1063312, by decide⟩ ⟨12, 2, 0, 1063312, 302699, 2389, 65536⟩
    (by decide) selected_cut_39212

theorem unmarked_context_11_75674_1063313 : frontier 10 ⟨1063313, by decide⟩
    (prefixCache 11 75674) (prefixPartial 11 75674) = false := by
  decide +kernel

theorem node_context_11_75674_1063313 : EJMOriginalGlobalDAGData.nodes 10 ⟨1063313, by decide⟩ =
    .split (coordinate 11) (![⟨1063214, by decide⟩,⟨1063276, by decide⟩,⟨661672, by decide⟩,⟨1063312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75674_1063313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75674 ⟨1063313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75674
    ⟨1063313, by decide⟩ (by decide) (![⟨1063214, by decide⟩,⟨1063276, by decide⟩,⟨661672, by decide⟩,⟨1063312, by decide⟩]) unmarked_context_11_75674_1063313 node_context_11_75674_1063313
  intro a
  fin_cases a
  · exact context_12_302696_1063214
  · exact context_12_302697_1063276
  · exact context_12_302698_661672
  · exact context_12_302699_1063312

theorem selected_cut_39213 : selected 9 ⟨1063342, by decide⟩
    (prefixPartial 12 302700) = some ⟨12, 2, 0, 1063342, 302700, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_302700_1063342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302700 ⟨1063342, by decide⟩ :=
  accepted_of_selected 12 302700 ⟨1063342, by decide⟩ ⟨12, 2, 0, 1063342, 302700, 1989, 65536⟩
    (by decide) selected_cut_39213

theorem selected_cut_39214 : selected 9 ⟨1063371, by decide⟩
    (prefixPartial 12 302701) = some ⟨12, 2, 0, 1063371, 302701, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_302701_1063371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302701 ⟨1063371, by decide⟩ :=
  accepted_of_selected 12 302701 ⟨1063371, by decide⟩ ⟨12, 2, 0, 1063371, 302701, 2225, 65536⟩
    (by decide) selected_cut_39214

theorem selected_cut_39215 : selected 9 ⟨1063398, by decide⟩
    (prefixPartial 12 302702) = some ⟨12, 2, 0, 1063398, 302702, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_302702_1063398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302702 ⟨1063398, by decide⟩ :=
  accepted_of_selected 12 302702 ⟨1063398, by decide⟩ ⟨12, 2, 0, 1063398, 302702, 1861, 65536⟩
    (by decide) selected_cut_39215

theorem selected_cut_39216 : selected 9 ⟨1063424, by decide⟩
    (prefixPartial 12 302703) = some ⟨12, 2, 0, 1063424, 302703, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_302703_1063424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302703 ⟨1063424, by decide⟩ :=
  accepted_of_selected 12 302703 ⟨1063424, by decide⟩ ⟨12, 2, 0, 1063424, 302703, 1937, 65536⟩
    (by decide) selected_cut_39216

theorem unmarked_context_11_75675_1063425 : frontier 10 ⟨1063425, by decide⟩
    (prefixCache 11 75675) (prefixPartial 11 75675) = false := by
  decide +kernel

theorem node_context_11_75675_1063425 : EJMOriginalGlobalDAGData.nodes 10 ⟨1063425, by decide⟩ =
    .split (coordinate 11) (![⟨1063342, by decide⟩,⟨1063371, by decide⟩,⟨1063398, by decide⟩,⟨1063424, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75675_1063425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75675 ⟨1063425, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75675
    ⟨1063425, by decide⟩ (by decide) (![⟨1063342, by decide⟩,⟨1063371, by decide⟩,⟨1063398, by decide⟩,⟨1063424, by decide⟩]) unmarked_context_11_75675_1063425 node_context_11_75675_1063425
  intro a
  fin_cases a
  · exact context_12_302700_1063342
  · exact context_12_302701_1063371
  · exact context_12_302702_1063398
  · exact context_12_302703_1063424

theorem unmarked_context_10_18918_1063426 : frontier 11 ⟨1063426, by decide⟩
    (prefixCache 10 18918) (prefixPartial 10 18918) = false := by
  decide +kernel

theorem node_context_10_18918_1063426 : EJMOriginalGlobalDAGData.nodes 11 ⟨1063426, by decide⟩ =
    .split (coordinate 10) (![⟨1063092, by decide⟩,⟨1063171, by decide⟩,⟨1063313, by decide⟩,⟨1063425, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18918_1063426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18918 ⟨1063426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18918
    ⟨1063426, by decide⟩ (by decide) (![⟨1063092, by decide⟩,⟨1063171, by decide⟩,⟨1063313, by decide⟩,⟨1063425, by decide⟩]) unmarked_context_10_18918_1063426 node_context_10_18918_1063426
  intro a
  fin_cases a
  · exact context_11_75672_1063092
  · exact context_11_75673_1063171
  · exact context_11_75674_1063313
  · exact context_11_75675_1063425

theorem selected_cut_39217 : selected 9 ⟨1063462, by decide⟩
    (prefixPartial 12 302704) = some ⟨12, 2, 0, 1063462, 302704, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_302704_1063462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302704 ⟨1063462, by decide⟩ :=
  accepted_of_selected 12 302704 ⟨1063462, by decide⟩ ⟨12, 2, 0, 1063462, 302704, 1869, 65536⟩
    (by decide) selected_cut_39217

theorem selected_cut_39218 : selected 9 ⟨1063491, by decide⟩
    (prefixPartial 12 302705) = some ⟨12, 2, 0, 1063491, 302705, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_302705_1063491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302705 ⟨1063491, by decide⟩ :=
  accepted_of_selected 12 302705 ⟨1063491, by decide⟩ ⟨12, 2, 0, 1063491, 302705, 1985, 65536⟩
    (by decide) selected_cut_39218

theorem selected_cut_39219 : selected 9 ⟨1063517, by decide⟩
    (prefixPartial 12 302706) = some ⟨12, 2, 0, 1063517, 302706, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_302706_1063517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302706 ⟨1063517, by decide⟩ :=
  accepted_of_selected 12 302706 ⟨1063517, by decide⟩ ⟨12, 2, 0, 1063517, 302706, 1649, 65536⟩
    (by decide) selected_cut_39219

theorem selected_cut_39220 : selected 9 ⟨1063542, by decide⟩
    (prefixPartial 12 302707) = some ⟨12, 2, 0, 1063542, 302707, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_302707_1063542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302707 ⟨1063542, by decide⟩ :=
  accepted_of_selected 12 302707 ⟨1063542, by decide⟩ ⟨12, 2, 0, 1063542, 302707, 1777, 65536⟩
    (by decide) selected_cut_39220

theorem unmarked_context_11_75676_1063543 : frontier 10 ⟨1063543, by decide⟩
    (prefixCache 11 75676) (prefixPartial 11 75676) = false := by
  decide +kernel

theorem node_context_11_75676_1063543 : EJMOriginalGlobalDAGData.nodes 10 ⟨1063543, by decide⟩ =
    .split (coordinate 11) (![⟨1063462, by decide⟩,⟨1063491, by decide⟩,⟨1063517, by decide⟩,⟨1063542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75676_1063543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75676 ⟨1063543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75676
    ⟨1063543, by decide⟩ (by decide) (![⟨1063462, by decide⟩,⟨1063491, by decide⟩,⟨1063517, by decide⟩,⟨1063542, by decide⟩]) unmarked_context_11_75676_1063543 node_context_11_75676_1063543
  intro a
  fin_cases a
  · exact context_12_302704_1063462
  · exact context_12_302705_1063491
  · exact context_12_302706_1063517
  · exact context_12_302707_1063542

theorem selected_cut_39221 : selected 9 ⟨1063573, by decide⟩
    (prefixPartial 12 302708) = some ⟨12, 2, 0, 1063573, 302708, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_302708_1063573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302708 ⟨1063573, by decide⟩ :=
  accepted_of_selected 12 302708 ⟨1063573, by decide⟩ ⟨12, 2, 0, 1063573, 302708, 1761, 65536⟩
    (by decide) selected_cut_39221

theorem selected_cut_39222 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 302709) = some ⟨12, 1, 0, 691709, 302709, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302709_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302709 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 302709 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 302709, 1, 65536⟩
    (by decide) selected_cut_39222

theorem selected_cut_39223 : selected 9 ⟨1063596, by decide⟩
    (prefixPartial 12 302710) = some ⟨12, 2, 0, 1063596, 302710, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_302710_1063596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302710 ⟨1063596, by decide⟩ :=
  accepted_of_selected 12 302710 ⟨1063596, by decide⟩ ⟨12, 2, 0, 1063596, 302710, 1629, 65536⟩
    (by decide) selected_cut_39223

theorem selected_cut_39224 : selected 9 ⟨1063622, by decide⟩
    (prefixPartial 12 302711) = some ⟨12, 2, 0, 1063622, 302711, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_302711_1063622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302711 ⟨1063622, by decide⟩ :=
  accepted_of_selected 12 302711 ⟨1063622, by decide⟩ ⟨12, 2, 0, 1063622, 302711, 1669, 65536⟩
    (by decide) selected_cut_39224

theorem unmarked_context_11_75677_1063623 : frontier 10 ⟨1063623, by decide⟩
    (prefixCache 11 75677) (prefixPartial 11 75677) = false := by
  decide +kernel

theorem node_context_11_75677_1063623 : EJMOriginalGlobalDAGData.nodes 10 ⟨1063623, by decide⟩ =
    .split (coordinate 11) (![⟨1063573, by decide⟩,⟨691709, by decide⟩,⟨1063596, by decide⟩,⟨1063622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75677_1063623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75677 ⟨1063623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75677
    ⟨1063623, by decide⟩ (by decide) (![⟨1063573, by decide⟩,⟨691709, by decide⟩,⟨1063596, by decide⟩,⟨1063622, by decide⟩]) unmarked_context_11_75677_1063623 node_context_11_75677_1063623
  intro a
  fin_cases a
  · exact context_12_302708_1063573
  · exact context_12_302709_691709
  · exact context_12_302710_1063596
  · exact context_12_302711_1063622

theorem selected_cut_39225 : selected 9 ⟨1063648, by decide⟩
    (prefixPartial 12 302712) = some ⟨12, 2, 0, 1063648, 302712, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_302712_1063648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302712 ⟨1063648, by decide⟩ :=
  accepted_of_selected 12 302712 ⟨1063648, by decide⟩ ⟨12, 2, 0, 1063648, 302712, 1841, 65536⟩
    (by decide) selected_cut_39225

theorem selected_cut_39226 : selected 9 ⟨1063683, by decide⟩
    (prefixPartial 12 302713) = some ⟨12, 2, 0, 1063683, 302713, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_302713_1063683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302713 ⟨1063683, by decide⟩ :=
  accepted_of_selected 12 302713 ⟨1063683, by decide⟩ ⟨12, 2, 0, 1063683, 302713, 2009, 65536⟩
    (by decide) selected_cut_39226

theorem selected_cut_39227 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 302714) = some ⟨12, 1, 0, 893903, 302714, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302714_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302714 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 302714 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 302714, 1, 65536⟩
    (by decide) selected_cut_39227

theorem selected_cut_39228 : selected 9 ⟨1063715, by decide⟩
    (prefixPartial 12 302715) = some ⟨12, 2, 0, 1063715, 302715, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_302715_1063715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302715 ⟨1063715, by decide⟩ :=
  accepted_of_selected 12 302715 ⟨1063715, by decide⟩ ⟨12, 2, 0, 1063715, 302715, 1885, 65536⟩
    (by decide) selected_cut_39228

theorem unmarked_context_11_75678_1063716 : frontier 10 ⟨1063716, by decide⟩
    (prefixCache 11 75678) (prefixPartial 11 75678) = false := by
  decide +kernel

theorem node_context_11_75678_1063716 : EJMOriginalGlobalDAGData.nodes 10 ⟨1063716, by decide⟩ =
    .split (coordinate 11) (![⟨1063648, by decide⟩,⟨1063683, by decide⟩,⟨893903, by decide⟩,⟨1063715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75678_1063716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75678 ⟨1063716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75678
    ⟨1063716, by decide⟩ (by decide) (![⟨1063648, by decide⟩,⟨1063683, by decide⟩,⟨893903, by decide⟩,⟨1063715, by decide⟩]) unmarked_context_11_75678_1063716 node_context_11_75678_1063716
  intro a
  fin_cases a
  · exact context_12_302712_1063648
  · exact context_12_302713_1063683
  · exact context_12_302714_893903
  · exact context_12_302715_1063715

theorem selected_cut_39229 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 75679) = some ⟨11, 1, 0, 977886, 75679, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75679_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75679 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 75679 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 75679, 1, 262144⟩
    (by decide) selected_cut_39229

theorem unmarked_context_10_18919_1063717 : frontier 11 ⟨1063717, by decide⟩
    (prefixCache 10 18919) (prefixPartial 10 18919) = false := by
  decide +kernel

theorem node_context_10_18919_1063717 : EJMOriginalGlobalDAGData.nodes 11 ⟨1063717, by decide⟩ =
    .split (coordinate 10) (![⟨1063543, by decide⟩,⟨1063623, by decide⟩,⟨1063716, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18919_1063717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18919 ⟨1063717, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18919
    ⟨1063717, by decide⟩ (by decide) (![⟨1063543, by decide⟩,⟨1063623, by decide⟩,⟨1063716, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18919_1063717 node_context_10_18919_1063717
  intro a
  fin_cases a
  · exact context_11_75676_1063543
  · exact context_11_75677_1063623
  · exact context_11_75678_1063716
  · exact context_11_75679_977886

theorem unmarked_context_9_4729_1063718 : frontier 12 ⟨1063718, by decide⟩
    (prefixCache 9 4729) (prefixPartial 9 4729) = false := by
  decide +kernel

theorem node_context_9_4729_1063718 : EJMOriginalGlobalDAGData.nodes 12 ⟨1063718, by decide⟩ =
    .split (coordinate 9) (![⟨1062959, by decide⟩,⟨893098, by decide⟩,⟨1063426, by decide⟩,⟨1063717, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4729_1063718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4729 ⟨1063718, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4729
    ⟨1063718, by decide⟩ (by decide) (![⟨1062959, by decide⟩,⟨893098, by decide⟩,⟨1063426, by decide⟩,⟨1063717, by decide⟩]) unmarked_context_9_4729_1063718 node_context_9_4729_1063718
  intro a
  fin_cases a
  · exact context_10_18916_1062959
  · exact context_10_18917_893098
  · exact context_10_18918_1063426
  · exact context_10_18919_1063717

theorem selected_cut_39230 : selected 10 ⟨1063770, by decide⟩
    (prefixPartial 11 75680) = some ⟨11, 2, 0, 1063770, 75680, 3129, 262144⟩ := by
  decide +kernel

theorem context_11_75680_1063770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75680 ⟨1063770, by decide⟩ :=
  accepted_of_selected 11 75680 ⟨1063770, by decide⟩ ⟨11, 2, 0, 1063770, 75680, 3129, 262144⟩
    (by decide) selected_cut_39230

theorem selected_cut_39231 : selected 9 ⟨1063796, by decide⟩
    (prefixPartial 12 302724) = some ⟨12, 2, 0, 1063796, 302724, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_302724_1063796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302724 ⟨1063796, by decide⟩ :=
  accepted_of_selected 12 302724 ⟨1063796, by decide⟩ ⟨12, 2, 0, 1063796, 302724, 1541, 65536⟩
    (by decide) selected_cut_39231

theorem selected_cut_39232 : selected 9 ⟨1063823, by decide⟩
    (prefixPartial 12 302725) = some ⟨12, 2, 0, 1063823, 302725, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_302725_1063823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302725 ⟨1063823, by decide⟩ :=
  accepted_of_selected 12 302725 ⟨1063823, by decide⟩ ⟨12, 2, 0, 1063823, 302725, 1621, 65536⟩
    (by decide) selected_cut_39232

theorem selected_cut_39233 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 302726) = some ⟨12, 1, 0, 984676, 302726, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302726_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302726 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 302726 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 302726, 1, 65536⟩
    (by decide) selected_cut_39233

theorem selected_cut_39234 : selected 9 ⟨1063848, by decide⟩
    (prefixPartial 12 302727) = some ⟨12, 2, 0, 1063848, 302727, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_302727_1063848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302727 ⟨1063848, by decide⟩ :=
  accepted_of_selected 12 302727 ⟨1063848, by decide⟩ ⟨12, 2, 0, 1063848, 302727, 1465, 65536⟩
    (by decide) selected_cut_39234

theorem unmarked_context_11_75681_1063849 : frontier 10 ⟨1063849, by decide⟩
    (prefixCache 11 75681) (prefixPartial 11 75681) = false := by
  decide +kernel

theorem node_context_11_75681_1063849 : EJMOriginalGlobalDAGData.nodes 10 ⟨1063849, by decide⟩ =
    .split (coordinate 11) (![⟨1063796, by decide⟩,⟨1063823, by decide⟩,⟨984676, by decide⟩,⟨1063848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75681_1063849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75681 ⟨1063849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75681
    ⟨1063849, by decide⟩ (by decide) (![⟨1063796, by decide⟩,⟨1063823, by decide⟩,⟨984676, by decide⟩,⟨1063848, by decide⟩]) unmarked_context_11_75681_1063849 node_context_11_75681_1063849
  intro a
  fin_cases a
  · exact context_12_302724_1063796
  · exact context_12_302725_1063823
  · exact context_12_302726_984676
  · exact context_12_302727_1063848

theorem selected_cut_39235 : selected 9 ⟨1063878, by decide⟩
    (prefixPartial 12 302728) = some ⟨12, 2, 0, 1063878, 302728, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_302728_1063878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302728 ⟨1063878, by decide⟩ :=
  accepted_of_selected 12 302728 ⟨1063878, by decide⟩ ⟨12, 2, 0, 1063878, 302728, 1633, 65536⟩
    (by decide) selected_cut_39235

theorem selected_cut_39236 : selected 9 ⟨1063902, by decide⟩
    (prefixPartial 12 302729) = some ⟨12, 2, 0, 1063902, 302729, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_302729_1063902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302729 ⟨1063902, by decide⟩ :=
  accepted_of_selected 12 302729 ⟨1063902, by decide⟩ ⟨12, 2, 0, 1063902, 302729, 1633, 65536⟩
    (by decide) selected_cut_39236

theorem selected_cut_39237 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 302730) = some ⟨12, 1, 0, 984676, 302730, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302730_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302730 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 302730 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 302730, 1, 65536⟩
    (by decide) selected_cut_39237

theorem selected_cut_39238 : selected 9 ⟨1063929, by decide⟩
    (prefixPartial 12 302731) = some ⟨12, 2, 0, 1063929, 302731, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_302731_1063929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302731 ⟨1063929, by decide⟩ :=
  accepted_of_selected 12 302731 ⟨1063929, by decide⟩ ⟨12, 2, 0, 1063929, 302731, 1597, 65536⟩
    (by decide) selected_cut_39238

theorem unmarked_context_11_75682_1063930 : frontier 10 ⟨1063930, by decide⟩
    (prefixCache 11 75682) (prefixPartial 11 75682) = false := by
  decide +kernel

theorem node_context_11_75682_1063930 : EJMOriginalGlobalDAGData.nodes 10 ⟨1063930, by decide⟩ =
    .split (coordinate 11) (![⟨1063878, by decide⟩,⟨1063902, by decide⟩,⟨984676, by decide⟩,⟨1063929, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75682_1063930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75682 ⟨1063930, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75682
    ⟨1063930, by decide⟩ (by decide) (![⟨1063878, by decide⟩,⟨1063902, by decide⟩,⟨984676, by decide⟩,⟨1063929, by decide⟩]) unmarked_context_11_75682_1063930 node_context_11_75682_1063930
  intro a
  fin_cases a
  · exact context_12_302728_1063878
  · exact context_12_302729_1063902
  · exact context_12_302730_984676
  · exact context_12_302731_1063929

theorem selected_cut_39239 : selected 9 ⟨1063954, by decide⟩
    (prefixPartial 12 302732) = some ⟨12, 2, 0, 1063954, 302732, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_302732_1063954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302732 ⟨1063954, by decide⟩ :=
  accepted_of_selected 12 302732 ⟨1063954, by decide⟩ ⟨12, 2, 0, 1063954, 302732, 1589, 65536⟩
    (by decide) selected_cut_39239

theorem selected_cut_39240 : selected 9 ⟨1063977, by decide⟩
    (prefixPartial 12 302733) = some ⟨12, 2, 0, 1063977, 302733, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_302733_1063977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302733 ⟨1063977, by decide⟩ :=
  accepted_of_selected 12 302733 ⟨1063977, by decide⟩ ⟨12, 2, 0, 1063977, 302733, 1541, 65536⟩
    (by decide) selected_cut_39240

theorem selected_cut_39241 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 302734) = some ⟨12, 1, 0, 984676, 302734, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302734_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302734 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 302734 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 302734, 1, 65536⟩
    (by decide) selected_cut_39241

theorem selected_cut_39242 : selected 9 ⟨1063996, by decide⟩
    (prefixPartial 12 302735) = some ⟨12, 2, 0, 1063996, 302735, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_302735_1063996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302735 ⟨1063996, by decide⟩ :=
  accepted_of_selected 12 302735 ⟨1063996, by decide⟩ ⟨12, 2, 0, 1063996, 302735, 1413, 65536⟩
    (by decide) selected_cut_39242

theorem unmarked_context_11_75683_1063997 : frontier 10 ⟨1063997, by decide⟩
    (prefixCache 11 75683) (prefixPartial 11 75683) = false := by
  decide +kernel

theorem node_context_11_75683_1063997 : EJMOriginalGlobalDAGData.nodes 10 ⟨1063997, by decide⟩ =
    .split (coordinate 11) (![⟨1063954, by decide⟩,⟨1063977, by decide⟩,⟨984676, by decide⟩,⟨1063996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75683_1063997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75683 ⟨1063997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75683
    ⟨1063997, by decide⟩ (by decide) (![⟨1063954, by decide⟩,⟨1063977, by decide⟩,⟨984676, by decide⟩,⟨1063996, by decide⟩]) unmarked_context_11_75683_1063997 node_context_11_75683_1063997
  intro a
  fin_cases a
  · exact context_12_302732_1063954
  · exact context_12_302733_1063977
  · exact context_12_302734_984676
  · exact context_12_302735_1063996

theorem unmarked_context_10_18920_1063998 : frontier 11 ⟨1063998, by decide⟩
    (prefixCache 10 18920) (prefixPartial 10 18920) = false := by
  decide +kernel

theorem node_context_10_18920_1063998 : EJMOriginalGlobalDAGData.nodes 11 ⟨1063998, by decide⟩ =
    .split (coordinate 10) (![⟨1063770, by decide⟩,⟨1063849, by decide⟩,⟨1063930, by decide⟩,⟨1063997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18920_1063998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18920 ⟨1063998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18920
    ⟨1063998, by decide⟩ (by decide) (![⟨1063770, by decide⟩,⟨1063849, by decide⟩,⟨1063930, by decide⟩,⟨1063997, by decide⟩]) unmarked_context_10_18920_1063998 node_context_10_18920_1063998
  intro a
  fin_cases a
  · exact context_11_75680_1063770
  · exact context_11_75681_1063849
  · exact context_11_75682_1063930
  · exact context_11_75683_1063997

theorem selected_cut_39243 : selected 9 ⟨1064018, by decide⟩
    (prefixPartial 12 302736) = some ⟨12, 2, 0, 1064018, 302736, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_302736_1064018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302736 ⟨1064018, by decide⟩ :=
  accepted_of_selected 12 302736 ⟨1064018, by decide⟩ ⟨12, 2, 0, 1064018, 302736, 1361, 65536⟩
    (by decide) selected_cut_39243

theorem selected_cut_39244 : selected 9 ⟨1064038, by decide⟩
    (prefixPartial 12 302737) = some ⟨12, 2, 0, 1064038, 302737, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_302737_1064038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302737 ⟨1064038, by decide⟩ :=
  accepted_of_selected 12 302737 ⟨1064038, by decide⟩ ⟨12, 2, 0, 1064038, 302737, 1397, 65536⟩
    (by decide) selected_cut_39244

theorem selected_cut_39245 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 302738) = some ⟨12, 1, 0, 984676, 302738, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302738_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302738 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 302738 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 302738, 1, 65536⟩
    (by decide) selected_cut_39245

theorem selected_cut_39246 : selected 9 ⟨1064062, by decide⟩
    (prefixPartial 12 302739) = some ⟨12, 2, 0, 1064062, 302739, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_302739_1064062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302739 ⟨1064062, by decide⟩ :=
  accepted_of_selected 12 302739 ⟨1064062, by decide⟩ ⟨12, 2, 0, 1064062, 302739, 1405, 65536⟩
    (by decide) selected_cut_39246

theorem unmarked_context_11_75684_1064063 : frontier 10 ⟨1064063, by decide⟩
    (prefixCache 11 75684) (prefixPartial 11 75684) = false := by
  decide +kernel

theorem node_context_11_75684_1064063 : EJMOriginalGlobalDAGData.nodes 10 ⟨1064063, by decide⟩ =
    .split (coordinate 11) (![⟨1064018, by decide⟩,⟨1064038, by decide⟩,⟨984676, by decide⟩,⟨1064062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75684_1064063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75684 ⟨1064063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75684
    ⟨1064063, by decide⟩ (by decide) (![⟨1064018, by decide⟩,⟨1064038, by decide⟩,⟨984676, by decide⟩,⟨1064062, by decide⟩]) unmarked_context_11_75684_1064063 node_context_11_75684_1064063
  intro a
  fin_cases a
  · exact context_12_302736_1064018
  · exact context_12_302737_1064038
  · exact context_12_302738_984676
  · exact context_12_302739_1064062

theorem selected_cut_39247 : selected 10 ⟨1064094, by decide⟩
    (prefixPartial 11 75685) = some ⟨11, 2, 0, 1064094, 75685, 2201, 262144⟩ := by
  decide +kernel

theorem context_11_75685_1064094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75685 ⟨1064094, by decide⟩ :=
  accepted_of_selected 11 75685 ⟨1064094, by decide⟩ ⟨11, 2, 0, 1064094, 75685, 2201, 262144⟩
    (by decide) selected_cut_39247

theorem selected_cut_39248 : selected 10 ⟨1064151, by decide⟩
    (prefixPartial 11 75686) = some ⟨11, 2, 0, 1064151, 75686, 3701, 262144⟩ := by
  decide +kernel

theorem context_11_75686_1064151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75686 ⟨1064151, by decide⟩ :=
  accepted_of_selected 11 75686 ⟨1064151, by decide⟩ ⟨11, 2, 0, 1064151, 75686, 3701, 262144⟩
    (by decide) selected_cut_39248

theorem selected_cut_39249 : selected 10 ⟨1064210, by decide⟩
    (prefixPartial 11 75687) = some ⟨11, 2, 0, 1064210, 75687, 3809, 262144⟩ := by
  decide +kernel

theorem context_11_75687_1064210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75687 ⟨1064210, by decide⟩ :=
  accepted_of_selected 11 75687 ⟨1064210, by decide⟩ ⟨11, 2, 0, 1064210, 75687, 3809, 262144⟩
    (by decide) selected_cut_39249

theorem unmarked_context_10_18921_1064211 : frontier 11 ⟨1064211, by decide⟩
    (prefixCache 10 18921) (prefixPartial 10 18921) = false := by
  decide +kernel

theorem node_context_10_18921_1064211 : EJMOriginalGlobalDAGData.nodes 11 ⟨1064211, by decide⟩ =
    .split (coordinate 10) (![⟨1064063, by decide⟩,⟨1064094, by decide⟩,⟨1064151, by decide⟩,⟨1064210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18921_1064211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18921 ⟨1064211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18921
    ⟨1064211, by decide⟩ (by decide) (![⟨1064063, by decide⟩,⟨1064094, by decide⟩,⟨1064151, by decide⟩,⟨1064210, by decide⟩]) unmarked_context_10_18921_1064211 node_context_10_18921_1064211
  intro a
  fin_cases a
  · exact context_11_75684_1064063
  · exact context_11_75685_1064094
  · exact context_11_75686_1064151
  · exact context_11_75687_1064210

theorem selected_cut_39250 : selected 10 ⟨1064252, by decide⟩
    (prefixPartial 11 75688) = some ⟨11, 2, 0, 1064252, 75688, 2829, 262144⟩ := by
  decide +kernel

theorem context_11_75688_1064252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75688 ⟨1064252, by decide⟩ :=
  accepted_of_selected 11 75688 ⟨1064252, by decide⟩ ⟨11, 2, 0, 1064252, 75688, 2829, 262144⟩
    (by decide) selected_cut_39250

theorem selected_cut_39251 : selected 10 ⟨1064293, by decide⟩
    (prefixPartial 11 75689) = some ⟨11, 2, 0, 1064293, 75689, 2489, 262144⟩ := by
  decide +kernel

theorem context_11_75689_1064293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75689 ⟨1064293, by decide⟩ :=
  accepted_of_selected 11 75689 ⟨1064293, by decide⟩ ⟨11, 2, 0, 1064293, 75689, 2489, 262144⟩
    (by decide) selected_cut_39251

theorem selected_cut_39252 : selected 10 ⟨1064304, by decide⟩
    (prefixPartial 11 75690) = some ⟨11, 2, 0, 1064304, 75690, 777, 262144⟩ := by
  decide +kernel

theorem context_11_75690_1064304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75690 ⟨1064304, by decide⟩ :=
  accepted_of_selected 11 75690 ⟨1064304, by decide⟩ ⟨11, 2, 0, 1064304, 75690, 777, 262144⟩
    (by decide) selected_cut_39252

theorem selected_cut_39253 : selected 10 ⟨1064338, by decide⟩
    (prefixPartial 11 75691) = some ⟨11, 2, 0, 1064338, 75691, 2541, 262144⟩ := by
  decide +kernel

theorem context_11_75691_1064338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75691 ⟨1064338, by decide⟩ :=
  accepted_of_selected 11 75691 ⟨1064338, by decide⟩ ⟨11, 2, 0, 1064338, 75691, 2541, 262144⟩
    (by decide) selected_cut_39253

theorem unmarked_context_10_18922_1064339 : frontier 11 ⟨1064339, by decide⟩
    (prefixCache 10 18922) (prefixPartial 10 18922) = false := by
  decide +kernel

theorem node_context_10_18922_1064339 : EJMOriginalGlobalDAGData.nodes 11 ⟨1064339, by decide⟩ =
    .split (coordinate 10) (![⟨1064252, by decide⟩,⟨1064293, by decide⟩,⟨1064304, by decide⟩,⟨1064338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18922_1064339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18922 ⟨1064339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18922
    ⟨1064339, by decide⟩ (by decide) (![⟨1064252, by decide⟩,⟨1064293, by decide⟩,⟨1064304, by decide⟩,⟨1064338, by decide⟩]) unmarked_context_10_18922_1064339 node_context_10_18922_1064339
  intro a
  fin_cases a
  · exact context_11_75688_1064252
  · exact context_11_75689_1064293
  · exact context_11_75690_1064304
  · exact context_11_75691_1064338

theorem selected_cut_39254 : selected 10 ⟨1064369, by decide⟩
    (prefixPartial 11 75692) = some ⟨11, 2, 0, 1064369, 75692, 2153, 262144⟩ := by
  decide +kernel

theorem context_11_75692_1064369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75692 ⟨1064369, by decide⟩ :=
  accepted_of_selected 11 75692 ⟨1064369, by decide⟩ ⟨11, 2, 0, 1064369, 75692, 2153, 262144⟩
    (by decide) selected_cut_39254

theorem selected_cut_39255 : selected 10 ⟨1064403, by decide⟩
    (prefixPartial 11 75693) = some ⟨11, 2, 0, 1064403, 75693, 2085, 262144⟩ := by
  decide +kernel

theorem context_11_75693_1064403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75693 ⟨1064403, by decide⟩ :=
  accepted_of_selected 11 75693 ⟨1064403, by decide⟩ ⟨11, 2, 0, 1064403, 75693, 2085, 262144⟩
    (by decide) selected_cut_39255

theorem selected_cut_39256 : selected 10 ⟨1064435, by decide⟩
    (prefixPartial 11 75694) = some ⟨11, 2, 0, 1064435, 75694, 2013, 262144⟩ := by
  decide +kernel

theorem context_11_75694_1064435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75694 ⟨1064435, by decide⟩ :=
  accepted_of_selected 11 75694 ⟨1064435, by decide⟩ ⟨11, 2, 0, 1064435, 75694, 2013, 262144⟩
    (by decide) selected_cut_39256

theorem selected_cut_39257 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 75695) = some ⟨11, 1, 0, 977886, 75695, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75695_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75695 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 75695 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 75695, 1, 262144⟩
    (by decide) selected_cut_39257

theorem unmarked_context_10_18923_1064436 : frontier 11 ⟨1064436, by decide⟩
    (prefixCache 10 18923) (prefixPartial 10 18923) = false := by
  decide +kernel

theorem node_context_10_18923_1064436 : EJMOriginalGlobalDAGData.nodes 11 ⟨1064436, by decide⟩ =
    .split (coordinate 10) (![⟨1064369, by decide⟩,⟨1064403, by decide⟩,⟨1064435, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18923_1064436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18923 ⟨1064436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18923
    ⟨1064436, by decide⟩ (by decide) (![⟨1064369, by decide⟩,⟨1064403, by decide⟩,⟨1064435, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18923_1064436 node_context_10_18923_1064436
  intro a
  fin_cases a
  · exact context_11_75692_1064369
  · exact context_11_75693_1064403
  · exact context_11_75694_1064435
  · exact context_11_75695_977886

theorem unmarked_context_9_4730_1064437 : frontier 12 ⟨1064437, by decide⟩
    (prefixCache 9 4730) (prefixPartial 9 4730) = false := by
  decide +kernel

theorem node_context_9_4730_1064437 : EJMOriginalGlobalDAGData.nodes 12 ⟨1064437, by decide⟩ =
    .split (coordinate 9) (![⟨1063998, by decide⟩,⟨1064211, by decide⟩,⟨1064339, by decide⟩,⟨1064436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4730_1064437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4730 ⟨1064437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4730
    ⟨1064437, by decide⟩ (by decide) (![⟨1063998, by decide⟩,⟨1064211, by decide⟩,⟨1064339, by decide⟩,⟨1064436, by decide⟩]) unmarked_context_9_4730_1064437 node_context_9_4730_1064437
  intro a
  fin_cases a
  · exact context_10_18920_1063998
  · exact context_10_18921_1064211
  · exact context_10_18922_1064339
  · exact context_10_18923_1064436

theorem selected_cut_39258 : selected 10 ⟨1064482, by decide⟩
    (prefixPartial 11 75696) = some ⟨11, 2, 0, 1064482, 75696, 2057, 262144⟩ := by
  decide +kernel

theorem context_11_75696_1064482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75696 ⟨1064482, by decide⟩ :=
  accepted_of_selected 11 75696 ⟨1064482, by decide⟩ ⟨11, 2, 0, 1064482, 75696, 2057, 262144⟩
    (by decide) selected_cut_39258

theorem selected_cut_39259 : selected 10 ⟨1064524, by decide⟩
    (prefixPartial 11 75697) = some ⟨11, 2, 0, 1064524, 75697, 2821, 262144⟩ := by
  decide +kernel

theorem context_11_75697_1064524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75697 ⟨1064524, by decide⟩ :=
  accepted_of_selected 11 75697 ⟨1064524, by decide⟩ ⟨11, 2, 0, 1064524, 75697, 2821, 262144⟩
    (by decide) selected_cut_39259

theorem selected_cut_39260 : selected 10 ⟨1064546, by decide⟩
    (prefixPartial 11 75698) = some ⟨11, 2, 0, 1064546, 75698, 1693, 262144⟩ := by
  decide +kernel

theorem context_11_75698_1064546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75698 ⟨1064546, by decide⟩ :=
  accepted_of_selected 11 75698 ⟨1064546, by decide⟩ ⟨11, 2, 0, 1064546, 75698, 1693, 262144⟩
    (by decide) selected_cut_39260

theorem selected_cut_39261 : selected 10 ⟨1064573, by decide⟩
    (prefixPartial 11 75699) = some ⟨11, 2, 0, 1064573, 75699, 1785, 262144⟩ := by
  decide +kernel

theorem context_11_75699_1064573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75699 ⟨1064573, by decide⟩ :=
  accepted_of_selected 11 75699 ⟨1064573, by decide⟩ ⟨11, 2, 0, 1064573, 75699, 1785, 262144⟩
    (by decide) selected_cut_39261

theorem unmarked_context_10_18924_1064574 : frontier 11 ⟨1064574, by decide⟩
    (prefixCache 10 18924) (prefixPartial 10 18924) = false := by
  decide +kernel

theorem node_context_10_18924_1064574 : EJMOriginalGlobalDAGData.nodes 11 ⟨1064574, by decide⟩ =
    .split (coordinate 10) (![⟨1064482, by decide⟩,⟨1064524, by decide⟩,⟨1064546, by decide⟩,⟨1064573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18924_1064574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18924 ⟨1064574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18924
    ⟨1064574, by decide⟩ (by decide) (![⟨1064482, by decide⟩,⟨1064524, by decide⟩,⟨1064546, by decide⟩,⟨1064573, by decide⟩]) unmarked_context_10_18924_1064574 node_context_10_18924_1064574
  intro a
  fin_cases a
  · exact context_11_75696_1064482
  · exact context_11_75697_1064524
  · exact context_11_75698_1064546
  · exact context_11_75699_1064573

theorem selected_cut_39262 : selected 10 ⟨1064598, by decide⟩
    (prefixPartial 11 75700) = some ⟨11, 2, 0, 1064598, 75700, 1805, 262144⟩ := by
  decide +kernel

theorem context_11_75700_1064598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75700 ⟨1064598, by decide⟩ :=
  accepted_of_selected 11 75700 ⟨1064598, by decide⟩ ⟨11, 2, 0, 1064598, 75700, 1805, 262144⟩
    (by decide) selected_cut_39262

theorem selected_cut_39263 : selected 10 ⟨1064615, by decide⟩
    (prefixPartial 11 75701) = some ⟨11, 2, 0, 1064615, 75701, 1121, 262144⟩ := by
  decide +kernel

theorem context_11_75701_1064615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75701 ⟨1064615, by decide⟩ :=
  accepted_of_selected 11 75701 ⟨1064615, by decide⟩ ⟨11, 2, 0, 1064615, 75701, 1121, 262144⟩
    (by decide) selected_cut_39263

theorem selected_cut_39264 : selected 10 ⟨1064631, by decide⟩
    (prefixPartial 11 75702) = some ⟨11, 2, 0, 1064631, 75702, 1073, 262144⟩ := by
  decide +kernel

theorem context_11_75702_1064631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75702 ⟨1064631, by decide⟩ :=
  accepted_of_selected 11 75702 ⟨1064631, by decide⟩ ⟨11, 2, 0, 1064631, 75702, 1073, 262144⟩
    (by decide) selected_cut_39264

theorem selected_cut_39265 : selected 10 ⟨1064639, by decide⟩
    (prefixPartial 11 75703) = some ⟨11, 2, 0, 1064639, 75703, 1101, 262144⟩ := by
  decide +kernel

theorem context_11_75703_1064639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75703 ⟨1064639, by decide⟩ :=
  accepted_of_selected 11 75703 ⟨1064639, by decide⟩ ⟨11, 2, 0, 1064639, 75703, 1101, 262144⟩
    (by decide) selected_cut_39265

theorem unmarked_context_10_18925_1064640 : frontier 11 ⟨1064640, by decide⟩
    (prefixCache 10 18925) (prefixPartial 10 18925) = false := by
  decide +kernel

theorem node_context_10_18925_1064640 : EJMOriginalGlobalDAGData.nodes 11 ⟨1064640, by decide⟩ =
    .split (coordinate 10) (![⟨1064598, by decide⟩,⟨1064615, by decide⟩,⟨1064631, by decide⟩,⟨1064639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18925_1064640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18925 ⟨1064640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18925
    ⟨1064640, by decide⟩ (by decide) (![⟨1064598, by decide⟩,⟨1064615, by decide⟩,⟨1064631, by decide⟩,⟨1064639, by decide⟩]) unmarked_context_10_18925_1064640 node_context_10_18925_1064640
  intro a
  fin_cases a
  · exact context_11_75700_1064598
  · exact context_11_75701_1064615
  · exact context_11_75702_1064631
  · exact context_11_75703_1064639

theorem selected_cut_39266 : selected 11 ⟨1064691, by decide⟩
    (prefixPartial 10 18926) = some ⟨10, 2, 0, 1064691, 18926, 2805, 1048576⟩ := by
  decide +kernel

theorem context_10_18926_1064691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18926 ⟨1064691, by decide⟩ :=
  accepted_of_selected 10 18926 ⟨1064691, by decide⟩ ⟨10, 2, 0, 1064691, 18926, 2805, 1048576⟩
    (by decide) selected_cut_39266

theorem selected_cut_39267 : selected 11 ⟨1064722, by decide⟩
    (prefixPartial 10 18927) = some ⟨10, 2, 0, 1064722, 18927, 609, 1048576⟩ := by
  decide +kernel

theorem context_10_18927_1064722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18927 ⟨1064722, by decide⟩ :=
  accepted_of_selected 10 18927 ⟨1064722, by decide⟩ ⟨10, 2, 0, 1064722, 18927, 609, 1048576⟩
    (by decide) selected_cut_39267

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
