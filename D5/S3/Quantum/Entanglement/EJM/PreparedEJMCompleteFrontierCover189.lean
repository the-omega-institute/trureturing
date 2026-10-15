/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover188
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_18146 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 71216) = some ⟨12, 1, 0, 445562, 71216, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71216_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71216 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 71216 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 71216, 1, 65536⟩
    (by decide) selected_cut_18146

theorem selected_cut_18147 : selected 8 ⟨465208, by decide⟩
    (prefixPartial 13 284868) = some ⟨13, 2, 0, 465208, 284868, 745, 16384⟩ := by
  decide +kernel

theorem context_13_284868_465208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284868 ⟨465208, by decide⟩ :=
  accepted_of_selected 13 284868 ⟨465208, by decide⟩ ⟨13, 2, 0, 465208, 284868, 745, 16384⟩
    (by decide) selected_cut_18147

theorem selected_cut_18148 : selected 8 ⟨465237, by decide⟩
    (prefixPartial 13 284869) = some ⟨13, 2, 0, 465237, 284869, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_284869_465237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284869 ⟨465237, by decide⟩ :=
  accepted_of_selected 13 284869 ⟨465237, by decide⟩ ⟨13, 2, 0, 465237, 284869, 2253, 16384⟩
    (by decide) selected_cut_18148

theorem selected_cut_18149 : selected 8 ⟨465253, by decide⟩
    (prefixPartial 13 284870) = some ⟨13, 2, 0, 465253, 284870, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_284870_465253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284870 ⟨465253, by decide⟩ :=
  accepted_of_selected 13 284870 ⟨465253, by decide⟩ ⟨13, 2, 0, 465253, 284870, 1225, 16384⟩
    (by decide) selected_cut_18149

theorem selected_cut_18150 : selected 8 ⟨465261, by decide⟩
    (prefixPartial 13 284871) = some ⟨13, 2, 0, 465261, 284871, 801, 16384⟩ := by
  decide +kernel

theorem context_13_284871_465261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284871 ⟨465261, by decide⟩ :=
  accepted_of_selected 13 284871 ⟨465261, by decide⟩ ⟨13, 2, 0, 465261, 284871, 801, 16384⟩
    (by decide) selected_cut_18150

theorem unmarked_context_12_71217_465262 : frontier 9 ⟨465262, by decide⟩
    (prefixCache 12 71217) (prefixPartial 12 71217) = false := by
  decide +kernel

theorem node_context_12_71217_465262 : EJMOriginalGlobalDAGData.nodes 9 ⟨465262, by decide⟩ =
    .split (coordinate 12) (![⟨465208, by decide⟩,⟨465237, by decide⟩,⟨465253, by decide⟩,⟨465261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71217_465262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71217 ⟨465262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71217
    ⟨465262, by decide⟩ (by decide) (![⟨465208, by decide⟩,⟨465237, by decide⟩,⟨465253, by decide⟩,⟨465261, by decide⟩]) unmarked_context_12_71217_465262 node_context_12_71217_465262
  intro a
  fin_cases a
  · exact context_13_284868_465208
  · exact context_13_284869_465237
  · exact context_13_284870_465253
  · exact context_13_284871_465261

theorem selected_cut_18151 : selected 8 ⟨465279, by decide⟩
    (prefixPartial 13 284872) = some ⟨13, 2, 0, 465279, 284872, 717, 16384⟩ := by
  decide +kernel

theorem context_13_284872_465279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284872 ⟨465279, by decide⟩ :=
  accepted_of_selected 13 284872 ⟨465279, by decide⟩ ⟨13, 2, 0, 465279, 284872, 717, 16384⟩
    (by decide) selected_cut_18151

theorem selected_cut_18152 : selected 8 ⟨465306, by decide⟩
    (prefixPartial 13 284873) = some ⟨13, 2, 0, 465306, 284873, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_284873_465306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284873 ⟨465306, by decide⟩ :=
  accepted_of_selected 13 284873 ⟨465306, by decide⟩ ⟨13, 2, 0, 465306, 284873, 2289, 16384⟩
    (by decide) selected_cut_18152

theorem selected_cut_18153 : selected 8 ⟨465320, by decide⟩
    (prefixPartial 13 284874) = some ⟨13, 2, 0, 465320, 284874, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_284874_465320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284874 ⟨465320, by decide⟩ :=
  accepted_of_selected 13 284874 ⟨465320, by decide⟩ ⟨13, 2, 0, 465320, 284874, 1161, 16384⟩
    (by decide) selected_cut_18153

theorem selected_cut_18154 : selected 8 ⟨465328, by decide⟩
    (prefixPartial 13 284875) = some ⟨13, 2, 0, 465328, 284875, 801, 16384⟩ := by
  decide +kernel

theorem context_13_284875_465328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284875 ⟨465328, by decide⟩ :=
  accepted_of_selected 13 284875 ⟨465328, by decide⟩ ⟨13, 2, 0, 465328, 284875, 801, 16384⟩
    (by decide) selected_cut_18154

theorem unmarked_context_12_71218_465329 : frontier 9 ⟨465329, by decide⟩
    (prefixCache 12 71218) (prefixPartial 12 71218) = false := by
  decide +kernel

theorem node_context_12_71218_465329 : EJMOriginalGlobalDAGData.nodes 9 ⟨465329, by decide⟩ =
    .split (coordinate 12) (![⟨465279, by decide⟩,⟨465306, by decide⟩,⟨465320, by decide⟩,⟨465328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71218_465329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71218 ⟨465329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71218
    ⟨465329, by decide⟩ (by decide) (![⟨465279, by decide⟩,⟨465306, by decide⟩,⟨465320, by decide⟩,⟨465328, by decide⟩]) unmarked_context_12_71218_465329 node_context_12_71218_465329
  intro a
  fin_cases a
  · exact context_13_284872_465279
  · exact context_13_284873_465306
  · exact context_13_284874_465320
  · exact context_13_284875_465328

theorem selected_cut_18155 : selected 8 ⟨465346, by decide⟩
    (prefixPartial 13 284876) = some ⟨13, 2, 0, 465346, 284876, 869, 16384⟩ := by
  decide +kernel

theorem context_13_284876_465346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284876 ⟨465346, by decide⟩ :=
  accepted_of_selected 13 284876 ⟨465346, by decide⟩ ⟨13, 2, 0, 465346, 284876, 869, 16384⟩
    (by decide) selected_cut_18155

theorem selected_cut_18156 : selected 8 ⟨465390, by decide⟩
    (prefixPartial 13 284877) = some ⟨13, 2, 0, 465390, 284877, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_284877_465390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284877 ⟨465390, by decide⟩ :=
  accepted_of_selected 13 284877 ⟨465390, by decide⟩ ⟨13, 2, 0, 465390, 284877, 2589, 16384⟩
    (by decide) selected_cut_18156

theorem selected_cut_18157 : selected 8 ⟨465407, by decide⟩
    (prefixPartial 13 284878) = some ⟨13, 2, 0, 465407, 284878, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_284878_465407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284878 ⟨465407, by decide⟩ :=
  accepted_of_selected 13 284878 ⟨465407, by decide⟩ ⟨13, 2, 0, 465407, 284878, 1377, 16384⟩
    (by decide) selected_cut_18157

theorem selected_cut_18158 : selected 8 ⟨465413, by decide⟩
    (prefixPartial 13 284879) = some ⟨13, 2, 0, 465413, 284879, 745, 16384⟩ := by
  decide +kernel

theorem context_13_284879_465413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284879 ⟨465413, by decide⟩ :=
  accepted_of_selected 13 284879 ⟨465413, by decide⟩ ⟨13, 2, 0, 465413, 284879, 745, 16384⟩
    (by decide) selected_cut_18158

theorem unmarked_context_12_71219_465414 : frontier 9 ⟨465414, by decide⟩
    (prefixCache 12 71219) (prefixPartial 12 71219) = false := by
  decide +kernel

theorem node_context_12_71219_465414 : EJMOriginalGlobalDAGData.nodes 9 ⟨465414, by decide⟩ =
    .split (coordinate 12) (![⟨465346, by decide⟩,⟨465390, by decide⟩,⟨465407, by decide⟩,⟨465413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71219_465414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71219 ⟨465414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71219
    ⟨465414, by decide⟩ (by decide) (![⟨465346, by decide⟩,⟨465390, by decide⟩,⟨465407, by decide⟩,⟨465413, by decide⟩]) unmarked_context_12_71219_465414 node_context_12_71219_465414
  intro a
  fin_cases a
  · exact context_13_284876_465346
  · exact context_13_284877_465390
  · exact context_13_284878_465407
  · exact context_13_284879_465413

theorem unmarked_context_11_17804_465415 : frontier 10 ⟨465415, by decide⟩
    (prefixCache 11 17804) (prefixPartial 11 17804) = false := by
  decide +kernel

theorem node_context_11_17804_465415 : EJMOriginalGlobalDAGData.nodes 10 ⟨465415, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨465262, by decide⟩,⟨465329, by decide⟩,⟨465414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17804_465415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17804 ⟨465415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17804
    ⟨465415, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨465262, by decide⟩,⟨465329, by decide⟩,⟨465414, by decide⟩]) unmarked_context_11_17804_465415 node_context_11_17804_465415
  intro a
  fin_cases a
  · exact context_12_71216_445562
  · exact context_12_71217_465262
  · exact context_12_71218_465329
  · exact context_12_71219_465414

theorem selected_cut_18159 : selected 8 ⟨465429, by decide⟩
    (prefixPartial 13 284880) = some ⟨13, 2, 0, 465429, 284880, 825, 16384⟩ := by
  decide +kernel

theorem context_13_284880_465429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284880 ⟨465429, by decide⟩ :=
  accepted_of_selected 13 284880 ⟨465429, by decide⟩ ⟨13, 2, 0, 465429, 284880, 825, 16384⟩
    (by decide) selected_cut_18159

theorem selected_cut_18160 : selected 8 ⟨465473, by decide⟩
    (prefixPartial 13 284881) = some ⟨13, 2, 0, 465473, 284881, 2953, 16384⟩ := by
  decide +kernel

theorem context_13_284881_465473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284881 ⟨465473, by decide⟩ :=
  accepted_of_selected 13 284881 ⟨465473, by decide⟩ ⟨13, 2, 0, 465473, 284881, 2953, 16384⟩
    (by decide) selected_cut_18160

theorem selected_cut_18161 : selected 8 ⟨465500, by decide⟩
    (prefixPartial 13 284882) = some ⟨13, 2, 0, 465500, 284882, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_284882_465500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284882 ⟨465500, by decide⟩ :=
  accepted_of_selected 13 284882 ⟨465500, by decide⟩ ⟨13, 2, 0, 465500, 284882, 1805, 16384⟩
    (by decide) selected_cut_18161

theorem selected_cut_18162 : selected 8 ⟨465507, by decide⟩
    (prefixPartial 13 284883) = some ⟨13, 2, 0, 465507, 284883, 949, 16384⟩ := by
  decide +kernel

theorem context_13_284883_465507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284883 ⟨465507, by decide⟩ :=
  accepted_of_selected 13 284883 ⟨465507, by decide⟩ ⟨13, 2, 0, 465507, 284883, 949, 16384⟩
    (by decide) selected_cut_18162

theorem unmarked_context_12_71220_465508 : frontier 9 ⟨465508, by decide⟩
    (prefixCache 12 71220) (prefixPartial 12 71220) = false := by
  decide +kernel

theorem node_context_12_71220_465508 : EJMOriginalGlobalDAGData.nodes 9 ⟨465508, by decide⟩ =
    .split (coordinate 12) (![⟨465429, by decide⟩,⟨465473, by decide⟩,⟨465500, by decide⟩,⟨465507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71220_465508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71220 ⟨465508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71220
    ⟨465508, by decide⟩ (by decide) (![⟨465429, by decide⟩,⟨465473, by decide⟩,⟨465500, by decide⟩,⟨465507, by decide⟩]) unmarked_context_12_71220_465508 node_context_12_71220_465508
  intro a
  fin_cases a
  · exact context_13_284880_465429
  · exact context_13_284881_465473
  · exact context_13_284882_465500
  · exact context_13_284883_465507

theorem selected_cut_18163 : selected 9 ⟨465567, by decide⟩
    (prefixPartial 12 71221) = some ⟨12, 2, 0, 465567, 71221, 4069, 65536⟩ := by
  decide +kernel

theorem context_12_71221_465567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71221 ⟨465567, by decide⟩ :=
  accepted_of_selected 12 71221 ⟨465567, by decide⟩ ⟨12, 2, 0, 465567, 71221, 4069, 65536⟩
    (by decide) selected_cut_18163

theorem selected_cut_18164 : selected 8 ⟨465577, by decide⟩
    (prefixPartial 13 284888) = some ⟨13, 2, 0, 465577, 284888, 605, 16384⟩ := by
  decide +kernel

theorem context_13_284888_465577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284888 ⟨465577, by decide⟩ :=
  accepted_of_selected 13 284888 ⟨465577, by decide⟩ ⟨13, 2, 0, 465577, 284888, 605, 16384⟩
    (by decide) selected_cut_18164

theorem selected_cut_18165 : selected 8 ⟨465602, by decide⟩
    (prefixPartial 13 284889) = some ⟨13, 2, 0, 465602, 284889, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_284889_465602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284889 ⟨465602, by decide⟩ :=
  accepted_of_selected 13 284889 ⟨465602, by decide⟩ ⟨13, 2, 0, 465602, 284889, 2013, 16384⟩
    (by decide) selected_cut_18165

theorem selected_cut_18166 : selected 8 ⟨465619, by decide⟩
    (prefixPartial 13 284890) = some ⟨13, 2, 0, 465619, 284890, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_284890_465619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284890 ⟨465619, by decide⟩ :=
  accepted_of_selected 13 284890 ⟨465619, by decide⟩ ⟨13, 2, 0, 465619, 284890, 1177, 16384⟩
    (by decide) selected_cut_18166

theorem selected_cut_18167 : selected 8 ⟨465626, by decide⟩
    (prefixPartial 13 284891) = some ⟨13, 2, 0, 465626, 284891, 825, 16384⟩ := by
  decide +kernel

theorem context_13_284891_465626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284891 ⟨465626, by decide⟩ :=
  accepted_of_selected 13 284891 ⟨465626, by decide⟩ ⟨13, 2, 0, 465626, 284891, 825, 16384⟩
    (by decide) selected_cut_18167

theorem unmarked_context_12_71222_465627 : frontier 9 ⟨465627, by decide⟩
    (prefixCache 12 71222) (prefixPartial 12 71222) = false := by
  decide +kernel

theorem node_context_12_71222_465627 : EJMOriginalGlobalDAGData.nodes 9 ⟨465627, by decide⟩ =
    .split (coordinate 12) (![⟨465577, by decide⟩,⟨465602, by decide⟩,⟨465619, by decide⟩,⟨465626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71222_465627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71222 ⟨465627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71222
    ⟨465627, by decide⟩ (by decide) (![⟨465577, by decide⟩,⟨465602, by decide⟩,⟨465619, by decide⟩,⟨465626, by decide⟩]) unmarked_context_12_71222_465627 node_context_12_71222_465627
  intro a
  fin_cases a
  · exact context_13_284888_465577
  · exact context_13_284889_465602
  · exact context_13_284890_465619
  · exact context_13_284891_465626

theorem selected_cut_18168 : selected 8 ⟨465640, by decide⟩
    (prefixPartial 13 284892) = some ⟨13, 2, 0, 465640, 284892, 573, 16384⟩ := by
  decide +kernel

theorem context_13_284892_465640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284892 ⟨465640, by decide⟩ :=
  accepted_of_selected 13 284892 ⟨465640, by decide⟩ ⟨13, 2, 0, 465640, 284892, 573, 16384⟩
    (by decide) selected_cut_18168

theorem selected_cut_18169 : selected 8 ⟨465668, by decide⟩
    (prefixPartial 13 284893) = some ⟨13, 2, 0, 465668, 284893, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_284893_465668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284893 ⟨465668, by decide⟩ :=
  accepted_of_selected 13 284893 ⟨465668, by decide⟩ ⟨13, 2, 0, 465668, 284893, 2109, 16384⟩
    (by decide) selected_cut_18169

theorem selected_cut_18170 : selected 8 ⟨465688, by decide⟩
    (prefixPartial 13 284894) = some ⟨13, 2, 0, 465688, 284894, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_284894_465688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284894 ⟨465688, by decide⟩ :=
  accepted_of_selected 13 284894 ⟨465688, by decide⟩ ⟨13, 2, 0, 465688, 284894, 1457, 16384⟩
    (by decide) selected_cut_18170

theorem selected_cut_18171 : selected 8 ⟨465695, by decide⟩
    (prefixPartial 13 284895) = some ⟨13, 2, 0, 465695, 284895, 769, 16384⟩ := by
  decide +kernel

theorem context_13_284895_465695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284895 ⟨465695, by decide⟩ :=
  accepted_of_selected 13 284895 ⟨465695, by decide⟩ ⟨13, 2, 0, 465695, 284895, 769, 16384⟩
    (by decide) selected_cut_18171

theorem unmarked_context_12_71223_465696 : frontier 9 ⟨465696, by decide⟩
    (prefixCache 12 71223) (prefixPartial 12 71223) = false := by
  decide +kernel

theorem node_context_12_71223_465696 : EJMOriginalGlobalDAGData.nodes 9 ⟨465696, by decide⟩ =
    .split (coordinate 12) (![⟨465640, by decide⟩,⟨465668, by decide⟩,⟨465688, by decide⟩,⟨465695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71223_465696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71223 ⟨465696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71223
    ⟨465696, by decide⟩ (by decide) (![⟨465640, by decide⟩,⟨465668, by decide⟩,⟨465688, by decide⟩,⟨465695, by decide⟩]) unmarked_context_12_71223_465696 node_context_12_71223_465696
  intro a
  fin_cases a
  · exact context_13_284892_465640
  · exact context_13_284893_465668
  · exact context_13_284894_465688
  · exact context_13_284895_465695

theorem unmarked_context_11_17805_465697 : frontier 10 ⟨465697, by decide⟩
    (prefixCache 11 17805) (prefixPartial 11 17805) = false := by
  decide +kernel

theorem node_context_11_17805_465697 : EJMOriginalGlobalDAGData.nodes 10 ⟨465697, by decide⟩ =
    .split (coordinate 11) (![⟨465508, by decide⟩,⟨465567, by decide⟩,⟨465627, by decide⟩,⟨465696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17805_465697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17805 ⟨465697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17805
    ⟨465697, by decide⟩ (by decide) (![⟨465508, by decide⟩,⟨465567, by decide⟩,⟨465627, by decide⟩,⟨465696, by decide⟩]) unmarked_context_11_17805_465697 node_context_11_17805_465697
  intro a
  fin_cases a
  · exact context_12_71220_465508
  · exact context_12_71221_465567
  · exact context_12_71222_465627
  · exact context_12_71223_465696

theorem selected_cut_18172 : selected 8 ⟨465705, by decide⟩
    (prefixPartial 13 284896) = some ⟨13, 2, 0, 465705, 284896, 553, 16384⟩ := by
  decide +kernel

theorem context_13_284896_465705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284896 ⟨465705, by decide⟩ :=
  accepted_of_selected 13 284896 ⟨465705, by decide⟩ ⟨13, 2, 0, 465705, 284896, 553, 16384⟩
    (by decide) selected_cut_18172

theorem selected_cut_18173 : selected 8 ⟨465747, by decide⟩
    (prefixPartial 13 284897) = some ⟨13, 2, 0, 465747, 284897, 3241, 16384⟩ := by
  decide +kernel

theorem context_13_284897_465747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284897 ⟨465747, by decide⟩ :=
  accepted_of_selected 13 284897 ⟨465747, by decide⟩ ⟨13, 2, 0, 465747, 284897, 3241, 16384⟩
    (by decide) selected_cut_18173

theorem selected_cut_18174 : selected 8 ⟨465771, by decide⟩
    (prefixPartial 13 284898) = some ⟨13, 2, 0, 465771, 284898, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_284898_465771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284898 ⟨465771, by decide⟩ :=
  accepted_of_selected 13 284898 ⟨465771, by decide⟩ ⟨13, 2, 0, 465771, 284898, 1817, 16384⟩
    (by decide) selected_cut_18174

theorem selected_cut_18175 : selected 8 ⟨465781, by decide⟩
    (prefixPartial 13 284899) = some ⟨13, 2, 0, 465781, 284899, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_284899_465781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284899 ⟨465781, by decide⟩ :=
  accepted_of_selected 13 284899 ⟨465781, by decide⟩ ⟨13, 2, 0, 465781, 284899, 1033, 16384⟩
    (by decide) selected_cut_18175

theorem unmarked_context_12_71224_465782 : frontier 9 ⟨465782, by decide⟩
    (prefixCache 12 71224) (prefixPartial 12 71224) = false := by
  decide +kernel

theorem node_context_12_71224_465782 : EJMOriginalGlobalDAGData.nodes 9 ⟨465782, by decide⟩ =
    .split (coordinate 12) (![⟨465705, by decide⟩,⟨465747, by decide⟩,⟨465771, by decide⟩,⟨465781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71224_465782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71224 ⟨465782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71224
    ⟨465782, by decide⟩ (by decide) (![⟨465705, by decide⟩,⟨465747, by decide⟩,⟨465771, by decide⟩,⟨465781, by decide⟩]) unmarked_context_12_71224_465782 node_context_12_71224_465782
  intro a
  fin_cases a
  · exact context_13_284896_465705
  · exact context_13_284897_465747
  · exact context_13_284898_465771
  · exact context_13_284899_465781

theorem selected_cut_18176 : selected 8 ⟨465791, by decide⟩
    (prefixPartial 13 284900) = some ⟨13, 2, 0, 465791, 284900, 341, 16384⟩ := by
  decide +kernel

theorem context_13_284900_465791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284900 ⟨465791, by decide⟩ :=
  accepted_of_selected 13 284900 ⟨465791, by decide⟩ ⟨13, 2, 0, 465791, 284900, 341, 16384⟩
    (by decide) selected_cut_18176

theorem selected_cut_18177 : selected 8 ⟨465818, by decide⟩
    (prefixPartial 13 284901) = some ⟨13, 2, 0, 465818, 284901, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_284901_465818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284901 ⟨465818, by decide⟩ :=
  accepted_of_selected 13 284901 ⟨465818, by decide⟩ ⟨13, 2, 0, 465818, 284901, 2021, 16384⟩
    (by decide) selected_cut_18177

theorem selected_cut_18178 : selected 8 ⟨465837, by decide⟩
    (prefixPartial 13 284902) = some ⟨13, 2, 0, 465837, 284902, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_284902_465837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284902 ⟨465837, by decide⟩ :=
  accepted_of_selected 13 284902 ⟨465837, by decide⟩ ⟨13, 2, 0, 465837, 284902, 1245, 16384⟩
    (by decide) selected_cut_18178

theorem selected_cut_18179 : selected 8 ⟨465844, by decide⟩
    (prefixPartial 13 284903) = some ⟨13, 2, 0, 465844, 284903, 885, 16384⟩ := by
  decide +kernel

theorem context_13_284903_465844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284903 ⟨465844, by decide⟩ :=
  accepted_of_selected 13 284903 ⟨465844, by decide⟩ ⟨13, 2, 0, 465844, 284903, 885, 16384⟩
    (by decide) selected_cut_18179

theorem unmarked_context_12_71225_465845 : frontier 9 ⟨465845, by decide⟩
    (prefixCache 12 71225) (prefixPartial 12 71225) = false := by
  decide +kernel

theorem node_context_12_71225_465845 : EJMOriginalGlobalDAGData.nodes 9 ⟨465845, by decide⟩ =
    .split (coordinate 12) (![⟨465791, by decide⟩,⟨465818, by decide⟩,⟨465837, by decide⟩,⟨465844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71225_465845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71225 ⟨465845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71225
    ⟨465845, by decide⟩ (by decide) (![⟨465791, by decide⟩,⟨465818, by decide⟩,⟨465837, by decide⟩,⟨465844, by decide⟩]) unmarked_context_12_71225_465845 node_context_12_71225_465845
  intro a
  fin_cases a
  · exact context_13_284900_465791
  · exact context_13_284901_465818
  · exact context_13_284902_465837
  · exact context_13_284903_465844

theorem selected_cut_18180 : selected 8 ⟨465852, by decide⟩
    (prefixPartial 13 284904) = some ⟨13, 2, 0, 465852, 284904, 549, 16384⟩ := by
  decide +kernel

theorem context_13_284904_465852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284904 ⟨465852, by decide⟩ :=
  accepted_of_selected 13 284904 ⟨465852, by decide⟩ ⟨13, 2, 0, 465852, 284904, 549, 16384⟩
    (by decide) selected_cut_18180

theorem selected_cut_18181 : selected 8 ⟨465921, by decide⟩
    (prefixPartial 13 284905) = some ⟨13, 2, 0, 465921, 284905, 3849, 16384⟩ := by
  decide +kernel

theorem context_13_284905_465921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284905 ⟨465921, by decide⟩ :=
  accepted_of_selected 13 284905 ⟨465921, by decide⟩ ⟨13, 2, 0, 465921, 284905, 3849, 16384⟩
    (by decide) selected_cut_18181

theorem selected_cut_18182 : selected 8 ⟨465945, by decide⟩
    (prefixPartial 13 284906) = some ⟨13, 2, 0, 465945, 284906, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_284906_465945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284906 ⟨465945, by decide⟩ :=
  accepted_of_selected 13 284906 ⟨465945, by decide⟩ ⟨13, 2, 0, 465945, 284906, 2089, 16384⟩
    (by decide) selected_cut_18182

theorem selected_cut_18183 : selected 8 ⟨465968, by decide⟩
    (prefixPartial 13 284907) = some ⟨13, 2, 0, 465968, 284907, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_284907_465968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284907 ⟨465968, by decide⟩ :=
  accepted_of_selected 13 284907 ⟨465968, by decide⟩ ⟨13, 2, 0, 465968, 284907, 1329, 16384⟩
    (by decide) selected_cut_18183

theorem unmarked_context_12_71226_465969 : frontier 9 ⟨465969, by decide⟩
    (prefixCache 12 71226) (prefixPartial 12 71226) = false := by
  decide +kernel

theorem node_context_12_71226_465969 : EJMOriginalGlobalDAGData.nodes 9 ⟨465969, by decide⟩ =
    .split (coordinate 12) (![⟨465852, by decide⟩,⟨465921, by decide⟩,⟨465945, by decide⟩,⟨465968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71226_465969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71226 ⟨465969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71226
    ⟨465969, by decide⟩ (by decide) (![⟨465852, by decide⟩,⟨465921, by decide⟩,⟨465945, by decide⟩,⟨465968, by decide⟩]) unmarked_context_12_71226_465969 node_context_12_71226_465969
  intro a
  fin_cases a
  · exact context_13_284904_465852
  · exact context_13_284905_465921
  · exact context_13_284906_465945
  · exact context_13_284907_465968

theorem selected_cut_18184 : selected 8 ⟨465977, by decide⟩
    (prefixPartial 13 284908) = some ⟨13, 2, 0, 465977, 284908, 293, 16384⟩ := by
  decide +kernel

theorem context_13_284908_465977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284908 ⟨465977, by decide⟩ :=
  accepted_of_selected 13 284908 ⟨465977, by decide⟩ ⟨13, 2, 0, 465977, 284908, 293, 16384⟩
    (by decide) selected_cut_18184

theorem selected_cut_18185 : selected 8 ⟨466015, by decide⟩
    (prefixPartial 13 284909) = some ⟨13, 2, 0, 466015, 284909, 2797, 16384⟩ := by
  decide +kernel

theorem context_13_284909_466015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284909 ⟨466015, by decide⟩ :=
  accepted_of_selected 13 284909 ⟨466015, by decide⟩ ⟨13, 2, 0, 466015, 284909, 2797, 16384⟩
    (by decide) selected_cut_18185

theorem selected_cut_18186 : selected 8 ⟨466034, by decide⟩
    (prefixPartial 13 284910) = some ⟨13, 2, 0, 466034, 284910, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_284910_466034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284910 ⟨466034, by decide⟩ :=
  accepted_of_selected 13 284910 ⟨466034, by decide⟩ ⟨13, 2, 0, 466034, 284910, 1461, 16384⟩
    (by decide) selected_cut_18186

theorem selected_cut_18187 : selected 8 ⟨466039, by decide⟩
    (prefixPartial 13 284911) = some ⟨13, 2, 0, 466039, 284911, 853, 16384⟩ := by
  decide +kernel

theorem context_13_284911_466039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284911 ⟨466039, by decide⟩ :=
  accepted_of_selected 13 284911 ⟨466039, by decide⟩ ⟨13, 2, 0, 466039, 284911, 853, 16384⟩
    (by decide) selected_cut_18187

theorem unmarked_context_12_71227_466040 : frontier 9 ⟨466040, by decide⟩
    (prefixCache 12 71227) (prefixPartial 12 71227) = false := by
  decide +kernel

theorem node_context_12_71227_466040 : EJMOriginalGlobalDAGData.nodes 9 ⟨466040, by decide⟩ =
    .split (coordinate 12) (![⟨465977, by decide⟩,⟨466015, by decide⟩,⟨466034, by decide⟩,⟨466039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71227_466040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71227 ⟨466040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71227
    ⟨466040, by decide⟩ (by decide) (![⟨465977, by decide⟩,⟨466015, by decide⟩,⟨466034, by decide⟩,⟨466039, by decide⟩]) unmarked_context_12_71227_466040 node_context_12_71227_466040
  intro a
  fin_cases a
  · exact context_13_284908_465977
  · exact context_13_284909_466015
  · exact context_13_284910_466034
  · exact context_13_284911_466039

theorem unmarked_context_11_17806_466041 : frontier 10 ⟨466041, by decide⟩
    (prefixCache 11 17806) (prefixPartial 11 17806) = false := by
  decide +kernel

theorem node_context_11_17806_466041 : EJMOriginalGlobalDAGData.nodes 10 ⟨466041, by decide⟩ =
    .split (coordinate 11) (![⟨465782, by decide⟩,⟨465845, by decide⟩,⟨465969, by decide⟩,⟨466040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17806_466041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17806 ⟨466041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17806
    ⟨466041, by decide⟩ (by decide) (![⟨465782, by decide⟩,⟨465845, by decide⟩,⟨465969, by decide⟩,⟨466040, by decide⟩]) unmarked_context_11_17806_466041 node_context_11_17806_466041
  intro a
  fin_cases a
  · exact context_12_71224_465782
  · exact context_12_71225_465845
  · exact context_12_71226_465969
  · exact context_12_71227_466040

theorem selected_cut_18188 : selected 8 ⟨466048, by decide⟩
    (prefixPartial 13 284912) = some ⟨13, 2, 0, 466048, 284912, 277, 16384⟩ := by
  decide +kernel

theorem context_13_284912_466048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284912 ⟨466048, by decide⟩ :=
  accepted_of_selected 13 284912 ⟨466048, by decide⟩ ⟨13, 2, 0, 466048, 284912, 277, 16384⟩
    (by decide) selected_cut_18188

theorem selected_cut_18189 : selected 8 ⟨466108, by decide⟩
    (prefixPartial 13 284913) = some ⟨13, 2, 0, 466108, 284913, 3469, 16384⟩ := by
  decide +kernel

theorem context_13_284913_466108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284913 ⟨466108, by decide⟩ :=
  accepted_of_selected 13 284913 ⟨466108, by decide⟩ ⟨13, 2, 0, 466108, 284913, 3469, 16384⟩
    (by decide) selected_cut_18189

theorem selected_cut_18190 : selected 8 ⟨466130, by decide⟩
    (prefixPartial 13 284914) = some ⟨13, 2, 0, 466130, 284914, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_284914_466130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284914 ⟨466130, by decide⟩ :=
  accepted_of_selected 13 284914 ⟨466130, by decide⟩ ⟨13, 2, 0, 466130, 284914, 1861, 16384⟩
    (by decide) selected_cut_18190

theorem selected_cut_18191 : selected 8 ⟨466136, by decide⟩
    (prefixPartial 13 284915) = some ⟨13, 2, 0, 466136, 284915, 897, 16384⟩ := by
  decide +kernel

theorem context_13_284915_466136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284915 ⟨466136, by decide⟩ :=
  accepted_of_selected 13 284915 ⟨466136, by decide⟩ ⟨13, 2, 0, 466136, 284915, 897, 16384⟩
    (by decide) selected_cut_18191

theorem unmarked_context_12_71228_466137 : frontier 9 ⟨466137, by decide⟩
    (prefixCache 12 71228) (prefixPartial 12 71228) = false := by
  decide +kernel

theorem node_context_12_71228_466137 : EJMOriginalGlobalDAGData.nodes 9 ⟨466137, by decide⟩ =
    .split (coordinate 12) (![⟨466048, by decide⟩,⟨466108, by decide⟩,⟨466130, by decide⟩,⟨466136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71228_466137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71228 ⟨466137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71228
    ⟨466137, by decide⟩ (by decide) (![⟨466048, by decide⟩,⟨466108, by decide⟩,⟨466130, by decide⟩,⟨466136, by decide⟩]) unmarked_context_12_71228_466137 node_context_12_71228_466137
  intro a
  fin_cases a
  · exact context_13_284912_466048
  · exact context_13_284913_466108
  · exact context_13_284914_466130
  · exact context_13_284915_466136

theorem selected_cut_18192 : selected 8 ⟨466142, by decide⟩
    (prefixPartial 13 284916) = some ⟨13, 2, 0, 466142, 284916, 177, 16384⟩ := by
  decide +kernel

theorem context_13_284916_466142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284916 ⟨466142, by decide⟩ :=
  accepted_of_selected 13 284916 ⟨466142, by decide⟩ ⟨13, 2, 0, 466142, 284916, 177, 16384⟩
    (by decide) selected_cut_18192

theorem selected_cut_18193 : selected 8 ⟨466172, by decide⟩
    (prefixPartial 13 284917) = some ⟨13, 2, 0, 466172, 284917, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_284917_466172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284917 ⟨466172, by decide⟩ :=
  accepted_of_selected 13 284917 ⟨466172, by decide⟩ ⟨13, 2, 0, 466172, 284917, 2145, 16384⟩
    (by decide) selected_cut_18193

theorem selected_cut_18194 : selected 8 ⟨466186, by decide⟩
    (prefixPartial 13 284918) = some ⟨13, 2, 0, 466186, 284918, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_284918_466186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284918 ⟨466186, by decide⟩ :=
  accepted_of_selected 13 284918 ⟨466186, by decide⟩ ⟨13, 2, 0, 466186, 284918, 1209, 16384⟩
    (by decide) selected_cut_18194

theorem selected_cut_18195 : selected 8 ⟨466192, by decide⟩
    (prefixPartial 13 284919) = some ⟨13, 2, 0, 466192, 284919, 733, 16384⟩ := by
  decide +kernel

theorem context_13_284919_466192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284919 ⟨466192, by decide⟩ :=
  accepted_of_selected 13 284919 ⟨466192, by decide⟩ ⟨13, 2, 0, 466192, 284919, 733, 16384⟩
    (by decide) selected_cut_18195

theorem unmarked_context_12_71229_466193 : frontier 9 ⟨466193, by decide⟩
    (prefixCache 12 71229) (prefixPartial 12 71229) = false := by
  decide +kernel

theorem node_context_12_71229_466193 : EJMOriginalGlobalDAGData.nodes 9 ⟨466193, by decide⟩ =
    .split (coordinate 12) (![⟨466142, by decide⟩,⟨466172, by decide⟩,⟨466186, by decide⟩,⟨466192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71229_466193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71229 ⟨466193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71229
    ⟨466193, by decide⟩ (by decide) (![⟨466142, by decide⟩,⟨466172, by decide⟩,⟨466186, by decide⟩,⟨466192, by decide⟩]) unmarked_context_12_71229_466193 node_context_12_71229_466193
  intro a
  fin_cases a
  · exact context_13_284916_466142
  · exact context_13_284917_466172
  · exact context_13_284918_466186
  · exact context_13_284919_466192

theorem selected_cut_18196 : selected 8 ⟨466196, by decide⟩
    (prefixPartial 13 284920) = some ⟨13, 2, 0, 466196, 284920, 109, 16384⟩ := by
  decide +kernel

theorem context_13_284920_466196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284920 ⟨466196, by decide⟩ :=
  accepted_of_selected 13 284920 ⟨466196, by decide⟩ ⟨13, 2, 0, 466196, 284920, 109, 16384⟩
    (by decide) selected_cut_18196

theorem selected_cut_18197 : selected 8 ⟨466226, by decide⟩
    (prefixPartial 13 284921) = some ⟨13, 2, 0, 466226, 284921, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_284921_466226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284921 ⟨466226, by decide⟩ :=
  accepted_of_selected 13 284921 ⟨466226, by decide⟩ ⟨13, 2, 0, 466226, 284921, 2561, 16384⟩
    (by decide) selected_cut_18197

theorem selected_cut_18198 : selected 8 ⟨466244, by decide⟩
    (prefixPartial 13 284922) = some ⟨13, 2, 0, 466244, 284922, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_284922_466244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284922 ⟨466244, by decide⟩ :=
  accepted_of_selected 13 284922 ⟨466244, by decide⟩ ⟨13, 2, 0, 466244, 284922, 1261, 16384⟩
    (by decide) selected_cut_18198

theorem selected_cut_18199 : selected 8 ⟨466250, by decide⟩
    (prefixPartial 13 284923) = some ⟨13, 2, 0, 466250, 284923, 749, 16384⟩ := by
  decide +kernel

theorem context_13_284923_466250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284923 ⟨466250, by decide⟩ :=
  accepted_of_selected 13 284923 ⟨466250, by decide⟩ ⟨13, 2, 0, 466250, 284923, 749, 16384⟩
    (by decide) selected_cut_18199

theorem unmarked_context_12_71230_466251 : frontier 9 ⟨466251, by decide⟩
    (prefixCache 12 71230) (prefixPartial 12 71230) = false := by
  decide +kernel

theorem node_context_12_71230_466251 : EJMOriginalGlobalDAGData.nodes 9 ⟨466251, by decide⟩ =
    .split (coordinate 12) (![⟨466196, by decide⟩,⟨466226, by decide⟩,⟨466244, by decide⟩,⟨466250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71230_466251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71230 ⟨466251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71230
    ⟨466251, by decide⟩ (by decide) (![⟨466196, by decide⟩,⟨466226, by decide⟩,⟨466244, by decide⟩,⟨466250, by decide⟩]) unmarked_context_12_71230_466251 node_context_12_71230_466251
  intro a
  fin_cases a
  · exact context_13_284920_466196
  · exact context_13_284921_466226
  · exact context_13_284922_466244
  · exact context_13_284923_466250

theorem selected_cut_18200 : selected 8 ⟨466255, by decide⟩
    (prefixPartial 13 284924) = some ⟨13, 2, 0, 466255, 284924, 81, 16384⟩ := by
  decide +kernel

theorem context_13_284924_466255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284924 ⟨466255, by decide⟩ :=
  accepted_of_selected 13 284924 ⟨466255, by decide⟩ ⟨13, 2, 0, 466255, 284924, 81, 16384⟩
    (by decide) selected_cut_18200

theorem selected_cut_18201 : selected 8 ⟨466291, by decide⟩
    (prefixPartial 13 284925) = some ⟨13, 2, 0, 466291, 284925, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_284925_466291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284925 ⟨466291, by decide⟩ :=
  accepted_of_selected 13 284925 ⟨466291, by decide⟩ ⟨13, 2, 0, 466291, 284925, 2749, 16384⟩
    (by decide) selected_cut_18201

theorem selected_cut_18202 : selected 8 ⟨466308, by decide⟩
    (prefixPartial 13 284926) = some ⟨13, 2, 0, 466308, 284926, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_284926_466308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284926 ⟨466308, by decide⟩ :=
  accepted_of_selected 13 284926 ⟨466308, by decide⟩ ⟨13, 2, 0, 466308, 284926, 1581, 16384⟩
    (by decide) selected_cut_18202

theorem selected_cut_18203 : selected 8 ⟨466313, by decide⟩
    (prefixPartial 13 284927) = some ⟨13, 2, 0, 466313, 284927, 693, 16384⟩ := by
  decide +kernel

theorem context_13_284927_466313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284927 ⟨466313, by decide⟩ :=
  accepted_of_selected 13 284927 ⟨466313, by decide⟩ ⟨13, 2, 0, 466313, 284927, 693, 16384⟩
    (by decide) selected_cut_18203

theorem unmarked_context_12_71231_466314 : frontier 9 ⟨466314, by decide⟩
    (prefixCache 12 71231) (prefixPartial 12 71231) = false := by
  decide +kernel

theorem node_context_12_71231_466314 : EJMOriginalGlobalDAGData.nodes 9 ⟨466314, by decide⟩ =
    .split (coordinate 12) (![⟨466255, by decide⟩,⟨466291, by decide⟩,⟨466308, by decide⟩,⟨466313, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71231_466314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71231 ⟨466314, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71231
    ⟨466314, by decide⟩ (by decide) (![⟨466255, by decide⟩,⟨466291, by decide⟩,⟨466308, by decide⟩,⟨466313, by decide⟩]) unmarked_context_12_71231_466314 node_context_12_71231_466314
  intro a
  fin_cases a
  · exact context_13_284924_466255
  · exact context_13_284925_466291
  · exact context_13_284926_466308
  · exact context_13_284927_466313

theorem unmarked_context_11_17807_466315 : frontier 10 ⟨466315, by decide⟩
    (prefixCache 11 17807) (prefixPartial 11 17807) = false := by
  decide +kernel

theorem node_context_11_17807_466315 : EJMOriginalGlobalDAGData.nodes 10 ⟨466315, by decide⟩ =
    .split (coordinate 11) (![⟨466137, by decide⟩,⟨466193, by decide⟩,⟨466251, by decide⟩,⟨466314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17807_466315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17807 ⟨466315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17807
    ⟨466315, by decide⟩ (by decide) (![⟨466137, by decide⟩,⟨466193, by decide⟩,⟨466251, by decide⟩,⟨466314, by decide⟩]) unmarked_context_11_17807_466315 node_context_11_17807_466315
  intro a
  fin_cases a
  · exact context_12_71228_466137
  · exact context_12_71229_466193
  · exact context_12_71230_466251
  · exact context_12_71231_466314

theorem unmarked_context_10_4451_466316 : frontier 11 ⟨466316, by decide⟩
    (prefixCache 10 4451) (prefixPartial 10 4451) = false := by
  decide +kernel

theorem node_context_10_4451_466316 : EJMOriginalGlobalDAGData.nodes 11 ⟨466316, by decide⟩ =
    .split (coordinate 10) (![⟨465415, by decide⟩,⟨465697, by decide⟩,⟨466041, by decide⟩,⟨466315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4451_466316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4451 ⟨466316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4451
    ⟨466316, by decide⟩ (by decide) (![⟨465415, by decide⟩,⟨465697, by decide⟩,⟨466041, by decide⟩,⟨466315, by decide⟩]) unmarked_context_10_4451_466316 node_context_10_4451_466316
  intro a
  fin_cases a
  · exact context_11_17804_465415
  · exact context_11_17805_465697
  · exact context_11_17806_466041
  · exact context_11_17807_466315

theorem unmarked_context_9_1112_466317 : frontier 12 ⟨466317, by decide⟩
    (prefixCache 9 1112) (prefixPartial 9 1112) = false := by
  decide +kernel

theorem node_context_9_1112_466317 : EJMOriginalGlobalDAGData.nodes 12 ⟨466317, by decide⟩ =
    .split (coordinate 9) (![⟨462725, by decide⟩,⟨464100, by decide⟩,⟨465197, by decide⟩,⟨466316, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1112_466317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1112 ⟨466317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1112
    ⟨466317, by decide⟩ (by decide) (![⟨462725, by decide⟩,⟨464100, by decide⟩,⟨465197, by decide⟩,⟨466316, by decide⟩]) unmarked_context_9_1112_466317 node_context_9_1112_466317
  intro a
  fin_cases a
  · exact context_10_4448_462725
  · exact context_10_4449_464100
  · exact context_10_4450_465197
  · exact context_10_4451_466316

theorem selected_cut_18204 : selected 9 ⟨466361, by decide⟩
    (prefixPartial 12 71232) = some ⟨12, 2, 0, 466361, 71232, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_71232_466361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71232 ⟨466361, by decide⟩ :=
  accepted_of_selected 12 71232 ⟨466361, by decide⟩ ⟨12, 2, 0, 466361, 71232, 3229, 65536⟩
    (by decide) selected_cut_18204

theorem selected_cut_18205 : selected 9 ⟨466416, by decide⟩
    (prefixPartial 12 71233) = some ⟨12, 2, 0, 466416, 71233, 4033, 65536⟩ := by
  decide +kernel

theorem context_12_71233_466416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71233 ⟨466416, by decide⟩ :=
  accepted_of_selected 12 71233 ⟨466416, by decide⟩ ⟨12, 2, 0, 466416, 71233, 4033, 65536⟩
    (by decide) selected_cut_18205

theorem selected_cut_18206 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 284936) = some ⟨13, 1, 0, 3444, 284936, 1, 16384⟩ := by
  decide +kernel

theorem context_13_284936_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284936 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 284936 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 284936, 1, 16384⟩
    (by decide) selected_cut_18206

theorem selected_cut_18207 : selected 8 ⟨466445, by decide⟩
    (prefixPartial 13 284937) = some ⟨13, 2, 0, 466445, 284937, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_284937_466445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284937 ⟨466445, by decide⟩ :=
  accepted_of_selected 13 284937 ⟨466445, by decide⟩ ⟨13, 2, 0, 466445, 284937, 2301, 16384⟩
    (by decide) selected_cut_18207

theorem selected_cut_18208 : selected 8 ⟨466461, by decide⟩
    (prefixPartial 13 284938) = some ⟨13, 2, 0, 466461, 284938, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_284938_466461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284938 ⟨466461, by decide⟩ :=
  accepted_of_selected 13 284938 ⟨466461, by decide⟩ ⟨13, 2, 0, 466461, 284938, 1237, 16384⟩
    (by decide) selected_cut_18208

theorem selected_cut_18209 : selected 8 ⟨466470, by decide⟩
    (prefixPartial 13 284939) = some ⟨13, 2, 0, 466470, 284939, 757, 16384⟩ := by
  decide +kernel

theorem context_13_284939_466470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284939 ⟨466470, by decide⟩ :=
  accepted_of_selected 13 284939 ⟨466470, by decide⟩ ⟨13, 2, 0, 466470, 284939, 757, 16384⟩
    (by decide) selected_cut_18209

theorem unmarked_context_12_71234_466471 : frontier 9 ⟨466471, by decide⟩
    (prefixCache 12 71234) (prefixPartial 12 71234) = false := by
  decide +kernel

theorem node_context_12_71234_466471 : EJMOriginalGlobalDAGData.nodes 9 ⟨466471, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨466445, by decide⟩,⟨466461, by decide⟩,⟨466470, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71234_466471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71234 ⟨466471, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71234
    ⟨466471, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨466445, by decide⟩,⟨466461, by decide⟩,⟨466470, by decide⟩]) unmarked_context_12_71234_466471 node_context_12_71234_466471
  intro a
  fin_cases a
  · exact context_13_284936_3444
  · exact context_13_284937_466445
  · exact context_13_284938_466461
  · exact context_13_284939_466470

theorem selected_cut_18210 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 284940) = some ⟨13, 1, 0, 3444, 284940, 1, 16384⟩ := by
  decide +kernel

theorem context_13_284940_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284940 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 284940 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 284940, 1, 16384⟩
    (by decide) selected_cut_18210

theorem selected_cut_18211 : selected 8 ⟨466505, by decide⟩
    (prefixPartial 13 284941) = some ⟨13, 2, 0, 466505, 284941, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_284941_466505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284941 ⟨466505, by decide⟩ :=
  accepted_of_selected 13 284941 ⟨466505, by decide⟩ ⟨13, 2, 0, 466505, 284941, 2437, 16384⟩
    (by decide) selected_cut_18211

theorem selected_cut_18212 : selected 8 ⟨466524, by decide⟩
    (prefixPartial 13 284942) = some ⟨13, 2, 0, 466524, 284942, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_284942_466524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284942 ⟨466524, by decide⟩ :=
  accepted_of_selected 13 284942 ⟨466524, by decide⟩ ⟨13, 2, 0, 466524, 284942, 1449, 16384⟩
    (by decide) selected_cut_18212

theorem selected_cut_18213 : selected 8 ⟨466529, by decide⟩
    (prefixPartial 13 284943) = some ⟨13, 2, 0, 466529, 284943, 649, 16384⟩ := by
  decide +kernel

theorem context_13_284943_466529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284943 ⟨466529, by decide⟩ :=
  accepted_of_selected 13 284943 ⟨466529, by decide⟩ ⟨13, 2, 0, 466529, 284943, 649, 16384⟩
    (by decide) selected_cut_18213

theorem unmarked_context_12_71235_466530 : frontier 9 ⟨466530, by decide⟩
    (prefixCache 12 71235) (prefixPartial 12 71235) = false := by
  decide +kernel

theorem node_context_12_71235_466530 : EJMOriginalGlobalDAGData.nodes 9 ⟨466530, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨466505, by decide⟩,⟨466524, by decide⟩,⟨466529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71235_466530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71235 ⟨466530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71235
    ⟨466530, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨466505, by decide⟩,⟨466524, by decide⟩,⟨466529, by decide⟩]) unmarked_context_12_71235_466530 node_context_12_71235_466530
  intro a
  fin_cases a
  · exact context_13_284940_3444
  · exact context_13_284941_466505
  · exact context_13_284942_466524
  · exact context_13_284943_466529

theorem unmarked_context_11_17808_466531 : frontier 10 ⟨466531, by decide⟩
    (prefixCache 11 17808) (prefixPartial 11 17808) = false := by
  decide +kernel

theorem node_context_11_17808_466531 : EJMOriginalGlobalDAGData.nodes 10 ⟨466531, by decide⟩ =
    .split (coordinate 11) (![⟨466361, by decide⟩,⟨466416, by decide⟩,⟨466471, by decide⟩,⟨466530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17808_466531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17808 ⟨466531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17808
    ⟨466531, by decide⟩ (by decide) (![⟨466361, by decide⟩,⟨466416, by decide⟩,⟨466471, by decide⟩,⟨466530, by decide⟩]) unmarked_context_11_17808_466531 node_context_11_17808_466531
  intro a
  fin_cases a
  · exact context_12_71232_466361
  · exact context_12_71233_466416
  · exact context_12_71234_466471
  · exact context_12_71235_466530

theorem selected_cut_18214 : selected 9 ⟨466577, by decide⟩
    (prefixPartial 12 71236) = some ⟨12, 2, 0, 466577, 71236, 3741, 65536⟩ := by
  decide +kernel

theorem context_12_71236_466577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71236 ⟨466577, by decide⟩ :=
  accepted_of_selected 12 71236 ⟨466577, by decide⟩ ⟨12, 2, 0, 466577, 71236, 3741, 65536⟩
    (by decide) selected_cut_18214

theorem selected_cut_18215 : selected 9 ⟨466619, by decide⟩
    (prefixPartial 12 71237) = some ⟨12, 2, 0, 466619, 71237, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_71237_466619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71237 ⟨466619, by decide⟩ :=
  accepted_of_selected 12 71237 ⟨466619, by decide⟩ ⟨12, 2, 0, 466619, 71237, 3557, 65536⟩
    (by decide) selected_cut_18215

theorem selected_cut_18216 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 284952) = some ⟨13, 1, 0, 3444, 284952, 1, 16384⟩ := by
  decide +kernel

theorem context_13_284952_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284952 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 284952 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 284952, 1, 16384⟩
    (by decide) selected_cut_18216

theorem selected_cut_18217 : selected 8 ⟨466647, by decide⟩
    (prefixPartial 13 284953) = some ⟨13, 2, 0, 466647, 284953, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_284953_466647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284953 ⟨466647, by decide⟩ :=
  accepted_of_selected 13 284953 ⟨466647, by decide⟩ ⟨13, 2, 0, 466647, 284953, 2045, 16384⟩
    (by decide) selected_cut_18217

theorem selected_cut_18218 : selected 8 ⟨466669, by decide⟩
    (prefixPartial 13 284954) = some ⟨13, 2, 0, 466669, 284954, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_284954_466669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284954 ⟨466669, by decide⟩ :=
  accepted_of_selected 13 284954 ⟨466669, by decide⟩ ⟨13, 2, 0, 466669, 284954, 1361, 16384⟩
    (by decide) selected_cut_18218

theorem selected_cut_18219 : selected 8 ⟨466677, by decide⟩
    (prefixPartial 13 284955) = some ⟨13, 2, 0, 466677, 284955, 757, 16384⟩ := by
  decide +kernel

theorem context_13_284955_466677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284955 ⟨466677, by decide⟩ :=
  accepted_of_selected 13 284955 ⟨466677, by decide⟩ ⟨13, 2, 0, 466677, 284955, 757, 16384⟩
    (by decide) selected_cut_18219

theorem unmarked_context_12_71238_466678 : frontier 9 ⟨466678, by decide⟩
    (prefixCache 12 71238) (prefixPartial 12 71238) = false := by
  decide +kernel

theorem node_context_12_71238_466678 : EJMOriginalGlobalDAGData.nodes 9 ⟨466678, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨466647, by decide⟩,⟨466669, by decide⟩,⟨466677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71238_466678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71238 ⟨466678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71238
    ⟨466678, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨466647, by decide⟩,⟨466669, by decide⟩,⟨466677, by decide⟩]) unmarked_context_12_71238_466678 node_context_12_71238_466678
  intro a
  fin_cases a
  · exact context_13_284952_3444
  · exact context_13_284953_466647
  · exact context_13_284954_466669
  · exact context_13_284955_466677

theorem selected_cut_18220 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 284956) = some ⟨13, 1, 0, 3444, 284956, 1, 16384⟩ := by
  decide +kernel

theorem context_13_284956_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284956 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 284956 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 284956, 1, 16384⟩
    (by decide) selected_cut_18220

theorem selected_cut_18221 : selected 8 ⟨466709, by decide⟩
    (prefixPartial 13 284957) = some ⟨13, 2, 0, 466709, 284957, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_284957_466709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284957 ⟨466709, by decide⟩ :=
  accepted_of_selected 13 284957 ⟨466709, by decide⟩ ⟨13, 2, 0, 466709, 284957, 2149, 16384⟩
    (by decide) selected_cut_18221

theorem selected_cut_18222 : selected 8 ⟨466728, by decide⟩
    (prefixPartial 13 284958) = some ⟨13, 2, 0, 466728, 284958, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_284958_466728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284958 ⟨466728, by decide⟩ :=
  accepted_of_selected 13 284958 ⟨466728, by decide⟩ ⟨13, 2, 0, 466728, 284958, 1501, 16384⟩
    (by decide) selected_cut_18222

theorem selected_cut_18223 : selected 8 ⟨466732, by decide⟩
    (prefixPartial 13 284959) = some ⟨13, 2, 0, 466732, 284959, 677, 16384⟩ := by
  decide +kernel

theorem context_13_284959_466732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284959 ⟨466732, by decide⟩ :=
  accepted_of_selected 13 284959 ⟨466732, by decide⟩ ⟨13, 2, 0, 466732, 284959, 677, 16384⟩
    (by decide) selected_cut_18223

theorem unmarked_context_12_71239_466733 : frontier 9 ⟨466733, by decide⟩
    (prefixCache 12 71239) (prefixPartial 12 71239) = false := by
  decide +kernel

theorem node_context_12_71239_466733 : EJMOriginalGlobalDAGData.nodes 9 ⟨466733, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨466709, by decide⟩,⟨466728, by decide⟩,⟨466732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71239_466733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71239 ⟨466733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71239
    ⟨466733, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨466709, by decide⟩,⟨466728, by decide⟩,⟨466732, by decide⟩]) unmarked_context_12_71239_466733 node_context_12_71239_466733
  intro a
  fin_cases a
  · exact context_13_284956_3444
  · exact context_13_284957_466709
  · exact context_13_284958_466728
  · exact context_13_284959_466732

theorem unmarked_context_11_17809_466734 : frontier 10 ⟨466734, by decide⟩
    (prefixCache 11 17809) (prefixPartial 11 17809) = false := by
  decide +kernel

theorem node_context_11_17809_466734 : EJMOriginalGlobalDAGData.nodes 10 ⟨466734, by decide⟩ =
    .split (coordinate 11) (![⟨466577, by decide⟩,⟨466619, by decide⟩,⟨466678, by decide⟩,⟨466733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17809_466734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17809 ⟨466734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17809
    ⟨466734, by decide⟩ (by decide) (![⟨466577, by decide⟩,⟨466619, by decide⟩,⟨466678, by decide⟩,⟨466733, by decide⟩]) unmarked_context_11_17809_466734 node_context_11_17809_466734
  intro a
  fin_cases a
  · exact context_12_71236_466577
  · exact context_12_71237_466619
  · exact context_12_71238_466678
  · exact context_12_71239_466733

theorem selected_cut_18224 : selected 9 ⟨466773, by decide⟩
    (prefixPartial 12 71240) = some ⟨12, 2, 0, 466773, 71240, 3637, 65536⟩ := by
  decide +kernel

theorem context_12_71240_466773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71240 ⟨466773, by decide⟩ :=
  accepted_of_selected 12 71240 ⟨466773, by decide⟩ ⟨12, 2, 0, 466773, 71240, 3637, 65536⟩
    (by decide) selected_cut_18224

theorem selected_cut_18225 : selected 9 ⟨466818, by decide⟩
    (prefixPartial 12 71241) = some ⟨12, 2, 0, 466818, 71241, 3865, 65536⟩ := by
  decide +kernel

theorem context_12_71241_466818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71241 ⟨466818, by decide⟩ :=
  accepted_of_selected 12 71241 ⟨466818, by decide⟩ ⟨12, 2, 0, 466818, 71241, 3865, 65536⟩
    (by decide) selected_cut_18225

theorem selected_cut_18226 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 284968) = some ⟨13, 1, 0, 3444, 284968, 1, 16384⟩ := by
  decide +kernel

theorem context_13_284968_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284968 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 284968 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 284968, 1, 16384⟩
    (by decide) selected_cut_18226

theorem selected_cut_18227 : selected 8 ⟨466880, by decide⟩
    (prefixPartial 13 284969) = some ⟨13, 2, 0, 466880, 284969, 3249, 16384⟩ := by
  decide +kernel

theorem context_13_284969_466880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284969 ⟨466880, by decide⟩ :=
  accepted_of_selected 13 284969 ⟨466880, by decide⟩ ⟨13, 2, 0, 466880, 284969, 3249, 16384⟩
    (by decide) selected_cut_18227

theorem selected_cut_18228 : selected 8 ⟨466915, by decide⟩
    (prefixPartial 13 284970) = some ⟨13, 2, 0, 466915, 284970, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_284970_466915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284970 ⟨466915, by decide⟩ :=
  accepted_of_selected 13 284970 ⟨466915, by decide⟩ ⟨13, 2, 0, 466915, 284970, 2217, 16384⟩
    (by decide) selected_cut_18228

theorem selected_cut_18229 : selected 8 ⟨466924, by decide⟩
    (prefixPartial 13 284971) = some ⟨13, 2, 0, 466924, 284971, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_284971_466924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284971 ⟨466924, by decide⟩ :=
  accepted_of_selected 13 284971 ⟨466924, by decide⟩ ⟨13, 2, 0, 466924, 284971, 1145, 16384⟩
    (by decide) selected_cut_18229

theorem unmarked_context_12_71242_466925 : frontier 9 ⟨466925, by decide⟩
    (prefixCache 12 71242) (prefixPartial 12 71242) = false := by
  decide +kernel

theorem node_context_12_71242_466925 : EJMOriginalGlobalDAGData.nodes 9 ⟨466925, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨466880, by decide⟩,⟨466915, by decide⟩,⟨466924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71242_466925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71242 ⟨466925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71242
    ⟨466925, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨466880, by decide⟩,⟨466915, by decide⟩,⟨466924, by decide⟩]) unmarked_context_12_71242_466925 node_context_12_71242_466925
  intro a
  fin_cases a
  · exact context_13_284968_3444
  · exact context_13_284969_466880
  · exact context_13_284970_466915
  · exact context_13_284971_466924

theorem selected_cut_18230 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 284972) = some ⟨13, 1, 0, 3444, 284972, 1, 16384⟩ := by
  decide +kernel

theorem context_13_284972_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284972 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 284972 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 284972, 1, 16384⟩
    (by decide) selected_cut_18230

theorem selected_cut_18231 : selected 8 ⟨466957, by decide⟩
    (prefixPartial 13 284973) = some ⟨13, 2, 0, 466957, 284973, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_284973_466957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284973 ⟨466957, by decide⟩ :=
  accepted_of_selected 13 284973 ⟨466957, by decide⟩ ⟨13, 2, 0, 466957, 284973, 2301, 16384⟩
    (by decide) selected_cut_18231

theorem selected_cut_18232 : selected 8 ⟨466974, by decide⟩
    (prefixPartial 13 284974) = some ⟨13, 2, 0, 466974, 284974, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_284974_466974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284974 ⟨466974, by decide⟩ :=
  accepted_of_selected 13 284974 ⟨466974, by decide⟩ ⟨13, 2, 0, 466974, 284974, 1553, 16384⟩
    (by decide) selected_cut_18232

theorem selected_cut_18233 : selected 8 ⟨466981, by decide⟩
    (prefixPartial 13 284975) = some ⟨13, 2, 0, 466981, 284975, 693, 16384⟩ := by
  decide +kernel

theorem context_13_284975_466981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284975 ⟨466981, by decide⟩ :=
  accepted_of_selected 13 284975 ⟨466981, by decide⟩ ⟨13, 2, 0, 466981, 284975, 693, 16384⟩
    (by decide) selected_cut_18233

theorem unmarked_context_12_71243_466982 : frontier 9 ⟨466982, by decide⟩
    (prefixCache 12 71243) (prefixPartial 12 71243) = false := by
  decide +kernel

theorem node_context_12_71243_466982 : EJMOriginalGlobalDAGData.nodes 9 ⟨466982, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨466957, by decide⟩,⟨466974, by decide⟩,⟨466981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71243_466982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71243 ⟨466982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71243
    ⟨466982, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨466957, by decide⟩,⟨466974, by decide⟩,⟨466981, by decide⟩]) unmarked_context_12_71243_466982 node_context_12_71243_466982
  intro a
  fin_cases a
  · exact context_13_284972_3444
  · exact context_13_284973_466957
  · exact context_13_284974_466974
  · exact context_13_284975_466981

theorem unmarked_context_11_17810_466983 : frontier 10 ⟨466983, by decide⟩
    (prefixCache 11 17810) (prefixPartial 11 17810) = false := by
  decide +kernel

theorem node_context_11_17810_466983 : EJMOriginalGlobalDAGData.nodes 10 ⟨466983, by decide⟩ =
    .split (coordinate 11) (![⟨466773, by decide⟩,⟨466818, by decide⟩,⟨466925, by decide⟩,⟨466982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17810_466983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17810 ⟨466983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17810
    ⟨466983, by decide⟩ (by decide) (![⟨466773, by decide⟩,⟨466818, by decide⟩,⟨466925, by decide⟩,⟨466982, by decide⟩]) unmarked_context_11_17810_466983 node_context_11_17810_466983
  intro a
  fin_cases a
  · exact context_12_71240_466773
  · exact context_12_71241_466818
  · exact context_12_71242_466925
  · exact context_12_71243_466982

theorem selected_cut_18234 : selected 9 ⟨467029, by decide⟩
    (prefixPartial 12 71244) = some ⟨12, 2, 0, 467029, 71244, 4073, 65536⟩ := by
  decide +kernel

theorem context_12_71244_467029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71244 ⟨467029, by decide⟩ :=
  accepted_of_selected 12 71244 ⟨467029, by decide⟩ ⟨12, 2, 0, 467029, 71244, 4073, 65536⟩
    (by decide) selected_cut_18234

theorem selected_cut_18235 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 284980) = some ⟨13, 1, 0, 3444, 284980, 1, 16384⟩ := by
  decide +kernel

theorem context_13_284980_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284980 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 284980 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 284980, 1, 16384⟩
    (by decide) selected_cut_18235

theorem selected_cut_18236 : selected 8 ⟨467056, by decide⟩
    (prefixPartial 13 284981) = some ⟨13, 2, 0, 467056, 284981, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_284981_467056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284981 ⟨467056, by decide⟩ :=
  accepted_of_selected 13 284981 ⟨467056, by decide⟩ ⟨13, 2, 0, 467056, 284981, 1869, 16384⟩
    (by decide) selected_cut_18236

theorem selected_cut_18237 : selected 8 ⟨467074, by decide⟩
    (prefixPartial 13 284982) = some ⟨13, 2, 0, 467074, 284982, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_284982_467074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284982 ⟨467074, by decide⟩ :=
  accepted_of_selected 13 284982 ⟨467074, by decide⟩ ⟨13, 2, 0, 467074, 284982, 1417, 16384⟩
    (by decide) selected_cut_18237

theorem selected_cut_18238 : selected 8 ⟨467079, by decide⟩
    (prefixPartial 13 284983) = some ⟨13, 2, 0, 467079, 284983, 841, 16384⟩ := by
  decide +kernel

theorem context_13_284983_467079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284983 ⟨467079, by decide⟩ :=
  accepted_of_selected 13 284983 ⟨467079, by decide⟩ ⟨13, 2, 0, 467079, 284983, 841, 16384⟩
    (by decide) selected_cut_18238

theorem unmarked_context_12_71245_467080 : frontier 9 ⟨467080, by decide⟩
    (prefixCache 12 71245) (prefixPartial 12 71245) = false := by
  decide +kernel

theorem node_context_12_71245_467080 : EJMOriginalGlobalDAGData.nodes 9 ⟨467080, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨467056, by decide⟩,⟨467074, by decide⟩,⟨467079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71245_467080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71245 ⟨467080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71245
    ⟨467080, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨467056, by decide⟩,⟨467074, by decide⟩,⟨467079, by decide⟩]) unmarked_context_12_71245_467080 node_context_12_71245_467080
  intro a
  fin_cases a
  · exact context_13_284980_3444
  · exact context_13_284981_467056
  · exact context_13_284982_467074
  · exact context_13_284983_467079

theorem selected_cut_18239 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 284984) = some ⟨13, 1, 0, 3444, 284984, 1, 16384⟩ := by
  decide +kernel

theorem context_13_284984_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284984 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 284984 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 284984, 1, 16384⟩
    (by decide) selected_cut_18239

theorem selected_cut_18240 : selected 8 ⟨467106, by decide⟩
    (prefixPartial 13 284985) = some ⟨13, 2, 0, 467106, 284985, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_284985_467106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284985 ⟨467106, by decide⟩ :=
  accepted_of_selected 13 284985 ⟨467106, by decide⟩ ⟨13, 2, 0, 467106, 284985, 2277, 16384⟩
    (by decide) selected_cut_18240

theorem selected_cut_18241 : selected 8 ⟨467127, by decide⟩
    (prefixPartial 13 284986) = some ⟨13, 2, 0, 467127, 284986, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_284986_467127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284986 ⟨467127, by decide⟩ :=
  accepted_of_selected 13 284986 ⟨467127, by decide⟩ ⟨13, 2, 0, 467127, 284986, 1509, 16384⟩
    (by decide) selected_cut_18241

theorem selected_cut_18242 : selected 8 ⟨467135, by decide⟩
    (prefixPartial 13 284987) = some ⟨13, 2, 0, 467135, 284987, 885, 16384⟩ := by
  decide +kernel

theorem context_13_284987_467135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 284987 ⟨467135, by decide⟩ :=
  accepted_of_selected 13 284987 ⟨467135, by decide⟩ ⟨13, 2, 0, 467135, 284987, 885, 16384⟩
    (by decide) selected_cut_18242

theorem unmarked_context_12_71246_467136 : frontier 9 ⟨467136, by decide⟩
    (prefixCache 12 71246) (prefixPartial 12 71246) = false := by
  decide +kernel

theorem node_context_12_71246_467136 : EJMOriginalGlobalDAGData.nodes 9 ⟨467136, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨467106, by decide⟩,⟨467127, by decide⟩,⟨467135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71246_467136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71246 ⟨467136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71246
    ⟨467136, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨467106, by decide⟩,⟨467127, by decide⟩,⟨467135, by decide⟩]) unmarked_context_12_71246_467136 node_context_12_71246_467136
  intro a
  fin_cases a
  · exact context_13_284984_3444
  · exact context_13_284985_467106
  · exact context_13_284986_467127
  · exact context_13_284987_467135

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
