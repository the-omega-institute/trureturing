/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover396
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_38115 : selected 9 ⟨1025246, by decide⟩
    (prefixPartial 12 300870) = some ⟨12, 2, 0, 1025246, 300870, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_300870_1025246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300870 ⟨1025246, by decide⟩ :=
  accepted_of_selected 12 300870 ⟨1025246, by decide⟩ ⟨12, 2, 0, 1025246, 300870, 2489, 65536⟩
    (by decide) selected_cut_38115

theorem selected_cut_38116 : selected 9 ⟨1025284, by decide⟩
    (prefixPartial 12 300871) = some ⟨12, 2, 0, 1025284, 300871, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_300871_1025284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300871 ⟨1025284, by decide⟩ :=
  accepted_of_selected 12 300871 ⟨1025284, by decide⟩ ⟨12, 2, 0, 1025284, 300871, 2397, 65536⟩
    (by decide) selected_cut_38116

theorem unmarked_context_11_75217_1025285 : frontier 10 ⟨1025285, by decide⟩
    (prefixCache 11 75217) (prefixPartial 11 75217) = false := by
  decide +kernel

theorem node_context_11_75217_1025285 : EJMOriginalGlobalDAGData.nodes 10 ⟨1025285, by decide⟩ =
    .split (coordinate 11) (![⟨1025168, by decide⟩,⟨1025203, by decide⟩,⟨1025246, by decide⟩,⟨1025284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75217_1025285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75217 ⟨1025285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75217
    ⟨1025285, by decide⟩ (by decide) (![⟨1025168, by decide⟩,⟨1025203, by decide⟩,⟨1025246, by decide⟩,⟨1025284, by decide⟩]) unmarked_context_11_75217_1025285 node_context_11_75217_1025285
  intro a
  fin_cases a
  · exact context_12_300868_1025168
  · exact context_12_300869_1025203
  · exact context_12_300870_1025246
  · exact context_12_300871_1025284

theorem selected_cut_38117 : selected 9 ⟨1025361, by decide⟩
    (prefixPartial 12 300872) = some ⟨12, 2, 0, 1025361, 300872, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_300872_1025361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300872 ⟨1025361, by decide⟩ :=
  accepted_of_selected 12 300872 ⟨1025361, by decide⟩ ⟨12, 2, 0, 1025361, 300872, 3453, 65536⟩
    (by decide) selected_cut_38117

theorem selected_cut_38118 : selected 9 ⟨1025407, by decide⟩
    (prefixPartial 12 300873) = some ⟨12, 2, 0, 1025407, 300873, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_300873_1025407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300873 ⟨1025407, by decide⟩ :=
  accepted_of_selected 12 300873 ⟨1025407, by decide⟩ ⟨12, 2, 0, 1025407, 300873, 2677, 65536⟩
    (by decide) selected_cut_38118

theorem selected_cut_38119 : selected 9 ⟨1025445, by decide⟩
    (prefixPartial 12 300874) = some ⟨12, 2, 0, 1025445, 300874, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_300874_1025445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300874 ⟨1025445, by decide⟩ :=
  accepted_of_selected 12 300874 ⟨1025445, by decide⟩ ⟨12, 2, 0, 1025445, 300874, 2877, 65536⟩
    (by decide) selected_cut_38119

theorem selected_cut_38120 : selected 9 ⟨1025481, by decide⟩
    (prefixPartial 12 300875) = some ⟨12, 2, 0, 1025481, 300875, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_300875_1025481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300875 ⟨1025481, by decide⟩ :=
  accepted_of_selected 12 300875 ⟨1025481, by decide⟩ ⟨12, 2, 0, 1025481, 300875, 2845, 65536⟩
    (by decide) selected_cut_38120

theorem unmarked_context_11_75218_1025482 : frontier 10 ⟨1025482, by decide⟩
    (prefixCache 11 75218) (prefixPartial 11 75218) = false := by
  decide +kernel

theorem node_context_11_75218_1025482 : EJMOriginalGlobalDAGData.nodes 10 ⟨1025482, by decide⟩ =
    .split (coordinate 11) (![⟨1025361, by decide⟩,⟨1025407, by decide⟩,⟨1025445, by decide⟩,⟨1025481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75218_1025482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75218 ⟨1025482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75218
    ⟨1025482, by decide⟩ (by decide) (![⟨1025361, by decide⟩,⟨1025407, by decide⟩,⟨1025445, by decide⟩,⟨1025481, by decide⟩]) unmarked_context_11_75218_1025482 node_context_11_75218_1025482
  intro a
  fin_cases a
  · exact context_12_300872_1025361
  · exact context_12_300873_1025407
  · exact context_12_300874_1025445
  · exact context_12_300875_1025481

theorem selected_cut_38121 : selected 9 ⟨1025548, by decide⟩
    (prefixPartial 12 300876) = some ⟨12, 2, 0, 1025548, 300876, 3177, 65536⟩ := by
  decide +kernel

theorem context_12_300876_1025548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300876 ⟨1025548, by decide⟩ :=
  accepted_of_selected 12 300876 ⟨1025548, by decide⟩ ⟨12, 2, 0, 1025548, 300876, 3177, 65536⟩
    (by decide) selected_cut_38121

theorem selected_cut_38122 : selected 9 ⟨1025591, by decide⟩
    (prefixPartial 12 300877) = some ⟨12, 2, 0, 1025591, 300877, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_300877_1025591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300877 ⟨1025591, by decide⟩ :=
  accepted_of_selected 12 300877 ⟨1025591, by decide⟩ ⟨12, 2, 0, 1025591, 300877, 2521, 65536⟩
    (by decide) selected_cut_38122

theorem selected_cut_38123 : selected 9 ⟨1025638, by decide⟩
    (prefixPartial 12 300878) = some ⟨12, 2, 0, 1025638, 300878, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_300878_1025638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300878 ⟨1025638, by decide⟩ :=
  accepted_of_selected 12 300878 ⟨1025638, by decide⟩ ⟨12, 2, 0, 1025638, 300878, 2965, 65536⟩
    (by decide) selected_cut_38123

theorem selected_cut_38124 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 300879) = some ⟨12, 1, 0, 903806, 300879, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300879_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300879 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 300879 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 300879, 1, 65536⟩
    (by decide) selected_cut_38124

theorem unmarked_context_11_75219_1025639 : frontier 10 ⟨1025639, by decide⟩
    (prefixCache 11 75219) (prefixPartial 11 75219) = false := by
  decide +kernel

theorem node_context_11_75219_1025639 : EJMOriginalGlobalDAGData.nodes 10 ⟨1025639, by decide⟩ =
    .split (coordinate 11) (![⟨1025548, by decide⟩,⟨1025591, by decide⟩,⟨1025638, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75219_1025639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75219 ⟨1025639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75219
    ⟨1025639, by decide⟩ (by decide) (![⟨1025548, by decide⟩,⟨1025591, by decide⟩,⟨1025638, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75219_1025639 node_context_11_75219_1025639
  intro a
  fin_cases a
  · exact context_12_300876_1025548
  · exact context_12_300877_1025591
  · exact context_12_300878_1025638
  · exact context_12_300879_903806

theorem unmarked_context_10_18804_1025640 : frontier 11 ⟨1025640, by decide⟩
    (prefixCache 10 18804) (prefixPartial 10 18804) = false := by
  decide +kernel

theorem node_context_10_18804_1025640 : EJMOriginalGlobalDAGData.nodes 11 ⟨1025640, by decide⟩ =
    .split (coordinate 10) (![⟨1025108, by decide⟩,⟨1025285, by decide⟩,⟨1025482, by decide⟩,⟨1025639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18804_1025640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18804 ⟨1025640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18804
    ⟨1025640, by decide⟩ (by decide) (![⟨1025108, by decide⟩,⟨1025285, by decide⟩,⟨1025482, by decide⟩,⟨1025639, by decide⟩]) unmarked_context_10_18804_1025640 node_context_10_18804_1025640
  intro a
  fin_cases a
  · exact context_11_75216_1025108
  · exact context_11_75217_1025285
  · exact context_11_75218_1025482
  · exact context_11_75219_1025639

theorem selected_cut_38125 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18805) = some ⟨10, 1, 0, 893098, 18805, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18805_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18805 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18805 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18805, 1, 1048576⟩
    (by decide) selected_cut_38125

theorem selected_cut_38126 : selected 9 ⟨1025680, by decide⟩
    (prefixPartial 12 300896) = some ⟨12, 2, 0, 1025680, 300896, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_300896_1025680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300896 ⟨1025680, by decide⟩ :=
  accepted_of_selected 12 300896 ⟨1025680, by decide⟩ ⟨12, 2, 0, 1025680, 300896, 2429, 65536⟩
    (by decide) selected_cut_38126

theorem selected_cut_38127 : selected 9 ⟨1025710, by decide⟩
    (prefixPartial 12 300897) = some ⟨12, 2, 0, 1025710, 300897, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_300897_1025710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300897 ⟨1025710, by decide⟩ :=
  accepted_of_selected 12 300897 ⟨1025710, by decide⟩ ⟨12, 2, 0, 1025710, 300897, 2081, 65536⟩
    (by decide) selected_cut_38127

theorem selected_cut_38128 : selected 9 ⟨1025746, by decide⟩
    (prefixPartial 12 300898) = some ⟨12, 2, 0, 1025746, 300898, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_300898_1025746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300898 ⟨1025746, by decide⟩ :=
  accepted_of_selected 12 300898 ⟨1025746, by decide⟩ ⟨12, 2, 0, 1025746, 300898, 2349, 65536⟩
    (by decide) selected_cut_38128

theorem selected_cut_38129 : selected 9 ⟨1025778, by decide⟩
    (prefixPartial 12 300899) = some ⟨12, 2, 0, 1025778, 300899, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_300899_1025778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300899 ⟨1025778, by decide⟩ :=
  accepted_of_selected 12 300899 ⟨1025778, by decide⟩ ⟨12, 2, 0, 1025778, 300899, 2121, 65536⟩
    (by decide) selected_cut_38129

theorem unmarked_context_11_75224_1025779 : frontier 10 ⟨1025779, by decide⟩
    (prefixCache 11 75224) (prefixPartial 11 75224) = false := by
  decide +kernel

theorem node_context_11_75224_1025779 : EJMOriginalGlobalDAGData.nodes 10 ⟨1025779, by decide⟩ =
    .split (coordinate 11) (![⟨1025680, by decide⟩,⟨1025710, by decide⟩,⟨1025746, by decide⟩,⟨1025778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75224_1025779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75224 ⟨1025779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75224
    ⟨1025779, by decide⟩ (by decide) (![⟨1025680, by decide⟩,⟨1025710, by decide⟩,⟨1025746, by decide⟩,⟨1025778, by decide⟩]) unmarked_context_11_75224_1025779 node_context_11_75224_1025779
  intro a
  fin_cases a
  · exact context_12_300896_1025680
  · exact context_12_300897_1025710
  · exact context_12_300898_1025746
  · exact context_12_300899_1025778

theorem selected_cut_38130 : selected 9 ⟨1025816, by decide⟩
    (prefixPartial 12 300900) = some ⟨12, 2, 0, 1025816, 300900, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_300900_1025816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300900 ⟨1025816, by decide⟩ :=
  accepted_of_selected 12 300900 ⟨1025816, by decide⟩ ⟨12, 2, 0, 1025816, 300900, 2033, 65536⟩
    (by decide) selected_cut_38130

theorem selected_cut_38131 : selected 9 ⟨1025817, by decide⟩
    (prefixPartial 12 300901) = some ⟨12, 1, 0, 1025817, 300901, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300901_1025817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300901 ⟨1025817, by decide⟩ :=
  accepted_of_selected 12 300901 ⟨1025817, by decide⟩ ⟨12, 1, 0, 1025817, 300901, 1, 65536⟩
    (by decide) selected_cut_38131

theorem selected_cut_38132 : selected 9 ⟨1025842, by decide⟩
    (prefixPartial 12 300902) = some ⟨12, 2, 0, 1025842, 300902, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_300902_1025842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300902 ⟨1025842, by decide⟩ :=
  accepted_of_selected 12 300902 ⟨1025842, by decide⟩ ⟨12, 2, 0, 1025842, 300902, 1805, 65536⟩
    (by decide) selected_cut_38132

theorem selected_cut_38133 : selected 9 ⟨1025867, by decide⟩
    (prefixPartial 12 300903) = some ⟨12, 2, 0, 1025867, 300903, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_300903_1025867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300903 ⟨1025867, by decide⟩ :=
  accepted_of_selected 12 300903 ⟨1025867, by decide⟩ ⟨12, 2, 0, 1025867, 300903, 1837, 65536⟩
    (by decide) selected_cut_38133

theorem unmarked_context_11_75225_1025868 : frontier 10 ⟨1025868, by decide⟩
    (prefixCache 11 75225) (prefixPartial 11 75225) = false := by
  decide +kernel

theorem node_context_11_75225_1025868 : EJMOriginalGlobalDAGData.nodes 10 ⟨1025868, by decide⟩ =
    .split (coordinate 11) (![⟨1025816, by decide⟩,⟨1025817, by decide⟩,⟨1025842, by decide⟩,⟨1025867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75225_1025868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75225 ⟨1025868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75225
    ⟨1025868, by decide⟩ (by decide) (![⟨1025816, by decide⟩,⟨1025817, by decide⟩,⟨1025842, by decide⟩,⟨1025867, by decide⟩]) unmarked_context_11_75225_1025868 node_context_11_75225_1025868
  intro a
  fin_cases a
  · exact context_12_300900_1025816
  · exact context_12_300901_1025817
  · exact context_12_300902_1025842
  · exact context_12_300903_1025867

theorem selected_cut_38134 : selected 9 ⟨1025913, by decide⟩
    (prefixPartial 12 300904) = some ⟨12, 2, 0, 1025913, 300904, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_300904_1025913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300904 ⟨1025913, by decide⟩ :=
  accepted_of_selected 12 300904 ⟨1025913, by decide⟩ ⟨12, 2, 0, 1025913, 300904, 2645, 65536⟩
    (by decide) selected_cut_38134

theorem selected_cut_38135 : selected 9 ⟨1025949, by decide⟩
    (prefixPartial 12 300905) = some ⟨12, 2, 0, 1025949, 300905, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_300905_1025949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300905 ⟨1025949, by decide⟩ :=
  accepted_of_selected 12 300905 ⟨1025949, by decide⟩ ⟨12, 2, 0, 1025949, 300905, 2265, 65536⟩
    (by decide) selected_cut_38135

theorem selected_cut_38136 : selected 9 ⟨1025950, by decide⟩
    (prefixPartial 12 300906) = some ⟨12, 1, 0, 1025950, 300906, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300906_1025950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300906 ⟨1025950, by decide⟩ :=
  accepted_of_selected 12 300906 ⟨1025950, by decide⟩ ⟨12, 1, 0, 1025950, 300906, 1, 65536⟩
    (by decide) selected_cut_38136

theorem selected_cut_38137 : selected 9 ⟨1025986, by decide⟩
    (prefixPartial 12 300907) = some ⟨12, 2, 0, 1025986, 300907, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_300907_1025986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300907 ⟨1025986, by decide⟩ :=
  accepted_of_selected 12 300907 ⟨1025986, by decide⟩ ⟨12, 2, 0, 1025986, 300907, 2365, 65536⟩
    (by decide) selected_cut_38137

theorem unmarked_context_11_75226_1025987 : frontier 10 ⟨1025987, by decide⟩
    (prefixCache 11 75226) (prefixPartial 11 75226) = false := by
  decide +kernel

theorem node_context_11_75226_1025987 : EJMOriginalGlobalDAGData.nodes 10 ⟨1025987, by decide⟩ =
    .split (coordinate 11) (![⟨1025913, by decide⟩,⟨1025949, by decide⟩,⟨1025950, by decide⟩,⟨1025986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75226_1025987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75226 ⟨1025987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75226
    ⟨1025987, by decide⟩ (by decide) (![⟨1025913, by decide⟩,⟨1025949, by decide⟩,⟨1025950, by decide⟩,⟨1025986, by decide⟩]) unmarked_context_11_75226_1025987 node_context_11_75226_1025987
  intro a
  fin_cases a
  · exact context_12_300904_1025913
  · exact context_12_300905_1025949
  · exact context_12_300906_1025950
  · exact context_12_300907_1025986

theorem selected_cut_38138 : selected 9 ⟨1026026, by decide⟩
    (prefixPartial 12 300908) = some ⟨12, 2, 0, 1026026, 300908, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_300908_1026026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300908 ⟨1026026, by decide⟩ :=
  accepted_of_selected 12 300908 ⟨1026026, by decide⟩ ⟨12, 2, 0, 1026026, 300908, 2221, 65536⟩
    (by decide) selected_cut_38138

theorem selected_cut_38139 : selected 9 ⟨1026060, by decide⟩
    (prefixPartial 12 300909) = some ⟨12, 2, 0, 1026060, 300909, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_300909_1026060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300909 ⟨1026060, by decide⟩ :=
  accepted_of_selected 12 300909 ⟨1026060, by decide⟩ ⟨12, 2, 0, 1026060, 300909, 2049, 65536⟩
    (by decide) selected_cut_38139

theorem selected_cut_38140 : selected 9 ⟨1026103, by decide⟩
    (prefixPartial 12 300910) = some ⟨12, 2, 0, 1026103, 300910, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_300910_1026103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300910 ⟨1026103, by decide⟩ :=
  accepted_of_selected 12 300910 ⟨1026103, by decide⟩ ⟨12, 2, 0, 1026103, 300910, 2245, 65536⟩
    (by decide) selected_cut_38140

theorem selected_cut_38141 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 300911) = some ⟨12, 1, 0, 903806, 300911, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300911_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300911 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 300911 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 300911, 1, 65536⟩
    (by decide) selected_cut_38141

theorem unmarked_context_11_75227_1026104 : frontier 10 ⟨1026104, by decide⟩
    (prefixCache 11 75227) (prefixPartial 11 75227) = false := by
  decide +kernel

theorem node_context_11_75227_1026104 : EJMOriginalGlobalDAGData.nodes 10 ⟨1026104, by decide⟩ =
    .split (coordinate 11) (![⟨1026026, by decide⟩,⟨1026060, by decide⟩,⟨1026103, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75227_1026104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75227 ⟨1026104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75227
    ⟨1026104, by decide⟩ (by decide) (![⟨1026026, by decide⟩,⟨1026060, by decide⟩,⟨1026103, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75227_1026104 node_context_11_75227_1026104
  intro a
  fin_cases a
  · exact context_12_300908_1026026
  · exact context_12_300909_1026060
  · exact context_12_300910_1026103
  · exact context_12_300911_903806

theorem unmarked_context_10_18806_1026105 : frontier 11 ⟨1026105, by decide⟩
    (prefixCache 10 18806) (prefixPartial 10 18806) = false := by
  decide +kernel

theorem node_context_10_18806_1026105 : EJMOriginalGlobalDAGData.nodes 11 ⟨1026105, by decide⟩ =
    .split (coordinate 10) (![⟨1025779, by decide⟩,⟨1025868, by decide⟩,⟨1025987, by decide⟩,⟨1026104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18806_1026105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18806 ⟨1026105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18806
    ⟨1026105, by decide⟩ (by decide) (![⟨1025779, by decide⟩,⟨1025868, by decide⟩,⟨1025987, by decide⟩,⟨1026104, by decide⟩]) unmarked_context_10_18806_1026105 node_context_10_18806_1026105
  intro a
  fin_cases a
  · exact context_11_75224_1025779
  · exact context_11_75225_1025868
  · exact context_11_75226_1025987
  · exact context_11_75227_1026104

theorem selected_cut_38142 : selected 9 ⟨1026135, by decide⟩
    (prefixPartial 12 300912) = some ⟨12, 2, 0, 1026135, 300912, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_300912_1026135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300912 ⟨1026135, by decide⟩ :=
  accepted_of_selected 12 300912 ⟨1026135, by decide⟩ ⟨12, 2, 0, 1026135, 300912, 2025, 65536⟩
    (by decide) selected_cut_38142

theorem selected_cut_38143 : selected 9 ⟨1026161, by decide⟩
    (prefixPartial 12 300913) = some ⟨12, 2, 0, 1026161, 300913, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_300913_1026161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300913 ⟨1026161, by decide⟩ :=
  accepted_of_selected 12 300913 ⟨1026161, by decide⟩ ⟨12, 2, 0, 1026161, 300913, 1821, 65536⟩
    (by decide) selected_cut_38143

theorem selected_cut_38144 : selected 9 ⟨1026193, by decide⟩
    (prefixPartial 12 300914) = some ⟨12, 2, 0, 1026193, 300914, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_300914_1026193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300914 ⟨1026193, by decide⟩ :=
  accepted_of_selected 12 300914 ⟨1026193, by decide⟩ ⟨12, 2, 0, 1026193, 300914, 2073, 65536⟩
    (by decide) selected_cut_38144

theorem selected_cut_38145 : selected 9 ⟨1026215, by decide⟩
    (prefixPartial 12 300915) = some ⟨12, 2, 0, 1026215, 300915, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_300915_1026215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300915 ⟨1026215, by decide⟩ :=
  accepted_of_selected 12 300915 ⟨1026215, by decide⟩ ⟨12, 2, 0, 1026215, 300915, 1665, 65536⟩
    (by decide) selected_cut_38145

theorem unmarked_context_11_75228_1026216 : frontier 10 ⟨1026216, by decide⟩
    (prefixCache 11 75228) (prefixPartial 11 75228) = false := by
  decide +kernel

theorem node_context_11_75228_1026216 : EJMOriginalGlobalDAGData.nodes 10 ⟨1026216, by decide⟩ =
    .split (coordinate 11) (![⟨1026135, by decide⟩,⟨1026161, by decide⟩,⟨1026193, by decide⟩,⟨1026215, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75228_1026216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75228 ⟨1026216, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75228
    ⟨1026216, by decide⟩ (by decide) (![⟨1026135, by decide⟩,⟨1026161, by decide⟩,⟨1026193, by decide⟩,⟨1026215, by decide⟩]) unmarked_context_11_75228_1026216 node_context_11_75228_1026216
  intro a
  fin_cases a
  · exact context_12_300912_1026135
  · exact context_12_300913_1026161
  · exact context_12_300914_1026193
  · exact context_12_300915_1026215

theorem selected_cut_38146 : selected 9 ⟨1026249, by decide⟩
    (prefixPartial 12 300916) = some ⟨12, 2, 0, 1026249, 300916, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_300916_1026249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300916 ⟨1026249, by decide⟩ :=
  accepted_of_selected 12 300916 ⟨1026249, by decide⟩ ⟨12, 2, 0, 1026249, 300916, 1789, 65536⟩
    (by decide) selected_cut_38146

theorem selected_cut_38147 : selected 9 ⟨1026250, by decide⟩
    (prefixPartial 12 300917) = some ⟨12, 1, 0, 1026250, 300917, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300917_1026250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300917 ⟨1026250, by decide⟩ :=
  accepted_of_selected 12 300917 ⟨1026250, by decide⟩ ⟨12, 1, 0, 1026250, 300917, 1, 65536⟩
    (by decide) selected_cut_38147

theorem selected_cut_38148 : selected 9 ⟨1026279, by decide⟩
    (prefixPartial 12 300918) = some ⟨12, 2, 0, 1026279, 300918, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_300918_1026279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300918 ⟨1026279, by decide⟩ :=
  accepted_of_selected 12 300918 ⟨1026279, by decide⟩ ⟨12, 2, 0, 1026279, 300918, 1665, 65536⟩
    (by decide) selected_cut_38148

theorem selected_cut_38149 : selected 9 ⟨1026302, by decide⟩
    (prefixPartial 12 300919) = some ⟨12, 2, 0, 1026302, 300919, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_300919_1026302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300919 ⟨1026302, by decide⟩ :=
  accepted_of_selected 12 300919 ⟨1026302, by decide⟩ ⟨12, 2, 0, 1026302, 300919, 1517, 65536⟩
    (by decide) selected_cut_38149

theorem unmarked_context_11_75229_1026303 : frontier 10 ⟨1026303, by decide⟩
    (prefixCache 11 75229) (prefixPartial 11 75229) = false := by
  decide +kernel

theorem node_context_11_75229_1026303 : EJMOriginalGlobalDAGData.nodes 10 ⟨1026303, by decide⟩ =
    .split (coordinate 11) (![⟨1026249, by decide⟩,⟨1026250, by decide⟩,⟨1026279, by decide⟩,⟨1026302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75229_1026303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75229 ⟨1026303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75229
    ⟨1026303, by decide⟩ (by decide) (![⟨1026249, by decide⟩,⟨1026250, by decide⟩,⟨1026279, by decide⟩,⟨1026302, by decide⟩]) unmarked_context_11_75229_1026303 node_context_11_75229_1026303
  intro a
  fin_cases a
  · exact context_12_300916_1026249
  · exact context_12_300917_1026250
  · exact context_12_300918_1026279
  · exact context_12_300919_1026302

theorem selected_cut_38150 : selected 9 ⟨1026336, by decide⟩
    (prefixPartial 12 300920) = some ⟨12, 2, 0, 1026336, 300920, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_300920_1026336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300920 ⟨1026336, by decide⟩ :=
  accepted_of_selected 12 300920 ⟨1026336, by decide⟩ ⟨12, 2, 0, 1026336, 300920, 2061, 65536⟩
    (by decide) selected_cut_38150

theorem selected_cut_38151 : selected 9 ⟨1026362, by decide⟩
    (prefixPartial 12 300921) = some ⟨12, 2, 0, 1026362, 300921, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_300921_1026362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300921 ⟨1026362, by decide⟩ :=
  accepted_of_selected 12 300921 ⟨1026362, by decide⟩ ⟨12, 2, 0, 1026362, 300921, 1765, 65536⟩
    (by decide) selected_cut_38151

theorem selected_cut_38152 : selected 9 ⟨1026389, by decide⟩
    (prefixPartial 12 300922) = some ⟨12, 2, 0, 1026389, 300922, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_300922_1026389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300922 ⟨1026389, by decide⟩ :=
  accepted_of_selected 12 300922 ⟨1026389, by decide⟩ ⟨12, 2, 0, 1026389, 300922, 1773, 65536⟩
    (by decide) selected_cut_38152

theorem selected_cut_38153 : selected 9 ⟨1026414, by decide⟩
    (prefixPartial 12 300923) = some ⟨12, 2, 0, 1026414, 300923, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_300923_1026414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300923 ⟨1026414, by decide⟩ :=
  accepted_of_selected 12 300923 ⟨1026414, by decide⟩ ⟨12, 2, 0, 1026414, 300923, 1677, 65536⟩
    (by decide) selected_cut_38153

theorem unmarked_context_11_75230_1026415 : frontier 10 ⟨1026415, by decide⟩
    (prefixCache 11 75230) (prefixPartial 11 75230) = false := by
  decide +kernel

theorem node_context_11_75230_1026415 : EJMOriginalGlobalDAGData.nodes 10 ⟨1026415, by decide⟩ =
    .split (coordinate 11) (![⟨1026336, by decide⟩,⟨1026362, by decide⟩,⟨1026389, by decide⟩,⟨1026414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75230_1026415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75230 ⟨1026415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75230
    ⟨1026415, by decide⟩ (by decide) (![⟨1026336, by decide⟩,⟨1026362, by decide⟩,⟨1026389, by decide⟩,⟨1026414, by decide⟩]) unmarked_context_11_75230_1026415 node_context_11_75230_1026415
  intro a
  fin_cases a
  · exact context_12_300920_1026336
  · exact context_12_300921_1026362
  · exact context_12_300922_1026389
  · exact context_12_300923_1026414

theorem selected_cut_38154 : selected 9 ⟨1026455, by decide⟩
    (prefixPartial 12 300924) = some ⟨12, 2, 0, 1026455, 300924, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_300924_1026455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300924 ⟨1026455, by decide⟩ :=
  accepted_of_selected 12 300924 ⟨1026455, by decide⟩ ⟨12, 2, 0, 1026455, 300924, 1965, 65536⟩
    (by decide) selected_cut_38154

theorem selected_cut_38155 : selected 9 ⟨1026483, by decide⟩
    (prefixPartial 12 300925) = some ⟨12, 2, 0, 1026483, 300925, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_300925_1026483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300925 ⟨1026483, by decide⟩ :=
  accepted_of_selected 12 300925 ⟨1026483, by decide⟩ ⟨12, 2, 0, 1026483, 300925, 1753, 65536⟩
    (by decide) selected_cut_38155

theorem selected_cut_38156 : selected 9 ⟨1026517, by decide⟩
    (prefixPartial 12 300926) = some ⟨12, 2, 0, 1026517, 300926, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_300926_1026517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300926 ⟨1026517, by decide⟩ :=
  accepted_of_selected 12 300926 ⟨1026517, by decide⟩ ⟨12, 2, 0, 1026517, 300926, 2009, 65536⟩
    (by decide) selected_cut_38156

theorem selected_cut_38157 : selected 9 ⟨762108, by decide⟩
    (prefixPartial 12 300927) = some ⟨12, 1, 0, 762108, 300927, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300927_762108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300927 ⟨762108, by decide⟩ :=
  accepted_of_selected 12 300927 ⟨762108, by decide⟩ ⟨12, 1, 0, 762108, 300927, 1, 65536⟩
    (by decide) selected_cut_38157

theorem unmarked_context_11_75231_1026518 : frontier 10 ⟨1026518, by decide⟩
    (prefixCache 11 75231) (prefixPartial 11 75231) = false := by
  decide +kernel

theorem node_context_11_75231_1026518 : EJMOriginalGlobalDAGData.nodes 10 ⟨1026518, by decide⟩ =
    .split (coordinate 11) (![⟨1026455, by decide⟩,⟨1026483, by decide⟩,⟨1026517, by decide⟩,⟨762108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75231_1026518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75231 ⟨1026518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75231
    ⟨1026518, by decide⟩ (by decide) (![⟨1026455, by decide⟩,⟨1026483, by decide⟩,⟨1026517, by decide⟩,⟨762108, by decide⟩]) unmarked_context_11_75231_1026518 node_context_11_75231_1026518
  intro a
  fin_cases a
  · exact context_12_300924_1026455
  · exact context_12_300925_1026483
  · exact context_12_300926_1026517
  · exact context_12_300927_762108

theorem unmarked_context_10_18807_1026519 : frontier 11 ⟨1026519, by decide⟩
    (prefixCache 10 18807) (prefixPartial 10 18807) = false := by
  decide +kernel

theorem node_context_10_18807_1026519 : EJMOriginalGlobalDAGData.nodes 11 ⟨1026519, by decide⟩ =
    .split (coordinate 10) (![⟨1026216, by decide⟩,⟨1026303, by decide⟩,⟨1026415, by decide⟩,⟨1026518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18807_1026519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18807 ⟨1026519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18807
    ⟨1026519, by decide⟩ (by decide) (![⟨1026216, by decide⟩,⟨1026303, by decide⟩,⟨1026415, by decide⟩,⟨1026518, by decide⟩]) unmarked_context_10_18807_1026519 node_context_10_18807_1026519
  intro a
  fin_cases a
  · exact context_11_75228_1026216
  · exact context_11_75229_1026303
  · exact context_11_75230_1026415
  · exact context_11_75231_1026518

theorem unmarked_context_9_4701_1026520 : frontier 12 ⟨1026520, by decide⟩
    (prefixCache 9 4701) (prefixPartial 9 4701) = false := by
  decide +kernel

theorem node_context_9_4701_1026520 : EJMOriginalGlobalDAGData.nodes 12 ⟨1026520, by decide⟩ =
    .split (coordinate 9) (![⟨1025640, by decide⟩,⟨893098, by decide⟩,⟨1026105, by decide⟩,⟨1026519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4701_1026520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4701 ⟨1026520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4701
    ⟨1026520, by decide⟩ (by decide) (![⟨1025640, by decide⟩,⟨893098, by decide⟩,⟨1026105, by decide⟩,⟨1026519, by decide⟩]) unmarked_context_9_4701_1026520 node_context_9_4701_1026520
  intro a
  fin_cases a
  · exact context_10_18804_1025640
  · exact context_10_18805_893098
  · exact context_10_18806_1026105
  · exact context_10_18807_1026519

theorem selected_cut_38158 : selected 9 ⟨1026557, by decide⟩
    (prefixPartial 12 300928) = some ⟨12, 2, 0, 1026557, 300928, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_300928_1026557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300928 ⟨1026557, by decide⟩ :=
  accepted_of_selected 12 300928 ⟨1026557, by decide⟩ ⟨12, 2, 0, 1026557, 300928, 1601, 65536⟩
    (by decide) selected_cut_38158

theorem selected_cut_38159 : selected 9 ⟨1026579, by decide⟩
    (prefixPartial 12 300929) = some ⟨12, 2, 0, 1026579, 300929, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_300929_1026579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300929 ⟨1026579, by decide⟩ :=
  accepted_of_selected 12 300929 ⟨1026579, by decide⟩ ⟨12, 2, 0, 1026579, 300929, 1337, 65536⟩
    (by decide) selected_cut_38159

theorem selected_cut_38160 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 300930) = some ⟨12, 1, 0, 984676, 300930, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300930_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300930 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 300930 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 300930, 1, 65536⟩
    (by decide) selected_cut_38160

theorem selected_cut_38161 : selected 9 ⟨1026602, by decide⟩
    (prefixPartial 12 300931) = some ⟨12, 2, 0, 1026602, 300931, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_300931_1026602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300931 ⟨1026602, by decide⟩ :=
  accepted_of_selected 12 300931 ⟨1026602, by decide⟩ ⟨12, 2, 0, 1026602, 300931, 1361, 65536⟩
    (by decide) selected_cut_38161

theorem unmarked_context_11_75232_1026603 : frontier 10 ⟨1026603, by decide⟩
    (prefixCache 11 75232) (prefixPartial 11 75232) = false := by
  decide +kernel

theorem node_context_11_75232_1026603 : EJMOriginalGlobalDAGData.nodes 10 ⟨1026603, by decide⟩ =
    .split (coordinate 11) (![⟨1026557, by decide⟩,⟨1026579, by decide⟩,⟨984676, by decide⟩,⟨1026602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75232_1026603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75232 ⟨1026603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75232
    ⟨1026603, by decide⟩ (by decide) (![⟨1026557, by decide⟩,⟨1026579, by decide⟩,⟨984676, by decide⟩,⟨1026602, by decide⟩]) unmarked_context_11_75232_1026603 node_context_11_75232_1026603
  intro a
  fin_cases a
  · exact context_12_300928_1026557
  · exact context_12_300929_1026579
  · exact context_12_300930_984676
  · exact context_12_300931_1026602

theorem selected_cut_38162 : selected 10 ⟨1026684, by decide⟩
    (prefixPartial 11 75233) = some ⟨11, 2, 0, 1026684, 75233, 3941, 262144⟩ := by
  decide +kernel

theorem context_11_75233_1026684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75233 ⟨1026684, by decide⟩ :=
  accepted_of_selected 11 75233 ⟨1026684, by decide⟩ ⟨11, 2, 0, 1026684, 75233, 3941, 262144⟩
    (by decide) selected_cut_38162

theorem selected_cut_38163 : selected 9 ⟨1026720, by decide⟩
    (prefixPartial 12 300936) = some ⟨12, 2, 0, 1026720, 300936, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_300936_1026720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300936 ⟨1026720, by decide⟩ :=
  accepted_of_selected 12 300936 ⟨1026720, by decide⟩ ⟨12, 2, 0, 1026720, 300936, 1549, 65536⟩
    (by decide) selected_cut_38163

theorem selected_cut_38164 : selected 9 ⟨1026742, by decide⟩
    (prefixPartial 12 300937) = some ⟨12, 2, 0, 1026742, 300937, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_300937_1026742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300937 ⟨1026742, by decide⟩ :=
  accepted_of_selected 12 300937 ⟨1026742, by decide⟩ ⟨12, 2, 0, 1026742, 300937, 1257, 65536⟩
    (by decide) selected_cut_38164

theorem selected_cut_38165 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 300938) = some ⟨12, 1, 0, 984676, 300938, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300938_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300938 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 300938 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 300938, 1, 65536⟩
    (by decide) selected_cut_38165

theorem selected_cut_38166 : selected 9 ⟨1026770, by decide⟩
    (prefixPartial 12 300939) = some ⟨12, 2, 0, 1026770, 300939, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_300939_1026770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300939 ⟨1026770, by decide⟩ :=
  accepted_of_selected 12 300939 ⟨1026770, by decide⟩ ⟨12, 2, 0, 1026770, 300939, 1305, 65536⟩
    (by decide) selected_cut_38166

theorem unmarked_context_11_75234_1026771 : frontier 10 ⟨1026771, by decide⟩
    (prefixCache 11 75234) (prefixPartial 11 75234) = false := by
  decide +kernel

theorem node_context_11_75234_1026771 : EJMOriginalGlobalDAGData.nodes 10 ⟨1026771, by decide⟩ =
    .split (coordinate 11) (![⟨1026720, by decide⟩,⟨1026742, by decide⟩,⟨984676, by decide⟩,⟨1026770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75234_1026771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75234 ⟨1026771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75234
    ⟨1026771, by decide⟩ (by decide) (![⟨1026720, by decide⟩,⟨1026742, by decide⟩,⟨984676, by decide⟩,⟨1026770, by decide⟩]) unmarked_context_11_75234_1026771 node_context_11_75234_1026771
  intro a
  fin_cases a
  · exact context_12_300936_1026720
  · exact context_12_300937_1026742
  · exact context_12_300938_984676
  · exact context_12_300939_1026770

theorem selected_cut_38167 : selected 10 ⟨1026826, by decide⟩
    (prefixPartial 11 75235) = some ⟨11, 2, 0, 1026826, 75235, 2613, 262144⟩ := by
  decide +kernel

theorem context_11_75235_1026826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75235 ⟨1026826, by decide⟩ :=
  accepted_of_selected 11 75235 ⟨1026826, by decide⟩ ⟨11, 2, 0, 1026826, 75235, 2613, 262144⟩
    (by decide) selected_cut_38167

theorem unmarked_context_10_18808_1026827 : frontier 11 ⟨1026827, by decide⟩
    (prefixCache 10 18808) (prefixPartial 10 18808) = false := by
  decide +kernel

theorem node_context_10_18808_1026827 : EJMOriginalGlobalDAGData.nodes 11 ⟨1026827, by decide⟩ =
    .split (coordinate 10) (![⟨1026603, by decide⟩,⟨1026684, by decide⟩,⟨1026771, by decide⟩,⟨1026826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18808_1026827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18808 ⟨1026827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18808
    ⟨1026827, by decide⟩ (by decide) (![⟨1026603, by decide⟩,⟨1026684, by decide⟩,⟨1026771, by decide⟩,⟨1026826, by decide⟩]) unmarked_context_10_18808_1026827 node_context_10_18808_1026827
  intro a
  fin_cases a
  · exact context_11_75232_1026603
  · exact context_11_75233_1026684
  · exact context_11_75234_1026771
  · exact context_11_75235_1026826

theorem selected_cut_38168 : selected 10 ⟨1026866, by decide⟩
    (prefixPartial 11 75236) = some ⟨11, 2, 0, 1026866, 75236, 2829, 262144⟩ := by
  decide +kernel

theorem context_11_75236_1026866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75236 ⟨1026866, by decide⟩ :=
  accepted_of_selected 11 75236 ⟨1026866, by decide⟩ ⟨11, 2, 0, 1026866, 75236, 2829, 262144⟩
    (by decide) selected_cut_38168

theorem selected_cut_38169 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 75237) = some ⟨11, 1, 0, 892405, 75237, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75237_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75237 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 75237 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 75237, 1, 262144⟩
    (by decide) selected_cut_38169

theorem selected_cut_38170 : selected 10 ⟨1026905, by decide⟩
    (prefixPartial 11 75238) = some ⟨11, 2, 0, 1026905, 75238, 2825, 262144⟩ := by
  decide +kernel

theorem context_11_75238_1026905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75238 ⟨1026905, by decide⟩ :=
  accepted_of_selected 11 75238 ⟨1026905, by decide⟩ ⟨11, 2, 0, 1026905, 75238, 2825, 262144⟩
    (by decide) selected_cut_38170

theorem selected_cut_38171 : selected 10 ⟨1026934, by decide⟩
    (prefixPartial 11 75239) = some ⟨11, 2, 0, 1026934, 75239, 1901, 262144⟩ := by
  decide +kernel

theorem context_11_75239_1026934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75239 ⟨1026934, by decide⟩ :=
  accepted_of_selected 11 75239 ⟨1026934, by decide⟩ ⟨11, 2, 0, 1026934, 75239, 1901, 262144⟩
    (by decide) selected_cut_38171

theorem unmarked_context_10_18809_1026935 : frontier 11 ⟨1026935, by decide⟩
    (prefixCache 10 18809) (prefixPartial 10 18809) = false := by
  decide +kernel

theorem node_context_10_18809_1026935 : EJMOriginalGlobalDAGData.nodes 11 ⟨1026935, by decide⟩ =
    .split (coordinate 10) (![⟨1026866, by decide⟩,⟨892405, by decide⟩,⟨1026905, by decide⟩,⟨1026934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18809_1026935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18809 ⟨1026935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18809
    ⟨1026935, by decide⟩ (by decide) (![⟨1026866, by decide⟩,⟨892405, by decide⟩,⟨1026905, by decide⟩,⟨1026934, by decide⟩]) unmarked_context_10_18809_1026935 node_context_10_18809_1026935
  intro a
  fin_cases a
  · exact context_11_75236_1026866
  · exact context_11_75237_892405
  · exact context_11_75238_1026905
  · exact context_11_75239_1026934

theorem selected_cut_38172 : selected 10 ⟨1026976, by decide⟩
    (prefixPartial 11 75240) = some ⟨11, 2, 0, 1026976, 75240, 2593, 262144⟩ := by
  decide +kernel

theorem context_11_75240_1026976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75240 ⟨1026976, by decide⟩ :=
  accepted_of_selected 11 75240 ⟨1026976, by decide⟩ ⟨11, 2, 0, 1026976, 75240, 2593, 262144⟩
    (by decide) selected_cut_38172

theorem selected_cut_38173 : selected 10 ⟨1026998, by decide⟩
    (prefixPartial 11 75241) = some ⟨11, 2, 0, 1026998, 75241, 2073, 262144⟩ := by
  decide +kernel

theorem context_11_75241_1026998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75241 ⟨1026998, by decide⟩ :=
  accepted_of_selected 11 75241 ⟨1026998, by decide⟩ ⟨11, 2, 0, 1026998, 75241, 2073, 262144⟩
    (by decide) selected_cut_38173

theorem selected_cut_38174 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 75242) = some ⟨11, 1, 0, 906566, 75242, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75242_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75242 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 75242 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 75242, 1, 262144⟩
    (by decide) selected_cut_38174

theorem selected_cut_38175 : selected 10 ⟨1027025, by decide⟩
    (prefixPartial 11 75243) = some ⟨11, 2, 0, 1027025, 75243, 1625, 262144⟩ := by
  decide +kernel

theorem context_11_75243_1027025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75243 ⟨1027025, by decide⟩ :=
  accepted_of_selected 11 75243 ⟨1027025, by decide⟩ ⟨11, 2, 0, 1027025, 75243, 1625, 262144⟩
    (by decide) selected_cut_38175

theorem unmarked_context_10_18810_1027026 : frontier 11 ⟨1027026, by decide⟩
    (prefixCache 10 18810) (prefixPartial 10 18810) = false := by
  decide +kernel

theorem node_context_10_18810_1027026 : EJMOriginalGlobalDAGData.nodes 11 ⟨1027026, by decide⟩ =
    .split (coordinate 10) (![⟨1026976, by decide⟩,⟨1026998, by decide⟩,⟨906566, by decide⟩,⟨1027025, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18810_1027026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18810 ⟨1027026, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18810
    ⟨1027026, by decide⟩ (by decide) (![⟨1026976, by decide⟩,⟨1026998, by decide⟩,⟨906566, by decide⟩,⟨1027025, by decide⟩]) unmarked_context_10_18810_1027026 node_context_10_18810_1027026
  intro a
  fin_cases a
  · exact context_11_75240_1026976
  · exact context_11_75241_1026998
  · exact context_11_75242_906566
  · exact context_11_75243_1027025

theorem selected_cut_38176 : selected 10 ⟨1027066, by decide⟩
    (prefixPartial 11 75244) = some ⟨11, 2, 0, 1027066, 75244, 2309, 262144⟩ := by
  decide +kernel

theorem context_11_75244_1027066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75244 ⟨1027066, by decide⟩ :=
  accepted_of_selected 11 75244 ⟨1027066, by decide⟩ ⟨11, 2, 0, 1027066, 75244, 2309, 262144⟩
    (by decide) selected_cut_38176

theorem selected_cut_38177 : selected 10 ⟨1027095, by decide⟩
    (prefixPartial 11 75245) = some ⟨11, 2, 0, 1027095, 75245, 1925, 262144⟩ := by
  decide +kernel

theorem context_11_75245_1027095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75245 ⟨1027095, by decide⟩ :=
  accepted_of_selected 11 75245 ⟨1027095, by decide⟩ ⟨11, 2, 0, 1027095, 75245, 1925, 262144⟩
    (by decide) selected_cut_38177

theorem selected_cut_38178 : selected 10 ⟨1027121, by decide⟩
    (prefixPartial 11 75246) = some ⟨11, 2, 0, 1027121, 75246, 1825, 262144⟩ := by
  decide +kernel

theorem context_11_75246_1027121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75246 ⟨1027121, by decide⟩ :=
  accepted_of_selected 11 75246 ⟨1027121, by decide⟩ ⟨11, 2, 0, 1027121, 75246, 1825, 262144⟩
    (by decide) selected_cut_38178

theorem selected_cut_38179 : selected 10 ⟨1027145, by decide⟩
    (prefixPartial 11 75247) = some ⟨11, 2, 0, 1027145, 75247, 1257, 262144⟩ := by
  decide +kernel

theorem context_11_75247_1027145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75247 ⟨1027145, by decide⟩ :=
  accepted_of_selected 11 75247 ⟨1027145, by decide⟩ ⟨11, 2, 0, 1027145, 75247, 1257, 262144⟩
    (by decide) selected_cut_38179

theorem unmarked_context_10_18811_1027146 : frontier 11 ⟨1027146, by decide⟩
    (prefixCache 10 18811) (prefixPartial 10 18811) = false := by
  decide +kernel

theorem node_context_10_18811_1027146 : EJMOriginalGlobalDAGData.nodes 11 ⟨1027146, by decide⟩ =
    .split (coordinate 10) (![⟨1027066, by decide⟩,⟨1027095, by decide⟩,⟨1027121, by decide⟩,⟨1027145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18811_1027146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18811 ⟨1027146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18811
    ⟨1027146, by decide⟩ (by decide) (![⟨1027066, by decide⟩,⟨1027095, by decide⟩,⟨1027121, by decide⟩,⟨1027145, by decide⟩]) unmarked_context_10_18811_1027146 node_context_10_18811_1027146
  intro a
  fin_cases a
  · exact context_11_75244_1027066
  · exact context_11_75245_1027095
  · exact context_11_75246_1027121
  · exact context_11_75247_1027145

theorem unmarked_context_9_4702_1027147 : frontier 12 ⟨1027147, by decide⟩
    (prefixCache 9 4702) (prefixPartial 9 4702) = false := by
  decide +kernel

theorem node_context_9_4702_1027147 : EJMOriginalGlobalDAGData.nodes 12 ⟨1027147, by decide⟩ =
    .split (coordinate 9) (![⟨1026827, by decide⟩,⟨1026935, by decide⟩,⟨1027026, by decide⟩,⟨1027146, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4702_1027147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4702 ⟨1027147, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4702
    ⟨1027147, by decide⟩ (by decide) (![⟨1026827, by decide⟩,⟨1026935, by decide⟩,⟨1027026, by decide⟩,⟨1027146, by decide⟩]) unmarked_context_9_4702_1027147 node_context_9_4702_1027147
  intro a
  fin_cases a
  · exact context_10_18808_1026827
  · exact context_10_18809_1026935
  · exact context_10_18810_1027026
  · exact context_10_18811_1027146

theorem selected_cut_38180 : selected 10 ⟨1027169, by decide⟩
    (prefixPartial 11 75248) = some ⟨11, 2, 0, 1027169, 75248, 1905, 262144⟩ := by
  decide +kernel

theorem context_11_75248_1027169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75248 ⟨1027169, by decide⟩ :=
  accepted_of_selected 11 75248 ⟨1027169, by decide⟩ ⟨11, 2, 0, 1027169, 75248, 1905, 262144⟩
    (by decide) selected_cut_38180

theorem selected_cut_38181 : selected 10 ⟨1027192, by decide⟩
    (prefixPartial 11 75249) = some ⟨11, 2, 0, 1027192, 75249, 1821, 262144⟩ := by
  decide +kernel

theorem context_11_75249_1027192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75249 ⟨1027192, by decide⟩ :=
  accepted_of_selected 11 75249 ⟨1027192, by decide⟩ ⟨11, 2, 0, 1027192, 75249, 1821, 262144⟩
    (by decide) selected_cut_38181

theorem selected_cut_38182 : selected 10 ⟨1027221, by decide⟩
    (prefixPartial 11 75250) = some ⟨11, 2, 0, 1027221, 75250, 1893, 262144⟩ := by
  decide +kernel

theorem context_11_75250_1027221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75250 ⟨1027221, by decide⟩ :=
  accepted_of_selected 11 75250 ⟨1027221, by decide⟩ ⟨11, 2, 0, 1027221, 75250, 1893, 262144⟩
    (by decide) selected_cut_38182

theorem selected_cut_38183 : selected 10 ⟨1027254, by decide⟩
    (prefixPartial 11 75251) = some ⟨11, 2, 0, 1027254, 75251, 1481, 262144⟩ := by
  decide +kernel

theorem context_11_75251_1027254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75251 ⟨1027254, by decide⟩ :=
  accepted_of_selected 11 75251 ⟨1027254, by decide⟩ ⟨11, 2, 0, 1027254, 75251, 1481, 262144⟩
    (by decide) selected_cut_38183

theorem unmarked_context_10_18812_1027255 : frontier 11 ⟨1027255, by decide⟩
    (prefixCache 10 18812) (prefixPartial 10 18812) = false := by
  decide +kernel

theorem node_context_10_18812_1027255 : EJMOriginalGlobalDAGData.nodes 11 ⟨1027255, by decide⟩ =
    .split (coordinate 10) (![⟨1027169, by decide⟩,⟨1027192, by decide⟩,⟨1027221, by decide⟩,⟨1027254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18812_1027255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18812 ⟨1027255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18812
    ⟨1027255, by decide⟩ (by decide) (![⟨1027169, by decide⟩,⟨1027192, by decide⟩,⟨1027221, by decide⟩,⟨1027254, by decide⟩]) unmarked_context_10_18812_1027255 node_context_10_18812_1027255
  intro a
  fin_cases a
  · exact context_11_75248_1027169
  · exact context_11_75249_1027192
  · exact context_11_75250_1027221
  · exact context_11_75251_1027254

theorem selected_cut_38184 : selected 11 ⟨1027313, by decide⟩
    (prefixPartial 10 18813) = some ⟨10, 2, 0, 1027313, 18813, 3545, 1048576⟩ := by
  decide +kernel

theorem context_10_18813_1027313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18813 ⟨1027313, by decide⟩ :=
  accepted_of_selected 10 18813 ⟨1027313, by decide⟩ ⟨10, 2, 0, 1027313, 18813, 3545, 1048576⟩
    (by decide) selected_cut_38184

theorem selected_cut_38185 : selected 11 ⟨1027372, by decide⟩
    (prefixPartial 10 18814) = some ⟨10, 2, 0, 1027372, 18814, 2713, 1048576⟩ := by
  decide +kernel

theorem context_10_18814_1027372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18814 ⟨1027372, by decide⟩ :=
  accepted_of_selected 10 18814 ⟨1027372, by decide⟩ ⟨10, 2, 0, 1027372, 18814, 2713, 1048576⟩
    (by decide) selected_cut_38185

theorem selected_cut_38186 : selected 11 ⟨1027413, by decide⟩
    (prefixPartial 10 18815) = some ⟨10, 2, 0, 1027413, 18815, 761, 1048576⟩ := by
  decide +kernel

theorem context_10_18815_1027413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18815 ⟨1027413, by decide⟩ :=
  accepted_of_selected 10 18815 ⟨1027413, by decide⟩ ⟨10, 2, 0, 1027413, 18815, 761, 1048576⟩
    (by decide) selected_cut_38186

theorem unmarked_context_9_4703_1027414 : frontier 12 ⟨1027414, by decide⟩
    (prefixCache 9 4703) (prefixPartial 9 4703) = false := by
  decide +kernel

theorem node_context_9_4703_1027414 : EJMOriginalGlobalDAGData.nodes 12 ⟨1027414, by decide⟩ =
    .split (coordinate 9) (![⟨1027255, by decide⟩,⟨1027313, by decide⟩,⟨1027372, by decide⟩,⟨1027413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4703_1027414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4703 ⟨1027414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4703
    ⟨1027414, by decide⟩ (by decide) (![⟨1027255, by decide⟩,⟨1027313, by decide⟩,⟨1027372, by decide⟩,⟨1027413, by decide⟩]) unmarked_context_9_4703_1027414 node_context_9_4703_1027414
  intro a
  fin_cases a
  · exact context_10_18812_1027255
  · exact context_10_18813_1027313
  · exact context_10_18814_1027372
  · exact context_10_18815_1027413

theorem unmarked_context_8_1175_1027415 : frontier 13 ⟨1027415, by decide⟩
    (prefixCache 8 1175) (prefixPartial 8 1175) = false := by
  decide +kernel

theorem node_context_8_1175_1027415 : EJMOriginalGlobalDAGData.nodes 13 ⟨1027415, by decide⟩ =
    .split (coordinate 8) (![⟨1024854, by decide⟩,⟨1026520, by decide⟩,⟨1027147, by decide⟩,⟨1027414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1175_1027415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1175 ⟨1027415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1175
    ⟨1027415, by decide⟩ (by decide) (![⟨1024854, by decide⟩,⟨1026520, by decide⟩,⟨1027147, by decide⟩,⟨1027414, by decide⟩]) unmarked_context_8_1175_1027415 node_context_8_1175_1027415
  intro a
  fin_cases a
  · exact context_9_4700_1024854
  · exact context_9_4701_1026520
  · exact context_9_4702_1027147
  · exact context_9_4703_1027414

theorem unmarked_context_7_293_1027416 : frontier 14 ⟨1027416, by decide⟩
    (prefixCache 7 293) (prefixPartial 7 293) = false := by
  decide +kernel

theorem node_context_7_293_1027416 : EJMOriginalGlobalDAGData.nodes 14 ⟨1027416, by decide⟩ =
    .split (coordinate 7) (![⟨1010499, by decide⟩,⟨1015426, by decide⟩,⟨1021848, by decide⟩,⟨1027415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_293_1027416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 293 ⟨1027416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 293
    ⟨1027416, by decide⟩ (by decide) (![⟨1010499, by decide⟩,⟨1015426, by decide⟩,⟨1021848, by decide⟩,⟨1027415, by decide⟩]) unmarked_context_7_293_1027416 node_context_7_293_1027416
  intro a
  fin_cases a
  · exact context_8_1172_1010499
  · exact context_8_1173_1015426
  · exact context_8_1174_1021848
  · exact context_8_1175_1027415

theorem selected_cut_38187 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 301056) = some ⟨12, 1, 0, 34034, 301056, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301056_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301056 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 301056 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 301056, 1, 65536⟩
    (by decide) selected_cut_38187

theorem selected_cut_38188 : selected 9 ⟨1027488, by decide⟩
    (prefixPartial 12 301057) = some ⟨12, 2, 0, 1027488, 301057, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_301057_1027488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301057 ⟨1027488, by decide⟩ :=
  accepted_of_selected 12 301057 ⟨1027488, by decide⟩ ⟨12, 2, 0, 1027488, 301057, 2137, 65536⟩
    (by decide) selected_cut_38188

theorem selected_cut_38189 : selected 9 ⟨1027489, by decide⟩
    (prefixPartial 12 301058) = some ⟨12, 1, 0, 1027489, 301058, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301058_1027489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301058 ⟨1027489, by decide⟩ :=
  accepted_of_selected 12 301058 ⟨1027489, by decide⟩ ⟨12, 1, 0, 1027489, 301058, 1, 65536⟩
    (by decide) selected_cut_38189

theorem selected_cut_38190 : selected 9 ⟨1027543, by decide⟩
    (prefixPartial 12 301059) = some ⟨12, 2, 0, 1027543, 301059, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_301059_1027543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301059 ⟨1027543, by decide⟩ :=
  accepted_of_selected 12 301059 ⟨1027543, by decide⟩ ⟨12, 2, 0, 1027543, 301059, 3201, 65536⟩
    (by decide) selected_cut_38190

theorem unmarked_context_11_75264_1027544 : frontier 10 ⟨1027544, by decide⟩
    (prefixCache 11 75264) (prefixPartial 11 75264) = false := by
  decide +kernel

theorem node_context_11_75264_1027544 : EJMOriginalGlobalDAGData.nodes 10 ⟨1027544, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1027488, by decide⟩,⟨1027489, by decide⟩,⟨1027543, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75264_1027544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75264 ⟨1027544, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75264
    ⟨1027544, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1027488, by decide⟩,⟨1027489, by decide⟩,⟨1027543, by decide⟩]) unmarked_context_11_75264_1027544 node_context_11_75264_1027544
  intro a
  fin_cases a
  · exact context_12_301056_34034
  · exact context_12_301057_1027488
  · exact context_12_301058_1027489
  · exact context_12_301059_1027543

theorem selected_cut_38191 : selected 9 ⟨1027632, by decide⟩
    (prefixPartial 12 301060) = some ⟨12, 2, 0, 1027632, 301060, 3713, 65536⟩ := by
  decide +kernel

theorem context_12_301060_1027632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301060 ⟨1027632, by decide⟩ :=
  accepted_of_selected 12 301060 ⟨1027632, by decide⟩ ⟨12, 2, 0, 1027632, 301060, 3713, 65536⟩
    (by decide) selected_cut_38191

theorem selected_cut_38192 : selected 9 ⟨1027699, by decide⟩
    (prefixPartial 12 301061) = some ⟨12, 2, 0, 1027699, 301061, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_301061_1027699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301061 ⟨1027699, by decide⟩ :=
  accepted_of_selected 12 301061 ⟨1027699, by decide⟩ ⟨12, 2, 0, 1027699, 301061, 3989, 65536⟩
    (by decide) selected_cut_38192

theorem selected_cut_38193 : selected 9 ⟨1027767, by decide⟩
    (prefixPartial 12 301062) = some ⟨12, 2, 0, 1027767, 301062, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_301062_1027767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301062 ⟨1027767, by decide⟩ :=
  accepted_of_selected 12 301062 ⟨1027767, by decide⟩ ⟨12, 2, 0, 1027767, 301062, 3809, 65536⟩
    (by decide) selected_cut_38193

theorem selected_cut_38194 : selected 9 ⟨1027841, by decide⟩
    (prefixPartial 12 301063) = some ⟨12, 2, 0, 1027841, 301063, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_301063_1027841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301063 ⟨1027841, by decide⟩ :=
  accepted_of_selected 12 301063 ⟨1027841, by decide⟩ ⟨12, 2, 0, 1027841, 301063, 4021, 65536⟩
    (by decide) selected_cut_38194

theorem unmarked_context_11_75265_1027842 : frontier 10 ⟨1027842, by decide⟩
    (prefixCache 11 75265) (prefixPartial 11 75265) = false := by
  decide +kernel

theorem node_context_11_75265_1027842 : EJMOriginalGlobalDAGData.nodes 10 ⟨1027842, by decide⟩ =
    .split (coordinate 11) (![⟨1027632, by decide⟩,⟨1027699, by decide⟩,⟨1027767, by decide⟩,⟨1027841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75265_1027842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75265 ⟨1027842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75265
    ⟨1027842, by decide⟩ (by decide) (![⟨1027632, by decide⟩,⟨1027699, by decide⟩,⟨1027767, by decide⟩,⟨1027841, by decide⟩]) unmarked_context_11_75265_1027842 node_context_11_75265_1027842
  intro a
  fin_cases a
  · exact context_12_301060_1027632
  · exact context_12_301061_1027699
  · exact context_12_301062_1027767
  · exact context_12_301063_1027841

theorem selected_cut_38195 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 301064) = some ⟨12, 1, 0, 450498, 301064, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301064_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301064 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 301064 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 301064, 1, 65536⟩
    (by decide) selected_cut_38195

theorem selected_cut_38196 : selected 8 ⟨1027877, by decide⟩
    (prefixPartial 13 1204260) = some ⟨13, 2, 0, 1027877, 1204260, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_1204260_1027877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1204260 ⟨1027877, by decide⟩ :=
  accepted_of_selected 13 1204260 ⟨1027877, by decide⟩ ⟨13, 2, 0, 1027877, 1204260, 1709, 16384⟩
    (by decide) selected_cut_38196

theorem selected_cut_38197 : selected 8 ⟨1027890, by decide⟩
    (prefixPartial 13 1204261) = some ⟨13, 2, 0, 1027890, 1204261, 937, 16384⟩ := by
  decide +kernel

theorem context_13_1204261_1027890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1204261 ⟨1027890, by decide⟩ :=
  accepted_of_selected 13 1204261 ⟨1027890, by decide⟩ ⟨13, 2, 0, 1027890, 1204261, 937, 16384⟩
    (by decide) selected_cut_38197

theorem selected_cut_38198 : selected 8 ⟨1027911, by decide⟩
    (prefixPartial 13 1204262) = some ⟨13, 2, 0, 1027911, 1204262, 885, 16384⟩ := by
  decide +kernel

theorem context_13_1204262_1027911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1204262 ⟨1027911, by decide⟩ :=
  accepted_of_selected 13 1204262 ⟨1027911, by decide⟩ ⟨13, 2, 0, 1027911, 1204262, 885, 16384⟩
    (by decide) selected_cut_38198

theorem selected_cut_38199 : selected 8 ⟨1027919, by decide⟩
    (prefixPartial 13 1204263) = some ⟨13, 2, 0, 1027919, 1204263, 597, 16384⟩ := by
  decide +kernel

theorem context_13_1204263_1027919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1204263 ⟨1027919, by decide⟩ :=
  accepted_of_selected 13 1204263 ⟨1027919, by decide⟩ ⟨13, 2, 0, 1027919, 1204263, 597, 16384⟩
    (by decide) selected_cut_38199

theorem unmarked_context_12_301065_1027920 : frontier 9 ⟨1027920, by decide⟩
    (prefixCache 12 301065) (prefixPartial 12 301065) = false := by
  decide +kernel

theorem node_context_12_301065_1027920 : EJMOriginalGlobalDAGData.nodes 9 ⟨1027920, by decide⟩ =
    .split (coordinate 12) (![⟨1027877, by decide⟩,⟨1027890, by decide⟩,⟨1027911, by decide⟩,⟨1027919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301065_1027920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301065 ⟨1027920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301065
    ⟨1027920, by decide⟩ (by decide) (![⟨1027877, by decide⟩,⟨1027890, by decide⟩,⟨1027911, by decide⟩,⟨1027919, by decide⟩]) unmarked_context_12_301065_1027920 node_context_12_301065_1027920
  intro a
  fin_cases a
  · exact context_13_1204260_1027877
  · exact context_13_1204261_1027890
  · exact context_13_1204262_1027911
  · exact context_13_1204263_1027919

theorem selected_cut_38200 : selected 9 ⟨1027980, by decide⟩
    (prefixPartial 12 301066) = some ⟨12, 2, 0, 1027980, 301066, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_301066_1027980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301066 ⟨1027980, by decide⟩ :=
  accepted_of_selected 12 301066 ⟨1027980, by decide⟩ ⟨12, 2, 0, 1027980, 301066, 3501, 65536⟩
    (by decide) selected_cut_38200

theorem selected_cut_38201 : selected 9 ⟨1028050, by decide⟩
    (prefixPartial 12 301067) = some ⟨12, 2, 0, 1028050, 301067, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_301067_1028050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301067 ⟨1028050, by decide⟩ :=
  accepted_of_selected 12 301067 ⟨1028050, by decide⟩ ⟨12, 2, 0, 1028050, 301067, 3941, 65536⟩
    (by decide) selected_cut_38201

theorem unmarked_context_11_75266_1028051 : frontier 10 ⟨1028051, by decide⟩
    (prefixCache 11 75266) (prefixPartial 11 75266) = false := by
  decide +kernel

theorem node_context_11_75266_1028051 : EJMOriginalGlobalDAGData.nodes 10 ⟨1028051, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1027920, by decide⟩,⟨1027980, by decide⟩,⟨1028050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75266_1028051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75266 ⟨1028051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75266
    ⟨1028051, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1027920, by decide⟩,⟨1027980, by decide⟩,⟨1028050, by decide⟩]) unmarked_context_11_75266_1028051 node_context_11_75266_1028051
  intro a
  fin_cases a
  · exact context_12_301064_450498
  · exact context_12_301065_1027920
  · exact context_12_301066_1027980
  · exact context_12_301067_1028050

theorem selected_cut_38202 : selected 9 ⟨1028116, by decide⟩
    (prefixPartial 12 301068) = some ⟨12, 2, 0, 1028116, 301068, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_301068_1028116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301068 ⟨1028116, by decide⟩ :=
  accepted_of_selected 12 301068 ⟨1028116, by decide⟩ ⟨12, 2, 0, 1028116, 301068, 3417, 65536⟩
    (by decide) selected_cut_38202

theorem selected_cut_38203 : selected 8 ⟨1028155, by decide⟩
    (prefixPartial 13 1204276) = some ⟨13, 2, 0, 1028155, 1204276, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_1204276_1028155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1204276 ⟨1028155, by decide⟩ :=
  accepted_of_selected 13 1204276 ⟨1028155, by decide⟩ ⟨13, 2, 0, 1028155, 1204276, 1737, 16384⟩
    (by decide) selected_cut_38203

theorem selected_cut_38204 : selected 8 ⟨1028168, by decide⟩
    (prefixPartial 13 1204277) = some ⟨13, 2, 0, 1028168, 1204277, 965, 16384⟩ := by
  decide +kernel

theorem context_13_1204277_1028168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1204277 ⟨1028168, by decide⟩ :=
  accepted_of_selected 13 1204277 ⟨1028168, by decide⟩ ⟨13, 2, 0, 1028168, 1204277, 965, 16384⟩
    (by decide) selected_cut_38204

theorem selected_cut_38205 : selected 8 ⟨1028187, by decide⟩
    (prefixPartial 13 1204278) = some ⟨13, 2, 0, 1028187, 1204278, 941, 16384⟩ := by
  decide +kernel

theorem context_13_1204278_1028187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1204278 ⟨1028187, by decide⟩ :=
  accepted_of_selected 13 1204278 ⟨1028187, by decide⟩ ⟨13, 2, 0, 1028187, 1204278, 941, 16384⟩
    (by decide) selected_cut_38205

theorem selected_cut_38206 : selected 8 ⟨1028193, by decide⟩
    (prefixPartial 13 1204279) = some ⟨13, 2, 0, 1028193, 1204279, 617, 16384⟩ := by
  decide +kernel

theorem context_13_1204279_1028193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1204279 ⟨1028193, by decide⟩ :=
  accepted_of_selected 13 1204279 ⟨1028193, by decide⟩ ⟨13, 2, 0, 1028193, 1204279, 617, 16384⟩
    (by decide) selected_cut_38206

theorem unmarked_context_12_301069_1028194 : frontier 9 ⟨1028194, by decide⟩
    (prefixCache 12 301069) (prefixPartial 12 301069) = false := by
  decide +kernel

theorem node_context_12_301069_1028194 : EJMOriginalGlobalDAGData.nodes 9 ⟨1028194, by decide⟩ =
    .split (coordinate 12) (![⟨1028155, by decide⟩,⟨1028168, by decide⟩,⟨1028187, by decide⟩,⟨1028193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301069_1028194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301069 ⟨1028194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301069
    ⟨1028194, by decide⟩ (by decide) (![⟨1028155, by decide⟩,⟨1028168, by decide⟩,⟨1028187, by decide⟩,⟨1028193, by decide⟩]) unmarked_context_12_301069_1028194 node_context_12_301069_1028194
  intro a
  fin_cases a
  · exact context_13_1204276_1028155
  · exact context_13_1204277_1028168
  · exact context_13_1204278_1028187
  · exact context_13_1204279_1028193

theorem selected_cut_38207 : selected 9 ⟨1028271, by decide⟩
    (prefixPartial 12 301070) = some ⟨12, 2, 0, 1028271, 301070, 3977, 65536⟩ := by
  decide +kernel

theorem context_12_301070_1028271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301070 ⟨1028271, by decide⟩ :=
  accepted_of_selected 12 301070 ⟨1028271, by decide⟩ ⟨12, 2, 0, 1028271, 301070, 3977, 65536⟩
    (by decide) selected_cut_38207

theorem selected_cut_38208 : selected 9 ⟨1028332, by decide⟩
    (prefixPartial 12 301071) = some ⟨12, 2, 0, 1028332, 301071, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_301071_1028332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301071 ⟨1028332, by decide⟩ :=
  accepted_of_selected 12 301071 ⟨1028332, by decide⟩ ⟨12, 2, 0, 1028332, 301071, 3633, 65536⟩
    (by decide) selected_cut_38208

theorem unmarked_context_11_75267_1028333 : frontier 10 ⟨1028333, by decide⟩
    (prefixCache 11 75267) (prefixPartial 11 75267) = false := by
  decide +kernel

theorem node_context_11_75267_1028333 : EJMOriginalGlobalDAGData.nodes 10 ⟨1028333, by decide⟩ =
    .split (coordinate 11) (![⟨1028116, by decide⟩,⟨1028194, by decide⟩,⟨1028271, by decide⟩,⟨1028332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75267_1028333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75267 ⟨1028333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75267
    ⟨1028333, by decide⟩ (by decide) (![⟨1028116, by decide⟩,⟨1028194, by decide⟩,⟨1028271, by decide⟩,⟨1028332, by decide⟩]) unmarked_context_11_75267_1028333 node_context_11_75267_1028333
  intro a
  fin_cases a
  · exact context_12_301068_1028116
  · exact context_12_301069_1028194
  · exact context_12_301070_1028271
  · exact context_12_301071_1028332

theorem unmarked_context_10_18816_1028334 : frontier 11 ⟨1028334, by decide⟩
    (prefixCache 10 18816) (prefixPartial 10 18816) = false := by
  decide +kernel

theorem node_context_10_18816_1028334 : EJMOriginalGlobalDAGData.nodes 11 ⟨1028334, by decide⟩ =
    .split (coordinate 10) (![⟨1027544, by decide⟩,⟨1027842, by decide⟩,⟨1028051, by decide⟩,⟨1028333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18816_1028334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18816 ⟨1028334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18816
    ⟨1028334, by decide⟩ (by decide) (![⟨1027544, by decide⟩,⟨1027842, by decide⟩,⟨1028051, by decide⟩,⟨1028333, by decide⟩]) unmarked_context_10_18816_1028334 node_context_10_18816_1028334
  intro a
  fin_cases a
  · exact context_11_75264_1027544
  · exact context_11_75265_1027842
  · exact context_11_75266_1028051
  · exact context_11_75267_1028333

theorem selected_cut_38209 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 301072) = some ⟨12, 1, 0, 985390, 301072, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301072_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301072 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 301072 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 301072, 1, 65536⟩
    (by decide) selected_cut_38209

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
