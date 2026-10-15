/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover423
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_40706 : selected 9 ⟨1108410, by decide⟩
    (prefixPartial 12 331802) = some ⟨12, 2, 0, 1108410, 331802, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_331802_1108410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331802 ⟨1108410, by decide⟩ :=
  accepted_of_selected 12 331802 ⟨1108410, by decide⟩ ⟨12, 2, 0, 1108410, 331802, 1949, 65536⟩
    (by decide) selected_cut_40706

theorem selected_cut_40707 : selected 9 ⟨1108462, by decide⟩
    (prefixPartial 12 331803) = some ⟨12, 2, 0, 1108462, 331803, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_331803_1108462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331803 ⟨1108462, by decide⟩ :=
  accepted_of_selected 12 331803 ⟨1108462, by decide⟩ ⟨12, 2, 0, 1108462, 331803, 2161, 65536⟩
    (by decide) selected_cut_40707

theorem unmarked_context_11_82950_1108463 : frontier 10 ⟨1108463, by decide⟩
    (prefixCache 11 82950) (prefixPartial 11 82950) = false := by
  decide +kernel

theorem node_context_11_82950_1108463 : EJMOriginalGlobalDAGData.nodes 10 ⟨1108463, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1108376, by decide⟩,⟨1108410, by decide⟩,⟨1108462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_82950_1108463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82950 ⟨1108463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 82950
    ⟨1108463, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1108376, by decide⟩,⟨1108410, by decide⟩,⟨1108462, by decide⟩]) unmarked_context_11_82950_1108463 node_context_11_82950_1108463
  intro a
  fin_cases a
  · exact context_12_331800_1108174
  · exact context_12_331801_1108376
  · exact context_12_331802_1108410
  · exact context_12_331803_1108462

theorem selected_cut_40708 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 82951) = some ⟨11, 1, 0, 1736, 82951, 1, 262144⟩ := by
  decide +kernel

theorem context_11_82951_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82951 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 82951 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 82951, 1, 262144⟩
    (by decide) selected_cut_40708

theorem unmarked_context_10_20737_1108464 : frontier 11 ⟨1108464, by decide⟩
    (prefixCache 10 20737) (prefixPartial 10 20737) = false := by
  decide +kernel

theorem node_context_10_20737_1108464 : EJMOriginalGlobalDAGData.nodes 11 ⟨1108464, by decide⟩ =
    .split (coordinate 10) (![⟨1108255, by decide⟩,⟨1108307, by decide⟩,⟨1108463, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20737_1108464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20737 ⟨1108464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20737
    ⟨1108464, by decide⟩ (by decide) (![⟨1108255, by decide⟩,⟨1108307, by decide⟩,⟨1108463, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_20737_1108464 node_context_10_20737_1108464
  intro a
  fin_cases a
  · exact context_11_82948_1108255
  · exact context_11_82949_1108307
  · exact context_11_82950_1108463
  · exact context_11_82951_1736

theorem selected_cut_40709 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 331808) = some ⟨12, 1, 0, 1108174, 331808, 1, 65536⟩ := by
  decide +kernel

theorem context_12_331808_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331808 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 331808 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 331808, 1, 65536⟩
    (by decide) selected_cut_40709

theorem selected_cut_40710 : selected 9 ⟨1108504, by decide⟩
    (prefixPartial 12 331809) = some ⟨12, 2, 0, 1108504, 331809, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_331809_1108504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331809 ⟨1108504, by decide⟩ :=
  accepted_of_selected 12 331809 ⟨1108504, by decide⟩ ⟨12, 2, 0, 1108504, 331809, 1921, 65536⟩
    (by decide) selected_cut_40710

theorem selected_cut_40711 : selected 9 ⟨1108546, by decide⟩
    (prefixPartial 12 331810) = some ⟨12, 2, 0, 1108546, 331810, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_331810_1108546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331810 ⟨1108546, by decide⟩ :=
  accepted_of_selected 12 331810 ⟨1108546, by decide⟩ ⟨12, 2, 0, 1108546, 331810, 1793, 65536⟩
    (by decide) selected_cut_40711

theorem selected_cut_40712 : selected 9 ⟨1108585, by decide⟩
    (prefixPartial 12 331811) = some ⟨12, 2, 0, 1108585, 331811, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_331811_1108585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331811 ⟨1108585, by decide⟩ :=
  accepted_of_selected 12 331811 ⟨1108585, by decide⟩ ⟨12, 2, 0, 1108585, 331811, 1725, 65536⟩
    (by decide) selected_cut_40712

theorem unmarked_context_11_82952_1108586 : frontier 10 ⟨1108586, by decide⟩
    (prefixCache 11 82952) (prefixPartial 11 82952) = false := by
  decide +kernel

theorem node_context_11_82952_1108586 : EJMOriginalGlobalDAGData.nodes 10 ⟨1108586, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1108504, by decide⟩,⟨1108546, by decide⟩,⟨1108585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_82952_1108586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82952 ⟨1108586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 82952
    ⟨1108586, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1108504, by decide⟩,⟨1108546, by decide⟩,⟨1108585, by decide⟩]) unmarked_context_11_82952_1108586 node_context_11_82952_1108586
  intro a
  fin_cases a
  · exact context_12_331808_1108174
  · exact context_12_331809_1108504
  · exact context_12_331810_1108546
  · exact context_12_331811_1108585

theorem selected_cut_40713 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 331812) = some ⟨12, 1, 0, 1108174, 331812, 1, 65536⟩ := by
  decide +kernel

theorem context_12_331812_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331812 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 331812 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 331812, 1, 65536⟩
    (by decide) selected_cut_40713

theorem selected_cut_40714 : selected 9 ⟨1108651, by decide⟩
    (prefixPartial 12 331813) = some ⟨12, 2, 0, 1108651, 331813, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_331813_1108651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331813 ⟨1108651, by decide⟩ :=
  accepted_of_selected 12 331813 ⟨1108651, by decide⟩ ⟨12, 2, 0, 1108651, 331813, 2213, 65536⟩
    (by decide) selected_cut_40714

theorem selected_cut_40715 : selected 9 ⟨1108691, by decide⟩
    (prefixPartial 12 331814) = some ⟨12, 2, 0, 1108691, 331814, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_331814_1108691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331814 ⟨1108691, by decide⟩ :=
  accepted_of_selected 12 331814 ⟨1108691, by decide⟩ ⟨12, 2, 0, 1108691, 331814, 1897, 65536⟩
    (by decide) selected_cut_40715

theorem selected_cut_40716 : selected 9 ⟨1108730, by decide⟩
    (prefixPartial 12 331815) = some ⟨12, 2, 0, 1108730, 331815, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_331815_1108730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331815 ⟨1108730, by decide⟩ :=
  accepted_of_selected 12 331815 ⟨1108730, by decide⟩ ⟨12, 2, 0, 1108730, 331815, 1821, 65536⟩
    (by decide) selected_cut_40716

theorem unmarked_context_11_82953_1108731 : frontier 10 ⟨1108731, by decide⟩
    (prefixCache 11 82953) (prefixPartial 11 82953) = false := by
  decide +kernel

theorem node_context_11_82953_1108731 : EJMOriginalGlobalDAGData.nodes 10 ⟨1108731, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1108651, by decide⟩,⟨1108691, by decide⟩,⟨1108730, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_82953_1108731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82953 ⟨1108731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 82953
    ⟨1108731, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1108651, by decide⟩,⟨1108691, by decide⟩,⟨1108730, by decide⟩]) unmarked_context_11_82953_1108731 node_context_11_82953_1108731
  intro a
  fin_cases a
  · exact context_12_331812_1108174
  · exact context_12_331813_1108651
  · exact context_12_331814_1108691
  · exact context_12_331815_1108730

theorem selected_cut_40717 : selected 10 ⟨1108826, by decide⟩
    (prefixPartial 11 82954) = some ⟨11, 2, 0, 1108826, 82954, 3645, 262144⟩ := by
  decide +kernel

theorem context_11_82954_1108826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82954 ⟨1108826, by decide⟩ :=
  accepted_of_selected 11 82954 ⟨1108826, by decide⟩ ⟨11, 2, 0, 1108826, 82954, 3645, 262144⟩
    (by decide) selected_cut_40717

theorem selected_cut_40718 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 331820) = some ⟨12, 1, 0, 1108174, 331820, 1, 65536⟩ := by
  decide +kernel

theorem context_12_331820_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331820 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 331820 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 331820, 1, 65536⟩
    (by decide) selected_cut_40718

theorem selected_cut_40719 : selected 9 ⟨1108868, by decide⟩
    (prefixPartial 12 331821) = some ⟨12, 2, 0, 1108868, 331821, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_331821_1108868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331821 ⟨1108868, by decide⟩ :=
  accepted_of_selected 12 331821 ⟨1108868, by decide⟩ ⟨12, 2, 0, 1108868, 331821, 1777, 65536⟩
    (by decide) selected_cut_40719

theorem selected_cut_40720 : selected 9 ⟨1108913, by decide⟩
    (prefixPartial 12 331822) = some ⟨12, 2, 0, 1108913, 331822, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_331822_1108913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331822 ⟨1108913, by decide⟩ :=
  accepted_of_selected 12 331822 ⟨1108913, by decide⟩ ⟨12, 2, 0, 1108913, 331822, 1749, 65536⟩
    (by decide) selected_cut_40720

theorem selected_cut_40721 : selected 9 ⟨1108945, by decide⟩
    (prefixPartial 12 331823) = some ⟨12, 2, 0, 1108945, 331823, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_331823_1108945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331823 ⟨1108945, by decide⟩ :=
  accepted_of_selected 12 331823 ⟨1108945, by decide⟩ ⟨12, 2, 0, 1108945, 331823, 1477, 65536⟩
    (by decide) selected_cut_40721

theorem unmarked_context_11_82955_1108946 : frontier 10 ⟨1108946, by decide⟩
    (prefixCache 11 82955) (prefixPartial 11 82955) = false := by
  decide +kernel

theorem node_context_11_82955_1108946 : EJMOriginalGlobalDAGData.nodes 10 ⟨1108946, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1108868, by decide⟩,⟨1108913, by decide⟩,⟨1108945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_82955_1108946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82955 ⟨1108946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 82955
    ⟨1108946, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1108868, by decide⟩,⟨1108913, by decide⟩,⟨1108945, by decide⟩]) unmarked_context_11_82955_1108946 node_context_11_82955_1108946
  intro a
  fin_cases a
  · exact context_12_331820_1108174
  · exact context_12_331821_1108868
  · exact context_12_331822_1108913
  · exact context_12_331823_1108945

theorem unmarked_context_10_20738_1108947 : frontier 11 ⟨1108947, by decide⟩
    (prefixCache 10 20738) (prefixPartial 10 20738) = false := by
  decide +kernel

theorem node_context_10_20738_1108947 : EJMOriginalGlobalDAGData.nodes 11 ⟨1108947, by decide⟩ =
    .split (coordinate 10) (![⟨1108586, by decide⟩,⟨1108731, by decide⟩,⟨1108826, by decide⟩,⟨1108946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20738_1108947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20738 ⟨1108947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20738
    ⟨1108947, by decide⟩ (by decide) (![⟨1108586, by decide⟩,⟨1108731, by decide⟩,⟨1108826, by decide⟩,⟨1108946, by decide⟩]) unmarked_context_10_20738_1108947 node_context_10_20738_1108947
  intro a
  fin_cases a
  · exact context_11_82952_1108586
  · exact context_11_82953_1108731
  · exact context_11_82954_1108826
  · exact context_11_82955_1108946

theorem selected_cut_40722 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 20739) = some ⟨10, 1, 0, 3440, 20739, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20739_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20739 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 20739 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 20739, 1, 1048576⟩
    (by decide) selected_cut_40722

theorem unmarked_context_9_5184_1108948 : frontier 12 ⟨1108948, by decide⟩
    (prefixCache 9 5184) (prefixPartial 9 5184) = false := by
  decide +kernel

theorem node_context_9_5184_1108948 : EJMOriginalGlobalDAGData.nodes 12 ⟨1108948, by decide⟩ =
    .split (coordinate 9) (![⟨1108173, by decide⟩,⟨1108464, by decide⟩,⟨1108947, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5184_1108948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5184 ⟨1108948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5184
    ⟨1108948, by decide⟩ (by decide) (![⟨1108173, by decide⟩,⟨1108464, by decide⟩,⟨1108947, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_5184_1108948 node_context_9_5184_1108948
  intro a
  fin_cases a
  · exact context_10_20736_1108173
  · exact context_10_20737_1108464
  · exact context_10_20738_1108947
  · exact context_10_20739_3440

theorem selected_cut_40723 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 20740) = some ⟨10, 1, 0, 3442, 20740, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20740_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20740 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 20740 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 20740, 1, 1048576⟩
    (by decide) selected_cut_40723

theorem selected_cut_40724 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 20741) = some ⟨10, 1, 0, 893098, 20741, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20741_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20741 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 20741 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 20741, 1, 1048576⟩
    (by decide) selected_cut_40724

theorem selected_cut_40725 : selected 10 ⟨1109056, by decide⟩
    (prefixPartial 11 82968) = some ⟨11, 2, 0, 1109056, 82968, 3869, 262144⟩ := by
  decide +kernel

theorem context_11_82968_1109056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82968 ⟨1109056, by decide⟩ :=
  accepted_of_selected 11 82968 ⟨1109056, by decide⟩ ⟨11, 2, 0, 1109056, 82968, 3869, 262144⟩
    (by decide) selected_cut_40725

theorem selected_cut_40726 : selected 10 ⟨1109151, by decide⟩
    (prefixPartial 11 82969) = some ⟨11, 2, 0, 1109151, 82969, 3433, 262144⟩ := by
  decide +kernel

theorem context_11_82969_1109151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82969 ⟨1109151, by decide⟩ :=
  accepted_of_selected 11 82969 ⟨1109151, by decide⟩ ⟨11, 2, 0, 1109151, 82969, 3433, 262144⟩
    (by decide) selected_cut_40726

theorem selected_cut_40727 : selected 10 ⟨1109253, by decide⟩
    (prefixPartial 11 82970) = some ⟨11, 2, 0, 1109253, 82970, 3205, 262144⟩ := by
  decide +kernel

theorem context_11_82970_1109253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82970 ⟨1109253, by decide⟩ :=
  accepted_of_selected 11 82970 ⟨1109253, by decide⟩ ⟨11, 2, 0, 1109253, 82970, 3205, 262144⟩
    (by decide) selected_cut_40727

theorem selected_cut_40728 : selected 10 ⟨1109357, by decide⟩
    (prefixPartial 11 82971) = some ⟨11, 2, 0, 1109357, 82971, 3377, 262144⟩ := by
  decide +kernel

theorem context_11_82971_1109357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82971 ⟨1109357, by decide⟩ :=
  accepted_of_selected 11 82971 ⟨1109357, by decide⟩ ⟨11, 2, 0, 1109357, 82971, 3377, 262144⟩
    (by decide) selected_cut_40728

theorem unmarked_context_10_20742_1109358 : frontier 11 ⟨1109358, by decide⟩
    (prefixCache 10 20742) (prefixPartial 10 20742) = false := by
  decide +kernel

theorem node_context_10_20742_1109358 : EJMOriginalGlobalDAGData.nodes 11 ⟨1109358, by decide⟩ =
    .split (coordinate 10) (![⟨1109056, by decide⟩,⟨1109151, by decide⟩,⟨1109253, by decide⟩,⟨1109357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20742_1109358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20742 ⟨1109358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20742
    ⟨1109358, by decide⟩ (by decide) (![⟨1109056, by decide⟩,⟨1109151, by decide⟩,⟨1109253, by decide⟩,⟨1109357, by decide⟩]) unmarked_context_10_20742_1109358 node_context_10_20742_1109358
  intro a
  fin_cases a
  · exact context_11_82968_1109056
  · exact context_11_82969_1109151
  · exact context_11_82970_1109253
  · exact context_11_82971_1109357

theorem selected_cut_40729 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 20743) = some ⟨10, 1, 0, 3440, 20743, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20743_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20743 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 20743 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 20743, 1, 1048576⟩
    (by decide) selected_cut_40729

theorem unmarked_context_9_5185_1109359 : frontier 12 ⟨1109359, by decide⟩
    (prefixCache 9 5185) (prefixPartial 9 5185) = false := by
  decide +kernel

theorem node_context_9_5185_1109359 : EJMOriginalGlobalDAGData.nodes 12 ⟨1109359, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1109358, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5185_1109359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5185 ⟨1109359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5185
    ⟨1109359, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1109358, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_5185_1109359 node_context_9_5185_1109359
  intro a
  fin_cases a
  · exact context_10_20740_3442
  · exact context_10_20741_893098
  · exact context_10_20742_1109358
  · exact context_10_20743_3440

theorem selected_cut_40730 : selected 12 ⟨1109532, by decide⟩
    (prefixPartial 9 5186) = some ⟨9, 2, 0, 1109532, 5186, 3901, 4194304⟩ := by
  decide +kernel

theorem context_9_5186_1109532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5186 ⟨1109532, by decide⟩ :=
  accepted_of_selected 9 5186 ⟨1109532, by decide⟩ ⟨9, 2, 0, 1109532, 5186, 3901, 4194304⟩
    (by decide) selected_cut_40730

theorem selected_cut_40731 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 5187) = some ⟨9, 1, 0, 4601, 5187, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_5187_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5187 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 5187 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 5187, 1, 4194304⟩
    (by decide) selected_cut_40731

theorem unmarked_context_8_1296_1109533 : frontier 13 ⟨1109533, by decide⟩
    (prefixCache 8 1296) (prefixPartial 8 1296) = false := by
  decide +kernel

theorem node_context_8_1296_1109533 : EJMOriginalGlobalDAGData.nodes 13 ⟨1109533, by decide⟩ =
    .split (coordinate 8) (![⟨1108948, by decide⟩,⟨1109359, by decide⟩,⟨1109532, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1296_1109533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1296 ⟨1109533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1296
    ⟨1109533, by decide⟩ (by decide) (![⟨1108948, by decide⟩,⟨1109359, by decide⟩,⟨1109532, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_1296_1109533 node_context_8_1296_1109533
  intro a
  fin_cases a
  · exact context_9_5184_1108948
  · exact context_9_5185_1109359
  · exact context_9_5186_1109532
  · exact context_9_5187_4601

theorem selected_cut_40732 : selected 13 ⟨1109534, by decide⟩
    (prefixPartial 8 1297) = some ⟨8, 1, 0, 1109534, 1297, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1297_1109534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1297 ⟨1109534, by decide⟩ :=
  accepted_of_selected 8 1297 ⟨1109534, by decide⟩ ⟨8, 1, 0, 1109534, 1297, 1, 16777216⟩
    (by decide) selected_cut_40732

theorem selected_cut_40733 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 83072) = some ⟨11, 1, 0, 434745, 83072, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83072_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83072 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 83072 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 83072, 1, 262144⟩
    (by decide) selected_cut_40733

theorem selected_cut_40734 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 332292) = some ⟨12, 1, 0, 895, 332292, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332292_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332292 ⟨895, by decide⟩ :=
  accepted_of_selected 12 332292 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 332292, 1, 65536⟩
    (by decide) selected_cut_40734

theorem selected_cut_40735 : selected 9 ⟨1109632, by decide⟩
    (prefixPartial 12 332293) = some ⟨12, 2, 0, 1109632, 332293, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_332293_1109632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332293 ⟨1109632, by decide⟩ :=
  accepted_of_selected 12 332293 ⟨1109632, by decide⟩ ⟨12, 2, 0, 1109632, 332293, 2153, 65536⟩
    (by decide) selected_cut_40735

theorem selected_cut_40736 : selected 9 ⟨1109734, by decide⟩
    (prefixPartial 12 332294) = some ⟨12, 2, 0, 1109734, 332294, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_332294_1109734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332294 ⟨1109734, by decide⟩ :=
  accepted_of_selected 12 332294 ⟨1109734, by decide⟩ ⟨12, 2, 0, 1109734, 332294, 2793, 65536⟩
    (by decide) selected_cut_40736

theorem selected_cut_40737 : selected 9 ⟨1109802, by decide⟩
    (prefixPartial 12 332295) = some ⟨12, 2, 0, 1109802, 332295, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_332295_1109802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332295 ⟨1109802, by decide⟩ :=
  accepted_of_selected 12 332295 ⟨1109802, by decide⟩ ⟨12, 2, 0, 1109802, 332295, 2737, 65536⟩
    (by decide) selected_cut_40737

theorem unmarked_context_11_83073_1109803 : frontier 10 ⟨1109803, by decide⟩
    (prefixCache 11 83073) (prefixPartial 11 83073) = false := by
  decide +kernel

theorem node_context_11_83073_1109803 : EJMOriginalGlobalDAGData.nodes 10 ⟨1109803, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨1109632, by decide⟩,⟨1109734, by decide⟩,⟨1109802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83073_1109803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83073 ⟨1109803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83073
    ⟨1109803, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨1109632, by decide⟩,⟨1109734, by decide⟩,⟨1109802, by decide⟩]) unmarked_context_11_83073_1109803 node_context_11_83073_1109803
  intro a
  fin_cases a
  · exact context_12_332292_895
  · exact context_12_332293_1109632
  · exact context_12_332294_1109734
  · exact context_12_332295_1109802

theorem selected_cut_40738 : selected 10 ⟨1109876, by decide⟩
    (prefixPartial 11 83074) = some ⟨11, 2, 0, 1109876, 83074, 2737, 262144⟩ := by
  decide +kernel

theorem context_11_83074_1109876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83074 ⟨1109876, by decide⟩ :=
  accepted_of_selected 11 83074 ⟨1109876, by decide⟩ ⟨11, 2, 0, 1109876, 83074, 2737, 262144⟩
    (by decide) selected_cut_40738

theorem selected_cut_40739 : selected 10 ⟨1109924, by decide⟩
    (prefixPartial 11 83075) = some ⟨11, 2, 0, 1109924, 83075, 1429, 262144⟩ := by
  decide +kernel

theorem context_11_83075_1109924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83075 ⟨1109924, by decide⟩ :=
  accepted_of_selected 11 83075 ⟨1109924, by decide⟩ ⟨11, 2, 0, 1109924, 83075, 1429, 262144⟩
    (by decide) selected_cut_40739

theorem unmarked_context_10_20768_1109925 : frontier 11 ⟨1109925, by decide⟩
    (prefixCache 10 20768) (prefixPartial 10 20768) = false := by
  decide +kernel

theorem node_context_10_20768_1109925 : EJMOriginalGlobalDAGData.nodes 11 ⟨1109925, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1109803, by decide⟩,⟨1109876, by decide⟩,⟨1109924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20768_1109925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20768 ⟨1109925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20768
    ⟨1109925, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1109803, by decide⟩,⟨1109876, by decide⟩,⟨1109924, by decide⟩]) unmarked_context_10_20768_1109925 node_context_10_20768_1109925
  intro a
  fin_cases a
  · exact context_11_83072_434745
  · exact context_11_83073_1109803
  · exact context_11_83074_1109876
  · exact context_11_83075_1109924

theorem selected_cut_40740 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 332304) = some ⟨12, 1, 0, 1108174, 332304, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332304_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332304 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 332304 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 332304, 1, 65536⟩
    (by decide) selected_cut_40740

theorem selected_cut_40741 : selected 9 ⟨1109985, by decide⟩
    (prefixPartial 12 332305) = some ⟨12, 2, 0, 1109985, 332305, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_332305_1109985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332305 ⟨1109985, by decide⟩ :=
  accepted_of_selected 12 332305 ⟨1109985, by decide⟩ ⟨12, 2, 0, 1109985, 332305, 2797, 65536⟩
    (by decide) selected_cut_40741

theorem selected_cut_40742 : selected 9 ⟨1110033, by decide⟩
    (prefixPartial 12 332306) = some ⟨12, 2, 0, 1110033, 332306, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_332306_1110033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332306 ⟨1110033, by decide⟩ :=
  accepted_of_selected 12 332306 ⟨1110033, by decide⟩ ⟨12, 2, 0, 1110033, 332306, 2453, 65536⟩
    (by decide) selected_cut_40742

theorem selected_cut_40743 : selected 9 ⟨1110085, by decide⟩
    (prefixPartial 12 332307) = some ⟨12, 2, 0, 1110085, 332307, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_332307_1110085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332307 ⟨1110085, by decide⟩ :=
  accepted_of_selected 12 332307 ⟨1110085, by decide⟩ ⟨12, 2, 0, 1110085, 332307, 2825, 65536⟩
    (by decide) selected_cut_40743

theorem unmarked_context_11_83076_1110086 : frontier 10 ⟨1110086, by decide⟩
    (prefixCache 11 83076) (prefixPartial 11 83076) = false := by
  decide +kernel

theorem node_context_11_83076_1110086 : EJMOriginalGlobalDAGData.nodes 10 ⟨1110086, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1109985, by decide⟩,⟨1110033, by decide⟩,⟨1110085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83076_1110086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83076 ⟨1110086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83076
    ⟨1110086, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1109985, by decide⟩,⟨1110033, by decide⟩,⟨1110085, by decide⟩]) unmarked_context_11_83076_1110086 node_context_11_83076_1110086
  intro a
  fin_cases a
  · exact context_12_332304_1108174
  · exact context_12_332305_1109985
  · exact context_12_332306_1110033
  · exact context_12_332307_1110085

theorem selected_cut_40744 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 332308) = some ⟨12, 1, 0, 1108174, 332308, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332308_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332308 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 332308 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 332308, 1, 65536⟩
    (by decide) selected_cut_40744

theorem selected_cut_40745 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 332309) = some ⟨12, 1, 0, 308705, 332309, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332309_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332309 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 332309 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 332309, 1, 65536⟩
    (by decide) selected_cut_40745

theorem selected_cut_40746 : selected 9 ⟨1110153, by decide⟩
    (prefixPartial 12 332310) = some ⟨12, 2, 0, 1110153, 332310, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_332310_1110153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332310 ⟨1110153, by decide⟩ :=
  accepted_of_selected 12 332310 ⟨1110153, by decide⟩ ⟨12, 2, 0, 1110153, 332310, 2609, 65536⟩
    (by decide) selected_cut_40746

theorem selected_cut_40747 : selected 9 ⟨1110214, by decide⟩
    (prefixPartial 12 332311) = some ⟨12, 2, 0, 1110214, 332311, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_332311_1110214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332311 ⟨1110214, by decide⟩ :=
  accepted_of_selected 12 332311 ⟨1110214, by decide⟩ ⟨12, 2, 0, 1110214, 332311, 2793, 65536⟩
    (by decide) selected_cut_40747

theorem unmarked_context_11_83077_1110215 : frontier 10 ⟨1110215, by decide⟩
    (prefixCache 11 83077) (prefixPartial 11 83077) = false := by
  decide +kernel

theorem node_context_11_83077_1110215 : EJMOriginalGlobalDAGData.nodes 10 ⟨1110215, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨308705, by decide⟩,⟨1110153, by decide⟩,⟨1110214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83077_1110215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83077 ⟨1110215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83077
    ⟨1110215, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨308705, by decide⟩,⟨1110153, by decide⟩,⟨1110214, by decide⟩]) unmarked_context_11_83077_1110215 node_context_11_83077_1110215
  intro a
  fin_cases a
  · exact context_12_332308_1108174
  · exact context_12_332309_308705
  · exact context_12_332310_1110153
  · exact context_12_332311_1110214

theorem selected_cut_40748 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 332312) = some ⟨12, 1, 0, 1108174, 332312, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332312_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332312 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 332312 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 332312, 1, 65536⟩
    (by decide) selected_cut_40748

theorem selected_cut_40749 : selected 9 ⟨1110271, by decide⟩
    (prefixPartial 12 332313) = some ⟨12, 2, 0, 1110271, 332313, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_332313_1110271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332313 ⟨1110271, by decide⟩ :=
  accepted_of_selected 12 332313 ⟨1110271, by decide⟩ ⟨12, 2, 0, 1110271, 332313, 2641, 65536⟩
    (by decide) selected_cut_40749

theorem selected_cut_40750 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 332314) = some ⟨12, 1, 0, 893903, 332314, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332314_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332314 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 332314 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 332314, 1, 65536⟩
    (by decide) selected_cut_40750

theorem selected_cut_40751 : selected 9 ⟨1110342, by decide⟩
    (prefixPartial 12 332315) = some ⟨12, 2, 0, 1110342, 332315, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_332315_1110342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332315 ⟨1110342, by decide⟩ :=
  accepted_of_selected 12 332315 ⟨1110342, by decide⟩ ⟨12, 2, 0, 1110342, 332315, 2781, 65536⟩
    (by decide) selected_cut_40751

theorem unmarked_context_11_83078_1110343 : frontier 10 ⟨1110343, by decide⟩
    (prefixCache 11 83078) (prefixPartial 11 83078) = false := by
  decide +kernel

theorem node_context_11_83078_1110343 : EJMOriginalGlobalDAGData.nodes 10 ⟨1110343, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1110271, by decide⟩,⟨893903, by decide⟩,⟨1110342, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83078_1110343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83078 ⟨1110343, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83078
    ⟨1110343, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1110271, by decide⟩,⟨893903, by decide⟩,⟨1110342, by decide⟩]) unmarked_context_11_83078_1110343 node_context_11_83078_1110343
  intro a
  fin_cases a
  · exact context_12_332312_1108174
  · exact context_12_332313_1110271
  · exact context_12_332314_893903
  · exact context_12_332315_1110342

theorem selected_cut_40752 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 332316) = some ⟨12, 1, 0, 1108174, 332316, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332316_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332316 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 332316 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 332316, 1, 65536⟩
    (by decide) selected_cut_40752

theorem selected_cut_40753 : selected 9 ⟨1110392, by decide⟩
    (prefixPartial 12 332317) = some ⟨12, 2, 0, 1110392, 332317, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_332317_1110392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332317 ⟨1110392, by decide⟩ :=
  accepted_of_selected 12 332317 ⟨1110392, by decide⟩ ⟨12, 2, 0, 1110392, 332317, 2569, 65536⟩
    (by decide) selected_cut_40753

theorem selected_cut_40754 : selected 9 ⟨1110440, by decide⟩
    (prefixPartial 12 332318) = some ⟨12, 2, 0, 1110440, 332318, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_332318_1110440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332318 ⟨1110440, by decide⟩ :=
  accepted_of_selected 12 332318 ⟨1110440, by decide⟩ ⟨12, 2, 0, 1110440, 332318, 2361, 65536⟩
    (by decide) selected_cut_40754

theorem selected_cut_40755 : selected 9 ⟨1110481, by decide⟩
    (prefixPartial 12 332319) = some ⟨12, 2, 0, 1110481, 332319, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_332319_1110481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332319 ⟨1110481, by decide⟩ :=
  accepted_of_selected 12 332319 ⟨1110481, by decide⟩ ⟨12, 2, 0, 1110481, 332319, 2133, 65536⟩
    (by decide) selected_cut_40755

theorem unmarked_context_11_83079_1110482 : frontier 10 ⟨1110482, by decide⟩
    (prefixCache 11 83079) (prefixPartial 11 83079) = false := by
  decide +kernel

theorem node_context_11_83079_1110482 : EJMOriginalGlobalDAGData.nodes 10 ⟨1110482, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1110392, by decide⟩,⟨1110440, by decide⟩,⟨1110481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83079_1110482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83079 ⟨1110482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83079
    ⟨1110482, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1110392, by decide⟩,⟨1110440, by decide⟩,⟨1110481, by decide⟩]) unmarked_context_11_83079_1110482 node_context_11_83079_1110482
  intro a
  fin_cases a
  · exact context_12_332316_1108174
  · exact context_12_332317_1110392
  · exact context_12_332318_1110440
  · exact context_12_332319_1110481

theorem unmarked_context_10_20769_1110483 : frontier 11 ⟨1110483, by decide⟩
    (prefixCache 10 20769) (prefixPartial 10 20769) = false := by
  decide +kernel

theorem node_context_10_20769_1110483 : EJMOriginalGlobalDAGData.nodes 11 ⟨1110483, by decide⟩ =
    .split (coordinate 10) (![⟨1110086, by decide⟩,⟨1110215, by decide⟩,⟨1110343, by decide⟩,⟨1110482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20769_1110483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20769 ⟨1110483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20769
    ⟨1110483, by decide⟩ (by decide) (![⟨1110086, by decide⟩,⟨1110215, by decide⟩,⟨1110343, by decide⟩,⟨1110482, by decide⟩]) unmarked_context_10_20769_1110483 node_context_10_20769_1110483
  intro a
  fin_cases a
  · exact context_11_83076_1110086
  · exact context_11_83077_1110215
  · exact context_11_83078_1110343
  · exact context_11_83079_1110482

theorem selected_cut_40756 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 332320) = some ⟨12, 1, 0, 1108174, 332320, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332320_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332320 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 332320 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 332320, 1, 65536⟩
    (by decide) selected_cut_40756

theorem selected_cut_40757 : selected 9 ⟨1110547, by decide⟩
    (prefixPartial 12 332321) = some ⟨12, 2, 0, 1110547, 332321, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_332321_1110547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332321 ⟨1110547, by decide⟩ :=
  accepted_of_selected 12 332321 ⟨1110547, by decide⟩ ⟨12, 2, 0, 1110547, 332321, 2641, 65536⟩
    (by decide) selected_cut_40757

theorem selected_cut_40758 : selected 9 ⟨1110592, by decide⟩
    (prefixPartial 12 332322) = some ⟨12, 2, 0, 1110592, 332322, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_332322_1110592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332322 ⟨1110592, by decide⟩ :=
  accepted_of_selected 12 332322 ⟨1110592, by decide⟩ ⟨12, 2, 0, 1110592, 332322, 2125, 65536⟩
    (by decide) selected_cut_40758

theorem selected_cut_40759 : selected 9 ⟨1110638, by decide⟩
    (prefixPartial 12 332323) = some ⟨12, 2, 0, 1110638, 332323, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_332323_1110638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332323 ⟨1110638, by decide⟩ :=
  accepted_of_selected 12 332323 ⟨1110638, by decide⟩ ⟨12, 2, 0, 1110638, 332323, 2393, 65536⟩
    (by decide) selected_cut_40759

theorem unmarked_context_11_83080_1110639 : frontier 10 ⟨1110639, by decide⟩
    (prefixCache 11 83080) (prefixPartial 11 83080) = false := by
  decide +kernel

theorem node_context_11_83080_1110639 : EJMOriginalGlobalDAGData.nodes 10 ⟨1110639, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1110547, by decide⟩,⟨1110592, by decide⟩,⟨1110638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83080_1110639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83080 ⟨1110639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83080
    ⟨1110639, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1110547, by decide⟩,⟨1110592, by decide⟩,⟨1110638, by decide⟩]) unmarked_context_11_83080_1110639 node_context_11_83080_1110639
  intro a
  fin_cases a
  · exact context_12_332320_1108174
  · exact context_12_332321_1110547
  · exact context_12_332322_1110592
  · exact context_12_332323_1110638

theorem selected_cut_40760 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 332324) = some ⟨12, 1, 0, 1108174, 332324, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332324_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332324 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 332324 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 332324, 1, 65536⟩
    (by decide) selected_cut_40760

theorem selected_cut_40761 : selected 9 ⟨1110738, by decide⟩
    (prefixPartial 12 332325) = some ⟨12, 2, 0, 1110738, 332325, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_332325_1110738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332325 ⟨1110738, by decide⟩ :=
  accepted_of_selected 12 332325 ⟨1110738, by decide⟩ ⟨12, 2, 0, 1110738, 332325, 3221, 65536⟩
    (by decide) selected_cut_40761

theorem selected_cut_40762 : selected 9 ⟨1110794, by decide⟩
    (prefixPartial 12 332326) = some ⟨12, 2, 0, 1110794, 332326, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_332326_1110794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332326 ⟨1110794, by decide⟩ :=
  accepted_of_selected 12 332326 ⟨1110794, by decide⟩ ⟨12, 2, 0, 1110794, 332326, 2265, 65536⟩
    (by decide) selected_cut_40762

theorem selected_cut_40763 : selected 9 ⟨1110846, by decide⟩
    (prefixPartial 12 332327) = some ⟨12, 2, 0, 1110846, 332327, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_332327_1110846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332327 ⟨1110846, by decide⟩ :=
  accepted_of_selected 12 332327 ⟨1110846, by decide⟩ ⟨12, 2, 0, 1110846, 332327, 2345, 65536⟩
    (by decide) selected_cut_40763

theorem unmarked_context_11_83081_1110847 : frontier 10 ⟨1110847, by decide⟩
    (prefixCache 11 83081) (prefixPartial 11 83081) = false := by
  decide +kernel

theorem node_context_11_83081_1110847 : EJMOriginalGlobalDAGData.nodes 10 ⟨1110847, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1110738, by decide⟩,⟨1110794, by decide⟩,⟨1110846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83081_1110847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83081 ⟨1110847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83081
    ⟨1110847, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1110738, by decide⟩,⟨1110794, by decide⟩,⟨1110846, by decide⟩]) unmarked_context_11_83081_1110847 node_context_11_83081_1110847
  intro a
  fin_cases a
  · exact context_12_332324_1108174
  · exact context_12_332325_1110738
  · exact context_12_332326_1110794
  · exact context_12_332327_1110846

theorem selected_cut_40764 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 332328) = some ⟨12, 1, 0, 1108174, 332328, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332328_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332328 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 332328 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 332328, 1, 65536⟩
    (by decide) selected_cut_40764

theorem selected_cut_40765 : selected 9 ⟨1110903, by decide⟩
    (prefixPartial 12 332329) = some ⟨12, 2, 0, 1110903, 332329, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_332329_1110903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332329 ⟨1110903, by decide⟩ :=
  accepted_of_selected 12 332329 ⟨1110903, by decide⟩ ⟨12, 2, 0, 1110903, 332329, 2557, 65536⟩
    (by decide) selected_cut_40765

theorem selected_cut_40766 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 332330) = some ⟨12, 1, 0, 474208, 332330, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332330_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332330 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 332330 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 332330, 1, 65536⟩
    (by decide) selected_cut_40766

theorem selected_cut_40767 : selected 9 ⟨1110969, by decide⟩
    (prefixPartial 12 332331) = some ⟨12, 2, 0, 1110969, 332331, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_332331_1110969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332331 ⟨1110969, by decide⟩ :=
  accepted_of_selected 12 332331 ⟨1110969, by decide⟩ ⟨12, 2, 0, 1110969, 332331, 2469, 65536⟩
    (by decide) selected_cut_40767

theorem unmarked_context_11_83082_1110970 : frontier 10 ⟨1110970, by decide⟩
    (prefixCache 11 83082) (prefixPartial 11 83082) = false := by
  decide +kernel

theorem node_context_11_83082_1110970 : EJMOriginalGlobalDAGData.nodes 10 ⟨1110970, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1110903, by decide⟩,⟨474208, by decide⟩,⟨1110969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83082_1110970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83082 ⟨1110970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83082
    ⟨1110970, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1110903, by decide⟩,⟨474208, by decide⟩,⟨1110969, by decide⟩]) unmarked_context_11_83082_1110970 node_context_11_83082_1110970
  intro a
  fin_cases a
  · exact context_12_332328_1108174
  · exact context_12_332329_1110903
  · exact context_12_332330_474208
  · exact context_12_332331_1110969

theorem selected_cut_40768 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 332332) = some ⟨12, 1, 0, 1108174, 332332, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332332_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332332 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 332332 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 332332, 1, 65536⟩
    (by decide) selected_cut_40768

theorem selected_cut_40769 : selected 9 ⟨1111021, by decide⟩
    (prefixPartial 12 332333) = some ⟨12, 2, 0, 1111021, 332333, 2409, 65536⟩ := by
  decide +kernel

theorem context_12_332333_1111021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332333 ⟨1111021, by decide⟩ :=
  accepted_of_selected 12 332333 ⟨1111021, by decide⟩ ⟨12, 2, 0, 1111021, 332333, 2409, 65536⟩
    (by decide) selected_cut_40769

theorem selected_cut_40770 : selected 9 ⟨1111066, by decide⟩
    (prefixPartial 12 332334) = some ⟨12, 2, 0, 1111066, 332334, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_332334_1111066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332334 ⟨1111066, by decide⟩ :=
  accepted_of_selected 12 332334 ⟨1111066, by decide⟩ ⟨12, 2, 0, 1111066, 332334, 2073, 65536⟩
    (by decide) selected_cut_40770

theorem selected_cut_40771 : selected 9 ⟨1111100, by decide⟩
    (prefixPartial 12 332335) = some ⟨12, 2, 0, 1111100, 332335, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_332335_1111100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332335 ⟨1111100, by decide⟩ :=
  accepted_of_selected 12 332335 ⟨1111100, by decide⟩ ⟨12, 2, 0, 1111100, 332335, 1897, 65536⟩
    (by decide) selected_cut_40771

theorem unmarked_context_11_83083_1111101 : frontier 10 ⟨1111101, by decide⟩
    (prefixCache 11 83083) (prefixPartial 11 83083) = false := by
  decide +kernel

theorem node_context_11_83083_1111101 : EJMOriginalGlobalDAGData.nodes 10 ⟨1111101, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1111021, by decide⟩,⟨1111066, by decide⟩,⟨1111100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83083_1111101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83083 ⟨1111101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83083
    ⟨1111101, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1111021, by decide⟩,⟨1111066, by decide⟩,⟨1111100, by decide⟩]) unmarked_context_11_83083_1111101 node_context_11_83083_1111101
  intro a
  fin_cases a
  · exact context_12_332332_1108174
  · exact context_12_332333_1111021
  · exact context_12_332334_1111066
  · exact context_12_332335_1111100

theorem unmarked_context_10_20770_1111102 : frontier 11 ⟨1111102, by decide⟩
    (prefixCache 10 20770) (prefixPartial 10 20770) = false := by
  decide +kernel

theorem node_context_10_20770_1111102 : EJMOriginalGlobalDAGData.nodes 11 ⟨1111102, by decide⟩ =
    .split (coordinate 10) (![⟨1110639, by decide⟩,⟨1110847, by decide⟩,⟨1110970, by decide⟩,⟨1111101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20770_1111102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20770 ⟨1111102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20770
    ⟨1111102, by decide⟩ (by decide) (![⟨1110639, by decide⟩,⟨1110847, by decide⟩,⟨1110970, by decide⟩,⟨1111101, by decide⟩]) unmarked_context_10_20770_1111102 node_context_10_20770_1111102
  intro a
  fin_cases a
  · exact context_11_83080_1110639
  · exact context_11_83081_1110847
  · exact context_11_83082_1110970
  · exact context_11_83083_1111101

theorem selected_cut_40772 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 332336) = some ⟨12, 1, 0, 1108174, 332336, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332336_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332336 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 332336 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 332336, 1, 65536⟩
    (by decide) selected_cut_40772

theorem selected_cut_40773 : selected 9 ⟨1111153, by decide⟩
    (prefixPartial 12 332337) = some ⟨12, 2, 0, 1111153, 332337, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_332337_1111153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332337 ⟨1111153, by decide⟩ :=
  accepted_of_selected 12 332337 ⟨1111153, by decide⟩ ⟨12, 2, 0, 1111153, 332337, 2037, 65536⟩
    (by decide) selected_cut_40773

theorem selected_cut_40774 : selected 9 ⟨1111191, by decide⟩
    (prefixPartial 12 332338) = some ⟨12, 2, 0, 1111191, 332338, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_332338_1111191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332338 ⟨1111191, by decide⟩ :=
  accepted_of_selected 12 332338 ⟨1111191, by decide⟩ ⟨12, 2, 0, 1111191, 332338, 1769, 65536⟩
    (by decide) selected_cut_40774

theorem selected_cut_40775 : selected 9 ⟨1111237, by decide⟩
    (prefixPartial 12 332339) = some ⟨12, 2, 0, 1111237, 332339, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_332339_1111237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332339 ⟨1111237, by decide⟩ :=
  accepted_of_selected 12 332339 ⟨1111237, by decide⟩ ⟨12, 2, 0, 1111237, 332339, 1869, 65536⟩
    (by decide) selected_cut_40775

theorem unmarked_context_11_83084_1111238 : frontier 10 ⟨1111238, by decide⟩
    (prefixCache 11 83084) (prefixPartial 11 83084) = false := by
  decide +kernel

theorem node_context_11_83084_1111238 : EJMOriginalGlobalDAGData.nodes 10 ⟨1111238, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1111153, by decide⟩,⟨1111191, by decide⟩,⟨1111237, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83084_1111238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83084 ⟨1111238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83084
    ⟨1111238, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1111153, by decide⟩,⟨1111191, by decide⟩,⟨1111237, by decide⟩]) unmarked_context_11_83084_1111238 node_context_11_83084_1111238
  intro a
  fin_cases a
  · exact context_12_332336_1108174
  · exact context_12_332337_1111153
  · exact context_12_332338_1111191
  · exact context_12_332339_1111237

theorem selected_cut_40776 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 332340) = some ⟨12, 1, 0, 1108174, 332340, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332340_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332340 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 332340 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 332340, 1, 65536⟩
    (by decide) selected_cut_40776

theorem selected_cut_40777 : selected 9 ⟨1111300, by decide⟩
    (prefixPartial 12 332341) = some ⟨12, 2, 0, 1111300, 332341, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_332341_1111300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332341 ⟨1111300, by decide⟩ :=
  accepted_of_selected 12 332341 ⟨1111300, by decide⟩ ⟨12, 2, 0, 1111300, 332341, 2509, 65536⟩
    (by decide) selected_cut_40777

theorem selected_cut_40778 : selected 9 ⟨1111335, by decide⟩
    (prefixPartial 12 332342) = some ⟨12, 2, 0, 1111335, 332342, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_332342_1111335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332342 ⟨1111335, by decide⟩ :=
  accepted_of_selected 12 332342 ⟨1111335, by decide⟩ ⟨12, 2, 0, 1111335, 332342, 1789, 65536⟩
    (by decide) selected_cut_40778

theorem selected_cut_40779 : selected 9 ⟨1111372, by decide⟩
    (prefixPartial 12 332343) = some ⟨12, 2, 0, 1111372, 332343, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_332343_1111372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332343 ⟨1111372, by decide⟩ :=
  accepted_of_selected 12 332343 ⟨1111372, by decide⟩ ⟨12, 2, 0, 1111372, 332343, 1853, 65536⟩
    (by decide) selected_cut_40779

theorem unmarked_context_11_83085_1111373 : frontier 10 ⟨1111373, by decide⟩
    (prefixCache 11 83085) (prefixPartial 11 83085) = false := by
  decide +kernel

theorem node_context_11_83085_1111373 : EJMOriginalGlobalDAGData.nodes 10 ⟨1111373, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1111300, by decide⟩,⟨1111335, by decide⟩,⟨1111372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83085_1111373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83085 ⟨1111373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83085
    ⟨1111373, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1111300, by decide⟩,⟨1111335, by decide⟩,⟨1111372, by decide⟩]) unmarked_context_11_83085_1111373 node_context_11_83085_1111373
  intro a
  fin_cases a
  · exact context_12_332340_1108174
  · exact context_12_332341_1111300
  · exact context_12_332342_1111335
  · exact context_12_332343_1111372

theorem selected_cut_40780 : selected 10 ⟨1111465, by decide⟩
    (prefixPartial 11 83086) = some ⟨11, 2, 0, 1111465, 83086, 3845, 262144⟩ := by
  decide +kernel

theorem context_11_83086_1111465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83086 ⟨1111465, by decide⟩ :=
  accepted_of_selected 11 83086 ⟨1111465, by decide⟩ ⟨11, 2, 0, 1111465, 83086, 3845, 262144⟩
    (by decide) selected_cut_40780

theorem selected_cut_40781 : selected 10 ⟨1111526, by decide⟩
    (prefixPartial 11 83087) = some ⟨11, 2, 0, 1111526, 83087, 3313, 262144⟩ := by
  decide +kernel

theorem context_11_83087_1111526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83087 ⟨1111526, by decide⟩ :=
  accepted_of_selected 11 83087 ⟨1111526, by decide⟩ ⟨11, 2, 0, 1111526, 83087, 3313, 262144⟩
    (by decide) selected_cut_40781

theorem unmarked_context_10_20771_1111527 : frontier 11 ⟨1111527, by decide⟩
    (prefixCache 10 20771) (prefixPartial 10 20771) = false := by
  decide +kernel

theorem node_context_10_20771_1111527 : EJMOriginalGlobalDAGData.nodes 11 ⟨1111527, by decide⟩ =
    .split (coordinate 10) (![⟨1111238, by decide⟩,⟨1111373, by decide⟩,⟨1111465, by decide⟩,⟨1111526, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20771_1111527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20771 ⟨1111527, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20771
    ⟨1111527, by decide⟩ (by decide) (![⟨1111238, by decide⟩,⟨1111373, by decide⟩,⟨1111465, by decide⟩,⟨1111526, by decide⟩]) unmarked_context_10_20771_1111527 node_context_10_20771_1111527
  intro a
  fin_cases a
  · exact context_11_83084_1111238
  · exact context_11_83085_1111373
  · exact context_11_83086_1111465
  · exact context_11_83087_1111526

theorem unmarked_context_9_5192_1111528 : frontier 12 ⟨1111528, by decide⟩
    (prefixCache 9 5192) (prefixPartial 9 5192) = false := by
  decide +kernel

theorem node_context_9_5192_1111528 : EJMOriginalGlobalDAGData.nodes 12 ⟨1111528, by decide⟩ =
    .split (coordinate 9) (![⟨1109925, by decide⟩,⟨1110483, by decide⟩,⟨1111102, by decide⟩,⟨1111527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5192_1111528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5192 ⟨1111528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5192
    ⟨1111528, by decide⟩ (by decide) (![⟨1109925, by decide⟩,⟨1110483, by decide⟩,⟨1111102, by decide⟩,⟨1111527, by decide⟩]) unmarked_context_9_5192_1111528 node_context_9_5192_1111528
  intro a
  fin_cases a
  · exact context_10_20768_1109925
  · exact context_10_20769_1110483
  · exact context_10_20770_1111102
  · exact context_10_20771_1111527

theorem selected_cut_40782 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 20772) = some ⟨10, 1, 0, 3442, 20772, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20772_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20772 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 20772 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 20772, 1, 1048576⟩
    (by decide) selected_cut_40782

theorem selected_cut_40783 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 20773) = some ⟨10, 1, 0, 893098, 20773, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20773_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20773 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 20773 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 20773, 1, 1048576⟩
    (by decide) selected_cut_40783

theorem selected_cut_40784 : selected 9 ⟨1111552, by decide⟩
    (prefixPartial 12 332384) = some ⟨12, 2, 0, 1111552, 332384, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_332384_1111552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332384 ⟨1111552, by decide⟩ :=
  accepted_of_selected 12 332384 ⟨1111552, by decide⟩ ⟨12, 2, 0, 1111552, 332384, 1421, 65536⟩
    (by decide) selected_cut_40784

theorem selected_cut_40785 : selected 9 ⟨1111581, by decide⟩
    (prefixPartial 12 332385) = some ⟨12, 2, 0, 1111581, 332385, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_332385_1111581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332385 ⟨1111581, by decide⟩ :=
  accepted_of_selected 12 332385 ⟨1111581, by decide⟩ ⟨12, 2, 0, 1111581, 332385, 1577, 65536⟩
    (by decide) selected_cut_40785

theorem selected_cut_40786 : selected 9 ⟨1111605, by decide⟩
    (prefixPartial 12 332386) = some ⟨12, 2, 0, 1111605, 332386, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_332386_1111605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332386 ⟨1111605, by decide⟩ :=
  accepted_of_selected 12 332386 ⟨1111605, by decide⟩ ⟨12, 2, 0, 1111605, 332386, 1369, 65536⟩
    (by decide) selected_cut_40786

theorem selected_cut_40787 : selected 9 ⟨1111635, by decide⟩
    (prefixPartial 12 332387) = some ⟨12, 2, 0, 1111635, 332387, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_332387_1111635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332387 ⟨1111635, by decide⟩ :=
  accepted_of_selected 12 332387 ⟨1111635, by decide⟩ ⟨12, 2, 0, 1111635, 332387, 1457, 65536⟩
    (by decide) selected_cut_40787

theorem unmarked_context_11_83096_1111636 : frontier 10 ⟨1111636, by decide⟩
    (prefixCache 11 83096) (prefixPartial 11 83096) = false := by
  decide +kernel

theorem node_context_11_83096_1111636 : EJMOriginalGlobalDAGData.nodes 10 ⟨1111636, by decide⟩ =
    .split (coordinate 11) (![⟨1111552, by decide⟩,⟨1111581, by decide⟩,⟨1111605, by decide⟩,⟨1111635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83096_1111636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83096 ⟨1111636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83096
    ⟨1111636, by decide⟩ (by decide) (![⟨1111552, by decide⟩,⟨1111581, by decide⟩,⟨1111605, by decide⟩,⟨1111635, by decide⟩]) unmarked_context_11_83096_1111636 node_context_11_83096_1111636
  intro a
  fin_cases a
  · exact context_12_332384_1111552
  · exact context_12_332385_1111581
  · exact context_12_332386_1111605
  · exact context_12_332387_1111635

theorem selected_cut_40788 : selected 10 ⟨1111703, by decide⟩
    (prefixPartial 11 83097) = some ⟨11, 2, 0, 1111703, 83097, 3865, 262144⟩ := by
  decide +kernel

theorem context_11_83097_1111703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83097 ⟨1111703, by decide⟩ :=
  accepted_of_selected 11 83097 ⟨1111703, by decide⟩ ⟨11, 2, 0, 1111703, 83097, 3865, 262144⟩
    (by decide) selected_cut_40788

theorem selected_cut_40789 : selected 9 ⟨1111732, by decide⟩
    (prefixPartial 12 332392) = some ⟨12, 2, 0, 1111732, 332392, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_332392_1111732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332392 ⟨1111732, by decide⟩ :=
  accepted_of_selected 12 332392 ⟨1111732, by decide⟩ ⟨12, 2, 0, 1111732, 332392, 1353, 65536⟩
    (by decide) selected_cut_40789

theorem selected_cut_40790 : selected 9 ⟨1111775, by decide⟩
    (prefixPartial 12 332393) = some ⟨12, 2, 0, 1111775, 332393, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_332393_1111775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332393 ⟨1111775, by decide⟩ :=
  accepted_of_selected 12 332393 ⟨1111775, by decide⟩ ⟨12, 2, 0, 1111775, 332393, 1405, 65536⟩
    (by decide) selected_cut_40790

theorem selected_cut_40791 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 332394) = some ⟨12, 1, 0, 474208, 332394, 1, 65536⟩ := by
  decide +kernel

theorem context_12_332394_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332394 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 332394 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 332394, 1, 65536⟩
    (by decide) selected_cut_40791

theorem selected_cut_40792 : selected 9 ⟨1111817, by decide⟩
    (prefixPartial 12 332395) = some ⟨12, 2, 0, 1111817, 332395, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_332395_1111817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332395 ⟨1111817, by decide⟩ :=
  accepted_of_selected 12 332395 ⟨1111817, by decide⟩ ⟨12, 2, 0, 1111817, 332395, 1453, 65536⟩
    (by decide) selected_cut_40792

theorem unmarked_context_11_83098_1111818 : frontier 10 ⟨1111818, by decide⟩
    (prefixCache 11 83098) (prefixPartial 11 83098) = false := by
  decide +kernel

theorem node_context_11_83098_1111818 : EJMOriginalGlobalDAGData.nodes 10 ⟨1111818, by decide⟩ =
    .split (coordinate 11) (![⟨1111732, by decide⟩,⟨1111775, by decide⟩,⟨474208, by decide⟩,⟨1111817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83098_1111818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83098 ⟨1111818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83098
    ⟨1111818, by decide⟩ (by decide) (![⟨1111732, by decide⟩,⟨1111775, by decide⟩,⟨474208, by decide⟩,⟨1111817, by decide⟩]) unmarked_context_11_83098_1111818 node_context_11_83098_1111818
  intro a
  fin_cases a
  · exact context_12_332392_1111732
  · exact context_12_332393_1111775
  · exact context_12_332394_474208
  · exact context_12_332395_1111817

theorem selected_cut_40793 : selected 9 ⟨1111850, by decide⟩
    (prefixPartial 12 332396) = some ⟨12, 2, 0, 1111850, 332396, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_332396_1111850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332396 ⟨1111850, by decide⟩ :=
  accepted_of_selected 12 332396 ⟨1111850, by decide⟩ ⟨12, 2, 0, 1111850, 332396, 1301, 65536⟩
    (by decide) selected_cut_40793

theorem selected_cut_40794 : selected 9 ⟨1111882, by decide⟩
    (prefixPartial 12 332397) = some ⟨12, 2, 0, 1111882, 332397, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_332397_1111882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332397 ⟨1111882, by decide⟩ :=
  accepted_of_selected 12 332397 ⟨1111882, by decide⟩ ⟨12, 2, 0, 1111882, 332397, 1305, 65536⟩
    (by decide) selected_cut_40794

theorem selected_cut_40795 : selected 9 ⟨1111909, by decide⟩
    (prefixPartial 12 332398) = some ⟨12, 2, 0, 1111909, 332398, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_332398_1111909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332398 ⟨1111909, by decide⟩ :=
  accepted_of_selected 12 332398 ⟨1111909, by decide⟩ ⟨12, 2, 0, 1111909, 332398, 1209, 65536⟩
    (by decide) selected_cut_40795

theorem selected_cut_40796 : selected 9 ⟨1111923, by decide⟩
    (prefixPartial 12 332399) = some ⟨12, 2, 0, 1111923, 332399, 1061, 65536⟩ := by
  decide +kernel

theorem context_12_332399_1111923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 332399 ⟨1111923, by decide⟩ :=
  accepted_of_selected 12 332399 ⟨1111923, by decide⟩ ⟨12, 2, 0, 1111923, 332399, 1061, 65536⟩
    (by decide) selected_cut_40796

theorem unmarked_context_11_83099_1111924 : frontier 10 ⟨1111924, by decide⟩
    (prefixCache 11 83099) (prefixPartial 11 83099) = false := by
  decide +kernel

theorem node_context_11_83099_1111924 : EJMOriginalGlobalDAGData.nodes 10 ⟨1111924, by decide⟩ =
    .split (coordinate 11) (![⟨1111850, by decide⟩,⟨1111882, by decide⟩,⟨1111909, by decide⟩,⟨1111923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83099_1111924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83099 ⟨1111924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83099
    ⟨1111924, by decide⟩ (by decide) (![⟨1111850, by decide⟩,⟨1111882, by decide⟩,⟨1111909, by decide⟩,⟨1111923, by decide⟩]) unmarked_context_11_83099_1111924 node_context_11_83099_1111924
  intro a
  fin_cases a
  · exact context_12_332396_1111850
  · exact context_12_332397_1111882
  · exact context_12_332398_1111909
  · exact context_12_332399_1111923

theorem unmarked_context_10_20774_1111925 : frontier 11 ⟨1111925, by decide⟩
    (prefixCache 10 20774) (prefixPartial 10 20774) = false := by
  decide +kernel

theorem node_context_10_20774_1111925 : EJMOriginalGlobalDAGData.nodes 11 ⟨1111925, by decide⟩ =
    .split (coordinate 10) (![⟨1111636, by decide⟩,⟨1111703, by decide⟩,⟨1111818, by decide⟩,⟨1111924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20774_1111925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20774 ⟨1111925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20774
    ⟨1111925, by decide⟩ (by decide) (![⟨1111636, by decide⟩,⟨1111703, by decide⟩,⟨1111818, by decide⟩,⟨1111924, by decide⟩]) unmarked_context_10_20774_1111925 node_context_10_20774_1111925
  intro a
  fin_cases a
  · exact context_11_83096_1111636
  · exact context_11_83097_1111703
  · exact context_11_83098_1111818
  · exact context_11_83099_1111924

theorem selected_cut_40797 : selected 10 ⟨1111988, by decide⟩
    (prefixPartial 11 83100) = some ⟨11, 2, 0, 1111988, 83100, 3465, 262144⟩ := by
  decide +kernel

theorem context_11_83100_1111988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83100 ⟨1111988, by decide⟩ :=
  accepted_of_selected 11 83100 ⟨1111988, by decide⟩ ⟨11, 2, 0, 1111988, 83100, 3465, 262144⟩
    (by decide) selected_cut_40797

theorem selected_cut_40798 : selected 10 ⟨1112035, by decide⟩
    (prefixPartial 11 83101) = some ⟨11, 2, 0, 1112035, 83101, 2385, 262144⟩ := by
  decide +kernel

theorem context_11_83101_1112035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83101 ⟨1112035, by decide⟩ :=
  accepted_of_selected 11 83101 ⟨1112035, by decide⟩ ⟨11, 2, 0, 1112035, 83101, 2385, 262144⟩
    (by decide) selected_cut_40798

theorem selected_cut_40799 : selected 10 ⟨1112094, by decide⟩
    (prefixPartial 11 83102) = some ⟨11, 2, 0, 1112094, 83102, 2281, 262144⟩ := by
  decide +kernel

theorem context_11_83102_1112094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83102 ⟨1112094, by decide⟩ :=
  accepted_of_selected 11 83102 ⟨1112094, by decide⟩ ⟨11, 2, 0, 1112094, 83102, 2281, 262144⟩
    (by decide) selected_cut_40799

theorem selected_cut_40800 : selected 10 ⟨1112145, by decide⟩
    (prefixPartial 11 83103) = some ⟨11, 2, 0, 1112145, 83103, 2069, 262144⟩ := by
  decide +kernel

theorem context_11_83103_1112145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83103 ⟨1112145, by decide⟩ :=
  accepted_of_selected 11 83103 ⟨1112145, by decide⟩ ⟨11, 2, 0, 1112145, 83103, 2069, 262144⟩
    (by decide) selected_cut_40800

theorem unmarked_context_10_20775_1112146 : frontier 11 ⟨1112146, by decide⟩
    (prefixCache 10 20775) (prefixPartial 10 20775) = false := by
  decide +kernel

theorem node_context_10_20775_1112146 : EJMOriginalGlobalDAGData.nodes 11 ⟨1112146, by decide⟩ =
    .split (coordinate 10) (![⟨1111988, by decide⟩,⟨1112035, by decide⟩,⟨1112094, by decide⟩,⟨1112145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20775_1112146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20775 ⟨1112146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20775
    ⟨1112146, by decide⟩ (by decide) (![⟨1111988, by decide⟩,⟨1112035, by decide⟩,⟨1112094, by decide⟩,⟨1112145, by decide⟩]) unmarked_context_10_20775_1112146 node_context_10_20775_1112146
  intro a
  fin_cases a
  · exact context_11_83100_1111988
  · exact context_11_83101_1112035
  · exact context_11_83102_1112094
  · exact context_11_83103_1112145

theorem unmarked_context_9_5193_1112147 : frontier 12 ⟨1112147, by decide⟩
    (prefixCache 9 5193) (prefixPartial 9 5193) = false := by
  decide +kernel

theorem node_context_9_5193_1112147 : EJMOriginalGlobalDAGData.nodes 12 ⟨1112147, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1111925, by decide⟩,⟨1112146, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5193_1112147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5193 ⟨1112147, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5193
    ⟨1112147, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1111925, by decide⟩,⟨1112146, by decide⟩]) unmarked_context_9_5193_1112147 node_context_9_5193_1112147
  intro a
  fin_cases a
  · exact context_10_20772_3442
  · exact context_10_20773_893098
  · exact context_10_20774_1111925
  · exact context_10_20775_1112146

theorem selected_cut_40801 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 20776) = some ⟨10, 1, 0, 3442, 20776, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20776_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20776 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 20776 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 20776, 1, 1048576⟩
    (by decide) selected_cut_40801

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
