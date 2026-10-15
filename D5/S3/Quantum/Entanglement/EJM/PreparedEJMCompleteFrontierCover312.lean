/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover311
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_29956 : selected 8 ⟨756643, by decide⟩
    (prefixPartial 13 375883) = some ⟨13, 2, 0, 756643, 375883, 697, 16384⟩ := by
  decide +kernel

theorem context_13_375883_756643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375883 ⟨756643, by decide⟩ :=
  accepted_of_selected 13 375883 ⟨756643, by decide⟩ ⟨13, 2, 0, 756643, 375883, 697, 16384⟩
    (by decide) selected_cut_29956

theorem unmarked_context_12_93970_756644 : frontier 9 ⟨756644, by decide⟩
    (prefixCache 12 93970) (prefixPartial 12 93970) = false := by
  decide +kernel

theorem node_context_12_93970_756644 : EJMOriginalGlobalDAGData.nodes 9 ⟨756644, by decide⟩ =
    .split (coordinate 12) (![⟨756568, by decide⟩,⟨756603, by decide⟩,⟨756635, by decide⟩,⟨756643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93970_756644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93970 ⟨756644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93970
    ⟨756644, by decide⟩ (by decide) (![⟨756568, by decide⟩,⟨756603, by decide⟩,⟨756635, by decide⟩,⟨756643, by decide⟩]) unmarked_context_12_93970_756644 node_context_12_93970_756644
  intro a
  fin_cases a
  · exact context_13_375880_756568
  · exact context_13_375881_756603
  · exact context_13_375882_756635
  · exact context_13_375883_756643

theorem selected_cut_29957 : selected 8 ⟨756678, by decide⟩
    (prefixPartial 13 375884) = some ⟨13, 2, 0, 756678, 375884, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_375884_756678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375884 ⟨756678, by decide⟩ :=
  accepted_of_selected 13 375884 ⟨756678, by decide⟩ ⟨13, 2, 0, 756678, 375884, 2561, 16384⟩
    (by decide) selected_cut_29957

theorem selected_cut_29958 : selected 8 ⟨756705, by decide⟩
    (prefixPartial 13 375885) = some ⟨13, 2, 0, 756705, 375885, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_375885_756705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375885 ⟨756705, by decide⟩ :=
  accepted_of_selected 13 375885 ⟨756705, by decide⟩ ⟨13, 2, 0, 756705, 375885, 1809, 16384⟩
    (by decide) selected_cut_29958

theorem selected_cut_29959 : selected 8 ⟨756733, by decide⟩
    (prefixPartial 13 375886) = some ⟨13, 2, 0, 756733, 375886, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_375886_756733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375886 ⟨756733, by decide⟩ :=
  accepted_of_selected 13 375886 ⟨756733, by decide⟩ ⟨13, 2, 0, 756733, 375886, 1837, 16384⟩
    (by decide) selected_cut_29959

theorem selected_cut_29960 : selected 8 ⟨756738, by decide⟩
    (prefixPartial 13 375887) = some ⟨13, 2, 0, 756738, 375887, 677, 16384⟩ := by
  decide +kernel

theorem context_13_375887_756738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375887 ⟨756738, by decide⟩ :=
  accepted_of_selected 13 375887 ⟨756738, by decide⟩ ⟨13, 2, 0, 756738, 375887, 677, 16384⟩
    (by decide) selected_cut_29960

theorem unmarked_context_12_93971_756739 : frontier 9 ⟨756739, by decide⟩
    (prefixCache 12 93971) (prefixPartial 12 93971) = false := by
  decide +kernel

theorem node_context_12_93971_756739 : EJMOriginalGlobalDAGData.nodes 9 ⟨756739, by decide⟩ =
    .split (coordinate 12) (![⟨756678, by decide⟩,⟨756705, by decide⟩,⟨756733, by decide⟩,⟨756738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93971_756739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93971 ⟨756739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93971
    ⟨756739, by decide⟩ (by decide) (![⟨756678, by decide⟩,⟨756705, by decide⟩,⟨756733, by decide⟩,⟨756738, by decide⟩]) unmarked_context_12_93971_756739 node_context_12_93971_756739
  intro a
  fin_cases a
  · exact context_13_375884_756678
  · exact context_13_375885_756705
  · exact context_13_375886_756733
  · exact context_13_375887_756738

theorem unmarked_context_11_23492_756740 : frontier 10 ⟨756740, by decide⟩
    (prefixCache 11 23492) (prefixPartial 11 23492) = false := by
  decide +kernel

theorem node_context_11_23492_756740 : EJMOriginalGlobalDAGData.nodes 10 ⟨756740, by decide⟩ =
    .split (coordinate 11) (![⟨756407, by decide⟩,⟨756522, by decide⟩,⟨756644, by decide⟩,⟨756739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23492_756740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23492 ⟨756740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23492
    ⟨756740, by decide⟩ (by decide) (![⟨756407, by decide⟩,⟨756522, by decide⟩,⟨756644, by decide⟩,⟨756739, by decide⟩]) unmarked_context_11_23492_756740 node_context_11_23492_756740
  intro a
  fin_cases a
  · exact context_12_93968_756407
  · exact context_12_93969_756522
  · exact context_12_93970_756644
  · exact context_12_93971_756739

theorem selected_cut_29961 : selected 8 ⟨756774, by decide⟩
    (prefixPartial 13 375888) = some ⟨13, 2, 0, 756774, 375888, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_375888_756774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375888 ⟨756774, by decide⟩ :=
  accepted_of_selected 13 375888 ⟨756774, by decide⟩ ⟨13, 2, 0, 756774, 375888, 2069, 16384⟩
    (by decide) selected_cut_29961

theorem selected_cut_29962 : selected 8 ⟨756813, by decide⟩
    (prefixPartial 13 375889) = some ⟨13, 2, 0, 756813, 375889, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_375889_756813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375889 ⟨756813, by decide⟩ :=
  accepted_of_selected 13 375889 ⟨756813, by decide⟩ ⟨13, 2, 0, 756813, 375889, 2105, 16384⟩
    (by decide) selected_cut_29962

theorem selected_cut_29963 : selected 8 ⟨756844, by decide⟩
    (prefixPartial 13 375890) = some ⟨13, 2, 0, 756844, 375890, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_375890_756844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375890 ⟨756844, by decide⟩ :=
  accepted_of_selected 13 375890 ⟨756844, by decide⟩ ⟨13, 2, 0, 756844, 375890, 1709, 16384⟩
    (by decide) selected_cut_29963

theorem selected_cut_29964 : selected 8 ⟨756849, by decide⟩
    (prefixPartial 13 375891) = some ⟨13, 2, 0, 756849, 375891, 765, 16384⟩ := by
  decide +kernel

theorem context_13_375891_756849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375891 ⟨756849, by decide⟩ :=
  accepted_of_selected 13 375891 ⟨756849, by decide⟩ ⟨13, 2, 0, 756849, 375891, 765, 16384⟩
    (by decide) selected_cut_29964

theorem unmarked_context_12_93972_756850 : frontier 9 ⟨756850, by decide⟩
    (prefixCache 12 93972) (prefixPartial 12 93972) = false := by
  decide +kernel

theorem node_context_12_93972_756850 : EJMOriginalGlobalDAGData.nodes 9 ⟨756850, by decide⟩ =
    .split (coordinate 12) (![⟨756774, by decide⟩,⟨756813, by decide⟩,⟨756844, by decide⟩,⟨756849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93972_756850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93972 ⟨756850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93972
    ⟨756850, by decide⟩ (by decide) (![⟨756774, by decide⟩,⟨756813, by decide⟩,⟨756844, by decide⟩,⟨756849, by decide⟩]) unmarked_context_12_93972_756850 node_context_12_93972_756850
  intro a
  fin_cases a
  · exact context_13_375888_756774
  · exact context_13_375889_756813
  · exact context_13_375890_756844
  · exact context_13_375891_756849

theorem selected_cut_29965 : selected 8 ⟨756882, by decide⟩
    (prefixPartial 13 375892) = some ⟨13, 2, 0, 756882, 375892, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_375892_756882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375892 ⟨756882, by decide⟩ :=
  accepted_of_selected 13 375892 ⟨756882, by decide⟩ ⟨13, 2, 0, 756882, 375892, 2397, 16384⟩
    (by decide) selected_cut_29965

theorem selected_cut_29966 : selected 8 ⟨756915, by decide⟩
    (prefixPartial 13 375893) = some ⟨13, 2, 0, 756915, 375893, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_375893_756915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375893 ⟨756915, by decide⟩ :=
  accepted_of_selected 13 375893 ⟨756915, by decide⟩ ⟨13, 2, 0, 756915, 375893, 1821, 16384⟩
    (by decide) selected_cut_29966

theorem selected_cut_29967 : selected 8 ⟨756946, by decide⟩
    (prefixPartial 13 375894) = some ⟨13, 2, 0, 756946, 375894, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_375894_756946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375894 ⟨756946, by decide⟩ :=
  accepted_of_selected 13 375894 ⟨756946, by decide⟩ ⟨13, 2, 0, 756946, 375894, 1829, 16384⟩
    (by decide) selected_cut_29967

theorem selected_cut_29968 : selected 8 ⟨756953, by decide⟩
    (prefixPartial 13 375895) = some ⟨13, 2, 0, 756953, 375895, 657, 16384⟩ := by
  decide +kernel

theorem context_13_375895_756953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375895 ⟨756953, by decide⟩ :=
  accepted_of_selected 13 375895 ⟨756953, by decide⟩ ⟨13, 2, 0, 756953, 375895, 657, 16384⟩
    (by decide) selected_cut_29968

theorem unmarked_context_12_93973_756954 : frontier 9 ⟨756954, by decide⟩
    (prefixCache 12 93973) (prefixPartial 12 93973) = false := by
  decide +kernel

theorem node_context_12_93973_756954 : EJMOriginalGlobalDAGData.nodes 9 ⟨756954, by decide⟩ =
    .split (coordinate 12) (![⟨756882, by decide⟩,⟨756915, by decide⟩,⟨756946, by decide⟩,⟨756953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93973_756954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93973 ⟨756954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93973
    ⟨756954, by decide⟩ (by decide) (![⟨756882, by decide⟩,⟨756915, by decide⟩,⟨756946, by decide⟩,⟨756953, by decide⟩]) unmarked_context_12_93973_756954 node_context_12_93973_756954
  intro a
  fin_cases a
  · exact context_13_375892_756882
  · exact context_13_375893_756915
  · exact context_13_375894_756946
  · exact context_13_375895_756953

theorem selected_cut_29969 : selected 8 ⟨756996, by decide⟩
    (prefixPartial 13 375896) = some ⟨13, 2, 0, 756996, 375896, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_375896_756996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375896 ⟨756996, by decide⟩ :=
  accepted_of_selected 13 375896 ⟨756996, by decide⟩ ⟨13, 2, 0, 756996, 375896, 2469, 16384⟩
    (by decide) selected_cut_29969

theorem selected_cut_29970 : selected 8 ⟨757037, by decide⟩
    (prefixPartial 13 375897) = some ⟨13, 2, 0, 757037, 375897, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_375897_757037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375897 ⟨757037, by decide⟩ :=
  accepted_of_selected 13 375897 ⟨757037, by decide⟩ ⟨13, 2, 0, 757037, 375897, 2025, 16384⟩
    (by decide) selected_cut_29970

theorem selected_cut_29971 : selected 8 ⟨757066, by decide⟩
    (prefixPartial 13 375898) = some ⟨13, 2, 0, 757066, 375898, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_375898_757066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375898 ⟨757066, by decide⟩ :=
  accepted_of_selected 13 375898 ⟨757066, by decide⟩ ⟨13, 2, 0, 757066, 375898, 1737, 16384⟩
    (by decide) selected_cut_29971

theorem selected_cut_29972 : selected 8 ⟨757071, by decide⟩
    (prefixPartial 13 375899) = some ⟨13, 2, 0, 757071, 375899, 765, 16384⟩ := by
  decide +kernel

theorem context_13_375899_757071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375899 ⟨757071, by decide⟩ :=
  accepted_of_selected 13 375899 ⟨757071, by decide⟩ ⟨13, 2, 0, 757071, 375899, 765, 16384⟩
    (by decide) selected_cut_29972

theorem unmarked_context_12_93974_757072 : frontier 9 ⟨757072, by decide⟩
    (prefixCache 12 93974) (prefixPartial 12 93974) = false := by
  decide +kernel

theorem node_context_12_93974_757072 : EJMOriginalGlobalDAGData.nodes 9 ⟨757072, by decide⟩ =
    .split (coordinate 12) (![⟨756996, by decide⟩,⟨757037, by decide⟩,⟨757066, by decide⟩,⟨757071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93974_757072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93974 ⟨757072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93974
    ⟨757072, by decide⟩ (by decide) (![⟨756996, by decide⟩,⟨757037, by decide⟩,⟨757066, by decide⟩,⟨757071, by decide⟩]) unmarked_context_12_93974_757072 node_context_12_93974_757072
  intro a
  fin_cases a
  · exact context_13_375896_756996
  · exact context_13_375897_757037
  · exact context_13_375898_757066
  · exact context_13_375899_757071

theorem selected_cut_29973 : selected 8 ⟨757106, by decide⟩
    (prefixPartial 13 375900) = some ⟨13, 2, 0, 757106, 375900, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_375900_757106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375900 ⟨757106, by decide⟩ :=
  accepted_of_selected 13 375900 ⟨757106, by decide⟩ ⟨13, 2, 0, 757106, 375900, 2317, 16384⟩
    (by decide) selected_cut_29973

theorem selected_cut_29974 : selected 8 ⟨757142, by decide⟩
    (prefixPartial 13 375901) = some ⟨13, 2, 0, 757142, 375901, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_375901_757142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375901 ⟨757142, by decide⟩ :=
  accepted_of_selected 13 375901 ⟨757142, by decide⟩ ⟨13, 2, 0, 757142, 375901, 2093, 16384⟩
    (by decide) selected_cut_29974

theorem selected_cut_29975 : selected 8 ⟨757166, by decide⟩
    (prefixPartial 13 375902) = some ⟨13, 2, 0, 757166, 375902, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_375902_757166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375902 ⟨757166, by decide⟩ :=
  accepted_of_selected 13 375902 ⟨757166, by decide⟩ ⟨13, 2, 0, 757166, 375902, 1925, 16384⟩
    (by decide) selected_cut_29975

theorem selected_cut_29976 : selected 8 ⟨757174, by decide⟩
    (prefixPartial 13 375903) = some ⟨13, 2, 0, 757174, 375903, 685, 16384⟩ := by
  decide +kernel

theorem context_13_375903_757174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375903 ⟨757174, by decide⟩ :=
  accepted_of_selected 13 375903 ⟨757174, by decide⟩ ⟨13, 2, 0, 757174, 375903, 685, 16384⟩
    (by decide) selected_cut_29976

theorem unmarked_context_12_93975_757175 : frontier 9 ⟨757175, by decide⟩
    (prefixCache 12 93975) (prefixPartial 12 93975) = false := by
  decide +kernel

theorem node_context_12_93975_757175 : EJMOriginalGlobalDAGData.nodes 9 ⟨757175, by decide⟩ =
    .split (coordinate 12) (![⟨757106, by decide⟩,⟨757142, by decide⟩,⟨757166, by decide⟩,⟨757174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93975_757175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93975 ⟨757175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93975
    ⟨757175, by decide⟩ (by decide) (![⟨757106, by decide⟩,⟨757142, by decide⟩,⟨757166, by decide⟩,⟨757174, by decide⟩]) unmarked_context_12_93975_757175 node_context_12_93975_757175
  intro a
  fin_cases a
  · exact context_13_375900_757106
  · exact context_13_375901_757142
  · exact context_13_375902_757166
  · exact context_13_375903_757174

theorem unmarked_context_11_23493_757176 : frontier 10 ⟨757176, by decide⟩
    (prefixCache 11 23493) (prefixPartial 11 23493) = false := by
  decide +kernel

theorem node_context_11_23493_757176 : EJMOriginalGlobalDAGData.nodes 10 ⟨757176, by decide⟩ =
    .split (coordinate 11) (![⟨756850, by decide⟩,⟨756954, by decide⟩,⟨757072, by decide⟩,⟨757175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23493_757176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23493 ⟨757176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23493
    ⟨757176, by decide⟩ (by decide) (![⟨756850, by decide⟩,⟨756954, by decide⟩,⟨757072, by decide⟩,⟨757175, by decide⟩]) unmarked_context_11_23493_757176 node_context_11_23493_757176
  intro a
  fin_cases a
  · exact context_12_93972_756850
  · exact context_12_93973_756954
  · exact context_12_93974_757072
  · exact context_12_93975_757175

theorem selected_cut_29977 : selected 8 ⟨757203, by decide⟩
    (prefixPartial 13 375904) = some ⟨13, 2, 0, 757203, 375904, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_375904_757203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375904 ⟨757203, by decide⟩ :=
  accepted_of_selected 13 375904 ⟨757203, by decide⟩ ⟨13, 2, 0, 757203, 375904, 1633, 16384⟩
    (by decide) selected_cut_29977

theorem selected_cut_29978 : selected 8 ⟨757237, by decide⟩
    (prefixPartial 13 375905) = some ⟨13, 2, 0, 757237, 375905, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_375905_757237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375905 ⟨757237, by decide⟩ :=
  accepted_of_selected 13 375905 ⟨757237, by decide⟩ ⟨13, 2, 0, 757237, 375905, 1841, 16384⟩
    (by decide) selected_cut_29978

theorem selected_cut_29979 : selected 8 ⟨757257, by decide⟩
    (prefixPartial 13 375906) = some ⟨13, 2, 0, 757257, 375906, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_375906_757257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375906 ⟨757257, by decide⟩ :=
  accepted_of_selected 13 375906 ⟨757257, by decide⟩ ⟨13, 2, 0, 757257, 375906, 1761, 16384⟩
    (by decide) selected_cut_29979

theorem selected_cut_29980 : selected 8 ⟨757266, by decide⟩
    (prefixPartial 13 375907) = some ⟨13, 2, 0, 757266, 375907, 749, 16384⟩ := by
  decide +kernel

theorem context_13_375907_757266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375907 ⟨757266, by decide⟩ :=
  accepted_of_selected 13 375907 ⟨757266, by decide⟩ ⟨13, 2, 0, 757266, 375907, 749, 16384⟩
    (by decide) selected_cut_29980

theorem unmarked_context_12_93976_757267 : frontier 9 ⟨757267, by decide⟩
    (prefixCache 12 93976) (prefixPartial 12 93976) = false := by
  decide +kernel

theorem node_context_12_93976_757267 : EJMOriginalGlobalDAGData.nodes 9 ⟨757267, by decide⟩ =
    .split (coordinate 12) (![⟨757203, by decide⟩,⟨757237, by decide⟩,⟨757257, by decide⟩,⟨757266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93976_757267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93976 ⟨757267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93976
    ⟨757267, by decide⟩ (by decide) (![⟨757203, by decide⟩,⟨757237, by decide⟩,⟨757257, by decide⟩,⟨757266, by decide⟩]) unmarked_context_12_93976_757267 node_context_12_93976_757267
  intro a
  fin_cases a
  · exact context_13_375904_757203
  · exact context_13_375905_757237
  · exact context_13_375906_757257
  · exact context_13_375907_757266

theorem selected_cut_29981 : selected 8 ⟨757298, by decide⟩
    (prefixPartial 13 375908) = some ⟨13, 2, 0, 757298, 375908, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_375908_757298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375908 ⟨757298, by decide⟩ :=
  accepted_of_selected 13 375908 ⟨757298, by decide⟩ ⟨13, 2, 0, 757298, 375908, 1937, 16384⟩
    (by decide) selected_cut_29981

theorem selected_cut_29982 : selected 8 ⟨757339, by decide⟩
    (prefixPartial 13 375909) = some ⟨13, 2, 0, 757339, 375909, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_375909_757339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375909 ⟨757339, by decide⟩ :=
  accepted_of_selected 13 375909 ⟨757339, by decide⟩ ⟨13, 2, 0, 757339, 375909, 1721, 16384⟩
    (by decide) selected_cut_29982

theorem selected_cut_29983 : selected 8 ⟨757363, by decide⟩
    (prefixPartial 13 375910) = some ⟨13, 2, 0, 757363, 375910, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_375910_757363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375910 ⟨757363, by decide⟩ :=
  accepted_of_selected 13 375910 ⟨757363, by decide⟩ ⟨13, 2, 0, 757363, 375910, 1993, 16384⟩
    (by decide) selected_cut_29983

theorem selected_cut_29984 : selected 8 ⟨757373, by decide⟩
    (prefixPartial 13 375911) = some ⟨13, 2, 0, 757373, 375911, 725, 16384⟩ := by
  decide +kernel

theorem context_13_375911_757373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375911 ⟨757373, by decide⟩ :=
  accepted_of_selected 13 375911 ⟨757373, by decide⟩ ⟨13, 2, 0, 757373, 375911, 725, 16384⟩
    (by decide) selected_cut_29984

theorem unmarked_context_12_93977_757374 : frontier 9 ⟨757374, by decide⟩
    (prefixCache 12 93977) (prefixPartial 12 93977) = false := by
  decide +kernel

theorem node_context_12_93977_757374 : EJMOriginalGlobalDAGData.nodes 9 ⟨757374, by decide⟩ =
    .split (coordinate 12) (![⟨757298, by decide⟩,⟨757339, by decide⟩,⟨757363, by decide⟩,⟨757373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93977_757374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93977 ⟨757374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93977
    ⟨757374, by decide⟩ (by decide) (![⟨757298, by decide⟩,⟨757339, by decide⟩,⟨757363, by decide⟩,⟨757373, by decide⟩]) unmarked_context_12_93977_757374 node_context_12_93977_757374
  intro a
  fin_cases a
  · exact context_13_375908_757298
  · exact context_13_375909_757339
  · exact context_13_375910_757363
  · exact context_13_375911_757373

theorem selected_cut_29985 : selected 8 ⟨757405, by decide⟩
    (prefixPartial 13 375912) = some ⟨13, 2, 0, 757405, 375912, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_375912_757405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375912 ⟨757405, by decide⟩ :=
  accepted_of_selected 13 375912 ⟨757405, by decide⟩ ⟨13, 2, 0, 757405, 375912, 1777, 16384⟩
    (by decide) selected_cut_29985

theorem selected_cut_29986 : selected 8 ⟨757448, by decide⟩
    (prefixPartial 13 375913) = some ⟨13, 2, 0, 757448, 375913, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_375913_757448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375913 ⟨757448, by decide⟩ :=
  accepted_of_selected 13 375913 ⟨757448, by decide⟩ ⟨13, 2, 0, 757448, 375913, 1913, 16384⟩
    (by decide) selected_cut_29986

theorem selected_cut_29987 : selected 8 ⟨757469, by decide⟩
    (prefixPartial 13 375914) = some ⟨13, 2, 0, 757469, 375914, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_375914_757469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375914 ⟨757469, by decide⟩ :=
  accepted_of_selected 13 375914 ⟨757469, by decide⟩ ⟨13, 2, 0, 757469, 375914, 1777, 16384⟩
    (by decide) selected_cut_29987

theorem selected_cut_29988 : selected 8 ⟨757474, by decide⟩
    (prefixPartial 13 375915) = some ⟨13, 2, 0, 757474, 375915, 737, 16384⟩ := by
  decide +kernel

theorem context_13_375915_757474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375915 ⟨757474, by decide⟩ :=
  accepted_of_selected 13 375915 ⟨757474, by decide⟩ ⟨13, 2, 0, 757474, 375915, 737, 16384⟩
    (by decide) selected_cut_29988

theorem unmarked_context_12_93978_757475 : frontier 9 ⟨757475, by decide⟩
    (prefixCache 12 93978) (prefixPartial 12 93978) = false := by
  decide +kernel

theorem node_context_12_93978_757475 : EJMOriginalGlobalDAGData.nodes 9 ⟨757475, by decide⟩ =
    .split (coordinate 12) (![⟨757405, by decide⟩,⟨757448, by decide⟩,⟨757469, by decide⟩,⟨757474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93978_757475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93978 ⟨757475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93978
    ⟨757475, by decide⟩ (by decide) (![⟨757405, by decide⟩,⟨757448, by decide⟩,⟨757469, by decide⟩,⟨757474, by decide⟩]) unmarked_context_12_93978_757475 node_context_12_93978_757475
  intro a
  fin_cases a
  · exact context_13_375912_757405
  · exact context_13_375913_757448
  · exact context_13_375914_757469
  · exact context_13_375915_757474

theorem selected_cut_29989 : selected 8 ⟨757506, by decide⟩
    (prefixPartial 13 375916) = some ⟨13, 2, 0, 757506, 375916, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_375916_757506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375916 ⟨757506, by decide⟩ :=
  accepted_of_selected 13 375916 ⟨757506, by decide⟩ ⟨13, 2, 0, 757506, 375916, 1725, 16384⟩
    (by decide) selected_cut_29989

theorem selected_cut_29990 : selected 8 ⟨757544, by decide⟩
    (prefixPartial 13 375917) = some ⟨13, 2, 0, 757544, 375917, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_375917_757544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375917 ⟨757544, by decide⟩ :=
  accepted_of_selected 13 375917 ⟨757544, by decide⟩ ⟨13, 2, 0, 757544, 375917, 1981, 16384⟩
    (by decide) selected_cut_29990

theorem selected_cut_29991 : selected 8 ⟨757574, by decide⟩
    (prefixPartial 13 375918) = some ⟨13, 2, 0, 757574, 375918, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_375918_757574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375918 ⟨757574, by decide⟩ :=
  accepted_of_selected 13 375918 ⟨757574, by decide⟩ ⟨13, 2, 0, 757574, 375918, 1913, 16384⟩
    (by decide) selected_cut_29991

theorem selected_cut_29992 : selected 8 ⟨757582, by decide⟩
    (prefixPartial 13 375919) = some ⟨13, 2, 0, 757582, 375919, 697, 16384⟩ := by
  decide +kernel

theorem context_13_375919_757582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375919 ⟨757582, by decide⟩ :=
  accepted_of_selected 13 375919 ⟨757582, by decide⟩ ⟨13, 2, 0, 757582, 375919, 697, 16384⟩
    (by decide) selected_cut_29992

theorem unmarked_context_12_93979_757583 : frontier 9 ⟨757583, by decide⟩
    (prefixCache 12 93979) (prefixPartial 12 93979) = false := by
  decide +kernel

theorem node_context_12_93979_757583 : EJMOriginalGlobalDAGData.nodes 9 ⟨757583, by decide⟩ =
    .split (coordinate 12) (![⟨757506, by decide⟩,⟨757544, by decide⟩,⟨757574, by decide⟩,⟨757582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93979_757583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93979 ⟨757583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93979
    ⟨757583, by decide⟩ (by decide) (![⟨757506, by decide⟩,⟨757544, by decide⟩,⟨757574, by decide⟩,⟨757582, by decide⟩]) unmarked_context_12_93979_757583 node_context_12_93979_757583
  intro a
  fin_cases a
  · exact context_13_375916_757506
  · exact context_13_375917_757544
  · exact context_13_375918_757574
  · exact context_13_375919_757582

theorem unmarked_context_11_23494_757584 : frontier 10 ⟨757584, by decide⟩
    (prefixCache 11 23494) (prefixPartial 11 23494) = false := by
  decide +kernel

theorem node_context_11_23494_757584 : EJMOriginalGlobalDAGData.nodes 10 ⟨757584, by decide⟩ =
    .split (coordinate 11) (![⟨757267, by decide⟩,⟨757374, by decide⟩,⟨757475, by decide⟩,⟨757583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23494_757584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23494 ⟨757584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23494
    ⟨757584, by decide⟩ (by decide) (![⟨757267, by decide⟩,⟨757374, by decide⟩,⟨757475, by decide⟩,⟨757583, by decide⟩]) unmarked_context_11_23494_757584 node_context_11_23494_757584
  intro a
  fin_cases a
  · exact context_12_93976_757267
  · exact context_12_93977_757374
  · exact context_12_93978_757475
  · exact context_12_93979_757583

theorem selected_cut_29993 : selected 8 ⟨757603, by decide⟩
    (prefixPartial 13 375920) = some ⟨13, 2, 0, 757603, 375920, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_375920_757603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375920 ⟨757603, by decide⟩ :=
  accepted_of_selected 13 375920 ⟨757603, by decide⟩ ⟨13, 2, 0, 757603, 375920, 1301, 16384⟩
    (by decide) selected_cut_29993

theorem selected_cut_29994 : selected 8 ⟨757629, by decide⟩
    (prefixPartial 13 375921) = some ⟨13, 2, 0, 757629, 375921, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_375921_757629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375921 ⟨757629, by decide⟩ :=
  accepted_of_selected 13 375921 ⟨757629, by decide⟩ ⟨13, 2, 0, 757629, 375921, 1581, 16384⟩
    (by decide) selected_cut_29994

theorem selected_cut_29995 : selected 8 ⟨757647, by decide⟩
    (prefixPartial 13 375922) = some ⟨13, 2, 0, 757647, 375922, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_375922_757647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375922 ⟨757647, by decide⟩ :=
  accepted_of_selected 13 375922 ⟨757647, by decide⟩ ⟨13, 2, 0, 757647, 375922, 1325, 16384⟩
    (by decide) selected_cut_29995

theorem selected_cut_29996 : selected 8 ⟨757655, by decide⟩
    (prefixPartial 13 375923) = some ⟨13, 2, 0, 757655, 375923, 629, 16384⟩ := by
  decide +kernel

theorem context_13_375923_757655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375923 ⟨757655, by decide⟩ :=
  accepted_of_selected 13 375923 ⟨757655, by decide⟩ ⟨13, 2, 0, 757655, 375923, 629, 16384⟩
    (by decide) selected_cut_29996

theorem unmarked_context_12_93980_757656 : frontier 9 ⟨757656, by decide⟩
    (prefixCache 12 93980) (prefixPartial 12 93980) = false := by
  decide +kernel

theorem node_context_12_93980_757656 : EJMOriginalGlobalDAGData.nodes 9 ⟨757656, by decide⟩ =
    .split (coordinate 12) (![⟨757603, by decide⟩,⟨757629, by decide⟩,⟨757647, by decide⟩,⟨757655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93980_757656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93980 ⟨757656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93980
    ⟨757656, by decide⟩ (by decide) (![⟨757603, by decide⟩,⟨757629, by decide⟩,⟨757647, by decide⟩,⟨757655, by decide⟩]) unmarked_context_12_93980_757656 node_context_12_93980_757656
  intro a
  fin_cases a
  · exact context_13_375920_757603
  · exact context_13_375921_757629
  · exact context_13_375922_757647
  · exact context_13_375923_757655

theorem selected_cut_29997 : selected 8 ⟨757678, by decide⟩
    (prefixPartial 13 375924) = some ⟨13, 2, 0, 757678, 375924, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_375924_757678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375924 ⟨757678, by decide⟩ :=
  accepted_of_selected 13 375924 ⟨757678, by decide⟩ ⟨13, 2, 0, 757678, 375924, 1425, 16384⟩
    (by decide) selected_cut_29997

theorem selected_cut_29998 : selected 8 ⟨757698, by decide⟩
    (prefixPartial 13 375925) = some ⟨13, 2, 0, 757698, 375925, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_375925_757698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375925 ⟨757698, by decide⟩ :=
  accepted_of_selected 13 375925 ⟨757698, by decide⟩ ⟨13, 2, 0, 757698, 375925, 1385, 16384⟩
    (by decide) selected_cut_29998

theorem selected_cut_29999 : selected 8 ⟨757717, by decide⟩
    (prefixPartial 13 375926) = some ⟨13, 2, 0, 757717, 375926, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_375926_757717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375926 ⟨757717, by decide⟩ :=
  accepted_of_selected 13 375926 ⟨757717, by decide⟩ ⟨13, 2, 0, 757717, 375926, 1721, 16384⟩
    (by decide) selected_cut_29999

theorem selected_cut_30000 : selected 8 ⟨757724, by decide⟩
    (prefixPartial 13 375927) = some ⟨13, 2, 0, 757724, 375927, 617, 16384⟩ := by
  decide +kernel

theorem context_13_375927_757724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375927 ⟨757724, by decide⟩ :=
  accepted_of_selected 13 375927 ⟨757724, by decide⟩ ⟨13, 2, 0, 757724, 375927, 617, 16384⟩
    (by decide) selected_cut_30000

theorem unmarked_context_12_93981_757725 : frontier 9 ⟨757725, by decide⟩
    (prefixCache 12 93981) (prefixPartial 12 93981) = false := by
  decide +kernel

theorem node_context_12_93981_757725 : EJMOriginalGlobalDAGData.nodes 9 ⟨757725, by decide⟩ =
    .split (coordinate 12) (![⟨757678, by decide⟩,⟨757698, by decide⟩,⟨757717, by decide⟩,⟨757724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93981_757725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93981 ⟨757725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93981
    ⟨757725, by decide⟩ (by decide) (![⟨757678, by decide⟩,⟨757698, by decide⟩,⟨757717, by decide⟩,⟨757724, by decide⟩]) unmarked_context_12_93981_757725 node_context_12_93981_757725
  intro a
  fin_cases a
  · exact context_13_375924_757678
  · exact context_13_375925_757698
  · exact context_13_375926_757717
  · exact context_13_375927_757724

theorem selected_cut_30001 : selected 8 ⟨757747, by decide⟩
    (prefixPartial 13 375928) = some ⟨13, 2, 0, 757747, 375928, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_375928_757747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375928 ⟨757747, by decide⟩ :=
  accepted_of_selected 13 375928 ⟨757747, by decide⟩ ⟨13, 2, 0, 757747, 375928, 1393, 16384⟩
    (by decide) selected_cut_30001

theorem selected_cut_30002 : selected 8 ⟨757782, by decide⟩
    (prefixPartial 13 375929) = some ⟨13, 2, 0, 757782, 375929, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_375929_757782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375929 ⟨757782, by decide⟩ :=
  accepted_of_selected 13 375929 ⟨757782, by decide⟩ ⟨13, 2, 0, 757782, 375929, 1685, 16384⟩
    (by decide) selected_cut_30002

theorem selected_cut_30003 : selected 8 ⟨757800, by decide⟩
    (prefixPartial 13 375930) = some ⟨13, 2, 0, 757800, 375930, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_375930_757800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375930 ⟨757800, by decide⟩ :=
  accepted_of_selected 13 375930 ⟨757800, by decide⟩ ⟨13, 2, 0, 757800, 375930, 1389, 16384⟩
    (by decide) selected_cut_30003

theorem selected_cut_30004 : selected 8 ⟨757805, by decide⟩
    (prefixPartial 13 375931) = some ⟨13, 2, 0, 757805, 375931, 669, 16384⟩ := by
  decide +kernel

theorem context_13_375931_757805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375931 ⟨757805, by decide⟩ :=
  accepted_of_selected 13 375931 ⟨757805, by decide⟩ ⟨13, 2, 0, 757805, 375931, 669, 16384⟩
    (by decide) selected_cut_30004

theorem unmarked_context_12_93982_757806 : frontier 9 ⟨757806, by decide⟩
    (prefixCache 12 93982) (prefixPartial 12 93982) = false := by
  decide +kernel

theorem node_context_12_93982_757806 : EJMOriginalGlobalDAGData.nodes 9 ⟨757806, by decide⟩ =
    .split (coordinate 12) (![⟨757747, by decide⟩,⟨757782, by decide⟩,⟨757800, by decide⟩,⟨757805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93982_757806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93982 ⟨757806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93982
    ⟨757806, by decide⟩ (by decide) (![⟨757747, by decide⟩,⟨757782, by decide⟩,⟨757800, by decide⟩,⟨757805, by decide⟩]) unmarked_context_12_93982_757806 node_context_12_93982_757806
  intro a
  fin_cases a
  · exact context_13_375928_757747
  · exact context_13_375929_757782
  · exact context_13_375930_757800
  · exact context_13_375931_757805

theorem selected_cut_30005 : selected 9 ⟨757807, by decide⟩
    (prefixPartial 12 93983) = some ⟨12, 1, 0, 757807, 93983, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93983_757807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93983 ⟨757807, by decide⟩ :=
  accepted_of_selected 12 93983 ⟨757807, by decide⟩ ⟨12, 1, 0, 757807, 93983, 1, 65536⟩
    (by decide) selected_cut_30005

theorem unmarked_context_11_23495_757808 : frontier 10 ⟨757808, by decide⟩
    (prefixCache 11 23495) (prefixPartial 11 23495) = false := by
  decide +kernel

theorem node_context_11_23495_757808 : EJMOriginalGlobalDAGData.nodes 10 ⟨757808, by decide⟩ =
    .split (coordinate 11) (![⟨757656, by decide⟩,⟨757725, by decide⟩,⟨757806, by decide⟩,⟨757807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23495_757808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23495 ⟨757808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23495
    ⟨757808, by decide⟩ (by decide) (![⟨757656, by decide⟩,⟨757725, by decide⟩,⟨757806, by decide⟩,⟨757807, by decide⟩]) unmarked_context_11_23495_757808 node_context_11_23495_757808
  intro a
  fin_cases a
  · exact context_12_93980_757656
  · exact context_12_93981_757725
  · exact context_12_93982_757806
  · exact context_12_93983_757807

theorem unmarked_context_10_5873_757809 : frontier 11 ⟨757809, by decide⟩
    (prefixCache 10 5873) (prefixPartial 10 5873) = false := by
  decide +kernel

theorem node_context_10_5873_757809 : EJMOriginalGlobalDAGData.nodes 11 ⟨757809, by decide⟩ =
    .split (coordinate 10) (![⟨756740, by decide⟩,⟨757176, by decide⟩,⟨757584, by decide⟩,⟨757808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5873_757809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5873 ⟨757809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5873
    ⟨757809, by decide⟩ (by decide) (![⟨756740, by decide⟩,⟨757176, by decide⟩,⟨757584, by decide⟩,⟨757808, by decide⟩]) unmarked_context_10_5873_757809 node_context_10_5873_757809
  intro a
  fin_cases a
  · exact context_11_23492_756740
  · exact context_11_23493_757176
  · exact context_11_23494_757584
  · exact context_11_23495_757808

theorem selected_cut_30006 : selected 8 ⟨757842, by decide⟩
    (prefixPartial 13 375936) = some ⟨13, 2, 0, 757842, 375936, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_375936_757842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375936 ⟨757842, by decide⟩ :=
  accepted_of_selected 13 375936 ⟨757842, by decide⟩ ⟨13, 2, 0, 757842, 375936, 1645, 16384⟩
    (by decide) selected_cut_30006

theorem selected_cut_30007 : selected 8 ⟨757890, by decide⟩
    (prefixPartial 13 375937) = some ⟨13, 2, 0, 757890, 375937, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_375937_757890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375937 ⟨757890, by decide⟩ :=
  accepted_of_selected 13 375937 ⟨757890, by decide⟩ ⟨13, 2, 0, 757890, 375937, 1977, 16384⟩
    (by decide) selected_cut_30007

theorem selected_cut_30008 : selected 8 ⟨757912, by decide⟩
    (prefixPartial 13 375938) = some ⟨13, 2, 0, 757912, 375938, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_375938_757912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375938 ⟨757912, by decide⟩ :=
  accepted_of_selected 13 375938 ⟨757912, by decide⟩ ⟨13, 2, 0, 757912, 375938, 1261, 16384⟩
    (by decide) selected_cut_30008

theorem selected_cut_30009 : selected 8 ⟨757917, by decide⟩
    (prefixPartial 13 375939) = some ⟨13, 2, 0, 757917, 375939, 677, 16384⟩ := by
  decide +kernel

theorem context_13_375939_757917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375939 ⟨757917, by decide⟩ :=
  accepted_of_selected 13 375939 ⟨757917, by decide⟩ ⟨13, 2, 0, 757917, 375939, 677, 16384⟩
    (by decide) selected_cut_30009

theorem unmarked_context_12_93984_757918 : frontier 9 ⟨757918, by decide⟩
    (prefixCache 12 93984) (prefixPartial 12 93984) = false := by
  decide +kernel

theorem node_context_12_93984_757918 : EJMOriginalGlobalDAGData.nodes 9 ⟨757918, by decide⟩ =
    .split (coordinate 12) (![⟨757842, by decide⟩,⟨757890, by decide⟩,⟨757912, by decide⟩,⟨757917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93984_757918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93984 ⟨757918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93984
    ⟨757918, by decide⟩ (by decide) (![⟨757842, by decide⟩,⟨757890, by decide⟩,⟨757912, by decide⟩,⟨757917, by decide⟩]) unmarked_context_12_93984_757918 node_context_12_93984_757918
  intro a
  fin_cases a
  · exact context_13_375936_757842
  · exact context_13_375937_757890
  · exact context_13_375938_757912
  · exact context_13_375939_757917

theorem selected_cut_30010 : selected 8 ⟨757948, by decide⟩
    (prefixPartial 13 375940) = some ⟨13, 2, 0, 757948, 375940, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_375940_757948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375940 ⟨757948, by decide⟩ :=
  accepted_of_selected 13 375940 ⟨757948, by decide⟩ ⟨13, 2, 0, 757948, 375940, 1677, 16384⟩
    (by decide) selected_cut_30010

theorem selected_cut_30011 : selected 8 ⟨757987, by decide⟩
    (prefixPartial 13 375941) = some ⟨13, 2, 0, 757987, 375941, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_375941_757987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375941 ⟨757987, by decide⟩ :=
  accepted_of_selected 13 375941 ⟨757987, by decide⟩ ⟨13, 2, 0, 757987, 375941, 2001, 16384⟩
    (by decide) selected_cut_30011

theorem selected_cut_30012 : selected 8 ⟨758007, by decide⟩
    (prefixPartial 13 375942) = some ⟨13, 2, 0, 758007, 375942, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_375942_758007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375942 ⟨758007, by decide⟩ :=
  accepted_of_selected 13 375942 ⟨758007, by decide⟩ ⟨13, 2, 0, 758007, 375942, 1497, 16384⟩
    (by decide) selected_cut_30012

theorem selected_cut_30013 : selected 8 ⟨758011, by decide⟩
    (prefixPartial 13 375943) = some ⟨13, 2, 0, 758011, 375943, 545, 16384⟩ := by
  decide +kernel

theorem context_13_375943_758011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375943 ⟨758011, by decide⟩ :=
  accepted_of_selected 13 375943 ⟨758011, by decide⟩ ⟨13, 2, 0, 758011, 375943, 545, 16384⟩
    (by decide) selected_cut_30013

theorem unmarked_context_12_93985_758012 : frontier 9 ⟨758012, by decide⟩
    (prefixCache 12 93985) (prefixPartial 12 93985) = false := by
  decide +kernel

theorem node_context_12_93985_758012 : EJMOriginalGlobalDAGData.nodes 9 ⟨758012, by decide⟩ =
    .split (coordinate 12) (![⟨757948, by decide⟩,⟨757987, by decide⟩,⟨758007, by decide⟩,⟨758011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93985_758012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93985 ⟨758012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93985
    ⟨758012, by decide⟩ (by decide) (![⟨757948, by decide⟩,⟨757987, by decide⟩,⟨758007, by decide⟩,⟨758011, by decide⟩]) unmarked_context_12_93985_758012 node_context_12_93985_758012
  intro a
  fin_cases a
  · exact context_13_375940_757948
  · exact context_13_375941_757987
  · exact context_13_375942_758007
  · exact context_13_375943_758011

theorem selected_cut_30014 : selected 8 ⟨758035, by decide⟩
    (prefixPartial 13 375944) = some ⟨13, 2, 0, 758035, 375944, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_375944_758035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375944 ⟨758035, by decide⟩ :=
  accepted_of_selected 13 375944 ⟨758035, by decide⟩ ⟨13, 2, 0, 758035, 375944, 1517, 16384⟩
    (by decide) selected_cut_30014

theorem selected_cut_30015 : selected 8 ⟨758080, by decide⟩
    (prefixPartial 13 375945) = some ⟨13, 2, 0, 758080, 375945, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_375945_758080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375945 ⟨758080, by decide⟩ :=
  accepted_of_selected 13 375945 ⟨758080, by decide⟩ ⟨13, 2, 0, 758080, 375945, 2029, 16384⟩
    (by decide) selected_cut_30015

theorem selected_cut_30016 : selected 8 ⟨758101, by decide⟩
    (prefixPartial 13 375946) = some ⟨13, 2, 0, 758101, 375946, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_375946_758101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375946 ⟨758101, by decide⟩ :=
  accepted_of_selected 13 375946 ⟨758101, by decide⟩ ⟨13, 2, 0, 758101, 375946, 1505, 16384⟩
    (by decide) selected_cut_30016

theorem selected_cut_30017 : selected 8 ⟨758108, by decide⟩
    (prefixPartial 13 375947) = some ⟨13, 2, 0, 758108, 375947, 689, 16384⟩ := by
  decide +kernel

theorem context_13_375947_758108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375947 ⟨758108, by decide⟩ :=
  accepted_of_selected 13 375947 ⟨758108, by decide⟩ ⟨13, 2, 0, 758108, 375947, 689, 16384⟩
    (by decide) selected_cut_30017

theorem unmarked_context_12_93986_758109 : frontier 9 ⟨758109, by decide⟩
    (prefixCache 12 93986) (prefixPartial 12 93986) = false := by
  decide +kernel

theorem node_context_12_93986_758109 : EJMOriginalGlobalDAGData.nodes 9 ⟨758109, by decide⟩ =
    .split (coordinate 12) (![⟨758035, by decide⟩,⟨758080, by decide⟩,⟨758101, by decide⟩,⟨758108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93986_758109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93986 ⟨758109, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93986
    ⟨758109, by decide⟩ (by decide) (![⟨758035, by decide⟩,⟨758080, by decide⟩,⟨758101, by decide⟩,⟨758108, by decide⟩]) unmarked_context_12_93986_758109 node_context_12_93986_758109
  intro a
  fin_cases a
  · exact context_13_375944_758035
  · exact context_13_375945_758080
  · exact context_13_375946_758101
  · exact context_13_375947_758108

theorem selected_cut_30018 : selected 8 ⟨758126, by decide⟩
    (prefixPartial 13 375948) = some ⟨13, 2, 0, 758126, 375948, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_375948_758126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375948 ⟨758126, by decide⟩ :=
  accepted_of_selected 13 375948 ⟨758126, by decide⟩ ⟨13, 2, 0, 758126, 375948, 1385, 16384⟩
    (by decide) selected_cut_30018

theorem selected_cut_30019 : selected 8 ⟨758160, by decide⟩
    (prefixPartial 13 375949) = some ⟨13, 2, 0, 758160, 375949, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_375949_758160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375949 ⟨758160, by decide⟩ :=
  accepted_of_selected 13 375949 ⟨758160, by decide⟩ ⟨13, 2, 0, 758160, 375949, 2025, 16384⟩
    (by decide) selected_cut_30019

theorem selected_cut_30020 : selected 8 ⟨758180, by decide⟩
    (prefixPartial 13 375950) = some ⟨13, 2, 0, 758180, 375950, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_375950_758180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375950 ⟨758180, by decide⟩ :=
  accepted_of_selected 13 375950 ⟨758180, by decide⟩ ⟨13, 2, 0, 758180, 375950, 1565, 16384⟩
    (by decide) selected_cut_30020

theorem selected_cut_30021 : selected 8 ⟨758186, by decide⟩
    (prefixPartial 13 375951) = some ⟨13, 2, 0, 758186, 375951, 625, 16384⟩ := by
  decide +kernel

theorem context_13_375951_758186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375951 ⟨758186, by decide⟩ :=
  accepted_of_selected 13 375951 ⟨758186, by decide⟩ ⟨13, 2, 0, 758186, 375951, 625, 16384⟩
    (by decide) selected_cut_30021

theorem unmarked_context_12_93987_758187 : frontier 9 ⟨758187, by decide⟩
    (prefixCache 12 93987) (prefixPartial 12 93987) = false := by
  decide +kernel

theorem node_context_12_93987_758187 : EJMOriginalGlobalDAGData.nodes 9 ⟨758187, by decide⟩ =
    .split (coordinate 12) (![⟨758126, by decide⟩,⟨758160, by decide⟩,⟨758180, by decide⟩,⟨758186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93987_758187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93987 ⟨758187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93987
    ⟨758187, by decide⟩ (by decide) (![⟨758126, by decide⟩,⟨758160, by decide⟩,⟨758180, by decide⟩,⟨758186, by decide⟩]) unmarked_context_12_93987_758187 node_context_12_93987_758187
  intro a
  fin_cases a
  · exact context_13_375948_758126
  · exact context_13_375949_758160
  · exact context_13_375950_758180
  · exact context_13_375951_758186

theorem unmarked_context_11_23496_758188 : frontier 10 ⟨758188, by decide⟩
    (prefixCache 11 23496) (prefixPartial 11 23496) = false := by
  decide +kernel

theorem node_context_11_23496_758188 : EJMOriginalGlobalDAGData.nodes 10 ⟨758188, by decide⟩ =
    .split (coordinate 11) (![⟨757918, by decide⟩,⟨758012, by decide⟩,⟨758109, by decide⟩,⟨758187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23496_758188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23496 ⟨758188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23496
    ⟨758188, by decide⟩ (by decide) (![⟨757918, by decide⟩,⟨758012, by decide⟩,⟨758109, by decide⟩,⟨758187, by decide⟩]) unmarked_context_11_23496_758188 node_context_11_23496_758188
  intro a
  fin_cases a
  · exact context_12_93984_757918
  · exact context_12_93985_758012
  · exact context_12_93986_758109
  · exact context_12_93987_758187

theorem selected_cut_30022 : selected 8 ⟨758206, by decide⟩
    (prefixPartial 13 375952) = some ⟨13, 2, 0, 758206, 375952, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_375952_758206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375952 ⟨758206, by decide⟩ :=
  accepted_of_selected 13 375952 ⟨758206, by decide⟩ ⟨13, 2, 0, 758206, 375952, 1201, 16384⟩
    (by decide) selected_cut_30022

theorem selected_cut_30023 : selected 8 ⟨758239, by decide⟩
    (prefixPartial 13 375953) = some ⟨13, 2, 0, 758239, 375953, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_375953_758239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375953 ⟨758239, by decide⟩ :=
  accepted_of_selected 13 375953 ⟨758239, by decide⟩ ⟨13, 2, 0, 758239, 375953, 1961, 16384⟩
    (by decide) selected_cut_30023

theorem selected_cut_30024 : selected 8 ⟨758261, by decide⟩
    (prefixPartial 13 375954) = some ⟨13, 2, 0, 758261, 375954, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_375954_758261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375954 ⟨758261, by decide⟩ :=
  accepted_of_selected 13 375954 ⟨758261, by decide⟩ ⟨13, 2, 0, 758261, 375954, 1465, 16384⟩
    (by decide) selected_cut_30024

theorem selected_cut_30025 : selected 8 ⟨758268, by decide⟩
    (prefixPartial 13 375955) = some ⟨13, 2, 0, 758268, 375955, 697, 16384⟩ := by
  decide +kernel

theorem context_13_375955_758268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375955 ⟨758268, by decide⟩ :=
  accepted_of_selected 13 375955 ⟨758268, by decide⟩ ⟨13, 2, 0, 758268, 375955, 697, 16384⟩
    (by decide) selected_cut_30025

theorem unmarked_context_12_93988_758269 : frontier 9 ⟨758269, by decide⟩
    (prefixCache 12 93988) (prefixPartial 12 93988) = false := by
  decide +kernel

theorem node_context_12_93988_758269 : EJMOriginalGlobalDAGData.nodes 9 ⟨758269, by decide⟩ =
    .split (coordinate 12) (![⟨758206, by decide⟩,⟨758239, by decide⟩,⟨758261, by decide⟩,⟨758268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93988_758269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93988 ⟨758269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93988
    ⟨758269, by decide⟩ (by decide) (![⟨758206, by decide⟩,⟨758239, by decide⟩,⟨758261, by decide⟩,⟨758268, by decide⟩]) unmarked_context_12_93988_758269 node_context_12_93988_758269
  intro a
  fin_cases a
  · exact context_13_375952_758206
  · exact context_13_375953_758239
  · exact context_13_375954_758261
  · exact context_13_375955_758268

theorem selected_cut_30026 : selected 8 ⟨758289, by decide⟩
    (prefixPartial 13 375956) = some ⟨13, 2, 0, 758289, 375956, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_375956_758289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375956 ⟨758289, by decide⟩ :=
  accepted_of_selected 13 375956 ⟨758289, by decide⟩ ⟨13, 2, 0, 758289, 375956, 1289, 16384⟩
    (by decide) selected_cut_30026

theorem selected_cut_30027 : selected 8 ⟨758313, by decide⟩
    (prefixPartial 13 375957) = some ⟨13, 2, 0, 758313, 375957, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_375957_758313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375957 ⟨758313, by decide⟩ :=
  accepted_of_selected 13 375957 ⟨758313, by decide⟩ ⟨13, 2, 0, 758313, 375957, 1813, 16384⟩
    (by decide) selected_cut_30027

theorem selected_cut_30028 : selected 8 ⟨758333, by decide⟩
    (prefixPartial 13 375958) = some ⟨13, 2, 0, 758333, 375958, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_375958_758333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375958 ⟨758333, by decide⟩ :=
  accepted_of_selected 13 375958 ⟨758333, by decide⟩ ⟨13, 2, 0, 758333, 375958, 1597, 16384⟩
    (by decide) selected_cut_30028

theorem selected_cut_30029 : selected 8 ⟨758338, by decide⟩
    (prefixPartial 13 375959) = some ⟨13, 2, 0, 758338, 375959, 549, 16384⟩ := by
  decide +kernel

theorem context_13_375959_758338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375959 ⟨758338, by decide⟩ :=
  accepted_of_selected 13 375959 ⟨758338, by decide⟩ ⟨13, 2, 0, 758338, 375959, 549, 16384⟩
    (by decide) selected_cut_30029

theorem unmarked_context_12_93989_758339 : frontier 9 ⟨758339, by decide⟩
    (prefixCache 12 93989) (prefixPartial 12 93989) = false := by
  decide +kernel

theorem node_context_12_93989_758339 : EJMOriginalGlobalDAGData.nodes 9 ⟨758339, by decide⟩ =
    .split (coordinate 12) (![⟨758289, by decide⟩,⟨758313, by decide⟩,⟨758333, by decide⟩,⟨758338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93989_758339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93989 ⟨758339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93989
    ⟨758339, by decide⟩ (by decide) (![⟨758289, by decide⟩,⟨758313, by decide⟩,⟨758333, by decide⟩,⟨758338, by decide⟩]) unmarked_context_12_93989_758339 node_context_12_93989_758339
  intro a
  fin_cases a
  · exact context_13_375956_758289
  · exact context_13_375957_758313
  · exact context_13_375958_758333
  · exact context_13_375959_758338

theorem selected_cut_30030 : selected 8 ⟨758359, by decide⟩
    (prefixPartial 13 375960) = some ⟨13, 2, 0, 758359, 375960, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_375960_758359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375960 ⟨758359, by decide⟩ :=
  accepted_of_selected 13 375960 ⟨758359, by decide⟩ ⟨13, 2, 0, 758359, 375960, 1201, 16384⟩
    (by decide) selected_cut_30030

theorem selected_cut_30031 : selected 8 ⟨758387, by decide⟩
    (prefixPartial 13 375961) = some ⟨13, 2, 0, 758387, 375961, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_375961_758387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375961 ⟨758387, by decide⟩ :=
  accepted_of_selected 13 375961 ⟨758387, by decide⟩ ⟨13, 2, 0, 758387, 375961, 1841, 16384⟩
    (by decide) selected_cut_30031

theorem selected_cut_30032 : selected 8 ⟨758405, by decide⟩
    (prefixPartial 13 375962) = some ⟨13, 2, 0, 758405, 375962, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_375962_758405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375962 ⟨758405, by decide⟩ :=
  accepted_of_selected 13 375962 ⟨758405, by decide⟩ ⟨13, 2, 0, 758405, 375962, 1541, 16384⟩
    (by decide) selected_cut_30032

theorem selected_cut_30033 : selected 8 ⟨758411, by decide⟩
    (prefixPartial 13 375963) = some ⟨13, 2, 0, 758411, 375963, 781, 16384⟩ := by
  decide +kernel

theorem context_13_375963_758411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375963 ⟨758411, by decide⟩ :=
  accepted_of_selected 13 375963 ⟨758411, by decide⟩ ⟨13, 2, 0, 758411, 375963, 781, 16384⟩
    (by decide) selected_cut_30033

theorem unmarked_context_12_93990_758412 : frontier 9 ⟨758412, by decide⟩
    (prefixCache 12 93990) (prefixPartial 12 93990) = false := by
  decide +kernel

theorem node_context_12_93990_758412 : EJMOriginalGlobalDAGData.nodes 9 ⟨758412, by decide⟩ =
    .split (coordinate 12) (![⟨758359, by decide⟩,⟨758387, by decide⟩,⟨758405, by decide⟩,⟨758411, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93990_758412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93990 ⟨758412, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93990
    ⟨758412, by decide⟩ (by decide) (![⟨758359, by decide⟩,⟨758387, by decide⟩,⟨758405, by decide⟩,⟨758411, by decide⟩]) unmarked_context_12_93990_758412 node_context_12_93990_758412
  intro a
  fin_cases a
  · exact context_13_375960_758359
  · exact context_13_375961_758387
  · exact context_13_375962_758405
  · exact context_13_375963_758411

theorem selected_cut_30034 : selected 8 ⟨758428, by decide⟩
    (prefixPartial 13 375964) = some ⟨13, 2, 0, 758428, 375964, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_375964_758428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375964 ⟨758428, by decide⟩ :=
  accepted_of_selected 13 375964 ⟨758428, by decide⟩ ⟨13, 2, 0, 758428, 375964, 1169, 16384⟩
    (by decide) selected_cut_30034

theorem selected_cut_30035 : selected 8 ⟨758458, by decide⟩
    (prefixPartial 13 375965) = some ⟨13, 2, 0, 758458, 375965, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_375965_758458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375965 ⟨758458, by decide⟩ :=
  accepted_of_selected 13 375965 ⟨758458, by decide⟩ ⟨13, 2, 0, 758458, 375965, 1921, 16384⟩
    (by decide) selected_cut_30035

theorem selected_cut_30036 : selected 8 ⟨758478, by decide⟩
    (prefixPartial 13 375966) = some ⟨13, 2, 0, 758478, 375966, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_375966_758478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375966 ⟨758478, by decide⟩ :=
  accepted_of_selected 13 375966 ⟨758478, by decide⟩ ⟨13, 2, 0, 758478, 375966, 1741, 16384⟩
    (by decide) selected_cut_30036

theorem selected_cut_30037 : selected 8 ⟨758483, by decide⟩
    (prefixPartial 13 375967) = some ⟨13, 2, 0, 758483, 375967, 677, 16384⟩ := by
  decide +kernel

theorem context_13_375967_758483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375967 ⟨758483, by decide⟩ :=
  accepted_of_selected 13 375967 ⟨758483, by decide⟩ ⟨13, 2, 0, 758483, 375967, 677, 16384⟩
    (by decide) selected_cut_30037

theorem unmarked_context_12_93991_758484 : frontier 9 ⟨758484, by decide⟩
    (prefixCache 12 93991) (prefixPartial 12 93991) = false := by
  decide +kernel

theorem node_context_12_93991_758484 : EJMOriginalGlobalDAGData.nodes 9 ⟨758484, by decide⟩ =
    .split (coordinate 12) (![⟨758428, by decide⟩,⟨758458, by decide⟩,⟨758478, by decide⟩,⟨758483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93991_758484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93991 ⟨758484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93991
    ⟨758484, by decide⟩ (by decide) (![⟨758428, by decide⟩,⟨758458, by decide⟩,⟨758478, by decide⟩,⟨758483, by decide⟩]) unmarked_context_12_93991_758484 node_context_12_93991_758484
  intro a
  fin_cases a
  · exact context_13_375964_758428
  · exact context_13_375965_758458
  · exact context_13_375966_758478
  · exact context_13_375967_758483

theorem unmarked_context_11_23497_758485 : frontier 10 ⟨758485, by decide⟩
    (prefixCache 11 23497) (prefixPartial 11 23497) = false := by
  decide +kernel

theorem node_context_11_23497_758485 : EJMOriginalGlobalDAGData.nodes 10 ⟨758485, by decide⟩ =
    .split (coordinate 11) (![⟨758269, by decide⟩,⟨758339, by decide⟩,⟨758412, by decide⟩,⟨758484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23497_758485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23497 ⟨758485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23497
    ⟨758485, by decide⟩ (by decide) (![⟨758269, by decide⟩,⟨758339, by decide⟩,⟨758412, by decide⟩,⟨758484, by decide⟩]) unmarked_context_11_23497_758485 node_context_11_23497_758485
  intro a
  fin_cases a
  · exact context_12_93988_758269
  · exact context_12_93989_758339
  · exact context_12_93990_758412
  · exact context_12_93991_758484

theorem selected_cut_30038 : selected 8 ⟨758496, by decide⟩
    (prefixPartial 13 375968) = some ⟨13, 2, 0, 758496, 375968, 877, 16384⟩ := by
  decide +kernel

theorem context_13_375968_758496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375968 ⟨758496, by decide⟩ :=
  accepted_of_selected 13 375968 ⟨758496, by decide⟩ ⟨13, 2, 0, 758496, 375968, 877, 16384⟩
    (by decide) selected_cut_30038

theorem selected_cut_30039 : selected 8 ⟨758533, by decide⟩
    (prefixPartial 13 375969) = some ⟨13, 2, 0, 758533, 375969, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_375969_758533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375969 ⟨758533, by decide⟩ :=
  accepted_of_selected 13 375969 ⟨758533, by decide⟩ ⟨13, 2, 0, 758533, 375969, 1993, 16384⟩
    (by decide) selected_cut_30039

theorem selected_cut_30040 : selected 8 ⟨758556, by decide⟩
    (prefixPartial 13 375970) = some ⟨13, 2, 0, 758556, 375970, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_375970_758556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375970 ⟨758556, by decide⟩ :=
  accepted_of_selected 13 375970 ⟨758556, by decide⟩ ⟨13, 2, 0, 758556, 375970, 1545, 16384⟩
    (by decide) selected_cut_30040

theorem selected_cut_30041 : selected 8 ⟨758563, by decide⟩
    (prefixPartial 13 375971) = some ⟨13, 2, 0, 758563, 375971, 653, 16384⟩ := by
  decide +kernel

theorem context_13_375971_758563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375971 ⟨758563, by decide⟩ :=
  accepted_of_selected 13 375971 ⟨758563, by decide⟩ ⟨13, 2, 0, 758563, 375971, 653, 16384⟩
    (by decide) selected_cut_30041

theorem unmarked_context_12_93992_758564 : frontier 9 ⟨758564, by decide⟩
    (prefixCache 12 93992) (prefixPartial 12 93992) = false := by
  decide +kernel

theorem node_context_12_93992_758564 : EJMOriginalGlobalDAGData.nodes 9 ⟨758564, by decide⟩ =
    .split (coordinate 12) (![⟨758496, by decide⟩,⟨758533, by decide⟩,⟨758556, by decide⟩,⟨758563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93992_758564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93992 ⟨758564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93992
    ⟨758564, by decide⟩ (by decide) (![⟨758496, by decide⟩,⟨758533, by decide⟩,⟨758556, by decide⟩,⟨758563, by decide⟩]) unmarked_context_12_93992_758564 node_context_12_93992_758564
  intro a
  fin_cases a
  · exact context_13_375968_758496
  · exact context_13_375969_758533
  · exact context_13_375970_758556
  · exact context_13_375971_758563

theorem selected_cut_30042 : selected 8 ⟨758580, by decide⟩
    (prefixPartial 13 375972) = some ⟨13, 2, 0, 758580, 375972, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_375972_758580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375972 ⟨758580, by decide⟩ :=
  accepted_of_selected 13 375972 ⟨758580, by decide⟩ ⟨13, 2, 0, 758580, 375972, 1093, 16384⟩
    (by decide) selected_cut_30042

theorem selected_cut_30043 : selected 8 ⟨758611, by decide⟩
    (prefixPartial 13 375973) = some ⟨13, 2, 0, 758611, 375973, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_375973_758611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375973 ⟨758611, by decide⟩ :=
  accepted_of_selected 13 375973 ⟨758611, by decide⟩ ⟨13, 2, 0, 758611, 375973, 1781, 16384⟩
    (by decide) selected_cut_30043

theorem selected_cut_30044 : selected 8 ⟨758632, by decide⟩
    (prefixPartial 13 375974) = some ⟨13, 2, 0, 758632, 375974, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_375974_758632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375974 ⟨758632, by decide⟩ :=
  accepted_of_selected 13 375974 ⟨758632, by decide⟩ ⟨13, 2, 0, 758632, 375974, 1717, 16384⟩
    (by decide) selected_cut_30044

theorem selected_cut_30045 : selected 8 ⟨758635, by decide⟩
    (prefixPartial 13 375975) = some ⟨13, 2, 0, 758635, 375975, 573, 16384⟩ := by
  decide +kernel

theorem context_13_375975_758635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375975 ⟨758635, by decide⟩ :=
  accepted_of_selected 13 375975 ⟨758635, by decide⟩ ⟨13, 2, 0, 758635, 375975, 573, 16384⟩
    (by decide) selected_cut_30045

theorem unmarked_context_12_93993_758636 : frontier 9 ⟨758636, by decide⟩
    (prefixCache 12 93993) (prefixPartial 12 93993) = false := by
  decide +kernel

theorem node_context_12_93993_758636 : EJMOriginalGlobalDAGData.nodes 9 ⟨758636, by decide⟩ =
    .split (coordinate 12) (![⟨758580, by decide⟩,⟨758611, by decide⟩,⟨758632, by decide⟩,⟨758635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93993_758636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93993 ⟨758636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93993
    ⟨758636, by decide⟩ (by decide) (![⟨758580, by decide⟩,⟨758611, by decide⟩,⟨758632, by decide⟩,⟨758635, by decide⟩]) unmarked_context_12_93993_758636 node_context_12_93993_758636
  intro a
  fin_cases a
  · exact context_13_375972_758580
  · exact context_13_375973_758611
  · exact context_13_375974_758632
  · exact context_13_375975_758635

theorem selected_cut_30046 : selected 8 ⟨758646, by decide⟩
    (prefixPartial 13 375976) = some ⟨13, 2, 0, 758646, 375976, 793, 16384⟩ := by
  decide +kernel

theorem context_13_375976_758646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375976 ⟨758646, by decide⟩ :=
  accepted_of_selected 13 375976 ⟨758646, by decide⟩ ⟨13, 2, 0, 758646, 375976, 793, 16384⟩
    (by decide) selected_cut_30046

theorem selected_cut_30047 : selected 8 ⟨758673, by decide⟩
    (prefixPartial 13 375977) = some ⟨13, 2, 0, 758673, 375977, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_375977_758673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375977 ⟨758673, by decide⟩ :=
  accepted_of_selected 13 375977 ⟨758673, by decide⟩ ⟨13, 2, 0, 758673, 375977, 1877, 16384⟩
    (by decide) selected_cut_30047

theorem selected_cut_30048 : selected 8 ⟨758693, by decide⟩
    (prefixPartial 13 375978) = some ⟨13, 2, 0, 758693, 375978, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_375978_758693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375978 ⟨758693, by decide⟩ :=
  accepted_of_selected 13 375978 ⟨758693, by decide⟩ ⟨13, 2, 0, 758693, 375978, 1649, 16384⟩
    (by decide) selected_cut_30048

theorem selected_cut_30049 : selected 8 ⟨758698, by decide⟩
    (prefixPartial 13 375979) = some ⟨13, 2, 0, 758698, 375979, 709, 16384⟩ := by
  decide +kernel

theorem context_13_375979_758698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375979 ⟨758698, by decide⟩ :=
  accepted_of_selected 13 375979 ⟨758698, by decide⟩ ⟨13, 2, 0, 758698, 375979, 709, 16384⟩
    (by decide) selected_cut_30049

theorem unmarked_context_12_93994_758699 : frontier 9 ⟨758699, by decide⟩
    (prefixCache 12 93994) (prefixPartial 12 93994) = false := by
  decide +kernel

theorem node_context_12_93994_758699 : EJMOriginalGlobalDAGData.nodes 9 ⟨758699, by decide⟩ =
    .split (coordinate 12) (![⟨758646, by decide⟩,⟨758673, by decide⟩,⟨758693, by decide⟩,⟨758698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93994_758699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93994 ⟨758699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93994
    ⟨758699, by decide⟩ (by decide) (![⟨758646, by decide⟩,⟨758673, by decide⟩,⟨758693, by decide⟩,⟨758698, by decide⟩]) unmarked_context_12_93994_758699 node_context_12_93994_758699
  intro a
  fin_cases a
  · exact context_13_375976_758646
  · exact context_13_375977_758673
  · exact context_13_375978_758693
  · exact context_13_375979_758698

theorem selected_cut_30050 : selected 8 ⟨758712, by decide⟩
    (prefixPartial 13 375980) = some ⟨13, 2, 0, 758712, 375980, 745, 16384⟩ := by
  decide +kernel

theorem context_13_375980_758712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375980 ⟨758712, by decide⟩ :=
  accepted_of_selected 13 375980 ⟨758712, by decide⟩ ⟨13, 2, 0, 758712, 375980, 745, 16384⟩
    (by decide) selected_cut_30050

theorem selected_cut_30051 : selected 8 ⟨758747, by decide⟩
    (prefixPartial 13 375981) = some ⟨13, 2, 0, 758747, 375981, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_375981_758747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375981 ⟨758747, by decide⟩ :=
  accepted_of_selected 13 375981 ⟨758747, by decide⟩ ⟨13, 2, 0, 758747, 375981, 1933, 16384⟩
    (by decide) selected_cut_30051

theorem selected_cut_30052 : selected 8 ⟨758769, by decide⟩
    (prefixPartial 13 375982) = some ⟨13, 2, 0, 758769, 375982, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_375982_758769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375982 ⟨758769, by decide⟩ :=
  accepted_of_selected 13 375982 ⟨758769, by decide⟩ ⟨13, 2, 0, 758769, 375982, 1757, 16384⟩
    (by decide) selected_cut_30052

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
