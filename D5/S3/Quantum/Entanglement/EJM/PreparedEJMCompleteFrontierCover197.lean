/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover196
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_18915 : selected 8 ⟨484605, by decide⟩
    (prefixPartial 13 287862) = some ⟨13, 2, 0, 484605, 287862, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_287862_484605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287862 ⟨484605, by decide⟩ :=
  accepted_of_selected 13 287862 ⟨484605, by decide⟩ ⟨13, 2, 0, 484605, 287862, 2137, 16384⟩
    (by decide) selected_cut_18915

theorem selected_cut_18916 : selected 8 ⟨484613, by decide⟩
    (prefixPartial 13 287863) = some ⟨13, 2, 0, 484613, 287863, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_287863_484613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287863 ⟨484613, by decide⟩ :=
  accepted_of_selected 13 287863 ⟨484613, by decide⟩ ⟨13, 2, 0, 484613, 287863, 1093, 16384⟩
    (by decide) selected_cut_18916

theorem unmarked_context_12_71965_484614 : frontier 9 ⟨484614, by decide⟩
    (prefixCache 12 71965) (prefixPartial 12 71965) = false := by
  decide +kernel

theorem node_context_12_71965_484614 : EJMOriginalGlobalDAGData.nodes 9 ⟨484614, by decide⟩ =
    .split (coordinate 12) (![⟨484547, by decide⟩,⟨484582, by decide⟩,⟨484605, by decide⟩,⟨484613, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71965_484614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71965 ⟨484614, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71965
    ⟨484614, by decide⟩ (by decide) (![⟨484547, by decide⟩,⟨484582, by decide⟩,⟨484605, by decide⟩,⟨484613, by decide⟩]) unmarked_context_12_71965_484614 node_context_12_71965_484614
  intro a
  fin_cases a
  · exact context_13_287860_484547
  · exact context_13_287861_484582
  · exact context_13_287862_484605
  · exact context_13_287863_484613

theorem selected_cut_18917 : selected 8 ⟨484668, by decide⟩
    (prefixPartial 13 287864) = some ⟨13, 2, 0, 484668, 287864, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_287864_484668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287864 ⟨484668, by decide⟩ :=
  accepted_of_selected 13 287864 ⟨484668, by decide⟩ ⟨13, 2, 0, 484668, 287864, 2433, 16384⟩
    (by decide) selected_cut_18917

theorem selected_cut_18918 : selected 8 ⟨484706, by decide⟩
    (prefixPartial 13 287865) = some ⟨13, 2, 0, 484706, 287865, 2909, 16384⟩ := by
  decide +kernel

theorem context_13_287865_484706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287865 ⟨484706, by decide⟩ :=
  accepted_of_selected 13 287865 ⟨484706, by decide⟩ ⟨13, 2, 0, 484706, 287865, 2909, 16384⟩
    (by decide) selected_cut_18918

theorem selected_cut_18919 : selected 8 ⟨484746, by decide⟩
    (prefixPartial 13 287866) = some ⟨13, 2, 0, 484746, 287866, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_287866_484746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287866 ⟨484746, by decide⟩ :=
  accepted_of_selected 13 287866 ⟨484746, by decide⟩ ⟨13, 2, 0, 484746, 287866, 2445, 16384⟩
    (by decide) selected_cut_18919

theorem selected_cut_18920 : selected 8 ⟨484763, by decide⟩
    (prefixPartial 13 287867) = some ⟨13, 2, 0, 484763, 287867, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_287867_484763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287867 ⟨484763, by decide⟩ :=
  accepted_of_selected 13 287867 ⟨484763, by decide⟩ ⟨13, 2, 0, 484763, 287867, 1265, 16384⟩
    (by decide) selected_cut_18920

theorem unmarked_context_12_71966_484764 : frontier 9 ⟨484764, by decide⟩
    (prefixCache 12 71966) (prefixPartial 12 71966) = false := by
  decide +kernel

theorem node_context_12_71966_484764 : EJMOriginalGlobalDAGData.nodes 9 ⟨484764, by decide⟩ =
    .split (coordinate 12) (![⟨484668, by decide⟩,⟨484706, by decide⟩,⟨484746, by decide⟩,⟨484763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71966_484764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71966 ⟨484764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71966
    ⟨484764, by decide⟩ (by decide) (![⟨484668, by decide⟩,⟨484706, by decide⟩,⟨484746, by decide⟩,⟨484763, by decide⟩]) unmarked_context_12_71966_484764 node_context_12_71966_484764
  intro a
  fin_cases a
  · exact context_13_287864_484668
  · exact context_13_287865_484706
  · exact context_13_287866_484746
  · exact context_13_287867_484763

theorem selected_cut_18921 : selected 8 ⟨484806, by decide⟩
    (prefixPartial 13 287868) = some ⟨13, 2, 0, 484806, 287868, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_287868_484806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287868 ⟨484806, by decide⟩ :=
  accepted_of_selected 13 287868 ⟨484806, by decide⟩ ⟨13, 2, 0, 484806, 287868, 2257, 16384⟩
    (by decide) selected_cut_18921

theorem selected_cut_18922 : selected 8 ⟨484847, by decide⟩
    (prefixPartial 13 287869) = some ⟨13, 2, 0, 484847, 287869, 2965, 16384⟩ := by
  decide +kernel

theorem context_13_287869_484847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287869 ⟨484847, by decide⟩ :=
  accepted_of_selected 13 287869 ⟨484847, by decide⟩ ⟨13, 2, 0, 484847, 287869, 2965, 16384⟩
    (by decide) selected_cut_18922

theorem selected_cut_18923 : selected 8 ⟨484881, by decide⟩
    (prefixPartial 13 287870) = some ⟨13, 2, 0, 484881, 287870, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_287870_484881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287870 ⟨484881, by decide⟩ :=
  accepted_of_selected 13 287870 ⟨484881, by decide⟩ ⟨13, 2, 0, 484881, 287870, 2505, 16384⟩
    (by decide) selected_cut_18923

theorem selected_cut_18924 : selected 8 ⟨484889, by decide⟩
    (prefixPartial 13 287871) = some ⟨13, 2, 0, 484889, 287871, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_287871_484889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287871 ⟨484889, by decide⟩ :=
  accepted_of_selected 13 287871 ⟨484889, by decide⟩ ⟨13, 2, 0, 484889, 287871, 1085, 16384⟩
    (by decide) selected_cut_18924

theorem unmarked_context_12_71967_484890 : frontier 9 ⟨484890, by decide⟩
    (prefixCache 12 71967) (prefixPartial 12 71967) = false := by
  decide +kernel

theorem node_context_12_71967_484890 : EJMOriginalGlobalDAGData.nodes 9 ⟨484890, by decide⟩ =
    .split (coordinate 12) (![⟨484806, by decide⟩,⟨484847, by decide⟩,⟨484881, by decide⟩,⟨484889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71967_484890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71967 ⟨484890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71967
    ⟨484890, by decide⟩ (by decide) (![⟨484806, by decide⟩,⟨484847, by decide⟩,⟨484881, by decide⟩,⟨484889, by decide⟩]) unmarked_context_12_71967_484890 node_context_12_71967_484890
  intro a
  fin_cases a
  · exact context_13_287868_484806
  · exact context_13_287869_484847
  · exact context_13_287870_484881
  · exact context_13_287871_484889

theorem unmarked_context_11_17991_484891 : frontier 10 ⟨484891, by decide⟩
    (prefixCache 11 17991) (prefixPartial 11 17991) = false := by
  decide +kernel

theorem node_context_11_17991_484891 : EJMOriginalGlobalDAGData.nodes 10 ⟨484891, by decide⟩ =
    .split (coordinate 11) (![⟨484508, by decide⟩,⟨484614, by decide⟩,⟨484764, by decide⟩,⟨484890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17991_484891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17991 ⟨484891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17991
    ⟨484891, by decide⟩ (by decide) (![⟨484508, by decide⟩,⟨484614, by decide⟩,⟨484764, by decide⟩,⟨484890, by decide⟩]) unmarked_context_11_17991_484891 node_context_11_17991_484891
  intro a
  fin_cases a
  · exact context_12_71964_484508
  · exact context_12_71965_484614
  · exact context_12_71966_484764
  · exact context_12_71967_484890

theorem unmarked_context_10_4497_484892 : frontier 11 ⟨484892, by decide⟩
    (prefixCache 10 4497) (prefixPartial 10 4497) = false := by
  decide +kernel

theorem node_context_10_4497_484892 : EJMOriginalGlobalDAGData.nodes 11 ⟨484892, by decide⟩ =
    .split (coordinate 10) (![⟨483488, by decide⟩,⟨483759, by decide⟩,⟨484293, by decide⟩,⟨484891, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4497_484892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4497 ⟨484892, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4497
    ⟨484892, by decide⟩ (by decide) (![⟨483488, by decide⟩,⟨483759, by decide⟩,⟨484293, by decide⟩,⟨484891, by decide⟩]) unmarked_context_10_4497_484892 node_context_10_4497_484892
  intro a
  fin_cases a
  · exact context_11_17988_483488
  · exact context_11_17989_483759
  · exact context_11_17990_484293
  · exact context_11_17991_484891

theorem selected_cut_18925 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 71968) = some ⟨12, 1, 0, 435790, 71968, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71968_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71968 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 71968 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 71968, 1, 65536⟩
    (by decide) selected_cut_18925

theorem selected_cut_18926 : selected 8 ⟨484922, by decide⟩
    (prefixPartial 13 287876) = some ⟨13, 2, 0, 484922, 287876, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_287876_484922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287876 ⟨484922, by decide⟩ :=
  accepted_of_selected 13 287876 ⟨484922, by decide⟩ ⟨13, 2, 0, 484922, 287876, 1581, 16384⟩
    (by decide) selected_cut_18926

theorem selected_cut_18927 : selected 8 ⟨484952, by decide⟩
    (prefixPartial 13 287877) = some ⟨13, 2, 0, 484952, 287877, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_287877_484952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287877 ⟨484952, by decide⟩ :=
  accepted_of_selected 13 287877 ⟨484952, by decide⟩ ⟨13, 2, 0, 484952, 287877, 2321, 16384⟩
    (by decide) selected_cut_18927

theorem selected_cut_18928 : selected 8 ⟨484972, by decide⟩
    (prefixPartial 13 287878) = some ⟨13, 2, 0, 484972, 287878, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_287878_484972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287878 ⟨484972, by decide⟩ :=
  accepted_of_selected 13 287878 ⟨484972, by decide⟩ ⟨13, 2, 0, 484972, 287878, 1773, 16384⟩
    (by decide) selected_cut_18928

theorem selected_cut_18929 : selected 8 ⟨484977, by decide⟩
    (prefixPartial 13 287879) = some ⟨13, 2, 0, 484977, 287879, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_287879_484977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287879 ⟨484977, by decide⟩ :=
  accepted_of_selected 13 287879 ⟨484977, by decide⟩ ⟨13, 2, 0, 484977, 287879, 1021, 16384⟩
    (by decide) selected_cut_18929

theorem unmarked_context_12_71969_484978 : frontier 9 ⟨484978, by decide⟩
    (prefixCache 12 71969) (prefixPartial 12 71969) = false := by
  decide +kernel

theorem node_context_12_71969_484978 : EJMOriginalGlobalDAGData.nodes 9 ⟨484978, by decide⟩ =
    .split (coordinate 12) (![⟨484922, by decide⟩,⟨484952, by decide⟩,⟨484972, by decide⟩,⟨484977, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71969_484978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71969 ⟨484978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71969
    ⟨484978, by decide⟩ (by decide) (![⟨484922, by decide⟩,⟨484952, by decide⟩,⟨484972, by decide⟩,⟨484977, by decide⟩]) unmarked_context_12_71969_484978 node_context_12_71969_484978
  intro a
  fin_cases a
  · exact context_13_287876_484922
  · exact context_13_287877_484952
  · exact context_13_287878_484972
  · exact context_13_287879_484977

theorem selected_cut_18930 : selected 8 ⟨485017, by decide⟩
    (prefixPartial 13 287880) = some ⟨13, 2, 0, 485017, 287880, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_287880_485017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287880 ⟨485017, by decide⟩ :=
  accepted_of_selected 13 287880 ⟨485017, by decide⟩ ⟨13, 2, 0, 485017, 287880, 1913, 16384⟩
    (by decide) selected_cut_18930

theorem selected_cut_18931 : selected 8 ⟨485066, by decide⟩
    (prefixPartial 13 287881) = some ⟨13, 2, 0, 485066, 287881, 2905, 16384⟩ := by
  decide +kernel

theorem context_13_287881_485066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287881 ⟨485066, by decide⟩ :=
  accepted_of_selected 13 287881 ⟨485066, by decide⟩ ⟨13, 2, 0, 485066, 287881, 2905, 16384⟩
    (by decide) selected_cut_18931

theorem selected_cut_18932 : selected 8 ⟨485102, by decide⟩
    (prefixPartial 13 287882) = some ⟨13, 2, 0, 485102, 287882, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_287882_485102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287882 ⟨485102, by decide⟩ :=
  accepted_of_selected 13 287882 ⟨485102, by decide⟩ ⟨13, 2, 0, 485102, 287882, 2025, 16384⟩
    (by decide) selected_cut_18932

theorem selected_cut_18933 : selected 8 ⟨485112, by decide⟩
    (prefixPartial 13 287883) = some ⟨13, 2, 0, 485112, 287883, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_287883_485112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287883 ⟨485112, by decide⟩ :=
  accepted_of_selected 13 287883 ⟨485112, by decide⟩ ⟨13, 2, 0, 485112, 287883, 1125, 16384⟩
    (by decide) selected_cut_18933

theorem unmarked_context_12_71970_485113 : frontier 9 ⟨485113, by decide⟩
    (prefixCache 12 71970) (prefixPartial 12 71970) = false := by
  decide +kernel

theorem node_context_12_71970_485113 : EJMOriginalGlobalDAGData.nodes 9 ⟨485113, by decide⟩ =
    .split (coordinate 12) (![⟨485017, by decide⟩,⟨485066, by decide⟩,⟨485102, by decide⟩,⟨485112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71970_485113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71970 ⟨485113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71970
    ⟨485113, by decide⟩ (by decide) (![⟨485017, by decide⟩,⟨485066, by decide⟩,⟨485102, by decide⟩,⟨485112, by decide⟩]) unmarked_context_12_71970_485113 node_context_12_71970_485113
  intro a
  fin_cases a
  · exact context_13_287880_485017
  · exact context_13_287881_485066
  · exact context_13_287882_485102
  · exact context_13_287883_485112

theorem selected_cut_18934 : selected 8 ⟨485150, by decide⟩
    (prefixPartial 13 287884) = some ⟨13, 2, 0, 485150, 287884, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_287884_485150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287884 ⟨485150, by decide⟩ :=
  accepted_of_selected 13 287884 ⟨485150, by decide⟩ ⟨13, 2, 0, 485150, 287884, 1921, 16384⟩
    (by decide) selected_cut_18934

theorem selected_cut_18935 : selected 8 ⟨485199, by decide⟩
    (prefixPartial 13 287885) = some ⟨13, 2, 0, 485199, 287885, 3001, 16384⟩ := by
  decide +kernel

theorem context_13_287885_485199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287885 ⟨485199, by decide⟩ :=
  accepted_of_selected 13 287885 ⟨485199, by decide⟩ ⟨13, 2, 0, 485199, 287885, 3001, 16384⟩
    (by decide) selected_cut_18935

theorem selected_cut_18936 : selected 8 ⟨485224, by decide⟩
    (prefixPartial 13 287886) = some ⟨13, 2, 0, 485224, 287886, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_287886_485224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287886 ⟨485224, by decide⟩ :=
  accepted_of_selected 13 287886 ⟨485224, by decide⟩ ⟨13, 2, 0, 485224, 287886, 2149, 16384⟩
    (by decide) selected_cut_18936

theorem selected_cut_18937 : selected 8 ⟨485231, by decide⟩
    (prefixPartial 13 287887) = some ⟨13, 2, 0, 485231, 287887, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_287887_485231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287887 ⟨485231, by decide⟩ :=
  accepted_of_selected 13 287887 ⟨485231, by decide⟩ ⟨13, 2, 0, 485231, 287887, 1017, 16384⟩
    (by decide) selected_cut_18937

theorem unmarked_context_12_71971_485232 : frontier 9 ⟨485232, by decide⟩
    (prefixCache 12 71971) (prefixPartial 12 71971) = false := by
  decide +kernel

theorem node_context_12_71971_485232 : EJMOriginalGlobalDAGData.nodes 9 ⟨485232, by decide⟩ =
    .split (coordinate 12) (![⟨485150, by decide⟩,⟨485199, by decide⟩,⟨485224, by decide⟩,⟨485231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71971_485232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71971 ⟨485232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71971
    ⟨485232, by decide⟩ (by decide) (![⟨485150, by decide⟩,⟨485199, by decide⟩,⟨485224, by decide⟩,⟨485231, by decide⟩]) unmarked_context_12_71971_485232 node_context_12_71971_485232
  intro a
  fin_cases a
  · exact context_13_287884_485150
  · exact context_13_287885_485199
  · exact context_13_287886_485224
  · exact context_13_287887_485231

theorem unmarked_context_11_17992_485233 : frontier 10 ⟨485233, by decide⟩
    (prefixCache 11 17992) (prefixPartial 11 17992) = false := by
  decide +kernel

theorem node_context_11_17992_485233 : EJMOriginalGlobalDAGData.nodes 10 ⟨485233, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨484978, by decide⟩,⟨485113, by decide⟩,⟨485232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17992_485233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17992 ⟨485233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17992
    ⟨485233, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨484978, by decide⟩,⟨485113, by decide⟩,⟨485232, by decide⟩]) unmarked_context_11_17992_485233 node_context_11_17992_485233
  intro a
  fin_cases a
  · exact context_12_71968_435790
  · exact context_12_71969_484978
  · exact context_12_71970_485113
  · exact context_12_71971_485232

theorem selected_cut_18938 : selected 8 ⟨485276, by decide⟩
    (prefixPartial 13 287888) = some ⟨13, 2, 0, 485276, 287888, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_287888_485276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287888 ⟨485276, by decide⟩ :=
  accepted_of_selected 13 287888 ⟨485276, by decide⟩ ⟨13, 2, 0, 485276, 287888, 2313, 16384⟩
    (by decide) selected_cut_18938

theorem selected_cut_18939 : selected 8 ⟨485330, by decide⟩
    (prefixPartial 13 287889) = some ⟨13, 2, 0, 485330, 287889, 3341, 16384⟩ := by
  decide +kernel

theorem context_13_287889_485330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287889 ⟨485330, by decide⟩ :=
  accepted_of_selected 13 287889 ⟨485330, by decide⟩ ⟨13, 2, 0, 485330, 287889, 3341, 16384⟩
    (by decide) selected_cut_18939

theorem selected_cut_18940 : selected 8 ⟨485356, by decide⟩
    (prefixPartial 13 287890) = some ⟨13, 2, 0, 485356, 287890, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_287890_485356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287890 ⟨485356, by decide⟩ :=
  accepted_of_selected 13 287890 ⟨485356, by decide⟩ ⟨13, 2, 0, 485356, 287890, 2021, 16384⟩
    (by decide) selected_cut_18940

theorem selected_cut_18941 : selected 8 ⟨485387, by decide⟩
    (prefixPartial 13 287891) = some ⟨13, 2, 0, 485387, 287891, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_287891_485387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287891 ⟨485387, by decide⟩ :=
  accepted_of_selected 13 287891 ⟨485387, by decide⟩ ⟨13, 2, 0, 485387, 287891, 1381, 16384⟩
    (by decide) selected_cut_18941

theorem unmarked_context_12_71972_485388 : frontier 9 ⟨485388, by decide⟩
    (prefixCache 12 71972) (prefixPartial 12 71972) = false := by
  decide +kernel

theorem node_context_12_71972_485388 : EJMOriginalGlobalDAGData.nodes 9 ⟨485388, by decide⟩ =
    .split (coordinate 12) (![⟨485276, by decide⟩,⟨485330, by decide⟩,⟨485356, by decide⟩,⟨485387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71972_485388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71972 ⟨485388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71972
    ⟨485388, by decide⟩ (by decide) (![⟨485276, by decide⟩,⟨485330, by decide⟩,⟨485356, by decide⟩,⟨485387, by decide⟩]) unmarked_context_12_71972_485388 node_context_12_71972_485388
  intro a
  fin_cases a
  · exact context_13_287888_485276
  · exact context_13_287889_485330
  · exact context_13_287890_485356
  · exact context_13_287891_485387

theorem selected_cut_18942 : selected 8 ⟨485433, by decide⟩
    (prefixPartial 13 287892) = some ⟨13, 2, 0, 485433, 287892, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_287892_485433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287892 ⟨485433, by decide⟩ :=
  accepted_of_selected 13 287892 ⟨485433, by decide⟩ ⟨13, 2, 0, 485433, 287892, 2389, 16384⟩
    (by decide) selected_cut_18942

theorem selected_cut_18943 : selected 8 ⟨485504, by decide⟩
    (prefixPartial 13 287893) = some ⟨13, 2, 0, 485504, 287893, 4093, 16384⟩ := by
  decide +kernel

theorem context_13_287893_485504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287893 ⟨485504, by decide⟩ :=
  accepted_of_selected 13 287893 ⟨485504, by decide⟩ ⟨13, 2, 0, 485504, 287893, 4093, 16384⟩
    (by decide) selected_cut_18943

theorem selected_cut_18944 : selected 8 ⟨485533, by decide⟩
    (prefixPartial 13 287894) = some ⟨13, 2, 0, 485533, 287894, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_287894_485533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287894 ⟨485533, by decide⟩ :=
  accepted_of_selected 13 287894 ⟨485533, by decide⟩ ⟨13, 2, 0, 485533, 287894, 2265, 16384⟩
    (by decide) selected_cut_18944

theorem selected_cut_18945 : selected 8 ⟨485558, by decide⟩
    (prefixPartial 13 287895) = some ⟨13, 2, 0, 485558, 287895, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_287895_485558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287895 ⟨485558, by decide⟩ :=
  accepted_of_selected 13 287895 ⟨485558, by decide⟩ ⟨13, 2, 0, 485558, 287895, 1517, 16384⟩
    (by decide) selected_cut_18945

theorem unmarked_context_12_71973_485559 : frontier 9 ⟨485559, by decide⟩
    (prefixCache 12 71973) (prefixPartial 12 71973) = false := by
  decide +kernel

theorem node_context_12_71973_485559 : EJMOriginalGlobalDAGData.nodes 9 ⟨485559, by decide⟩ =
    .split (coordinate 12) (![⟨485433, by decide⟩,⟨485504, by decide⟩,⟨485533, by decide⟩,⟨485558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71973_485559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71973 ⟨485559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71973
    ⟨485559, by decide⟩ (by decide) (![⟨485433, by decide⟩,⟨485504, by decide⟩,⟨485533, by decide⟩,⟨485558, by decide⟩]) unmarked_context_12_71973_485559 node_context_12_71973_485559
  intro a
  fin_cases a
  · exact context_13_287892_485433
  · exact context_13_287893_485504
  · exact context_13_287894_485533
  · exact context_13_287895_485558

theorem selected_cut_18946 : selected 8 ⟨485597, by decide⟩
    (prefixPartial 13 287896) = some ⟨13, 2, 0, 485597, 287896, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_287896_485597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287896 ⟨485597, by decide⟩ :=
  accepted_of_selected 13 287896 ⟨485597, by decide⟩ ⟨13, 2, 0, 485597, 287896, 1737, 16384⟩
    (by decide) selected_cut_18946

theorem selected_cut_18947 : selected 8 ⟨485633, by decide⟩
    (prefixPartial 13 287897) = some ⟨13, 2, 0, 485633, 287897, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_287897_485633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287897 ⟨485633, by decide⟩ :=
  accepted_of_selected 13 287897 ⟨485633, by decide⟩ ⟨13, 2, 0, 485633, 287897, 2761, 16384⟩
    (by decide) selected_cut_18947

theorem selected_cut_18948 : selected 8 ⟨485654, by decide⟩
    (prefixPartial 13 287898) = some ⟨13, 2, 0, 485654, 287898, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_287898_485654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287898 ⟨485654, by decide⟩ :=
  accepted_of_selected 13 287898 ⟨485654, by decide⟩ ⟨13, 2, 0, 485654, 287898, 1577, 16384⟩
    (by decide) selected_cut_18948

theorem selected_cut_18949 : selected 8 ⟨485665, by decide⟩
    (prefixPartial 13 287899) = some ⟨13, 2, 0, 485665, 287899, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_287899_485665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287899 ⟨485665, by decide⟩ :=
  accepted_of_selected 13 287899 ⟨485665, by decide⟩ ⟨13, 2, 0, 485665, 287899, 1249, 16384⟩
    (by decide) selected_cut_18949

theorem unmarked_context_12_71974_485666 : frontier 9 ⟨485666, by decide⟩
    (prefixCache 12 71974) (prefixPartial 12 71974) = false := by
  decide +kernel

theorem node_context_12_71974_485666 : EJMOriginalGlobalDAGData.nodes 9 ⟨485666, by decide⟩ =
    .split (coordinate 12) (![⟨485597, by decide⟩,⟨485633, by decide⟩,⟨485654, by decide⟩,⟨485665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71974_485666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71974 ⟨485666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71974
    ⟨485666, by decide⟩ (by decide) (![⟨485597, by decide⟩,⟨485633, by decide⟩,⟨485654, by decide⟩,⟨485665, by decide⟩]) unmarked_context_12_71974_485666 node_context_12_71974_485666
  intro a
  fin_cases a
  · exact context_13_287896_485597
  · exact context_13_287897_485633
  · exact context_13_287898_485654
  · exact context_13_287899_485665

theorem selected_cut_18950 : selected 8 ⟨485695, by decide⟩
    (prefixPartial 13 287900) = some ⟨13, 2, 0, 485695, 287900, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_287900_485695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287900 ⟨485695, by decide⟩ :=
  accepted_of_selected 13 287900 ⟨485695, by decide⟩ ⟨13, 2, 0, 485695, 287900, 1721, 16384⟩
    (by decide) selected_cut_18950

theorem selected_cut_18951 : selected 8 ⟨485729, by decide⟩
    (prefixPartial 13 287901) = some ⟨13, 2, 0, 485729, 287901, 2921, 16384⟩ := by
  decide +kernel

theorem context_13_287901_485729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287901 ⟨485729, by decide⟩ :=
  accepted_of_selected 13 287901 ⟨485729, by decide⟩ ⟨13, 2, 0, 485729, 287901, 2921, 16384⟩
    (by decide) selected_cut_18951

theorem selected_cut_18952 : selected 8 ⟨485750, by decide⟩
    (prefixPartial 13 287902) = some ⟨13, 2, 0, 485750, 287902, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_287902_485750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287902 ⟨485750, by decide⟩ :=
  accepted_of_selected 13 287902 ⟨485750, by decide⟩ ⟨13, 2, 0, 485750, 287902, 1837, 16384⟩
    (by decide) selected_cut_18952

theorem selected_cut_18953 : selected 8 ⟨485756, by decide⟩
    (prefixPartial 13 287903) = some ⟨13, 2, 0, 485756, 287903, 973, 16384⟩ := by
  decide +kernel

theorem context_13_287903_485756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287903 ⟨485756, by decide⟩ :=
  accepted_of_selected 13 287903 ⟨485756, by decide⟩ ⟨13, 2, 0, 485756, 287903, 973, 16384⟩
    (by decide) selected_cut_18953

theorem unmarked_context_12_71975_485757 : frontier 9 ⟨485757, by decide⟩
    (prefixCache 12 71975) (prefixPartial 12 71975) = false := by
  decide +kernel

theorem node_context_12_71975_485757 : EJMOriginalGlobalDAGData.nodes 9 ⟨485757, by decide⟩ =
    .split (coordinate 12) (![⟨485695, by decide⟩,⟨485729, by decide⟩,⟨485750, by decide⟩,⟨485756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71975_485757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71975 ⟨485757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71975
    ⟨485757, by decide⟩ (by decide) (![⟨485695, by decide⟩,⟨485729, by decide⟩,⟨485750, by decide⟩,⟨485756, by decide⟩]) unmarked_context_12_71975_485757 node_context_12_71975_485757
  intro a
  fin_cases a
  · exact context_13_287900_485695
  · exact context_13_287901_485729
  · exact context_13_287902_485750
  · exact context_13_287903_485756

theorem unmarked_context_11_17993_485758 : frontier 10 ⟨485758, by decide⟩
    (prefixCache 11 17993) (prefixPartial 11 17993) = false := by
  decide +kernel

theorem node_context_11_17993_485758 : EJMOriginalGlobalDAGData.nodes 10 ⟨485758, by decide⟩ =
    .split (coordinate 11) (![⟨485388, by decide⟩,⟨485559, by decide⟩,⟨485666, by decide⟩,⟨485757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17993_485758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17993 ⟨485758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17993
    ⟨485758, by decide⟩ (by decide) (![⟨485388, by decide⟩,⟨485559, by decide⟩,⟨485666, by decide⟩,⟨485757, by decide⟩]) unmarked_context_11_17993_485758 node_context_11_17993_485758
  intro a
  fin_cases a
  · exact context_12_71972_485388
  · exact context_12_71973_485559
  · exact context_12_71974_485666
  · exact context_12_71975_485757

theorem selected_cut_18954 : selected 8 ⟨485794, by decide⟩
    (prefixPartial 13 287904) = some ⟨13, 2, 0, 485794, 287904, 749, 16384⟩ := by
  decide +kernel

theorem context_13_287904_485794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287904 ⟨485794, by decide⟩ :=
  accepted_of_selected 13 287904 ⟨485794, by decide⟩ ⟨13, 2, 0, 485794, 287904, 749, 16384⟩
    (by decide) selected_cut_18954

theorem selected_cut_18955 : selected 7 ⟨485819, by decide⟩
    (prefixPartial 14 1151620) = some ⟨14, 2, 0, 485819, 1151620, 1033, 4096⟩ := by
  decide +kernel

theorem context_14_1151620_485819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151620 ⟨485819, by decide⟩ :=
  accepted_of_selected 14 1151620 ⟨485819, by decide⟩ ⟨14, 2, 0, 485819, 1151620, 1033, 4096⟩
    (by decide) selected_cut_18955

theorem selected_cut_18956 : selected 7 ⟨485845, by decide⟩
    (prefixPartial 14 1151621) = some ⟨14, 2, 0, 485845, 1151621, 1085, 4096⟩ := by
  decide +kernel

theorem context_14_1151621_485845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151621 ⟨485845, by decide⟩ :=
  accepted_of_selected 14 1151621 ⟨485845, by decide⟩ ⟨14, 2, 0, 485845, 1151621, 1085, 4096⟩
    (by decide) selected_cut_18956

theorem selected_cut_18957 : selected 7 ⟨485891, by decide⟩
    (prefixPartial 14 1151622) = some ⟨14, 2, 0, 485891, 1151622, 1353, 4096⟩ := by
  decide +kernel

theorem context_14_1151622_485891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151622 ⟨485891, by decide⟩ :=
  accepted_of_selected 14 1151622 ⟨485891, by decide⟩ ⟨14, 2, 0, 485891, 1151622, 1353, 4096⟩
    (by decide) selected_cut_18957

theorem selected_cut_18958 : selected 7 ⟨485936, by decide⟩
    (prefixPartial 14 1151623) = some ⟨14, 2, 0, 485936, 1151623, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_1151623_485936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151623 ⟨485936, by decide⟩ :=
  accepted_of_selected 14 1151623 ⟨485936, by decide⟩ ⟨14, 2, 0, 485936, 1151623, 1181, 4096⟩
    (by decide) selected_cut_18958

theorem unmarked_context_13_287905_485937 : frontier 8 ⟨485937, by decide⟩
    (prefixCache 13 287905) (prefixPartial 13 287905) = false := by
  decide +kernel

theorem node_context_13_287905_485937 : EJMOriginalGlobalDAGData.nodes 8 ⟨485937, by decide⟩ =
    .split (coordinate 13) (![⟨485819, by decide⟩,⟨485845, by decide⟩,⟨485891, by decide⟩,⟨485936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287905_485937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287905 ⟨485937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287905
    ⟨485937, by decide⟩ (by decide) (![⟨485819, by decide⟩,⟨485845, by decide⟩,⟨485891, by decide⟩,⟨485936, by decide⟩]) unmarked_context_13_287905_485937 node_context_13_287905_485937
  intro a
  fin_cases a
  · exact context_14_1151620_485819
  · exact context_14_1151621_485845
  · exact context_14_1151622_485891
  · exact context_14_1151623_485936

theorem selected_cut_18959 : selected 8 ⟨72292, by decide⟩
    (prefixPartial 13 287906) = some ⟨13, 1, 0, 72292, 287906, 1, 16384⟩ := by
  decide +kernel

theorem context_13_287906_72292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287906 ⟨72292, by decide⟩ :=
  accepted_of_selected 13 287906 ⟨72292, by decide⟩ ⟨13, 1, 0, 72292, 287906, 1, 16384⟩
    (by decide) selected_cut_18959

theorem selected_cut_18960 : selected 8 ⟨486042, by decide⟩
    (prefixPartial 13 287907) = some ⟨13, 2, 0, 486042, 287907, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_287907_486042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287907 ⟨486042, by decide⟩ :=
  accepted_of_selected 13 287907 ⟨486042, by decide⟩ ⟨13, 2, 0, 486042, 287907, 1349, 16384⟩
    (by decide) selected_cut_18960

theorem unmarked_context_12_71976_486043 : frontier 9 ⟨486043, by decide⟩
    (prefixCache 12 71976) (prefixPartial 12 71976) = false := by
  decide +kernel

theorem node_context_12_71976_486043 : EJMOriginalGlobalDAGData.nodes 9 ⟨486043, by decide⟩ =
    .split (coordinate 12) (![⟨485794, by decide⟩,⟨485937, by decide⟩,⟨72292, by decide⟩,⟨486042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71976_486043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71976 ⟨486043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71976
    ⟨486043, by decide⟩ (by decide) (![⟨485794, by decide⟩,⟨485937, by decide⟩,⟨72292, by decide⟩,⟨486042, by decide⟩]) unmarked_context_12_71976_486043 node_context_12_71976_486043
  intro a
  fin_cases a
  · exact context_13_287904_485794
  · exact context_13_287905_485937
  · exact context_13_287906_72292
  · exact context_13_287907_486042

theorem selected_cut_18961 : selected 8 ⟨486072, by decide⟩
    (prefixPartial 13 287908) = some ⟨13, 2, 0, 486072, 287908, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_287908_486072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287908 ⟨486072, by decide⟩ :=
  accepted_of_selected 13 287908 ⟨486072, by decide⟩ ⟨13, 2, 0, 486072, 287908, 1689, 16384⟩
    (by decide) selected_cut_18961

theorem selected_cut_18962 : selected 8 ⟨486107, by decide⟩
    (prefixPartial 13 287909) = some ⟨13, 2, 0, 486107, 287909, 2905, 16384⟩ := by
  decide +kernel

theorem context_13_287909_486107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287909 ⟨486107, by decide⟩ :=
  accepted_of_selected 13 287909 ⟨486107, by decide⟩ ⟨13, 2, 0, 486107, 287909, 2905, 16384⟩
    (by decide) selected_cut_18962

theorem selected_cut_18963 : selected 8 ⟨486130, by decide⟩
    (prefixPartial 13 287910) = some ⟨13, 2, 0, 486130, 287910, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_287910_486130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287910 ⟨486130, by decide⟩ :=
  accepted_of_selected 13 287910 ⟨486130, by decide⟩ ⟨13, 2, 0, 486130, 287910, 2189, 16384⟩
    (by decide) selected_cut_18963

theorem selected_cut_18964 : selected 8 ⟨486155, by decide⟩
    (prefixPartial 13 287911) = some ⟨13, 2, 0, 486155, 287911, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_287911_486155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287911 ⟨486155, by decide⟩ :=
  accepted_of_selected 13 287911 ⟨486155, by decide⟩ ⟨13, 2, 0, 486155, 287911, 1365, 16384⟩
    (by decide) selected_cut_18964

theorem unmarked_context_12_71977_486156 : frontier 9 ⟨486156, by decide⟩
    (prefixCache 12 71977) (prefixPartial 12 71977) = false := by
  decide +kernel

theorem node_context_12_71977_486156 : EJMOriginalGlobalDAGData.nodes 9 ⟨486156, by decide⟩ =
    .split (coordinate 12) (![⟨486072, by decide⟩,⟨486107, by decide⟩,⟨486130, by decide⟩,⟨486155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71977_486156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71977 ⟨486156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71977
    ⟨486156, by decide⟩ (by decide) (![⟨486072, by decide⟩,⟨486107, by decide⟩,⟨486130, by decide⟩,⟨486155, by decide⟩]) unmarked_context_12_71977_486156 node_context_12_71977_486156
  intro a
  fin_cases a
  · exact context_13_287908_486072
  · exact context_13_287909_486107
  · exact context_13_287910_486130
  · exact context_13_287911_486155

theorem selected_cut_18965 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 71978) = some ⟨12, 1, 0, 474208, 71978, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71978_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71978 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 71978 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 71978, 1, 65536⟩
    (by decide) selected_cut_18965

theorem selected_cut_18966 : selected 8 ⟨486188, by decide⟩
    (prefixPartial 13 287916) = some ⟨13, 2, 0, 486188, 287916, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_287916_486188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287916 ⟨486188, by decide⟩ :=
  accepted_of_selected 13 287916 ⟨486188, by decide⟩ ⟨13, 2, 0, 486188, 287916, 1929, 16384⟩
    (by decide) selected_cut_18966

theorem selected_cut_18967 : selected 8 ⟨486237, by decide⟩
    (prefixPartial 13 287917) = some ⟨13, 2, 0, 486237, 287917, 3701, 16384⟩ := by
  decide +kernel

theorem context_13_287917_486237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287917 ⟨486237, by decide⟩ :=
  accepted_of_selected 13 287917 ⟨486237, by decide⟩ ⟨13, 2, 0, 486237, 287917, 3701, 16384⟩
    (by decide) selected_cut_18967

theorem selected_cut_18968 : selected 8 ⟨486275, by decide⟩
    (prefixPartial 13 287918) = some ⟨13, 2, 0, 486275, 287918, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_287918_486275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287918 ⟨486275, by decide⟩ :=
  accepted_of_selected 13 287918 ⟨486275, by decide⟩ ⟨13, 2, 0, 486275, 287918, 2521, 16384⟩
    (by decide) selected_cut_18968

theorem selected_cut_18969 : selected 8 ⟨486290, by decide⟩
    (prefixPartial 13 287919) = some ⟨13, 2, 0, 486290, 287919, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_287919_486290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287919 ⟨486290, by decide⟩ :=
  accepted_of_selected 13 287919 ⟨486290, by decide⟩ ⟨13, 2, 0, 486290, 287919, 1305, 16384⟩
    (by decide) selected_cut_18969

theorem unmarked_context_12_71979_486291 : frontier 9 ⟨486291, by decide⟩
    (prefixCache 12 71979) (prefixPartial 12 71979) = false := by
  decide +kernel

theorem node_context_12_71979_486291 : EJMOriginalGlobalDAGData.nodes 9 ⟨486291, by decide⟩ =
    .split (coordinate 12) (![⟨486188, by decide⟩,⟨486237, by decide⟩,⟨486275, by decide⟩,⟨486290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71979_486291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71979 ⟨486291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71979
    ⟨486291, by decide⟩ (by decide) (![⟨486188, by decide⟩,⟨486237, by decide⟩,⟨486275, by decide⟩,⟨486290, by decide⟩]) unmarked_context_12_71979_486291 node_context_12_71979_486291
  intro a
  fin_cases a
  · exact context_13_287916_486188
  · exact context_13_287917_486237
  · exact context_13_287918_486275
  · exact context_13_287919_486290

theorem unmarked_context_11_17994_486292 : frontier 10 ⟨486292, by decide⟩
    (prefixCache 11 17994) (prefixPartial 11 17994) = false := by
  decide +kernel

theorem node_context_11_17994_486292 : EJMOriginalGlobalDAGData.nodes 10 ⟨486292, by decide⟩ =
    .split (coordinate 11) (![⟨486043, by decide⟩,⟨486156, by decide⟩,⟨474208, by decide⟩,⟨486291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17994_486292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17994 ⟨486292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17994
    ⟨486292, by decide⟩ (by decide) (![⟨486043, by decide⟩,⟨486156, by decide⟩,⟨474208, by decide⟩,⟨486291, by decide⟩]) unmarked_context_11_17994_486292 node_context_11_17994_486292
  intro a
  fin_cases a
  · exact context_12_71976_486043
  · exact context_12_71977_486156
  · exact context_12_71978_474208
  · exact context_12_71979_486291

theorem selected_cut_18970 : selected 8 ⟨486321, by decide⟩
    (prefixPartial 13 287920) = some ⟨13, 2, 0, 486321, 287920, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_287920_486321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287920 ⟨486321, by decide⟩ :=
  accepted_of_selected 13 287920 ⟨486321, by decide⟩ ⟨13, 2, 0, 486321, 287920, 1741, 16384⟩
    (by decide) selected_cut_18970

theorem selected_cut_18971 : selected 8 ⟨486383, by decide⟩
    (prefixPartial 13 287921) = some ⟨13, 2, 0, 486383, 287921, 3965, 16384⟩ := by
  decide +kernel

theorem context_13_287921_486383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287921 ⟨486383, by decide⟩ :=
  accepted_of_selected 13 287921 ⟨486383, by decide⟩ ⟨13, 2, 0, 486383, 287921, 3965, 16384⟩
    (by decide) selected_cut_18971

theorem selected_cut_18972 : selected 8 ⟨486432, by decide⟩
    (prefixPartial 13 287922) = some ⟨13, 2, 0, 486432, 287922, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_287922_486432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287922 ⟨486432, by decide⟩ :=
  accepted_of_selected 13 287922 ⟨486432, by decide⟩ ⟨13, 2, 0, 486432, 287922, 2701, 16384⟩
    (by decide) selected_cut_18972

theorem selected_cut_18973 : selected 8 ⟨486466, by decide⟩
    (prefixPartial 13 287923) = some ⟨13, 2, 0, 486466, 287923, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_287923_486466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287923 ⟨486466, by decide⟩ :=
  accepted_of_selected 13 287923 ⟨486466, by decide⟩ ⟨13, 2, 0, 486466, 287923, 1525, 16384⟩
    (by decide) selected_cut_18973

theorem unmarked_context_12_71980_486467 : frontier 9 ⟨486467, by decide⟩
    (prefixCache 12 71980) (prefixPartial 12 71980) = false := by
  decide +kernel

theorem node_context_12_71980_486467 : EJMOriginalGlobalDAGData.nodes 9 ⟨486467, by decide⟩ =
    .split (coordinate 12) (![⟨486321, by decide⟩,⟨486383, by decide⟩,⟨486432, by decide⟩,⟨486466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71980_486467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71980 ⟨486467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71980
    ⟨486467, by decide⟩ (by decide) (![⟨486321, by decide⟩,⟨486383, by decide⟩,⟨486432, by decide⟩,⟨486466, by decide⟩]) unmarked_context_12_71980_486467 node_context_12_71980_486467
  intro a
  fin_cases a
  · exact context_13_287920_486321
  · exact context_13_287921_486383
  · exact context_13_287922_486432
  · exact context_13_287923_486466

theorem selected_cut_18974 : selected 8 ⟨486488, by decide⟩
    (prefixPartial 13 287924) = some ⟨13, 2, 0, 486488, 287924, 933, 16384⟩ := by
  decide +kernel

theorem context_13_287924_486488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287924 ⟨486488, by decide⟩ :=
  accepted_of_selected 13 287924 ⟨486488, by decide⟩ ⟨13, 2, 0, 486488, 287924, 933, 16384⟩
    (by decide) selected_cut_18974

theorem selected_cut_18975 : selected 8 ⟨486527, by decide⟩
    (prefixPartial 13 287925) = some ⟨13, 2, 0, 486527, 287925, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_287925_486527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287925 ⟨486527, by decide⟩ :=
  accepted_of_selected 13 287925 ⟨486527, by decide⟩ ⟨13, 2, 0, 486527, 287925, 2333, 16384⟩
    (by decide) selected_cut_18975

theorem selected_cut_18976 : selected 8 ⟨486551, by decide⟩
    (prefixPartial 13 287926) = some ⟨13, 2, 0, 486551, 287926, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_287926_486551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287926 ⟨486551, by decide⟩ :=
  accepted_of_selected 13 287926 ⟨486551, by decide⟩ ⟨13, 2, 0, 486551, 287926, 1969, 16384⟩
    (by decide) selected_cut_18976

theorem selected_cut_18977 : selected 8 ⟨486559, by decide⟩
    (prefixPartial 13 287927) = some ⟨13, 2, 0, 486559, 287927, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_287927_486559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287927 ⟨486559, by decide⟩ :=
  accepted_of_selected 13 287927 ⟨486559, by decide⟩ ⟨13, 2, 0, 486559, 287927, 1041, 16384⟩
    (by decide) selected_cut_18977

theorem unmarked_context_12_71981_486560 : frontier 9 ⟨486560, by decide⟩
    (prefixCache 12 71981) (prefixPartial 12 71981) = false := by
  decide +kernel

theorem node_context_12_71981_486560 : EJMOriginalGlobalDAGData.nodes 9 ⟨486560, by decide⟩ =
    .split (coordinate 12) (![⟨486488, by decide⟩,⟨486527, by decide⟩,⟨486551, by decide⟩,⟨486559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71981_486560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71981 ⟨486560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71981
    ⟨486560, by decide⟩ (by decide) (![⟨486488, by decide⟩,⟨486527, by decide⟩,⟨486551, by decide⟩,⟨486559, by decide⟩]) unmarked_context_12_71981_486560 node_context_12_71981_486560
  intro a
  fin_cases a
  · exact context_13_287924_486488
  · exact context_13_287925_486527
  · exact context_13_287926_486551
  · exact context_13_287927_486559

theorem selected_cut_18978 : selected 8 ⟨486581, by decide⟩
    (prefixPartial 13 287928) = some ⟨13, 2, 0, 486581, 287928, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_287928_486581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287928 ⟨486581, by decide⟩ :=
  accepted_of_selected 13 287928 ⟨486581, by decide⟩ ⟨13, 2, 0, 486581, 287928, 1109, 16384⟩
    (by decide) selected_cut_18978

theorem selected_cut_18979 : selected 8 ⟨486633, by decide⟩
    (prefixPartial 13 287929) = some ⟨13, 2, 0, 486633, 287929, 3061, 16384⟩ := by
  decide +kernel

theorem context_13_287929_486633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287929 ⟨486633, by decide⟩ :=
  accepted_of_selected 13 287929 ⟨486633, by decide⟩ ⟨13, 2, 0, 486633, 287929, 3061, 16384⟩
    (by decide) selected_cut_18979

theorem selected_cut_18980 : selected 8 ⟨486676, by decide⟩
    (prefixPartial 13 287930) = some ⟨13, 2, 0, 486676, 287930, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_287930_486676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287930 ⟨486676, by decide⟩ :=
  accepted_of_selected 13 287930 ⟨486676, by decide⟩ ⟨13, 2, 0, 486676, 287930, 2217, 16384⟩
    (by decide) selected_cut_18980

theorem selected_cut_18981 : selected 8 ⟨486689, by decide⟩
    (prefixPartial 13 287931) = some ⟨13, 2, 0, 486689, 287931, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_287931_486689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287931 ⟨486689, by decide⟩ :=
  accepted_of_selected 13 287931 ⟨486689, by decide⟩ ⟨13, 2, 0, 486689, 287931, 1153, 16384⟩
    (by decide) selected_cut_18981

theorem unmarked_context_12_71982_486690 : frontier 9 ⟨486690, by decide⟩
    (prefixCache 12 71982) (prefixPartial 12 71982) = false := by
  decide +kernel

theorem node_context_12_71982_486690 : EJMOriginalGlobalDAGData.nodes 9 ⟨486690, by decide⟩ =
    .split (coordinate 12) (![⟨486581, by decide⟩,⟨486633, by decide⟩,⟨486676, by decide⟩,⟨486689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71982_486690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71982 ⟨486690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71982
    ⟨486690, by decide⟩ (by decide) (![⟨486581, by decide⟩,⟨486633, by decide⟩,⟨486676, by decide⟩,⟨486689, by decide⟩]) unmarked_context_12_71982_486690 node_context_12_71982_486690
  intro a
  fin_cases a
  · exact context_13_287928_486581
  · exact context_13_287929_486633
  · exact context_13_287930_486676
  · exact context_13_287931_486689

theorem selected_cut_18982 : selected 8 ⟨486711, by decide⟩
    (prefixPartial 13 287932) = some ⟨13, 2, 0, 486711, 287932, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_287932_486711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287932 ⟨486711, by decide⟩ :=
  accepted_of_selected 13 287932 ⟨486711, by decide⟩ ⟨13, 2, 0, 486711, 287932, 1081, 16384⟩
    (by decide) selected_cut_18982

theorem selected_cut_18983 : selected 8 ⟨486757, by decide⟩
    (prefixPartial 13 287933) = some ⟨13, 2, 0, 486757, 287933, 3161, 16384⟩ := by
  decide +kernel

theorem context_13_287933_486757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287933 ⟨486757, by decide⟩ :=
  accepted_of_selected 13 287933 ⟨486757, by decide⟩ ⟨13, 2, 0, 486757, 287933, 3161, 16384⟩
    (by decide) selected_cut_18983

theorem selected_cut_18984 : selected 8 ⟨486783, by decide⟩
    (prefixPartial 13 287934) = some ⟨13, 2, 0, 486783, 287934, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_287934_486783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287934 ⟨486783, by decide⟩ :=
  accepted_of_selected 13 287934 ⟨486783, by decide⟩ ⟨13, 2, 0, 486783, 287934, 2241, 16384⟩
    (by decide) selected_cut_18984

theorem selected_cut_18985 : selected 8 ⟨486791, by decide⟩
    (prefixPartial 13 287935) = some ⟨13, 2, 0, 486791, 287935, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_287935_486791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287935 ⟨486791, by decide⟩ :=
  accepted_of_selected 13 287935 ⟨486791, by decide⟩ ⟨13, 2, 0, 486791, 287935, 1065, 16384⟩
    (by decide) selected_cut_18985

theorem unmarked_context_12_71983_486792 : frontier 9 ⟨486792, by decide⟩
    (prefixCache 12 71983) (prefixPartial 12 71983) = false := by
  decide +kernel

theorem node_context_12_71983_486792 : EJMOriginalGlobalDAGData.nodes 9 ⟨486792, by decide⟩ =
    .split (coordinate 12) (![⟨486711, by decide⟩,⟨486757, by decide⟩,⟨486783, by decide⟩,⟨486791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71983_486792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71983 ⟨486792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71983
    ⟨486792, by decide⟩ (by decide) (![⟨486711, by decide⟩,⟨486757, by decide⟩,⟨486783, by decide⟩,⟨486791, by decide⟩]) unmarked_context_12_71983_486792 node_context_12_71983_486792
  intro a
  fin_cases a
  · exact context_13_287932_486711
  · exact context_13_287933_486757
  · exact context_13_287934_486783
  · exact context_13_287935_486791

theorem unmarked_context_11_17995_486793 : frontier 10 ⟨486793, by decide⟩
    (prefixCache 11 17995) (prefixPartial 11 17995) = false := by
  decide +kernel

theorem node_context_11_17995_486793 : EJMOriginalGlobalDAGData.nodes 10 ⟨486793, by decide⟩ =
    .split (coordinate 11) (![⟨486467, by decide⟩,⟨486560, by decide⟩,⟨486690, by decide⟩,⟨486792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17995_486793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17995 ⟨486793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17995
    ⟨486793, by decide⟩ (by decide) (![⟨486467, by decide⟩,⟨486560, by decide⟩,⟨486690, by decide⟩,⟨486792, by decide⟩]) unmarked_context_11_17995_486793 node_context_11_17995_486793
  intro a
  fin_cases a
  · exact context_12_71980_486467
  · exact context_12_71981_486560
  · exact context_12_71982_486690
  · exact context_12_71983_486792

theorem unmarked_context_10_4498_486794 : frontier 11 ⟨486794, by decide⟩
    (prefixCache 10 4498) (prefixPartial 10 4498) = false := by
  decide +kernel

theorem node_context_10_4498_486794 : EJMOriginalGlobalDAGData.nodes 11 ⟨486794, by decide⟩ =
    .split (coordinate 10) (![⟨485233, by decide⟩,⟨485758, by decide⟩,⟨486292, by decide⟩,⟨486793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4498_486794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4498 ⟨486794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4498
    ⟨486794, by decide⟩ (by decide) (![⟨485233, by decide⟩,⟨485758, by decide⟩,⟨486292, by decide⟩,⟨486793, by decide⟩]) unmarked_context_10_4498_486794 node_context_10_4498_486794
  intro a
  fin_cases a
  · exact context_11_17992_485233
  · exact context_11_17993_485758
  · exact context_11_17994_486292
  · exact context_11_17995_486793

theorem selected_cut_18986 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 71984) = some ⟨12, 1, 0, 445562, 71984, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71984_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71984 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 71984 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 71984, 1, 65536⟩
    (by decide) selected_cut_18986

theorem selected_cut_18987 : selected 8 ⟨486807, by decide⟩
    (prefixPartial 13 287940) = some ⟨13, 2, 0, 486807, 287940, 929, 16384⟩ := by
  decide +kernel

theorem context_13_287940_486807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287940 ⟨486807, by decide⟩ :=
  accepted_of_selected 13 287940 ⟨486807, by decide⟩ ⟨13, 2, 0, 486807, 287940, 929, 16384⟩
    (by decide) selected_cut_18987

theorem selected_cut_18988 : selected 8 ⟨486836, by decide⟩
    (prefixPartial 13 287941) = some ⟨13, 2, 0, 486836, 287941, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_287941_486836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287941 ⟨486836, by decide⟩ :=
  accepted_of_selected 13 287941 ⟨486836, by decide⟩ ⟨13, 2, 0, 486836, 287941, 2337, 16384⟩
    (by decide) selected_cut_18988

theorem selected_cut_18989 : selected 8 ⟨486858, by decide⟩
    (prefixPartial 13 287942) = some ⟨13, 2, 0, 486858, 287942, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_287942_486858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287942 ⟨486858, by decide⟩ :=
  accepted_of_selected 13 287942 ⟨486858, by decide⟩ ⟨13, 2, 0, 486858, 287942, 1893, 16384⟩
    (by decide) selected_cut_18989

theorem selected_cut_18990 : selected 8 ⟨486863, by decide⟩
    (prefixPartial 13 287943) = some ⟨13, 2, 0, 486863, 287943, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_287943_486863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287943 ⟨486863, by decide⟩ :=
  accepted_of_selected 13 287943 ⟨486863, by decide⟩ ⟨13, 2, 0, 486863, 287943, 1033, 16384⟩
    (by decide) selected_cut_18990

theorem unmarked_context_12_71985_486864 : frontier 9 ⟨486864, by decide⟩
    (prefixCache 12 71985) (prefixPartial 12 71985) = false := by
  decide +kernel

theorem node_context_12_71985_486864 : EJMOriginalGlobalDAGData.nodes 9 ⟨486864, by decide⟩ =
    .split (coordinate 12) (![⟨486807, by decide⟩,⟨486836, by decide⟩,⟨486858, by decide⟩,⟨486863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71985_486864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71985 ⟨486864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71985
    ⟨486864, by decide⟩ (by decide) (![⟨486807, by decide⟩,⟨486836, by decide⟩,⟨486858, by decide⟩,⟨486863, by decide⟩]) unmarked_context_12_71985_486864 node_context_12_71985_486864
  intro a
  fin_cases a
  · exact context_13_287940_486807
  · exact context_13_287941_486836
  · exact context_13_287942_486858
  · exact context_13_287943_486863

theorem selected_cut_18991 : selected 8 ⟨486888, by decide⟩
    (prefixPartial 13 287944) = some ⟨13, 2, 0, 486888, 287944, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_287944_486888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287944 ⟨486888, by decide⟩ :=
  accepted_of_selected 13 287944 ⟨486888, by decide⟩ ⟨13, 2, 0, 486888, 287944, 1241, 16384⟩
    (by decide) selected_cut_18991

theorem selected_cut_18992 : selected 8 ⟨486934, by decide⟩
    (prefixPartial 13 287945) = some ⟨13, 2, 0, 486934, 287945, 2881, 16384⟩ := by
  decide +kernel

theorem context_13_287945_486934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287945 ⟨486934, by decide⟩ :=
  accepted_of_selected 13 287945 ⟨486934, by decide⟩ ⟨13, 2, 0, 486934, 287945, 2881, 16384⟩
    (by decide) selected_cut_18992

theorem selected_cut_18993 : selected 8 ⟨486978, by decide⟩
    (prefixPartial 13 287946) = some ⟨13, 2, 0, 486978, 287946, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_287946_486978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287946 ⟨486978, by decide⟩ :=
  accepted_of_selected 13 287946 ⟨486978, by decide⟩ ⟨13, 2, 0, 486978, 287946, 2301, 16384⟩
    (by decide) selected_cut_18993

theorem selected_cut_18994 : selected 8 ⟨486987, by decide⟩
    (prefixPartial 13 287947) = some ⟨13, 2, 0, 486987, 287947, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_287947_486987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287947 ⟨486987, by decide⟩ :=
  accepted_of_selected 13 287947 ⟨486987, by decide⟩ ⟨13, 2, 0, 486987, 287947, 1137, 16384⟩
    (by decide) selected_cut_18994

theorem unmarked_context_12_71986_486988 : frontier 9 ⟨486988, by decide⟩
    (prefixCache 12 71986) (prefixPartial 12 71986) = false := by
  decide +kernel

theorem node_context_12_71986_486988 : EJMOriginalGlobalDAGData.nodes 9 ⟨486988, by decide⟩ =
    .split (coordinate 12) (![⟨486888, by decide⟩,⟨486934, by decide⟩,⟨486978, by decide⟩,⟨486987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71986_486988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71986 ⟨486988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71986
    ⟨486988, by decide⟩ (by decide) (![⟨486888, by decide⟩,⟨486934, by decide⟩,⟨486978, by decide⟩,⟨486987, by decide⟩]) unmarked_context_12_71986_486988 node_context_12_71986_486988
  intro a
  fin_cases a
  · exact context_13_287944_486888
  · exact context_13_287945_486934
  · exact context_13_287946_486978
  · exact context_13_287947_486987

theorem selected_cut_18995 : selected 8 ⟨487009, by decide⟩
    (prefixPartial 13 287948) = some ⟨13, 2, 0, 487009, 287948, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_287948_487009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287948 ⟨487009, by decide⟩ :=
  accepted_of_selected 13 287948 ⟨487009, by decide⟩ ⟨13, 2, 0, 487009, 287948, 1261, 16384⟩
    (by decide) selected_cut_18995

theorem selected_cut_18996 : selected 8 ⟨487050, by decide⟩
    (prefixPartial 13 287949) = some ⟨13, 2, 0, 487050, 287949, 2905, 16384⟩ := by
  decide +kernel

theorem context_13_287949_487050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287949 ⟨487050, by decide⟩ :=
  accepted_of_selected 13 287949 ⟨487050, by decide⟩ ⟨13, 2, 0, 487050, 287949, 2905, 16384⟩
    (by decide) selected_cut_18996

theorem selected_cut_18997 : selected 8 ⟨487090, by decide⟩
    (prefixPartial 13 287950) = some ⟨13, 2, 0, 487090, 287950, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_287950_487090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287950 ⟨487090, by decide⟩ :=
  accepted_of_selected 13 287950 ⟨487090, by decide⟩ ⟨13, 2, 0, 487090, 287950, 2313, 16384⟩
    (by decide) selected_cut_18997

theorem selected_cut_18998 : selected 8 ⟨487096, by decide⟩
    (prefixPartial 13 287951) = some ⟨13, 2, 0, 487096, 287951, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_287951_487096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287951 ⟨487096, by decide⟩ :=
  accepted_of_selected 13 287951 ⟨487096, by decide⟩ ⟨13, 2, 0, 487096, 287951, 1005, 16384⟩
    (by decide) selected_cut_18998

theorem unmarked_context_12_71987_487097 : frontier 9 ⟨487097, by decide⟩
    (prefixCache 12 71987) (prefixPartial 12 71987) = false := by
  decide +kernel

theorem node_context_12_71987_487097 : EJMOriginalGlobalDAGData.nodes 9 ⟨487097, by decide⟩ =
    .split (coordinate 12) (![⟨487009, by decide⟩,⟨487050, by decide⟩,⟨487090, by decide⟩,⟨487096, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71987_487097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71987 ⟨487097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71987
    ⟨487097, by decide⟩ (by decide) (![⟨487009, by decide⟩,⟨487050, by decide⟩,⟨487090, by decide⟩,⟨487096, by decide⟩]) unmarked_context_12_71987_487097 node_context_12_71987_487097
  intro a
  fin_cases a
  · exact context_13_287948_487009
  · exact context_13_287949_487050
  · exact context_13_287950_487090
  · exact context_13_287951_487096

theorem unmarked_context_11_17996_487098 : frontier 10 ⟨487098, by decide⟩
    (prefixCache 11 17996) (prefixPartial 11 17996) = false := by
  decide +kernel

theorem node_context_11_17996_487098 : EJMOriginalGlobalDAGData.nodes 10 ⟨487098, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨486864, by decide⟩,⟨486988, by decide⟩,⟨487097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17996_487098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17996 ⟨487098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17996
    ⟨487098, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨486864, by decide⟩,⟨486988, by decide⟩,⟨487097, by decide⟩]) unmarked_context_11_17996_487098 node_context_11_17996_487098
  intro a
  fin_cases a
  · exact context_12_71984_445562
  · exact context_12_71985_486864
  · exact context_12_71986_486988
  · exact context_12_71987_487097

theorem selected_cut_18999 : selected 8 ⟨487115, by decide⟩
    (prefixPartial 13 287952) = some ⟨13, 2, 0, 487115, 287952, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_287952_487115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287952 ⟨487115, by decide⟩ :=
  accepted_of_selected 13 287952 ⟨487115, by decide⟩ ⟨13, 2, 0, 487115, 287952, 1129, 16384⟩
    (by decide) selected_cut_18999

theorem selected_cut_19000 : selected 8 ⟨487165, by decide⟩
    (prefixPartial 13 287953) = some ⟨13, 2, 0, 487165, 287953, 3533, 16384⟩ := by
  decide +kernel

theorem context_13_287953_487165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287953 ⟨487165, by decide⟩ :=
  accepted_of_selected 13 287953 ⟨487165, by decide⟩ ⟨13, 2, 0, 487165, 287953, 3533, 16384⟩
    (by decide) selected_cut_19000

theorem selected_cut_19001 : selected 8 ⟨487208, by decide⟩
    (prefixPartial 13 287954) = some ⟨13, 2, 0, 487208, 287954, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_287954_487208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287954 ⟨487208, by decide⟩ :=
  accepted_of_selected 13 287954 ⟨487208, by decide⟩ ⟨13, 2, 0, 487208, 287954, 2553, 16384⟩
    (by decide) selected_cut_19001

theorem selected_cut_19002 : selected 8 ⟨487228, by decide⟩
    (prefixPartial 13 287955) = some ⟨13, 2, 0, 487228, 287955, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_287955_487228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287955 ⟨487228, by decide⟩ :=
  accepted_of_selected 13 287955 ⟨487228, by decide⟩ ⟨13, 2, 0, 487228, 287955, 1265, 16384⟩
    (by decide) selected_cut_19002

theorem unmarked_context_12_71988_487229 : frontier 9 ⟨487229, by decide⟩
    (prefixCache 12 71988) (prefixPartial 12 71988) = false := by
  decide +kernel

theorem node_context_12_71988_487229 : EJMOriginalGlobalDAGData.nodes 9 ⟨487229, by decide⟩ =
    .split (coordinate 12) (![⟨487115, by decide⟩,⟨487165, by decide⟩,⟨487208, by decide⟩,⟨487228, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71988_487229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71988 ⟨487229, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71988
    ⟨487229, by decide⟩ (by decide) (![⟨487115, by decide⟩,⟨487165, by decide⟩,⟨487208, by decide⟩,⟨487228, by decide⟩]) unmarked_context_12_71988_487229 node_context_12_71988_487229
  intro a
  fin_cases a
  · exact context_13_287952_487115
  · exact context_13_287953_487165
  · exact context_13_287954_487208
  · exact context_13_287955_487228

theorem selected_cut_19003 : selected 8 ⟨487249, by decide⟩
    (prefixPartial 13 287956) = some ⟨13, 2, 0, 487249, 287956, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_287956_487249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287956 ⟨487249, by decide⟩ :=
  accepted_of_selected 13 287956 ⟨487249, by decide⟩ ⟨13, 2, 0, 487249, 287956, 1121, 16384⟩
    (by decide) selected_cut_19003

theorem selected_cut_19004 : selected 7 ⟨487261, by decide⟩
    (prefixPartial 14 1151828) = some ⟨14, 2, 0, 487261, 1151828, 889, 4096⟩ := by
  decide +kernel

theorem context_14_1151828_487261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151828 ⟨487261, by decide⟩ :=
  accepted_of_selected 14 1151828 ⟨487261, by decide⟩ ⟨14, 2, 0, 487261, 1151828, 889, 4096⟩
    (by decide) selected_cut_19004

theorem selected_cut_19005 : selected 7 ⟨487288, by decide⟩
    (prefixPartial 14 1151829) = some ⟨14, 2, 0, 487288, 1151829, 1437, 4096⟩ := by
  decide +kernel

theorem context_14_1151829_487288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151829 ⟨487288, by decide⟩ :=
  accepted_of_selected 14 1151829 ⟨487288, by decide⟩ ⟨14, 2, 0, 487288, 1151829, 1437, 4096⟩
    (by decide) selected_cut_19005

theorem selected_cut_19006 : selected 7 ⟨487306, by decide⟩
    (prefixPartial 14 1151830) = some ⟨14, 2, 0, 487306, 1151830, 1049, 4096⟩ := by
  decide +kernel

theorem context_14_1151830_487306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151830 ⟨487306, by decide⟩ :=
  accepted_of_selected 14 1151830 ⟨487306, by decide⟩ ⟨14, 2, 0, 487306, 1151830, 1049, 4096⟩
    (by decide) selected_cut_19006

theorem selected_cut_19007 : selected 7 ⟨487326, by decide⟩
    (prefixPartial 14 1151831) = some ⟨14, 2, 0, 487326, 1151831, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_1151831_487326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1151831 ⟨487326, by decide⟩ :=
  accepted_of_selected 14 1151831 ⟨487326, by decide⟩ ⟨14, 2, 0, 487326, 1151831, 1097, 4096⟩
    (by decide) selected_cut_19007

theorem unmarked_context_13_287957_487327 : frontier 8 ⟨487327, by decide⟩
    (prefixCache 13 287957) (prefixPartial 13 287957) = false := by
  decide +kernel

theorem node_context_13_287957_487327 : EJMOriginalGlobalDAGData.nodes 8 ⟨487327, by decide⟩ =
    .split (coordinate 13) (![⟨487261, by decide⟩,⟨487288, by decide⟩,⟨487306, by decide⟩,⟨487326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_287957_487327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287957 ⟨487327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 287957
    ⟨487327, by decide⟩ (by decide) (![⟨487261, by decide⟩,⟨487288, by decide⟩,⟨487306, by decide⟩,⟨487326, by decide⟩]) unmarked_context_13_287957_487327 node_context_13_287957_487327
  intro a
  fin_cases a
  · exact context_14_1151828_487261
  · exact context_14_1151829_487288
  · exact context_14_1151830_487306
  · exact context_14_1151831_487326

theorem selected_cut_19008 : selected 8 ⟨487381, by decide⟩
    (prefixPartial 13 287958) = some ⟨13, 2, 0, 487381, 287958, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_287958_487381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287958 ⟨487381, by decide⟩ :=
  accepted_of_selected 13 287958 ⟨487381, by decide⟩ ⟨13, 2, 0, 487381, 287958, 2785, 16384⟩
    (by decide) selected_cut_19008

theorem selected_cut_19009 : selected 8 ⟨487414, by decide⟩
    (prefixPartial 13 287959) = some ⟨13, 2, 0, 487414, 287959, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_287959_487414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287959 ⟨487414, by decide⟩ :=
  accepted_of_selected 13 287959 ⟨487414, by decide⟩ ⟨13, 2, 0, 487414, 287959, 1449, 16384⟩
    (by decide) selected_cut_19009

theorem unmarked_context_12_71989_487415 : frontier 9 ⟨487415, by decide⟩
    (prefixCache 12 71989) (prefixPartial 12 71989) = false := by
  decide +kernel

theorem node_context_12_71989_487415 : EJMOriginalGlobalDAGData.nodes 9 ⟨487415, by decide⟩ =
    .split (coordinate 12) (![⟨487249, by decide⟩,⟨487327, by decide⟩,⟨487381, by decide⟩,⟨487414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71989_487415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71989 ⟨487415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71989
    ⟨487415, by decide⟩ (by decide) (![⟨487249, by decide⟩,⟨487327, by decide⟩,⟨487381, by decide⟩,⟨487414, by decide⟩]) unmarked_context_12_71989_487415 node_context_12_71989_487415
  intro a
  fin_cases a
  · exact context_13_287956_487249
  · exact context_13_287957_487327
  · exact context_13_287958_487381
  · exact context_13_287959_487414

theorem selected_cut_19010 : selected 8 ⟨487426, by decide⟩
    (prefixPartial 13 287960) = some ⟨13, 2, 0, 487426, 287960, 801, 16384⟩ := by
  decide +kernel

theorem context_13_287960_487426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 287960 ⟨487426, by decide⟩ :=
  accepted_of_selected 13 287960 ⟨487426, by decide⟩ ⟨13, 2, 0, 487426, 287960, 801, 16384⟩
    (by decide) selected_cut_19010

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
