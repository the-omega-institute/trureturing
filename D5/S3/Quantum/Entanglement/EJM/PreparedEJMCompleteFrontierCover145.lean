/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover144
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_26948_362989 : frontier 9 ⟨362989, by decide⟩
    (prefixCache 12 26948) (prefixPartial 12 26948) = false := by
  decide +kernel

theorem node_context_12_26948_362989 : EJMOriginalGlobalDAGData.nodes 9 ⟨362989, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨362966, by decide⟩,⟨362984, by decide⟩,⟨362988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26948_362989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26948 ⟨362989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26948
    ⟨362989, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨362966, by decide⟩,⟨362984, by decide⟩,⟨362988, by decide⟩]) unmarked_context_12_26948_362989 node_context_12_26948_362989
  intro a
  fin_cases a
  · exact context_13_107792_3444
  · exact context_13_107793_362966
  · exact context_13_107794_362984
  · exact context_13_107795_362988

theorem selected_cut_13923 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 26949) = some ⟨12, 1, 0, 126884, 26949, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26949_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26949 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 26949 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 26949, 1, 65536⟩
    (by decide) selected_cut_13923

theorem selected_cut_13924 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107800) = some ⟨13, 1, 0, 3444, 107800, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107800_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107800 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107800 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107800, 1, 16384⟩
    (by decide) selected_cut_13924

theorem selected_cut_13925 : selected 8 ⟨363011, by decide⟩
    (prefixPartial 13 107801) = some ⟨13, 2, 0, 363011, 107801, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_107801_363011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107801 ⟨363011, by decide⟩ :=
  accepted_of_selected 13 107801 ⟨363011, by decide⟩ ⟨13, 2, 0, 363011, 107801, 2093, 16384⟩
    (by decide) selected_cut_13925

theorem selected_cut_13926 : selected 8 ⟨363031, by decide⟩
    (prefixPartial 13 107802) = some ⟨13, 2, 0, 363031, 107802, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_107802_363031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107802 ⟨363031, by decide⟩ :=
  accepted_of_selected 13 107802 ⟨363031, by decide⟩ ⟨13, 2, 0, 363031, 107802, 1877, 16384⟩
    (by decide) selected_cut_13926

theorem selected_cut_13927 : selected 8 ⟨363040, by decide⟩
    (prefixPartial 13 107803) = some ⟨13, 2, 0, 363040, 107803, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_107803_363040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107803 ⟨363040, by decide⟩ :=
  accepted_of_selected 13 107803 ⟨363040, by decide⟩ ⟨13, 2, 0, 363040, 107803, 1037, 16384⟩
    (by decide) selected_cut_13927

theorem unmarked_context_12_26950_363041 : frontier 9 ⟨363041, by decide⟩
    (prefixCache 12 26950) (prefixPartial 12 26950) = false := by
  decide +kernel

theorem node_context_12_26950_363041 : EJMOriginalGlobalDAGData.nodes 9 ⟨363041, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363011, by decide⟩,⟨363031, by decide⟩,⟨363040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26950_363041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26950 ⟨363041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26950
    ⟨363041, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363011, by decide⟩,⟨363031, by decide⟩,⟨363040, by decide⟩]) unmarked_context_12_26950_363041 node_context_12_26950_363041
  intro a
  fin_cases a
  · exact context_13_107800_3444
  · exact context_13_107801_363011
  · exact context_13_107802_363031
  · exact context_13_107803_363040

theorem selected_cut_13928 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107804) = some ⟨13, 1, 0, 3444, 107804, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107804_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107804 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107804 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107804, 1, 16384⟩
    (by decide) selected_cut_13928

theorem selected_cut_13929 : selected 8 ⟨363062, by decide⟩
    (prefixPartial 13 107805) = some ⟨13, 2, 0, 363062, 107805, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_107805_363062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107805 ⟨363062, by decide⟩ :=
  accepted_of_selected 13 107805 ⟨363062, by decide⟩ ⟨13, 2, 0, 363062, 107805, 2217, 16384⟩
    (by decide) selected_cut_13929

theorem selected_cut_13930 : selected 8 ⟨363082, by decide⟩
    (prefixPartial 13 107806) = some ⟨13, 2, 0, 363082, 107806, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_107806_363082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107806 ⟨363082, by decide⟩ :=
  accepted_of_selected 13 107806 ⟨363082, by decide⟩ ⟨13, 2, 0, 363082, 107806, 2005, 16384⟩
    (by decide) selected_cut_13930

theorem selected_cut_13931 : selected 8 ⟨363095, by decide⟩
    (prefixPartial 13 107807) = some ⟨13, 2, 0, 363095, 107807, 993, 16384⟩ := by
  decide +kernel

theorem context_13_107807_363095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107807 ⟨363095, by decide⟩ :=
  accepted_of_selected 13 107807 ⟨363095, by decide⟩ ⟨13, 2, 0, 363095, 107807, 993, 16384⟩
    (by decide) selected_cut_13931

theorem unmarked_context_12_26951_363096 : frontier 9 ⟨363096, by decide⟩
    (prefixCache 12 26951) (prefixPartial 12 26951) = false := by
  decide +kernel

theorem node_context_12_26951_363096 : EJMOriginalGlobalDAGData.nodes 9 ⟨363096, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363062, by decide⟩,⟨363082, by decide⟩,⟨363095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26951_363096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26951 ⟨363096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26951
    ⟨363096, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363062, by decide⟩,⟨363082, by decide⟩,⟨363095, by decide⟩]) unmarked_context_12_26951_363096 node_context_12_26951_363096
  intro a
  fin_cases a
  · exact context_13_107804_3444
  · exact context_13_107805_363062
  · exact context_13_107806_363082
  · exact context_13_107807_363095

theorem unmarked_context_11_6737_363097 : frontier 10 ⟨363097, by decide⟩
    (prefixCache 11 6737) (prefixPartial 11 6737) = false := by
  decide +kernel

theorem node_context_11_6737_363097 : EJMOriginalGlobalDAGData.nodes 10 ⟨363097, by decide⟩ =
    .split (coordinate 11) (![⟨362989, by decide⟩,⟨126884, by decide⟩,⟨363041, by decide⟩,⟨363096, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6737_363097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6737 ⟨363097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6737
    ⟨363097, by decide⟩ (by decide) (![⟨362989, by decide⟩,⟨126884, by decide⟩,⟨363041, by decide⟩,⟨363096, by decide⟩]) unmarked_context_11_6737_363097 node_context_11_6737_363097
  intro a
  fin_cases a
  · exact context_12_26948_362989
  · exact context_12_26949_126884
  · exact context_12_26950_363041
  · exact context_12_26951_363096

theorem selected_cut_13932 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107808) = some ⟨13, 1, 0, 3444, 107808, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107808_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107808 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107808 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107808, 1, 16384⟩
    (by decide) selected_cut_13932

theorem selected_cut_13933 : selected 8 ⟨363123, by decide⟩
    (prefixPartial 13 107809) = some ⟨13, 2, 0, 363123, 107809, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_107809_363123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107809 ⟨363123, by decide⟩ :=
  accepted_of_selected 13 107809 ⟨363123, by decide⟩ ⟨13, 2, 0, 363123, 107809, 2269, 16384⟩
    (by decide) selected_cut_13933

theorem selected_cut_13934 : selected 8 ⟨363144, by decide⟩
    (prefixPartial 13 107810) = some ⟨13, 2, 0, 363144, 107810, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_107810_363144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107810 ⟨363144, by decide⟩ :=
  accepted_of_selected 13 107810 ⟨363144, by decide⟩ ⟨13, 2, 0, 363144, 107810, 1929, 16384⟩
    (by decide) selected_cut_13934

theorem selected_cut_13935 : selected 8 ⟨363151, by decide⟩
    (prefixPartial 13 107811) = some ⟨13, 2, 0, 363151, 107811, 985, 16384⟩ := by
  decide +kernel

theorem context_13_107811_363151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107811 ⟨363151, by decide⟩ :=
  accepted_of_selected 13 107811 ⟨363151, by decide⟩ ⟨13, 2, 0, 363151, 107811, 985, 16384⟩
    (by decide) selected_cut_13935

theorem unmarked_context_12_26952_363152 : frontier 9 ⟨363152, by decide⟩
    (prefixCache 12 26952) (prefixPartial 12 26952) = false := by
  decide +kernel

theorem node_context_12_26952_363152 : EJMOriginalGlobalDAGData.nodes 9 ⟨363152, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363123, by decide⟩,⟨363144, by decide⟩,⟨363151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26952_363152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26952 ⟨363152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26952
    ⟨363152, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363123, by decide⟩,⟨363144, by decide⟩,⟨363151, by decide⟩]) unmarked_context_12_26952_363152 node_context_12_26952_363152
  intro a
  fin_cases a
  · exact context_13_107808_3444
  · exact context_13_107809_363123
  · exact context_13_107810_363144
  · exact context_13_107811_363151

theorem selected_cut_13936 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107812) = some ⟨13, 1, 0, 3444, 107812, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107812_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107812 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107812 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107812, 1, 16384⟩
    (by decide) selected_cut_13936

theorem selected_cut_13937 : selected 8 ⟨363177, by decide⟩
    (prefixPartial 13 107813) = some ⟨13, 2, 0, 363177, 107813, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_107813_363177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107813 ⟨363177, by decide⟩ :=
  accepted_of_selected 13 107813 ⟨363177, by decide⟩ ⟨13, 2, 0, 363177, 107813, 2445, 16384⟩
    (by decide) selected_cut_13937

theorem selected_cut_13938 : selected 8 ⟨363194, by decide⟩
    (prefixPartial 13 107814) = some ⟨13, 2, 0, 363194, 107814, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_107814_363194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107814 ⟨363194, by decide⟩ :=
  accepted_of_selected 13 107814 ⟨363194, by decide⟩ ⟨13, 2, 0, 363194, 107814, 2321, 16384⟩
    (by decide) selected_cut_13938

theorem selected_cut_13939 : selected 8 ⟨363205, by decide⟩
    (prefixPartial 13 107815) = some ⟨13, 2, 0, 363205, 107815, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_107815_363205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107815 ⟨363205, by decide⟩ :=
  accepted_of_selected 13 107815 ⟨363205, by decide⟩ ⟨13, 2, 0, 363205, 107815, 1277, 16384⟩
    (by decide) selected_cut_13939

theorem unmarked_context_12_26953_363206 : frontier 9 ⟨363206, by decide⟩
    (prefixCache 12 26953) (prefixPartial 12 26953) = false := by
  decide +kernel

theorem node_context_12_26953_363206 : EJMOriginalGlobalDAGData.nodes 9 ⟨363206, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363177, by decide⟩,⟨363194, by decide⟩,⟨363205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26953_363206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26953 ⟨363206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26953
    ⟨363206, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363177, by decide⟩,⟨363194, by decide⟩,⟨363205, by decide⟩]) unmarked_context_12_26953_363206 node_context_12_26953_363206
  intro a
  fin_cases a
  · exact context_13_107812_3444
  · exact context_13_107813_363177
  · exact context_13_107814_363194
  · exact context_13_107815_363205

theorem selected_cut_13940 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107816) = some ⟨13, 1, 0, 3444, 107816, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107816_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107816 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107816 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107816, 1, 16384⟩
    (by decide) selected_cut_13940

theorem selected_cut_13941 : selected 8 ⟨363228, by decide⟩
    (prefixPartial 13 107817) = some ⟨13, 2, 0, 363228, 107817, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_107817_363228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107817 ⟨363228, by decide⟩ :=
  accepted_of_selected 13 107817 ⟨363228, by decide⟩ ⟨13, 2, 0, 363228, 107817, 2177, 16384⟩
    (by decide) selected_cut_13941

theorem selected_cut_13942 : selected 8 ⟨363248, by decide⟩
    (prefixPartial 13 107818) = some ⟨13, 2, 0, 363248, 107818, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_107818_363248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107818 ⟨363248, by decide⟩ :=
  accepted_of_selected 13 107818 ⟨363248, by decide⟩ ⟨13, 2, 0, 363248, 107818, 2129, 16384⟩
    (by decide) selected_cut_13942

theorem selected_cut_13943 : selected 8 ⟨363257, by decide⟩
    (prefixPartial 13 107819) = some ⟨13, 2, 0, 363257, 107819, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_107819_363257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107819 ⟨363257, by decide⟩ :=
  accepted_of_selected 13 107819 ⟨363257, by decide⟩ ⟨13, 2, 0, 363257, 107819, 1085, 16384⟩
    (by decide) selected_cut_13943

theorem unmarked_context_12_26954_363258 : frontier 9 ⟨363258, by decide⟩
    (prefixCache 12 26954) (prefixPartial 12 26954) = false := by
  decide +kernel

theorem node_context_12_26954_363258 : EJMOriginalGlobalDAGData.nodes 9 ⟨363258, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363228, by decide⟩,⟨363248, by decide⟩,⟨363257, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26954_363258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26954 ⟨363258, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26954
    ⟨363258, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363228, by decide⟩,⟨363248, by decide⟩,⟨363257, by decide⟩]) unmarked_context_12_26954_363258 node_context_12_26954_363258
  intro a
  fin_cases a
  · exact context_13_107816_3444
  · exact context_13_107817_363228
  · exact context_13_107818_363248
  · exact context_13_107819_363257

theorem selected_cut_13944 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107820) = some ⟨13, 1, 0, 3444, 107820, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107820_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107820 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107820 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107820, 1, 16384⟩
    (by decide) selected_cut_13944

theorem selected_cut_13945 : selected 8 ⟨363276, by decide⟩
    (prefixPartial 13 107821) = some ⟨13, 2, 0, 363276, 107821, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_107821_363276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107821 ⟨363276, by decide⟩ :=
  accepted_of_selected 13 107821 ⟨363276, by decide⟩ ⟨13, 2, 0, 363276, 107821, 2321, 16384⟩
    (by decide) selected_cut_13945

theorem selected_cut_13946 : selected 8 ⟨363299, by decide⟩
    (prefixPartial 13 107822) = some ⟨13, 2, 0, 363299, 107822, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_107822_363299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107822 ⟨363299, by decide⟩ :=
  accepted_of_selected 13 107822 ⟨363299, by decide⟩ ⟨13, 2, 0, 363299, 107822, 2185, 16384⟩
    (by decide) selected_cut_13946

theorem selected_cut_13947 : selected 8 ⟨363307, by decide⟩
    (prefixPartial 13 107823) = some ⟨13, 2, 0, 363307, 107823, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_107823_363307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107823 ⟨363307, by decide⟩ :=
  accepted_of_selected 13 107823 ⟨363307, by decide⟩ ⟨13, 2, 0, 363307, 107823, 1105, 16384⟩
    (by decide) selected_cut_13947

theorem unmarked_context_12_26955_363308 : frontier 9 ⟨363308, by decide⟩
    (prefixCache 12 26955) (prefixPartial 12 26955) = false := by
  decide +kernel

theorem node_context_12_26955_363308 : EJMOriginalGlobalDAGData.nodes 9 ⟨363308, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363276, by decide⟩,⟨363299, by decide⟩,⟨363307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26955_363308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26955 ⟨363308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26955
    ⟨363308, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363276, by decide⟩,⟨363299, by decide⟩,⟨363307, by decide⟩]) unmarked_context_12_26955_363308 node_context_12_26955_363308
  intro a
  fin_cases a
  · exact context_13_107820_3444
  · exact context_13_107821_363276
  · exact context_13_107822_363299
  · exact context_13_107823_363307

theorem unmarked_context_11_6738_363309 : frontier 10 ⟨363309, by decide⟩
    (prefixCache 11 6738) (prefixPartial 11 6738) = false := by
  decide +kernel

theorem node_context_11_6738_363309 : EJMOriginalGlobalDAGData.nodes 10 ⟨363309, by decide⟩ =
    .split (coordinate 11) (![⟨363152, by decide⟩,⟨363206, by decide⟩,⟨363258, by decide⟩,⟨363308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6738_363309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6738 ⟨363309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6738
    ⟨363309, by decide⟩ (by decide) (![⟨363152, by decide⟩,⟨363206, by decide⟩,⟨363258, by decide⟩,⟨363308, by decide⟩]) unmarked_context_11_6738_363309 node_context_11_6738_363309
  intro a
  fin_cases a
  · exact context_12_26952_363152
  · exact context_12_26953_363206
  · exact context_12_26954_363258
  · exact context_12_26955_363308

theorem selected_cut_13948 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107824) = some ⟨13, 1, 0, 3444, 107824, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107824_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107824 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107824 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107824, 1, 16384⟩
    (by decide) selected_cut_13948

theorem selected_cut_13949 : selected 8 ⟨363335, by decide⟩
    (prefixPartial 13 107825) = some ⟨13, 2, 0, 363335, 107825, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_107825_363335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107825 ⟨363335, by decide⟩ :=
  accepted_of_selected 13 107825 ⟨363335, by decide⟩ ⟨13, 2, 0, 363335, 107825, 2037, 16384⟩
    (by decide) selected_cut_13949

theorem selected_cut_13950 : selected 8 ⟨363352, by decide⟩
    (prefixPartial 13 107826) = some ⟨13, 2, 0, 363352, 107826, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_107826_363352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107826 ⟨363352, by decide⟩ :=
  accepted_of_selected 13 107826 ⟨363352, by decide⟩ ⟨13, 2, 0, 363352, 107826, 1929, 16384⟩
    (by decide) selected_cut_13950

theorem selected_cut_13951 : selected 8 ⟨363361, by decide⟩
    (prefixPartial 13 107827) = some ⟨13, 2, 0, 363361, 107827, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_107827_363361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107827 ⟨363361, by decide⟩ :=
  accepted_of_selected 13 107827 ⟨363361, by decide⟩ ⟨13, 2, 0, 363361, 107827, 1101, 16384⟩
    (by decide) selected_cut_13951

theorem unmarked_context_12_26956_363362 : frontier 9 ⟨363362, by decide⟩
    (prefixCache 12 26956) (prefixPartial 12 26956) = false := by
  decide +kernel

theorem node_context_12_26956_363362 : EJMOriginalGlobalDAGData.nodes 9 ⟨363362, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363335, by decide⟩,⟨363352, by decide⟩,⟨363361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26956_363362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26956 ⟨363362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26956
    ⟨363362, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363335, by decide⟩,⟨363352, by decide⟩,⟨363361, by decide⟩]) unmarked_context_12_26956_363362 node_context_12_26956_363362
  intro a
  fin_cases a
  · exact context_13_107824_3444
  · exact context_13_107825_363335
  · exact context_13_107826_363352
  · exact context_13_107827_363361

theorem selected_cut_13952 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107828) = some ⟨13, 1, 0, 3444, 107828, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107828_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107828 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107828 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107828, 1, 16384⟩
    (by decide) selected_cut_13952

theorem selected_cut_13953 : selected 8 ⟨363390, by decide⟩
    (prefixPartial 13 107829) = some ⟨13, 2, 0, 363390, 107829, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_107829_363390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107829 ⟨363390, by decide⟩ :=
  accepted_of_selected 13 107829 ⟨363390, by decide⟩ ⟨13, 2, 0, 363390, 107829, 2369, 16384⟩
    (by decide) selected_cut_13953

theorem selected_cut_13954 : selected 8 ⟨363410, by decide⟩
    (prefixPartial 13 107830) = some ⟨13, 2, 0, 363410, 107830, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_107830_363410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107830 ⟨363410, by decide⟩ :=
  accepted_of_selected 13 107830 ⟨363410, by decide⟩ ⟨13, 2, 0, 363410, 107830, 2381, 16384⟩
    (by decide) selected_cut_13954

theorem selected_cut_13955 : selected 8 ⟨363416, by decide⟩
    (prefixPartial 13 107831) = some ⟨13, 2, 0, 363416, 107831, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_107831_363416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107831 ⟨363416, by decide⟩ :=
  accepted_of_selected 13 107831 ⟨363416, by decide⟩ ⟨13, 2, 0, 363416, 107831, 1261, 16384⟩
    (by decide) selected_cut_13955

theorem unmarked_context_12_26957_363417 : frontier 9 ⟨363417, by decide⟩
    (prefixCache 12 26957) (prefixPartial 12 26957) = false := by
  decide +kernel

theorem node_context_12_26957_363417 : EJMOriginalGlobalDAGData.nodes 9 ⟨363417, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363390, by decide⟩,⟨363410, by decide⟩,⟨363416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26957_363417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26957 ⟨363417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26957
    ⟨363417, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363390, by decide⟩,⟨363410, by decide⟩,⟨363416, by decide⟩]) unmarked_context_12_26957_363417 node_context_12_26957_363417
  intro a
  fin_cases a
  · exact context_13_107828_3444
  · exact context_13_107829_363390
  · exact context_13_107830_363410
  · exact context_13_107831_363416

theorem selected_cut_13956 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107832) = some ⟨13, 1, 0, 3444, 107832, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107832_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107832 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107832 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107832, 1, 16384⟩
    (by decide) selected_cut_13956

theorem selected_cut_13957 : selected 8 ⟨363441, by decide⟩
    (prefixPartial 13 107833) = some ⟨13, 2, 0, 363441, 107833, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_107833_363441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107833 ⟨363441, by decide⟩ :=
  accepted_of_selected 13 107833 ⟨363441, by decide⟩ ⟨13, 2, 0, 363441, 107833, 1989, 16384⟩
    (by decide) selected_cut_13957

theorem selected_cut_13958 : selected 8 ⟨363463, by decide⟩
    (prefixPartial 13 107834) = some ⟨13, 2, 0, 363463, 107834, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_107834_363463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107834 ⟨363463, by decide⟩ :=
  accepted_of_selected 13 107834 ⟨363463, by decide⟩ ⟨13, 2, 0, 363463, 107834, 2045, 16384⟩
    (by decide) selected_cut_13958

theorem selected_cut_13959 : selected 8 ⟨363469, by decide⟩
    (prefixPartial 13 107835) = some ⟨13, 2, 0, 363469, 107835, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_107835_363469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107835 ⟨363469, by decide⟩ :=
  accepted_of_selected 13 107835 ⟨363469, by decide⟩ ⟨13, 2, 0, 363469, 107835, 1137, 16384⟩
    (by decide) selected_cut_13959

theorem unmarked_context_12_26958_363470 : frontier 9 ⟨363470, by decide⟩
    (prefixCache 12 26958) (prefixPartial 12 26958) = false := by
  decide +kernel

theorem node_context_12_26958_363470 : EJMOriginalGlobalDAGData.nodes 9 ⟨363470, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363441, by decide⟩,⟨363463, by decide⟩,⟨363469, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26958_363470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26958 ⟨363470, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26958
    ⟨363470, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363441, by decide⟩,⟨363463, by decide⟩,⟨363469, by decide⟩]) unmarked_context_12_26958_363470 node_context_12_26958_363470
  intro a
  fin_cases a
  · exact context_13_107832_3444
  · exact context_13_107833_363441
  · exact context_13_107834_363463
  · exact context_13_107835_363469

theorem selected_cut_13960 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107836) = some ⟨13, 1, 0, 3444, 107836, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107836_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107836 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107836 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107836, 1, 16384⟩
    (by decide) selected_cut_13960

theorem selected_cut_13961 : selected 8 ⟨363487, by decide⟩
    (prefixPartial 13 107837) = some ⟨13, 2, 0, 363487, 107837, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_107837_363487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107837 ⟨363487, by decide⟩ :=
  accepted_of_selected 13 107837 ⟨363487, by decide⟩ ⟨13, 2, 0, 363487, 107837, 1969, 16384⟩
    (by decide) selected_cut_13961

theorem selected_cut_13962 : selected 8 ⟨363506, by decide⟩
    (prefixPartial 13 107838) = some ⟨13, 2, 0, 363506, 107838, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_107838_363506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107838 ⟨363506, by decide⟩ :=
  accepted_of_selected 13 107838 ⟨363506, by decide⟩ ⟨13, 2, 0, 363506, 107838, 2129, 16384⟩
    (by decide) selected_cut_13962

theorem selected_cut_13963 : selected 8 ⟨363515, by decide⟩
    (prefixPartial 13 107839) = some ⟨13, 2, 0, 363515, 107839, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_107839_363515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107839 ⟨363515, by decide⟩ :=
  accepted_of_selected 13 107839 ⟨363515, by decide⟩ ⟨13, 2, 0, 363515, 107839, 1149, 16384⟩
    (by decide) selected_cut_13963

theorem unmarked_context_12_26959_363516 : frontier 9 ⟨363516, by decide⟩
    (prefixCache 12 26959) (prefixPartial 12 26959) = false := by
  decide +kernel

theorem node_context_12_26959_363516 : EJMOriginalGlobalDAGData.nodes 9 ⟨363516, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363487, by decide⟩,⟨363506, by decide⟩,⟨363515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26959_363516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26959 ⟨363516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26959
    ⟨363516, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363487, by decide⟩,⟨363506, by decide⟩,⟨363515, by decide⟩]) unmarked_context_12_26959_363516 node_context_12_26959_363516
  intro a
  fin_cases a
  · exact context_13_107836_3444
  · exact context_13_107837_363487
  · exact context_13_107838_363506
  · exact context_13_107839_363515

theorem unmarked_context_11_6739_363517 : frontier 10 ⟨363517, by decide⟩
    (prefixCache 11 6739) (prefixPartial 11 6739) = false := by
  decide +kernel

theorem node_context_11_6739_363517 : EJMOriginalGlobalDAGData.nodes 10 ⟨363517, by decide⟩ =
    .split (coordinate 11) (![⟨363362, by decide⟩,⟨363417, by decide⟩,⟨363470, by decide⟩,⟨363516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6739_363517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6739 ⟨363517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6739
    ⟨363517, by decide⟩ (by decide) (![⟨363362, by decide⟩,⟨363417, by decide⟩,⟨363470, by decide⟩,⟨363516, by decide⟩]) unmarked_context_11_6739_363517 node_context_11_6739_363517
  intro a
  fin_cases a
  · exact context_12_26956_363362
  · exact context_12_26957_363417
  · exact context_12_26958_363470
  · exact context_12_26959_363516

theorem unmarked_context_10_1684_363518 : frontier 11 ⟨363518, by decide⟩
    (prefixCache 10 1684) (prefixPartial 10 1684) = false := by
  decide +kernel

theorem node_context_10_1684_363518 : EJMOriginalGlobalDAGData.nodes 11 ⟨363518, by decide⟩ =
    .split (coordinate 10) (![⟨362941, by decide⟩,⟨363097, by decide⟩,⟨363309, by decide⟩,⟨363517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1684_363518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1684 ⟨363518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1684
    ⟨363518, by decide⟩ (by decide) (![⟨362941, by decide⟩,⟨363097, by decide⟩,⟨363309, by decide⟩,⟨363517, by decide⟩]) unmarked_context_10_1684_363518 node_context_10_1684_363518
  intro a
  fin_cases a
  · exact context_11_6736_362941
  · exact context_11_6737_363097
  · exact context_11_6738_363309
  · exact context_11_6739_363517

theorem selected_cut_13964 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107840) = some ⟨13, 1, 0, 3444, 107840, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107840_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107840 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107840 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107840, 1, 16384⟩
    (by decide) selected_cut_13964

theorem selected_cut_13965 : selected 8 ⟨363537, by decide⟩
    (prefixPartial 13 107841) = some ⟨13, 2, 0, 363537, 107841, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_107841_363537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107841 ⟨363537, by decide⟩ :=
  accepted_of_selected 13 107841 ⟨363537, by decide⟩ ⟨13, 2, 0, 363537, 107841, 1729, 16384⟩
    (by decide) selected_cut_13965

theorem selected_cut_13966 : selected 8 ⟨363553, by decide⟩
    (prefixPartial 13 107842) = some ⟨13, 2, 0, 363553, 107842, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_107842_363553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107842 ⟨363553, by decide⟩ :=
  accepted_of_selected 13 107842 ⟨363553, by decide⟩ ⟨13, 2, 0, 363553, 107842, 1505, 16384⟩
    (by decide) selected_cut_13966

theorem selected_cut_13967 : selected 8 ⟨363561, by decide⟩
    (prefixPartial 13 107843) = some ⟨13, 2, 0, 363561, 107843, 893, 16384⟩ := by
  decide +kernel

theorem context_13_107843_363561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107843 ⟨363561, by decide⟩ :=
  accepted_of_selected 13 107843 ⟨363561, by decide⟩ ⟨13, 2, 0, 363561, 107843, 893, 16384⟩
    (by decide) selected_cut_13967

theorem unmarked_context_12_26960_363562 : frontier 9 ⟨363562, by decide⟩
    (prefixCache 12 26960) (prefixPartial 12 26960) = false := by
  decide +kernel

theorem node_context_12_26960_363562 : EJMOriginalGlobalDAGData.nodes 9 ⟨363562, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363537, by decide⟩,⟨363553, by decide⟩,⟨363561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26960_363562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26960 ⟨363562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26960
    ⟨363562, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363537, by decide⟩,⟨363553, by decide⟩,⟨363561, by decide⟩]) unmarked_context_12_26960_363562 node_context_12_26960_363562
  intro a
  fin_cases a
  · exact context_13_107840_3444
  · exact context_13_107841_363537
  · exact context_13_107842_363553
  · exact context_13_107843_363561

theorem selected_cut_13968 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 26961) = some ⟨12, 1, 0, 170504, 26961, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26961_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26961 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 26961 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 26961, 1, 65536⟩
    (by decide) selected_cut_13968

theorem selected_cut_13969 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107848) = some ⟨13, 1, 0, 3444, 107848, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107848_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107848 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107848 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107848, 1, 16384⟩
    (by decide) selected_cut_13969

theorem selected_cut_13970 : selected 8 ⟨363582, by decide⟩
    (prefixPartial 13 107849) = some ⟨13, 2, 0, 363582, 107849, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_107849_363582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107849 ⟨363582, by decide⟩ :=
  accepted_of_selected 13 107849 ⟨363582, by decide⟩ ⟨13, 2, 0, 363582, 107849, 1905, 16384⟩
    (by decide) selected_cut_13970

theorem selected_cut_13971 : selected 8 ⟨363603, by decide⟩
    (prefixPartial 13 107850) = some ⟨13, 2, 0, 363603, 107850, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_107850_363603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107850 ⟨363603, by decide⟩ :=
  accepted_of_selected 13 107850 ⟨363603, by decide⟩ ⟨13, 2, 0, 363603, 107850, 1961, 16384⟩
    (by decide) selected_cut_13971

theorem selected_cut_13972 : selected 8 ⟨363612, by decide⟩
    (prefixPartial 13 107851) = some ⟨13, 2, 0, 363612, 107851, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_107851_363612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107851 ⟨363612, by decide⟩ :=
  accepted_of_selected 13 107851 ⟨363612, by decide⟩ ⟨13, 2, 0, 363612, 107851, 1121, 16384⟩
    (by decide) selected_cut_13972

theorem unmarked_context_12_26962_363613 : frontier 9 ⟨363613, by decide⟩
    (prefixCache 12 26962) (prefixPartial 12 26962) = false := by
  decide +kernel

theorem node_context_12_26962_363613 : EJMOriginalGlobalDAGData.nodes 9 ⟨363613, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363582, by decide⟩,⟨363603, by decide⟩,⟨363612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26962_363613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26962 ⟨363613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26962
    ⟨363613, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363582, by decide⟩,⟨363603, by decide⟩,⟨363612, by decide⟩]) unmarked_context_12_26962_363613 node_context_12_26962_363613
  intro a
  fin_cases a
  · exact context_13_107848_3444
  · exact context_13_107849_363582
  · exact context_13_107850_363603
  · exact context_13_107851_363612

theorem selected_cut_13973 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107852) = some ⟨13, 1, 0, 3444, 107852, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107852_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107852 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107852 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107852, 1, 16384⟩
    (by decide) selected_cut_13973

theorem selected_cut_13974 : selected 8 ⟨363631, by decide⟩
    (prefixPartial 13 107853) = some ⟨13, 2, 0, 363631, 107853, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_107853_363631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107853 ⟨363631, by decide⟩ :=
  accepted_of_selected 13 107853 ⟨363631, by decide⟩ ⟨13, 2, 0, 363631, 107853, 1845, 16384⟩
    (by decide) selected_cut_13974

theorem selected_cut_13975 : selected 8 ⟨363651, by decide⟩
    (prefixPartial 13 107854) = some ⟨13, 2, 0, 363651, 107854, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_107854_363651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107854 ⟨363651, by decide⟩ :=
  accepted_of_selected 13 107854 ⟨363651, by decide⟩ ⟨13, 2, 0, 363651, 107854, 2013, 16384⟩
    (by decide) selected_cut_13975

theorem selected_cut_13976 : selected 8 ⟨363661, by decide⟩
    (prefixPartial 13 107855) = some ⟨13, 2, 0, 363661, 107855, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_107855_363661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107855 ⟨363661, by decide⟩ :=
  accepted_of_selected 13 107855 ⟨363661, by decide⟩ ⟨13, 2, 0, 363661, 107855, 1061, 16384⟩
    (by decide) selected_cut_13976

theorem unmarked_context_12_26963_363662 : frontier 9 ⟨363662, by decide⟩
    (prefixCache 12 26963) (prefixPartial 12 26963) = false := by
  decide +kernel

theorem node_context_12_26963_363662 : EJMOriginalGlobalDAGData.nodes 9 ⟨363662, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363631, by decide⟩,⟨363651, by decide⟩,⟨363661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26963_363662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26963 ⟨363662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26963
    ⟨363662, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363631, by decide⟩,⟨363651, by decide⟩,⟨363661, by decide⟩]) unmarked_context_12_26963_363662 node_context_12_26963_363662
  intro a
  fin_cases a
  · exact context_13_107852_3444
  · exact context_13_107853_363631
  · exact context_13_107854_363651
  · exact context_13_107855_363661

theorem unmarked_context_11_6740_363663 : frontier 10 ⟨363663, by decide⟩
    (prefixCache 11 6740) (prefixPartial 11 6740) = false := by
  decide +kernel

theorem node_context_11_6740_363663 : EJMOriginalGlobalDAGData.nodes 10 ⟨363663, by decide⟩ =
    .split (coordinate 11) (![⟨363562, by decide⟩,⟨170504, by decide⟩,⟨363613, by decide⟩,⟨363662, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6740_363663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6740 ⟨363663, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6740
    ⟨363663, by decide⟩ (by decide) (![⟨363562, by decide⟩,⟨170504, by decide⟩,⟨363613, by decide⟩,⟨363662, by decide⟩]) unmarked_context_11_6740_363663 node_context_11_6740_363663
  intro a
  fin_cases a
  · exact context_12_26960_363562
  · exact context_12_26961_170504
  · exact context_12_26962_363613
  · exact context_12_26963_363662

theorem selected_cut_13977 : selected 9 ⟨363706, by decide⟩
    (prefixPartial 12 26964) = some ⟨12, 2, 0, 363706, 26964, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_26964_363706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26964 ⟨363706, by decide⟩ :=
  accepted_of_selected 12 26964 ⟨363706, by decide⟩ ⟨12, 2, 0, 363706, 26964, 3409, 65536⟩
    (by decide) selected_cut_13977

theorem selected_cut_13978 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 26965) = some ⟨12, 1, 0, 170504, 26965, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26965_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26965 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 26965 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 26965, 1, 65536⟩
    (by decide) selected_cut_13978

theorem selected_cut_13979 : selected 9 ⟨363751, by decide⟩
    (prefixPartial 12 26966) = some ⟨12, 2, 0, 363751, 26966, 4085, 65536⟩ := by
  decide +kernel

theorem context_12_26966_363751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26966 ⟨363751, by decide⟩ :=
  accepted_of_selected 12 26966 ⟨363751, by decide⟩ ⟨12, 2, 0, 363751, 26966, 4085, 65536⟩
    (by decide) selected_cut_13979

theorem selected_cut_13980 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107868) = some ⟨13, 1, 0, 3444, 107868, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107868_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107868 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107868 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107868, 1, 16384⟩
    (by decide) selected_cut_13980

theorem selected_cut_13981 : selected 8 ⟨363768, by decide⟩
    (prefixPartial 13 107869) = some ⟨13, 2, 0, 363768, 107869, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_107869_363768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107869 ⟨363768, by decide⟩ :=
  accepted_of_selected 13 107869 ⟨363768, by decide⟩ ⟨13, 2, 0, 363768, 107869, 1589, 16384⟩
    (by decide) selected_cut_13981

theorem selected_cut_13982 : selected 8 ⟨363788, by decide⟩
    (prefixPartial 13 107870) = some ⟨13, 2, 0, 363788, 107870, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_107870_363788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107870 ⟨363788, by decide⟩ :=
  accepted_of_selected 13 107870 ⟨363788, by decide⟩ ⟨13, 2, 0, 363788, 107870, 1609, 16384⟩
    (by decide) selected_cut_13982

theorem selected_cut_13983 : selected 8 ⟨363797, by decide⟩
    (prefixPartial 13 107871) = some ⟨13, 2, 0, 363797, 107871, 961, 16384⟩ := by
  decide +kernel

theorem context_13_107871_363797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107871 ⟨363797, by decide⟩ :=
  accepted_of_selected 13 107871 ⟨363797, by decide⟩ ⟨13, 2, 0, 363797, 107871, 961, 16384⟩
    (by decide) selected_cut_13983

theorem unmarked_context_12_26967_363798 : frontier 9 ⟨363798, by decide⟩
    (prefixCache 12 26967) (prefixPartial 12 26967) = false := by
  decide +kernel

theorem node_context_12_26967_363798 : EJMOriginalGlobalDAGData.nodes 9 ⟨363798, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363768, by decide⟩,⟨363788, by decide⟩,⟨363797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26967_363798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26967 ⟨363798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26967
    ⟨363798, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363768, by decide⟩,⟨363788, by decide⟩,⟨363797, by decide⟩]) unmarked_context_12_26967_363798 node_context_12_26967_363798
  intro a
  fin_cases a
  · exact context_13_107868_3444
  · exact context_13_107869_363768
  · exact context_13_107870_363788
  · exact context_13_107871_363797

theorem unmarked_context_11_6741_363799 : frontier 10 ⟨363799, by decide⟩
    (prefixCache 11 6741) (prefixPartial 11 6741) = false := by
  decide +kernel

theorem node_context_11_6741_363799 : EJMOriginalGlobalDAGData.nodes 10 ⟨363799, by decide⟩ =
    .split (coordinate 11) (![⟨363706, by decide⟩,⟨170504, by decide⟩,⟨363751, by decide⟩,⟨363798, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6741_363799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6741 ⟨363799, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6741
    ⟨363799, by decide⟩ (by decide) (![⟨363706, by decide⟩,⟨170504, by decide⟩,⟨363751, by decide⟩,⟨363798, by decide⟩]) unmarked_context_11_6741_363799 node_context_11_6741_363799
  intro a
  fin_cases a
  · exact context_12_26964_363706
  · exact context_12_26965_170504
  · exact context_12_26966_363751
  · exact context_12_26967_363798

theorem selected_cut_13984 : selected 9 ⟨363839, by decide⟩
    (prefixPartial 12 26968) = some ⟨12, 2, 0, 363839, 26968, 3937, 65536⟩ := by
  decide +kernel

theorem context_12_26968_363839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26968 ⟨363839, by decide⟩ :=
  accepted_of_selected 12 26968 ⟨363839, by decide⟩ ⟨12, 2, 0, 363839, 26968, 3937, 65536⟩
    (by decide) selected_cut_13984

theorem selected_cut_13985 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 26969) = some ⟨12, 1, 0, 126371, 26969, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26969_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26969 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 26969 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 26969, 1, 65536⟩
    (by decide) selected_cut_13985

theorem selected_cut_13986 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107880) = some ⟨13, 1, 0, 3444, 107880, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107880_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107880 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107880 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107880, 1, 16384⟩
    (by decide) selected_cut_13986

theorem selected_cut_13987 : selected 8 ⟨363854, by decide⟩
    (prefixPartial 13 107881) = some ⟨13, 2, 0, 363854, 107881, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_107881_363854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107881 ⟨363854, by decide⟩ :=
  accepted_of_selected 13 107881 ⟨363854, by decide⟩ ⟨13, 2, 0, 363854, 107881, 1497, 16384⟩
    (by decide) selected_cut_13987

theorem selected_cut_13988 : selected 8 ⟨363878, by decide⟩
    (prefixPartial 13 107882) = some ⟨13, 2, 0, 363878, 107882, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_107882_363878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107882 ⟨363878, by decide⟩ :=
  accepted_of_selected 13 107882 ⟨363878, by decide⟩ ⟨13, 2, 0, 363878, 107882, 1857, 16384⟩
    (by decide) selected_cut_13988

theorem selected_cut_13989 : selected 8 ⟨363887, by decide⟩
    (prefixPartial 13 107883) = some ⟨13, 2, 0, 363887, 107883, 949, 16384⟩ := by
  decide +kernel

theorem context_13_107883_363887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107883 ⟨363887, by decide⟩ :=
  accepted_of_selected 13 107883 ⟨363887, by decide⟩ ⟨13, 2, 0, 363887, 107883, 949, 16384⟩
    (by decide) selected_cut_13989

theorem unmarked_context_12_26970_363888 : frontier 9 ⟨363888, by decide⟩
    (prefixCache 12 26970) (prefixPartial 12 26970) = false := by
  decide +kernel

theorem node_context_12_26970_363888 : EJMOriginalGlobalDAGData.nodes 9 ⟨363888, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363854, by decide⟩,⟨363878, by decide⟩,⟨363887, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26970_363888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26970 ⟨363888, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26970
    ⟨363888, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363854, by decide⟩,⟨363878, by decide⟩,⟨363887, by decide⟩]) unmarked_context_12_26970_363888 node_context_12_26970_363888
  intro a
  fin_cases a
  · exact context_13_107880_3444
  · exact context_13_107881_363854
  · exact context_13_107882_363878
  · exact context_13_107883_363887

theorem selected_cut_13990 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107884) = some ⟨13, 1, 0, 3444, 107884, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107884_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107884 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107884 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107884, 1, 16384⟩
    (by decide) selected_cut_13990

theorem selected_cut_13991 : selected 8 ⟨363905, by decide⟩
    (prefixPartial 13 107885) = some ⟨13, 2, 0, 363905, 107885, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_107885_363905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107885 ⟨363905, by decide⟩ :=
  accepted_of_selected 13 107885 ⟨363905, by decide⟩ ⟨13, 2, 0, 363905, 107885, 1509, 16384⟩
    (by decide) selected_cut_13991

theorem selected_cut_13992 : selected 8 ⟨363926, by decide⟩
    (prefixPartial 13 107886) = some ⟨13, 2, 0, 363926, 107886, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_107886_363926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107886 ⟨363926, by decide⟩ :=
  accepted_of_selected 13 107886 ⟨363926, by decide⟩ ⟨13, 2, 0, 363926, 107886, 1837, 16384⟩
    (by decide) selected_cut_13992

theorem selected_cut_13993 : selected 8 ⟨363936, by decide⟩
    (prefixPartial 13 107887) = some ⟨13, 2, 0, 363936, 107887, 937, 16384⟩ := by
  decide +kernel

theorem context_13_107887_363936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107887 ⟨363936, by decide⟩ :=
  accepted_of_selected 13 107887 ⟨363936, by decide⟩ ⟨13, 2, 0, 363936, 107887, 937, 16384⟩
    (by decide) selected_cut_13993

theorem unmarked_context_12_26971_363937 : frontier 9 ⟨363937, by decide⟩
    (prefixCache 12 26971) (prefixPartial 12 26971) = false := by
  decide +kernel

theorem node_context_12_26971_363937 : EJMOriginalGlobalDAGData.nodes 9 ⟨363937, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363905, by decide⟩,⟨363926, by decide⟩,⟨363936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26971_363937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26971 ⟨363937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26971
    ⟨363937, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363905, by decide⟩,⟨363926, by decide⟩,⟨363936, by decide⟩]) unmarked_context_12_26971_363937 node_context_12_26971_363937
  intro a
  fin_cases a
  · exact context_13_107884_3444
  · exact context_13_107885_363905
  · exact context_13_107886_363926
  · exact context_13_107887_363936

theorem unmarked_context_11_6742_363938 : frontier 10 ⟨363938, by decide⟩
    (prefixCache 11 6742) (prefixPartial 11 6742) = false := by
  decide +kernel

theorem node_context_11_6742_363938 : EJMOriginalGlobalDAGData.nodes 10 ⟨363938, by decide⟩ =
    .split (coordinate 11) (![⟨363839, by decide⟩,⟨126371, by decide⟩,⟨363888, by decide⟩,⟨363937, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6742_363938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6742 ⟨363938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6742
    ⟨363938, by decide⟩ (by decide) (![⟨363839, by decide⟩,⟨126371, by decide⟩,⟨363888, by decide⟩,⟨363937, by decide⟩]) unmarked_context_11_6742_363938 node_context_11_6742_363938
  intro a
  fin_cases a
  · exact context_12_26968_363839
  · exact context_12_26969_126371
  · exact context_12_26970_363888
  · exact context_12_26971_363937

theorem selected_cut_13994 : selected 9 ⟨363978, by decide⟩
    (prefixPartial 12 26972) = some ⟨12, 2, 0, 363978, 26972, 3833, 65536⟩ := by
  decide +kernel

theorem context_12_26972_363978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26972 ⟨363978, by decide⟩ :=
  accepted_of_selected 12 26972 ⟨363978, by decide⟩ ⟨12, 2, 0, 363978, 26972, 3833, 65536⟩
    (by decide) selected_cut_13994

theorem selected_cut_13995 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 26973) = some ⟨12, 1, 0, 320864, 26973, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26973_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26973 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 26973 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 26973, 1, 65536⟩
    (by decide) selected_cut_13995

theorem selected_cut_13996 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107896) = some ⟨13, 1, 0, 3444, 107896, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107896_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107896 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107896 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107896, 1, 16384⟩
    (by decide) selected_cut_13996

theorem selected_cut_13997 : selected 8 ⟨363992, by decide⟩
    (prefixPartial 13 107897) = some ⟨13, 2, 0, 363992, 107897, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_107897_363992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107897 ⟨363992, by decide⟩ :=
  accepted_of_selected 13 107897 ⟨363992, by decide⟩ ⟨13, 2, 0, 363992, 107897, 1469, 16384⟩
    (by decide) selected_cut_13997

theorem selected_cut_13998 : selected 8 ⟨364013, by decide⟩
    (prefixPartial 13 107898) = some ⟨13, 2, 0, 364013, 107898, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_107898_364013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107898 ⟨364013, by decide⟩ :=
  accepted_of_selected 13 107898 ⟨364013, by decide⟩ ⟨13, 2, 0, 364013, 107898, 1709, 16384⟩
    (by decide) selected_cut_13998

theorem selected_cut_13999 : selected 8 ⟨364019, by decide⟩
    (prefixPartial 13 107899) = some ⟨13, 2, 0, 364019, 107899, 985, 16384⟩ := by
  decide +kernel

theorem context_13_107899_364019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107899 ⟨364019, by decide⟩ :=
  accepted_of_selected 13 107899 ⟨364019, by decide⟩ ⟨13, 2, 0, 364019, 107899, 985, 16384⟩
    (by decide) selected_cut_13999

theorem unmarked_context_12_26974_364020 : frontier 9 ⟨364020, by decide⟩
    (prefixCache 12 26974) (prefixPartial 12 26974) = false := by
  decide +kernel

theorem node_context_12_26974_364020 : EJMOriginalGlobalDAGData.nodes 9 ⟨364020, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨363992, by decide⟩,⟨364013, by decide⟩,⟨364019, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26974_364020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26974 ⟨364020, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26974
    ⟨364020, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨363992, by decide⟩,⟨364013, by decide⟩,⟨364019, by decide⟩]) unmarked_context_12_26974_364020 node_context_12_26974_364020
  intro a
  fin_cases a
  · exact context_13_107896_3444
  · exact context_13_107897_363992
  · exact context_13_107898_364013
  · exact context_13_107899_364019

theorem selected_cut_14000 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107900) = some ⟨13, 1, 0, 3444, 107900, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107900_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107900 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107900 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107900, 1, 16384⟩
    (by decide) selected_cut_14000

theorem selected_cut_14001 : selected 8 ⟨364035, by decide⟩
    (prefixPartial 13 107901) = some ⟨13, 2, 0, 364035, 107901, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_107901_364035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107901 ⟨364035, by decide⟩ :=
  accepted_of_selected 13 107901 ⟨364035, by decide⟩ ⟨13, 2, 0, 364035, 107901, 1413, 16384⟩
    (by decide) selected_cut_14001

theorem selected_cut_14002 : selected 8 ⟨364057, by decide⟩
    (prefixPartial 13 107902) = some ⟨13, 2, 0, 364057, 107902, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_107902_364057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107902 ⟨364057, by decide⟩ :=
  accepted_of_selected 13 107902 ⟨364057, by decide⟩ ⟨13, 2, 0, 364057, 107902, 1741, 16384⟩
    (by decide) selected_cut_14002

theorem selected_cut_14003 : selected 8 ⟨364063, by decide⟩
    (prefixPartial 13 107903) = some ⟨13, 2, 0, 364063, 107903, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_107903_364063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107903 ⟨364063, by decide⟩ :=
  accepted_of_selected 13 107903 ⟨364063, by decide⟩ ⟨13, 2, 0, 364063, 107903, 1005, 16384⟩
    (by decide) selected_cut_14003

theorem unmarked_context_12_26975_364064 : frontier 9 ⟨364064, by decide⟩
    (prefixCache 12 26975) (prefixPartial 12 26975) = false := by
  decide +kernel

theorem node_context_12_26975_364064 : EJMOriginalGlobalDAGData.nodes 9 ⟨364064, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨364035, by decide⟩,⟨364057, by decide⟩,⟨364063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26975_364064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26975 ⟨364064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26975
    ⟨364064, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨364035, by decide⟩,⟨364057, by decide⟩,⟨364063, by decide⟩]) unmarked_context_12_26975_364064 node_context_12_26975_364064
  intro a
  fin_cases a
  · exact context_13_107900_3444
  · exact context_13_107901_364035
  · exact context_13_107902_364057
  · exact context_13_107903_364063

theorem unmarked_context_11_6743_364065 : frontier 10 ⟨364065, by decide⟩
    (prefixCache 11 6743) (prefixPartial 11 6743) = false := by
  decide +kernel

theorem node_context_11_6743_364065 : EJMOriginalGlobalDAGData.nodes 10 ⟨364065, by decide⟩ =
    .split (coordinate 11) (![⟨363978, by decide⟩,⟨320864, by decide⟩,⟨364020, by decide⟩,⟨364064, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6743_364065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6743 ⟨364065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6743
    ⟨364065, by decide⟩ (by decide) (![⟨363978, by decide⟩,⟨320864, by decide⟩,⟨364020, by decide⟩,⟨364064, by decide⟩]) unmarked_context_11_6743_364065 node_context_11_6743_364065
  intro a
  fin_cases a
  · exact context_12_26972_363978
  · exact context_12_26973_320864
  · exact context_12_26974_364020
  · exact context_12_26975_364064

theorem unmarked_context_10_1685_364066 : frontier 11 ⟨364066, by decide⟩
    (prefixCache 10 1685) (prefixPartial 10 1685) = false := by
  decide +kernel

theorem node_context_10_1685_364066 : EJMOriginalGlobalDAGData.nodes 11 ⟨364066, by decide⟩ =
    .split (coordinate 10) (![⟨363663, by decide⟩,⟨363799, by decide⟩,⟨363938, by decide⟩,⟨364065, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1685_364066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1685 ⟨364066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1685
    ⟨364066, by decide⟩ (by decide) (![⟨363663, by decide⟩,⟨363799, by decide⟩,⟨363938, by decide⟩,⟨364065, by decide⟩]) unmarked_context_10_1685_364066 node_context_10_1685_364066
  intro a
  fin_cases a
  · exact context_11_6740_363663
  · exact context_11_6741_363799
  · exact context_11_6742_363938
  · exact context_11_6743_364065

theorem selected_cut_14004 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107904) = some ⟨13, 1, 0, 3444, 107904, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107904_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107904 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107904 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107904, 1, 16384⟩
    (by decide) selected_cut_14004

theorem selected_cut_14005 : selected 8 ⟨364079, by decide⟩
    (prefixPartial 13 107905) = some ⟨13, 2, 0, 364079, 107905, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_107905_364079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107905 ⟨364079, by decide⟩ :=
  accepted_of_selected 13 107905 ⟨364079, by decide⟩ ⟨13, 2, 0, 364079, 107905, 1609, 16384⟩
    (by decide) selected_cut_14005

theorem selected_cut_14006 : selected 8 ⟨364095, by decide⟩
    (prefixPartial 13 107906) = some ⟨13, 2, 0, 364095, 107906, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_107906_364095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107906 ⟨364095, by decide⟩ :=
  accepted_of_selected 13 107906 ⟨364095, by decide⟩ ⟨13, 2, 0, 364095, 107906, 1557, 16384⟩
    (by decide) selected_cut_14006

theorem selected_cut_14007 : selected 8 ⟨364099, by decide⟩
    (prefixPartial 13 107907) = some ⟨13, 2, 0, 364099, 107907, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_107907_364099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107907 ⟨364099, by decide⟩ :=
  accepted_of_selected 13 107907 ⟨364099, by decide⟩ ⟨13, 2, 0, 364099, 107907, 1005, 16384⟩
    (by decide) selected_cut_14007

theorem unmarked_context_12_26976_364100 : frontier 9 ⟨364100, by decide⟩
    (prefixCache 12 26976) (prefixPartial 12 26976) = false := by
  decide +kernel

theorem node_context_12_26976_364100 : EJMOriginalGlobalDAGData.nodes 9 ⟨364100, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨364079, by decide⟩,⟨364095, by decide⟩,⟨364099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26976_364100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26976 ⟨364100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26976
    ⟨364100, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨364079, by decide⟩,⟨364095, by decide⟩,⟨364099, by decide⟩]) unmarked_context_12_26976_364100 node_context_12_26976_364100
  intro a
  fin_cases a
  · exact context_13_107904_3444
  · exact context_13_107905_364079
  · exact context_13_107906_364095
  · exact context_13_107907_364099

theorem selected_cut_14008 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107908) = some ⟨13, 1, 0, 3444, 107908, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107908_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107908 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107908 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107908, 1, 16384⟩
    (by decide) selected_cut_14008

theorem selected_cut_14009 : selected 8 ⟨364120, by decide⟩
    (prefixPartial 13 107909) = some ⟨13, 2, 0, 364120, 107909, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_107909_364120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107909 ⟨364120, by decide⟩ :=
  accepted_of_selected 13 107909 ⟨364120, by decide⟩ ⟨13, 2, 0, 364120, 107909, 1721, 16384⟩
    (by decide) selected_cut_14009

theorem selected_cut_14010 : selected 8 ⟨364146, by decide⟩
    (prefixPartial 13 107910) = some ⟨13, 2, 0, 364146, 107910, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_107910_364146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107910 ⟨364146, by decide⟩ :=
  accepted_of_selected 13 107910 ⟨364146, by decide⟩ ⟨13, 2, 0, 364146, 107910, 2261, 16384⟩
    (by decide) selected_cut_14010

theorem selected_cut_14011 : selected 8 ⟨364153, by decide⟩
    (prefixPartial 13 107911) = some ⟨13, 2, 0, 364153, 107911, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_107911_364153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107911 ⟨364153, by decide⟩ :=
  accepted_of_selected 13 107911 ⟨364153, by decide⟩ ⟨13, 2, 0, 364153, 107911, 1257, 16384⟩
    (by decide) selected_cut_14011

theorem unmarked_context_12_26977_364154 : frontier 9 ⟨364154, by decide⟩
    (prefixCache 12 26977) (prefixPartial 12 26977) = false := by
  decide +kernel

theorem node_context_12_26977_364154 : EJMOriginalGlobalDAGData.nodes 9 ⟨364154, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨364120, by decide⟩,⟨364146, by decide⟩,⟨364153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26977_364154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26977 ⟨364154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26977
    ⟨364154, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨364120, by decide⟩,⟨364146, by decide⟩,⟨364153, by decide⟩]) unmarked_context_12_26977_364154 node_context_12_26977_364154
  intro a
  fin_cases a
  · exact context_13_107908_3444
  · exact context_13_107909_364120
  · exact context_13_107910_364146
  · exact context_13_107911_364153

theorem selected_cut_14012 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107912) = some ⟨13, 1, 0, 3444, 107912, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107912_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107912 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107912 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107912, 1, 16384⟩
    (by decide) selected_cut_14012

theorem selected_cut_14013 : selected 8 ⟨364176, by decide⟩
    (prefixPartial 13 107913) = some ⟨13, 2, 0, 364176, 107913, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_107913_364176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107913 ⟨364176, by decide⟩ :=
  accepted_of_selected 13 107913 ⟨364176, by decide⟩ ⟨13, 2, 0, 364176, 107913, 1501, 16384⟩
    (by decide) selected_cut_14013

theorem selected_cut_14014 : selected 8 ⟨364199, by decide⟩
    (prefixPartial 13 107914) = some ⟨13, 2, 0, 364199, 107914, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_107914_364199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107914 ⟨364199, by decide⟩ :=
  accepted_of_selected 13 107914 ⟨364199, by decide⟩ ⟨13, 2, 0, 364199, 107914, 1821, 16384⟩
    (by decide) selected_cut_14014

theorem selected_cut_14015 : selected 8 ⟨364208, by decide⟩
    (prefixPartial 13 107915) = some ⟨13, 2, 0, 364208, 107915, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_107915_364208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107915 ⟨364208, by decide⟩ :=
  accepted_of_selected 13 107915 ⟨364208, by decide⟩ ⟨13, 2, 0, 364208, 107915, 1061, 16384⟩
    (by decide) selected_cut_14015

theorem unmarked_context_12_26978_364209 : frontier 9 ⟨364209, by decide⟩
    (prefixCache 12 26978) (prefixPartial 12 26978) = false := by
  decide +kernel

theorem node_context_12_26978_364209 : EJMOriginalGlobalDAGData.nodes 9 ⟨364209, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨364176, by decide⟩,⟨364199, by decide⟩,⟨364208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26978_364209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26978 ⟨364209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26978
    ⟨364209, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨364176, by decide⟩,⟨364199, by decide⟩,⟨364208, by decide⟩]) unmarked_context_12_26978_364209 node_context_12_26978_364209
  intro a
  fin_cases a
  · exact context_13_107912_3444
  · exact context_13_107913_364176
  · exact context_13_107914_364199
  · exact context_13_107915_364208

theorem selected_cut_14016 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 107916) = some ⟨13, 1, 0, 3444, 107916, 1, 16384⟩ := by
  decide +kernel

theorem context_13_107916_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107916 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 107916 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 107916, 1, 16384⟩
    (by decide) selected_cut_14016

theorem selected_cut_14017 : selected 8 ⟨364224, by decide⟩
    (prefixPartial 13 107917) = some ⟨13, 2, 0, 364224, 107917, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_107917_364224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107917 ⟨364224, by decide⟩ :=
  accepted_of_selected 13 107917 ⟨364224, by decide⟩ ⟨13, 2, 0, 364224, 107917, 1509, 16384⟩
    (by decide) selected_cut_14017

theorem selected_cut_14018 : selected 8 ⟨364247, by decide⟩
    (prefixPartial 13 107918) = some ⟨13, 2, 0, 364247, 107918, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_107918_364247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107918 ⟨364247, by decide⟩ :=
  accepted_of_selected 13 107918 ⟨364247, by decide⟩ ⟨13, 2, 0, 364247, 107918, 2041, 16384⟩
    (by decide) selected_cut_14018

theorem selected_cut_14019 : selected 8 ⟨364255, by decide⟩
    (prefixPartial 13 107919) = some ⟨13, 2, 0, 364255, 107919, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_107919_364255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107919 ⟨364255, by decide⟩ :=
  accepted_of_selected 13 107919 ⟨364255, by decide⟩ ⟨13, 2, 0, 364255, 107919, 1057, 16384⟩
    (by decide) selected_cut_14019

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
