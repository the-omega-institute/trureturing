/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover320
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_30819 : selected 8 ⟨783545, by decide⟩
    (prefixPartial 13 420936) = some ⟨13, 2, 0, 783545, 420936, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_420936_783545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420936 ⟨783545, by decide⟩ :=
  accepted_of_selected 13 420936 ⟨783545, by decide⟩ ⟨13, 2, 0, 783545, 420936, 2289, 16384⟩
    (by decide) selected_cut_30819

theorem selected_cut_30820 : selected 8 ⟨783574, by decide⟩
    (prefixPartial 13 420937) = some ⟨13, 2, 0, 783574, 420937, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_420937_783574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420937 ⟨783574, by decide⟩ :=
  accepted_of_selected 13 420937 ⟨783574, by decide⟩ ⟨13, 2, 0, 783574, 420937, 2137, 16384⟩
    (by decide) selected_cut_30820

theorem selected_cut_30821 : selected 8 ⟨783600, by decide⟩
    (prefixPartial 13 420938) = some ⟨13, 2, 0, 783600, 420938, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_420938_783600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420938 ⟨783600, by decide⟩ :=
  accepted_of_selected 13 420938 ⟨783600, by decide⟩ ⟨13, 2, 0, 783600, 420938, 1373, 16384⟩
    (by decide) selected_cut_30821

theorem selected_cut_30822 : selected 8 ⟨783607, by decide⟩
    (prefixPartial 13 420939) = some ⟨13, 2, 0, 783607, 420939, 589, 16384⟩ := by
  decide +kernel

theorem context_13_420939_783607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420939 ⟨783607, by decide⟩ :=
  accepted_of_selected 13 420939 ⟨783607, by decide⟩ ⟨13, 2, 0, 783607, 420939, 589, 16384⟩
    (by decide) selected_cut_30822

theorem unmarked_context_12_105234_783608 : frontier 9 ⟨783608, by decide⟩
    (prefixCache 12 105234) (prefixPartial 12 105234) = false := by
  decide +kernel

theorem node_context_12_105234_783608 : EJMOriginalGlobalDAGData.nodes 9 ⟨783608, by decide⟩ =
    .split (coordinate 12) (![⟨783545, by decide⟩,⟨783574, by decide⟩,⟨783600, by decide⟩,⟨783607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105234_783608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105234 ⟨783608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105234
    ⟨783608, by decide⟩ (by decide) (![⟨783545, by decide⟩,⟨783574, by decide⟩,⟨783600, by decide⟩,⟨783607, by decide⟩]) unmarked_context_12_105234_783608 node_context_12_105234_783608
  intro a
  fin_cases a
  · exact context_13_420936_783545
  · exact context_13_420937_783574
  · exact context_13_420938_783600
  · exact context_13_420939_783607

theorem selected_cut_30823 : selected 8 ⟨783640, by decide⟩
    (prefixPartial 13 420940) = some ⟨13, 2, 0, 783640, 420940, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_420940_783640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420940 ⟨783640, by decide⟩ :=
  accepted_of_selected 13 420940 ⟨783640, by decide⟩ ⟨13, 2, 0, 783640, 420940, 2021, 16384⟩
    (by decide) selected_cut_30823

theorem selected_cut_30824 : selected 8 ⟨783668, by decide⟩
    (prefixPartial 13 420941) = some ⟨13, 2, 0, 783668, 420941, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_420941_783668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420941 ⟨783668, by decide⟩ :=
  accepted_of_selected 13 420941 ⟨783668, by decide⟩ ⟨13, 2, 0, 783668, 420941, 2209, 16384⟩
    (by decide) selected_cut_30824

theorem selected_cut_30825 : selected 8 ⟨783690, by decide⟩
    (prefixPartial 13 420942) = some ⟨13, 2, 0, 783690, 420942, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_420942_783690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420942 ⟨783690, by decide⟩ :=
  accepted_of_selected 13 420942 ⟨783690, by decide⟩ ⟨13, 2, 0, 783690, 420942, 1349, 16384⟩
    (by decide) selected_cut_30825

theorem selected_cut_30826 : selected 8 ⟨783697, by decide⟩
    (prefixPartial 13 420943) = some ⟨13, 2, 0, 783697, 420943, 569, 16384⟩ := by
  decide +kernel

theorem context_13_420943_783697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420943 ⟨783697, by decide⟩ :=
  accepted_of_selected 13 420943 ⟨783697, by decide⟩ ⟨13, 2, 0, 783697, 420943, 569, 16384⟩
    (by decide) selected_cut_30826

theorem unmarked_context_12_105235_783698 : frontier 9 ⟨783698, by decide⟩
    (prefixCache 12 105235) (prefixPartial 12 105235) = false := by
  decide +kernel

theorem node_context_12_105235_783698 : EJMOriginalGlobalDAGData.nodes 9 ⟨783698, by decide⟩ =
    .split (coordinate 12) (![⟨783640, by decide⟩,⟨783668, by decide⟩,⟨783690, by decide⟩,⟨783697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105235_783698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105235 ⟨783698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105235
    ⟨783698, by decide⟩ (by decide) (![⟨783640, by decide⟩,⟨783668, by decide⟩,⟨783690, by decide⟩,⟨783697, by decide⟩]) unmarked_context_12_105235_783698 node_context_12_105235_783698
  intro a
  fin_cases a
  · exact context_13_420940_783640
  · exact context_13_420941_783668
  · exact context_13_420942_783690
  · exact context_13_420943_783697

theorem unmarked_context_11_26308_783699 : frontier 10 ⟨783699, by decide⟩
    (prefixCache 11 26308) (prefixPartial 11 26308) = false := by
  decide +kernel

theorem node_context_11_26308_783699 : EJMOriginalGlobalDAGData.nodes 10 ⟨783699, by decide⟩ =
    .split (coordinate 11) (![⟨783397, by decide⟩,⟨783511, by decide⟩,⟨783608, by decide⟩,⟨783698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26308_783699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26308 ⟨783699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26308
    ⟨783699, by decide⟩ (by decide) (![⟨783397, by decide⟩,⟨783511, by decide⟩,⟨783608, by decide⟩,⟨783698, by decide⟩]) unmarked_context_11_26308_783699 node_context_11_26308_783699
  intro a
  fin_cases a
  · exact context_12_105232_783397
  · exact context_12_105233_783511
  · exact context_12_105234_783608
  · exact context_12_105235_783698

theorem selected_cut_30827 : selected 8 ⟨783728, by decide⟩
    (prefixPartial 13 420944) = some ⟨13, 2, 0, 783728, 420944, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_420944_783728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420944 ⟨783728, by decide⟩ :=
  accepted_of_selected 13 420944 ⟨783728, by decide⟩ ⟨13, 2, 0, 783728, 420944, 1493, 16384⟩
    (by decide) selected_cut_30827

theorem selected_cut_30828 : selected 8 ⟨783760, by decide⟩
    (prefixPartial 13 420945) = some ⟨13, 2, 0, 783760, 420945, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_420945_783760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420945 ⟨783760, by decide⟩ :=
  accepted_of_selected 13 420945 ⟨783760, by decide⟩ ⟨13, 2, 0, 783760, 420945, 1989, 16384⟩
    (by decide) selected_cut_30828

theorem selected_cut_30829 : selected 8 ⟨783782, by decide⟩
    (prefixPartial 13 420946) = some ⟨13, 2, 0, 783782, 420946, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_420946_783782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420946 ⟨783782, by decide⟩ :=
  accepted_of_selected 13 420946 ⟨783782, by decide⟩ ⟨13, 2, 0, 783782, 420946, 1045, 16384⟩
    (by decide) selected_cut_30829

theorem selected_cut_30830 : selected 8 ⟨783796, by decide⟩
    (prefixPartial 13 420947) = some ⟨13, 2, 0, 783796, 420947, 753, 16384⟩ := by
  decide +kernel

theorem context_13_420947_783796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420947 ⟨783796, by decide⟩ :=
  accepted_of_selected 13 420947 ⟨783796, by decide⟩ ⟨13, 2, 0, 783796, 420947, 753, 16384⟩
    (by decide) selected_cut_30830

theorem unmarked_context_12_105236_783797 : frontier 9 ⟨783797, by decide⟩
    (prefixCache 12 105236) (prefixPartial 12 105236) = false := by
  decide +kernel

theorem node_context_12_105236_783797 : EJMOriginalGlobalDAGData.nodes 9 ⟨783797, by decide⟩ =
    .split (coordinate 12) (![⟨783728, by decide⟩,⟨783760, by decide⟩,⟨783782, by decide⟩,⟨783796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105236_783797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105236 ⟨783797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105236
    ⟨783797, by decide⟩ (by decide) (![⟨783728, by decide⟩,⟨783760, by decide⟩,⟨783782, by decide⟩,⟨783796, by decide⟩]) unmarked_context_12_105236_783797 node_context_12_105236_783797
  intro a
  fin_cases a
  · exact context_13_420944_783728
  · exact context_13_420945_783760
  · exact context_13_420946_783782
  · exact context_13_420947_783796

theorem selected_cut_30831 : selected 8 ⟨783834, by decide⟩
    (prefixPartial 13 420948) = some ⟨13, 2, 0, 783834, 420948, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_420948_783834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420948 ⟨783834, by decide⟩ :=
  accepted_of_selected 13 420948 ⟨783834, by decide⟩ ⟨13, 2, 0, 783834, 420948, 1925, 16384⟩
    (by decide) selected_cut_30831

theorem selected_cut_30832 : selected 8 ⟨783868, by decide⟩
    (prefixPartial 13 420949) = some ⟨13, 2, 0, 783868, 420949, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_420949_783868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420949 ⟨783868, by decide⟩ :=
  accepted_of_selected 13 420949 ⟨783868, by decide⟩ ⟨13, 2, 0, 783868, 420949, 1985, 16384⟩
    (by decide) selected_cut_30832

theorem selected_cut_30833 : selected 8 ⟨783890, by decide⟩
    (prefixPartial 13 420950) = some ⟨13, 2, 0, 783890, 420950, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_420950_783890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420950 ⟨783890, by decide⟩ :=
  accepted_of_selected 13 420950 ⟨783890, by decide⟩ ⟨13, 2, 0, 783890, 420950, 1065, 16384⟩
    (by decide) selected_cut_30833

theorem selected_cut_30834 : selected 8 ⟨783898, by decide⟩
    (prefixPartial 13 420951) = some ⟨13, 2, 0, 783898, 420951, 757, 16384⟩ := by
  decide +kernel

theorem context_13_420951_783898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420951 ⟨783898, by decide⟩ :=
  accepted_of_selected 13 420951 ⟨783898, by decide⟩ ⟨13, 2, 0, 783898, 420951, 757, 16384⟩
    (by decide) selected_cut_30834

theorem unmarked_context_12_105237_783899 : frontier 9 ⟨783899, by decide⟩
    (prefixCache 12 105237) (prefixPartial 12 105237) = false := by
  decide +kernel

theorem node_context_12_105237_783899 : EJMOriginalGlobalDAGData.nodes 9 ⟨783899, by decide⟩ =
    .split (coordinate 12) (![⟨783834, by decide⟩,⟨783868, by decide⟩,⟨783890, by decide⟩,⟨783898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105237_783899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105237 ⟨783899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105237
    ⟨783899, by decide⟩ (by decide) (![⟨783834, by decide⟩,⟨783868, by decide⟩,⟨783890, by decide⟩,⟨783898, by decide⟩]) unmarked_context_12_105237_783899 node_context_12_105237_783899
  intro a
  fin_cases a
  · exact context_13_420948_783834
  · exact context_13_420949_783868
  · exact context_13_420950_783890
  · exact context_13_420951_783898

theorem selected_cut_30835 : selected 8 ⟨783929, by decide⟩
    (prefixPartial 13 420952) = some ⟨13, 2, 0, 783929, 420952, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_420952_783929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420952 ⟨783929, by decide⟩ :=
  accepted_of_selected 13 420952 ⟨783929, by decide⟩ ⟨13, 2, 0, 783929, 420952, 1693, 16384⟩
    (by decide) selected_cut_30835

theorem selected_cut_30836 : selected 8 ⟨783959, by decide⟩
    (prefixPartial 13 420953) = some ⟨13, 2, 0, 783959, 420953, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_420953_783959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420953 ⟨783959, by decide⟩ :=
  accepted_of_selected 13 420953 ⟨783959, by decide⟩ ⟨13, 2, 0, 783959, 420953, 2073, 16384⟩
    (by decide) selected_cut_30836

theorem selected_cut_30837 : selected 8 ⟨783982, by decide⟩
    (prefixPartial 13 420954) = some ⟨13, 2, 0, 783982, 420954, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_420954_783982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420954 ⟨783982, by decide⟩ :=
  accepted_of_selected 13 420954 ⟨783982, by decide⟩ ⟨13, 2, 0, 783982, 420954, 1129, 16384⟩
    (by decide) selected_cut_30837

theorem selected_cut_30838 : selected 8 ⟨783989, by decide⟩
    (prefixPartial 13 420955) = some ⟨13, 2, 0, 783989, 420955, 701, 16384⟩ := by
  decide +kernel

theorem context_13_420955_783989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420955 ⟨783989, by decide⟩ :=
  accepted_of_selected 13 420955 ⟨783989, by decide⟩ ⟨13, 2, 0, 783989, 420955, 701, 16384⟩
    (by decide) selected_cut_30838

theorem unmarked_context_12_105238_783990 : frontier 9 ⟨783990, by decide⟩
    (prefixCache 12 105238) (prefixPartial 12 105238) = false := by
  decide +kernel

theorem node_context_12_105238_783990 : EJMOriginalGlobalDAGData.nodes 9 ⟨783990, by decide⟩ =
    .split (coordinate 12) (![⟨783929, by decide⟩,⟨783959, by decide⟩,⟨783982, by decide⟩,⟨783989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105238_783990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105238 ⟨783990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105238
    ⟨783990, by decide⟩ (by decide) (![⟨783929, by decide⟩,⟨783959, by decide⟩,⟨783982, by decide⟩,⟨783989, by decide⟩]) unmarked_context_12_105238_783990 node_context_12_105238_783990
  intro a
  fin_cases a
  · exact context_13_420952_783929
  · exact context_13_420953_783959
  · exact context_13_420954_783982
  · exact context_13_420955_783989

theorem selected_cut_30839 : selected 8 ⟨784020, by decide⟩
    (prefixPartial 13 420956) = some ⟨13, 2, 0, 784020, 420956, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_420956_784020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420956 ⟨784020, by decide⟩ :=
  accepted_of_selected 13 420956 ⟨784020, by decide⟩ ⟨13, 2, 0, 784020, 420956, 1617, 16384⟩
    (by decide) selected_cut_30839

theorem selected_cut_30840 : selected 8 ⟨784052, by decide⟩
    (prefixPartial 13 420957) = some ⟨13, 2, 0, 784052, 420957, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_420957_784052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420957 ⟨784052, by decide⟩ :=
  accepted_of_selected 13 420957 ⟨784052, by decide⟩ ⟨13, 2, 0, 784052, 420957, 2129, 16384⟩
    (by decide) selected_cut_30840

theorem selected_cut_30841 : selected 8 ⟨784072, by decide⟩
    (prefixPartial 13 420958) = some ⟨13, 2, 0, 784072, 420958, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_420958_784072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420958 ⟨784072, by decide⟩ :=
  accepted_of_selected 13 420958 ⟨784072, by decide⟩ ⟨13, 2, 0, 784072, 420958, 1105, 16384⟩
    (by decide) selected_cut_30841

theorem selected_cut_30842 : selected 8 ⟨784079, by decide⟩
    (prefixPartial 13 420959) = some ⟨13, 2, 0, 784079, 420959, 633, 16384⟩ := by
  decide +kernel

theorem context_13_420959_784079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420959 ⟨784079, by decide⟩ :=
  accepted_of_selected 13 420959 ⟨784079, by decide⟩ ⟨13, 2, 0, 784079, 420959, 633, 16384⟩
    (by decide) selected_cut_30842

theorem unmarked_context_12_105239_784080 : frontier 9 ⟨784080, by decide⟩
    (prefixCache 12 105239) (prefixPartial 12 105239) = false := by
  decide +kernel

theorem node_context_12_105239_784080 : EJMOriginalGlobalDAGData.nodes 9 ⟨784080, by decide⟩ =
    .split (coordinate 12) (![⟨784020, by decide⟩,⟨784052, by decide⟩,⟨784072, by decide⟩,⟨784079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105239_784080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105239 ⟨784080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105239
    ⟨784080, by decide⟩ (by decide) (![⟨784020, by decide⟩,⟨784052, by decide⟩,⟨784072, by decide⟩,⟨784079, by decide⟩]) unmarked_context_12_105239_784080 node_context_12_105239_784080
  intro a
  fin_cases a
  · exact context_13_420956_784020
  · exact context_13_420957_784052
  · exact context_13_420958_784072
  · exact context_13_420959_784079

theorem unmarked_context_11_26309_784081 : frontier 10 ⟨784081, by decide⟩
    (prefixCache 11 26309) (prefixPartial 11 26309) = false := by
  decide +kernel

theorem node_context_11_26309_784081 : EJMOriginalGlobalDAGData.nodes 10 ⟨784081, by decide⟩ =
    .split (coordinate 11) (![⟨783797, by decide⟩,⟨783899, by decide⟩,⟨783990, by decide⟩,⟨784080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26309_784081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26309 ⟨784081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26309
    ⟨784081, by decide⟩ (by decide) (![⟨783797, by decide⟩,⟨783899, by decide⟩,⟨783990, by decide⟩,⟨784080, by decide⟩]) unmarked_context_11_26309_784081 node_context_11_26309_784081
  intro a
  fin_cases a
  · exact context_12_105236_783797
  · exact context_12_105237_783899
  · exact context_12_105238_783990
  · exact context_12_105239_784080

theorem selected_cut_30843 : selected 8 ⟨784106, by decide⟩
    (prefixPartial 13 420960) = some ⟨13, 2, 0, 784106, 420960, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_420960_784106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420960 ⟨784106, by decide⟩ :=
  accepted_of_selected 13 420960 ⟨784106, by decide⟩ ⟨13, 2, 0, 784106, 420960, 1213, 16384⟩
    (by decide) selected_cut_30843

theorem selected_cut_30844 : selected 8 ⟨784128, by decide⟩
    (prefixPartial 13 420961) = some ⟨13, 2, 0, 784128, 420961, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_420961_784128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420961 ⟨784128, by decide⟩ :=
  accepted_of_selected 13 420961 ⟨784128, by decide⟩ ⟨13, 2, 0, 784128, 420961, 1677, 16384⟩
    (by decide) selected_cut_30844

theorem selected_cut_30845 : selected 8 ⟨784157, by decide⟩
    (prefixPartial 13 420962) = some ⟨13, 2, 0, 784157, 420962, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_420962_784157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420962 ⟨784157, by decide⟩ :=
  accepted_of_selected 13 420962 ⟨784157, by decide⟩ ⟨13, 2, 0, 784157, 420962, 1289, 16384⟩
    (by decide) selected_cut_30845

theorem selected_cut_30846 : selected 8 ⟨784166, by decide⟩
    (prefixPartial 13 420963) = some ⟨13, 2, 0, 784166, 420963, 709, 16384⟩ := by
  decide +kernel

theorem context_13_420963_784166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420963 ⟨784166, by decide⟩ :=
  accepted_of_selected 13 420963 ⟨784166, by decide⟩ ⟨13, 2, 0, 784166, 420963, 709, 16384⟩
    (by decide) selected_cut_30846

theorem unmarked_context_12_105240_784167 : frontier 9 ⟨784167, by decide⟩
    (prefixCache 12 105240) (prefixPartial 12 105240) = false := by
  decide +kernel

theorem node_context_12_105240_784167 : EJMOriginalGlobalDAGData.nodes 9 ⟨784167, by decide⟩ =
    .split (coordinate 12) (![⟨784106, by decide⟩,⟨784128, by decide⟩,⟨784157, by decide⟩,⟨784166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105240_784167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105240 ⟨784167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105240
    ⟨784167, by decide⟩ (by decide) (![⟨784106, by decide⟩,⟨784128, by decide⟩,⟨784157, by decide⟩,⟨784166, by decide⟩]) unmarked_context_12_105240_784167 node_context_12_105240_784167
  intro a
  fin_cases a
  · exact context_13_420960_784106
  · exact context_13_420961_784128
  · exact context_13_420962_784157
  · exact context_13_420963_784166

theorem selected_cut_30847 : selected 8 ⟨784196, by decide⟩
    (prefixPartial 13 420964) = some ⟨13, 2, 0, 784196, 420964, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_420964_784196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420964 ⟨784196, by decide⟩ :=
  accepted_of_selected 13 420964 ⟨784196, by decide⟩ ⟨13, 2, 0, 784196, 420964, 1597, 16384⟩
    (by decide) selected_cut_30847

theorem selected_cut_30848 : selected 8 ⟨784230, by decide⟩
    (prefixPartial 13 420965) = some ⟨13, 2, 0, 784230, 420965, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_420965_784230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420965 ⟨784230, by decide⟩ :=
  accepted_of_selected 13 420965 ⟨784230, by decide⟩ ⟨13, 2, 0, 784230, 420965, 1853, 16384⟩
    (by decide) selected_cut_30848

theorem selected_cut_30849 : selected 8 ⟨784262, by decide⟩
    (prefixPartial 13 420966) = some ⟨13, 2, 0, 784262, 420966, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_420966_784262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420966 ⟨784262, by decide⟩ :=
  accepted_of_selected 13 420966 ⟨784262, by decide⟩ ⟨13, 2, 0, 784262, 420966, 1385, 16384⟩
    (by decide) selected_cut_30849

theorem selected_cut_30850 : selected 8 ⟨784268, by decide⟩
    (prefixPartial 13 420967) = some ⟨13, 2, 0, 784268, 420967, 741, 16384⟩ := by
  decide +kernel

theorem context_13_420967_784268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420967 ⟨784268, by decide⟩ :=
  accepted_of_selected 13 420967 ⟨784268, by decide⟩ ⟨13, 2, 0, 784268, 420967, 741, 16384⟩
    (by decide) selected_cut_30850

theorem unmarked_context_12_105241_784269 : frontier 9 ⟨784269, by decide⟩
    (prefixCache 12 105241) (prefixPartial 12 105241) = false := by
  decide +kernel

theorem node_context_12_105241_784269 : EJMOriginalGlobalDAGData.nodes 9 ⟨784269, by decide⟩ =
    .split (coordinate 12) (![⟨784196, by decide⟩,⟨784230, by decide⟩,⟨784262, by decide⟩,⟨784268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105241_784269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105241 ⟨784269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105241
    ⟨784269, by decide⟩ (by decide) (![⟨784196, by decide⟩,⟨784230, by decide⟩,⟨784262, by decide⟩,⟨784268, by decide⟩]) unmarked_context_12_105241_784269 node_context_12_105241_784269
  intro a
  fin_cases a
  · exact context_13_420964_784196
  · exact context_13_420965_784230
  · exact context_13_420966_784262
  · exact context_13_420967_784268

theorem selected_cut_30851 : selected 8 ⟨784292, by decide⟩
    (prefixPartial 13 420968) = some ⟨13, 2, 0, 784292, 420968, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_420968_784292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420968 ⟨784292, by decide⟩ :=
  accepted_of_selected 13 420968 ⟨784292, by decide⟩ ⟨13, 2, 0, 784292, 420968, 1469, 16384⟩
    (by decide) selected_cut_30851

theorem selected_cut_30852 : selected 8 ⟨784317, by decide⟩
    (prefixPartial 13 420969) = some ⟨13, 2, 0, 784317, 420969, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_420969_784317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420969 ⟨784317, by decide⟩ :=
  accepted_of_selected 13 420969 ⟨784317, by decide⟩ ⟨13, 2, 0, 784317, 420969, 1869, 16384⟩
    (by decide) selected_cut_30852

theorem selected_cut_30853 : selected 8 ⟨784339, by decide⟩
    (prefixPartial 13 420970) = some ⟨13, 2, 0, 784339, 420970, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_420970_784339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420970 ⟨784339, by decide⟩ :=
  accepted_of_selected 13 420970 ⟨784339, by decide⟩ ⟨13, 2, 0, 784339, 420970, 1433, 16384⟩
    (by decide) selected_cut_30853

theorem selected_cut_30854 : selected 8 ⟨784345, by decide⟩
    (prefixPartial 13 420971) = some ⟨13, 2, 0, 784345, 420971, 665, 16384⟩ := by
  decide +kernel

theorem context_13_420971_784345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420971 ⟨784345, by decide⟩ :=
  accepted_of_selected 13 420971 ⟨784345, by decide⟩ ⟨13, 2, 0, 784345, 420971, 665, 16384⟩
    (by decide) selected_cut_30854

theorem unmarked_context_12_105242_784346 : frontier 9 ⟨784346, by decide⟩
    (prefixCache 12 105242) (prefixPartial 12 105242) = false := by
  decide +kernel

theorem node_context_12_105242_784346 : EJMOriginalGlobalDAGData.nodes 9 ⟨784346, by decide⟩ =
    .split (coordinate 12) (![⟨784292, by decide⟩,⟨784317, by decide⟩,⟨784339, by decide⟩,⟨784345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105242_784346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105242 ⟨784346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105242
    ⟨784346, by decide⟩ (by decide) (![⟨784292, by decide⟩,⟨784317, by decide⟩,⟨784339, by decide⟩,⟨784345, by decide⟩]) unmarked_context_12_105242_784346 node_context_12_105242_784346
  intro a
  fin_cases a
  · exact context_13_420968_784292
  · exact context_13_420969_784317
  · exact context_13_420970_784339
  · exact context_13_420971_784345

theorem selected_cut_30855 : selected 8 ⟨784369, by decide⟩
    (prefixPartial 13 420972) = some ⟨13, 2, 0, 784369, 420972, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_420972_784369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420972 ⟨784369, by decide⟩ :=
  accepted_of_selected 13 420972 ⟨784369, by decide⟩ ⟨13, 2, 0, 784369, 420972, 1405, 16384⟩
    (by decide) selected_cut_30855

theorem selected_cut_30856 : selected 8 ⟨784399, by decide⟩
    (prefixPartial 13 420973) = some ⟨13, 2, 0, 784399, 420973, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_420973_784399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420973 ⟨784399, by decide⟩ :=
  accepted_of_selected 13 420973 ⟨784399, by decide⟩ ⟨13, 2, 0, 784399, 420973, 2041, 16384⟩
    (by decide) selected_cut_30856

theorem selected_cut_30857 : selected 8 ⟨784424, by decide⟩
    (prefixPartial 13 420974) = some ⟨13, 2, 0, 784424, 420974, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_420974_784424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420974 ⟨784424, by decide⟩ :=
  accepted_of_selected 13 420974 ⟨784424, by decide⟩ ⟨13, 2, 0, 784424, 420974, 1381, 16384⟩
    (by decide) selected_cut_30857

theorem selected_cut_30858 : selected 8 ⟨784430, by decide⟩
    (prefixPartial 13 420975) = some ⟨13, 2, 0, 784430, 420975, 657, 16384⟩ := by
  decide +kernel

theorem context_13_420975_784430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420975 ⟨784430, by decide⟩ :=
  accepted_of_selected 13 420975 ⟨784430, by decide⟩ ⟨13, 2, 0, 784430, 420975, 657, 16384⟩
    (by decide) selected_cut_30858

theorem unmarked_context_12_105243_784431 : frontier 9 ⟨784431, by decide⟩
    (prefixCache 12 105243) (prefixPartial 12 105243) = false := by
  decide +kernel

theorem node_context_12_105243_784431 : EJMOriginalGlobalDAGData.nodes 9 ⟨784431, by decide⟩ =
    .split (coordinate 12) (![⟨784369, by decide⟩,⟨784399, by decide⟩,⟨784424, by decide⟩,⟨784430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105243_784431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105243 ⟨784431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105243
    ⟨784431, by decide⟩ (by decide) (![⟨784369, by decide⟩,⟨784399, by decide⟩,⟨784424, by decide⟩,⟨784430, by decide⟩]) unmarked_context_12_105243_784431 node_context_12_105243_784431
  intro a
  fin_cases a
  · exact context_13_420972_784369
  · exact context_13_420973_784399
  · exact context_13_420974_784424
  · exact context_13_420975_784430

theorem unmarked_context_11_26310_784432 : frontier 10 ⟨784432, by decide⟩
    (prefixCache 11 26310) (prefixPartial 11 26310) = false := by
  decide +kernel

theorem node_context_11_26310_784432 : EJMOriginalGlobalDAGData.nodes 10 ⟨784432, by decide⟩ =
    .split (coordinate 11) (![⟨784167, by decide⟩,⟨784269, by decide⟩,⟨784346, by decide⟩,⟨784431, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26310_784432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26310 ⟨784432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26310
    ⟨784432, by decide⟩ (by decide) (![⟨784167, by decide⟩,⟨784269, by decide⟩,⟨784346, by decide⟩,⟨784431, by decide⟩]) unmarked_context_11_26310_784432 node_context_11_26310_784432
  intro a
  fin_cases a
  · exact context_12_105240_784167
  · exact context_12_105241_784269
  · exact context_12_105242_784346
  · exact context_12_105243_784431

theorem selected_cut_30859 : selected 8 ⟨784451, by decide⟩
    (prefixPartial 13 420976) = some ⟨13, 2, 0, 784451, 420976, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_420976_784451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420976 ⟨784451, by decide⟩ :=
  accepted_of_selected 13 420976 ⟨784451, by decide⟩ ⟨13, 2, 0, 784451, 420976, 1193, 16384⟩
    (by decide) selected_cut_30859

theorem selected_cut_30860 : selected 8 ⟨784472, by decide⟩
    (prefixPartial 13 420977) = some ⟨13, 2, 0, 784472, 420977, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_420977_784472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420977 ⟨784472, by decide⟩ :=
  accepted_of_selected 13 420977 ⟨784472, by decide⟩ ⟨13, 2, 0, 784472, 420977, 1297, 16384⟩
    (by decide) selected_cut_30860

theorem selected_cut_30861 : selected 8 ⟨784497, by decide⟩
    (prefixPartial 13 420978) = some ⟨13, 2, 0, 784497, 420978, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_420978_784497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420978 ⟨784497, by decide⟩ :=
  accepted_of_selected 13 420978 ⟨784497, by decide⟩ ⟨13, 2, 0, 784497, 420978, 1197, 16384⟩
    (by decide) selected_cut_30861

theorem selected_cut_30862 : selected 8 ⟨784505, by decide⟩
    (prefixPartial 13 420979) = some ⟨13, 2, 0, 784505, 420979, 725, 16384⟩ := by
  decide +kernel

theorem context_13_420979_784505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420979 ⟨784505, by decide⟩ :=
  accepted_of_selected 13 420979 ⟨784505, by decide⟩ ⟨13, 2, 0, 784505, 420979, 725, 16384⟩
    (by decide) selected_cut_30862

theorem unmarked_context_12_105244_784506 : frontier 9 ⟨784506, by decide⟩
    (prefixCache 12 105244) (prefixPartial 12 105244) = false := by
  decide +kernel

theorem node_context_12_105244_784506 : EJMOriginalGlobalDAGData.nodes 9 ⟨784506, by decide⟩ =
    .split (coordinate 12) (![⟨784451, by decide⟩,⟨784472, by decide⟩,⟨784497, by decide⟩,⟨784505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105244_784506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105244 ⟨784506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105244
    ⟨784506, by decide⟩ (by decide) (![⟨784451, by decide⟩,⟨784472, by decide⟩,⟨784497, by decide⟩,⟨784505, by decide⟩]) unmarked_context_12_105244_784506 node_context_12_105244_784506
  intro a
  fin_cases a
  · exact context_13_420976_784451
  · exact context_13_420977_784472
  · exact context_13_420978_784497
  · exact context_13_420979_784505

theorem selected_cut_30863 : selected 8 ⟨784532, by decide⟩
    (prefixPartial 13 420980) = some ⟨13, 2, 0, 784532, 420980, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_420980_784532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420980 ⟨784532, by decide⟩ :=
  accepted_of_selected 13 420980 ⟨784532, by decide⟩ ⟨13, 2, 0, 784532, 420980, 1461, 16384⟩
    (by decide) selected_cut_30863

theorem selected_cut_30864 : selected 8 ⟨784560, by decide⟩
    (prefixPartial 13 420981) = some ⟨13, 2, 0, 784560, 420981, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_420981_784560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420981 ⟨784560, by decide⟩ :=
  accepted_of_selected 13 420981 ⟨784560, by decide⟩ ⟨13, 2, 0, 784560, 420981, 1597, 16384⟩
    (by decide) selected_cut_30864

theorem selected_cut_30865 : selected 8 ⟨784593, by decide⟩
    (prefixPartial 13 420982) = some ⟨13, 2, 0, 784593, 420982, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_420982_784593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420982 ⟨784593, by decide⟩ :=
  accepted_of_selected 13 420982 ⟨784593, by decide⟩ ⟨13, 2, 0, 784593, 420982, 1381, 16384⟩
    (by decide) selected_cut_30865

theorem selected_cut_30866 : selected 8 ⟨784604, by decide⟩
    (prefixPartial 13 420983) = some ⟨13, 2, 0, 784604, 420983, 741, 16384⟩ := by
  decide +kernel

theorem context_13_420983_784604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420983 ⟨784604, by decide⟩ :=
  accepted_of_selected 13 420983 ⟨784604, by decide⟩ ⟨13, 2, 0, 784604, 420983, 741, 16384⟩
    (by decide) selected_cut_30866

theorem unmarked_context_12_105245_784605 : frontier 9 ⟨784605, by decide⟩
    (prefixCache 12 105245) (prefixPartial 12 105245) = false := by
  decide +kernel

theorem node_context_12_105245_784605 : EJMOriginalGlobalDAGData.nodes 9 ⟨784605, by decide⟩ =
    .split (coordinate 12) (![⟨784532, by decide⟩,⟨784560, by decide⟩,⟨784593, by decide⟩,⟨784604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105245_784605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105245 ⟨784605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105245
    ⟨784605, by decide⟩ (by decide) (![⟨784532, by decide⟩,⟨784560, by decide⟩,⟨784593, by decide⟩,⟨784604, by decide⟩]) unmarked_context_12_105245_784605 node_context_12_105245_784605
  intro a
  fin_cases a
  · exact context_13_420980_784532
  · exact context_13_420981_784560
  · exact context_13_420982_784593
  · exact context_13_420983_784604

theorem selected_cut_30867 : selected 8 ⟨784626, by decide⟩
    (prefixPartial 13 420984) = some ⟨13, 2, 0, 784626, 420984, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_420984_784626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420984 ⟨784626, by decide⟩ :=
  accepted_of_selected 13 420984 ⟨784626, by decide⟩ ⟨13, 2, 0, 784626, 420984, 1369, 16384⟩
    (by decide) selected_cut_30867

theorem selected_cut_30868 : selected 8 ⟨784656, by decide⟩
    (prefixPartial 13 420985) = some ⟨13, 2, 0, 784656, 420985, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_420985_784656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420985 ⟨784656, by decide⟩ :=
  accepted_of_selected 13 420985 ⟨784656, by decide⟩ ⟨13, 2, 0, 784656, 420985, 1861, 16384⟩
    (by decide) selected_cut_30868

theorem selected_cut_30869 : selected 8 ⟨784690, by decide⟩
    (prefixPartial 13 420986) = some ⟨13, 2, 0, 784690, 420986, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_420986_784690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420986 ⟨784690, by decide⟩ :=
  accepted_of_selected 13 420986 ⟨784690, by decide⟩ ⟨13, 2, 0, 784690, 420986, 1325, 16384⟩
    (by decide) selected_cut_30869

theorem selected_cut_30870 : selected 8 ⟨784696, by decide⟩
    (prefixPartial 13 420987) = some ⟨13, 2, 0, 784696, 420987, 685, 16384⟩ := by
  decide +kernel

theorem context_13_420987_784696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420987 ⟨784696, by decide⟩ :=
  accepted_of_selected 13 420987 ⟨784696, by decide⟩ ⟨13, 2, 0, 784696, 420987, 685, 16384⟩
    (by decide) selected_cut_30870

theorem unmarked_context_12_105246_784697 : frontier 9 ⟨784697, by decide⟩
    (prefixCache 12 105246) (prefixPartial 12 105246) = false := by
  decide +kernel

theorem node_context_12_105246_784697 : EJMOriginalGlobalDAGData.nodes 9 ⟨784697, by decide⟩ =
    .split (coordinate 12) (![⟨784626, by decide⟩,⟨784656, by decide⟩,⟨784690, by decide⟩,⟨784696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105246_784697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105246 ⟨784697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105246
    ⟨784697, by decide⟩ (by decide) (![⟨784626, by decide⟩,⟨784656, by decide⟩,⟨784690, by decide⟩,⟨784696, by decide⟩]) unmarked_context_12_105246_784697 node_context_12_105246_784697
  intro a
  fin_cases a
  · exact context_13_420984_784626
  · exact context_13_420985_784656
  · exact context_13_420986_784690
  · exact context_13_420987_784696

theorem selected_cut_30871 : selected 8 ⟨784733, by decide⟩
    (prefixPartial 13 420988) = some ⟨13, 2, 0, 784733, 420988, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_420988_784733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420988 ⟨784733, by decide⟩ :=
  accepted_of_selected 13 420988 ⟨784733, by decide⟩ ⟨13, 2, 0, 784733, 420988, 2113, 16384⟩
    (by decide) selected_cut_30871

theorem selected_cut_30872 : selected 8 ⟨784777, by decide⟩
    (prefixPartial 13 420989) = some ⟨13, 2, 0, 784777, 420989, 2689, 16384⟩ := by
  decide +kernel

theorem context_13_420989_784777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420989 ⟨784777, by decide⟩ :=
  accepted_of_selected 13 420989 ⟨784777, by decide⟩ ⟨13, 2, 0, 784777, 420989, 2689, 16384⟩
    (by decide) selected_cut_30872

theorem selected_cut_30873 : selected 8 ⟨784859, by decide⟩
    (prefixPartial 13 420990) = some ⟨13, 2, 0, 784859, 420990, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_420990_784859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420990 ⟨784859, by decide⟩ :=
  accepted_of_selected 13 420990 ⟨784859, by decide⟩ ⟨13, 2, 0, 784859, 420990, 2253, 16384⟩
    (by decide) selected_cut_30873

theorem selected_cut_30874 : selected 8 ⟨784878, by decide⟩
    (prefixPartial 13 420991) = some ⟨13, 2, 0, 784878, 420991, 989, 16384⟩ := by
  decide +kernel

theorem context_13_420991_784878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420991 ⟨784878, by decide⟩ :=
  accepted_of_selected 13 420991 ⟨784878, by decide⟩ ⟨13, 2, 0, 784878, 420991, 989, 16384⟩
    (by decide) selected_cut_30874

theorem unmarked_context_12_105247_784879 : frontier 9 ⟨784879, by decide⟩
    (prefixCache 12 105247) (prefixPartial 12 105247) = false := by
  decide +kernel

theorem node_context_12_105247_784879 : EJMOriginalGlobalDAGData.nodes 9 ⟨784879, by decide⟩ =
    .split (coordinate 12) (![⟨784733, by decide⟩,⟨784777, by decide⟩,⟨784859, by decide⟩,⟨784878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105247_784879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105247 ⟨784879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105247
    ⟨784879, by decide⟩ (by decide) (![⟨784733, by decide⟩,⟨784777, by decide⟩,⟨784859, by decide⟩,⟨784878, by decide⟩]) unmarked_context_12_105247_784879 node_context_12_105247_784879
  intro a
  fin_cases a
  · exact context_13_420988_784733
  · exact context_13_420989_784777
  · exact context_13_420990_784859
  · exact context_13_420991_784878

theorem unmarked_context_11_26311_784880 : frontier 10 ⟨784880, by decide⟩
    (prefixCache 11 26311) (prefixPartial 11 26311) = false := by
  decide +kernel

theorem node_context_11_26311_784880 : EJMOriginalGlobalDAGData.nodes 10 ⟨784880, by decide⟩ =
    .split (coordinate 11) (![⟨784506, by decide⟩,⟨784605, by decide⟩,⟨784697, by decide⟩,⟨784879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26311_784880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26311 ⟨784880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26311
    ⟨784880, by decide⟩ (by decide) (![⟨784506, by decide⟩,⟨784605, by decide⟩,⟨784697, by decide⟩,⟨784879, by decide⟩]) unmarked_context_11_26311_784880 node_context_11_26311_784880
  intro a
  fin_cases a
  · exact context_12_105244_784506
  · exact context_12_105245_784605
  · exact context_12_105246_784697
  · exact context_12_105247_784879

theorem unmarked_context_10_6577_784881 : frontier 11 ⟨784881, by decide⟩
    (prefixCache 10 6577) (prefixPartial 10 6577) = false := by
  decide +kernel

theorem node_context_10_6577_784881 : EJMOriginalGlobalDAGData.nodes 11 ⟨784881, by decide⟩ =
    .split (coordinate 10) (![⟨783699, by decide⟩,⟨784081, by decide⟩,⟨784432, by decide⟩,⟨784880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6577_784881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6577 ⟨784881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6577
    ⟨784881, by decide⟩ (by decide) (![⟨783699, by decide⟩,⟨784081, by decide⟩,⟨784432, by decide⟩,⟨784880, by decide⟩]) unmarked_context_10_6577_784881 node_context_10_6577_784881
  intro a
  fin_cases a
  · exact context_11_26308_783699
  · exact context_11_26309_784081
  · exact context_11_26310_784432
  · exact context_11_26311_784880

theorem selected_cut_30875 : selected 9 ⟨784949, by decide⟩
    (prefixPartial 12 105248) = some ⟨12, 2, 0, 784949, 105248, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_105248_784949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105248 ⟨784949, by decide⟩ :=
  accepted_of_selected 12 105248 ⟨784949, by decide⟩ ⟨12, 2, 0, 784949, 105248, 3809, 65536⟩
    (by decide) selected_cut_30875

theorem selected_cut_30876 : selected 8 ⟨784979, by decide⟩
    (prefixPartial 13 420996) = some ⟨13, 2, 0, 784979, 420996, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_420996_784979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420996 ⟨784979, by decide⟩ :=
  accepted_of_selected 13 420996 ⟨784979, by decide⟩ ⟨13, 2, 0, 784979, 420996, 1193, 16384⟩
    (by decide) selected_cut_30876

theorem selected_cut_30877 : selected 8 ⟨785002, by decide⟩
    (prefixPartial 13 420997) = some ⟨13, 2, 0, 785002, 420997, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_420997_785002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420997 ⟨785002, by decide⟩ :=
  accepted_of_selected 13 420997 ⟨785002, by decide⟩ ⟨13, 2, 0, 785002, 420997, 1769, 16384⟩
    (by decide) selected_cut_30877

theorem selected_cut_30878 : selected 8 ⟨785020, by decide⟩
    (prefixPartial 13 420998) = some ⟨13, 2, 0, 785020, 420998, 953, 16384⟩ := by
  decide +kernel

theorem context_13_420998_785020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420998 ⟨785020, by decide⟩ :=
  accepted_of_selected 13 420998 ⟨785020, by decide⟩ ⟨13, 2, 0, 785020, 420998, 953, 16384⟩
    (by decide) selected_cut_30878

theorem selected_cut_30879 : selected 8 ⟨785027, by decide⟩
    (prefixPartial 13 420999) = some ⟨13, 2, 0, 785027, 420999, 693, 16384⟩ := by
  decide +kernel

theorem context_13_420999_785027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420999 ⟨785027, by decide⟩ :=
  accepted_of_selected 13 420999 ⟨785027, by decide⟩ ⟨13, 2, 0, 785027, 420999, 693, 16384⟩
    (by decide) selected_cut_30879

theorem unmarked_context_12_105249_785028 : frontier 9 ⟨785028, by decide⟩
    (prefixCache 12 105249) (prefixPartial 12 105249) = false := by
  decide +kernel

theorem node_context_12_105249_785028 : EJMOriginalGlobalDAGData.nodes 9 ⟨785028, by decide⟩ =
    .split (coordinate 12) (![⟨784979, by decide⟩,⟨785002, by decide⟩,⟨785020, by decide⟩,⟨785027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105249_785028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105249 ⟨785028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105249
    ⟨785028, by decide⟩ (by decide) (![⟨784979, by decide⟩,⟨785002, by decide⟩,⟨785020, by decide⟩,⟨785027, by decide⟩]) unmarked_context_12_105249_785028 node_context_12_105249_785028
  intro a
  fin_cases a
  · exact context_13_420996_784979
  · exact context_13_420997_785002
  · exact context_13_420998_785020
  · exact context_13_420999_785027

theorem selected_cut_30880 : selected 8 ⟨785051, by decide⟩
    (prefixPartial 13 421000) = some ⟨13, 2, 0, 785051, 421000, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_421000_785051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421000 ⟨785051, by decide⟩ :=
  accepted_of_selected 13 421000 ⟨785051, by decide⟩ ⟨13, 2, 0, 785051, 421000, 1121, 16384⟩
    (by decide) selected_cut_30880

theorem selected_cut_30881 : selected 8 ⟨785074, by decide⟩
    (prefixPartial 13 421001) = some ⟨13, 2, 0, 785074, 421001, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_421001_785074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421001 ⟨785074, by decide⟩ :=
  accepted_of_selected 13 421001 ⟨785074, by decide⟩ ⟨13, 2, 0, 785074, 421001, 1689, 16384⟩
    (by decide) selected_cut_30881

theorem selected_cut_30882 : selected 8 ⟨785099, by decide⟩
    (prefixPartial 13 421002) = some ⟨13, 2, 0, 785099, 421002, 957, 16384⟩ := by
  decide +kernel

theorem context_13_421002_785099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421002 ⟨785099, by decide⟩ :=
  accepted_of_selected 13 421002 ⟨785099, by decide⟩ ⟨13, 2, 0, 785099, 421002, 957, 16384⟩
    (by decide) selected_cut_30882

theorem selected_cut_30883 : selected 8 ⟨785103, by decide⟩
    (prefixPartial 13 421003) = some ⟨13, 2, 0, 785103, 421003, 585, 16384⟩ := by
  decide +kernel

theorem context_13_421003_785103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421003 ⟨785103, by decide⟩ :=
  accepted_of_selected 13 421003 ⟨785103, by decide⟩ ⟨13, 2, 0, 785103, 421003, 585, 16384⟩
    (by decide) selected_cut_30883

theorem unmarked_context_12_105250_785104 : frontier 9 ⟨785104, by decide⟩
    (prefixCache 12 105250) (prefixPartial 12 105250) = false := by
  decide +kernel

theorem node_context_12_105250_785104 : EJMOriginalGlobalDAGData.nodes 9 ⟨785104, by decide⟩ =
    .split (coordinate 12) (![⟨785051, by decide⟩,⟨785074, by decide⟩,⟨785099, by decide⟩,⟨785103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105250_785104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105250 ⟨785104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105250
    ⟨785104, by decide⟩ (by decide) (![⟨785051, by decide⟩,⟨785074, by decide⟩,⟨785099, by decide⟩,⟨785103, by decide⟩]) unmarked_context_12_105250_785104 node_context_12_105250_785104
  intro a
  fin_cases a
  · exact context_13_421000_785051
  · exact context_13_421001_785074
  · exact context_13_421002_785099
  · exact context_13_421003_785103

theorem selected_cut_30884 : selected 8 ⟨785121, by decide⟩
    (prefixPartial 13 421004) = some ⟨13, 2, 0, 785121, 421004, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_421004_785121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421004 ⟨785121, by decide⟩ :=
  accepted_of_selected 13 421004 ⟨785121, by decide⟩ ⟨13, 2, 0, 785121, 421004, 1009, 16384⟩
    (by decide) selected_cut_30884

theorem selected_cut_30885 : selected 8 ⟨785139, by decide⟩
    (prefixPartial 13 421005) = some ⟨13, 2, 0, 785139, 421005, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_421005_785139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421005 ⟨785139, by decide⟩ :=
  accepted_of_selected 13 421005 ⟨785139, by decide⟩ ⟨13, 2, 0, 785139, 421005, 1557, 16384⟩
    (by decide) selected_cut_30885

theorem selected_cut_30886 : selected 8 ⟨785159, by decide⟩
    (prefixPartial 13 421006) = some ⟨13, 2, 0, 785159, 421006, 921, 16384⟩ := by
  decide +kernel

theorem context_13_421006_785159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421006 ⟨785159, by decide⟩ :=
  accepted_of_selected 13 421006 ⟨785159, by decide⟩ ⟨13, 2, 0, 785159, 421006, 921, 16384⟩
    (by decide) selected_cut_30886

theorem selected_cut_30887 : selected 8 ⟨785167, by decide⟩
    (prefixPartial 13 421007) = some ⟨13, 2, 0, 785167, 421007, 645, 16384⟩ := by
  decide +kernel

theorem context_13_421007_785167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421007 ⟨785167, by decide⟩ :=
  accepted_of_selected 13 421007 ⟨785167, by decide⟩ ⟨13, 2, 0, 785167, 421007, 645, 16384⟩
    (by decide) selected_cut_30887

theorem unmarked_context_12_105251_785168 : frontier 9 ⟨785168, by decide⟩
    (prefixCache 12 105251) (prefixPartial 12 105251) = false := by
  decide +kernel

theorem node_context_12_105251_785168 : EJMOriginalGlobalDAGData.nodes 9 ⟨785168, by decide⟩ =
    .split (coordinate 12) (![⟨785121, by decide⟩,⟨785139, by decide⟩,⟨785159, by decide⟩,⟨785167, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105251_785168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105251 ⟨785168, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105251
    ⟨785168, by decide⟩ (by decide) (![⟨785121, by decide⟩,⟨785139, by decide⟩,⟨785159, by decide⟩,⟨785167, by decide⟩]) unmarked_context_12_105251_785168 node_context_12_105251_785168
  intro a
  fin_cases a
  · exact context_13_421004_785121
  · exact context_13_421005_785139
  · exact context_13_421006_785159
  · exact context_13_421007_785167

theorem unmarked_context_11_26312_785169 : frontier 10 ⟨785169, by decide⟩
    (prefixCache 11 26312) (prefixPartial 11 26312) = false := by
  decide +kernel

theorem node_context_11_26312_785169 : EJMOriginalGlobalDAGData.nodes 10 ⟨785169, by decide⟩ =
    .split (coordinate 11) (![⟨784949, by decide⟩,⟨785028, by decide⟩,⟨785104, by decide⟩,⟨785168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26312_785169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26312 ⟨785169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26312
    ⟨785169, by decide⟩ (by decide) (![⟨784949, by decide⟩,⟨785028, by decide⟩,⟨785104, by decide⟩,⟨785168, by decide⟩]) unmarked_context_11_26312_785169 node_context_11_26312_785169
  intro a
  fin_cases a
  · exact context_12_105248_784949
  · exact context_12_105249_785028
  · exact context_12_105250_785104
  · exact context_12_105251_785168

theorem selected_cut_30888 : selected 8 ⟨785192, by decide⟩
    (prefixPartial 13 421008) = some ⟨13, 2, 0, 785192, 421008, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_421008_785192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421008 ⟨785192, by decide⟩ :=
  accepted_of_selected 13 421008 ⟨785192, by decide⟩ ⟨13, 2, 0, 785192, 421008, 1065, 16384⟩
    (by decide) selected_cut_30888

theorem selected_cut_30889 : selected 8 ⟨785225, by decide⟩
    (prefixPartial 13 421009) = some ⟨13, 2, 0, 785225, 421009, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_421009_785225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421009 ⟨785225, by decide⟩ :=
  accepted_of_selected 13 421009 ⟨785225, by decide⟩ ⟨13, 2, 0, 785225, 421009, 1813, 16384⟩
    (by decide) selected_cut_30889

theorem selected_cut_30890 : selected 8 ⟨785246, by decide⟩
    (prefixPartial 13 421010) = some ⟨13, 2, 0, 785246, 421010, 873, 16384⟩ := by
  decide +kernel

theorem context_13_421010_785246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421010 ⟨785246, by decide⟩ :=
  accepted_of_selected 13 421010 ⟨785246, by decide⟩ ⟨13, 2, 0, 785246, 421010, 873, 16384⟩
    (by decide) selected_cut_30890

theorem selected_cut_30891 : selected 8 ⟨785254, by decide⟩
    (prefixPartial 13 421011) = some ⟨13, 2, 0, 785254, 421011, 837, 16384⟩ := by
  decide +kernel

theorem context_13_421011_785254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421011 ⟨785254, by decide⟩ :=
  accepted_of_selected 13 421011 ⟨785254, by decide⟩ ⟨13, 2, 0, 785254, 421011, 837, 16384⟩
    (by decide) selected_cut_30891

theorem unmarked_context_12_105252_785255 : frontier 9 ⟨785255, by decide⟩
    (prefixCache 12 105252) (prefixPartial 12 105252) = false := by
  decide +kernel

theorem node_context_12_105252_785255 : EJMOriginalGlobalDAGData.nodes 9 ⟨785255, by decide⟩ =
    .split (coordinate 12) (![⟨785192, by decide⟩,⟨785225, by decide⟩,⟨785246, by decide⟩,⟨785254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105252_785255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105252 ⟨785255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105252
    ⟨785255, by decide⟩ (by decide) (![⟨785192, by decide⟩,⟨785225, by decide⟩,⟨785246, by decide⟩,⟨785254, by decide⟩]) unmarked_context_12_105252_785255 node_context_12_105252_785255
  intro a
  fin_cases a
  · exact context_13_421008_785192
  · exact context_13_421009_785225
  · exact context_13_421010_785246
  · exact context_13_421011_785254

theorem selected_cut_30892 : selected 8 ⟨785276, by decide⟩
    (prefixPartial 13 421012) = some ⟨13, 2, 0, 785276, 421012, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_421012_785276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421012 ⟨785276, by decide⟩ :=
  accepted_of_selected 13 421012 ⟨785276, by decide⟩ ⟨13, 2, 0, 785276, 421012, 1061, 16384⟩
    (by decide) selected_cut_30892

theorem selected_cut_30893 : selected 8 ⟨785297, by decide⟩
    (prefixPartial 13 421013) = some ⟨13, 2, 0, 785297, 421013, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_421013_785297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421013 ⟨785297, by decide⟩ :=
  accepted_of_selected 13 421013 ⟨785297, by decide⟩ ⟨13, 2, 0, 785297, 421013, 1657, 16384⟩
    (by decide) selected_cut_30893

theorem selected_cut_30894 : selected 8 ⟨785315, by decide⟩
    (prefixPartial 13 421014) = some ⟨13, 2, 0, 785315, 421014, 873, 16384⟩ := by
  decide +kernel

theorem context_13_421014_785315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421014 ⟨785315, by decide⟩ :=
  accepted_of_selected 13 421014 ⟨785315, by decide⟩ ⟨13, 2, 0, 785315, 421014, 873, 16384⟩
    (by decide) selected_cut_30894

theorem selected_cut_30895 : selected 8 ⟨785321, by decide⟩
    (prefixPartial 13 421015) = some ⟨13, 2, 0, 785321, 421015, 785, 16384⟩ := by
  decide +kernel

theorem context_13_421015_785321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421015 ⟨785321, by decide⟩ :=
  accepted_of_selected 13 421015 ⟨785321, by decide⟩ ⟨13, 2, 0, 785321, 421015, 785, 16384⟩
    (by decide) selected_cut_30895

theorem unmarked_context_12_105253_785322 : frontier 9 ⟨785322, by decide⟩
    (prefixCache 12 105253) (prefixPartial 12 105253) = false := by
  decide +kernel

theorem node_context_12_105253_785322 : EJMOriginalGlobalDAGData.nodes 9 ⟨785322, by decide⟩ =
    .split (coordinate 12) (![⟨785276, by decide⟩,⟨785297, by decide⟩,⟨785315, by decide⟩,⟨785321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105253_785322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105253 ⟨785322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105253
    ⟨785322, by decide⟩ (by decide) (![⟨785276, by decide⟩,⟨785297, by decide⟩,⟨785315, by decide⟩,⟨785321, by decide⟩]) unmarked_context_12_105253_785322 node_context_12_105253_785322
  intro a
  fin_cases a
  · exact context_13_421012_785276
  · exact context_13_421013_785297
  · exact context_13_421014_785315
  · exact context_13_421015_785321

theorem selected_cut_30896 : selected 8 ⟨785337, by decide⟩
    (prefixPartial 13 421016) = some ⟨13, 2, 0, 785337, 421016, 909, 16384⟩ := by
  decide +kernel

theorem context_13_421016_785337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421016 ⟨785337, by decide⟩ :=
  accepted_of_selected 13 421016 ⟨785337, by decide⟩ ⟨13, 2, 0, 785337, 421016, 909, 16384⟩
    (by decide) selected_cut_30896

theorem selected_cut_30897 : selected 8 ⟨785362, by decide⟩
    (prefixPartial 13 421017) = some ⟨13, 2, 0, 785362, 421017, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_421017_785362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421017 ⟨785362, by decide⟩ :=
  accepted_of_selected 13 421017 ⟨785362, by decide⟩ ⟨13, 2, 0, 785362, 421017, 1837, 16384⟩
    (by decide) selected_cut_30897

theorem selected_cut_30898 : selected 8 ⟨785388, by decide⟩
    (prefixPartial 13 421018) = some ⟨13, 2, 0, 785388, 421018, 921, 16384⟩ := by
  decide +kernel

theorem context_13_421018_785388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421018 ⟨785388, by decide⟩ :=
  accepted_of_selected 13 421018 ⟨785388, by decide⟩ ⟨13, 2, 0, 785388, 421018, 921, 16384⟩
    (by decide) selected_cut_30898

theorem selected_cut_30899 : selected 8 ⟨785394, by decide⟩
    (prefixPartial 13 421019) = some ⟨13, 2, 0, 785394, 421019, 721, 16384⟩ := by
  decide +kernel

theorem context_13_421019_785394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421019 ⟨785394, by decide⟩ :=
  accepted_of_selected 13 421019 ⟨785394, by decide⟩ ⟨13, 2, 0, 785394, 421019, 721, 16384⟩
    (by decide) selected_cut_30899

theorem unmarked_context_12_105254_785395 : frontier 9 ⟨785395, by decide⟩
    (prefixCache 12 105254) (prefixPartial 12 105254) = false := by
  decide +kernel

theorem node_context_12_105254_785395 : EJMOriginalGlobalDAGData.nodes 9 ⟨785395, by decide⟩ =
    .split (coordinate 12) (![⟨785337, by decide⟩,⟨785362, by decide⟩,⟨785388, by decide⟩,⟨785394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105254_785395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105254 ⟨785395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105254
    ⟨785395, by decide⟩ (by decide) (![⟨785337, by decide⟩,⟨785362, by decide⟩,⟨785388, by decide⟩,⟨785394, by decide⟩]) unmarked_context_12_105254_785395 node_context_12_105254_785395
  intro a
  fin_cases a
  · exact context_13_421016_785337
  · exact context_13_421017_785362
  · exact context_13_421018_785388
  · exact context_13_421019_785394

theorem selected_cut_30900 : selected 9 ⟨785457, by decide⟩
    (prefixPartial 12 105255) = some ⟨12, 2, 0, 785457, 105255, 4053, 65536⟩ := by
  decide +kernel

theorem context_12_105255_785457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105255 ⟨785457, by decide⟩ :=
  accepted_of_selected 12 105255 ⟨785457, by decide⟩ ⟨12, 2, 0, 785457, 105255, 4053, 65536⟩
    (by decide) selected_cut_30900

theorem unmarked_context_11_26313_785458 : frontier 10 ⟨785458, by decide⟩
    (prefixCache 11 26313) (prefixPartial 11 26313) = false := by
  decide +kernel

theorem node_context_11_26313_785458 : EJMOriginalGlobalDAGData.nodes 10 ⟨785458, by decide⟩ =
    .split (coordinate 11) (![⟨785255, by decide⟩,⟨785322, by decide⟩,⟨785395, by decide⟩,⟨785457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26313_785458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26313 ⟨785458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26313
    ⟨785458, by decide⟩ (by decide) (![⟨785255, by decide⟩,⟨785322, by decide⟩,⟨785395, by decide⟩,⟨785457, by decide⟩]) unmarked_context_11_26313_785458 node_context_11_26313_785458
  intro a
  fin_cases a
  · exact context_12_105252_785255
  · exact context_12_105253_785322
  · exact context_12_105254_785395
  · exact context_12_105255_785457

theorem selected_cut_30901 : selected 10 ⟨766338, by decide⟩
    (prefixPartial 11 26314) = some ⟨11, 1, 0, 766338, 26314, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26314_766338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26314 ⟨766338, by decide⟩ :=
  accepted_of_selected 11 26314 ⟨766338, by decide⟩ ⟨11, 1, 0, 766338, 26314, 1, 262144⟩
    (by decide) selected_cut_30901

theorem selected_cut_30902 : selected 9 ⟨785513, by decide⟩
    (prefixPartial 12 105260) = some ⟨12, 2, 0, 785513, 105260, 3789, 65536⟩ := by
  decide +kernel

theorem context_12_105260_785513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105260 ⟨785513, by decide⟩ :=
  accepted_of_selected 12 105260 ⟨785513, by decide⟩ ⟨12, 2, 0, 785513, 105260, 3789, 65536⟩
    (by decide) selected_cut_30902

theorem selected_cut_30903 : selected 9 ⟨785577, by decide⟩
    (prefixPartial 12 105261) = some ⟨12, 2, 0, 785577, 105261, 3937, 65536⟩ := by
  decide +kernel

theorem context_12_105261_785577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105261 ⟨785577, by decide⟩ :=
  accepted_of_selected 12 105261 ⟨785577, by decide⟩ ⟨12, 2, 0, 785577, 105261, 3937, 65536⟩
    (by decide) selected_cut_30903

theorem selected_cut_30904 : selected 9 ⟨785638, by decide⟩
    (prefixPartial 12 105262) = some ⟨12, 2, 0, 785638, 105262, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_105262_785638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105262 ⟨785638, by decide⟩ :=
  accepted_of_selected 12 105262 ⟨785638, by decide⟩ ⟨12, 2, 0, 785638, 105262, 3881, 65536⟩
    (by decide) selected_cut_30904

theorem selected_cut_30905 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 105263) = some ⟨12, 1, 0, 758968, 105263, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105263_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105263 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 105263 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 105263, 1, 65536⟩
    (by decide) selected_cut_30905

theorem unmarked_context_11_26315_785639 : frontier 10 ⟨785639, by decide⟩
    (prefixCache 11 26315) (prefixPartial 11 26315) = false := by
  decide +kernel

theorem node_context_11_26315_785639 : EJMOriginalGlobalDAGData.nodes 10 ⟨785639, by decide⟩ =
    .split (coordinate 11) (![⟨785513, by decide⟩,⟨785577, by decide⟩,⟨785638, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26315_785639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26315 ⟨785639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26315
    ⟨785639, by decide⟩ (by decide) (![⟨785513, by decide⟩,⟨785577, by decide⟩,⟨785638, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_26315_785639 node_context_11_26315_785639
  intro a
  fin_cases a
  · exact context_12_105260_785513
  · exact context_12_105261_785577
  · exact context_12_105262_785638
  · exact context_12_105263_758968

theorem unmarked_context_10_6578_785640 : frontier 11 ⟨785640, by decide⟩
    (prefixCache 10 6578) (prefixPartial 10 6578) = false := by
  decide +kernel

theorem node_context_10_6578_785640 : EJMOriginalGlobalDAGData.nodes 11 ⟨785640, by decide⟩ =
    .split (coordinate 10) (![⟨785169, by decide⟩,⟨785458, by decide⟩,⟨766338, by decide⟩,⟨785639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6578_785640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6578 ⟨785640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6578
    ⟨785640, by decide⟩ (by decide) (![⟨785169, by decide⟩,⟨785458, by decide⟩,⟨766338, by decide⟩,⟨785639, by decide⟩]) unmarked_context_10_6578_785640 node_context_10_6578_785640
  intro a
  fin_cases a
  · exact context_11_26312_785169
  · exact context_11_26313_785458
  · exact context_11_26314_766338
  · exact context_11_26315_785639

theorem selected_cut_30906 : selected 9 ⟨785707, by decide⟩
    (prefixPartial 12 105264) = some ⟨12, 2, 0, 785707, 105264, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_105264_785707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105264 ⟨785707, by decide⟩ :=
  accepted_of_selected 12 105264 ⟨785707, by decide⟩ ⟨12, 2, 0, 785707, 105264, 3401, 65536⟩
    (by decide) selected_cut_30906

theorem selected_cut_30907 : selected 8 ⟨785720, by decide⟩
    (prefixPartial 13 421060) = some ⟨13, 2, 0, 785720, 421060, 557, 16384⟩ := by
  decide +kernel

theorem context_13_421060_785720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421060 ⟨785720, by decide⟩ :=
  accepted_of_selected 13 421060 ⟨785720, by decide⟩ ⟨13, 2, 0, 785720, 421060, 557, 16384⟩
    (by decide) selected_cut_30907

theorem selected_cut_30908 : selected 8 ⟨785775, by decide⟩
    (prefixPartial 13 421061) = some ⟨13, 2, 0, 785775, 421061, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_421061_785775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421061 ⟨785775, by decide⟩ :=
  accepted_of_selected 13 421061 ⟨785775, by decide⟩ ⟨13, 2, 0, 785775, 421061, 1953, 16384⟩
    (by decide) selected_cut_30908

theorem selected_cut_30909 : selected 8 ⟨785790, by decide⟩
    (prefixPartial 13 421062) = some ⟨13, 2, 0, 785790, 421062, 865, 16384⟩ := by
  decide +kernel

theorem context_13_421062_785790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421062 ⟨785790, by decide⟩ :=
  accepted_of_selected 13 421062 ⟨785790, by decide⟩ ⟨13, 2, 0, 785790, 421062, 865, 16384⟩
    (by decide) selected_cut_30909

theorem selected_cut_30910 : selected 8 ⟨785802, by decide⟩
    (prefixPartial 13 421063) = some ⟨13, 2, 0, 785802, 421063, 821, 16384⟩ := by
  decide +kernel

theorem context_13_421063_785802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421063 ⟨785802, by decide⟩ :=
  accepted_of_selected 13 421063 ⟨785802, by decide⟩ ⟨13, 2, 0, 785802, 421063, 821, 16384⟩
    (by decide) selected_cut_30910

theorem unmarked_context_12_105265_785803 : frontier 9 ⟨785803, by decide⟩
    (prefixCache 12 105265) (prefixPartial 12 105265) = false := by
  decide +kernel

theorem node_context_12_105265_785803 : EJMOriginalGlobalDAGData.nodes 9 ⟨785803, by decide⟩ =
    .split (coordinate 12) (![⟨785720, by decide⟩,⟨785775, by decide⟩,⟨785790, by decide⟩,⟨785802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105265_785803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105265 ⟨785803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105265
    ⟨785803, by decide⟩ (by decide) (![⟨785720, by decide⟩,⟨785775, by decide⟩,⟨785790, by decide⟩,⟨785802, by decide⟩]) unmarked_context_12_105265_785803 node_context_12_105265_785803
  intro a
  fin_cases a
  · exact context_13_421060_785720
  · exact context_13_421061_785775
  · exact context_13_421062_785790
  · exact context_13_421063_785802

theorem selected_cut_30911 : selected 9 ⟨785872, by decide⟩
    (prefixPartial 12 105266) = some ⟨12, 2, 0, 785872, 105266, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_105266_785872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105266 ⟨785872, by decide⟩ :=
  accepted_of_selected 12 105266 ⟨785872, by decide⟩ ⟨12, 2, 0, 785872, 105266, 3933, 65536⟩
    (by decide) selected_cut_30911

theorem selected_cut_30912 : selected 9 ⟨785927, by decide⟩
    (prefixPartial 12 105267) = some ⟨12, 2, 0, 785927, 105267, 3833, 65536⟩ := by
  decide +kernel

theorem context_12_105267_785927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105267 ⟨785927, by decide⟩ :=
  accepted_of_selected 12 105267 ⟨785927, by decide⟩ ⟨12, 2, 0, 785927, 105267, 3833, 65536⟩
    (by decide) selected_cut_30912

theorem unmarked_context_11_26316_785928 : frontier 10 ⟨785928, by decide⟩
    (prefixCache 11 26316) (prefixPartial 11 26316) = false := by
  decide +kernel

theorem node_context_11_26316_785928 : EJMOriginalGlobalDAGData.nodes 10 ⟨785928, by decide⟩ =
    .split (coordinate 11) (![⟨785707, by decide⟩,⟨785803, by decide⟩,⟨785872, by decide⟩,⟨785927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26316_785928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26316 ⟨785928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26316
    ⟨785928, by decide⟩ (by decide) (![⟨785707, by decide⟩,⟨785803, by decide⟩,⟨785872, by decide⟩,⟨785927, by decide⟩]) unmarked_context_11_26316_785928 node_context_11_26316_785928
  intro a
  fin_cases a
  · exact context_12_105264_785707
  · exact context_12_105265_785803
  · exact context_12_105266_785872
  · exact context_12_105267_785927

theorem selected_cut_30913 : selected 9 ⟨786007, by decide⟩
    (prefixPartial 12 105268) = some ⟨12, 2, 0, 786007, 105268, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_105268_786007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105268 ⟨786007, by decide⟩ :=
  accepted_of_selected 12 105268 ⟨786007, by decide⟩ ⟨12, 2, 0, 786007, 105268, 3777, 65536⟩
    (by decide) selected_cut_30913

theorem selected_cut_30914 : selected 9 ⟨786092, by decide⟩
    (prefixPartial 12 105269) = some ⟨12, 2, 0, 786092, 105269, 3813, 65536⟩ := by
  decide +kernel

theorem context_12_105269_786092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105269 ⟨786092, by decide⟩ :=
  accepted_of_selected 12 105269 ⟨786092, by decide⟩ ⟨12, 2, 0, 786092, 105269, 3813, 65536⟩
    (by decide) selected_cut_30914

theorem selected_cut_30915 : selected 9 ⟨786161, by decide⟩
    (prefixPartial 12 105270) = some ⟨12, 2, 0, 786161, 105270, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_105270_786161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105270 ⟨786161, by decide⟩ :=
  accepted_of_selected 12 105270 ⟨786161, by decide⟩ ⟨12, 2, 0, 786161, 105270, 3705, 65536⟩
    (by decide) selected_cut_30915

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
