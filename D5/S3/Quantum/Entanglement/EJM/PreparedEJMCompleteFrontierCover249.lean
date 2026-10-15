/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover248
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_8_299_603600 : frontier 13 ⟨603600, by decide⟩
    (prefixCache 8 299) (prefixPartial 8 299) = false := by
  decide +kernel

theorem node_context_8_299_603600 : EJMOriginalGlobalDAGData.nodes 13 ⟨603600, by decide⟩ =
    .split (coordinate 8) (![⟨599138, by decide⟩,⟨602107, by decide⟩,⟨603312, by decide⟩,⟨603599, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_299_603600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 299 ⟨603600, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 299
    ⟨603600, by decide⟩ (by decide) (![⟨599138, by decide⟩,⟨602107, by decide⟩,⟨603312, by decide⟩,⟨603599, by decide⟩]) unmarked_context_8_299_603600 node_context_8_299_603600
  intro a
  fin_cases a
  · exact context_9_1196_599138
  · exact context_9_1197_602107
  · exact context_9_1198_603312
  · exact context_9_1199_603599

theorem unmarked_context_7_74_603601 : frontier 14 ⟨603601, by decide⟩
    (prefixCache 7 74) (prefixPartial 7 74) = false := by
  decide +kernel

theorem node_context_7_74_603601 : EJMOriginalGlobalDAGData.nodes 14 ⟨603601, by decide⟩ =
    .split (coordinate 7) (![⟨580333, by decide⟩,⟨587044, by decide⟩,⟨595780, by decide⟩,⟨603600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_74_603601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 74 ⟨603601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 74
    ⟨603601, by decide⟩ (by decide) (![⟨580333, by decide⟩,⟨587044, by decide⟩,⟨595780, by decide⟩,⟨603600, by decide⟩]) unmarked_context_7_74_603601 node_context_7_74_603601
  intro a
  fin_cases a
  · exact context_8_296_580333
  · exact context_8_297_587044
  · exact context_8_298_595780
  · exact context_8_299_603600

theorem selected_cut_23907 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 19200) = some ⟨11, 1, 0, 434745, 19200, 1, 262144⟩ := by
  decide +kernel

theorem context_11_19200_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19200 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 19200 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 19200, 1, 262144⟩
    (by decide) selected_cut_23907

theorem selected_cut_23908 : selected 10 ⟨603786, by decide⟩
    (prefixPartial 11 19201) = some ⟨11, 2, 0, 603786, 19201, 4049, 262144⟩ := by
  decide +kernel

theorem context_11_19201_603786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19201 ⟨603786, by decide⟩ :=
  accepted_of_selected 11 19201 ⟨603786, by decide⟩ ⟨11, 2, 0, 603786, 19201, 4049, 262144⟩
    (by decide) selected_cut_23908

theorem selected_cut_23909 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 76808) = some ⟨12, 1, 0, 448748, 76808, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76808_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76808 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 76808 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 76808, 1, 65536⟩
    (by decide) selected_cut_23909

theorem selected_cut_23910 : selected 8 ⟨603886, by decide⟩
    (prefixPartial 13 307236) = some ⟨13, 2, 0, 603886, 307236, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_307236_603886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307236 ⟨603886, by decide⟩ :=
  accepted_of_selected 13 307236 ⟨603886, by decide⟩ ⟨13, 2, 0, 603886, 307236, 2765, 16384⟩
    (by decide) selected_cut_23910

theorem selected_cut_23911 : selected 8 ⟨603951, by decide⟩
    (prefixPartial 13 307237) = some ⟨13, 2, 0, 603951, 307237, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_307237_603951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307237 ⟨603951, by decide⟩ :=
  accepted_of_selected 13 307237 ⟨603951, by decide⟩ ⟨13, 2, 0, 603951, 307237, 2757, 16384⟩
    (by decide) selected_cut_23911

theorem selected_cut_23912 : selected 8 ⟨604065, by decide⟩
    (prefixPartial 13 307238) = some ⟨13, 2, 0, 604065, 307238, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_307238_604065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307238 ⟨604065, by decide⟩ :=
  accepted_of_selected 13 307238 ⟨604065, by decide⟩ ⟨13, 2, 0, 604065, 307238, 2593, 16384⟩
    (by decide) selected_cut_23912

theorem selected_cut_23913 : selected 8 ⟨604129, by decide⟩
    (prefixPartial 13 307239) = some ⟨13, 2, 0, 604129, 307239, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_307239_604129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307239 ⟨604129, by decide⟩ :=
  accepted_of_selected 13 307239 ⟨604129, by decide⟩ ⟨13, 2, 0, 604129, 307239, 1025, 16384⟩
    (by decide) selected_cut_23913

theorem unmarked_context_12_76809_604130 : frontier 9 ⟨604130, by decide⟩
    (prefixCache 12 76809) (prefixPartial 12 76809) = false := by
  decide +kernel

theorem node_context_12_76809_604130 : EJMOriginalGlobalDAGData.nodes 9 ⟨604130, by decide⟩ =
    .split (coordinate 12) (![⟨603886, by decide⟩,⟨603951, by decide⟩,⟨604065, by decide⟩,⟨604129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76809_604130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76809 ⟨604130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76809
    ⟨604130, by decide⟩ (by decide) (![⟨603886, by decide⟩,⟨603951, by decide⟩,⟨604065, by decide⟩,⟨604129, by decide⟩]) unmarked_context_12_76809_604130 node_context_12_76809_604130
  intro a
  fin_cases a
  · exact context_13_307236_603886
  · exact context_13_307237_603951
  · exact context_13_307238_604065
  · exact context_13_307239_604129

theorem selected_cut_23914 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 76810) = some ⟨12, 1, 0, 524302, 76810, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76810_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76810 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 76810 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 76810, 1, 65536⟩
    (by decide) selected_cut_23914

theorem selected_cut_23915 : selected 9 ⟨604131, by decide⟩
    (prefixPartial 12 76811) = some ⟨12, 1, 0, 604131, 76811, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76811_604131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76811 ⟨604131, by decide⟩ :=
  accepted_of_selected 12 76811 ⟨604131, by decide⟩ ⟨12, 1, 0, 604131, 76811, 1, 65536⟩
    (by decide) selected_cut_23915

theorem unmarked_context_11_19202_604132 : frontier 10 ⟨604132, by decide⟩
    (prefixCache 11 19202) (prefixPartial 11 19202) = false := by
  decide +kernel

theorem node_context_11_19202_604132 : EJMOriginalGlobalDAGData.nodes 10 ⟨604132, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨604130, by decide⟩,⟨524302, by decide⟩,⟨604131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19202_604132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19202 ⟨604132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19202
    ⟨604132, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨604130, by decide⟩,⟨524302, by decide⟩,⟨604131, by decide⟩]) unmarked_context_11_19202_604132 node_context_11_19202_604132
  intro a
  fin_cases a
  · exact context_12_76808_448748
  · exact context_12_76809_604130
  · exact context_12_76810_524302
  · exact context_12_76811_604131

theorem selected_cut_23916 : selected 10 ⟨604133, by decide⟩
    (prefixPartial 11 19203) = some ⟨11, 2, 0, 604133, 19203, 5, 262144⟩ := by
  decide +kernel

theorem context_11_19203_604133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19203 ⟨604133, by decide⟩ :=
  accepted_of_selected 11 19203 ⟨604133, by decide⟩ ⟨11, 2, 0, 604133, 19203, 5, 262144⟩
    (by decide) selected_cut_23916

theorem unmarked_context_10_4800_604134 : frontier 11 ⟨604134, by decide⟩
    (prefixCache 10 4800) (prefixPartial 10 4800) = false := by
  decide +kernel

theorem node_context_10_4800_604134 : EJMOriginalGlobalDAGData.nodes 11 ⟨604134, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨603786, by decide⟩,⟨604132, by decide⟩,⟨604133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4800_604134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4800 ⟨604134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4800
    ⟨604134, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨603786, by decide⟩,⟨604132, by decide⟩,⟨604133, by decide⟩]) unmarked_context_10_4800_604134 node_context_10_4800_604134
  intro a
  fin_cases a
  · exact context_11_19200_434745
  · exact context_11_19201_603786
  · exact context_11_19202_604132
  · exact context_11_19203_604133

theorem selected_cut_23917 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 76816) = some ⟨12, 1, 0, 435160, 76816, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76816_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76816 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 76816 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 76816, 1, 65536⟩
    (by decide) selected_cut_23917

theorem selected_cut_23918 : selected 8 ⟨604181, by decide⟩
    (prefixPartial 13 307268) = some ⟨13, 2, 0, 604181, 307268, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_307268_604181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307268 ⟨604181, by decide⟩ :=
  accepted_of_selected 13 307268 ⟨604181, by decide⟩ ⟨13, 2, 0, 604181, 307268, 1593, 16384⟩
    (by decide) selected_cut_23918

theorem selected_cut_23919 : selected 8 ⟨604222, by decide⟩
    (prefixPartial 13 307269) = some ⟨13, 2, 0, 604222, 307269, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_307269_604222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307269 ⟨604222, by decide⟩ :=
  accepted_of_selected 13 307269 ⟨604222, by decide⟩ ⟨13, 2, 0, 604222, 307269, 1717, 16384⟩
    (by decide) selected_cut_23919

theorem selected_cut_23920 : selected 8 ⟨604267, by decide⟩
    (prefixPartial 13 307270) = some ⟨13, 2, 0, 604267, 307270, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_307270_604267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307270 ⟨604267, by decide⟩ :=
  accepted_of_selected 13 307270 ⟨604267, by decide⟩ ⟨13, 2, 0, 604267, 307270, 1541, 16384⟩
    (by decide) selected_cut_23920

theorem selected_cut_23921 : selected 8 ⟨604284, by decide⟩
    (prefixPartial 13 307271) = some ⟨13, 2, 0, 604284, 307271, 681, 16384⟩ := by
  decide +kernel

theorem context_13_307271_604284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307271 ⟨604284, by decide⟩ :=
  accepted_of_selected 13 307271 ⟨604284, by decide⟩ ⟨13, 2, 0, 604284, 307271, 681, 16384⟩
    (by decide) selected_cut_23921

theorem unmarked_context_12_76817_604285 : frontier 9 ⟨604285, by decide⟩
    (prefixCache 12 76817) (prefixPartial 12 76817) = false := by
  decide +kernel

theorem node_context_12_76817_604285 : EJMOriginalGlobalDAGData.nodes 9 ⟨604285, by decide⟩ =
    .split (coordinate 12) (![⟨604181, by decide⟩,⟨604222, by decide⟩,⟨604267, by decide⟩,⟨604284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76817_604285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76817 ⟨604285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76817
    ⟨604285, by decide⟩ (by decide) (![⟨604181, by decide⟩,⟨604222, by decide⟩,⟨604267, by decide⟩,⟨604284, by decide⟩]) unmarked_context_12_76817_604285 node_context_12_76817_604285
  intro a
  fin_cases a
  · exact context_13_307268_604181
  · exact context_13_307269_604222
  · exact context_13_307270_604267
  · exact context_13_307271_604284

theorem selected_cut_23922 : selected 8 ⟨604326, by decide⟩
    (prefixPartial 13 307272) = some ⟨13, 2, 0, 604326, 307272, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_307272_604326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307272 ⟨604326, by decide⟩ :=
  accepted_of_selected 13 307272 ⟨604326, by decide⟩ ⟨13, 2, 0, 604326, 307272, 1381, 16384⟩
    (by decide) selected_cut_23922

theorem selected_cut_23923 : selected 8 ⟨604368, by decide⟩
    (prefixPartial 13 307273) = some ⟨13, 2, 0, 604368, 307273, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_307273_604368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307273 ⟨604368, by decide⟩ :=
  accepted_of_selected 13 307273 ⟨604368, by decide⟩ ⟨13, 2, 0, 604368, 307273, 1633, 16384⟩
    (by decide) selected_cut_23923

theorem selected_cut_23924 : selected 8 ⟨604399, by decide⟩
    (prefixPartial 13 307274) = some ⟨13, 2, 0, 604399, 307274, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_307274_604399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307274 ⟨604399, by decide⟩ :=
  accepted_of_selected 13 307274 ⟨604399, by decide⟩ ⟨13, 2, 0, 604399, 307274, 1133, 16384⟩
    (by decide) selected_cut_23924

theorem selected_cut_23925 : selected 8 ⟨604416, by decide⟩
    (prefixPartial 13 307275) = some ⟨13, 2, 0, 604416, 307275, 681, 16384⟩ := by
  decide +kernel

theorem context_13_307275_604416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307275 ⟨604416, by decide⟩ :=
  accepted_of_selected 13 307275 ⟨604416, by decide⟩ ⟨13, 2, 0, 604416, 307275, 681, 16384⟩
    (by decide) selected_cut_23925

theorem unmarked_context_12_76818_604417 : frontier 9 ⟨604417, by decide⟩
    (prefixCache 12 76818) (prefixPartial 12 76818) = false := by
  decide +kernel

theorem node_context_12_76818_604417 : EJMOriginalGlobalDAGData.nodes 9 ⟨604417, by decide⟩ =
    .split (coordinate 12) (![⟨604326, by decide⟩,⟨604368, by decide⟩,⟨604399, by decide⟩,⟨604416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76818_604417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76818 ⟨604417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76818
    ⟨604417, by decide⟩ (by decide) (![⟨604326, by decide⟩,⟨604368, by decide⟩,⟨604399, by decide⟩,⟨604416, by decide⟩]) unmarked_context_12_76818_604417 node_context_12_76818_604417
  intro a
  fin_cases a
  · exact context_13_307272_604326
  · exact context_13_307273_604368
  · exact context_13_307274_604399
  · exact context_13_307275_604416

theorem selected_cut_23926 : selected 8 ⟨604460, by decide⟩
    (prefixPartial 13 307276) = some ⟨13, 2, 0, 604460, 307276, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_307276_604460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307276 ⟨604460, by decide⟩ :=
  accepted_of_selected 13 307276 ⟨604460, by decide⟩ ⟨13, 2, 0, 604460, 307276, 1449, 16384⟩
    (by decide) selected_cut_23926

theorem selected_cut_23927 : selected 8 ⟨604491, by decide⟩
    (prefixPartial 13 307277) = some ⟨13, 2, 0, 604491, 307277, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_307277_604491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307277 ⟨604491, by decide⟩ :=
  accepted_of_selected 13 307277 ⟨604491, by decide⟩ ⟨13, 2, 0, 604491, 307277, 1729, 16384⟩
    (by decide) selected_cut_23927

theorem selected_cut_23928 : selected 8 ⟨604520, by decide⟩
    (prefixPartial 13 307278) = some ⟨13, 2, 0, 604520, 307278, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_307278_604520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307278 ⟨604520, by decide⟩ :=
  accepted_of_selected 13 307278 ⟨604520, by decide⟩ ⟨13, 2, 0, 604520, 307278, 1489, 16384⟩
    (by decide) selected_cut_23928

theorem selected_cut_23929 : selected 8 ⟨604534, by decide⟩
    (prefixPartial 13 307279) = some ⟨13, 2, 0, 604534, 307279, 673, 16384⟩ := by
  decide +kernel

theorem context_13_307279_604534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307279 ⟨604534, by decide⟩ :=
  accepted_of_selected 13 307279 ⟨604534, by decide⟩ ⟨13, 2, 0, 604534, 307279, 673, 16384⟩
    (by decide) selected_cut_23929

theorem unmarked_context_12_76819_604535 : frontier 9 ⟨604535, by decide⟩
    (prefixCache 12 76819) (prefixPartial 12 76819) = false := by
  decide +kernel

theorem node_context_12_76819_604535 : EJMOriginalGlobalDAGData.nodes 9 ⟨604535, by decide⟩ =
    .split (coordinate 12) (![⟨604460, by decide⟩,⟨604491, by decide⟩,⟨604520, by decide⟩,⟨604534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76819_604535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76819 ⟨604535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76819
    ⟨604535, by decide⟩ (by decide) (![⟨604460, by decide⟩,⟨604491, by decide⟩,⟨604520, by decide⟩,⟨604534, by decide⟩]) unmarked_context_12_76819_604535 node_context_12_76819_604535
  intro a
  fin_cases a
  · exact context_13_307276_604460
  · exact context_13_307277_604491
  · exact context_13_307278_604520
  · exact context_13_307279_604534

theorem unmarked_context_11_19204_604536 : frontier 10 ⟨604536, by decide⟩
    (prefixCache 11 19204) (prefixPartial 11 19204) = false := by
  decide +kernel

theorem node_context_11_19204_604536 : EJMOriginalGlobalDAGData.nodes 10 ⟨604536, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨604285, by decide⟩,⟨604417, by decide⟩,⟨604535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19204_604536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19204 ⟨604536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19204
    ⟨604536, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨604285, by decide⟩,⟨604417, by decide⟩,⟨604535, by decide⟩]) unmarked_context_11_19204_604536 node_context_11_19204_604536
  intro a
  fin_cases a
  · exact context_12_76816_435160
  · exact context_12_76817_604285
  · exact context_12_76818_604417
  · exact context_12_76819_604535

theorem selected_cut_23930 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 76820) = some ⟨12, 1, 0, 435160, 76820, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76820_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76820 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 76820 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 76820, 1, 65536⟩
    (by decide) selected_cut_23930

theorem selected_cut_23931 : selected 8 ⟨604582, by decide⟩
    (prefixPartial 13 307284) = some ⟨13, 2, 0, 604582, 307284, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_307284_604582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307284 ⟨604582, by decide⟩ :=
  accepted_of_selected 13 307284 ⟨604582, by decide⟩ ⟨13, 2, 0, 604582, 307284, 1589, 16384⟩
    (by decide) selected_cut_23931

theorem selected_cut_23932 : selected 8 ⟨604622, by decide⟩
    (prefixPartial 13 307285) = some ⟨13, 2, 0, 604622, 307285, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_307285_604622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307285 ⟨604622, by decide⟩ :=
  accepted_of_selected 13 307285 ⟨604622, by decide⟩ ⟨13, 2, 0, 604622, 307285, 2073, 16384⟩
    (by decide) selected_cut_23932

theorem selected_cut_23933 : selected 8 ⟨604664, by decide⟩
    (prefixPartial 13 307286) = some ⟨13, 2, 0, 604664, 307286, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_307286_604664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307286 ⟨604664, by decide⟩ :=
  accepted_of_selected 13 307286 ⟨604664, by decide⟩ ⟨13, 2, 0, 604664, 307286, 1893, 16384⟩
    (by decide) selected_cut_23933

theorem selected_cut_23934 : selected 8 ⟨604678, by decide⟩
    (prefixPartial 13 307287) = some ⟨13, 2, 0, 604678, 307287, 765, 16384⟩ := by
  decide +kernel

theorem context_13_307287_604678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307287 ⟨604678, by decide⟩ :=
  accepted_of_selected 13 307287 ⟨604678, by decide⟩ ⟨13, 2, 0, 604678, 307287, 765, 16384⟩
    (by decide) selected_cut_23934

theorem unmarked_context_12_76821_604679 : frontier 9 ⟨604679, by decide⟩
    (prefixCache 12 76821) (prefixPartial 12 76821) = false := by
  decide +kernel

theorem node_context_12_76821_604679 : EJMOriginalGlobalDAGData.nodes 9 ⟨604679, by decide⟩ =
    .split (coordinate 12) (![⟨604582, by decide⟩,⟨604622, by decide⟩,⟨604664, by decide⟩,⟨604678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76821_604679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76821 ⟨604679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76821
    ⟨604679, by decide⟩ (by decide) (![⟨604582, by decide⟩,⟨604622, by decide⟩,⟨604664, by decide⟩,⟨604678, by decide⟩]) unmarked_context_12_76821_604679 node_context_12_76821_604679
  intro a
  fin_cases a
  · exact context_13_307284_604582
  · exact context_13_307285_604622
  · exact context_13_307286_604664
  · exact context_13_307287_604678

theorem selected_cut_23935 : selected 8 ⟨604721, by decide⟩
    (prefixPartial 13 307288) = some ⟨13, 2, 0, 604721, 307288, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_307288_604721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307288 ⟨604721, by decide⟩ :=
  accepted_of_selected 13 307288 ⟨604721, by decide⟩ ⟨13, 2, 0, 604721, 307288, 1645, 16384⟩
    (by decide) selected_cut_23935

theorem selected_cut_23936 : selected 8 ⟨604774, by decide⟩
    (prefixPartial 13 307289) = some ⟨13, 2, 0, 604774, 307289, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_307289_604774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307289 ⟨604774, by decide⟩ :=
  accepted_of_selected 13 307289 ⟨604774, by decide⟩ ⟨13, 2, 0, 604774, 307289, 2213, 16384⟩
    (by decide) selected_cut_23936

theorem selected_cut_23937 : selected 8 ⟨604802, by decide⟩
    (prefixPartial 13 307290) = some ⟨13, 2, 0, 604802, 307290, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_307290_604802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307290 ⟨604802, by decide⟩ :=
  accepted_of_selected 13 307290 ⟨604802, by decide⟩ ⟨13, 2, 0, 604802, 307290, 1469, 16384⟩
    (by decide) selected_cut_23937

theorem selected_cut_23938 : selected 8 ⟨604815, by decide⟩
    (prefixPartial 13 307291) = some ⟨13, 2, 0, 604815, 307291, 789, 16384⟩ := by
  decide +kernel

theorem context_13_307291_604815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307291 ⟨604815, by decide⟩ :=
  accepted_of_selected 13 307291 ⟨604815, by decide⟩ ⟨13, 2, 0, 604815, 307291, 789, 16384⟩
    (by decide) selected_cut_23938

theorem unmarked_context_12_76822_604816 : frontier 9 ⟨604816, by decide⟩
    (prefixCache 12 76822) (prefixPartial 12 76822) = false := by
  decide +kernel

theorem node_context_12_76822_604816 : EJMOriginalGlobalDAGData.nodes 9 ⟨604816, by decide⟩ =
    .split (coordinate 12) (![⟨604721, by decide⟩,⟨604774, by decide⟩,⟨604802, by decide⟩,⟨604815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76822_604816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76822 ⟨604816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76822
    ⟨604816, by decide⟩ (by decide) (![⟨604721, by decide⟩,⟨604774, by decide⟩,⟨604802, by decide⟩,⟨604815, by decide⟩]) unmarked_context_12_76822_604816 node_context_12_76822_604816
  intro a
  fin_cases a
  · exact context_13_307288_604721
  · exact context_13_307289_604774
  · exact context_13_307290_604802
  · exact context_13_307291_604815

theorem selected_cut_23939 : selected 8 ⟨604858, by decide⟩
    (prefixPartial 13 307292) = some ⟨13, 2, 0, 604858, 307292, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_307292_604858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307292 ⟨604858, by decide⟩ :=
  accepted_of_selected 13 307292 ⟨604858, by decide⟩ ⟨13, 2, 0, 604858, 307292, 1673, 16384⟩
    (by decide) selected_cut_23939

theorem selected_cut_23940 : selected 8 ⟨604898, by decide⟩
    (prefixPartial 13 307293) = some ⟨13, 2, 0, 604898, 307293, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_307293_604898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307293 ⟨604898, by decide⟩ :=
  accepted_of_selected 13 307293 ⟨604898, by decide⟩ ⟨13, 2, 0, 604898, 307293, 2261, 16384⟩
    (by decide) selected_cut_23940

theorem selected_cut_23941 : selected 8 ⟨604938, by decide⟩
    (prefixPartial 13 307294) = some ⟨13, 2, 0, 604938, 307294, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_307294_604938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307294 ⟨604938, by decide⟩ :=
  accepted_of_selected 13 307294 ⟨604938, by decide⟩ ⟨13, 2, 0, 604938, 307294, 1857, 16384⟩
    (by decide) selected_cut_23941

theorem selected_cut_23942 : selected 8 ⟨604952, by decide⟩
    (prefixPartial 13 307295) = some ⟨13, 2, 0, 604952, 307295, 801, 16384⟩ := by
  decide +kernel

theorem context_13_307295_604952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307295 ⟨604952, by decide⟩ :=
  accepted_of_selected 13 307295 ⟨604952, by decide⟩ ⟨13, 2, 0, 604952, 307295, 801, 16384⟩
    (by decide) selected_cut_23942

theorem unmarked_context_12_76823_604953 : frontier 9 ⟨604953, by decide⟩
    (prefixCache 12 76823) (prefixPartial 12 76823) = false := by
  decide +kernel

theorem node_context_12_76823_604953 : EJMOriginalGlobalDAGData.nodes 9 ⟨604953, by decide⟩ =
    .split (coordinate 12) (![⟨604858, by decide⟩,⟨604898, by decide⟩,⟨604938, by decide⟩,⟨604952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76823_604953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76823 ⟨604953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76823
    ⟨604953, by decide⟩ (by decide) (![⟨604858, by decide⟩,⟨604898, by decide⟩,⟨604938, by decide⟩,⟨604952, by decide⟩]) unmarked_context_12_76823_604953 node_context_12_76823_604953
  intro a
  fin_cases a
  · exact context_13_307292_604858
  · exact context_13_307293_604898
  · exact context_13_307294_604938
  · exact context_13_307295_604952

theorem unmarked_context_11_19205_604954 : frontier 10 ⟨604954, by decide⟩
    (prefixCache 11 19205) (prefixPartial 11 19205) = false := by
  decide +kernel

theorem node_context_11_19205_604954 : EJMOriginalGlobalDAGData.nodes 10 ⟨604954, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨604679, by decide⟩,⟨604816, by decide⟩,⟨604953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19205_604954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19205 ⟨604954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19205
    ⟨604954, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨604679, by decide⟩,⟨604816, by decide⟩,⟨604953, by decide⟩]) unmarked_context_11_19205_604954 node_context_11_19205_604954
  intro a
  fin_cases a
  · exact context_12_76820_435160
  · exact context_12_76821_604679
  · exact context_12_76822_604816
  · exact context_12_76823_604953

theorem selected_cut_23943 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 76824) = some ⟨12, 1, 0, 449505, 76824, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76824_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76824 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 76824 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 76824, 1, 65536⟩
    (by decide) selected_cut_23943

theorem selected_cut_23944 : selected 8 ⟨604994, by decide⟩
    (prefixPartial 13 307300) = some ⟨13, 2, 0, 604994, 307300, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_307300_604994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307300 ⟨604994, by decide⟩ :=
  accepted_of_selected 13 307300 ⟨604994, by decide⟩ ⟨13, 2, 0, 604994, 307300, 1633, 16384⟩
    (by decide) selected_cut_23944

theorem selected_cut_23945 : selected 8 ⟨605041, by decide⟩
    (prefixPartial 13 307301) = some ⟨13, 2, 0, 605041, 307301, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_307301_605041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307301 ⟨605041, by decide⟩ :=
  accepted_of_selected 13 307301 ⟨605041, by decide⟩ ⟨13, 2, 0, 605041, 307301, 2269, 16384⟩
    (by decide) selected_cut_23945

theorem selected_cut_23946 : selected 8 ⟨605088, by decide⟩
    (prefixPartial 13 307302) = some ⟨13, 2, 0, 605088, 307302, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_307302_605088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307302 ⟨605088, by decide⟩ :=
  accepted_of_selected 13 307302 ⟨605088, by decide⟩ ⟨13, 2, 0, 605088, 307302, 2141, 16384⟩
    (by decide) selected_cut_23946

theorem selected_cut_23947 : selected 8 ⟨605107, by decide⟩
    (prefixPartial 13 307303) = some ⟨13, 2, 0, 605107, 307303, 889, 16384⟩ := by
  decide +kernel

theorem context_13_307303_605107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307303 ⟨605107, by decide⟩ :=
  accepted_of_selected 13 307303 ⟨605107, by decide⟩ ⟨13, 2, 0, 605107, 307303, 889, 16384⟩
    (by decide) selected_cut_23947

theorem unmarked_context_12_76825_605108 : frontier 9 ⟨605108, by decide⟩
    (prefixCache 12 76825) (prefixPartial 12 76825) = false := by
  decide +kernel

theorem node_context_12_76825_605108 : EJMOriginalGlobalDAGData.nodes 9 ⟨605108, by decide⟩ =
    .split (coordinate 12) (![⟨604994, by decide⟩,⟨605041, by decide⟩,⟨605088, by decide⟩,⟨605107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76825_605108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76825 ⟨605108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76825
    ⟨605108, by decide⟩ (by decide) (![⟨604994, by decide⟩,⟨605041, by decide⟩,⟨605088, by decide⟩,⟨605107, by decide⟩]) unmarked_context_12_76825_605108 node_context_12_76825_605108
  intro a
  fin_cases a
  · exact context_13_307300_604994
  · exact context_13_307301_605041
  · exact context_13_307302_605088
  · exact context_13_307303_605107

theorem selected_cut_23948 : selected 8 ⟨605137, by decide⟩
    (prefixPartial 13 307304) = some ⟨13, 2, 0, 605137, 307304, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_307304_605137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307304 ⟨605137, by decide⟩ :=
  accepted_of_selected 13 307304 ⟨605137, by decide⟩ ⟨13, 2, 0, 605137, 307304, 1169, 16384⟩
    (by decide) selected_cut_23948

theorem selected_cut_23949 : selected 8 ⟨605170, by decide⟩
    (prefixPartial 13 307305) = some ⟨13, 2, 0, 605170, 307305, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_307305_605170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307305 ⟨605170, by decide⟩ :=
  accepted_of_selected 13 307305 ⟨605170, by decide⟩ ⟨13, 2, 0, 605170, 307305, 1933, 16384⟩
    (by decide) selected_cut_23949

theorem selected_cut_23950 : selected 8 ⟨605191, by decide⟩
    (prefixPartial 13 307306) = some ⟨13, 2, 0, 605191, 307306, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_307306_605191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307306 ⟨605191, by decide⟩ :=
  accepted_of_selected 13 307306 ⟨605191, by decide⟩ ⟨13, 2, 0, 605191, 307306, 1489, 16384⟩
    (by decide) selected_cut_23950

theorem selected_cut_23951 : selected 8 ⟨605205, by decide⟩
    (prefixPartial 13 307307) = some ⟨13, 2, 0, 605205, 307307, 821, 16384⟩ := by
  decide +kernel

theorem context_13_307307_605205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307307 ⟨605205, by decide⟩ :=
  accepted_of_selected 13 307307 ⟨605205, by decide⟩ ⟨13, 2, 0, 605205, 307307, 821, 16384⟩
    (by decide) selected_cut_23951

theorem unmarked_context_12_76826_605206 : frontier 9 ⟨605206, by decide⟩
    (prefixCache 12 76826) (prefixPartial 12 76826) = false := by
  decide +kernel

theorem node_context_12_76826_605206 : EJMOriginalGlobalDAGData.nodes 9 ⟨605206, by decide⟩ =
    .split (coordinate 12) (![⟨605137, by decide⟩,⟨605170, by decide⟩,⟨605191, by decide⟩,⟨605205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76826_605206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76826 ⟨605206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76826
    ⟨605206, by decide⟩ (by decide) (![⟨605137, by decide⟩,⟨605170, by decide⟩,⟨605191, by decide⟩,⟨605205, by decide⟩]) unmarked_context_12_76826_605206 node_context_12_76826_605206
  intro a
  fin_cases a
  · exact context_13_307304_605137
  · exact context_13_307305_605170
  · exact context_13_307306_605191
  · exact context_13_307307_605205

theorem selected_cut_23952 : selected 8 ⟨605242, by decide⟩
    (prefixPartial 13 307308) = some ⟨13, 2, 0, 605242, 307308, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_307308_605242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307308 ⟨605242, by decide⟩ :=
  accepted_of_selected 13 307308 ⟨605242, by decide⟩ ⟨13, 2, 0, 605242, 307308, 1421, 16384⟩
    (by decide) selected_cut_23952

theorem selected_cut_23953 : selected 8 ⟨605282, by decide⟩
    (prefixPartial 13 307309) = some ⟨13, 2, 0, 605282, 307309, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_307309_605282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307309 ⟨605282, by decide⟩ :=
  accepted_of_selected 13 307309 ⟨605282, by decide⟩ ⟨13, 2, 0, 605282, 307309, 2317, 16384⟩
    (by decide) selected_cut_23953

theorem selected_cut_23954 : selected 8 ⟨605314, by decide⟩
    (prefixPartial 13 307310) = some ⟨13, 2, 0, 605314, 307310, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_307310_605314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307310 ⟨605314, by decide⟩ :=
  accepted_of_selected 13 307310 ⟨605314, by decide⟩ ⟨13, 2, 0, 605314, 307310, 1933, 16384⟩
    (by decide) selected_cut_23954

theorem selected_cut_23955 : selected 8 ⟨605336, by decide⟩
    (prefixPartial 13 307311) = some ⟨13, 2, 0, 605336, 307311, 881, 16384⟩ := by
  decide +kernel

theorem context_13_307311_605336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307311 ⟨605336, by decide⟩ :=
  accepted_of_selected 13 307311 ⟨605336, by decide⟩ ⟨13, 2, 0, 605336, 307311, 881, 16384⟩
    (by decide) selected_cut_23955

theorem unmarked_context_12_76827_605337 : frontier 9 ⟨605337, by decide⟩
    (prefixCache 12 76827) (prefixPartial 12 76827) = false := by
  decide +kernel

theorem node_context_12_76827_605337 : EJMOriginalGlobalDAGData.nodes 9 ⟨605337, by decide⟩ =
    .split (coordinate 12) (![⟨605242, by decide⟩,⟨605282, by decide⟩,⟨605314, by decide⟩,⟨605336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76827_605337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76827 ⟨605337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76827
    ⟨605337, by decide⟩ (by decide) (![⟨605242, by decide⟩,⟨605282, by decide⟩,⟨605314, by decide⟩,⟨605336, by decide⟩]) unmarked_context_12_76827_605337 node_context_12_76827_605337
  intro a
  fin_cases a
  · exact context_13_307308_605242
  · exact context_13_307309_605282
  · exact context_13_307310_605314
  · exact context_13_307311_605336

theorem unmarked_context_11_19206_605338 : frontier 10 ⟨605338, by decide⟩
    (prefixCache 11 19206) (prefixPartial 11 19206) = false := by
  decide +kernel

theorem node_context_11_19206_605338 : EJMOriginalGlobalDAGData.nodes 10 ⟨605338, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨605108, by decide⟩,⟨605206, by decide⟩,⟨605337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19206_605338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19206 ⟨605338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19206
    ⟨605338, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨605108, by decide⟩,⟨605206, by decide⟩,⟨605337, by decide⟩]) unmarked_context_11_19206_605338 node_context_11_19206_605338
  intro a
  fin_cases a
  · exact context_12_76824_449505
  · exact context_12_76825_605108
  · exact context_12_76826_605206
  · exact context_12_76827_605337

theorem selected_cut_23956 : selected 9 ⟨539296, by decide⟩
    (prefixPartial 12 76828) = some ⟨12, 1, 0, 539296, 76828, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76828_539296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76828 ⟨539296, by decide⟩ :=
  accepted_of_selected 12 76828 ⟨539296, by decide⟩ ⟨12, 1, 0, 539296, 76828, 1, 65536⟩
    (by decide) selected_cut_23956

theorem selected_cut_23957 : selected 8 ⟨605368, by decide⟩
    (prefixPartial 13 307316) = some ⟨13, 2, 0, 605368, 307316, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_307316_605368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307316 ⟨605368, by decide⟩ :=
  accepted_of_selected 13 307316 ⟨605368, by decide⟩ ⟨13, 2, 0, 605368, 307316, 1321, 16384⟩
    (by decide) selected_cut_23957

theorem selected_cut_23958 : selected 8 ⟨605410, by decide⟩
    (prefixPartial 13 307317) = some ⟨13, 2, 0, 605410, 307317, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_307317_605410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307317 ⟨605410, by decide⟩ :=
  accepted_of_selected 13 307317 ⟨605410, by decide⟩ ⟨13, 2, 0, 605410, 307317, 2429, 16384⟩
    (by decide) selected_cut_23958

theorem selected_cut_23959 : selected 8 ⟨605447, by decide⟩
    (prefixPartial 13 307318) = some ⟨13, 2, 0, 605447, 307318, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_307318_605447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307318 ⟨605447, by decide⟩ :=
  accepted_of_selected 13 307318 ⟨605447, by decide⟩ ⟨13, 2, 0, 605447, 307318, 1917, 16384⟩
    (by decide) selected_cut_23959

theorem selected_cut_23960 : selected 8 ⟨605459, by decide⟩
    (prefixPartial 13 307319) = some ⟨13, 2, 0, 605459, 307319, 773, 16384⟩ := by
  decide +kernel

theorem context_13_307319_605459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307319 ⟨605459, by decide⟩ :=
  accepted_of_selected 13 307319 ⟨605459, by decide⟩ ⟨13, 2, 0, 605459, 307319, 773, 16384⟩
    (by decide) selected_cut_23960

theorem unmarked_context_12_76829_605460 : frontier 9 ⟨605460, by decide⟩
    (prefixCache 12 76829) (prefixPartial 12 76829) = false := by
  decide +kernel

theorem node_context_12_76829_605460 : EJMOriginalGlobalDAGData.nodes 9 ⟨605460, by decide⟩ =
    .split (coordinate 12) (![⟨605368, by decide⟩,⟨605410, by decide⟩,⟨605447, by decide⟩,⟨605459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76829_605460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76829 ⟨605460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76829
    ⟨605460, by decide⟩ (by decide) (![⟨605368, by decide⟩,⟨605410, by decide⟩,⟨605447, by decide⟩,⟨605459, by decide⟩]) unmarked_context_12_76829_605460 node_context_12_76829_605460
  intro a
  fin_cases a
  · exact context_13_307316_605368
  · exact context_13_307317_605410
  · exact context_13_307318_605447
  · exact context_13_307319_605459

theorem selected_cut_23961 : selected 8 ⟨605483, by decide⟩
    (prefixPartial 13 307320) = some ⟨13, 2, 0, 605483, 307320, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_307320_605483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307320 ⟨605483, by decide⟩ :=
  accepted_of_selected 13 307320 ⟨605483, by decide⟩ ⟨13, 2, 0, 605483, 307320, 1089, 16384⟩
    (by decide) selected_cut_23961

theorem selected_cut_23962 : selected 8 ⟨605522, by decide⟩
    (prefixPartial 13 307321) = some ⟨13, 2, 0, 605522, 307321, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_307321_605522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307321 ⟨605522, by decide⟩ :=
  accepted_of_selected 13 307321 ⟨605522, by decide⟩ ⟨13, 2, 0, 605522, 307321, 2225, 16384⟩
    (by decide) selected_cut_23962

theorem selected_cut_23963 : selected 8 ⟨605544, by decide⟩
    (prefixPartial 13 307322) = some ⟨13, 2, 0, 605544, 307322, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_307322_605544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307322 ⟨605544, by decide⟩ :=
  accepted_of_selected 13 307322 ⟨605544, by decide⟩ ⟨13, 2, 0, 605544, 307322, 1421, 16384⟩
    (by decide) selected_cut_23963

theorem selected_cut_23964 : selected 8 ⟨605554, by decide⟩
    (prefixPartial 13 307323) = some ⟨13, 2, 0, 605554, 307323, 801, 16384⟩ := by
  decide +kernel

theorem context_13_307323_605554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307323 ⟨605554, by decide⟩ :=
  accepted_of_selected 13 307323 ⟨605554, by decide⟩ ⟨13, 2, 0, 605554, 307323, 801, 16384⟩
    (by decide) selected_cut_23964

theorem unmarked_context_12_76830_605555 : frontier 9 ⟨605555, by decide⟩
    (prefixCache 12 76830) (prefixPartial 12 76830) = false := by
  decide +kernel

theorem node_context_12_76830_605555 : EJMOriginalGlobalDAGData.nodes 9 ⟨605555, by decide⟩ =
    .split (coordinate 12) (![⟨605483, by decide⟩,⟨605522, by decide⟩,⟨605544, by decide⟩,⟨605554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76830_605555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76830 ⟨605555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76830
    ⟨605555, by decide⟩ (by decide) (![⟨605483, by decide⟩,⟨605522, by decide⟩,⟨605544, by decide⟩,⟨605554, by decide⟩]) unmarked_context_12_76830_605555 node_context_12_76830_605555
  intro a
  fin_cases a
  · exact context_13_307320_605483
  · exact context_13_307321_605522
  · exact context_13_307322_605544
  · exact context_13_307323_605554

theorem selected_cut_23965 : selected 8 ⟨605585, by decide⟩
    (prefixPartial 13 307324) = some ⟨13, 2, 0, 605585, 307324, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_307324_605585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307324 ⟨605585, by decide⟩ :=
  accepted_of_selected 13 307324 ⟨605585, by decide⟩ ⟨13, 2, 0, 605585, 307324, 1097, 16384⟩
    (by decide) selected_cut_23965

theorem selected_cut_23966 : selected 8 ⟨605615, by decide⟩
    (prefixPartial 13 307325) = some ⟨13, 2, 0, 605615, 307325, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_307325_605615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307325 ⟨605615, by decide⟩ :=
  accepted_of_selected 13 307325 ⟨605615, by decide⟩ ⟨13, 2, 0, 605615, 307325, 2205, 16384⟩
    (by decide) selected_cut_23966

theorem selected_cut_23967 : selected 8 ⟨605634, by decide⟩
    (prefixPartial 13 307326) = some ⟨13, 2, 0, 605634, 307326, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_307326_605634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307326 ⟨605634, by decide⟩ :=
  accepted_of_selected 13 307326 ⟨605634, by decide⟩ ⟨13, 2, 0, 605634, 307326, 1709, 16384⟩
    (by decide) selected_cut_23967

theorem selected_cut_23968 : selected 8 ⟨605650, by decide⟩
    (prefixPartial 13 307327) = some ⟨13, 2, 0, 605650, 307327, 761, 16384⟩ := by
  decide +kernel

theorem context_13_307327_605650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307327 ⟨605650, by decide⟩ :=
  accepted_of_selected 13 307327 ⟨605650, by decide⟩ ⟨13, 2, 0, 605650, 307327, 761, 16384⟩
    (by decide) selected_cut_23968

theorem unmarked_context_12_76831_605651 : frontier 9 ⟨605651, by decide⟩
    (prefixCache 12 76831) (prefixPartial 12 76831) = false := by
  decide +kernel

theorem node_context_12_76831_605651 : EJMOriginalGlobalDAGData.nodes 9 ⟨605651, by decide⟩ =
    .split (coordinate 12) (![⟨605585, by decide⟩,⟨605615, by decide⟩,⟨605634, by decide⟩,⟨605650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76831_605651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76831 ⟨605651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76831
    ⟨605651, by decide⟩ (by decide) (![⟨605585, by decide⟩,⟨605615, by decide⟩,⟨605634, by decide⟩,⟨605650, by decide⟩]) unmarked_context_12_76831_605651 node_context_12_76831_605651
  intro a
  fin_cases a
  · exact context_13_307324_605585
  · exact context_13_307325_605615
  · exact context_13_307326_605634
  · exact context_13_307327_605650

theorem unmarked_context_11_19207_605652 : frontier 10 ⟨605652, by decide⟩
    (prefixCache 11 19207) (prefixPartial 11 19207) = false := by
  decide +kernel

theorem node_context_11_19207_605652 : EJMOriginalGlobalDAGData.nodes 10 ⟨605652, by decide⟩ =
    .split (coordinate 11) (![⟨539296, by decide⟩,⟨605460, by decide⟩,⟨605555, by decide⟩,⟨605651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19207_605652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19207 ⟨605652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19207
    ⟨605652, by decide⟩ (by decide) (![⟨539296, by decide⟩,⟨605460, by decide⟩,⟨605555, by decide⟩,⟨605651, by decide⟩]) unmarked_context_11_19207_605652 node_context_11_19207_605652
  intro a
  fin_cases a
  · exact context_12_76828_539296
  · exact context_12_76829_605460
  · exact context_12_76830_605555
  · exact context_12_76831_605651

theorem unmarked_context_10_4801_605653 : frontier 11 ⟨605653, by decide⟩
    (prefixCache 10 4801) (prefixPartial 10 4801) = false := by
  decide +kernel

theorem node_context_10_4801_605653 : EJMOriginalGlobalDAGData.nodes 11 ⟨605653, by decide⟩ =
    .split (coordinate 10) (![⟨604536, by decide⟩,⟨604954, by decide⟩,⟨605338, by decide⟩,⟨605652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4801_605653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4801 ⟨605653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4801
    ⟨605653, by decide⟩ (by decide) (![⟨604536, by decide⟩,⟨604954, by decide⟩,⟨605338, by decide⟩,⟨605652, by decide⟩]) unmarked_context_10_4801_605653 node_context_10_4801_605653
  intro a
  fin_cases a
  · exact context_11_19204_604536
  · exact context_11_19205_604954
  · exact context_11_19206_605338
  · exact context_11_19207_605652

theorem selected_cut_23969 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 76832) = some ⟨12, 1, 0, 435790, 76832, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76832_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76832 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 76832 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 76832, 1, 65536⟩
    (by decide) selected_cut_23969

theorem selected_cut_23970 : selected 8 ⟨605676, by decide⟩
    (prefixPartial 13 307332) = some ⟨13, 2, 0, 605676, 307332, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_307332_605676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307332 ⟨605676, by decide⟩ :=
  accepted_of_selected 13 307332 ⟨605676, by decide⟩ ⟨13, 2, 0, 605676, 307332, 1021, 16384⟩
    (by decide) selected_cut_23970

theorem selected_cut_23971 : selected 8 ⟨605711, by decide⟩
    (prefixPartial 13 307333) = some ⟨13, 2, 0, 605711, 307333, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_307333_605711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307333 ⟨605711, by decide⟩ :=
  accepted_of_selected 13 307333 ⟨605711, by decide⟩ ⟨13, 2, 0, 605711, 307333, 1801, 16384⟩
    (by decide) selected_cut_23971

theorem selected_cut_23972 : selected 8 ⟨605735, by decide⟩
    (prefixPartial 13 307334) = some ⟨13, 2, 0, 605735, 307334, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_307334_605735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307334 ⟨605735, by decide⟩ :=
  accepted_of_selected 13 307334 ⟨605735, by decide⟩ ⟨13, 2, 0, 605735, 307334, 1369, 16384⟩
    (by decide) selected_cut_23972

theorem selected_cut_23973 : selected 8 ⟨605745, by decide⟩
    (prefixPartial 13 307335) = some ⟨13, 2, 0, 605745, 307335, 689, 16384⟩ := by
  decide +kernel

theorem context_13_307335_605745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307335 ⟨605745, by decide⟩ :=
  accepted_of_selected 13 307335 ⟨605745, by decide⟩ ⟨13, 2, 0, 605745, 307335, 689, 16384⟩
    (by decide) selected_cut_23973

theorem unmarked_context_12_76833_605746 : frontier 9 ⟨605746, by decide⟩
    (prefixCache 12 76833) (prefixPartial 12 76833) = false := by
  decide +kernel

theorem node_context_12_76833_605746 : EJMOriginalGlobalDAGData.nodes 9 ⟨605746, by decide⟩ =
    .split (coordinate 12) (![⟨605676, by decide⟩,⟨605711, by decide⟩,⟨605735, by decide⟩,⟨605745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76833_605746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76833 ⟨605746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76833
    ⟨605746, by decide⟩ (by decide) (![⟨605676, by decide⟩,⟨605711, by decide⟩,⟨605735, by decide⟩,⟨605745, by decide⟩]) unmarked_context_12_76833_605746 node_context_12_76833_605746
  intro a
  fin_cases a
  · exact context_13_307332_605676
  · exact context_13_307333_605711
  · exact context_13_307334_605735
  · exact context_13_307335_605745

theorem selected_cut_23974 : selected 8 ⟨605767, by decide⟩
    (prefixPartial 13 307336) = some ⟨13, 2, 0, 605767, 307336, 873, 16384⟩ := by
  decide +kernel

theorem context_13_307336_605767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307336 ⟨605767, by decide⟩ :=
  accepted_of_selected 13 307336 ⟨605767, by decide⟩ ⟨13, 2, 0, 605767, 307336, 873, 16384⟩
    (by decide) selected_cut_23974

theorem selected_cut_23975 : selected 8 ⟨605802, by decide⟩
    (prefixPartial 13 307337) = some ⟨13, 2, 0, 605802, 307337, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_307337_605802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307337 ⟨605802, by decide⟩ :=
  accepted_of_selected 13 307337 ⟨605802, by decide⟩ ⟨13, 2, 0, 605802, 307337, 1657, 16384⟩
    (by decide) selected_cut_23975

theorem selected_cut_23976 : selected 8 ⟨605821, by decide⟩
    (prefixPartial 13 307338) = some ⟨13, 2, 0, 605821, 307338, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_307338_605821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307338 ⟨605821, by decide⟩ :=
  accepted_of_selected 13 307338 ⟨605821, by decide⟩ ⟨13, 2, 0, 605821, 307338, 1025, 16384⟩
    (by decide) selected_cut_23976

theorem selected_cut_23977 : selected 8 ⟨605829, by decide⟩
    (prefixPartial 13 307339) = some ⟨13, 2, 0, 605829, 307339, 665, 16384⟩ := by
  decide +kernel

theorem context_13_307339_605829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307339 ⟨605829, by decide⟩ :=
  accepted_of_selected 13 307339 ⟨605829, by decide⟩ ⟨13, 2, 0, 605829, 307339, 665, 16384⟩
    (by decide) selected_cut_23977

theorem unmarked_context_12_76834_605830 : frontier 9 ⟨605830, by decide⟩
    (prefixCache 12 76834) (prefixPartial 12 76834) = false := by
  decide +kernel

theorem node_context_12_76834_605830 : EJMOriginalGlobalDAGData.nodes 9 ⟨605830, by decide⟩ =
    .split (coordinate 12) (![⟨605767, by decide⟩,⟨605802, by decide⟩,⟨605821, by decide⟩,⟨605829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76834_605830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76834 ⟨605830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76834
    ⟨605830, by decide⟩ (by decide) (![⟨605767, by decide⟩,⟨605802, by decide⟩,⟨605821, by decide⟩,⟨605829, by decide⟩]) unmarked_context_12_76834_605830 node_context_12_76834_605830
  intro a
  fin_cases a
  · exact context_13_307336_605767
  · exact context_13_307337_605802
  · exact context_13_307338_605821
  · exact context_13_307339_605829

theorem selected_cut_23978 : selected 8 ⟨605850, by decide⟩
    (prefixPartial 13 307340) = some ⟨13, 2, 0, 605850, 307340, 973, 16384⟩ := by
  decide +kernel

theorem context_13_307340_605850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307340 ⟨605850, by decide⟩ :=
  accepted_of_selected 13 307340 ⟨605850, by decide⟩ ⟨13, 2, 0, 605850, 307340, 973, 16384⟩
    (by decide) selected_cut_23978

theorem selected_cut_23979 : selected 8 ⟨605886, by decide⟩
    (prefixPartial 13 307341) = some ⟨13, 2, 0, 605886, 307341, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_307341_605886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307341 ⟨605886, by decide⟩ :=
  accepted_of_selected 13 307341 ⟨605886, by decide⟩ ⟨13, 2, 0, 605886, 307341, 1865, 16384⟩
    (by decide) selected_cut_23979

theorem selected_cut_23980 : selected 8 ⟨605907, by decide⟩
    (prefixPartial 13 307342) = some ⟨13, 2, 0, 605907, 307342, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_307342_605907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307342 ⟨605907, by decide⟩ :=
  accepted_of_selected 13 307342 ⟨605907, by decide⟩ ⟨13, 2, 0, 605907, 307342, 1293, 16384⟩
    (by decide) selected_cut_23980

theorem selected_cut_23981 : selected 8 ⟨605919, by decide⟩
    (prefixPartial 13 307343) = some ⟨13, 2, 0, 605919, 307343, 729, 16384⟩ := by
  decide +kernel

theorem context_13_307343_605919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307343 ⟨605919, by decide⟩ :=
  accepted_of_selected 13 307343 ⟨605919, by decide⟩ ⟨13, 2, 0, 605919, 307343, 729, 16384⟩
    (by decide) selected_cut_23981

theorem unmarked_context_12_76835_605920 : frontier 9 ⟨605920, by decide⟩
    (prefixCache 12 76835) (prefixPartial 12 76835) = false := by
  decide +kernel

theorem node_context_12_76835_605920 : EJMOriginalGlobalDAGData.nodes 9 ⟨605920, by decide⟩ =
    .split (coordinate 12) (![⟨605850, by decide⟩,⟨605886, by decide⟩,⟨605907, by decide⟩,⟨605919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76835_605920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76835 ⟨605920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76835
    ⟨605920, by decide⟩ (by decide) (![⟨605850, by decide⟩,⟨605886, by decide⟩,⟨605907, by decide⟩,⟨605919, by decide⟩]) unmarked_context_12_76835_605920 node_context_12_76835_605920
  intro a
  fin_cases a
  · exact context_13_307340_605850
  · exact context_13_307341_605886
  · exact context_13_307342_605907
  · exact context_13_307343_605919

theorem unmarked_context_11_19208_605921 : frontier 10 ⟨605921, by decide⟩
    (prefixCache 11 19208) (prefixPartial 11 19208) = false := by
  decide +kernel

theorem node_context_11_19208_605921 : EJMOriginalGlobalDAGData.nodes 10 ⟨605921, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨605746, by decide⟩,⟨605830, by decide⟩,⟨605920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19208_605921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19208 ⟨605921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19208
    ⟨605921, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨605746, by decide⟩,⟨605830, by decide⟩,⟨605920, by decide⟩]) unmarked_context_11_19208_605921 node_context_11_19208_605921
  intro a
  fin_cases a
  · exact context_12_76832_435790
  · exact context_12_76833_605746
  · exact context_12_76834_605830
  · exact context_12_76835_605920

theorem selected_cut_23982 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 76836) = some ⟨12, 1, 0, 450498, 76836, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76836_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76836 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 76836 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 76836, 1, 65536⟩
    (by decide) selected_cut_23982

theorem selected_cut_23983 : selected 8 ⟨605946, by decide⟩
    (prefixPartial 13 307348) = some ⟨13, 2, 0, 605946, 307348, 993, 16384⟩ := by
  decide +kernel

theorem context_13_307348_605946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307348 ⟨605946, by decide⟩ :=
  accepted_of_selected 13 307348 ⟨605946, by decide⟩ ⟨13, 2, 0, 605946, 307348, 993, 16384⟩
    (by decide) selected_cut_23983

theorem selected_cut_23984 : selected 8 ⟨605979, by decide⟩
    (prefixPartial 13 307349) = some ⟨13, 2, 0, 605979, 307349, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_307349_605979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307349 ⟨605979, by decide⟩ :=
  accepted_of_selected 13 307349 ⟨605979, by decide⟩ ⟨13, 2, 0, 605979, 307349, 2169, 16384⟩
    (by decide) selected_cut_23984

theorem selected_cut_23985 : selected 8 ⟨606002, by decide⟩
    (prefixPartial 13 307350) = some ⟨13, 2, 0, 606002, 307350, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_307350_606002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307350 ⟨606002, by decide⟩ :=
  accepted_of_selected 13 307350 ⟨606002, by decide⟩ ⟨13, 2, 0, 606002, 307350, 1765, 16384⟩
    (by decide) selected_cut_23985

theorem selected_cut_23986 : selected 8 ⟨606013, by decide⟩
    (prefixPartial 13 307351) = some ⟨13, 2, 0, 606013, 307351, 845, 16384⟩ := by
  decide +kernel

theorem context_13_307351_606013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307351 ⟨606013, by decide⟩ :=
  accepted_of_selected 13 307351 ⟨606013, by decide⟩ ⟨13, 2, 0, 606013, 307351, 845, 16384⟩
    (by decide) selected_cut_23986

theorem unmarked_context_12_76837_606014 : frontier 9 ⟨606014, by decide⟩
    (prefixCache 12 76837) (prefixPartial 12 76837) = false := by
  decide +kernel

theorem node_context_12_76837_606014 : EJMOriginalGlobalDAGData.nodes 9 ⟨606014, by decide⟩ =
    .split (coordinate 12) (![⟨605946, by decide⟩,⟨605979, by decide⟩,⟨606002, by decide⟩,⟨606013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76837_606014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76837 ⟨606014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76837
    ⟨606014, by decide⟩ (by decide) (![⟨605946, by decide⟩,⟨605979, by decide⟩,⟨606002, by decide⟩,⟨606013, by decide⟩]) unmarked_context_12_76837_606014 node_context_12_76837_606014
  intro a
  fin_cases a
  · exact context_13_307348_605946
  · exact context_13_307349_605979
  · exact context_13_307350_606002
  · exact context_13_307351_606013

theorem selected_cut_23987 : selected 8 ⟨606039, by decide⟩
    (prefixPartial 13 307352) = some ⟨13, 2, 0, 606039, 307352, 953, 16384⟩ := by
  decide +kernel

theorem context_13_307352_606039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307352 ⟨606039, by decide⟩ :=
  accepted_of_selected 13 307352 ⟨606039, by decide⟩ ⟨13, 2, 0, 606039, 307352, 953, 16384⟩
    (by decide) selected_cut_23987

theorem selected_cut_23988 : selected 8 ⟨606094, by decide⟩
    (prefixPartial 13 307353) = some ⟨13, 2, 0, 606094, 307353, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_307353_606094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307353 ⟨606094, by decide⟩ :=
  accepted_of_selected 13 307353 ⟨606094, by decide⟩ ⟨13, 2, 0, 606094, 307353, 2309, 16384⟩
    (by decide) selected_cut_23988

theorem selected_cut_23989 : selected 8 ⟨606120, by decide⟩
    (prefixPartial 13 307354) = some ⟨13, 2, 0, 606120, 307354, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_307354_606120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307354 ⟨606120, by decide⟩ :=
  accepted_of_selected 13 307354 ⟨606120, by decide⟩ ⟨13, 2, 0, 606120, 307354, 1381, 16384⟩
    (by decide) selected_cut_23989

theorem selected_cut_23990 : selected 8 ⟨606130, by decide⟩
    (prefixPartial 13 307355) = some ⟨13, 2, 0, 606130, 307355, 881, 16384⟩ := by
  decide +kernel

theorem context_13_307355_606130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307355 ⟨606130, by decide⟩ :=
  accepted_of_selected 13 307355 ⟨606130, by decide⟩ ⟨13, 2, 0, 606130, 307355, 881, 16384⟩
    (by decide) selected_cut_23990

theorem unmarked_context_12_76838_606131 : frontier 9 ⟨606131, by decide⟩
    (prefixCache 12 76838) (prefixPartial 12 76838) = false := by
  decide +kernel

theorem node_context_12_76838_606131 : EJMOriginalGlobalDAGData.nodes 9 ⟨606131, by decide⟩ =
    .split (coordinate 12) (![⟨606039, by decide⟩,⟨606094, by decide⟩,⟨606120, by decide⟩,⟨606130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76838_606131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76838 ⟨606131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76838
    ⟨606131, by decide⟩ (by decide) (![⟨606039, by decide⟩,⟨606094, by decide⟩,⟨606120, by decide⟩,⟨606130, by decide⟩]) unmarked_context_12_76838_606131 node_context_12_76838_606131
  intro a
  fin_cases a
  · exact context_13_307352_606039
  · exact context_13_307353_606094
  · exact context_13_307354_606120
  · exact context_13_307355_606130

theorem selected_cut_23991 : selected 8 ⟨606154, by decide⟩
    (prefixPartial 13 307356) = some ⟨13, 2, 0, 606154, 307356, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_307356_606154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307356 ⟨606154, by decide⟩ :=
  accepted_of_selected 13 307356 ⟨606154, by decide⟩ ⟨13, 2, 0, 606154, 307356, 1021, 16384⟩
    (by decide) selected_cut_23991

theorem selected_cut_23992 : selected 8 ⟨606191, by decide⟩
    (prefixPartial 13 307357) = some ⟨13, 2, 0, 606191, 307357, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_307357_606191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307357 ⟨606191, by decide⟩ :=
  accepted_of_selected 13 307357 ⟨606191, by decide⟩ ⟨13, 2, 0, 606191, 307357, 2349, 16384⟩
    (by decide) selected_cut_23992

theorem selected_cut_23993 : selected 8 ⟨606223, by decide⟩
    (prefixPartial 13 307358) = some ⟨13, 2, 0, 606223, 307358, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_307358_606223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307358 ⟨606223, by decide⟩ :=
  accepted_of_selected 13 307358 ⟨606223, by decide⟩ ⟨13, 2, 0, 606223, 307358, 1749, 16384⟩
    (by decide) selected_cut_23993

theorem selected_cut_23994 : selected 8 ⟨606240, by decide⟩
    (prefixPartial 13 307359) = some ⟨13, 2, 0, 606240, 307359, 945, 16384⟩ := by
  decide +kernel

theorem context_13_307359_606240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307359 ⟨606240, by decide⟩ :=
  accepted_of_selected 13 307359 ⟨606240, by decide⟩ ⟨13, 2, 0, 606240, 307359, 945, 16384⟩
    (by decide) selected_cut_23994

theorem unmarked_context_12_76839_606241 : frontier 9 ⟨606241, by decide⟩
    (prefixCache 12 76839) (prefixPartial 12 76839) = false := by
  decide +kernel

theorem node_context_12_76839_606241 : EJMOriginalGlobalDAGData.nodes 9 ⟨606241, by decide⟩ =
    .split (coordinate 12) (![⟨606154, by decide⟩,⟨606191, by decide⟩,⟨606223, by decide⟩,⟨606240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76839_606241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76839 ⟨606241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76839
    ⟨606241, by decide⟩ (by decide) (![⟨606154, by decide⟩,⟨606191, by decide⟩,⟨606223, by decide⟩,⟨606240, by decide⟩]) unmarked_context_12_76839_606241 node_context_12_76839_606241
  intro a
  fin_cases a
  · exact context_13_307356_606154
  · exact context_13_307357_606191
  · exact context_13_307358_606223
  · exact context_13_307359_606240

theorem unmarked_context_11_19209_606242 : frontier 10 ⟨606242, by decide⟩
    (prefixCache 11 19209) (prefixPartial 11 19209) = false := by
  decide +kernel

theorem node_context_11_19209_606242 : EJMOriginalGlobalDAGData.nodes 10 ⟨606242, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨606014, by decide⟩,⟨606131, by decide⟩,⟨606241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19209_606242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19209 ⟨606242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19209
    ⟨606242, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨606014, by decide⟩,⟨606131, by decide⟩,⟨606241, by decide⟩]) unmarked_context_11_19209_606242 node_context_11_19209_606242
  intro a
  fin_cases a
  · exact context_12_76836_450498
  · exact context_12_76837_606014
  · exact context_12_76838_606131
  · exact context_12_76839_606241

theorem selected_cut_23995 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 76840) = some ⟨12, 1, 0, 435790, 76840, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76840_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76840 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 76840 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 76840, 1, 65536⟩
    (by decide) selected_cut_23995

theorem selected_cut_23996 : selected 8 ⟨606268, by decide⟩
    (prefixPartial 13 307364) = some ⟨13, 2, 0, 606268, 307364, 985, 16384⟩ := by
  decide +kernel

theorem context_13_307364_606268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307364 ⟨606268, by decide⟩ :=
  accepted_of_selected 13 307364 ⟨606268, by decide⟩ ⟨13, 2, 0, 606268, 307364, 985, 16384⟩
    (by decide) selected_cut_23996

theorem selected_cut_23997 : selected 8 ⟨606307, by decide⟩
    (prefixPartial 13 307365) = some ⟨13, 2, 0, 606307, 307365, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_307365_606307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307365 ⟨606307, by decide⟩ :=
  accepted_of_selected 13 307365 ⟨606307, by decide⟩ ⟨13, 2, 0, 606307, 307365, 2449, 16384⟩
    (by decide) selected_cut_23997

theorem selected_cut_23998 : selected 8 ⟨606337, by decide⟩
    (prefixPartial 13 307366) = some ⟨13, 2, 0, 606337, 307366, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_307366_606337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307366 ⟨606337, by decide⟩ :=
  accepted_of_selected 13 307366 ⟨606337, by decide⟩ ⟨13, 2, 0, 606337, 307366, 1977, 16384⟩
    (by decide) selected_cut_23998

theorem selected_cut_23999 : selected 8 ⟨606353, by decide⟩
    (prefixPartial 13 307367) = some ⟨13, 2, 0, 606353, 307367, 901, 16384⟩ := by
  decide +kernel

theorem context_13_307367_606353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307367 ⟨606353, by decide⟩ :=
  accepted_of_selected 13 307367 ⟨606353, by decide⟩ ⟨13, 2, 0, 606353, 307367, 901, 16384⟩
    (by decide) selected_cut_23999

theorem unmarked_context_12_76841_606354 : frontier 9 ⟨606354, by decide⟩
    (prefixCache 12 76841) (prefixPartial 12 76841) = false := by
  decide +kernel

theorem node_context_12_76841_606354 : EJMOriginalGlobalDAGData.nodes 9 ⟨606354, by decide⟩ =
    .split (coordinate 12) (![⟨606268, by decide⟩,⟨606307, by decide⟩,⟨606337, by decide⟩,⟨606353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76841_606354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76841 ⟨606354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76841
    ⟨606354, by decide⟩ (by decide) (![⟨606268, by decide⟩,⟨606307, by decide⟩,⟨606337, by decide⟩,⟨606353, by decide⟩]) unmarked_context_12_76841_606354 node_context_12_76841_606354
  intro a
  fin_cases a
  · exact context_13_307364_606268
  · exact context_13_307365_606307
  · exact context_13_307366_606337
  · exact context_13_307367_606353

theorem selected_cut_24000 : selected 8 ⟨606374, by decide⟩
    (prefixPartial 13 307368) = some ⟨13, 2, 0, 606374, 307368, 681, 16384⟩ := by
  decide +kernel

theorem context_13_307368_606374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307368 ⟨606374, by decide⟩ :=
  accepted_of_selected 13 307368 ⟨606374, by decide⟩ ⟨13, 2, 0, 606374, 307368, 681, 16384⟩
    (by decide) selected_cut_24000

theorem selected_cut_24001 : selected 8 ⟨606416, by decide⟩
    (prefixPartial 13 307369) = some ⟨13, 2, 0, 606416, 307369, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_307369_606416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307369 ⟨606416, by decide⟩ :=
  accepted_of_selected 13 307369 ⟨606416, by decide⟩ ⟨13, 2, 0, 606416, 307369, 2161, 16384⟩
    (by decide) selected_cut_24001

theorem selected_cut_24002 : selected 8 ⟨606444, by decide⟩
    (prefixPartial 13 307370) = some ⟨13, 2, 0, 606444, 307370, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_307370_606444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307370 ⟨606444, by decide⟩ :=
  accepted_of_selected 13 307370 ⟨606444, by decide⟩ ⟨13, 2, 0, 606444, 307370, 1469, 16384⟩
    (by decide) selected_cut_24002

theorem selected_cut_24003 : selected 8 ⟨606456, by decide⟩
    (prefixPartial 13 307371) = some ⟨13, 2, 0, 606456, 307371, 849, 16384⟩ := by
  decide +kernel

theorem context_13_307371_606456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307371 ⟨606456, by decide⟩ :=
  accepted_of_selected 13 307371 ⟨606456, by decide⟩ ⟨13, 2, 0, 606456, 307371, 849, 16384⟩
    (by decide) selected_cut_24003

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
