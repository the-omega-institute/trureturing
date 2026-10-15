/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover437
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_42051 : selected 9 ⟨1149592, by decide⟩
    (prefixPartial 12 337197) = some ⟨12, 2, 0, 1149592, 337197, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_337197_1149592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337197 ⟨1149592, by decide⟩ :=
  accepted_of_selected 12 337197 ⟨1149592, by decide⟩ ⟨12, 2, 0, 1149592, 337197, 2061, 65536⟩
    (by decide) selected_cut_42051

theorem selected_cut_42052 : selected 9 ⟨1149623, by decide⟩
    (prefixPartial 12 337198) = some ⟨12, 2, 0, 1149623, 337198, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_337198_1149623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337198 ⟨1149623, by decide⟩ :=
  accepted_of_selected 12 337198 ⟨1149623, by decide⟩ ⟨12, 2, 0, 1149623, 337198, 2149, 65536⟩
    (by decide) selected_cut_42052

theorem selected_cut_42053 : selected 9 ⟨1149664, by decide⟩
    (prefixPartial 12 337199) = some ⟨12, 2, 0, 1149664, 337199, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_337199_1149664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337199 ⟨1149664, by decide⟩ :=
  accepted_of_selected 12 337199 ⟨1149664, by decide⟩ ⟨12, 2, 0, 1149664, 337199, 2529, 65536⟩
    (by decide) selected_cut_42053

theorem unmarked_context_11_84299_1149665 : frontier 10 ⟨1149665, by decide⟩
    (prefixCache 11 84299) (prefixPartial 11 84299) = false := by
  decide +kernel

theorem node_context_11_84299_1149665 : EJMOriginalGlobalDAGData.nodes 10 ⟨1149665, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1149592, by decide⟩,⟨1149623, by decide⟩,⟨1149664, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84299_1149665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84299 ⟨1149665, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84299
    ⟨1149665, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1149592, by decide⟩,⟨1149623, by decide⟩,⟨1149664, by decide⟩]) unmarked_context_11_84299_1149665 node_context_11_84299_1149665
  intro a
  fin_cases a
  · exact context_12_337196_1108174
  · exact context_12_337197_1149592
  · exact context_12_337198_1149623
  · exact context_12_337199_1149664

theorem unmarked_context_10_21074_1149666 : frontier 11 ⟨1149666, by decide⟩
    (prefixCache 10 21074) (prefixPartial 10 21074) = false := by
  decide +kernel

theorem node_context_10_21074_1149666 : EJMOriginalGlobalDAGData.nodes 11 ⟨1149666, by decide⟩ =
    .split (coordinate 10) (![⟨1149411, by decide⟩,⟨1149491, by decide⟩,⟨1149561, by decide⟩,⟨1149665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21074_1149666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21074 ⟨1149666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21074
    ⟨1149666, by decide⟩ (by decide) (![⟨1149411, by decide⟩,⟨1149491, by decide⟩,⟨1149561, by decide⟩,⟨1149665, by decide⟩]) unmarked_context_10_21074_1149666 node_context_10_21074_1149666
  intro a
  fin_cases a
  · exact context_11_84296_1149411
  · exact context_11_84297_1149491
  · exact context_11_84298_1149561
  · exact context_11_84299_1149665

theorem selected_cut_42054 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337200) = some ⟨12, 1, 0, 1108174, 337200, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337200_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337200 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337200 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337200, 1, 65536⟩
    (by decide) selected_cut_42054

theorem selected_cut_42055 : selected 9 ⟨1149699, by decide⟩
    (prefixPartial 12 337201) = some ⟨12, 2, 0, 1149699, 337201, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_337201_1149699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337201 ⟨1149699, by decide⟩ :=
  accepted_of_selected 12 337201 ⟨1149699, by decide⟩ ⟨12, 2, 0, 1149699, 337201, 2145, 65536⟩
    (by decide) selected_cut_42055

theorem selected_cut_42056 : selected 9 ⟨1149731, by decide⟩
    (prefixPartial 12 337202) = some ⟨12, 2, 0, 1149731, 337202, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_337202_1149731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337202 ⟨1149731, by decide⟩ :=
  accepted_of_selected 12 337202 ⟨1149731, by decide⟩ ⟨12, 2, 0, 1149731, 337202, 2257, 65536⟩
    (by decide) selected_cut_42056

theorem selected_cut_42057 : selected 9 ⟨1149784, by decide⟩
    (prefixPartial 12 337203) = some ⟨12, 2, 0, 1149784, 337203, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_337203_1149784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337203 ⟨1149784, by decide⟩ :=
  accepted_of_selected 12 337203 ⟨1149784, by decide⟩ ⟨12, 2, 0, 1149784, 337203, 2573, 65536⟩
    (by decide) selected_cut_42057

theorem unmarked_context_11_84300_1149785 : frontier 10 ⟨1149785, by decide⟩
    (prefixCache 11 84300) (prefixPartial 11 84300) = false := by
  decide +kernel

theorem node_context_11_84300_1149785 : EJMOriginalGlobalDAGData.nodes 10 ⟨1149785, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1149699, by decide⟩,⟨1149731, by decide⟩,⟨1149784, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84300_1149785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84300 ⟨1149785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84300
    ⟨1149785, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1149699, by decide⟩,⟨1149731, by decide⟩,⟨1149784, by decide⟩]) unmarked_context_11_84300_1149785 node_context_11_84300_1149785
  intro a
  fin_cases a
  · exact context_12_337200_1108174
  · exact context_12_337201_1149699
  · exact context_12_337202_1149731
  · exact context_12_337203_1149784

theorem selected_cut_42058 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337204) = some ⟨12, 1, 0, 1108174, 337204, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337204_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337204 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337204 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337204, 1, 65536⟩
    (by decide) selected_cut_42058

theorem selected_cut_42059 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 337205) = some ⟨12, 1, 0, 891951, 337205, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337205_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337205 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 337205 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 337205, 1, 65536⟩
    (by decide) selected_cut_42059

theorem selected_cut_42060 : selected 9 ⟨1149812, by decide⟩
    (prefixPartial 12 337206) = some ⟨12, 2, 0, 1149812, 337206, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_337206_1149812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337206 ⟨1149812, by decide⟩ :=
  accepted_of_selected 12 337206 ⟨1149812, by decide⟩ ⟨12, 2, 0, 1149812, 337206, 2017, 65536⟩
    (by decide) selected_cut_42060

theorem selected_cut_42061 : selected 9 ⟨1149846, by decide⟩
    (prefixPartial 12 337207) = some ⟨12, 2, 0, 1149846, 337207, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_337207_1149846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337207 ⟨1149846, by decide⟩ :=
  accepted_of_selected 12 337207 ⟨1149846, by decide⟩ ⟨12, 2, 0, 1149846, 337207, 2149, 65536⟩
    (by decide) selected_cut_42061

theorem unmarked_context_11_84301_1149847 : frontier 10 ⟨1149847, by decide⟩
    (prefixCache 11 84301) (prefixPartial 11 84301) = false := by
  decide +kernel

theorem node_context_11_84301_1149847 : EJMOriginalGlobalDAGData.nodes 10 ⟨1149847, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨891951, by decide⟩,⟨1149812, by decide⟩,⟨1149846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84301_1149847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84301 ⟨1149847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84301
    ⟨1149847, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨891951, by decide⟩,⟨1149812, by decide⟩,⟨1149846, by decide⟩]) unmarked_context_11_84301_1149847 node_context_11_84301_1149847
  intro a
  fin_cases a
  · exact context_12_337204_1108174
  · exact context_12_337205_891951
  · exact context_12_337206_1149812
  · exact context_12_337207_1149846

theorem selected_cut_42062 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337208) = some ⟨12, 1, 0, 1108174, 337208, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337208_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337208 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337208 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337208, 1, 65536⟩
    (by decide) selected_cut_42062

theorem selected_cut_42063 : selected 9 ⟨1149876, by decide⟩
    (prefixPartial 12 337209) = some ⟨12, 2, 0, 1149876, 337209, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_337209_1149876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337209 ⟨1149876, by decide⟩ :=
  accepted_of_selected 12 337209 ⟨1149876, by decide⟩ ⟨12, 2, 0, 1149876, 337209, 1981, 65536⟩
    (by decide) selected_cut_42063

theorem selected_cut_42064 : selected 9 ⟨1149902, by decide⟩
    (prefixPartial 12 337210) = some ⟨12, 2, 0, 1149902, 337210, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_337210_1149902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337210 ⟨1149902, by decide⟩ :=
  accepted_of_selected 12 337210 ⟨1149902, by decide⟩ ⟨12, 2, 0, 1149902, 337210, 2033, 65536⟩
    (by decide) selected_cut_42064

theorem selected_cut_42065 : selected 9 ⟨1149940, by decide⟩
    (prefixPartial 12 337211) = some ⟨12, 2, 0, 1149940, 337211, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_337211_1149940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337211 ⟨1149940, by decide⟩ :=
  accepted_of_selected 12 337211 ⟨1149940, by decide⟩ ⟨12, 2, 0, 1149940, 337211, 2241, 65536⟩
    (by decide) selected_cut_42065

theorem unmarked_context_11_84302_1149941 : frontier 10 ⟨1149941, by decide⟩
    (prefixCache 11 84302) (prefixPartial 11 84302) = false := by
  decide +kernel

theorem node_context_11_84302_1149941 : EJMOriginalGlobalDAGData.nodes 10 ⟨1149941, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1149876, by decide⟩,⟨1149902, by decide⟩,⟨1149940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84302_1149941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84302 ⟨1149941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84302
    ⟨1149941, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1149876, by decide⟩,⟨1149902, by decide⟩,⟨1149940, by decide⟩]) unmarked_context_11_84302_1149941 node_context_11_84302_1149941
  intro a
  fin_cases a
  · exact context_12_337208_1108174
  · exact context_12_337209_1149876
  · exact context_12_337210_1149902
  · exact context_12_337211_1149940

theorem selected_cut_42066 : selected 10 ⟨1149992, by decide⟩
    (prefixPartial 11 84303) = some ⟨11, 2, 0, 1149992, 84303, 3737, 262144⟩ := by
  decide +kernel

theorem context_11_84303_1149992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84303 ⟨1149992, by decide⟩ :=
  accepted_of_selected 11 84303 ⟨1149992, by decide⟩ ⟨11, 2, 0, 1149992, 84303, 3737, 262144⟩
    (by decide) selected_cut_42066

theorem unmarked_context_10_21075_1149993 : frontier 11 ⟨1149993, by decide⟩
    (prefixCache 10 21075) (prefixPartial 10 21075) = false := by
  decide +kernel

theorem node_context_10_21075_1149993 : EJMOriginalGlobalDAGData.nodes 11 ⟨1149993, by decide⟩ =
    .split (coordinate 10) (![⟨1149785, by decide⟩,⟨1149847, by decide⟩,⟨1149941, by decide⟩,⟨1149992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21075_1149993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21075 ⟨1149993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21075
    ⟨1149993, by decide⟩ (by decide) (![⟨1149785, by decide⟩,⟨1149847, by decide⟩,⟨1149941, by decide⟩,⟨1149992, by decide⟩]) unmarked_context_10_21075_1149993 node_context_10_21075_1149993
  intro a
  fin_cases a
  · exact context_11_84300_1149785
  · exact context_11_84301_1149847
  · exact context_11_84302_1149941
  · exact context_11_84303_1149992

theorem unmarked_context_9_5268_1149994 : frontier 12 ⟨1149994, by decide⟩
    (prefixCache 9 5268) (prefixPartial 9 5268) = false := by
  decide +kernel

theorem node_context_9_5268_1149994 : EJMOriginalGlobalDAGData.nodes 12 ⟨1149994, by decide⟩ =
    .split (coordinate 9) (![⟨1148906, by decide⟩,⟨1149263, by decide⟩,⟨1149666, by decide⟩,⟨1149993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5268_1149994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5268 ⟨1149994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5268
    ⟨1149994, by decide⟩ (by decide) (![⟨1148906, by decide⟩,⟨1149263, by decide⟩,⟨1149666, by decide⟩,⟨1149993, by decide⟩]) unmarked_context_9_5268_1149994 node_context_9_5268_1149994
  intro a
  fin_cases a
  · exact context_10_21072_1148906
  · exact context_10_21073_1149263
  · exact context_10_21074_1149666
  · exact context_10_21075_1149993

theorem selected_cut_42067 : selected 10 ⟨1150057, by decide⟩
    (prefixPartial 11 84304) = some ⟨11, 2, 0, 1150057, 84304, 4065, 262144⟩ := by
  decide +kernel

theorem context_11_84304_1150057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84304 ⟨1150057, by decide⟩ :=
  accepted_of_selected 11 84304 ⟨1150057, by decide⟩ ⟨11, 2, 0, 1150057, 84304, 4065, 262144⟩
    (by decide) selected_cut_42067

theorem selected_cut_42068 : selected 9 ⟨1150084, by decide⟩
    (prefixPartial 12 337220) = some ⟨12, 2, 0, 1150084, 337220, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_337220_1150084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337220 ⟨1150084, by decide⟩ :=
  accepted_of_selected 12 337220 ⟨1150084, by decide⟩ ⟨12, 2, 0, 1150084, 337220, 1301, 65536⟩
    (by decide) selected_cut_42068

theorem selected_cut_42069 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 337221) = some ⟨12, 1, 0, 170504, 337221, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337221_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337221 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 337221 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 337221, 1, 65536⟩
    (by decide) selected_cut_42069

theorem selected_cut_42070 : selected 9 ⟨1150105, by decide⟩
    (prefixPartial 12 337222) = some ⟨12, 2, 0, 1150105, 337222, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_337222_1150105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337222 ⟨1150105, by decide⟩ :=
  accepted_of_selected 12 337222 ⟨1150105, by decide⟩ ⟨12, 2, 0, 1150105, 337222, 1517, 65536⟩
    (by decide) selected_cut_42070

theorem selected_cut_42071 : selected 9 ⟨1150126, by decide⟩
    (prefixPartial 12 337223) = some ⟨12, 2, 0, 1150126, 337223, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_337223_1150126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337223 ⟨1150126, by decide⟩ :=
  accepted_of_selected 12 337223 ⟨1150126, by decide⟩ ⟨12, 2, 0, 1150126, 337223, 1513, 65536⟩
    (by decide) selected_cut_42071

theorem unmarked_context_11_84305_1150127 : frontier 10 ⟨1150127, by decide⟩
    (prefixCache 11 84305) (prefixPartial 11 84305) = false := by
  decide +kernel

theorem node_context_11_84305_1150127 : EJMOriginalGlobalDAGData.nodes 10 ⟨1150127, by decide⟩ =
    .split (coordinate 11) (![⟨1150084, by decide⟩,⟨170504, by decide⟩,⟨1150105, by decide⟩,⟨1150126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84305_1150127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84305 ⟨1150127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84305
    ⟨1150127, by decide⟩ (by decide) (![⟨1150084, by decide⟩,⟨170504, by decide⟩,⟨1150105, by decide⟩,⟨1150126, by decide⟩]) unmarked_context_11_84305_1150127 node_context_11_84305_1150127
  intro a
  fin_cases a
  · exact context_12_337220_1150084
  · exact context_12_337221_170504
  · exact context_12_337222_1150105
  · exact context_12_337223_1150126

theorem selected_cut_42072 : selected 9 ⟨1150146, by decide⟩
    (prefixPartial 12 337224) = some ⟨12, 2, 0, 1150146, 337224, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_337224_1150146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337224 ⟨1150146, by decide⟩ :=
  accepted_of_selected 12 337224 ⟨1150146, by decide⟩ ⟨12, 2, 0, 1150146, 337224, 1529, 65536⟩
    (by decide) selected_cut_42072

theorem selected_cut_42073 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 337225) = some ⟨12, 1, 0, 126371, 337225, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337225_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337225 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 337225 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 337225, 1, 65536⟩
    (by decide) selected_cut_42073

theorem selected_cut_42074 : selected 9 ⟨1150178, by decide⟩
    (prefixPartial 12 337226) = some ⟨12, 2, 0, 1150178, 337226, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_337226_1150178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337226 ⟨1150178, by decide⟩ :=
  accepted_of_selected 12 337226 ⟨1150178, by decide⟩ ⟨12, 2, 0, 1150178, 337226, 1949, 65536⟩
    (by decide) selected_cut_42074

theorem selected_cut_42075 : selected 9 ⟨1150209, by decide⟩
    (prefixPartial 12 337227) = some ⟨12, 2, 0, 1150209, 337227, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_337227_1150209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337227 ⟨1150209, by decide⟩ :=
  accepted_of_selected 12 337227 ⟨1150209, by decide⟩ ⟨12, 2, 0, 1150209, 337227, 1937, 65536⟩
    (by decide) selected_cut_42075

theorem unmarked_context_11_84306_1150210 : frontier 10 ⟨1150210, by decide⟩
    (prefixCache 11 84306) (prefixPartial 11 84306) = false := by
  decide +kernel

theorem node_context_11_84306_1150210 : EJMOriginalGlobalDAGData.nodes 10 ⟨1150210, by decide⟩ =
    .split (coordinate 11) (![⟨1150146, by decide⟩,⟨126371, by decide⟩,⟨1150178, by decide⟩,⟨1150209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84306_1150210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84306 ⟨1150210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84306
    ⟨1150210, by decide⟩ (by decide) (![⟨1150146, by decide⟩,⟨126371, by decide⟩,⟨1150178, by decide⟩,⟨1150209, by decide⟩]) unmarked_context_11_84306_1150210 node_context_11_84306_1150210
  intro a
  fin_cases a
  · exact context_12_337224_1150146
  · exact context_12_337225_126371
  · exact context_12_337226_1150178
  · exact context_12_337227_1150209

theorem selected_cut_42076 : selected 9 ⟨1150229, by decide⟩
    (prefixPartial 12 337228) = some ⟨12, 2, 0, 1150229, 337228, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_337228_1150229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337228 ⟨1150229, by decide⟩ :=
  accepted_of_selected 12 337228 ⟨1150229, by decide⟩ ⟨12, 2, 0, 1150229, 337228, 1525, 65536⟩
    (by decide) selected_cut_42076

theorem selected_cut_42077 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 337229) = some ⟨12, 1, 0, 320864, 337229, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337229_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337229 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 337229 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 337229, 1, 65536⟩
    (by decide) selected_cut_42077

theorem selected_cut_42078 : selected 9 ⟨1150260, by decide⟩
    (prefixPartial 12 337230) = some ⟨12, 2, 0, 1150260, 337230, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_337230_1150260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337230 ⟨1150260, by decide⟩ :=
  accepted_of_selected 12 337230 ⟨1150260, by decide⟩ ⟨12, 2, 0, 1150260, 337230, 1861, 65536⟩
    (by decide) selected_cut_42078

theorem selected_cut_42079 : selected 9 ⟨1150290, by decide⟩
    (prefixPartial 12 337231) = some ⟨12, 2, 0, 1150290, 337231, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_337231_1150290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337231 ⟨1150290, by decide⟩ :=
  accepted_of_selected 12 337231 ⟨1150290, by decide⟩ ⟨12, 2, 0, 1150290, 337231, 1973, 65536⟩
    (by decide) selected_cut_42079

theorem unmarked_context_11_84307_1150291 : frontier 10 ⟨1150291, by decide⟩
    (prefixCache 11 84307) (prefixPartial 11 84307) = false := by
  decide +kernel

theorem node_context_11_84307_1150291 : EJMOriginalGlobalDAGData.nodes 10 ⟨1150291, by decide⟩ =
    .split (coordinate 11) (![⟨1150229, by decide⟩,⟨320864, by decide⟩,⟨1150260, by decide⟩,⟨1150290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84307_1150291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84307 ⟨1150291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84307
    ⟨1150291, by decide⟩ (by decide) (![⟨1150229, by decide⟩,⟨320864, by decide⟩,⟨1150260, by decide⟩,⟨1150290, by decide⟩]) unmarked_context_11_84307_1150291 node_context_11_84307_1150291
  intro a
  fin_cases a
  · exact context_12_337228_1150229
  · exact context_12_337229_320864
  · exact context_12_337230_1150260
  · exact context_12_337231_1150290

theorem unmarked_context_10_21076_1150292 : frontier 11 ⟨1150292, by decide⟩
    (prefixCache 10 21076) (prefixPartial 10 21076) = false := by
  decide +kernel

theorem node_context_10_21076_1150292 : EJMOriginalGlobalDAGData.nodes 11 ⟨1150292, by decide⟩ =
    .split (coordinate 10) (![⟨1150057, by decide⟩,⟨1150127, by decide⟩,⟨1150210, by decide⟩,⟨1150291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21076_1150292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21076 ⟨1150292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21076
    ⟨1150292, by decide⟩ (by decide) (![⟨1150057, by decide⟩,⟨1150127, by decide⟩,⟨1150210, by decide⟩,⟨1150291, by decide⟩]) unmarked_context_10_21076_1150292 node_context_10_21076_1150292
  intro a
  fin_cases a
  · exact context_11_84304_1150057
  · exact context_11_84305_1150127
  · exact context_11_84306_1150210
  · exact context_11_84307_1150291

theorem selected_cut_42080 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21077) = some ⟨10, 1, 0, 893098, 21077, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21077_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21077 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21077 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21077, 1, 1048576⟩
    (by decide) selected_cut_42080

theorem selected_cut_42081 : selected 9 ⟨1150322, by decide⟩
    (prefixPartial 12 337248) = some ⟨12, 2, 0, 1150322, 337248, 857, 65536⟩ := by
  decide +kernel

theorem context_12_337248_1150322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337248 ⟨1150322, by decide⟩ :=
  accepted_of_selected 12 337248 ⟨1150322, by decide⟩ ⟨12, 2, 0, 1150322, 337248, 857, 65536⟩
    (by decide) selected_cut_42081

theorem selected_cut_42082 : selected 9 ⟨219808, by decide⟩
    (prefixPartial 12 337249) = some ⟨12, 1, 0, 219808, 337249, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337249_219808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337249 ⟨219808, by decide⟩ :=
  accepted_of_selected 12 337249 ⟨219808, by decide⟩ ⟨12, 1, 0, 219808, 337249, 1, 65536⟩
    (by decide) selected_cut_42082

theorem selected_cut_42083 : selected 9 ⟨1150345, by decide⟩
    (prefixPartial 12 337250) = some ⟨12, 2, 0, 1150345, 337250, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_337250_1150345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337250 ⟨1150345, by decide⟩ :=
  accepted_of_selected 12 337250 ⟨1150345, by decide⟩ ⟨12, 2, 0, 1150345, 337250, 1697, 65536⟩
    (by decide) selected_cut_42083

theorem selected_cut_42084 : selected 9 ⟨1150370, by decide⟩
    (prefixPartial 12 337251) = some ⟨12, 2, 0, 1150370, 337251, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_337251_1150370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337251 ⟨1150370, by decide⟩ :=
  accepted_of_selected 12 337251 ⟨1150370, by decide⟩ ⟨12, 2, 0, 1150370, 337251, 1745, 65536⟩
    (by decide) selected_cut_42084

theorem unmarked_context_11_84312_1150371 : frontier 10 ⟨1150371, by decide⟩
    (prefixCache 11 84312) (prefixPartial 11 84312) = false := by
  decide +kernel

theorem node_context_11_84312_1150371 : EJMOriginalGlobalDAGData.nodes 10 ⟨1150371, by decide⟩ =
    .split (coordinate 11) (![⟨1150322, by decide⟩,⟨219808, by decide⟩,⟨1150345, by decide⟩,⟨1150370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84312_1150371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84312 ⟨1150371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84312
    ⟨1150371, by decide⟩ (by decide) (![⟨1150322, by decide⟩,⟨219808, by decide⟩,⟨1150345, by decide⟩,⟨1150370, by decide⟩]) unmarked_context_11_84312_1150371 node_context_11_84312_1150371
  intro a
  fin_cases a
  · exact context_12_337248_1150322
  · exact context_12_337249_219808
  · exact context_12_337250_1150345
  · exact context_12_337251_1150370

theorem selected_cut_42085 : selected 10 ⟨1150425, by decide⟩
    (prefixPartial 11 84313) = some ⟨11, 2, 0, 1150425, 84313, 3957, 262144⟩ := by
  decide +kernel

theorem context_11_84313_1150425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84313 ⟨1150425, by decide⟩ :=
  accepted_of_selected 11 84313 ⟨1150425, by decide⟩ ⟨11, 2, 0, 1150425, 84313, 3957, 262144⟩
    (by decide) selected_cut_42085

theorem selected_cut_42086 : selected 9 ⟨1150441, by decide⟩
    (prefixPartial 12 337256) = some ⟨12, 2, 0, 1150441, 337256, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_337256_1150441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337256 ⟨1150441, by decide⟩ :=
  accepted_of_selected 12 337256 ⟨1150441, by decide⟩ ⟨12, 2, 0, 1150441, 337256, 1341, 65536⟩
    (by decide) selected_cut_42086

theorem selected_cut_42087 : selected 9 ⟨1150458, by decide⟩
    (prefixPartial 12 337257) = some ⟨12, 2, 0, 1150458, 337257, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_337257_1150458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337257 ⟨1150458, by decide⟩ :=
  accepted_of_selected 12 337257 ⟨1150458, by decide⟩ ⟨12, 2, 0, 1150458, 337257, 1337, 65536⟩
    (by decide) selected_cut_42087

theorem selected_cut_42088 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 337258) = some ⟨12, 1, 0, 1113261, 337258, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337258_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337258 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 337258 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 337258, 1, 65536⟩
    (by decide) selected_cut_42088

theorem selected_cut_42089 : selected 9 ⟨1150483, by decide⟩
    (prefixPartial 12 337259) = some ⟨12, 2, 0, 1150483, 337259, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_337259_1150483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337259 ⟨1150483, by decide⟩ :=
  accepted_of_selected 12 337259 ⟨1150483, by decide⟩ ⟨12, 2, 0, 1150483, 337259, 1621, 65536⟩
    (by decide) selected_cut_42089

theorem unmarked_context_11_84314_1150484 : frontier 10 ⟨1150484, by decide⟩
    (prefixCache 11 84314) (prefixPartial 11 84314) = false := by
  decide +kernel

theorem node_context_11_84314_1150484 : EJMOriginalGlobalDAGData.nodes 10 ⟨1150484, by decide⟩ =
    .split (coordinate 11) (![⟨1150441, by decide⟩,⟨1150458, by decide⟩,⟨1113261, by decide⟩,⟨1150483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84314_1150484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84314 ⟨1150484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84314
    ⟨1150484, by decide⟩ (by decide) (![⟨1150441, by decide⟩,⟨1150458, by decide⟩,⟨1113261, by decide⟩,⟨1150483, by decide⟩]) unmarked_context_11_84314_1150484 node_context_11_84314_1150484
  intro a
  fin_cases a
  · exact context_12_337256_1150441
  · exact context_12_337257_1150458
  · exact context_12_337258_1113261
  · exact context_12_337259_1150483

theorem selected_cut_42090 : selected 9 ⟨1150498, by decide⟩
    (prefixPartial 12 337260) = some ⟨12, 2, 0, 1150498, 337260, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_337260_1150498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337260 ⟨1150498, by decide⟩ :=
  accepted_of_selected 12 337260 ⟨1150498, by decide⟩ ⟨12, 2, 0, 1150498, 337260, 1409, 65536⟩
    (by decide) selected_cut_42090

theorem selected_cut_42091 : selected 9 ⟨1150515, by decide⟩
    (prefixPartial 12 337261) = some ⟨12, 2, 0, 1150515, 337261, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_337261_1150515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337261 ⟨1150515, by decide⟩ :=
  accepted_of_selected 12 337261 ⟨1150515, by decide⟩ ⟨12, 2, 0, 1150515, 337261, 1353, 65536⟩
    (by decide) selected_cut_42091

theorem selected_cut_42092 : selected 9 ⟨1150532, by decide⟩
    (prefixPartial 12 337262) = some ⟨12, 2, 0, 1150532, 337262, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_337262_1150532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337262 ⟨1150532, by decide⟩ :=
  accepted_of_selected 12 337262 ⟨1150532, by decide⟩ ⟨12, 2, 0, 1150532, 337262, 1505, 65536⟩
    (by decide) selected_cut_42092

theorem selected_cut_42093 : selected 9 ⟨1150556, by decide⟩
    (prefixPartial 12 337263) = some ⟨12, 2, 0, 1150556, 337263, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_337263_1150556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337263 ⟨1150556, by decide⟩ :=
  accepted_of_selected 12 337263 ⟨1150556, by decide⟩ ⟨12, 2, 0, 1150556, 337263, 1657, 65536⟩
    (by decide) selected_cut_42093

theorem unmarked_context_11_84315_1150557 : frontier 10 ⟨1150557, by decide⟩
    (prefixCache 11 84315) (prefixPartial 11 84315) = false := by
  decide +kernel

theorem node_context_11_84315_1150557 : EJMOriginalGlobalDAGData.nodes 10 ⟨1150557, by decide⟩ =
    .split (coordinate 11) (![⟨1150498, by decide⟩,⟨1150515, by decide⟩,⟨1150532, by decide⟩,⟨1150556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84315_1150557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84315 ⟨1150557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84315
    ⟨1150557, by decide⟩ (by decide) (![⟨1150498, by decide⟩,⟨1150515, by decide⟩,⟨1150532, by decide⟩,⟨1150556, by decide⟩]) unmarked_context_11_84315_1150557 node_context_11_84315_1150557
  intro a
  fin_cases a
  · exact context_12_337260_1150498
  · exact context_12_337261_1150515
  · exact context_12_337262_1150532
  · exact context_12_337263_1150556

theorem unmarked_context_10_21078_1150558 : frontier 11 ⟨1150558, by decide⟩
    (prefixCache 10 21078) (prefixPartial 10 21078) = false := by
  decide +kernel

theorem node_context_10_21078_1150558 : EJMOriginalGlobalDAGData.nodes 11 ⟨1150558, by decide⟩ =
    .split (coordinate 10) (![⟨1150371, by decide⟩,⟨1150425, by decide⟩,⟨1150484, by decide⟩,⟨1150557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21078_1150558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21078 ⟨1150558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21078
    ⟨1150558, by decide⟩ (by decide) (![⟨1150371, by decide⟩,⟨1150425, by decide⟩,⟨1150484, by decide⟩,⟨1150557, by decide⟩]) unmarked_context_10_21078_1150558 node_context_10_21078_1150558
  intro a
  fin_cases a
  · exact context_11_84312_1150371
  · exact context_11_84313_1150425
  · exact context_11_84314_1150484
  · exact context_11_84315_1150557

theorem selected_cut_42094 : selected 10 ⟨1150637, by decide⟩
    (prefixPartial 11 84316) = some ⟨11, 2, 0, 1150637, 84316, 3965, 262144⟩ := by
  decide +kernel

theorem context_11_84316_1150637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84316 ⟨1150637, by decide⟩ :=
  accepted_of_selected 11 84316 ⟨1150637, by decide⟩ ⟨11, 2, 0, 1150637, 84316, 3965, 262144⟩
    (by decide) selected_cut_42094

theorem selected_cut_42095 : selected 10 ⟨1150681, by decide⟩
    (prefixPartial 11 84317) = some ⟨11, 2, 0, 1150681, 84317, 3625, 262144⟩ := by
  decide +kernel

theorem context_11_84317_1150681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84317 ⟨1150681, by decide⟩ :=
  accepted_of_selected 11 84317 ⟨1150681, by decide⟩ ⟨11, 2, 0, 1150681, 84317, 3625, 262144⟩
    (by decide) selected_cut_42095

theorem selected_cut_42096 : selected 9 ⟨1150693, by decide⟩
    (prefixPartial 12 337272) = some ⟨12, 2, 0, 1150693, 337272, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_337272_1150693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337272 ⟨1150693, by decide⟩ :=
  accepted_of_selected 12 337272 ⟨1150693, by decide⟩ ⟨12, 2, 0, 1150693, 337272, 1281, 65536⟩
    (by decide) selected_cut_42096

theorem selected_cut_42097 : selected 9 ⟨1150712, by decide⟩
    (prefixPartial 12 337273) = some ⟨12, 2, 0, 1150712, 337273, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_337273_1150712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337273 ⟨1150712, by decide⟩ :=
  accepted_of_selected 12 337273 ⟨1150712, by decide⟩ ⟨12, 2, 0, 1150712, 337273, 1293, 65536⟩
    (by decide) selected_cut_42097

theorem selected_cut_42098 : selected 9 ⟨1150733, by decide⟩
    (prefixPartial 12 337274) = some ⟨12, 2, 0, 1150733, 337274, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_337274_1150733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337274 ⟨1150733, by decide⟩ :=
  accepted_of_selected 12 337274 ⟨1150733, by decide⟩ ⟨12, 2, 0, 1150733, 337274, 1429, 65536⟩
    (by decide) selected_cut_42098

theorem selected_cut_42099 : selected 9 ⟨1150751, by decide⟩
    (prefixPartial 12 337275) = some ⟨12, 2, 0, 1150751, 337275, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_337275_1150751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337275 ⟨1150751, by decide⟩ :=
  accepted_of_selected 12 337275 ⟨1150751, by decide⟩ ⟨12, 2, 0, 1150751, 337275, 1445, 65536⟩
    (by decide) selected_cut_42099

theorem unmarked_context_11_84318_1150752 : frontier 10 ⟨1150752, by decide⟩
    (prefixCache 11 84318) (prefixPartial 11 84318) = false := by
  decide +kernel

theorem node_context_11_84318_1150752 : EJMOriginalGlobalDAGData.nodes 10 ⟨1150752, by decide⟩ =
    .split (coordinate 11) (![⟨1150693, by decide⟩,⟨1150712, by decide⟩,⟨1150733, by decide⟩,⟨1150751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84318_1150752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84318 ⟨1150752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84318
    ⟨1150752, by decide⟩ (by decide) (![⟨1150693, by decide⟩,⟨1150712, by decide⟩,⟨1150733, by decide⟩,⟨1150751, by decide⟩]) unmarked_context_11_84318_1150752 node_context_11_84318_1150752
  intro a
  fin_cases a
  · exact context_12_337272_1150693
  · exact context_12_337273_1150712
  · exact context_12_337274_1150733
  · exact context_12_337275_1150751

theorem selected_cut_42100 : selected 10 ⟨1150800, by decide⟩
    (prefixPartial 11 84319) = some ⟨11, 2, 0, 1150800, 84319, 3649, 262144⟩ := by
  decide +kernel

theorem context_11_84319_1150800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84319 ⟨1150800, by decide⟩ :=
  accepted_of_selected 11 84319 ⟨1150800, by decide⟩ ⟨11, 2, 0, 1150800, 84319, 3649, 262144⟩
    (by decide) selected_cut_42100

theorem unmarked_context_10_21079_1150801 : frontier 11 ⟨1150801, by decide⟩
    (prefixCache 10 21079) (prefixPartial 10 21079) = false := by
  decide +kernel

theorem node_context_10_21079_1150801 : EJMOriginalGlobalDAGData.nodes 11 ⟨1150801, by decide⟩ =
    .split (coordinate 10) (![⟨1150637, by decide⟩,⟨1150681, by decide⟩,⟨1150752, by decide⟩,⟨1150800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21079_1150801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21079 ⟨1150801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21079
    ⟨1150801, by decide⟩ (by decide) (![⟨1150637, by decide⟩,⟨1150681, by decide⟩,⟨1150752, by decide⟩,⟨1150800, by decide⟩]) unmarked_context_10_21079_1150801 node_context_10_21079_1150801
  intro a
  fin_cases a
  · exact context_11_84316_1150637
  · exact context_11_84317_1150681
  · exact context_11_84318_1150752
  · exact context_11_84319_1150800

theorem unmarked_context_9_5269_1150802 : frontier 12 ⟨1150802, by decide⟩
    (prefixCache 9 5269) (prefixPartial 9 5269) = false := by
  decide +kernel

theorem node_context_9_5269_1150802 : EJMOriginalGlobalDAGData.nodes 12 ⟨1150802, by decide⟩ =
    .split (coordinate 9) (![⟨1150292, by decide⟩,⟨893098, by decide⟩,⟨1150558, by decide⟩,⟨1150801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5269_1150802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5269 ⟨1150802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5269
    ⟨1150802, by decide⟩ (by decide) (![⟨1150292, by decide⟩,⟨893098, by decide⟩,⟨1150558, by decide⟩,⟨1150801, by decide⟩]) unmarked_context_9_5269_1150802 node_context_9_5269_1150802
  intro a
  fin_cases a
  · exact context_10_21076_1150292
  · exact context_10_21077_893098
  · exact context_10_21078_1150558
  · exact context_10_21079_1150801

theorem selected_cut_42101 : selected 10 ⟨1150845, by decide⟩
    (prefixPartial 11 84320) = some ⟨11, 2, 0, 1150845, 84320, 3717, 262144⟩ := by
  decide +kernel

theorem context_11_84320_1150845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84320 ⟨1150845, by decide⟩ :=
  accepted_of_selected 11 84320 ⟨1150845, by decide⟩ ⟨11, 2, 0, 1150845, 84320, 3717, 262144⟩
    (by decide) selected_cut_42101

theorem selected_cut_42102 : selected 10 ⟨1150900, by decide⟩
    (prefixPartial 11 84321) = some ⟨11, 2, 0, 1150900, 84321, 3517, 262144⟩ := by
  decide +kernel

theorem context_11_84321_1150900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84321 ⟨1150900, by decide⟩ :=
  accepted_of_selected 11 84321 ⟨1150900, by decide⟩ ⟨11, 2, 0, 1150900, 84321, 3517, 262144⟩
    (by decide) selected_cut_42102

theorem selected_cut_42103 : selected 9 ⟨1150920, by decide⟩
    (prefixPartial 12 337288) = some ⟨12, 2, 0, 1150920, 337288, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_337288_1150920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337288 ⟨1150920, by decide⟩ :=
  accepted_of_selected 12 337288 ⟨1150920, by decide⟩ ⟨12, 2, 0, 1150920, 337288, 1289, 65536⟩
    (by decide) selected_cut_42103

theorem selected_cut_42104 : selected 9 ⟨1150940, by decide⟩
    (prefixPartial 12 337289) = some ⟨12, 2, 0, 1150940, 337289, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_337289_1150940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337289 ⟨1150940, by decide⟩ :=
  accepted_of_selected 12 337289 ⟨1150940, by decide⟩ ⟨12, 2, 0, 1150940, 337289, 1313, 65536⟩
    (by decide) selected_cut_42104

theorem selected_cut_42105 : selected 9 ⟨1109520, by decide⟩
    (prefixPartial 12 337290) = some ⟨12, 1, 0, 1109520, 337290, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337290_1109520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337290 ⟨1109520, by decide⟩ :=
  accepted_of_selected 12 337290 ⟨1109520, by decide⟩ ⟨12, 1, 0, 1109520, 337290, 1, 65536⟩
    (by decide) selected_cut_42105

theorem selected_cut_42106 : selected 9 ⟨1150967, by decide⟩
    (prefixPartial 12 337291) = some ⟨12, 2, 0, 1150967, 337291, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_337291_1150967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337291 ⟨1150967, by decide⟩ :=
  accepted_of_selected 12 337291 ⟨1150967, by decide⟩ ⟨12, 2, 0, 1150967, 337291, 1513, 65536⟩
    (by decide) selected_cut_42106

theorem unmarked_context_11_84322_1150968 : frontier 10 ⟨1150968, by decide⟩
    (prefixCache 11 84322) (prefixPartial 11 84322) = false := by
  decide +kernel

theorem node_context_11_84322_1150968 : EJMOriginalGlobalDAGData.nodes 10 ⟨1150968, by decide⟩ =
    .split (coordinate 11) (![⟨1150920, by decide⟩,⟨1150940, by decide⟩,⟨1109520, by decide⟩,⟨1150967, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84322_1150968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84322 ⟨1150968, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84322
    ⟨1150968, by decide⟩ (by decide) (![⟨1150920, by decide⟩,⟨1150940, by decide⟩,⟨1109520, by decide⟩,⟨1150967, by decide⟩]) unmarked_context_11_84322_1150968 node_context_11_84322_1150968
  intro a
  fin_cases a
  · exact context_12_337288_1150920
  · exact context_12_337289_1150940
  · exact context_12_337290_1109520
  · exact context_12_337291_1150967

theorem selected_cut_42107 : selected 9 ⟨1150980, by decide⟩
    (prefixPartial 12 337292) = some ⟨12, 2, 0, 1150980, 337292, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_337292_1150980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337292 ⟨1150980, by decide⟩ :=
  accepted_of_selected 12 337292 ⟨1150980, by decide⟩ ⟨12, 2, 0, 1150980, 337292, 1065, 65536⟩
    (by decide) selected_cut_42107

theorem selected_cut_42108 : selected 9 ⟨1150991, by decide⟩
    (prefixPartial 12 337293) = some ⟨12, 2, 0, 1150991, 337293, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_337293_1150991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337293 ⟨1150991, by decide⟩ :=
  accepted_of_selected 12 337293 ⟨1150991, by decide⟩ ⟨12, 2, 0, 1150991, 337293, 1089, 65536⟩
    (by decide) selected_cut_42108

theorem selected_cut_42109 : selected 9 ⟨1151012, by decide⟩
    (prefixPartial 12 337294) = some ⟨12, 2, 0, 1151012, 337294, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_337294_1151012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337294 ⟨1151012, by decide⟩ :=
  accepted_of_selected 12 337294 ⟨1151012, by decide⟩ ⟨12, 2, 0, 1151012, 337294, 1217, 65536⟩
    (by decide) selected_cut_42109

theorem selected_cut_42110 : selected 9 ⟨1151033, by decide⟩
    (prefixPartial 12 337295) = some ⟨12, 2, 0, 1151033, 337295, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_337295_1151033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337295 ⟨1151033, by decide⟩ :=
  accepted_of_selected 12 337295 ⟨1151033, by decide⟩ ⟨12, 2, 0, 1151033, 337295, 1277, 65536⟩
    (by decide) selected_cut_42110

theorem unmarked_context_11_84323_1151034 : frontier 10 ⟨1151034, by decide⟩
    (prefixCache 11 84323) (prefixPartial 11 84323) = false := by
  decide +kernel

theorem node_context_11_84323_1151034 : EJMOriginalGlobalDAGData.nodes 10 ⟨1151034, by decide⟩ =
    .split (coordinate 11) (![⟨1150980, by decide⟩,⟨1150991, by decide⟩,⟨1151012, by decide⟩,⟨1151033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84323_1151034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84323 ⟨1151034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84323
    ⟨1151034, by decide⟩ (by decide) (![⟨1150980, by decide⟩,⟨1150991, by decide⟩,⟨1151012, by decide⟩,⟨1151033, by decide⟩]) unmarked_context_11_84323_1151034 node_context_11_84323_1151034
  intro a
  fin_cases a
  · exact context_12_337292_1150980
  · exact context_12_337293_1150991
  · exact context_12_337294_1151012
  · exact context_12_337295_1151033

theorem unmarked_context_10_21080_1151035 : frontier 11 ⟨1151035, by decide⟩
    (prefixCache 10 21080) (prefixPartial 10 21080) = false := by
  decide +kernel

theorem node_context_10_21080_1151035 : EJMOriginalGlobalDAGData.nodes 11 ⟨1151035, by decide⟩ =
    .split (coordinate 10) (![⟨1150845, by decide⟩,⟨1150900, by decide⟩,⟨1150968, by decide⟩,⟨1151034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21080_1151035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21080 ⟨1151035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21080
    ⟨1151035, by decide⟩ (by decide) (![⟨1150845, by decide⟩,⟨1150900, by decide⟩,⟨1150968, by decide⟩,⟨1151034, by decide⟩]) unmarked_context_10_21080_1151035 node_context_10_21080_1151035
  intro a
  fin_cases a
  · exact context_11_84320_1150845
  · exact context_11_84321_1150900
  · exact context_11_84322_1150968
  · exact context_11_84323_1151034

theorem selected_cut_42111 : selected 10 ⟨1151077, by decide⟩
    (prefixPartial 11 84324) = some ⟨11, 2, 0, 1151077, 84324, 3717, 262144⟩ := by
  decide +kernel

theorem context_11_84324_1151077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84324 ⟨1151077, by decide⟩ :=
  accepted_of_selected 11 84324 ⟨1151077, by decide⟩ ⟨11, 2, 0, 1151077, 84324, 3717, 262144⟩
    (by decide) selected_cut_42111

theorem selected_cut_42112 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 84325) = some ⟨11, 1, 0, 892405, 84325, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84325_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84325 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 84325 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 84325, 1, 262144⟩
    (by decide) selected_cut_42112

theorem selected_cut_42113 : selected 10 ⟨1151122, by decide⟩
    (prefixPartial 11 84326) = some ⟨11, 2, 0, 1151122, 84326, 3109, 262144⟩ := by
  decide +kernel

theorem context_11_84326_1151122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84326 ⟨1151122, by decide⟩ :=
  accepted_of_selected 11 84326 ⟨1151122, by decide⟩ ⟨11, 2, 0, 1151122, 84326, 3109, 262144⟩
    (by decide) selected_cut_42113

theorem selected_cut_42114 : selected 10 ⟨1151167, by decide⟩
    (prefixPartial 11 84327) = some ⟨11, 2, 0, 1151167, 84327, 3545, 262144⟩ := by
  decide +kernel

theorem context_11_84327_1151167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84327 ⟨1151167, by decide⟩ :=
  accepted_of_selected 11 84327 ⟨1151167, by decide⟩ ⟨11, 2, 0, 1151167, 84327, 3545, 262144⟩
    (by decide) selected_cut_42114

theorem unmarked_context_10_21081_1151168 : frontier 11 ⟨1151168, by decide⟩
    (prefixCache 10 21081) (prefixPartial 10 21081) = false := by
  decide +kernel

theorem node_context_10_21081_1151168 : EJMOriginalGlobalDAGData.nodes 11 ⟨1151168, by decide⟩ =
    .split (coordinate 10) (![⟨1151077, by decide⟩,⟨892405, by decide⟩,⟨1151122, by decide⟩,⟨1151167, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21081_1151168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21081 ⟨1151168, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21081
    ⟨1151168, by decide⟩ (by decide) (![⟨1151077, by decide⟩,⟨892405, by decide⟩,⟨1151122, by decide⟩,⟨1151167, by decide⟩]) unmarked_context_10_21081_1151168 node_context_10_21081_1151168
  intro a
  fin_cases a
  · exact context_11_84324_1151077
  · exact context_11_84325_892405
  · exact context_11_84326_1151122
  · exact context_11_84327_1151167

theorem selected_cut_42115 : selected 10 ⟨1151200, by decide⟩
    (prefixPartial 11 84328) = some ⟨11, 2, 0, 1151200, 84328, 2437, 262144⟩ := by
  decide +kernel

theorem context_11_84328_1151200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84328 ⟨1151200, by decide⟩ :=
  accepted_of_selected 11 84328 ⟨1151200, by decide⟩ ⟨11, 2, 0, 1151200, 84328, 2437, 262144⟩
    (by decide) selected_cut_42115

theorem selected_cut_42116 : selected 10 ⟨1151227, by decide⟩
    (prefixPartial 11 84329) = some ⟨11, 2, 0, 1151227, 84329, 1653, 262144⟩ := by
  decide +kernel

theorem context_11_84329_1151227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84329 ⟨1151227, by decide⟩ :=
  accepted_of_selected 11 84329 ⟨1151227, by decide⟩ ⟨11, 2, 0, 1151227, 84329, 1653, 262144⟩
    (by decide) selected_cut_42116

theorem selected_cut_42117 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84330) = some ⟨11, 1, 0, 1109453, 84330, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84330_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84330 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84330 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84330, 1, 262144⟩
    (by decide) selected_cut_42117

theorem selected_cut_42118 : selected 10 ⟨1151255, by decide⟩
    (prefixPartial 11 84331) = some ⟨11, 2, 0, 1151255, 84331, 2313, 262144⟩ := by
  decide +kernel

theorem context_11_84331_1151255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84331 ⟨1151255, by decide⟩ :=
  accepted_of_selected 11 84331 ⟨1151255, by decide⟩ ⟨11, 2, 0, 1151255, 84331, 2313, 262144⟩
    (by decide) selected_cut_42118

theorem unmarked_context_10_21082_1151256 : frontier 11 ⟨1151256, by decide⟩
    (prefixCache 10 21082) (prefixPartial 10 21082) = false := by
  decide +kernel

theorem node_context_10_21082_1151256 : EJMOriginalGlobalDAGData.nodes 11 ⟨1151256, by decide⟩ =
    .split (coordinate 10) (![⟨1151200, by decide⟩,⟨1151227, by decide⟩,⟨1109453, by decide⟩,⟨1151255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21082_1151256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21082 ⟨1151256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21082
    ⟨1151256, by decide⟩ (by decide) (![⟨1151200, by decide⟩,⟨1151227, by decide⟩,⟨1109453, by decide⟩,⟨1151255, by decide⟩]) unmarked_context_10_21082_1151256 node_context_10_21082_1151256
  intro a
  fin_cases a
  · exact context_11_84328_1151200
  · exact context_11_84329_1151227
  · exact context_11_84330_1109453
  · exact context_11_84331_1151255

theorem selected_cut_42119 : selected 10 ⟨1151294, by decide⟩
    (prefixPartial 11 84332) = some ⟨11, 2, 0, 1151294, 84332, 2833, 262144⟩ := by
  decide +kernel

theorem context_11_84332_1151294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84332 ⟨1151294, by decide⟩ :=
  accepted_of_selected 11 84332 ⟨1151294, by decide⟩ ⟨11, 2, 0, 1151294, 84332, 2833, 262144⟩
    (by decide) selected_cut_42119

theorem selected_cut_42120 : selected 10 ⟨1151321, by decide⟩
    (prefixPartial 11 84333) = some ⟨11, 2, 0, 1151321, 84333, 1941, 262144⟩ := by
  decide +kernel

theorem context_11_84333_1151321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84333 ⟨1151321, by decide⟩ :=
  accepted_of_selected 11 84333 ⟨1151321, by decide⟩ ⟨11, 2, 0, 1151321, 84333, 1941, 262144⟩
    (by decide) selected_cut_42120

theorem selected_cut_42121 : selected 10 ⟨1151349, by decide⟩
    (prefixPartial 11 84334) = some ⟨11, 2, 0, 1151349, 84334, 2021, 262144⟩ := by
  decide +kernel

theorem context_11_84334_1151349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84334 ⟨1151349, by decide⟩ :=
  accepted_of_selected 11 84334 ⟨1151349, by decide⟩ ⟨11, 2, 0, 1151349, 84334, 2021, 262144⟩
    (by decide) selected_cut_42121

theorem selected_cut_42122 : selected 10 ⟨1151372, by decide⟩
    (prefixPartial 11 84335) = some ⟨11, 2, 0, 1151372, 84335, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_84335_1151372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84335 ⟨1151372, by decide⟩ :=
  accepted_of_selected 11 84335 ⟨1151372, by decide⟩ ⟨11, 2, 0, 1151372, 84335, 1661, 262144⟩
    (by decide) selected_cut_42122

theorem unmarked_context_10_21083_1151373 : frontier 11 ⟨1151373, by decide⟩
    (prefixCache 10 21083) (prefixPartial 10 21083) = false := by
  decide +kernel

theorem node_context_10_21083_1151373 : EJMOriginalGlobalDAGData.nodes 11 ⟨1151373, by decide⟩ =
    .split (coordinate 10) (![⟨1151294, by decide⟩,⟨1151321, by decide⟩,⟨1151349, by decide⟩,⟨1151372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21083_1151373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21083 ⟨1151373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21083
    ⟨1151373, by decide⟩ (by decide) (![⟨1151294, by decide⟩,⟨1151321, by decide⟩,⟨1151349, by decide⟩,⟨1151372, by decide⟩]) unmarked_context_10_21083_1151373 node_context_10_21083_1151373
  intro a
  fin_cases a
  · exact context_11_84332_1151294
  · exact context_11_84333_1151321
  · exact context_11_84334_1151349
  · exact context_11_84335_1151372

theorem unmarked_context_9_5270_1151374 : frontier 12 ⟨1151374, by decide⟩
    (prefixCache 9 5270) (prefixPartial 9 5270) = false := by
  decide +kernel

theorem node_context_9_5270_1151374 : EJMOriginalGlobalDAGData.nodes 12 ⟨1151374, by decide⟩ =
    .split (coordinate 9) (![⟨1151035, by decide⟩,⟨1151168, by decide⟩,⟨1151256, by decide⟩,⟨1151373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5270_1151374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5270 ⟨1151374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5270
    ⟨1151374, by decide⟩ (by decide) (![⟨1151035, by decide⟩,⟨1151168, by decide⟩,⟨1151256, by decide⟩,⟨1151373, by decide⟩]) unmarked_context_9_5270_1151374 node_context_9_5270_1151374
  intro a
  fin_cases a
  · exact context_10_21080_1151035
  · exact context_10_21081_1151168
  · exact context_10_21082_1151256
  · exact context_10_21083_1151373

theorem selected_cut_42123 : selected 10 ⟨1151394, by decide⟩
    (prefixPartial 11 84336) = some ⟨11, 2, 0, 1151394, 84336, 1613, 262144⟩ := by
  decide +kernel

theorem context_11_84336_1151394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84336 ⟨1151394, by decide⟩ :=
  accepted_of_selected 11 84336 ⟨1151394, by decide⟩ ⟨11, 2, 0, 1151394, 84336, 1613, 262144⟩
    (by decide) selected_cut_42123

theorem selected_cut_42124 : selected 10 ⟨1151408, by decide⟩
    (prefixPartial 11 84337) = some ⟨11, 2, 0, 1151408, 84337, 1293, 262144⟩ := by
  decide +kernel

theorem context_11_84337_1151408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84337 ⟨1151408, by decide⟩ :=
  accepted_of_selected 11 84337 ⟨1151408, by decide⟩ ⟨11, 2, 0, 1151408, 84337, 1293, 262144⟩
    (by decide) selected_cut_42124

theorem selected_cut_42125 : selected 10 ⟨1151431, by decide⟩
    (prefixPartial 11 84338) = some ⟨11, 2, 0, 1151431, 84338, 1693, 262144⟩ := by
  decide +kernel

theorem context_11_84338_1151431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84338 ⟨1151431, by decide⟩ :=
  accepted_of_selected 11 84338 ⟨1151431, by decide⟩ ⟨11, 2, 0, 1151431, 84338, 1693, 262144⟩
    (by decide) selected_cut_42125

theorem selected_cut_42126 : selected 10 ⟨1151446, by decide⟩
    (prefixPartial 11 84339) = some ⟨11, 2, 0, 1151446, 84339, 1241, 262144⟩ := by
  decide +kernel

theorem context_11_84339_1151446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84339 ⟨1151446, by decide⟩ :=
  accepted_of_selected 11 84339 ⟨1151446, by decide⟩ ⟨11, 2, 0, 1151446, 84339, 1241, 262144⟩
    (by decide) selected_cut_42126

theorem unmarked_context_10_21084_1151447 : frontier 11 ⟨1151447, by decide⟩
    (prefixCache 10 21084) (prefixPartial 10 21084) = false := by
  decide +kernel

theorem node_context_10_21084_1151447 : EJMOriginalGlobalDAGData.nodes 11 ⟨1151447, by decide⟩ =
    .split (coordinate 10) (![⟨1151394, by decide⟩,⟨1151408, by decide⟩,⟨1151431, by decide⟩,⟨1151446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21084_1151447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21084 ⟨1151447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21084
    ⟨1151447, by decide⟩ (by decide) (![⟨1151394, by decide⟩,⟨1151408, by decide⟩,⟨1151431, by decide⟩,⟨1151446, by decide⟩]) unmarked_context_10_21084_1151447 node_context_10_21084_1151447
  intro a
  fin_cases a
  · exact context_11_84336_1151394
  · exact context_11_84337_1151408
  · exact context_11_84338_1151431
  · exact context_11_84339_1151446

theorem selected_cut_42127 : selected 11 ⟨1151488, by decide⟩
    (prefixPartial 10 21085) = some ⟨10, 2, 0, 1151488, 21085, 3153, 1048576⟩ := by
  decide +kernel

theorem context_10_21085_1151488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21085 ⟨1151488, by decide⟩ :=
  accepted_of_selected 10 21085 ⟨1151488, by decide⟩ ⟨10, 2, 0, 1151488, 21085, 3153, 1048576⟩
    (by decide) selected_cut_42127

theorem selected_cut_42128 : selected 11 ⟨1151527, by decide⟩
    (prefixPartial 10 21086) = some ⟨10, 2, 0, 1151527, 21086, 2177, 1048576⟩ := by
  decide +kernel

theorem context_10_21086_1151527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21086 ⟨1151527, by decide⟩ :=
  accepted_of_selected 10 21086 ⟨1151527, by decide⟩ ⟨10, 2, 0, 1151527, 21086, 2177, 1048576⟩
    (by decide) selected_cut_42128

theorem selected_cut_42129 : selected 11 ⟨1151537, by decide⟩
    (prefixPartial 10 21087) = some ⟨10, 2, 0, 1151537, 21087, 465, 1048576⟩ := by
  decide +kernel

theorem context_10_21087_1151537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21087 ⟨1151537, by decide⟩ :=
  accepted_of_selected 10 21087 ⟨1151537, by decide⟩ ⟨10, 2, 0, 1151537, 21087, 465, 1048576⟩
    (by decide) selected_cut_42129

theorem unmarked_context_9_5271_1151538 : frontier 12 ⟨1151538, by decide⟩
    (prefixCache 9 5271) (prefixPartial 9 5271) = false := by
  decide +kernel

theorem node_context_9_5271_1151538 : EJMOriginalGlobalDAGData.nodes 12 ⟨1151538, by decide⟩ =
    .split (coordinate 9) (![⟨1151447, by decide⟩,⟨1151488, by decide⟩,⟨1151527, by decide⟩,⟨1151537, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5271_1151538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5271 ⟨1151538, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5271
    ⟨1151538, by decide⟩ (by decide) (![⟨1151447, by decide⟩,⟨1151488, by decide⟩,⟨1151527, by decide⟩,⟨1151537, by decide⟩]) unmarked_context_9_5271_1151538 node_context_9_5271_1151538
  intro a
  fin_cases a
  · exact context_10_21084_1151447
  · exact context_10_21085_1151488
  · exact context_10_21086_1151527
  · exact context_10_21087_1151537

theorem unmarked_context_8_1317_1151539 : frontier 13 ⟨1151539, by decide⟩
    (prefixCache 8 1317) (prefixPartial 8 1317) = false := by
  decide +kernel

theorem node_context_8_1317_1151539 : EJMOriginalGlobalDAGData.nodes 13 ⟨1151539, by decide⟩ =
    .split (coordinate 8) (![⟨1149994, by decide⟩,⟨1150802, by decide⟩,⟨1151374, by decide⟩,⟨1151538, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1317_1151539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1317 ⟨1151539, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1317
    ⟨1151539, by decide⟩ (by decide) (![⟨1149994, by decide⟩,⟨1150802, by decide⟩,⟨1151374, by decide⟩,⟨1151538, by decide⟩]) unmarked_context_8_1317_1151539 node_context_8_1317_1151539
  intro a
  fin_cases a
  · exact context_9_5268_1149994
  · exact context_9_5269_1150802
  · exact context_9_5270_1151374
  · exact context_9_5271_1151538

theorem selected_cut_42130 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84352) = some ⟨11, 1, 0, 434745, 84352, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84352_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84352 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84352 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84352, 1, 262144⟩
    (by decide) selected_cut_42130

theorem selected_cut_42131 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 337412) = some ⟨12, 1, 0, 448748, 337412, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337412_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337412 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 337412 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 337412, 1, 65536⟩
    (by decide) selected_cut_42131

theorem selected_cut_42132 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 337413) = some ⟨12, 1, 0, 34034, 337413, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337413_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337413 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 337413 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 337413, 1, 65536⟩
    (by decide) selected_cut_42132

theorem selected_cut_42133 : selected 9 ⟨1151578, by decide⟩
    (prefixPartial 12 337414) = some ⟨12, 2, 0, 1151578, 337414, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_337414_1151578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337414 ⟨1151578, by decide⟩ :=
  accepted_of_selected 12 337414 ⟨1151578, by decide⟩ ⟨12, 2, 0, 1151578, 337414, 2769, 65536⟩
    (by decide) selected_cut_42133

theorem selected_cut_42134 : selected 9 ⟨1151635, by decide⟩
    (prefixPartial 12 337415) = some ⟨12, 2, 0, 1151635, 337415, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_337415_1151635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337415 ⟨1151635, by decide⟩ :=
  accepted_of_selected 12 337415 ⟨1151635, by decide⟩ ⟨12, 2, 0, 1151635, 337415, 3285, 65536⟩
    (by decide) selected_cut_42134

theorem unmarked_context_11_84353_1151636 : frontier 10 ⟨1151636, by decide⟩
    (prefixCache 11 84353) (prefixPartial 11 84353) = false := by
  decide +kernel

theorem node_context_11_84353_1151636 : EJMOriginalGlobalDAGData.nodes 10 ⟨1151636, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1151578, by decide⟩,⟨1151635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84353_1151636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84353 ⟨1151636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84353
    ⟨1151636, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1151578, by decide⟩,⟨1151635, by decide⟩]) unmarked_context_11_84353_1151636 node_context_11_84353_1151636
  intro a
  fin_cases a
  · exact context_12_337412_448748
  · exact context_12_337413_34034
  · exact context_12_337414_1151578
  · exact context_12_337415_1151635

theorem selected_cut_42135 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 337416) = some ⟨12, 1, 0, 448748, 337416, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337416_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337416 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 337416 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 337416, 1, 65536⟩
    (by decide) selected_cut_42135

theorem selected_cut_42136 : selected 9 ⟨1151691, by decide⟩
    (prefixPartial 12 337417) = some ⟨12, 2, 0, 1151691, 337417, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_337417_1151691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337417 ⟨1151691, by decide⟩ :=
  accepted_of_selected 12 337417 ⟨1151691, by decide⟩ ⟨12, 2, 0, 1151691, 337417, 2721, 65536⟩
    (by decide) selected_cut_42136

theorem selected_cut_42137 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 337418) = some ⟨12, 1, 0, 893903, 337418, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337418_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337418 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 337418 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 337418, 1, 65536⟩
    (by decide) selected_cut_42137

theorem selected_cut_42138 : selected 9 ⟨1151757, by decide⟩
    (prefixPartial 12 337419) = some ⟨12, 2, 0, 1151757, 337419, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_337419_1151757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337419 ⟨1151757, by decide⟩ :=
  accepted_of_selected 12 337419 ⟨1151757, by decide⟩ ⟨12, 2, 0, 1151757, 337419, 3465, 65536⟩
    (by decide) selected_cut_42138

theorem unmarked_context_11_84354_1151758 : frontier 10 ⟨1151758, by decide⟩
    (prefixCache 11 84354) (prefixPartial 11 84354) = false := by
  decide +kernel

theorem node_context_11_84354_1151758 : EJMOriginalGlobalDAGData.nodes 10 ⟨1151758, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1151691, by decide⟩,⟨893903, by decide⟩,⟨1151757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84354_1151758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84354 ⟨1151758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84354
    ⟨1151758, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1151691, by decide⟩,⟨893903, by decide⟩,⟨1151757, by decide⟩]) unmarked_context_11_84354_1151758 node_context_11_84354_1151758
  intro a
  fin_cases a
  · exact context_12_337416_448748
  · exact context_12_337417_1151691
  · exact context_12_337418_893903
  · exact context_12_337419_1151757

theorem selected_cut_42139 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 337420) = some ⟨12, 1, 0, 448748, 337420, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337420_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337420 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 337420 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 337420, 1, 65536⟩
    (by decide) selected_cut_42139

theorem selected_cut_42140 : selected 9 ⟨1151798, by decide⟩
    (prefixPartial 12 337421) = some ⟨12, 2, 0, 1151798, 337421, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_337421_1151798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337421 ⟨1151798, by decide⟩ :=
  accepted_of_selected 12 337421 ⟨1151798, by decide⟩ ⟨12, 2, 0, 1151798, 337421, 2617, 65536⟩
    (by decide) selected_cut_42140

theorem selected_cut_42141 : selected 9 ⟨1151850, by decide⟩
    (prefixPartial 12 337422) = some ⟨12, 2, 0, 1151850, 337422, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_337422_1151850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337422 ⟨1151850, by decide⟩ :=
  accepted_of_selected 12 337422 ⟨1151850, by decide⟩ ⟨12, 2, 0, 1151850, 337422, 2909, 65536⟩
    (by decide) selected_cut_42141

theorem selected_cut_42142 : selected 9 ⟨1151897, by decide⟩
    (prefixPartial 12 337423) = some ⟨12, 2, 0, 1151897, 337423, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_337423_1151897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337423 ⟨1151897, by decide⟩ :=
  accepted_of_selected 12 337423 ⟨1151897, by decide⟩ ⟨12, 2, 0, 1151897, 337423, 3065, 65536⟩
    (by decide) selected_cut_42142

theorem unmarked_context_11_84355_1151898 : frontier 10 ⟨1151898, by decide⟩
    (prefixCache 11 84355) (prefixPartial 11 84355) = false := by
  decide +kernel

theorem node_context_11_84355_1151898 : EJMOriginalGlobalDAGData.nodes 10 ⟨1151898, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1151798, by decide⟩,⟨1151850, by decide⟩,⟨1151897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84355_1151898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84355 ⟨1151898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84355
    ⟨1151898, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1151798, by decide⟩,⟨1151850, by decide⟩,⟨1151897, by decide⟩]) unmarked_context_11_84355_1151898 node_context_11_84355_1151898
  intro a
  fin_cases a
  · exact context_12_337420_448748
  · exact context_12_337421_1151798
  · exact context_12_337422_1151850
  · exact context_12_337423_1151897

theorem unmarked_context_10_21088_1151899 : frontier 11 ⟨1151899, by decide⟩
    (prefixCache 10 21088) (prefixPartial 10 21088) = false := by
  decide +kernel

theorem node_context_10_21088_1151899 : EJMOriginalGlobalDAGData.nodes 11 ⟨1151899, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1151636, by decide⟩,⟨1151758, by decide⟩,⟨1151898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21088_1151899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21088 ⟨1151899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21088
    ⟨1151899, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1151636, by decide⟩,⟨1151758, by decide⟩,⟨1151898, by decide⟩]) unmarked_context_10_21088_1151899 node_context_10_21088_1151899
  intro a
  fin_cases a
  · exact context_11_84352_434745
  · exact context_11_84353_1151636
  · exact context_11_84354_1151758
  · exact context_11_84355_1151898

theorem selected_cut_42143 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337424) = some ⟨12, 1, 0, 1108174, 337424, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337424_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337424 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337424 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337424, 1, 65536⟩
    (by decide) selected_cut_42143

theorem selected_cut_42144 : selected 9 ⟨1151931, by decide⟩
    (prefixPartial 12 337425) = some ⟨12, 2, 0, 1151931, 337425, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_337425_1151931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337425 ⟨1151931, by decide⟩ :=
  accepted_of_selected 12 337425 ⟨1151931, by decide⟩ ⟨12, 2, 0, 1151931, 337425, 2361, 65536⟩
    (by decide) selected_cut_42144

theorem selected_cut_42145 : selected 9 ⟨1151970, by decide⟩
    (prefixPartial 12 337426) = some ⟨12, 2, 0, 1151970, 337426, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_337426_1151970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337426 ⟨1151970, by decide⟩ :=
  accepted_of_selected 12 337426 ⟨1151970, by decide⟩ ⟨12, 2, 0, 1151970, 337426, 2669, 65536⟩
    (by decide) selected_cut_42145

theorem selected_cut_42146 : selected 9 ⟨1152026, by decide⟩
    (prefixPartial 12 337427) = some ⟨12, 2, 0, 1152026, 337427, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_337427_1152026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337427 ⟨1152026, by decide⟩ :=
  accepted_of_selected 12 337427 ⟨1152026, by decide⟩ ⟨12, 2, 0, 1152026, 337427, 3125, 65536⟩
    (by decide) selected_cut_42146

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
